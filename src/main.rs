mod macros;

use clap::Parser;
use hashbrown::HashSet;
use llvm_ir::Module;
use pointer_analysis::analysis::{Cell, Config, PointsToAnalysis, PointsToResult, ResultTrait};
use pointer_analysis::cli::{Args, CallGraphMode, CountMode, DemandMode, SolverMode, TermSet};
use pointer_analysis::module_visitor::VarIdent;
use pointer_analysis::solver::{
    BasicDemandSolver, BasicHashSolver, BasicRoaringSolver, Demands, HashTidalPropagationSolver,
    RcSharedBitVecTidalPropagationSolver, RoaringTidalPropagationSolver,
    SharedBitVecTidalPropagationSolver, StatSolver,
};
use pointer_analysis::solver::{
    BasicSharedBitVecSolver, CallStringSelector, ContextInsensitiveSolver, Demand,
    HashContextWavePropagationSolver, JustificationSolver, RoaringContextWavePropagationSolver,
    SharedBitVecContextWavePropagationSolver, Solver, SolverExt, SolverSolution, TermSetTrait,
};
use pointer_analysis::visualizer::{AsDynamicVisualizableExt, DynamicVisualizableSolver};
use serde::Serialize;
use std::fmt::Debug;
use std::io::Write;
use std::time::{Duration, Instant};
use std::{io, mem};

const STRING_FILTER: &'static str = ".str.";

fn get_demands(args: &Args) -> Demands<Cell> {
    match args.demand_mode {
        DemandMode::All => Demands::All,
        DemandMode::CallGraph => match args.call_graph_mode {
            CallGraphMode::PointsTo => Demands::CallGraphPointsTo,
            CallGraphMode::PointedBy => Demands::CallGraphPointedBy,
            CallGraphMode::NonTrivial => Demands::NonTrivial,
        },
        DemandMode::Escape => Demands::Escape,
        DemandMode::List => {
            let demands = args
                .points_to_queries
                .iter()
                .map(|s| Demand::PointsTo(s.parse().unwrap()))
                .chain(
                    args.pointed_by_queries
                        .iter()
                        .map(|s| Demand::PointedBy(s.parse().unwrap())),
                )
                .collect();
            Demands::List(demands)
        }
    }
}

fn show_count_metrics<T, S>(result: &T)
where
    T: ResultTrait<TermSet = S>,
    S: TermSetTrait,
{
    print!("Collecting count metrics...");
    if result.get_cells().len() > 200000 {
        print!(" (this might take a while)")
    }
    println!();

    let mut counts: Vec<_> = result
        .iter_solutions()
        .map(|(_, mut set)| set.get_len())
        .collect();

    if counts.is_empty() {
        println!("No metrics possible: empty result set");
        return;
    }
    let num_cells = counts.len();
    let total = counts.iter().sum::<usize>();
    let max = counts.iter().max().copied().unwrap_or(0);
    let mean = total as f64 / num_cells as f64;
    let median = counts.select_nth_unstable(num_cells / 2).1;
    println!("Total: {total}");
    println!("Max: {max}");
    println!("Mean: {mean}");
    println!("Median: {median}");
}

fn apply_filters<'b, S>(
    result: &'b impl ResultTrait<TermSet = S>,
    args: &'b Args,
) -> impl ResultTrait + 'b
where
    S: TermSetTrait<Term = Cell>,
{
    result.filter_result(
        |c, set, cache| {
            matches!(c, Cell::Stack(..) | Cell::Global(..) | Cell::Var(..))
                && (args.include_empty || !set.get().is_empty())
                && (!args.exclude_strings || !cache.string_of(c).contains(STRING_FILTER))
        },
        |_pointer, pointee, cache| {
            !args.exclude_strings || !cache.string_of(pointee).contains(STRING_FILTER)
        },
        args.include_keywords.clone(),
        args.exclude_keywords.clone(),
    )
}

fn show_output<S>(mut result: PointsToResult<S>, args: &Args)
where
    S: SolverSolution<Term = Cell>,
    S::TermSet: Debug + IntoIterator<Item = Cell> + FromIterator<Cell>,
{
    if !args.dont_output {
        match mem::take(&mut result.demands) {
            Some(demands) => {
                let mut points_to_demands = HashSet::new();
                let mut pointed_by_demands = HashSet::new();

                for q in demands {
                    match q {
                        Demand::PointsTo(cell) => {
                            points_to_demands.insert(cell);
                        }
                        Demand::PointedBy(cell) => {
                            pointed_by_demands.insert(cell);
                        }
                    }
                }

                let demand_filtered = result.filter_result(
                    |c, set, _cache| {
                        points_to_demands.contains(c)
                            || (!pointed_by_demands.is_empty()
                                && set.get().iter().any(|t| pointed_by_demands.contains(&t)))
                    },
                    |pointer, pointee, _cache| {
                        points_to_demands.contains(pointer) || pointed_by_demands.contains(pointee)
                    },
                    Vec::new(),
                    Vec::new(),
                );
                let filtered_result = apply_filters(&demand_filtered, args);
                println!("{filtered_result}");
                if args.count_terms == CountMode::Filtered {
                    show_count_metrics(&filtered_result);
                }
            }
            None => {
                let filtered_result = apply_filters(&result, args);
                println!("{filtered_result}");
                if args.count_terms == CountMode::Filtered {
                    show_count_metrics(&filtered_result);
                }
            }
        }
    }
    if args.count_terms == CountMode::Unfiltered {
        show_count_metrics(&result);
    }

    if args.interactive_output {
        loop {
            print!("Search nodes: ");
            std::io::stdout().flush().expect("Could not flush stdout");
            let mut input = String::new();
            std::io::stdin()
                .read_line(&mut input)
                .expect("Cannot read user input");
            let cleaned_input = input.trim();
            if cleaned_input == "" {
                break;
            }
            let filtered_result = result.filter_result(
                |c, set, cache| {
                    (args.include_empty || !set.get().is_empty())
                        && cache.string_of(c).contains(cleaned_input)
                },
                |_pointer, pointee, cache| {
                    !args.exclude_strings || !cache.string_of(pointee).contains(STRING_FILTER)
                },
                vec![],
                vec![],
            );
            println!("{filtered_result}");
        }
    }
}

#[derive(Serialize)]
struct JsonOutput {
    module_parse_time_ms: f64,
    pre_analysis_time_ms: f64,
    constraint_gen_time_ms: f64,
    solver_time_ms: f64,
    num_called_functions: u64,
    num_called_non_trivial_functions: u64,
    mean_call_edges: f64,
    mean_non_trivial_call_edges: f64,
    #[serde(flatten)]
    solver_output: Box<dyn erased_serde::Serialize>,
}

impl JsonOutput {
    pub fn from_result<S>(result: PointsToResult<S>, module_parse_time: Duration) -> Self
    where
        S: SolverSolution<Term = Cell>,
    {
        eprintln!("Counting call edges...");
        let mut total_call_edges = 0;
        let mut total_non_trivial_call_edges = 0;
        let num_called_functions = result.called_functions.len() as u64;
        let mut num_called_non_trivial_functions = 0;
        for function in &result.called_functions {
            let num_call_edges = result
                .get(&function)
                .expect("Function not found")
                .get()
                .iter()
                .filter(|c| matches!(c, Cell::Return(_)))
                .count();
            total_call_edges += num_call_edges;
            if !matches!(function, Cell::Var(VarIdent::Global { .. })) {
                num_called_non_trivial_functions += 1;
                total_non_trivial_call_edges += num_call_edges;
            }
        }
        let mean_call_edges = if num_called_functions == 0 {
            eprintln!("Warning: no functions called");
            0f64
        } else {
            total_call_edges as f64 / num_called_functions as f64
        };
        let mean_non_trivial_call_edges = if num_called_non_trivial_functions == 0 {
            eprintln!("Warning: no non-trivial functions called");
            0f64
        } else {
            total_non_trivial_call_edges as f64 / num_called_non_trivial_functions as f64
        };

        Self {
            module_parse_time_ms: module_parse_time.as_secs_f64() * 1000.0,
            pre_analysis_time_ms: result.pre_analysis_time.as_secs_f64() * 1000.0,
            constraint_gen_time_ms: result.constraint_gen_time.as_secs_f64() * 1000.0,
            solver_time_ms: result.solver_time.as_secs_f64() * 1000.0,
            num_called_functions,
            num_called_non_trivial_functions,
            mean_call_edges,
            mean_non_trivial_call_edges,
            solver_output: result.into_solution().as_serialize(),
        }
    }
}

fn main() -> io::Result<()> {
    let args = Args::parse();

    stderrlog::new()
        .module(module_path!())
        .verbosity(log::Level::Warn)
        .quiet(args.quiet)
        .init()
        .unwrap();

    let demands = get_demands(&args);

    let file_path = args.file_path.clone();
    let module_parse_start = Instant::now();
    let module = Module::from_bc_path(&file_path).expect("Error parsing bc file");
    let module_parse_time = module_parse_start.elapsed();

    let context_selector = CallStringSelector::<2>::with_call_string_length(args.call_string);
    let config = Config {
        malloc_wrappers: args.malloc_wrappers.iter().cloned().collect(),
        realloc_wrappers: args.realloc_wrappers.iter().cloned().collect(),
    };

    let solver: DynamicVisualizableSolver<_, _> = match (args.solver, args.termset) {
        // Basic solver
        (SolverMode::Basic, TermSet::Hash) => BasicHashSolver::new()
            .as_context_sensitive()
            .as_generic()
            .as_demand_driven()
            .as_dynamic_visualizable(),
        (SolverMode::Basic, TermSet::Roaring) => BasicRoaringSolver::new()
            .as_context_sensitive()
            .as_generic()
            .as_demand_driven()
            .as_dynamic_visualizable(),
        (SolverMode::Basic, TermSet::SharedBitVec) => BasicSharedBitVecSolver::new()
            .as_context_sensitive()
            .as_generic()
            .as_demand_driven()
            .as_dynamic_visualizable(),
        // Wave prop solver
        (SolverMode::Wave, TermSet::Hash) => HashContextWavePropagationSolver::new()
            .as_demand_driven()
            .as_dynamic_visualizable(),
        (SolverMode::Wave, TermSet::Roaring) => RoaringContextWavePropagationSolver::new()
            .as_demand_driven()
            .as_dynamic_visualizable(),
        (SolverMode::Wave, TermSet::SharedBitVec) => {
            SharedBitVecContextWavePropagationSolver::new()
                .as_demand_driven()
                .as_dynamic_visualizable()
        }
        (SolverMode::DryRun, _) => StatSolver::<Cell>::new()
            .as_context_sensitive()
            .as_demand_driven()
            .as_dynamic_visualizable(),
        // with demands
        (SolverMode::BasicDemand, _) => BasicDemandSolver::new().as_dynamic_visualizable(),
        (SolverMode::Tidal, TermSet::Hash) => {
            HashTidalPropagationSolver::new(false).as_dynamic_visualizable()
        }
        (SolverMode::Tidal, TermSet::Roaring) => {
            RoaringTidalPropagationSolver::new(false).as_dynamic_visualizable()
        }
        (SolverMode::Tidal, TermSet::SharedBitVec) => {
            if args.aggressive_sharing {
                RcSharedBitVecTidalPropagationSolver::new(true).as_dynamic_visualizable()
            } else {
                SharedBitVecTidalPropagationSolver::new(false).as_dynamic_visualizable()
            }
        }
        (SolverMode::Justify, _) => {
            let solver = JustificationSolver::<Cell>::new()
                .as_context_sensitive()
                .as_demand_driven();
            let justifier =
                PointsToAnalysis::run(&solver, &module, context_selector, demands, &config)
                    .into_solution();
            loop {
                let mut input = String::new();
                print!("Enter node to justify: ");
                io::stdout().flush()?;
                io::stdin().read_line(&mut input)?;
                let cleaned_input = input.trim();
                if cleaned_input == "" {
                    continue;
                }
                let Ok(node) = cleaned_input.parse() else {
                    println!("Could not parse node");
                    continue;
                };
                input.clear();
                print!("Enter term to justify: ");
                io::stdout().flush()?;
                io::stdin().read_line(&mut input)?;
                let cleaned_input = input.trim();
                if cleaned_input == "" {
                    continue;
                }
                let Ok(term) = cleaned_input.parse() else {
                    println!("Could not parse term");
                    continue;
                };
                justifier.justify(node, term);
            }
        }
    };

    let result = match &args.visualize {
        Some(path) => PointsToAnalysis::run_and_visualize(
            &solver,
            &module,
            context_selector,
            demands.clone(),
            &config,
            path,
        ),
        None => PointsToAnalysis::run(&solver, &module, context_selector, demands.clone(), &config),
    };

    if args.json_output {
        let json_output = JsonOutput::from_result(result, module_parse_time);
        println!(
            "{}",
            serde_json::to_string_pretty(&json_output).expect("Could not serialize")
        );
        return Ok(());
    }

    show_output(result, &args);

    Ok(())
}
