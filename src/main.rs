mod macros;

use clap::Parser;
use hashbrown::HashSet;
use llvm_ir::Module;
use pointer_analysis::analysis::{Cell, Config, PointsToAnalysis, PointsToResult, ResultTrait};
use pointer_analysis::cli::{Args, CountMode, SolverMode, TermSet};
use pointer_analysis::solver::{
    BasicDemandSolver, BasicHashSolver, BasicRoaringSolver, StatSolver,
};
use pointer_analysis::solver::{
    BasicSharedBitVecSolver, CallStringSelector, ContextInsensitiveSolver, Demand,
    HashContextWavePropagationSolver, JustificationSolver, RoaringContextWavePropagationSolver,
    SharedBitVecContextWavePropagationSolver, Solver, SolverExt, SolverSolution, TermSetTrait,
};
use pointer_analysis::visualizer::{AsDynamicVisualizableExt, DynamicVisualizableSolver};
use std::fmt::Debug;
use std::io;
use std::io::Write;

const STRING_FILTER: &'static str = ".str.";

fn get_demands<'a>(args: &Args) -> Vec<Demand<Cell<'a>>> {
    args.points_to_queries
        .iter()
        .map(|s| Demand::PointsTo(s.parse().unwrap()))
        .chain(
            args.pointed_by_queries
                .iter()
                .map(|s| Demand::PointedBy(s.parse().unwrap())),
        )
        .collect()
}

fn show_count_metrics<'a, T, S>(result: &T)
where
    T: ResultTrait<'a, TermSet = S>,
    S: TermSetTrait,
{
    let mut counts: Vec<_> = result
        .iter_solutions()
        .into_iter()
        .map(|(_, set)| set.len())
        .collect();
    let num_cells = counts.len();
    let total = counts.iter().sum::<usize>();
    let max = counts.iter().copied().max().unwrap_or(0);
    let mean = total as f64 / num_cells as f64;
    let median = counts.select_nth_unstable(num_cells / 2).1;
    println!("Total: {total}");
    println!("Max: {max}");
    println!("Mean: {mean}");
    println!("Median: {median}");
}

fn show_output<'a, S>(
    result: PointsToResult<'a, S>,
    args: &Args,
    demand_filter: Option<&[Demand<Cell<'a>>]>,
) where
    S: SolverSolution<Term = Cell<'a>>,
    S::TermSet: Debug + IntoIterator<Item = Cell<'a>> + FromIterator<Cell<'a>>,
{
    if !args.dont_output {
        let filtered_result = result.filter_result(
            |c, set, cache| {
                matches!(c, Cell::Stack(..) | Cell::Global(..))
                    && (args.include_empty || !set.is_empty())
                    && (!args.exclude_strings || !cache.string_of(c).contains(STRING_FILTER))
            },
            |_pointer, pointee, cache| {
                !args.exclude_strings || !cache.string_of(pointee).contains(STRING_FILTER)
            },
            args.include_keywords.clone(),
            args.exclude_keywords.clone(),
        );
        match demand_filter {
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

                let demand_filtered = filtered_result.filter_result(
                    |c, set, _cache| {
                        points_to_demands.contains(c)
                            || set.iter().any(|t| pointed_by_demands.contains(t))
                    },
                    |pointer, pointee, _cache| {
                        points_to_demands.contains(pointer) || pointed_by_demands.contains(pointee)
                    },
                    Vec::new(),
                    Vec::new(),
                );
                println!("{demand_filtered}");
                if args.count_terms == CountMode::Filtered {
                    show_count_metrics(&demand_filtered);
                }
            }
            None => {
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
                    (args.include_empty || !set.is_empty())
                        && cache.string_of(c).contains(cleaned_input)
                },
                |pointer, pointee, cache| {
                    !args.exclude_strings || !cache.string_of(pointee).contains(STRING_FILTER)
                },
                vec![],
                vec![],
            );
            println!("{filtered_result}");
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
    let module = Module::from_bc_path(&file_path).expect("Error parsing bc file");

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
        (SolverMode::DryRun, _) => StatSolver::<Cell<'_>>::new()
            .as_context_sensitive()
            .as_demand_driven()
            .as_dynamic_visualizable(),
        // with demands
        (SolverMode::BasicDemand, _) => BasicDemandSolver::new().as_dynamic_visualizable(),
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
    let demand_filter = if demands.is_empty() || args.full_query_output {
        None
    } else {
        Some(demands.as_ref())
    };
    show_output(result, &args, demand_filter);

    Ok(())
}
