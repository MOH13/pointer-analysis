mod macros;

use clap::Parser;
use llvm_ir::Module;
use pointer_analysis::analysis::{Cell, PointsToAnalysis, PointsToResult};
use pointer_analysis::cli::{Args, SolverMode, TermSet};
use pointer_analysis::solver::{
    BasicBetterBitVecSolver, BasicSharedBitVecSolver, CallStringSelector, ContextInsensitiveSolver,
    JustificationSolver, RoaringWavePropagationSolver, SharedBitVecContextWavePropagationSolver,
    SharedBitVecWavePropagationSolver, Solver, SolverSolution, TermSetTrait,
};
use pointer_analysis::solver::{BasicHashSolver, BasicRoaringSolver, StatSolver};
use pointer_analysis::solver::{BetterBitVecWavePropagationSolver, HashWavePropagationSolver};
use std::fmt::Debug;
use std::io;
use std::io::Write;

const STRING_FILTER: &'static str = ".str.";

fn show_output<'a, S>(result: PointsToResult<'a, S>, args: &Args)
where
    S: SolverSolution<Term = Cell<'a>>,
    S::TermSet: Debug + IntoIterator<Item = Cell<'a>> + FromIterator<Cell<'a>>,
{
    if !args.dont_output {
        let filtered_result = result.get_filtered_entries(
            |c, set| {
                matches!(c, Cell::Stack(..) | Cell::Global(..))
                    && (args.include_empty || !set.is_empty())
                    && (!args.exclude_strings || !c.to_string().contains(STRING_FILTER))
            },
            |pointee| (!args.exclude_strings || !pointee.to_string().contains(STRING_FILTER)),
            args.include_keywords.iter().map(|s| s.as_str()).collect(),
            args.exclude_keywords.iter().map(|s| s.as_str()).collect(),
        );
        println!("{filtered_result}");
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
            let filtered_result = result.get_filtered_entries(
                |c, set| {
                    (args.include_empty || !set.is_empty()) && c.to_string().contains(cleaned_input)
                },
                |pointee| (!args.exclude_strings || !pointee.to_string().contains(STRING_FILTER)),
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

    let file_path = args.file_path.clone();
    let module = Module::from_bc_path(&file_path).expect("Error parsing bc file");

    let context_selector = CallStringSelector::<1>;

    match (args.solver, args.termset, args.visualize.clone()) {
        // Basic solver
        (SolverMode::Basic, TermSet::Hash, visualize) => {
            let solver = BasicHashSolver::new().as_context_sensitive().as_generic();
            let result = match visualize {
                Some(path) => {
                    PointsToAnalysis::run_and_visualize(solver, &module, context_selector, &path)
                }
                None => PointsToAnalysis::run(solver, &module, context_selector),
            };
            show_output(result, &args);
        }
        (SolverMode::Basic, TermSet::Roaring, visualize) => {
            let solver = BasicRoaringSolver::new()
                .as_context_sensitive()
                .as_generic();
            let result = match visualize {
                Some(path) => {
                    PointsToAnalysis::run_and_visualize(solver, &module, context_selector, &path)
                }
                None => PointsToAnalysis::run(solver, &module, context_selector),
            };
            show_output(result, &args);
        }
        (SolverMode::Basic, TermSet::BitVec, visualize) => {
            let solver = BasicBetterBitVecSolver::new()
                .as_context_sensitive()
                .as_generic();
            let result = match visualize {
                Some(path) => {
                    PointsToAnalysis::run_and_visualize(solver, &module, context_selector, &path)
                }
                None => PointsToAnalysis::run(solver, &module, context_selector),
            };
            show_output(result, &args);
        }
        (SolverMode::Basic, TermSet::SharedBitVec, visualize) => {
            let solver = BasicSharedBitVecSolver::new()
                .as_context_sensitive()
                .as_generic();
            let result = match visualize {
                Some(path) => {
                    PointsToAnalysis::run_and_visualize(solver, &module, context_selector, &path)
                }
                None => PointsToAnalysis::run(solver, &module, context_selector),
            };
            show_output(result, &args);
        }
        // Wave prop solver
        // Basic solver
        (SolverMode::Wave, TermSet::Hash, visualize) => {
            let solver = HashWavePropagationSolver::new()
                .as_context_sensitive()
                .as_generic();
            let result = match visualize {
                Some(path) => {
                    PointsToAnalysis::run_and_visualize(solver, &module, context_selector, &path)
                }
                None => PointsToAnalysis::run(solver, &module, context_selector),
            };
            show_output(result, &args);
        }
        (SolverMode::Wave, TermSet::Roaring, visualize) => {
            let solver = RoaringWavePropagationSolver::new()
                .as_context_sensitive()
                .as_generic();
            let result = match visualize {
                Some(path) => {
                    PointsToAnalysis::run_and_visualize(solver, &module, context_selector, &path)
                }
                None => PointsToAnalysis::run(solver, &module, context_selector),
            };
            show_output(result, &args);
        }
        (SolverMode::Wave, TermSet::SharedBitVec, visualize) => {
            let solver = SharedBitVecWavePropagationSolver::new()
                .as_context_sensitive()
                .as_generic();
            let result = match visualize {
                Some(path) => {
                    PointsToAnalysis::run_and_visualize(solver, &module, context_selector, &path)
                }
                None => PointsToAnalysis::run(solver, &module, context_selector),
            };
            show_output(result, &args);
        }
        (SolverMode::Wave, TermSet::BitVec, visualize) => {
            let solver = BetterBitVecWavePropagationSolver::new()
                .as_context_sensitive()
                .as_generic();
            let result = match visualize {
                Some(path) => {
                    PointsToAnalysis::run_and_visualize(solver, &module, context_selector, &path)
                }
                None => PointsToAnalysis::run(solver, &module, context_selector),
            };
            show_output(result, &args);
        }
        (SolverMode::Context, _, visualize) => {
            let solver = SharedBitVecContextWavePropagationSolver::new();
            let result = match visualize {
                Some(path) => {
                    PointsToAnalysis::run_and_visualize(solver, &module, context_selector, &path)
                }
                None => PointsToAnalysis::run(solver, &module, context_selector),
            };
            show_output(result, &args);
        }
        (SolverMode::DryRun, _, visualize) => {
            let solver = StatSolver::new().as_context_sensitive();
            let result = match visualize {
                Some(path) => {
                    PointsToAnalysis::run_and_visualize(solver, &module, context_selector, &path)
                }
                None => PointsToAnalysis::run(solver, &module, context_selector),
            };
            show_output(result, &args);
        }
        (SolverMode::Justify, ..) => {
            let solver = JustificationSolver::new().as_context_sensitive();
            let justifier = PointsToAnalysis::run(solver, &module, context_selector).0;
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
    }

    Ok(())
}
