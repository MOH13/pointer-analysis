mod macros;

use clap::Parser;
use hashbrown::HashSet;
use llvm_ir::Module;
use pointer_analysis::analysis::{cell_is_in_function, Cell, PointsToAnalysis, PointsToResult};
use pointer_analysis::cli::{Args, SolverMode, TermSet};
use pointer_analysis::solver::{BasicBetterBitVecSolver, RoaringWavePropagationSolver, Solver};
use pointer_analysis::solver::{BasicHashSolver, BasicRoaringSolver, GenericSolver, StatSolver};
use pointer_analysis::solver::{BetterBitVecWavePropagationSolver, HashWavePropagationSolver};
use std::io;
use std::io::Write;

const STRING_FILTER: &'static str = ".str.";

fn show_output<'a, S: Solver<Term = Cell<'a>, TermSet = HashSet<Cell<'a>>>>(
    result: PointsToResult<'a, S>,
    args: &Args,
) {
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
            print!("Search nodes in function: ");
            std::io::stdout().flush().expect("Could not flush stdout");
            let mut input = String::new();
            std::io::stdin()
                .read_line(&mut input)
                .expect("Cannot read user input");
            let function = input.trim();
            if function == "" {
                break;
            }
            let filtered_result = result.get_filtered_entries(
                |c, set| {
                    cell_is_in_function(c, function) && (args.include_empty || !set.is_empty())
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

    match (args.solver, args.termset, args.visualize.clone()) {
        // Basic solver
        (SolverMode::Basic, TermSet::Hash, visualize) => {
            let result = match visualize {
                Some(path) => PointsToAnalysis::run_and_visualize::<
                    GenericSolver<_, BasicHashSolver, _>,
                >(&module, &path),
                None => PointsToAnalysis::run::<GenericSolver<_, BasicHashSolver, _>>(&module),
            };
            show_output(result, &args);
        }
        (SolverMode::Basic, TermSet::Roaring, visualize) => {
            let result = match visualize {
                Some(path) => PointsToAnalysis::run_and_visualize::<
                    GenericSolver<_, BasicRoaringSolver, _>,
                >(&module, &path),
                None => PointsToAnalysis::run::<GenericSolver<_, BasicRoaringSolver, _>>(&module),
            };
            show_output(result, &args);
        }
        (SolverMode::Basic, TermSet::BitVec, visualize) => {
            let result = match visualize {
                Some(path) => PointsToAnalysis::run_and_visualize::<
                    GenericSolver<_, BasicBetterBitVecSolver, _>,
                >(&module, &path),
                None => {
                    PointsToAnalysis::run::<GenericSolver<_, BasicBetterBitVecSolver, _>>(&module)
                }
            };
            show_output(result, &args);
        }
        // Wave prop solver
        // Basic solver
        (SolverMode::Wave, TermSet::Hash, visualize) => {
            let result = match visualize {
                Some(path) => PointsToAnalysis::run_and_visualize::<
                    GenericSolver<_, HashWavePropagationSolver, _>,
                >(&module, &path),
                None => {
                    PointsToAnalysis::run::<GenericSolver<_, HashWavePropagationSolver, _>>(&module)
                }
            };
            show_output(result, &args);
        }
        (SolverMode::Wave, TermSet::Roaring, visualize) => {
            let result = match visualize {
                Some(path) => PointsToAnalysis::run_and_visualize::<
                    GenericSolver<_, RoaringWavePropagationSolver, _>,
                >(&module, &path),
                None => PointsToAnalysis::run::<GenericSolver<_, RoaringWavePropagationSolver, _>>(
                    &module,
                ),
            };
            show_output(result, &args);
        }
        (SolverMode::Wave, TermSet::BitVec, visualize) => {
            let result = match visualize {
                Some(path) => PointsToAnalysis::run_and_visualize::<
                    GenericSolver<_, BetterBitVecWavePropagationSolver, _>,
                >(&module, &path),
                None => PointsToAnalysis::run::<
                    GenericSolver<_, BetterBitVecWavePropagationSolver, _>,
                >(&module),
            };
            show_output(result, &args);
        }
        (SolverMode::DryRun, _, visualize) => {
            let result = match visualize {
                Some(path) => PointsToAnalysis::run_and_visualize::<StatSolver<_>>(&module, &path),
                None => PointsToAnalysis::run::<StatSolver<_>>(&module),
            };
            show_output(result, &args);
        }
    }

    Ok(())
}
