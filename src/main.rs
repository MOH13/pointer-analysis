#![feature(trace_macros)]

mod macros;

use clap::Parser;
use hashbrown::HashMap;
use llvm_ir::Module;
use pointer_analysis::analysis::{cell_is_in_function, Cell, PointsToAnalysis, PointsToResult};
use pointer_analysis::cli::{Args, SolverMode, TermSet};
use pointer_analysis::solver::RoaringWavePropagationSolver;
use pointer_analysis::solver::{
    BasicBitVecSolver, BasicHashSolver, BasicRoaringSolver, GenericSolver, StatSolver,
};
use pointer_analysis::solver::{BetterBitVecWavePropagationSolver, HashWavePropagationSolver};
use std::io;
use std::io::Write;

const STRING_FILTER: &'static str = ".str.";

fn main() -> io::Result<()> {
    let args = Args::parse();

    stderrlog::new()
        .module(module_path!())
        .verbosity(log::Level::Warn)
        .quiet(args.quiet)
        .init()
        .unwrap();

    let file_path = args.file_path;
    let module = Module::from_bc_path(&file_path).expect("Error parsing bc file");

    let result: PointsToResult<GenericSolver<_, BasicHashSolver, _>> =
        PointsToResult(match (args.solver, args.termset) {
            // Basic solver
            (SolverMode::Basic, TermSet::Hash) => {
                PointsToAnalysis::run::<GenericSolver<_, BasicHashSolver, _>>(&module).0
            }
            (SolverMode::Basic, TermSet::Roaring) => {
                PointsToAnalysis::run::<GenericSolver<_, BasicRoaringSolver, _>>(&module).0
            }
            (SolverMode::Basic, TermSet::BitVec) => {
                PointsToAnalysis::run::<GenericSolver<_, BasicBitVecSolver, _>>(&module).0
            }
            // Wave prop solver
            // Basic solver
            (SolverMode::Wave, TermSet::Hash) => {
                PointsToAnalysis::run::<GenericSolver<_, HashWavePropagationSolver, _>>(&module).0
            }
            (SolverMode::Wave, TermSet::Roaring) => {
                PointsToAnalysis::run::<GenericSolver<_, RoaringWavePropagationSolver, _>>(&module)
                    .0
            }
            (SolverMode::Wave, TermSet::BitVec) => {
                PointsToAnalysis::run::<GenericSolver<_, BetterBitVecWavePropagationSolver, _>>(
                    &module,
                )
                .0
            }
            (SolverMode::None, _) => {
                PointsToAnalysis::run::<StatSolver<_>>(&module);
                HashMap::new()
            }
        });

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

    Ok(())
}
