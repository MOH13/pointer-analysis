use analysis::PointsToAnalysis;
use clap::Parser;
use clap::ValueEnum;
use llvm_ir::Module;
use solver::{BasicHashSolver, GenericSolver};
use std::io;

use crate::analysis::PointsToResult;
use crate::solver::BasicBitVecSolver;

mod analysis;
mod bit_index_utils;
mod module_visitor;
mod solver;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    file_path: String,
    #[arg(short, long)]
    solver: Option<SolverMode>,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum SolverMode {
    /// Bitvec based solver
    Bitvec,
    /// Hashset based solver
    Hash,
}

fn main() -> io::Result<()> {
    let args = Args::parse();

    let file_path = args.file_path;
    let module = Module::from_bc_path(&file_path).expect("Error parsing bc file");

    let result: PointsToResult<GenericSolver<_, BasicHashSolver>> =
        PointsToResult(match args.solver {
            Some(SolverMode::Hash) => {
                PointsToAnalysis::run::<GenericSolver<_, BasicHashSolver>>(&module).0
            }
            Some(SolverMode::Bitvec) => {
                PointsToAnalysis::run::<GenericSolver<_, BasicBitVecSolver>>(&module).0
            }
            None => PointsToAnalysis::run::<GenericSolver<_, BasicHashSolver>>(&module).0,
        });
    println!("{result}");

    Ok(())
}
