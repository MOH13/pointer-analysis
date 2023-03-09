use analysis::PointsToAnalysis;
use llvm_ir::Module;
use solver::{BasicSolver, GenericSolver};
use std::env;
use std::io;

mod analysis;
mod bit_index_utils;
mod module_visitor;
mod solver;

fn main() -> io::Result<()> {
    let file_path = env::args().nth(1).expect("Missing bc file path");
    let module = Module::from_bc_path(&file_path).expect("Error parsing bc file");

    let result = PointsToAnalysis::run::<GenericSolver<_, BasicSolver>>(&module);
    println!("{result}");

    Ok(())
}
