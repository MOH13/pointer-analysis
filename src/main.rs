use analysis::PointsToAnalysis;
use clap::Parser;
use clap::ValueEnum;
use llvm_ir::Module;
use solver::{BasicHashSolver, GenericSolver};
use std::io;

use crate::analysis::Cell;
use crate::analysis::PointsToResult;
use crate::solver::BasicBitVecSolver;

mod analysis;
mod bit_index_utils;
mod module_visitor;
mod solver;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to .bc file
    file_path: String,
    #[arg(short, long)]
    // Select used solver
    solver: Option<SolverMode>,
    #[arg(short, long)]
    /// List of keywords that must present to be included in output
    include_keywords: Vec<String>,
    #[arg(short, long)]
    /// List of keywords to exclude from output
    exclude_keywords: Vec<String>,
    #[arg(short = 'E', long, default_value_t = false)]
    /// Include empty points-to sets in output
    include_empty: bool,
    #[arg(short = 'S', long, default_value_t = false)]
    /// Exclude strings from points-to set output
    exclude_strings: bool,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
enum SolverMode {
    /// Bitvec based solver
    Bitvec,
    /// Hashset based solver
    Hash,
}

const STRING_FILTER: &'static str = ".str.";

fn main() -> io::Result<()> {
    let args = Args::parse();

    //dbg!(&args);

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

    Ok(())
}
