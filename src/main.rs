use clap::Parser;
use clap::ValueEnum;
use hashbrown::HashMap;
use llvm_ir::Module;
use pointer_analysis::analysis::{cell_is_in_function, Cell, PointsToAnalysis, PointsToResult};
use pointer_analysis::solver::{
    BasicBitVecSolver, BasicHashSolver, GenericSolver, RoaringSolver, StatSolver,
};
use std::io;
use std::io::Write;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to .bc file
    file_path: String,
    // Select used solver
    #[arg(short, long)]
    solver: Option<SolverMode>,
    /// List of keywords that must present to be included in output
    #[arg(short, long)]
    include_keywords: Vec<String>,
    /// List of keywords to exclude from output
    #[arg(short, long)]
    exclude_keywords: Vec<String>,
    /// Include empty points-to sets in output
    #[arg(short = 'E', long, default_value_t = false)]
    include_empty: bool,
    /// Exclude strings from points-to set output
    #[arg(short = 'S', long, default_value_t = false)]
    exclude_strings: bool,
    #[arg(short = 'I', long, default_value_t = false)]
    interactive_output: bool,
    /// Don't print warnings
    #[arg(short = 'q', long, default_value_t = false)]
    quiet: bool,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
enum SolverMode {
    /// Bitvec based solver
    BitVec,
    /// Hashset based solver
    Hash,
    /// Roaring bitmap based solver
    Roaring,
    /// Do not solve (used to test constraint generation speed)
    None,
}

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
        PointsToResult(match args.solver {
            Some(SolverMode::Hash) => {
                PointsToAnalysis::run::<GenericSolver<_, BasicHashSolver, _>>(&module).0
            }
            Some(SolverMode::Roaring) => {
                PointsToAnalysis::run::<GenericSolver<_, RoaringSolver, _>>(&module).0
            }
            Some(SolverMode::BitVec) => {
                PointsToAnalysis::run::<GenericSolver<_, BasicBitVecSolver, _>>(&module).0
            }
            Some(SolverMode::None) => {
                PointsToAnalysis::run::<StatSolver<_>>(&module);
                HashMap::new()
            }
            None => PointsToAnalysis::run::<GenericSolver<_, BasicHashSolver, _>>(&module).0,
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
