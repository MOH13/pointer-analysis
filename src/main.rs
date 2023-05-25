use clap::Parser;
use clap::ValueEnum;
use hashbrown::HashMap;
use llvm_ir::Module;
use log::error;
use pointer_analysis::analysis::{cell_is_in_function, Cell, PointsToAnalysis, PointsToResult};
use pointer_analysis::solver::HashWavePropagationSolver;
use pointer_analysis::solver::RoaringWavePropagationSolver;
use pointer_analysis::solver::{
    BasicBitVecSolver, BasicHashSolver, BasicRoaringSolver, GenericSolver, StatSolver,
};
use std::io::Write;
use std::{io, process};

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
    /// Visualize constraint graph after solving (creates a Graphviz DOT file at given path)
    #[arg(short = 'v', long)]
    visualize: Option<String>,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
enum SolverMode {
    /// Bitvec based solver
    BitVec,
    /// Hashset based solver
    Hash,
    /// Roaring bitmap based solver
    Roaring,
    /// Hashset based wave propagation
    HashWave,
    /// Roaring bitmap based wave propagation
    RoaringWave,
    /// Do not solve (used to test constraint generation speed)
    DryRun,
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
        PointsToResult(match (args.solver, args.visualize) {
            (Some(SolverMode::Hash), Some(path)) => {
                PointsToAnalysis::run_and_visualize::<GenericSolver<_, BasicHashSolver, _>>(
                    &module, &path,
                )
                .0
            }
            (Some(SolverMode::Roaring), Some(path)) => {
                PointsToAnalysis::run_and_visualize::<GenericSolver<_, BasicRoaringSolver, _>>(
                    &module, &path,
                )
                .0
            }
            (Some(SolverMode::Hash), None) => {
                PointsToAnalysis::run::<GenericSolver<_, BasicHashSolver, _>>(&module).0
            }
            (Some(SolverMode::Roaring), None) => {
                PointsToAnalysis::run::<GenericSolver<_, BasicRoaringSolver, _>>(&module).0
            }
            (Some(SolverMode::HashWave), Some(path)) => PointsToAnalysis::run_and_visualize::<
                GenericSolver<_, HashWavePropagationSolver, _>,
            >(&module, &path)
            .0,
            (Some(SolverMode::RoaringWave), Some(path)) | (None, Some(path)) => {
                PointsToAnalysis::run_and_visualize::<
                    GenericSolver<_, RoaringWavePropagationSolver, _>,
                >(&module, &path)
                .0
            }
            (Some(SolverMode::HashWave), None) => {
                PointsToAnalysis::run::<GenericSolver<_, HashWavePropagationSolver, _>>(&module).0
            }
            (Some(SolverMode::RoaringWave), None) | (None, None) => {
                PointsToAnalysis::run::<GenericSolver<_, RoaringWavePropagationSolver, _>>(&module)
                    .0
            }
            (Some(SolverMode::BitVec), None) => {
                PointsToAnalysis::run::<GenericSolver<_, BasicBitVecSolver, _>>(&module).0
            }
            (Some(SolverMode::DryRun), Some(path)) => {
                PointsToAnalysis::run_and_visualize::<StatSolver<_>>(&module, &path);
                HashMap::new()
            }
            (Some(SolverMode::DryRun), None) => {
                PointsToAnalysis::run::<StatSolver<_>>(&module);
                HashMap::new()
            }
            _ => {
                error!("Cannot visualize with chosen Solver Mode");
                process::exit(1)
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
