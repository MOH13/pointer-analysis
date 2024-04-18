use std::fmt::Display;

use clap::Parser;
use clap::ValueEnum;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Path to .bc file
    pub file_path: String,
    // Select used solver
    #[arg(short, long, default_value_t = SolverMode::Wave)]
    pub solver: SolverMode,
    #[arg(short, long, default_value_t = TermSet::Roaring)]
    pub termset: TermSet,
    /// List of keywords that must present to be included in output
    #[arg(short, long)]
    pub include_keywords: Vec<String>,
    /// List of keywords to exclude from output
    #[arg(short, long)]
    pub exclude_keywords: Vec<String>,
    /// Don't print any output
    #[arg(short = 'O', long, default_value_t = false)]
    pub dont_output: bool,
    /// Include empty points-to sets in output
    #[arg(short = 'E', long, default_value_t = false)]
    pub include_empty: bool,
    /// Exclude strings from points-to set output
    #[arg(short = 'S', long, default_value_t = false)]
    pub exclude_strings: bool,
    #[arg(short = 'I', long, default_value_t = false)]
    pub interactive_output: bool,
    /// Don't print warnings
    #[arg(short = 'q', long, default_value_t = false)]
    pub quiet: bool,
    /// Print information about term set sizes
    #[arg(short = 'C', long, default_value_t = false)]
    pub count_terms: bool,
    /// Visualize constraint graph after solving (creates a Graphviz DOT file at given path)
    #[arg(short = 'v', long)]
    pub visualize: Option<String>,
    /// List of functions to treat as malloc
    #[arg(short, long)]
    pub malloc_wrappers: Vec<String>,
    /// List of functions to treat as realloc
    #[arg(short, long)]
    pub realloc_wrappers: Vec<String>,
    /// Set call string length when using context-sensitivity (range: 0 - 2)
    #[arg(short = 'c', long, default_value_t = 1)]
    pub call_string: usize,
    /// List of points-to queries
    #[arg(long)]
    pub points_to_queries: Vec<String>,
    /// List of pointed-by queries
    #[arg(long)]
    pub pointed_by_queries: Vec<String>,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
pub enum SolverMode {
    /// Basic worklist based solver
    Basic,
    /// Wave propagation based solver
    Wave,
    /// Do not solve (used to test constraint generation speed)
    DryRun,
    // Solve context sensitively
    Context,
    // Justification
    Justify,
}

impl Display for SolverMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SolverMode::Basic => write!(f, "basic"),
            SolverMode::Wave => write!(f, "wave"),
            SolverMode::DryRun => write!(f, "dry-run"),
            SolverMode::Context => write!(f, "context"),
            SolverMode::Justify => write!(f, "justify"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
pub enum TermSet {
    /// Hashset
    Hash,
    /// Roaring bitmap
    Roaring,
    /// Shared Bitvec
    SharedBitVec,
}

impl Display for TermSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TermSet::Hash => write!(f, "hash"),
            TermSet::Roaring => write!(f, "roaring"),
            TermSet::SharedBitVec => write!(f, "shared bitvec"),
        }
    }
}
