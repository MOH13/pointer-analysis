use std::fmt::Display;

use clap::Parser;
use clap::ValueEnum;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Path to .bc file
    pub file_path: String,
    // Select used solver
    #[arg(short, long, default_value_t = SolverMode::Basic)]
    pub solver: SolverMode,
    #[arg(short, long, default_value_t = TermSet::Hash)]
    pub termset: TermSet,
    /// List of keywords that must present to be included in output
    #[arg(short, long)]
    pub include_keywords: Vec<String>,
    /// List of keywords to exclude from output
    #[arg(short, long)]
    pub exclude_keywords: Vec<String>,
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
    /// Visualize constraint graph after solving (creates a Graphviz DOT file at given path)
    #[arg(short = 'v', long)]
    pub visualize: Option<String>,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
pub enum SolverMode {
    /// Basic worklist based solver
    Basic,
    /// Wave propagation based solver
    Wave,
    /// Do not solve (used to test constraint generation speed)
    DryRun,
}

impl Display for SolverMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SolverMode::Basic => write!(f, "basic"),
            SolverMode::Wave => write!(f, "wave"),
            SolverMode::DryRun => write!(f, "dry-run"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
pub enum TermSet {
    /// Bitvec
    BitVec,
    /// Hashset
    Hash,
    /// Roaring bitmap
    Roaring,
}

impl Display for TermSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TermSet::BitVec => write!(f, "bitvec"),
            TermSet::Hash => write!(f, "hash"),
            TermSet::Roaring => write!(f, "roaring"),
        }
    }
}
