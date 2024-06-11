use std::fmt::{self, Display, Formatter};

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
    // Term set representation used in solver
    #[arg(short, long, default_value_t = TermSet::SharedBitVec)]
    pub termset: TermSet,
    /// Use RcTermSet for Tidal Prop with SharedBitVecs
    #[arg(short, long, default_value_t = false)]
    pub aggressive_sharing: bool,
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
    /// Start an interactive shell after solving
    #[arg(short = 'I', long, default_value_t = false)]
    pub interactive_output: bool,
    /// Don't print warnings
    #[arg(short = 'q', long, default_value_t = false)]
    pub quiet: bool,
    /// Print information about term set sizes
    #[arg(short = 'C', long, default_value_t = CountMode::Off)]
    pub count_terms: CountMode,
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
    #[arg(short = 'c', long, default_value_t = 0)]
    pub call_string: usize,
    /// List of points-to queries
    #[arg(short = 'T', long)]
    pub points_to_queries: Vec<String>,
    /// List of pointed-by queries
    #[arg(short = 'B', long)]
    pub pointed_by_queries: Vec<String>,
    /// The kind of demand-driven analysis to run
    #[arg(short, long, default_value_t = DemandMode::All)]
    pub demand_mode: DemandMode,
    /// The kind of call graph analysis to run, requires --demand-mode call-graph
    #[arg(short = 'g', long, default_value_t = CallGraphMode::PointedBy)]
    pub call_graph_mode: CallGraphMode,
    ///
    #[arg(short, long, default_value_t = false)]
    pub full_query_output: bool,
    /// JSON output, ignores all other output options
    #[arg(short, long = "json", default_value_t = false)]
    pub json_output: bool,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
pub enum SolverMode {
    /// Basic worklist based solver
    Basic,
    /// Wave propagation based solver
    Wave,
    /// Do not solve (used to test constraint generation speed)
    DryRun,
    /// Justification
    Justify,
    /// Demand-driven woklist based solver
    BasicDemand,
    /// Tidal propagation based solver
    Tidal,
}

impl Display for SolverMode {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            SolverMode::Basic => write!(f, "basic"),
            SolverMode::Wave => write!(f, "wave"),
            SolverMode::DryRun => write!(f, "dry-run"),
            SolverMode::Justify => write!(f, "justify"),
            SolverMode::BasicDemand => write!(f, "basic-demand"),
            SolverMode::Tidal => write!(f, "tidal"),
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
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            TermSet::Hash => write!(f, "hash"),
            TermSet::Roaring => write!(f, "roaring"),
            TermSet::SharedBitVec => write!(f, "shared-bit-vec"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
pub enum CountMode {
    /// Do not show term counts
    Off,
    /// Show count of all terms
    Unfiltered,
    /// Show count of terms matching filter and demands
    Filtered,
}

impl Default for CountMode {
    fn default() -> Self {
        Self::Off
    }
}

impl Display for CountMode {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            CountMode::Off => write!(f, "off"),
            CountMode::Unfiltered => write!(f, "unfiltered"),
            CountMode::Filtered => write!(f, "filtered"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
pub enum DemandMode {
    All,
    CallGraph,
    Escape,
    List,
}

impl Display for DemandMode {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            DemandMode::All => write!(f, "all"),
            DemandMode::CallGraph => write!(f, "call-graph"),
            DemandMode::Escape => write!(f, "escape"),
            DemandMode::List => write!(f, "list"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
pub enum CallGraphMode {
    PointsTo,
    PointedBy,
    NonTrivial,
}

impl Display for CallGraphMode {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            CallGraphMode::PointsTo => write!(f, "points-to"),
            CallGraphMode::PointedBy => write!(f, "pointed-by"),
            CallGraphMode::NonTrivial => write!(f, "non-trivial"),
        }
    }
}
