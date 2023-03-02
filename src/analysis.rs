use std::fmt::{self, Debug, Display, Formatter};

use hashbrown::HashMap;
use llvm_ir::Module;

use crate::module_visitor::{ModuleVisitor, PointerInstruction, PointerModuleVisitor, VarIdent};
use crate::solver::{Constraint, Solver};

pub struct PointsToAnalysis;

impl PointsToAnalysis {
    /// Runs the points-to analysis on LLVM module `module` using `solver`.
    pub fn run<'a, S>(module: &'a Module) -> PointsToResult<S>
    where
        S: Solver<Term = Cell<'a>> + 'a,
    {
        let mut pre_analyzer = PointsToPreAnalyzer::new();
        pre_analyzer.visit_module(module);
        let cells_copy = pre_analyzer.cells.clone();

        let solver = S::new(pre_analyzer.cells);
        let mut points_to_solver = PointsToSolver {
            solver,
            summaries: pre_analyzer.summaries,
        };
        points_to_solver.visit_module(module);

        let result_map = cells_copy
            .into_iter()
            .filter(|c| matches!(c, Cell::Stack { .. }))
            .map(|c| {
                let sol = points_to_solver.solver.get_solution(&c);
                (c, sol)
            })
            .collect();
        PointsToResult(result_map)
    }
}

pub struct PointsToResult<'a, S: Solver>(HashMap<Cell<'a>, S::TermSet>);

impl<'a, S> Display for PointsToResult<'a, S>
where
    S: Solver,
    S::TermSet: fmt::Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for (cell, set) in &self.0 {
            writeln!(f, "[[{cell}]] = {set:#?}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum Cell<'a> {
    Var(VarIdent<'a>),
    // Since LLVM is in SSA, we can use the name of the allocation register to refer to the allocation site
    Stack(VarIdent<'a>),
    Heap(VarIdent<'a>),
    Global(VarIdent<'a>),
}

impl<'a> Display for Cell<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Var(ident) => write!(f, "{ident}"),
            Self::Stack(ident) => write!(f, "stack-{ident}"),
            Self::Heap(ident) => write!(f, "heap-{ident}"),
            Self::Global(ident) => write!(f, "global-{ident}"),
        }
    }
}

impl<'a> Debug for Cell<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

struct FunctionSummary<'a> {
    parameters: Vec<VarIdent<'a>>,
    return_reg: Option<VarIdent<'a>>,
}

/// Visits a module and finds all cells in that module.
/// An allocation site abstraction is used for heap allocations.
/// TODO: Field sensitivity?
struct PointsToPreAnalyzer<'a> {
    cells: Vec<Cell<'a>>,
    summaries: HashMap<&'a str, FunctionSummary<'a>>,
}

impl<'a> PointsToPreAnalyzer<'a> {
    fn new() -> Self {
        Self {
            cells: vec![],
            summaries: HashMap::new(),
        }
    }
}

impl<'a> PointerModuleVisitor<'a> for PointsToPreAnalyzer<'a> {
    fn handle_ptr_function(&mut self, name: &'a str, parameters: Vec<VarIdent<'a>>) {
        for &param in &parameters {
            self.cells.push(Cell::Var(param));
        }

        let summary = FunctionSummary {
            parameters,
            return_reg: None,
        };
        self.summaries.insert(name, summary);
    }

    fn handle_ptr_global(&mut self, ident: VarIdent<'a>) {
        self.cells.push(Cell::Var(ident));
        self.cells.push(Cell::Global(ident));
    }

    fn handle_ptr_instruction(&mut self, instr: PointerInstruction<'a>, fun_name: &'a str) {
        match instr {
            PointerInstruction::Assign { dest, .. }
            | PointerInstruction::Load { dest, .. }
            | PointerInstruction::Phi { dest, .. }
            | PointerInstruction::Call {
                dest: Some(dest), ..
            } => self.cells.push(Cell::Var(dest)),

            PointerInstruction::Alloca { dest } => {
                self.cells.push(Cell::Var(dest));
                self.cells.push(Cell::Stack(dest));
            }

            PointerInstruction::Return { return_reg } => {
                self.summaries.entry_ref(fun_name).and_modify(|s| {
                    s.return_reg = Some(return_reg);
                });
            }

            _ => {}
        }
    }
}

/// Visits a module, generating and solving constraints using a supplied constraint solver.
struct PointsToSolver<'a, S> {
    solver: S,
    summaries: HashMap<&'a str, FunctionSummary<'a>>,
}

impl<'a, S> PointerModuleVisitor<'a> for PointsToSolver<'a, S>
where
    S: Solver<Term = Cell<'a>>,
{
    fn handle_ptr_function(&mut self, _name: &str, _parameters: Vec<VarIdent>) {}

    fn handle_ptr_global(&mut self, ident: VarIdent<'a>) {
        let c = Constraint::Inclusion {
            term: Cell::Global(ident),
            node: Cell::Var(ident),
        };
        self.solver.add_constraint(c);

        // TODO: Fix global initializer stuff
    }

    fn handle_ptr_instruction(&mut self, instr: PointerInstruction<'a>, _fun_name: &'a str) {
        match instr {
            PointerInstruction::Assign { dest, value } => {
                let c = Constraint::Subset {
                    left: Cell::Var(value),
                    right: Cell::Var(dest),
                };
                self.solver.add_constraint(c);
            }

            PointerInstruction::Store { address, value } => {
                let c = Constraint::UnivCondSubsetRight {
                    cond_node: Cell::Var(address),
                    left: Cell::Var(value),
                };
                self.solver.add_constraint(c);
            }

            PointerInstruction::Load { dest, address } => {
                let c = Constraint::UnivCondSubsetLeft {
                    cond_node: Cell::Var(address),
                    right: Cell::Var(dest),
                };
                self.solver.add_constraint(c);
            }

            PointerInstruction::Alloca { dest } => {
                let c = Constraint::Inclusion {
                    term: Cell::Stack(dest),
                    node: Cell::Var(dest),
                };
                self.solver.add_constraint(c);
            }

            PointerInstruction::Phi {
                dest,
                incoming_values,
            } => {
                for value in incoming_values {
                    let c = Constraint::Subset {
                        left: Cell::Var(value),
                        right: Cell::Var(dest),
                    };
                    self.solver.add_constraint(c);
                }
            }

            PointerInstruction::Call {
                dest,
                function,
                arguments,
            } => {
                let summary = &self.summaries[function];
                for (arg, &param) in arguments
                    .iter()
                    .zip(&summary.parameters)
                    .filter_map(|(a, p)| a.map(|a| (a, p)))
                {
                    let c = Constraint::Subset {
                        left: Cell::Var(arg),
                        right: Cell::Var(param),
                    };
                    self.solver.add_constraint(c);
                }

                match (summary.return_reg, dest) {
                    (Some(return_name), Some(dest_name)) => {
                        let c = Constraint::Subset {
                            left: Cell::Var(return_name),
                            right: Cell::Var(dest_name),
                        };
                        self.solver.add_constraint(c);
                    }
                    _ => {}
                }
            }

            _ => {}
        }
    }
}
