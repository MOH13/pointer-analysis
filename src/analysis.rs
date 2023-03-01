use std::fmt::{self, Debug, Display, Formatter};

use hashbrown::HashMap;
use llvm_ir::{Module, Name};

use crate::module_visitor::{
    ModuleVisitor, PointerContext, PointerInstruction, PointerModuleVisitor,
};
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
            writeln!(f, "[[{cell:?}]] = {set:#?}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum Cell<'a> {
    Local {
        reg_name: &'a Name,
        fun_name: &'a str,
    },
    // Since LLVM is in SSA, we can use the name of the allocation register to refer to the allocation site
    Stack {
        reg_name: &'a Name,
        fun_name: &'a str,
    },
    Heap {
        reg_name: &'a Name,
        fun_name: &'a str,
    },
}

impl<'a> Cell<'a> {
    fn new_local(reg_name: &'a Name, fun_name: &'a str) -> Self {
        Self::Local { reg_name, fun_name }
    }
    fn new_stack(reg_name: &'a Name, fun_name: &'a str) -> Self {
        Self::Stack { reg_name, fun_name }
    }
    fn new_heap(reg_name: &'a Name, fun_name: &'a str) -> Self {
        Self::Heap { reg_name, fun_name }
    }
}

impl<'a> Debug for Cell<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Local { reg_name, fun_name } => write!(f, "{reg_name}@{fun_name}"),
            Self::Stack { reg_name, fun_name } => write!(f, "stack-{reg_name}@{fun_name}"),
            Self::Heap { reg_name, fun_name } => write!(f, "heap-{reg_name}@{fun_name}"),
        }
    }
}

struct FunctionSummary<'a> {
    parameters: Vec<&'a Name>,
    return_reg: Option<&'a Name>,
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

    fn add_local(&mut self, reg_name: &'a Name, fun_name: &'a str) {
        self.cells.push(Cell::Local { reg_name, fun_name });
    }

    fn add_stack(&mut self, reg_name: &'a Name, fun_name: &'a str) {
        self.cells.push(Cell::Stack { reg_name, fun_name });
    }

    fn add_heap(&mut self, reg_name: &'a Name, fun_name: &'a str) {
        self.cells.push(Cell::Heap { reg_name, fun_name });
    }
}

impl<'a> PointerModuleVisitor<'a> for PointsToPreAnalyzer<'a> {
    fn handle_ptr_function(&mut self, name: &'a str, parameters: Vec<&'a Name>) {
        for &param in &parameters {
            self.cells.push(Cell::Local {
                reg_name: param,
                fun_name: name,
            });
        }
        let summary = FunctionSummary {
            parameters,
            return_reg: None,
        };
        self.summaries.insert(name, summary);
    }

    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        context: PointerContext<'a>,
    ) {
        match instr {
            PointerInstruction::Assign { dest, .. }
            | PointerInstruction::Load { dest, .. }
            | PointerInstruction::Phi { dest, .. }
            | PointerInstruction::Call {
                dest: Some(dest), ..
            } => self.add_local(dest, context.fun_name),

            PointerInstruction::Alloca { dest } => {
                self.add_local(dest, context.fun_name);
                self.add_stack(dest, context.fun_name)
            }

            PointerInstruction::Return { return_reg } => {
                self.summaries.entry_ref(&context.fun_name).and_modify(|s| {
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
    fn handle_ptr_function(&mut self, _name: &str, _parameters: Vec<&Name>) {}

    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        context: PointerContext<'a>,
    ) {
        match instr {
            PointerInstruction::Assign { dest, value } => {
                let c = Constraint::Subset {
                    left: Cell::new_local(value, context.fun_name),
                    right: Cell::new_local(dest, context.fun_name),
                };
                self.solver.add_constraint(c);
            }

            PointerInstruction::Store { address, value } => {
                let c = Constraint::UnivCondSubsetRight {
                    cond_node: Cell::new_local(address, context.fun_name),
                    left: Cell::new_local(value, context.fun_name),
                };
                self.solver.add_constraint(c);
            }

            PointerInstruction::Load { dest, address } => {
                let c = Constraint::UnivCondSubsetLeft {
                    cond_node: Cell::new_local(address, context.fun_name),
                    right: Cell::new_local(dest, context.fun_name),
                };
                self.solver.add_constraint(c);
            }

            PointerInstruction::Alloca { dest } => {
                let c = Constraint::Inclusion {
                    term: Cell::new_stack(dest, context.fun_name),
                    node: Cell::new_local(dest, context.fun_name),
                };
                self.solver.add_constraint(c);
            }

            PointerInstruction::Phi {
                dest,
                incoming_values,
            } => {
                for value in incoming_values {
                    let c = Constraint::Subset {
                        left: Cell::new_local(value, context.fun_name),
                        right: Cell::new_local(dest, context.fun_name),
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
                        left: Cell::new_local(arg, context.fun_name),
                        right: Cell::new_local(param, function),
                    };
                    self.solver.add_constraint(c);
                }

                match (summary.return_reg, dest) {
                    (Some(return_name), Some(dest_name)) => {
                        let c = Constraint::Subset {
                            left: Cell::new_local(return_name, function),
                            right: Cell::new_local(dest_name, context.fun_name),
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
