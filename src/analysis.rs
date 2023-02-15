use llvm_ir::instruction::{GetElementPtr, Load, Phi, Store};
use llvm_ir::{Constant, ConstantRef, Instruction, Module, Name, Operand, Terminator};

use crate::module_visitor::{Context, ModuleVisitor};
use crate::solver::{Constraint, Solver};

pub struct PointsToAnalysis;

impl PointsToAnalysis {
    /// Runs the points-to analysis on LLVM module `module` using `solver`.
    pub fn run<S>(module: &Module) -> PointsToResult
    where
        S: Solver<Term = Cell>,
    {
        let mut cell_finder = PointsToCellFinder::new();
        cell_finder.visit_module(module);

        let solver = S::new(cell_finder.cells);
        let mut points_to_solver = PointsToSolver { solver };
        points_to_solver.visit_module(module);

        // TODO: add method to `PointsToSolver` that outputs result
        PointsToResult
    }
}

pub struct PointsToResult;

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Cell {
    Local(Name),
    // Since LLVM is in SSA, we can use the name of the allocation variable to refer to the allocation site
    Heap(Name),
}

/// Visits a module and finds all cells in that module.
/// An allocation site abstraction is used for heap allocations.
/// TODO: Field sensitivity?
struct PointsToCellFinder {
    cells: Vec<Cell>,
}

impl PointsToCellFinder {
    fn new() -> Self {
        Self { cells: vec![] }
    }
}

impl ModuleVisitor for PointsToCellFinder {
    fn handle_instruction(&mut self, instr: &Instruction, context: Context) {
        todo!()
    }

    fn handle_terminator(&mut self, term: &Terminator, context: Context) {
        todo!()
    }
}

/// Visits a module, generating and solving constraints using a supplied constraint solver.
struct PointsToSolver<S> {
    solver: S,
}

impl<S> ModuleVisitor for PointsToSolver<S>
where
    S: Solver<Term = Cell>,
{
    fn handle_instruction(&mut self, instr: &Instruction, _context: Context) {
        match instr {
            // x = &y
            Instruction::GetElementPtr(GetElementPtr {
                address:
                    Operand::LocalOperand {
                        name: addr_name, ..
                    },
                indices,
                dest,
                ..
            }) => {
                if indices.len() != 1
                    || !matches!(
                        indices[0].as_constant(),
                        Some(Constant::Int { value: 0, .. })
                    )
                {
                    return;
                }

                let c = Constraint::Inclusion {
                    term: Cell::Local(addr_name.clone()),
                    node: Cell::Local(dest.clone()),
                };
                self.solver.add_constraint(c);
            }

            // x = \phi(y1, y2, ...)
            Instruction::Phi(Phi {
                incoming_values,
                dest,
                ..
            }) => {
                for (value, _) in incoming_values {
                    let value_name = match value {
                        Operand::LocalOperand { name, .. } => name,
                        _ => continue,
                    };

                    let c = Constraint::Subset {
                        left: Cell::Local(value_name.clone()),
                        right: Cell::Local(dest.clone()),
                    };
                    self.solver.add_constraint(c);
                }
            }

            // x = *y
            Instruction::Load(Load {
                address:
                    Operand::LocalOperand {
                        name: addr_name, ..
                    },
                dest,
                ..
            }) => {
                // TODO: Get rid of clones
                let c = Constraint::UnivCondSubsetLeft {
                    cond_node: Cell::Local(addr_name.clone()),
                    right: Cell::Local(dest.clone()),
                };
                self.solver.add_constraint(c);
            }

            // *x = y
            Instruction::Store(Store {
                address:
                    Operand::LocalOperand {
                        name: addr_name, ..
                    },
                value:
                    Operand::LocalOperand {
                        name: value_name, ..
                    },
                ..
            }) => {
                let c = Constraint::UnivCondSubsetRight {
                    cond_node: Cell::Local(addr_name.clone()),
                    left: Cell::Local(value_name.clone()),
                };
                self.solver.add_constraint(c);
            }

            _ => {}
        }
    }

    fn handle_terminator(&mut self, _term: &Terminator, _context: Context) {}
}
