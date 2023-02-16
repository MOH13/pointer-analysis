use std::fmt::{self, Display, Formatter};

use hashbrown::HashMap;
use llvm_ir::instruction::{AddrSpaceCast, Alloca, BitCast, Load, Phi, Store};
use llvm_ir::types::Type;
use llvm_ir::{Instruction, Module, Name, Operand, Terminator};

use crate::module_visitor::{Context, ModuleVisitor};
use crate::solver::{Constraint, Solver};

pub struct PointsToAnalysis;

impl PointsToAnalysis {
    /// Runs the points-to analysis on LLVM module `module` using `solver`.
    pub fn run<S>(module: &Module) -> PointsToResult<S>
    where
        S: Solver<Term = Cell>,
    {
        let mut cell_finder = PointsToCellFinder::new();
        cell_finder.visit_module(module);
        let cells_copy = cell_finder.cells.clone();

        let solver = S::new(cell_finder.cells);
        let mut points_to_solver = PointsToSolver { solver };
        points_to_solver.visit_module(module);

        let result_map = cells_copy
            .into_iter()
            .map(|c| {
                let sol = points_to_solver.solver.get_solution(&c);
                (c, sol)
            })
            .collect();
        PointsToResult(result_map)
    }
}

pub struct PointsToResult<S: Solver>(HashMap<Cell, S::TermSet>);

impl<S> Display for PointsToResult<S>
where
    S: Solver,
    S::TermSet: fmt::Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum Cell {
    Local(Name),
    // Since LLVM is in SSA, we can use the name of the allocation variable to refer to the allocation site
    Stack(Name),
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
    fn handle_instruction(&mut self, instr: &Instruction, _context: Context) {
        match instr {
            // Instruction::ExtractElement(_) => todo!(),
            // Instruction::ExtractValue(_) => todo!(),
            Instruction::Alloca(Alloca { dest, .. }) => {
                self.cells.push(Cell::Local(dest.clone()));
                self.cells.push(Cell::Stack(dest.clone()));
            }

            Instruction::Load(Load {
                address: Operand::LocalOperand { ty, .. },
                dest,
                ..
            }) => {
                let pointee_type = match ty.as_ref() {
                    Type::PointerType { pointee_type, .. } => pointee_type,
                    _ => return,
                };
                if !matches!(pointee_type.as_ref(), Type::PointerType { .. }) {
                    return;
                }

                self.cells.push(Cell::Local(dest.clone()));
            }

            // Instruction::GetElementPtr(_) => todo!(),
            // Instruction::IntToPtr(_) => todo!(),
            Instruction::BitCast(BitCast { to_type, dest, .. })
            | Instruction::AddrSpaceCast(AddrSpaceCast { to_type, dest, .. })
            | Instruction::Phi(Phi { to_type, dest, .. }) => {
                if !matches!(to_type.as_ref(), Type::PointerType { .. }) {
                    return;
                }
                self.cells.push(Cell::Local(dest.clone()));
            }

            // Instruction::Select(_) => todo!(),
            // Instruction::Freeze(_) => todo!(),
            // Instruction::Call(_) => todo!(),
            // Instruction::VAArg(_) => todo!(),
            _ => {}
        }
    }

    fn handle_terminator(&mut self, _term: &Terminator, _context: Context) {}
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
            // x = alloca ..
            Instruction::Alloca(Alloca { dest, .. }) => {
                let c = Constraint::Inclusion {
                    term: Cell::Stack(dest.clone()),
                    node: Cell::Local(dest.clone()),
                };
                self.solver.add_constraint(c);
            }

            // x = bitcast y to T*
            Instruction::BitCast(BitCast {
                operand:
                    Operand::LocalOperand {
                        name: value_name, ..
                    },
                to_type,
                dest,
                ..
            })
            | Instruction::AddrSpaceCast(AddrSpaceCast {
                operand:
                    Operand::LocalOperand {
                        name: value_name, ..
                    },
                to_type,
                dest,
                ..
            }) => {
                if !matches!(to_type.as_ref(), Type::PointerType { .. }) {
                    return;
                }
                let c = Constraint::Subset {
                    left: Cell::Local(value_name.clone()),
                    right: Cell::Local(dest.clone()),
                };
                self.solver.add_constraint(c);
            }

            // x = \phi(y1, y2, ..)
            Instruction::Phi(Phi {
                incoming_values,
                dest,
                to_type,
                ..
            }) => {
                if !matches!(to_type.as_ref(), Type::PointerType { .. }) {
                    return;
                }
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
                        name: addr_name,
                        ty,
                    },
                dest,
                ..
            }) => {
                let pointee_type = match ty.as_ref() {
                    Type::PointerType { pointee_type, .. } => pointee_type,
                    _ => return,
                };
                if !matches!(pointee_type.as_ref(), Type::PointerType { .. }) {
                    return;
                }

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
                        name: value_name,
                        ty,
                    },
                ..
            }) => {
                if !matches!(ty.as_ref(), Type::PointerType { .. }) {
                    return;
                }
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
