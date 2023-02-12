use llvm_ir::instruction::{Load, Store};
use llvm_ir::{Instruction, Module, Name, Operand, Terminator};

use crate::module_visitor::{Context, ModuleVisitor};
use crate::solver::{Constraint, Solver};

pub struct PointsToAnalysis;

impl PointsToAnalysis {
    /// Runs the points-to analysis on LLVM module `module` using `solver`.
    pub fn run<S>(module: &Module, solver: S) -> PointsToResult
    where
        S: Solver<Term = Cell, Node = Cell>,
    {
        let mut cell_finder = PointsToCellFinder::new();
        cell_finder.visit_module(module);

        let mut points_to_solver = PointsToSolver {
            cells: cell_finder.cells,
            solver,
        };
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
    cells: Vec<Cell>,
    solver: S,
}

impl<S> ModuleVisitor for PointsToSolver<S>
where
    S: Solver<Term = Cell, Node = Cell>,
{
    fn handle_instruction(&mut self, instr: &Instruction, _context: Context) {
        match instr {
            Instruction::Load(Load {
                address:
                    Operand::LocalOperand {
                        name: addr_name, ..
                    },
                dest,
                ..
            }) => {
                for cell in &self.cells {
                    // TODO: Get rid of clones
                    let c = Constraint::CondSubset {
                        term: cell.clone(),
                        cond_node: Cell::Local(addr_name.clone()),
                        left: cell.clone(),
                        right: Cell::Local(dest.clone()),
                    };
                    self.solver.add_constraint(c);
                }
            }

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
                for cell in &self.cells {
                    // TODO: Get rid of clones
                    let c = Constraint::CondSubset {
                        term: cell.clone(),
                        cond_node: Cell::Local(addr_name.clone()),
                        left: Cell::Local(value_name.clone()),
                        right: cell.clone(),
                    };
                    self.solver.add_constraint(c);
                }
            }
            _ => {}
        }
    }

    fn handle_terminator(&mut self, term: &Terminator, context: Context) {
        todo!()
    }
}
