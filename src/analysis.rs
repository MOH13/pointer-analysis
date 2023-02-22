use std::fmt::{self, Debug, Display, Formatter};

use hashbrown::HashMap;
use llvm_ir::instruction::{AddrSpaceCast, Alloca, BitCast, Load, Phi, Store};
use llvm_ir::terminator::Ret;
use llvm_ir::types::Type;
use llvm_ir::{Function, Instruction, Module, Name, Operand, Terminator};

use crate::module_visitor::{Context, ModuleVisitor};
use crate::solver::{Constraint, Solver};

pub struct PointsToAnalysis;

impl PointsToAnalysis {
    /// Runs the points-to analysis on LLVM module `module` using `solver`.
    pub fn run<S>(module: &Module) -> PointsToResult<S>
    where
        S: Solver<Term = Cell>,
    {
        let mut cell_finder = PointsToPreAnalyzer::new();
        cell_finder.visit_module(module);
        let cells_copy = cell_finder.cells.clone();

        let solver = S::new(cell_finder.cells);
        let mut points_to_solver = PointsToSolver {
            solver,
            summaries: cell_finder.summaries,
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

pub struct PointsToResult<S: Solver>(HashMap<Cell, S::TermSet>);

impl<S> Display for PointsToResult<S>
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

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Cell {
    Local { reg_name: Name, fun_name: String },
    // Since LLVM is in SSA, we can use the name of the allocation register to refer to the allocation site
    Stack { reg_name: Name, fun_name: String },
    Heap { reg_name: Name, fun_name: String },
}

impl Debug for Cell {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Local { reg_name, fun_name } => write!(f, "{reg_name}@{fun_name}"),
            Self::Stack { reg_name, fun_name } => write!(f, "stack-{reg_name}@{fun_name}"),
            Self::Heap { reg_name, fun_name } => write!(f, "heap-{reg_name}@{fun_name}"),
        }
    }
}

impl Cell {
    fn new_local(reg_name: &Name, Context { function, .. }: Context) -> Self {
        Cell::Local {
            reg_name: reg_name.clone(),
            fun_name: function.name.clone(),
        }
    }

    fn new_stack(reg_name: &Name, Context { function, .. }: Context) -> Self {
        Cell::Stack {
            reg_name: reg_name.clone(),
            fun_name: function.name.clone(),
        }
    }

    fn new_heap(reg_name: &Name, Context { function, .. }: Context) -> Self {
        Cell::Heap {
            reg_name: reg_name.clone(),
            fun_name: function.name.clone(),
        }
    }
}

struct FunctionSummary {
    params: Vec<Name>,
    return_reg: Option<Name>,
}

/// Visits a module and finds all cells in that module.
/// An allocation site abstraction is used for heap allocations.
/// TODO: Field sensitivity?
struct PointsToPreAnalyzer {
    cells: Vec<Cell>,
    summaries: HashMap<String, FunctionSummary>,
}

impl PointsToPreAnalyzer {
    fn new() -> Self {
        Self {
            cells: vec![],
            summaries: HashMap::new(),
        }
    }

    fn add_local(&mut self, reg_name: &Name, context: Context) {
        self.cells.push(Cell::new_local(reg_name, context));
    }

    fn add_stack(&mut self, reg_name: &Name, context: Context) {
        self.cells.push(Cell::new_stack(reg_name, context));
    }

    fn add_heap(&mut self, reg_name: &Name, context: Context) {
        self.cells.push(Cell::new_heap(reg_name, context));
    }
}

impl ModuleVisitor for PointsToPreAnalyzer {
    fn handle_function(&mut self, function: &Function, _module: &Module) {
        let mut params = Vec::with_capacity(function.parameters.len());
        for param in &function.parameters {
            params.push(param.name.clone());
            self.cells.push(Cell::Local {
                reg_name: param.name.clone(),
                fun_name: function.name.clone(),
            });
        }
        let summary = FunctionSummary {
            params,
            return_reg: None,
        };
        self.summaries.insert(function.name.clone(), summary);
    }

    fn handle_instruction(&mut self, instr: &Instruction, context: Context) {
        match instr {
            // Instruction::ExtractElement(_) => todo!(),
            // Instruction::ExtractValue(_) => todo!(),
            Instruction::Alloca(Alloca { dest, .. }) => {
                self.add_local(dest, context);
                self.add_stack(dest, context);
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

                self.add_local(dest, context);
            }

            // Instruction::GetElementPtr(_) => todo!(),
            // Instruction::IntToPtr(_) => todo!(),
            Instruction::BitCast(BitCast { to_type, dest, .. })
            | Instruction::AddrSpaceCast(AddrSpaceCast { to_type, dest, .. })
            | Instruction::Phi(Phi { to_type, dest, .. }) => {
                if !matches!(to_type.as_ref(), Type::PointerType { .. }) {
                    return;
                }
                self.add_local(dest, context);
            }

            // Instruction::Select(_) => todo!(),
            // Instruction::Freeze(_) => todo!(),
            // Instruction::Call(_) => todo!(),
            // Instruction::VAArg(_) => todo!(),
            _ => {}
        }
    }

    fn handle_terminator(&mut self, term: &Terminator, Context { function, .. }: Context) {
        if let Terminator::Ret(Ret {
            return_operand:
                Some(Operand::LocalOperand {
                    name: ret_name,
                    ty: ret_ty,
                }),
            ..
        }) = term
        {
            if !matches!(ret_ty.as_ref(), Type::PointerType { .. }) {
                return;
            }

            self.summaries.entry_ref(&function.name).and_modify(|s| {
                s.return_reg = Some(ret_name.clone());
            });
        }
    }
}

/// Visits a module, generating and solving constraints using a supplied constraint solver.
struct PointsToSolver<S> {
    solver: S,
    summaries: HashMap<String, FunctionSummary>,
}

impl<S> ModuleVisitor for PointsToSolver<S>
where
    S: Solver<Term = Cell>,
{
    fn handle_function(&mut self, _function: &Function, _module: &Module) {}

    fn handle_instruction(&mut self, instr: &Instruction, context: Context) {
        match instr {
            // x = alloca ..
            Instruction::Alloca(Alloca { dest, .. }) => {
                let c = Constraint::Inclusion {
                    term: Cell::new_stack(dest, context),
                    node: Cell::new_local(dest, context),
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
                    left: Cell::new_local(value_name, context),
                    right: Cell::new_local(dest, context),
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
                        left: Cell::new_local(value_name, context),
                        right: Cell::new_local(dest, context),
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
                    cond_node: Cell::new_local(addr_name, context),
                    right: Cell::new_local(dest, context),
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
                    cond_node: Cell::new_local(addr_name, context),
                    left: Cell::new_local(value_name, context),
                };
                self.solver.add_constraint(c);
            }

            _ => {}
        }
    }

    fn handle_terminator(&mut self, _term: &Terminator, _context: Context) {}
}
