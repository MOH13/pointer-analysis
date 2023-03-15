use std::fmt::{self, Debug, Display, Formatter};

use hashbrown::HashMap;
use llvm_ir::Module;

use crate::cstr;
use crate::module_visitor::{
    ModuleVisitor, PointerContext, PointerInstruction, PointerModuleVisitor, StructType, VarIdent,
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

        let solver = S::new(pre_analyzer.cells, vec![]);
        let mut points_to_solver = PointsToSolver {
            solver,
            summaries: pre_analyzer.summaries,
        };
        points_to_solver.visit_module(module);

        let result_map = cells_copy
            .into_iter()
            .filter(|c| matches!(c, Cell::Stack(..) | Cell::Global(..)))
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

    fn add_stack_cells(&mut self, dest: VarIdent<'a>, struct_type: Option<StructType<'a>>) {
        match struct_type {
            Some(StructType { fields }) => todo!(),
            None => self.cells.push(Cell::Stack(dest)),
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

    fn handle_ptr_global(&mut self, ident: VarIdent<'a>, _init_ref: Option<VarIdent<'a>>) {
        self.cells.push(Cell::Var(ident));
        self.cells.push(Cell::Global(ident));
    }

    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        context: PointerContext<'a, '_>,
    ) {
        match instr {
            PointerInstruction::Assign { dest, .. }
            | PointerInstruction::Load { dest, .. }
            | PointerInstruction::Phi { dest, .. }
            | PointerInstruction::Call {
                dest: Some(dest), ..
            } => self.cells.push(Cell::Var(dest)),

            PointerInstruction::Alloca { dest, struct_type } => {
                self.cells.push(Cell::Var(dest));
                self.add_stack_cells(dest, struct_type);
            }

            PointerInstruction::Return { return_reg } => {
                self.summaries.entry_ref(context.fun_name).and_modify(|s| {
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

    fn handle_ptr_global(&mut self, ident: VarIdent<'a>, init_ref: Option<VarIdent<'a>>) {
        let global_cell = Cell::Global(ident);
        let var_cell = Cell::Var(ident);
        let c = cstr!(global_cell in var_cell);
        self.solver.add_constraint(c);

        if let Some(init_ident) = init_ref {
            let init_global_cell = Cell::Global(init_ident);
            let c = cstr!(init_global_cell in global_cell);
            self.solver.add_constraint(c);
        }
    }

    fn handle_ptr_instruction(&mut self, instr: PointerInstruction<'a>, _context: PointerContext) {
        match instr {
            PointerInstruction::Assign { dest, value } => {
                let value_cell = Cell::Var(value);
                let dest_cell = Cell::Var(dest);
                let c = cstr!(value_cell <= dest_cell);
                self.solver.add_constraint(c);
            }

            PointerInstruction::Store { address, value } => {
                let address_cell = Cell::Var(address);
                let value_cell = Cell::Var(value);
                let c = cstr!(c in address_cell : value_cell <= c);
                self.solver.add_constraint(c);
            }

            PointerInstruction::Load { dest, address } => {
                let address_cell = Cell::Var(address);
                let dest_cell = Cell::Var(dest);
                let c = cstr!(c in address_cell : c <= dest_cell);
                self.solver.add_constraint(c);
            }

            PointerInstruction::Alloca { dest, struct_type } => {
                let stack_cell = Cell::Stack(dest);
                let var_cell = Cell::Var(dest);
                let c = cstr!(stack_cell in var_cell);
                self.solver.add_constraint(c);
            }

            PointerInstruction::Phi {
                dest,
                incoming_values,
            } => {
                for value in incoming_values {
                    let value_cell = Cell::Var(value);
                    let dest_cell = Cell::Var(dest);
                    let c = cstr!(value_cell <= dest_cell);
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
                    let arg_cell = Cell::Var(arg);
                    let param_cell = Cell::Var(param);
                    let c = cstr!(arg_cell <= param_cell);
                    self.solver.add_constraint(c);
                }

                match (summary.return_reg, dest) {
                    (Some(return_name), Some(dest_name)) => {
                        let return_cell = Cell::Var(return_name);
                        let dest_cell = Cell::Var(dest_name);
                        let c = cstr!(return_cell <= dest_cell);
                        self.solver.add_constraint(c);
                    }
                    _ => {}
                }
            }

            _ => {}
        }
    }
}
