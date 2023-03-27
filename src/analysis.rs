use std::fmt::{self, Debug, Display, Formatter};

use hashbrown::HashMap;
use llvm_ir::Module;

use crate::cstr;
use crate::module_visitor::{
    ModuleVisitor, PointerContext, PointerInstruction, PointerModuleVisitor, StructType, VarIdent,
};
use crate::solver::Solver;

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

        let solver = S::new(pre_analyzer.cells, pre_analyzer.allowed_offsets);
        let mut points_to_solver = PointsToSolver {
            solver,
            summaries: pre_analyzer.summaries,
        };
        points_to_solver.visit_module(module);

        let result_map = cells_copy
            .into_iter()
            .filter(|c| matches!(c, Cell::Stack(..) | Cell::Global(..) | Cell::Offset(..)))
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

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Cell<'a> {
    Var(VarIdent<'a>),
    // Since LLVM is in SSA, we can use the name of the allocation register to refer to the allocation site
    Stack(VarIdent<'a>),
    Heap(VarIdent<'a>),
    Global(VarIdent<'a>),
    Offset(Box<Cell<'a>>, usize),
}

impl<'a> Display for Cell<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Var(ident) => write!(f, "{ident}"),
            Self::Stack(ident) => write!(f, "stack-{ident}"),
            Self::Heap(ident) => write!(f, "heap-{ident}"),
            Self::Global(ident) => write!(f, "global-{ident}"),
            Self::Offset(sub_cell, offset) => write!(f, "{sub_cell}.{offset}"),
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
    allowed_offsets: Vec<(Cell<'a>, usize)>,
    summaries: HashMap<&'a str, FunctionSummary<'a>>,
}

impl<'a> PointsToPreAnalyzer<'a> {
    fn new() -> Self {
        Self {
            cells: vec![],
            allowed_offsets: vec![],
            summaries: HashMap::new(),
        }
    }

    fn add_stack_cells(
        &mut self,
        stack_cell: Cell<'a>,
        struct_type: Option<&StructType>,
        context: PointerContext<'a, '_>,
    ) -> usize {
        match struct_type {
            Some(StructType { fields }) => {
                let mut num_sub_cells = 0;

                for (i, field) in fields.iter().enumerate() {
                    let offset_cell = Cell::Offset(Box::new(stack_cell.clone()), i);
                    num_sub_cells +=
                        self.add_stack_cells(offset_cell, field.as_ref().map(|(s, _)| s), context);
                }

                num_sub_cells
            }

            None => {
                self.cells.push(stack_cell);
                1
            }
        }
    }

    fn add_stack_cells_and_allowed_offsets(
        &mut self,
        ident: VarIdent<'a>,
        struct_type: Option<&StructType>,
        context: PointerContext<'a, '_>,
    ) {
        let added = self.add_stack_cells(Cell::Stack(ident), struct_type, context);
        for (i, cell) in self.cells.iter().rev().take(added).enumerate() {
            self.allowed_offsets.push((cell.clone(), i));
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
            | PointerInstruction::Gep { dest, .. }
            | PointerInstruction::Phi { dest, .. }
            | PointerInstruction::Call {
                dest: Some(dest), ..
            } => self.cells.push(Cell::Var(dest)),

            PointerInstruction::Alloca { dest, struct_type } => {
                self.cells.push(Cell::Var(dest));
                self.add_stack_cells_and_allowed_offsets(dest, struct_type.as_ref(), context);
            }

            PointerInstruction::Malloc { dest } => {
                self.cells.push(Cell::Var(dest));
                self.cells.push(Cell::Heap(dest));
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
            let global_cell = Cell::Global(ident);
            let init_global_cell = Cell::Global(init_ident);
            let c = cstr!(init_global_cell in global_cell);
            self.solver.add_constraint(c);
        }
    }

    fn handle_ptr_instruction(&mut self, instr: PointerInstruction<'a>, context: PointerContext) {
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
                let stack_cell = match struct_type {
                    Some(_) => Cell::Offset(Box::new(Cell::Stack(dest)), 0),
                    None => Cell::Stack(dest),
                };
                let var_cell = Cell::Var(dest);
                let c = cstr!(stack_cell in var_cell);
                self.solver.add_constraint(c);
            }

            PointerInstruction::Malloc { dest } => {
                let heap_cell = Cell::Heap(dest);
                let var_cell = Cell::Var(dest);
                let c = cstr!(heap_cell in var_cell);
                self.solver.add_constraint(c);
            }

            PointerInstruction::Gep {
                dest,
                address,
                indices,
                struct_type,
            } => {
                let mut offset = 0;
                let mut next_sty = Some(&struct_type);
                for i in indices {
                    let sty = next_sty.expect("Gep indices should correspond to struct fields");
                    next_sty = sty.fields[i].as_ref().map(|(s, _)| s);

                    if i == 0 {
                        continue;
                    }

                    for j in 0..i {
                        offset += match &sty.fields[j] {
                            Some((s, _)) => count_struct_cells(s, context),
                            None => 1,
                        }
                    }
                }

                let dest_cell = Cell::Var(dest);
                let address_cell = Cell::Var(address);
                let c = cstr!(address_cell + offset <= dest_cell);
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
                let summary = match self.summaries.get(function) {
                    Some(s) => s,
                    None => return, // TODO: Handle outside function calls
                };
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

fn count_struct_cells(struct_type: &StructType, context: PointerContext) -> usize {
    let mut num_sub_cells = 0;

    for field in &struct_type.fields {
        num_sub_cells += match field {
            Some((s, _)) => count_struct_cells(s, context),
            None => 1,
        };
    }

    num_sub_cells
}
