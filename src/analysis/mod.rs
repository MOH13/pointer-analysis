use std::fmt::{self, Debug, Display, Formatter};
use std::str::FromStr;

use hashbrown::HashMap;
use llvm_ir::Module;

use crate::cstr;
use crate::module_visitor::pointer::{
    PointerContext, PointerInstruction, PointerModuleObserver, PointerModuleVisitor,
};
use crate::module_visitor::structs::{count_flattened_fields, StructType};
use crate::module_visitor::{ModuleVisitor, VarIdent};
use crate::solver::Solver;

#[cfg(test)]
mod tests;

pub struct PointsToAnalysis;

impl PointsToAnalysis {
    /// Runs the points-to analysis on LLVM module `module` using `solver`.
    pub fn run<'a, S>(module: &'a Module) -> PointsToResult<S>
    where
        S: Solver<Term = Cell<'a>> + 'a,
    {
        let mut pre_analyzer = PointsToPreAnalyzer::new();
        PointerModuleVisitor::new(&mut pre_analyzer).visit_module(module);
        let cells_copy = pre_analyzer.cells.clone();

        let mut points_to_solver = PointsToSolver {
            solver: S::new(pre_analyzer.cells, pre_analyzer.allowed_offsets),
            summaries: pre_analyzer.summaries,
        };
        PointerModuleVisitor::new(&mut points_to_solver).visit_module(module);

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

#[derive(Debug)]
pub struct PointsToResult<'a, S: Solver>(HashMap<Cell<'a>, S::TermSet>);

impl<'a, S> Display for PointsToResult<'a, S>
where
    S: Solver,
    S::TermSet: fmt::Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for (cell, set) in self
            .0
            .iter()
            .filter(|(c, _)| matches!(c, Cell::Stack(..) | Cell::Global(..) | Cell::Offset(..)))
        {
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

fn parse_offset<'a>(s: &str) -> Option<Result<Cell<'a>, String>> {
    if let Some((l, r)) = s.rsplit_once('.') {
        match r.parse() {
            Ok(offset) => Some(
                l.parse()
                    .map(|sub_cell| Cell::Offset(Box::new(sub_cell), offset)),
            ),
            Err(_) => None,
        }
    } else {
        None
    }
}

impl<'a> FromStr for Cell<'a> {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(offset_cell_result) = parse_offset(s) {
            offset_cell_result
        } else if s.starts_with("stack-") {
            s["stack-".len()..].parse().map(Self::Stack)
        } else if s.starts_with("heap-") {
            s["heap-".len()..].parse().map(Self::Stack)
        } else if s.starts_with("global-") {
            s["global-".len()..].parse().map(Self::Global)
        } else {
            s.parse().map(Self::Var)
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

    fn add_struct_cells(&mut self, base_cell: Cell<'a>, struct_type: Option<&StructType>) -> usize {
        match struct_type {
            Some(StructType { fields }) => {
                let mut num_sub_cells = 0;

                for (i, field) in fields.iter().enumerate() {
                    let offset_cell = Cell::Offset(Box::new(base_cell.clone()), i);
                    num_sub_cells += self.add_struct_cells(offset_cell, field.as_deref());
                }

                num_sub_cells
            }

            None => {
                self.cells.push(base_cell);
                1
            }
        }
    }

    fn add_struct_cells_and_allowed_offsets(
        &mut self,
        base_cell: Cell<'a>,
        struct_type: Option<&StructType>,
    ) {
        let added = self.add_struct_cells(base_cell, struct_type);
        for (i, cell) in self.cells.iter().rev().take(added).enumerate() {
            self.allowed_offsets.push((cell.clone(), i));
        }
    }
}

impl<'a> PointerModuleObserver<'a> for PointsToPreAnalyzer<'a> {
    fn handle_ptr_function(&mut self, name: &'a str, parameters: Vec<VarIdent<'a>>) {
        for param in &parameters {
            self.cells.push(Cell::Var(param.clone()));
        }

        let summary = FunctionSummary {
            parameters,
            return_reg: None,
        };
        self.summaries.insert(name, summary);
    }

    fn handle_ptr_global(
        &mut self,
        ident: VarIdent<'a>,
        _init_ref: Option<VarIdent<'a>>,
        struct_type: Option<&StructType>,
    ) {
        self.cells.push(Cell::Var(ident.clone()));
        self.add_struct_cells_and_allowed_offsets(Cell::Global(ident), struct_type);
    }

    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        context: PointerContext<'a>,
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
                self.cells.push(Cell::Var(dest.clone()));
                self.add_struct_cells_and_allowed_offsets(
                    Cell::Stack(dest),
                    struct_type.as_deref(),
                );
            }

            PointerInstruction::Malloc { dest } => {
                self.cells.push(Cell::Var(dest.clone()));
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

impl<'a, S> PointerModuleObserver<'a> for PointsToSolver<'a, S>
where
    S: Solver<Term = Cell<'a>>,
{
    fn handle_ptr_function(&mut self, _name: &str, _parameters: Vec<VarIdent>) {}

    fn handle_ptr_global(
        &mut self,
        ident: VarIdent<'a>,
        init_ref: Option<VarIdent<'a>>,
        _struct_type: Option<&StructType>,
    ) {
        let global_cell = Cell::Global(ident.clone());
        let var_cell = Cell::Var(ident.clone());
        let c = cstr!(global_cell in var_cell);
        self.solver.add_constraint(c);

        if let Some(init_ident) = init_ref {
            let global_cell = Cell::Global(ident);
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
                let mut stack_cell = Cell::Stack(dest.clone());
                let mut struct_type = struct_type.as_deref();
                while let Some(st) = struct_type {
                    stack_cell = Cell::Offset(Box::new(stack_cell), 0);
                    struct_type = st.fields[0].as_deref();
                }

                let var_cell = Cell::Var(dest);
                let c = cstr!(stack_cell in var_cell);
                self.solver.add_constraint(c);
            }

            PointerInstruction::Malloc { dest } => {
                let heap_cell = Cell::Heap(dest.clone());
                let var_cell = Cell::Var(dest);
                let c = cstr!(heap_cell in var_cell);
                self.solver.add_constraint(c);
            }

            // Flat gep
            PointerInstruction::Gep {
                dest,
                address,
                indices,
                struct_type: None,
            } => {
                let dest_cell = Cell::Var(dest);
                let address_cell = Cell::Var(address);

                if indices.len() != 1 {
                    panic!("Got flat gep with more than one index");
                }
                let offset = indices[0];
                let c = cstr!(address_cell + offset <= dest_cell);
                self.solver.add_constraint(c);
            }

            PointerInstruction::Gep {
                dest,
                address,
                indices,
                struct_type: Some(struct_type),
            } => {
                let mut offset = 0;
                let mut next_sty = Some(&*struct_type);
                for i in indices {
                    let sty = next_sty.expect("Gep indices should correspond to struct fields");
                    next_sty = sty.fields[i].as_deref();

                    if i == 0 {
                        continue;
                    }

                    for j in 0..i {
                        offset += match &sty.fields[j] {
                            Some(f) => count_flattened_fields(f),
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
                    let dest_cell = Cell::Var(dest.clone());
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
                for (arg, param) in arguments
                    .iter()
                    .zip(&summary.parameters)
                    .filter_map(|(a, p)| a.as_ref().map(|a| (a, p)))
                {
                    let arg_cell = Cell::Var(arg.clone());
                    let param_cell = Cell::Var(param.clone());
                    let c = cstr!(arg_cell <= param_cell);
                    self.solver.add_constraint(c);
                }

                match (&summary.return_reg, dest) {
                    (Some(return_name), Some(dest_name)) => {
                        let return_cell = Cell::Var(return_name.clone());
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
