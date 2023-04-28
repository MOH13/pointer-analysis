use std::fmt::{self, Debug, Display, Formatter};
use std::rc::Rc;
use std::str::FromStr;

use hashbrown::HashMap;
use llvm_ir::Module;

use crate::cstr;
use crate::module_visitor::pointer::{
    PointerContext, PointerInstruction, PointerModuleObserver, PointerModuleVisitor,
};
use crate::module_visitor::structs::{StructMap, StructType};
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
            .filter(|(c, _)| matches!(c, Cell::Stack(..) | Cell::Global(..)))
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

impl<'a> FromStr for Cell<'a> {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("stack-") {
            s["stack-".len()..].parse().map(Self::Stack)
        } else if s.starts_with("heap-") {
            s["heap-".len()..].parse().map(Self::Heap)
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
    num_cells_per_malloc: usize,
}

fn get_and_push_cells<'a>(
    base_ident: VarIdent<'a>,
    struct_type: Option<&StructType>,
    ident_to_cell: fn(VarIdent<'a>) -> Cell<'a>,
    cells: &mut Vec<Cell<'a>>,
) -> usize {
    match struct_type {
        Some(StructType { fields, .. }) => {
            let mut num_sub_cells = 0;

            let base_rc = Rc::new(base_ident);

            for (i, field) in fields.iter().enumerate() {
                let offset_ident = VarIdent::Offset {
                    base: base_rc.clone(),
                    offset: i,
                };
                num_sub_cells +=
                    get_and_push_cells(offset_ident, field.st.as_deref(), ident_to_cell, cells);
            }

            num_sub_cells
        }

        None => {
            cells.push(ident_to_cell(base_ident));
            1
        }
    }
}

impl<'a> PointsToPreAnalyzer<'a> {
    fn new() -> Self {
        Self {
            cells: vec![],
            allowed_offsets: vec![],
            summaries: HashMap::new(),
            num_cells_per_malloc: 0,
        }
    }

    fn add_cells(
        &mut self,
        base_ident: VarIdent<'a>,
        struct_type: Option<&StructType>,
        ident_to_cell: fn(VarIdent<'a>) -> Cell<'a>,
    ) -> usize {
        get_and_push_cells(base_ident, struct_type, ident_to_cell, &mut self.cells)
    }

    fn add_cells_and_allowed_offsets(
        &mut self,
        base_ident: VarIdent<'a>,
        struct_type: Option<&StructType>,
        ident_to_cell: fn(VarIdent<'a>) -> Cell<'a>,
    ) {
        let added = self.add_cells(base_ident, struct_type, ident_to_cell);
        for (i, cell) in self.cells.iter().rev().take(added).enumerate() {
            if i > 0 {
                self.allowed_offsets.push((cell.clone(), i));
            }
        }
    }
}

impl<'a> PointerModuleObserver<'a> for PointsToPreAnalyzer<'a> {
    fn init(&mut self, structs: &StructMap) {
        self.num_cells_per_malloc = structs.values().map(|st| st.size).max().unwrap_or(0);
    }

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
        self.add_cells_and_allowed_offsets(ident, struct_type, Cell::Global);
    }

    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        context: PointerContext<'a>,
    ) {
        match instr {
            PointerInstruction::Gep { dest, .. } => {
                self.add_cells_and_allowed_offsets(dest, None, Cell::Var)
            }
            PointerInstruction::Assign {
                dest, struct_type, ..
            }
            | PointerInstruction::Load {
                dest, struct_type, ..
            }
            | PointerInstruction::Phi {
                dest, struct_type, ..
            }
            | PointerInstruction::Call {
                dest: Some(dest),
                return_struct_type: struct_type,
                ..
            } => self.add_cells_and_allowed_offsets(dest, struct_type.as_deref(), Cell::Var),

            PointerInstruction::Alloca { dest, struct_type } => {
                self.cells.push(Cell::Var(dest.clone()));
                self.add_cells_and_allowed_offsets(dest, struct_type.as_deref(), Cell::Stack);
            }

            PointerInstruction::Malloc { dest } => {
                self.cells.push(Cell::Var(dest.clone()));
                let num_cells = self.num_cells_per_malloc;
                let base_rc = Rc::new(dest);
                for i in 0..num_cells {
                    let cell = Cell::Heap(VarIdent::Offset {
                        base: base_rc.clone(),
                        offset: i,
                    });
                    self.cells.push(cell.clone());
                    self.allowed_offsets.push((cell, num_cells - i - 1));
                }
            }

            PointerInstruction::Return { return_reg } => {
                let fun_name = context
                    .fun_name
                    .expect("return instructions should only be generated inside functions");
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

fn first_ident<'a>(base_ident: VarIdent<'a>, struct_type: Option<&StructType>) -> VarIdent<'a> {
    if let Some(st) = struct_type {
        let offset_ident = VarIdent::Offset {
            base: Rc::new(base_ident),
            offset: 0,
        };
        first_ident(offset_ident, st.fields[0].st.as_deref())
    } else {
        base_ident
    }
}

impl<'a, S> PointsToSolver<'a, S>
where
    S: Solver<Term = Cell<'a>>,
{
    fn do_assignment(
        &mut self,
        dest: VarIdent<'a>,
        value: VarIdent<'a>,
        struct_type: Option<&StructType>,
    ) {
        match struct_type {
            Some(_) => {
                let mut value_vec = vec![];
                let mut dest_vec = vec![];
                get_and_push_cells(value, struct_type.as_deref(), Cell::Var, &mut value_vec);
                get_and_push_cells(dest, struct_type.as_deref(), Cell::Var, &mut dest_vec);
                for (value_cell, dest_cell) in value_vec.into_iter().zip(dest_vec) {
                    let c = cstr!(value_cell <= dest_cell);
                    self.solver.add_constraint(c);
                }
            }
            None => {
                let value_cell = Cell::Var(value);
                let dest_cell = Cell::Var(dest);
                let c = cstr!(value_cell <= dest_cell);
                self.solver.add_constraint(c);
            }
        };
    }
}

impl<'a, S> PointerModuleObserver<'a> for PointsToSolver<'a, S>
where
    S: Solver<Term = Cell<'a>>,
{
    fn init(&mut self, _structs: &StructMap) {}

    fn handle_ptr_function(&mut self, _name: &str, _parameters: Vec<VarIdent>) {}

    fn handle_ptr_global(
        &mut self,
        ident: VarIdent<'a>,
        init_ref: Option<VarIdent<'a>>,
        struct_type: Option<&StructType>,
    ) {
        let global_cell = Cell::Global(first_ident(ident.clone(), struct_type.as_deref()));
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
            PointerInstruction::Assign {
                dest,
                value,
                struct_type,
            } => {
                self.do_assignment(dest, value, struct_type.as_deref());
            }

            PointerInstruction::Store {
                address,
                value,
                struct_type,
            } => {
                let address_cell = Cell::Var(address);
                match struct_type {
                    Some(_) => {
                        let mut value_vec = vec![];
                        get_and_push_cells(
                            value,
                            struct_type.as_deref(),
                            Cell::Var,
                            &mut value_vec,
                        );
                        for (offset, value_cell) in value_vec.into_iter().enumerate() {
                            let c = cstr!(c in (address_cell.clone()) + offset : value_cell <= c);
                            self.solver.add_constraint(c);
                        }
                    }
                    None => {
                        let value_cell = Cell::Var(value);
                        let c = cstr!(c in address_cell : value_cell <= c);
                        self.solver.add_constraint(c);
                    }
                };
            }

            PointerInstruction::Load {
                dest,
                address,
                struct_type,
            } => {
                let address_cell = Cell::Var(address);
                match struct_type {
                    Some(_) => {
                        let mut dest_vec = vec![];
                        get_and_push_cells(dest, struct_type.as_deref(), Cell::Var, &mut dest_vec);
                        for (offset, dest_cell) in dest_vec.into_iter().enumerate() {
                            let c = cstr!(c in (address_cell.clone()) + offset : c <= dest_cell);
                            self.solver.add_constraint(c);
                        }
                    }
                    None => {
                        let dest_cell = Cell::Var(dest);
                        let c = cstr!(c in address_cell : c <= dest_cell);
                        self.solver.add_constraint(c);
                    }
                };
            }

            PointerInstruction::Alloca { dest, struct_type } => {
                let stack_cell = Cell::Stack(first_ident(dest.clone(), struct_type.as_deref()));
                let var_cell = Cell::Var(dest);
                let c = cstr!(stack_cell in var_cell);
                self.solver.add_constraint(c);
            }

            PointerInstruction::Malloc { dest } => {
                let heap_cell = Cell::Heap(VarIdent::Offset {
                    base: Rc::new(dest.clone()),
                    offset: 0,
                });
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
                    next_sty = sty.fields[i].st.as_deref();

                    if i == 0 {
                        continue;
                    }

                    for j in 0..i {
                        offset += match &sty.fields[j].st {
                            Some(f) => f.size,
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
                struct_type,
            } => {
                for value in incoming_values {
                    self.do_assignment(dest.clone(), value, struct_type.as_deref());
                }
            }

            PointerInstruction::Call {
                dest,
                function,
                arguments,
                return_struct_type,
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
                    (Some(return_ident), Some(dest_ident)) => self.do_assignment(
                        dest_ident,
                        return_ident.clone(),
                        return_struct_type.as_deref(),
                    ),
                    _ => {}
                }
            }

            _ => {}
        }
    }
}
