use std::borrow::Cow;
use std::fmt::{self, Debug, Display, Formatter};
use std::rc::Rc;
use std::str::FromStr;

use hashbrown::HashMap;
use llvm_ir::{Module, Name};
use log::error;

use crate::cstr;
use crate::module_visitor::pointer::{
    PointerContext, PointerInstruction, PointerModuleObserver, PointerModuleVisitor,
};
use crate::module_visitor::structs::{StructMap, StructType};
use crate::module_visitor::{ModuleVisitor, VarIdent};
use crate::solver::Solver;
use crate::visualizer::{visualize, Graph};

#[cfg(test)]
mod tests;

pub struct PointsToAnalysis;

impl PointsToAnalysis {
    fn solve_module<'a, S>(module: &'a Module) -> (S, Vec<Cell<'a>>)
    where
        S: Solver<Term = Cell<'a>> + 'a,
    {
        let mut pre_analyzer = PointsToPreAnalyzer::new();
        PointerModuleVisitor::new(&mut pre_analyzer).visit_module(module);
        let cells_copy = pre_analyzer.cells.clone();

        let mut points_to_solver =
            PointsToSolver::<'a, S>::new(pre_analyzer.cells, pre_analyzer.allowed_offsets);
        PointerModuleVisitor::new(&mut points_to_solver).visit_module(module);
        points_to_solver.solver.finalize();

        (points_to_solver.solver, cells_copy)
    }

    /// Runs the points-to analysis on LLVM module `module` using `solver`.
    pub fn run<'a, S>(module: &'a Module) -> PointsToResult<S>
    where
        S: Solver<Term = Cell<'a>> + 'a,
    {
        let (solver, cells) = Self::solve_module::<S>(module);

        PointsToResult(solver, cells)
    }

    pub fn run_and_visualize<'a, S>(
        module: &'a Module,
        dot_output_path: &str,
    ) -> PointsToResult<'a, S>
    where
        S: Solver<Term = Cell<'a>> + Graph + 'a,
    {
        let (solver, cells) = Self::solve_module::<S>(module);
        if let Err(e) = visualize(&solver, dot_output_path) {
            error!("Error visualizing graph: {e}");
        }
        PointsToResult(solver, cells)
    }
}

#[derive(Debug, Clone)]
pub struct PointsToResult<'a, S: Solver>(pub S, pub Vec<Cell<'a>>);

pub struct FilteredResults<'a, 'b, S: Solver, F1, F2> {
    result: &'b PointsToResult<'a, S>,
    key_filter: F1,
    value_filter: F2,
    include_strs: Vec<&'b str>,
    exclude_strs: Vec<&'b str>,
}

impl<'a, S: Solver> PointsToResult<'a, S> {
    pub fn get_filtered_entries<
        'b,
        F1: Fn(&Cell<'a>, &S::TermSet) -> bool,
        F2: Fn(&Cell<'a>) -> bool,
    >(
        &'b self,
        key_filter: F1,
        value_filter: F2,
        include_strs: Vec<&'b str>,
        exclude_strs: Vec<&'b str>,
    ) -> FilteredResults<'a, 'b, S, F1, F2> {
        FilteredResults {
            result: self,
            key_filter,
            value_filter,
            include_strs,
            exclude_strs,
        }
    }

    pub fn get_all_entries<'b>(
        &'b self,
    ) -> FilteredResults<'a, 'b, S, fn(&Cell<'a>, &S::TermSet) -> bool, fn(&Cell<'a>) -> bool> {
        FilteredResults {
            result: self,
            key_filter: |_, _| true,
            value_filter: |_| true,
            include_strs: Vec::new(),
            exclude_strs: Vec::new(),
        }
    }
}

impl<
        'a,
        'b,
        S: Solver<Term = Cell<'a>>,
        F1: Fn(&Cell<'a>, &S::TermSet) -> bool,
        F2: Fn(&Cell<'a>) -> bool,
    > FilteredResults<'a, 'b, S, F1, F2>
where
    S::TermSet: IntoIterator<Item = Cell<'a>>,
    S::TermSet: FromIterator<Cell<'a>>,
    S::TermSet: Clone,
{
    pub fn iter_solutions(&'b self) -> impl Iterator<Item = (Cell<'a>, S::TermSet)> + 'b {
        self.result
            .1
            .iter()
            .map(|cell| (cell.clone(), self.result.0.get_solution(cell)))
            .map(|(cell, set)| (cell, set.into_iter().filter(&self.value_filter).collect()))
            .filter(|(cell, set)| {
                let cell_str = cell.to_string();
                (self.key_filter)(cell, set)
                    && (self.include_strs.is_empty()
                        || self.include_strs.iter().any(|s| cell_str.contains(s)))
                    && (self.exclude_strs.iter().all(|s| !cell_str.contains(s)))
            })
    }
}

impl<'a, S: Solver<Term = Cell<'a>>> Display for PointsToResult<'a, S>
where
    S::TermSet: fmt::Debug,
    S::TermSet: IntoIterator<Item = Cell<'a>>,
    S::TermSet: FromIterator<Cell<'a>>,
    S::TermSet: Clone,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let filtered = self.get_all_entries();
        writeln!(f, "{filtered}")?;
        Ok(())
    }
}

impl<
        'a,
        'b,
        S: Solver<Term = Cell<'a>>,
        F1: Fn(&Cell<'a>, &S::TermSet) -> bool,
        F2: Fn(&Cell<'a>) -> bool,
    > Display for FilteredResults<'a, 'b, S, F1, F2>
where
    S::TermSet: fmt::Debug,
    S::TermSet: IntoIterator<Item = Cell<'a>>,
    S::TermSet: FromIterator<Cell<'a>>,
    S::TermSet: Clone,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for (cell, set) in self.iter_solutions() {
            writeln!(f, "[[{cell}]] = {set:#?}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Cell<'a> {
    Var(VarIdent<'a>),
    Return(VarIdent<'a>),
    // Since LLVM is in SSA, we can use the name of the
    // allocation register to refer to the allocation site
    Stack(VarIdent<'a>),
    Heap(VarIdent<'a>),
    Global(VarIdent<'a>),
}

impl<'a> Display for Cell<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Var(ident) => write!(f, "{ident}"),
            Self::Return(ident) => write!(f, "ret-{ident}"),
            Self::Stack(ident) => write!(f, "stack-{ident}"),
            Self::Heap(ident) => write!(f, "heap-{ident}"),
            Self::Global(ident) => write!(f, "global-{ident}"),
        }
    }
}

impl<'a> FromStr for Cell<'a> {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("ret-") {
            s["ret-".len()..].parse().map(Self::Return)
        } else if s.starts_with("stack-") {
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

struct PointsToPreAnalyzer<'a> {
    cells: Vec<Cell<'a>>,
    allowed_offsets: Vec<(Cell<'a>, usize)>,
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
        self.num_cells_per_malloc = structs.values().map(|st| st.size).max().unwrap_or(0).max(1);
    }

    fn handle_ptr_function(
        &mut self,
        ident: VarIdent<'a>,
        parameters: Vec<VarIdent<'a>>,
        return_struct_type: Option<Rc<StructType>>,
    ) {
        self.cells.push(Cell::Var(ident.clone()));

        let offset = self.add_cells(ident.clone(), return_struct_type.as_deref(), Cell::Return)
            + parameters.len()
            - 1;

        for param in &parameters {
            self.cells.push(Cell::Var(param.clone()));
        }

        let first_cell = Cell::Return(first_ident(ident, return_struct_type.as_deref()));
        self.allowed_offsets.push((first_cell, offset));
    }

    fn handle_ptr_global(
        &mut self,
        ident: VarIdent<'a>,
        _init_ref: Option<VarIdent<'a>>,
        struct_type: Option<Rc<StructType>>,
    ) {
        self.cells.push(Cell::Var(ident.clone()));
        self.add_cells_and_allowed_offsets(ident, struct_type.as_deref(), Cell::Global);
    }

    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        _context: PointerContext<'a>,
    ) {
        match instr {
            PointerInstruction::Fresh { ident, struct_type } => {
                self.add_cells_and_allowed_offsets(ident, struct_type.as_deref(), Cell::Var)
            }
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
            PointerInstruction::Call { dest: None, .. } => {}

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

            PointerInstruction::Return { .. } => {}

            PointerInstruction::Store { .. } => {}
        }
    }
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

/// Visits a module, generating and solving constraints using a supplied constraint solver.
struct PointsToSolver<'a, S> {
    solver: S,
    return_struct_types: HashMap<VarIdent<'a>, Option<Rc<StructType>>>,
}

impl<'a, S> PointsToSolver<'a, S>
where
    S: Solver<Term = Cell<'a>>,
{
    fn new(cells: Vec<Cell<'a>>, allowed_offsets: Vec<(Cell<'a>, usize)>) -> Self {
        Self {
            solver: S::new(cells, allowed_offsets),
            return_struct_types: HashMap::new(),
        }
    }

    fn do_assignment(
        &mut self,
        dest: VarIdent<'a>,
        dest_cell_type: fn(VarIdent<'a>) -> Cell<'a>,
        value: VarIdent<'a>,
        value_cell_type: fn(VarIdent<'a>) -> Cell<'a>,
        struct_type: Option<&StructType>,
    ) {
        match struct_type {
            Some(_) => {
                let mut dest_vec = vec![];
                let mut value_vec = vec![];
                get_and_push_cells(dest, struct_type.as_deref(), dest_cell_type, &mut dest_vec);
                get_and_push_cells(
                    value,
                    struct_type.as_deref(),
                    value_cell_type,
                    &mut value_vec,
                );
                for (value_cell, dest_cell) in value_vec.into_iter().zip(dest_vec) {
                    let c = cstr!(value_cell <= dest_cell);
                    self.solver.add_constraint(c);
                }
            }
            None => {
                let value_cell = value_cell_type(value);
                let dest_cell = dest_cell_type(dest);
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

    fn handle_ptr_function(
        &mut self,
        ident: VarIdent<'a>,
        _parameters: Vec<VarIdent<'a>>,
        return_struct_type: Option<Rc<StructType>>,
    ) {
        let first_cell = Cell::Return(first_ident(ident.clone(), return_struct_type.as_deref()));
        let var_cell = Cell::Var(ident.clone());
        let c = cstr!(first_cell in var_cell);
        self.solver.add_constraint(c);

        self.return_struct_types.insert(ident, return_struct_type);
    }

    fn handle_ptr_global(
        &mut self,
        ident: VarIdent<'a>,
        init_ref: Option<VarIdent<'a>>,
        struct_type: Option<Rc<StructType>>,
    ) {
        let global_cell = Cell::Global(first_ident(ident.clone(), struct_type.as_deref()));
        let var_cell = Cell::Var(ident.clone());
        let c = cstr!(global_cell in var_cell);
        self.solver.add_constraint(c);

        if let Some(init_ident) = init_ref {
            self.do_assignment(
                ident,
                Cell::Global,
                init_ident,
                Cell::Var,
                struct_type.as_deref(),
            );
        }
    }

    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        context: PointerContext<'a>,
    ) {
        match instr {
            PointerInstruction::Assign {
                dest,
                value,
                struct_type,
            } => {
                self.do_assignment(dest, Cell::Var, value, Cell::Var, struct_type.as_deref());
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
                    self.do_assignment(
                        dest.clone(),
                        Cell::Var,
                        value,
                        Cell::Var,
                        struct_type.as_deref(),
                    );
                }
            }

            PointerInstruction::Call {
                dest,
                function,
                arguments,
                return_struct_type,
            } => {
                let function_cell = Cell::Var(function);
                for (i, arg) in arguments
                    .iter()
                    .enumerate()
                    .filter_map(|(i, a)| a.clone().map(|a| (i, a)))
                {
                    let arg_cell = Cell::Var(arg);
                    let offset = return_struct_type.as_ref().map(|st| st.size).unwrap_or(1) + i;
                    let c = cstr!(c in (function_cell.clone()) + offset : arg_cell <= c);
                    self.solver.add_constraint(c);
                }

                // Constraints for function return
                if let Some(dest_ident) = dest {
                    let mut dest_cells = vec![];
                    get_and_push_cells(
                        dest_ident,
                        return_struct_type.as_deref(),
                        Cell::Var,
                        &mut dest_cells,
                    );

                    for (i, cell) in dest_cells.into_iter().enumerate() {
                        let c = cstr!(c in (function_cell.clone()) + i : c <= cell);
                        self.solver.add_constraint(c);
                    }
                }
            }

            PointerInstruction::Return { return_reg } => {
                let fun_name = context
                    .fun_name
                    .expect("return instructions should only be generated inside functions");
                let function = VarIdent::Global {
                    name: Cow::Owned(Name::Name(Box::new(fun_name.into()))),
                };

                let return_struct_type = self
                    .return_struct_types
                    .get(&function)
                    .expect("StructType should have been added in handle_ptr_function")
                    .clone();

                self.do_assignment(
                    function,
                    Cell::Return,
                    return_reg,
                    Cell::Var,
                    return_struct_type.as_deref(),
                );
            }
            PointerInstruction::Fresh { .. } => (),
        }
    }
}

pub fn cell_is_in_function<'a>(cell: &Cell<'a>, function: &str) -> bool {
    match cell {
        Cell::Var(ident)
        | Cell::Return(ident)
        | Cell::Stack(ident)
        | Cell::Heap(ident)
        | Cell::Global(ident) => ident_is_in_function(ident, function),
    }
}

fn ident_is_in_function<'a>(ident: &VarIdent<'a>, function: &str) -> bool {
    match ident {
        VarIdent::Local { fun_name, .. } => fun_name == function,
        VarIdent::Offset { base, .. } => ident_is_in_function(base.as_ref(), function),
        VarIdent::Global { .. } => false,
        VarIdent::Fresh { .. } => false,
    }
}
