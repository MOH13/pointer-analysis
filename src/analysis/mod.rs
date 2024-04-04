use indexmap::IndexMap;
use std::borrow::Cow;
use std::fmt::{self, Debug, Display, Formatter};
use std::mem;
use std::rc::Rc;
use std::str::FromStr;

use hashbrown::{HashMap, HashSet};
use llvm_ir::Module;
use log::error;

use crate::cstr;
use crate::module_visitor::pointer::{
    PointerContext, PointerInstruction, PointerModuleObserver, PointerModuleVisitor,
};
use crate::module_visitor::structs::{StructMap, StructType};
use crate::module_visitor::{ModuleVisitor, VarIdent};
use crate::solver::{
    CallSite, ConstrainedTerms, Constraint, ContextSensitiveInput, FunctionInput, Solver,
    SolverSolution, TermSetTrait, TermType,
};
use crate::visualizer::{visualize, Graph};

#[cfg(test)]
mod tests;

#[derive(Default)]
pub struct Config {
    pub malloc_wrappers: HashSet<String>,
    pub realloc_wrappers: HashSet<String>,
    pub count_terms: bool,
}

pub struct PointsToAnalysis;

impl PointsToAnalysis {
    fn solve_module<'a, S, C>(
        solver: S,
        module: &'a Module,
        context_selector: C,
        config: &Config,
    ) -> (S::Solution, Vec<Cell<'a>>)
    where
        S: Solver<ContextSensitiveInput<Cell<'a>, C>> + 'a,
    {
        let mut pre_analyzer = PointsToPreAnalyzer::new();
        PointerModuleVisitor::new(
            &mut pre_analyzer,
            &config.malloc_wrappers,
            &config.realloc_wrappers,
        )
        .visit_module(module);
        let cells_copy = pre_analyzer
            .functions
            .iter()
            .flat_map(|(_, content)| {
                content
                    .return_and_parameter_cells
                    .iter()
                    .chain(&content.cells)
            })
            .cloned()
            .collect();

        let mut constraint_generator = ConstraintGenerator::new();
        PointerModuleVisitor::new(
            &mut constraint_generator,
            &config.malloc_wrappers,
            &config.realloc_wrappers,
        )
        .visit_module(module);

        let pre_analysis_global = mem::take(pre_analyzer.functions.get_mut(&None).unwrap());
        let global_constraints = constraint_generator
            .constraints
            .get_mut(&None)
            .map(mem::take)
            .unwrap_or_default();

        let (_, entry) = pre_analysis_global.combine_with_constraints(global_constraints);

        let main_function_index = pre_analyzer
            .functions
            .iter()
            .filter_map(|(f, _)| *f)
            .position(|func_name| func_name == "main")
            .expect("Could not find a main function");

        let functions: Vec<_> = pre_analyzer
            .functions
            .into_iter()
            .filter_map(|(func, state)| func.map(|func| (func, state)))
            .map(|(func, state)| {
                let constraints = constraint_generator
                    .constraints
                    .get_mut(&Some(func))
                    .map(mem::take)
                    .unwrap_or_default();
                let (return_and_parameter_terms, constrained_terms) =
                    state.combine_with_constraints(constraints);
                FunctionInput {
                    fun_name: func.into(),
                    return_and_parameter_terms,
                    constrained_terms,
                }
            })
            .collect();

        let input = ContextSensitiveInput {
            global: entry,
            functions,
            entrypoints: vec![main_function_index],
            context_selector,
        };

        let solution = solver.solve(input);

        (solution, cells_copy)
    }

    /// Runs the points-to analysis on LLVM module `module` using `solver`.
    pub fn run<'a, S, C>(
        solver: S,
        module: &'a Module,
        context_selector: C,
        config: &Config,
    ) -> PointsToResult<'a, S::Solution>
    where
        S: Solver<ContextSensitiveInput<Cell<'a>, C>> + 'a,
    {
        let (solution, cells) = Self::solve_module(solver, module, context_selector, config);

        if config.count_terms {
            let mut counts: Vec<_> = cells.iter().map(|c| solution.get(c).len()).collect();
            let max = counts.iter().copied().max().unwrap_or(0);
            let mean = counts.iter().sum::<usize>() as f64 / counts.len() as f64;
            let median = counts.select_nth_unstable(cells.len() / 2).1;
            println!("Max: {max}");
            println!("Mean: {mean}");
            println!("Median: {median}");
        }

        PointsToResult(solution, cells)
    }

    pub fn run_and_visualize<'a, S, C>(
        solver: S,
        module: &'a Module,
        context_selector: C,
        config: &Config,
        dot_output_path: &str,
    ) -> PointsToResult<'a, S::Solution>
    where
        S: Solver<ContextSensitiveInput<Cell<'a>, C>> + 'a,
        S::Solution: Graph,
    {
        let (solution, cells) = Self::solve_module(solver, module, context_selector, config);
        if let Err(e) = visualize(&solution, dot_output_path) {
            error!("Error visualizing graph: {e}");
        }
        PointsToResult(solution, cells)
    }
}

#[derive(Debug, Clone)]
pub struct PointsToResult<'a, S: SolverSolution>(pub S, pub Vec<Cell<'a>>);

pub struct FilteredResults<'a, 'b, S: SolverSolution, F1, F2> {
    result: &'b PointsToResult<'a, S>,
    key_filter: F1,
    value_filter: F2,
    include_strs: Vec<&'b str>,
    exclude_strs: Vec<&'b str>,
}

impl<'a, S: SolverSolution> PointsToResult<'a, S> {
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

impl<'a, 'b, S, F1, F2> FilteredResults<'a, 'b, S, F1, F2>
where
    S: SolverSolution<Term = Cell<'a>>,
    S::TermSet: FromIterator<Cell<'a>>,
    F1: Fn(&Cell<'a>, &S::TermSet) -> bool,
    F2: Fn(&Cell<'a>) -> bool,
{
    pub fn iter_solutions(&'b self) -> impl Iterator<Item = (Cell<'a>, S::TermSet)> + 'b {
        self.result
            .1
            .iter()
            .map(|cell| (cell.clone(), self.result.0.get(cell)))
            .map(|(cell, set)| (cell, set.iter().filter(&self.value_filter).collect()))
            .filter(|(cell, set)| {
                let cell_str = cell.to_string();
                (self.key_filter)(cell, set)
                    && (self.include_strs.is_empty()
                        || self.include_strs.iter().any(|s| cell_str.contains(s)))
                    && (self.exclude_strs.iter().all(|s| !cell_str.contains(s)))
            })
    }
}

impl<'a, S> Display for PointsToResult<'a, S>
where
    S: SolverSolution<Term = Cell<'a>>,
    S::TermSet: fmt::Debug + IntoIterator<Item = Cell<'a>> + FromIterator<Cell<'a>>,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let filtered = self.get_all_entries();
        writeln!(f, "{filtered}")?;
        Ok(())
    }
}

impl<'a, 'b, S, F1, F2> Display for FilteredResults<'a, 'b, S, F1, F2>
where
    S: SolverSolution<Term = Cell<'a>>,
    S::TermSet: fmt::Debug + FromIterator<Cell<'a>>,
    F1: Fn(&Cell<'a>, &S::TermSet) -> bool,
    F2: Fn(&Cell<'a>) -> bool,
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

#[derive(Default)]
struct PointsToPreAnalyzerFunctionState<'a> {
    dests_already_added: HashSet<VarIdent<'a>>,
    return_and_parameter_cells: Vec<Cell<'a>>,
    cells: Vec<Cell<'a>>,
    term_types: Vec<(Cell<'a>, TermType)>,
}

impl<'a> PointsToPreAnalyzerFunctionState<'a> {
    fn combine_with_constraints(
        self,
        constraints: Vec<Constraint<Cell<'a>>>,
    ) -> (Vec<Cell<'a>>, ConstrainedTerms<Cell<'a>>) {
        (
            self.return_and_parameter_cells,
            ConstrainedTerms {
                terms: self.cells,
                term_types: self.term_types,
                constraints: constraints,
            },
        )
    }
}

struct PointsToPreAnalyzer<'a> {
    functions: IndexMap<Option<&'a str>, PointsToPreAnalyzerFunctionState<'a>>,
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

fn push_term_types<'a>(
    base_ident: VarIdent<'a>,
    struct_type: Option<&StructType>,
    ident_to_cell: fn(VarIdent<'a>) -> Cell<'a>,
    term_types: &mut Vec<(Cell<'a>, TermType)>,
    first_offset: Option<usize>,
) {
    match struct_type {
        Some(StructType { fields, .. }) => {
            let base_rc = Rc::new(base_ident);

            let num_sub_cells = count_cells(struct_type);
            let mut first_offset = first_offset.or_else(|| num_sub_cells.checked_sub(1));

            for (i, field) in fields.iter().enumerate() {
                let offset_ident = VarIdent::Offset {
                    base: base_rc.clone(),
                    offset: i,
                };
                first_offset = first_offset.filter(|_| i == 0);
                push_term_types(
                    offset_ident,
                    field.st.as_deref(),
                    ident_to_cell,
                    term_types,
                    first_offset,
                );
            }
        }

        None => {
            if let Some(offset) = first_offset {
                term_types.push((ident_to_cell(base_ident), TermType::Struct(offset)));
            }
        }
    }
}

fn count_cells(struct_type: Option<&StructType>) -> usize {
    match struct_type {
        Some(StructType { fields, .. }) => {
            fields.iter().map(|f| count_cells(f.st.as_deref())).sum()
        }
        None => 1,
    }
}

impl<'a> PointsToPreAnalyzer<'a> {
    fn new() -> Self {
        Self {
            functions: IndexMap::new(),
            num_cells_per_malloc: 0,
        }
    }

    fn add_cells_and_term_types(
        &mut self,
        base_ident: VarIdent<'a>,
        struct_type: Option<&StructType>,
        ident_to_cell: fn(VarIdent<'a>) -> Cell<'a>,
        fun_name: Option<&'a str>,
    ) {
        let function_state = self.functions.entry(fun_name).or_default();

        if !function_state
            .dests_already_added
            .insert(base_ident.clone())
        {
            return;
        }
        get_and_push_cells(
            base_ident.clone(),
            struct_type,
            ident_to_cell,
            &mut function_state.cells,
        );
        push_term_types(
            base_ident,
            struct_type,
            ident_to_cell,
            &mut function_state.term_types,
            None,
        );
        // for (i, cell) in function_state.cells.iter().rev().take(added).enumerate() {
        //     if i > 0 {
        //         function_state
        //             .term_types
        //             .push((cell.clone(), TermType::Struct(i)));
        //     }
        // }
    }
}

impl<'a> PointerModuleObserver<'a> for PointsToPreAnalyzer<'a> {
    fn init(&mut self, structs: &StructMap) {
        self.num_cells_per_malloc = structs.values().map(|st| st.size).max().unwrap_or(0).max(1);
    }

    fn handle_ptr_function(
        &mut self,
        fun_name: &'a str,
        ident: VarIdent<'a>,
        type_index: u32,
        parameters: Vec<VarIdent<'a>>,
        return_struct_type: Option<Rc<StructType>>,
    ) {
        let function_state = self.functions.entry(Some(fun_name)).or_default();

        let offset = get_and_push_cells(
            ident.clone(),
            return_struct_type.as_deref(),
            Cell::Return,
            &mut function_state.return_and_parameter_cells,
        ) + parameters.len()
            - 1;

        for param in &parameters {
            function_state
                .return_and_parameter_cells
                .push(Cell::Var(param.clone()));
        }

        let first_cell = Cell::Return(first_ident(ident.clone(), return_struct_type.as_deref()));
        function_state
            .term_types
            .push((first_cell, TermType::Function(offset, type_index)));

        let global_state = self.functions.entry(None).or_default();

        global_state.cells.push(Cell::Var(ident));
    }

    fn handle_ptr_global(
        &mut self,
        ident: VarIdent<'a>,
        _init_ref: Option<VarIdent<'a>>,
        struct_type: Option<Rc<StructType>>,
    ) {
        let global_state = self.functions.entry(None).or_default();

        global_state.cells.push(Cell::Var(ident.clone()));
        self.add_cells_and_term_types(ident, struct_type.as_deref(), Cell::Global, None);
    }

    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        context: PointerContext<'a>,
    ) {
        let function_state = self.functions.entry(context.fun_name).or_default();

        match instr {
            PointerInstruction::Fresh { ident, struct_type } => self.add_cells_and_term_types(
                ident,
                struct_type.as_deref(),
                Cell::Var,
                context.fun_name,
            ),
            PointerInstruction::Gep { dest, .. } => {
                self.add_cells_and_term_types(dest, None, Cell::Var, context.fun_name)
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
            } => self.add_cells_and_term_types(
                dest,
                struct_type.as_deref(),
                Cell::Var,
                context.fun_name,
            ),
            PointerInstruction::Call { dest: None, .. } => {}

            PointerInstruction::Alloca { dest, struct_type } => {
                function_state.cells.push(Cell::Var(dest.clone()));
                self.add_cells_and_term_types(
                    dest,
                    struct_type.as_deref(),
                    Cell::Stack,
                    context.fun_name,
                );
            }

            PointerInstruction::Malloc { dest, single } => {
                function_state.cells.push(Cell::Var(dest.clone()));
                if single {
                    let cell = Cell::Heap(dest);
                    function_state.cells.push(cell.clone());
                    return;
                }

                let base_rc = Rc::new(dest);
                let num_cells = self.num_cells_per_malloc;
                for i in 0..num_cells {
                    let cell = Cell::Heap(VarIdent::Offset {
                        base: base_rc.clone(),
                        offset: i,
                    });
                    function_state.cells.push(cell.clone());
                    function_state
                        .term_types
                        .push((cell, TermType::Struct(num_cells - i - 1)));
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

/// Visits a module, generating constraints.
struct ConstraintGenerator<'a> {
    call_site_counter: u32,
    constraints: HashMap<Option<&'a str>, Vec<Constraint<Cell<'a>>>>,
    return_struct_types: HashMap<VarIdent<'a>, Option<Rc<StructType>>>,
}

fn do_assignment<'a>(
    dest: VarIdent<'a>,
    dest_cell_type: fn(VarIdent<'a>) -> Cell<'a>,
    value: VarIdent<'a>,
    value_cell_type: fn(VarIdent<'a>) -> Cell<'a>,
    struct_type: Option<&StructType>,
    constraints: &mut Vec<Constraint<Cell<'a>>>,
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
                let constraint = cstr!(value_cell <= dest_cell);
                constraints.push(constraint);
            }
        }
        None => {
            let value_cell = value_cell_type(value);
            let dest_cell = dest_cell_type(dest);
            let constraint = cstr!(value_cell <= dest_cell);
            constraints.push(constraint);
        }
    };
}

impl<'a> ConstraintGenerator<'a> {
    fn new() -> Self {
        Self {
            call_site_counter: 0,
            constraints: HashMap::new(),
            return_struct_types: HashMap::new(),
        }
    }
}

impl<'a> PointerModuleObserver<'a> for ConstraintGenerator<'a> {
    fn init(&mut self, _structs: &StructMap) {}

    fn handle_ptr_function(
        &mut self,
        fun_name: &'a str,
        ident: VarIdent<'a>,
        _type_index: u32,
        _parameters: Vec<VarIdent<'a>>,
        return_struct_type: Option<Rc<StructType>>,
    ) {
        let function_constraints = self.constraints.entry(Some(fun_name)).or_default();

        let first_cell = Cell::Return(first_ident(ident.clone(), return_struct_type.as_deref()));
        let var_cell = Cell::Var(ident.clone());
        let constraint = cstr!(first_cell in var_cell);
        function_constraints.push(constraint);

        self.return_struct_types.insert(ident, return_struct_type);
    }

    fn handle_ptr_global(
        &mut self,
        ident: VarIdent<'a>,
        init_ref: Option<VarIdent<'a>>,
        struct_type: Option<Rc<StructType>>,
    ) {
        let global_constraints = self.constraints.entry(None).or_default();

        let global_cell = Cell::Global(first_ident(ident.clone(), struct_type.as_deref()));
        let var_cell = Cell::Var(ident.clone());
        let constraint = cstr!(global_cell in var_cell);
        global_constraints.push(constraint);

        if let Some(init_ident) = init_ref {
            do_assignment(
                ident,
                Cell::Global,
                init_ident,
                Cell::Var,
                struct_type.as_deref(),
                global_constraints,
            );
        }
    }

    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        context: PointerContext<'a>,
    ) {
        let function_constraints = self.constraints.entry(context.fun_name).or_default();

        match instr {
            PointerInstruction::Assign {
                dest,
                value,
                struct_type,
            } => {
                do_assignment(
                    dest,
                    Cell::Var,
                    value,
                    Cell::Var,
                    struct_type.as_deref(),
                    function_constraints,
                );
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
                            let constraint =
                                cstr!(value_cell <= *((address_cell.clone()) + offset));
                            function_constraints.push(constraint);
                        }
                    }
                    None => {
                        let value_cell = Cell::Var(value);
                        let constraint = cstr!(value_cell <= *address_cell);
                        function_constraints.push(constraint);
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
                            let constraint = cstr!(*((address_cell.clone()) + offset) <= dest_cell);
                            function_constraints.push(constraint);
                        }
                    }
                    None => {
                        let dest_cell = Cell::Var(dest);
                        let constraint = cstr!(*address_cell <= dest_cell);
                        function_constraints.push(constraint);
                    }
                };
            }

            PointerInstruction::Alloca { dest, struct_type } => {
                let stack_cell = Cell::Stack(first_ident(dest.clone(), struct_type.as_deref()));
                let var_cell = Cell::Var(dest);
                let constraint = cstr!(stack_cell in var_cell);
                function_constraints.push(constraint);
            }

            PointerInstruction::Malloc { dest, single } => {
                let heap_cell = if single {
                    Cell::Heap(dest.clone())
                } else {
                    Cell::Heap(VarIdent::Offset {
                        base: Rc::new(dest.clone()),
                        offset: 0,
                    })
                };
                let var_cell = Cell::Var(dest);
                let constraint = cstr!(heap_cell in var_cell);
                function_constraints.push(constraint);
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
                let constraint = cstr!(address_cell + offset <= dest_cell);
                function_constraints.push(constraint);
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
                let constraint = cstr!(address_cell + offset <= dest_cell);
                function_constraints.push(constraint);
            }

            PointerInstruction::Phi {
                dest,
                incoming_values,
                struct_type,
            } => {
                for value in incoming_values {
                    do_assignment(
                        dest.clone(),
                        Cell::Var,
                        value,
                        Cell::Var,
                        struct_type.as_deref(),
                        function_constraints,
                    );
                }
            }

            PointerInstruction::Call {
                dest,
                function,
                func_type_id,
                arguments,
                return_struct_type,
            } => {
                let function_cell = Cell::Var(function.clone());
                let call_site_desc = if let Some(dest) = dest.clone() {
                    dest.to_string()
                } else {
                    let fun_name = context.fun_name.expect("no calls outside functions");
                    let counter = self.call_site_counter;
                    self.call_site_counter += 1;
                    let function_string = function.to_string();
                    let function_str = function_string.split("@").next().unwrap();
                    format!("{fun_name} called {function_str}#{}", counter)
                };
                let call_site = CallSite::new(call_site_desc, func_type_id);
                function_constraints.push(Constraint::CallDummy {
                    cond_node: function_cell.clone(),
                    arguments: vec![],
                    result_node: function_cell.clone(),
                    call_site: call_site.clone(),
                });
                for (i, arg) in arguments
                    .iter()
                    .enumerate()
                    .filter_map(|(i, a)| a.clone().map(|a| (i, a)))
                {
                    let arg_cell = Cell::Var(arg);
                    let offset = return_struct_type.as_ref().map(|st| st.size).unwrap_or(1) + i;
                    let c = call_site.clone();
                    let constraint = cstr!(c: arg_cell <= *fn ((function_cell.clone()) + offset));
                    function_constraints.push(constraint);
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
                        let c = call_site.clone();
                        let constraint = cstr!(c: *fn ((function_cell.clone()) + i) <= cell);
                        function_constraints.push(constraint);
                    }
                }
            }

            PointerInstruction::Return { return_reg } => {
                let fun_name = context
                    .fun_name
                    .expect("return instructions should only be generated inside functions");
                let function = VarIdent::Global {
                    name: Cow::Owned(String::from(fun_name)),
                };

                let return_struct_type = self
                    .return_struct_types
                    .get(&function)
                    .expect("StructType should have been added in handle_ptr_function")
                    .clone();

                do_assignment(
                    function,
                    Cell::Return,
                    return_reg,
                    Cell::Var,
                    return_struct_type.as_deref(),
                    function_constraints,
                );
            }
            PointerInstruction::Fresh { .. } => (),
        }
    }
}

pub fn cell_is_in_function<'a>(cell: &Cell<'a>, function: &str) -> bool {
    match cell {
        Cell::Var(ident) | Cell::Return(ident) | Cell::Stack(ident) | Cell::Heap(ident) => {
            ident_is_in_function(ident, function)
        }
        Cell::Global(_) => false,
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
