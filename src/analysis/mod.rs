use indexmap::IndexMap;
use itertools::Itertools;
use std::cell::{RefCell, RefMut};
use std::fmt::{self, Debug, Display, Formatter};
use std::mem;
use std::ops::Deref;
use std::rc::Rc;
use std::str::FromStr;
use std::time::{Duration, Instant};

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
    CallSite, ConstrainedTerms, Constraint, ContextSensitiveInput, Demand,
    DemandContextSensitiveInput, DemandInput, Demands, FunctionInput, Solver, SolverSolution,
    TermSetTrait, TermType,
};
use crate::visualizer::Visualizable;

#[cfg(test)]
mod tests;

#[derive(Default)]
pub struct Config {
    pub malloc_wrappers: HashSet<String>,
    pub realloc_wrappers: HashSet<String>,
}

pub struct PointsToAnalysis;

fn try_get_call_dummy_cond_node(cstr: &Constraint<Cell>) -> Option<Cell> {
    if let Constraint::CallDummy { cond_node, .. } = cstr {
        if !matches!(cond_node, Cell::Var(VarIdent::Global { .. })) {
            return Some(cond_node.clone());
        }
    }
    return None;
}

impl PointsToAnalysis {
    fn solve_module<'a, S, C>(
        solver: &S,
        module: &'a Module,
        context_selector: C,
        demands: Demands<Cell>,
        config: &Config,
    ) -> PointsToResult<S::Solution>
    where
        S: Solver<DemandContextSensitiveInput<Cell, C>> + 'a,
    {
        let pre_analysis_start = Instant::now();

        let mut pre_analyzer = PointsToPreAnalyzer::new();
        PointerModuleVisitor::new(
            &mut pre_analyzer,
            &config.malloc_wrappers,
            &config.realloc_wrappers,
        )
        .visit_module(module);

        let cells_copy: Vec<_> = pre_analyzer
            .functions
            .iter()
            .flat_map(|(_, content)| {
                content
                    .return_cells
                    .iter()
                    .chain(&content.parameter_cells)
                    .chain(&content.cells)
            })
            .cloned()
            .collect();

        let pre_analysis_time = pre_analysis_start.elapsed();
        let constraint_gen_start = Instant::now();

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

        let (_, _, entry) = pre_analysis_global.combine_with_constraints(global_constraints);

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
                let (return_terms, parameter_terms, constrained_terms) =
                    state.combine_with_constraints(constraints);
                FunctionInput {
                    fun_name: func.into(),
                    return_terms,
                    parameter_terms,
                    constrained_terms,
                }
            })
            .collect();

        let (demands_list, all) = match demands {
            Demands::All => {
                let list = cells_copy
                    .iter()
                    .map(|c| Demand::PointedBy(c.clone()))
                    .collect();
                (list, true)
            }
            Demands::List(list) => (list, false),
            Demands::CallGraphPointsTo => {
                let mut list = vec![];
                for cstr in functions
                    .iter()
                    .flat_map(|f| &f.constrained_terms.constraints)
                {
                    if let Constraint::CallDummy { cond_node, .. } = cstr {
                        list.push(Demand::PointsTo(cond_node.clone()));
                    }
                }
                (list, false)
            }
            Demands::CallGraphPointedBy => {
                let list = functions
                    .iter()
                    .map(|f| Demand::PointedBy(f.return_terms[0].clone()))
                    .collect();
                (list, false)
            }
            Demands::NonTrivial => {
                let mut list = vec![];
                for cstr in functions
                    .iter()
                    .flat_map(|f| &f.constrained_terms.constraints)
                {
                    if let Constraint::CallDummy { cond_node, .. } = cstr {
                        if !matches!(cond_node, Cell::Var(VarIdent::Global { .. })) {
                            list.push(Demand::PointsTo(cond_node.clone()));
                        }
                    }
                }
                (list, false)
            }
            Demands::NonTrivialOnlyHalf => {
                let mut func_vec = functions
                    .iter()
                    .map(|f| {
                        f.constrained_terms
                            .constraints
                            .iter()
                            .filter_map(try_get_call_dummy_cond_node)
                            .map(Demand::PointsTo)
                            .collect_vec()
                    })
                    .collect_vec();
                func_vec.sort_by_key(|f| f.len());

                let list = func_vec.into_iter().rev().take(1).flatten().collect_vec();

                dbg!(&list);

                (list, false)
            }
            Demands::Escape => {
                let list = functions
                    .iter()
                    .flat_map(|f| &f.return_terms)
                    .map(|t| Demand::PointsTo(t.clone()))
                    .collect();
                (list, false)
            }
        };

        let demands_copy = if all {
            None
        } else {
            Some(demands_list.clone())
        };

        let input = DemandInput {
            demands: demands_list,
            input: ContextSensitiveInput {
                global: entry,
                functions,
                entrypoints: vec![main_function_index],
                context_selector,
            },
        };

        let constraint_gen_time = constraint_gen_start.elapsed();

        // Find called funcitons
        let mut called_functions = HashSet::new();
        for function in &input.input.functions {
            for constraint in &function.constrained_terms.constraints {
                if let Constraint::CallDummy { cond_node, .. } = constraint {
                    called_functions.insert(cond_node.clone());
                }
            }
        }

        let solver_start = Instant::now();

        let solution = solver.solve(input);

        let solver_time = solver_start.elapsed();

        PointsToResult {
            solution,
            cells: cells_copy,
            demands: demands_copy,
            called_functions,
            cell_cache: CellCache::new(),
            pre_analysis_time,
            constraint_gen_time,
            solver_time,
        }
    }

    /// Runs the points-to analysis on LLVM module `module` using `solver`.
    pub fn run<'a, S, C>(
        solver: &S,
        module: &'a Module,
        context_selector: C,
        demands: Demands<Cell>,
        config: &Config,
    ) -> PointsToResult<S::Solution>
    where
        S: Solver<DemandContextSensitiveInput<Cell, C>> + 'a,
    {
        Self::solve_module(solver, module, context_selector, demands, config)
    }

    pub fn run_and_visualize<'a, S, C>(
        solver: &S,
        module: &'a Module,
        context_selector: C,
        demands: Demands<Cell>,
        config: &Config,
        dot_output_path: &str,
    ) -> PointsToResult<S::Solution>
    where
        S: Solver<DemandContextSensitiveInput<Cell, C>> + 'a,
        S::Solution: Visualizable,
    {
        let res = Self::solve_module(solver, module, context_selector, demands, config);
        if let Err(e) = res.solution.visualize(dot_output_path) {
            error!("Error visualizing graph: {e}");
        }
        res
    }
}

#[derive(Debug, Clone)]
pub struct CellCache(RefCell<HashMap<Cell, String>>);

pub struct CacheEntry<'b>(RefMut<'b, String>);

#[derive(Debug, Clone)]
pub struct PointsToResult<S> {
    pub solution: S,
    pub cells: Vec<Cell>,
    pub demands: Option<Vec<Demand<Cell>>>,
    pub cell_cache: CellCache,
    pub called_functions: HashSet<Cell>,
    pub pre_analysis_time: Duration,
    pub constraint_gen_time: Duration,
    pub solver_time: Duration,
}

impl<'a> CellCache {
    pub fn new() -> Self {
        Self(RefCell::new(HashMap::new()))
    }

    pub fn string_of<'b>(&'b self, cell: &Cell) -> CacheEntry<'b> {
        let borrow = self.0.borrow_mut();
        let a = RefMut::map(borrow, |m| {
            m.entry(cell.clone()).or_insert_with(|| cell.to_string())
        });
        CacheEntry(a)
    }
}

impl<'a, 'b> Deref for CacheEntry<'b> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub trait ResultTrait: Display {
    type TermSet: TermSetTrait<Term = Cell>;
    fn get<'a>(&'a self, cell: &Cell) -> Option<LazyTermSet<'a, Self>>
    where
        Self: Sized;

    fn get_eager<'a>(&'a self, cell: &Cell) -> Option<Self::TermSet>
    where
        Self: Sized;

    fn get_len<'a>(&'a self, cell: &Cell) -> Option<usize>
    where
        Self: Sized;

    fn iter_solutions<'a>(&'a self) -> impl Iterator<Item = (Cell, LazyTermSet<'a, Self>)>
    where
        Self: Sized;
    fn get_cells(&self) -> &[Cell];
    fn get_cell_cache(&self) -> &CellCache;

    fn filter_result<
        'a,
        F3: Fn(&Cell, &mut LazyTermSet<'a, Self>, &CellCache) -> bool,
        F4: Fn(&Cell, &Cell, &CellCache) -> bool,
    >(
        &'a self,
        key_filter: F3,
        value_filter: F4,
        include_strs: Vec<String>,
        exclude_strs: Vec<String>,
    ) -> FilteredResults<'a, F3, F4, Self>
    where
        Self: Sized,
    {
        FilteredResults {
            result: self,
            key_filter,
            value_filter,
            include_strs,
            exclude_strs,
        }
    }
}

pub enum LazyTermSet<'a, R: ResultTrait> {
    FromResult(Cell, &'a R),
    FromLen(usize, Cell, &'a R),
    FromSet(R::TermSet),
}

impl<'a, R> LazyTermSet<'a, R>
where
    R: ResultTrait,
{
    pub fn from_set(set: R::TermSet) -> Self {
        Self::FromSet(set)
    }

    pub fn from_result(cell: Cell, result: &'a R) -> Self {
        Self::FromResult(cell, result)
    }

    pub fn get(&mut self) -> &R::TermSet {
        if let LazyTermSet::FromResult(cell, result) | LazyTermSet::FromLen(_, cell, result) =
            &*self
        {
            let new_set = result
                .get_eager(&cell)
                .expect("Result set should not be none for LazyTermSet");
            *self = LazyTermSet::FromSet(new_set);
        }
        match &*self {
            LazyTermSet::FromSet(set) => set,
            _ => unreachable!(),
        }
    }

    pub fn get_len(&mut self) -> usize {
        if let Self::FromResult(cell, result) = self {
            let new_len = result
                .get_len(&cell)
                .expect("Result set should not be none for LazyTermSet");
            *self = LazyTermSet::FromLen(new_len, cell.clone(), result);
        }
        match &*self {
            LazyTermSet::FromSet(set) => set.len(),
            LazyTermSet::FromLen(len, _, _) => *len,
            _ => unreachable!(),
        }
    }

    pub fn into_inner(mut self) -> R::TermSet {
        self.get();
        match self {
            LazyTermSet::FromSet(set) => set,
            _ => unreachable!(),
        }
    }
}

impl<S> ResultTrait for PointsToResult<S>
where
    S: SolverSolution<Term = Cell>,
{
    type TermSet = S::TermSet;

    fn get<'a>(&'a self, cell: &Cell) -> Option<LazyTermSet<'a, Self>> {
        Some(LazyTermSet::from_result(cell.clone(), self))
    }

    fn get_eager<'a>(&'a self, cell: &Cell) -> Option<Self::TermSet> {
        Some(self.solution.get(cell))
    }

    fn get_len<'a>(&'a self, cell: &Cell) -> Option<usize> {
        Some(self.solution.get_len(cell))
    }

    fn iter_solutions<'a>(&'a self) -> impl Iterator<Item = (Cell, LazyTermSet<'a, Self>)> {
        self.cells.iter().map(|c| (c.clone(), self.get(c).unwrap()))
    }

    fn get_cells(&self) -> &[Cell] {
        &self.cells
    }

    fn get_cell_cache(&self) -> &CellCache {
        &self.cell_cache
    }
}

pub struct FilteredResults<'a, F1, F2, R> {
    result: &'a R,
    key_filter: F1,
    value_filter: F2,
    include_strs: Vec<String>,
    exclude_strs: Vec<String>,
}

impl<'a, F1, F2, R> ResultTrait for FilteredResults<'a, F1, F2, R>
where
    R: ResultTrait,
    R::TermSet: TermSetTrait<Term = Cell>,
    F1: Fn(&Cell, &mut LazyTermSet<'a, R>, &CellCache) -> bool,
    F2: Fn(&Cell, &Cell, &CellCache) -> bool,
{
    type TermSet = HashSet<Cell>;

    fn get<'b>(&'b self, cell: &Cell) -> Option<LazyTermSet<'b, Self>> {
        self.get_eager(cell).map(LazyTermSet::from_set)
    }

    fn get_eager<'b>(&'b self, cell: &Cell) -> Option<Self::TermSet> {
        if !self.include_strs.is_empty() || !self.exclude_strs.is_empty() {
            let cell_str = self.get_cell_cache().string_of(cell);
            if !self.include_strs.is_empty()
                && !self.include_strs.iter().any(|s| cell_str.contains(s))
            {
                return None;
            }
            if self.exclude_strs.iter().any(|s| cell_str.contains(s)) {
                return None;
            }
        }

        let mut result_solution = self.result.get(cell)?;
        if !(self.key_filter)(cell, &mut result_solution, self.result.get_cell_cache()) {
            return None;
        }

        Some(
            result_solution
                .get()
                .iter()
                .filter(|t| (self.value_filter)(cell, t, self.result.get_cell_cache()))
                .collect(),
        )
    }

    fn get_len<'b>(&'b self, cell: &Cell) -> Option<usize> {
        self.get_eager(cell).map(|s| s.len())
    }

    fn iter_solutions<'b>(&'b self) -> impl Iterator<Item = (Cell, LazyTermSet<'b, Self>)> {
        self.get_cells()
            .iter()
            .filter_map(|c| self.get(c).map(|s| (c.clone(), s)))
    }

    fn get_cells(&self) -> &[Cell] {
        self.result.get_cells()
    }

    fn get_cell_cache(&self) -> &CellCache {
        self.result.get_cell_cache()
    }
}

impl<S> PointsToResult<S>
where
    S: SolverSolution<Term = Cell>,
{
    pub fn get_all_entries<'a>(
        &'a self,
    ) -> FilteredResults<
        'a,
        fn(&Cell, &mut LazyTermSet<'a, Self>, &CellCache) -> bool,
        fn(&Cell, &Cell, &CellCache) -> bool,
        Self,
    > {
        FilteredResults {
            result: self,
            key_filter: |_, _, _| true,
            value_filter: |_, _, _| true,
            include_strs: Vec::new(),
            exclude_strs: Vec::new(),
        }
    }

    pub fn into_solution(self) -> S {
        self.solution
    }
}

impl<S> Display for PointsToResult<S>
where
    S: SolverSolution<Term = Cell>,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let filtered = self.get_all_entries();
        filtered.fmt(f)?;
        Ok(())
    }
}

impl<'b, F1, F2, R> Display for FilteredResults<'b, F1, F2, R>
where
    Self: ResultTrait,
    <Self as ResultTrait>::TermSet: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for (cell, set) in self.iter_solutions() {
            let set = set.into_inner();
            writeln!(f, "[[{cell}]] = {set:#?}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Cell {
    Var(VarIdent),
    Return(VarIdent),
    // Since LLVM is in SSA, we can use the name of the
    // allocation register to refer to the allocation site
    Stack(VarIdent),
    Heap(VarIdent),
    Global(VarIdent),
}

impl Display for Cell {
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

impl FromStr for Cell {
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

impl<'a> Debug for Cell {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

#[derive(Default)]
struct PointsToPreAnalyzerFunctionState {
    dests_already_added: HashSet<VarIdent>,
    return_cells: Vec<Cell>,
    parameter_cells: Vec<Cell>,
    cells: Vec<Cell>,
    term_types: Vec<(Cell, TermType)>,
}

impl PointsToPreAnalyzerFunctionState {
    fn combine_with_constraints(
        self,
        constraints: Vec<Constraint<Cell>>,
    ) -> (Vec<Cell>, Vec<Cell>, ConstrainedTerms<Cell>) {
        (
            self.return_cells,
            self.parameter_cells,
            ConstrainedTerms {
                terms: self.cells,
                term_types: self.term_types,
                constraints: constraints,
            },
        )
    }
}

struct PointsToPreAnalyzer<'a> {
    functions: IndexMap<Option<&'a str>, PointsToPreAnalyzerFunctionState>,
    num_cells_per_malloc: usize,
}

fn get_and_push_cells(
    base_ident: VarIdent,
    struct_type: Option<&StructType>,
    ident_to_cell: fn(VarIdent) -> Cell,
    cells: &mut Vec<Cell>,
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

fn push_term_types(
    base_ident: VarIdent,
    struct_type: Option<&StructType>,
    ident_to_cell: fn(VarIdent) -> Cell,
    term_types: &mut Vec<(Cell, TermType)>,
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
        base_ident: VarIdent,
        struct_type: Option<&StructType>,
        ident_to_cell: fn(VarIdent) -> Cell,
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
        ident: VarIdent,
        type_index: u32,
        parameters: Vec<VarIdent>,
        return_struct_type: Option<Rc<StructType>>,
    ) {
        let function_state = self.functions.entry(Some(fun_name)).or_default();

        let offset = get_and_push_cells(
            ident.clone(),
            return_struct_type.as_deref(),
            Cell::Return,
            &mut function_state.return_cells,
        ) + parameters.len()
            - 1;

        for param in &parameters {
            function_state
                .parameter_cells
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
        ident: VarIdent,
        _init_ref: Option<VarIdent>,
        struct_type: Option<Rc<StructType>>,
    ) {
        let global_state = self.functions.entry(None).or_default();

        global_state.cells.push(Cell::Var(ident.clone()));
        self.add_cells_and_term_types(ident, struct_type.as_deref(), Cell::Global, None);
    }

    fn handle_ptr_instruction(&mut self, instr: PointerInstruction, context: PointerContext<'a>) {
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

fn first_ident<'a>(base_ident: VarIdent, struct_type: Option<&StructType>) -> VarIdent {
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
    constraints: HashMap<Option<&'a str>, Vec<Constraint<Cell>>>,
    return_struct_types: HashMap<VarIdent, Option<Rc<StructType>>>,
}

fn do_assignment(
    dest: VarIdent,
    dest_cell_type: fn(VarIdent) -> Cell,
    value: VarIdent,
    value_cell_type: fn(VarIdent) -> Cell,
    struct_type: Option<&StructType>,
    constraints: &mut Vec<Constraint<Cell>>,
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
        ident: VarIdent,
        _type_index: u32,
        _parameters: Vec<VarIdent>,
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
        ident: VarIdent,
        init_ref: Option<VarIdent>,
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

    fn handle_ptr_instruction(&mut self, instr: PointerInstruction, context: PointerContext<'a>) {
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
                    name: String::from(fun_name).into(),
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

pub fn cell_is_in_function(cell: &Cell, function: &str) -> bool {
    match cell {
        Cell::Var(ident) | Cell::Return(ident) | Cell::Stack(ident) | Cell::Heap(ident) => {
            ident_is_in_function(ident, function)
        }
        Cell::Global(_) => false,
    }
}

fn ident_is_in_function(ident: &VarIdent, function: &str) -> bool {
    match ident {
        VarIdent::Local { fun_name, .. } => fun_name.as_ref() == function,
        VarIdent::Offset { base, .. } => ident_is_in_function(base.as_ref(), function),
        VarIdent::Global { .. } => false,
        VarIdent::Fresh { .. } => false,
    }
}
