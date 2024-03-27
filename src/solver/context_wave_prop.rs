use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;
use std::marker::PhantomData;
use std::mem;
use std::rc::Rc;

use bitvec::bitvec;
use bitvec::prelude::*;
use hashbrown::{HashMap, HashSet};
use once_cell::unsync::Lazy;
use roaring::RoaringBitmap;

use super::shared_bitvec::SharedBitVec;
use super::{
    edges_between, BetterBitVec, CallSite, Constraint, ContextSelector, ContextSensitiveInput,
    FunctionInput, IntegerTerm, Solver, SolverSolution, TermSetTrait, TermType,
};
use crate::solver::GenericIdMap;
use crate::visualizer::{Edge, EdgeKind, Graph, Node, OffsetWeight};

#[derive(Clone)]
struct CondLeftEntry<C> {
    cond_node: IntegerTerm,
    right: IntegerTerm,
    offset: usize,
    call_site: Option<CallSite>,
    context: C,
}

#[derive(Clone)]
struct CondRightEntry<C> {
    cond_node: IntegerTerm,
    left: IntegerTerm,
    offset: usize,
    call_site: Option<CallSite>,
    context: C,
}

#[derive(Clone)]
struct CallDummyEntry<C> {
    cond_node: IntegerTerm,
    call_site: CallSite,
    context: C,
}

#[derive(Clone)]
enum TemplateTerm {
    Internal(u32),
    Global(u32),
}

struct TemplateSentinelInfo {
    pointer_node: IntegerTerm,
    term_type: TermType,
}

#[derive(Clone)]
struct FunctionTemplate {
    _fun_name: Rc<str>,
    start_index: u32,
    types: Vec<TermType>,
    constraints: Vec<Constraint<TemplateTerm>>,
    function_node_index: u32,
}

#[derive(Clone)]
pub struct ContextWavePropagationSolver<S, C>(PhantomData<S>, PhantomData<C>);

impl<S, C> ContextWavePropagationSolver<S, C> {
    pub fn new() -> Self {
        Self(PhantomData, PhantomData)
    }
}

pub struct ContextWavePropagationSolverState<T, S, C: ContextSelector> {
    mapping: GenericIdMap<T>,
    context_selector: C,
    templates: Vec<FunctionTemplate>,
    instantiated_contexts: Vec<HashMap<C::Context, IntegerTerm>>,
    sentinel_functions: HashMap<IntegerTerm, u32>,
    edges: Edges<S, C>,
    term_types: Vec<TermType>,
    parents: Vec<IntegerTerm>,
    top_order: Vec<IntegerTerm>,
    /// Maps from concrete (instantiated) terms to their abstract term.
    abstract_indices: Vec<IntegerTerm>,
}

impl<T, S, C: ContextSelector> ContextWavePropagationSolverState<T, S, C> {
    fn term_count(&self) -> usize {
        self.edges.sols.len()
    }
}

impl<T, S, C> ContextWavePropagationSolverState<T, S, C>
where
    C: ContextSelector,
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = u32>,
{
    fn run_wave_propagation(&mut self) {
        SCC::run(self).apply_to_graph(self);

        let mut iters = 0usize;

        let mut changed = true;
        while changed {
            iters += 1;
            SCC::run(self).apply_to_graph(self);
            SCC::run_with_weighted(self).apply_to_graph_weighted(self);

            let mut nodes_with_new_outgoing = S::new();

            changed = self.wave_propagate_iteration();

            changed |= self.add_edges_after_wave_prop(&mut nodes_with_new_outgoing);
        }
        println!("SCC count: {}", self.top_order.len());
        println!("Iterations: {}", iters);
    }

    fn wave_propagate_iteration(&mut self) -> bool {
        let mut changed = false;
        for &v in self.top_order.iter().rev() {
            // Skip if no new terms in solution set
            if self.edges.sols[v as usize].len() == self.edges.p_old[v as usize].len() {
                continue;
            }
            changed = true;
            let p_dif = self.edges.sols[v as usize].weak_difference(&self.edges.p_old[v as usize]);
            let p_dif_vec = Lazy::new(|| p_dif.iter().collect::<Vec<IntegerTerm>>());
            self.edges.p_old[v as usize].clone_from(&self.edges.sols[v as usize]);

            for (&w, offsets) in &self.edges.subset[v as usize] {
                for o in offsets.iter() {
                    propagate_terms_into(
                        &p_dif,
                        p_dif_vec.iter().copied(),
                        o,
                        &mut self.edges.sols[w as usize],
                        &self.term_types,
                    );
                }
            }
        }
        changed
    }

    fn add_edges_after_wave_prop(&mut self, nodes_with_new_outgoing: &mut S) -> bool {
        let mut changed = false;
        let call_dummies = self.edges.call_dummies.clone();
        for (
            i,
            CallDummyEntry {
                cond_node,
                call_site,
                context,
            },
        ) in call_dummies.into_iter().enumerate()
        {
            let cond_node = get_representative(&mut self.parents, cond_node);

            if self.edges.sols[cond_node as usize].len() == self.edges.p_cache_call_dummies[i].len()
            {
                continue;
            }
            let p_new =
                self.edges.sols[cond_node as usize].difference(&self.edges.p_cache_call_dummies[i]);
            self.edges.p_cache_call_dummies[i].union_assign(&p_new);
            for t in p_new.iter() {
                self.offset_term_vec_offsets(t, Some(call_site.clone()), 0, &context);
            }
        }
        let left_conds = self.edges.left_conds.clone();
        for (
            i,
            CondLeftEntry {
                cond_node,
                right,
                offset,
                call_site,
                context,
            },
        ) in left_conds.into_iter().enumerate()
        {
            let cond_node = get_representative(&mut self.parents, cond_node);
            let right = get_representative(&mut self.parents, right);

            if self.edges.sols[cond_node as usize].len() == self.edges.p_cache_left[i].len() {
                continue;
            }
            let p_new = self.edges.sols[cond_node as usize].difference(&self.edges.p_cache_left[i]);
            self.edges.p_cache_left[i].union_assign(&p_new);
            for t in p_new.iter() {
                if let Some(t) =
                    self.offset_term_vec_offsets(t, call_site.clone(), offset, &context)
                {
                    let t = get_representative(&mut self.parents, t);
                    if t == right {
                        continue;
                    }
                    if edges_between(&mut self.edges.subset, t, right).insert(0) {
                        self.edges.sols[right as usize].union_assign(&self.edges.p_old[t as usize]);
                        self.edges.rev_subset[right as usize].insert(t);
                        changed = true;
                        nodes_with_new_outgoing.insert(t);
                    }
                }
            }
        }
        let right_conds = self.edges.right_conds.clone();
        for (
            i,
            CondRightEntry {
                cond_node,
                left,
                offset,
                call_site,
                context,
            },
        ) in right_conds.into_iter().enumerate()
        {
            let cond_node = get_representative(&mut self.parents, cond_node);
            let left = get_representative(&mut self.parents, left);

            if self.edges.sols[cond_node as usize].len() == self.edges.p_cache_right[i].len() {
                continue;
            }
            let p_new =
                self.edges.sols[cond_node as usize].difference(&self.edges.p_cache_right[i]);
            self.edges.p_cache_right[i].union_assign(&p_new);
            for t in p_new.iter() {
                if let Some(t) =
                    self.offset_term_vec_offsets(t, call_site.clone(), offset, &context)
                {
                    let t = get_representative(&mut self.parents, t);
                    if t == left {
                        continue;
                    }
                    if edges_between(&mut self.edges.subset, left, t).insert(0) {
                        self.edges.sols[t as usize].union_assign(&self.edges.p_old[left as usize]);
                        self.edges.rev_subset[t as usize].insert(left);
                        changed = true;
                        nodes_with_new_outgoing.insert(t);
                    }
                }
            }
        }
        changed
    }

    fn offset_term_vec_offsets(
        &mut self,
        term: IntegerTerm,
        call_site: Option<CallSite>,
        offset: usize,
        context: &C::Context,
    ) -> Option<IntegerTerm> {
        let term_type = self.term_types[usize::try_from(term).unwrap()];
        match term_type {
            TermType::Basic if call_site.is_none() && offset == 0 => Some(term),
            TermType::Struct(allowed) if call_site.is_none() => {
                (offset <= allowed).then(|| term + offset as IntegerTerm)
            }
            TermType::Function(allowed, func_type) => {
                let Some(call_site) = call_site else {
                    return None;
                };
                // if func_type != call_site.0.func_type_index {
                //     return None;
                // }
                let new_context = self.context_selector.select_context(context, call_site);
                let f_index = *self
                    .sentinel_functions
                    .get(&term)
                    .expect("sentinel should have a function")
                    as usize;
                let function_term = self.get_or_instantiate_function(f_index, new_context);
                (offset <= allowed).then(|| function_term + offset as IntegerTerm)
            }
            _ => None,
        }
    }

    fn get_or_instantiate_function(&mut self, f_index: usize, context: C::Context) -> IntegerTerm {
        let template = &self.templates[f_index];
        if let Some(start_index) = self.instantiated_contexts[f_index].get(&context) {
            return *start_index + template.function_node_index;
        }

        let instantiated_start_index = self.term_count();
        let num_instantiated = template.types.len();
        let new_len = instantiated_start_index + num_instantiated;
        self.edges.sols.resize_with(new_len, S::new);
        self.edges.subset.resize_with(new_len, HashMap::new);
        self.edges.rev_subset.resize_with(new_len, HashSet::new);
        self.term_types.extend_from_slice(&template.types);
        self.parents
            .extend((0..num_instantiated).map(|i| (instantiated_start_index + i) as IntegerTerm));
        self.abstract_indices
            .extend((0..num_instantiated).map(|i| template.start_index + i as u32));
        self.edges.p_old.resize_with(new_len, S::new);

        for constraint in &template.constraints {
            let concrete_constraint = constraint.map_terms(|tt| match tt {
                &TemplateTerm::Internal(index) => instantiated_start_index as IntegerTerm + index,
                &TemplateTerm::Global(index) => index,
            });
            self.edges
                .add_constraint(concrete_constraint.clone(), context.clone());

            if let Constraint::Subset {
                left: TemplateTerm::Global(_),
                ..
            } = constraint
            {
                // If we add a subset edge from a global node, we need to propagate along it immediately,
                // so the destination node will be marked as changed.
                let Constraint::Subset {
                    left,
                    right,
                    offset,
                } = concrete_constraint
                else {
                    unreachable!();
                };
                let left_sols = self.edges.sols[left as usize].clone();
                let left_sols_iter = left_sols.iter();
                let right_sols = &mut self.edges.sols[right as usize];
                propagate_terms_into(
                    &left_sols,
                    left_sols_iter,
                    offset,
                    right_sols,
                    &self.term_types,
                );
            }
        }
        self.instantiated_contexts[f_index]
            .insert(context, instantiated_start_index as IntegerTerm);

        instantiated_start_index as IntegerTerm + template.function_node_index
    }

    fn get_function_and_relative_index_from_term(
        &self,
        term: &T,
    ) -> (Option<IntegerTerm>, IntegerTerm) {
        let abstract_index = self.mapping.term_to_integer(term);

        self.get_function_and_relative_index_from_abstract_index(abstract_index)
    }

    fn get_function_and_relative_index_from_abstract_index(
        &self,
        abstract_index: IntegerTerm,
    ) -> (Option<IntegerTerm>, IntegerTerm) {
        let fun_index = match self
            .templates
            .binary_search_by_key(&abstract_index, |t| t.start_index)
        {
            Ok(i) => Some(i),
            Err(i) => i.checked_sub(1),
        };

        // If global term
        match fun_index {
            Some(i) => (
                Some(i as IntegerTerm),
                abstract_index - self.templates[i].start_index,
            ),
            None => (None, abstract_index),
        }
    }

    fn context_of_concrete_index(&self, index: IntegerTerm) -> C::Context {
        if self.sentinel_functions.contains_key(&index) {
            return self.context_selector.empty();
        }

        let abstract_index = self.abstract_indices[index as usize];

        let (fun_index, relative_index) =
            self.get_function_and_relative_index_from_abstract_index(abstract_index);

        match fun_index {
            Some(i) => {
                let start_index = index - relative_index;
                self.instantiated_contexts[i as usize]
                    .iter()
                    .find(|(_, i)| **i == start_index)
                    .expect("there should be an instantiated context")
                    .0
                    .clone()
            }
            None => self.context_selector.empty(),
        }
    }

    fn concrete_to_input(&self, term: IntegerTerm) -> T {
        self.mapping
            .integer_to_term(self.abstract_indices[term as usize])
    }
}

fn propagate_terms_into<S: TermSetTrait<Term = IntegerTerm>>(
    term_set: &S,
    term_set_iter: impl IntoIterator<Item = IntegerTerm>,
    offset: usize,
    dest_term_set: &mut S,
    term_types: &[TermType],
) {
    if offset == 0 {
        dest_term_set.union_assign(term_set);
    } else {
        let to_add = term_set_iter.into_iter().filter_map(|t| {
            if let TermType::Struct(allowed) = term_types[t as usize] {
                (offset <= allowed).then(|| t + offset as IntegerTerm)
            } else {
                None
            }
        });
        dest_term_set.extend(to_add);
    }
}

fn function_to_template<T>(
    function: &FunctionInput<T>,
    mapping: &GenericIdMap<T>,
) -> (FunctionTemplate, TemplateSentinelInfo)
where
    T: Hash + Eq + Clone + Debug,
{
    let FunctionInput {
        fun_name,
        constrained_terms,
    } = function;

    let start_index = mapping.term_to_integer(&constrained_terms.terms[0]);

    let mut types = vec![TermType::Basic; constrained_terms.terms.len()];

    for (t, tt) in &constrained_terms.term_types {
        types[(mapping.term_to_integer(&t) - start_index) as usize] = *tt;
    }

    let function_terms_set: HashSet<_> = constrained_terms
        .terms
        .iter()
        .map(|t| mapping.term_to_integer(t))
        .collect();

    let mut constraints = vec![];
    let mut sentinel_info_and_function_node = None;

    for c in &constrained_terms.constraints {
        if let Constraint::Inclusion { term, node } = &c {
            let abstract_index = mapping.term_to_integer(term);
            if function_terms_set.contains(&abstract_index) {
                let relative_index = abstract_index - start_index;
                let term_type = types[relative_index as usize];
                if matches!(term_type, TermType::Function(_, _)) {
                    if sentinel_info_and_function_node.is_some() {
                        panic!("Multiple function terms found");
                    }
                    sentinel_info_and_function_node = Some((
                        TemplateSentinelInfo {
                            pointer_node: mapping.term_to_integer(node),
                            term_type,
                        },
                        relative_index,
                    ));
                    continue;
                }
            }
        }
        constraints.push(c.map_terms(|t| {
            let index = mapping.term_to_integer(t);
            if function_terms_set.contains(&index) {
                TemplateTerm::Internal(index - start_index)
            } else {
                TemplateTerm::Global(index)
            }
        }));
    }

    let (sentinel, function_node_index) =
        sentinel_info_and_function_node.expect("No function term found");

    (
        FunctionTemplate {
            _fun_name: fun_name.clone(),
            start_index,
            types,
            constraints,
            function_node_index,
        },
        sentinel,
    )
}

impl<T, S, C> Solver<ContextSensitiveInput<T, C>> for ContextWavePropagationSolver<S, C>
where
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = IntegerTerm>,
    C: ContextSelector,
{
    type Solution = ContextWavePropagationSolverState<T, S, C>;

    fn solve(self, input: ContextSensitiveInput<T, C>) -> Self::Solution {
        let terms = input
            .global
            .terms
            .iter()
            .chain(
                input
                    .functions
                    .iter()
                    .flat_map(|t| &t.constrained_terms.terms),
            )
            .cloned()
            .collect();
        let mapping = GenericIdMap::new(terms);

        let mut sols = vec![S::new(); input.global.terms.len()];
        let mut subset: Vec<HashMap<IntegerTerm, Offsets>> =
            vec![HashMap::new(); input.global.terms.len()];
        let mut rev_subset = vec![HashSet::new(); input.global.terms.len()];
        let instantiated_contexts = vec![HashMap::new(); input.functions.len()];
        let mut abstract_indices = Vec::with_capacity(mapping.terms.len());
        abstract_indices.extend(0..input.global.terms.len() as IntegerTerm);

        let mut term_types = vec![TermType::Basic; input.global.terms.len()];
        for (t, tt) in &input.global.term_types {
            let abstract_term = mapping.term_to_integer(t);
            term_types[abstract_term as usize] = *tt;
        }

        let mut templates = Vec::with_capacity(input.functions.len());
        let mut sentinel_functions = HashMap::new();

        for (i, (template, sentinel_info)) in input
            .functions
            .iter()
            .map(|f| function_to_template(f, &mapping))
            .enumerate()
        {
            let sentinel_index = sols.len() as IntegerTerm;
            sols.push(S::new());
            term_types.push(sentinel_info.term_type);
            sols[sentinel_info.pointer_node as usize].insert(sentinel_index);
            subset.push(HashMap::new());
            rev_subset.push(HashSet::new());
            abstract_indices
                .push(template.start_index + template.function_node_index as IntegerTerm);

            templates.push(template);
            sentinel_functions.insert(sentinel_index, i as IntegerTerm);
        }
        let parents = Vec::from_iter(0..sols.len() as IntegerTerm);
        let top_order = Vec::new();

        let empty_context = input.context_selector.empty();

        let left_conds = vec![];
        let right_conds = vec![];
        let call_dummies = vec![];
        let p_old = vec![S::new(); sols.len()];
        let p_cache_left = vec![S::new(); left_conds.len()];
        let p_cache_right = vec![S::new(); right_conds.len()];
        let p_cache_call_dummies = vec![];
        let mut state = ContextWavePropagationSolverState {
            mapping,
            context_selector: input.context_selector,
            templates,
            instantiated_contexts,
            sentinel_functions,
            edges: Edges {
                sols,
                subset,
                rev_subset,
                left_conds,
                right_conds,
                call_dummies,
                p_old,
                p_cache_left,
                p_cache_right,
                p_cache_call_dummies,
            },
            term_types,
            parents,
            top_order,
            abstract_indices,
        };

        for c in input.global.constraints {
            state.edges.add_constraint(
                state.mapping.translate_constraint(&c),
                empty_context.clone(),
            );
        }

        for entrypoint in input.entrypoints {
            state.get_or_instantiate_function(entrypoint, empty_context.clone());
        }

        state.run_wave_propagation();

        println!(
            "Max: {}",
            state.edges.sols.iter().map(|s| s.len()).max().unwrap()
        );
        println!(
            "Mean: {}",
            state.edges.sols.iter().map(|s| s.len() as f64).sum::<f64>()
                / state.term_count() as f64
        );
        println!(
            "Median: {}",
            state
                .edges
                .sols
                .iter()
                .map(|s| s.len())
                .collect::<Vec<usize>>()
                .select_nth_unstable(state.term_count() / 2)
                .1
        );

        state
    }
}

impl<T, S, C> SolverSolution for ContextWavePropagationSolverState<T, S, C>
where
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = IntegerTerm>,
    C: ContextSelector,
{
    type Term = T;
    type TermSet = HashSet<T>;

    fn get(&self, term: &T) -> Self::TermSet {
        let (fun_index, relative_index) = self.get_function_and_relative_index_from_term(term);

        match fun_index {
            Some(i) => self.instantiated_contexts[i as usize]
                .iter()
                .flat_map(|(_, start_index)| {
                    let concrete_index = start_index + relative_index;
                    self.edges.sols
                        [get_representative_no_mutation(&self.parents, concrete_index) as usize]
                        .iter()
                })
                .map(|concrete_index| self.concrete_to_input(concrete_index))
                .collect(),
            None => self.edges.sols
                [get_representative_no_mutation(&self.parents, relative_index) as usize as usize]
                .iter()
                .map(|concrete_index| self.concrete_to_input(concrete_index))
                .collect(),
        }
    }
}

struct Edges<S, C: ContextSelector> {
    sols: Vec<S>,
    subset: Vec<HashMap<IntegerTerm, Offsets>>,
    rev_subset: Vec<HashSet<IntegerTerm>>,
    left_conds: Vec<CondLeftEntry<C::Context>>,
    right_conds: Vec<CondRightEntry<C::Context>>,
    call_dummies: Vec<CallDummyEntry<C::Context>>,
    p_old: Vec<S>,
    p_cache_left: Vec<S>,
    p_cache_right: Vec<S>,
    p_cache_call_dummies: Vec<S>,
}

impl<S, C> Edges<S, C>
where
    S: TermSetTrait<Term = IntegerTerm>,
    C: ContextSelector,
{
    fn add_constraint(&mut self, c: Constraint<IntegerTerm>, context: C::Context) {
        match c {
            Constraint::Inclusion { term, node } => {
                self.sols[node as usize].insert(term);
            }
            Constraint::Subset {
                left,
                right,
                offset,
            } => {
                self.add_edge(left, right, offset);
            }
            Constraint::UnivCondSubsetLeft {
                cond_node,
                right,
                offset,
                call_site,
            } => {
                self.left_conds.push(CondLeftEntry {
                    cond_node,
                    right,
                    offset,
                    call_site,
                    context,
                });
                self.p_cache_left.push(S::new());
            }
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
                call_site,
            } => {
                self.right_conds.push(CondRightEntry {
                    cond_node,
                    left,
                    offset,
                    call_site,
                    context,
                });
                self.p_cache_right.push(S::new());
            }
            Constraint::CallDummy {
                cond_node,
                call_site,
            } => {
                self.call_dummies.push(CallDummyEntry {
                    cond_node,
                    call_site,
                    context,
                });
                self.p_cache_call_dummies.push(S::new());
            }
        };
    }

    fn add_edge(&mut self, left: IntegerTerm, right: IntegerTerm, offset: usize) -> bool {
        let res = edges_between(&mut self.subset, left, right).insert(offset);
        if res {
            self.rev_subset[right as usize].insert(left);
        }
        res
    }
}

#[derive(Clone, Default)]
struct Offsets {
    zero: bool,
    offsets: Vec<usize>,
}

impl Offsets {
    fn contains(&self, offset: usize) -> bool {
        if offset == 0 {
            return self.zero;
        }
        return self.offsets.contains(&offset);
    }

    fn insert(&mut self, offset: usize) -> bool {
        if offset == 0 {
            if !self.zero {
                self.zero = true;
                true
            } else {
                false
            }
        } else {
            match self.offsets.binary_search(&offset) {
                Ok(_) => false,
                Err(i) => {
                    self.offsets.insert(i, offset);
                    true
                }
            }
        }
    }

    fn union_assign(&mut self, other: &Self) {
        self.zero = other.zero;
        for offset in &other.offsets {
            self.insert(*offset);
        }
    }

    fn len(&self) -> usize {
        self.zero as usize + self.offsets.len()
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.zero
            .then_some(0)
            .into_iter()
            .chain(self.offsets.iter().copied())
    }
}

struct SCC<T, S, C> {
    iterative: bool,
    node_count: usize,
    iteration: usize,
    /// 0 means not visited.
    d: Vec<usize>,
    r: Vec<Option<IntegerTerm>>,
    c: BitVec,
    s: Vec<IntegerTerm>,
    top_order: Vec<IntegerTerm>,
    term_phantom: PhantomData<T>,
    term_set_type_phantom: PhantomData<S>,
    context_selector_phantom: PhantomData<C>,
}

impl<T, S, C> SCC<T, S, C>
where
    S: TermSetTrait<Term = IntegerTerm> + Default + Clone,
    C: ContextSelector,
{
    fn visit(&mut self, v: IntegerTerm, solver: &ContextWavePropagationSolverState<T, S, C>) {
        self.iteration += 1;
        self.d[v as usize] = self.iteration;
        self.r[v as usize] = Some(v);
        if solver.edges.subset[v as usize].is_empty() {
            self.c.set(v as usize, true);
            return;
        }

        for (&w, offsets) in &solver.edges.subset[v as usize] {
            if !offsets.contains(0) {
                continue;
            }

            if self.d[w as usize] == 0 {
                self.visit(w, solver);
            }
            if !self.c[w as usize] {
                let r_v = self.r[v as usize].unwrap();
                let r_w = self.r[w as usize].unwrap();
                self.r[v as usize] = Some(if self.d[r_v as usize] < self.d[r_w as usize] {
                    r_v
                } else {
                    r_w
                });
            }
        }

        if self.r[v as usize] == Some(v) {
            self.c.set(v as usize, true);
            while let Some(&w) = self.s.last() {
                if self.d[w as usize] <= self.d[v as usize] {
                    break;
                }
                self.s.pop();
                self.c.set(w as usize, true);
                self.r[w as usize] = Some(v);
            }
            self.top_order.push(v);
        } else {
            self.s.push(v);
        }
    }

    fn dfs_add_and_finish(
        &mut self,
        v: IntegerTerm,
        solver: &ContextWavePropagationSolverState<T, S, C>,
    ) {
        if self.c[v as usize] {
            return;
        }

        self.c.set(v as usize, true);

        for (&w, offsets) in &solver.edges.subset[v as usize] {
            if !offsets.contains(0) || self.r[v as usize] != self.r[w as usize] {
                continue;
            }

            self.dfs_add_and_finish(w, solver);
        }

        self.top_order.push(v);
    }

    fn visit_with_weighted(
        &mut self,
        v: IntegerTerm,
        state: &ContextWavePropagationSolverState<T, S, C>,
    ) {
        self.iteration += 1;
        self.d[v as usize] = self.iteration;
        self.r[v as usize] = Some(v);
        if state.edges.subset[v as usize].is_empty() {
            self.c.set(v as usize, true);
            return;
        }

        for (&w, offsets) in &state.edges.subset[v as usize] {
            debug_assert!(offsets.len() > 0);

            if self.d[w as usize] == 0 {
                self.visit_with_weighted(w, state);
            }
            if !self.c[w as usize] {
                let r_v = self.r[v as usize].unwrap();
                let r_w = self.r[w as usize].unwrap();
                self.r[v as usize] = Some(if self.d[r_v as usize] < self.d[r_w as usize] {
                    r_v
                } else {
                    r_w
                });
            }
        }
        if self.r[v as usize] == Some(v) {
            for &w in self.s.iter().rev() {
                if self.d[w as usize] <= self.d[v as usize] {
                    break;
                }
                self.r[w as usize] = Some(v);
            }
            while let Some(&w) = self.s.last() {
                if self.d[w as usize] <= self.d[v as usize] {
                    break;
                }
                self.s.pop();
                self.dfs_add_and_finish(w, state);
            }
            self.dfs_add_and_finish(v, state);
        } else {
            self.s.push(v);
        }
    }

    fn init_result(iterative: bool, state: &ContextWavePropagationSolverState<T, S, C>) -> Self {
        let node_count = state.term_count();
        Self {
            iterative,
            node_count,
            iteration: 0,
            d: vec![0; node_count],
            r: vec![None; node_count],
            c: bitvec![0; node_count],
            s: vec![],
            top_order: vec![],
            term_phantom: PhantomData,
            term_set_type_phantom: PhantomData,
            context_selector_phantom: PhantomData,
        }
    }

    fn run(solver: &mut ContextWavePropagationSolverState<T, S, C>) -> Self {
        let mut result = SCC::init_result(false, solver);
        for v in 0..result.node_count as u32 {
            if result.d[v as usize] == 0 {
                result.visit(v, solver);
            }
        }
        result
    }

    fn run_with_weighted(solver: &mut ContextWavePropagationSolverState<T, S, C>) -> Self {
        let mut result = SCC::init_result(false, solver);
        for v in 0..result.node_count as u32 {
            if result.d[v as usize] == 0 {
                result.visit_with_weighted(v, solver);
            }
        }

        result
    }

    fn unify(
        &self,
        child: IntegerTerm,
        parent: IntegerTerm,
        state: &mut ContextWavePropagationSolverState<T, S, C>,
    ) {
        debug_assert_ne!(child, parent);

        let child_sols = mem::take(&mut state.edges.sols[child as usize]);
        state.edges.sols[parent as usize].union_assign(&child_sols);

        let child_edges = mem::take(&mut state.edges.subset[child as usize]);

        for (&other, offsets) in &child_edges {
            debug_assert_ne!(0, offsets.len());

            let other = if other == child { parent } else { other };

            state.edges.subset[parent as usize]
                .entry(other)
                .or_default()
                .union_assign(&offsets);
            // Self::do_remove_stuff(&mut solver.rev_edges, other, child);
            // solver.num_removes += 1;
            state.edges.rev_subset[other as usize].remove(&child);
            state.edges.rev_subset[other as usize].insert(parent);
        }
        let child_rev_edges = mem::take(&mut state.edges.rev_subset[child as usize]);
        for &i in child_rev_edges.iter() {
            if i == child {
                continue;
            }
            match state.edges.subset[i as usize].remove(&child) {
                Some(orig_edges) => {
                    state.edges.subset[i as usize]
                        .entry(parent)
                        .or_default()
                        .union_assign(&orig_edges);
                }
                None => {
                    panic!("Expected edges from {i} to {child}");
                }
            }
        }

        state.edges.rev_subset[parent as usize].union_assign(&child_rev_edges);

        if state.edges.rev_subset[parent as usize].remove(&(child as IntegerTerm)) {
            state.edges.rev_subset[parent as usize].insert(parent as IntegerTerm);
        }

        state.parents[child as usize] = parent;
    }

    // Collapse cycles and update topological order
    fn apply_to_graph(self, state: &mut ContextWavePropagationSolverState<T, S, C>) {
        let mut removed = HashSet::new();
        for v in 0..self.node_count as u32 {
            if let Some(r_v) = self.r[v as usize] {
                if r_v != v {
                    self.unify(v, r_v, state);
                    if self.iterative {
                        removed.insert(v);
                    }
                }
            }
        }
        if self.iterative {
            if !removed.is_empty() {
                state.top_order = state
                    .top_order
                    .iter()
                    .copied()
                    .filter(|node| !removed.contains(node))
                    .collect()
            }
        } else {
            state.top_order = self.top_order;
        }
    }

    // Collapse cycles and update topological order
    fn apply_to_graph_weighted(self, solver: &mut ContextWavePropagationSolverState<T, S, C>) {
        solver.top_order = self.top_order;
    }
}

fn get_representative_no_mutation(parents: &Vec<IntegerTerm>, child: IntegerTerm) -> IntegerTerm {
    let mut node = child;
    loop {
        let parent = parents[child as usize];
        if parent == node {
            return node;
        }
        node = parent;
    }
}

fn get_representative(parents: &mut Vec<IntegerTerm>, child: IntegerTerm) -> IntegerTerm {
    let parent = parents[child as usize];
    if parent == child {
        return child;
    }
    let representative = get_representative(parents, parent);
    parents[child as usize] = representative;
    representative
}

pub type HashContextWavePropagationSolver<C> =
    ContextWavePropagationSolver<HashSet<IntegerTerm>, C>;
pub type RoaringContextWavePropagationSolver<C> = ContextWavePropagationSolver<RoaringBitmap, C>;
pub type BetterBitVecContextWavePropagationSolver<C> =
    ContextWavePropagationSolver<BetterBitVec, C>;
pub type SharedBitVecContextWavePropagationSolver<C> =
    ContextWavePropagationSolver<SharedBitVec, C>;

#[derive(Clone)]
pub struct ContextWavePropagationNode<T, C> {
    term: T,
    context: C,
    count: usize,
}

impl<T: Display, C: Display> Display for ContextWavePropagationNode<T, C> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}: {} ({})", self.context, self.term, self.count)
    }
}

impl<T, S, C> ContextWavePropagationSolverState<T, S, C>
where
    T: Display + Debug + Clone + PartialEq + Eq + Hash,
    S: TermSetTrait<Term = IntegerTerm>,
    C: ContextSelector,
{
    fn get_representative_counts(&self) -> HashMap<IntegerTerm, Node<usize>> {
        let mut reps = HashMap::new();
        for n in 0..self.edges.sols.len() {
            let rep = get_representative_no_mutation(&self.parents, n as IntegerTerm);
            reps.entry(rep)
                .or_insert(Node {
                    inner: 0,
                    id: rep as usize,
                })
                .inner += 1;
        }
        reps
    }
}

impl<T, S, C> Graph for ContextWavePropagationSolverState<T, S, C>
where
    T: Display + Debug + Clone + PartialEq + Eq + Hash,
    S: TermSetTrait<Term = IntegerTerm>,
    C: ContextSelector,
    C::Context: Display,
{
    type Node = ContextWavePropagationNode<T, C::Context>;
    type Weight = OffsetWeight;

    fn nodes(&self) -> Vec<Node<Self::Node>> {
        let reps = self.get_representative_counts();
        reps.into_iter()
            .map(|(t, node)| {
                let inner = ContextWavePropagationNode {
                    term: self.concrete_to_input(t),
                    context: self.context_of_concrete_index(t),
                    count: node.inner,
                };
                Node { inner, id: node.id }
            })
            .collect()
    }

    fn edges(&self) -> Vec<Edge<Self::Node, Self::Weight>> {
        let mut edges = vec![];

        let reps = self.get_representative_counts();
        for (from, outgoing) in self.edges.subset.iter().enumerate() {
            if outgoing.is_empty() {
                continue;
            }

            let inner = ContextWavePropagationNode {
                term: self.concrete_to_input(from as IntegerTerm),
                context: self.context_of_concrete_index(from as IntegerTerm),
                count: reps.get(&(from as u32)).unwrap().inner,
            };
            let from_node = Node { inner, id: from };

            for (to, weights) in outgoing {
                let inner = ContextWavePropagationNode {
                    term: self.concrete_to_input(*to as IntegerTerm),
                    context: self.context_of_concrete_index(*to as IntegerTerm),
                    count: reps.get(to).unwrap().inner,
                };
                let to_node = Node {
                    inner,
                    id: *to as usize,
                };

                for weight in weights.iter() {
                    let edge = Edge {
                        from: from_node.clone(),
                        to: to_node.clone(),
                        weight: OffsetWeight(weight as IntegerTerm),
                        kind: EdgeKind::Subset,
                    };
                    edges.push(edge);
                }
            }
        }

        // for from in reps.keys().copied() {
        //     let inner = WavePropagationNode {
        //         term: self.t2_to_term(from),
        //         count: reps.get(&from).unwrap().inner,
        //     };
        //     let from_node = Node {
        //         inner,
        //         id: from as usize,
        //     };
        //     for to in self.sub_solver.get_solution(&from).iter() {
        //         if get_representative_no_mutation(&self.sub_solver.parents, to) != to {
        //             continue;
        //         }
        //         let inner = WavePropagationNode {
        //             term: self.t2_to_term(to),
        //             count: reps.get(&to).unwrap().inner,
        //         };
        //         let to_node = Node {
        //             inner,
        //             id: to as usize,
        //         };
        //         let edge = Edge {
        //             from: from_node.clone(),
        //             to: to_node.clone(),
        //             weight: OffsetWeight(0),
        //             kind: EdgeKind::Inclusion,
        //         };
        //         edges.push(edge);
        //     }
        // }

        edges
    }
}
