use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;
use std::marker::PhantomData;
use std::time::Duration;
use std::{iter, mem};

use either::Either;
use hashbrown::hash_map::Entry;
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use once_cell::unsync::Lazy;
use roaring::RoaringBitmap;
use serde::Serialize;
use thin_vec::ThinVec;

use super::context::{ContextState, TemplateTerm};
use super::rc_termset::RcTermSet;
use super::scc::{SccEdges, SccGraph};
use super::shared_bitvec::SharedBitVec;
use super::{
    insert_edge, try_offset_term, CallSite, Constraint, ContextSelector, ContextSensitiveInput,
    IntegerTerm, Offsets, OnlyOnceStack, Solver, SolverExt, SolverSolution, TermSetTrait, TermType,
};
use crate::solver::scc::scc;
use crate::util::GetManyMutExt;
use crate::visualizer::{Edge, EdgeKind, Graph, Node, OffsetWeight};

#[derive(Clone, Debug)]
enum CondEntry<C> {
    Left {
        right: IntegerTerm,
        offset: usize,
        call_site: Option<CallSite>,
        context: C,
    },
    Right {
        left: IntegerTerm,
        offset: usize,
        call_site: Option<CallSite>,
        context: C,
    },
    CallDummy {
        call_site: CallSite,
        context: C,
    },
}

#[derive(Debug)]
struct CachedCondEntry<C, S> {
    entry: CondEntry<C>,
    cache: S,
}
impl<C, S: TermSetTrait> CachedCondEntry<C, S> {
    fn new(entry: CondEntry<C>) -> Self {
        Self {
            entry,
            cache: S::new(),
        }
    }
}

#[derive(Clone)]
pub struct WavePropagationSolver<S, C>(PhantomData<S>, PhantomData<C>, bool);

impl<S, C> WavePropagationSolver<S, C> {
    pub fn new() -> Self {
        Self(PhantomData, PhantomData, false)
    }
    pub fn new_with_aggressive_dedup() -> Self {
        Self(PhantomData, PhantomData, true)
    }
}

pub struct WavePropagationSolverState<T, S, C: ContextSelector> {
    context_state: ContextState<T, C>,
    edges: Edges<S, C>,
    term_types: Vec<TermType>,
    parents: Vec<IntegerTerm>,
    new_incoming: Vec<IntegerTerm>,
    iters: u64,
    scc_time: Duration,
    propagation_time: Duration,
    edge_instantiation_time: Duration,
    aggressive_dedup: bool,
}

impl<T, S, C> WavePropagationSolverState<T, S, C>
where
    C: ContextSelector + Clone,
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = u32> + Debug,
{
    fn run_wave_propagation(&mut self) {
        let mut changed = true;
        while changed {
            self.iters += 1;

            let scc_start = std::time::Instant::now();
            let top_order = scc(&self.edges, mem::take(&mut self.new_incoming), |_, _| {})
                .collapse_cycles(self)
                .into_top_order();
            self.scc_time += scc_start.elapsed();

            let propagation_start = std::time::Instant::now();
            changed = self.wave_propagate_iteration(&top_order);
            self.propagation_time += propagation_start.elapsed();

            let edge_instantiation_start = std::time::Instant::now();
            changed |= self.add_edges_after_wave_prop(&top_order);
            self.edge_instantiation_time += edge_instantiation_start.elapsed();

            if self.aggressive_dedup {
                self.deduplicate(&top_order);
            }

            eprintln!("Iteration {}", self.iters);
        }
    }

    fn wave_propagate_iteration(&mut self, top_order: &[IntegerTerm]) -> bool {
        let mut changed = false;
        for &v in top_order.iter().rev() {
            // Skip if no new terms in solution set
            if self.edges.sols[v as usize].len() == self.edges.p_old[v as usize].len() {
                continue;
            }
            changed = true;
            let p_dif = self.edges.sols[v as usize].weak_difference(&self.edges.p_old[v as usize]);
            let p_dif_vec = Lazy::new(|| p_dif.iter().collect::<Vec<IntegerTerm>>());
            if self.aggressive_dedup {
                self.edges.p_old[v as usize].clone_from(&self.edges.sols[v as usize]);
            } else {
                self.edges.p_old[v as usize].union_assign(&p_dif);
            }

            for (&w, offsets) in &self.edges.subset[v as usize] {
                let mut should_set_new_incoming = false;
                for o in offsets.iter() {
                    should_set_new_incoming = propagate_terms_into(
                        &p_dif,
                        p_dif_vec.iter().copied(),
                        o,
                        &mut self.edges.sols[w as usize],
                        &self.term_types,
                    ) && o > 0;
                    if o == 0 {
                        if self.aggressive_dedup {
                            if let Some((a, b)) =
                                self.edges.sols.get_two_mut(v as usize, w as usize)
                            {
                                S::deduplicate_subset_pair(a, b);
                            }
                        }
                    }
                }

                if should_set_new_incoming {
                    self.new_incoming.push(w);
                }
            }
        }
        changed
    }

    fn add_edges_after_wave_prop(&mut self, changed_terms: &[IntegerTerm]) -> bool {
        let mut changed = false;
        for &cond_node in changed_terms {
            for i in 0..self.edges.conds[cond_node as usize].len() {
                let cond = &mut self.edges.conds[cond_node as usize][i];
                if self.edges.sols[cond_node as usize].len() == cond.cache.len() {
                    continue;
                }
                let sols = &self.edges.sols[cond_node as usize];
                let p_new = sols.difference(&cond.cache);
                cond.cache.clone_from(sols);

                match cond.entry.clone() {
                    CondEntry::Left {
                        right,
                        offset,
                        call_site,
                        context,
                    } => {
                        let right = get_representative(&mut self.parents, right);
                        for t in p_new.iter() {
                            if let Some(t) = self.try_offset_and_instantiate(
                                t,
                                call_site.as_ref(),
                                offset,
                                &context,
                            ) {
                                let t = get_representative(&mut self.parents, t);
                                if t == right {
                                    continue;
                                }
                                if insert_edge(&mut self.edges.subset, t, right, 0) {
                                    self.edges.sols[right as usize]
                                        .union_assign(&self.edges.p_old[t as usize]);
                                    self.edges.rev_subset[right as usize].insert(t);
                                    self.new_incoming.push(right);
                                    changed = true;
                                }
                            }
                        }
                    }
                    CondEntry::Right {
                        left,
                        offset,
                        call_site,
                        context,
                    } => {
                        let left = get_representative(&mut self.parents, left);
                        for t in p_new.iter() {
                            if let Some(t) = self.try_offset_and_instantiate(
                                t,
                                call_site.as_ref(),
                                offset,
                                &context,
                            ) {
                                let t = get_representative(&mut self.parents, t);
                                if t == left {
                                    continue;
                                }
                                if insert_edge(&mut self.edges.subset, left, t, 0) {
                                    self.edges.sols[t as usize]
                                        .union_assign(&self.edges.p_old[left as usize]);
                                    self.edges.rev_subset[t as usize].insert(left);
                                    self.new_incoming.push(t);
                                    changed = true;
                                }
                            }
                        }
                    }
                    CondEntry::CallDummy { call_site, context } => {
                        for t in p_new.iter() {
                            changed |= self
                                .try_offset_and_instantiate(t, Some(&call_site), 0, &context)
                                .is_some();
                        }
                    }
                }
            }
        }
        changed
    }

    fn deduplicate(&mut self, changed_terms: &[IntegerTerm]) {
        let sets = self
            .edges
            .sols
            .my_get_many_mut(changed_terms)
            .into_iter()
            .chain(self.edges.p_old.my_get_many_mut(changed_terms))
            .flatten()
            .chain(
                self.edges
                    .conds
                    .my_get_many_mut(changed_terms)
                    .into_iter()
                    .flatten()
                    .flat_map(|conds| conds.iter_mut())
                    .map(|c| &mut c.cache),
            );
        S::deduplicate(sets);
    }

    fn try_offset_and_instantiate(
        &mut self,
        term: IntegerTerm,
        call_site: Option<&CallSite>,
        offset: usize,
        context: &C::Context,
    ) -> Option<IntegerTerm> {
        let term_type = self.term_types[term as usize];
        let Some(call_site) = call_site else {
            return try_offset_term(term, term_type, offset);
        };
        match term_type {
            TermType::Function(allowed, func_type) => {
                if func_type != call_site.0.func_type_index {
                    return None;
                }
                let new_context = self
                    .context_state
                    .context_selector
                    .select_context(context, call_site);
                let f_index = *self
                    .context_state
                    .function_term_functions
                    .get(&term)
                    .unwrap_or_else(|| {
                        panic!(
                            "function term should have a function: {:?}\n{:?}",
                            self.context_state.concrete_to_input(term),
                            (0..self.context_state.num_concrete_terms() as IntegerTerm)
                                .map(|t| self.context_state.concrete_to_input(t))
                                .collect_vec()
                        )
                    }) as usize;
                let function_term = self.get_or_instantiate_function(f_index, new_context);
                (offset <= allowed).then(|| function_term + offset as IntegerTerm)
            }
            _ => None,
        }
    }

    fn get_or_instantiate_function(&mut self, f_index: usize, context: C::Context) -> IntegerTerm {
        let (index, instantiated_template) = self
            .context_state
            .get_or_instantiate_function(f_index, context.clone());

        if let Some(template) = instantiated_template {
            let instantiated_start_index = self.edges.sols.len();
            let num_instantiated = template.types.len();
            let new_len = instantiated_start_index + num_instantiated;
            self.edges.sols.resize_with(new_len, S::new);
            self.edges.subset.resize_with(new_len, HashMap::new);
            self.edges.rev_subset.resize_with(new_len, HashSet::new);
            self.edges.conds.resize_with(new_len, ThinVec::new);
            self.term_types.extend_from_slice(&template.types);
            self.parents.extend(
                (0..num_instantiated).map(|i| (instantiated_start_index + i) as IntegerTerm),
            );
            self.edges.p_old.resize_with(new_len, S::new);

            let constraints = template.constraints.clone();
            for constraint in constraints {
                let concrete_constraint = constraint.map_terms(|tt| match tt {
                    &TemplateTerm::Internal(index) => {
                        instantiated_start_index as IntegerTerm + index
                    }
                    &TemplateTerm::Global(index) => index,
                });
                self.add_constraint(concrete_constraint.clone(), context.clone());

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
                    let left = get_representative(&mut self.parents, left);
                    let right = get_representative(&mut self.parents, right);
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
                    self.new_incoming.push(right);
                }
            }
        }
        index
    }

    fn add_constraint(&mut self, c: Constraint<IntegerTerm>, context: C::Context) {
        let c = c.map_terms(|&t| get_representative(&mut self.parents, t));
        match c {
            Constraint::Inclusion { node, .. } => {
                self.new_incoming.push(node);
            }
            Constraint::Subset { right, .. } => {
                self.new_incoming.push(right);
            }
            Constraint::UnivCondSubsetLeft { cond_node, .. }
            | Constraint::UnivCondSubsetRight { cond_node, .. }
            | Constraint::CallDummy { cond_node, .. } => {
                self.new_incoming.push(cond_node);
            }
        }
        self.edges.add_constraint(c, context);
    }
}

impl<T, S, C> SccGraph for WavePropagationSolverState<T, S, C>
where
    C: ContextSelector + Clone,
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = u32> + Debug,
{
    fn unify(&mut self, child: IntegerTerm, parent_fn: impl Fn(IntegerTerm) -> IntegerTerm) {
        let parent = parent_fn(child);
        debug_assert_ne!(child, parent);

        let child_sols = mem::take(&mut self.edges.sols[child as usize]);
        self.edges.sols[parent as usize].union_assign(&child_sols);

        let p_old = &self.edges.p_old[parent as usize];
        let p_old_vec = Lazy::new(|| p_old.iter().collect::<Vec<IntegerTerm>>());
        let child_edges = mem::take(&mut self.edges.subset[child as usize]);

        for (&other, offsets) in &child_edges {
            debug_assert_ne!(0, offsets.len());

            let other_parent = parent_fn(other);

            if offsets.has_non_zero() || other_parent != parent {
                let other_term_set = &mut self.edges.sols[other_parent as usize];
                let mut entry = self.edges.subset[parent as usize].entry(other_parent);
                let mut existing_offsets = match entry {
                    Entry::Occupied(ref mut entry) => Either::Left(entry.get_mut()),
                    Entry::Vacant(entry) => Either::Right(entry),
                };

                for offset in offsets.iter() {
                    if let Either::Left(offs) = &existing_offsets {
                        if offs.contains(offset) {
                            continue;
                        }
                    }
                    propagate_terms_into(
                        p_old,
                        p_old_vec.iter().copied(),
                        offset,
                        other_term_set,
                        &self.term_types,
                    );
                    match existing_offsets {
                        Either::Left(ref mut offs) => {
                            offs.insert(offset);
                        }
                        Either::Right(entry) => {
                            existing_offsets = Either::Left(entry.insert(Offsets::single(offset)));
                        }
                    }
                }
            }

            self.edges.rev_subset[other as usize].remove(&child);
            self.edges.rev_subset[other_parent as usize].insert(parent);
        }

        let child_rev_edges = mem::take(&mut self.edges.rev_subset[child as usize]);
        for &i in child_rev_edges.iter() {
            if i == child {
                continue;
            }
            match self.edges.subset[i as usize].remove(&child) {
                Some(orig_edges) => {
                    self.edges.subset[i as usize]
                        .entry(parent)
                        .and_modify(|e| e.union_assign(&orig_edges))
                        .or_insert_with(|| orig_edges.clone());
                }
                None => {
                    panic!("Expected edges from {i} to {child}");
                }
            }
        }

        self.edges.rev_subset[parent as usize].union_assign(&child_rev_edges);
        let child_conds = mem::take(&mut self.edges.conds[child as usize]);
        self.edges.conds[parent as usize].extend(child_conds);

        self.parents[child as usize] = parent;
        self.edges.p_old[child as usize] = S::new();
    }

    fn parent_heuristic(&self, node: IntegerTerm) -> u32 {
        self.edges.subset[node as usize].len() as u32
    }
}

/// Return true if new terms were offset propagated
fn propagate_terms_into<S: TermSetTrait<Term = IntegerTerm>>(
    term_set: &S,
    term_set_iter: impl IntoIterator<Item = IntegerTerm>,
    offset: usize,
    dest_term_set: &mut S,
    term_types: &[TermType],
) -> bool {
    let mut propagated_term_weighted = false;
    if offset == 0 {
        dest_term_set.union_assign(term_set);
        return false;
    } else {
        let to_add = term_set_iter.into_iter().filter_map(|t| {
            if let TermType::Struct(allowed) = term_types[t as usize] {
                (offset <= allowed).then(|| t + offset as IntegerTerm)
            } else {
                None
            }
        });
        for t in to_add {
            dest_term_set.insert(t);
            propagated_term_weighted = true;
        }
    }
    propagated_term_weighted
}

impl<S, C> SolverExt for WavePropagationSolver<S, C>
where
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    C: ContextSelector,
{
}

impl<T, S, C> Solver<ContextSensitiveInput<T, C>> for WavePropagationSolver<S, C>
where
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    C: ContextSelector + Clone,
{
    type Solution = WavePropagationSolverState<T, S, C>;

    fn solve(&self, input: ContextSensitiveInput<T, C>) -> Self::Solution {
        let (context_state, function_term_infos) = ContextState::from_context_input(&input);
        let empty_context = context_state.context_selector.empty();

        let num_terms = context_state.num_concrete_terms();

        let mut sols = vec![S::new(); num_terms];
        let subset: Vec<HashMap<IntegerTerm, Offsets>> = vec![HashMap::new(); num_terms];
        let rev_subset = vec![HashSet::new(); num_terms];

        let mut term_types = vec![TermType::Basic; sols.len()];
        for (t, tt) in &input.global.term_types {
            let abstract_term = context_state.mapping.term_to_integer(t);
            term_types[abstract_term as usize] = *tt;
        }

        let mut new_incoming = vec![];

        for (i, function_term_info) in function_term_infos.into_iter().enumerate() {
            let fun_term = context_state.function_to_fun_term(i as u32);
            term_types[fun_term as usize] = function_term_info.term_type;
            sols[function_term_info.pointer_node as usize].insert(fun_term);
            new_incoming.push(function_term_info.pointer_node);
        }

        let parents = Vec::from_iter(0..sols.len() as IntegerTerm);
        let conds = iter::repeat_with(ThinVec::new).take(num_terms).collect();
        let p_old = vec![S::new(); sols.len()];
        let mut state = WavePropagationSolverState {
            context_state,
            edges: Edges {
                sols,
                subset,
                rev_subset,
                conds,
                p_old,
            },
            term_types,
            parents,
            new_incoming,
            iters: 0,
            scc_time: Duration::ZERO,
            propagation_time: Duration::ZERO,
            edge_instantiation_time: Duration::ZERO,
            aggressive_dedup: self.2,
        };

        for c in input.global.constraints {
            state.add_constraint(
                state.context_state.mapping.translate_constraint(&c),
                empty_context.clone(),
            );
        }

        for entrypoint in input.entrypoints {
            state.get_or_instantiate_function(entrypoint, empty_context.clone());
        }
        // for entrypoint in 0..state.context_state.templates.len() {
        //     state.get_or_instantiate_function(entrypoint, empty_context.clone());
        // }

        state.run_wave_propagation();

        state
    }
}

impl<T, S, C> WavePropagationSolverState<T, S, C>
where
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    C: ContextSelector + Clone,
{
    fn get_stack(&self, term: &T) -> OnlyOnceStack {
        let (fun_index, relative_index) = self
            .context_state
            .get_function_and_relative_index_from_term(term);

        let mut stack = OnlyOnceStack::new(self.context_state.num_abstract_terms());

        match fun_index {
            Some(i) => {
                let iter = self.context_state.instantiated_contexts[i as usize]
                    .iter()
                    .flat_map(|(_, start_index)| {
                        let concrete_index = start_index + relative_index;
                        self.edges.sols
                            [get_representative_no_mutation(&self.parents, concrete_index) as usize]
                            .iter()
                    })
                    .map(|concrete_index| self.context_state.concrete_to_abstract(concrete_index));
                for term in iter {
                    stack.push(term);
                }
            }
            None => {
                let iter = self.edges.sols
                    [get_representative_no_mutation(&self.parents, relative_index) as usize]
                    .iter()
                    .map(|concrete_index| self.context_state.concrete_to_abstract(concrete_index));
                for term in iter {
                    stack.push(term);
                }
            }
        }

        stack
    }
}

impl<T, S, C> SolverSolution for WavePropagationSolverState<T, S, C>
where
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    C: ContextSelector + Clone,
{
    type Term = T;
    type TermSet = HashSet<T>;

    fn get(&self, term: &T) -> Self::TermSet {
        let stack = self.get_stack(term);

        HashSet::from_iter(
            stack
                .into_iter()
                .map(|term| self.context_state.abstract_to_input(term)),
        )
    }

    fn get_len(&self, term: &T) -> usize {
        let stack = self.get_stack(term);
        stack.len()
    }

    fn as_serialize(&self) -> Box<dyn erased_serde::Serialize> {
        Box::new(WavePropSerialize {
            sccs: self
                .parents
                .iter()
                .enumerate()
                .filter(|&(v, &p)| v == p as usize)
                .count(),
            edges: self
                .edges
                .subset
                .iter()
                .flat_map(|m| m.values())
                .map(|o| o.len())
                .sum(),
            iterations: self.iters,
            instantiated_contexts: self.context_state.num_instantiated_contexts(),
            instantiated_nodes: self.edges.sols.len(),
            non_empty_nodes: (0..self.edges.sols.len())
                .filter(|&v| {
                    !self.edges.sols
                        [get_representative_no_mutation(&self.parents, v as u32) as usize]
                        .is_empty()
                })
                .count(),
            scc_time_ms: self.scc_time.as_secs_f64() * 1000.0,
            term_propagation_time_ms: self.propagation_time.as_secs_f64() * 1000.0,
            edge_instantiation_time_ms: self.edge_instantiation_time.as_secs_f64() * 1000.0,
        })
    }
}

struct Edges<S, C: ContextSelector> {
    sols: Vec<S>,
    subset: Vec<HashMap<IntegerTerm, Offsets>>,
    rev_subset: Vec<HashSet<IntegerTerm>>,
    conds: Vec<ThinVec<CachedCondEntry<C::Context, S>>>,
    p_old: Vec<S>,
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
                self.conds[cond_node as usize].push(CachedCondEntry::new(CondEntry::Left {
                    right,
                    offset,
                    call_site,
                    context,
                }));
            }
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
                call_site,
            } => {
                self.conds[cond_node as usize].push(CachedCondEntry::new(CondEntry::Right {
                    left,
                    offset,
                    call_site,
                    context,
                }));
            }
            Constraint::CallDummy {
                cond_node,
                arguments: _,
                result_node: _,
                call_site,
            } => {
                self.conds[cond_node as usize].push(CachedCondEntry::new(CondEntry::CallDummy {
                    call_site,
                    context,
                }));
            }
        };
    }

    fn add_edge(&mut self, left: IntegerTerm, right: IntegerTerm, offset: usize) -> bool {
        if insert_edge(&mut self.subset, left, right, offset) {
            self.rev_subset[right as usize].insert(left);
            return true;
        }
        false
    }
}

impl<S, C> SccEdges for Edges<S, C>
where
    S: TermSetTrait<Term = IntegerTerm>,
    C: ContextSelector,
{
    fn node_count(&self) -> usize {
        self.sols.len()
    }

    fn successors(
        &self,
        node: IntegerTerm,
    ) -> impl Iterator<Item = (IntegerTerm, super::scc::SccEdgeWeight)> {
        self.subset[node as usize]
            .iter()
            .map(|(w, offsets)| (*w, offsets.scc_edge_weight()))
    }
}

fn get_representative_no_mutation(parents: &Vec<IntegerTerm>, child: IntegerTerm) -> IntegerTerm {
    let mut node = child;
    loop {
        let parent = parents[node as usize];
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

pub type HashWavePropagationSolver<C> = WavePropagationSolver<HashSet<IntegerTerm>, C>;
pub type RoaringWavePropagationSolver<C> = WavePropagationSolver<RoaringBitmap, C>;
pub type SharedBitVecWavePropagationSolver<C> = WavePropagationSolver<SharedBitVec, C>;
pub type RcRoaringWavePropagationSolver<C> = WavePropagationSolver<RcTermSet<RoaringBitmap>, C>;
pub type RcSharedBitVecWavePropagationSolver<C> = WavePropagationSolver<RcTermSet<SharedBitVec>, C>;

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

impl<T, S, C> WavePropagationSolverState<T, S, C>
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

impl<T, S, C> Graph for WavePropagationSolverState<T, S, C>
where
    T: Display + Debug + Clone + PartialEq + Eq + Hash,
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    C: ContextSelector + Clone,
    C::Context: Display,
{
    type Node = ContextWavePropagationNode<T, C::Context>;
    type Weight = OffsetWeight;

    fn nodes(&self) -> Vec<Node<Self::Node>> {
        let reps = self.get_representative_counts();
        reps.into_iter()
            .map(|(t, node)| {
                let inner = ContextWavePropagationNode {
                    term: self.context_state.concrete_to_input(t),
                    context: self.context_state.context_of_concrete_index(t),
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
                term: self.context_state.concrete_to_input(from as IntegerTerm),
                context: self
                    .context_state
                    .context_of_concrete_index(from as IntegerTerm),
                count: reps.get(&(from as u32)).unwrap().inner,
            };
            let from_node = Node { inner, id: from };

            for (to, weights) in outgoing {
                let inner = ContextWavePropagationNode {
                    term: self.context_state.concrete_to_input(*to as IntegerTerm),
                    context: self
                        .context_state
                        .context_of_concrete_index(*to as IntegerTerm),
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

#[derive(Serialize)]
pub(crate) struct WavePropSerialize {
    pub sccs: usize,
    pub edges: usize,
    pub iterations: u64,
    pub instantiated_contexts: usize,
    pub instantiated_nodes: usize,
    pub non_empty_nodes: usize,
    pub scc_time_ms: f64,
    pub term_propagation_time_ms: f64,
    pub edge_instantiation_time_ms: f64,
}
