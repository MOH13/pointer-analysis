use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;
use std::marker::PhantomData;
use std::time::Duration;
use std::{iter, mem};

use bitvec::prelude::*;
use either::Either;
use hashbrown::hash_map::Entry;
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use once_cell::unsync::Lazy;
use roaring::RoaringBitmap;
use serde::Serialize;
use smallvec::SmallVec;
use thin_vec::ThinVec;

use super::context::{ContextState, TemplateTerm};
use super::context_wave_prop::WavePropSerialize;
use super::rc_termset::RcTermSet;
use super::scc::{scc, SccEdges, SccGraph};
use super::shared_bitvec::SharedBitVec;
use super::{
    insert_edge, try_offset_term, CallSite, Constraint, ContextSelector, Demand,
    DemandContextSensitiveInput, IntegerTerm, Offsets, OnlyOnceStack, Solver, SolverExt,
    SolverSolution, TermSetTrait, TermType,
};

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
pub struct TidalPropagationSolver<S, C>(PhantomData<S>, PhantomData<C>, bool);

impl<S, C> TidalPropagationSolver<S, C> {
    pub fn new() -> Self {
        Self(PhantomData, PhantomData, false)
    }
    pub fn new_with_aggressive_dedup() -> Self {
        Self(PhantomData, PhantomData, true)
    }
}

struct PointedByQueries<S> {
    bitset: uniset::BitSet,
    termset: S,
}

impl<S: TermSetTrait<Term = IntegerTerm>> PointedByQueries<S> {
    fn new(len: usize) -> Self {
        Self {
            bitset: uniset::BitSet::with_capacity(len),
            termset: S::new(),
        }
    }

    fn insert(&mut self, term: IntegerTerm) -> bool {
        if !self.contains(term) {
            self.bitset.set(term as usize);
            self.termset.insert(term);
            return true;
        }
        false
    }

    fn contains(&self, term: IntegerTerm) -> bool {
        self.bitset.test(term as usize)
    }

    fn get_termset(&self) -> &S {
        &self.termset
    }
}

pub struct TidalPropagationSolverState<T, S, C: ContextSelector> {
    sols: Vec<S>,
    p_old: Vec<S>,
    context_state: ContextState<T, C>,
    edges: Edges<C, S>,
    term_types: Vec<TermType>,
    abstract_rev_offsets: Vec<SmallVec<[u32; 2]>>,
    parents: Vec<IntegerTerm>,
    points_to_queries: uniset::BitSet,
    pointed_by_queries: PointedByQueries<S>,
    visited_pointed_by: uniset::BitSet,
    /// For each node, track functions to query if node gets points-to query
    mention_points_to: Vec<SmallVec<[u32; 2]>>,
    /// For each node, track functions to query if node gets pointed-by query
    mention_pointed_by: Vec<SmallVec<[u32; 2]>>,
    return_and_parameter_children: Vec<SmallVec<[IntegerTerm; 2]>>,
    abstract_points_to_queries: BitVec,
    abstract_pointed_by_queries: BitVec,
    new_points_to_queries: Vec<IntegerTerm>,
    new_pointed_by_queries: Vec<IntegerTerm>,
    new_incoming: Vec<IntegerTerm>,
    iters: u64,
    scc_time: Duration,
    query_propagation_time: Duration,
    term_propagation_time: Duration,
    edge_instantiation_time: Duration,
    aggressive_dedup: bool,
}

impl<T, S, C: ContextSelector> TidalPropagationSolverState<T, S, C> {
    fn term_count(&self) -> usize {
        self.sols.len()
    }
}

impl<T, S, C> TidalPropagationSolverState<T, S, C>
where
    C: ContextSelector + Clone,
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = u32> + Debug,
{
    fn run_tidal_propagation(&mut self) {
        let mut changed = true;
        while changed {
            self.iters += 1;

            let scc_start = std::time::Instant::now();
            self.collapse_cycles();
            self.scc_time += scc_start.elapsed();

            let query_propagation_start = std::time::Instant::now();
            self.query_propagation();
            self.query_propagation_time += query_propagation_start.elapsed();

            let term_propagation_start = std::time::Instant::now();
            let (changed_terms, prop_changed) = self.term_propagation();
            changed = prop_changed;
            self.term_propagation_time += term_propagation_start.elapsed();

            let edge_instantiation_start = std::time::Instant::now();
            changed |= self.add_edges_after_wave_prop(&changed_terms);
            self.edge_instantiation_time += edge_instantiation_start.elapsed();

            if self.aggressive_dedup {
                self.deduplicate(&changed_terms);
            }

            eprintln!("Iteration {}", self.iters);
        }

        eprintln!(
            "SCC count: {}",
            self.parents
                .iter()
                .enumerate()
                .filter(|(child, parent)| *child == **parent as usize)
                .count()
        );
    }

    fn collapse_cycles(&mut self) {
        scc(
            &self
                .edges
                .scc_edges(SccDirection::Forward, EdgeVisitMode::OnlyNonWeighted),
            self.new_incoming.clone(),
            |_, _| {},
        )
        .collapse_cycles(self)
        .finish();
    }

    fn query_propagation(&mut self) {
        let mut changed = true;
        let mut iters = 0;
        let mut new_incoming = self.new_incoming.clone();
        while changed {
            let mut new_queries = 0;
            changed = false;

            let mut pt_starting_nodes = new_incoming
                .iter()
                .map(|&t| get_representative(&mut self.parents, t))
                .filter(|t| self.points_to_queries.test(*t as usize))
                .collect_vec();

            pt_starting_nodes.extend(
                self.new_points_to_queries
                    .drain(..)
                    .map(|v| get_representative(&mut self.parents, v)),
            );

            // Points-to query propagation
            scc(
                &self
                    .edges
                    .scc_edges(SccDirection::Backward, EdgeVisitMode::WithWeighted),
                pt_starting_nodes,
                |v, to_visit| {
                    if self.points_to_queries.test(v as usize) {
                        return;
                    }
                    self.points_to_queries.set(v as usize);
                    new_queries += 1;
                    self.new_pointed_by_queries.push(v);
                    self.new_incoming.push(v);

                    for &w in &self.edges.rev_addr_ofs[v as usize] {
                        self.sols[v as usize].insert(w);
                    }

                    for &w in &self.edges.loads[v as usize] {
                        to_visit.push(get_representative(&mut self.parents, w));
                    }

                    for &w in &self.return_and_parameter_children[v as usize] {
                        let (fun_index, relative_index) = self
                            .context_state
                            .get_function_and_relative_index_from_concrete_index(w);
                        let fun_index = fun_index.expect("Term should be in a function");
                        let template = &self.context_state.templates[fun_index as usize];
                        if relative_index >= template.num_return_terms
                            && relative_index
                                < template.num_return_terms + template.num_parameter_terms
                        {
                            self.new_pointed_by_queries
                                .push(self.context_state.templates[0].start_index + fun_index);
                        }
                    }

                    for f_index in mem::take(&mut self.mention_points_to[v as usize]) {
                        self.new_pointed_by_queries
                            .push(self.context_state.function_to_fun_term(f_index));
                    }
                },
            )
            .finish();

            let mut pb_starting_nodes = vec![];
            let mut local_new_pb_queries = OnlyOnceStack::new(self.term_count());

            for q in self.new_pointed_by_queries.drain(..) {
                for q2 in offsetable_terms(q, &self.context_state, &self.abstract_rev_offsets) {
                    local_new_pb_queries.push(q2);
                }
                local_new_pb_queries.push(q);
            }

            local_new_pb_queries.retain(|&q| !self.pointed_by_queries.contains(q));

            for &q in &local_new_pb_queries {
                for &t in &self.edges.addr_ofs[q as usize] {
                    // TODO: deduplicate?
                    pb_starting_nodes.push(get_representative(&mut self.parents, t));
                }
            }

            for v in new_incoming.drain(..) {
                let v = get_representative(&mut self.parents, v);
                if self.sols[v as usize].overlaps(self.pointed_by_queries.get_termset()) {
                    pb_starting_nodes.push(v);
                }
            }

            // Pointed-by query propagation
            scc(
                &self
                    .edges
                    .scc_edges(SccDirection::Forward, EdgeVisitMode::OnlyNonWeighted),
                pb_starting_nodes,
                |v, to_visit| {
                    if self.visited_pointed_by.test(v as usize) {
                        return;
                    }
                    self.visited_pointed_by.set(v as usize);
                    local_new_pb_queries.push(v);

                    for q in offsetable_terms(v, &self.context_state, &self.abstract_rev_offsets) {
                        if self.pointed_by_queries.contains(q) {
                            continue;
                        }
                        if local_new_pb_queries.push(q) {
                            for &t in &self.edges.addr_ofs[q as usize] {
                                to_visit.push(get_representative(&mut self.parents, t));
                            }
                        }
                    }

                    for &w in &self.edges.addr_ofs[v as usize] {
                        let w = get_representative(&mut self.parents, w);
                        to_visit.push(w);
                    }

                    for &w in &self.edges.stores[v as usize] {
                        self.new_points_to_queries.push(w);
                        changed = true;
                    }

                    for &w in &self.return_and_parameter_children[v as usize] {
                        let (fun_index, relative_index) = self
                            .context_state
                            .get_function_and_relative_index_from_concrete_index(w);
                        let fun_index = fun_index.expect("Term should be in a function");
                        let num_return_terms =
                            self.context_state.templates[fun_index as usize].num_return_terms;
                        if relative_index < num_return_terms {
                            let fun_term = self.context_state.templates[0].start_index + fun_index;
                            if self.pointed_by_queries.contains(fun_term) {
                                continue;
                            }
                            if local_new_pb_queries.push(fun_term) {
                                for &t in &self.edges.addr_ofs[fun_term as usize] {
                                    to_visit.push(get_representative(&mut self.parents, t));
                                }
                            }
                        }
                    }
                },
            )
            .finish();

            let mut new_pointed_by_queries_bitset =
                BitVec::<usize>::repeat(false, self.term_count());

            for v in local_new_pb_queries {
                if self.pointed_by_queries.contains(v) {
                    continue;
                }
                if !new_pointed_by_queries_bitset[v as usize] {
                    new_pointed_by_queries_bitset.set(v as usize, true);
                    for &w in &self.edges.addr_ofs[v as usize] {
                        let w = get_representative(&mut self.parents, w);
                        self.sols[w as usize].insert(v);
                        self.new_incoming.push(w);
                    }
                    self.pointed_by_queries.insert(v);

                    for f_index in mem::take(&mut self.mention_pointed_by[v as usize]) {
                        self.new_pointed_by_queries
                            .push(self.context_state.function_to_fun_term(f_index));
                    }
                }
            }
            iters += 1;
        }
        eprintln!("{iters} query iterations");
    }

    fn term_propagation(&mut self) -> (Vec<IntegerTerm>, bool) {
        let mut changed = false;

        let new_incoming = self
            .new_incoming
            .drain(..)
            .map(|t| get_representative(&mut self.parents, t))
            .collect();
        let top_order = scc(
            &self
                .edges
                .scc_edges(SccDirection::Forward, EdgeVisitMode::WithWeighted),
            new_incoming,
            |_, _| {},
        )
        .into_top_order();
        // .get_pre_top(
        //     &self
        //         .edges
        //         .scc(SccDirection::Forward, EdgeVisitMode::WithWeighted),
        // );

        for &v in top_order.iter().rev() {
            // Skip if no new terms in solution set
            if self.sols[v as usize].len() == self.p_old[v as usize].len() {
                continue;
            }
            changed = true;
            let p_dif = self.sols[v as usize].weak_difference(&self.p_old[v as usize]);
            let p_dif_vec = Lazy::new(|| p_dif.iter().collect::<Vec<IntegerTerm>>());
            if self.aggressive_dedup {
                self.p_old[v as usize].clone_from(&self.sols[v as usize]);
            } else {
                self.p_old[v as usize].union_assign(&p_dif);
            }

            for (&w, offsets) in &self.edges.subset[v as usize] {
                let mut should_set_new_incoming = false;
                for o in offsets.iter() {
                    if o == 0 {
                        self.sols[w as usize].union_assign(&p_dif);
                        if self.aggressive_dedup {
                            if let Some((a, b)) = self.sols.get_two_mut(v as usize, w as usize) {
                                S::deduplicate_subset_pair(a, b);
                            }
                        }
                    } else {
                        let to_add = p_dif_vec
                            .iter()
                            .filter_map(|&t| try_offset_term(t, self.term_types[t as usize], o));
                        for t in to_add {
                            self.sols[w as usize].insert(t);
                            should_set_new_incoming = true;
                            if !self.pointed_by_queries.contains(t) {
                                self.edges.addr_ofs[t as usize].push(w);
                                self.edges.rev_addr_ofs[w as usize].push(t);
                            }
                        }
                    }
                }

                if should_set_new_incoming {
                    self.new_incoming.push(w);
                }
            }
        }

        (top_order, changed)
    }

    fn add_edges_after_wave_prop(&mut self, changed_terms: &[IntegerTerm]) -> bool {
        let mut changed = false;
        for &cond_node in changed_terms {
            for i in 0..self.edges.conds[cond_node as usize].len() {
                let cond = &mut self.edges.conds[cond_node as usize][i];
                if self.sols[cond_node as usize].len() == cond.cache.len() {
                    continue;
                }
                let mut sols = self.sols[cond_node as usize].clone();

                if !self.points_to_queries.test(cond_node as usize) {
                    sols.intersection_assign(self.pointed_by_queries.get_termset());
                    if sols.len() == cond.cache.len() {
                        continue;
                    }
                }

                let p_new = sols.difference(&cond.cache);
                cond.cache = sols;

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
                                    self.sols[right as usize].union_assign(&self.p_old[t as usize]);
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
                                    self.sols[t as usize].union_assign(&self.p_old[left as usize]);
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
            .sols
            .my_get_many_mut(changed_terms)
            .into_iter()
            .chain(self.p_old.my_get_many_mut(changed_terms))
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
                    .expect("function term should have a function")
                    as usize;
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
            let instantiated_start_index = self.sols.len();
            let num_instantiated = template.types.len();
            let new_len = instantiated_start_index + num_instantiated;
            self.sols.resize_with(new_len, S::new);
            self.edges.resize(new_len);
            self.term_types.extend_from_slice(&template.types);
            self.parents.extend(
                (0..num_instantiated).map(|i| (instantiated_start_index + i) as IntegerTerm),
            );

            self.p_old.resize_with(new_len, S::new);
            self.mention_points_to.resize_with(new_len, SmallVec::new);
            self.mention_pointed_by.resize_with(new_len, SmallVec::new);
            self.return_and_parameter_children
                .resize_with(new_len, SmallVec::new);
            for i in 0..(template.num_return_terms + template.num_parameter_terms) as usize {
                self.return_and_parameter_children[instantiated_start_index + i]
                    .push((instantiated_start_index + i) as IntegerTerm);
            }

            for i in 0..num_instantiated as u32 {
                let abstract_term = template.start_index + i;
                let concrete_term = instantiated_start_index as IntegerTerm + i;
                if self.abstract_points_to_queries[abstract_term as usize] {
                    self.new_points_to_queries.push(concrete_term);
                }
                if self.abstract_pointed_by_queries[abstract_term as usize] {
                    self.new_pointed_by_queries.push(concrete_term);
                }
            }

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
                    let left_sols = self.sols[left as usize].clone();
                    let left_sols_iter = left_sols.iter();
                    let right_sols = &mut self.sols[right as usize];
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
        let rep_c = c.map_terms(|&t| get_representative(&mut self.parents, t));
        self.edges.add_constraint(rep_c, context);
        match c {
            Constraint::UnivCondSubsetLeft {
                cond_node, right, ..
            } => {
                if self.points_to_queries.test(right as usize) {
                    self.new_points_to_queries.push(cond_node);
                }
                self.new_incoming.push(cond_node);
            }
            Constraint::UnivCondSubsetRight {
                cond_node, left, ..
            } => {
                if self.visited_pointed_by.test(left as usize) {
                    self.new_points_to_queries.push(cond_node);
                }
                self.new_incoming.push(cond_node)
            }
            Constraint::CallDummy { cond_node, .. } => self.new_incoming.push(cond_node),
            _ => {}
        }
    }

    /// Returns the corresponding function term if `node` is function, otherwise None
    /// Todo: Improve
    fn global_to_fun_term(&self, node: IntegerTerm) -> Option<IntegerTerm> {
        for t in &self.edges.rev_addr_ofs[node as usize] {
            if self.context_state.function_term_functions.contains_key(t) {
                return Some(*t);
            }
        }
        None
    }
}

fn offsetable_terms<T, C: ContextSelector + Clone>(
    term: IntegerTerm,
    context_state: &ContextState<T, C>,
    abstract_rev_offsets: &[SmallVec<[u32; 2]>],
) -> impl Iterator<Item = IntegerTerm> {
    let abstract_term = context_state.concrete_to_abstract(term);
    abstract_rev_offsets[abstract_term as usize]
        .clone()
        .into_iter()
        .map(move |o| term - o)
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
        let to_add = term_set_iter
            .into_iter()
            .filter_map(|t| try_offset_term(t, term_types[t as usize], offset));
        dest_term_set.extend(to_add);
    }
}

impl<S, C> SolverExt for TidalPropagationSolver<S, C>
where
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    C: ContextSelector,
{
}

impl<T, S, C> Solver<DemandContextSensitiveInput<T, C>> for TidalPropagationSolver<S, C>
where
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    C: ContextSelector + Clone,
{
    type Solution = TidalPropagationSolverState<T, S, C>;

    fn solve(&self, input: DemandContextSensitiveInput<T, C>) -> Self::Solution {
        let (context_state, fun_term_infos) = ContextState::from_context_input(&input.input);
        let empty_context = context_state.context_selector.empty();

        let num_terms = context_state.num_concrete_terms();
        let num_abstract = context_state.num_abstract_terms();

        let mut edges = Edges {
            addr_ofs: vec![SmallVec::new(); num_terms],
            rev_addr_ofs: vec![SmallVec::new(); num_terms],
            subset: vec![HashMap::new(); num_terms],
            rev_subset: vec![HashSet::new(); num_terms],
            conds: iter::repeat_with(ThinVec::new).take(num_terms).collect(),
            loads: vec![SmallVec::new(); num_terms],
            stores: vec![SmallVec::new(); num_terms],
        };

        let mut term_types = vec![TermType::Basic; num_terms];
        let mut abstract_rev_offsets = vec![SmallVec::new(); num_abstract];

        let global_term_types_iter = input
            .input
            .global
            .term_types
            .iter()
            .map(|(t, tt)| (context_state.input_to_abstract(t), *tt));
        let template_term_types_iter = context_state.templates.iter().flat_map(|t| {
            t.types
                .iter()
                .enumerate()
                .map(|(i, tt)| (t.start_index + i as u32, *tt))
        });
        for (from, tt) in global_term_types_iter.clone() {
            term_types[from as usize] = tt;
        }
        for (from, tt) in global_term_types_iter.chain(template_term_types_iter) {
            if let TermType::Struct(max_offset) = tt {
                for offset in 1..=max_offset as u32 {
                    let to = from + offset;
                    abstract_rev_offsets[to as usize].push(offset);
                }
            }
        }

        for (i, function_term_info) in fun_term_infos.iter().enumerate() {
            let fun_term = context_state.function_to_fun_term(i as u32);
            term_types[fun_term as usize] = function_term_info.term_type;
            edges.add_constraint(
                Constraint::Inclusion {
                    term: fun_term,
                    node: function_term_info.pointer_node,
                },
                empty_context.clone(),
            );
        }

        let num_abstract_terms = context_state.num_abstract_terms();
        let mut state = TidalPropagationSolverState {
            edges,
            context_state,
            sols: vec![S::new(); num_terms],
            p_old: vec![S::new(); num_terms],
            term_types,
            abstract_rev_offsets,
            parents: Vec::from_iter(0..num_terms as IntegerTerm),
            points_to_queries: uniset::BitSet::new(),
            pointed_by_queries: PointedByQueries::new(num_terms),
            visited_pointed_by: uniset::BitSet::new(),
            mention_points_to: vec![SmallVec::new(); num_terms],
            mention_pointed_by: vec![SmallVec::new(); num_terms],
            return_and_parameter_children: vec![SmallVec::new(); num_terms],
            abstract_points_to_queries: bitvec::bitvec![0; num_abstract_terms],
            abstract_pointed_by_queries: bitvec::bitvec![0; num_abstract_terms],
            new_points_to_queries: vec![],
            new_pointed_by_queries: vec![],
            new_incoming: vec![],
            iters: 0,
            scc_time: Duration::ZERO,
            query_propagation_time: Duration::ZERO,
            term_propagation_time: Duration::ZERO,
            edge_instantiation_time: Duration::ZERO,
            aggressive_dedup: self.2,
        };

        for c in &input.input.global.constraints {
            state.add_constraint(
                state.context_state.mapping.translate_constraint(c),
                empty_context.clone(),
            );
        }

        for (f_index, f) in input.input.functions.iter().enumerate() {
            let f_index = f_index as u32;
            for c in &f.constrained_terms.constraints {
                let (left, right) = c.get_left_and_right();
                if let Some(left) = left {
                    if let Some(global) = state.context_state.term_to_concrete_global(left) {
                        state.mention_points_to[global as usize].push(f_index);
                        state.mention_pointed_by[global as usize].push(f_index);

                        if let Some(fun_term) = state.global_to_fun_term(global) {
                            state.mention_pointed_by[fun_term as usize].push(f_index);
                        }
                    }
                }
                if let Some(global) = state.context_state.term_to_concrete_global(right) {
                    state.mention_points_to[global as usize].push(f_index);
                    state.mention_pointed_by[global as usize].push(f_index);

                    if let Some(fun_term) = state.global_to_fun_term(global) {
                        state.mention_pointed_by[fun_term as usize].push(f_index);
                    }
                }
            }
        }

        for demand in input.demands {
            match demand {
                Demand::PointsTo(term) => {
                    let abstract_term = state.context_state.input_to_abstract(&term);
                    state
                        .abstract_points_to_queries
                        .set(abstract_term as usize, true);
                    if let Some(term) = state.context_state.term_to_concrete_global(&term) {
                        state.new_points_to_queries.push(term);
                    } else if let (Some(fun), _) = state
                        .context_state
                        .get_function_and_relative_index_from_term(&term)
                    {
                        state
                            .new_pointed_by_queries
                            .push(state.context_state.function_to_fun_term(fun));
                    }
                }
                Demand::PointedBy(term) => {
                    let abstract_term = state.context_state.input_to_abstract(&term);
                    state
                        .abstract_pointed_by_queries
                        .set(abstract_term as usize, true);
                    if let Some(term) = state.context_state.term_to_concrete_global(&term) {
                        state.new_pointed_by_queries.push(term);
                    } else if let (Some(fun), _) = state
                        .context_state
                        .get_function_and_relative_index_from_term(&term)
                    {
                        state
                            .new_pointed_by_queries
                            .push(state.context_state.function_to_fun_term(fun));
                    }
                }
            }
        }

        for entrypoint in input.input.entrypoints {
            state.get_or_instantiate_function(entrypoint, empty_context.clone());
        }
        // for entrypoint in 0..state.context_state.templates.len() {
        //     state.get_or_instantiate_function(entrypoint, empty_context.clone());
        // }

        state.run_tidal_propagation();

        let mut points_to_queries = state.points_to_queries.clone();
        for i in 0..state.sols.len() {
            let rep = get_representative_no_mutation(&state.parents, i as u32);
            if points_to_queries.test(rep as usize) {
                points_to_queries.set(i);
            }
        }

        eprintln!("points to queries: {}", points_to_queries.iter().count());
        eprintln!(
            "pointed by queries: {:?}",
            state.pointed_by_queries.termset.len()
        );

        state
    }
}

impl<T, S, C> TidalPropagationSolverState<T, S, C>
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
                        self.sols
                            [get_representative_no_mutation(&self.parents, concrete_index) as usize]
                            .iter()
                    })
                    .map(|concrete_index| self.context_state.concrete_to_abstract(concrete_index));
                for term in iter {
                    stack.push(term);
                }
            }
            None => {
                let iter = self.sols
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

impl<T, S, C> SccGraph for TidalPropagationSolverState<T, S, C>
where
    C: ContextSelector + Clone,
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = u32> + Debug,
{
    fn unify(&mut self, child: IntegerTerm, parent_fn: impl Fn(IntegerTerm) -> IntegerTerm) {
        let parent = parent_fn(child);
        debug_assert_ne!(child, parent);
        debug_assert!(self.parents[child as usize] == child);

        let child_sols = mem::take(&mut self.sols[child as usize]);
        self.sols[parent as usize].union_assign(&child_sols);

        let p_old = &self.p_old[parent as usize];
        let p_old_vec = Lazy::new(|| p_old.iter().collect::<Vec<IntegerTerm>>());
        let child_edges = mem::take(&mut self.edges.subset[child as usize]);

        for (&other, offsets) in &child_edges {
            debug_assert_ne!(0, offsets.len());

            let other_parent = parent_fn(other);

            if offsets.has_non_zero() || other_parent != parent {
                let other_term_set = &mut self.sols[other_parent as usize];
                let mut entry = self.edges.subset[parent as usize].entry(other_parent);
                let mut existing_offsets = match entry {
                    Entry::Occupied(ref mut entry) => Either::Left(entry.get_mut()),
                    Entry::Vacant(entry) => Either::Right(entry),
                };

                for o in offsets.iter() {
                    if let Either::Left(offs) = &existing_offsets {
                        if offs.contains(o) {
                            continue;
                        }
                    }

                    if o == 0 {
                        other_term_set.union_assign(&p_old);
                    } else {
                        let to_add = p_old_vec
                            .iter()
                            .filter_map(|&t| try_offset_term(t, self.term_types[t as usize], o));
                        for t in to_add {
                            other_term_set.insert(t);
                            if self.pointed_by_queries.contains(t) {
                                self.new_incoming.push(other_parent);
                            } else {
                                self.edges.addr_ofs[t as usize].push(other_parent);
                                self.edges.rev_addr_ofs[other_parent as usize].push(t);
                            }
                        }
                    }

                    match existing_offsets {
                        Either::Left(ref mut offs) => {
                            offs.insert(o);
                        }
                        Either::Right(entry) => {
                            existing_offsets = Either::Left(entry.insert(Offsets::single(o)));
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

        if self.visited_pointed_by.test(parent as usize)
            && !self.visited_pointed_by.test(child as usize)
        {
            self.new_pointed_by_queries.push(child);
            for &w in &self.edges.stores[child as usize] {
                self.new_points_to_queries.push(w);
            }

            for &w in &self.return_and_parameter_children[child as usize] {
                let (fun_index, relative_index) = self
                    .context_state
                    .get_function_and_relative_index_from_concrete_index(w);
                let fun_index = fun_index.expect("Term should be in a function");
                let num_return_terms =
                    self.context_state.templates[fun_index as usize].num_return_terms;
                if relative_index < num_return_terms {
                    let fun_term = self.context_state.templates[0].start_index + fun_index;
                    self.new_pointed_by_queries.push(fun_term);
                }
            }
        }

        if !self.points_to_queries.test(parent as usize)
            && self.points_to_queries.test(child as usize)
        {
            self.new_points_to_queries.push(parent);
        }

        if self.points_to_queries.test(parent as usize)
            && !self.points_to_queries.test(child as usize)
        {
            for &w in &self.edges.loads[child as usize] {
                self.new_points_to_queries.push(w);
            }

            for &w in &self.return_and_parameter_children[child as usize] {
                let (fun_index, relative_index) = self
                    .context_state
                    .get_function_and_relative_index_from_concrete_index(w);
                let fun_index = fun_index.expect("Term should be in a function");
                let template = &self.context_state.templates[fun_index as usize];
                if relative_index >= template.num_return_terms
                    && relative_index < template.num_return_terms + template.num_parameter_terms
                {
                    self.new_pointed_by_queries
                        .push(self.context_state.templates[0].start_index + fun_index);
                }
            }
        }

        self.edges.rev_subset[parent as usize].union_assign(&child_rev_edges);

        let child_mention_points_to = mem::take(&mut self.mention_points_to[child as usize]);
        self.mention_points_to[parent as usize].extend_from_slice(&child_mention_points_to);

        let child_return_and_parameter_children =
            mem::take(&mut self.return_and_parameter_children[child as usize]);
        self.return_and_parameter_children[parent as usize]
            .extend_from_slice(&child_return_and_parameter_children);

        let child_rev_addr_ofs = mem::take(&mut self.edges.rev_addr_ofs[child as usize]);
        self.edges.rev_addr_ofs[parent as usize].extend_from_slice(child_rev_addr_ofs.as_slice());
        let child_conds = mem::take(&mut self.edges.conds[child as usize]);
        self.edges.conds[parent as usize].extend(child_conds);
        let child_loads = mem::take(&mut self.edges.loads[child as usize]);
        self.edges.loads[parent as usize].extend_from_slice(child_loads.as_slice());
        let child_stores = mem::take(&mut self.edges.stores[child as usize]);
        self.edges.stores[parent as usize].extend_from_slice(child_stores.as_slice());

        self.parents[child as usize] = parent;
        self.p_old[child as usize] = S::new();
    }

    fn parent_heuristic(&self, node: IntegerTerm) -> u32 {
        self.edges.subset[node as usize].len() as u32
    }
}

impl<T, S, C> SolverSolution for TidalPropagationSolverState<T, S, C>
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
        let mut points_to_queries = self.points_to_queries.clone();
        for i in 0..self.sols.len() {
            let rep = get_representative_no_mutation(&self.parents, i as u32);
            if points_to_queries.test(rep as usize) {
                points_to_queries.set(i);
            }
        }

        let non_empty_set_iter = self
            .sols
            .iter()
            .chain(&self.p_old)
            .chain(self.edges.conds.iter().flatten().map(|c| &c.cache))
            .filter(|s| !s.is_empty());

        let term_set_dedup_stats = Some(S::get_deduplicate_stats(non_empty_set_iter));

        Box::new(TidalPropSerialize {
            wave_prop: WavePropSerialize {
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
                instantiated_nodes: self.sols.len(),
                non_empty_nodes: (0..self.sols.len())
                    .filter(|&v| {
                        !self.sols[get_representative_no_mutation(&self.parents, v as u32) as usize]
                            .is_empty()
                    })
                    .count(),
                scc_time_ms: self.scc_time.as_secs_f64() * 1000.0,
                term_propagation_time_ms: self.term_propagation_time.as_secs_f64() * 1000.0,
                edge_instantiation_time_ms: self.edge_instantiation_time.as_secs_f64() * 1000.0,
            },
            query_propagation_time_ms: self.query_propagation_time.as_secs_f64() * 1000.0,
            points_to_queries: points_to_queries.iter().count(),
            pointed_by_queries: self.pointed_by_queries.termset.len(),
            term_set_dedup_stats,
        })
    }
}

struct Edges<C: ContextSelector, S> {
    subset: Vec<HashMap<IntegerTerm, Offsets>>,
    rev_subset: Vec<HashSet<IntegerTerm>>,
    conds: Vec<ThinVec<CachedCondEntry<C::Context, S>>>,
    loads: Vec<SmallVec<[IntegerTerm; 2]>>,
    stores: Vec<SmallVec<[IntegerTerm; 2]>>,
    addr_ofs: Vec<SmallVec<[IntegerTerm; 2]>>,
    rev_addr_ofs: Vec<SmallVec<[IntegerTerm; 2]>>,
}

impl<C: ContextSelector, S: TermSetTrait> Edges<C, S> {
    fn add_constraint(&mut self, c: Constraint<IntegerTerm>, context: C::Context) {
        match c {
            Constraint::Inclusion { term, node } => {
                // self.sols[node as usize].insert(term);
                self.addr_ofs[term as usize].push(node);
                self.rev_addr_ofs[node as usize].push(term);
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
                self.loads[right as usize].push(cond_node);
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
                self.stores[left as usize].push(cond_node);
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
        let res = insert_edge(&mut self.subset, left, right, offset);
        if res {
            self.rev_subset[right as usize].insert(left);
        }
        res
    }

    fn resize(&mut self, size: usize) {
        self.subset.resize_with(size, HashMap::new);
        self.rev_subset.resize_with(size, HashSet::new);
        self.addr_ofs.resize_with(size, SmallVec::new);
        self.rev_addr_ofs.resize_with(size, SmallVec::new);
        self.conds.resize_with(size, ThinVec::new);
        self.loads.resize_with(size, SmallVec::new);
        self.stores.resize_with(size, SmallVec::new);
    }

    fn scc_edges<'e>(
        &'e self,
        direction: SccDirection,
        mode: EdgeVisitMode,
    ) -> SccEdgesAdapter<'e, C, S> {
        SccEdgesAdapter {
            edges: self,
            direction,
            mode,
        }
    }
}

#[derive(Clone, Copy)]
enum SccDirection {
    Forward,
    Backward,
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum EdgeVisitMode {
    OnlyNonWeighted,
    WithWeighted,
}

struct SccEdgesAdapter<'e, C: ContextSelector, S> {
    edges: &'e Edges<C, S>,
    direction: SccDirection,
    mode: EdgeVisitMode,
}

impl<'e, C: ContextSelector, S> SccEdges for SccEdgesAdapter<'e, C, S> {
    fn node_count(&self) -> usize {
        self.edges.subset.len()
    }

    fn successors(
        &self,
        node: IntegerTerm,
    ) -> impl Iterator<Item = (IntegerTerm, super::scc::SccEdgeWeight)> {
        let edges_iter = match self.direction {
            SccDirection::Forward => Either::Left(self.edges.subset[node as usize].iter()),
            SccDirection::Backward => Either::Right(
                self.edges.rev_subset[node as usize]
                    .iter()
                    .map(move |w| (w, self.edges.subset[*w as usize].get(&node).unwrap())),
            ),
        };
        edges_iter.filter_map(|(w, offsets)| {
            if self.mode == EdgeVisitMode::OnlyNonWeighted {
                return offsets
                    .scc_edge_only_unweighted()
                    .map(|weight| (*w, weight));
            }
            Some((*w, offsets.scc_edge_weight()))
        })
    }
}

fn get_representative_no_mutation(parents: &[IntegerTerm], child: IntegerTerm) -> IntegerTerm {
    let mut node = child;
    loop {
        let parent = parents[node as usize];
        if parent == node {
            return node;
        }
        node = parent;
    }
}

fn get_representative(parents: &mut [IntegerTerm], child: IntegerTerm) -> IntegerTerm {
    let parent = parents[child as usize];
    if parent == child {
        return child;
    }
    let representative = get_representative(parents, parent);
    parents[child as usize] = representative;
    representative
}

pub type HashTidalPropagationSolver<C> = TidalPropagationSolver<HashSet<IntegerTerm>, C>;
pub type RoaringTidalPropagationSolver<C> = TidalPropagationSolver<RoaringBitmap, C>;
pub type SharedBitVecTidalPropagationSolver<C> = TidalPropagationSolver<SharedBitVec, C>;
pub type RcRoaringTidalPropagationSolver<C> = TidalPropagationSolver<RcTermSet<RoaringBitmap>, C>;
pub type RcSharedBitVecTidalPropagationSolver<C> =
    TidalPropagationSolver<RcTermSet<SharedBitVec>, C>;

#[derive(Clone)]
pub struct TidalPropagationNode<T, C> {
    term: T,
    context: C,
    count: usize,
}

impl<T: Display, C: Display> Display for TidalPropagationNode<T, C> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}: {} ({})", self.context, self.term, self.count)
    }
}

impl<T, S, C> TidalPropagationSolverState<T, S, C>
where
    T: Display + Debug + Clone + PartialEq + Eq + Hash,
    S: TermSetTrait<Term = IntegerTerm>,
    C: ContextSelector,
{
    fn get_representative_counts(&self) -> HashMap<IntegerTerm, Node<usize>> {
        let mut reps = HashMap::new();
        for n in 0..self.sols.len() {
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

impl<T, S, C> Graph for TidalPropagationSolverState<T, S, C>
where
    T: Display + Debug + Clone + PartialEq + Eq + Hash,
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    C: ContextSelector + Clone,
    C::Context: Display,
{
    type Node = TidalPropagationNode<T, C::Context>;
    type Weight = OffsetWeight;

    fn nodes(&self) -> Vec<Node<Self::Node>> {
        let reps = self.get_representative_counts();
        reps.into_iter()
            .map(|(t, node)| {
                let inner = TidalPropagationNode {
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

            let inner = TidalPropagationNode {
                term: self.context_state.concrete_to_input(from as IntegerTerm),
                context: self
                    .context_state
                    .context_of_concrete_index(from as IntegerTerm),
                count: reps.get(&(from as u32)).unwrap().inner,
            };
            let from_node = Node { inner, id: from };

            for (to, weights) in outgoing {
                let inner = TidalPropagationNode {
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
struct TidalPropSerialize {
    #[serde(flatten)]
    wave_prop: WavePropSerialize,
    query_propagation_time_ms: f64,
    points_to_queries: usize,
    pointed_by_queries: usize,
    #[serde(flatten)]
    term_set_dedup_stats: Option<Box<dyn erased_serde::Serialize>>,
}

#[cfg(test)]
mod tests {
    use llvm_ir::Module;

    use crate::analysis::{Config, PointsToAnalysis};
    use crate::solver::tidal_prop::get_representative_no_mutation;
    use crate::solver::{try_offset_term, CallStringSelector, Demands, IntegerTerm, TermSetTrait};

    use super::{offsetable_terms, SharedBitVecTidalPropagationSolver};

    #[test]
    fn tidal_invariants() {
        let solver = SharedBitVecTidalPropagationSolver::new();
        let module =
            Module::from_bc_path("benchmarks/make/bench.bc").expect("Error parsing bc file");
        // let demands = vec![Demand::PointsTo(Cell::Var(VarIdent::new_local(
        //     &Name::Number(6),
        //     "eval_buffer",
        // )))];
        let state = PointsToAnalysis::run(
            &solver,
            &module,
            CallStringSelector::<1>::new(),
            // Demands::List(demands),
            Demands::All,
            &Config::default(),
        )
        .into_solution();

        // Points-to invariants
        for i in 0..state.sols.len() {
            if state.points_to_queries.test(i) {
                for &t in state.edges.rev_addr_ofs[i].iter() {
                    assert!(state.sols[i].contains(t));
                }
                for j in &state.edges.loads[i] {
                    assert!(state
                        .points_to_queries
                        .test(get_representative_no_mutation(&state.parents, *j) as usize));
                }
            }
            for (j, offsets) in &state.edges.subset[i as usize] {
                if state.points_to_queries.test(*j as usize) {
                    assert!(state.points_to_queries.test(i as usize));
                    for offset in offsets.iter() {
                        for t in state.sols[i as usize].iter() {
                            if let Some(t) =
                                try_offset_term(t, state.term_types[t as usize], offset)
                            {
                                assert!(state.sols[*j as usize].contains(t));
                            }
                        }
                    }
                }
            }
        }
        // Pointed-by invariants
        for i in 0..state.sols.len() {
            if state.pointed_by_queries.contains(i as IntegerTerm) {
                for x in &state.edges.addr_ofs[i as usize] {
                    assert!(state.sols[*x as usize].contains(i as IntegerTerm));
                }
                for t in
                    offsetable_terms(i as u32, &state.context_state, &state.abstract_rev_offsets)
                {
                    assert!(state.pointed_by_queries.contains(t));
                }
            }
            for t in state.sols[i as usize].iter() {
                if state.pointed_by_queries.contains(t) {
                    for cond in &state.edges.stores[i] {
                        let cond_rep =
                            get_representative_no_mutation(&state.parents, *cond) as usize;
                        assert!(
                            state
                                .points_to_queries
                                .test(
                                    cond_rep
                                ),
                            "{:?} ({i}) points to {:?} ({t}). *{:?} ({cond}) (query: {}) [rep {:?} ({cond_rep})] <- {:?} ({i})",
                            state.context_state.concrete_to_input(i as u32),
                            state.context_state.concrete_to_input(t),
                            state.context_state.concrete_to_input(*cond),
                            state.points_to_queries.test(*cond as usize),
                            state.context_state.concrete_to_input(cond_rep as u32),
                            state.context_state.concrete_to_input(i as u32),
                        );
                    }
                    assert!(
                        state.visited_pointed_by.test(i),
                        "{:?} ({i}) points to {:?} ({t})",
                        state.context_state.concrete_to_input(i as u32),
                        state.context_state.concrete_to_input(t),
                    );
                }
                for (j, offsets) in &state.edges.subset[i as usize] {
                    for offset in offsets.iter() {
                        if let Some(t2) = try_offset_term(t, state.term_types[t as usize], offset) {
                            if state.pointed_by_queries.contains(t2) {
                                assert!(
                                    state.sols[*j as usize].contains(t2),
                                    "{:?} ({i}) visited: {} -> {:?} ({j}) visited: {}\n{:?} ({t}) + {offset} = {:?} ({t2})",
                                    state.context_state.concrete_to_input(i as u32),
                                    state.visited_pointed_by.test(i),
                                    state.context_state.concrete_to_input(*j),
                                    state.visited_pointed_by.test(*j as usize),
                                    state.context_state.concrete_to_input(t),
                                    state.context_state.concrete_to_input(t2),
                                );
                            }
                        }
                    }
                }
            }
            if state.parents[i] == i as u32 && state.visited_pointed_by.test(i) {
                assert!(state.sols[i].overlaps(state.pointed_by_queries.get_termset()));
            }
        }
        for (fun_idx, template) in state.context_state.templates.iter().enumerate() {
            let mut should_have_query = false;
            'outer: for (_, start) in &state.context_state.instantiated_contexts[fun_idx] {
                for ret in *start..*start + template.num_return_terms as u32 {
                    if state.sols[ret as usize].overlaps(state.pointed_by_queries.get_termset()) {
                        should_have_query = true;
                        break 'outer;
                    }
                }
                for param in *start + template.num_return_terms
                    ..*start + template.num_return_terms + template.num_parameter_terms as u32
                {
                    if state.points_to_queries.test(param as usize) {
                        should_have_query = true;
                        break 'outer;
                    }
                }
            }
            let fun_term = state.context_state.templates[0].start_index + fun_idx as u32;

            assert!(
                !should_have_query || state.pointed_by_queries.contains(fun_term),
                "fun_term: {:?} ({}), has points-to: {}, rep: {:?}",
                state.context_state.concrete_to_input(fun_term),
                fun_term,
                state.points_to_queries.test(fun_term as usize),
                state.parents[fun_term as usize],
            );
        }
    }
}
