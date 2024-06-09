use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;
use std::marker::PhantomData;
use std::mem;
use std::time::Duration;

use bitvec::bitvec;
use bitvec::prelude::*;
use either::Either;
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use once_cell::unsync::Lazy;
use roaring::RoaringBitmap;
use serde::Serialize;
use smallvec::SmallVec;

use super::context::{ContextState, TemplateTerm};
use super::context_wave_prop::WavePropSerialize;
use super::shared_bitvec::SharedBitVec;
use super::{
    edges_between, try_offset_term, CallSite, Constraint, ContextSelector, Demand,
    DemandContextSensitiveInput, IntegerTerm, Offsets, OnlyOnceStack, Solver, SolverExt,
    SolverSolution, TermSetTrait, TermType,
};
use crate::solver::Demands;
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
pub struct TidalPropagationSolver<S, C>(PhantomData<S>, PhantomData<C>);

impl<S, C> TidalPropagationSolver<S, C> {
    pub fn new() -> Self {
        Self(PhantomData, PhantomData)
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
    p_cache_left: Vec<S>,
    p_cache_right: Vec<S>,
    p_cache_call_dummies: Vec<S>,
    context_state: ContextState<T, C>,
    edges: Edges<C>,
    term_types: Vec<TermType>,
    abstract_rev_offsets: Vec<SmallVec<[u32; 2]>>,
    parents: Vec<IntegerTerm>,
    points_to_queries: uniset::BitSet,
    pointed_by_queries: PointedByQueries<S>,
    visited_pointed_by: uniset::BitSet,
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
            changed = self.term_propagation();
            self.term_propagation_time += term_propagation_start.elapsed();

            let edge_instantiation_start = std::time::Instant::now();
            changed |= self.add_edges_after_wave_prop();
            self.edge_instantiation_time += edge_instantiation_start.elapsed();

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
        self.scc(
            SccDirection::Forward,
            EdgeVisitMode::OnlyNonWeighted,
            CollapseMode::On,
            (0..self.term_count() as IntegerTerm).collect(),
            |_, _, _| {},
        );
    }

    fn query_propagation(&mut self) {
        let mut changed = true;
        let mut iters = 0;
        while changed {
            let mut new_queries = 0;
            changed = false;

            let mut pt_starting_nodes = self
                .new_incoming
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
            self.scc(
                SccDirection::Backward,
                EdgeVisitMode::WithWeighted,
                CollapseMode::Off,
                pt_starting_nodes,
                |v, state, to_visit| {
                    if state.points_to_queries.test(v as usize) {
                        return;
                    }
                    state.points_to_queries.set(v as usize);
                    new_queries += 1;
                    state.new_pointed_by_queries.push(v);

                    for &w in &state.edges.rev_addr_ofs[v as usize] {
                        state.sols[v as usize].insert(w);
                    }

                    for &w in &state.edges.rev_subset[v as usize] {
                        if state.p_old[w as usize].len() > 0 {
                            let p_pt_old = &state.p_old[w as usize];
                            let p_pt_old_vec =
                                Lazy::new(|| p_pt_old.iter().collect::<Vec<IntegerTerm>>());
                            for offset in state.edges.subset[w as usize][&v].iter() {
                                propagate_terms_into(
                                    p_pt_old,
                                    p_pt_old_vec.iter().copied(),
                                    offset,
                                    &mut state.sols[v as usize],
                                    &state.term_types,
                                );
                            }
                        }
                    }

                    for &w in &state.edges.loads[v as usize] {
                        to_visit.push(get_representative(state.parents, w))
                    }

                    for &w in &state.return_and_parameter_children[v as usize] {
                        let (fun_index, relative_index) = state
                            .context_state
                            .get_function_and_relative_index_from_concrete_index(w);
                        let fun_index = fun_index.expect("Term should be in a function");
                        let template = &state.context_state.templates[fun_index as usize];
                        if relative_index >= template.num_return_terms
                            && relative_index
                                < template.num_return_terms + template.num_parameter_terms
                        {
                            state
                                .new_pointed_by_queries
                                .push(state.context_state.templates[0].start_index + fun_index);
                        }
                    }
                },
            );

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

            for v in self.new_incoming.drain(..) {
                let v = get_representative(&mut self.parents, v);
                if self.sols[v as usize].overlaps(self.pointed_by_queries.get_termset()) {
                    pb_starting_nodes.push(v);
                }
            }

            // Pointed-by query propagation
            self.scc(
                SccDirection::Forward,
                EdgeVisitMode::OnlyNonWeighted,
                CollapseMode::Off,
                pb_starting_nodes,
                |v, state, to_visit| {
                    if state.visited_pointed_by.test(v as usize) {
                        return;
                    }
                    // println!("{}, {}", to_visit.len(), state.p_old.len());
                    state.visited_pointed_by.set(v as usize);
                    local_new_pb_queries.push(v);

                    for q in offsetable_terms(v, &state.context_state, state.abstract_rev_offsets) {
                        // TODO: deduplicate?
                        local_new_pb_queries.push(q);
                        for &t in &state.edges.addr_ofs[q as usize] {
                            to_visit.push(get_representative(&mut state.parents, t));
                        }
                    }

                    for &w in &state.edges.addr_ofs[v as usize] {
                        let w = get_representative(state.parents, w);
                        to_visit.push(w);
                    }

                    for &w in &state.edges.stores[v as usize] {
                        state.new_points_to_queries.push(w);
                        changed = true;
                    }

                    for &w in &state.return_and_parameter_children[v as usize] {
                        let (fun_index, relative_index) = state
                            .context_state
                            .get_function_and_relative_index_from_concrete_index(w);
                        let fun_index = fun_index.expect("Term should be in a function");
                        let num_return_terms =
                            state.context_state.templates[fun_index as usize].num_return_terms;
                        if relative_index < num_return_terms {
                            let fun_term = state.context_state.templates[0].start_index + fun_index;
                            local_new_pb_queries.push(fun_term);
                            for &t in &state.edges.addr_ofs[fun_term as usize] {
                                to_visit.push(get_representative(&mut state.parents, t));
                            }
                        }
                    }
                },
            );

            let mut new_pointed_by_queries_bitset =
                BitVec::<usize>::repeat(false, self.term_count());

            for v in local_new_pb_queries {
                if !new_pointed_by_queries_bitset[v as usize] {
                    new_pointed_by_queries_bitset.set(v as usize, true);
                    for &w in &self.edges.addr_ofs[v as usize] {
                        let w = get_representative(&mut self.parents, w);
                        self.sols[w as usize].insert(v);
                    }
                    self.pointed_by_queries.insert(v);
                }
            }
            iters += 1;
        }
        eprintln!("{iters} query iterations");
    }

    fn term_propagation(&mut self) -> bool {
        let mut changed = false;

        let top_order = self.scc(
            SccDirection::Forward,
            EdgeVisitMode::OnlyNonWeighted,
            CollapseMode::On,
            (0..self.term_count() as IntegerTerm).collect(),
            |_, _, _| {},
        );

        for &v in top_order.iter().rev() {
            // Skip if no new terms in solution set
            if self.sols[v as usize].len() == self.p_old[v as usize].len() {
                continue;
            }
            changed = true;
            let p_dif = self.sols[v as usize].weak_difference(&self.p_old[v as usize]);
            let p_dif_vec = Lazy::new(|| p_dif.iter().collect::<Vec<IntegerTerm>>());
            self.p_old[v as usize].union_assign(&p_dif);

            for (&w, offsets) in &self.edges.subset[v as usize] {
                let mut should_set_new_incoming = false;
                for o in offsets.iter() {
                    if o == 0 {
                        self.sols[w as usize].union_assign(&p_dif);
                    } else {
                        let to_add = p_dif_vec
                            .iter()
                            .filter_map(|&t| try_offset_term(t, self.term_types[t as usize], o));
                        for t in to_add {
                            self.sols[w as usize].insert(t);
                            if self.pointed_by_queries.contains(t) {
                                should_set_new_incoming = true;
                            } else {
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

        changed
    }

    fn add_edges_after_wave_prop(&mut self) -> bool {
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

            let mut sols = self.sols[cond_node as usize].clone();
            if !self.points_to_queries.test(cond_node as usize) {
                sols.intersection_assign(self.pointed_by_queries.get_termset());
            }

            if sols.len() == self.p_cache_call_dummies[i].len() {
                continue;
            }
            let p_new = sols.difference(&self.p_cache_call_dummies[i]);
            self.p_cache_call_dummies[i] = sols;
            for t in p_new.iter() {
                changed |= self
                    .try_offset_and_instantiate(t, Some(&call_site), 0, &context)
                    .is_some();
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

            let mut sols = self.sols[cond_node as usize].clone();
            if !self.points_to_queries.test(cond_node as usize) {
                sols.intersection_assign(self.pointed_by_queries.get_termset());
            }

            if sols.len() == self.p_cache_left[i].len() {
                continue;
            }
            let p_new = sols.difference(&self.p_cache_left[i]);
            self.p_cache_left[i] = sols;
            for t in p_new.iter() {
                if let Some(t) =
                    self.try_offset_and_instantiate(t, call_site.as_ref(), offset, &context)
                {
                    let t = get_representative(&mut self.parents, t);
                    if t == right {
                        continue;
                    }
                    if edges_between(&mut self.edges.subset, t, right).insert(0) {
                        self.sols[right as usize].union_assign(&self.p_old[t as usize]);
                        self.edges.rev_subset[right as usize].insert(t);
                        self.new_incoming.push(right);
                        changed = true;
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

            let mut sols = self.sols[cond_node as usize].clone();
            if !self.points_to_queries.test(cond_node as usize) {
                sols.intersection_assign(self.pointed_by_queries.get_termset());
            }

            if sols.len() == self.p_cache_right[i].len() {
                continue;
            }
            let p_new = sols.difference(&self.p_cache_right[i]);
            self.p_cache_right[i] = sols;
            for t in p_new.iter() {
                if let Some(t) =
                    self.try_offset_and_instantiate(t, call_site.as_ref(), offset, &context)
                {
                    let t = get_representative(&mut self.parents, t);
                    if t == left {
                        continue;
                    }
                    if edges_between(&mut self.edges.subset, left, t).insert(0) {
                        self.sols[t as usize].union_assign(&self.p_old[left as usize]);
                        self.edges.rev_subset[t as usize].insert(left);
                        self.new_incoming.push(t);
                        changed = true;
                    }
                }
            }
        }
        changed
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
                }
            }
        }
        index
    }

    fn add_constraint(&mut self, c: Constraint<IntegerTerm>, context: C::Context) {
        let rep_c = c.map_terms(|&t| get_representative(&mut self.parents, t));
        self.edges.add_constraint(rep_c, context);
        match c {
            Constraint::UnivCondSubsetLeft { .. } => self.p_cache_left.push(S::new()),
            Constraint::UnivCondSubsetRight { .. } => self.p_cache_right.push(S::new()),
            Constraint::CallDummy { .. } => self.p_cache_call_dummies.push(S::new()),
            _ => {}
        }
    }

    fn scc<F>(
        &mut self,
        direction: SccDirection,
        visit_weighted: EdgeVisitMode,
        collapse_cycles: CollapseMode,
        initial_nodes: Vec<IntegerTerm>,
        mut visit_handler: F,
    ) -> Vec<IntegerTerm>
    where
        F: FnMut(IntegerTerm, &mut SccVisitState<T, S, C>, &mut OnlyOnceStack),
    {
        let node_count = self.term_count();

        let to_visit = OnlyOnceStack::from_nodes(initial_nodes, node_count);

        let mut internal_state = SccInternalState {
            direction,
            visit_weighted,
            node_count,
            iteration: 0,
            d: vec![0; node_count],
            r: vec![None; node_count],
            c: bitvec![0; node_count],
            s: vec![],
            to_visit,
            top_order: vec![],
        };

        let mut visit_state = SccVisitState {
            sols: &mut self.sols,
            term_types: &self.term_types,
            abstract_rev_offsets: &self.abstract_rev_offsets,
            p_old: &mut self.p_old,
            context_state: &self.context_state,
            edges: &self.edges,
            points_to_queries: &mut self.points_to_queries,
            visited_pointed_by: &mut self.visited_pointed_by,
            return_and_parameter_children: &self.return_and_parameter_children,
            new_points_to_queries: &mut self.new_points_to_queries,
            new_pointed_by_queries: &mut self.new_pointed_by_queries,
            parents: &mut self.parents,
        };

        while let Some(v) = internal_state.to_visit.pop() {
            if internal_state.d[v as usize] == 0 {
                visit(&mut internal_state, &mut visit_state, &mut visit_handler, v);
            }
        }

        if collapse_cycles == CollapseMode::Off {
            return internal_state.top_order;
        }

        let mut nodes = vec![];
        let mut components: HashMap<IntegerTerm, (IntegerTerm, u32)> = HashMap::new();
        for v in 0..internal_state.node_count as u32 {
            if let Some(r_v) = internal_state.r[v as usize] {
                let edge_count = self.edges.subset[v as usize].len() as u32;
                if edge_count == 0 {
                    continue;
                }
                nodes.push((v, r_v));
                if let Err(mut cur) = components.try_insert(r_v, (v, edge_count)) {
                    let (cur_best, best_edge_count) = cur.entry.get_mut();
                    if edge_count > *best_edge_count {
                        *cur_best = v;
                        *best_edge_count = edge_count;
                    }
                }
            }
        }
        for (v, r_v) in nodes {
            let &(rep, _) = components.get(&r_v).unwrap();
            if v != rep {
                self.unify(v, |w| {
                    components
                        .get(&internal_state.r[w as usize].unwrap())
                        .map(|(rep, _)| *rep)
                        .unwrap_or(w)
                });
            }
        }

        internal_state.top_order
    }

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

            let other = if other == child { parent } else { other };
            let other_parent = parent_fn(other);

            if offsets.has_non_zero() || other_parent != parent {
                let other_term_set = &mut self.sols[other as usize];
                let existing_offsets = self.edges.subset[parent as usize]
                    .entry(other_parent)
                    .or_default();
                for o in offsets.iter() {
                    if existing_offsets.contains(o) {
                        continue;
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
                                self.new_incoming.push(other);
                            } else {
                                self.edges.addr_ofs[t as usize].push(other);
                                self.edges.rev_addr_ofs[other as usize].push(t);
                            }
                        }
                    }
                    existing_offsets.insert(o);
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
                        .or_default()
                        .union_assign(&orig_edges);
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
        if self.edges.rev_subset[parent as usize].remove(&(child as IntegerTerm)) {
            self.edges.rev_subset[parent as usize].insert(parent as IntegerTerm);
        }

        let child_return_and_parameter_children =
            mem::take(&mut self.return_and_parameter_children[child as usize]);
        self.return_and_parameter_children[parent as usize]
            .extend_from_slice(&child_return_and_parameter_children);

        let child_rev_addr_ofs = mem::take(&mut self.edges.rev_addr_ofs[child as usize]);
        self.edges.rev_addr_ofs[parent as usize].extend_from_slice(child_rev_addr_ofs.as_slice());
        let child_loads = mem::take(&mut self.edges.loads[child as usize]);
        self.edges.loads[parent as usize].extend_from_slice(child_loads.as_slice());
        let child_stores = mem::take(&mut self.edges.stores[child as usize]);
        self.edges.stores[parent as usize].extend_from_slice(child_stores.as_slice());

        self.parents[child as usize] = parent;
        self.p_old[child as usize] = S::new();
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
        let num_abstract = context_state.mapping.terms.len();

        let mut edges = Edges {
            addr_ofs: vec![SmallVec::new(); num_terms],
            rev_addr_ofs: vec![SmallVec::new(); num_terms],
            subset: vec![HashMap::new(); num_terms],
            rev_subset: vec![HashSet::new(); num_terms],
            left_conds: vec![],
            right_conds: vec![],
            call_dummies: vec![],
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
            let fun_term = (input.input.global.terms.len() + i) as IntegerTerm;
            term_types[fun_term as usize] = function_term_info.term_type;
            edges.add_constraint(
                Constraint::Inclusion {
                    term: fun_term,
                    node: function_term_info.pointer_node,
                },
                empty_context.clone(),
            );
        }

        let num_abstract_terms = context_state.mapping.terms.len();
        let mut state = TidalPropagationSolverState {
            edges,
            context_state,
            sols: vec![S::new(); num_terms],
            p_old: vec![S::new(); num_terms],
            p_cache_left: vec![],
            p_cache_right: vec![],
            p_cache_call_dummies: vec![],
            term_types,
            abstract_rev_offsets,
            parents: Vec::from_iter(0..num_terms as IntegerTerm),
            points_to_queries: uniset::BitSet::new(),
            pointed_by_queries: PointedByQueries::new(num_terms),
            visited_pointed_by: uniset::BitSet::new(),
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
        };

        for c in &input.input.global.constraints {
            state.add_constraint(
                state.context_state.mapping.translate_constraint(c),
                empty_context.clone(),
            );
        }

        match input.demands {
            Demands::All => {
                state.abstract_pointed_by_queries = bitvec::bitvec![1; num_abstract_terms];
                for term in 0..num_terms as u32 {
                    state.new_pointed_by_queries.push(term);
                }
            }
            Demands::CallGraphPointsTo => {
                let function_constraints = input
                    .input
                    .functions
                    .iter()
                    .flat_map(|f| &f.constrained_terms.constraints);
                for constraint in input
                    .input
                    .global
                    .constraints
                    .iter()
                    .chain(function_constraints)
                {
                    if let Constraint::CallDummy { cond_node, .. } = constraint {
                        let abstract_term = state.context_state.mapping.term_to_integer(cond_node);
                        state
                            .abstract_points_to_queries
                            .set(abstract_term as usize, true);
                        if let Some(term) = state.context_state.term_to_concrete_global(cond_node) {
                            state.new_points_to_queries.push(term);
                        }
                    }
                }
            }
            Demands::CallGraphPointedBy => {
                for i in 0..fun_term_infos.len() {
                    let fun_term = (input.input.global.terms.len() + i) as IntegerTerm;
                    state.new_pointed_by_queries.push(fun_term);
                }
            }
            Demands::List(demands) => {
                for demand in demands {
                    match demand {
                        Demand::PointsTo(term) => {
                            let abstract_term = state.context_state.mapping.term_to_integer(&term);
                            state
                                .abstract_points_to_queries
                                .set(abstract_term as usize, true);
                            if let Some(term) = state.context_state.term_to_concrete_global(&term) {
                                state.new_points_to_queries.push(term);
                            }
                        }
                        Demand::PointedBy(term) => {
                            let abstract_term = state.context_state.mapping.term_to_integer(&term);
                            state
                                .abstract_pointed_by_queries
                                .set(abstract_term as usize, true);
                            if let Some(term) = state.context_state.term_to_concrete_global(&term) {
                                state.new_pointed_by_queries.push(term);
                            }
                        }
                    }
                }
            }
        }

        // for entrypoint in entrypoints {
        //     state.get_or_instantiate_function(entrypoint, empty_context.clone());
        // }
        for entrypoint in 0..state.context_state.templates.len() {
            state.get_or_instantiate_function(entrypoint, empty_context.clone());
        }

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
                scc_time_ms: self.scc_time.as_millis() as u64,
                term_propagation_time_ms: self.term_propagation_time.as_millis() as u64,
                edge_instantiation_time_ms: self.edge_instantiation_time.as_millis() as u64,
            },
            query_propagation_time_ms: self.query_propagation_time.as_millis() as u64,
            points_to_queries: points_to_queries.iter().count(),
            pointed_by_queries: self.pointed_by_queries.termset.len(),
        })
    }
}

struct Edges<C: ContextSelector> {
    subset: Vec<HashMap<IntegerTerm, Offsets>>,
    rev_subset: Vec<HashSet<IntegerTerm>>,
    left_conds: Vec<CondLeftEntry<C::Context>>,
    right_conds: Vec<CondRightEntry<C::Context>>,
    call_dummies: Vec<CallDummyEntry<C::Context>>,
    loads: Vec<SmallVec<[IntegerTerm; 2]>>,
    stores: Vec<SmallVec<[IntegerTerm; 2]>>,
    addr_ofs: Vec<SmallVec<[IntegerTerm; 2]>>,
    rev_addr_ofs: Vec<SmallVec<[IntegerTerm; 2]>>,
}

impl<C: ContextSelector> Edges<C> {
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
                self.left_conds.push(CondLeftEntry {
                    cond_node,
                    right,
                    offset,
                    call_site,
                    context,
                });
                self.loads[right as usize].push(cond_node);
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
                self.stores[left as usize].push(cond_node);
            }
            Constraint::CallDummy {
                cond_node,
                arguments: _,
                result_node: _,
                call_site,
            } => {
                self.call_dummies.push(CallDummyEntry {
                    cond_node,
                    call_site,
                    context,
                });
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

    fn resize(&mut self, size: usize) {
        self.subset.resize_with(size, HashMap::new);
        self.rev_subset.resize_with(size, HashSet::new);
        self.addr_ofs.resize_with(size, SmallVec::new);
        self.rev_addr_ofs.resize_with(size, SmallVec::new);
        self.loads.resize_with(size, SmallVec::new);
        self.stores.resize_with(size, SmallVec::new);
    }
}

fn visit<'a, F, T, S, C>(
    internal: &mut SccInternalState,
    visit_state: &mut SccVisitState<'a, T, S, C>,
    visit_handler: &mut F,
    v: IntegerTerm,
) where
    for<'b> F: FnMut(IntegerTerm, &mut SccVisitState<'b, T, S, C>, &mut OnlyOnceStack),
    C: ContextSelector,
{
    if internal.d[v as usize] != 0 {
        return;
    }
    visit_handler(v, visit_state, &mut internal.to_visit);

    internal.iteration += 1;
    internal.d[v as usize] = internal.iteration;
    internal.r[v as usize] = Some(v);

    let edges_iter = match internal.direction {
        SccDirection::Forward => Either::Left(visit_state.edges.subset[v as usize].iter()),
        SccDirection::Backward => Either::Right(
            visit_state.edges.rev_subset[v as usize]
                .iter()
                .map(|w| (w, visit_state.edges.subset[*w as usize].get(&v).unwrap())),
        ),
    };

    for (&w, offsets) in edges_iter {
        if !offsets.contains(0) {
            debug_assert!(offsets.has_non_zero());
            if internal.visit_weighted == EdgeVisitMode::WithWeighted {
                internal.to_visit.push(w);
            }
            continue;
        }

        if internal.d[w as usize] == 0 {
            visit(internal, visit_state, visit_handler, w);
        }
        if !internal.c[w as usize] {
            let r_v = internal.r[v as usize].unwrap();
            let r_w = internal.r[w as usize].unwrap();
            internal.r[v as usize] = Some(if internal.d[r_v as usize] < internal.d[r_w as usize] {
                r_v
            } else {
                r_w
            });
        }
    }

    if internal.r[v as usize] == Some(v) {
        internal.c.set(v as usize, true);
        while let Some(&w) = internal.s.last() {
            if internal.d[w as usize] <= internal.d[v as usize] {
                break;
            }
            internal.s.pop();
            internal.c.set(w as usize, true);
            internal.r[w as usize] = Some(v);
        }
        internal.top_order.push(v);
    } else {
        internal.s.push(v);
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

#[derive(PartialEq, Eq, Clone, Copy)]
enum CollapseMode {
    On,
    Off,
}

struct SccInternalState {
    direction: SccDirection,
    visit_weighted: EdgeVisitMode,
    node_count: usize,
    iteration: usize,
    /// 0 means not visited.
    d: Vec<usize>,
    r: Vec<Option<IntegerTerm>>,
    c: BitVec,
    s: Vec<IntegerTerm>,
    to_visit: OnlyOnceStack,
    top_order: Vec<IntegerTerm>,
}

struct SccVisitState<'a, T, S, C: ContextSelector> {
    sols: &'a mut [S],
    term_types: &'a [TermType],
    abstract_rev_offsets: &'a [SmallVec<[u32; 2]>],
    p_old: &'a [S],
    context_state: &'a ContextState<T, C>,
    edges: &'a Edges<C>,
    points_to_queries: &'a mut uniset::BitSet,
    visited_pointed_by: &'a mut uniset::BitSet,
    return_and_parameter_children: &'a [SmallVec<[IntegerTerm; 2]>],
    new_points_to_queries: &'a mut Vec<IntegerTerm>,
    new_pointed_by_queries: &'a mut Vec<IntegerTerm>,
    parents: &'a mut [IntegerTerm],
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

#[cfg(test)]
mod tests {
    use llvm_ir::{Module, Name};

    use crate::analysis::{Cell, Config, PointsToAnalysis};
    use crate::module_visitor::VarIdent;
    use crate::solver::tidal_prop::get_representative_no_mutation;
    use crate::solver::{
        try_offset_term, ContextInsensitiveSelector, Demand, Demands, IntegerTerm, TermSetTrait,
    };

    use super::{offsetable_terms, SharedBitVecTidalPropagationSolver};

    #[test]
    fn tidal_invariants() {
        let solver = SharedBitVecTidalPropagationSolver::new();
        let module =
            Module::from_bc_path("benchmarks/make/bench.bc").expect("Error parsing bc file");
        let demands = vec![Demand::PointsTo(Cell::Var(VarIdent::new_local(
            &Name::Number(6),
            "eval_buffer",
        )))];
        let state = PointsToAnalysis::run(
            &solver,
            &module,
            ContextInsensitiveSelector,
            Demands::List(demands),
            &Config::default(),
        )
        .into_solution();

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
                        state.context_state.concrete_to_input(t)
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

#[derive(Serialize)]
struct TidalPropSerialize {
    #[serde(flatten)]
    wave_prop: WavePropSerialize,
    query_propagation_time_ms: u64,
    points_to_queries: usize,
    pointed_by_queries: usize,
}
