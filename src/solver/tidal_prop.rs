use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;
use std::marker::PhantomData;
use std::mem;

use bitvec::bitvec;
use bitvec::prelude::*;
use either::Either;
use hashbrown::{HashMap, HashSet};
use once_cell::unsync::Lazy;
use roaring::RoaringBitmap;
use smallvec::SmallVec;

use super::context::{ContextState, TemplateTerm};
use super::shared_bitvec::SharedBitVec;
use super::{
    edges_between, try_offset_term, CallSite, Constraint, ContextSelector, Demand,
    DemandContextSensitiveInput, IntegerTerm, Offsets, Solver, SolverExt, SolverSolution,
    TermSetTrait, TermType,
};
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

pub struct TidalPropagationSolverState<T, S, C: ContextSelector> {
    sols: Vec<S>,
    p_old_points_to: Vec<S>,
    p_old_pointed_by: Vec<S>,
    p_cache_left: Vec<S>,
    p_cache_right: Vec<S>,
    p_cache_call_dummies: Vec<S>,
    context_state: ContextState<T, C>,
    edges: Edges<C>,
    term_types: Vec<TermType>,
    abstract_rev_offsets: Vec<SmallVec<[u32; 2]>>,
    parents: Vec<IntegerTerm>,
    points_to_queries: uniset::BitSet,
    pointed_by_queries: S,
    visited_pointed_by: uniset::BitSet,
    is_return_or_parameter: BitVec,
    abstract_points_to_queries: BitVec,
    abstract_pointed_by_queries: BitVec,
    new_points_to_queries: Vec<IntegerTerm>,
    new_pointed_by_queries: Vec<IntegerTerm>,
    new_incoming: Vec<IntegerTerm>,
}

impl<T, S, C: ContextSelector> TidalPropagationSolverState<T, S, C> {
    fn term_count(&self) -> usize {
        self.sols.len()
    }
}

impl<T, S, C> TidalPropagationSolverState<T, S, C>
where
    C: ContextSelector,
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = u32> + Debug,
{
    fn run_tidal_propagation(&mut self) {
        let mut iters = 0u64;

        let mut changed = true;
        while changed {
            iters += 1;
            changed = self.points_to_propagation();

            // let mut new_pbs = HashSet::new();
            // for &i in self.new_pointed_by_queries.iter() {
            //     new_pbs.insert(self.context_state.concrete_to_input(i));
            // }

            changed |= self.pointed_by_propagation();
            changed |= self.add_edges_after_wave_prop();

            // let mut pts = HashSet::new();
            // for i in self.points_to_queries.iter() {
            //     pts.insert(self.context_state.concrete_to_input(i as IntegerTerm));
            // }
            // let mut new_pts = HashSet::new();
            // for &i in self.new_points_to_queries.iter() {
            //     new_pts.insert(self.context_state.concrete_to_input(i as IntegerTerm));
            // }
            // let mut pbs = HashSet::new();
            // for i in self.pointed_by_queries.iter() {
            //     pbs.insert(self.context_state.concrete_to_input(i));
            // }
            // let edges = self.edges.subset.iter().enumerate().flat_map(|(f, e)| {
            //     let ctx = &self.context_state;
            //     e.iter().flat_map(move |(t, o)| {
            //         o.iter().map(move |o| {
            //             (
            //                 ctx.concrete_to_input(f as u32),
            //                 o,
            //                 ctx.concrete_to_input(*t),
            //             )
            //         })
            //     })
            // });

            // println!("Points-to queries: {:?}", pts);
            // println!("New points-to queries: {:?}", new_pts);
            // println!("Pointed-by queries: {:?}", pbs);
            // println!("New pointed-by queries: {:?}", new_pbs);
            // println!("Edges: {:?}", edges.collect::<Vec<_>>());

            println!("Iteration {iters}");
        }

        println!("Iterations: {}", iters);
    }

    fn points_to_propagation(&mut self) -> bool {
        let mut changed = false;
        let top_order = self.scc(
            SccDirection::Backward,
            true,
            self.points_to_queries
                .iter()
                .map(|t| t as IntegerTerm)
                .chain(self.new_points_to_queries.iter().copied())
                .collect(),
            |v, state, to_visit| {
                if state.points_to_queries.test(v as usize) {
                    return;
                }
                state.points_to_queries.set(v as usize);
                state.new_pointed_by_queries.push(v);

                for &w in &state.edges.rev_addr_ofs[v as usize] {
                    state.sols[v as usize].insert(w);
                }

                for &w in &state.edges.rev_subset[v as usize] {
                    if state.p_old_points_to.len() > 0 {
                        let p_pt_old = &state.p_old_points_to[w as usize];
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

                if state.is_return_or_parameter[v as usize] {
                    let (fun_index, relative_index) = state
                        .context_state
                        .get_function_and_relative_index_from_concrete_index(v);
                    let fun_index = fun_index.expect("Term should be in a function");
                    let template = &state.context_state.templates[fun_index as usize];
                    if relative_index >= template.num_return_terms
                        && relative_index < template.num_return_terms + template.num_parameter_terms
                    {
                        state
                            .new_pointed_by_queries
                            .push(state.context_state.templates[0].start_index + fun_index);
                    }
                }
            },
        );

        for &v in top_order.iter() {
            // Skip if no new terms in solution set
            if self.sols[v as usize].len() == self.p_old_points_to[v as usize].len() {
                continue;
            }
            changed = true;
            let p_dif = self.sols[v as usize].weak_difference(&self.p_old_points_to[v as usize]);
            let p_dif_vec = Lazy::new(|| p_dif.iter().collect::<Vec<IntegerTerm>>());
            self.p_old_points_to[v as usize].clone_from(&self.sols[v as usize]);

            for (&w, offsets) in &self.edges.subset[v as usize] {
                if !self.points_to_queries.test(w as usize) {
                    continue;
                }
                for o in offsets.iter() {
                    propagate_terms_into(
                        &p_dif,
                        p_dif_vec.iter().copied(),
                        o,
                        &mut self.sols[w as usize],
                        &self.term_types,
                    );
                }
            }
        }

        self.new_points_to_queries.clear();
        changed
    }

    fn pointed_by_propagation(&mut self) -> bool {
        let mut changed = false;
        let mut new_pointed_by_queries_term_set: S = S::new();

        let mut starting_nodes = vec![];

        for &q in &self.new_pointed_by_queries.clone() {
            for q2 in offsetable_terms(
                q,
                &self.context_state.abstract_indices,
                &self.abstract_rev_offsets,
            ) {
                self.new_pointed_by_queries.push(q2);
            }
        }

        for &q in &self.new_pointed_by_queries {
            for &t in &self.edges.addr_ofs[q as usize] {
                // TODO: deduplicate?
                starting_nodes.push(get_representative(&mut self.parents, t));
            }
        }

        for v in self.new_incoming.drain(..) {
            let v = get_representative(&mut self.parents, v);
            if self.sols[v as usize].overlaps(&self.pointed_by_queries) {
                starting_nodes.push(v);
            }
        }

        let top_order = self.scc(
            SccDirection::Forward,
            false,
            starting_nodes,
            |v, state, to_visit| {
                if state.visited_pointed_by.test(v as usize) {
                    return;
                }
                state.visited_pointed_by.set(v as usize);
                state.new_pointed_by_queries.push(v);

                for q in offsetable_terms(
                    v,
                    &state.context_state.abstract_indices,
                    state.abstract_rev_offsets,
                ) {
                    // TODO: deduplicate?
                    state.new_pointed_by_queries.push(q);
                    for &t in &state.edges.addr_ofs[q as usize] {
                        to_visit.push(get_representative(&mut state.parents, t));
                    }
                }

                for &w in &state.edges.addr_ofs[v as usize] {
                    let w = get_representative(state.parents, w);
                    to_visit.push(w);
                }

                for &w in &state.edges.stores[v as usize] {
                    state
                        .new_points_to_queries
                        .push(get_representative(state.parents, w));
                }

                if state.is_return_or_parameter[v as usize] {
                    let (fun_index, relative_index) = state
                        .context_state
                        .get_function_and_relative_index_from_concrete_index(v);
                    let fun_index = fun_index.expect("Term should be in a function");
                    let num_return_terms =
                        state.context_state.templates[fun_index as usize].num_return_terms;
                    if relative_index < num_return_terms {
                        state
                            .new_pointed_by_queries
                            .push(state.context_state.templates[0].start_index + fun_index);
                    }
                }
            },
        );
        // dbg!(top_order
        //     .iter()
        //     .map(|t| self.context_state.concrete_to_input(*t))
        //     .collect::<Vec<_>>());

        for &v in &self.new_pointed_by_queries {
            new_pointed_by_queries_term_set.insert(v);
            for &w in &self.edges.addr_ofs[v as usize] {
                let w = get_representative(&mut self.parents, w);
                self.sols[w as usize].insert(v);
            }
            self.pointed_by_queries.insert(v);
        }

        for &v in top_order.iter().rev() {
            // Skip if no new terms in solution set
            if self.sols[v as usize].len() == self.p_old_pointed_by[v as usize].len() {
                continue;
            }
            changed = true;
            let p_old_without_new_queries =
                self.p_old_pointed_by[v as usize].difference(&new_pointed_by_queries_term_set);
            // TODO: intersection
            let mut pointed_by_sols = self.sols[v as usize].clone();
            pointed_by_sols.intersection_assign(&self.pointed_by_queries);
            let p_dif = pointed_by_sols.weak_difference(&p_old_without_new_queries);
            let p_dif_vec = Lazy::new(|| p_dif.iter().collect::<Vec<IntegerTerm>>());
            self.p_old_pointed_by[v as usize] = pointed_by_sols;

            for (&w, offsets) in &self.edges.subset[v as usize] {
                let mut should_set_new_incoming = false;
                for o in offsets.iter() {
                    if o == 0 {
                        self.sols[w as usize].union_assign(&p_dif);
                    } else {
                        let to_add = p_dif_vec.iter().filter_map(|&t| {
                            if let TermType::Struct(allowed) = self.term_types[t as usize] {
                                (o <= allowed).then(|| t + o as IntegerTerm)
                            } else {
                                None
                            }
                        });
                        for t in to_add {
                            if self.pointed_by_queries.contains(t) {
                                should_set_new_incoming |= self.sols[w as usize].insert(t);
                            } else {
                                self.edges.addr_ofs[t as usize].push(w);
                            }
                        }
                    }
                }
                if should_set_new_incoming {
                    self.new_incoming.push(w);
                }
            }
        }

        self.new_pointed_by_queries.clear();
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

            if self.sols[cond_node as usize].len() == self.p_cache_call_dummies[i].len() {
                continue;
            }
            let p_new = self.sols[cond_node as usize].difference(&self.p_cache_call_dummies[i]);
            self.p_cache_call_dummies[i].union_assign(&p_new);
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

            if self.sols[cond_node as usize].len() == self.p_cache_left[i].len() {
                continue;
            }
            let p_new = self.sols[cond_node as usize].difference(&self.p_cache_left[i]);
            self.p_cache_left[i].union_assign(&p_new);
            for t in p_new.iter() {
                if let Some(t) =
                    self.try_offset_and_instantiate(t, call_site.as_ref(), offset, &context)
                {
                    let t = get_representative(&mut self.parents, t);
                    if t == right {
                        continue;
                    }
                    if edges_between(&mut self.edges.subset, t, right).insert(0) {
                        if self.points_to_queries.test(right as usize) {
                            self.sols[right as usize]
                                .union_assign(&self.p_old_points_to[t as usize]);
                        } else {
                            self.sols[right as usize]
                                .union_assign(&self.p_old_pointed_by[t as usize]);
                        }
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

            if self.sols[cond_node as usize].len() == self.p_cache_right[i].len() {
                continue;
            }
            let p_new = self.sols[cond_node as usize].difference(&self.p_cache_right[i]);
            self.p_cache_right[i].union_assign(&p_new);
            for t in p_new.iter() {
                if let Some(t) =
                    self.try_offset_and_instantiate(t, call_site.as_ref(), offset, &context)
                {
                    let t = get_representative(&mut self.parents, t);
                    if t == left {
                        continue;
                    }
                    if edges_between(&mut self.edges.subset, left, t).insert(0) {
                        if self.points_to_queries.test(t as usize) {
                            self.sols[t as usize]
                                .union_assign(&self.p_old_points_to[left as usize]);
                        } else {
                            self.sols[t as usize]
                                .union_assign(&self.p_old_pointed_by[left as usize]);
                        }
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
                    .unwrap_or_else(|| {
                        let input_term = self.context_state.concrete_to_input(term);
                        dbg!(term - self.context_state.templates[0].start_index);
                        dbg!(self.context_state.templates.len());
                        panic!("function term {input_term:?} should have a function")
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
            let instantiated_start_index = self.sols.len();
            let num_instantiated = template.types.len();
            let new_len = instantiated_start_index + num_instantiated;
            self.sols.resize_with(new_len, S::new);
            self.edges.resize(new_len);
            self.term_types.extend_from_slice(&template.types);
            self.parents.extend(
                (0..num_instantiated).map(|i| (instantiated_start_index + i) as IntegerTerm),
            );
            self.p_old_points_to.resize_with(new_len, S::new);
            self.p_old_pointed_by.resize_with(new_len, S::new);
            self.is_return_or_parameter.resize(new_len, false);

            for i in 0..(template.num_return_terms + template.num_parameter_terms) as usize {
                self.is_return_or_parameter
                    .set(instantiated_start_index + i, true);
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
        visit_weighted: bool,
        initial_nodes: Vec<IntegerTerm>,
        visit_handler: F,
    ) -> Vec<IntegerTerm>
    where
        F: Fn(IntegerTerm, &mut SccVisitState<T, S, C>, &mut Vec<IntegerTerm>),
    {
        let node_count = self.term_count();
        let mut internal_state = SccInternalState {
            direction,
            visit_weighted,
            node_count,
            iteration: 0,
            d: vec![0; node_count],
            r: vec![None; node_count],
            c: bitvec![0; node_count],
            s: vec![],
            to_visit: initial_nodes,
            top_order: vec![],
        };

        let mut visit_state = SccVisitState {
            sols: &mut self.sols,
            term_types: &self.term_types,
            abstract_rev_offsets: &self.abstract_rev_offsets,
            p_old_points_to: &mut self.p_old_points_to,
            context_state: &self.context_state,
            edges: &self.edges,
            points_to_queries: &mut self.points_to_queries,
            visited_pointed_by: &mut self.visited_pointed_by,
            is_return_or_parameter: &self.is_return_or_parameter,
            new_points_to_queries: &mut self.new_points_to_queries,
            new_pointed_by_queries: &mut self.new_pointed_by_queries,
            parents: &mut self.parents,
        };

        while let Some(v) = internal_state.to_visit.pop() {
            if internal_state.d[v as usize] == 0 {
                visit(
                    &mut internal_state,
                    &mut visit_state,
                    &self.edges,
                    &visit_handler,
                    v,
                );
            }
        }

        for v in 0..internal_state.node_count as u32 {
            if let Some(r_v) = internal_state.r[v as usize] {
                if r_v != v {
                    self.unify(v, r_v);
                }
            }
        }

        internal_state.top_order
    }

    fn unify(&mut self, child: IntegerTerm, parent: IntegerTerm) {
        debug_assert_ne!(child, parent);

        let child_sols = mem::take(&mut self.sols[child as usize]);
        self.sols[parent as usize].union_assign(&child_sols);

        let p_pt_old = &self.p_old_points_to[parent as usize];
        let p_pt_old_vec = Lazy::new(|| p_pt_old.iter().collect::<Vec<IntegerTerm>>());
        let p_pb_old = &self.p_old_pointed_by[parent as usize];
        // let p_pb_old_vec = Lazy::new(|| p_pb_old.iter().collect::<Vec<IntegerTerm>>());
        let child_edges = mem::take(&mut self.edges.subset[child as usize]);

        for (&other, offsets) in &child_edges {
            debug_assert_ne!(0, offsets.len());

            let other = if other == child { parent } else { other };
            let other_term_set = &mut self.sols[other as usize];

            if self.points_to_queries.test(other as usize) {
                for offset in offsets.iter() {
                    propagate_terms_into(
                        p_pt_old,
                        p_pt_old_vec.iter().copied(),
                        offset,
                        other_term_set,
                        &self.term_types,
                    );
                }
            }
            if offsets.contains(0) {
                other_term_set.union_assign(&p_pb_old);
            } else {
                // Todo: Pointed-by prop
            }

            self.edges.subset[parent as usize]
                .entry(other)
                .or_default()
                .union_assign(&offsets);
            self.edges.rev_subset[other as usize].remove(&child);
            self.edges.rev_subset[other as usize].insert(parent);
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

        self.edges.rev_subset[parent as usize].union_assign(&child_rev_edges);

        if self.edges.rev_subset[parent as usize].remove(&(child as IntegerTerm)) {
            self.edges.rev_subset[parent as usize].insert(parent as IntegerTerm);
        }

        let child_addr_ofs = mem::take(&mut self.edges.addr_ofs[child as usize]);
        self.edges.rev_addr_ofs[parent as usize].extend_from_slice(child_addr_ofs.as_slice());
        let child_loads = mem::take(&mut self.edges.loads[child as usize]);
        self.edges.loads[parent as usize].extend_from_slice(child_loads.as_slice());
        let child_stores = mem::take(&mut self.edges.stores[child as usize]);
        self.edges.stores[parent as usize].extend_from_slice(child_stores.as_slice());

        self.parents[child as usize] = parent;
        self.p_old_points_to[child as usize] = S::new();
        self.p_old_pointed_by[child as usize] = S::new();
    }
}

fn offsetable_terms(
    term: IntegerTerm,
    abstract_indices: &[IntegerTerm],
    abstract_rev_offsets: &[SmallVec<[u32; 2]>],
) -> impl Iterator<Item = IntegerTerm> {
    let abstract_term = abstract_indices[term as usize];
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
    C: ContextSelector,
{
    type Solution = TidalPropagationSolverState<T, S, C>;

    fn solve(&self, input: DemandContextSensitiveInput<T, C>) -> Self::Solution {
        let global = input.input.global.clone();
        // let entrypoints = input.input.entrypoints.clone();

        let (context_state, function_term_infos) = ContextState::from_context_input(input.input);
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

        let global_term_types_iter = global
            .term_types
            .iter()
            .map(|(t, tt)| (context_state.mapping.term_to_integer(t), *tt));
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

        for (i, function_term_info) in function_term_infos.into_iter().enumerate() {
            let fun_term = (global.terms.len() + i) as IntegerTerm;
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
            p_old_points_to: vec![S::new(); num_terms],
            p_old_pointed_by: vec![S::new(); num_terms],
            p_cache_left: vec![],
            p_cache_right: vec![],
            p_cache_call_dummies: vec![],
            term_types,
            abstract_rev_offsets,
            parents: Vec::from_iter(0..num_terms as IntegerTerm),
            points_to_queries: uniset::BitSet::new(),
            pointed_by_queries: S::new(),
            visited_pointed_by: uniset::BitSet::new(),
            is_return_or_parameter: bitvec::bitvec![0; num_terms],
            abstract_points_to_queries: bitvec::bitvec![0; num_abstract_terms],
            abstract_pointed_by_queries: bitvec::bitvec![0; num_abstract_terms],
            new_points_to_queries: vec![],
            new_pointed_by_queries: vec![],
            new_incoming: vec![],
        };

        for c in global.constraints {
            state.add_constraint(
                state.context_state.mapping.translate_constraint(&c),
                empty_context.clone(),
            );
        }

        for demand in input.demands {
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

        // for entrypoint in entrypoints {
        //     state.get_or_instantiate_function(entrypoint, empty_context.clone());
        // }
        for entrypoint in 0..state.context_state.templates.len() {
            state.get_or_instantiate_function(entrypoint, empty_context.clone());
        }

        state.run_tidal_propagation();

        state
    }
}

impl<T, S, C> SolverSolution for TidalPropagationSolverState<T, S, C>
where
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    C: ContextSelector,
{
    type Term = T;
    type TermSet = HashSet<T>;

    fn get(&self, term: &T) -> Self::TermSet {
        let (fun_index, relative_index) = self
            .context_state
            .get_function_and_relative_index_from_term(term);

        match fun_index {
            Some(i) => self.context_state.instantiated_contexts[i as usize]
                .iter()
                .flat_map(|(_, start_index)| {
                    let concrete_index = start_index + relative_index;
                    self.sols
                        [get_representative_no_mutation(&self.parents, concrete_index) as usize]
                        .iter()
                })
                .map(|concrete_index| self.context_state.concrete_to_input(concrete_index))
                .collect(),
            None => self.sols
                [get_representative_no_mutation(&self.parents, relative_index) as usize]
                .iter()
                .map(|concrete_index| self.context_state.concrete_to_input(concrete_index))
                .collect(),
        }
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
    edges: &Edges<C>,
    visit_handler: &F,
    v: IntegerTerm,
) where
    for<'b> F: Fn(IntegerTerm, &mut SccVisitState<'b, T, S, C>, &mut Vec<IntegerTerm>),
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
        SccDirection::Forward => Either::Left(edges.subset[v as usize].iter()),
        SccDirection::Backward => Either::Right(
            edges.rev_subset[v as usize]
                .iter()
                .map(|w| (w, edges.subset[*w as usize].get(&v).unwrap())),
        ),
    };

    for (&w, offsets) in edges_iter {
        if !offsets.contains(0) {
            debug_assert!(offsets.has_non_zero());
            if internal.visit_weighted {
                internal.to_visit.push(w);
            }
            continue;
        }

        if internal.d[w as usize] == 0 {
            visit(internal, visit_state, edges, visit_handler, w);
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

struct SccInternalState {
    direction: SccDirection,
    visit_weighted: bool,
    node_count: usize,
    iteration: usize,
    /// 0 means not visited.
    d: Vec<usize>,
    r: Vec<Option<IntegerTerm>>,
    c: BitVec,
    s: Vec<IntegerTerm>,
    to_visit: Vec<IntegerTerm>,
    top_order: Vec<IntegerTerm>,
}

struct SccVisitState<'a, T, S, C: ContextSelector> {
    sols: &'a mut [S],
    term_types: &'a [TermType],
    abstract_rev_offsets: &'a [SmallVec<[u32; 2]>],
    p_old_points_to: &'a [S],
    context_state: &'a ContextState<T, C>,
    edges: &'a Edges<C>,
    points_to_queries: &'a mut uniset::BitSet,
    visited_pointed_by: &'a mut uniset::BitSet,
    is_return_or_parameter: &'a BitVec,
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
    C: ContextSelector,
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
