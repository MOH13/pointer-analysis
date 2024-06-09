use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;
use std::marker::PhantomData;
use std::mem;
use std::time::Duration;

use bitvec::bitvec;
use bitvec::prelude::*;
use hashbrown::{HashMap, HashSet};
use once_cell::unsync::Lazy;
use roaring::RoaringBitmap;
use serde::Serialize;

use super::context::{ContextState, TemplateTerm};
use super::shared_bitvec::SharedBitVec;
use super::{
    edges_between, try_offset_term, CallSite, Constraint, ContextSelector, ContextSensitiveInput,
    IntegerTerm, Offsets, OnlyOnceStack, Solver, SolverExt, SolverSolution, TermSetTrait, TermType,
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
pub struct ContextWavePropagationSolver<S, C>(PhantomData<S>, PhantomData<C>);

impl<S, C> ContextWavePropagationSolver<S, C> {
    pub fn new() -> Self {
        Self(PhantomData, PhantomData)
    }
}

pub struct ContextWavePropagationSolverState<T, S, C: ContextSelector> {
    context_state: ContextState<T, C>,
    edges: Edges<S, C>,
    term_types: Vec<TermType>,
    parents: Vec<IntegerTerm>,
    top_order: Vec<IntegerTerm>,
    iters: u64,
    scc_time: Duration,
    propagation_time: Duration,
    edge_instantiation_time: Duration,
}

impl<T, S, C: ContextSelector> ContextWavePropagationSolverState<T, S, C> {
    fn term_count(&self) -> usize {
        self.edges.sols.len()
    }
}

impl<T, S, C> ContextWavePropagationSolverState<T, S, C>
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
            SCC::run(self).apply_to_graph(self);
            SCC::run_with_weighted(self).apply_to_graph_weighted(self);
            self.scc_time += scc_start.elapsed();

            let propagation_start = std::time::Instant::now();
            changed = self.wave_propagate_iteration();
            self.propagation_time += propagation_start.elapsed();

            let edge_instantiation_start = std::time::Instant::now();
            let mut nodes_with_new_outgoing = S::new();
            changed |= self.add_edges_after_wave_prop(&mut nodes_with_new_outgoing);
            self.edge_instantiation_time += edge_instantiation_start.elapsed();

            eprintln!("Iteration {}", self.iters);
        }
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
            self.edges.p_old[v as usize].union_assign(&p_dif);

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

            if self.edges.sols[cond_node as usize].len() == self.edges.p_cache_left[i].len() {
                continue;
            }
            let p_new = self.edges.sols[cond_node as usize].difference(&self.edges.p_cache_left[i]);
            self.edges.p_cache_left[i].union_assign(&p_new);
            for t in p_new.iter() {
                if let Some(t) =
                    self.try_offset_and_instantiate(t, call_site.as_ref(), offset, &context)
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
                    self.try_offset_and_instantiate(t, call_site.as_ref(), offset, &context)
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
            let instantiated_start_index = self.edges.sols.len();
            let num_instantiated = template.types.len();
            let new_len = instantiated_start_index + num_instantiated;
            self.edges.sols.resize_with(new_len, S::new);
            self.edges.subset.resize_with(new_len, HashMap::new);
            self.edges.rev_subset.resize_with(new_len, HashSet::new);
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
                }
            }
        }
        index
    }

    fn add_constraint(&mut self, c: Constraint<IntegerTerm>, context: C::Context) {
        let c = c.map_terms(|&t| get_representative(&mut self.parents, t));
        self.edges.add_constraint(c, context);
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

impl<S, C> SolverExt for ContextWavePropagationSolver<S, C>
where
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    C: ContextSelector,
{
}

impl<T, S, C> Solver<ContextSensitiveInput<T, C>> for ContextWavePropagationSolver<S, C>
where
    T: Hash + Eq + Clone + Debug,
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    C: ContextSelector + Clone,
{
    type Solution = ContextWavePropagationSolverState<T, S, C>;

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

        for (i, function_term_info) in function_term_infos.into_iter().enumerate() {
            let fun_term = (input.global.terms.len() + i) as IntegerTerm;
            term_types[fun_term as usize] = function_term_info.term_type;
            sols[function_term_info.pointer_node as usize].insert(fun_term);
        }

        let parents = Vec::from_iter(0..sols.len() as IntegerTerm);
        let top_order = Vec::new();

        let left_conds = vec![];
        let right_conds = vec![];
        let call_dummies = vec![];
        let p_old = vec![S::new(); sols.len()];
        let p_cache_left = vec![S::new(); left_conds.len()];
        let p_cache_right = vec![S::new(); right_conds.len()];
        let p_cache_call_dummies = vec![];
        let mut state = ContextWavePropagationSolverState {
            context_state,
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
            iters: 0,
            scc_time: Duration::ZERO,
            propagation_time: Duration::ZERO,
            edge_instantiation_time: Duration::ZERO,
        };

        for c in input.global.constraints {
            state.add_constraint(
                state.context_state.mapping.translate_constraint(&c),
                empty_context.clone(),
            );
        }

        // for entrypoint in entrypoints {
        //     state.get_or_instantiate_function(entrypoint, empty_context.clone());
        // }
        for entrypoint in 0..state.context_state.templates.len() {
            state.get_or_instantiate_function(entrypoint, empty_context.clone());
        }

        state.run_wave_propagation();

        state
    }
}

impl<T, S, C> ContextWavePropagationSolverState<T, S, C>
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

impl<T, S, C> SolverSolution for ContextWavePropagationSolverState<T, S, C>
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
            scc_time_ms: self.scc_time.as_millis() as u64,
            term_propagation_time_ms: self.propagation_time.as_millis() as u64,
            edge_instantiation_time_ms: self.edge_instantiation_time.as_millis() as u64,
        })
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
                arguments: _,
                result_node: _,
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

struct SCC<T, S, C> {
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
    S: TermSetTrait<Term = IntegerTerm> + Debug,
    T: Hash + Eq + Clone + Debug,
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

    fn init_result(state: &ContextWavePropagationSolverState<T, S, C>) -> Self {
        let node_count = state.term_count();
        Self {
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
        let mut result = SCC::init_result(solver);
        for v in 0..result.node_count as u32 {
            if result.d[v as usize] == 0 {
                result.visit(v, solver);
            }
        }
        result
    }

    fn run_with_weighted(solver: &mut ContextWavePropagationSolverState<T, S, C>) -> Self {
        let mut result = SCC::init_result(solver);
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
        parent_fn: impl Fn(IntegerTerm) -> IntegerTerm,
        state: &mut ContextWavePropagationSolverState<T, S, C>,
    ) {
        let parent = parent_fn(child);
        debug_assert_ne!(child, parent);

        let child_sols = mem::take(&mut state.edges.sols[child as usize]);
        state.edges.sols[parent as usize].union_assign(&child_sols);

        let p_old = &state.edges.p_old[parent as usize];
        let p_old_vec = Lazy::new(|| p_old.iter().collect::<Vec<IntegerTerm>>());
        let child_edges = mem::take(&mut state.edges.subset[child as usize]);

        for (&other, offsets) in &child_edges {
            debug_assert_ne!(0, offsets.len());

            let other_parent = parent_fn(other);

            if offsets.has_non_zero() || other_parent != parent {
                let other_term_set = &mut state.edges.sols[other_parent as usize];
                let existing_offsets = state.edges.subset[parent as usize]
                    .entry(other_parent)
                    .or_default();
                for offset in offsets.iter() {
                    if existing_offsets.contains(offset) {
                        continue;
                    }
                    propagate_terms_into(
                        p_old,
                        p_old_vec.iter().copied(),
                        offset,
                        other_term_set,
                        &state.term_types,
                    );
                    existing_offsets.insert(offset);
                }
            }

            state.edges.rev_subset[other as usize].remove(&child);
            state.edges.rev_subset[other_parent as usize].insert(parent);
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

        state.parents[child as usize] = parent;
        state.edges.p_old[child as usize] = S::new();
    }

    // Collapse cycles and update topological order
    fn apply_to_graph(self, state: &mut ContextWavePropagationSolverState<T, S, C>) {
        let mut nodes = vec![];
        let mut components: HashMap<IntegerTerm, (IntegerTerm, u32)> = HashMap::new();
        for v in 0..self.node_count as u32 {
            if let Some(r_v) = self.r[v as usize] {
                let edge_count = state.edges.subset[v as usize].len() as u32;
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
                self.unify(
                    v,
                    |w| {
                        components
                            .get(&self.r[w as usize].unwrap())
                            .map(|(rep, _)| *rep)
                            .unwrap_or(w)
                    },
                    state,
                );
            }
        }
        state.top_order = self.top_order;
    }

    // Collapse cycles and update topological order
    fn apply_to_graph_weighted(self, solver: &mut ContextWavePropagationSolverState<T, S, C>) {
        solver.top_order = self.top_order;
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

pub type HashContextWavePropagationSolver<C> =
    ContextWavePropagationSolver<HashSet<IntegerTerm>, C>;
pub type RoaringContextWavePropagationSolver<C> = ContextWavePropagationSolver<RoaringBitmap, C>;
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
    pub scc_time_ms: u64,
    pub term_propagation_time_ms: u64,
    pub edge_instantiation_time_ms: u64,
}
