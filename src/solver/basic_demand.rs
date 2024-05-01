use std::collections::VecDeque;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::mem;
use std::ops::{Index, IndexMut};

use bitvec::vec::BitVec;
use hashbrown::{HashMap, HashSet};
use smallvec::SmallVec;

use super::context::{ContextState, TemplateTerm};
use super::{
    try_offset_term, CallSite, Constraint, ContextSelector, Demand, DemandContextSensitiveInput,
    IntegerTerm, Offsets, Solver, SolverExt, SolverSolution, TermType,
};
use crate::util::GetTwoMutExt;
use crate::visualizer::{Edge, EdgeKind, Graph, Node, OffsetWeight};

#[derive(Clone)]
struct CondLeft<C> {
    right: IntegerTerm,
    offset: usize,
    call_site: Option<CallSite>,
    context: C,
}

#[derive(Clone)]
struct CondRight<C> {
    left: IntegerTerm,
    offset: usize,
    call_site: Option<CallSite>,
    context: C,
}

#[derive(Clone)]
struct CallDummy<C> {
    call_site: CallSite,
    context: C,
}

#[derive(Clone)]
enum Cond<C> {
    Left(CondLeft<C>),
    Right(CondRight<C>),
    Dummy(CallDummy<C>),
}

pub struct BasicDemandSolver;

impl BasicDemandSolver {
    pub fn new() -> Self {
        Self
    }
}

impl SolverExt for BasicDemandSolver {}

impl<T, C> Solver<DemandContextSensitiveInput<T, C>> for BasicDemandSolver
where
    T: Hash + Eq + Clone + Debug,
    C: ContextSelector,
{
    type Solution = BasicDemandSolverState<T, C>;

    fn solve(&self, input: DemandContextSensitiveInput<T, C>) -> Self::Solution {
        let global = input.input.global.clone();
        let entrypoints = input.input.entrypoints.clone();

        let (context_state, fun_term_infos) = ContextState::from_context_input(input.input);
        let empty_context = context_state.context_selector.empty();

        let num_terms = context_state.num_concrete_terms();
        let num_abstract = context_state.mapping.terms.len();

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

        let mut edges = Edges {
            sols: vec![HashSet::new(); num_terms],
            subsets: Subsets {
                subset: vec![HashMap::new(); num_terms],
                rev_subset: vec![HashMap::new(); num_terms],
            },
            conds: vec![vec![]; num_terms],
            loads: vec![SmallVec::new(); num_terms],
            stores: vec![SmallVec::new(); num_terms],
            pointed_by_buffers: vec![SmallVec::new(); num_terms],
            rev_addr_ofs: vec![SmallVec::new(); num_terms],
        };

        for c in global.constraints {
            let constraint = context_state.mapping.translate_constraint(&c);
            edges.add_constraint(constraint, empty_context.clone());
        }

        for (i, fun_term_info) in fun_term_infos.into_iter().enumerate() {
            let fun_term = (global.terms.len() + i) as IntegerTerm;
            term_types[fun_term as usize] = fun_term_info.term_type;
            edges.add_constraint(
                Constraint::Inclusion {
                    term: fun_term,
                    node: fun_term_info.pointer_node,
                },
                empty_context.clone(),
            );
        }

        let num_abstract_terms = context_state.mapping.terms.len();
        let mut state = BasicDemandSolverState {
            context_state,
            worklist: VecDeque::new(),
            edges,
            term_types,
            abstract_rev_offsets,
            points_to_queries: bitvec::bitvec![0; num_terms],
            pointed_by_queries: bitvec::bitvec![0; num_terms],
            is_return_or_parameter: bitvec::bitvec![0; num_terms],
            abstract_points_to_queries: bitvec::bitvec![0; num_abstract_terms],
            abstract_pointed_by_queries: bitvec::bitvec![0; num_abstract_terms],
        };

        for demand in input.demands {
            match demand {
                Demand::PointsTo(term) => {
                    let abstract_term = state.context_state.mapping.term_to_integer(&term);
                    state
                        .abstract_points_to_queries
                        .set(abstract_term as usize, true);
                    if let Some(term) = state.context_state.term_to_concrete_global(&term) {
                        add_points_to_query(
                            term,
                            &mut state.points_to_queries,
                            &mut state.worklist,
                        );
                    }
                }
                Demand::PointedBy(node) => {
                    let abstract_term = state.context_state.mapping.term_to_integer(&node);
                    state
                        .abstract_pointed_by_queries
                        .set(abstract_term as usize, true);
                    if let Some(node) = state.context_state.term_to_concrete_global(&node) {
                        add_pointed_by_query(
                            node,
                            &mut state.points_to_queries,
                            &mut state.worklist,
                        );
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
        state.solve();
        state
    }
}

#[derive(Debug)]
enum WorklistEntry<T = IntegerTerm> {
    Demand(Demand<T>),
    Inserted(T, T),
}

impl<T> WorklistEntry<T> {
    fn map_terms<U, F>(&self, mut f: F) -> WorklistEntry<U>
    where
        F: FnMut(&T) -> U,
    {
        match self {
            WorklistEntry::Demand(demand) => WorklistEntry::Demand(demand.map_term(f)),
            WorklistEntry::Inserted(t1, t2) => WorklistEntry::Inserted(f(t1), f(t2)),
        }
    }
}

pub struct BasicDemandSolverState<T, C: ContextSelector> {
    context_state: ContextState<T, C>,
    worklist: VecDeque<WorklistEntry>,
    edges: Edges<C::Context>,
    term_types: Vec<TermType>,
    abstract_rev_offsets: Vec<SmallVec<[u32; 2]>>,
    points_to_queries: BitVec,
    pointed_by_queries: BitVec,
    is_return_or_parameter: BitVec,
    abstract_points_to_queries: BitVec,
    abstract_pointed_by_queries: BitVec,
}

fn add_points_to_query(
    term: IntegerTerm,
    points_to_queries: &mut BitVec,
    worklist: &mut VecDeque<WorklistEntry>,
) {
    if !points_to_queries[term as usize] {
        worklist.push_back(WorklistEntry::Demand(Demand::PointsTo(term)));
    }
}

fn add_pointed_by_query(
    term: IntegerTerm,
    pointed_by_queries: &mut BitVec,
    worklist: &mut VecDeque<WorklistEntry>,
) {
    if !pointed_by_queries[term as usize] {
        worklist.push_back(WorklistEntry::Demand(Demand::PointedBy(term)));
    }
}

fn add_edge(
    from: IntegerTerm,
    to: IntegerTerm,
    offset: usize,
    subsets: &mut Subsets,
    sols: &mut [HashSet<IntegerTerm>],
    pointed_by_buffers: &mut [SmallVec<[IntegerTerm; 2]>],
    points_to_queries: &mut BitVec,
    pointed_by_queries: &BitVec,
    term_types: &[TermType],
    worklist: &mut VecDeque<WorklistEntry>,
) -> bool {
    if subsets.add(from, to, offset) {
        if points_to_queries[to as usize] {
            add_points_to_query(from, points_to_queries, worklist);
        }
        propagate_edge(
            from,
            to,
            offset,
            sols,
            pointed_by_buffers,
            points_to_queries,
            pointed_by_queries,
            term_types,
            worklist,
        );
        return true;
    }
    false
}

macro_rules! add_edge {
    ($state:expr, $from:expr, $to:expr, $offset:expr) => {
        add_edge(
            $from,
            $to,
            $offset,
            &mut $state.edges.subsets,
            &mut $state.edges.sols,
            &mut $state.edges.pointed_by_buffers,
            &mut $state.points_to_queries,
            &$state.pointed_by_queries,
            &$state.term_types,
            &mut $state.worklist,
        )
    };
}

fn propagate_edge(
    from: IntegerTerm,
    to: IntegerTerm,
    offset: usize,
    sols: &mut [HashSet<IntegerTerm>],
    pointed_by_buffers: &mut [SmallVec<[IntegerTerm; 2]>],
    points_to_queries: &mut BitVec,
    pointed_by_queries: &BitVec,
    term_types: &[TermType],
    worklist: &mut VecDeque<WorklistEntry>,
) {
    if points_to_queries[to as usize] {
        propagate_edge_all(from, to, offset, sols, term_types, worklist);
    } else {
        let mut to_insert = SmallVec::<[_; 64]>::new();
        for &t in &sols[from as usize] {
            let term_type = term_types[t as usize];
            let Some(new_term) = try_offset_term(t, term_type, offset) else {
                continue;
            };
            let has_pointed_by = pointed_by_queries[new_term as usize];

            if offset != 0 && !has_pointed_by {
                pointed_by_buffers[new_term as usize].push(to);
            }

            if has_pointed_by && !sols[to as usize].contains(&new_term) {
                to_insert.push(new_term);
            }
        }
        for t in to_insert {
            sols[to as usize].insert(t);
            worklist.push_back(WorklistEntry::Inserted(to, t));
        }
    }
}

macro_rules! propagate_edge {
    ($state:expr, $from:expr, $to:expr, $offset:expr) => {
        propagate_edge(
            $from,
            $to,
            $offset,
            &mut $state.edges.sols,
            &mut $state.edges.pointed_by_buffers,
            &mut $state.points_to_queries,
            &$state.pointed_by_queries,
            &$state.term_types,
            &mut $state.worklist,
        )
    };
}

fn propagate_edge_all(
    from: IntegerTerm,
    to: IntegerTerm,
    offset: usize,
    sols: &mut [HashSet<IntegerTerm>],
    term_types: &[TermType],
    worklist: &mut VecDeque<WorklistEntry>,
) {
    if let Some((from_set, to_set)) = sols.get_two_mut(from as usize, to as usize) {
        for &t in &*from_set {
            let term_type = term_types[t as usize];
            let Some(new_term) = try_offset_term(t, term_type, offset) else {
                continue;
            };
            if to_set.insert(new_term) {
                // TODO: we check for pointed by queries
                worklist.push_back(WorklistEntry::Inserted(to, new_term));
            }
        }
    } else {
        let mut to_insert = SmallVec::<[_; 64]>::new();
        for &t in &sols[from as usize] {
            let term_type = term_types[t as usize];
            let Some(new_term) = try_offset_term(t, term_type, offset) else {
                continue;
            };
            if !sols[to as usize].contains(&new_term) {
                to_insert.push(new_term);
            }
        }
        for t in to_insert {
            sols[to as usize].insert(t);
            worklist.push_back(WorklistEntry::Inserted(to, t));
        }
    }
}

macro_rules! propagate_edge_all {
    ($state:expr, $from:expr, $to:expr, $offset:expr) => {
        propagate_edge_all(
            $from,
            $to,
            $offset,
            &mut $state.edges.sols,
            &$state.term_types,
            &mut $state.worklist,
        )
    };
}

impl<T, C> BasicDemandSolverState<T, C>
where
    T: Hash + Eq + Clone + Debug,
    C: ContextSelector,
{
    fn solve(&mut self) {
        while let Some(entry) = self.worklist.pop_front() {
            // dbg!(
            //     entry.map_terms(|&t| self.context_state.concrete_to_input(t)),
            //     // &self.worklist
            // );
            match entry {
                WorklistEntry::Demand(Demand::PointsTo(x)) => {
                    self.handle_points_to(x);
                }
                WorklistEntry::Demand(Demand::PointedBy(t)) => {
                    self.handle_pointed_by(t);
                }
                WorklistEntry::Inserted(x, t) => {
                    self.handle_inserted(x, t);
                }
            }
        }
    }

    fn handle_points_to(&mut self, x: IntegerTerm) {
        if self.points_to_queries[x as usize] {
            return;
        }
        self.points_to_queries.set(x as usize, true);

        for &t in &self.edges.rev_addr_ofs[x as usize] {
            if self.edges.sols[x as usize].insert(t) {
                self.worklist.push_back(WorklistEntry::Inserted(x, t));
            }
        }

        // self.handle_pointed_by(x);
        add_pointed_by_query(x, &mut self.pointed_by_queries, &mut self.worklist);

        for &cond_node in &self.edges.loads[x as usize] {
            add_points_to_query(cond_node, &mut self.points_to_queries, &mut self.worklist);
        }

        for (from, offsets) in self.edges.subsets.rev(x) {
            add_points_to_query(*from, &mut self.points_to_queries, &mut self.worklist);

            for offset in offsets.iter() {
                propagate_edge_all!(self, *from, x, offset);
            }
        }

        if self.is_return_or_parameter[x as usize] {
            let (fun_index, relative_index) = self
                .context_state
                .get_function_and_relative_index_from_concrete_index(x);
            let fun_index = fun_index.expect("Term should be in a function");
            let template = &self.context_state.templates[fun_index as usize];
            if relative_index >= template.num_return_terms
                && relative_index < template.num_return_terms + template.num_parameter_terms
            {
                add_pointed_by_query(
                    self.context_state.templates[0].start_index + fun_index,
                    &mut self.pointed_by_queries,
                    &mut self.worklist,
                );
            }
        }
    }

    fn handle_pointed_by(&mut self, t: IntegerTerm) {
        if self.pointed_by_queries[t as usize] {
            return;
        }
        self.pointed_by_queries.set(t as usize, true);

        for from in self.offsetable_terms(t) {
            if !self.pointed_by_queries[from as usize] {
                self.handle_pointed_by(from);
            }
        }

        let max_offset = match self.term_types[t as usize] {
            TermType::Basic | TermType::Function(..) => 0,
            TermType::Struct(o) => o,
        };
        let mut stack = mem::take(&mut self.edges.pointed_by_buffers[t as usize]);
        let mut visited = HashSet::new();
        while let Some(x) = stack.pop() {
            if !visited.insert(x) {
                continue;
            }
            if self.edges.sols[x as usize].insert(t) {
                self.worklist.push_back(WorklistEntry::Inserted(x, t));
            }
            add_pointed_by_query(x, &mut self.pointed_by_queries, &mut self.worklist);
            for &cond_node in &self.edges.stores[x as usize] {
                add_points_to_query(cond_node, &mut self.points_to_queries, &mut self.worklist);
            }
            for (y, offsets) in &self.edges.subsets[x] {
                for offset in offsets.iter() {
                    if visited.contains(y) {
                        continue;
                    }
                    if offset == 0 {
                        stack.push(*y);
                    } else if offset <= max_offset {
                        self.edges.pointed_by_buffers[t as usize + offset].push(*y);
                    }
                }
            }
        }
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

    fn handle_inserted(&mut self, x: IntegerTerm, t: IntegerTerm) {
        if self.pointed_by_queries[t as usize] {
            add_pointed_by_query(x, &mut self.pointed_by_queries, &mut self.worklist);
            for &cond_node in &self.edges.stores[x as usize] {
                add_points_to_query(cond_node, &mut self.points_to_queries, &mut self.worklist);
            }
            if self.is_return_or_parameter[x as usize] {
                let (fun_index, relative_index) = self
                    .context_state
                    .get_function_and_relative_index_from_concrete_index(x);
                let fun_index = fun_index.expect("Term should be in a function");
                let num_return_terms =
                    self.context_state.templates[fun_index as usize].num_return_terms;
                if relative_index < num_return_terms {
                    add_pointed_by_query(
                        self.context_state.templates[0].start_index + fun_index,
                        &mut self.pointed_by_queries,
                        &mut self.worklist,
                    );
                }
            }
        }

        for cond in self.edges.conds[x as usize].clone() {
            match cond {
                Cond::Left(cond) => {
                    if let Some(offset_term) = self.try_offset_and_instantiate(
                        t,
                        cond.call_site.as_ref(),
                        cond.offset,
                        &cond.context,
                    ) {
                        add_edge!(self, offset_term, cond.right, 0);
                    }
                }
                Cond::Right(cond) => {
                    if let Some(offset_term) = self.try_offset_and_instantiate(
                        t,
                        cond.call_site.as_ref(),
                        cond.offset,
                        &cond.context,
                    ) {
                        add_edge!(self, cond.left, offset_term, 0);
                    }
                }
                Cond::Dummy(cond) => {
                    self.try_offset_and_instantiate(t, Some(&cond.call_site), 0, &cond.context);
                }
            }
        }

        let t_term_type = self.term_types[t as usize];
        for (to, offsets) in &self.edges.subsets[x] {
            for offset in offsets.iter() {
                let Some(new_term) = try_offset_term(t, t_term_type, offset) else {
                    break;
                };
                if offset != 0 && !self.pointed_by_queries[new_term as usize] {
                    self.edges.pointed_by_buffers[new_term as usize].push(*to);
                }
                if !self.points_to_queries[*to as usize]
                    && !self.pointed_by_queries[new_term as usize]
                {
                    continue;
                }
                if self.edges.sols[*to as usize].insert(new_term) {
                    self.worklist
                        .push_back(WorklistEntry::Inserted(*to, new_term));
                }
            }
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
            self.term_types.extend_from_slice(&template.types);
            self.edges.resize(new_len);
            self.points_to_queries.resize(new_len, false);
            self.pointed_by_queries.resize(new_len, false);
            self.is_return_or_parameter.resize(new_len, false);
            for i in 0..(template.num_return_terms + template.num_parameter_terms) as usize {
                self.is_return_or_parameter
                    .set(instantiated_start_index + i, true);
            }
            for i in 0..num_instantiated as u32 {
                let abstract_term = template.start_index + i;
                let concrete_term = instantiated_start_index as IntegerTerm + i;
                if self.abstract_points_to_queries[abstract_term as usize] {
                    self.worklist
                        .push_back(WorklistEntry::Demand(Demand::PointsTo(concrete_term)));
                }
                if self.abstract_pointed_by_queries[abstract_term as usize] {
                    self.worklist
                        .push_back(WorklistEntry::Demand(Demand::PointedBy(concrete_term)));
                }
            }

            for constraint in &template.constraints {
                let concrete_constraint = constraint.map_terms(|tt| match tt {
                    &TemplateTerm::Internal(index) => {
                        instantiated_start_index as IntegerTerm + index
                    }
                    &TemplateTerm::Global(index) => index,
                });
                self.edges
                    .add_constraint(concrete_constraint.clone(), context.clone());

                let mut cond_nodes = HashSet::new();
                match concrete_constraint {
                    Constraint::Inclusion { term, node } => {
                        if self.pointed_by_queries[term as usize] {
                            self.edges.pointed_by_buffers[term as usize].pop();
                        }
                        if self.pointed_by_queries[term as usize]
                            || self.points_to_queries[node as usize]
                        {
                            if self.edges.sols[node as usize].insert(term) {
                                self.worklist.push_back(WorklistEntry::Inserted(node, term));
                            }
                        }
                    }
                    Constraint::Subset {
                        left,
                        right,
                        offset,
                    } => {
                        if self.points_to_queries[right as usize] {
                            add_points_to_query(
                                left,
                                &mut self.points_to_queries,
                                &mut self.worklist,
                            );
                        }
                        propagate_edge!(self, left, right, offset);
                    }
                    Constraint::UnivCondSubsetLeft {
                        cond_node, right, ..
                    } => {
                        if self.points_to_queries[right as usize] {
                            add_points_to_query(
                                cond_node,
                                &mut self.points_to_queries,
                                &mut self.worklist,
                            );
                        }
                        cond_nodes.insert(cond_node);
                    }
                    Constraint::UnivCondSubsetRight {
                        cond_node, left, ..
                    } => {
                        for &t in &self.edges.sols[left as usize] {
                            if self.pointed_by_queries[t as usize] {
                                add_points_to_query(
                                    cond_node,
                                    &mut self.points_to_queries,
                                    &mut self.worklist,
                                );
                            }
                        }
                        cond_nodes.insert(cond_node);
                    }
                    Constraint::CallDummy { cond_node, .. } => {
                        cond_nodes.insert(cond_node);
                    }
                }
                for cond_node in cond_nodes {
                    for &t in &self.edges.sols[cond_node as usize] {
                        self.worklist
                            .push_back(WorklistEntry::Inserted(cond_node, t));
                    }
                }
            }
        }
        index
    }

    fn offsetable_terms(&self, term: IntegerTerm) -> impl Iterator<Item = IntegerTerm> {
        let abstract_term = self.context_state.abstract_indices[term as usize];
        self.abstract_rev_offsets[abstract_term as usize]
            .clone()
            .into_iter()
            .map(move |o| term - o)
    }
}

impl<T, C> SolverSolution for BasicDemandSolverState<T, C>
where
    T: Hash + Eq + Clone + Debug,
    C: ContextSelector,
{
    type Term = T;

    type TermSet = HashSet<T>;

    fn get(&self, term: &Self::Term) -> Self::TermSet {
        let (fun_index, relative_index) = self
            .context_state
            .get_function_and_relative_index_from_term(term);

        match fun_index {
            Some(i) => self.context_state.instantiated_contexts[i as usize]
                .iter()
                .flat_map(|(_, start_index)| {
                    let concrete_index = start_index + relative_index;
                    self.edges.sols[concrete_index as usize].iter()
                })
                .map(|&concrete_index| self.context_state.concrete_to_input(concrete_index))
                .collect(),
            None => self.edges.sols[relative_index as usize]
                .iter()
                .map(|&concrete_index| self.context_state.concrete_to_input(concrete_index))
                .collect(),
        }
    }
}

struct Edges<C> {
    sols: Vec<HashSet<IntegerTerm>>,
    subsets: Subsets,
    conds: Vec<Vec<Cond<C>>>,
    loads: Vec<SmallVec<[IntegerTerm; 1]>>,
    stores: Vec<SmallVec<[IntegerTerm; 1]>>,
    pointed_by_buffers: Vec<SmallVec<[IntegerTerm; 2]>>,
    rev_addr_ofs: Vec<SmallVec<[IntegerTerm; 2]>>,
}

impl<C> Edges<C> {
    fn add_constraint(&mut self, c: Constraint<IntegerTerm>, context: C) {
        match c {
            Constraint::Inclusion { term, node } => {
                self.pointed_by_buffers[term as usize].push(node);
                self.rev_addr_ofs[node as usize].push(term);
            }
            Constraint::Subset {
                left,
                right,
                offset,
            } => {
                self.subsets.add(left, right, offset);
            }
            Constraint::UnivCondSubsetLeft {
                cond_node,
                right,
                offset,
                call_site,
            } => {
                self.conds[cond_node as usize].push(Cond::Left(CondLeft {
                    right,
                    offset,
                    call_site: call_site.clone(),
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
                self.conds[cond_node as usize].push(Cond::Right(CondRight {
                    left,
                    offset,
                    call_site: call_site.clone(),
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
                self.conds[cond_node as usize].push(Cond::Dummy(CallDummy {
                    call_site: call_site.clone(),
                    context,
                }));
            }
        }
    }

    fn resize(&mut self, new_len: usize) {
        self.sols.resize_with(new_len, HashSet::new);
        self.subsets.resize(new_len);
        self.conds.resize_with(new_len, Vec::new);
        self.loads.resize_with(new_len, SmallVec::new);
        self.stores.resize_with(new_len, SmallVec::new);
        self.pointed_by_buffers.resize_with(new_len, SmallVec::new);
        self.rev_addr_ofs.resize_with(new_len, SmallVec::new);
    }
}

struct Subsets {
    subset: Vec<HashMap<IntegerTerm, Offsets>>,
    rev_subset: Vec<HashMap<IntegerTerm, Offsets>>,
}

impl Subsets {
    fn rev(&self, index: IntegerTerm) -> &HashMap<IntegerTerm, Offsets> {
        &self.rev_subset[index as usize]
    }

    fn add(&mut self, from: IntegerTerm, to: IntegerTerm, offset: usize) -> bool {
        if self.subset[from as usize]
            .entry(to)
            .or_default()
            .insert(offset)
        {
            self.rev_subset[to as usize]
                .entry(from)
                .or_default()
                .insert(offset);
            return true;
        }
        false
    }

    fn resize(&mut self, new_len: usize) {
        self.subset.resize_with(new_len, HashMap::new);
        self.rev_subset.resize_with(new_len, HashMap::new);
    }
}

impl Index<IntegerTerm> for Subsets {
    type Output = HashMap<IntegerTerm, Offsets>;

    fn index(&self, index: IntegerTerm) -> &Self::Output {
        &self.subset[index as usize]
    }
}

impl IndexMut<IntegerTerm> for Subsets {
    fn index_mut(&mut self, index: IntegerTerm) -> &mut Self::Output {
        &mut self.subset[index as usize]
    }
}

#[derive(Debug, Clone)]
pub struct BasicDemandSolverNode<T, C>(T, C);

impl<T, C> Display for BasicDemandSolverNode<T, C>
where
    T: Hash + Eq + Clone + Display + Debug,
    C: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let node = &self.0;
        let context = &self.1;
        write!(f, "{node}, {context:?}")
    }
}

impl<T, C> BasicDemandSolverState<T, C>
where
    T: Hash + Eq + Clone + Debug,
    C: ContextSelector,
{
    fn concrete_index_to_graph_node(
        &self,
        concrete_index: IntegerTerm,
    ) -> Node<BasicDemandSolverNode<T, C::Context>> {
        Node {
            inner: BasicDemandSolverNode(
                self.context_state.concrete_to_input(concrete_index),
                self.context_state.context_of_concrete_index(concrete_index),
            ),
            id: concrete_index as usize,
        }
    }
}

impl<T, C> Graph for BasicDemandSolverState<T, C>
where
    T: Hash + Eq + Clone + Display + Debug,
    C: ContextSelector,
{
    type Node = BasicDemandSolverNode<T, C::Context>;
    type Weight = OffsetWeight;

    fn nodes(&self) -> Vec<Node<Self::Node>> {
        (0..self.edges.sols.len() as IntegerTerm)
            .into_iter()
            .map(|i| self.concrete_index_to_graph_node(i))
            .collect()
    }

    fn edges(&self) -> Vec<Edge<Self::Node, Self::Weight>> {
        self.edges
            .subsets
            .subset
            .iter()
            .enumerate()
            .flat_map(|(from, edges)| {
                edges.iter().flat_map(move |(&to, offsets)| {
                    offsets.iter().map(move |weight| Edge {
                        from: self.concrete_index_to_graph_node(from as IntegerTerm),
                        to: self.concrete_index_to_graph_node(to as IntegerTerm),
                        weight: OffsetWeight(weight as u32),
                        kind: EdgeKind::Subset,
                    })
                })
            })
            .collect()
    }
}
