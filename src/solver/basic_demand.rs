use std::collections::VecDeque;
use std::ops::Index;

use bitvec::vec::{self, BitVec};
use hashbrown::{HashMap, HashSet};
use smallvec::SmallVec;

use super::{
    CallSite, Constraint, ContextSelector, ContextSensitiveInput, ContextSensitiveSolver, Demand,
    DemandContextSensitiveInput, DemandInput, IntegerTerm, Offsets, Solver, SolverSolution,
    TermType, UnivCond,
};
use crate::util::GetTwoMutExt;

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

impl<C: ContextSelector> Solver<DemandContextSensitiveInput<IntegerTerm, C>> for BasicDemandSolver {
    type Solution = BasicDemandSolverState<C>;

    fn solve(self, input: DemandContextSensitiveInput<IntegerTerm, C>) -> Self::Solution {
        let terms: Vec<_> = input
            .input
            .global
            .terms
            .iter()
            .chain(input.input.functions.iter().flat_map(|t| {
                t.return_and_parameter_terms
                    .iter()
                    .chain(&t.constrained_terms.terms)
            }))
            .cloned()
            .collect();

        let term_types = vec![TermType::Basic; terms.len()];
        let mut offsetable_terms = vec![None; terms.len()];
        for (from, tt) in term_types.iter().enumerate() {
            let from = from as IntegerTerm;
            let max_offset = tt.into_offset() as u32;
            for to in (from + 1)..=(from + max_offset) {
                offsetable_terms[to as usize] = Some(from);
            }
        }

        let mut state = BasicDemandSolverState {
            context_selector: input.input.context_selector,
            worklist: VecDeque::new(),
            edges: Edges {
                sols: vec![HashSet::new(); terms.len()],
                subsets: Subsets {
                    subset: vec![HashMap::new(); terms.len()],
                    rev_subset: vec![HashMap::new(); terms.len()],
                },
                conds: vec![vec![]; terms.len()],
                addr_ofs: vec![SmallVec::new(); terms.len()],
                rev_addr_ofs: vec![SmallVec::new(); terms.len()],
            },
            term_types,
            offsetable_terms: offsetable_terms,
            points_to_queries: bitvec::bitvec![0; terms.len()],
            pointed_by_queries: bitvec::bitvec![0; terms.len()],
        };
        todo!();

        state.solve();
        state
    }
}

enum WorklistEntry {
    Demand(Demand<IntegerTerm>),
    Inserted(IntegerTerm, IntegerTerm),
}

pub struct BasicDemandSolverState<C: ContextSelector> {
    context_selector: C,
    worklist: VecDeque<WorklistEntry>,
    edges: Edges<C::Context>,
    term_types: Vec<TermType>,
    offsetable_terms: Vec<Option<IntegerTerm>>,
    points_to_queries: BitVec,
    pointed_by_queries: BitVec,
}

impl<C: ContextSelector> BasicDemandSolverState<C> {
    fn solve(&mut self) {
        while let Some(entry) = self.worklist.pop_front() {
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
        for &t in &self.edges.rev_addr_ofs[x as usize] {
            if self.edges.sols[x as usize].insert(t) {
                self.worklist.push_back(WorklistEntry::Inserted(x, t));
            }
        }

        if !self.pointed_by_queries[x as usize] {
            self.pointed_by_queries.set(x as usize, true);
            self.worklist
                .push_back(WorklistEntry::Demand(Demand::PointedBy(x)));
            // self.handle_pointed_by(x);
        }

        for (from, offsets) in self.edges.subsets.rev(x) {
            if !self.points_to_queries[*from as usize] {
                self.points_to_queries.set(*from as usize, true);
                self.worklist
                    .push_back(WorklistEntry::Demand(Demand::PointsTo(*from)));
                continue;
            }

            // Special handling when from == x
            if *from == x {
                let mut to_insert = SmallVec::<[_; 64]>::new();
                for &t in &self.edges.sols[x as usize] {
                    let term_type = self.term_types[t as usize];
                    for offset in offsets.iter() {
                        if offset > term_type.into_offset() {
                            continue;
                        }
                        let new_term = t + offset as u32;
                        if !self.edges.sols[x as usize].contains(&new_term) {
                            to_insert.push(new_term);
                        }
                    }
                }
                for t in to_insert {
                    self.edges.sols[x as usize].insert(t);
                    self.worklist.push_back(WorklistEntry::Inserted(x, t));
                }
                continue;
            }

            let (from_set, to_set) = self.edges.sols.get_two_mut(*from as usize, x as usize);
            for &t in &*from_set {
                let term_type = self.term_types[t as usize];
                for offset in offsets.iter() {
                    if offset > term_type.into_offset() {
                        continue;
                    }
                    let new_term = t + offset as u32;
                    if to_set.insert(new_term) {
                        // TODO: we check for pointed by queries
                        self.worklist
                            .push_back(WorklistEntry::Inserted(x, new_term));
                    }
                }
            }
        }
    }

    fn handle_pointed_by(&mut self, t: IntegerTerm) {
        //TODO
        if let Some(from) = self.offsetable_terms[t as usize] {
            if !self.pointed_by_queries[from as usize] {
                self.pointed_by_queries.set(from as usize, true);
                self.worklist
                    .push_back(WorklistEntry::Demand(Demand::PointedBy(from)));
            }
        }

        let mut stack = self.edges.addr_ofs[t as usize].to_vec();
        let mut visited: HashSet<_> = stack.iter().copied().collect();
        while let Some(x) = stack.pop() {
            if self.edges.sols[x as usize].insert(t) {
                self.worklist.push_back(WorklistEntry::Inserted(x, t));
            }
            for (y, offsets) in &self.edges.subsets[x] {
                if !visited.insert(*y) {
                    continue;
                }
                if offsets.zero {
                    stack.push(*y);
                }
            }
        }
    }

    fn handle_inserted(&mut self, x: IntegerTerm, t: IntegerTerm) {
        for cond in &self.edges.conds[x as usize] {
            let mut edge = None;
            match cond {
                Cond::Left(cond) => match (self.term_types[t as usize], &cond.call_site) {
                    (TermType::Basic, None) if cond.offset == 0 => {
                        self.edges.subsets.add(t, cond.right, 0);
                        edge = Some((t, cond.right));
                    }

                    (TermType::Struct(max), None) | (TermType::Function(max, _), Some(_))
                        if cond.offset <= max =>
                    {
                        self.edges
                            .subsets
                            .add(t + cond.offset as u32, cond.right, 0);
                        edge = Some((t + cond.offset as u32, cond.right));
                    }

                    _ => {}
                },
                Cond::Right(cond) => match (self.term_types[t as usize], &cond.call_site) {
                    (TermType::Basic, None) if cond.offset == 0 => {
                        self.edges.subsets.add(cond.left, t, 0);
                        edge = Some((cond.left, t));
                    }

                    (TermType::Struct(max), None) | (TermType::Function(max, _), Some(_))
                        if cond.offset <= max =>
                    {
                        self.edges.subsets.add(cond.left, t + cond.offset as u32, 0);
                        edge = Some((cond.left, t + cond.offset as u32));
                    }

                    _ => {}
                },
                Cond::Dummy(cond) => {
                    todo!()
                }
            }
            if let Some((from, to)) = edge {
                if from == to {
                    continue;
                }
                let (from_set, to_set) = self.edges.sols.get_two_mut(from as usize, to as usize);
                for &term in &*from_set {
                    if !self.points_to_queries[to as usize]
                        && !self.pointed_by_queries[term as usize]
                    {
                        continue;
                    }
                    if to_set.insert(term) {
                        self.worklist.push_back(WorklistEntry::Inserted(to, term));
                    }
                }

                if self.pointed_by_queries[to as usize] && !self.pointed_by_queries[from as usize] {
                    self.pointed_by_queries.set(from as usize, true);
                    self.worklist
                        .push_back(WorklistEntry::Demand(Demand::PointedBy(from)));
                }
            }
        }

        let t_term_type = self.term_types[t as usize];
        for (to, offsets) in &self.edges.subsets[x] {
            for offset in offsets.iter() {
                let new_term = t + offset as u32;
                if offset > t_term_type.into_offset()
                    || (!self.points_to_queries[*to as usize]
                        && !self.pointed_by_queries[new_term as usize])
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
}

impl<C: ContextSelector> SolverSolution for BasicDemandSolverState<C> {
    type Term = IntegerTerm;

    type TermSet = HashSet<IntegerTerm>;

    fn get(&self, node: &Self::Term) -> Self::TermSet {
        todo!()
    }
}

struct Edges<C> {
    sols: Vec<HashSet<IntegerTerm>>,
    subsets: Subsets,
    conds: Vec<Vec<Cond<C>>>,
    addr_ofs: Vec<SmallVec<[IntegerTerm; 1]>>,
    rev_addr_ofs: Vec<SmallVec<[IntegerTerm; 1]>>,
}

impl<C> Edges<C> {
    fn add_constraint(&mut self, c: Constraint<IntegerTerm>, context: C) {
        match c {
            Constraint::Inclusion { term, node } => {
                self.addr_ofs[term as usize].push(node);
                self.rev_addr_ofs[node as usize].push(term);
            }
            Constraint::Subset {
                left,
                right,
                offset,
            } => self.subsets.add(left, right, offset),
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
}

struct Subsets {
    subset: Vec<HashMap<IntegerTerm, Offsets>>,
    rev_subset: Vec<HashMap<IntegerTerm, Offsets>>,
}

impl Subsets {
    fn rev(&self, index: IntegerTerm) -> &HashMap<IntegerTerm, Offsets> {
        &self.rev_subset[index as usize]
    }

    fn add(&mut self, from: IntegerTerm, to: IntegerTerm, offset: usize) {
        self.subset[from as usize]
            .entry(to)
            .or_default()
            .insert(offset);
        self.rev_subset[to as usize]
            .entry(from)
            .or_default()
            .insert(offset);
    }
}

impl Index<IntegerTerm> for Subsets {
    type Output = HashMap<IntegerTerm, Offsets>;

    fn index(&self, index: IntegerTerm) -> &Self::Output {
        &self.subset[index as usize]
    }
}
