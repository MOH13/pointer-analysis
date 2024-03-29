use hashbrown::{HashMap, HashSet};

use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::marker::PhantomData;

use crate::visualizer::{Edge, EdgeKind, Graph, Node, OffsetWeight};

use super::{ConstrainedTerms, Constraint, Solver, SolverSolution, TermSetTrait};

pub struct StatSolver<T> {
    terms: Vec<T>,
    inclusions: Vec<(T, T)>,
    subsets: Vec<(T, usize, T)>,
    cond_lefts: Vec<(T, usize, T)>,
    cond_rights: Vec<(T, usize, T)>,
}

#[derive(PartialEq, Eq, Clone, Hash)]
struct DummyTermSet<T> {
    phantom: PhantomData<T>,
}

impl<T> Default for DummyTermSet<T> {
    fn default() -> Self {
        Self {
            phantom: Default::default(),
        }
    }
}

impl<T: Hash + Eq + Clone> TermSetTrait for DummyTermSet<T> {
    type Term = T;

    fn new() -> Self {
        Self::default()
    }

    fn len(&self) -> usize {
        0
    }

    fn contains(&self, _term: Self::Term) -> bool {
        false
    }

    fn remove(&mut self, _term: Self::Term) -> bool {
        false
    }

    fn insert(&mut self, _term: Self::Term) -> bool {
        true
    }

    fn union_assign(&mut self, _other: &Self) {}

    fn extend<U: Iterator<Item = Self::Term>>(&mut self, _other: U) {}

    fn difference(&self, _other: &Self) -> Self {
        Self::default()
    }

    fn iter(&self) -> impl Iterator<Item = Self::Term> {
        [].into_iter()
    }
}

impl<T: Eq + PartialEq + Hash + Clone> StatSolver<T> {
    pub fn new() -> Self {
        Self {
            terms: vec![],
            inclusions: vec![],
            subsets: vec![],
            cond_lefts: vec![],
            cond_rights: vec![],
        }
    }

    fn add_constraint(&mut self, c: Constraint<T>) {
        match c {
            Constraint::Inclusion { term, node } => self.inclusions.push((node, term)),
            Constraint::Subset {
                left,
                right,
                offset,
            } => self.subsets.push((left, offset, right)),
            Constraint::UnivCondSubsetLeft {
                cond_node,
                right,
                offset,
                call_site: _, // TODO
            } => self.cond_lefts.push((cond_node, offset, right)),
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
                call_site: _,
            } => self.cond_rights.push((cond_node, offset, left)),
            Constraint::CallDummy { .. } => {}
        }
    }
}

impl<T: Eq + PartialEq + Hash + Clone> Solver<ConstrainedTerms<T>> for StatSolver<T>
where
    T: Hash + Eq + Clone + Debug,
{
    type Solution = StatSolver<T>;

    fn solve(mut self, input: ConstrainedTerms<T>) -> Self::Solution {
        self.terms = input.terms;
        self.inclusions = vec![];
        self.subsets = vec![];
        self.cond_lefts = vec![];
        self.cond_rights = vec![];

        for c in input.constraints {
            self.add_constraint(c);
        }

        println!("Terms:\t\t{}", self.terms.len());
        println!("Inclusion:\t{}", self.inclusions.len());

        let num_offset_subsets = self.subsets.iter().filter(|(_, o, _)| *o != 0).count();
        println!(
            "Subset:\t\t{} ({} offset constraints)",
            self.subsets.len(),
            num_offset_subsets
        );

        let num_offset_conds = self
            .cond_lefts
            .iter()
            .chain(&self.cond_rights)
            .filter(|(_, o, _)| *o != 0)
            .count();
        println!(
            "Univ. cond.:\t{} ({} offset constraints)",
            self.cond_lefts.len() + self.cond_rights.len(),
            num_offset_conds
        );

        let total = self.inclusions.len()
            + self.subsets.len()
            + self.cond_lefts.len()
            + self.cond_rights.len();
        println!("Total:\t\t{total}");

        self
    }
}

impl<T> SolverSolution for StatSolver<T>
where
    T: Hash + Eq + Clone + Debug,
{
    type Term = T;
    type TermSet = HashSet<T>;

    fn get(&self, _node: &Self::Term) -> Self::TermSet {
        HashSet::new()
    }
}

impl<T> Graph for StatSolver<T>
where
    T: Display + Debug + Clone + PartialEq + Eq + Hash,
{
    type Node = T;
    type Weight = OffsetWeight;

    fn nodes(&self) -> Vec<Node<Self::Node>> {
        self.terms
            .iter()
            .enumerate()
            .map(|(n, t)| Node {
                inner: t.clone(),
                id: n,
            })
            .collect()
    }

    fn edges(&self) -> Vec<Edge<Self::Node, Self::Weight>> {
        let term_ids: HashMap<_, _> = self.terms.iter().enumerate().map(|(i, t)| (t, i)).collect();
        let term_to_node = |t: &T| {
            let id = term_ids[t];
            Node {
                inner: t.clone(),
                id,
            }
        };

        self.subsets
            .iter()
            .map(|e| (e, EdgeKind::Subset))
            .chain(self.cond_lefts.iter().map(|e| (e, EdgeKind::CondLeft)))
            .chain(self.cond_rights.iter().map(|e| (e, EdgeKind::CondRight)))
            .map(|((l, o, r), kind)| Edge {
                from: term_to_node(l),
                to: term_to_node(r),
                weight: OffsetWeight(*o as u32),
                kind,
            })
            .chain(self.inclusions.iter().map(|(l, r)| Edge {
                from: term_to_node(l),
                to: term_to_node(r),
                weight: OffsetWeight(0),
                kind: EdgeKind::Inclusion,
            }))
            .collect()
    }
}
