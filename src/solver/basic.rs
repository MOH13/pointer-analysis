use std::collections::VecDeque;
use std::fmt::{Debug, Display};
use std::hash::Hash;

use hashbrown::{HashMap, HashSet};
use roaring::RoaringBitmap;

use super::shared_bitvec::SharedBitVec;
use super::{
    edges_between, offset_term, offset_terms, BetterBitVec, Constraint, GenericSolver, Solver,
    TermSetTrait, TermType, UnivCond,
};
use crate::visualizer::{Edge, EdgeKind, Graph, Node, OffsetWeight};

pub struct BasicSolver<T: Clone, U> {
    worklist: VecDeque<(T, T)>,
    sols: Vec<U>,
    edges: Vec<HashMap<T, U>>,
    conds: Vec<Vec<UnivCond<T>>>,
    allowed_offsets: HashMap<T, usize>,
}

macro_rules! add_token {
    ($solver:expr, $term:expr, $node:expr) => {
        if $solver.sols[$node as usize].insert($term) {
            $solver.worklist.push_back(($term, $node));
        }
    };
}

impl<T: TermSetTrait<Term = u32>> BasicSolver<u32, T> {
    fn propagate(&mut self) {
        while let Some((term, node)) = self.worklist.pop_front() {
            for cond in &self.conds[node as usize].clone() {
                match cond {
                    UnivCond::SubsetLeft { right, offset } => {
                        if let Some(t) = offset_term(term, &self.allowed_offsets, *offset) {
                            self.add_edge(t, *right, 0)
                        }
                    }
                    UnivCond::SubsetRight { left, offset } => {
                        if let Some(t) = offset_term(term, &self.allowed_offsets, *offset) {
                            self.add_edge(*left, t, 0)
                        }
                    }
                }
            }

            for (&n2, edges) in &self.edges[node as usize] {
                for offset in edges.iter() {
                    if let Some(t) = offset_term(term, &self.allowed_offsets, offset as usize) {
                        add_token!(self, t, n2);
                    }
                }
            }
        }
    }

    fn add_edge(&mut self, left: u32, right: u32, offset: usize) {
        let edges = edges_between(&mut self.edges, left, right);
        if edges.insert(offset as u32) {
            for t in offset_terms(
                self.sols[left as usize].iter(),
                &self.allowed_offsets,
                offset,
            ) {
                add_token!(self, t, right);
            }
        }
    }
}

impl<T: TermSetTrait<Term = u32>> Solver for BasicSolver<u32, T> {
    type Term = u32;
    type TermSet = T;

    fn new(terms: Vec<Self::Term>, term_types: Vec<(Self::Term, TermType)>) -> Self {
        Self {
            worklist: VecDeque::new(),
            sols: vec![T::new(); terms.len()],
            edges: vec![HashMap::new(); terms.len()],
            conds: vec![vec![]; terms.len()],
            // TODO: use term types instead
            allowed_offsets: term_types
                .into_iter()
                .map(|(t, ty)| (t, ty.into_offset()))
                .collect(),
        }
    }

    fn add_constraint(&mut self, c: Constraint<Self::Term>) {
        match c {
            Constraint::Inclusion { term, node } => {
                add_token!(self, term, node);
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
                ..// TODO: functions
            } => {
                self.conds[cond_node as usize].push(UnivCond::SubsetLeft { right, offset });
                let terms = offset_terms(
                    self.sols[cond_node as usize].iter(),
                    &self.allowed_offsets,
                    offset,
                );

                for t in terms {
                    self.add_edge(t, right, 0);
                }
            }
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
                ..// TODO: functions
            } => {
                self.conds[cond_node as usize].push(UnivCond::SubsetRight { left, offset });
                let terms = offset_terms(
                    self.sols[cond_node as usize].iter(),
                    &self.allowed_offsets,
                    offset,
                );

                for t in terms {
                    self.add_edge(left, t, 0);
                }
            }
        };
        self.propagate();
    }

    fn get_solution(&self, node: &Self::Term) -> Self::TermSet {
        self.sols[*node as usize].clone()
    }

    fn finalize(&mut self) {}
}

pub type BasicHashSolver = BasicSolver<u32, HashSet<u32>>;
pub type BasicRoaringSolver = BasicSolver<u32, RoaringBitmap>;
pub type BasicBetterBitVecSolver = BasicSolver<u32, BetterBitVec>;
pub type BasicSharedBitVecSolver = BasicSolver<u32, SharedBitVec>;

impl<T, S> Graph for GenericSolver<T, BasicSolver<u32, S>, u32>
where
    T: Display + Debug + Clone + PartialEq + Eq + Hash,
    S: TermSetTrait<Term = u32>,
{
    type Node = T;
    type Weight = OffsetWeight;

    fn nodes(&self) -> Vec<Node<Self::Node>> {
        self.terms_as_nodes()
    }

    fn edges(&self) -> Vec<Edge<Self::Node, Self::Weight>> {
        let mut edges = vec![];

        for (from, outgoing) in self.sub_solver.edges.iter().enumerate() {
            let from = Node {
                inner: self.t2_to_term(from as u32),
                id: from,
            };
            for (&to, weights) in outgoing {
                let to = Node {
                    inner: self.t2_to_term(to as u32),
                    id: to as usize,
                };
                for weight in weights.iter() {
                    let edge = Edge {
                        from: from.clone(),
                        to: to.clone(),
                        weight: OffsetWeight(weight),
                        kind: EdgeKind::Subset,
                    };
                    edges.push(edge);
                }
            }
        }

        for from in 0..self.terms.len() {
            let from_node = Node {
                inner: self.t2_to_term(from as u32),
                id: from,
            };
            for to in self.sub_solver.get_solution(&(from as u32)).iter() {
                let to_node = Node {
                    inner: self.t2_to_term(to),
                    id: to as usize,
                };
                let edge = Edge {
                    from: from_node.clone(),
                    to: to_node.clone(),
                    weight: OffsetWeight(0),
                    kind: EdgeKind::Inclusion,
                };
                edges.push(edge);
            }
        }

        edges
    }
}
