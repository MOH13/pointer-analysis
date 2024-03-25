use std::collections::VecDeque;
use std::fmt::{Debug, Display};
use std::hash::Hash;

use hashbrown::{HashMap, HashSet};
use roaring::RoaringBitmap;

use super::shared_bitvec::SharedBitVec;
use super::{
    edges_between, offset_term, offset_terms, BetterBitVec, Constraint, ContextInsensitiveInput,
    GenericSolverSolution, IntegerTerm, Solver, SolverSolution, TermSetTrait, UnivCond,
};
use crate::visualizer::{Edge, EdgeKind, Graph, Node, OffsetWeight};

#[derive(Clone)]
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

impl<T: TermSetTrait<Term = IntegerTerm>> BasicSolver<IntegerTerm, T> {
    pub fn new() -> Self {
        Self {
            worklist: VecDeque::new(),
            sols: vec![],
            edges: vec![],
            conds: vec![],
            allowed_offsets: HashMap::new(),
        }
    }

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

    fn add_edge(&mut self, left: IntegerTerm, right: IntegerTerm, offset: usize) {
        let edges = edges_between(&mut self.edges, left, right);
        if edges.insert(offset as IntegerTerm) {
            for t in offset_terms(
                self.sols[left as usize].iter(),
                &self.allowed_offsets,
                offset,
            ) {
                add_token!(self, t, right);
            }
        }
    }

    fn add_constraint(&mut self, c: Constraint<IntegerTerm>) {
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
            Constraint::CallDummy { .. } => {}
        };
        self.propagate();
    }
}

impl<T: TermSetTrait<Term = IntegerTerm>> Solver<ContextInsensitiveInput<IntegerTerm>>
    for BasicSolver<IntegerTerm, T>
{
    type Solution = Self;

    fn solve(mut self, input: ContextInsensitiveInput<IntegerTerm>) -> Self::Solution {
        self.sols = vec![T::new(); input.terms.len()];
        self.edges = vec![HashMap::new(); input.terms.len()];
        self.conds = vec![vec![]; input.terms.len()];
        self.allowed_offsets = input
            .term_types
            .into_iter()
            .map(|(t, ty)| (t as IntegerTerm, ty.into_offset()))
            .collect();

        for c in input.constraints {
            self.add_constraint(c);
        }

        self
    }
}

impl<T: TermSetTrait<Term = IntegerTerm>> SolverSolution for BasicSolver<IntegerTerm, T> {
    type Term = IntegerTerm;

    type TermSet = T;

    fn get(&self, node: &Self::Term) -> Self::TermSet {
        self.sols[*node as usize].clone()
    }
}

pub type BasicHashSolver = BasicSolver<IntegerTerm, HashSet<IntegerTerm>>;
pub type BasicRoaringSolver = BasicSolver<IntegerTerm, RoaringBitmap>;
pub type BasicBetterBitVecSolver = BasicSolver<IntegerTerm, BetterBitVec>;
pub type BasicSharedBitVecSolver = BasicSolver<IntegerTerm, SharedBitVec>;

impl<T, S> Graph for GenericSolverSolution<BasicSolver<IntegerTerm, S>, T>
where
    T: Display + Debug + Clone + PartialEq + Eq + Hash,
    S: TermSetTrait<Term = IntegerTerm>,
{
    type Node = T;
    type Weight = OffsetWeight;

    fn nodes(&self) -> Vec<Node<Self::Node>> {
        self.mapping.terms_as_nodes()
    }

    fn edges(&self) -> Vec<Edge<Self::Node, Self::Weight>> {
        let mut edges = vec![];

        for (from, outgoing) in self.sub_solution.edges.iter().enumerate() {
            let from = Node {
                inner: self.mapping.integer_to_term(from as IntegerTerm),
                id: from,
            };
            for (&to, weights) in outgoing {
                let to = Node {
                    inner: self.mapping.integer_to_term(to as IntegerTerm),
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

        // for from in 0..self.mapping.terms.len() {
        //     let from_node = Node {
        //         inner: self.mapping.integer_to_term(from as IntegerTerm),
        //         id: from,
        //     };
        //     for to in self.sub_solution.get(&(from as IntegerTerm)).iter() {
        //         let to_node = Node {
        //             inner: self.mapping.integer_to_term(to),
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
