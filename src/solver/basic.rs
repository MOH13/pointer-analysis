use std::collections::VecDeque;

use hashbrown::{HashMap, HashSet};
use roaring::RoaringBitmap;

use super::{edges_between, offset_term, offset_terms, Constraint, Solver, TermSetTrait, UnivCond};

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

    fn new(terms: Vec<Self::Term>, allowed_offsets: Vec<(Self::Term, usize)>) -> Self {
        Self {
            worklist: VecDeque::new(),
            sols: vec![T::new(); terms.len()],
            edges: vec![HashMap::new(); terms.len()],
            conds: vec![vec![]; terms.len()],
            allowed_offsets: allowed_offsets.into_iter().collect(),
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
