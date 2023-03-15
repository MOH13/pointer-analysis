use bitvec::prelude::*;
use std::collections::VecDeque;

use bitvec::vec::BitVec;

use crate::bit_index_utils::no_alloc_difference;

use super::{Constraint, Solver, UnivCond};

pub struct BasicBitVecSolver {
    worklist: VecDeque<(usize, usize)>,
    sols: Vec<BitVec<usize>>,
    edges: Vec<BitVec<usize>>,
    // offset_edges: Vec<HashMap<usize, usize>>,
    conds: Vec<Vec<UnivCond<usize>>>,
    temp_mem: Vec<usize>,
}

macro_rules! add_token {
    ($solver:expr, $term:expr, $node:expr) => {
        if !$solver.sols[$node][$term] {
            $solver.sols[$node].set($term, true);
            $solver.worklist.push_back(($term, $node));
        }
    };
}

impl BasicBitVecSolver {
    fn propagate(&mut self) {
        while let Some((term, node)) = self.worklist.pop_front() {
            for cond in &self.conds[node].clone() {
                match cond {
                    UnivCond::SubsetLeft(right) => self.add_edge(node, *right, 0),
                    UnivCond::SubsetRight(left) => self.add_edge(*left, node, 0),
                }
            }

            for n2 in self.edges[node].iter_ones() {
                add_token!(self, term, n2);
            }
        }
    }

    fn add_edge(&mut self, left: usize, right: usize, offset: usize) {
        if !self.edges[left][right] {
            self.edges[left].set(right, true);

            for i in no_alloc_difference(&self.sols[left], &self.sols[right]).collect::<Vec<_>>() {
                add_token!(self, i, right);
            }
        }
    }
}

impl Solver for BasicBitVecSolver {
    type Term = usize;
    type TermSet = BitVec;

    fn new(terms: Vec<usize>, allowed_offsets: Vec<(usize, usize)>) -> Self {
        Self {
            worklist: VecDeque::new(),
            sols: vec![bitvec![0; terms.len()]; terms.len()],
            edges: vec![bitvec![0; terms.len()]; terms.len()],
            conds: vec![vec![]; terms.len()],
            temp_mem: vec![],
        }
    }

    fn add_constraint(&mut self, c: Constraint<usize>) {
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
            Constraint::UnivCondSubsetLeft { cond_node, right } => {
                self.conds[cond_node].push(UnivCond::SubsetLeft(right));
                let terms: Vec<_> = self.sols[cond_node].iter_ones().collect();

                for t in terms {
                    self.add_edge(t, right, 0);
                }
            }
            Constraint::UnivCondSubsetRight { cond_node, left } => {
                self.conds[cond_node].push(UnivCond::SubsetRight(left));
                let terms: Vec<_> = self.sols[cond_node].iter_ones().collect();

                for t in terms {
                    self.add_edge(left, t, 0);
                }
            }
        };
        self.propagate()
    }

    fn get_solution(&self, node: &usize) -> BitVec {
        self.sols[*node].clone()
    }
}
