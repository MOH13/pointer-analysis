use bitvec::prelude::*;
use hashbrown::{HashMap, HashSet};
use std::collections::VecDeque;

use bitvec::vec::BitVec;

use crate::bit_index_utils::{no_alloc_and, no_alloc_difference, BitIndexIter};

use super::{offset_term, offset_terms, Constraint, Solver, UnivCond};

pub struct BasicBitVecSolver {
    worklist: VecDeque<(usize, usize)>,
    sols: Vec<BitVec<usize>>,
    edges: Vec<BitVec<usize>>,
    conds: Vec<Vec<UnivCond<usize>>>,
    weighted_edges: Vec<HashMap<usize, usize>>,
    offset_bitmask: BitVec<usize>,
    allowed_offsets: HashMap<usize, usize>,
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

            for n2 in self.edges[node].iter_ones() {
                add_token!(self, term, n2);
            }

            for (&n2, offset) in &self.weighted_edges[node] {
                if let Some(t) = offset_term(term, &self.allowed_offsets, *offset) {
                    add_token!(self, t, n2);
                }
            }
        }
    }

    fn add_edge(&mut self, left: usize, right: usize, offset: usize) {
        if offset == 0 {
            if !self.edges[left][right] {
                self.edges[left].set(right, true);

                let left_block_iter = self.sols[left].as_raw_slice().iter().copied();
                let right_block_iter = self.sols[right].as_raw_slice().iter().copied();

                for i in BitIndexIter::new(no_alloc_difference(left_block_iter, right_block_iter))
                    .collect::<Vec<_>>()
                {
                    add_token!(self, i, right);
                }
            }
        } else if self.weighted_edges[left].insert(right, offset).is_none() {
            let left_block_iter = self.sols[left].as_raw_slice().iter().copied();
            let offset_mask_iter = self.offset_bitmask.as_raw_slice().iter().copied();

            let offsetable_indices =
                BitIndexIter::new(no_alloc_and(left_block_iter, offset_mask_iter));
            let terms = offset_terms(offsetable_indices, &self.allowed_offsets, offset);

            for i in terms {
                add_token!(self, i, right)
            }
        } else {
            unreachable!()
        }
    }
}

impl Solver for BasicBitVecSolver {
    type Term = usize;
    type TermSet = HashSet<usize>;

    fn new(terms: Vec<usize>, allowed_offsets: Vec<(usize, usize)>) -> Self {
        let mut offset_bitmask = bitvec![0; terms.len()];
        for &(i, max_offset) in &allowed_offsets {
            if max_offset > 0 {
                offset_bitmask.set(i, true);
            }
        }

        Self {
            worklist: VecDeque::new(),
            sols: vec![bitvec![0; terms.len()]; terms.len()],
            edges: vec![bitvec![0; terms.len()]; terms.len()],
            conds: vec![vec![]; terms.len()],
            weighted_edges: vec![HashMap::new(); terms.len()],
            offset_bitmask: offset_bitmask,
            allowed_offsets: allowed_offsets.into_iter().collect(),
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
            Constraint::UnivCondSubsetLeft {
                cond_node,
                right,
                offset,
            } => {
                self.conds[cond_node].push(UnivCond::SubsetLeft { right, offset });
                let terms = offset_terms(
                    self.sols[cond_node].iter_ones(),
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
                self.conds[cond_node].push(UnivCond::SubsetRight { left, offset });
                let terms = offset_terms(
                    self.sols[cond_node].iter_ones(),
                    &self.allowed_offsets,
                    offset,
                );

                for t in terms {
                    self.add_edge(left, t, 0);
                }
            }
        };
        self.propagate()
    }

    fn get_solution(&self, node: &usize) -> HashSet<usize> {
        self.sols[*node].iter_ones().collect()
    }

    fn finalize(&mut self) {}
}
