use bitvec::prelude::*;
use hashbrown::{hash_set, HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::Copied;

mod bit_vec;
mod hash;
mod stats;
#[cfg(test)]
mod tests;
mod wave_propagation;

pub use bit_vec::BasicBitVecSolver;
pub use hash::BasicHashSolver;
pub use stats::StatSolver;

#[derive(Debug)]
pub enum Constraint<T> {
    Inclusion {
        term: T,
        node: T,
    },
    Subset {
        left: T,
        right: T,
        offset: usize,
    },
    UnivCondSubsetLeft {
        cond_node: T,
        right: T,
        offset: usize,
    },
    UnivCondSubsetRight {
        cond_node: T,
        left: T,
        offset: usize,
    },
}

#[macro_export]
macro_rules! cstr {
    ($term:tt in $node:tt) => {
        $crate::solver::Constraint::Inclusion {
            term: $term,
            node: $node,
        }
    };
    ($left:tt <= $right:tt) => {
        $crate::solver::Constraint::Subset {
            left: $left,
            right: $right,
            offset: 0,
        }
    };
    ($left:tt + $offset:tt <= $right:tt) => {
        $crate::solver::Constraint::Subset {
            left: $left,
            right: $right,
            offset: $offset,
        }
    };
    (c in $cond_node:tt : c <= $right:tt) => {
        $crate::solver::Constraint::UnivCondSubsetLeft {
            cond_node: $cond_node,
            right: $right,
            offset: 0,
        }
    };
    (c in $cond_node:tt : $left:tt <= c) => {
        $crate::solver::Constraint::UnivCondSubsetRight {
            cond_node: $cond_node,
            left: $left,
            offset: 0,
        }
    };
    (c in $cond_node:tt + $offset:tt : c <= $right:tt) => {
        $crate::solver::Constraint::UnivCondSubsetLeft {
            cond_node: $cond_node,
            right: $right,
            offset: $offset,
        }
    };
    (c in $cond_node:tt + $offset:tt : $left:tt <= c) => {
        $crate::solver::Constraint::UnivCondSubsetRight {
            cond_node: $cond_node,
            left: $left,
            offset: $offset,
        }
    };
}

#[derive(Clone, Debug)]
enum UnivCond<T: Clone> {
    SubsetLeft { right: T, offset: usize },
    SubsetRight { left: T, offset: usize },
}

pub trait Solver {
    type Term;
    type TermSet;

    fn new(terms: Vec<Self::Term>, allowed_offsets: Vec<(Self::Term, usize)>) -> Self;

    fn add_constraint(&mut self, c: Constraint<Self::Term>);
    fn get_solution(&self, node: &Self::Term) -> Self::TermSet;

    fn finalize(&mut self);
}

pub trait IterableTermSet<T> {
    type Iter<'a>: Iterator<Item = T>
    where
        Self: 'a;
    fn iter_term_set<'a>(&'a self) -> Self::Iter<'a>;
}

impl<T> IterableTermSet<T> for HashSet<T>
where
    T: Copy,
{
    type Iter<'a> = Copied<hash_set::Iter<'a, T>> where T: 'a;

    fn iter_term_set<'a>(&'a self) -> Self::Iter<'a> {
        self.iter().copied()
    }
}

impl IterableTermSet<usize> for BitVec {
    type Iter<'a> = bitvec::slice::IterOnes<'a, usize, Lsb0>;

    fn iter_term_set<'a>(&'a self) -> Self::Iter<'a> {
        self.iter_ones()
    }
}

pub struct GenericSolver<T, S> {
    terms: Vec<T>,
    term_map: HashMap<T, usize>,
    sub_solver: S,
}

fn term_to_usize<T>(term_map: &HashMap<T, usize>, term: &T) -> usize
where
    T: Hash + Eq + Debug,
{
    *term_map.get(term).expect(&format!(
        "Invalid lookup for term that was not passed in during initialization: {term:?}"
    ))
}

fn edges_between(
    edges: &mut Vec<HashMap<usize, HashSet<usize>>>,
    left: usize,
    right: usize,
) -> &mut HashSet<usize> {
    edges[left].entry(right).or_default()
}

fn offset_term(
    term: usize,
    allowed_offsets: &HashMap<usize, usize>,
    offset: usize,
) -> Option<usize> {
    if offset == 0 {
        Some(term)
    } else {
        allowed_offsets
            .get(&term)
            .and_then(|&max_offset| (offset <= max_offset).then(|| term + offset))
    }
}

fn offset_terms<'a>(
    terms: impl Iterator<Item = usize>,
    allowed_offsets: &HashMap<usize, usize>,
    offset: usize,
) -> Vec<usize> {
    if offset == 0 {
        terms.collect()
    } else {
        terms
            .filter_map(|t| offset_term(t, allowed_offsets, offset))
            .collect()
    }
}

impl<T, S> GenericSolver<T, S>
where
    T: Hash + Eq + Clone + Debug,
{
    fn term_to_usize(&self, term: &T) -> usize {
        term_to_usize(&self.term_map, term)
    }

    fn usize_to_term(&self, i: usize) -> T {
        self.terms[i].clone()
    }

    fn translate_constraint(&self, c: Constraint<T>) -> Constraint<usize> {
        match c {
            Constraint::Inclusion { term, node } => {
                let term = self.term_to_usize(&term);
                let node = self.term_to_usize(&node);
                cstr!(term in node)
            }
            Constraint::Subset {
                left,
                right,
                offset,
            } => {
                let left = self.term_to_usize(&left);
                let right = self.term_to_usize(&right);
                cstr!(left + offset <= right)
            }
            Constraint::UnivCondSubsetLeft {
                cond_node,
                right,
                offset,
            } => {
                let cond_node = self.term_to_usize(&cond_node);
                let right = self.term_to_usize(&right);
                cstr!(c in cond_node + offset : c <= right)
            }
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
            } => {
                let cond_node = self.term_to_usize(&cond_node);
                let left = self.term_to_usize(&left);
                cstr!(c in cond_node + offset : left <= c)
            }
        }
    }
}

impl<T, S> Solver for GenericSolver<T, S>
where
    T: Hash + Eq + Clone + Debug,
    S: Solver<Term = usize>,
    S::TermSet: IterableTermSet<usize>,
{
    type Term = T;
    type TermSet = HashSet<T>;

    fn new(terms: Vec<Self::Term>, allowed_offsets: Vec<(Self::Term, usize)>) -> Self {
        let length = terms.len();
        let term_map = terms
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, t)| (t, i))
            .collect();
        let sub_solver = S::new(
            (0..length).collect(),
            allowed_offsets
                .into_iter()
                .map(|(term, offset)| (term_to_usize(&term_map, &term), offset))
                .collect(),
        );
        Self {
            terms,
            term_map,
            sub_solver,
        }
    }

    fn add_constraint(&mut self, c: Constraint<T>) {
        self.sub_solver.add_constraint(self.translate_constraint(c))
    }

    fn get_solution(&self, node: &T) -> HashSet<T> {
        let sol = self.sub_solver.get_solution(&self.term_to_usize(node));
        HashSet::from_iter(sol.iter_term_set().map(|i| self.usize_to_term(i)))
    }

    fn finalize(&mut self) {
        self.sub_solver.finalize();
    }
}
