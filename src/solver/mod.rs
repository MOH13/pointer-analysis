use hashbrown::{HashMap, HashSet};
use roaring::RoaringBitmap;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Add;

mod basic;
mod better_bitvec;
mod bit_vec;
mod shared_bitvec;
mod stats;
#[cfg(test)]
mod tests;
mod wave_prop;

pub use basic::{
    BasicBetterBitVecSolver, BasicHashSolver, BasicRoaringSolver, BasicSharedBitVecSolver,
};
pub use better_bitvec::BetterBitVec;
pub use bit_vec::BasicBitVecSolver;
pub use stats::StatSolver;
pub use wave_prop::{
    BetterBitVecWavePropagationSolver, HashWavePropagationSolver, RoaringWavePropagationSolver,
    SharedBitVecWavePropagationSolver,
};

use crate::visualizer::Node;

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

pub trait TermSetTrait: Clone + Default {
    type Term;

    fn new() -> Self;
    fn len(&self) -> usize;
    fn contains(&self, term: Self::Term) -> bool;
    // Returns true if the term was present before removal
    fn remove(&mut self, term: Self::Term) -> bool;
    // Returns true if the term was not present before insertion
    fn insert(&mut self, term: Self::Term) -> bool;
    fn union_assign(&mut self, other: &Self);
    fn extend<T: Iterator<Item = Self::Term>>(&mut self, other: T);
    fn difference(&self, other: &Self) -> Self;
    fn iter(&self) -> impl Iterator<Item = Self::Term>;
}

impl<T: Eq + PartialEq + Hash + Clone> TermSetTrait for HashSet<T> {
    type Term = T;

    #[inline]
    fn new() -> Self {
        HashSet::new()
    }

    #[inline]
    fn len(&self) -> usize {
        HashSet::len(&self)
    }

    #[inline]
    fn contains(&self, term: Self::Term) -> bool {
        HashSet::contains(self, &term)
    }

    #[inline]
    fn remove(&mut self, term: Self::Term) -> bool {
        HashSet::remove(self, &term)
    }

    #[inline]
    fn insert(&mut self, term: Self::Term) -> bool {
        HashSet::insert(self, term)
    }

    #[inline]
    fn union_assign(&mut self, other: &Self) {
        Extend::extend(self, other.iter().cloned());
    }

    #[inline]
    fn extend<U: Iterator<Item = Self::Term>>(&mut self, other: U) {
        Extend::extend(self, other);
    }

    #[inline]
    fn difference(&self, other: &Self) -> Self {
        HashSet::difference(self, other).cloned().collect()
    }

    #[inline]
    fn iter(&self) -> impl Iterator<Item = Self::Term> {
        HashSet::iter(self).cloned()
    }
}

impl TermSetTrait for RoaringBitmap {
    type Term = u32;

    #[inline]
    fn new() -> Self {
        RoaringBitmap::new()
    }

    #[inline]
    fn len(&self) -> usize {
        RoaringBitmap::len(self) as usize
    }

    #[inline]
    fn contains(&self, term: Self::Term) -> bool {
        RoaringBitmap::contains(&self, term)
    }

    #[inline]
    fn remove(&mut self, term: Self::Term) -> bool {
        RoaringBitmap::remove(self, term)
    }

    #[inline]
    fn insert(&mut self, term: Self::Term) -> bool {
        RoaringBitmap::insert(self, term)
    }

    #[inline]
    fn union_assign(&mut self, other: &Self) {
        *self |= other;
    }

    #[inline]
    fn extend<T: Iterator<Item = Self::Term>>(&mut self, other: T) {
        Extend::extend(self, other)
    }

    #[inline]
    fn difference(&self, other: &Self) -> Self {
        self - other
    }

    #[inline]
    fn iter(&self) -> impl Iterator<Item = Self::Term> {
        RoaringBitmap::iter(&self)
    }
}

pub trait Solver {
    type Term;
    type TermSet: TermSetTrait<Term = Self::Term>;

    fn new(terms: Vec<Self::Term>, allowed_offsets: Vec<(Self::Term, usize)>) -> Self;

    fn add_constraint(&mut self, c: Constraint<Self::Term>);
    fn get_solution(&self, node: &Self::Term) -> Self::TermSet;

    fn finalize(&mut self);
}

pub struct GenericSolver<T, S, T2> {
    terms: Vec<T>,
    term_map: HashMap<T, T2>,
    sub_solver: S,
}

fn term_to_t2<T, T2>(term_map: &HashMap<T, T2>, term: &T) -> T2
where
    T: Hash + Eq + Debug,
    T2: Copy,
{
    *term_map.get(term).unwrap_or_else(|| {
        panic!("Invalid lookup for term that was not passed in during initialization: {term:?}")
    })
}

fn edges_between<T: Hash + Eq + TryInto<usize>, U: Default>(
    edges: &mut Vec<HashMap<T, U>>,
    left: T,
    right: T,
) -> &mut U {
    edges[left
        .try_into()
        .map_err(|_| ())
        .expect("Could not convert to usize")]
    .entry(right)
    .or_default()
}

fn offset_term<T>(term: T, allowed_offsets: &HashMap<T, usize>, offset: usize) -> Option<T>
where
    T: Hash + Eq + Ord + TryInto<usize> + TryFrom<usize> + Add<T, Output = T>,
{
    if offset == 0 {
        Some(term)
    } else {
        allowed_offsets.get(&term).and_then(|&max_offset| {
            (offset <= max_offset).then(|| {
                term + offset
                    .try_into()
                    .map_err(|_| ())
                    .expect("Could not convert from usize")
            })
        })
    }
}

fn offset_terms<T>(
    terms: impl Iterator<Item = T>,
    allowed_offsets: &HashMap<T, usize>,
    offset: usize,
) -> Vec<T>
where
    T: Hash + Eq + Ord + TryInto<usize> + TryFrom<usize> + Add<T, Output = T>,
{
    if offset == 0 {
        terms.collect()
    } else {
        terms
            .filter_map(|t| offset_term(t, allowed_offsets, offset))
            .collect()
    }
}

fn to_usize<T>(v: T) -> usize
where
    T: TryInto<usize>,
{
    v.try_into()
        .map_err(|_| ())
        .expect("Could not convert to usize")
}

fn from_usize<T>(v: usize) -> T
where
    T: TryFrom<usize>,
{
    v.try_into()
        .map_err(|_| ())
        .expect("Could not convert to usize")
}

impl<T: Clone, S, T2> GenericSolver<T, S, T2> {
    fn terms_as_nodes(&self) -> Vec<Node<T>> {
        self.terms
            .iter()
            .enumerate()
            .map(|(n, t)| Node {
                inner: t.clone(),
                id: n,
            })
            .collect()
    }
}

impl<T, S> GenericSolver<T, S, S::Term>
where
    T: Hash + Eq + Clone + Debug,
    S: Solver,
    S::Term: TryInto<usize> + TryFrom<usize> + Copy,
{
    fn term_to_t2(&self, term: &T) -> S::Term {
        term_to_t2(&self.term_map, term)
    }

    fn t2_to_term(&self, i: S::Term) -> T {
        self.terms[to_usize(i)].clone()
    }

    fn translate_constraint(&self, c: Constraint<T>) -> Constraint<S::Term> {
        match c {
            Constraint::Inclusion { term, node } => {
                let term = self.term_to_t2(&term);
                let node = self.term_to_t2(&node);
                cstr!(term in node)
            }
            Constraint::Subset {
                left,
                right,
                offset,
            } => {
                let left = self.term_to_t2(&left);
                let right = self.term_to_t2(&right);
                cstr!(left + offset <= right)
            }
            Constraint::UnivCondSubsetLeft {
                cond_node,
                right,
                offset,
            } => {
                let cond_node = self.term_to_t2(&cond_node);
                let right = self.term_to_t2(&right);
                cstr!(c in cond_node + offset : c <= right)
            }
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
            } => {
                let cond_node = self.term_to_t2(&cond_node);
                let left = self.term_to_t2(&left);
                cstr!(c in cond_node + offset : left <= c)
            }
        }
    }
}

impl<T, S> Solver for GenericSolver<T, S, S::Term>
where
    T: Hash + Eq + Clone + Debug,
    S: Solver,
    S::Term: TryInto<usize> + TryFrom<usize> + Copy,
{
    type Term = T;
    type TermSet = HashSet<T>;

    fn new(terms: Vec<Self::Term>, allowed_offsets: Vec<(Self::Term, usize)>) -> Self {
        let length = terms.len();
        let term_map = terms
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, t)| (t, from_usize(i)))
            .collect();
        let sub_solver = S::new(
            (0..length)
                .map(|v| {
                    v.try_into()
                        .map_err(|_| ())
                        .expect("Could not convert to usize")
                })
                .collect(),
            allowed_offsets
                .into_iter()
                .map(|(term, offset)| (term_to_t2(&term_map, &term), offset))
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
        let sol = self.sub_solver.get_solution(&self.term_to_t2(node));
        HashSet::from_iter(sol.iter().map(|i| self.t2_to_term(i)))
    }

    fn finalize(&mut self) {
        self.sub_solver.finalize();
    }
}
