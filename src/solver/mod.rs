use hashbrown::{HashMap, HashSet};
use roaring::RoaringBitmap;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::Cloned;
use std::ops::Add;

mod basic;
mod better_bitvec;
mod bit_vec;
mod stats;
#[cfg(test)]
mod tests;
mod wave_prop;

pub use basic::{BasicBetterBitVecSolver, BasicHashSolver, BasicRoaringSolver};
pub use better_bitvec::BetterBitVec;
pub use bit_vec::BasicBitVecSolver;
pub use stats::StatSolver;
pub use wave_prop::{
    BetterBitVecWavePropagationSolver, HashWavePropagationSolver, RoaringWavePropagationSolver,
};

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

    type Iterator<'a>: Iterator<Item = Self::Term>
    where
        Self: 'a;

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
    fn iter<'a>(&'a self) -> Self::Iterator<'a>;
}

impl<T: Eq + PartialEq + Hash + Clone> TermSetTrait for HashSet<T> {
    type Term = T;

    type Iterator<'a> = Cloned<hashbrown::hash_set::Iter<'a, T>> where T: 'a;

    #[inline(always)]
    fn new() -> Self {
        HashSet::new()
    }

    #[inline(always)]
    fn len(&self) -> usize {
        HashSet::len(&self)
    }

    #[inline(always)]
    fn contains(&self, term: Self::Term) -> bool {
        HashSet::contains(self, &term)
    }

    #[inline(always)]
    fn remove(&mut self, term: Self::Term) -> bool {
        HashSet::remove(self, &term)
    }

    #[inline(always)]
    fn insert(&mut self, term: Self::Term) -> bool {
        HashSet::insert(self, term)
    }

    #[inline(always)]
    fn union_assign(&mut self, other: &Self) {
        Extend::extend(self, other.iter().cloned());
    }

    #[inline(always)]
    fn extend<U: Iterator<Item = Self::Term>>(&mut self, other: U) {
        Extend::extend(self, other);
    }

    #[inline(always)]
    fn difference(&self, other: &Self) -> Self {
        HashSet::difference(self, other).cloned().collect()
    }

    #[inline(always)]
    fn iter<'a>(&'a self) -> Self::Iterator<'a> {
        HashSet::iter(self).cloned()
    }
}

impl TermSetTrait for RoaringBitmap {
    type Term = u32;

    type Iterator<'a> = roaring::bitmap::Iter<'a>;

    #[inline(always)]
    fn new() -> Self {
        RoaringBitmap::new()
    }

    #[inline(always)]
    fn len(&self) -> usize {
        RoaringBitmap::len(self) as usize
    }

    #[inline(always)]
    fn contains(&self, term: Self::Term) -> bool {
        RoaringBitmap::contains(&self, term)
    }

    #[inline(always)]
    fn remove(&mut self, term: Self::Term) -> bool {
        RoaringBitmap::remove(self, term)
    }

    #[inline(always)]
    fn insert(&mut self, term: Self::Term) -> bool {
        RoaringBitmap::insert(self, term)
    }

    #[inline(always)]
    fn union_assign(&mut self, other: &Self) {
        *self |= other;
    }

    #[inline(always)]
    fn extend<T: Iterator<Item = Self::Term>>(&mut self, other: T) {
        Extend::extend(self, other)
    }

    #[inline(always)]
    fn difference(&self, other: &Self) -> Self {
        self - other
    }

    #[inline(always)]
    fn iter<'a>(&'a self) -> Self::Iterator<'a> {
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
    *term_map.get(term).expect(&format!(
        "Invalid lookup for term that was not passed in during initialization: {term:?}"
    ))
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
