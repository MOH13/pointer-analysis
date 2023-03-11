use bitvec::prelude::*;
use hashbrown::{hash_set, HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::Copied;

mod bit_vec;
mod hash;

pub use bit_vec::BasicBitVecSolver;
pub use hash::BasicHashSolver;

pub enum Constraint<T> {
    Inclusion { term: T, node: T },
    Subset { left: T, right: T, offset: usize },
    UnivCondSubsetLeft { cond_node: T, right: T },
    UnivCondSubsetRight { cond_node: T, left: T },
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
        }
    };
    (c in $cond_node:tt : $left:tt <= c) => {
        $crate::solver::Constraint::UnivCondSubsetRight {
            cond_node: $cond_node,
            left: $left,
        }
    };
}

#[derive(Clone)]
enum UnivCond<T: Clone> {
    SubsetLeft(T),
    SubsetRight(T),
}

pub trait Solver {
    type Term;
    type TermSet;

    fn new(terms: Vec<Self::Term>) -> Self;

    fn add_constraint(&mut self, c: Constraint<Self::Term>);
    fn get_solution(&self, node: &Self::Term) -> Self::TermSet;
}

trait IterableTermSet<T> {
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

impl<T, S> GenericSolver<T, S>
where
    T: Hash + Eq + Clone + Debug,
{
    fn term_to_usize(&self, term: &T) -> usize {
        *self.term_map.get(term).expect(&format!(
            "Invalid lookup for term that was not passed in during initialization: {term:?}"
        ))
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
            Constraint::UnivCondSubsetLeft { cond_node, right } => {
                let cond_node = self.term_to_usize(&cond_node);
                let right = self.term_to_usize(&right);
                cstr!(c in cond_node : c <= right)
            }
            Constraint::UnivCondSubsetRight { cond_node, left } => {
                let cond_node = self.term_to_usize(&cond_node);
                let left = self.term_to_usize(&left);
                cstr!(c in cond_node : left <= c)
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

    fn new(terms: Vec<Self::Term>) -> Self {
        let length = terms.len();
        Self {
            terms: terms.clone(),
            term_map: HashMap::from_iter(terms.into_iter().enumerate().map(|(i, t)| (t, i))),
            sub_solver: S::new((0..length).collect()),
        }
    }

    fn add_constraint(&mut self, c: Constraint<T>) {
        self.sub_solver.add_constraint(self.translate_constraint(c))
    }

    fn get_solution(&self, node: &T) -> HashSet<T> {
        let sol = self.sub_solver.get_solution(&self.term_to_usize(node));
        HashSet::from_iter(sol.iter_term_set().map(|i| self.usize_to_term(i)))
    }
}

#[cfg(test)]
mod tests {
    use core::hash::Hash;
    use hashbrown::{HashMap, HashSet};
    use std::fmt::Debug;

    use super::{
        BasicBitVecSolver, BasicHashSolver, Constraint, GenericSolver, IterableTermSet, Solver,
    };
    use crate::cstr;

    macro_rules! output {
        [ $( $ptr:tt -> { $($target:tt),* } ),* ] => {
            [$( ($ptr, vec![$( $target ),*] ) ),*]
                .into_iter()
                .map(|(t, elems)| (t, HashSet::from_iter(elems)))
                .collect::<HashMap<_, HashSet<_>>>()
        };
    }

    fn solver_test_template<T, S>(
        terms: Vec<T>,
        constraints: impl IntoIterator<Item = Constraint<T>>,
        expected_output: HashMap<T, HashSet<T>>,
    ) where
        T: Eq + Hash + Copy + Debug,
        S: Solver<Term = T>,
        S::TermSet: IterableTermSet<T>,
    {
        let mut solver = S::new(terms.clone());
        for c in constraints {
            solver.add_constraint(c);
        }

        let actual_output: HashMap<T, HashSet<T>> = terms
            .into_iter()
            .map(|t| (t, solver.get_solution(&t).iter_term_set().collect()))
            .collect();

        assert_eq!(expected_output, actual_output);
    }

    /// Pseudo code:
    /// ```
    /// x = &y
    /// z = x
    /// *z = x
    /// w = null
    /// ```
    fn simple_ref_store_template<T, S>(x: T, y: T, z: T, w: T)
    where
        T: Eq + Hash + Copy + Debug,
        S: Solver<Term = T>,
        S::TermSet: IterableTermSet<T>,
    {
        let terms = vec![x, y, z, w];
        let constraints = [cstr!(y in x), cstr!(x <= z), cstr!(c in z : x <= c)];
        let expected_output = output![x -> {y}, y -> {y}, z -> {y}, w -> {}];
        solver_test_template::<T, S>(terms, constraints, expected_output);
    }

    #[test]
    fn simple_ref_store_basic_hash_solver() {
        simple_ref_store_template::<_, BasicHashSolver>(0, 1, 2, 3);
    }

    #[test]
    fn simple_ref_store_basic_bit_vec_solver() {
        simple_ref_store_template::<_, BasicBitVecSolver>(0, 1, 2, 3);
    }

    #[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
    enum SimpleRefStoreTerm {
        X,
        Y,
        Z,
        W,
    }

    #[test]
    fn simple_ref_store_generic_solver() {
        let x = SimpleRefStoreTerm::X;
        let y = SimpleRefStoreTerm::Y;
        let z = SimpleRefStoreTerm::Z;
        let w = SimpleRefStoreTerm::W;
        simple_ref_store_template::<_, GenericSolver<_, BasicHashSolver>>(x, y, z, w);
    }

    /// Pseudo code:
    /// ```
    /// x = null
    /// y = { f: 0, g: &x }
    /// py = &y
    /// pg = &py->g
    /// z = *pg
    /// *z = py
    /// *pg = py
    /// ```
    fn field_load_store_template<T, S>(x: T, yf: T, yg: T, py: T, pg: T, z: T)
    where
        T: Eq + Hash + Copy + Debug,
        S: Solver<Term = T>,
        S::TermSet: IterableTermSet<T>,
    {
        let terms = vec![x, yf, yg, py, pg, z];
        let constraints = [
            cstr!(x in yg),
            cstr!(yf in py),
            cstr!(py + 1 <= pg),
            cstr!(c in pg : c <= z),
            cstr!(c in z : py <= c),
            cstr!(c in pg : py <= c),
        ];
        let expected_output =
            output![x -> {yf}, yf -> {}, yg -> {x, yf}, py -> {yf}, pg -> {yg}, z -> {x, yf}];
        solver_test_template::<T, S>(terms, constraints, expected_output);
    }

    #[test]
    fn field_load_store_basic_hash_solver() {
        field_load_store_template::<_, BasicHashSolver>(0, 1, 2, 3, 4, 5);
    }

    #[test]
    fn field_load_store_basic_bit_vec_solver() {
        field_load_store_template::<_, BasicBitVecSolver>(0, 1, 2, 3, 4, 5);
    }

    #[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
    enum FieldLoadStoreTerm {
        X,
        Yf,
        Yg,
        Py,
        Pg,
        Z,
    }

    #[test]
    fn field_load_store_generic_solver() {
        let x = FieldLoadStoreTerm::X;
        let yf = FieldLoadStoreTerm::Yf;
        let yg = FieldLoadStoreTerm::Yg;
        let py = FieldLoadStoreTerm::Py;
        let pg = FieldLoadStoreTerm::Pg;
        let z = FieldLoadStoreTerm::Z;
        field_load_store_template::<_, GenericSolver<_, BasicHashSolver>>(x, yf, yg, py, pg, z);
    }
}
