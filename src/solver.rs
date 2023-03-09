use bitvec::prelude::*;
use hashbrown::{hash_set, HashMap, HashSet};
use std::collections::VecDeque;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::Copied;

use crate::bit_index_utils::no_alloc_difference;

pub enum Constraint<T> {
    Inclusion { term: T, node: T },
    Subset { left: T, right: T },
    UnivCondSubsetLeft { cond_node: T, right: T },
    UnivCondSubsetRight { cond_node: T, left: T },
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

pub struct BasicSolver {
    worklist: VecDeque<(usize, usize)>,
    sols: Vec<HashSet<usize>>,
    edges: Vec<HashSet<usize>>,
    conds: Vec<Vec<UnivCond<usize>>>,
}

impl BasicSolver {
    fn propagate(&mut self) {
        while let Some((term, node)) = self.worklist.pop_front() {
            for cond in &self.conds[node].clone() {
                match cond {
                    UnivCond::SubsetLeft(right) => self.add_edge(node, *right),
                    UnivCond::SubsetRight(left) => self.add_edge(*left, node),
                }
            }

            for n2 in self.edges[node].clone() {
                self.add_token(term, n2);
            }
        }
    }

    fn add_token(&mut self, term: usize, node: usize) {
        if self.sols[node].insert(term) {
            self.worklist.push_back((term, node));
        }
    }

    fn add_edge(&mut self, left: usize, right: usize) {
        if self.edges[left].insert(right) {
            let not_in_right: Vec<_> = self.sols[left]
                .difference(&self.sols[right])
                .copied()
                .collect();
            for t in not_in_right {
                self.add_token(t, right);
            }
        }
    }
}

impl Solver for BasicSolver {
    type Term = usize;
    type TermSet = HashSet<usize>;

    fn new(terms: Vec<usize>) -> Self {
        Self {
            worklist: VecDeque::new(),
            sols: vec![HashSet::new(); terms.len()],
            edges: vec![HashSet::new(); terms.len()],
            conds: vec![vec![]; terms.len()],
        }
    }

    fn add_constraint(&mut self, c: Constraint<usize>) {
        match c {
            Constraint::Inclusion { term, node } => {
                self.add_token(term, node);
            }
            Constraint::Subset { left, right } => {
                self.add_edge(left, right);
            }
            Constraint::UnivCondSubsetLeft { cond_node, right } => {
                self.conds[cond_node].push(UnivCond::SubsetLeft(right));
                let terms: Vec<_> = self.sols[cond_node].iter().copied().collect();

                for t in terms {
                    self.add_edge(t, right);
                }
            }
            Constraint::UnivCondSubsetRight { cond_node, left } => {
                self.conds[cond_node].push(UnivCond::SubsetRight(left));
                let terms: Vec<_> = self.sols[cond_node].iter().copied().collect();

                for t in terms {
                    self.add_edge(left, t);
                }
            }
        };
        self.propagate()
    }

    fn get_solution(&self, node: &usize) -> HashSet<usize> {
        self.sols[*node].clone()
    }
}

pub struct BasicBitVecSolver {
    worklist: VecDeque<(usize, usize)>,
    sols: Vec<BitVec<usize>>,
    edges: Vec<BitVec<usize>>,
    conds: Vec<Vec<UnivCond<usize>>>,
    temp_mem: Vec<usize>,
}

impl BasicBitVecSolver {
    fn propagate(&mut self) {
        while let Some((term, node)) = self.worklist.pop_front() {
            for cond in &self.conds[node].clone() {
                match cond {
                    UnivCond::SubsetLeft(right) => self.add_edge(node, *right),
                    UnivCond::SubsetRight(left) => self.add_edge(*left, node),
                }
            }

            for n2 in self.edges[node].iter_ones().collect::<Vec<_>>() {
                self.add_token(term, n2);
            }
        }
    }

    fn add_token(&mut self, term: usize, node: usize) {
        if !self.sols[node][term] {
            self.sols[node].set(term, true);
            self.worklist.push_back((term, node));
        }
    }

    fn add_edge(&mut self, left: usize, right: usize) {
        if !self.edges[left][right] {
            self.edges[left].set(right, true);

            for i in no_alloc_difference(&self.sols[left], &self.sols[right]).collect::<Vec<_>>() {
                self.add_token(i, right)
            }
        }
    }
}

impl Solver for BasicBitVecSolver {
    type Term = usize;
    type TermSet = BitVec;

    fn new(terms: Vec<usize>) -> Self {
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
                self.add_token(term, node);
            }
            Constraint::Subset { left, right } => {
                self.add_edge(left, right);
            }
            Constraint::UnivCondSubsetLeft { cond_node, right } => {
                self.conds[cond_node].push(UnivCond::SubsetLeft(right));
                let terms: Vec<_> = self.sols[cond_node].iter_ones().collect();

                for t in terms {
                    self.add_edge(t, right);
                }
            }
            Constraint::UnivCondSubsetRight { cond_node, left } => {
                self.conds[cond_node].push(UnivCond::SubsetRight(left));
                let terms: Vec<_> = self.sols[cond_node].iter_ones().collect();

                for t in terms {
                    self.add_edge(left, t);
                }
            }
        };
        self.propagate()
    }

    fn get_solution(&self, node: &usize) -> BitVec {
        self.sols[*node].clone()
    }
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
            Constraint::Inclusion { term, node } => Constraint::Inclusion {
                term: self.term_to_usize(&term),
                node: self.term_to_usize(&node),
            },
            Constraint::Subset { left, right } => Constraint::Subset {
                left: self.term_to_usize(&left),
                right: self.term_to_usize(&right),
            },
            Constraint::UnivCondSubsetLeft { cond_node, right } => Constraint::UnivCondSubsetLeft {
                cond_node: self.term_to_usize(&cond_node),
                right: self.term_to_usize(&right),
            },
            Constraint::UnivCondSubsetRight { cond_node, left } => {
                Constraint::UnivCondSubsetRight {
                    cond_node: self.term_to_usize(&cond_node),
                    left: self.term_to_usize(&left),
                }
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
        BasicBitVecSolver, BasicSolver, Constraint, GenericSolver, IterableTermSet, Solver,
    };

    fn simple_solver_test_template<T, S>(x: T, y: T, z: T, w: T)
    where
        T: Eq + Hash + Copy + Debug,
        S: Solver<Term = T>,
        S::TermSet: IterableTermSet<T>,
    {
        /*
           Pseudocode:
               x = &y
               z = x
               *z = x
        */
        let terms = vec![x, y, z, w];

        let mut solver = S::new(terms.clone());
        let constraints = [
            Constraint::Inclusion { term: y, node: x },
            Constraint::Subset { left: x, right: z },
            Constraint::UnivCondSubsetRight {
                cond_node: z,
                left: x,
            },
        ];

        for c in constraints {
            solver.add_constraint(c);
        }

        let expected_points_to_sets: HashMap<T, HashSet<T>> = HashMap::from_iter(
            [(x, vec![y]), (y, vec![y]), (z, vec![y]), (w, vec![])]
                .map(|(t, elems)| (t, HashSet::from_iter(elems))),
        );

        let actual_points_to_sets: HashMap<T, HashSet<T>> =
            HashMap::from_iter(vec![x, y, z, w].into_iter().map(|t| {
                (
                    t,
                    HashSet::from_iter(solver.get_solution(&t).iter_term_set()),
                )
            }));

        assert_eq!(expected_points_to_sets, actual_points_to_sets);
    }

    #[test]
    fn simple_solver_test_basic_solver() {
        let x = 0;
        let y = 1;
        let z = 2;
        let w = 3;
        simple_solver_test_template::<_, BasicSolver>(x, y, z, w)
    }

    #[test]
    fn simple_solver_test_basic_bit_vec_solver() {
        let x = 0;
        let y = 1;
        let z = 2;
        let w = 3;
        simple_solver_test_template::<_, BasicBitVecSolver>(x, y, z, w)
    }

    #[derive(PartialEq, Eq, Hash, Debug)]
    enum TestEnum {
        X,
        Y,
        Z,
        W,
    }

    #[test]
    fn simple_solver_test_generic_solver() {
        let x = TestEnum::X;
        let y = TestEnum::Y;
        let z = TestEnum::Z;
        let w = TestEnum::W;
        simple_solver_test_template::<_, GenericSolver<_, BasicSolver>>(&x, &y, &z, &w)
    }
}
