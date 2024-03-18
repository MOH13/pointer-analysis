use hashbrown::{HashMap, HashSet};
use roaring::RoaringBitmap;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::mem;

mod basic;
mod better_bitvec;
mod shared_bitvec;
mod stats;
#[cfg(test)]
mod tests;
mod wave_prop;

pub use basic::{
    BasicBetterBitVecSolver, BasicHashSolver, BasicRoaringSolver, BasicSharedBitVecSolver,
};
pub use better_bitvec::BetterBitVec;
// pub use bit_vec::BasicBitVecSolver;
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
        is_function: bool,
    },
    UnivCondSubsetRight {
        cond_node: T,
        left: T,
        offset: usize,
        is_function: bool,
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
    (*($cond_node:tt + $offset:tt) <= $right:tt) => {
        $crate::solver::Constraint::UnivCondSubsetLeft {
            cond_node: $cond_node,
            right: $right,
            offset: $offset,
            is_function: false,
        }
    };
    ($left:tt <= *($cond_node:tt + $offset:tt)) => {
        $crate::solver::Constraint::UnivCondSubsetRight {
            cond_node: $cond_node,
            left: $left,
            offset: $offset,
            is_function: false,
        }
    };
    (*$cond_node:tt <= $right:tt) => {
        $crate::solver::Constraint::UnivCondSubsetLeft {
            cond_node: $cond_node,
            right: $right,
            offset: 0,
            is_function: false,
        }
    };
    ($left:tt <= *$cond_node:tt) => {
        $crate::solver::Constraint::UnivCondSubsetRight {
            cond_node: $cond_node,
            left: $left,
            offset: 0,
            is_function: false,
        }
    };
    (*fn ($cond_node:tt + $offset:tt) <= $right:tt) => {
        $crate::solver::Constraint::UnivCondSubsetLeft {
            cond_node: $cond_node,
            right: $right,
            offset: $offset,
            is_function: true,
        }
    };
    ($left:tt <= *fn ($cond_node:tt + $offset:tt)) => {
        $crate::solver::Constraint::UnivCondSubsetRight {
            cond_node: $cond_node,
            left: $left,
            offset: $offset,
            is_function: true,
        }
    };
}

pub type IntegerTerm = u32;

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
    fn iter(&self) -> impl Iterator<Item = Self::Term>;
    fn difference(&self, other: &Self) -> Self;
    // Only guarantees that if self is superset of other, then the result is a subset of self and a superset of self.difference(other)
    fn weak_difference(&self, other: &Self) -> Self {
        self.difference(other)
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
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
    type Term = IntegerTerm;

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

#[derive(Debug)]
pub struct ConstrainedTerms<T> {
    pub terms: Vec<T>,
    pub term_types: Vec<(T, TermType)>,
    pub constraints: Vec<Constraint<T>>,
}

impl<T> ConstrainedTerms<T> {
    fn combine(&mut self, other: Self) {
        self.terms.extend(other.terms);
        self.term_types.extend(other.term_types);
        self.constraints.extend(other.constraints);
    }
}
pub trait Solver<I>
where
    I: SolverInput,
{
    type Solution: SolverSolution<Term = I::Term>;

    fn solve(self, input: I) -> Self::Solution;

    fn as_generic(self) -> GenericSolver<Self>
    where
        Self: Sized,
        I: SolverInput<Term = IntegerTerm>,
    {
        GenericSolver::new(self)
    }
}

// impl<F, I, O> Solver<I> for F
// where
//     F: FnOnce(I) -> O,
//     I: SolverInput<Term = O::Term>,
//     O: SolverSolution,
// {
//     type Solution = O;

//     fn solve(self, input: I) -> Self::Solution {
//         self(input)
//     }
// }

pub trait SolverInput {
    type Term;
}

pub struct ContextSensitiveInput<T, F> {
    pub entry: ConstrainedTerms<T>,
    pub functions: Vec<(F, ConstrainedTerms<T>)>,
}

impl<T, F> SolverInput for ContextSensitiveInput<T, F> {
    type Term = T;
}

pub type ContextInsensitiveInput<T> = ConstrainedTerms<T>;

impl<T> SolverInput for ContextInsensitiveInput<T> {
    type Term = T;
}

pub trait SolverSolution {
    type Term;
    type TermSet: TermSetTrait<Term = Self::Term>;

    fn get(&self, node: &Self::Term) -> Self::TermSet;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TermType {
    Basic,
    Struct(usize),
    Function(usize),
}

impl TermType {
    pub fn into_offset(self) -> usize {
        match self {
            TermType::Basic => 0,
            TermType::Struct(offset) | TermType::Function(offset) => offset,
        }
    }

    pub fn is_basic(self) -> bool {
        self == TermType::Basic
    }
}

pub trait ContextInsensitiveSolver<T>: Solver<ContextInsensitiveInput<T>> {
    type ContextSensitiveSolver<F>: Solver<ContextSensitiveInput<T, F>>;

    fn as_context_sensitive<F>(self) -> Self::ContextSensitiveSolver<F>;
}

impl<S, T> ContextInsensitiveSolver<T> for S
where
    S: Solver<ContextInsensitiveInput<T>> + Sized,
{
    type ContextSensitiveSolver<F> = AsContextSensitive<S, F>;

    fn as_context_sensitive<F>(self) -> Self::ContextSensitiveSolver<F> {
        AsContextSensitive(self, PhantomData)
    }
}

#[derive(Clone)]
pub struct AsContextSensitive<S, F>(pub S, PhantomData<F>);

impl<S, T, F> Solver<ContextSensitiveInput<T, F>> for AsContextSensitive<S, F>
where
    S: Solver<ContextInsensitiveInput<T>>,
{
    type Solution = S::Solution;

    fn solve(self, mut input: ContextSensitiveInput<T, F>) -> Self::Solution {
        for (_, t) in input.functions {
            input.entry.combine(t);
        }
        self.0.solve(input.entry)
    }
}

pub struct WithoutContext<S>(pub S);

impl<S, T, F> Solver<ContextSensitiveInput<T, F>> for WithoutContext<S>
where
    S: Solver<ContextSensitiveInput<T, F>>,
{
    type Solution = S::Solution;

    fn solve(self, mut input: ContextSensitiveInput<T, F>) -> Self::Solution {
        let funcs = mem::take(&mut input.functions);
        for (_, t) in funcs {
            input.entry.combine(t);
        }
        self.0.solve(input)
    }
}

#[derive(Clone)]
pub struct GenericSolver<S> {
    sub_solver: S,
}

impl<S> GenericSolver<S> {
    pub fn new(sub_solver: S) -> Self {
        Self { sub_solver }
    }
}

impl<S, T> Solver<ContextInsensitiveInput<T>> for GenericSolver<S>
where
    T: Hash + Eq + Clone + Debug,
    S: Solver<ContextInsensitiveInput<IntegerTerm>>,
{
    type Solution = GenericSolverSolution<S::Solution, T>;

    fn solve(self, constrained_terms: ContextInsensitiveInput<T>) -> Self::Solution {
        let terms = constrained_terms.terms.clone();
        let mapping = GenericIdMap::from_terms(terms);

        let translated = mapping.translate_constrained_terms(&constrained_terms);
        let sub_solution = self.sub_solver.solve(translated);
        GenericSolverSolution {
            mapping,
            sub_solution,
        }
    }
}

impl<S, T, F> Solver<ContextSensitiveInput<T, F>> for GenericSolver<S>
where
    T: Hash + Eq + Clone + Debug,
    F: Hash + Eq + Clone + Debug,
    S: Solver<ContextSensitiveInput<IntegerTerm, IntegerTerm>>,
{
    type Solution = GenericSolverSolution<S::Solution, T, F>;

    fn solve(self, input: ContextSensitiveInput<T, F>) -> Self::Solution {
        let terms = input
            .entry
            .terms
            .iter()
            .chain(input.functions.iter().flat_map(|(_, t)| &t.terms))
            .cloned()
            .collect();
        let functions = input.functions.iter().map(|(f, _)| f.clone()).collect();
        let mapping = GenericIdMap::new(terms, functions);

        let translated_entry = mapping.translate_constrained_terms(&input.entry);
        let translated_functions = input
            .functions
            .iter()
            .map(|(id, f)| {
                (
                    mapping.function_to_integer(id),
                    mapping.translate_constrained_terms(f),
                )
            })
            .collect();
        let translated_input = ContextSensitiveInput {
            entry: translated_entry,
            functions: translated_functions,
        };
        let sub_solution = self.sub_solver.solve(translated_input);
        GenericSolverSolution {
            mapping,
            sub_solution,
        }
    }
}

pub struct GenericIdMap<T, F = ()> {
    terms: Vec<T>,
    term_map: HashMap<T, IntegerTerm>,
    _functions: Vec<F>,
    function_map: HashMap<F, IntegerTerm>,
}

impl<T, F> GenericIdMap<T, F>
where
    T: Hash + Eq + Clone + Debug,
{
    fn from_terms(terms: Vec<T>) -> Self {
        let term_map = terms
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, t)| (t, i as IntegerTerm))
            .collect();
        Self {
            terms,
            term_map,
            _functions: vec![],
            function_map: HashMap::new(),
        }
    }

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

    fn term_to_integer(&self, term: &T) -> IntegerTerm {
        *self.term_map.get(term).unwrap_or_else(|| {
            panic!("Invalid lookup for term that was not passed in during initialization: {term:?}")
        })
    }

    fn integer_to_term(&self, i: IntegerTerm) -> T {
        self.terms[i as usize].clone()
    }

    fn translate_constraint(&self, c: &Constraint<T>) -> Constraint<IntegerTerm> {
        match c {
            Constraint::Inclusion { term, node } => {
                let term = self.term_to_integer(term);
                let node = self.term_to_integer(node);
                cstr!(term in node)
            }
            Constraint::Subset {
                left,
                right,
                offset,
            } => {
                let left = self.term_to_integer(&left);
                let right = self.term_to_integer(&right);
                cstr!(left + (*offset) <= right)
            }
            Constraint::UnivCondSubsetLeft {
                cond_node,
                right,
                offset,
                is_function,
            } => {
                let cond_node = self.term_to_integer(&cond_node);
                let right = self.term_to_integer(&right);
                if *is_function {
                    cstr!(*fn (cond_node + (*offset)) <= right)
                } else {
                    cstr!(*(cond_node + (*offset)) <= right)
                }
            }
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
                is_function,
            } => {
                let cond_node = self.term_to_integer(&cond_node);
                let left = self.term_to_integer(&left);
                if *is_function {
                    cstr!(left <= *fn (cond_node + (*offset)))
                } else {
                    cstr!(left <= *(cond_node + (*offset)))
                }
            }
        }
    }

    fn translate_constrained_terms(
        &self,
        constrained_terms: &ConstrainedTerms<T>,
    ) -> ConstrainedTerms<IntegerTerm> {
        let translated_terms = constrained_terms
            .terms
            .iter()
            .map(|t| self.term_to_integer(t))
            .collect();
        let translated_term_types = constrained_terms
            .term_types
            .iter()
            .map(|(t, tt)| (self.term_to_integer(t), *tt))
            .collect();
        let translated_constraints = constrained_terms
            .constraints
            .iter()
            .map(|c| self.translate_constraint(c))
            .collect();
        ConstrainedTerms {
            terms: translated_terms,
            term_types: translated_term_types,
            constraints: translated_constraints,
        }
    }
}

impl<T, F> GenericIdMap<T, F>
where
    T: Hash + Eq + Clone + Debug,
    F: Hash + Eq + Clone + Debug,
{
    fn new(terms: Vec<T>, functions: Vec<F>) -> Self {
        let term_mapping = GenericIdMap::<T>::from_terms(terms);
        let function_map = functions
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, f)| (f, i as IntegerTerm))
            .collect();
        Self {
            terms: term_mapping.terms,
            term_map: term_mapping.term_map,
            _functions: functions,
            function_map,
        }
    }

    fn function_to_integer(&self, function: &F) -> IntegerTerm {
        *self.function_map.get(function).unwrap_or_else(|| {
            panic!("Invalid lookup for function that was not passed in during initialization: {function:?}")
        })
    }

    fn _integer_to_function(&self, i: IntegerTerm) -> F {
        self._functions[i as usize].clone()
    }
}

pub struct GenericSolverSolution<S, T, F = ()> {
    mapping: GenericIdMap<T, F>,
    sub_solution: S,
}

impl<S, T, F> SolverSolution for GenericSolverSolution<S, T, F>
where
    T: Hash + Eq + Clone + Debug,
    S: SolverSolution<Term = IntegerTerm>,
{
    type Term = T;
    type TermSet = HashSet<T>;

    fn get(&self, node: &Self::Term) -> Self::TermSet {
        let sol = self.sub_solution.get(&self.mapping.term_to_integer(node));
        HashSet::from_iter(sol.iter().map(|i| self.mapping.integer_to_term(i)))
    }
}

fn edges_between<U>(
    edges: &mut Vec<HashMap<IntegerTerm, U>>,
    left: IntegerTerm,
    right: IntegerTerm,
) -> &mut U
where
    U: Default,
{
    edges[usize::try_from(left).expect("Could not convert to usize")]
        .entry(right)
        .or_default()
}

fn offset_term_vec_offsets(
    term: IntegerTerm,
    is_function: bool,
    term_types: &[TermType],
    offset: usize,
) -> Option<IntegerTerm> {
    let term_type = term_types[usize::try_from(term).unwrap()];
    match term_type {
        TermType::Basic if !is_function && offset == 0 => Some(term),
        TermType::Struct(allowed) if !is_function => {
            (offset <= allowed).then(|| term + u32::try_from(offset).unwrap())
        }
        TermType::Function(allowed) if is_function => {
            (offset <= allowed).then(|| term + u32::try_from(offset).unwrap())
        }
        _ => None,
    }
}

fn offset_term(
    term: IntegerTerm,
    allowed_offsets: &HashMap<IntegerTerm, usize>,
    offset: usize,
) -> Option<IntegerTerm> {
    if offset == 0 {
        Some(term)
    } else {
        allowed_offsets.get(&term).and_then(|&max_offset| {
            (offset <= max_offset)
                .then(|| term + u32::try_from(offset).expect("Could not convert from usize"))
        })
    }
}

fn offset_terms(
    terms: impl Iterator<Item = IntegerTerm>,
    allowed_offsets: &HashMap<IntegerTerm, usize>,
    offset: usize,
) -> Vec<IntegerTerm> {
    if offset == 0 {
        terms.collect()
    } else {
        terms
            .filter_map(|t| offset_term(t, allowed_offsets, offset))
            .collect()
    }
}
