use arrayvec::ArrayVec;
use core::fmt;
use hashbrown::{HashMap, HashSet};
use roaring::RoaringBitmap;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ptr;
use std::rc::Rc;

mod basic;
mod context_wave_prop;
mod shared_bitvec;
mod stats;
#[cfg(test)]
mod tests;
mod wave_prop;

pub use basic::{
    BasicHashSolver, BasicRoaringSolver, BasicSharedBitVecSolver, JustificationSolver,
};
// pub use bit_vec::BasicBitVecSolver;
pub use context_wave_prop::SharedBitVecContextWavePropagationSolver;
pub use stats::StatSolver;
pub use wave_prop::{
    HashWavePropagationSolver, RoaringWavePropagationSolver, SharedBitVecWavePropagationSolver,
};

use crate::visualizer::Node;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
        call_site: Option<CallSite>,
    },
    UnivCondSubsetRight {
        cond_node: T,
        left: T,
        offset: usize,
        call_site: Option<CallSite>,
    },
    CallDummy {
        cond_node: T,
        // TODO: do something with this?
        arguments: Vec<T>,
        result_node: T,
        call_site: CallSite,
    },
}

impl<T> Constraint<T> {
    pub fn map_terms<U, F>(&self, f: F) -> Constraint<U>
    where
        F: Fn(&T) -> U,
    {
        match self {
            Self::Inclusion { term, node } => Constraint::Inclusion {
                term: f(term),
                node: f(node),
            },
            Self::Subset {
                left,
                right,
                offset,
            } => Constraint::Subset {
                left: f(left),
                right: f(right),
                offset: *offset,
            },
            Self::UnivCondSubsetLeft {
                cond_node,
                right,
                offset,
                call_site,
            } => Constraint::UnivCondSubsetLeft {
                cond_node: f(cond_node),
                right: f(right),
                offset: *offset,
                call_site: call_site.clone(),
            },
            Self::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
                call_site,
            } => Constraint::UnivCondSubsetRight {
                cond_node: f(cond_node),
                left: f(left),
                offset: *offset,
                call_site: call_site.clone(),
            },
            Self::CallDummy {
                cond_node,
                arguments,
                result_node,
                call_site,
            } => Constraint::CallDummy {
                cond_node: f(cond_node),
                arguments: arguments.iter().map(&f).collect(),
                result_node: f(result_node),
                call_site: call_site.clone(),
            },
        }
    }
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
            call_site: None,
        }
    };
    ($left:tt <= *($cond_node:tt + $offset:tt)) => {
        $crate::solver::Constraint::UnivCondSubsetRight {
            cond_node: $cond_node,
            left: $left,
            offset: $offset,
            call_site: None,
        }
    };
    (*$cond_node:tt <= $right:tt) => {
        $crate::solver::Constraint::UnivCondSubsetLeft {
            cond_node: $cond_node,
            right: $right,
            offset: 0,
            call_site: None,
        }
    };
    ($left:tt <= *$cond_node:tt) => {
        $crate::solver::Constraint::UnivCondSubsetRight {
            cond_node: $cond_node,
            left: $left,
            offset: 0,
            call_site: None,
        }
    };
    ($call_site:tt : *fn ($cond_node:tt + $offset:tt) <= $right:tt) => {
        $crate::solver::Constraint::UnivCondSubsetLeft {
            cond_node: $cond_node,
            right: $right,
            offset: $offset,
            call_site: Some($call_site),
        }
    };
    ($call_site:tt : $left:tt <= *fn ($cond_node:tt + $offset:tt)) => {
        $crate::solver::Constraint::UnivCondSubsetRight {
            cond_node: $cond_node,
            left: $left,
            offset: $offset,
            call_site: Some($call_site),
        }
    };
}

pub type IntegerTerm = u32;

#[derive(Clone, Debug)]
enum UnivCond<T: Clone> {
    SubsetLeft { right: T, offset: usize },
    SubsetRight { left: T, offset: usize },
}

pub trait TermSetTrait: Clone + Default + PartialEq {
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

#[derive(Debug, Clone)]
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

#[derive(Debug)]
pub struct FunctionInput<T> {
    pub fun_name: Rc<str>,
    pub return_and_parameter_terms: Vec<T>,
    pub constrained_terms: ConstrainedTerms<T>,
}

#[derive(Debug)]
pub struct ContextSensitiveInput<T, C> {
    pub global: ConstrainedTerms<T>,
    pub functions: Vec<FunctionInput<T>>,
    pub entrypoints: Vec<usize>,
    pub context_selector: C,
}

impl<T, C> SolverInput for ContextSensitiveInput<T, C> {
    type Term = T;
}

pub trait ContextSelector: Debug {
    type Context: Clone + Debug + PartialEq + Eq + Hash;
    fn select_context(&self, current: &Self::Context, call_site: CallSite) -> Self::Context;
    fn empty(&self) -> Self::Context;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ContextInsensitiveContext;

impl Display for ContextInsensitiveContext {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "()")
    }
}

#[derive(Clone, Debug)]
pub struct ContextInsensitiveSelector;

impl ContextSelector for ContextInsensitiveSelector {
    type Context = ContextInsensitiveContext;

    fn select_context(&self, _: &Self::Context, _: CallSite) -> Self::Context {
        ContextInsensitiveContext
    }

    fn empty(&self) -> Self::Context {
        ContextInsensitiveContext
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct CallSiteInner {
    pub desc: String,
    pub func_type_index: u32,
}

#[derive(Clone, Eq, Debug)]
pub struct CallSite(pub Rc<CallSiteInner>);

impl CallSite {
    pub fn new(desc: String, func_type: u32) -> Self {
        CallSite(Rc::new(CallSiteInner {
            desc,
            func_type_index: func_type,
        }))
    }
}

impl PartialEq for CallSite {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Hash for CallSite {
    fn hash<H: Hasher>(&self, state: &mut H) {
        ptr::hash(Rc::as_ptr(&self.0), state);
    }
}

impl Display for CallSite {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", &self.0.desc)
    }
}

#[derive(Clone, Debug)]
pub struct CallStringSelector<const MAX: usize> {
    call_string_length: usize,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct CallStringContext<const MAX: usize>(ArrayVec<CallSite, MAX>);

impl<const MAX: usize> CallStringSelector<MAX> {
    /// Construct a `CallStringSelector` with `call_string_length = 0`
    pub fn new() -> Self {
        Self::with_call_string_length(MAX)
    }

    pub fn with_call_string_length(length: usize) -> Self {
        if length as usize > MAX {
            panic!("Length should be less than or equal to MAX");
        }
        Self {
            call_string_length: length,
        }
    }
}

impl<const K: usize> ContextSelector for CallStringSelector<K> {
    type Context = CallStringContext<K>;

    fn select_context(&self, current: &Self::Context, call_site: CallSite) -> Self::Context {
        let mut context = current.clone();

        if self.call_string_length == 0 {
            return context;
        }

        if context.0.len() == self.call_string_length {
            context.0.remove(0);
        }
        context.0.push(call_site);
        context
    }

    fn empty(&self) -> Self::Context {
        CallStringContext(ArrayVec::new())
    }
}

impl<const K: usize> Display for CallStringContext<K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let string = self
            .0
            .iter()
            .map(CallSite::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(f, "[{string}]",)
    }
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
    Function(usize, u32),
}

impl TermType {
    pub fn into_offset(self) -> usize {
        match self {
            TermType::Basic => 0,
            TermType::Struct(offset) | TermType::Function(offset, _) => offset,
        }
    }

    pub fn is_basic(self) -> bool {
        self == TermType::Basic
    }
}

pub trait ContextSensitiveSolver<T, C>: Solver<ContextSensitiveInput<T, C>> {}

impl<S, T, C> ContextSensitiveSolver<T, C> for S where S: Solver<ContextSensitiveInput<T, C>> {}

// pub trait ContextSensitiveExt {
//     fn with_flat_context(self) -> WithFlatContext<Self>;
//     fn as_context_insensitive(self) -> AsContextInsensitive<Self>;
// }

// impl<S, T, C> ContextSensitiveExt for S
// where
//     S: ContextSensitiveSolver<T, C> + Sized,
// {
//     fn with_flat_context(self) -> WithFlatContext<Self> {
//         WithFlatContext(self)
//     }

//     fn as_context_insensitive(self) -> AsContextInsensitive<Self> {
//         AsContextInsensitive(self)
//     }
// }

pub trait ContextInsensitiveSolver<T>: Solver<ContextInsensitiveInput<T>> {
    type ContextSensitiveSolver<C>: ContextSensitiveSolver<T, C>;

    fn as_context_sensitive<C>(self) -> Self::ContextSensitiveSolver<C>;
}

impl<S, T> ContextInsensitiveSolver<T> for S
where
    S: Solver<ContextInsensitiveInput<T>> + Sized,
{
    type ContextSensitiveSolver<C> = AsContextSensitive<S, C>;

    fn as_context_sensitive<C>(self) -> Self::ContextSensitiveSolver<C> {
        AsContextSensitive(self, PhantomData)
    }
}

#[derive(Clone)]
pub struct AsContextSensitive<S, C>(pub S, PhantomData<C>);

impl<S, T, C> Solver<ContextSensitiveInput<T, C>> for AsContextSensitive<S, C>
where
    S: Solver<ContextInsensitiveInput<T>>,
{
    type Solution = S::Solution;

    fn solve(self, mut input: ContextSensitiveInput<T, C>) -> Self::Solution {
        for f in input.functions.into_iter() {
            input.global.terms.extend(f.return_and_parameter_terms);
            input.global.combine(f.constrained_terms);
        }
        self.0.solve(input.global)
    }
}

#[derive(Clone)]
pub struct WithFlatContext<S>(pub S);

impl<S, T, C> Solver<ContextSensitiveInput<T, C>> for WithFlatContext<S>
where
    S: Solver<ContextSensitiveInput<T, ContextInsensitiveSelector>>,
{
    type Solution = S::Solution;

    fn solve(self, input: ContextSensitiveInput<T, C>) -> Self::Solution {
        self.0.solve(ContextSensitiveInput {
            global: input.global,
            entrypoints: (0..input.functions.len()).collect(),
            functions: input.functions,
            context_selector: ContextInsensitiveSelector,
        })
    }
}

#[derive(Clone)]
pub struct AsContextInsensitive<S>(pub S);

impl<S, T> Solver<ContextInsensitiveInput<T>> for AsContextInsensitive<S>
where
    S: ContextSensitiveSolver<T, ContextInsensitiveSelector>,
{
    type Solution = S::Solution;

    fn solve(self, input: ContextInsensitiveInput<T>) -> Self::Solution {
        self.0.solve(ContextSensitiveInput {
            global: input,
            functions: vec![],
            entrypoints: vec![],
            context_selector: ContextInsensitiveSelector,
        })
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
        let mapping = GenericIdMap::new(terms);

        let translated = mapping.translate_constrained_terms(&constrained_terms);
        let sub_solution = self.sub_solver.solve(translated);
        GenericSolverSolution {
            mapping,
            sub_solution,
        }
    }
}

impl<S, T, C> Solver<ContextSensitiveInput<T, C>> for GenericSolver<S>
where
    T: Hash + Eq + Clone + Debug,
    S: Solver<ContextSensitiveInput<IntegerTerm, C>>,
    C: ContextSelector,
{
    type Solution = GenericSolverSolution<S::Solution, T>;

    fn solve(self, input: ContextSensitiveInput<T, C>) -> Self::Solution {
        let terms = input
            .global
            .terms
            .iter()
            .chain(input.functions.iter().flat_map(|t| {
                t.return_and_parameter_terms
                    .iter()
                    .chain(&t.constrained_terms.terms)
            }))
            .cloned()
            .collect();
        let mapping = GenericIdMap::new(terms);

        let translated_entry = mapping.translate_constrained_terms(&input.global);
        let translated_functions = input
            .functions
            .iter()
            .map(|f| mapping.translate_function(&f))
            .collect();
        let translated_input = ContextSensitiveInput {
            global: translated_entry,
            functions: translated_functions,
            entrypoints: input.entrypoints,
            context_selector: input.context_selector,
        };
        let sub_solution = self.sub_solver.solve(translated_input);
        GenericSolverSolution {
            mapping,
            sub_solution,
        }
    }
}

#[derive(Clone)]
pub struct GenericIdMap<T> {
    terms: Vec<T>,
    term_map: HashMap<T, IntegerTerm>,
}

impl<T> GenericIdMap<T>
where
    T: Hash + Eq + Clone + Debug,
{
    fn new(terms: Vec<T>) -> Self {
        let term_map = terms
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, t)| (t, i as IntegerTerm))
            .collect();
        Self { terms, term_map }
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
                call_site,
            } => {
                let cond_node = self.term_to_integer(&cond_node);
                let right = self.term_to_integer(&right);
                if let Some(c) = call_site.clone() {
                    cstr!(c: *fn (cond_node + (*offset)) <= right)
                } else {
                    cstr!(*(cond_node + (*offset)) <= right)
                }
            }
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
                call_site,
            } => {
                let cond_node = self.term_to_integer(&cond_node);
                let left = self.term_to_integer(&left);
                if let Some(c) = call_site.clone() {
                    cstr!(c: left <= *fn (cond_node + (*offset)))
                } else {
                    cstr!(left <= *(cond_node + (*offset)))
                }
            }
            Constraint::CallDummy {
                cond_node,
                arguments,
                result_node,
                call_site,
            } => {
                let cond_node = self.term_to_integer(&cond_node);
                let arguments = arguments.iter().map(|a| self.term_to_integer(a)).collect();
                let result_node = self.term_to_integer(&result_node);
                Constraint::CallDummy {
                    cond_node,
                    arguments,
                    result_node,
                    call_site: call_site.clone(),
                }
            }
        }
    }

    fn translate_function(&self, function: &FunctionInput<T>) -> FunctionInput<IntegerTerm> {
        FunctionInput {
            fun_name: function.fun_name.clone(),
            return_and_parameter_terms: function
                .return_and_parameter_terms
                .iter()
                .map(|t| self.term_to_integer(t))
                .collect(),
            constrained_terms: self.translate_constrained_terms(&function.constrained_terms),
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

pub struct GenericSolverSolution<S, T> {
    mapping: GenericIdMap<T>,
    sub_solution: S,
}

impl<S, T> SolverSolution for GenericSolverSolution<S, T>
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
        // TODO: Filter on function type
        TermType::Function(allowed, _) if is_function => {
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

#[derive(Clone, Default)]
pub struct Offsets {
    zero: bool,
    offsets: Vec<usize>,
}

impl Offsets {
    pub fn contains(&self, offset: usize) -> bool {
        if offset == 0 {
            return self.zero;
        }
        return self.offsets.contains(&offset);
    }

    pub fn insert(&mut self, offset: usize) -> bool {
        if offset == 0 {
            if !self.zero {
                self.zero = true;
                true
            } else {
                false
            }
        } else {
            match self.offsets.binary_search(&offset) {
                Ok(_) => false,
                Err(i) => {
                    self.offsets.insert(i, offset);
                    true
                }
            }
        }
    }

    pub fn union_assign(&mut self, other: &Self) {
        self.zero = other.zero;
        for offset in &other.offsets {
            self.insert(*offset);
        }
    }

    pub fn len(&self) -> usize {
        self.zero as usize + self.offsets.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.zero
            .then_some(0)
            .into_iter()
            .chain(self.offsets.iter().copied())
    }
}
