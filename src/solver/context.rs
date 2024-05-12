use std::rc::Rc;

use arrayvec::ArrayVec;
use core::fmt;
use hashbrown::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ptr;

use super::{
    ConstrainedTerms, Constraint, DemandInput, GenericIdMap, IntegerTerm, Solver, SolverInput,
    TermType,
};

#[derive(Clone, Debug)]
pub struct FunctionInput<T> {
    pub fun_name: Rc<str>,
    pub return_terms: Vec<T>,
    pub parameter_terms: Vec<T>,
    pub constrained_terms: ConstrainedTerms<T>,
}

#[derive(Clone, Debug)]
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
    fn select_context(&self, current: &Self::Context, call_site: &CallSite) -> Self::Context;
    fn empty(&self) -> Self::Context;
}

pub type DemandContextSensitiveInput<T, C> = DemandInput<T, ContextSensitiveInput<T, C>>;

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

    fn select_context(&self, _: &Self::Context, _: &CallSite) -> Self::Context {
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
    /// Construct a `CallStringSelector` with `call_string_length = MAX`
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

    fn select_context(&self, current: &Self::Context, call_site: &CallSite) -> Self::Context {
        let mut context = current.clone();

        if self.call_string_length == 0 {
            return context;
        }

        if context.0.len() == self.call_string_length {
            context.0.remove(0);
        }
        context.0.push(call_site.clone());
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

pub trait ContextSensitiveSolver<T, C>: Solver<ContextSensitiveInput<T, C>> {}

impl<S, T, C> ContextSensitiveSolver<T, C> for S where S: Solver<ContextSensitiveInput<T, C>> {}

#[derive(Clone)]
pub enum TemplateTerm {
    Internal(u32),
    Global(u32),
}

pub struct FunctionTermInfo {
    pub pointer_node: IntegerTerm,
    pub term_type: TermType,
}

#[derive(Clone)]
pub struct FunctionTemplate {
    pub _fun_name: Rc<str>,
    pub start_index: u32,
    pub num_return_terms: u32,
    pub num_parameter_terms: u32,
    pub types: Vec<TermType>,
    pub constraints: Vec<Constraint<TemplateTerm>>,
}

pub struct ContextState<T, C: ContextSelector> {
    pub mapping: GenericIdMap<T>,
    pub templates: Vec<FunctionTemplate>,
    pub function_term_functions: HashMap<IntegerTerm, u32>,
    pub instantiated_contexts: Vec<HashMap<C::Context, IntegerTerm>>,
    pub context_selector: C,
    /// Maps from concrete (instantiated) terms to their abstract term.
    pub abstract_indices: Vec<IntegerTerm>,
}

pub fn function_to_template<T>(
    mapping: &GenericIdMap<T>,
    function: &FunctionInput<T>,
) -> (FunctionTemplate, FunctionTermInfo)
where
    T: Hash + Eq + Clone + Debug,
{
    let FunctionInput {
        fun_name,
        return_terms,
        parameter_terms,
        constrained_terms,
    } = function;

    let start_index = mapping.term_to_integer(&return_terms[0]);
    let num_return_terms = return_terms.len() as u32;
    let num_parameter_terms = parameter_terms.len() as u32;

    let mut types = vec![
        TermType::Basic;
        num_return_terms as usize
            + num_parameter_terms as usize
            + constrained_terms.terms.len()
    ];

    for (t, tt) in &constrained_terms.term_types {
        types[(mapping.term_to_integer(&t) - start_index) as usize] = *tt;
    }

    let function_terms_set: HashSet<_> = constrained_terms
        .terms
        .iter()
        .chain(return_terms)
        .chain(parameter_terms)
        .map(|t| mapping.term_to_integer(t))
        .collect();

    let mut constraints = vec![];
    let mut function_term_info = None;

    for c in &constrained_terms.constraints {
        if let Constraint::Inclusion { term, node } = &c {
            let abstract_index = mapping.term_to_integer(term);
            if function_terms_set.contains(&abstract_index) {
                let relative_index = abstract_index - start_index;
                let term_type = types[relative_index as usize];
                if matches!(term_type, TermType::Function(_, _)) {
                    if function_term_info.is_some() {
                        panic!("Multiple function terms found");
                    }
                    function_term_info = Some(FunctionTermInfo {
                        pointer_node: mapping.term_to_integer(node),
                        term_type,
                    });
                    continue;
                }
            }
        }
        constraints.push(c.map_terms(|t| {
            let index = mapping.term_to_integer(t);
            if function_terms_set.contains(&index) {
                TemplateTerm::Internal(index - start_index)
            } else {
                TemplateTerm::Global(index)
            }
        }));
    }

    let function_term = function_term_info.expect("No function term found");

    (
        FunctionTemplate {
            _fun_name: fun_name.clone(),
            start_index,
            num_return_terms,
            num_parameter_terms,
            types,
            constraints,
        },
        function_term,
    )
}

impl<T, C: ContextSelector> ContextState<T, C>
where
    T: Hash + Eq + Clone + Debug,
{
    pub fn from_context_input(input: ContextSensitiveInput<T, C>) -> (Self, Vec<FunctionTermInfo>) {
        let mapping = GenericIdMap::from_context_input(&input);

        let mut abstract_indices = (0..input.global.terms.len() as IntegerTerm).collect::<Vec<_>>();

        let mut templates = Vec::with_capacity(input.functions.len());
        let mut function_term_functions = HashMap::new();
        let instantiated_contexts = vec![HashMap::new(); input.functions.len()];

        let mut function_term_infos = Vec::with_capacity(input.functions.len());

        for (i, (template, function_term_info)) in input
            .functions
            .iter()
            .map(|f| function_to_template(&mapping, f))
            .enumerate()
        {
            let function_term_index = abstract_indices.len() as IntegerTerm;

            abstract_indices.push(template.start_index);

            templates.push(template);
            function_term_infos.push(function_term_info);
            function_term_functions.insert(function_term_index, i as IntegerTerm);
        }

        let state = Self {
            mapping,
            templates,
            function_term_functions,
            instantiated_contexts,
            context_selector: input.context_selector,
            abstract_indices,
        };

        (state, function_term_infos)
    }

    pub fn get_or_instantiate_function(
        &mut self,
        f_index: usize,
        context: C::Context,
    ) -> (IntegerTerm, Option<&FunctionTemplate>) {
        let template = &self.templates[f_index];
        if let Some(start_index) = self.instantiated_contexts[f_index].get(&context) {
            return (*start_index, None);
        }

        let instantiated_start_index = self.abstract_indices.len();
        let num_instantiated = template.types.len();
        self.abstract_indices
            .extend((0..num_instantiated).map(|i| template.start_index + i as u32));

        self.instantiated_contexts[f_index]
            .insert(context, instantiated_start_index as IntegerTerm);

        (instantiated_start_index as IntegerTerm, Some(template))
    }

    pub fn get_function_and_relative_index_from_term(
        &self,
        term: &T,
    ) -> (Option<IntegerTerm>, IntegerTerm) {
        let abstract_index = self.mapping.term_to_integer(term);

        self.get_function_and_relative_index_from_abstract_index(abstract_index)
    }

    pub fn get_function_and_relative_index_from_concrete_index(
        &self,
        concrete_index: IntegerTerm,
    ) -> (Option<IntegerTerm>, IntegerTerm) {
        let abstract_index = self.abstract_indices[concrete_index as usize];

        self.get_function_and_relative_index_from_abstract_index(abstract_index)
    }

    pub fn get_function_and_relative_index_from_abstract_index(
        &self,
        abstract_index: IntegerTerm,
    ) -> (Option<IntegerTerm>, IntegerTerm) {
        let fun_index = match self
            .templates
            .binary_search_by_key(&abstract_index, |t| t.start_index)
        {
            Ok(i) => Some(i),
            Err(i) => i.checked_sub(1),
        };

        // If global term
        match fun_index {
            Some(i) => (
                Some(i as IntegerTerm),
                abstract_index - self.templates[i].start_index,
            ),
            None => (None, abstract_index),
        }
    }

    pub fn context_of_concrete_index(&self, concrete_index: IntegerTerm) -> C::Context {
        if self.function_term_functions.contains_key(&concrete_index) {
            return self.context_selector.empty();
        }

        let (fun_index, relative_index) =
            self.get_function_and_relative_index_from_concrete_index(concrete_index);

        match fun_index {
            Some(i) => {
                let start_index = concrete_index - relative_index;
                self.instantiated_contexts[i as usize]
                    .iter()
                    .find(|(_, i)| **i == start_index)
                    .expect("there should be an instantiated context")
                    .0
                    .clone()
            }
            None => self.context_selector.empty(),
        }
    }

    pub fn concrete_to_input(&self, term: IntegerTerm) -> T {
        self.mapping
            .integer_to_term(self.abstract_indices[term as usize])
    }

    pub fn num_concrete_terms(&self) -> usize {
        self.abstract_indices.len()
    }

    pub fn term_to_concrete_global(&self, term: &T) -> Option<IntegerTerm> {
        let (fun_index, relative_index) = self.get_function_and_relative_index_from_term(term);
        match fun_index {
            Some(f) if relative_index == 0 => Some(self.templates[0].start_index + f),
            None => Some(relative_index),
            _ => None,
        }
    }
}
