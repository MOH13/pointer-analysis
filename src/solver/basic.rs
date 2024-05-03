use std::collections::VecDeque;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::marker::PhantomData;

use hashbrown::{HashMap, HashSet};
use roaring::RoaringBitmap;

use super::shared_bitvec::SharedBitVec;
use super::{
    edges_between, CallSite, Constraint, ContextInsensitiveInput, GenericSolverSolution,
    IntegerTerm, Offsets, Solver, SolverExt, SolverSolution, TermSetTrait, TermType,
};
use crate::visualizer::{Edge, EdgeKind, Graph, Node, OffsetWeight};

static mut TOTAL: usize = 0;
static mut INSERTED: usize = 0;

#[derive(Clone, Debug)]
enum UnivCond<T: Clone> {
    SubsetLeft {
        right: T,
        offset: usize,
        call_site: Option<CallSite>,
    },
    SubsetRight {
        left: T,
        offset: usize,
        call_site: Option<CallSite>,
    },
}

pub struct BasicSolver<T>(PhantomData<T>);

impl<T> BasicSolver<T> {
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

#[derive(Clone)]
pub struct BasicSolverState<T: Clone, U> {
    worklist: VecDeque<(T, T)>,
    sols: Vec<U>,
    edges: Vec<HashMap<T, Offsets>>,
    conds: Vec<Vec<UnivCond<T>>>,
    term_types: Vec<TermType>,
}

macro_rules! add_token {
    ($solver:expr, $term:expr, $node:expr) => {
        unsafe {
            TOTAL += 1;
        }
        if $solver.sols[$node as usize].insert($term) {
            $solver.worklist.push_back(($term, $node));
            unsafe {
                INSERTED += 1;
            }
        }
    };
}

impl<T: TermSetTrait<Term = IntegerTerm>> BasicSolverState<IntegerTerm, T> {
    pub fn new() -> Self {
        Self {
            worklist: VecDeque::new(),
            sols: vec![],
            edges: vec![],
            conds: vec![],
            term_types: vec![],
        }
    }

    fn try_offset_term(
        &self,
        term: IntegerTerm,
        call_site: Option<&CallSite>,
        offset: usize,
    ) -> Option<IntegerTerm> {
        let term_type = self.term_types[term as usize];
        if call_site.is_none() && offset == 0 {
            return Some(term);
        }
        match term_type {
            TermType::Struct(allowed) if call_site.is_none() => {
                (offset <= allowed).then(|| term + offset as u32)
            }
            TermType::Function(allowed, func_type) => {
                let Some(call_site) = call_site else {
                    return None;
                };
                if func_type != call_site.0.func_type_index {
                    return None;
                }
                (offset <= allowed).then(|| term + offset as u32)
            }
            _ => None,
        }
    }

    fn propagate(&mut self) {
        while let Some((term, node)) = self.worklist.pop_front() {
            for cond in self.conds[node as usize].clone() {
                match cond {
                    UnivCond::SubsetLeft {
                        right,
                        offset,
                        call_site,
                    } => {
                        if let Some(t) = self.try_offset_term(term, call_site.as_ref(), offset) {
                            self.add_edge(t, right, 0)
                        }
                    }
                    UnivCond::SubsetRight {
                        left,
                        offset,
                        call_site,
                    } => {
                        if let Some(t) = self.try_offset_term(term, call_site.as_ref(), offset) {
                            self.add_edge(left, t, 0)
                        }
                    }
                }
            }

            for (&n2, edges) in &self.edges[node as usize] {
                for offset in edges.iter() {
                    if let Some(t) = self.try_offset_term(term, None, offset as usize) {
                        add_token!(self, t, n2);
                    }
                }
            }
        }
    }

    fn add_edge(&mut self, left: IntegerTerm, right: IntegerTerm, offset: usize) {
        let edges = edges_between(&mut self.edges, left, right);
        if edges.insert(offset) {
            for term in self.sols[left as usize].clone().iter() {
                if let Some(t) = self.try_offset_term(term, None, offset) {
                    add_token!(self, t, right);
                }
            }
        }
    }

    fn add_constraint(&mut self, c: Constraint<IntegerTerm>) {
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
                call_site,
            } => {
                self.conds[cond_node as usize].push(UnivCond::SubsetLeft {
                    right,
                    offset,
                    call_site: call_site.clone(),
                });
                for term in self.sols[cond_node as usize].clone().iter() {
                    if let Some(t) = self.try_offset_term(term, call_site.as_ref(), offset) {
                        self.add_edge(t, right, 0);
                    }
                }
            }
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
                call_site,
            } => {
                self.conds[cond_node as usize].push(UnivCond::SubsetRight {
                    left,
                    offset,
                    call_site: call_site.clone(),
                });
                for term in self.sols[cond_node as usize].clone().iter() {
                    if let Some(t) = self.try_offset_term(term, call_site.as_ref(), offset) {
                        self.add_edge(left, t, 0);
                    }
                }
            }
            Constraint::CallDummy { .. } => {}
        };
        self.propagate();
    }

    fn solve(&mut self, input: ContextInsensitiveInput<IntegerTerm>) {
        self.sols = vec![T::new(); input.terms.len()];
        self.edges = vec![HashMap::new(); input.terms.len()];
        self.conds = vec![vec![]; input.terms.len()];
        self.term_types = vec![TermType::Basic; input.terms.len()];
        for (t, ty) in input.term_types {
            self.term_types[t as usize] = ty;
        }

        for c in input.constraints {
            self.add_constraint(c);
        }

        println!("Total: {} Inserted: {}", unsafe { TOTAL }, unsafe {
            INSERTED
        });
    }
}

impl<T: TermSetTrait<Term = IntegerTerm>> SolverExt for BasicSolver<T> {}

impl<T: TermSetTrait<Term = IntegerTerm>> Solver<ContextInsensitiveInput<IntegerTerm>>
    for BasicSolver<T>
{
    type Solution = BasicSolverState<IntegerTerm, T>;

    fn solve(&self, input: ContextInsensitiveInput<IntegerTerm>) -> Self::Solution {
        let mut state = BasicSolverState::new();
        state.solve(input);
        state
    }
}

impl<T: TermSetTrait<Term = IntegerTerm>> SolverSolution for BasicSolverState<IntegerTerm, T> {
    type Term = IntegerTerm;

    type TermSet = T;

    fn get(&self, node: &Self::Term) -> Self::TermSet {
        self.sols[*node as usize].clone()
    }
}

pub type BasicHashSolver = BasicSolver<HashSet<IntegerTerm>>;
pub type BasicRoaringSolver = BasicSolver<RoaringBitmap>;
pub type BasicSharedBitVecSolver = BasicSolver<SharedBitVec>;

impl<T, S> Graph for GenericSolverSolution<BasicSolverState<IntegerTerm, S>, T>
where
    T: Display + Debug + Clone + PartialEq + Eq + Hash,
    S: TermSetTrait<Term = IntegerTerm>,
{
    type Node = T;
    type Weight = OffsetWeight;

    fn nodes(&self) -> Vec<Node<Self::Node>> {
        self.mapping.terms_as_nodes()
    }

    fn edges(&self) -> Vec<Edge<Self::Node, Self::Weight>> {
        let mut edges = vec![];

        for (from, outgoing) in self.sub_solution.edges.iter().enumerate() {
            let from = Node {
                inner: self.mapping.integer_to_term(from as IntegerTerm),
                id: from,
            };
            for (&to, weights) in outgoing {
                let to = Node {
                    inner: self.mapping.integer_to_term(to as IntegerTerm),
                    id: to as usize,
                };
                for weight in weights.iter() {
                    let edge = Edge {
                        from: from.clone(),
                        to: to.clone(),
                        weight: OffsetWeight(weight as u32),
                        kind: EdgeKind::Subset,
                    };
                    edges.push(edge);
                }
            }
        }

        // for from in 0..self.mapping.terms.len() {
        //     let from_node = Node {
        //         inner: self.mapping.integer_to_term(from as IntegerTerm),
        //         id: from,
        //     };
        //     for to in self.sub_solution.get(&(from as IntegerTerm)).iter() {
        //         let to_node = Node {
        //             inner: self.mapping.integer_to_term(to),
        //             id: to as usize,
        //         };
        //         let edge = Edge {
        //             from: from_node.clone(),
        //             to: to_node.clone(),
        //             weight: OffsetWeight(0),
        //             kind: EdgeKind::Inclusion,
        //         };
        //         edges.push(edge);
        //     }
        // }

        edges
    }
}

pub struct JustificationSolver<T>(PhantomData<T>);

impl<T> JustificationSolver<T> {
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

impl<T> SolverExt for JustificationSolver<T> {}

impl<T> Solver<ContextInsensitiveInput<T>> for JustificationSolver<T>
where
    T: Clone + Debug + Display + Eq + Hash,
{
    type Solution = Justifier<T>;

    fn solve(&self, input: ContextInsensitiveInput<T>) -> Self::Solution {
        let solver = BasicSolver::new().as_generic();
        let solution = solver.solve(input.clone());
        let constraints: HashSet<_> = input
            .constraints
            .iter()
            .map(|c| c.map_terms(|t| solution.mapping.term_to_integer(t)))
            .collect();
        let mut loads = HashMap::new();
        let mut stores = HashMap::new();
        for c in &constraints {
            match c {
                Constraint::UnivCondSubsetLeft {
                    cond_node,
                    right,
                    offset,
                    call_site,
                } => {
                    loads.entry(*right).or_insert_with(Vec::new).push((
                        *cond_node,
                        *offset,
                        call_site.clone(),
                    ));
                }
                Constraint::UnivCondSubsetRight {
                    cond_node,
                    left,
                    offset,
                    call_site,
                } => {
                    stores.entry(*left).or_insert_with(Vec::new).push((
                        *cond_node,
                        *offset,
                        call_site.clone(),
                    ));
                }
                _ => {}
            }
        }
        let mut rev_edges = vec![HashMap::<IntegerTerm, Offsets>::new(); input.terms.len()];
        for (from, outgoing) in solution.sub_solution.edges.iter().enumerate() {
            for (&to, weights) in outgoing {
                rev_edges[to as usize]
                    .entry(from as IntegerTerm)
                    .or_default()
                    .union_assign(weights);
            }
        }
        Justifier {
            constraints,
            solution,
            rev_edges,
            loads,
            stores,
        }
    }
}

pub struct Justifier<T> {
    solution: GenericSolverSolution<BasicSolverState<IntegerTerm, HashSet<IntegerTerm>>, T>,
    rev_edges: Vec<HashMap<IntegerTerm, Offsets>>,
    constraints: HashSet<Constraint<IntegerTerm>>,
    loads: HashMap<IntegerTerm, Vec<(IntegerTerm, usize, Option<CallSite>)>>,
    stores: HashMap<IntegerTerm, Vec<(IntegerTerm, usize, Option<CallSite>)>>,
}

impl<T> Justifier<T>
where
    T: Clone + Debug + Display + Eq + Hash,
{
    pub fn justify(&self, node: T, term: T) {
        if !self.solution.get(&node).contains(&term) {
            println!("Term {} not in node {}", term, node);
            return;
        }
        let int_node = self.to_int(&node);
        let int_term = self.to_int(&term);
        let mut queue = VecDeque::new();
        let mut visited = HashSet::new();
        let mut parents = HashMap::new();
        queue.push_back((int_node, int_term));
        visited.insert((int_node, int_term));

        let mut dest = None;
        while let Some((v, t)) = queue.pop_front() {
            if self
                .constraints
                .contains(&Constraint::Inclusion { term: t, node: v })
            {
                dest = Some((v, t));
                break;
            }

            for (from, weights) in &self.rev_edges[v as usize] {
                for w in weights.iter() {
                    let Some(from_t) = t.checked_sub(w as u32) else {
                        continue;
                    };
                    let allowed =
                        self.solution.sub_solution.try_offset_term(from_t, None, w) == Some(t);
                    if !allowed
                        || visited.contains(&(*from, from_t))
                        || !self.solution.sub_solution.sols[*from as usize].contains(&from_t)
                    {
                        continue;
                    }
                    visited.insert((*from, from_t));
                    parents.insert((*from, from_t), (v, t));
                    queue.push_back((*from, from_t));
                }
            }
        }
        let Some((mut from, mut from_t)) = dest else {
            println!("Could not justify term {term} in node {node}");
            return;
        };
        println!(
            "\n{} <- &{}",
            self.display_int(from),
            self.display_int(from_t)
        );
        let mut path = vec![(from, from_t)];
        while (from, from_t) != (int_node, int_term) {
            let (to, to_t) = parents[&(from, from_t)];
            path.push((to, to_t));
            from = to;
            from_t = to_t;
        }
        if path.len() == 1 {
            return;
        }

        let start = path[0].0;
        print!("{}", self.display_int(start));
        for edge in path.windows(2) {
            let (_, from_t) = edge[0];
            let (to, to_t) = edge[1];
            let w = to_t - from_t;
            if w > 0 {
                print!(" -{w}> {}", self.display_int(to));
            } else {
                print!(" -> {}", self.display_int(to));
            }
        }
        println!("\n");
        for edge in path.windows(2) {
            let (from, from_t) = edge[0];
            let (to, to_t) = edge[1];
            let w = to_t - from_t;
            if !self.justify_edge(from, to, w as usize) {
                return;
            }
            println!();
        }
    }

    fn justify_edge(&self, from: IntegerTerm, to: IntegerTerm, offset: usize) -> bool {
        if self.constraints.contains(&Constraint::Subset {
            left: from,
            right: to,
            offset,
        }) {
            print!("assign:\t");
            if offset > 0 {
                println!(
                    "{} <{offset}- {}",
                    self.display_int(to),
                    self.display_int(from)
                );
            } else {
                println!("{} <- {}", self.display_int(to), self.display_int(from));
            }
            return true;
        }

        if offset > 0 {
            println!(
                "Could not justify edge from {} to {} with offset {offset}",
                self.display_int(from),
                self.display_int(to)
            );
            return false;
        }

        if let Some(loads) = self.loads.get(&to) {
            for (cond_node, offset, call_site) in loads {
                let Some(pred) = from.checked_sub(*offset as u32) else {
                    continue;
                };
                if self
                    .solution
                    .sub_solution
                    .try_offset_term(pred, call_site.as_ref(), *offset)
                    == Some(from)
                    || !self.solution.sub_solution.sols[*cond_node as usize].contains(&pred)
                {
                    continue;
                }
                println!("load:");
                let premise1 = if let Some(call_site) = call_site {
                    format!(
                        "{} <{offset}- *{} ({})",
                        self.display_int(to),
                        self.display_int(*cond_node),
                        call_site
                    )
                } else if *offset > 0 {
                    format!(
                        "{} <{offset}- *{}",
                        self.display_int(to),
                        self.display_int(*cond_node),
                    )
                } else {
                    format!(
                        "{} <- *{}",
                        self.display_int(to),
                        self.display_int(*cond_node)
                    )
                };
                let premise2 = format!(
                    "{} ∈ [[{}]]",
                    self.display_int(pred),
                    self.display_int(*cond_node)
                );
                println!("\t{premise1}");
                println!("\t{premise2}");
                println!("\t{}", "─".repeat(premise1.len().max(premise2.len())));
                println!("\t{} -> {}", self.display_int(from), self.display_int(to));
                return true;
            }
        }

        if let Some(stores) = self.stores.get(&from) {
            for (cond_node, offset, call_site) in stores {
                let Some(pred) = to.checked_sub(*offset as u32) else {
                    continue;
                };
                if self
                    .solution
                    .sub_solution
                    .try_offset_term(pred, call_site.as_ref(), *offset)
                    == Some(to)
                    || !self.solution.sub_solution.sols[*cond_node as usize].contains(&pred)
                {
                    continue;
                }
                println!("store:");
                let premise1 = if let Some(call_site) = call_site {
                    format!(
                        "*{} <{offset}- {} ({})",
                        self.display_int(*cond_node),
                        self.display_int(from),
                        call_site
                    )
                } else if *offset > 0 {
                    format!(
                        "*{} <{offset}- {}",
                        self.display_int(*cond_node),
                        self.display_int(from),
                    )
                } else {
                    format!(
                        "*{} <- {}",
                        self.display_int(*cond_node),
                        self.display_int(from)
                    )
                };
                let premise2 = format!(
                    "{} ∈ [[{}]]",
                    self.display_int(pred),
                    self.display_int(*cond_node)
                );
                println!("\t{premise1}");
                println!("\t{premise2}");
                println!("\t{}", "─".repeat(premise1.len().max(premise2.len())));
                println!("\t{} -> {}", self.display_int(from), self.display_int(to));
                return true;
            }
        }

        println!(
            "Could not justify edge from {} to {} with offset {offset}",
            self.display_int(from),
            self.display_int(to),
        );
        return false;
    }

    fn to_int(&self, t: &T) -> IntegerTerm {
        self.solution.mapping.term_to_integer(t)
    }

    fn display_int(&self, t: IntegerTerm) -> T {
        self.solution.mapping.integer_to_term(t)
    }
}

impl<T> SolverSolution for Justifier<T>
where
    T: Clone + Debug + Display + Eq + Hash,
{
    type Term = T;
    type TermSet = HashSet<T>;

    fn get(&self, node: &Self::Term) -> Self::TermSet {
        self.solution.get(node)
    }
}
