use std::collections::VecDeque;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::marker::PhantomData;

use hashbrown::{HashMap, HashSet};
use roaring::RoaringBitmap;

use super::shared_bitvec::SharedBitVec;
use super::{
    edges_between, offset_term, offset_terms, BetterBitVec, CallSite, Constraint,
    ContextInsensitiveInput, GenericSolverSolution, IntegerTerm, Solver, SolverSolution,
    TermSetTrait, UnivCond,
};
use crate::visualizer::{Edge, EdgeKind, Graph, Node, OffsetWeight};

#[derive(Clone)]
pub struct BasicSolver<T: Clone, U> {
    worklist: VecDeque<(T, T)>,
    sols: Vec<U>,
    edges: Vec<HashMap<T, U>>,
    conds: Vec<Vec<UnivCond<T>>>,
    allowed_offsets: HashMap<T, usize>,
}

macro_rules! add_token {
    ($solver:expr, $term:expr, $node:expr) => {
        if $solver.sols[$node as usize].insert($term) {
            $solver.worklist.push_back(($term, $node));
        }
    };
}

impl<T: TermSetTrait<Term = IntegerTerm>> BasicSolver<IntegerTerm, T> {
    pub fn new() -> Self {
        Self {
            worklist: VecDeque::new(),
            sols: vec![],
            edges: vec![],
            conds: vec![],
            allowed_offsets: HashMap::new(),
        }
    }

    fn propagate(&mut self) {
        while let Some((term, node)) = self.worklist.pop_front() {
            for cond in &self.conds[node as usize].clone() {
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

            for (&n2, edges) in &self.edges[node as usize] {
                for offset in edges.iter() {
                    if let Some(t) = offset_term(term, &self.allowed_offsets, offset as usize) {
                        add_token!(self, t, n2);
                    }
                }
            }
        }
    }

    fn add_edge(&mut self, left: IntegerTerm, right: IntegerTerm, offset: usize) {
        let edges = edges_between(&mut self.edges, left, right);
        if edges.insert(offset as IntegerTerm) {
            for t in offset_terms(
                self.sols[left as usize].iter(),
                &self.allowed_offsets,
                offset,
            ) {
                add_token!(self, t, right);
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
                ..// TODO: functions
            } => {
                self.conds[cond_node as usize].push(UnivCond::SubsetLeft { right, offset });
                let terms = offset_terms(
                    self.sols[cond_node as usize].iter(),
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
                ..// TODO: functions
            } => {
                self.conds[cond_node as usize].push(UnivCond::SubsetRight { left, offset });
                let terms = offset_terms(
                    self.sols[cond_node as usize].iter(),
                    &self.allowed_offsets,
                    offset,
                );

                for t in terms {
                    self.add_edge(left, t, 0);
                }
            }
            Constraint::CallDummy { .. } => {}
        };
        self.propagate();
    }
}

impl<T: TermSetTrait<Term = IntegerTerm>> Solver<ContextInsensitiveInput<IntegerTerm>>
    for BasicSolver<IntegerTerm, T>
{
    type Solution = Self;

    fn solve(mut self, input: ContextInsensitiveInput<IntegerTerm>) -> Self::Solution {
        self.sols = vec![T::new(); input.terms.len()];
        self.edges = vec![HashMap::new(); input.terms.len()];
        self.conds = vec![vec![]; input.terms.len()];
        self.allowed_offsets = input
            .term_types
            .into_iter()
            .map(|(t, ty)| (t as IntegerTerm, ty.into_offset()))
            .collect();

        for c in input.constraints {
            self.add_constraint(c);
        }

        self
    }
}

impl<T: TermSetTrait<Term = IntegerTerm>> SolverSolution for BasicSolver<IntegerTerm, T> {
    type Term = IntegerTerm;

    type TermSet = T;

    fn get(&self, node: &Self::Term) -> Self::TermSet {
        self.sols[*node as usize].clone()
    }
}

pub type BasicHashSolver = BasicSolver<IntegerTerm, HashSet<IntegerTerm>>;
pub type BasicRoaringSolver = BasicSolver<IntegerTerm, RoaringBitmap>;
pub type BasicBetterBitVecSolver = BasicSolver<IntegerTerm, BetterBitVec>;
pub type BasicSharedBitVecSolver = BasicSolver<IntegerTerm, SharedBitVec>;

impl<T, S> Graph for GenericSolverSolution<BasicSolver<IntegerTerm, S>, T>
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
                        weight: OffsetWeight(weight),
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

impl<T> Solver<ContextInsensitiveInput<T>> for JustificationSolver<T>
where
    T: Clone + Debug + Display + Eq + Hash,
{
    type Solution = Justifier<T>;

    fn solve(self, input: ContextInsensitiveInput<T>) -> Self::Solution {
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
        let mut rev_edges = vec![HashMap::new(); input.terms.len()];
        for (from, outgoing) in solution.sub_solution.edges.iter().enumerate() {
            for (&to, weights) in outgoing {
                rev_edges[to as usize]
                    .entry(from as IntegerTerm)
                    .or_insert_with(HashSet::new)
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
    solution: GenericSolverSolution<BasicSolver<IntegerTerm, HashSet<IntegerTerm>>, T>,
    rev_edges: Vec<HashMap<IntegerTerm, HashSet<IntegerTerm>>>,
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
            // println!(
            //     "Looking for {} in {}",
            //     self.display_int(t),
            //     self.display_int(v)
            // );
            if self
                .constraints
                .contains(&Constraint::Inclusion { term: t, node: v })
            {
                dest = Some((v, t));
                break;
            }

            // println!(
            //     "incomming: {:?}",
            //     self.rev_edges[v as usize]
            //         .iter()
            //         .map(|(u, _)| self.display_int(*u))
            //         .collect::<Vec<_>>()
            // );
            for (from, weights) in &self.rev_edges[v as usize] {
                for &w in weights.iter() {
                    let Some(from_t) = t.checked_sub(w) else {
                        continue;
                    };
                    let allowed = *self
                        .solution
                        .sub_solution
                        .allowed_offsets
                        .get(&from_t)
                        .unwrap_or(&0);
                    if visited.contains(&(*from, from_t))
                        || allowed < w as usize
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
                if *self
                    .solution
                    .sub_solution
                    .allowed_offsets
                    .get(&pred)
                    .unwrap_or(&0)
                    < *offset
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
                if *self
                    .solution
                    .sub_solution
                    .allowed_offsets
                    .get(&pred)
                    .unwrap_or(&0)
                    < *offset
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
