use std::cmp::min;
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;
use std::marker::PhantomData;
use std::mem;

use bitvec::bitvec;
use bitvec::prelude::*;
use hashbrown::{HashMap, HashSet};
use once_cell::unsync::Lazy;
use roaring::RoaringBitmap;

use super::shared_bitvec::SharedBitVec;
use super::{
    edges_between, offset_term_vec_offsets, BetterBitVec, Constraint, ContextInsensitiveInput,
    GenericSolverSolution, IntegerTerm, Solver, SolverSolution, TermSetTrait, TermType,
};
use crate::visualizer::{Edge, EdgeKind, Graph, Node, OffsetWeight};

#[derive(Clone)]
struct CondLeftEntry {
    cond_node: IntegerTerm,
    right: IntegerTerm,
    offset: usize,
    is_function: bool,
}

#[derive(Clone)]
struct CondRightEntry {
    cond_node: IntegerTerm,
    left: IntegerTerm,
    offset: usize,
    is_function: bool,
}

#[derive(Clone)]
pub struct WavePropagationSolver<T> {
    sols: Vec<T>,
    edges: Vec<HashMap<IntegerTerm, Edges>>,
    rev_edges: Vec<HashSet<IntegerTerm>>,
    left_conds: Vec<CondLeftEntry>,
    right_conds: Vec<CondRightEntry>,
    term_types: Vec<TermType>,
    parents: Vec<IntegerTerm>,
    top_order: Vec<IntegerTerm>,
}

#[derive(Clone, Default)]
struct Edges {
    zero: bool,
    offsets: Vec<usize>,
}

impl Edges {
    fn contains(&self, offset: usize) -> bool {
        if offset == 0 {
            return self.zero;
        }
        return self.offsets.contains(&offset);
    }

    fn insert(&mut self, offset: usize) -> bool {
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

    fn union_assign(&mut self, other: &Self) {
        self.zero = other.zero;
        for offset in &other.offsets {
            self.insert(*offset);
        }
    }

    fn len(&self) -> usize {
        self.zero as usize + self.offsets.len()
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.zero
            .then_some(0)
            .into_iter()
            .chain(self.offsets.iter().copied())
    }
}

struct SCC<T> {
    iterative: bool,
    node_count: usize,
    iteration: usize,
    /// 0 means not visited.
    d: Vec<usize>,
    r: Vec<Option<IntegerTerm>>,
    c: BitVec,
    s: Vec<IntegerTerm>,
    top_order: Vec<IntegerTerm>,
    term_set_type_phantom: PhantomData<T>,
}

impl<T: TermSetTrait<Term = IntegerTerm> + Default + Clone> SCC<T> {
    fn visit(&mut self, v: IntegerTerm, solver: &WavePropagationSolver<T>) {
        self.iteration += 1;
        self.d[v as usize] = self.iteration;
        self.r[v as usize] = Some(v);
        if solver.edges[v as usize].is_empty() {
            self.c.set(v as usize, true);
            return;
        }

        for (&w, offsets) in &solver.edges[v as usize] {
            if !offsets.contains(0) {
                continue;
            }

            if self.d[w as usize] == 0 {
                self.visit(w, solver);
            }
            if !self.c[w as usize] {
                let r_v = self.r[v as usize].unwrap();
                let r_w = self.r[w as usize].unwrap();
                self.r[v as usize] = Some(if self.d[r_v as usize] < self.d[r_w as usize] {
                    r_v
                } else {
                    r_w
                });
            }
        }

        if self.r[v as usize] == Some(v) {
            self.c.set(v as usize, true);
            while let Some(&w) = self.s.last() {
                if self.d[w as usize] <= self.d[v as usize] {
                    break;
                }
                self.s.pop();
                self.c.set(w as usize, true);
                self.r[w as usize] = Some(v);
            }
            self.top_order.push(v);
        } else {
            self.s.push(v);
        }
    }

    fn dfs_add_and_finish(&mut self, v: IntegerTerm, solver: &WavePropagationSolver<T>) {
        if self.c[v as usize] {
            return;
        }

        self.c.set(v as usize, true);

        for (&w, offsets) in &solver.edges[v as usize] {
            if !offsets.contains(0) || self.r[v as usize] != self.r[w as usize] {
                continue;
            }

            self.dfs_add_and_finish(w, solver);
        }

        self.top_order.push(v);
    }

    fn visit_with_weighted(&mut self, v: IntegerTerm, solver: &WavePropagationSolver<T>) {
        self.iteration += 1;
        self.d[v as usize] = self.iteration;
        self.r[v as usize] = Some(v);
        if solver.edges[v as usize].is_empty() {
            self.c.set(v as usize, true);
            return;
        }

        for (&w, offsets) in &solver.edges[v as usize] {
            debug_assert!(offsets.len() > 0);

            if self.d[w as usize] == 0 {
                self.visit_with_weighted(w, solver);
            }
            if !self.c[w as usize] {
                let r_v = self.r[v as usize].unwrap();
                let r_w = self.r[w as usize].unwrap();
                self.r[v as usize] = Some(if self.d[r_v as usize] < self.d[r_w as usize] {
                    r_v
                } else {
                    r_w
                });
            }
        }
        if self.r[v as usize] == Some(v) {
            for &w in self.s.iter().rev() {
                if self.d[w as usize] <= self.d[v as usize] {
                    break;
                }
                self.r[w as usize] = Some(v);
            }
            while let Some(&w) = self.s.last() {
                if self.d[w as usize] <= self.d[v as usize] {
                    break;
                }
                self.s.pop();
                self.dfs_add_and_finish(w, solver);
            }
            self.dfs_add_and_finish(v, solver);
        } else {
            self.s.push(v);
        }
    }

    fn init_result(iterative: bool, solver: &WavePropagationSolver<T>) -> Self {
        let node_count = solver.edges.len();
        Self {
            iterative,
            node_count,
            iteration: 0,
            d: vec![0; node_count],
            r: vec![None; node_count],
            c: bitvec![0; node_count],
            s: vec![],
            top_order: vec![],
            term_set_type_phantom: PhantomData,
        }
    }

    fn run(solver: &mut WavePropagationSolver<T>) -> Self {
        let mut result = SCC::init_result(false, solver);
        for v in 0..result.node_count as u32 {
            if result.d[v as usize] == 0 {
                result.visit(v, solver);
            }
        }
        result
    }

    fn run_with_weighted(solver: &mut WavePropagationSolver<T>) -> Self {
        let mut result = SCC::init_result(false, solver);
        for v in 0..result.node_count as u32 {
            if result.d[v as usize] == 0 {
                result.visit_with_weighted(v, solver);
            }
        }

        result
    }

    fn unify(
        &self,
        child: IntegerTerm,
        parent: IntegerTerm,
        solver: &mut WavePropagationSolver<T>,
    ) {
        debug_assert_ne!(child, parent);

        let child_sols = mem::take(&mut solver.sols[child as usize]);
        solver.sols[parent as usize].union_assign(&child_sols);

        let child_edges = mem::take(&mut solver.edges[child as usize]);

        for (&other, offsets) in &child_edges {
            debug_assert_ne!(0, offsets.len());

            let other = if other == child { parent } else { other };

            solver.edges[parent as usize]
                .entry(other)
                .or_default()
                .union_assign(&offsets);
            // Self::do_remove_stuff(&mut solver.rev_edges, other, child);
            // solver.num_removes += 1;
            solver.rev_edges[other as usize].remove(&child);
            solver.rev_edges[other as usize].insert(parent);
        }
        let child_rev_edges = mem::take(&mut solver.rev_edges[child as usize]);
        for &i in child_rev_edges.iter() {
            if i == child {
                continue;
            }
            match solver.edges[i as usize].remove(&child) {
                Some(orig_edges) => {
                    solver.edges[i as usize]
                        .entry(parent)
                        .or_default()
                        .union_assign(&orig_edges);
                }
                None => {
                    panic!("Expected edges from {i} to {child}");
                }
            }
        }

        solver.rev_edges[parent as usize].union_assign(&child_rev_edges);

        if solver.rev_edges[parent as usize].remove(&(child as IntegerTerm)) {
            solver.rev_edges[parent as usize].insert(parent as IntegerTerm);
        }

        solver.parents[child as usize] = parent;
    }

    // Collapse cycles and update topological order
    fn apply_to_graph(self, solver: &mut WavePropagationSolver<T>) {
        let mut removed = HashSet::new();
        for v in 0..self.node_count as u32 {
            if let Some(r_v) = self.r[v as usize] {
                if r_v != v {
                    self.unify(v, r_v, solver);
                    if self.iterative {
                        removed.insert(v);
                    }
                }
            }
        }
        if self.iterative {
            if !removed.is_empty() {
                solver.top_order = solver
                    .top_order
                    .iter()
                    .copied()
                    .filter(|node| !removed.contains(node))
                    .collect()
            }
        } else {
            solver.top_order = self.top_order;
        }
    }

    // Collapse cycles and update topological order
    fn apply_to_graph_weighted(self, solver: &mut WavePropagationSolver<T>) {
        solver.top_order = self.top_order;
    }
}

impl<T: TermSetTrait<Term = u32>> WavePropagationSolver<T> {
    pub fn new() -> Self {
        Self {
            sols: vec![],
            edges: vec![],
            rev_edges: vec![],
            left_conds: vec![],
            right_conds: vec![],
            term_types: vec![],
            parents: vec![],
            top_order: vec![],
        }
    }

    fn run_wave_propagation(&mut self) {
        let mut p_old = vec![T::new(); self.sols.len()];
        let mut p_cache_left = vec![T::new(); self.left_conds.len()];
        let mut p_cache_right = vec![T::new(); self.right_conds.len()];

        SCC::run(self).apply_to_graph(self);

        let mut iters = 0usize;

        let mut changed = true;
        while changed {
            iters += 1;
            // SCC::run_iteratively(self, nodes_with_new_outgoing.iter()).apply_to_graph(self);
            let approx_node_count = self.top_order.len();
            SCC::run(self).apply_to_graph(self);
            SCC::run_with_weighted(self).apply_to_graph_weighted(self);

            let removed = approx_node_count - min(self.top_order.len(), approx_node_count);
            println!("{iters}: Removed approx {removed} nodes");

            let mut nodes_with_new_outgoing = T::new();

            changed = self.wave_propagate_iteration(&mut p_old);

            changed |= self.add_edges_after_wave_prop(
                &mut p_cache_left,
                &mut p_cache_right,
                &mut p_old,
                &mut nodes_with_new_outgoing,
            );
        }
        println!("SCC count: {}", self.top_order.len());
        println!("Iterations: {}", iters);
    }

    fn wave_propagate_iteration(&mut self, p_old: &mut Vec<T>) -> bool {
        let mut changed = false;
        for &v in self.top_order.iter().rev() {
            // Skip if no new terms in solution set
            if self.sols[v as usize].len() == p_old[v as usize].len() {
                continue;
            }
            changed = true;
            let p_dif = self.sols[v as usize].weak_difference(&p_old[v as usize]);
            let p_dif_vec = Lazy::new(|| p_dif.iter().collect::<Vec<IntegerTerm>>());
            p_old[v as usize].clone_from(&self.sols[v as usize]);

            for (&w, offsets) in &self.edges[v as usize] {
                for o in offsets.iter() {
                    if o == 0 {
                        self.sols[w as usize].union_assign(&p_dif);
                    } else {
                        let to_add = p_dif_vec.iter().filter_map(|&t| {
                            if let TermType::Struct(allowed) = self.term_types[t as usize] {
                                (o <= allowed).then(|| t + o as IntegerTerm)
                            } else {
                                None
                            }
                        });
                        self.sols[w as usize].extend(to_add);
                    }
                }
            }
        }
        changed
    }

    fn add_edges_after_wave_prop(
        &mut self,
        p_cache_left: &mut Vec<T>,
        p_cache_right: &mut Vec<T>,
        p_old: &mut Vec<T>,
        nodes_with_new_outgoing: &mut T,
    ) -> bool {
        let mut changed = false;
        for (
            i,
            CondLeftEntry {
                cond_node,
                right,
                offset,
                is_function,
            },
        ) in self.left_conds.iter().enumerate()
        {
            let cond_node = get_representative(&mut self.parents, *cond_node);
            let right = get_representative(&mut self.parents, *right);

            if self.sols[cond_node as usize].len() == p_cache_left[i].len() {
                continue;
            }
            let p_new = self.sols[cond_node as usize].difference(&p_cache_left[i]);
            p_cache_left[i].union_assign(&p_new);
            for t in p_new.iter() {
                if let Some(t) = offset_term_vec_offsets(t, *is_function, &self.term_types, *offset)
                {
                    let t = get_representative(&mut self.parents, t);
                    if t == right {
                        continue;
                    }
                    if edges_between(&mut self.edges, t, right).insert(0) {
                        self.sols[right as usize].union_assign(&p_old[t as usize]);
                        self.rev_edges[right as usize].insert(t);
                        changed = true;
                        nodes_with_new_outgoing.insert(t);
                    }
                }
            }
        }
        for (
            i,
            CondRightEntry {
                cond_node,
                left,
                offset,
                is_function,
            },
        ) in self.right_conds.iter().enumerate()
        {
            let cond_node = get_representative(&mut self.parents, *cond_node);
            let left = get_representative(&mut self.parents, *left);

            if self.sols[cond_node as usize].len() == p_cache_right[i].len() {
                continue;
            }
            let p_new = self.sols[cond_node as usize].difference(&p_cache_right[i]);
            p_cache_right[i].union_assign(&p_new);
            for t in p_new.iter() {
                if let Some(t) = offset_term_vec_offsets(t, *is_function, &self.term_types, *offset)
                {
                    let t = get_representative(&mut self.parents, t);
                    if t == left {
                        continue;
                    }
                    if edges_between(&mut self.edges, left, t).insert(0) {
                        self.sols[t as usize].union_assign(&p_old[left as usize]);
                        self.rev_edges[t as usize].insert(left);
                        changed = true;
                        nodes_with_new_outgoing.insert(t);
                    }
                }
            }
        }
        changed
    }

    fn add_edge(&mut self, left: IntegerTerm, right: IntegerTerm, offset: usize) -> bool {
        let res = edges_between(&mut self.edges, left, right).insert(offset);
        if res {
            self.rev_edges[right as usize].insert(left);
        }
        res
    }

    fn add_constraint(&mut self, c: Constraint<u32>) {
        match c {
            Constraint::Inclusion { term, node } => {
                self.sols[node as usize].insert(term);
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
                self.left_conds.push(CondLeftEntry {
                    cond_node,
                    right,
                    offset,
                    is_function: call_site.is_some(),
                });
            }
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
                call_site,
            } => {
                self.right_conds.push(CondRightEntry {
                    cond_node,
                    left,
                    offset,
                    is_function: call_site.is_some(),
                });
            }
            Constraint::CallDummy { .. } => {}
        };
    }
}

impl<T: TermSetTrait<Term = IntegerTerm>> Solver<ContextInsensitiveInput<IntegerTerm>>
    for WavePropagationSolver<T>
{
    type Solution = Self;

    fn solve(mut self, input: ContextInsensitiveInput<IntegerTerm>) -> Self::Solution {
        self.sols = vec![T::new(); input.terms.len()];
        self.edges = vec![HashMap::new(); input.terms.len()];
        self.rev_edges = vec![HashSet::new(); input.terms.len()];
        self.left_conds = vec![];
        self.right_conds = vec![];
        self.term_types = vec![TermType::Basic; input.terms.len()];
        for (t, tt) in input.term_types {
            self.term_types[t as usize] = tt;
        }
        self.parents = Vec::from_iter(0..input.terms.len() as IntegerTerm);
        self.top_order = Vec::new();

        for c in input.constraints {
            self.add_constraint(c);
        }

        self.run_wave_propagation();

        println!("Max: {}", self.sols.iter().map(|s| s.len()).max().unwrap());
        println!(
            "Mean: {}",
            self.sols.iter().map(|s| s.len() as f64).sum::<f64>() / self.sols.len() as f64
        );
        println!(
            "Median: {}",
            self.sols
                .iter()
                .map(|s| s.len())
                .collect::<Vec<usize>>()
                .select_nth_unstable(self.sols.len() / 2)
                .1
        );

        self
    }
}

impl<T: TermSetTrait<Term = IntegerTerm>> SolverSolution for WavePropagationSolver<T> {
    type Term = IntegerTerm;
    type TermSet = T;

    fn get(&self, node: &IntegerTerm) -> Self::TermSet {
        let representative = get_representative_no_mutation(&self.parents, *node);
        self.sols[representative as usize].clone()
    }
}

fn get_representative_no_mutation(parents: &Vec<IntegerTerm>, child: IntegerTerm) -> IntegerTerm {
    let mut node = child;
    loop {
        let parent = parents[child as usize];
        if parent == node {
            return node;
        }
        node = parent;
    }
}

fn get_representative(parents: &mut Vec<IntegerTerm>, child: IntegerTerm) -> IntegerTerm {
    let parent = parents[child as usize];
    if parent == child {
        return child;
    }
    let representative = get_representative(parents, parent);
    parents[child as usize] = representative;
    representative
}

pub type HashWavePropagationSolver = WavePropagationSolver<HashSet<IntegerTerm>>;
pub type RoaringWavePropagationSolver = WavePropagationSolver<RoaringBitmap>;
pub type BetterBitVecWavePropagationSolver = WavePropagationSolver<BetterBitVec>;
pub type SharedBitVecWavePropagationSolver = WavePropagationSolver<SharedBitVec>;

#[derive(Clone)]
pub struct WavePropagationNode<T> {
    term: T,
    count: usize,
}

impl<T: Display> Display for WavePropagationNode<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{} ({})", self.term, self.count)
    }
}

impl<T, S> GenericSolverSolution<WavePropagationSolver<S>, T>
where
    T: Display + Debug + Clone + PartialEq + Eq + Hash,
    S: TermSetTrait<Term = IntegerTerm>,
{
    fn get_representative_counts(&self) -> HashMap<IntegerTerm, Node<usize>> {
        let mut reps = HashMap::new();
        for n in 0..self.mapping.terms.len() {
            let rep = get_representative_no_mutation(&self.sub_solution.parents, n as IntegerTerm);
            reps.entry(rep)
                .or_insert(Node {
                    inner: 0,
                    id: rep as usize,
                })
                .inner += 1;
        }
        reps
    }
}

impl<T, S> Graph for GenericSolverSolution<WavePropagationSolver<S>, T>
where
    T: Display + Debug + Clone + PartialEq + Eq + Hash,
    S: TermSetTrait<Term = IntegerTerm>,
{
    type Node = WavePropagationNode<T>;
    type Weight = OffsetWeight;

    fn nodes(&self) -> Vec<Node<Self::Node>> {
        let reps = self.get_representative_counts();
        reps.into_iter()
            .map(|(t, node)| {
                let inner = WavePropagationNode {
                    term: self.mapping.integer_to_term(t),
                    count: node.inner,
                };
                Node { inner, id: node.id }
            })
            .collect()
    }

    fn edges(&self) -> Vec<Edge<Self::Node, Self::Weight>> {
        let mut edges = vec![];

        let reps = self.get_representative_counts();
        for (from, outgoing) in self.sub_solution.edges.iter().enumerate() {
            if outgoing.is_empty() {
                continue;
            }

            let inner = WavePropagationNode {
                term: self.mapping.integer_to_term(from as u32),
                count: reps.get(&(from as u32)).unwrap().inner,
            };
            let from_node = Node { inner, id: from };

            for (to, weights) in outgoing {
                let inner = WavePropagationNode {
                    term: self.mapping.integer_to_term(*to),
                    count: reps.get(to).unwrap().inner,
                };
                let to_node = Node {
                    inner,
                    id: *to as usize,
                };

                for weight in weights.iter() {
                    let edge = Edge {
                        from: from_node.clone(),
                        to: to_node.clone(),
                        weight: OffsetWeight(weight as IntegerTerm),
                        kind: EdgeKind::Subset,
                    };
                    edges.push(edge);
                }
            }
        }

        // for from in reps.keys().copied() {
        //     let inner = WavePropagationNode {
        //         term: self.t2_to_term(from),
        //         count: reps.get(&from).unwrap().inner,
        //     };
        //     let from_node = Node {
        //         inner,
        //         id: from as usize,
        //     };
        //     for to in self.sub_solver.get_solution(&from).iter() {
        //         if get_representative_no_mutation(&self.sub_solver.parents, to) != to {
        //             continue;
        //         }
        //         let inner = WavePropagationNode {
        //             term: self.t2_to_term(to),
        //             count: reps.get(&to).unwrap().inner,
        //         };
        //         let to_node = Node {
        //             inner,
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
