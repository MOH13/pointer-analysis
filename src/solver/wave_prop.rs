use core::{hash::Hash, panic};
use std::cmp::max;
use std::marker::PhantomData;
use std::mem;

use hashbrown::{HashMap, HashSet};
use once_cell::unsync::Lazy;
use roaring::RoaringBitmap;

use super::{edges_between, offset_term, Constraint, Solver, TermSetTrait};

type Term = u32;

struct CondLeftEntry {
    cond_node: Term,
    right: Term,
    offset: usize,
}

struct CondRightEntry {
    cond_node: Term,
    left: Term,
    offset: usize,
}

pub struct WavePropagationSolver<T> {
    sols: Vec<T>,
    edges: Vec<HashMap<Term, T>>,
    rev_edges: Vec<T>,
    left_conds: Vec<CondLeftEntry>,
    right_conds: Vec<CondRightEntry>,
    allowed_offsets: HashMap<Term, usize>,
    parents: HashMap<Term, Term>,
    top_order: Vec<Term>,
}

struct SCC<T> {
    iterative: bool,
    node_count: usize,
    iteration: usize,
    d: Vec<Option<usize>>,
    r: Vec<Option<Term>>,
    c: HashSet<Term>,
    s: Vec<Term>,
    top_order: Vec<Term>,
    term_set_type_phantom: PhantomData<T>,
}

impl<T: TermSetTrait<Term = u32> + Default + Clone> SCC<T> {
    fn visit(&mut self, v: Term, solver: &WavePropagationSolver<T>) {
        self.iteration += 1;
        self.d[v as usize] = Some(self.iteration);
        self.r[v as usize] = Some(v);
        for (&w, offsets) in &solver.edges[v as usize] {
            if offsets.contains(0) {
                if self.d[w as usize] == None {
                    self.visit(w, solver);
                }
                if !self.c.contains(&w) {
                    let r_v = self.r[v as usize].unwrap();
                    let r_w = self.r[w as usize].unwrap();
                    self.r[v as usize] = Some(if self.d[r_v as usize] < self.d[r_w as usize] {
                        r_v
                    } else {
                        r_w
                    });
                }
            }
        }
        if self.r[v as usize] == Some(v) {
            self.c.insert(v);
            while let Some(&w) = self.s.last() {
                if self.d[w as usize] <= self.d[v as usize] {
                    break;
                } else {
                    self.s.pop();
                    self.c.insert(w);
                    self.r[w as usize] = Some(v);
                }
            }
            self.top_order.push(v);
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
            d: vec![None; node_count],
            r: vec![None; node_count],
            c: HashSet::new(),
            s: vec![],
            top_order: vec![],
            term_set_type_phantom: PhantomData,
        }
    }

    fn run(solver: &mut WavePropagationSolver<T>) -> Self {
        let mut result = SCC::init_result(false, solver);
        for v in 0..result.node_count as u32 {
            if result.d[v as usize] == None {
                result.visit(v, solver);
            }
        }
        result
    }

    fn run_iteratively<I: Iterator<Item = Term>>(
        solver: &mut WavePropagationSolver<T>,
        nodes_to_search: I,
    ) -> Self {
        let mut result = SCC::init_result(true, solver);
        for v in nodes_to_search {
            if result.d[v as usize] == None {
                result.visit(v, solver);
            }
        }
        result
    }

    fn unify(&self, child: Term, parent: Term, solver: &mut WavePropagationSolver<T>) {
        let child_sols = mem::take(&mut solver.sols[child as usize]);
        solver.sols[parent as usize].union_assign(&child_sols);
        for (other, offsets) in solver.edges[child as usize].clone() {
            solver.edges[parent as usize]
                .entry(other)
                .or_default()
                .union_assign(&offsets);
        }
        let child_rev_edges = mem::take(&mut solver.rev_edges[child as usize]);
        for i in child_rev_edges.iter() {
            match solver.edges[i as usize].get_mut(&child) {
                Some(orig_edges) => {
                    let orig_edges = mem::take(orig_edges);
                    solver.edges[i as usize]
                        .entry(parent)
                        .or_default()
                        .union_assign(&orig_edges);
                }
                None => {
                    if solver.parents.get(&i).is_none() {
                        panic!("Expected edges from {i} to {child}");
                    }
                }
            }
        }
        solver.rev_edges[parent as usize].union_assign(&child_rev_edges);
        if solver.rev_edges[parent as usize].remove(child as u32) {
            solver.rev_edges[parent as usize].insert(parent as u32);
        }

        solver.edges[child as usize] = HashMap::new();

        // Required to be sound
        let child_allowed_offset = solver.allowed_offsets.get(&(child as u32));
        if let Some(&o1) = child_allowed_offset {
            solver
                .allowed_offsets
                .entry(parent)
                .and_modify(|o2| *o2 = max(o1, *o2))
                .or_insert(o1);
        }
        solver.parents.insert(child, parent);
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
}

impl<T: TermSetTrait<Term = u32>> WavePropagationSolver<T> {
    fn run_wave_propagation(&mut self) {
        let mut p_old = vec![T::new(); self.sols.len()];
        let mut p_cache_left = vec![T::new(); self.left_conds.len()];
        let mut p_cache_right = vec![T::new(); self.right_conds.len()];
        let mut nodes_with_new_outgoing = T::new();

        SCC::run(self).apply_to_graph(self);

        loop {
            SCC::run_iteratively(self, nodes_with_new_outgoing.iter()).apply_to_graph(self);
            nodes_with_new_outgoing = T::new();

            let changed = self.wave_propagate_iteration(&mut p_old);

            if !changed {
                break;
            }

            self.add_edges_after_wave_prop(
                &mut p_cache_left,
                &mut p_cache_right,
                &mut p_old,
                &mut nodes_with_new_outgoing,
            );
        }
    }

    fn wave_propagate_iteration(&mut self, p_old: &mut Vec<T>) -> bool {
        let mut changed = false;
        for &v in self.top_order.iter().rev() {
            // Skip if no new terms in solution set
            if self.sols[v as usize].len() == p_old[v as usize].len() {
                continue;
            }
            changed = true;
            let p_dif = self.sols[v as usize].difference(&p_old[v as usize]);
            p_old[v as usize] = self.sols[v as usize].clone();

            let allowed_offsets = Lazy::new(|| {
                p_dif
                    .iter()
                    .map(|t| self.allowed_offsets.get(&t).copied().unwrap_or(0))
                    .collect::<Vec<usize>>()
            });
            for (&w, offsets) in &self.edges[v as usize] {
                for o in offsets.iter() {
                    if o == 0 {
                        self.sols[w as usize].union_assign(&p_dif);
                    } else {
                        let to_add = p_dif.iter().enumerate().filter_map(|(i, t)| {
                            (o <= allowed_offsets[i as usize] as Term).then(|| t + o as Term)
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
            },
        ) in self.left_conds.iter().enumerate()
        {
            let cond_node = get_representative(&mut self.parents, *cond_node);
            let right = get_representative(&mut self.parents, *right);

            let p_new = self.sols[cond_node as usize].difference(&p_cache_left[i]);
            p_cache_left[i].union_assign(&p_new);
            for t in p_new.iter() {
                if let Some(t) = offset_term(t, &self.allowed_offsets, *offset) {
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
            },
        ) in self.right_conds.iter().enumerate()
        {
            let cond_node = get_representative(&mut self.parents, *cond_node);
            let left = get_representative(&mut self.parents, *left);

            let p_new = self.sols[cond_node as usize].difference(&p_cache_right[i]);
            p_cache_right[i].union_assign(&p_new);
            for t in p_new.iter() {
                if let Some(t) = offset_term(t, &self.allowed_offsets, *offset) {
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

    fn add_edge(&mut self, left: Term, right: Term, offset: Term) -> bool {
        edges_between(&mut self.edges, left, right).insert(offset)
    }
}

impl<T: TermSetTrait<Term = u32>> Solver for WavePropagationSolver<T> {
    type Term = Term;
    type TermSet = T;

    fn new(terms: Vec<Term>, allowed_offsets: Vec<(Term, usize)>) -> Self {
        Self {
            sols: vec![T::new(); terms.len()],
            edges: vec![HashMap::new(); terms.len()],
            rev_edges: vec![T::new(); terms.len()],
            left_conds: vec![],
            right_conds: vec![],
            allowed_offsets: allowed_offsets.into_iter().collect(),
            parents: HashMap::new(),
            top_order: Vec::new(),
        }
    }

    fn add_constraint(&mut self, c: Constraint<Term>) {
        match c {
            Constraint::Inclusion { term, node } => {
                self.sols[node as usize].insert(term);
            }
            Constraint::Subset {
                left,
                right,
                offset,
            } => {
                self.add_edge(left, right, offset as Term);
                self.rev_edges[right as usize].insert(left);
            }
            Constraint::UnivCondSubsetLeft {
                cond_node,
                right,
                offset,
            } => {
                self.left_conds.push(CondLeftEntry {
                    cond_node,
                    right,
                    offset,
                });
            }
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
            } => {
                self.right_conds.push(CondRightEntry {
                    cond_node,
                    left,
                    offset,
                });
            }
        };
    }

    fn finalize(&mut self) {
        self.run_wave_propagation();
    }

    fn get_solution(&self, node: &Term) -> Self::TermSet {
        let representative = get_representative_no_mutation(&self.parents, *node);
        self.sols[representative as usize].clone()
    }
}

fn get_representative_no_mutation<T: Eq + PartialEq + Hash + Copy>(
    parents: &HashMap<T, T>,
    child: T,
) -> T {
    let mut node = child;
    while let Some(&parent) = parents.get(&node) {
        node = parent;
    }
    node
}

fn get_representative<T: Eq + PartialEq + Hash + Copy>(parents: &mut HashMap<T, T>, child: T) -> T {
    if let Some(&parent) = parents.get(&child) {
        let representative = get_representative(parents, parent);
        parents.insert(child, parent);
        representative
    } else {
        child
    }
}

pub type HashWavePropagationSolver = WavePropagationSolver<HashSet<Term>>;
pub type RoaringWavePropagationSolver = WavePropagationSolver<RoaringBitmap>;
