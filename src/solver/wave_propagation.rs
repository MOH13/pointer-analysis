use core::panic;
use std::cmp::{max, min};
use std::mem;

use hashbrown::{HashMap, HashSet};
use once_cell::unsync::Lazy;

use super::{edges_between, offset_term, offset_terms, Constraint, Solver, UnivCond};

struct CondLeftEntry {
    cond_node: usize,
    right: usize,
    offset: usize,
}

struct CondRightEntry {
    cond_node: usize,
    left: usize,
    offset: usize,
}

pub struct WavePropagationSolver {
    sols: Vec<HashSet<usize>>,
    edges: Vec<HashMap<usize, HashSet<usize>>>,
    rev_edges: Vec<HashSet<usize>>,
    left_conds: Vec<CondLeftEntry>,
    right_conds: Vec<CondRightEntry>,
    allowed_offsets: HashMap<usize, usize>,
}

struct SCC {
    node_count: usize,
    iteration: usize,
    d: Vec<Option<usize>>,
    r: Vec<Option<usize>>,
    c: HashSet<usize>,
    s: Vec<usize>,
    top_order: Vec<usize>,
}

impl SCC {
    fn visit(&mut self, v: usize, solver: &WavePropagationSolver) {
        self.iteration += 1;
        self.d[v] = Some(self.iteration);
        self.r[v] = Some(v);
        for (&w, offsets) in &solver.edges[v] {
            if offsets.contains(&0) {
                if self.d[w] == None {
                    self.visit(w, solver)
                }
                if !self.c.contains(&w) {
                    let r_v = self.r[v].unwrap();
                    let r_w = self.r[w].unwrap();
                    self.r[v] = Some(if self.d[r_v] < self.d[r_w] { r_v } else { r_w });
                }
            }
        }
        if self.r[v] == Some(v) {
            self.c.insert(v);
            while let Some(&w) = self.s.last() {
                if self.d[w] <= self.d[v] {
                    break;
                } else {
                    self.s.pop();
                    self.c.insert(w.clone());
                    self.r[w] = Some(v);
                }
            }
            self.top_order.push(v);
        } else {
            self.s.push(v);
        }
    }

    fn run(solver: &mut WavePropagationSolver) -> Self {
        let node_count = solver.edges.len();
        let mut result = Self {
            node_count,
            iteration: 0,
            d: vec![None; node_count],
            r: vec![None; node_count],
            c: HashSet::new(),
            s: vec![],
            top_order: vec![],
        };
        for v in 0..node_count {
            if result.d[v] == None {
                result.visit(v, solver);
            }
        }
        result
    }

    fn unify(&self, child: usize, parent: usize, solver: &mut WavePropagationSolver) {
        let child_sols = mem::take(&mut solver.sols[child]);
        solver.sols[parent].extend(child_sols);
        for (other, offsets) in solver.edges[child].clone() {
            solver.edges[parent]
                .entry(other)
                .or_default()
                .extend(offsets.clone());
        }
        let child_rev_edges = mem::take(&mut solver.rev_edges[child]);
        for &i in &child_rev_edges {
            match solver.edges[i].get_mut(&child) {
                Some(orig_edges) => {
                    let orig_edges = mem::take(orig_edges);
                    solver.edges[i]
                        .entry(parent)
                        .or_default()
                        .extend(orig_edges.iter());
                }
                None => panic!("Expected edges from {i} to {child}"),
            }
        }
        solver.rev_edges[parent].extend(child_rev_edges);

        // Required to be sound
        let child_allowed_offset = solver.allowed_offsets.get(&child);
        if let Some(&o1) = child_allowed_offset {
            solver
                .allowed_offsets
                .entry(parent)
                .and_modify(|o2| *o2 = max(o1, *o2))
                .or_insert(o1);
        }
    }

    fn apply_to_graph(&self, solver: &mut WavePropagationSolver) {
        for v in 0..self.node_count {
            let r_v = self.r[v].unwrap();
            if r_v != v {
                self.unify(v, r_v, solver)
            }
        }
    }
}

impl WavePropagationSolver {
    fn run_wave_propagation(&mut self) {
        let mut p_old = vec![HashSet::new(); self.sols.len()];
        let mut p_cache_left = vec![HashSet::new(); self.left_conds.len()];
        let mut p_cache_right = vec![HashSet::new(); self.right_conds.len()];
        loop {
            let scc = SCC::run(self);
            scc.apply_to_graph(self);
            self.wave_propagate_iteration(&scc.top_order, &mut p_old);
            let changed =
                self.add_edges_after_wave_prop(&mut p_cache_left, &mut p_cache_right, &mut p_old);
            self.wave_propagate_iteration(&scc.top_order, &mut p_old);
            if !changed {
                break;
            }
        }
    }

    fn wave_propagate_iteration(
        &mut self,
        top_order: &Vec<usize>,
        p_old: &mut Vec<HashSet<usize>>,
    ) {
        for &v in top_order.iter().rev() {
            let p_dif: Vec<usize> = self.sols[v].difference(&p_old[v]).copied().collect();
            p_old[v] = self.sols[v].clone();

            let allowed_offsets = Lazy::new(|| {
                p_dif
                    .iter()
                    .map(|t| self.allowed_offsets.get(t).copied().unwrap_or(0))
                    .collect::<Vec<usize>>()
            });
            for (&w, offsets) in &self.edges[v] {
                for &o in offsets {
                    if o == 0 {
                        self.sols[w].extend(&p_dif);
                    } else {
                        let to_add = p_dif
                            .iter()
                            .enumerate()
                            .filter_map(|(i, &t)| (o <= allowed_offsets[i]).then(|| t + o));
                        self.sols[w].extend(to_add);
                    }
                }
            }
        }
    }

    fn add_edges_after_wave_prop(
        &mut self,
        p_cache_left: &mut Vec<HashSet<usize>>,
        p_cache_right: &mut Vec<HashSet<usize>>,
        p_old: &mut Vec<HashSet<usize>>,
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
            let p_new: Vec<_> = self.sols[*cond_node]
                .difference(&p_cache_left[i])
                .copied()
                .collect();
            p_cache_left[i].extend(&p_new);
            for t in p_new {
                if let Some(t) = offset_term(t, &self.allowed_offsets, *offset) {
                    if t == *right {
                        continue;
                    }
                    if edges_between(&mut self.edges, t, *right).insert(0) {
                        self.sols[*right].extend(&p_old[t]);
                        changed = true;
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
            let p_new: Vec<_> = self.sols[*cond_node]
                .difference(&p_cache_right[i])
                .copied()
                .collect();
            p_cache_right[i].extend(&p_new);
            for t in p_new {
                if let Some(t) = offset_term(t, &self.allowed_offsets, *offset) {
                    if t == *left {
                        continue;
                    }
                    if edges_between(&mut self.edges, *left, t).insert(0) {
                        self.sols[t].extend(&p_old[*left]);
                        changed = true;
                    }
                }
            }
        }
        changed
    }

    fn add_edge(&mut self, left: usize, right: usize, offset: usize) -> bool {
        edges_between(&mut self.edges, left, right).insert(offset)
    }
}

impl Solver for WavePropagationSolver {
    type Term = usize;
    type TermSet = HashSet<usize>;

    fn new(terms: Vec<usize>, allowed_offsets: Vec<(usize, usize)>) -> Self {
        Self {
            sols: vec![HashSet::new(); terms.len()],
            edges: vec![HashMap::new(); terms.len()],
            rev_edges: vec![HashSet::new(); terms.len()],
            left_conds: vec![],
            right_conds: vec![],
            allowed_offsets: allowed_offsets.into_iter().collect(),
        }
    }

    fn add_constraint(&mut self, c: Constraint<usize>) {
        match c {
            Constraint::Inclusion { term, node } => {
                self.sols[node].insert(term);
            }
            Constraint::Subset {
                left,
                right,
                offset,
            } => {
                self.add_edge(left, right, offset);
                self.rev_edges[right].insert(left);
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

    fn get_solution(&self, node: &usize) -> HashSet<usize> {
        self.sols[*node].clone()
    }
}
