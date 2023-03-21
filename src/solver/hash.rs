use std::collections::VecDeque;

use hashbrown::{HashMap, HashSet};

use super::{Constraint, Solver, UnivCond};

pub struct BasicHashSolver {
    worklist: VecDeque<(usize, usize)>,
    sols: Vec<HashSet<usize>>,
    edges: Vec<HashMap<usize, HashSet<usize>>>,
    conds: Vec<Vec<UnivCond<usize>>>,
    allowed_offsets: HashMap<usize, usize>,
}

macro_rules! add_token {
    ($solver:expr, $term:expr, $node:expr) => {
        if $solver.sols[$node].insert($term) {
            $solver.worklist.push_back(($term, $node));
        }
    };
}

impl BasicHashSolver {
    fn propagate(&mut self) {
        while let Some((term, node)) = self.worklist.pop_front() {
            for cond in &self.conds[node].clone() {
                match cond {
                    UnivCond::SubsetLeft(right) => self.add_edge(term, *right, 0),
                    UnivCond::SubsetRight(left) => self.add_edge(*left, term, 0),
                }
            }

            for (&n2, edges) in &self.edges[node] {
                for &offset in edges {
                    if offset == 0 {
                        add_token!(self, term, n2);
                    } else {
                        match self.allowed_offsets.get(&term) {
                            Some(max_offset) => {
                                if *max_offset <= offset {
                                    add_token!(self, term + offset, n2)
                                }
                            }
                            None => (),
                        }
                    }
                }
            }
        }
    }

    fn get_edges<'a>(&'a mut self, left: usize, right: usize) -> &'a mut HashSet<usize> {
        if !self.edges[left].contains_key(&right) {
            self.edges[left].insert(right, HashSet::new());
        }
        self.edges[left].get_mut(&right).unwrap()
    }

    fn add_edge(&mut self, left: usize, right: usize, offset: usize) {
        let edges = self.get_edges(left, right);
        if edges.insert(offset) {
            let to_add: Vec<_> = self.sols[left]
                .iter()
                .filter_map(|&t| {
                    if offset == 0 {
                        Some(t)
                    } else {
                        self.allowed_offsets
                            .get(&t)
                            .and_then(|&max_offset| (max_offset <= offset).then(|| t + offset))
                    }
                })
                .collect();
            for t in to_add {
                add_token!(self, t, right);
            }
        }
    }
}

impl Solver for BasicHashSolver {
    type Term = usize;
    type TermSet = HashSet<usize>;

    fn new(terms: Vec<usize>, allowed_offsets: Vec<(usize, usize)>) -> Self {
        Self {
            worklist: VecDeque::new(),
            sols: vec![HashSet::new(); terms.len()],
            edges: vec![HashMap::new(); terms.len()],
            conds: vec![vec![]; terms.len()],
            allowed_offsets: allowed_offsets.into_iter().collect(),
        }
    }

    fn add_constraint(&mut self, c: Constraint<usize>) {
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
            Constraint::UnivCondSubsetLeft { cond_node, right } => {
                self.conds[cond_node].push(UnivCond::SubsetLeft(right));
                let terms: Vec<_> = self.sols[cond_node].iter().copied().collect();

                for t in terms {
                    self.add_edge(t, right, 0);
                }
            }
            Constraint::UnivCondSubsetRight { cond_node, left } => {
                self.conds[cond_node].push(UnivCond::SubsetRight(left));
                let terms: Vec<_> = self.sols[cond_node].iter().copied().collect();

                for t in terms {
                    self.add_edge(left, t, 0);
                }
            }
        };
        self.propagate();
    }

    fn get_solution(&self, node: &usize) -> HashSet<usize> {
        self.sols[*node].clone()
    }
}
