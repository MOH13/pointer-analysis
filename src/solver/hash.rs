use std::collections::VecDeque;

use hashbrown::{HashMap, HashSet};

use super::{Constraint, Solver, UnivCond};

pub struct BasicHashSolver {
    worklist: VecDeque<(usize, usize)>,
    sols: Vec<HashSet<usize>>,
    edges: Vec<HashMap<usize, usize>>,
    conds: Vec<Vec<UnivCond<usize>>>,
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
                    UnivCond::SubsetLeft(right) => self.add_edge(node, *right, 0),
                    UnivCond::SubsetRight(left) => self.add_edge(*left, node, 0),
                }
            }

            for (&n2, &offset) in &self.edges[node] {
                add_token!(self, term + offset, n2);
            }
        }
    }

    fn add_edge(&mut self, left: usize, right: usize, offset: usize) {
        if self.edges[left].insert(right, offset).is_none() {
            let not_in_right: Vec<_> = self.sols[left]
                .iter()
                .map(|&t| t + offset)
                .filter(|t| !self.sols[right].contains(t))
                .collect();
            for t in not_in_right {
                add_token!(self, t, right);
            }
        } else {
            panic!("Use of parallel offset edges is unsuported");
        }
    }
}

impl Solver for BasicHashSolver {
    type Term = usize;
    type TermSet = HashSet<usize>;

    fn new(terms: Vec<usize>) -> Self {
        Self {
            worklist: VecDeque::new(),
            sols: vec![HashSet::new(); terms.len()],
            edges: vec![HashMap::new(); terms.len()],
            conds: vec![vec![]; terms.len()],
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
        self.propagate()
    }

    fn get_solution(&self, node: &usize) -> HashSet<usize> {
        self.sols[*node].clone()
    }
}