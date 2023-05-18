use std::collections::VecDeque;

use hashbrown::{HashMap, HashSet};

use super::{edges_between, offset_term, offset_terms, Constraint, Solver, UnivCond};

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

            for (&n2, edges) in &self.edges[node] {
                for &offset in edges {
                    if let Some(t) = offset_term(term, &self.allowed_offsets, offset) {
                        add_token!(self, t, n2);
                    }
                }
            }
        }
    }

    fn add_edge(&mut self, left: usize, right: usize, offset: usize) {
        let edges = edges_between(&mut self.edges, left, right);
        if edges.insert(offset) {
            for t in offset_terms(
                self.sols[left].iter().copied(),
                &self.allowed_offsets,
                offset,
            ) {
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
            Constraint::UnivCondSubsetLeft {
                cond_node,
                right,
                offset,
            } => {
                self.conds[cond_node].push(UnivCond::SubsetLeft { right, offset });
                let terms = offset_terms(
                    self.sols[cond_node].iter().copied(),
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
            } => {
                self.conds[cond_node].push(UnivCond::SubsetRight { left, offset });
                let terms = offset_terms(
                    self.sols[cond_node].iter().copied(),
                    &self.allowed_offsets,
                    offset,
                );

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
