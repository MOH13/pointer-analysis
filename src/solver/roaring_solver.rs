use std::collections::VecDeque;

use hashbrown::HashMap;

use roaring::RoaringBitmap;

use super::{edges_between, offset_term, offset_terms, Constraint, Solver, UnivCond};

pub struct RoaringSolver {
    worklist: VecDeque<(u32, u32)>,
    sols: Vec<RoaringBitmap>,
    edges: Vec<HashMap<u32, RoaringBitmap>>,
    conds: Vec<Vec<UnivCond<u32>>>,
    allowed_offsets: HashMap<usize, usize>,
}

macro_rules! add_token {
    ($solver:expr, $term:expr, $node:expr) => {
        if $solver.sols[$node as usize].insert($term) {
            $solver.worklist.push_back(($term, $node));
        }
    };
}

impl RoaringSolver {
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
                for offset in edges {
                    if let Some(t) =
                        offset_term(term as usize, &self.allowed_offsets, offset as usize)
                    {
                        add_token!(self, t as u32, n2 as u32);
                    }
                }
            }
        }
    }

    fn add_edge(&mut self, left: u32, right: u32, offset: usize) {
        let edges = edges_between(&mut self.edges, left, right);
        if edges.insert(offset as u32) {
            for t in offset_terms(
                self.sols[left as usize].iter(),
                &self.allowed_offsets,
                offset,
            ) {
                add_token!(self, t as u32, right as u32);
            }
        }
    }
}

impl Solver for RoaringSolver {
    type Term = usize;
    type TermSet = RoaringBitmap;

    fn new(terms: Vec<usize>, allowed_offsets: Vec<(usize, usize)>) -> Self {
        Self {
            worklist: VecDeque::new(),
            sols: vec![RoaringBitmap::new(); terms.len()],
            edges: vec![HashMap::new(); terms.len()],
            conds: vec![vec![]; terms.len()],
            allowed_offsets: allowed_offsets.into_iter().collect(),
        }
    }

    fn add_constraint(&mut self, c: Constraint<usize>) {
        match c {
            Constraint::Inclusion { term, node } => {
                add_token!(self, term as u32, node as u32);
            }
            Constraint::Subset {
                left,
                right,
                offset,
            } => {
                self.add_edge(left as u32, right as u32, offset);
            }
            Constraint::UnivCondSubsetLeft {
                cond_node,
                right,
                offset,
            } => {
                self.conds[cond_node].push(UnivCond::SubsetLeft {
                    right: right as u32,
                    offset,
                });
                let terms =
                    offset_terms(self.sols[cond_node].iter(), &self.allowed_offsets, offset);

                for t in terms {
                    self.add_edge(t, right as u32, 0);
                }
            }
            Constraint::UnivCondSubsetRight {
                cond_node,
                left,
                offset,
            } => {
                self.conds[cond_node].push(UnivCond::SubsetRight {
                    left: left as u32,
                    offset,
                });
                let terms =
                    offset_terms(self.sols[cond_node].iter(), &self.allowed_offsets, offset);

                for t in terms {
                    self.add_edge(left as u32, t, 0);
                }
            }
        };
        self.propagate();
    }

    fn get_solution(&self, node: &usize) -> RoaringBitmap {
        self.sols[*node].clone()
    }

    fn finalize(&mut self) {}
}
