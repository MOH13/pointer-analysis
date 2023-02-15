use hashbrown::HashSet;
use std::collections::VecDeque;
use std::hash::Hash;

pub enum Constraint<T> {
    Inclusion { term: T, node: T },
    Subset { left: T, right: T },
    UnivCondSubsetLeft { cond_node: T, right: T },
    UnivCondSubsetRight { cond_node: T, left: T },
}

#[derive(Clone)]
enum UnivCond<T: Clone> {
    SubsetLeft(T),
    SubsetRight(T),
}

pub trait Solver {
    type Term;
    type TermSet;

    fn new(terms: Vec<Self::Term>) -> Self;

    fn add_constraint(&mut self, c: Constraint<Self::Term>);
    fn get_solution(&self, node: Self::Term) -> &Self::TermSet;
}

pub struct BasicSolver {
    worklist: VecDeque<(usize, usize)>,
    sols: Vec<HashSet<usize>>,
    edges: Vec<HashSet<usize>>,
    conds: Vec<Vec<UnivCond<usize>>>,
}

impl BasicSolver {
    fn propagate(&mut self) {
        while let Some((term, node)) = self.worklist.pop_front() {
            for cond in &self.conds[node].clone() {
                match cond {
                    UnivCond::SubsetLeft(right) => self.add_edge(node, *right),
                    UnivCond::SubsetRight(left) => self.add_edge(*left, node),
                }
            }

            for n2 in self.edges[node].clone() {
                self.add_token(term, n2);
            }
        }
    }

    fn add_token(&mut self, term: usize, node: usize) {
        if self.sols[node].insert(term) {
            self.worklist.push_back((term, node));
        }
    }

    fn add_edge(&mut self, left: usize, right: usize) {
        if self.edges[left].insert(right) {
            let not_in_right: Vec<_> = self.sols[left]
                .difference(&self.sols[right])
                .copied()
                .collect();
            for t in not_in_right {
                self.add_token(t, right);
            }
        }
    }
}

impl Solver for BasicSolver {
    type Term = usize;
    type TermSet = HashSet<usize>;

    fn new(terms: Vec<usize>) -> Self {
        Self {
            worklist: VecDeque::new(),
            sols: vec![HashSet::new(); terms.len()],
            edges: vec![HashSet::new(); terms.len()],
            conds: vec![vec![]; terms.len()],
        }
    }

    fn add_constraint(&mut self, c: Constraint<usize>) {
        match c {
            Constraint::Inclusion { term, node } => {
                self.add_token(term, node);
                self.propagate();
            }
            Constraint::Subset { left, right } => {
                self.add_edge(left, right);
                self.propagate();
            }
            Constraint::UnivCondSubsetLeft { cond_node, right } => {
                self.conds[cond_node].push(UnivCond::SubsetLeft(right));
                let terms: Vec<_> = self.sols[cond_node].iter().copied().collect();

                for t in terms {
                    self.add_edge(t, right);
                }
            }
            Constraint::UnivCondSubsetRight { cond_node, left } => {
                self.conds[cond_node].push(UnivCond::SubsetRight(left));
                let terms: Vec<_> = self.sols[cond_node].iter().copied().collect();

                for t in terms {
                    self.add_edge(left, t);
                }
            }
        };
        self.propagate()
    }

    fn get_solution(&self, node: usize) -> &HashSet<usize> {
        &self.sols[node]
    }
}

pub struct GenericSolver<T> {
    terms: Vec<T>,
}

impl<T> Solver for GenericSolver<T>
where
    T: Hash + Eq,
{
    type Term = T;
    type TermSet = HashSet<T>;

    fn new(terms: Vec<Self::Term>) -> Self {
        todo!()
    }

    fn add_constraint(&mut self, c: Constraint<T>) {
        todo!()
    }

    fn get_solution(&self, node: T) -> &HashSet<T> {
        todo!()
    }
}
