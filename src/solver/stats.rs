use super::{Constraint, Solver};

pub struct StatSolver<T> {
    pub terms: Vec<T>,
    pub constraints: usize,
}

impl<T> Solver for StatSolver<T> {
    type Term = T;
    type TermSet = ();

    fn new(terms: Vec<Self::Term>, _allowed_offsets: Vec<(Self::Term, usize)>) -> Self {
        Self {
            terms,
            constraints: 0,
        }
    }

    fn add_constraint(&mut self, _c: Constraint<Self::Term>) {
        self.constraints += 1;
    }

    fn get_solution(&self, _node: &Self::Term) -> Self::TermSet {}

    fn finalize(&mut self) {
        println!("Constraints: {}", self.constraints);
    }
}
