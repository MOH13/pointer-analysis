use super::{Constraint, Solver};

pub struct StatSolver<T> {
    terms: Vec<T>,
    num_inclusion: u64,
    num_subset: u64,
    num_offset_subset: u64,
    num_univ_cond: u64,
    num_offset_univ_cond: u64,
}

impl<T> Solver for StatSolver<T> {
    type Term = T;
    type TermSet = ();

    fn new(terms: Vec<Self::Term>, _allowed_offsets: Vec<(Self::Term, usize)>) -> Self {
        Self {
            terms,
            num_inclusion: 0,
            num_subset: 0,
            num_offset_subset: 0,
            num_univ_cond: 0,
            num_offset_univ_cond: 0,
        }
    }

    fn add_constraint(&mut self, c: Constraint<Self::Term>) {
        match c {
            Constraint::Inclusion { .. } => self.num_inclusion += 1,
            Constraint::Subset { offset, .. } => {
                self.num_subset += 1;
                if offset != 0 {
                    self.num_offset_subset += 1;
                }
            }
            Constraint::UnivCondSubsetLeft { offset, .. }
            | Constraint::UnivCondSubsetRight { offset, .. } => {
                self.num_univ_cond += 1;
                if offset != 0 {
                    self.num_offset_univ_cond += 1;
                }
            }
        }
    }

    fn get_solution(&self, _node: &Self::Term) -> Self::TermSet {}

    fn finalize(&mut self) {
        let total = self.num_inclusion + self.num_subset + self.num_univ_cond;
        println!("Terms:\t\t{}", self.terms.len());
        println!("Inclusion:\t{}", self.num_inclusion);
        println!(
            "Subset:\t\t{} ({} offset constraints)",
            self.num_subset, self.num_offset_subset
        );
        println!(
            "Univ. cond.:\t{} ({} offset constraints)",
            self.num_univ_cond, self.num_offset_univ_cond
        );
        println!("Total:\t\t{total}");
    }
}
