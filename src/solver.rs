use std::collections::HashSet;
use std::hash::Hash;

enum Constraint<T, N> {
    Inclusion {
        term: T,
        node: N,
    },
    Subset {
        left: N,
        right: N,
    },
    CondSubset {
        term: T,
        cond_node: N,
        left: N,
        right: N,
    },
}

trait Solver {
    type Term;
    type Node;
    type TermSet;

    fn add_constraint(&mut self, c: Constraint<Self::Term, Self::Node>);
    fn get_solution(&self, node: Self::Node) -> Self::TermSet;
}

struct GenericSolver<T, N> {
    t: T,
    n: N,
}

impl<T, N> GenericSolver<T, N> {
    fn new() -> Self {
        todo!()
    }
}

impl<T, N> Solver for GenericSolver<T, N>
where
    N: Hash + Eq,
{
    type Term = T;

    type Node = N;

    type TermSet = HashSet<T>;

    fn add_constraint(&mut self, c: Constraint<Self::Term, Self::Node>) {
        todo!()
    }

    fn get_solution(&self, node: N) -> Self::TermSet {
        todo!()
    }
}
