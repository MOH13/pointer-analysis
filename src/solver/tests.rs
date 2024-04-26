use core::hash::Hash;
use hashbrown::{HashMap, HashSet};
use std::fmt::Debug;

use super::{Constraint, ContextInsensitiveInput, ContextInsensitiveSolver, Solver, TermType};
use crate::cstr;
use crate::solver::{SolverSolution, TermSetTrait};

macro_rules! output {
    [ $( $ptr:tt -> { $($target:tt),* } ),* ] => {
        [$( ($ptr, vec![$( $target ),*] ) ),*]
            .into_iter()
            .map(|(t, elems)| (t, HashSet::from_iter(elems)))
            .collect::<HashMap<_, HashSet<_>>>()
    };
}

macro_rules! solver_tests {
    { $( fn $test_name:ident ( $solver:ident, $($var:ident),+ ) $body:block )* } => {
        $(
            mod $test_name {
                macro_rules! vars {
                    ( $solver_ty:ty ) => {
                        #[allow(unused_assignments)]
                        {
                            let mut index = 0 as <<$solver_ty as Solver<ContextInsensitiveInput<_>>>::Solution as SolverSolution>::Term;
                            $(
                                let $var = index;
                                index += 1;
                            )+
                            let $solver = <$solver_ty>::new();
                            $body
                        }
                    }
                }

                use super::*;
                #[test]
                fn hash() {
                    vars!($crate::solver::BasicHashSolver)
                }
                #[test]
                fn hash_wave_prop() {
                    vars!($crate::solver::HashWavePropagationSolver)
                }
                #[test]
                fn roaring_wave_prop() {
                    vars!($crate::solver::RoaringWavePropagationSolver)
                }
                #[test]
                fn shared_bitvec_wave_prop() {
                    vars!($crate::solver::SharedBitVecWavePropagationSolver)
                }
                #[test]
                fn roaring() {
                    vars!($crate::solver::BasicRoaringSolver)
                }
                #[test]
                fn context_insensitive() {
                    #[allow(non_camel_case_types)]
                    #[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
                    enum Term {
                        $( $var , )+
                    }
                    use Term::*;
                    use $crate::solver::AsContextInsensitive;
                    let $solver = AsContextInsensitive($crate::solver::SharedBitVecContextWavePropagationSolver::new());
                    $body
                }
                #[test]
                fn generic() {
                    #[allow(non_camel_case_types)]
                    #[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
                    enum Term {
                        $( $var , )+
                    }
                    use Term::*;
                    use $crate::solver::IntegerTerm;
                    let $solver = $crate::solver::BasicHashSolver::new().as_generic();
                    $body
                }
            }
        )*
    };
}

fn solver_test_template<T, S>(
    solver: S,
    terms: Vec<T>,
    term_types: Vec<(T, TermType)>,
    constraints: impl IntoIterator<Item = Constraint<T>>,
    expected_output: HashMap<T, HashSet<T>>,
) where
    T: Eq + Hash + Copy + Debug,
    S: ContextInsensitiveSolver<T>,
    S::Solution: SolverSolution<Term = T>,
{
    let input = ContextInsensitiveInput {
        terms: terms.clone(),
        term_types,
        constraints: constraints.into_iter().collect(),
    };
    let sol = solver.solve(input);

    let actual_output: HashMap<T, HashSet<T>> = terms
        .into_iter()
        .map(|t| (t, sol.get(&t).iter().collect()))
        .collect();

    assert_eq!(expected_output, actual_output);
}

solver_tests! {
    // Pseudo code:
    //
    // x = &y
    // z = x
    // *z = x
    // z = &w
    // a = null
    fn simple_ref_store(solver, x, y, z, w, a) {
        let terms = vec![x, y, z, w, a];
        let constraints = [
            cstr!(y in x),
            cstr!(x <= z),
            cstr!(x <= *z),
            cstr!(w in z),
        ];
        let expected_output = output![x -> {y}, y -> {y}, z -> {y, w}, w -> {y}, a -> {}];
        solver_test_template(solver, terms, vec![], constraints, expected_output);
    }

    // Pseudo code:
    //
    // x = null
    // y = { f: 0, g: &x }
    // py = &y
    // pg = &py->g
    // z = *pg
    // *z = py
    // *pg = py
    fn field_load_store(solver, x, yf, yg, py, pg, z) {
        let terms = vec![x, yf, yg, py, pg, z];
        let constraints = [
            cstr!(x in yg),
            cstr!(yf in py),
            cstr!(py + 1 <= pg),
            cstr!(*pg <= z),
            cstr!(py <= *z),
            cstr!(py <= *pg),
        ];
        let expected_output =
            output![x -> {yf}, yf -> {yf}, yg -> {x, yf}, py -> {yf}, pg -> {yg}, z -> {x, yf}];
        solver_test_template(solver, terms, vec![(yf, TermType::Struct(1))], constraints, expected_output);
    }

    // Pseudo code:
    //
    // y = null
    // x1 = null
    // x1 = &x1
    // x2 = x1 + 1
    // x1 = x2
    fn positive_cycle(solver, x1, x2, y) {
        let terms = vec![x1, x2, y];
        let constraints = [cstr!(x1 in x1), cstr!(x1 + 1 <= x2), cstr!(x2 <= x1)];
        let expected_output = output![x1 -> {x1,x2}, x2 -> {x2}, y -> {}];
        solver_test_template(solver, terms, vec![(x1, TermType::Struct(1))], constraints, expected_output);
    }

    // Pseudo code:
    //
    // x = null
    // a = { f: 0, g: &x }
    // b = malloc { f: 0, g: null }
    // *b = a
    // c = *b
    fn struct_load_store(solver, x, af, ag, b, hf, hg, cf, cg) {
        let terms = vec![x, af, ag, b, hf, hg, cf, cg];
        let constraints = [
            cstr!(x in ag),
            cstr!(hf in b),
            cstr!(af <= *(b + 0)),
            cstr!(ag <= *(b + 1)),
            cstr!(*(b + 0) <= cf),
            cstr!(*(b + 1) <= cg),
        ];
        let expected_output = output![
            x -> {},
            af -> {},
            ag -> {x},
            b -> {hf},
            hf -> {},
            hg -> {x},
            cf -> {},
            cg -> {x}
        ];
        let allowed_offsets = vec![(af, TermType::Struct(1)), (hf, TermType::Struct(1)), (cf, TermType::Struct(1))];
        solver_test_template(solver, terms, allowed_offsets, constraints, expected_output);
    }
}
