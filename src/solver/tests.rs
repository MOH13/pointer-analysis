use core::hash::Hash;
use hashbrown::{HashMap, HashSet};
use std::fmt::Debug;

use super::{Constraint, IterableTermSet, Solver};
use crate::cstr;

macro_rules! output {
    [ $( $ptr:tt -> { $($target:tt),* } ),* ] => {
        [$( ($ptr, vec![$( $target ),*] ) ),*]
            .into_iter()
            .map(|(t, elems)| (t, HashSet::from_iter(elems)))
            .collect::<HashMap<_, HashSet<_>>>()
    };
}

macro_rules! solver_tests {
    { $( fn $test_name:ident < $solver:ident > ( $($var:ident),+ ) $body:block )* } => {
        $(
            mod $test_name {
                macro_rules! vars {
                    ( $solver_ty:ty ) => {
                        #[allow(unused_assignments)]
                        {
                            let mut index = 0;
                            $(
                                let $var = index;
                                index += 1;
                            )+
                            type $solver = $solver_ty;
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
                fn bit_vec() {
                    vars!($crate::solver::BasicBitVecSolver)
                }
                #[test]
                fn wave_prop() {
                    vars!($crate::solver::WavePropagationSolver)
                }
                #[test]
                fn roaring() {
                    vars!($crate::solver::RoaringSolver)
                }
                #[test]
                fn generic() {
                    #[allow(non_camel_case_types)]
                    #[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
                    enum Term {
                        $( $var , )+
                    }
                    type $solver = $crate::solver::GenericSolver<Term, $crate::solver::BasicHashSolver>;
                    use Term::*;
                    $body
                }
            }
        )*
    };
}

fn solver_test_template<T, S>(
    terms: Vec<T>,
    allowed_offsets: Vec<(T, usize)>,
    constraints: impl IntoIterator<Item = Constraint<T>>,
    expected_output: HashMap<T, HashSet<T>>,
) where
    T: Eq + Hash + Copy + Debug,
    S: Solver<Term = T>,
    S::TermSet: IterableTermSet<T>,
{
    let mut solver = S::new(terms.clone(), allowed_offsets);
    for c in constraints {
        solver.add_constraint(c);
    }
    solver.finalize();

    let actual_output: HashMap<T, HashSet<T>> = terms
        .into_iter()
        .map(|t| (t, solver.get_solution(&t).iter_term_set().collect()))
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
    fn simple_ref_store<S>(x, y, z, w, a) {
        let terms = vec![x, y, z, w, a];
        let constraints = [
            cstr!(y in x),
            cstr!(x <= z),
            cstr!(c in z : x <= c),
            cstr!(w in z),
        ];
        let expected_output = output![x -> {y}, y -> {y}, z -> {y, w}, w -> {y}, a -> {}];
        solver_test_template::<_, S>(terms, vec![], constraints, expected_output);
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
    fn field_load_store<S>(x, yf, yg, py, pg, z) {
        let terms = vec![x, yf, yg, py, pg, z];
        let constraints = [
            cstr!(x in yg),
            cstr!(yf in py),
            cstr!(py + 1 <= pg),
            cstr!(c in pg : c <= z),
            cstr!(c in z : py <= c),
            cstr!(c in pg : py <= c),
        ];
        let expected_output =
            output![x -> {yf}, yf -> {yf}, yg -> {x, yf}, py -> {yf}, pg -> {yg}, z -> {x, yf}];
        solver_test_template::<_, S>(terms, vec![(yf, 1)], constraints, expected_output);
    }

    // Pseudo code:
    //
    // y = null
    // x1 = null
    // x1 = &x1
    // x2 = x1 + 1
    // x1 = x2
    fn positive_cycle<S>(x1, x2, y) {
        let terms = vec![x1, x2, y];
        let constraints = [cstr!(x1 in x1), cstr!(x1 + 1 <= x2), cstr!(x2 <= x1)];
        let expected_output = output![x1 -> {x1,x2}, x2 -> {x2}, y -> {}];
        solver_test_template::<_, S>(terms, vec![(x1, 1)], constraints, expected_output);
    }

    // Pseudo code:
    //
    // x = null
    // a = { f: 0, g: &x }
    // b = malloc { f: 0, g: null }
    // *b = a
    // c = *b
    fn struct_load_store<S>(x, af, ag, b, hf, hg, cf, cg) {
        let terms = vec![x, af, ag, b, hf, hg, cf, cg];
        let constraints = [
            cstr!(x in ag),
            cstr!(hf in b),
            cstr!(c in b + 0 : af <= c),
            cstr!(c in b + 1 : ag <= c),
            cstr!(c in b + 0 : c <= cf),
            cstr!(c in b + 1 : c <= cg),
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
        let allowed_offsets = vec![(af, 1), (hf, 1), (cf, 1)];
        solver_test_template::<_, S>(terms, allowed_offsets, constraints, expected_output);
    }
}
