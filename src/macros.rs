// // The macro that expands into all pairs
// macro_rules! for_all_pairs {

//     // The head/tail recursion: pick the first element of the first list
//     // and recursively do it for the tail.
//     ($mac:ident: $head:tt%$($tail:tt)%*; $($y:tt)%*; $($acc:tt)*) => {
//         for_all_pairs!($mac: $($tail)%*; $($y)%*; $($acc)* $($mac!($head, $y))*)
//     };

//     // The end of iteration: we exhausted the list
//     ($mac:ident: $head:tt; $($y:tt)%*; $($acc:tt)*) => {
//         $mac!(@body $($acc)* $($mac!($head, $y))*)
//     }
// }

// macro_rules! for_all_solver_term_set_pairs {
//     ($mac:ident) => {
//         for_all_pairs!(
//             $mac:
//                 (pointer_analysis::solver::BasicSolver, pointer_analysis::cli::SolverMode::Basic, basic)
//                 % (pointer_analysis::solver::WavePropagationSolver, pointer_analysis::cli::SolverMode::Wave, wave)
//                 ;
//                 (hashbrown::HashSet<u32>, pointer_analysis::cli::TermSet::Hash, hash)
//                 % (roaring::bitmap::RoaringBitmap, pointer_analysis::cli::TermSet::Roaring, roaring)
//                 ;
//         )
//     }
// }

// #[cfg(test)]
// mod test {
//     macro_rules! forall_test1 {
//         ($a:ident, $b:ident) => {
//             $a+$b,
//         };
//         (@body $($rest:tt)*) => {
//             [$($rest)*]
//         }
//     }

//     macro_rules! forall_test2 {
//         (($t1:ty, $e1:expr, $n1:ident), ($t2:ty, $e2:expr, $n2:ident)) => {
//             let concat_idents!($n1, $n2) = stringify!($n1) + stringify!($n2);
//             123
//         };
//         (@body $($rest:tt)*) => {
//             {
//                 $($rest)*
//             }
//         }
//     }

//     #[test]
//     fn test_forall() {
//         let a = 1;
//         let b = 2;
//         let c = 3;
//         let d = 4;
//         let e = 5;
//         let f = 6;
//         trace_macros!(true);
//         let v = for_all_pairs! (forall_test1: a%b;d%e; );
//         trace_macros!(false);
//         //for_all_solver_term_set_pairs!(forall_test)
//     }
// }
