pub mod analysis;
pub mod cli;
pub mod module_visitor;
pub mod solver;
pub mod visualizer;

mod util {
    pub trait GetTwoMutExt<T> {
        fn get_two_mut(&mut self, i: usize, j: usize) -> (&mut T, &mut T);
    }

    impl<T> GetTwoMutExt<T> for [T] {
        fn get_two_mut(&mut self, i: usize, j: usize) -> (&mut T, &mut T) {
            assert_ne!(i, j);
            let ptr = self.as_mut_ptr();
            unsafe { (&mut *ptr.add(i), &mut *ptr.add(j)) }
        }
    }
}
