pub mod analysis;
pub mod cli;
pub mod module_visitor;
pub mod solver;
pub mod visualizer;

mod util {
    pub trait GetTwoMutExt<T> {
        fn get_two_mut(&mut self, i: usize, j: usize) -> Option<(&mut T, &mut T)>;
    }

    impl<T> GetTwoMutExt<T> for [T] {
        fn get_two_mut(&mut self, i: usize, j: usize) -> Option<(&mut T, &mut T)> {
            if i == j {
                return None;
            }
            let ptr = self.as_mut_ptr();
            unsafe { Some((&mut *ptr.add(i), &mut *ptr.add(j))) }
        }
    }
}
