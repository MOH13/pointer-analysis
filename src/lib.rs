pub mod analysis;
pub mod cli;
pub mod module_visitor;
pub mod solver;
pub mod visualizer;

mod util {
    use bitvec::vec::BitVec;

    pub trait GetManyMutExt<T> {
        fn get_two_mut(&mut self, i: usize, j: usize) -> Option<(&mut T, &mut T)>;
        fn my_get_many_mut(&mut self, indices: &[u32]) -> Option<Vec<&mut T>>;
    }

    impl<T> GetManyMutExt<T> for [T] {
        fn get_two_mut(&mut self, i: usize, j: usize) -> Option<(&mut T, &mut T)> {
            if i >= self.len() || j >= self.len() || i == j {
                return None;
            }
            let ptr = self.as_mut_ptr();
            unsafe { Some((&mut *ptr.add(i), &mut *ptr.add(j))) }
        }

        fn my_get_many_mut(&mut self, indices: &[u32]) -> Option<Vec<&mut T>> {
            let mut bitvec = BitVec::<usize>::repeat(false, self.len());

            for &i in indices {
                if i as usize >= self.len() || bitvec[i as usize] {
                    return None;
                }
                bitvec.set(i as usize, true);
            }

            let ptr = self.as_mut_ptr();
            Some(
                indices
                    .iter()
                    .map(|&i| unsafe { &mut *ptr.add(i as usize) })
                    .collect(),
            )
        }
    }
}
