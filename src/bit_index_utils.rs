#[derive(Debug)]
pub struct BitIndexIter<I> {
    iter: I,
    cur_block_index: usize,
    remaining_block_value: usize,
}

impl<I: Iterator<Item = usize>> BitIndexIter<I> {
    pub fn new(mut iter: I) -> Self {
        let block_val = iter.next().unwrap_or(0);
        Self {
            iter,
            cur_block_index: 0,
            remaining_block_value: block_val,
        }
    }

    fn try_load_next_non_empty_block(&mut self) -> bool {
        self.cur_block_index = self.cur_block_index + 1;
        match self.iter.next() {
            Some(0) => self.try_load_next_non_empty_block(),
            Some(v) => {
                self.remaining_block_value = v;
                true
            }
            None => false,
        }
    }
}

impl<I: Iterator<Item = usize>> Iterator for BitIndexIter<I> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining_block_value == 0 && !self.try_load_next_non_empty_block() {
            return None;
        } else {
            // Invariant: There is at least a single 1 bit somewhere in remaining block
            let index_in_block = self.remaining_block_value.trailing_zeros() as usize;
            self.remaining_block_value = self.remaining_block_value ^ (1 << index_in_block);
            Some(index_in_block + usize::BITS as usize * self.cur_block_index)
        }
    }
}

pub fn no_alloc_combine(
    left: impl Iterator<Item = usize>,
    right: impl Iterator<Item = usize>,
    f: fn((usize, usize)) -> usize,
) -> impl Iterator<Item = usize> {
    left.zip(right).map(f)
}

pub fn no_alloc_and(
    left: impl Iterator<Item = usize>,
    right: impl Iterator<Item = usize>,
) -> impl Iterator<Item = usize> {
    no_alloc_combine(left, right, |(lblock, rblock)| lblock & rblock)
}

pub fn no_alloc_difference(
    left: impl Iterator<Item = usize>,
    right: impl Iterator<Item = usize>,
) -> impl Iterator<Item = usize> {
    no_alloc_combine(left, right, |(lblock, rblock)| lblock & !rblock)
}

#[cfg(test)]
mod tests {
    use bitvec::prelude::*;

    use super::BitIndexIter;

    #[test]
    fn bit_index_test() {
        let bits = bitvec![0, 1, 0, 1, 0, 1, 0, 1];
        let ones = Vec::from_iter(BitIndexIter::new(bits.as_raw_slice().iter().copied()));

        assert_eq!(vec![1, 3, 5, 7], ones);
    }
}
