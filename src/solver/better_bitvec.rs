use std::cmp::{max, min};

use bitvec::prelude::*;
use bitvec::vec::BitVec;

use super::TermSetTrait;

#[derive(Clone, Default)]
pub struct BetterBitVec {
    bitvec: BitVec<usize>,
    offset: usize,
    ones: usize,
}

pub struct OffsetIter<I> {
    iter: I,
    offset: usize,
}

impl<I: Iterator<Item = usize>> Iterator for OffsetIter<I> {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|t| (t + self.offset) as u32)
    }
}

struct BlockView<'a> {
    slice: &'a [usize],
    start: usize,
    end: usize,
}

impl<'a> BlockView<'a> {
    fn from_better_bitvec(bitvec: &'a BetterBitVec) -> Self {
        Self::from_slice(bitvec.bitvec.as_raw_slice(), bitvec.offset)
    }

    fn from_slice(slice: &'a [usize], offset: usize) -> Self {
        Self {
            slice,
            start: offset,
            end: offset + slice.len(),
        }
    }

    fn is_finished(&self, cur_block: usize) -> bool {
        cur_block >= self.end
    }

    fn get_block(&self, block: usize) -> Option<usize> {
        if block < self.start {
            return None;
        }
        let offset_block = block - self.start;
        self.slice.get(offset_block).map(|v| *v)
    }

    unsafe fn get_block_unchecked(&self, block: usize) -> usize {
        let offset_block = block - self.start;
        *self.slice.get_unchecked(offset_block)
    }
}

fn join_bitvecs<'a, 'b, I: Iterator<Item = usize>>(
    first: &'a BetterBitVec,
    second: &'b BetterBitVec,
    iter_func: impl Fn(&'a BetterBitVec, &'b BetterBitVec) -> (I, usize),
    trim: bool,
) -> BetterBitVec {
    let (iter, mut offset) = iter_func(first, second);

    let mut peekable = iter.peekable();

    if trim {
        while let Some(&v) = peekable.peek() {
            if v == 0 {
                peekable.next();
                offset += 1;
            } else {
                break;
            }
        }
    }

    let mut vec: Vec<_> = peekable.collect();

    if trim {
        if let Some(i) = vec.iter().rposition(|x| *x != 0) {
            vec.truncate(i + 1);
        }
    }

    let bitvec = BitVec::from_vec(vec);
    let ones = bitvec.count_ones();

    BetterBitVec {
        bitvec,
        offset,
        ones,
    }
}

struct UnionIter<'a> {
    first: BlockView<'a>,
    second: BlockView<'a>,
    cur_block: usize,
}

impl<'a> UnionIter<'a> {
    fn iter_better_bitvecs(first: &'a BetterBitVec, second: &'a BetterBitVec) -> (Self, usize) {
        let cur_block = min(first.offset, second.offset);
        (
            Self {
                first: BlockView::from_better_bitvec(first),
                second: BlockView::from_better_bitvec(second),
                cur_block,
            },
            cur_block,
        )
    }

    fn is_finished(&self) -> bool {
        self.first.is_finished(self.cur_block) && self.second.is_finished(self.cur_block)
    }
}

impl<'a> Iterator for UnionIter<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_finished() {
            return None;
        }
        let res = Some(
            match (
                self.first.get_block(self.cur_block),
                self.second.get_block(self.cur_block),
            ) {
                (None, None) => 0,
                (None, Some(v)) | (Some(v), None) => v,
                (Some(v1), Some(v2)) => v1 | v2,
            },
        );
        self.cur_block += 1;
        res
    }
}

struct DifferenceIter<'a> {
    first: BlockView<'a>,
    second: BlockView<'a>,
    cur_block: usize,
}

impl<'a> DifferenceIter<'a> {
    fn iter_better_bitvecs(first: &'a BetterBitVec, second: &'a BetterBitVec) -> (Self, usize) {
        let cur_block = min(first.offset, second.offset);
        (
            Self {
                first: BlockView::from_better_bitvec(first),
                second: BlockView::from_better_bitvec(second),
                cur_block,
            },
            cur_block,
        )
    }

    fn is_finished(&self) -> bool {
        self.first.is_finished(self.cur_block) && self.second.is_finished(self.cur_block)
    }
}

impl<'a> Iterator for DifferenceIter<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_finished() {
            return None;
        }
        let res = Some(
            match (
                self.first.get_block(self.cur_block),
                self.second.get_block(self.cur_block),
            ) {
                (None, None) => 0,
                (None, Some(_)) => 0,
                (Some(v), None) => v,
                (Some(v1), Some(v2)) => v1 & !v2,
            },
        );
        self.cur_block += 1;
        res
    }
}

impl BetterBitVec {
    #[inline]
    fn offset_bits(&self) -> usize {
        self.offset * usize::BITS as usize
    }

    #[inline]
    fn offset_index(&self, index: usize) -> Option<usize> {
        let offset_bits = self.offset_bits();
        if index >= self.get_start() && index < self.get_end() {
            return Some(index - offset_bits);
        }
        None
    }

    #[inline]
    fn get_block_count(&self) -> usize {
        self.bitvec.as_raw_slice().len()
    }

    #[inline]
    fn get_start_block(&self) -> usize {
        self.offset
    }

    #[inline]
    fn get_end_block(&self) -> usize {
        self.get_start_block() + self.get_block_count()
    }

    #[inline]
    fn get_start(&self) -> usize {
        self.get_start_block() * usize::BITS as usize
    }

    #[inline]
    fn get_end(&self) -> usize {
        self.get_end_block() * usize::BITS as usize
    }

    #[inline]
    fn expand_to(&mut self, index: usize) {
        let block_of_bit = index / usize::BITS as usize;
        if self.get_block_count() == 0 {
            debug_assert_eq!(0, self.ones);
            *self = Self {
                bitvec: BitVec::from_vec(vec![0]),
                offset: block_of_bit,
                ones: 0,
            };
            return;
        }
        let start_block = self.get_start_block();
        let end_block = self.get_end_block();
        let block_count = self.get_block_count();
        let block_to_expand_to = if block_of_bit >= end_block {
            max(block_of_bit, start_block + block_count * 2)
        } else if block_of_bit < start_block {
            if start_block < block_count {
                0
            } else {
                min(block_of_bit, start_block - block_count)
            }
        } else {
            return;
        };
        let new_start_block = min(start_block, block_to_expand_to);
        let new_end_block = max(end_block, block_to_expand_to);
        let mut new_bitvec = BitVec::from_vec(vec![0; new_end_block - new_start_block + 1]);
        new_bitvec.as_raw_mut_slice()[start_block - new_start_block..end_block - new_start_block]
            .copy_from_slice(self.bitvec.as_raw_slice());
        *self = Self {
            bitvec: new_bitvec,
            offset: new_start_block,
            ones: self.ones,
        };
        debug_assert!(matches!(self.offset_index(index), Some(_)));
    }
}

impl TermSetTrait for BetterBitVec {
    type Term = u32;

    #[inline]
    fn new() -> Self {
        Self {
            bitvec: bitvec![],
            offset: 0,
            ones: 0,
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.ones
    }

    #[inline]
    fn contains(&self, term: Self::Term) -> bool {
        if let Some(index) = self.offset_index(term as usize) {
            unsafe { *self.bitvec.get_unchecked(index) }
        } else {
            false
        }
    }

    #[inline]
    fn remove(&mut self, term: Self::Term) -> bool {
        if let Some(index) = self.offset_index(term as usize) {
            unsafe {
                let mut val = self.bitvec.get_unchecked_mut(index);
                if *val {
                    *val = false;
                    self.ones -= 1;
                    return true;
                }
            }
        }
        false
    }

    #[inline]
    fn insert(&mut self, term: Self::Term) -> bool {
        if let Some(index) = self.offset_index(term as usize) {
            unsafe {
                let mut val = self.bitvec.get_unchecked_mut(index);
                if !*val {
                    *val = true;
                    self.ones += 1;
                    true
                } else {
                    false
                }
            }
        } else {
            self.expand_to(term as usize);
            self.insert(term)
        }
    }

    #[inline]
    fn union_assign(&mut self, other: &Self) {
        if other.ones == 0 {
            return;
        }
        if other.get_start_block() >= self.get_start_block()
            && other.get_end_block() <= self.get_end_block()
        {
            let mut block = other.offset;

            let my_slice = self.bitvec.as_raw_mut_slice();
            let other_view = BlockView::from_better_bitvec(other);
            while block < other.get_end_block() {
                let my_view = BlockView::from_slice(my_slice, self.offset);
                unsafe {
                    let value =
                        my_view.get_block_unchecked(block) | other_view.get_block_unchecked(block);

                    my_slice[block - self.offset] = value;
                    block += 1;
                }
            }
            self.ones = self.bitvec.count_ones();
        } else {
            *self = join_bitvecs(self, other, UnionIter::iter_better_bitvecs, true)
        }
    }

    #[inline]
    fn extend<T: Iterator<Item = Self::Term>>(&mut self, other: T) {
        for t in other {
            self.insert(t);
        }
    }

    #[inline]
    fn difference(&self, other: &Self) -> Self {
        if other.ones == 0 {
            return self.clone();
        }
        join_bitvecs(self, other, DifferenceIter::iter_better_bitvecs, true)
    }

    #[inline]
    fn iter(&self) -> impl Iterator<Item = Self::Term> {
        let offset_bits = self.offset_bits();
        OffsetIter {
            iter: self.bitvec.iter_ones(),
            offset: offset_bits,
        }
    }
}

#[cfg(test)]
mod test {
    use bitvec::vec::BitVec;

    use crate::solver::TermSetTrait;

    use super::BetterBitVec;

    #[test]
    fn insert_test1() {
        let mut bitvec = BetterBitVec::new();
        assert_eq!(true, bitvec.insert(1));
        assert_eq!(false, bitvec.insert(1));
    }

    #[test]
    fn insert_test2() {
        let mut bitvec = BetterBitVec::new();
        assert_eq!(true, bitvec.insert(1));
        assert_eq!(true, bitvec.contains(1));
        assert_eq!(&[2], bitvec.bitvec.as_raw_slice())
    }

    #[test]
    fn insert_test3() {
        let mut bitvec = BetterBitVec::new();
        assert_eq!(true, bitvec.insert(64));
        assert_eq!(true, bitvec.contains(64));
        assert_eq!(false, bitvec.contains(63));
        assert_eq!(&[1], bitvec.bitvec.as_raw_slice());
        assert_eq!(1, bitvec.offset);
    }

    #[test]
    fn insert_remove_test1() {
        let mut bitvec = BetterBitVec::new();
        assert_eq!(true, bitvec.insert(1));
        assert_eq!(true, bitvec.contains(1));
        assert_eq!(true, bitvec.remove(1));
        assert_eq!(false, bitvec.contains(1));
    }

    #[test]
    fn test_union1() {
        let mut bitvec1 = BetterBitVec {
            bitvec: BitVec::from_slice(&[0b11110000, 0b10010100]),
            offset: 1,
            ones: 7,
        };
        let bitvec2 = BetterBitVec {
            bitvec: BitVec::from_slice(&[0b01010000, 15]),
            offset: 2,
            ones: 6,
        };

        bitvec1.union_assign(&bitvec2);

        assert_eq!(&[0b11110000, 0b11010100, 15], bitvec1.bitvec.as_raw_slice());
        assert_eq!(1, bitvec1.offset);
    }

    #[test]
    fn test_union2() {
        let mut bitvec1 = BetterBitVec {
            bitvec: BitVec::from_slice(&[0b11110000, 0b10010100]),
            offset: 1,
            ones: 7,
        };
        let bitvec2 = BetterBitVec {
            bitvec: BitVec::from_slice(&[0b01010000, 15]),
            offset: 4,
            ones: 6,
        };

        bitvec1.union_assign(&bitvec2);

        assert_eq!(
            &[0b11110000, 0b10010100, 0, 0b01010000, 15],
            bitvec1.bitvec.as_raw_slice()
        );
        assert_eq!(1, bitvec1.offset);
    }

    #[test]
    fn test_difference1() {
        let bitvec1 = BetterBitVec {
            bitvec: BitVec::from_slice(&[0b11110000, 0b10010100]),
            offset: 1,
            ones: 7,
        };
        let bitvec2 = BetterBitVec {
            bitvec: BitVec::from_slice(&[0b01010000, 15]),
            offset: 2,
            ones: 6,
        };

        let bitvec3 = bitvec1.difference(&bitvec2);

        assert_eq!(&[0b11110000, 0b10000100], bitvec3.bitvec.as_raw_slice());
        assert_eq!(1, bitvec3.offset);
    }

    #[test]
    fn test_truncate() {
        let mut vec: Vec<usize> = vec![1, 2, 3, 4];
        vec.truncate(2);
        let bitvec: BitVec<usize> = BitVec::from_vec(vec);

        assert_eq!(&[1, 2], bitvec.as_raw_slice());
    }
}
