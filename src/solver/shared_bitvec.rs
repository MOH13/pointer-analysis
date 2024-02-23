use std::collections::VecDeque;
use std::rc::Rc;

use arrayvec::ArrayVec;
use either::Either;
use smallvec::SmallVec;
use tinybitset::TinyBitSet;

use super::TermSetTrait;

type Term = u32;
type Chunk = TinyBitSet<u64, CHUNK_SIZE>;

const CHUNK_SIZE: usize = 64;
const ELEMS_IN_CHUNK: Term = usize::BITS * CHUNK_SIZE as Term;
const BACKING_ARRAY_SIZE: usize = 4;

// Maximal size of a sorted list of u32 terms so that it has the same size as InnerBitVec
const ARRAY_VEC_SIZE: usize = 19; // wrong: (std::mem::size_of::<InnerBitVec>() - 4) / 4 - 1;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Segment {
    start_index: Term,
    chunk: Rc<Chunk>,
}

impl Segment {
    fn len(&self) -> u32 {
        self.chunk.len() as u32
    }
}

#[derive(PartialEq, Eq, Debug)]
pub enum SharedBitVec {
    Array(ArrayVec<Term, ARRAY_VEC_SIZE>),
    BitVec(InnerBitVec),
}

impl Default for SharedBitVec {
    fn default() -> Self {
        Self::Array(ArrayVec::new())
    }
}

impl Clone for SharedBitVec {
    fn clone(&self) -> Self {
        match self {
            Self::Array(terms) => Self::Array(terms.clone()),
            Self::BitVec(segments) => Self::BitVec(segments.clone()),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        match (self, source) {
            (SharedBitVec::Array(self_terms), SharedBitVec::Array(source_terms)) => {
                self_terms.clone_from(source_terms);
            }
            (SharedBitVec::BitVec(self_inner), SharedBitVec::BitVec(source_inner)) => {
                self_inner.clone_from(source_inner);
            }
            (this, _) => *this = source.clone(),
        }
    }
}

#[derive(Default, PartialEq, Eq, Debug)]
pub struct InnerBitVec {
    segments: SmallVec<[Segment; BACKING_ARRAY_SIZE]>,
    len: u32,
}

impl Clone for InnerBitVec {
    fn clone(&self) -> Self {
        Self {
            segments: self.segments.clone(),
            len: self.len,
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.segments.clone_from(&source.segments);
        self.len = source.len;
    }
}

impl InnerBitVec {
    fn contains(&self, term: Term) -> bool {
        let start_index = start_index_of_term(term);
        match self
            .segments
            .binary_search_by_key(&start_index, |segment| segment.start_index)
        {
            Ok(i) => {
                let chunk_index = index_in_chunk(term);
                self.segments[i].chunk[chunk_index]
            }
            Err(_) => false,
        }
    }

    fn insert(&mut self, term: Term) -> bool {
        let start_index = start_index_of_term(term);
        let index_in_chunk = index_in_chunk(term);

        let segment = match self
            .segments
            .binary_search_by_key(&start_index, |segment| segment.start_index)
        {
            Ok(i) => {
                if self.segments[i].chunk[index_in_chunk] {
                    return false;
                }
                &mut self.segments[i]
            }
            Err(i) => {
                self.segments.insert(
                    i,
                    Segment {
                        start_index,
                        chunk: Rc::new(TinyBitSet::new()),
                    },
                );
                &mut self.segments[i]
            }
        };

        Rc::make_mut(&mut segment.chunk).insert(index_in_chunk);
        self.len += 1;
        true
    }

    fn remove(&mut self, term: Term) -> bool {
        let start_index = start_index_of_term(term);
        let index_in_chunk = index_in_chunk(term);

        let segment = match self
            .segments
            .binary_search_by_key(&start_index, |segment| segment.start_index)
        {
            Ok(i) => {
                if !self.segments[i].chunk[index_in_chunk] {
                    return false;
                }
                &mut self.segments[i]
            }
            Err(_) => {
                return false;
            }
        };

        Rc::make_mut(&mut segment.chunk).remove(index_in_chunk);
        self.len -= 1;
        true
    }
}

fn start_index_of_term(term: Term) -> Term {
    term / ELEMS_IN_CHUNK
}

fn index_in_chunk(term: Term) -> usize {
    (term % ELEMS_IN_CHUNK) as usize
}

fn chunk_diff(big: &Chunk, small: &Chunk) -> usize {
    big.len() - small.len()
}

impl TermSetTrait for SharedBitVec {
    type Term = u32;

    fn new() -> Self {
        Default::default()
    }

    fn len(&self) -> usize {
        match self {
            SharedBitVec::Array(terms) => terms.len(),
            SharedBitVec::BitVec(segments) => segments.len as usize,
        }
    }

    fn contains(&self, term: Self::Term) -> bool {
        match self {
            SharedBitVec::Array(terms) => terms.binary_search(&term).is_ok(),
            SharedBitVec::BitVec(segments) => segments.contains(term),
        }
    }

    fn remove(&mut self, term: Self::Term) -> bool {
        match self {
            SharedBitVec::Array(terms) => {
                let Ok(index) = terms.binary_search(&term) else {
                    return false;
                };
                terms.remove(index);
                true
            }
            SharedBitVec::BitVec(inner) => inner.remove(term),
        }
    }

    fn insert(&mut self, term: Self::Term) -> bool {
        match self {
            SharedBitVec::Array(terms) => {
                let Err(index) = terms.binary_search(&term) else {
                    return false;
                };

                let Err(_) = terms.try_insert(index, term) else {
                    return true;
                };

                // Change to bitvec
                let mut inner = InnerBitVec::default();
                for &mut term in terms {
                    inner.insert(term);
                }
                inner.insert(term);
                *self = SharedBitVec::BitVec(inner);

                true
            }
            SharedBitVec::BitVec(inner) => inner.insert(term),
        }
    }

    fn union_assign(&mut self, other: &Self) {
        match (self, other) {
            (this @ SharedBitVec::Array(_), SharedBitVec::Array(other_terms)) => {
                // TODO: Help us Polonius, you are our only hope
                let self_terms = match this {
                    SharedBitVec::Array(terms) => terms,
                    _ => unreachable!(),
                };

                let mut merged: ArrayVec<_, ARRAY_VEC_SIZE> = ArrayVec::new();
                let mut self_idx = 0;
                let mut other_idx = 0;
                while (self_idx < self_terms.len() || other_idx < other_terms.len())
                    && !merged.is_full()
                {
                    match (self_terms.get(self_idx), other_terms.get(other_idx)) {
                        (Some(&self_term), Some(&other_term)) => {
                            if self_term < other_term {
                                merged.push(self_term);
                                self_idx += 1;
                            } else if self_term > other_term {
                                merged.push(other_term);
                                other_idx += 1;
                            } else {
                                merged.push(self_term);
                                self_idx += 1;
                                other_idx += 1;
                            }
                        }
                        (Some(&self_term), None) => {
                            merged.push(self_term);
                            self_idx += 1;
                        }
                        (None, Some(&other_term)) => {
                            merged.push(other_term);
                            other_idx += 1;
                        }
                        (None, None) => unreachable!(),
                    }
                }

                if merged.is_full() {
                    let mut inner = InnerBitVec::default();
                    for &term in merged
                        .iter()
                        .chain(&self_terms[self_idx..])
                        .chain(&other_terms[other_idx..])
                    {
                        inner.insert(term);
                    }
                    *this = SharedBitVec::BitVec(inner);
                } else {
                    *this = SharedBitVec::Array(merged);
                }
            }
            (this @ SharedBitVec::Array(_), SharedBitVec::BitVec(_)) => {
                // TODO: Help us Polonius, you are our only hope
                let terms = match this {
                    SharedBitVec::Array(terms) => terms,
                    _ => unreachable!(),
                };

                let mut new_bitvec = other.clone();
                new_bitvec.union_assign(&SharedBitVec::Array(terms.clone()));
                *this = new_bitvec;
            }
            (SharedBitVec::BitVec(inner), SharedBitVec::Array(terms)) => {
                for &term in terms {
                    inner.insert(term);
                }
            }
            (SharedBitVec::BitVec(self_inner), SharedBitVec::BitVec(other_inner)) => {
                let self_segments = &mut self_inner.segments;
                let other_segments = &other_inner.segments;

                let mut queue = VecDeque::<Segment>::new();
                let mut self_idx = 0;
                let mut other_idx = 0;

                while self_idx < self_segments.len() || other_idx < other_segments.len() {
                    match (
                        self_segments.get_mut(self_idx),
                        other_segments.get(self_idx),
                    ) {
                        (Some(self_segment), Some(other_segment)) => {
                            if self_segment.start_index < other_segment.start_index {
                                if let Some(mut queue_segment) = queue.pop_front() {
                                    if self_segment.start_index > queue_segment.start_index {
                                        self_inner.len -= self_segment.len();
                                        self_inner.len += queue_segment.len();
                                        std::mem::swap(self_segment, &mut queue_segment);
                                        queue.push_back(queue_segment);
                                    } else {
                                        let new_chunk = *self_segment.chunk | *queue_segment.chunk;
                                        let new_count = chunk_diff(&new_chunk, &self_segment.chunk);
                                        if new_count > 0 {
                                            self_segment.chunk = Rc::new(new_chunk);
                                            self_inner.len += new_count as u32;
                                        }
                                    }
                                }
                                self_idx += 1;
                            } else if self_segment.start_index > other_segment.start_index {
                                if queue.front().map_or(true, |queue_segment| {
                                    other_segment.start_index < queue_segment.start_index
                                }) {
                                    let mut new_segment = other_segment.clone();
                                    self_inner.len -= self_segment.len();
                                    self_inner.len += new_segment.len();
                                    std::mem::swap(self_segment, &mut new_segment);
                                    queue.push_back(new_segment);
                                    other_idx += 1;
                                } else {
                                    let mut queue_segment = queue.pop_front().unwrap();
                                    if other_segment.start_index > queue_segment.start_index {
                                        self_inner.len -= self_segment.len();
                                        self_inner.len += queue_segment.len();
                                        std::mem::swap(self_segment, &mut queue_segment);
                                        queue.push_back(queue_segment);
                                    } else {
                                        let new_chunk = *other_segment.chunk | *queue_segment.chunk;
                                        let new_count = chunk_diff(&new_chunk, &self_segment.chunk);
                                        if new_count > 0 {
                                            self_segment.chunk = Rc::new(new_chunk);
                                            self_inner.len += new_count as u32;
                                        }
                                        other_idx += 1;
                                    }
                                }
                            } else {
                                let new_chunk = *self_segment.chunk | *other_segment.chunk;
                                let new_count = chunk_diff(&new_chunk, &self_segment.chunk);
                                if new_count > 0 {
                                    self_segment.chunk = Rc::new(new_chunk);
                                    self_inner.len += new_count as u32;
                                }
                                self_idx += 1;
                                other_idx += 1;
                            }
                        }
                        (Some(self_segment), None) => {
                            if let Some(mut queue_segment) = queue.pop_front() {
                                if self_segment.start_index > queue_segment.start_index {
                                    self_inner.len -= self_segment.len();
                                    self_inner.len += queue_segment.len();
                                    std::mem::swap(self_segment, &mut queue_segment);
                                    queue.push_back(queue_segment);
                                } else {
                                    let new_chunk = *self_segment.chunk | *queue_segment.chunk;
                                    let new_count = chunk_diff(&new_chunk, &self_segment.chunk);
                                    if new_count > 0 {
                                        self_segment.chunk = Rc::new(new_chunk);
                                        self_inner.len += new_count as u32;
                                    }
                                }
                            }
                            self_idx += 1;
                        }
                        (None, Some(other_segment)) => {
                            if queue.front().map_or(true, |queue_segment| {
                                other_segment.start_index < queue_segment.start_index
                            }) {
                                self_segments.push(other_segment.clone());
                                self_inner.len += other_segment.len();
                                other_idx += 1;
                            } else {
                                let queue_segment = queue.pop_front().unwrap();
                                if other_segment.start_index > queue_segment.start_index {
                                    self_segments.push(queue_segment);
                                } else {
                                    let new_chunk = *other_segment.chunk | *queue_segment.chunk;
                                    let new_count = new_chunk.len();
                                    if new_count > 0 {
                                        self_segments.push(Segment {
                                            start_index: other_segment.start_index,
                                            chunk: Rc::new(new_chunk),
                                        });
                                        self_inner.len += new_count as u32;
                                    }
                                    other_idx += 1;
                                }
                                other_idx += 1;
                            }
                        }
                        (None, None) => unreachable!(),
                    }
                }
            }
        }
    }

    fn extend<T: Iterator<Item = Self::Term>>(&mut self, other: T) {
        for term in other {
            self.insert(term);
        }
    }

    fn difference(&self, other: &Self) -> Self {
        match (self, other) {
            (SharedBitVec::Array(self_terms), SharedBitVec::Array(other_terms)) => {
                let mut diff = ArrayVec::new();
                let mut self_iter = self_terms.iter();
                let mut other_idx = 0;
                while let Some(&term) = self_iter.next() {
                    while other_idx < other_terms.len() && other_terms[other_idx] < term {
                        other_idx += 1;
                    }
                    if other_idx == other_terms.len() {
                        diff.push(term);
                        diff.extend(self_iter.copied());
                        break;
                    }

                    if other_terms[other_idx] != term {
                        diff.push(term);
                    }
                }
                Self::Array(diff)
            }
            (SharedBitVec::Array(self_terms), SharedBitVec::BitVec(other_inner)) => {
                let mut diff = ArrayVec::new();
                for &term in self_terms {
                    if !other_inner.contains(term) {
                        diff.push(term);
                    }
                }
                Self::Array(diff)
            }
            (SharedBitVec::BitVec(self_inner), SharedBitVec::Array(other_terms)) => {
                let mut diff = self_inner.clone();
                for &term in other_terms {
                    diff.remove(term);
                }
                Self::BitVec(diff)
            }
            (SharedBitVec::BitVec(self_inner), SharedBitVec::BitVec(other_inner)) => {
                let other_segments = &other_inner.segments;
                let mut diff = InnerBitVec::default();
                let mut self_iter = self_inner.segments.iter();
                let mut other_idx = 0;
                while let Some(segment) = self_iter.next() {
                    match other_segments[other_idx..]
                        .binary_search_by_key(&segment.start_index, |s| s.start_index)
                    {
                        Ok(i) => {
                            other_idx += i + 1;
                            let other_segment = &other_segments[other_idx - 1];
                            let new_chunk = *segment.chunk & !*other_segment.chunk;
                            let new_chunk_len = new_chunk.len() as u32;
                            if new_chunk_len == 0 {
                                continue;
                            }
                            diff.len += new_chunk_len;
                            if *segment.chunk == new_chunk {
                                diff.segments.push(segment.clone());
                            } else {
                                diff.segments.push(Segment {
                                    start_index: segment.start_index,
                                    chunk: Rc::new(new_chunk),
                                });
                            }
                        }
                        Err(i) => {
                            other_idx += i;
                            diff.len += segment.len();
                            diff.segments.push(segment.clone());
                        }
                    };

                    if other_idx == other_segments.len() {
                        diff.segments.extend(self_iter.cloned());
                        break;
                    }
                }
                Self::BitVec(diff)
            }
        }
    }

    fn iter(&self) -> impl Iterator<Item = Self::Term> {
        match self {
            SharedBitVec::Array(terms) => Either::Left(terms.iter().copied()),
            SharedBitVec::BitVec(inner) => Either::Right(
                inner
                    .segments
                    .iter()
                    .map(|s| {
                        s.chunk
                            .iter()
                            .map(|i| i as u32 + s.start_index * CHUNK_SIZE as u32)
                    })
                    .flatten(),
            ),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use arrayvec::ArrayVec;

    #[test]
    fn test_difference() {
        let bitvec1 = SharedBitVec::Array(ArrayVec::try_from([1, 2, 3, 4, 5].as_slice()).unwrap());
        let bitvec2 = SharedBitVec::Array(ArrayVec::try_from([3, 4].as_slice()).unwrap());
        let expected = SharedBitVec::Array(ArrayVec::try_from([1, 2, 5].as_slice()).unwrap());
        assert_eq!(bitvec1.difference(&bitvec2), expected);
    }

    #[test]
    fn test_iter() {
        let bitvec = SharedBitVec::Array(ArrayVec::try_from([1, 2, 3, 4, 5].as_slice()).unwrap());
        let mut iter = bitvec.iter();
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_extend() {
        let mut bitvec = SharedBitVec::Array(ArrayVec::try_from([1, 2, 5].as_slice()).unwrap());
        bitvec.extend([4, 3].into_iter());
        assert_eq!(
            bitvec,
            SharedBitVec::Array(ArrayVec::try_from([1, 2, 3, 4, 5].as_slice()).unwrap())
        );
    }
}
