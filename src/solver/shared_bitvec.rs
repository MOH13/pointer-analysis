use std::collections::VecDeque;
use std::ops::{BitAnd, BitOr};
use std::rc::Rc;

use arrayvec::ArrayVec;
use either::Either;
use smallvec::SmallVec;
use tinybitset::TinyBitSet;

use super::TermSetTrait;

type Term = u32;

const BLOCKS_IN_CHUNK: usize = 24;
const ELEMS_IN_CHUNK: Term = u64::BITS * BLOCKS_IN_CHUNK as Term;
const BACKING_ARRAY_SIZE: usize = 2;

// Maximal size of a sorted list of u32 terms so that it has the same size as InnerBitVec
const ARRAY_VEC_SIZE: usize = 14; // wrong: (std::mem::size_of::<InnerBitVec>() - 4) / 4 - 1;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Segment {
    start_index: Term,
    chunk: Rc<Chunk>,
}

impl Segment {
    fn len(&self) -> u32 {
        self.chunk.len
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
struct Chunk {
    data: TinyBitSet<u64, BLOCKS_IN_CHUNK>,
    len: u32,
}

impl Chunk {
    fn difference(self, rhs: Self) -> Self {
        let new_data = self.data & !rhs.data;
        Chunk {
            data: new_data,
            len: new_data.len() as u32,
        }
    }
}

impl BitOr for Chunk {
    type Output = Chunk;

    fn bitor(self, rhs: Self) -> Self::Output {
        let new_data = self.data | rhs.data;
        Chunk {
            data: new_data,
            len: new_data.len() as u32,
        }
    }
}

impl BitAnd for Chunk {
    type Output = Chunk;

    fn bitand(self, rhs: Self) -> Self::Output {
        let new_data = self.data & rhs.data;
        Chunk {
            data: new_data,
            len: new_data.len() as u32,
        }
    }
}

#[derive(Eq, Debug)]
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

impl PartialEq for SharedBitVec {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Array(terms1), Self::Array(term2)) => terms1 == term2,
            (Self::BitVec(inner1), Self::BitVec(inner2)) => inner1 == inner2,
            (Self::BitVec(inner), Self::Array(terms))
            | (Self::Array(terms), Self::BitVec(inner)) => {
                if terms.len() != inner.len as usize {
                    return false;
                }
                for term in terms {
                    if !inner.contains(*term) {
                        return false;
                    }
                }
                true
            }
        }
    }
}

#[derive(Default, Eq, Debug)]
pub struct InnerBitVec {
    segments: SmallVec<[Segment; BACKING_ARRAY_SIZE]>,
    len: u32,
    last_accessed_chunk_index: u32,
}

impl Clone for InnerBitVec {
    fn clone(&self) -> Self {
        Self {
            segments: self.segments.clone(),
            len: self.len,
            last_accessed_chunk_index: 0,
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
                self.segments[i].chunk.data[chunk_index]
            }
            Err(_) => false,
        }
    }

    fn insert(&mut self, term: Term) -> bool {
        let start_index = start_index_of_term(term);
        let index_in_chunk = index_in_chunk(term);

        let segment = if self.segments.len() > self.last_accessed_chunk_index as usize
            && self.segments[self.last_accessed_chunk_index as usize].start_index == start_index
        {
            if self.segments[self.last_accessed_chunk_index as usize]
                .chunk
                .data[index_in_chunk]
            {
                return false;
            }
            &mut self.segments[self.last_accessed_chunk_index as usize]
        } else {
            match self
                .segments
                .binary_search_by_key(&start_index, |segment| segment.start_index)
            {
                Ok(i) => {
                    if self.segments[i].chunk.data[index_in_chunk] {
                        return false;
                    }
                    self.last_accessed_chunk_index = i as u32;
                    &mut self.segments[i]
                }
                Err(i) => {
                    self.segments.insert(
                        i,
                        Segment {
                            start_index,
                            chunk: Rc::default(),
                        },
                    );
                    self.last_accessed_chunk_index = i as u32;
                    &mut self.segments[i]
                }
            }
        };

        let chunk = Rc::make_mut(&mut segment.chunk);
        chunk.data.insert(index_in_chunk);
        chunk.len += 1;
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
            Ok(i) => &mut self.segments[i],
            Err(_) => return false,
        };

        if !segment.chunk.data[index_in_chunk] {
            return false;
        }

        let chunk = Rc::make_mut(&mut segment.chunk);
        chunk.data.remove(index_in_chunk);
        chunk.len -= 1;
        self.len -= 1;
        true
    }
}

impl PartialEq for InnerBitVec {
    fn eq(&self, other: &Self) -> bool {
        self.segments == other.segments
    }
}

fn start_index_of_term(term: Term) -> Term {
    term / ELEMS_IN_CHUNK
}

fn index_in_chunk(term: Term) -> usize {
    (term % ELEMS_IN_CHUNK) as usize
}

fn chunk_diff(big: &Chunk, small: &Chunk) -> u32 {
    big.len - small.len
}

/// For debugging
// #[inline(never)]
// fn new_never_inline<T>(v: T) -> Rc<T> {
//     Rc::new(v)
// }

// /// For debugging
// #[inline(never)]
// fn make_mut_never_inline<T: Clone>(v: &mut Rc<T>) -> &mut T {
//     Rc::make_mut(v)
// }

impl TermSetTrait for SharedBitVec {
    type Term = u32;

    fn new() -> Self {
        Default::default()
    }

    fn len(&self) -> usize {
        match self {
            SharedBitVec::Array(terms) => terms.len(),
            SharedBitVec::BitVec(inner) => inner.len as usize,
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
                if other_terms.len() == 0 {
                    return;
                }

                // TODO: Help us Polonius, you are our only hope
                let self_terms = match this {
                    SharedBitVec::Array(terms) => terms,
                    _ => unreachable!(),
                };

                let mut merged: ArrayVec<_, ARRAY_VEC_SIZE> = ArrayVec::new();
                let mut self_idx = 0;
                let mut other_idx = 0;
                while self_idx < self_terms.len() || other_idx < other_terms.len() {
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
                        return;
                    }
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

                *this = SharedBitVec::Array(merged);
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

                if other_segments.len() == 0 {
                    return;
                }

                let start_index = match self_segments
                    .binary_search_by_key(&other_segments[0].start_index, |s| s.start_index)
                {
                    Ok(i) => i,
                    Err(i) => i,
                };

                let mut self_iter = self_segments[start_index..].iter_mut();
                let mut other_idx = 0;

                for self_segment in &mut self_iter {
                    let Some(other_segment) = other_segments.get(other_idx) else {
                        if let Some(mut queue_segment) = queue.pop_front() {
                            // queue_segment always comes from earlier in self_segment
                            debug_assert!(self_segment.start_index > queue_segment.start_index);
                            self_inner.len -= self_segment.len();
                            self_inner.len += queue_segment.len();
                            std::mem::swap(self_segment, &mut queue_segment);
                            queue.push_back(queue_segment);
                            continue;
                        } else {
                            return;
                        }
                    };

                    if queue
                        .front()
                        .is_some_and(|q| q.start_index <= other_segment.start_index)
                    {
                        let mut queue_segment = queue.pop_front().unwrap();
                        // queue_segment always comes from earlier in self_segment
                        debug_assert!(self_segment.start_index > queue_segment.start_index);
                        self_inner.len -= self_segment.len();
                        self_inner.len += queue_segment.len();
                        std::mem::swap(self_segment, &mut queue_segment);
                        queue.push_back(queue_segment);
                    }

                    if self_segment.start_index > other_segment.start_index {
                        let mut new_segment = other_segment.clone();
                        self_inner.len -= self_segment.len();
                        self_inner.len += new_segment.len();
                        std::mem::swap(self_segment, &mut new_segment);
                        queue.push_back(new_segment);
                        other_idx += 1;
                    } else if self_segment.start_index == other_segment.start_index {
                        if Rc::ptr_eq(&self_segment.chunk, &other_segment.chunk) {
                            other_idx += 1;
                            continue;
                        }
                        let new_chunk = *self_segment.chunk | *other_segment.chunk;
                        let new_count = chunk_diff(&new_chunk, &self_segment.chunk);
                        if new_chunk.len == other_segment.chunk.len {
                            self_segment.chunk = other_segment.chunk.clone();
                            self_inner.len += new_count as u32;
                        } else if new_count > 0 {
                            *Rc::make_mut(&mut self_segment.chunk) = new_chunk;
                            self_inner.len += new_count as u32;
                        }
                        other_idx += 1;
                    }
                }

                'other_loop: for other_segment in &other_segments[other_idx..] {
                    while let Some(queue_segment) = queue.front() {
                        if queue_segment.start_index > other_segment.start_index {
                            break;
                        }
                        let queue_segment = queue.pop_front().unwrap();
                        if queue_segment.start_index < other_segment.start_index {
                            self_inner.len += queue_segment.len();
                            self_segments.push(queue_segment);
                        } else {
                            let new_chunk = *other_segment.chunk | *queue_segment.chunk;
                            self_inner.len += new_chunk.len;
                            self_segments.push(Segment {
                                start_index: other_segment.start_index,
                                chunk: Rc::new(new_chunk),
                            });
                            continue 'other_loop;
                        }
                    }
                    self_inner.len += other_segment.len();
                    self_segments.push(other_segment.clone());
                }

                for queue_segment in queue.drain(..) {
                    self_inner.len += queue_segment.len();
                    self_segments.push(queue_segment);
                }
            }
        }
    }

    fn intersection_assign(&mut self, other: &Self) {
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
                while self_idx < self_terms.len() || other_idx < other_terms.len() {
                    match (self_terms.get(self_idx), other_terms.get(other_idx)) {
                        (Some(&self_term), Some(&other_term)) => {
                            if self_term < other_term {
                                self_idx += 1;
                            } else if self_term > other_term {
                                other_idx += 1;
                            } else {
                                merged.push(self_term);
                                self_idx += 1;
                                other_idx += 1;
                            }
                        }
                        _ => break,
                    }
                }

                *this = SharedBitVec::Array(merged);
            }
            (this @ SharedBitVec::Array(_), SharedBitVec::BitVec(_)) => {
                // TODO: Help us Polonius, you are our only hope
                let terms = match this {
                    SharedBitVec::Array(terms) => terms,
                    _ => unreachable!(),
                };

                terms.retain(|term| other.contains(*term));
            }
            (this @ SharedBitVec::BitVec(_), SharedBitVec::Array(_)) => {
                let mut new_array_vec = other.clone();
                new_array_vec.intersection_assign(this);
                *this = new_array_vec;
            }
            (SharedBitVec::BitVec(self_inner), SharedBitVec::BitVec(other_inner)) => {
                let self_segments = &mut self_inner.segments;
                let other_segments = &other_inner.segments;

                if other_segments.len() == 0 {
                    return;
                }

                let start_index = match self_segments
                    .binary_search_by_key(&other_segments[0].start_index, |s| s.start_index)
                {
                    Ok(i) => i,
                    Err(i) => i,
                };

                let mut other_idx = 0;
                let mut cur_write_idx = 0;

                for self_idx in start_index..self_segments.len() {
                    let self_segment = &self_segments[self_idx];
                    self_inner.len -= self_segment.chunk.len;
                    match other_segments[other_idx..]
                        .binary_search_by_key(&self_segment.start_index, |s| s.start_index)
                    {
                        Ok(idx) => {
                            let new_chunk = *self_segment.chunk & *other_segments[idx].chunk;
                            if &new_chunk == self_segment.chunk.as_ref() {
                                self_inner.len += new_chunk.len;
                                cur_write_idx += 1;
                            } else if new_chunk.len > 0 {
                                *Rc::make_mut(&mut self_segments[cur_write_idx].chunk) = new_chunk;
                                self_inner.len += new_chunk.len;
                                cur_write_idx += 1;
                            }
                            other_idx = idx;
                        }
                        Err(idx) => {
                            other_idx = idx;
                        }
                    }
                }
                self_segments.truncate(cur_write_idx);
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
                            if Rc::ptr_eq(&segment.chunk, &other_segment.chunk) {
                                continue;
                            }
                            let new_chunk = segment.chunk.difference(*other_segment.chunk);
                            let new_chunk_len = new_chunk.len;
                            if new_chunk_len == 0 {
                                continue;
                            }
                            diff.len += new_chunk_len;
                            if segment.chunk.data == new_chunk.data {
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
                        for segment in self_iter.cloned() {
                            diff.len += segment.len();
                            diff.segments.push(segment);
                        }
                        break;
                    }
                }
                Self::BitVec(diff)
            }
        }
    }

    fn weak_difference(&self, other: &Self) -> Self {
        match (self, other) {
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
                            if Rc::ptr_eq(&segment.chunk, &other_segment.chunk) {
                                continue;
                            }
                            if segment.len() > other_segment.len() {
                                diff.len += segment.len();
                                diff.segments.push(segment.clone());
                            }
                        }
                        Err(i) => {
                            other_idx += i;
                            diff.len += segment.len();
                            diff.segments.push(segment.clone());
                        }
                    };

                    if other_idx == other_segments.len() {
                        for segment in self_iter.cloned() {
                            diff.len += segment.len();
                            diff.segments.push(segment);
                        }
                        break;
                    }
                }
                Self::BitVec(diff)
            }
            _ => self.difference(other),
        }
    }

    fn iter(&self) -> impl Iterator<Item = Self::Term> {
        match self {
            SharedBitVec::Array(terms) => Either::Left(terms.iter().copied()),
            SharedBitVec::BitVec(inner) => Either::Right(inner.segments.iter().flat_map(|s| {
                s.chunk
                    .data
                    .iter()
                    .map(|i| i as Term + s.start_index * ELEMS_IN_CHUNK as Term)
            })),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use arrayvec::ArrayVec;
    use quickcheck_macros::quickcheck;

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

    #[quickcheck]
    fn test_contains(terms: Vec<Term>) -> bool {
        let mut bitvec = SharedBitVec::new();
        for term in &terms {
            bitvec.insert(*term);
        }
        for term in &terms {
            if !bitvec.contains(*term) {
                return false;
            }
        }
        true
    }

    #[quickcheck]
    fn test_iter_quickcheck(terms: Vec<Term>) -> bool {
        let mut bitvec = SharedBitVec::new();
        for term in &terms {
            bitvec.insert(*term);
        }
        for term in bitvec.iter() {
            if !terms.contains(&term) {
                return false;
            }
        }
        true
    }

    #[quickcheck]
    fn test_union_assign_strictly_sorted(t1: Vec<Term>, t2: Vec<Term>) -> bool {
        let mut bitvec1 = SharedBitVec::new();
        let mut bitvec2 = SharedBitVec::new();
        for term in &t1 {
            bitvec1.insert(*term);
        }
        for term in &t2 {
            bitvec2.insert(*term);
        }
        bitvec1.union_assign(&bitvec2);

        match &bitvec1 {
            SharedBitVec::Array(_) => true,
            SharedBitVec::BitVec(inner) => inner
                .segments
                .windows(2)
                .all(|w| w[0].start_index < w[1].start_index),
        }
    }
}
