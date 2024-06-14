use std::hash::Hash;
use std::mem;
use std::rc::Rc;

use either::Either;
use hashbrown::HashMap;
use serde::Serialize;

use super::TermSetTrait;

#[derive(PartialEq, Eq, Clone, Default, Debug)]
pub struct RcTermSet<S>(Option<Rc<S>>);

impl<S: Clone + Default> RcTermSet<S> {
    fn populate_rc(&mut self) -> &mut S {
        Rc::make_mut(self.0.get_or_insert_with(Default::default))
    }
}

impl<S> TermSetTrait for RcTermSet<S>
where
    S: TermSetTrait + Eq + Default,
    S::Term: Eq + Hash,
{
    type Term = S::Term;

    fn new() -> Self {
        Self(None)
    }

    fn len(&self) -> usize {
        match &self.0 {
            Some(set) => set.len(),
            None => 0,
        }
    }

    fn contains(&self, term: Self::Term) -> bool {
        match &self.0 {
            Some(set) => set.contains(term),
            None => todo!(),
        }
    }

    fn remove(&mut self, term: Self::Term) -> bool {
        match &mut self.0 {
            Some(set) => Rc::make_mut(set).remove(term),
            None => false,
        }
    }

    fn insert(&mut self, term: Self::Term) -> bool {
        self.populate_rc().insert(term)
    }

    fn union_assign(&mut self, other: &Self) {
        if self.len() == 0 {
            self.0 = other.0.clone();
            return;
        }
        let Some(other_s) = &other.0 else {
            return;
        };
        self.populate_rc().union_assign(other_s);
        if self.len() == other.len() {
            self.0 = other.0.clone();
        }
    }

    fn intersection_assign(&mut self, other: &Self) {
        if self.len() == 0 {
            return;
        }
        let Some(other_s) = &other.0 else {
            self.0 = None;
            return;
        };
        self.populate_rc().intersection_assign(other_s);
        if self.len() == other.len() {
            self.0 = other.0.clone();
        }
    }

    fn extend<T: Iterator<Item = Self::Term>>(&mut self, other: T) {
        self.populate_rc().extend(other);
    }

    fn iter(&self) -> impl Iterator<Item = Self::Term> {
        match &self.0 {
            Some(set) => Either::Left(set.iter()),
            None => Either::Right(None.into_iter()),
        }
    }

    fn difference(&self, other: &Self) -> Self {
        let Some(self_s) = &self.0 else {
            return Self::new();
        };
        let Some(other_s) = &other.0 else {
            return self.clone();
        };
        Self(Some(Rc::new(self_s.difference(other_s))))
    }

    fn weak_difference(&self, other: &Self) -> Self {
        let Some(self_s) = &self.0 else {
            return Self::new();
        };
        let Some(other_s) = &other.0 else {
            return self.clone();
        };
        Self(Some(Rc::new(self_s.weak_difference(other_s))))
    }

    fn is_empty(&self) -> bool {
        match &self.0 {
            Some(set) => set.is_empty(),
            None => true,
        }
    }

    fn overlaps(&self, other: &Self) -> bool {
        let Some(self_s) = &self.0 else {
            return false;
        };
        let Some(other_s) = &other.0 else {
            return false;
        };
        self_s.overlaps(other_s)
    }

    fn deduplicate_subset_pair(set1: &Self, set2: &mut Self) {
        let Some(set1_s) = &set1.0 else {
            return;
        };
        let Some(set2_s) = &mut set2.0 else {
            return;
        };
        if Rc::ptr_eq(set1_s, set2_s) {
            return;
        }
        if set1_s.len() == set2_s.len() {
            set2.clone_from(set1);
            return;
        }
        S::deduplicate_subset_pair(&set1_s, Rc::make_mut(set2_s));
    }

    fn deduplicate<'a>(sets: impl Iterator<Item = &'a mut Self>)
    where
        Self: 'a,
    {
        let mut set_dups: Vec<_> = get_duplicates(sets.filter_map(|set| set.0.as_mut()), |s| {
            (s.len(), s.iter().next())
        })
        .collect();

        S::deduplicate(set_dups.iter_mut().map(|(s, _)| Rc::make_mut(s)));

        for (set, dups) in set_dups {
            for dup in dups {
                *dup = (*set).clone();
            }
        }
    }

    fn get_deduplicate_stats<'a>(
        sets: impl Iterator<Item = &'a Self>,
    ) -> Box<dyn erased_serde::Serialize>
    where
        Self: 'a,
    {
        Box::new(RcDedupStats {
            set_stats: S::get_deduplicate_stats(sets.filter_map(|s| s.0.as_ref().map(Rc::as_ref))),
        })
    }
}

#[derive(Serialize)]
pub struct RcDedupStats<T: erased_serde::Serialize> {
    #[serde(flatten)]
    set_stats: T,
}

pub fn deduplicate<'a, T, K, F1, F2>(
    elems: impl Iterator<Item = &'a mut T>,
    mut key_fn: F1,
    mut dedup_fn: F2,
) where
    T: Eq + 'a,
    K: PartialEq + Eq + Hash,
    F1: FnMut(&T) -> K,
    F2: FnMut(&mut T, &T),
{
    let mut unique_sets_map = HashMap::<K, Vec<&'a T>>::new();
    for elem in elems {
        let similar_sets = unique_sets_map.entry(key_fn(elem)).or_default();
        let mut found_dup = false;
        for s2 in similar_sets.iter() {
            if elem == *s2 {
                dedup_fn(elem, s2);
                found_dup = true;
                break;
            }
        }
        if !found_dup {
            similar_sets.push(elem);
        }
    }
}

pub fn get_duplicates<T, K, F>(
    elems: impl Iterator<Item = T>,
    mut key_fn: F,
) -> impl Iterator<Item = (T, Vec<T>)>
where
    T: Eq,
    F: FnMut(&T) -> K,
    K: PartialEq + Eq + Hash,
{
    let mut unique_sets_map = HashMap::<K, Vec<(T, Vec<T>)>>::new();
    for elem in elems {
        let similar_sets = unique_sets_map.entry(key_fn(&elem)).or_default();
        let mut val = Some(elem);
        for (s2, duplicates) in similar_sets.as_mut_slice() {
            let Some(inner) = &val else { unreachable!() };
            if inner == s2 {
                duplicates.push((mem::take(&mut val)).unwrap());
                break;
            }
        }
        if let Some(val) = val {
            similar_sets.push((val, vec![]));
        }
    }

    unique_sets_map.into_values().flatten()
}
