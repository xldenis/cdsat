use std::collections::BTreeSet;
use std::ops::Index;

use creusot_std::{prelude::*, invariant::Invariant};
use creusot_std::logic::FSet;
use crate::trail::{TrailIndex, *};

pub(crate) struct ConflictHeap(Vec<TrailIndex>);

impl Invariant for ConflictHeap {
    #[logic(open)]
    fn invariant(self) -> bool {
        seq_unique(self.0.shallow_model()) && self.0.shallow_model().sorted()
    }
}

impl ConflictHeap {
    #[ensures(result@ == FSet::EMPTY)]
    pub(crate) fn new() -> Self {
        ConflictHeap(Vec::new())
    }

    // #[trusted]
    #[ensures((^self)@ == (self@).insert(e))]
    pub(crate) fn insert(&mut self, e: TrailIndex) -> bool {
        let old = snapshot! { * self };
        let mut i = 0;
        #[invariant(forall<j : _> 0 <= j && j < i@ ==>  self.0[j] < e)]
        while i < self.0.len() {
            if e < self.0[i] {
                self.0.insert(i, e);
                proof_assert!(forall<a : _> old@.contains(a) ==> self@.contains(a));
                proof_assert!(forall<a : _> self@.contains(a) ==> old@.contains(a) || a == e);
                proof_assert!(self@.ext_eq(old@.insert(e)));

                return true;
            } else if e == self.0[i] {
                return false;
            }

            i += 1;
        }
        proof_assert!(!self.0@.contains(e));
        proof_assert!(!self@.contains(e));
        self.0.push(e);
        proof_assert!(forall<a : _> old.0@.contains(a) ==> self.0@.contains(a));
        proof_assert!(forall<a : _> old@.contains(a) ==> self@.contains(a));
        proof_assert!(forall<a : _> self@.contains(a) ==> old@.contains(a) || a == e);
        proof_assert!(self@.ext_eq(old@.insert(e)));
        true
    }

    #[ensures(
        match result {
            Some(a) => self@.contains(*a) && set_max(self@) == *a,
            None => self@ == FSet::EMPTY
        })]
    pub(crate) fn last(&self) -> Option<&TrailIndex> {
        if self.0.len() == 0 {
            return None;
        }
        self.0.get(self.0.len() - 1)
    }

    #[ensures(((self@) == FSet::EMPTY) == (result == None))]
    #[ensures(forall<a : _> result == Some(a) ==>
        (^self)@ == (self@).remove(a) && (self@).contains(a) &&
        (forall<other : TrailIndex> ((^self)@).contains(other) ==> other <= a)
    )]
    pub(crate) fn pop_last(&mut self) -> Option<TrailIndex> {
        self.0.pop()
    }

    #[ensures(forall<e : _> self@.contains(e) == result@.contains(e))]
    #[ensures(forall<i : _> 0 <= i && i < result@.len() ==> self@.contains(result@[i]))]
    #[ensures(seq_unique(result@))]
    pub(crate) fn into_vec(self) -> Vec<TrailIndex> {
       self.0
    }
}

impl View for ConflictHeap {
    type ViewTy = FSet<TrailIndex>;

    #[logic(open)]
    #[ensures(forall<x : _> self.0@.contains(x) == result.contains(x))]
    fn view(self) -> Self::ViewTy {
        to_set(self.0.view())
    }
}

#[logic]
#[ensures(forall<x : _> s.contains(x) == result.contains(x))]
#[variant(s.len())]
fn to_set<T: creusot_std::ghost::Plain>(s : Seq<T>) -> FSet<T> {
    if s.is_empty_ghost() {
        FSet::new().into_inner()
    } else {
        let seq  = s.subsequence(1, s.len_ghost());
        let mut out = to_set(seq);
        out.insert_ghost(s[Int::new(0).into_inner()]);
        out
    }
}
