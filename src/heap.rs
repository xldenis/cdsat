use ::std::collections::BTreeSet;

use creusot_contracts::{*, invariant::Invariant};
use creusot_contracts::logic::FSet;
use crate::trail::{TrailIndex, *};

impl creusot_contracts::ShallowModel for ConflictHeap {
    type ShallowModelTy = FSet<TrailIndex>;

    #[ghost]
    #[open(self)]
    #[trusted]
    fn shallow_model(self) -> Self::ShallowModelTy {
        absurd
    }
}

#[trusted]
pub(crate) struct ConflictHeap(BTreeSet<TrailIndex>);

impl ConflictHeap {
    #[trusted]
    #[ensures(result@ == FSet::EMPTY)]
    pub fn new() -> Self {
        ConflictHeap(BTreeSet::new())
    }

    #[trusted]
    #[ensures((^self)@ == (self@).insert(e))]
    pub fn insert(&mut self, e: TrailIndex) -> bool {
        self.0.insert(e)
    }

    #[trusted]
    #[ensures(match result {
        Some(a) => self@.contains(*a) && set_max(self@) == *a,
        None => self@ == FSet::EMPTY
    })]
    pub fn last(&self) -> Option<&TrailIndex> {
        self.0.last()
    }

    #[trusted]
    #[ensures(((self@) == FSet::EMPTY) == (result == None))]
    #[ensures(forall<a : _> result == Some(a) ==>
        (^self)@ == (self@).remove(a) && (self@).contains(a) &&
        (forall<other : TrailIndex> ((^self)@).contains(other) ==> other <= a)
    )]
    pub fn pop_last(&mut self) -> Option<TrailIndex> {
        self.0.pop_last()
    }

    #[trusted]
    #[ensures(forall<e : _> self@.contains(e) == result@.contains(e))]
    #[ensures(forall<i : _> 0 <= i && i < result@.len() ==> self@.contains(result@[i]))]
    #[ensures(result@.len() == self@.len())]
    #[ensures(seq_unique(result@))]
    pub fn into_vec(self) -> Vec<TrailIndex> {
        // self.0.into_vec()
        self.0.into_iter().collect()
    }
}

struct NaiveHeap(Vec<TrailIndex>);

impl Invariant for NaiveHeap {
    #[predicate]
    #[open(crate)]
    fn invariant(self) -> bool {
        seq_unique(self.0.shallow_model()) && self.0.shallow_model().sorted()
    }
}

impl NaiveHeap {
    #[ensures(result@ == FSet::EMPTY)]
    fn new() -> Self {
        NaiveHeap(Vec::new())
    }

    // #[trusted]
    #[ensures((^self)@ == (self@).insert(e))]
    fn insert(&mut self, e: TrailIndex) -> bool {
        let old = gh! { * self };
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
    fn last(&self) -> Option<&TrailIndex> {
        self.0.get(self.0.len() - 1)
    }

    #[ensures(((self@) == FSet::EMPTY) == (result == None))]
    #[ensures(forall<a : _> result == Some(a) ==>
        (^self)@ == (self@).remove(a) && (self@).contains(a) &&
        (forall<other : TrailIndex> ((^self)@).contains(other) ==> other <= a)
    )]
    fn pop_last(&mut self) -> Option<TrailIndex> {
        self.0.pop()
    }

    #[ensures(forall<e : _> self@.contains(e) == result@.contains(e))]
    #[ensures(forall<i : _> 0 <= i && i < result@.len() ==> self@.contains(result@[i]))]
    #[ensures(result@.len() == self@.len())]
    #[ensures(seq_unique(result@))]
    fn into_vec(self) -> Vec<TrailIndex> {
       self.0
    }
}

impl creusot_contracts::ShallowModel for NaiveHeap {
    type ShallowModelTy = FSet<TrailIndex>;

    #[ghost]
    #[open(self)]
    #[ensures(forall<x : _> self.0@.contains(x) == result.contains(x))]
    fn shallow_model(self) -> Self::ShallowModelTy {
        to_set(self.0.shallow_model())
    }
}

#[ghost]
#[ensures(forall<x : _> s.contains(x) == result.contains(x))]
#[variant(s.len())]
fn to_set<T>(s : Seq<T>) -> FSet<T> {
    if s == Seq::EMPTY {
        FSet::EMPTY
    } else {
        to_set(s.subsequence(1, s.len())).insert(s[0])
    }
}