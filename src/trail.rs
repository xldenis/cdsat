use crate::theory::{self, Assign};
use ::std::ops::Index;
use creusot_contracts::{logic::*, vec, DeepModel, *};
use creusot_contracts::{Clone, PartialEq};
// use num_rational::BigRational;
//
#[cfg(not(creusot))]
struct FSet<T>(T);

// // Todo: Distinguish between boolean and fo assignments as an optim?
// #[cfg_attr(not(creusot), derive(Hash))]
#[cfg_attr(not(creusot), derive(Debug))]
#[derive(Clone, PartialEq, Eq, DeepModel)]
pub struct Assignment {
    // TODO: Make private
    pub term: Term,
    // TODO: Make private
    pub val: Value,
    // TODO: Make private
    pub reason: Reason,
    // TODO: Make private
    pub level: usize,
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Assignment {
    type ShallowModelTy = <Self as DeepModel>::DeepModelTy;

    #[open]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

// #[cfg_attr(not(creusot), derive(Hash))]
#[cfg_attr(not(creusot), derive(Debug))]
#[derive(Clone, PartialEq, Eq, DeepModel)]
pub enum Reason {
    Justified(Vec<TrailIndex>),
    Decision,
    Input,
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Reason {
    type ShallowModelTy = <Self as DeepModel>::DeepModelTy;

    #[open]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

#[cfg_attr(not(creusot), derive(Debug))]
#[derive(Clone, PartialEq, Eq, DeepModel)]
#[DeepModelTy = "theory::Sort"]
pub enum Sort {
    Boolean,
    Rational,
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Sort {
    type ShallowModelTy = theory::Sort;

    #[open]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

#[cfg_attr(not(creusot), derive(Debug))]
#[derive(Clone, PartialEq, Eq)]
pub enum Term {
    Variable(usize, Sort),
    Value(Value),
    Plus(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Conj(Box<Term>, Box<Term>),
    Neg(Box<Term>),
    Disj(Box<Term>, Box<Term>),
    Impl(Box<Term>, Box<Term>),
    // TODO: complete others
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Term {
    type ShallowModelTy = theory::Term;
    #[open]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

#[cfg(creusot)]
impl creusot_contracts::DeepModel for Term {
    type DeepModelTy = theory::Term;

    #[open]
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Term::Variable(v, s) => {
                theory::Term::Variable(theory::Var(v.deep_model(), s.deep_model()))
            }
            Term::Value(v) => theory::Term::Value(v.deep_model()),
            Term::Plus(l, r) => {
                theory::Term::Plus(Box::new((*l).deep_model()), Box::new((*r).deep_model()))
            }
            Term::Eq(l, r) => {
                theory::Term::Eq(Box::new((*l).deep_model()), Box::new((*r).deep_model()))
            }
            Term::Conj(l, r) => {
                theory::Term::Conj(Box::new((*l).deep_model()), Box::new((*r).deep_model()))
            }
            _ => theory::Term::Value(theory::Value::Bool(true)),
        }
    }
}

#[cfg_attr(not(creusot), derive(Debug))]
#[cfg_attr(not(creusot), derive(Hash))]
#[derive(Clone, PartialEq, Eq, DeepModel)]
#[DeepModelTy = "theory::Value"]
pub enum Value {
    Bool(bool),
    Rat(u64),
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Value {
    type ShallowModelTy = theory::Value;

    #[open]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

impl Value {
    #[requires((self@).is_bool())]
    pub fn bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Rat(_) => unreachable!(),
        }
    }

    #[ensures(result == (self@).is_bool())]
    pub fn is_bool(&self) -> bool {
        match self {
            Value::Bool(_) => true,
            Value::Rat(_) => false,
        }
    }

    #[requires((self@).is_bool())]
    #[ensures(result@ == (self@).negate())]
    pub(crate) fn negate(&self) -> Self {
        match self {
            Value::Bool(b) => Value::Bool(!*b),
            _ => unreachable!(),
        }
    }
}

#[cfg_attr(not(creusot), derive(Debug))]
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TrailIndex(usize, pub usize);

impl PartialOrd for TrailIndex {
    #[ensures(result == Some(self.cmp_log(*other)))]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TrailIndex {
    #[ensures(result == self.cmp_log(*other))]
    fn cmp(&self, other: &Self) -> Ordering {
        match self.0.cmp(&other.0) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => self.1.cmp(&other.1),
        }
    }
}

use ::std::cmp::Ordering;
use creusot_contracts::OrdLogic;
impl OrdLogic for TrailIndex {
    #[open]
    #[logic]
    fn cmp_log(self, rhs: Self) -> Ordering {
        match self.0.cmp_log(rhs.0) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => self.1.cmp_log(rhs.1),
        }
    }

    #[law]
    #[open(self)]
    #[ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
    fn cmp_le_log(x: Self, y: Self) {}

    #[law]
    #[open(self)]
    #[ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
    fn cmp_lt_log(x: Self, y: Self) {}

    #[law]
    #[open(self)]
    #[ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
    fn cmp_ge_log(x: Self, y: Self) {}

    #[law]
    #[open(self)]
    #[ensures(x.gt_log(y) == (x.cmp_log(y) == Ordering::Greater))]
    fn cmp_gt_log(x: Self, y: Self) {}

    #[law]
    #[open(self)]
    #[ensures(x.cmp_log(x) == Ordering::Equal)]
    fn refl(x: Self) {}

    #[law]
    #[open(self)]
    #[requires(x.cmp_log(y) == o)]
    #[requires(y.cmp_log(z) == o)]
    #[ensures(x.cmp_log(z) == o)]
    fn trans(x: Self, y: Self, z: Self, o: Ordering) {}

    #[law]
    #[open(self)]
    #[requires(x.cmp_log(y) == Ordering::Less)]
    #[ensures(y.cmp_log(x) == Ordering::Greater)]
    fn antisym1(x: Self, y: Self) {}

    #[law]
    #[open(self)]
    #[requires(x.cmp_log(y) == Ordering::Greater)]
    #[ensures(y.cmp_log(x) == Ordering::Less)]
    fn antisym2(x: Self, y: Self) {}

    #[law]
    #[open(self)]
    #[ensures((x == y) == (x.cmp_log(y) == Ordering::Equal))]
    fn eq_cmp(x: Self, y: Self) {}
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for TrailIndex {
    type ShallowModelTy = Self;

    #[open]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self
    }
}

#[cfg(creusot)]
impl creusot_contracts::DeepModel for TrailIndex {
    type DeepModelTy = Self;

    #[open]
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}

impl TrailIndex {
    #[ensures(result == self.0)]
    pub fn level(&self) -> usize {
        self.0
    }

    #[open]
    #[logic]
    pub fn level_log(self) -> Int {
        self.0.shallow_model()
    }
}

type Justification = Vec<TrailIndex>;

pub struct Trail {
    // todo make private
    pub assignments: Vec<Vec<Assignment>>,
    pub level: usize,
    pub ghost: Ghost<theory::Trail>,
}

#[cfg(not(creusot))]
impl ::std::fmt::Debug for Trail {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        self.assignments.fmt(f)
    }
}

impl Trail {
    #[trusted]
    #[ensures(result.invariant())]
    #[ensures(result.ghost.sound())]
    pub fn new(inputs: Vec<(Term, Value)>) -> Self {
        let mut input = Vec::new();
        for (term, val) in inputs {
            input.push(Assignment {
                term,
                val,
                reason: Reason::Input,
                level: 0,
            })
        }

        let mut assignments = Vec::new();
        assignments.insert(0, input);

        Trail {
            assignments,
            level: 0,
            ghost: ghost! { theory::Trail::Empty },
        }
    }

    #[ensures(result@ == (self.assignments@).len())]
    pub fn len(&self) -> usize {
        self.assignments.len()
    }

    #[open]
    #[predicate]
    pub fn unsat(self) -> bool {
        self.ghost.unsat()
    }

    #[open]
    #[predicate]
    pub fn sat(self) -> bool {
        self.ghost.sat()
    }

    #[open]
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            self.abstract_relation() && self.ghost.sound() && self.ghost.invariant()
            && self.ghost.level() == self.level@
            && self.level@ == (self.assignments@).len() - 1
            && (forall< i : _ > 0 <= i && i < self.level@ ==> self.assignments[i]@.len() > 0 )
            && (forall<ix : _> self.contains(ix) ==> ix.1@ == 0 == self.ghost.is_decision(self.index_logic(ix)))
            // && pearlite! { forall<l : _> 0 <= l && l < (self.assignments@).len() ==> (@(self.assignments@)[l]).unique() }
            && pearlite! { forall<i : TrailIndex, j : TrailIndex> self.contains(i) ==> self.contains(j) ==> i != j ==> self.index_logic(i) != self.index_logic(j) }
            && self.justified_is_justified()
        }
    }

    #[open]
    #[predicate]
    pub fn justified_is_justified(self) -> bool {
        pearlite! {
            forall<ix : _> self.contains(ix) ==>
                { let reason = self.assignments[ix.0@][ix.1@].reason;

                  (reason == Reason::Decision == self.ghost.is_decision(self.index_logic(ix))) &&
                  (reason == Reason::Input == self.ghost.is_input(self.index_logic(ix))) &&
                  (exists<j : _> reason == Reason::Justified(j)) == self.ghost.is_justified(self.index_logic(ix)) &&

                  (forall<j : _> reason == Reason::Justified(j) ==> ((forall<i : _> j@.contains(i) ==> self.contains(i)) && self.ghost.justification(self.index_logic(ix)) == self.abstract_justification(j@)))
                }

        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[requires(self.ghost.is_justified(self.index_logic(ix)))]
    #[ensures(forall<x : _> self.ghost.justification(self.index_logic(ix)).contains(x) ==> self.ghost.level_of(x) <= ix.level_log())]
    fn justified_level(self, ix: TrailIndex) {
        proof_assert!(self.ghost.level_of(self.index_logic(ix)) == ix.level_log());
    }

    #[open]
    #[predicate]
    pub fn abstract_relation(self) -> bool {
        pearlite! {
            (forall<ix : _> self.contains(ix) ==> self.ghost.contains(self.index_logic(ix))) &&
            (forall<ix : _> self.contains(ix) ==> self.ghost.level_of(self.index_logic(ix)) == ix.0@) &&
            (forall<a : _> self.ghost.contains(a) ==> exists<ix : _> self.contains(ix) && ix.level_log() == self.ghost.level_of(a) && self.index_logic(ix) == a)
        }
    }

    #[open]
    #[predicate]
    pub fn contains(self, ix: TrailIndex) -> bool {
        pearlite! {
            ix.0@ < (self.assignments@).len() && ix.1@ < ((self.assignments)@[ix.0@]@).len()
        }
    }

    #[logic]
    fn abstract_assign(&self, a: Assignment) -> theory::Assign {
        match a.reason {
            Reason::Input => theory::Assign::Input(a.term.shallow_model(), a.val.shallow_model()),
            Reason::Decision => {
                theory::Assign::Decision(a.term.shallow_model(), a.val.shallow_model())
            }
            Reason::Justified(just) => theory::Assign::Justified(
                self.abstract_justification(just.shallow_model()),
                a.term.shallow_model(),
                a.val.shallow_model(),
            ),
        }
    }

    #[logic]
    #[open(self)]
    #[variant(just.len())]
    #[requires(forall<i : _> 0 <= i && i < just.len() ==> self.contains(just[i]))]
    #[ensures(result.len() <= just.len())]
    #[ensures(forall< a : _> result.contains(a) ==> exists<ix : _> self.contains(ix) && a == self.index_logic(ix))]
    #[ensures(forall< a : _> result.contains(a) ==> exists<ix : _> just.contains(ix) && a == self.index_logic(ix))]
    #[ensures(forall<i : _> 0 <= i && i < just.len() ==> result.contains(self.index_logic(just[i])))]
    pub fn abstract_justification(
        &self,
        just: Seq<TrailIndex>,
    ) -> FSet<(theory::Term, theory::Value)> {
        if just.len() > 0 {
            let set = self.abstract_justification(remove(just, just[0]));
            let a = self.index_logic(just[0]);
            set.insert(a)
        } else {
            FSet::EMPTY
        }
    }


    #[predicate]
    fn trail_extension(self, o : Self) -> bool {
        if self.level <= o.level {
            pearlite! {
                (forall<ix : _> self.contains(ix) ==> self.index_logic(ix) == o.index_logic(ix)) &&
                (forall<kv : _> self.ghost.contains(kv) ==> self.ghost.find(kv) == o.ghost.find(kv))

            }
        } else {
            pearlite! {
                (forall<ix : _> o.contains(ix) ==> self.index_logic(ix) == o.index_logic(ix)) &&
                (forall<kv : _> o.ghost.contains(kv) ==> o.ghost.find(kv) == self.ghost.find(kv))
            }
        }
    }

    #[logic]
    #[variant(just.len())]
    #[requires(self.trail_extension(o))]
    #[requires(forall<i : _> 0 <= i && i < just.len() ==> self.contains(just[i]) && o.contains(just[i]))]
    #[ensures(self.abstract_justification(just) == o.abstract_justification(just))]
    fn lemma_abs_just(self, o : Self, just: Seq<TrailIndex>) {
        if just.len() == 0 {
            ()
        } else {
            self.lemma_abs_just(o, remove(just, just[0]))
        }
    }

    #[logic]
    #[variant(just.len())]
    #[requires(self.contains(elem))]
    #[requires(forall<i : _> 0 <= i && i < just.len() ==> self.contains(just[i]))]
    #[ensures(self.abstract_justification(Seq::singleton(elem).concat(just)) == self.abstract_justification(just).insert(self.index_logic(elem)))]
    fn abs_just_cons(self, just: Seq<TrailIndex>, elem: TrailIndex) {
        ()
    }

    #[logic]
    #[variant(just.len())]
    #[requires(self.contains(elem))]
    #[requires(forall<i : _> 0 <= i && i < just.len() ==> self.contains(just[i]))]
    #[ensures(self.abstract_justification(just.push(elem)) == self.abstract_justification(just).insert(self.index_logic(elem)))]
    fn abs_just_snoc(self, just: Seq<TrailIndex>, elem: TrailIndex) {
        if just == Seq::EMPTY {
            ()
        } else {
            let j = just.push(elem);
            let _ = self.abs_just_cons(j.subsequence(1, j.len()), j[0]);
            self.abs_just_snoc(just.subsequence(1, just.len()), elem)
        }
    }

    pub(crate) fn level(&self) -> usize {
        self.level
    }

    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    #[requires(self.ghost.acceptable(term@, val@))]
    #[ensures(self.ghost.impls(*(^self).ghost))]
    #[trusted] // for arithmetic
    pub(crate) fn add_decision(&mut self, term: Term, val: Value) {
        self.assignments.len();
        self.level += 1;
        let assign = Assignment {
            term,
            val,
            reason: Reason::Decision,
            level: self.level,
        };
        self.assignments.push(vec![assign]);
    }

    pub(crate) fn index_of(&self, a: &Term) -> Option<TrailIndex> {
        let mut level = 0;
        for assignments in &self.assignments {
            let mut offset = 0;
            for asgn in assignments {
                if &asgn.term == a {
                    return Some(TrailIndex(level, offset));
                }
                offset += 1;
            }
            level += 1;
        }
        None
    }

    // what specification to give?
    // this is a method on the trail as planning for future forms of justification
    // which need information from the trail to determine the set of relevant clauses
    #[requires(self.invariant())]
    #[requires(self.contains(a))]
    #[requires(self.ghost.is_justified(self.index_logic(a)))]
    #[ensures(forall<i : _> 0 <= i && i < (result@).len() ==> self.contains((result@)[i]))]
    #[ensures(self.abstract_justification(result@) == self.ghost.justification(self.index_logic(a)))]
    #[ensures(forall<i : _> 0 <= i && i < (result@).len() ==> (result@)[i].level_log() <= a.level_log())]
    pub(crate) fn justification(&self, a: TrailIndex) -> Vec<TrailIndex> {
        match &self[a].reason {
            Reason::Justified(v) => {
                proof_assert!(self.ghost.justification_contains(self.index_logic(a)); true);
                v.clone()
            }
            Reason::Decision => Vec::new(),
            Reason::Input => Vec::new(),
        }
    }

    // Need some sort of theorem here
    #[maintains((mut self).invariant())]
    #[requires((val@).is_bool())]
    #[requires(forall<i : _> 0 <= i && i < into_vec@.len() ==> self.contains(into_vec@[i]))]
    #[requires(self.ghost.acceptable(term@, val@))]
    #[requires(forall<m : theory::Model> m.invariant() ==> m.satisfy_set(self.abstract_justification(into_vec@)) ==> m.satisfies((term@, val@)))]
    #[ensures(self.ghost.impls(*(^self).ghost))]
    pub(crate) fn add_justified(&mut self, into_vec: Vec<TrailIndex>, term: Term, val: Value) {
        let old = ghost! { * self };
        let level = self.max_level(&into_vec);

        proof_assert!(level@ <= self.ghost.level());
        let xxx = ghost! { into_vec.shallow_model() };
        let just: Ghost<FSet<(theory::Term, theory::Value)>> =
            ghost! { self.abstract_justification(into_vec.shallow_model()) };
        proof_assert!(self.ghost.set_level(*just) <= self.ghost.level());
        let g: Ghost<theory::Assign> =
            ghost! { Assign::Justified(*just, term.shallow_model(), val.shallow_model()) };

        // proof_assert!(forall<i : _> 0 <= i && i < self.ghost.level() ==> exists<tv : _> self.ghost.contains(tv) && self.ghost.level_of(tv) == i);
        proof_assert!(level <= self.level);

        proof_assert!(g.invariant());
        proof_assert!(g.justified_sound());

        self.ghost = ghost! { self.ghost.add_justified(*just, term.shallow_model(), val.shallow_model())};

        proof_assert!({old.ghost.just_stable(*self.ghost, (term.shallow_model(), val.shallow_model())); true});

        let a = Assignment {
            term,
            val,
            reason: Reason::Justified(into_vec),
            level,
        };


        proof_assert!(self.ghost.invariant());
            let x = self.assignments[level].len();
        proof_assert!(x@ > 0);
        self.assignments[level].push(a);
        ghost! { old.lemma_abs_just(*self, *xxx) };

        proof_assert!(forall<ix : _> old.contains(ix) ==> self.contains(ix));
        proof_assert!(forall<ix : _> old.contains(ix) ==> old.index_logic(ix) == self.index_logic(ix));

    }

    // #[trusted]
    #[maintains((mut self).invariant())]
    #[requires(level@ <= self.level@)]
    #[ensures(*(^self).ghost == self.ghost.restrict(level@))]
    // Redundant but incredibly useful
    #[ensures(forall<ix : TrailIndex> ix.level_log() <= level@ ==> self.contains(ix) ==> (^self).contains(ix))]
    #[ensures(forall<ix : TrailIndex> (^self).contains(ix) ==> self.index_logic(ix) == (^self).index_logic(ix))]
    pub(crate) fn restrict(&mut self, level: usize) {
        let old: Ghost<&mut Trail> = ghost! { self };

        #[invariant(forall<i : _> 0 <= i && i <= self.level@ ==> (self.assignments@)[i] == (old.assignments)@[i])]
        #[invariant(self.invariant())]
        #[invariant(^self == ^*old)]
        #[invariant(*self.ghost == old.ghost.restrict(self.level@))]
        #[invariant(self.level >= level)]
        while level < self.level {
            self.assignments.pop();
            self.level -= 1;
            proof_assert!(exists<t : _> (self.ghost.restrict_kind_unchanged(self.level.shallow_model(), t) == () || true) );
            proof_assert!((exists<t : _> self.ghost.justification_contains(t) == () || true));
            self.ghost = ghost! { self.ghost.restrict(self.level.shallow_model()) };
            proof_assert! {
                forall<ix : _> self.contains(ix) ==> ((self.assignments)@[ix.0@])@[ix.1@] == ((old.assignments)@[ix.0@])@[ix.1@]
            };
            proof_assert!(forall<ix : _> self.contains(ix) ==> self.ghost.contains(self.index_logic(ix)));
            proof_assert!(self.ghost.restrict_idempotent(self.level@, self.level@ + 1); true);
            proof_assert!(forall<ix : _> self.contains(ix) ==> self.index_logic(ix) == old.index_logic(ix));
            proof_assert!(self.justified_is_justified());
            // proof_assert!(forall<ix : _> old.abstract_justification(?) ==)
        }
        proof_assert!(level == self.level);
        proof_assert!(
            self.ghost.inner() == old.inner().ghost.inner().restrict(level.shallow_model())
        );
        proof_assert!(old.ghost.restrict_sound(level@); true);
    }

    #[trusted] // proof passes modulo annoying details on `to_owned`
    #[requires(self.invariant())]
    #[requires(forall<i : _> 0 <= i && i < (assignments@).len() ==> self.contains((assignments@)[i]))]
    #[ensures(self.ghost.set_level(self.abstract_justification(assignments@)) == result@)]
    pub(crate) fn max_level(&self, assignments: &[TrailIndex]) -> usize {
        let mut max = 0;
        #[invariant(true)]
        #[invariant(self.ghost.set_level(self.abstract_justification(produced.to_owned())) == max@)]
        for ix in assignments {
            proof_assert!(self.abs_just_snoc(produced.to_owned(), *ix); true);
            proof_assert!(self.abstract_justification(assignments@).insert(self.index_logic(*ix)) == self.abstract_justification((assignments@).push(*ix)));
            proof_assert!((assignments@).contains(*ix));
            proof_assert!(self.contains(*ix));
            proof_assert! { self.ghost.level_of(self.index_logic(*ix)) == ix.0@ };
            if ix.0 >= max {
                proof_assert!(self.ghost.set_level_max(self.abstract_justification(produced.to_owned()), self.index_logic(*ix)); true);
                max = ix.0
            } else {
                proof_assert!(self.ghost.set_level_min(self.abstract_justification(produced.to_owned()), self.index_logic(*ix)); true);
            }
        }
        max
    }

    #[open]
    #[logic]
    pub fn index_logic(self, ix: TrailIndex) -> (theory::Term, theory::Value) {
        pearlite! {
            ((self.assignments)@[ix.0@])@[ix.1@].term_value()
        }
    }

    pub(crate) fn indices(&mut self) -> IndexIterator<'_> {
        IndexIterator {
            trail: self,
            cur_ix: TrailIndex(0, 0),
        }
    }
}

/// Offers an iterator over all indices in the trail, while allowing new justified decisions to be added
///
pub struct IndexIterator<'a> {
    trail: &'a mut Trail,
    cur_ix: TrailIndex,
}

impl IndexIterator<'_> {
    #[trusted]
    pub fn add_justified(&mut self, just: Justification, term: Term, value: Value) {
        self.trail.add_justified(just, term, value)
    }

    pub fn trail(&self) -> &Trail {
        &self.trail
    }

    // Not an actual iterator impl because it crashes...
    #[trusted]
    pub fn next(&mut self) -> Option<TrailIndex> {
        if self.cur_ix.0 >= self.trail.assignments.len() {
            return None;
        };

        if self.cur_ix.1 < self.trail.assignments[self.cur_ix.0].len() {
            let res = self.cur_ix;
            self.cur_ix.1 += 1;
            return Some(res);
        }

        self.cur_ix.0 += 1;
        self.cur_ix.1 = 0;

        self.next()
    }
}

impl Index<TrailIndex> for Trail {
    type Output = Assignment;

    // #[requires(index@ < (self.assignments@).len())]
    // #[ensures(*result == (self.assignments@)[index@])]
    #[requires(self.contains(index))]
    #[ensures(*result == ((self.assignments)@[index.0@])@[index.1@])]
    fn index(&self, index: TrailIndex) -> &Self::Output {
        &self.assignments[index.0][index.1]
    }
}

impl Assignment {
    #[open]
    #[logic]
    pub fn term_value(&self) -> (theory::Term, theory::Value) {
        (self.term.shallow_model(), self.val.shallow_model())
    }

    #[ensures(result == self.level)]
    pub(crate) fn level(&self) -> usize {
        self.level
    }

    #[ensures(result == (self.val@).is_bool())]
    pub(crate) fn is_bool(&self) -> bool {
        self.val.is_bool()
    }

    #[ensures(result != (self.val@).is_bool())]
    pub(crate) fn is_first_order(&self) -> bool {
        !self.is_bool()
    }

    #[ensures(result == (exists<j : _> self.reason == Reason::Justified(j)))]
    pub(crate) fn is_justified(&self) -> bool {
        matches!(self.reason, Reason::Justified(_))
    }

    #[ensures(result == (self.reason == Reason::Decision))]
    pub(crate) fn is_decision(&self) -> bool {
        self.reason == Reason::Decision
    }

    #[ensures(result == (self.reason == Reason::Input))]
    pub(crate) fn is_input(&self) -> bool {
        self.reason == Reason::Input
    }

    #[ensures(*result == self.val)]
    pub(crate) fn value(&self) -> &Value {
        &self.val
    }

    #[ensures(*result == self.term)]
    pub(crate) fn term(&self) -> &Term {
        &self.term
    }
}

// This is the same as `abstract_justification`...
#[logic]
#[open(self)]
#[variant(s.len())]
#[ensures(forall<ix :_> s.contains(ix) ==> result.contains(t.index_logic(ix)))]
#[ensures(forall<a :_> result.contains(a) ==> exists<ix :_> a == t.index_logic(ix) && s.contains(ix))]
pub(crate) fn ix_to_abs(t: Trail, s: FSet<TrailIndex>) -> FSet<(theory::Term, theory::Value)> {
    if s == FSet::EMPTY {
        FSet::EMPTY
    } else {
        let a = s.peek();
        ix_to_abs(t, s.remove(a)).insert(t.index_logic(a))
    }
}

#[logic]
#[open(self)]
#[variant(s.len())]
// #[requires(seq_unique(s))]
#[requires(forall<i : _> s.contains(i) ==> t.contains(i))]
#[requires(forall<i : _> t.contains(i) ==> s.contains(i))]
#[ensures(trail.abstract_justification(s) == ix_to_abs(trail, t))]
pub(crate) fn seq_to_set(trail: Trail, s: Seq<TrailIndex>, t: FSet<TrailIndex>) {
    if s == Seq::EMPTY {
        ()
    } else {
        let a = s[0];
        seq_to_set(trail, remove(s, a), t.remove(a))
    }
}

#[logic]
#[variant(s.len())]
#[ensures(forall<t : _> s.contains(t) ==> e != t ==> result.contains(t))]
#[ensures(forall<t : _> result.contains(t) ==>  s.contains(t))]
#[ensures(forall<t : _> result.contains(t) ==> t != e)]
#[ensures(s.contains(e) ==> result.len() < s.len())]
#[ensures(result.len() <= s.len())]
fn remove<T>(s: Seq<T>, e: T) -> Seq<T> {
    if s == Seq::EMPTY {
        Seq::EMPTY
    } else {
        if s[s.len() - 1] == e {
            remove(s.subsequence(0, s.len() - 1), e)
        } else {
            remove(s.subsequence(0, s.len() - 1), e).push(s[s.len() - 1])
        }
    }
}

#[predicate]
#[open]
pub(crate) fn seq_unique<T>(s: Seq<T>) -> bool {
    pearlite! { forall<i : _, j : _> 0 <= i && i <= j && j < s.len() ==> i != j ==> s[i] != s[j] }
}

#[logic]
#[open(self)]
#[requires(!s.is_empty())]
#[variant(s.len())]
#[ensures(s.contains(result))]
#[ensures(forall<o : _> s.contains(o) ==> o <= result )]
pub(crate) fn set_max(s: FSet<TrailIndex>) -> TrailIndex {
    let x = s.peek();
    let s = s.remove(x);

    if s.is_empty() {
        x
    } else {
        let rec = set_max(s);
        if x >= rec {
            x
        } else {
            rec
        }
    }
}

#[logic]
#[open(self)]
#[requires(t.invariant())]
#[variant(s.len())]
#[requires(forall<i :_> s.contains(i) ==> t.contains(i))]
#[ensures(!s.is_empty() ==> t.ghost.set_level(ix_to_abs(t, s)) == set_max(s).level_log())]
#[ensures(s.is_empty() ==> t.ghost.set_level(ix_to_abs(t, s)) == 0)]
pub(crate) fn ix_to_abs_level(t: Trail, s: FSet<TrailIndex>) {
    ()
}

#[logic]
#[open(self)]
#[variant(s.len())]
#[requires(t.invariant())]
#[requires(t.contains(x))]
#[requires(forall<i : _> s.contains(i) ==> t.contains(i))]
#[ensures(ix_to_abs(t, s.remove(x)) == ix_to_abs(t, s).remove(t.index_logic(x)))]
pub(crate) fn ix_to_abs_remove(t: Trail, x: TrailIndex, s: FSet<TrailIndex>) {
    ()
}

#[logic]
#[open(self)]
#[variant(s.len())]
#[requires(t.invariant())]
#[requires(t.contains(x))]
#[requires(forall<i : _> s.contains(i) ==> t.contains(i))]
#[ensures(ix_to_abs(t, s.insert(x)) == ix_to_abs(t, s).insert(t.index_logic(x)))]
pub(crate) fn ix_to_abs_insert(t: Trail, x: TrailIndex, s: FSet<TrailIndex>) {
    ()
}

#[logic]
#[open(self)]
#[variant(s.len())]
#[requires(t.invariant())]
#[requires(t.contains(x))]
#[requires(forall<i : _> s.contains(i) ==> t.contains(i))]
#[ensures(t.abstract_justification(s.push(x)) == t.abstract_justification(s).insert(t.index_logic(x)) )]
pub(crate) fn abstract_justification_insert(t: Trail, x: TrailIndex, s: Seq<TrailIndex>) {
    t.abstract_justification(s.push(x));
}


