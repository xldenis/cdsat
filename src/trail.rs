use crate::log::info;
#[allow(unused_imports)]
use crate::{
    term::{Term, Value},
    theory::{self},
};
use ::std::{fmt::Display, ops::Index, unreachable};
use creusot_contracts::{logic::*, vec, Clone, DeepModel, PartialEq, *};
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

impl Display for Assignment {
    #[trusted]
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "{} <- {}", self.term, self.val)
    }
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Assignment {
    type ShallowModelTy = <Self as DeepModel>::DeepModelTy;

    #[open]
    #[ghost]
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
    #[ghost]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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
    #[ghost]
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
    #[ghost]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self
    }
}

#[cfg(creusot)]
impl creusot_contracts::DeepModel for TrailIndex {
    type DeepModelTy = Self;

    #[open]
    #[ghost]
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
    #[ghost]
    pub fn level_log(self) -> Int {
        self.0.shallow_model()
    }
}

type Justification = Vec<TrailIndex>;

pub struct Trail {
    // todo make private
    pub assignments: Vec<Vec<Assignment>>,
    pub level: usize,
    pub ghost: Ghost![theory::Trail],
    pub num_assign: usize,
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
            input.push(Assignment { term, val, reason: Reason::Input, level: 0 })
        }

        let mut assignments = Vec::new();
        assignments.insert(0, input);

        Trail { assignments, level: 0, ghost: gh! { theory::Trail::Empty }, num_assign: 0 }
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
            && self.level@ == self.assignments@.len() - 1
            && (forall< i : _ > 0 <= i && i < self.assignments@.len() ==> self.assignments[i]@.len() > 0 )
            && (forall<ix : _> self.contains(ix) ==> ix.1@ == 0 == self.ghost.is_decision(self.index_logic(ix)))
            // && pearlite! { forall<l : _> 0 <= l && l < (self.assignments@).len() ==> (@(self.assignments@)[l]).unique() }
            && pearlite! { forall<i : TrailIndex, j : TrailIndex> self.contains(i) ==> self.contains(j) ==> i != j ==> self.index_logic(i) != self.index_logic(j) }
            && self.justified_is_justified()
            && (forall< ix : _> self.contains(ix) ==> self[ix].0.well_sorted())
        }
    }

    #[open]
    #[predicate]
    pub fn justified_is_justified(self) -> bool {
        pearlite! {
            forall<ix : _> self.contains(ix) ==>
                { let reason = self.reason(ix);
                  (reason == Reason::Decision == self.ghost.is_decision(self.index_logic(ix))) &&
                  (reason == Reason::Input == self.ghost.is_input(self.index_logic(ix))) &&
                  (forall<j : _> reason == Reason::Justified(j) ==>
                    self.justified_correct(ix, j))
                }

        }
    }
    #[open]
    #[predicate]
    pub fn justified_correct(self, ix: TrailIndex, j: Vec<TrailIndex>) -> bool {
        pearlite!{
            (forall<i : _> j@.contains(i) ==> i < ix && self.contains(i)) &&
            self.ghost.is_justified(self.index_logic(ix)) &&
            self.ghost.justification(self.index_logic(ix)) == self.abstract_justification(j@)
        }
    }

    #[open]
    #[predicate]
    pub fn abstract_relation(self) -> bool {
        pearlite! {
            (forall<ix : _> self.contains(ix) ==> self.ghost.contains(self.index_logic(ix))) &&
            (forall<ix : _> self.contains(ix) ==> self.ghost.level_of(self.index_logic(ix)) == ix.0@) &&
            (forall<a : _> self.ghost.contains(a) ==>
              exists<ix : _> self.contains(ix) && ix.level_log() == self.ghost.level_of(a) && self.index_logic(ix) == a
            )
        }
    }

    #[open]
    #[predicate]
    pub fn contains(self, ix: TrailIndex) -> bool {
        pearlite! {
            ix.0@ < (self.assignments@).len() && ix.1@ < ((self.assignments)@[ix.0@]@).len()
        }
    }

    #[ghost]
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

    #[ghost]
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
    fn trail_extension(self, o: Self) -> bool {
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

    #[ghost]
    #[variant(just.len())]
    #[requires(self.trail_extension(o))]
    #[requires(forall<i : _> 0 <= i && i < just.len() ==> self.contains(just[i]) && o.contains(just[i]))]
    #[ensures(self.abstract_justification(just) == o.abstract_justification(just))]
    fn lemma_abs_just(self, o: Self, just: Seq<TrailIndex>) {
        if just.len() == 0 {
            ()
        } else {
            self.lemma_abs_just(o, remove(just, just[0]))
        }
    }

    #[ghost]
    #[open(self)]
    #[variant(just.len())]
    #[requires(forall<i : _> 0 <= i && i < just2.len() ==> self.contains(just2[i]))]
    #[requires(forall<ix : _> just.contains(ix) ==> just2.contains(ix))]
    #[ensures(forall<tv : _> self.abstract_justification(just).contains(tv) ==> self.abstract_justification(just2).contains(tv))]
    pub fn abs_just_extend(self, just: Seq<TrailIndex>, just2: Seq<TrailIndex>) {
        proof_assert!(forall<i : _> 0 <= i && i < just.len() ==> self.contains(just[i]));
        proof_assert!(forall<i : _> 0 <= i && i < just2.len() ==> self.contains(just2[i]));
    }

    #[ghost]
    #[variant(just.len())]
    #[requires(self.contains(elem))]
    #[requires(forall<i : _> 0 <= i && i < just.len() ==> self.contains(just[i]))]
    #[ensures(self.abstract_justification(Seq::singleton(elem).concat(just)) == self.abstract_justification(just).insert(self.index_logic(elem)))]
    fn abs_just_cons(self, just: Seq<TrailIndex>, elem: TrailIndex) {
        ()
    }

    #[ghost]
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

    #[requires(term@.well_sorted())]
    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    #[requires(self.ghost.acceptable(term@, val@))]
    #[ensures(self.ghost.impls(*(^self).ghost))]
    pub(crate) fn add_decision(&mut self, term: Term, val: Value) {
        info!("? {term} <- {val}");
        let old = gh! { * self };
        self.assignments.len();
        self.level += 1;
        let kv = gh! { (term.shallow_model(), val.shallow_model())};
        self.ghost = gh! { theory::Normal(*self.ghost).decidef(term@, val@).0};
        let assign = Assignment { term, val, reason: Reason::Decision, level: self.level };
        self.assignments.push(vec![assign]);
        proof_assert!(forall<ix : _> old.contains(ix) ==> self.reason(ix) == old.reason(ix));
        proof_assert!(forall<ix : _> old.contains(ix) ==> old.index_logic(ix) == self.index_logic(ix));
        gh! { Self::abs_just_equiv };
        let new_ix = TrailIndex(self.level, 0);
        proof_assert!(self[new_ix] == *kv);
        let _: Ghost![_] = gh! { theory::Trail::just_stable };
        proof_assert!(self.abstract_relation());
        proof_assert!(self.justified_is_justified());
        // self.num_assign += 1;
    }

    #[ensures(match result {
        Some(x) => self.contains(x) && self.index_logic(x).0 == a@,
        None => forall<ix : _> self.contains(ix) ==> self[ix].0 != a@
    })]
    pub(crate) fn index_of(&self, a: &Term) -> Option<TrailIndex> {
        let mut level = 0;
        #[invariant(forall<ix : TrailIndex > 0 <= ix.0@ && ix.0@ < produced.len() ==> self.contains(ix) ==> self[ix].0 != a@)]
        #[invariant(level@ == produced.len())]
        for assignments in &self.assignments {
            let mut offset = 0;
            #[invariant(offset@ == produced.len())]
            #[invariant(forall<ix : TrailIndex > ix.0 == level ==> ix.1 < offset ==> self.contains(ix) ==> self[ix].0 != a@)]
            for asgn in assignments {
                let ix = TrailIndex(level, offset);
                proof_assert!(self.contains(ix));
                if &asgn.term == a {
                    proof_assert!(self[ix].0 == asgn.term@);
                    proof_assert!(asgn.term@ == a@);
                    return Some(ix);
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
    #[ensures(forall<i : _> 0 <= i && i < result@.len() ==> self.contains(result[i]))]
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

    #[trusted]
    fn log_justified(&self, just: &[TrailIndex], term: &Term, val: &Value) {
        use ::std::fmt::Write;
        let mut s = String::from("{");
        for i in just {
            write!(s, "{}, ", &self[*i]).unwrap();
        }
        s.push('}');
        info!("{s} |- {term} <- {val}");
    }

    // This proof is weirdly hard to get to pass, for such a trivial operation..
    // Additionally the proof still requires manual intervention in the why3 session
    #[maintains((mut self).invariant())]
    #[requires(term@.well_sorted())]
    #[requires((val@).is_bool())]
    #[requires(forall<i : _> into_vec@.contains(i) ==> self.contains(i))]
    #[requires(self.ghost.acceptable(term@, val@))]
    #[requires(forall<m : theory::Model>  m.satisfy_set(self.abstract_justification(into_vec@)) ==> m.satisfies((term@, val@)))]
    #[ensures(self.ghost.impls(*(^self).ghost))]
    pub(crate) fn add_justified(&mut self, into_vec: Vec<TrailIndex>, term: Term, val: Value) {
        self.log_justified(&into_vec, &term, &val);
        proof_assert!(forall<ix : _> self.contains(ix) ==> self.index_logic(ix) != (term@, val@));

        let level = self.max_level(&into_vec);

        // proof_assert!(level <= self.level);
        let g_vec: Ghost![_] = gh! { into_vec };
        let just: Ghost![FSet<(theory::Term, theory::Value)>] =
            gh! { self.abstract_justification(into_vec.shallow_model()) };

        proof_assert!(level@ == self.ghost.set_level(*just));

        let _: Ghost![_] = gh! { theory::Normal(*self.ghost).deducef(*just, term.shallow_model(), val.shallow_model()) };

        let old: Ghost![_] = gh! { self };

        self.ghost =
            gh! { self.ghost.add_justified(*just, term.shallow_model(), val.shallow_model())};


        let v: Ghost![_] = gh! { (term.shallow_model(), val.shallow_model())};

        proof_assert!(self.ghost.level_of(*v) == level@);
        let a = Assignment { term, val, reason: Reason::Justified(into_vec), level };
        let x = self.assignments[level].len();
        let new_ix = TrailIndex(level, x);

        proof_assert!(forall<i : _> g_vec@.contains(i) ==> i.0 <= new_ix.0);
        proof_assert!(forall<i : _> g_vec@.contains(i) ==> i < new_ix);

        proof_assert!(x@ > 0);

        self.assignments[level].push(a);
        // self.num_assign += 1;

        let _: Ghost![()] = gh! { self.abs_just_equiv(**old, g_vec@)};
        let _: Ghost![_] = gh! { theory::Trail::just_stable };
        proof_assert!(forall<ix : _> old.contains(ix) ==> self.reason(ix) == old.reason(ix));
        proof_assert!(forall<ix : _> old.contains(ix) ==> old.index_logic(ix) == self.index_logic(ix));

        proof_assert!(forall<j : _> self.contains(j) ==> j == new_ix || old.contains(j));
        proof_assert!(old.ghost.ext(*self.ghost));
        proof_assert!(self.justified_is_justified());
        proof_assert!(self.abstract_relation());
    }

    #[ghost]
    #[open(self)]
    #[requires(forall<j : _> just.contains(j) ==> self.contains(j) && other.contains(j) && self.index_logic(j) == other.index_logic(j))]
    #[ensures(self.abstract_justification(just) == other.abstract_justification(just))]
    pub fn abs_just_equiv(self, other: Self, just: Seq<TrailIndex>) {
        ()
    }

    #[logic]
    #[open]
    pub fn reason(self, ix: TrailIndex) -> Reason {
        self.assignments[ix.0][ix.1].reason
    }

    #[ghost]
    #[requires(self.invariant())]
    #[requires(other.abstract_relation() && other.ghost.invariant())]
    #[requires(self.ghost.restrict(other.level@) == *other.ghost)]
    #[requires(other.ghost.level() == other.level@)]
    #[requires(forall<ix : _> other.contains(ix) ==> self.contains(ix))]
    #[requires(forall<ix :_> other.contains(ix) ==> self.index_logic(ix) == other.index_logic(ix))]
    #[requires(forall<ix : _> other.contains(ix) ==> self.reason(ix) == other.reason(ix))]
    #[ensures(other.justified_is_justified())]
    fn reasons_dont_change(self, other: Self) {
        let _ = theory::Trail::restrict_kind_unchanged;
        proof_assert!(forall<ix : _> self.contains(ix) ==> ix.level_log() <= other.level@ ==> other.contains(ix));
        proof_assert!(forall<a : _> other.ghost.contains(a) ==>
            self.ghost.is_justified(a) == other.ghost.is_justified(a));
        proof_assert!(forall<a : _> other.ghost.contains(a) ==>
            self.ghost.is_decision(a) == other.ghost.is_decision(a));
        proof_assert!(forall<a : _> other.ghost.contains(a) ==>
            self.ghost.is_input(a) == other.ghost.is_input(a) );
        proof_assert!(forall<a : _> other.ghost.contains(a) ==>
            self.ghost.justification(a) == other.ghost.justification(a));
        proof_assert!(forall<ix : _> other.contains(ix) ==> ix.level_log() <= other.ghost.level());
        proof_assert!(forall<ix : _, j : _> other.contains(ix) ==>  other.reason(ix) == Reason::Justified(j) ==>
            forall<i : _> j@.contains(i) ==> i < ix && other.contains(i)
        );
    }

    #[maintains((mut self).invariant())]
    #[requires(level@ <= self.level@)]
    #[ensures(*(^self).ghost == self.ghost.restrict(level@))]
    // Redundant but incredibly useful
    #[ensures(forall<ix : TrailIndex> ix.level_log() <= level@ ==> self.contains(ix) ==> (^self).contains(ix))]
    #[ensures(forall<ix : TrailIndex> (^self).contains(ix) ==> self.index_logic(ix) == (^self).index_logic(ix))]
    pub(crate) fn restrict(&mut self, level: usize) {
        let old: Ghost![&mut Trail] = gh! { self };

        // Restate as a subsequence?
        // #[invariant(forall<i : _> 0 <= i && i <= self.level@ ==> (self.assignments@)[i] == (old.assignments)@[i])]
        #[invariant(*self.ghost == old.ghost.restrict(self.level@))]
        #[invariant(self.level >= level)]
        #[invariant(forall<ix : TrailIndex> self.contains(ix) ==> old.index_logic(ix) == self.index_logic(ix))]
        #[invariant(forall<ix : _> self.contains(ix) ==> self.reason(ix) == old.reason(ix))]
        // #[invariant(forall<ix : _> old.contains(ix) ==> ix.level_log() <= self.level@ ==> self.contains(ix))]
        #[invariant(self.invariant())]
        while level < self.level {
            let _: Ghost![_] = gh!(theory::Trail::restrict_idempotent);
            let _: Ghost![_] = gh!(theory::Trail::restrict_kind_unchanged);
            let _: Ghost![_] = gh!(theory::Trail::restrict_sound);

            // This is a load bearing `unwrap`. It allows the provers to properly see that `pop` returned `Some` here
            // and use the appropriate specification. They don't want to break the `match` in the postcondition of `pop` otherwise.
            self.assignments.pop().unwrap();
            proof_assert!(forall<ix : _> self.contains(ix) ==> old.contains(ix));

            self.level -= 1;
            self.ghost = gh! { self.ghost.restrict(self.level.shallow_model()) };

            proof_assert!(self.abstract_relation());
            gh!(old.reasons_dont_change(*self));
        }
    }

    #[requires(self.invariant())]
    #[requires(forall<i : _> 0 <= i && i < assignments@.len() ==> self.contains(assignments[i]))]
    #[ensures(self.ghost.set_level(self.abstract_justification(assignments@)) == result@)]
    pub(crate) fn max_level(&self, assignments: &[TrailIndex]) -> usize {
        let mut max = 0;
        let mut other = gh! { Seq::EMPTY };
        #[invariant(*other == produced.to_owned_seq())]
        #[invariant(self.ghost.set_level(self.abstract_justification(produced.to_owned_seq())) == max@)]
        for ix in assignments {
            proof_assert!(forall<i : _> 0 <= i && i < produced.len() ==> assignments[i] == *produced[i]);
            gh! { self.abs_just_snoc(*other, *ix) };
            let just = gh! { self.abstract_justification(*other) };
            proof_assert!(self.ghost.set_level(*just) == max@);
            if ix.0 >= max {
                max = ix.0;
                proof_assert!(self.ghost.level_of(self[*ix]) == ix.0@);
                gh! { self.ghost.set_level_max(*just, self[*ix]) };
            } else {
                proof_assert!(ix.0 < max );
                gh! { self.ghost.set_level_min(*just, self[*ix]) };

            }
            other = gh! { other.push(*ix)};
            proof_assert!(other.ext_eq(produced.to_owned_seq()));
        }
        proof_assert!(other.ext_eq(assignments@));
        max
    }

    #[open]
    #[ghost]
    pub fn index_logic(self, ix: TrailIndex) -> (theory::Term, theory::Value) {
        pearlite! {
            ((self.assignments)@[ix.0@])@[ix.1@].term_value()
        }
    }

    #[ensures(result.trail == self)]
    pub(crate) fn indices(&mut self) -> IndexIterator<'_> {
        IndexIterator { trail: self, cur_ix: TrailIndex(0, 0) }
    }
}

/// Offers an iterator over all indices in the trail, while allowing new justified decisions to be added
///
pub struct IndexIterator<'a> {
    pub(crate) trail: &'a mut Trail,
    cur_ix: TrailIndex,
}

#[trusted]
impl<'a> creusot_contracts::Resolve for IndexIterator<'a> {
    #[open]
    #[predicate]
    fn resolve(self) -> bool {
        self.trail.resolve()
    }
}

impl IndexIterator<'_> {
    #[trusted] // Used in LRA theory
    pub fn add_justified(&mut self, just: Justification, term: Term, value: Value) {
        if self.trail.index_of(&term).is_none() {
            self.trail.add_justified(just, term, value)
        }
    }

    #[ensures(*result == *self.trail)]
    pub fn trail(&self) -> &Trail {
        &self.trail
    }

    // Not an actual iterator impl because it crashes...
    #[ensures((^self).trail == (*self).trail )]
    #[ensures(match result {
        Some(ix) => self.trail.contains(ix),
        None => true,
    })]
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
    #[ghost]
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

    // #[ensures(result != (self.val@).is_bool())]
    pub(crate) fn is_rational(&self) -> bool {
        !self.val.is_bool()
            || matches!(self.term, Term::Lt(_, _) | Term::Plus(_, _) | Term::Eq(_, _))
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
#[ghost]
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

#[ghost]
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

#[ghost]
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

#[ghost]
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

#[ghost]
#[open(self)]
#[requires(t.invariant())]
#[variant(s.len())]
#[requires(forall<i :_> s.contains(i) ==> t.contains(i))]
#[ensures(!s.is_empty() ==> t.ghost.set_level(ix_to_abs(t, s)) == set_max(s).level_log())]
#[ensures(s.is_empty() ==> t.ghost.set_level(ix_to_abs(t, s)) == 0)]
pub(crate) fn ix_to_abs_level(t: Trail, s: FSet<TrailIndex>) {
    if s.is_empty() {
        ()
    } else {
        let max_elem = set_max(s);
        let max_asgn = t.index_logic(max_elem);
        let ghost_set = ix_to_abs(t, s);
        proof_assert!(forall<i : _> s.contains(i) ==> i.level_log() <= max_elem.level_log());
        proof_assert!(forall<a : _> ghost_set.contains(a) ==> t.ghost.level_of(a) <= t.ghost.level_of(max_asgn));
    }
}

#[ghost]
#[open(self)]
#[variant(s.len())]
#[requires(t.invariant())]
#[requires(t.contains(x))]
#[requires(forall<i : _> s.contains(i) ==> t.contains(i))]
#[ensures(ix_to_abs(t, s.remove(x)) == ix_to_abs(t, s).remove(t.index_logic(x)))]
pub(crate) fn ix_to_abs_remove(t: Trail, x: TrailIndex, s: FSet<TrailIndex>) {
    proof_assert!(
        ix_to_abs(t, s.remove(x)).ext_eq(ix_to_abs(t, s).remove(t.index_logic(x)))
    )
}

#[ghost]
#[open(self)]
#[variant(s.len())]
#[requires(t.invariant())]
#[requires(t.contains(x))]
#[requires(forall<i : _> s.contains(i) ==> t.contains(i))]
#[ensures(ix_to_abs(t, s.insert(x)) == ix_to_abs(t, s).insert(t.index_logic(x)))]
pub(crate) fn ix_to_abs_insert(t: Trail, x: TrailIndex, s: FSet<TrailIndex>) {
    proof_assert!(ix_to_abs(t, s.insert(x)).ext_eq(ix_to_abs(t, s).insert(t.index_logic(x))));
}

#[ghost]
#[open(self)]
#[variant(s.len())]
#[requires(t.invariant())]
#[requires(t.contains(x))]
#[requires(forall<i : _> s.contains(i) ==> t.contains(i))]
#[ensures(t.abstract_justification(s.push(x)) == t.abstract_justification(s).insert(t.index_logic(x)) )]
pub(crate) fn abstract_justification_insert(t: Trail, x: TrailIndex, s: Seq<TrailIndex>) {
    t.abs_just_snoc(s, x)
}
