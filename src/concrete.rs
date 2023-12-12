// use ::std::collections::{BinaryHeap, HashSet};
// // use creusot_contracts::derive::{PartialEq};

use ::std::{collections::BTreeSet, fmt::Write};

use crate::term::{Term, Value};
// use creusot_contracts::*;
use crate::{bool::*, log::info, lra::*, theory, trail::*};
use creusot_contracts::{logic::*, std::*, PartialEq, *};

use crate::ghost::Ghost;

pub struct Solver {
    bool_th: BoolTheory,
    bool_state: TheoryState,
    lra_th: LRATheory,
    lra_state: TheoryState,
}

#[derive(PartialEq, Eq, DeepModel)]
enum TheoryState {
    Sat,
    Decision(Term, Value),
    Unknown,
}

impl Solver {
    pub fn new() -> Self {
        Solver {
            bool_th: BoolTheory,
            bool_state: TheoryState::Unknown,
            lra_th: LRATheory,
            lra_state: TheoryState::Unknown,
        }
    }

    #[ensures(match result {
        None => true,
        Some(c) => {
            let conflict = (^trail).abstract_justification(c@);
            c@.len() > 0 &&
            // members of conflict area within the trail
            (forall<t : _> (c@).contains(t) ==> (^trail).contains(t)) &&
            // (forall<i : _> 0 <= i && i < (c@).len() ==> @(c@)[i] < (@(^tl).assignments).len()) &&
            (forall<m : theory::Model> m.satisfy_set(conflict) ==> false)
        }
    })]
    #[maintains((mut trail).invariant())]
    #[requires(self.bool_state == TheoryState::Unknown && self.lra_state == TheoryState::Unknown)]
    #[ensures((^self).dec_acc(^trail))]
    #[ensures(trail.ghost.impls(*(^trail).ghost))]
    fn extend_next(&mut self, trail: &mut Trail) -> Option<Vec<TrailIndex>> {
        let old: Ghost![_] = gh! { trail };
        use TheoryState::*;
        let (res, state) = if self.bool_state == Unknown {
            (self.bool_th.extend(trail), &mut self.bool_state)
        } else if self.lra_state == Unknown {
            (self.lra_th.extend(trail), &mut self.lra_state)
        } else {
            return None;
        };

        proof_assert!(trail.invariant());
        proof_assert!(old.ghost.impls(*trail.ghost));

        match res {
            ExtendResult::Decision(t, v) => *state = TheoryState::Decision(t, v),
            ExtendResult::Satisfied => *state = TheoryState::Sat,
            ExtendResult::Conflict(c) => {
                self.bool_state = TheoryState::Unknown;
                self.lra_state = TheoryState::Unknown;
                return Some(c);
            }
        };
        return None;
    }

    #[predicate]

    fn dec_acc(self, trail: Trail) -> bool {
        pearlite! { forall<t :_, v : _>
            self.bool_state == TheoryState::Decision(t, v) || self.lra_state == TheoryState::Decision(t, v)
            ==> trail.ghost.acceptable(t@, v@)
        }
    }

    #[ensures(result == (self.bool_state == TheoryState::Unknown || self.lra_state == TheoryState::Unknown))]
    pub fn can_deduce(&self) -> bool {
        self.bool_state == TheoryState::Unknown || self.lra_state == TheoryState::Unknown
    }

    #[ensures(result == (self.bool_state == TheoryState::Sat && self.lra_state == TheoryState::Sat))]
    pub fn sat(&self) -> bool {
        self.bool_state == TheoryState::Sat && self.lra_state == TheoryState::Sat
    }

    #[requires(exists<t :_, v : _>
        self.bool_state == TheoryState::Decision(t, v) || self.lra_state == TheoryState::Decision(t, v))]
    #[ensures(self.bool_state == TheoryState::Decision(result.0, result.1) || self.lra_state == TheoryState::Decision(result.0, result.1))]
    pub fn decision(&mut self) -> (Term, Value) {
        match (&mut self.bool_state, &mut self.lra_state) {
            (TheoryState::Decision(t, v), _) | (_, TheoryState::Decision(t, v)) => {
                let answer = (t.clone(), v.clone());
                self.bool_state = TheoryState::Unknown;
                self.lra_state = TheoryState::Unknown;
                return answer;
            }
            _ => unreachable!(),
        }
    }

    #[maintains((mut trail).invariant())]
    #[ensures(trail.ghost.impls(*(^trail).ghost))]
    pub fn solver(&mut self, trail: &mut Trail) -> Answer {
        let old_trail: Ghost![_] = gh! { trail};
        #[invariant(old_trail.ghost.impls(*trail.ghost))]
        #[invariant(trail.invariant())]
        loop {
            // if trail.num_assign > 10 { panic!() }
            let iter_trail: Ghost![_] = gh! { trail };
            // self.bool_state = TheoryState::Unknown;
            // self.lra_state = TheoryState::Unknown;
            #[invariant(iter_trail.ghost.impls(*trail.ghost))]
            #[invariant(trail.invariant())]
            #[invariant(self.dec_acc(*trail))]
            while self.can_deduce() {
                // self.bool_state = TheoryState::Unknown;
                // self.lra_state = TheoryState::Unknown;

                if let Some(cflct) = self.extend_next(trail) {
                    // info!("conflict {cflct:?}");
                    if trail.max_level(&cflct) > 0 {
                        self.resolve_conflict(trail, cflct);
                        self.bool_state = TheoryState::Unknown;
                        self.lra_state = TheoryState::Unknown;
                    } else {
                        return Answer::Unsat;
                    }
                }
            }

            proof_assert!(self.dec_acc(*trail));
            if self.sat() {
                return Answer::Sat;
            } else {
                proof_assert!(self.bool_state == TheoryState::Sat || self.bool_state == TheoryState::Unknown || exists<t :_, v :_> self.bool_state  == TheoryState::Decision(t, v));
                proof_assert!(self.lra_state == TheoryState::Sat || self.lra_state == TheoryState::Unknown || exists<t :_, v :_> self.lra_state  == TheoryState::Decision(t, v));

                proof_assert!(( exists<t :_, v :_> self.lra_state  == TheoryState::Decision(t, v)) || (exists<t :_, v :_> self.bool_state  == TheoryState::Decision(t, v)));
                let (t, v) = self.decision();
                info!("Adding decision {t} <- {v}");
                trail.add_decision(t, v);
            }
        }
    }

    #[maintains((mut trail).invariant())]
    #[requires((conflict@).len() > 0)]
    #[requires(forall< i : _ > 0 <= i && i < (conflict@).len() ==> trail.contains((conflict@)[i]))]
    #[requires({
        let conflict = trail.abstract_justification(conflict@);
        trail.ghost.set_level(conflict) > 0 &&
        (forall< m : theory::Model> m.satisfy_set(conflict) ==> false)
    })]
    #[requires(forall<ix : TrailIndex> trail.contains(ix) ==> (ix.1@ == 0) == trail.ghost.is_decision(trail.index_logic(ix)))]
    #[ensures((^trail).invariant())]
    #[ensures((*trail).ghost.impls(*(^trail).ghost))]
    fn resolve_conflict(&mut self, trail: &mut Trail, conflict: Vec<TrailIndex>) {
        let mut heap: ConflictHeap = ConflictHeap::new();
        let old_conflict: Ghost![Vec<TrailIndex>] = gh! { conflict };
        let old_trail: Ghost![&mut Trail] = gh! { trail };

        #[invariant(forall<a : _> heap@.contains(a) == produced.contains(a))]
        for a in conflict {
            heap.insert(a);
        }

        let mut abs_cflct =
            gh! { theory::Conflict(trail.ghost.inner(), ix_to_abs(*trail, heap.shallow_model()))};

        let max_ix = *heap.last().unwrap();
        let conflict_level = max_ix.level();

        // The level in `abs_cflct` and `heap` agree
        gh! { ix_to_abs_level(*trail, heap.shallow_model()) };

        #[invariant(forall<ix : _> heap@.contains(ix) ==> trail.contains(ix))]
        #[invariant(trail.invariant())]
        // #[invariant(abs_cflct.1 == ix_to_abs(*trail, heap@))]
        #[invariant(forall<ix : _> heap@.contains(ix) ==> abs_cflct.1.contains(trail[ix]))]
        #[invariant(forall<a : _> abs_cflct.1.contains(a) ==> exists<ix : _> heap@.contains(ix) && trail[ix] == a)]
        #[invariant(abs_cflct.invariant() && abs_cflct.sound() && abs_cflct.0 == *trail.ghost && abs_cflct.level() == conflict_level@)]
        while let Some(ix) = heap.pop_last() {
            // proof_assert!(ix_to_abs_remove(*trail, ix, heap@); true);
            let rem_level = match heap.last() {
                Some(ix2) => ix2.level(),
                None => 0,
            };

            // proof_assert!(ix.level_log() == conflict_level@);
            proof_assert!(forall<i : _> heap@.contains(i) ==> i <= ix);
            proof_assert!(forall<i : _> heap@.contains(i) ==> i.level_log() <= ix.level_log());

            proof_assert!(set_max(heap@).level_log() == rem_level@ || rem_level@ == 0);
            proof_assert!(rem_level@ <= ix.level_log());
            proof_assert!(forall<i : _> heap@.contains(i) ==> i.level_log() <= rem_level@);

            proof_assert!(trail.contains(ix));
            // proof_assert!(abs_cflct.1.contains(trail[ix]));
            let a = trail[ix].clone();
            // Backjump
            if a.is_bool() && ix.level() > rem_level {
                proof_assert!(ix.level_log() == trail.ghost.level_of(trail[ix]));

                let _ = gh! { abs_cflct.backjump2(trail[ix]) };

                let oheap = gh! { heap };
                let just = heap.into_vec();

                let old = gh! { trail.abstract_justification(just.shallow_model()) };
                gh! { set_remove(*old, trail[ix]) };

                proof_assert!(forall<a : _> ix_to_abs(*trail, oheap@).contains(a) ==> old.contains(a));
                proof_assert!(old.ext_eq(abs_cflct.1.remove(trail[ix])));

                let old_trail = gh! { *trail};

                trail.restrict(rem_level);

                gh!(trail.abs_just_equiv(*old_trail, just.shallow_model()));
                info!("backjump");

                gh! { set_remove(*old, trail[ix]) };
                gh! { abs_cflct.learn_justified(old_trail[ix]) };
                // proof_assert!(forall<a : _> old.contains(a) ==>
                //     abs_cflct.1.remove(trail[ix]).contains(a)
                // );
                trail.add_justified(just, a.term, a.val.negate());

                return;
            }

            // proof_assert!(!trail.ghost.is_input(trail[ix]));

            // Undo Clear
            if a.is_first_order() && a.is_decision() {
                // info!("undo clear {a}");
                info!("undo clear");
                trail.restrict(ix.level() - 1);
                return;
            }

            // The key fact we need to prove is that `ix` has the level of the conflict.
            // This would simplify the following assertion.
            proof_assert!(trail.ghost.level_of(trail[ix]) > 0);
            gh!(theory::Trail::is_input_inv);
            proof_assert!(!trail.ghost.is_input(trail[ix]));
            proof_assert!(!trail.ghost.is_decision(trail[ix]));
            proof_assert!(trail.ghost.is_justified(trail[ix]));
            gh! {trail.ghost.justified_is_bool(trail[ix])};
            // proof_assert!(trail[ix].1.is_bool());
            let just = trail.justification(ix);
            let just_ghost = gh! { just };
            // proof_assert!(forall<i : _> 0 <= i && i < just@.len() ==> trail.contains(just[i]));

            let abs_just = gh! { trail.abstract_justification(just@)};
            #[invariant(forall<i : _> 0 <= i && i < produced.len() ==>
                abs_just.contains(trail[*produced[i]])
            )]
            #[invariant(forall<i : _> 0 <= i && i < produced.len() ==>
                ! trail[*produced[i]].1.is_bool() ==>
                trail.ghost.is_decision(trail[*produced[i]]) ==>
                trail.ghost.level_of(trail[*produced[i]]) < abs_cflct.level()
            )]
            for jix in just.iter() {
                proof_assert!(just_ghost@.contains(*jix));
                assert!(jix.level() <= ix.level());
                let j = &trail[*jix]; // should pass
                if j.is_first_order() && j.is_decision() {
                    if jix.level() == ix.level() {
                        info!("undo decide");

                        trail.restrict(ix.level() - 1);
                        trail.add_decision(a.term, a.val.negate());
                        return;
                    } else {
                        assert!(jix.level() < ix.level());
                        proof_assert!(trail.ghost.level_of(trail[*jix]) < abs_cflct.level());
                    }
                }
            }
            // here we need to prove that `produced == just`

            info!("resolve");

            abs_cflct = gh! { abs_cflct.resolvef(a.term_value()) };

            let old_heap: Ghost![ConflictHeap] = gh! { heap };

            // Resolve
            #[invariant(forall<a : _> heap@.contains(a) == (old_heap@.contains(a) || produced.contains(a)))]
            #[invariant(forall<a : _> produced.contains(a) ==> just_ghost@.contains(a))]
            #[invariant(forall<a : _> produced.contains(a) ==> heap@.contains(a))]
            for a in just {
                // let _ = gh!(ix_to_abs_insert(*trail, a, heap.shallow_model()));

                heap.insert(a);
            }

            // proof_assert!(heap@.ext_eq(old_heap@.union(produced....)))
        }
    }
}

#[ghost]
#[open(self)]
#[ensures(forall<x : _> a != x ==> s.contains(x) ==> s.remove(a).contains(x))]
fn set_remove<T>(s: FSet<T>, a: T) {}

#[ghost]
#[open(self)]
#[ensures(forall<x : _> s.remove(a).contains(x) ==> s.contains(x))]
fn set_remove2<T>(s: FSet<T>, a: T) {}

#[derive(Debug, PartialEq, Eq, DeepModel)]
pub enum Answer {
    Sat,
    Unsat,
}

#[derive(Debug)]
pub enum ExtendResult {
    Conflict(Vec<TrailIndex>),
    Decision(Term, Value),
    Satisfied,
}

// trait Theory {
//     // Requires `self` to be coherent up to `last_index` with `tl`
//     // Ensures `self` is fully coherent with `^tl`
//     // Returns an acceptable decision
//     // Returns sat when is satisfied by trail
//     // Returns conflict when there is a conflict
//     fn extend(&mut self, tl: &mut Trail) -> ExtendResult;

//     // Restricts it's model to be at most `level` deep.
//     // Ensures that is consistent up to `tl` len
//     fn restrict(&mut self, level: usize, tl: &Trail);

//     // Must be invariant to extensions of the trail beyond `ix` ie has 'prefix property'
//     #[predicate]
//     fn coherent(self, tl: Trail, ix: usize);

//     // The last index that we have seen and can be held accountable for
//     #[ghost]
//     fn last_index(self) -> usize;
// }

// use crate::bag::*;
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
struct ConflictHeap(BTreeSet<TrailIndex>);

impl ConflictHeap {
    #[trusted]
    #[ensures(result@ == FSet::EMPTY)]
    fn new() -> Self {
        ConflictHeap(BTreeSet::new())
    }

    #[trusted]
    #[ensures((^self)@ == (self@).insert(e))]
    fn insert(&mut self, e: TrailIndex) -> bool {
        self.0.insert(e)
    }

    #[trusted]
    #[ensures(
        match result {
            Some(a) => self@.contains(*a) && set_max(self@) == *a,
            None => self@ == FSet::EMPTY
        })]
    fn last(&self) -> Option<&TrailIndex> {
        self.0.last()
    }

    #[trusted]
    #[ensures(((self@) == FSet::EMPTY) == (result == None))]
    #[ensures(forall<a : _> result == Some(a) ==>
        (^self)@ == (self@).remove(a) && (self@).contains(a) &&
        (forall<other : TrailIndex> ((^self)@).contains(other) ==> other <= a)
    )]
    fn pop_last(&mut self) -> Option<TrailIndex> {
        self.0.pop_last()
    }

    #[trusted]
    #[ensures(forall<e : _> self@.contains(e) == result@.contains(e))]
    #[ensures(forall<i : _> 0 <= i && i < result@.len() ==> self@.contains(result@[i]))]
    #[ensures(result@.len() == self@.len())]
    #[ensures(seq_unique(result@))]
    fn into_vec(self) -> Vec<TrailIndex> {
        // self.0.into_vec()
        self.0.into_iter().collect()
    }
}
