// use ::std::collections::{BinaryHeap, HashSet};
// // use creusot_contracts::derive::{PartialEq};

use ::std::{collections::BTreeSet, fmt::Write};

use crate::term::{Term, Value};
// use creusot_contracts::*;
use crate::{bool::*, lra::*, theory, trail::*};
use creusot_contracts::{logic::*, std::*, PartialEq, *};
use log::info;
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
        let old = gh! { trail };
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
        pearlite!{ forall<t :_, v : _>
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
        let old_trail = gh ! { trail};
        #[invariant(old_trail.ghost.impls(*trail.ghost))]
        #[invariant(trail.invariant())]
        loop {
            let iter_trail = gh! { trail };
            self.bool_state = TheoryState::Unknown;
            self.lra_state = TheoryState::Unknown;
            #[invariant(iter_trail.ghost.impls(*trail.ghost))]
            #[invariant(trail.invariant())]
            #[invariant(self.dec_acc(*trail))]
            while self.can_deduce() {
                self.bool_state = TheoryState::Unknown;
                self.lra_state = TheoryState::Unknown;

                if let Some(cflct) = self.extend_next(trail) {
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
        // let mut s = String::from("resolving conflict ");
        // for i in &conflict {
        //     write!(s, "{} <- {} ", &trail[*i].term, &trail[*i].val).unwrap();
        // }
        // info!("{s}");

        let mut heap: ConflictHeap = ConflictHeap::new();
        let old_conflict: Ghost<Vec<TrailIndex>> = gh! { conflict };
        let old_trail: Ghost<&mut Trail> = gh! { trail };

        #[invariant(forall<a : _> produced.contains(a) ==> (heap@).contains(a))]
        #[invariant(forall<i : _> 0 <= i && i < produced.len() ==> (heap@).contains(produced[i]))]
        #[invariant(forall<a :_> (heap@).contains(a) ==> produced.contains(a))]
        for a in conflict {
            heap.insert(a);
        }
        proof_assert!(
            trail.abstract_justification(old_conflict.shallow_model())
                == ix_to_abs(*trail, heap.shallow_model())
        );
        let mut abs_cflct: Ghost<theory::Conflict> =
            gh! { theory::Conflict(trail.ghost.inner(), ix_to_abs(*trail, heap.shallow_model()))};

        let max_ix = *heap.last().unwrap();
        let conflict_level = max_ix.level();
        proof_assert!(exists<ix : _> (heap@).contains(ix) && ix.level_log() > 0);
        // proof_assert!(ix.level_log());
        proof_assert!(0 < conflict_level@);
        #[invariant(old_trail.ghost.impls(*trail.ghost))]
        #[invariant(abs_cflct.0 == *trail.ghost)]
        #[invariant(abs_cflct.sound())]
        #[invariant(abs_cflct.invariant())]
        #[invariant(abs_cflct.level() == conflict_level@)]
        // should be free from ix_to_abs
        #[invariant(forall<ix : _> (heap@).contains(ix) ==> ix.level_log() <= conflict_level@)]
        #[invariant(ix_to_abs(*trail, heap@) == abs_cflct.1)]
        // should come from ix_to_abs
        #[invariant(forall<a : _> (heap@).contains(a) ==> trail.contains(a) && abs_cflct.1.contains(trail.index_logic(a)))]
        // same
        #[invariant(forall< a : _> abs_cflct.1.contains(a) ==>
            exists<ix : _> trail.contains(ix) && (heap@).contains(ix) && trail.index_logic(ix) == a
        )]
        while let Some(ix) = heap.pop_last() {
            proof_assert!(ix.level_log() == abs_cflct.level());
            proof_assert!(ix_to_abs_remove(*trail, ix, heap@); true);
            let rem_level = match heap.last() {
                Some(ix2) => ix2.level(),
                None => 0,
            };

            // Some of these might be useless
            proof_assert!(ix_to_abs(*trail, heap@).ext_eq(abs_cflct.1.remove(trail.index_logic(ix))));
            proof_assert!(abs_cflct.0.set_level(abs_cflct.1) == ix.level_log());
            proof_assert!({ix_to_abs_level(*trail, heap@); true});
            proof_assert!(abs_cflct.0.set_level(abs_cflct.1.remove(trail.index_logic(ix))) == rem_level@);

            let a = trail[ix].clone();
            // Backjump
            if a.is_bool() && ix.level() > rem_level {
                proof_assert!(trail.index_logic(ix) == a.term_value());
                // Somehow this should provide us the info we need to say that the justification won't change from restriction?
                let _: Ghost<bool> = gh! { abs_cflct.backjump2(a.term_value()); true };

                let oheap: Ghost<ConflictHeap> = gh! { heap };
                let just = heap.into_vec();

                let _: Ghost<()> =
                    gh!(seq_to_set(*trail, just.shallow_model(), oheap.shallow_model()));

                let old: Ghost<FSet<(theory::Term, theory::Value)>> = gh! { trail.abstract_justification(just.shallow_model()) };
                trail.restrict(rem_level);
                let new: Ghost<FSet<(theory::Term, theory::Value)>> = gh! { trail.abstract_justification(just.shallow_model()) };

                proof_assert!(new.ext_eq(*old));
                trail.add_justified(just, a.term, a.val.negate());
                return;
            }

            // Undo Clear
            if a.is_first_order() && a.is_decision() {
                trail.restrict(ix.level() - 1);
                return;
            }

            proof_assert!(forall<t : theory::Trail, a :_> t.is_decision(a) ==> !t.is_input(a) && !t.is_justified(a));
            proof_assert!(abs_cflct.0.is_decision(a.term_value()) ==> ix.level_log() > rem_level@);

            // It can't be a boolean deceision
            proof_assert!(!trail.ghost.is_decision(a.term_value()));
            // Trivial: Trail has non-zero level so by invariant we can't be input.
            proof_assert!({
                trail.ghost.is_input_inv(a.term_value());
                true
            });
            proof_assert!(trail.ghost.is_justified(a.term_value()));
            let just = trail.justification(ix);

            proof_assert!(trail.ghost.justified_is_bool(a.term_value()); true);

            #[invariant(forall<i : _> 0 <= i && i < produced.len() ==> !trail.index_logic(*produced[i]).1.is_bool() ==>
                    abs_cflct.0.is_decision(trail.index_logic(*produced[i])) ==>
                    abs_cflct.0.level_of(trail.index_logic(*produced[i])) < abs_cflct.0.set_level(abs_cflct.1))]
            for jix in just.iter() {
                let j = &trail[*jix]; // should pass
                proof_assert!(trail.contains(*jix));
                if j.is_first_order() && j.is_decision() {
                    if jix.level() == ix.level() {
                        // undo decide
                        trail.restrict(ix.level() - 1);
                        trail.add_decision(a.term, a.val.negate());
                        return;
                    } else {
                        proof_assert!(jix.level_log() < ix.level_log());
                    }
                }

                proof_assert!(!trail.index_logic(*jix).1.is_bool() ==>
                    abs_cflct.0.is_decision(trail.index_logic(*jix)) ==>
                    abs_cflct.0.level_of(trail.index_logic(*jix)) < abs_cflct.0.set_level(abs_cflct.1)
                );
            }

            proof_assert!(
                let j = trail.abstract_justification(just@);
                forall<t : _> j.contains(t) ==> !t.1.is_bool() ==>
                    abs_cflct.0.is_decision(t) ==>
                    abs_cflct.0.level_of(t) < abs_cflct.0.set_level(abs_cflct.1)
            );

            #[allow(unused)]
            abs_cflct = gh! { abs_cflct.resolvef(a.term_value()) };

            let old_heap: Ghost<ConflictHeap> = gh! { heap };

            proof_assert!(
                forall<i : _ > 0 <= i && i < just@.len() ==> abs_cflct.1.contains(trail.index_logic(just@[i]))
            );
            proof_assert!(ix_to_abs(*trail, heap.shallow_model()).union(trail.abstract_justification(just@)) == abs_cflct.1);

            // Resolve
            #[invariant(forall<ix : _> (heap@).contains(ix) ==> ix.level_log() <= conflict_level@)]
            #[invariant(forall<a : _> (heap@).contains(a) ==> trail.contains(a) && abs_cflct.1.contains(trail.index_logic(a)))]
            #[invariant(forall<ix : _> (old_heap@).contains(ix) ==> (heap@).contains(ix))]
            // #[invariant(forall<i : _> 0 <= i && i < produced.len() ==> (heap@).contains(produced[i]))]
            #[invariant(ix_to_abs(*trail, heap@) == ix_to_abs(*trail, old_heap@).union(trail.abstract_justification(*produced)))]
            // Need invariant saying we only add things
            for a in just {
                let _: Ghost<()> = gh!(ix_to_abs_insert(*trail, a, heap.shallow_model()));
                proof_assert!(abstract_justification_insert(*trail, a, just@) == ());
                proof_assert!(a.level_log() <= ix.level_log());
                proof_assert!(abs_cflct.1.contains(trail.index_logic(a)));
                heap.insert(a);
            }
        }
    }
}

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
    #[ensures(forall<a : _> result == Some(a) ==>
        (self@).contains(*a) &&
        forall<other : TrailIndex> (self@).contains(other) ==> other <= *a
    )]
    #[ensures(((self@) == FSet::EMPTY) == (result == None))]
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
    #[ensures(forall<e : _> (self@).contains(e) ==> (result@).contains(e))]
    #[ensures(forall<i : _> 0 <= i && i < (result@).len() ==> (self@).contains((result@)[i]))]
    #[ensures(result@.len() == self@.len())]
    #[ensures(seq_unique(result@))]
    fn into_vec(self) -> Vec<TrailIndex> {
        // self.0.into_vec()
        self.0.into_iter().collect()
    }
}
