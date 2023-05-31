// use ::std::collections::{BinaryHeap, HashSet};
// // use creusot_contracts::derive::{PartialEq};

use ::std::collections::BTreeSet;
use ::std::collections::BinaryHeap;

// use creusot_contracts::*;
use crate::theory;
use crate::trail::*;
use creusot_contracts::logic::*;
use creusot_contracts::std::*;
use creusot_contracts::{vec, *};
use priority_queue::PriorityQueue;

pub struct Solver {
    bool_th: BoolTheory,
}

enum TheoryState {
    Sat,
    Decision(Term, Value),
    Unknown,
}

impl Solver {
    pub fn new() -> Self {
        Solver {
            bool_th: BoolTheory,
        }
    }

    #[requires(trail.invariant())]
    #[ensures((^trail).invariant())]
    #[ensures(trail.ghost.impls(*(^trail).ghost))]
    #[ensures(match result {
        Answer::Unsat => trail.unsat(),
        Answer::Sat => true, // ignore completeness for now.
        Answer::Unknown => true,
    })]
    pub fn solver(&mut self, trail: &mut Trail) -> Answer {
        let old_trail: Ghost<&mut Trail> = ghost! { trail };
        // Invariant:
        // Every theory is coherent up to last_index with the trail
        // Invariant: trail is sound & has type invariants
        #[invariant(trail.invariant())]
        #[invariant(^trail == ^*old_trail)]
        #[invariant(old_trail.ghost.impls(*trail.ghost))]
        loop {
            // Tracks if all theories are satisfied with the trail.
            let mut states;
            // Invariant:
            // TheoryState::Sat => Theory_k is Sat for trail
            // TheoryState::Decision => the decision is acceptable with the current trail
            // Invariant:
            // Every theory is coherent up to last_index with the trail
            // Invariant: trail is sound & has type invariants
            #[invariant(trail.invariant())]
            #[invariant(^trail == ^*old_trail)]
            #[invariant(old_trail.ghost.impls(*trail.ghost))]
            loop {
                // println!("{:?}", trail.len());
                let trail_len = trail.len();
                let th_res = self.bool_th.extend(trail);
                if trail_len != trail.len() {
                    states = TheoryState::Unknown;
                };

                // eprintln!("boolean said {th_res:?}");
                match th_res {
                    ExtendResult::Conflict(c) => {
                        if trail.max_level(&c) == 0 {
                            // eprintln!("{trail:?}");
                            proof_assert!(theory::Normal(*trail.ghost).fail2(trail.abstract_justification(c@)));
                            return Answer::Unsat;
                        };
                        states = TheoryState::Unknown;
                        // need to calculate level of a set
                        // proof_assert!(Normal(trail.ghost).conflict_solve2(trail.abstract_justification(c ), Conflict(trail.ghost, trail.abstract_justification(c@), 0)));
                        self.resolve_conflict(trail, c)
                    }
                    ExtendResult::Decision(t, v) => states = TheoryState::Decision(t, v),
                    ExtendResult::Satisfied => states = TheoryState::Sat,
                }

                if matches!(states, TheoryState::Decision(_, _) | TheoryState::Sat) {
                    break;
                }
            }

            proof_assert! { trail.invariant() };

            // Assert: Every theory is fully coherent with the trail
            // Assert: Theory states are necessarily either decision or sat
            // Assert: Every theory is sat => formula is sat
            match states {
                TheoryState::Sat => return Answer::Sat,
                TheoryState::Decision(t, v) => trail.add_decision(t, v),
                _ => unreachable!(),
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
    fn resolve_conflict(&mut self, trail: &mut Trail, conflict: Vec<TrailIndex>) {
        // eprintln!("conflict!");
        let mut heap: ConflictHeap = ConflictHeap::new();
        let mut abs_cflct: Ghost<theory::Conflict> = ghost! { theory::Conflict(trail.ghost.inner(), trail.abstract_justification(conflict.shallow_model()))};

        #[invariant(forall<a : _> produced.contains(a) ==> (heap@).contains(a))]
        #[invariant(forall<i : _> 0 <= i && i < produced.len() ==> (heap@).contains(produced[i]))]
        #[invariant(forall<a :_> (heap@).contains(a) ==> produced.contains(a))]
        for a in conflict {
            heap.insert(a);
        }
        proof_assert!(forall<a : _> (heap@).contains(a) ==> abs_cflct.1.contains(trail.index_logic(a)));

        proof_assert!((heap@) != FSet::EMPTY);
        let max_ix = *heap.last().unwrap();
        let conflict_level = max_ix.level();
        proof_assert!(exists<ix : _> (heap@).contains(ix) && ix.level_log() > 0);
        proof_assert!(0 < conflict_level@);
        #[invariant(abs_cflct.0 == *trail.ghost)]
        #[invariant(abs_cflct.sound())]
        #[invariant(abs_cflct.invariant())]
        #[invariant(forall<ix : _> (heap@).contains(ix) ==> ix.level_log() <= conflict_level@)]
        // #[invariant(ix_to_abs(*trail, heap@) == abs_cflct.1)]
        #[invariant(forall<a : _> (heap@).contains(a) ==> trail.contains(a) && abs_cflct.1.contains(trail.index_logic(a)))]
        #[invariant(forall< a : _> abs_cflct.1.contains(a) ==> exists<ix : _> trail.contains(ix) && (heap@).contains(ix) && trail.index_logic(ix) == a)]
        while let Some(ix) = heap.pop_last() {
            // proof_assert!(ix_to_abs_remove(*trail, ix, heap@); true);
            proof_assert!(!(heap@).contains(ix));
            // proof_assert!(ix_to_abs_remove(abs_cflct.0, ))
            proof_assert!(ix.level_log() <= max_ix.level_log());
            let rem_level = match heap.last() {
                Some(ix2) => {
                    proof_assert!(ix2.level_log() <= ix.level_log());
                    ix2.level()
                }
                None => 0,
            };

            // proof_assert!(ix_to_abs(*trail, heap@).ext_eq(abs_cflct.1.remove(trail.index_logic(ix))));

            // TODO: Show this to be true because the rem_level is the second highest level. (Spec of peek)
            proof_assert!(abs_cflct.0.set_level(abs_cflct.1.remove(trail.index_logic(ix))) == rem_level@);

            let a = trail[ix].clone();
            proof_assert!(trail.contains(ix));
            proof_assert!(rem_level@ <= abs_cflct.level());
            proof_assert!(rem_level@ <= ix.level_log());
            proof_assert!(ix.level_log() == abs_cflct.level());

            // Backjump
            if a.is_bool() && ix.level() > rem_level {
                proof_assert!(trail.contains(ix));
                proof_assert!(ix.level_log() == abs_cflct.0.level_of(trail.index_logic(ix)));
                proof_assert!(trail.index_logic(ix) == a.term_value());
                trail.restrict(rem_level);
                let just = heap.into_vec();
                proof_assert!(rem_level@ < ix.level_log());
                proof_assert!(abs_cflct.0.set_level(abs_cflct.1.remove(a.term_value())) == rem_level@);
                proof_assert!(abs_cflct.0.set_level(abs_cflct.1) == ix.level_log());
                proof_assert!(
                    abs_cflct.0.set_level(abs_cflct.1.remove(a.term_value())) < ix.level_log()
                );
                proof_assert! { abs_cflct.backjump2_pre(a.term_value()) };
                let n: Ghost<theory::Normal> = ghost! { abs_cflct.backjump2(a.term_value()) };
                proof_assert!(abs_cflct.0.acceptable(a.term_value().0, a.term_value().1));

                trail.add_justified(just, a.term, a.val.negate());

                return;
            }

            // False?
            // proof_assert!((a@.val).is_bool() ==> !trail.ghost.is_decision(a.term_value()));
            // if a is a boolean then the rem_level == ix_level which if we have dec < just implies it must be justified.

            // If we use an order st dec < just then this is not enough...

            // Undo Clear
            if a.is_first_order() && a.is_decision() {
                trail.restrict(ix.level() - 1);
                return;
            }

            // Use an order such that decision < justified,
            // thus we should now have that rem_level == level???

            proof_assert!(forall<t : theory::Trail, a :_> t.is_decision(a) ==> !t.is_input(a) && !t.is_justified(a));
            // It can't be a boolean deceision
            proof_assert!(!(trail.ghost.is_decision(a.term_value()) && (a@.val).is_bool()));
            // It can't be a boolean deceision
            proof_assert!(!(trail.ghost.is_decision(a.term_value()) && !(a@.val).is_bool()));
            proof_assert!(!trail.ghost.is_decision(a.term_value()));
            // Trivial: Trail has non-zero level so by invariant we can't be input.
            //  Proof is blocked due to properties of `find`.
            proof_assert!({
                trail.ghost.is_input_inv(a.term_value());
                !trail.ghost.is_input(a.term_value())
            });
            proof_assert!(trail.ghost.is_justified(a.term_value()));
            // proof_assert!()
            let just = trail.justification(ix);

            proof_assert!(trail.ghost.justified_is_bool(a.term_value()); true);
            proof_assert!(trail.ghost.is_justified(a.term_value()) && a.term_value().1.is_bool());

            proof_assert!(forall<i : _> 0 <= i && i < just@.len() ==> trail.contains(just@[i]));
            #[invariant(forall<i : _> 0 <= i && i < produced.len() ==> !trail.index_logic(*produced[i]).1.is_bool() ==>
                    abs_cflct.0.is_decision(trail.index_logic(*produced[i])) ==>
                    abs_cflct.0.level_of(trail.index_logic(*produced[i])) < abs_cflct.0.set_level(abs_cflct.1))]
            for jix in just.iter() {
                let j = &trail[*jix]; // should pass

                proof_assert!(jix.level_log() <= ix.level_log());
                // proof_assert!(abs_cflct.0.level_of(trail.index_logic(*jix)) <= abs_cflct.0.level_of(trail.index_logic(ix)));
                if jix.level() == ix.level() && j.is_first_order() && j.is_decision() {
                    // undo decide
                    trail.restrict(ix.level() - 1);
                    trail.add_decision(a.term, a.val.negate());
                    return;
                }

                proof_assert!(j.reason == Reason::Decision ==> trail.ghost.is_decision(trail.index_logic(*jix)));
                proof_assert!(j.reason == Reason::Input ==> trail.ghost.is_input(trail.index_logic(*jix)));
                proof_assert!((exists<v:_> j.reason == Reason::Justified(v)) ==> trail.ghost.is_justified(trail.index_logic(*jix)));

                proof_assert!(!(
                    jix.level_log() == ix.level_log() &&
                    !j.val@.is_bool() &&
                    abs_cflct.0.is_decision(j.term_value())
                ));
                proof_assert!((abs_cflct.0.is_decision(j.term_value()) && !j@.val.is_bool()) ==> jix.level_log() < ix.level_log());

                // proof_assert!(
                //     trail.index_logic(*jix).1.is_bool() ||
                //     !abs_cflct.0.is_decision(trail.index_logic(*jix)) ||
                //     abs_cflct.0.level_of(trail.index_logic(*jix)) != abs_cflct.0.level_of(trail.index_logic(ix))
                // );
            }

            proof_assert!(
                let j = trail.abstract_justification(just@);
                forall<t : _> j.contains(t) ==> !t.1.is_bool() ==>
                    abs_cflct.0.is_decision(t) ==>
                    abs_cflct.0.level_of(t) < abs_cflct.0.set_level(abs_cflct.1)
            );

            // TODO MINIMIZE ASSERTIONS
            // Do abstract resolve rule here
            let old_c: Ghost<theory::Conflict> = ghost! { abs_cflct.inner() };
            abs_cflct = ghost! { abs_cflct.resolvef(a.term_value()) };

            let old_heap: Ghost<ConflictHeap> = ghost! { heap };

            proof_assert!(ix.level_log() <= conflict_level@);

            proof_assert!(
                forall<i : _ > 0 <= i && i < just@.len() ==> abs_cflct.1.contains(trail.index_logic(just@[i]))
            );

            // Resolve
            #[invariant(forall<ix : _> (heap@).contains(ix) ==> ix.level_log() <= conflict_level@)]
            #[invariant(forall<a : _> (heap@).contains(a) ==> trail.contains(a) && abs_cflct.1.contains(trail.index_logic(a)))]
            #[invariant(forall<ix : _> (old_heap@).contains(ix) ==> (heap@).contains(ix))]
            #[invariant(forall<i : _> 0 <= i && i < produced.len() ==> (heap@).contains(produced[i]))]
            // Need invariant saying we only add things
            for a in just {
                proof_assert!(a.level_log() <= ix.level_log());
                proof_assert!(abs_cflct.1.contains(trail.index_logic(a)));
                heap.insert(a);
            }

            proof_assert!(old_c.0.is_justified(a.term_value()));
            proof_assert!(old_c.1.contains(a.term_value()));

            // Key missing property
            //
            // The reasoning should be that if
            proof_assert!(let just = old_c.0.justification(a.term_value());
                forall<a : (theory::Term, theory::Value)> just.contains(a) && !a.1.is_bool() ==>
                old_c.0.is_decision(a) ==>
                old_c.0.level_of(a) < old_c.0.set_level(old_c.1)
            );

            proof_assert!((*old_c).resolve(a.term_value(), *abs_cflct));
        }
    }
}

#[logic]
#[variant(s.len())]
#[ensures(forall<ix :_> s.contains(ix) ==> result.contains(t.index_logic(ix)))]
#[ensures(forall<a :_> result.contains(a) ==> exists<ix :_> a == t.index_logic(ix) && s.contains(ix))]
fn ix_to_abs(t: Trail, s: FSet<TrailIndex>) -> FSet<(theory::Term, theory::Value)> {
    if s == FSet::EMPTY {
        FSet::EMPTY
    } else {
        let a = s.peek();
        ix_to_abs(t, s.remove(a)).insert(t.index_logic(a))
    }
}

#[logic]
#[variant(s.len())]
#[requires(t.contains(x))]
#[ensures(ix_to_abs(t, s.remove(x)) == ix_to_abs(t, s).remove(t.index_logic(x)))]
fn ix_to_abs_remove(t: Trail, x: TrailIndex, s: FSet<TrailIndex>) {
    if s == FSet::EMPTY {
        ()
    } else {
        let a = s.peek();
        ix_to_abs_remove(t, x, s.remove(a))
    }
}

// #[derive(Debug, PartialEq, Eq)]
pub enum Answer {
    Sat,
    Unsat,
    Unknown,
}

#[cfg_attr(not(creusot), derive(Debug))]
enum ExtendResult {
    Conflict(Vec<TrailIndex>),
    Decision(Term, Value),
    Satisfied,
}

struct BoolTheory;

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
//     #[logic]
//     fn last_index(self) -> usize;
// }

impl BoolTheory {
    // Extend the trail with 1 or more deductions, or backtrack to a non-conflicting state
    // Returns `Fail` if we encounter a conflict at level 0
    // Return Satisfied if the trail is satisfactory to us
    #[trusted]
    #[maintains((mut tl).invariant())]
    #[ensures(match result {
        ExtendResult::Satisfied => true,
        ExtendResult::Decision(t, v) => (^tl).ghost.acceptable(t@, v@),
        ExtendResult::Conflict(c) => {
            let conflict = (^tl).abstract_justification(c@);

            // members of conflict area within the trail
            true
            // (forall<i : _> 0 <= i && i < (c@).len() ==> @(c@)[i] < (@(^tl).assignments).len()) &&
            // (forall<m : theory::Model> m.satisfy_set(conflict) ==> false)
        }
    })]
    #[ensures(tl.ghost.impls(*(^tl).ghost))]
    fn extend(&mut self, tl: &mut Trail) -> ExtendResult {
        let mut iter = tl.indices();

        while let Some(ix) = iter.next() {
            let tl = iter.trail();

            if tl[ix].is_bool() {
                match self.eval(tl, &tl[ix].term) {
                    Result::Err(dec) => {
                        return ExtendResult::Decision(dec, Value::Bool(true));
                    }
                    Result::Ok((mut subterms, res)) => {
                        if res != tl[ix].val {
                            subterms.push(ix);
                            return ExtendResult::Conflict(subterms);
                        }
                    }
                }
            }
        }

        // while i < tl.len() {

        //     i += 1;
        // }

        return ExtendResult::Satisfied;
    }

    // Ensures:
    //  - Free Var list is non-empty, all not on trail
    //  - If ok: there is a justified entailment between the justification and tm <- value?
    // #[ensures(forall<just : _, val: _> result == Ok((just, val)) ==> forall<m : _> m.satisfy_set(just@) ==> m.satisfies((tm@, val@)))]
    #[trusted]
    fn eval(&mut self, tl: &Trail, tm: &Term) -> Result<(Vec<TrailIndex>, Value), Term> {
        match tm {
            Term::Eq(l, r) => {
                let (mut j1, v1) = self.eval_memo(tl, l)?;
                let (j2, v2) = self.eval_memo(tl, r)?;
                j1.extend(j2);
                return Ok((j1, Value::Bool(v1 == v2)));
            }
            Term::Conj(l, r) => {
                let (mut j1, v1) = self.eval_memo(tl, l)?;
                let (j2, v2) = self.eval_memo(tl, r)?;
                j1.extend(j2);
                return Ok((j1, Value::Bool(v1.bool() && v2.bool())));
            }
            Term::Disj(l, r) => {
                let (mut j1, v1) = self.eval_memo(tl, l)?;
                let (j2, v2) = self.eval_memo(tl, r)?;
                j1.extend(j2);
                return Ok((j1, Value::Bool(v1.bool() || v2.bool())));
            }
            Term::Neg(t) => {
                let (j, v) = self.eval_memo(tl, t)?;
                Ok((j, v.negate()))
            }
            a => match tl.index_of(a) {
                Some(i) => Ok((vec![i], tl[i].value().clone())),
                None => Err(a.clone()),
            },
        }
    }

    #[trusted]
    fn eval_memo(&mut self, tl: &Trail, tm: &Term) -> Result<(Vec<TrailIndex>, Value), Term> {
        if let Some(x) = tl.index_of(tm) {
            return Ok((vec![x], tl[x].val.clone()));
        }
        self.eval(tl, tm)
    }
}

// use crate::bag::*;
impl creusot_contracts::ShallowModel for ConflictHeap {
    type ShallowModelTy = FSet<TrailIndex>;

    #[logic]
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
    fn into_vec(self) -> Vec<TrailIndex> {
        // self.0.into_vec()
        self.0.into_iter().collect()
    }
}
