// use ::std::collections::{BinaryHeap, HashSet};
// // use creusot_contracts::derive::{PartialEq};

use ::std::collections::BTreeSet;
use ::std::collections::BinaryHeap;

// use creusot_contracts::*;
use crate::theory;
use crate::trail::*;
use creusot_contracts::{vec, *};
use creusot_contracts::logic::*;
use creusot_contracts::std::*;
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
        #[invariant(tl_inv, trail.invariant())]
        #[invariant(proph, ^trail == ^*old_trail)]
        #[invariant(sound, old_trail.ghost.impls(*trail.ghost))]
        loop {
            // Tracks if all theories are satisfied with the trail.
            let mut states;
            // Invariant:
            // TheoryState::Sat => Theory_k is Sat for trail
            // TheoryState::Decision => the decision is acceptable with the current trail
            // Invariant:
            // Every theory is coherent up to last_index with the trail
            // Invariant: trail is sound & has type invariants
            #[invariant(tl_inv, trail.invariant())]
            #[invariant(proph, ^trail == ^*old_trail)]
            #[invariant(sound, old_trail.ghost.impls(*trail.ghost))]
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
                            proof_assert!(theory::Normal(*trail.ghost).fail2(trail.abstract_justification(@c)));
                            return Answer::Unsat;
                        };
                        states = TheoryState::Unknown;
                        // need to calculate level of a set
                        // proof_assert!(Normal(trail.ghost).conflict_solve2(trail.abstract_justification(@c), Conflict(trail.ghost, trail.abstract_justification(@c), 0)));
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
    #[requires((@conflict).len() > 0)]
    #[requires(forall< i : _ > 0 <= i && i < (@conflict).len() ==> trail.contains((@conflict)[i]))]
    #[requires({
        let conflict = trail.abstract_justification(@conflict);
        trail.ghost.set_level(conflict) > 0 &&
        (forall< m : theory::Model> m.satisfy_set(conflict) ==> false)
    })]
    fn resolve_conflict(&mut self, trail: &mut Trail, conflict: Vec<TrailIndex>) {
        // eprintln!("conflict!");
        let mut heap: ConflictHeap = ConflictHeap::new();
        let mut abs_cflct: Ghost<theory::Conflict> = ghost! { theory::Conflict(trail.ghost.inner(), trail.abstract_justification(conflict.shallow_model()))};

        #[invariant(mem, forall<a : _> produced.contains(a) ==> (@heap).contains(a))]
        #[invariant(mem, forall<i : _> 0 <= i && i < produced.len() ==> (@heap).contains(produced[i]))]
        #[invariant(mem2, forall<a :_> (@heap).contains(a) ==> produced.contains(a))]
        for a in conflict {
            heap.insert(a);
        }
        proof_assert!(forall<a : _> (@heap).contains(a) ==> abs_cflct.1.contains(trail.index_logic(a)));

        proof_assert!((@heap) != FSet::EMPTY);
        let max_ix = *heap.last().unwrap();
        let conflict_level = max_ix.level();
        proof_assert!(exists<ix : _> (@heap).contains(ix) && ix.level_log() > 0);
        proof_assert!(0 < @conflict_level);
        #[invariant(cflict, abs_cflct.0 == *trail.ghost)]
        #[invariant(cflct_sound, abs_cflct.sound())]
        #[invariant(cflict_inv, abs_cflct.invariant())]
        #[invariant(level, forall<ix : _> (@heap).contains(ix) ==> ix.level_log() <= @conflict_level)]
        #[invariant(to_cflct, forall<a : _> (@heap).contains(a) ==> trail.contains(a) && abs_cflct.1.contains(trail.index_logic(a)))]
        #[invariant(from_cflct, forall< a : _> abs_cflct.1.contains(a) ==> exists<ix : _> trail.contains(ix) && (@heap).contains(ix) && trail.index_logic(ix) == a)]
        while let Some(ix) = heap.pop_last() {
            proof_assert!(!(@heap).contains(ix));

            proof_assert!(ix.level_log() <= max_ix.level_log());
            let rem_level = match heap.last() {
                Some(ix2) => {
                    proof_assert!(ix2.level_log() <= ix.level_log());
                    ix2.level()
                }
                None => 0,
            };

            let a = trail[ix].clone();
            proof_assert!(@rem_level <= ix.level_log());

            if a.is_bool() && ix.level() > rem_level {
                //     // TODO: Optimize this proof
                proof_assert!(trail.ghost.restrict_too_big(ix.level_log(), a.term_value()); true);
                proof_assert!(trail.ghost.contains_inverse(a.term_value()); true);
                let just = heap.into_vec();
                proof_assert!(forall<i : _> 0 <= i && i < (@just).len() ==> (@just)[i].level_log() <= @rem_level);

                proof_assert!(forall<b : _> b != a.term_value() ==> abs_cflct.1.contains(b) ==> exists<ix : _> (@just).contains(ix) && trail.index_logic(ix) == b);
                trail.restrict(rem_level);
                proof_assert!(forall<b : _> b != a.term_value() ==> abs_cflct.1.contains(b) ==> exists<ix : _> (@just).contains(ix) && trail.index_logic(ix) == b);

                proof_assert!((@a.term).is_bool());
                proof_assert!(forall<i : _> 0 <= i && i < (@just).len() ==> trail.contains((@just)[i]));
                proof_assert!(abs_cflct.learn_justified(a.term_value()); true);
                proof_assert!(forall<b : _> b != a.term_value() ==> abs_cflct.1.contains(b) ==> trail.abstract_justification(@just).contains(b));
                trail.add_justified(just, a.term, a.val.negate());
                // proof_assert!(abs_cflct.backjump(a.term_value(), theory::Normal(trail)));
                // eprintln!("backjump!");
                return;
            }

            if a.is_first_order() && a.decision() {
                trail.restrict(ix.level() - 1);
                // eprintln!("undo clear!");
                return;
            }

            // TODO: PROVE A is justified here
            //
            let just = trail.justification(ix);

            if rem_level == ix.level() {
                #[invariant(dummy, true)]
                for jix in just.iter() {
                    let j = &trail[*jix];

                    if jix.level() == ix.level() && j.is_first_order() && j.decision() {
                        // TODO: true because decisions cannot have level 0
                        proof_assert!(jix.level_log() > 0);
                        // TODO: True because justified assignments are always boolean and a is justified
                        proof_assert!((@a.val).is_bool());
                        // undo decide
                        trail.restrict(ix.level() - 1);
                        trail.add_decision(a.term, a.val.negate());
                        return;
                    }
                }
            }

            // TODO MINIMIZE ASSERTIONS
            proof_assert!(forall<m : theory::Model> m.entails(trail.abstract_justification(@just), a.term_value()));
            proof_assert!(forall<a : _> (@heap).contains(a) ==>abs_cflct.1.contains(trail.index_logic(a)));
            proof_assert!(forall<a : _> (@heap).contains(a) ==> trail.contains(a));
            // NEED TO SHOW THAT each concrete ix leads to a different abstract term
            // Only need to require that levels are unique
            proof_assert!(trail.contains(ix));
            proof_assert!(ix.level_log() == trail.ghost.level_of(a.term_value()));
            proof_assert!(forall<ix : _> (@heap).contains(ix) ==>abs_cflct.1.remove(a.term_value()).contains(trail.index_logic(ix)));
            // proof_assert!(forall< a2 : _> abs_cflct.1.remove(a).contains(a2) ==> exists<ix : _> (@heap).contains(ix) && trail.index_logic(ix) == a2);

            proof_assert!(trail.abstract_justification(@just) == trail.ghost.justification(trail.index_logic(ix)));
            // Do abstract resolve rule here
            let old_c : Ghost<theory::Conflict> = ghost! { abs_cflct.inner() };
            // abs_cflct = ghost! { theory::Conflict(abs_cflct.inner().0, abs_cflct.inner().1.remove(a.term_value()).union(trail.abstract_justification(just.shallow_model())))};
            abs_cflct = ghost! { abs_cflct.resolvef(a.term_value()) };

            proof_assert!(old_c.inner().resolve(a.term_value(), abs_cflct.inner()));

            proof_assert!(forall<a : _> (@heap).contains(a) ==>abs_cflct.1.contains(trail.index_logic(a)));
            let old_heap: Ghost<ConflictHeap> = ghost! { heap };
            let abs_just: Ghost<FSet<(theory::Term, theory::Value)>> = ghost! { trail.abstract_justification(just.shallow_model()) };
            proof_assert!(forall<a : _> abs_just.contains(a) ==> exists<ix : TrailIndex> (@just).contains(ix) && trail.index_logic(ix) == a);
            // Resolve
            #[invariant(level, forall<ix : _> (@heap).contains(ix) ==> ix.level_log() <= @conflict_level)]
            #[invariant(to_cflct, forall<a : _> (@heap).contains(a) ==> trail.contains(a) && abs_cflct.1.contains(trail.index_logic(a)))]
            #[invariant(adding, forall<ix : _> (@old_heap).contains(ix) ==> (@heap).contains(ix))]
            #[invariant(seen, forall<i : _> 0 <= i && i < produced.len() ==> (@heap).contains(produced[i]))]
            // Need invariant saying we only add things
            for a in just {
                heap.insert(a);
            }

            proof_assert!(forall< a : _> abs_just.contains(a) ==> exists<ix : _> trail.contains(ix) && (@heap).contains(ix) && trail.index_logic(ix) == a);
            // True because either the value is in just (trivial), or it was in the heap already (and we only added things)
            proof_assert!(forall< a : _> abs_cflct.1.contains(a) ==> exists<ix : _> trail.contains(ix) && trail.index_logic(ix) == a);
            proof_assert!(forall< a : _> abs_cflct.1.contains(a) ==> exists<ix : _> (@heap).contains(ix) && trail.index_logic(ix) == a);
            proof_assert!(forall< a : _> abs_cflct.1.contains(a) ==> exists<ix : _> trail.contains(ix) && (@heap).contains(ix) && trail.index_logic(ix) == a);
        }
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
        ExtendResult::Decision(t, v) => (^tl).ghost.acceptable(@t, @v),
        ExtendResult::Conflict(c) => {
            let conflict = (^tl).abstract_justification(@c);

            // members of conflict area within the trail
            true
            // (forall<i : _> 0 <= i && i < (@c).len() ==> @(@c)[i] < (@(^tl).assignments).len()) &&
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
    // #[ensures(forall<just : _, val: _> result == Ok((just, val)) ==> forall<m : _> m.satisfy_set(@just) ==> m.satisfies((@tm, @val)))]
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
    #[ensures(@result == FSet::EMPTY)]
    fn new() -> Self {
        ConflictHeap(BTreeSet::new())
    }

    #[trusted]
    #[ensures(@^self == (@self).insert(e))]
    fn insert(&mut self, e: TrailIndex) -> bool {
        self.0.insert(e)
    }

    #[trusted]
    #[ensures(forall<a : _> result == Some(a) ==>
        (@self).contains(*a) &&
        forall<other : TrailIndex> (@self).contains(other) ==> other <= *a
    )]
    #[ensures(((@self) == FSet::EMPTY) == (result == None))]
    fn last(&self) -> Option<&TrailIndex> {
        self.0.last()
    }

    #[trusted]
    #[ensures(((@self) == FSet::EMPTY) == (result == None))]
    #[ensures(forall<a : _> result == Some(a) ==>
        @^self == (@self).remove(a) && (@self).contains(a) &&
        (forall<other : TrailIndex> (@^self).contains(other) ==> other <= a)
    )]
    fn pop_last(&mut self) -> Option<TrailIndex> {
        self.0.pop_last()
    }

    #[trusted]
    #[ensures(forall<e : _> (@self).contains(e) ==> (@result).contains(e))]
    #[ensures(forall<i : _> 0 <= i && i < (@result).len() ==> (@self).contains((@result)[i]))]
    fn into_vec(self) -> Vec<TrailIndex> {
        // self.0.into_vec()
        self.0.into_iter().collect()
    }
}
