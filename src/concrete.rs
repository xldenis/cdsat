// use ::std::collections::{BinaryHeap, HashSet};
// // use creusot_contracts::derive::{PartialEq};

use ::std::collections::BinaryHeap;

// use creusot_contracts::*;
use crate::theory;
use crate::trail::*;
use creusot_contracts::*;
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

    fn resolve_conflict(&mut self, trail: &mut Trail, conflict: Vec<TrailIndex>) {
        // eprintln!("conflict!");
        let mut heap: ConflictHeap = ConflictHeap::new();
        for a in conflict {
            heap.push(a);
        }

        let conflict_level = heap.peek().unwrap().level();

        while let Some(ix) = heap.pop() {
            let rem_level = match heap.peek() {
                Some(ix) => ix.level(),
                None => 0,
            };
            let a = trail[ix].clone();

            if a.is_bool() && ix.level() > rem_level {
                trail.restrict(rem_level);
                trail.add_justified(heap.into_vec(), a.term, a.val);
                // eprintln!("backjump!");
                return;
            }

            if a.is_first_order() && a.decision() && ix.level() > rem_level {
                trail.restrict(conflict_level - 1);
                // eprintln!("undo clear!");
                return;
            }

            if let Some(just) = trail.justification(&a) {
                for j in just.iter() {
                    let j = &trail[*j];
                    if j.level() == conflict_level && j.is_first_order() && j.decision() {
                        // undo decide
                        if rem_level == ix.level() {
                            trail.restrict(conflict_level - 1);
                            trail.add_decision(a.term().clone(), a.value().negate());
                            // eprintln!("undo decide!");
                            return;
                        }
                    }
                }

                for a in just {
                    heap.push(a);
                }
            }
        }
    }
}

// #[derive(Debug, PartialEq, Eq)]
pub enum Answer {
    Sat,
    Unsat,
    Unknown,
}

#[cfg_attr(not(feature = "contracts"), derive(Debug))]
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

#[trusted]
struct ConflictHeap(BinaryHeap<TrailIndex>);

impl ConflictHeap {
    #[trusted]
    fn new() -> Self {
        ConflictHeap(BinaryHeap::new())
    }

    #[trusted]
    fn push(&mut self, e: TrailIndex) {
        self.0.push(e)
    }

    #[trusted]
    fn peek(&self) -> Option<&TrailIndex> {
        self.0.peek()
    }

    #[trusted]
    fn pop(&mut self) -> Option<TrailIndex> {
        self.0.pop()
    }

    #[trusted]
    fn into_vec(self) -> Vec<TrailIndex> {
        self.0.into_vec()
    }
}
