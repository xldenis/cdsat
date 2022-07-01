use std::collections::{BinaryHeap, HashSet};

use creusot_contracts::proof_assert;
use priority_queue::PriorityQueue;

use crate::trail::*;

pub struct Solver {
    bool_th: BoolTheory,
}

enum TheoryState {
    Sat,
    Decision(Term, Value),
    Unknown,
}

impl Solver {
    pub fn solver(&mut self, trail: &mut Trail) -> Answer {
        // Invariant:
        // Every theory is coherent up to last_index with the trail
        // Invariant: trail is sound & has type invariants
        loop {
            // Tracks if all theories are satisfied with the trail.
            let mut states = TheoryState::Unknown;
            // Invariant:
            // TheoryState::Sat => Theory_k is Sat for trail
            // TheoryState::Decision => the decision is acceptable with the current trail
            // Invariant:
            // Every theory is coherent up to last_index with the trail
            // Invariant: trail is sound & has type invariants
            loop {
                let trail_len = trail.len();
                let th_res = self.bool_th.extend(trail);
                if trail_len != trail.len() {
                    states = TheoryState::Unknown;
                };

                match th_res {
                    ExtendResult::Conflict(c) => {
                        if trail.level() == 0 {
                            return Answer::Unsat;
                        };
                        states = TheoryState::Unknown;
                        self.resolve_conflict(trail, c)
                    }
                    ExtendResult::Decision(t, v) => states = TheoryState::Decision(t, v),
                    ExtendResult::Satisfied => states = TheoryState::Sat,
                }

                if matches!(states, TheoryState::Decision(_, _) | TheoryState::Sat) {
                    break;
                }
            }

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

    // Requires `trail` and `conflict` to form a conflict state
    // Requires that `trail` level is > 0
    // Ensures that `trail` is non-conflicting
    pub fn resolve_conflict(&mut self, trail: &mut Trail, conflict: Vec<Assignment>) {
        // Can store index in trail in as part of the priority using lexicographic order
        let mut heap : PriorityQueue<Assignment, usize> = PriorityQueue::new();

        // calculate level of the conflict
        for a in conflict.into_iter() {
            let l = a.level();
            heap.push(a, l);
        }

        let level = *heap.peek().unwrap().1;

        // #[variant()]
        while let Some((a, l)) = heap.pop() {
            // back jump
            if a.is_bool() && l > *heap.peek().unwrap().1 {
                trail.restrict(*heap.peek().unwrap().1);
                trail.add_justified(heap.into_vec(), a.term(), a.value().negate());
                return;
            };

            if let Some(just) = trail.justification(a) {
                for j in just.iter() {
                    if j.level() == level && j.first_order() && j.decision() {
                        // undo decide
                        if *heap.peek().unwrap().1 == l {
                            trail.restrict(level - 1);
                            trail.add_decision(a.term(), a.value().negate());
                            return;
                        }
                        // undo clear
                        else {
                            trail.restrict(level-1);
                            return;
                        }
                    }
                }

                // resolve
                for a in j.into_iter() {
                    let l = a.level();
                    heap.push(a, l);
                }
            }
        }
    }
}

pub enum Answer {
    Sat,
    Unsat,
    Unknown,
}

enum ExtendResult {
    Conflict(Vec<Assignment>),
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
    fn extend(&mut self, tl: &mut Trail) -> ExtendResult {
        let i = 0;

        while i < tl.len() {
        	if tl[i].is_bool() {
                match self.eval(tl, &tl[i].term) {
                    Result::Err(mut fvs) => {
                        let decision = fvs.pop().unwrap();
                        return ExtendResult::Decision(decision, Value::Bool(true))
                    },
                    Result::Ok((mut subterms, res)) => {
                        if res != tl[i].val {
                            subterms.push(tl[i].clone());
                            return ExtendResult::Conflict(subterms)
                        }
                    }
                }
        	}
        }

        return ExtendResult::Satisfied
    }

    // Ensures:
    //  - Free Var list is non-empty, all not on trail
    //  - If ok: there is a justified entailment between the justification and tm <- value?
    #[ensures(forall<just : _, val: _> result == Ok((just, val)) ==> forall<m : _> m.satisfy_set(@just) ==> m.satisfies((@tm, @val)))]
    fn eval(&mut self, tl: &Trail, tm: &Term) -> Result<(Vec<Assignment>, Value), Vec<Term>> {
        match tm {
            Term::Conj(l, r) => {
                let l = self.eval(tl, l);
                let r = self.eval(tl, r);

                match (l, r) {
                    (Ok((mut j1, v1)), Ok((j2, v2))) => {
                        j1.extend(j2);
                        if v1.bool() && v2.bool() {
                            return Ok((j1, Value::Bool(true)))
                        } else {
                            return Ok((j1, Value::Bool(false)))
                        }
                    },
                    (Err(mut f1), Err(f2)) => { f1.extend(f2); return Err(f1)},
                    (_, Err(f)) | (Err(f), _) => return Err(f)
                }
            }
            a => match tl.get(a) {
                Some(asn) => Ok((vec![asn.clone()], asn.value().clone())),
                None => Err(vec![a.clone()]),
            }
        }
    }
}
