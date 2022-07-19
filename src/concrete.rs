// use ::std::collections::{BinaryHeap, HashSet};
// // use creusot_contracts::derive::{PartialEq};

// use creusot_contracts::*;
use priority_queue::PriorityQueue;
use crate::theory;
use crate::trail::*;
use creusot_contracts::*;

pub struct Solver {
    bool_th: BoolTheory,
}

enum TheoryState {
    Sat,
    Decision(Term, Value),
    Unknown,
}

impl Solver {
    //     pub fn new() -> Self {
    //         Solver {
    //             bool_th: BoolTheory,
    //         }
    //     }

    #[requires(trail.invariant())]
    #[ensures((^trail).invariant())]
    #[ensures(trail.ghost.impls(*(^trail).ghost))]
    #[ensures(match result {
        Answer::Unsat => trail.unsat(),
        Answer::Sat => true, // ignore completeness for now.
        Answer::Unknown => true,
    })]
    pub fn solver(&mut self, trail: &mut Trail) -> Answer {
        let old_trail = ghost! { trail };
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

                match th_res {
                    ExtendResult::Conflict(c) => {
                        if trail.max_level(&c) == 0 {
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

    // #[cfg(feature = "contracts")]
    // #[trusted]
    // #[maintains((mut trail).invariant())]
    // #[ensures(trail.ghost.impls(*(^trail).ghost))]
    // pub fn resolve_conflict(&mut self, trail: &mut Trail, conflict: Vec<usize>) {}

    // Requires `trail` and `conflict` to form a conflict state
    // Requires that `trail` level is > 0
    // Ensures that `trail` is non-conflicting
    // #[trusted`]
    // #[cfg(not(feature = "contracts"))]
    #[maintains((mut trail).invariant())]
    #[ensures(trail.ghost.impls(*(^trail).ghost))]
    #[requires(forall<i : _> 0 <= i && i < (@conflict).len() ==> @(@conflict)[i] < (@trail.assignments).len())]
    #[requires((@conflict).len() > 0)]
    pub fn resolve_conflict(&mut self, trail: &mut Trail, conflict: Vec<usize>) {
        // Can store index in trail in as part of the priority using lexicographic order
        let mut heap: ConflictHeap = ConflictHeap::new();
        use creusot_contracts::std::iter::IteratorSpec;

        // calculate level of the conflict
        #[invariant(xx, forall<i : _> 0 <= i && i < produced.len() ==> exists<l : _> (@heap).get(@produced[i]) == Some(l))]
        for a in conflict {
            let l = trail[a].level();
            heap.push(a, l);
        }

        let level = *heap.peek().unwrap().1;

        // #[variant()]
        while let Some((a, l)) = heap.pop() {
            let a = trail[a].clone();
            // back jump
            if a.is_bool() && l > *heap.peek().unwrap().1 {
                trail.restrict(*heap.peek().unwrap().1);
                trail.add_justified(heap.into_vec(), a.term().clone(), a.value().negate());
                return;
            };

            if let Some(just) = trail.justification(&a) {
                for j in just.iter() {
                    let j = &trail[*j];
                    if j.level() == level && j.first_order() && j.decision() {
                        // undo decide
                        if *heap.peek().unwrap().1 == l {
                            trail.restrict(level - 1);
                            trail.add_decision(a.term().clone(), a.value().negate());
                            return;
                        }
                        // undo clear
                        else {
                            trail.restrict(level - 1);
                            return;
                        }
                    }
                }

                // resolve
                for a in just.into_iter() {
                    let l = trail[a].level();
                    heap.push(a, l);
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

enum ExtendResult {
    Conflict(Vec<usize>),
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
            (forall<i : _> 0 <= i && i < (@c).len() ==> @(@c)[i] < (@(^tl).assignments).len()) &&
            (forall<m : theory::Model> m.satisfy_set(conflict) ==> false)
        }
    })]
    #[ensures(tl.ghost.impls(*(^tl).ghost))]
    fn extend(&mut self, tl: &mut Trail) -> ExtendResult {
        let mut i = 0;

        while i < tl.len() {
            if tl[i].is_bool() {
                match self.eval(tl, &tl[i].term) {
                    Result::Err(mut fvs) => {
                        let decision = fvs.pop().unwrap();
                        return ExtendResult::Decision(decision, Value::Bool(true));
                    }
                    Result::Ok((mut subterms, res)) => {
                        if res != tl[i].val {
                            subterms.push(i);
                            return ExtendResult::Conflict(subterms);
                        }
                    }
                }
            }
            i += 1;
        }

        return ExtendResult::Satisfied;
    }

    // Ensures:
    //  - Free Var list is non-empty, all not on trail
    //  - If ok: there is a justified entailment between the justification and tm <- value?
    // #[ensures(forall<just : _, val: _> result == Ok((just, val)) ==> forall<m : _> m.satisfy_set(@just) ==> m.satisfies((@tm, @val)))]
    #[trusted]
    fn eval(&mut self, tl: &Trail, tm: &Term) -> Result<(Vec<usize>, Value), Vec<Term>> {
        match tm {
            Term::Conj(l, r) => {
                let l = self.eval(tl, l);
                let r = self.eval(tl, r);

                match (l, r) {
                    (Ok((mut j1, v1)), Ok((j2, v2))) => {
                        j1.extend(j2);
                        if v1.bool() && v2.bool() {
                            return Ok((j1, Value::Bool(true)));
                        } else {
                            return Ok((j1, Value::Bool(false)));
                        }
                    }
                    (Err(mut f1), Err(f2)) => {
                        f1.extend(f2);
                        return Err(f1);
                    }
                    (_, Err(f)) | (Err(f), _) => return Err(f),
                }
            }
            a => match tl.index_of(a) {
                Some(i) => Ok((vec![i], tl[i].value().clone())),
                None => Err(vec![a.clone()]),
            },
        }
    }
}


#[trusted]
struct ConflictHeap(PriorityQueue<usize, usize>);

#[cfg(feature= "contracts")]
impl creusot_contracts::Model for ConflictHeap {
    type ModelTy = creusot_contracts::Mapping<Int, Option<Int>>;

    #[logic]
    #[trusted]
    #[ensures(@self == Mapping::cst(None))]
    fn model(self) -> Self::ModelTy {
        pearlite! { absurd }
    }
}

impl ConflictHeap {
    #[trusted]
    fn new() -> Self {
        ConflictHeap(PriorityQueue::new())
    }

    #[trusted]
    #[ensures((@^self) == (@self).set(@e, Some(@prio)))]
    fn push(&mut self, e : usize, prio: usize) -> Option<usize> {
        self.0.push(e, prio)
    }

    #[trusted]
    #[ensures(result == None ==> (@self) == Mapping::cst(None))]
    #[ensures(forall<e : _, l : _> result == Some((e, l)) ==> (@self).get(@e) == Some(@l))]
    fn peek(&self) -> Option<(&usize, &usize)> {
        self.0.peek()
    }

    #[trusted]
    fn pop(&mut self) -> Option<(usize, usize)> {
        self.0.pop()
    }

    #[trusted]
    fn into_vec(self) -> Vec<usize> {
        self.0.into_vec()
    }
}