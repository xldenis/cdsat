use crate::ghost::Ghost;
use creusot_contracts::{vec, *};
use log::{info, trace};

#[cfg(creusot)]
use crate::theory;
use crate::{
    concrete::ExtendResult,
    term::{Sort, Term, Value},
    trail::{Assignment, Trail, TrailIndex},
};

pub struct BoolTheory;

impl BoolTheory {
    // Extend the trail with 1 or more deductions, or backtrack to a non-conflicting state
    // Returns `Fail` if we encounter a conflict at level 0
    // Return Satisfied if the trail is satisfactory to us
    #[maintains((mut tl).invariant())]
    #[ensures(match result {
        ExtendResult::Satisfied => true,
        ExtendResult::Decision(t, v) => (^tl).ghost.acceptable(t@, v@),
        ExtendResult::Conflict(c) => {
            let conflict = (^tl).abstract_justification(c@);
            c@.len() > 0 &&
            // members of conflict area within the trail
            (forall<t : _> (c@).contains(t) ==> (^tl).contains(t)) &&
            // (forall<i : _> 0 <= i && i < (c@).len() ==> @(c@)[i] < (@(^tl).assignments).len()) &&
            (forall<m : theory::Model> m.satisfy_set(conflict) ==> false)
        }
    })]
    #[ensures(tl.ghost.impls(*(^tl).ghost))]
    pub fn extend(&mut self, tl: &mut Trail) -> ExtendResult {
        let old_tl: Ghost![_] = gh! { tl };
        let mut iter = tl.indices();
        let old_iter: Ghost![_] = gh! { iter };
        // info!("Bool is performing deductions");
        #[invariant(forall<i : _> old_tl.contains(i) ==> iter.trail.contains(i))]
        #[invariant(old_tl.ghost.impls(*iter.trail.ghost))]
        #[invariant(iter.trail.invariant())]
        #[invariant(^iter.trail == ^old_iter.trail)]
        while let Some(ix) = iter.next() {
            let tl = iter.trail();

            let assign = &tl[ix];
            if !self.is_relevant(assign) {
                continue;
            }
            trace!("Bool is considering {}", &tl[ix]);

            proof_assert!(assign.term@.well_sorted());
            // info!("Bool is evaluating {}", &tl[ix]);
            let (mut just, res) = self.eval(tl, &assign.term);

            trace!("Bool eval of {} resulted in {:?}", assign, res);
            match res {
                Result::Err(dec) => {
                    proof_assert!(tl.ghost.acceptable(dec@, Value::Bool(true)@));
                    if dec.sort() == Sort::Boolean {
                        // info!("Bool proposes {dec}");
                        return ExtendResult::Decision(dec, Value::Bool(true));
                    }
                }
                Result::Ok(res) => {
                    if res != assign.val {
                        just.push(ix);
                        proof_assert!(res@ != assign.val@);
                        let _: Ghost![_] = gh! {crate::trail::abstract_justification_insert};
                        let _: Ghost![_] = gh! { theory::Model::consistent };

                        proof_assert!(^iter.trail == ^*old_tl);

                        proof_assert!(
                            forall<m : theory::Model> m.satisfy_set(tl.abstract_justification(just@)) ==> false
                        );
                        return ExtendResult::Conflict(just);
                    }
                }
            }
        }

        proof_assert!(^iter.trail == ^*old_tl);

        info!("Bool is satisfied");
        return ExtendResult::Satisfied;
    }

    #[ensures(result ==> a.term@.is_bool())]
    fn is_relevant(&self, a: &Assignment) -> bool {
        match &a.term {
            Term::Variable(_, Sort::Boolean) => true,
            Term::Value(Value::Bool(_)) => true,
            Term::Plus(_, _) => false,
            Term::Times(_, _) => false,
            Term::Eq(_, r) => r.sort() == Sort::Boolean,
            Term::Lt(_, _) => false,
            Term::Conj(_, _) => true,
            Term::Neg(_) => true,
            Term::Disj(_, _) => true,
            Term::Impl(_, _) => true,
            _ => false,
        }
    }

    #[requires(tl.invariant())]
    #[requires(tm@.well_sorted())]
    #[requires(tm@.is_bool())]
    #[ensures(forall<ix : _> result.0@.contains(ix) ==> tl.contains(ix))]
    #[ensures(match result.1 {
        Ok(v) => { v@.is_bool()  &&
            (forall<m : theory::Model>
                m.satisfy_set(tl.abstract_justification(result.0@)) ==> m.satisfies((tm@, v@)))

        }
        Err(t) => { tl.ghost.acceptable(t@, Value::Bool(true)@) }
    })]
    fn eval(&mut self, tl: &Trail, tm: &Term) -> (Vec<TrailIndex>, Result<Value, Term>) {
        let mut v = Vec::new();

        let res = self.eval_inner(tl, tm, &mut v);
        (v, res)
    }

    // Ensures:
    //  - Free Var list is non-empty, all not on trail
    //  - If ok: there is a justified entailment between the justification and tm <- value?
    // #[ensures(forall<just : _, val: _> result == Ok((just, val)) ==> forall<m : _> m.satisfy_set(just@) ==> m.satisfies((tm@, val@)))]
    #[requires(tl.invariant())]
    #[requires(tm@.well_sorted())]
    #[requires(tm@.is_bool())]
    #[requires(forall<ix : _> used@.contains(ix) ==> tl.contains(ix))]
    #[ensures(match result {
        Ok(v) => { v@.is_bool()  &&
            (forall<m : theory::Model>
                m.satisfy_set(tl.abstract_justification((^used)@)) ==> m.satisfies((tm@, v@)))

        }
        Err(t) => {  tl.ghost.acceptable(t@, Value::Bool(true)@) }
    })]
    #[ensures(forall<ix : _> used@.contains(ix) ==> (^used)@.contains(ix))]
    #[ensures(forall<ix : _> (^used)@.contains(ix) ==> tl.contains(ix))]
    fn eval_inner(
        &mut self,
        tl: &Trail,
        tm: &Term,
        used: &mut Vec<TrailIndex>,
    ) -> Result<Value, Term> {
        // if let Some(x) = tl.index_of(tm) {
        //     used.push(x);
        //     proof_assert!(tl.index_logic(x).0 == tm@);
        //     proof_assert!(tl.index_logic(x).1.is_bool());
        //     return Ok(tl[x].val.clone());
        // }

        let _: Ghost![_] = gh! {Trail::abs_just_extend};
        let _: Ghost![_] = gh! { theory::Model::subset};

        match tm {
            Term::Value(v @ Value::Bool(_)) => return Ok(v.clone()),
            Term::Eq(l, r) if r.sort() == Sort::Boolean => {
                let v1 = match self.eval_inner(tl, l, used) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                let v2 = match self.eval_inner(tl, r, used) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                proof_assert!(forall<m : theory::Model> m.satisfy_set(tl.abstract_justification((^used)@))
                    ==> m.satisfies((l@, v1@)) && m.satisfies((r@, v2@)));
                return Ok(Value::Bool(v1 == v2));
            }
            // Term::Eq(_, _) => todo!(),
            Term::Conj(l, r) => {
                let v1 = match self.eval_inner(tl, l, used) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                let v2 = match self.eval_inner(tl, r, used) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                proof_assert!(forall<m : theory::Model> m.satisfy_set(tl.abstract_justification((^used)@))
                    ==> m.satisfies((l@, v1@)) && m.satisfies((r@, v2@)));
                return Ok(Value::Bool(v1.bool() && v2.bool()));
            }
            Term::Neg(t) => match self.eval_inner(tl, t, used) {
                Ok(v) => Ok(v.negate()),
                Err(t) => Err(t),
            },
            Term::Disj(l, r) => {
                let v1 = match self.eval_inner(tl, l, used) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                let v2 = match self.eval_inner(tl, r, used) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                proof_assert!(forall<m : theory::Model> m.satisfy_set(tl.abstract_justification((^used)@))
                    ==> m.satisfies((l@, v1@)) && m.satisfies((r@, v2@)));
                return Ok(Value::Bool(v1.bool() || v2.bool()));
            }
            Term::Impl(l, r) => {
                let v1 = match self.eval_inner(tl, l, used) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                let v2 = match self.eval_inner(tl, r, used) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                proof_assert!(forall<m : theory::Model> m.satisfy_set(tl.abstract_justification((^used)@))
                    ==> m.satisfies((l@, v1@)) && m.satisfies((r@, v2@)));
                return Ok(Value::Bool(!v1.bool() || v2.bool()));
            }
            _ => {
                if let Some(x) = tl.index_of(tm) {
                    used.push(x);
                    proof_assert!(tl.index_logic(x).0 == tm@);
                    proof_assert!(tl.index_logic(x).1.is_bool());
                    return Ok(tl[x].val.clone());
                } else {
                    Err(tm.clone())
                }
            }
        }
    }
}
