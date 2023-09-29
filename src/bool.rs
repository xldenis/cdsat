use creusot_contracts::{vec, *};
use log::info;

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
    // #[trusted]
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
        let mut iter = tl.indices();
        // info!("Bool is performing deductions");
        while let Some(ix) = iter.next() {
            let tl = iter.trail();

            if self.is_relevant(&tl[ix]) {
                // info!("Bool is evaluating {}", &tl[ix]);
                match self.eval(tl, &tl[ix].term) {
                    Result::Err(dec) => {
                        if dec.sort() == Sort::Boolean {
                            if dec == Term::Value(Value::Bool(false)) {
                                panic!()
                            };
                            // info!("Bool proposes {dec}");
                            return ExtendResult::Decision(dec, Value::Bool(true));
                        }
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
        // info!("Bool is satisfied");
        return ExtendResult::Satisfied;
    }

    // #[trusted]
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

    // Ensures:
    //  - Free Var list is non-empty, all not on trail
    //  - If ok: there is a justified entailment between the justification and tm <- value?
    // #[ensures(forall<just : _, val: _> result == Ok((just, val)) ==> forall<m : _> m.satisfy_set(just@) ==> m.satisfies((tm@, val@)))]
    // #[trusted]
    fn eval(&mut self, tl: &Trail, tm: &Term) -> Result<(Vec<TrailIndex>, Value), Term> {
        if let Some(x) = tl.index_of(tm) {
            return Ok((vec![x], tl[x].val.clone()));
        };
        match tm {
            Term::Eq(l, r) if r.sort() == Sort::Boolean => {
                let (mut j1, v1) = match self.eval(tl, l) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                let (j2, v2) = match self.eval(tl, r) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                j1.extend(j2);
                return Ok((j1, Value::Bool(v1 == v2)));
            }
            Term::Conj(l, r) => {
                let (mut j1, v1) = match self.eval(tl, l) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                let (j2, v2) = match self.eval(tl, r) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                j1.extend(j2);
                return Ok((j1, Value::Bool(v1.bool() && v2.bool())));
            }
            Term::Disj(l, r) => {
                let (mut j1, v1) = match self.eval(tl, l) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                let (j2, v2) = match self.eval(tl, r) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                j1.extend(j2);
                return Ok((j1, Value::Bool(v1.bool() || v2.bool())));
            }
            Term::Neg(t) => {
                let (j, v) = match self.eval(tl, t) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                Ok((j, v.negate()))
            }
            Term::Value(v @ Value::Bool(_)) => return Ok((Vec::new(), v.clone())),
            a => match tl.index_of(a) {
                Some(i) => Ok((vec![i], tl[i].value().clone())),
                None => Err(a.clone()),
            },
        }
    }
}
