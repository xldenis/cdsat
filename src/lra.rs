use std::{collections::HashMap, fmt::Display, ops::Neg, unimplemented, unreachable};

use log::info;
use num::{BigInt, Signed};
use num_rational::BigRational;

use crate::{
    concrete::ExtendResult,
    term::{Sort, Term, Value},
    trail::{Trail, TrailIndex},
};
pub struct LRATheory;

use creusot_contracts::{trusted, DeepModel, ghost, open, ensures, maintains};

#[derive(Debug, Ord, Eq, Clone, PartialEq, PartialOrd, DeepModel)]
enum Bound {
    Exclusive { value: BigRational, just: TrailIndex },
    Inclusive { value: BigRational, just: TrailIndex },
    Missing,
}

impl Bound {
    #[trusted]
    fn get_inner(&self) -> Option<&BigRational> {
        match self {
            Bound::Exclusive { value, .. } => Some(&value),
            Bound::Inclusive { value, .. } => Some(&value),
            Bound::Missing => None,
        }
    }
}

impl Display for Bound {
    #[trusted]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bound::Exclusive { value, .. } => write!(f, "[{}", value),
            Bound::Inclusive { value, .. } => write!(f, "({}", value),
            Bound::Missing => write!(f, "--",),
        }
    }
}

#[derive(Debug, Clone)]
struct Bounds {
    lower: Bound,
    upper: Bound,
}

enum Pick {
    Choice(BigRational),
    Fixed(BigRational),
    Fm(TrailIndex, TrailIndex),
}

impl Bounds {
    #[trusted]
    fn valid(&self) -> bool {
        match (&self.lower, &self.upper) {
            (Bound::Exclusive { value: a, .. }, Bound::Exclusive { value: b, .. }) => a < b,
            (Bound::Exclusive { value: a, .. }, Bound::Inclusive { value: b, .. }) => a < b,
            (Bound::Inclusive { value: a, .. }, Bound::Exclusive { value: b, .. }) => a < b,
            (Bound::Inclusive { value: a, .. }, Bound::Inclusive { value: b, .. }) => a <= b,
            (Bound::Exclusive { value: a, .. }, Bound::Missing) => true,
            (Bound::Inclusive { value, .. }, Bound::Missing) => true,
            (Bound::Missing, Bound::Exclusive { value, .. }) => true,
            (Bound::Missing, Bound::Inclusive { value, .. }) => true,
            (Bound::Missing, Bound::Missing) => true,
        }
    }

    #[trusted]
    fn update_upper(&mut self, just: TrailIndex, nature: Nature, value: BigRational) {
        let new_bnd = match nature {
            Nature::Eq => Bound::Inclusive { value, just },
            Nature::Lt => Bound::Exclusive { value, just },
            _ => unreachable!(),
        };
        if self.upper > new_bnd {
            self.upper = new_bnd;
        }
    }

    #[trusted]
    fn update_lower(&mut self, just: TrailIndex, nature: Nature, value: BigRational) {
        let new_bnd = match nature {
            Nature::Eq => Bound::Inclusive { value, just },
            Nature::Lt => Bound::Exclusive { value, just },
            _ => unreachable!(),
        };
        if self.lower > new_bnd {
            self.lower = new_bnd;
        }
    }

    #[trusted]
    fn pick(self) -> Pick {
        if self.lower == self.upper && self.lower != Bound::Missing {
            Pick::Fixed(self.lower.get_inner().unwrap().clone())
        } else {
            use Bound::*;
            match (self.lower, self.upper) {
                (Exclusive { value, just }, Exclusive { value: v2, just: j2 }) => {
                    if value > v2 {
                        Pick::Fm(just, j2)
                    } else {
                        Pick::Choice((value + v2) / BigInt::from(2))
                    }
                }
                (Exclusive { value, just }, Inclusive { value: v2, just: j2 }) => {
                    if value > v2 {
                        Pick::Fm(just, j2)
                    } else {
                        Pick::Choice((value + v2) / BigInt::from(2))
                    }
                }
                (Inclusive { value, just }, Exclusive { value: v2, just: j2 }) => {
                    if value > v2 {
                        Pick::Fm(just, j2)
                    } else {
                        Pick::Choice((value + v2) / BigInt::from(2))
                    }
                }
                (Inclusive { value, just }, Inclusive { value: v2, just: j2 }) => {
                    if value > v2 {
                        Pick::Fm(just, j2)
                    } else {
                        Pick::Choice((value + v2) / BigInt::from(2))
                    }
                }
                (Exclusive { value, .. }, Missing) => Pick::Choice(value + BigInt::from(1)),
                (Inclusive { value, .. }, Missing) => Pick::Choice(value + BigInt::from(1)),
                (Missing, Exclusive { value, .. }) => Pick::Choice(value - BigInt::from(1)),
                (Missing, Inclusive { value, .. }) => Pick::Choice(value - BigInt::from(1)),
                (Missing, Missing) => Pick::Choice(BigRational::new(0.into(), BigInt::from(1))),
            }
        }
    }
}

struct Domain(HashMap<Term, Bounds>);

impl Domain {
    #[cfg(creusot)]
    fn insert(&mut self, term: Term) {}
    #[cfg(not(creusot))]
    #[trusted]
    fn insert(&mut self, term: Term) {
        self.0.entry(term).or_insert(Bounds { lower: Bound::Missing, upper: Bound::Missing });
    }

    #[cfg(creusot)]
    #[trusted]
    fn update(&mut self, just: TrailIndex, term: Term, nature: Nature, value: BigRational) -> bool { true }

    #[cfg(not(creusot))]
    #[trusted]
    fn update(&mut self, just: TrailIndex, term: Term, nature: Nature, value: BigRational) -> bool {
        let entry =
            self.0.entry(term).or_insert(Bounds { lower: Bound::Missing, upper: Bound::Missing });

        if nature == Nature::Eq {
            entry.update_upper(just, nature, value.clone());
            entry.update_lower(just, nature, value);
        } else {
            if value.is_positive() {
                entry.update_upper(just, nature, value)
            } else {
                entry.update_lower(just, nature, value.neg())
            }
        }

        // Whether this bound is still valid
        entry.valid()
    }

    #[cfg(creusot)]
    #[trusted]
    fn get(&self, t: &Term) -> &Bounds {
        todo!()
    }

    #[cfg(not(creusot))]
    #[trusted]
    fn get(&self, t: &Term) -> &Bounds {
        &self.0[t]
    }
}

impl LRATheory {
    #[trusted]
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

        let mut domains: Domain = Domain(HashMap::new());
        info!("LRA is performing inferences");
        while let Some(ix) = iter.next() {
            let tl = iter.trail();

            if !is_relevant(&tl[ix].term) {
                continue;
            }

            info!("LRA is considering {}", &tl[ix]);
            let mut t = Summary::summarize(&tl[ix].term.clone());

            let mut used = t.eval(iter.trail());
            used.push(ix);

            match t.term() {
                Answer::Unit(t, n, v) => {
                    let j = match n {
                        Nature::Lt => Term::lt(t.clone(), Term::val(Value::Rat(v.clone()))),
                        Nature::Eq => Term::eq_(t.clone(), Term::val(Value::Rat(v.clone()))),
                        Nature::Term => t.clone(),
                    };
                    if &t != &tl[ix].term {
                        let val = tl[ix].val.clone();
                        iter.add_justified(used, j.clone(), val);
                        let valid =
                            domains.update(iter.trail().index_of(&j).unwrap(), t.clone(), n, v);

                        if !valid {
                            let Pick::Fm(tj, tk) = domains.get(&t).clone().pick() else { panic!("should have conflict") };
                            return ExtendResult::Conflict(vec![tj, tk]);
                        }
                    }
                }
                Answer::Val(v) => {
                    if &v != &tl[ix].val {
                        return ExtendResult::Conflict(used);
                    }
                }
                Answer::Other(t, watches) => {
                    if &t != &tl[ix].term {
                        let v = tl[ix].val.clone();
                        iter.add_justified(used, t, v);
                    }

                    watches.into_iter().for_each(|w| {
                        domains.insert(w);
                    });
                }
            };
        }

        if domains.0.len() > 0 {
            for (t, bnds) in domains.0 {
                match bnds.pick() {
                    Pick::Choice(v) => {
                        info!("LRA is proposing a choice {t} <- {v}");
                        return ExtendResult::Decision(t, Value::Rat(v));
                    }
                    Pick::Fixed(_) => continue,
                    Pick::Fm(tj, tk) => todo!(),
                }
            }
        }

        return ExtendResult::Satisfied;
    }
}

#[trusted]
fn is_relevant(t: &Term) -> bool {
    match t {
        Term::Eq(l, r) => l.sort() == Sort::Rational,
        Term::Lt(_, _) => true,
        Term::Plus(_, _) => true,
        Term::Times(_, _) => true,
        Term::Value(v) => v.sort() == Sort::Rational,
        Term::Variable(_, s) => *s == Sort::Rational,
        _ => false,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Nature {
    Eq,
    Lt,
    Term,
}

struct Summary {
    // Pairs of variables and coefficients
    vars: HashMap<Term, isize>,
    cst: BigRational,
    nature: Nature,
}

enum Answer {
    Unit(Term, Nature, BigRational),
    Other(Term, Vec<Term>),
    Val(Value),
}

impl Summary {
    #[trusted]
    fn sub(&mut self, o: Self) {
        for (k, v) in o.vars {
            *self.vars.entry(k).or_insert(0) -= v;
        }
        self.cst -= o.cst;
    }

    #[trusted]
    fn summarize(tm: &Term) -> Summary {
        let nature = match tm {
            Term::Eq(_, _) => Nature::Eq,
            Term::Lt(_, _) => Nature::Lt,
            Term::Variable(_, _) | Term::Plus(_, _) | Term::Times(_, _) | Term::Value(_) => {
                Nature::Term
            }
            _ => unimplemented!(),
        };
        let mut s =
            Summary { vars: Default::default(), cst: BigRational::new(0.into(), 1.into()), nature };
        match tm {
            Term::Eq(l, r) => {
                s.summarize_inner(l);
                let mut rs = Summary {
                    vars: Default::default(),
                    cst: BigRational::new(0.into(), 1.into()),
                    nature,
                };
                rs.summarize_inner(r);
                s.sub(rs);
            }
            Term::Lt(l, r) => {
                s.summarize_inner(l);
                let mut rs = Summary {
                    vars: Default::default(),
                    cst: BigRational::new(0.into(), 1.into()),
                    nature,
                };
                rs.summarize_inner(r);
                s.sub(rs);
            }
            t => s.summarize_inner(t),
        }
        s
    }

    #[trusted]
    fn eval(&mut self, tl: &Trail) -> Vec<TrailIndex> {
        let mut ixs = Vec::new();
        for (k, v) in self.vars.iter_mut() {
            if let Some(ix) = tl.index_of(k) {
                ixs.push(ix);
                let Value::Rat(r) = &tl[ix].val else { panic!() };
                self.cst += r * BigInt::from(*v);
                *v = 0;
            }
        }
        ixs
    }

    #[trusted]
    fn term(self) -> Answer {
        let mut present_vars: Vec<_> = self.vars.into_iter().filter(|(_, v)| *v != 0).collect();
        let num_vars = present_vars.len();
        if num_vars == 1 {
            let (unit_var, cnt) = present_vars.remove(0);

            return Answer::Unit(unit_var, self.nature, -self.cst / BigInt::from(cnt));
        }

        let watches = present_vars.iter().take(2).map(|(t, _)| t.clone()).collect();
        let lhs = present_vars
            .into_iter()
            .filter_map(|(v, k)| if k == 0 { None } else { Some(Term::times(k, v)) })
            .reduce(Term::plus)
            .unwrap_or(Term::Value(Value::rat(0, 1)));

        let rhs = Term::val(Value::Rat(self.cst * BigInt::from(-1)));

        let t = if num_vars == 0 {
            let v = match self.nature {
                Nature::Eq => {
                    if lhs == rhs {
                        Term::true_()
                    } else {
                        Term::false_()
                    }
                }
                Nature::Lt => {
                    if lhs.as_val() < rhs.as_val() {
                        Term::true_()
                    } else {
                        Term::false_()
                    }
                }
                Nature::Term => rhs,
            };
            return Answer::Val(v.as_val());
        } else {
            match self.nature {
                Nature::Eq => Term::eq_(lhs, rhs),
                Nature::Lt => Term::lt(lhs, rhs),
                Nature::Term => lhs,
            }
        };

        Answer::Other(t, watches)
    }

    #[trusted]
    fn summarize_inner(&mut self, tm: &Term) {
        match tm {
            Term::Eq(l, r) => {
                unreachable!();
            }
            Term::Plus(l, r) => {
                self.summarize_inner(l);
                self.summarize_inner(r);
            }
            Term::Times(k, r) => {
                *self.vars.entry((&**r).clone()).or_insert(0) += k;
            }
            Term::Lt(l, r) => {
                unreachable!()
            }
            Term::Value(Value::Rat(r)) => {
                self.cst += r;
            }
            a => {
                *self.vars.entry(tm.clone()).or_insert(0) += 1;
            }
        };
    }
}
