use std::{
    assert_ne, collections::BTreeMap, eprintln, fmt::Display, ops::Neg, unimplemented, unreachable,
};

use indexmap::IndexMap;

use log::{info, trace};
use num::{BigInt, One, Signed, Zero};
use num::rational::BigRational;

use crate::{
    concrete::ExtendResult,
    term::{Sort, Term, Value},
    trail::{Trail, TrailIndex},
};
pub struct LRATheory;

use creusot_std::prelude::{ensures, ghost, maintains, trusted, DeepModel};

#[derive(Debug, Default, Ord, Eq, Clone, PartialEq, PartialOrd, DeepModel)]
enum Bound {
    Exclusive {
        value: BigRational,
        just: TrailIndex,
    },
    Inclusive {
        value: BigRational,
        just: TrailIndex,
    },
    #[default]
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
            Bound::Exclusive { value, .. } => write!(f, "({}", value),
            Bound::Inclusive { value, .. } => write!(f, "[{}", value),
            Bound::Missing => write!(f, "--",),
        }
    }
}

#[derive(Debug, Clone, Default)]
struct Bounds {
    lower: Bound,
    upper: Bound,
    excluded: BTreeMap<BigRational, TrailIndex>,
}

impl Display for Bounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.lower {
            Bound::Exclusive { value, .. } => write!(f, "({}", value)?,
            Bound::Inclusive { value, .. } => write!(f, "[{}", value)?,
            Bound::Missing => write!(f, "--",)?,
        };
        write!(f, " , ")?;
        match &self.upper {
            Bound::Exclusive { value, .. } => write!(f, "{})", value)?,
            Bound::Inclusive { value, .. } => write!(f, "{}]", value)?,
            Bound::Missing => write!(f, "--",)?,
        };
        Ok(())
    }
}

enum Pick {
    Choice(BigRational),
    Fixed(BigRational),
    Fm(TrailIndex, TrailIndex),
    DisEq(TrailIndex, TrailIndex, TrailIndex),
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
            Nature::Le => Bound::Inclusive { value, just },
            Nature::Ge => Bound::Inclusive { value, just },
            Nature::Gt => Bound::Exclusive { value, just },
            _ => unreachable!(),
        };
        use Bound::*;
        match (&self.upper, &new_bnd) {
            (Bound::Missing, _) => self.upper = new_bnd,
            (
                Exclusive { value, .. },
                Exclusive { value: value2, .. } | Inclusive { value: value2, .. },
            ) => {
                if value2 < value {
                    self.upper = new_bnd
                };
            }
            (Inclusive { value, .. }, Inclusive { value: value2, .. }) => {
                if value2 < value {
                    self.upper = new_bnd
                };
            }
            (Inclusive { value, .. }, Exclusive { value: value2, .. }) => {
                if value2 <= value {
                    self.upper = new_bnd
                };
            }
            (_, Missing) => {}
        }
    }

    #[trusted]
    fn update_lower(&mut self, just: TrailIndex, nature: Nature, value: BigRational) {
        let new_bnd = match nature {
            Nature::Eq => Bound::Inclusive { value, just },
            Nature::Lt => Bound::Exclusive { value, just },
            Nature::Le => Bound::Inclusive { value, just },
            Nature::Ge => Bound::Inclusive { value, just },
            Nature::Gt => Bound::Exclusive { value, just },
            _ => unreachable!(),
        };
        use Bound::*;
        match (&self.lower, &new_bnd) {
            (Bound::Missing, _) => self.lower = new_bnd,
            (
                Exclusive { value, .. },
                Exclusive { value: value2, .. } | Inclusive { value: value2, .. },
            ) => {
                if value < value2 {
                    self.lower = new_bnd
                };
            }
            (Inclusive { value, .. }, Inclusive { value: value2, .. }) => {
                if value < value2 {
                    self.lower = new_bnd
                };
            }
            (Inclusive { value, .. }, Exclusive { value: value2, .. }) => {
                if value <= value2 {
                    self.lower = new_bnd
                };
            }
            (_, Missing) => {}
        }
    }

    fn exclude(&mut self, just: TrailIndex, value: BigRational) {
        self.excluded.entry(value).or_insert(just);
    }

    // Provides an in bounds value if the interval is non-empty.
    // Does not check anything with respect to excluded values.
    // Integrate dis-disequality elimination
    #[trusted]
    fn value(lower: &Bound, upper: &Bound) -> Pick {
        if lower == upper && lower != &Bound::Missing {
            Pick::Fixed(lower.get_inner().unwrap().clone())
        } else {
            use Bound::*;
            match (lower, upper) {
                (Exclusive { value, just }, Exclusive { value: v2, just: j2 }) => {
                    if value > v2 {
                        Pick::Fm(*just, *j2)
                    } else {
                        Pick::Choice((value + v2) / BigInt::from(2))
                    }
                }
                (Exclusive { value, just }, Inclusive { value: v2, just: j2 }) => {
                    if value >= v2 {
                        Pick::Fm(*just, *j2)
                    } else {
                        Pick::Choice((value + v2) / BigInt::from(2))
                    }
                }
                (Inclusive { value, just }, Exclusive { value: v2, just: j2 }) => {
                    if value >= v2 {
                        Pick::Fm(*just, *j2)
                    } else {
                        Pick::Choice((value + v2) / BigInt::from(2))
                    }
                }
                (Inclusive { value, just }, Inclusive { value: v2, just: j2 }) => {
                    if value > v2 {
                        Pick::Fm(*just, *j2)
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

    // Integrate dis-disequality elimination
    #[trusted]
    fn pick(&self) -> Pick {
        let p = Self::value(&self.lower, &self.upper);
        let Pick::Choice(v) = p else {return p };

        if !self.excluded.contains_key(&v) {
            return Pick::Choice(v);
        }

        let middle = Bound::Exclusive { just: self.excluded[&v], value: v.clone() };
        // Attempt to see if there is any other value we could choose:

        let right_ub = if let Some((k, v)) =
            self.excluded.lower_bound(std::ops::Bound::Excluded(&v)).next()
        {
            Bound::Exclusive { value: k.clone(), just: *v }
        } else {
            self.upper.clone()
        };

        let right = Self::value(&middle, &right_ub);
        if let Pick::Choice(v) = right {
            return Pick::Choice(v);
        }

        let left_lb = if let Some((k, v)) =
            self.excluded.upper_bound(std::ops::Bound::Excluded(&v)).next()
        {
            Bound::Exclusive { value: k.clone(), just: *v }
        } else {
            self.lower.clone()
        };
        let left = Self::value(&left_lb, &middle);
        if let Pick::Choice(v) = left {
            return Pick::Choice(v);
        }

        todo!()
        // return Pick::DisEq(_, _, _);
    }
}

struct Domain(IndexMap<Term, Bounds>);

impl Domain {
    #[cfg(creusot)]
    fn insert(&mut self, term: Term) {}
    #[cfg(not(creusot))]
    #[trusted]
    fn insert(&mut self, term: Term) {
        self.0.entry(term).or_default();
    }

    #[cfg(creusot)]
    #[trusted]
    fn update(&mut self, just: TrailIndex, term: Term, nature: Nature, value: BigRational) -> Pick {
        todo!()
    }

    #[cfg(not(creusot))]
    #[trusted]
    fn update(&mut self, just: TrailIndex, term: Term, nature: Nature, value: BigRational) -> Pick {
        let entry = self.0.entry(term).or_default();

        trace!("bounds were {}", entry);
        match nature {
            Nature::Neq => {
                entry.exclude(just, value);
            }
            Nature::Eq => {
                entry.update_upper(just, nature, value.clone());
                entry.update_lower(just, nature, value);
            }
            Nature::Lt | Nature::Le => {
                // if value.is_negative() {
                entry.update_upper(just, nature, value)
                // } else {
                // entry.update_lower(just, nature, value.neg())
                // }
            }
            Nature::Gt | Nature::Ge => {
                // eprintln!("updating {entry} {nature:?} {value}");
                // if !value.is_negative() {
                entry.update_lower(just, nature, value)
                // } else {
                // entry.update_upper(just, nature, value.neg())
                // }
            }
            Nature::Term => todo!(),
        };

        trace!("bounds are now {}", entry);
        // Whether this bound is still valid
        entry.pick()
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
        ExtendResult::Decision(t, v) => (^tl).ghost.acceptable(t@, v@) && t@.well_sorted(),
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

        let mut domains: Domain = Domain(IndexMap::new());
        trace!("LRA is performing inferences");
        while let Some(ix) = iter.next() {
            let tl = iter.trail();

            if !is_relevant(&tl[ix].term) {
                continue;
            }

            trace!("LRA is considering {ix:?}, {}", &tl[ix]);
            let mut t = Eval::normalize(&tl[ix].term.clone());

            let mut used = t.eval(iter.trail());
            used.push(ix);

            let ans = t.term();
            // info!("Eval said {:?}", ans);

            match ans {
                Answer::Unit(t, mut n, v) => {
                    if tl[ix].val != Value::true_() {
                        n = n.negate();
                    };

                    trace!("updating bounds of {t} {n:?} {v}");
                    // make it return the conflcit instead of a bool
                    let pick = domains.update(ix, t.clone(), n, v.clone());
                    match pick {
                        Pick::Fm(tj, tk) => {
                            info!(
                                "Found FM conflict in {} explained by {} and {}",
                                tl[ix], tl[tj], tl[tk]
                            );
                            let resolv = fourier_motzkin_resolvent(&tl[tj].term, &tl[tk].term, &t);

                            let mut fm_sum = Eval::normalize(&resolv);
                            let mut fm_eval = fm_sum.eval(&iter.trail());

                            // Uh-oh we already have a value for this FM resolution
                            if let Some(fm_ix) = iter.trail().index_of(&resolv) {
                                assert!(iter.trail()[fm_ix].val != Value::true_());

                                return ExtendResult::Conflict(vec![fm_ix, tj, tk]);
                            }

                            iter.add_justified(vec![tj, tk], resolv.clone(), Value::true_());

                            let tj = iter.trail().index_of(&resolv).unwrap();
                            fm_eval.push(tj);

                            return ExtendResult::Conflict(fm_eval);
                        }
                        Pick::DisEq(ta, tb, tc) => {
                            panic!("Disequality")
                        }
                        _ => {},
                    }
                }
                Answer::Val(v) => {
                    if &v != &tl[ix].val {
                        trace!(
                            "failed normalization of {} expected {} got {}",
                            tl[ix].term,
                            tl[ix].val,
                            v
                        );
                        return ExtendResult::Conflict(used);
                    }
                }
                Answer::Other(t, watches) => {
                    // if &t != &tl[ix].term {
                    //     let v = tl[ix].val.clone();
                    //     iter.add_justified(used, t, v);
                    // }

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
                    Pick::DisEq(_, _, _) => todo!(),
                }
            }
        }

        info!("LRA is satisifed");

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
    Neq,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Term,
}

impl Nature {
    // "Negate" the head of this clause ie < -> >=, but do nothing for Term
    fn negate(self) -> Self {
        match self {
            Nature::Neq => Nature::Eq,
            Nature::Eq => Nature::Neq,
            Nature::Lt => Nature::Ge,
            Nature::Le => Nature::Gt,
            Nature::Gt => Nature::Le,
            Nature::Ge => Nature::Lt,
            Nature::Term => Nature::Term,
        }
    }
}

#[derive(Debug)]
struct Eval {
    // Pairs of variables and coefficients
    vars: IndexMap<Term, BigRational>,
    cst: BigRational,
    nature: Nature,
}

#[derive(Debug)]
enum Answer {
    Unit(Term, Nature, BigRational),
    Other(Term, Vec<Term>),
    Val(Value),
}

impl Eval {
    #[trusted]
    fn sub(&mut self, o: Self) {
        for (k, v) in o.vars {
            *self.vars.entry(k).or_insert_with(|| BigRational::zero()) -= v;
        }
        self.cst -= o.cst;
    }

    #[trusted]
    fn normalize(tm: &Term) -> Eval {
        let nature = match tm {
            Term::Eq(_, _) => Nature::Eq,
            Term::Lt(_, _) => Nature::Lt,
            Term::Variable(_, _) | Term::Plus(_, _) | Term::Times(_, _) | Term::Value(_) => {
                Nature::Term
            }
            _ => unimplemented!(),
        };
        let mut s = Eval { vars: Default::default(), cst: BigRational::zero(), nature };
        match tm {
            Term::Eq(l, r) => {
                s.normalize_inner(BigRational::one(), l);
                let mut rs = Eval { vars: Default::default(), cst: BigRational::zero(), nature };
                rs.normalize_inner(BigRational::one(), r);
                s.sub(rs);
            }
            Term::Lt(l, r) => {
                s.normalize_inner(BigRational::one(), l);
                let mut rs = Eval { vars: Default::default(), cst: BigRational::zero(), nature };
                rs.normalize_inner(BigRational::one(), r);
                s.sub(rs);
            }
            t => s.normalize_inner(BigRational::one(), t),
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
                self.cst += r * v.clone();
                *v = BigRational::zero();
            }
        }
        ixs
    }

    #[trusted]
    fn term(self) -> Answer {
        let mut present_vars: Vec<_> =
            self.vars.into_iter().filter(|(_, v)| !v.is_zero()).collect();
        let num_vars = present_vars.len();
        if num_vars == 1 {
            let (unit_var, cnt) = present_vars.remove(0);
            use Nature::*;
            // Flip sign of inequalities
            let nature = if cnt.is_negative() && matches!(self.nature, Lt | Le | Gt | Ge) {
                self.nature.negate()
            } else {
                self.nature
            };
            return Answer::Unit(unit_var, nature, -self.cst / cnt);
        }

        let watches = present_vars.iter().take(2).map(|(t, _)| t.clone()).collect();
        let lhs = present_vars
            .into_iter()
            .filter_map(|(v, k)| if k.is_zero() { None } else { Some(Term::times(k, v)) })
            .reduce(Term::plus)
            .unwrap_or(Term::Value(Value::rat(0, 1)));

        let rhs = if let Nature::Term = self.nature {
            Term::val(Value::Rat(self.cst))
        } else {
            Term::val(Value::Rat(self.cst * BigInt::from(-1)))
        };

        if num_vars == 0 {
            let v_bool = match self.nature {
                Nature::Eq => lhs == rhs,
                Nature::Neq => lhs != rhs,
                Nature::Lt => lhs.as_val() < rhs.as_val(),
                Nature::Term => return Answer::Val(rhs.as_val()),
                Nature::Le => lhs.as_val() <= rhs.as_val(),
                Nature::Gt => lhs.as_val() > rhs.as_val(),
                Nature::Ge => lhs.as_val() >= rhs.as_val(),
            };

            let v = if v_bool { Term::true_() } else { Term::false_() };
            return Answer::Val(v.as_val());
        } else {
            let t = match self.nature {
                Nature::Eq => Term::eq_(lhs, rhs),
                Nature::Lt => Term::lt(lhs, rhs),
                Nature::Term => lhs,
                Nature::Neq => todo!(),
                Nature::Le => todo!(),
                Nature::Gt => todo!(),
                Nature::Ge => todo!(),
            };
            return Answer::Other(t, watches);
        };
    }

    #[trusted]
    fn normalize_inner(&mut self, scale: BigRational, tm: &Term) {
        match tm {
            Term::Eq(l, r) => {
                unreachable!();
            }
            Term::Plus(l, r) => {
                self.normalize_inner(scale.clone(), l);
                self.normalize_inner(scale, r);
            }
            Term::Times(k, r) => {
                self.normalize_inner(scale * k, r);
            }
            Term::Lt(l, r) => {
                unreachable!()
            }
            Term::Value(Value::Rat(r)) => {
                self.cst += r;
            }
            a => {
                *self.vars.entry(tm.clone()).or_insert_with(|| BigRational::zero()) += scale;
            }
        };
    }

    // Takes a term looking like -k1*var + k2*t1 + ... + C < 0
    // turn it into (k2*t1 + ... + C) / k < var
    // Takes a term and produces the lower bound for `var` (ie: `result < var`)
    fn lower_bound_for(mut self, var: &Term) -> Term {
        let mut coef = self.vars.remove(var).unwrap();
        // Only accept simple bounds
        assert!(matches!(self.nature, Nature::Lt | Nature::Le | Nature::Eq));
        // We need the coefficient for the variable we are eliminating to be negative to recover a correct bound
        assert!(coef.is_negative() || matches!(self.nature, Nature::Eq));
        // Move `var` to the rhs.
        coef = coef.neg();

        let bound_vars: Vec<_> = self.vars.into_iter().filter(|(_, v)| !v.is_zero()).collect();
        let lhs = bound_vars
            .into_iter()
            .map(|(v, k)| Term::times(k / coef.clone(), v))
            .fold(Term::val(Value::Rat(self.cst)), Term::plus);

        lhs
    }

    // Takes a term looking like -k1*var + k2*t1 + ... + C < 0
    // turn it into var < (-k2*t1 + -... + -C) / k
    // Takes a term and produces the lower bound for `var` (ie: `result < var`)
    fn upper_bound_for(mut self, var: &Term) -> Term {
        let coef = self.vars.remove(var).unwrap();

        // Only accept simple bounds
        assert!(matches!(self.nature, Nature::Lt | Nature::Le | Nature::Eq));
        // We need the coefficient for the variable we are eliminating to be positive to recover a correct bound
        assert!(coef.is_positive() || matches!(self.nature, Nature::Eq));

        let bound_vars: Vec<_> = self.vars.into_iter().filter(|(_, v)| !v.is_zero()).collect();
        let lhs = bound_vars
            .into_iter()
            .map(|(v, k)| Term::times(-k / coef.clone(), v))
            .fold(Term::val(Value::Rat(self.cst)), Term::plus);

        lhs
    }
}

fn fourier_motzkin_symbol(nat1: Nature, nat2: Nature) -> Nature {
    use Nature::*;
    match (nat1, nat2) {
        (Lt, _) | (_, Lt) => Lt,
        (Le, _) | (_, Le) => Le,
        (Eq, Eq) => Eq,
        _ => unreachable!("Attempted to eliminate variable between non-normal clauses"),
    }
}

// Given two terms [term1] and [term2] this seeks to eliminate a third variable [var] (which in general is a term) from them
fn fourier_motzkin_resolvent(term1: &Term, term2: &Term, var: &Term) -> Term {
    let s1 = Eval::normalize(&term1);
    let s2 = Eval::normalize(&term2);
    let sym = fourier_motzkin_symbol(s1.nature, s2.nature);

    assert!(s1.vars.contains_key(var));
    assert!(s2.vars.contains_key(var));

    let lhs = s1.lower_bound_for(var);
    let rhs = s2.upper_bound_for(var);

    trace!("FM produced {lhs} {sym:?} {rhs}");
    match sym {
        Nature::Lt => Term::lt(lhs, rhs),
        Nature::Le => Term::leq(lhs, rhs),
        Nature::Eq => Term::eq_(lhs, rhs),
        _ => unreachable!(),
    }
    // let sym = fourier_motzkin_symbol(s1.nature, s2.nature);
}
