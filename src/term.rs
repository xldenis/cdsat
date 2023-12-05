use std::{fmt::Display, unreachable};

use creusot_contracts::{
    ensures, ghost, logic, open, requires, trusted, Clone, DeepModel, PartialEq,
};

use num::{One, Zero};
use num_rational::BigRational;

#[cfg(creusot)]
use crate::theory;

// #[cfg_attr(not(creusot), derive(Hash))]
#[derive(Clone, Debug, PartialEq, Eq, DeepModel, Copy, Hash)]
#[DeepModelTy = "theory::Sort"]
pub enum Sort {
    Boolean,
    Rational,
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Sort {
    type ShallowModelTy = theory::Sort;

    #[open]
    #[ghost]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

// #[cfg_attr(not(creusot), derive(Hash))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Variable(usize, Sort),
    Value(Value),
    Plus(Box<Term>, Box<Term>),
    Times(BigRational, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Lt(Box<Term>, Box<Term>),
    Conj(Box<Term>, Box<Term>),
    Neg(Box<Term>),
    Disj(Box<Term>, Box<Term>),
    Impl(Box<Term>, Box<Term>),
    // TODO: complete others
}

impl Term {
    #[ensures(result@ == self@.sort())]
    pub(crate) fn sort(&self) -> Sort {
        match self {
            Term::Variable(_, s) => *s,
            Term::Value(Value::Bool(_)) => Sort::Boolean,
            Term::Value(Value::Rat(_)) => Sort::Rational,
            Term::Plus(_, _) => Sort::Rational,
            Term::Eq(_, _) => Sort::Boolean,
            Term::Lt(_, _) => Sort::Boolean,
            Term::Conj(_, _) => Sort::Boolean,
            Term::Neg(_) => Sort::Boolean,
            Term::Disj(_, _) => Sort::Boolean,
            Term::Impl(_, _) => Sort::Boolean,
            Term::Times(_, _) => Sort::Rational,
        }
    }

    pub(crate) fn not(remove: Term) -> Term {
        Term::Neg(Box::new(remove))
    }

    pub fn true_() -> Self {
        Term::Value(Value::Bool(true))
    }

    pub fn false_() -> Self {
        Term::Value(Value::Bool(false))
    }

    pub fn var(ix: usize, sort: Sort) -> Self {
        Term::Variable(ix, sort)
    }

    pub fn val(v: Value) -> Self {
        Term::Value(v)
    }

    pub fn plus(a: Self, b: Self) -> Self {
        Term::Plus(Box::new(a), Box::new(b))
    }

    pub fn times(k: BigRational, b: Self) -> Self {
        if k.is_zero() {
            Term::val(Value::zero())
        } else if k.is_one() {
            b
        } else {
            Term::Times(k, Box::new(b))
        }
    }

    pub fn and(a: Self, b: Self) -> Self {
        Term::Conj(Box::new(a), Box::new(b))
    }

    pub fn or(a: Self, b: Self) -> Self {
        Term::Disj(Box::new(a), Box::new(b))
    }

    pub fn leq(a: Self, b: Self) -> Self {
        Term::Disj(
            Box::new(Term::Lt(Box::new(a.clone()), Box::new(b.clone()))),
            Box::new(Term::Eq(Box::new(a), Box::new(b))),
        )
    }

    pub fn geq(a: Self, b: Self) -> Self {
        Term::leq(b, a)
    }

    pub fn lt(a: Self, b: Self) -> Self {
        Term::Lt(Box::new(a), Box::new(b))
    }

    pub fn eq_(a: Self, b: Self) -> Self {
        Term::Eq(Box::new(a), Box::new(b))
    }

    pub(crate) fn as_val(&self) -> Value {
        if let Term::Value(v) = self {
            v.clone()
        } else {
            panic!()
        }
    }
}

impl Display for Term {
    #[trusted]
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        match self {
            Term::Variable(v, Sort::Boolean) => write!(f, "b{}", v),
            Term::Variable(v, Sort::Rational) => write!(f, "r{}", v),
            Term::Value(v) => write!(f, "{}", v),
            Term::Plus(l, r) => write!(f, "({} + {})", l, r),
            Term::Eq(l, r) => write!(f, "({} = {})", l, r),
            Term::Lt(l, r) => write!(f, "({} < {})", l, r),
            Term::Conj(l, r) => write!(f, "({} ∧ {})", l, r),
            Term::Neg(t) => write!(f, "¬({})", t),
            Term::Disj(l, r) => write!(f, "({} ∨ {})", l, r),
            Term::Impl(l, r) => write!(f, "({} → {})", l, r),
            Term::Times(k, r) => write!(f, "({} * {})", k, r),
        }
    }
}

impl Display for Value {
    #[trusted]
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::Rat(r) => write!(f, "{}", r),
        }
    }
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Term {
    type ShallowModelTy = theory::Term;
    #[open]
    #[ghost]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

#[cfg(creusot)]
impl creusot_contracts::DeepModel for Term {
    type DeepModelTy = theory::Term;

    #[open]
    #[ghost]
    fn deep_model(self) -> Self::DeepModelTy {
        use creusot_contracts::num_rational::Real;
        match self {
            Term::Variable(v, s) => {
                theory::Term::Variable(theory::Var(v.deep_model(), s.deep_model()))
            }
            Term::Value(v) => theory::Term::Value(v.deep_model()),
            Term::Plus(l, r) => {
                theory::Term::Plus(Box::new((*l).deep_model()), Box::new((*r).deep_model()))
            }
            Term::Eq(l, r) => {
                theory::Term::Eq(Box::new((*l).deep_model()), Box::new((*r).deep_model()))
            }
            Term::Conj(l, r) => {
                theory::Term::Conj(Box::new((*l).deep_model()), Box::new((*r).deep_model()))
            }
            Term::Disj(l, r) => {
                theory::Term::Disj(Box::new((*l).deep_model()), Box::new((*r).deep_model()))
            }
            Term::Neg(t) => theory::Term::Neg(Box::new((*t).deep_model())),
            Term::Impl(l, r) => theory::Term::Disj(
                Box::new(theory::Term::Neg(Box::new((*l).deep_model()))),
                Box::new((*r).deep_model()),
            ),
            // WRONG
            Term::Times(l, r) => theory::Term::Plus(
                Box::new(theory::Term::Value(theory::Value::Rat(l.deep_model()))),
                Box::new((*r).deep_model()),
            ),
            Term::Lt(l, r) => {
                theory::Term::Eq(Box::new((*l).deep_model()), Box::new((*r).deep_model()))
            } // _ => theory::Term::Value(theory::Value::Bool(true)),
        }
    }
}

#[cfg_attr(not(creusot), derive(Ord, PartialOrd))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Value {
    Bool(bool),
    Rat(BigRational),
}

#[cfg(creusot)]
impl DeepModel for Value {
    type DeepModelTy = theory::Value;
    #[ghost]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            crate::Value::Bool(b) => theory::Value::Bool(b),
            crate::Value::Rat(br) => theory::Value::Rat(br.deep_model()),
        }
    }
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Value {
    type ShallowModelTy = theory::Value;

    #[open]
    #[ghost]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

impl Value {
    #[ensures(result@ == self@.sort())]
    pub fn sort(&self) -> Sort {
        match self {
            Value::Bool(_) => Sort::Boolean,
            Value::Rat(_) => Sort::Rational,
        }
    }

    #[requires(self@.is_bool())]
    #[ensures(*self == Value::Bool(result))]
    pub fn bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Rat(_) => unreachable!(),
        }
    }

    #[trusted]
    // #[requires(self@.is_rational())]
    // #[requires(o@.is_rational())]
    pub fn lt(self, o: Self) -> Self {
        match (self, o) {
            (Value::Rat(a), Value::Rat(b)) => Value::Bool(a < b),
            _ => unreachable!(),
        }
    }

    #[trusted]
    // #[requires(self@.is_rational())]
    // #[requires(o@.is_rational())]
    pub fn add(self, o: Self) -> Self {
        match (self, o) {
            (Value::Rat(a), Value::Rat(b)) => Value::Rat(a + b),
            _ => unreachable!(),
        }
    }

    #[ensures(result == (self@).is_bool())]
    pub fn is_bool(&self) -> bool {
        match self {
            Value::Bool(_) => true,
            Value::Rat(_) => false,
        }
    }

    #[requires((self@).is_bool())]
    #[ensures(result@ == (self@).negate())]
    pub(crate) fn negate(&self) -> Self {
        match self {
            Value::Bool(b) => Value::Bool(!*b),
            _ => unreachable!(),
        }
    }
}

// Smart constructors

impl Value {
    pub(crate) fn true_() -> Self {
        Value::Bool(true)
    }

    pub(crate) fn false_() -> Self {
        Value::Bool(false)
    }

    pub fn zero() -> Self {
        Value::rat(0, 1)
    }
}

impl Value {
    pub fn scale(self, k: isize) -> Self {
        match self {
            Value::Rat(r) => Value::Rat(r * BigRational::new(k.into(), 1.into())),
            Value::Bool(_) => unreachable!(),
        }
    }
    pub fn rat(a: i64, b: i64) -> Self {
        Value::Rat(BigRational::new(a.into(), b.into()))
    }
}
