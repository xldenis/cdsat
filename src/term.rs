use std::{fmt::Display, unreachable};

use creusot_contracts::{DeepModel, requires, ensures};
use num_rational::BigRational;

#[cfg_attr(not(creusot), derive(Debug))]
#[derive(Clone, PartialEq, Eq, DeepModel, Copy, PartialOrd, Ord)]
#[DeepModelTy = "theory::Sort"]
pub enum Sort {
    Boolean,
    Rational,
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Sort {
    type ShallowModelTy = theory::Sort;

    #[open]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

#[cfg_attr(not(creusot), derive(Debug))]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Variable(usize, Sort),
    Value(Value),
    Plus(Box<Term>, Box<Term>),
    Times(isize, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Lt(Box<Term>, Box<Term>),
    Conj(Box<Term>, Box<Term>),
    Neg(Box<Term>),
    Disj(Box<Term>, Box<Term>),
    Impl(Box<Term>, Box<Term>),
    // TODO: complete others
}

impl Term {
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
}

impl Display for Term {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        match self {
            Term::Variable(v, _) => write!(f, "x{}", v),
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
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

#[cfg(creusot)]
impl creusot_contracts::DeepModel for Term {
    type DeepModelTy = theory::Term;

    #[open]
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
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
            _ => theory::Term::Value(theory::Value::Bool(true)),
        }
    }
}

#[cfg_attr(not(creusot), derive(Debug))]
#[cfg_attr(not(creusot), derive(Hash))]
#[derive(Clone, PartialEq, Eq, DeepModel, PartialOrd, Ord)]
#[DeepModelTy = "theory::Value"]
pub enum Value {
    Bool(bool),
    Rat(BigRational),
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Value {
    type ShallowModelTy = theory::Value;

    #[open]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.deep_model()
    }
}

impl Value {
    pub fn sort(&self) -> Sort {
        match self {
            Value::Bool(_) => Sort::Boolean,
            Value::Rat(_) => Sort::Rational,
        }
    }
    #[requires(self@.is_bool())]
    pub fn bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Rat(_) => unreachable!(),
        }
    }

    #[requires(self@.is_rational())]
    #[requires(o@.is_rational())]
    pub fn lt(self, o: Self) -> Self {
        match (self, o) {
            (Value::Rat(a), Value::Rat(b)) => Value::Bool(a < b),
            _ => unreachable!(),
        }
    }

    #[requires(self@.is_rational())]
    #[requires(o@.is_rational())]
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

    pub fn zero() -> Self {
        Value::rat(0, 1)
    }
}

impl Term {
    pub fn var(ix: usize, sort: Sort) -> Self {
        Term::Variable(ix, sort)
    }

    pub fn val(v: Value) -> Self {
        Term::Value(v)
    }

    pub fn plus(a: Self, b: Self) -> Self {
        Term::Plus(Box::new(a), Box::new(b))
    }

    pub fn times(k : isize, b: Self) -> Self {
        if k == 0 {
            Term::val(Value::zero())
        } else if k == 1 {
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

    pub fn lt(a: Self, b: Self) -> Self {
        Term::Lt(Box::new(a), Box::new(b))
    }

    pub fn eq_(a: Self, b: Self) -> Self {
        Term::Eq(Box::new(a), Box::new(b))
    }
}

impl Value {
    pub fn scale(self, k : isize) -> Self {
        match self {
            Value::Rat(r) => Value::Rat(r * BigRational::new(k.into(), 1.into())),
            Value::Bool(_) => unreachable!()
        }
    }
    pub fn rat(a: i64, b: i64) -> Self {
        Value::Rat(BigRational::new(a.into(), b.into()))
    }
}