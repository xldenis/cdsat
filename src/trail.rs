use ::std::ops::Index;
use creusot_contracts::derive::PartialEq;
use creusot_contracts::*;
// use num_rational::BigRational;

// // Todo: Distinguish between boolean and fo assignments as an optim?
#[cfg_attr(not(feature = "contracts"), derive(Hash))]
#[derive(Clone, PartialEq, Eq)]
pub struct Assignment {
    pub term: Term,
    pub val: Value,
    reason: Reason,
    level: usize,
}

#[cfg(feature = "contracts")]
impl creusot_contracts::Model for Assignment {
    type ModelTy = Self;

    #[logic]
    fn model(self) -> Self {
        self
    }
}

#[cfg_attr(not(feature = "contracts"), derive(Hash))]
#[derive(Clone, PartialEq, Eq)]
enum Reason {
    Justified(Vec<Assignment>),
    Decision,
    Input,
}

#[cfg(feature = "contracts")]
impl creusot_contracts::Model for Reason {
    type ModelTy = Self;

    #[logic]
    fn model(self) -> Self {
        self
    }
}

#[cfg_attr(not(feature = "contracts"), derive(Hash))]
#[derive(Clone, PartialEq, Eq)]
pub enum Term {
    Variable(usize),
    Value(Value),
    Plus(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Conj(Box<Term>, Box<Term>),
    // TODO: complete others
}

#[cfg(feature = "contracts")]
impl creusot_contracts::Model for Term {
    type ModelTy = Self;

    #[logic]
    fn model(self) -> Self {
        self
    }
}

#[cfg_attr(not(feature = "contracts"), derive(Hash))]
#[derive(Clone, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Rat(bool),
}

#[cfg(feature = "contracts")]
impl creusot_contracts::Model for Value {
    type ModelTy = Self;

    #[logic]
    fn model(self) -> Self {
        self
    }
}

impl Value {
    pub fn bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Rat(_) => unreachable!(),
        }
    }

    fn is_bool(&self) -> bool {
        match self {
            Value::Bool(_) => true,
            Value::Rat(_) => false,
        }
    }

    pub(crate) fn negate(&self) -> Self {
        match self {
            Value::Bool(b) => Value::Bool(!b),
            _ => unreachable!(),
        }
    }
}

pub struct Trail {
    assignments: Vec<Assignment>,
    level: usize,
}

impl Trail {
    pub fn new(inputs: Vec<(Term, Value)>) -> Self {
        let mut assignments = Vec::new();
        for (term, val) in inputs {
            assignments.push(Assignment { term, val, reason: Reason::Input, level: 0 })
        }

        Trail { assignments, level: 0 }
    }

    pub fn len(&self) -> usize {
        self.assignments.len()
    }

    // Add a justified assignment to the trail
    // pub(crate) fn add_justified(&self, lit: &Term, polarity: Value) {
    //     todo!()
    // }

    // pub(crate) fn restrict(&mut self, level: usize) {
    //     todo!()
    // }

    pub(crate) fn level(&self) -> usize {
        self.level
    }

    pub(crate) fn add_decision(&mut self, term: Term, val: Value) {
        self.level += 1;
        self.assignments.push(Assignment {
            term, val, reason: Reason::Decision, level: self.level,
        });
    }

    pub(crate) fn get(&self, a: &Term) -> Option<&Assignment> {
        let mut i = 0;
        while i < self.len() {
            if &self[i].term == a {
                return Some(&self[i])
            }
            i += 1
        }

        return None
    }

    #[trusted]
    pub(crate) fn justification(&self, a: &Assignment) -> Option<Vec<Assignment>> {
        match &a.reason {
            Reason::Justified(v) => Some(v.clone()),
            Reason::Decision => None,
            Reason::Input => None,
        }
    }

    pub(crate) fn add_justified(&mut self, into_vec: Vec<Assignment>, term: Term, val: Value) {
        self.assignments.push(Assignment { term, val, reason: Reason::Justified(into_vec), level: self.level })
    }

    pub(crate) fn restrict(&mut self, level: usize) {
        let mut i = 0;

        while i < self.assignments.len() {
            if self.assignments[self.assignments.len() - i].level > level {
                self.assignments.remove(self.assignments.len() - i);
            } else {
                i += 1;
            }
        }
    }
}

impl Index<usize> for Trail {
    type Output = Assignment;

    fn index(&self, index: usize) -> &Self::Output {
        &self.assignments[index]
    }
}

impl Assignment {
    pub(crate) fn level(&self) -> usize {
        self.level
    }

    pub(crate) fn is_bool(&self) -> bool {
        self.val.is_bool()
    }

    pub(crate) fn first_order(&self) -> bool {
        !self.is_bool()
    }

    pub(crate) fn decision(&self) -> bool {
        self.reason == Reason::Decision
    }

    pub(crate) fn value(&self) -> &Value {
        &self.val
    }

    pub(crate) fn term(&self) -> &Term {
        &self.term
    }
}
