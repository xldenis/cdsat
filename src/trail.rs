use std::ops::Index;

use num_rational::BigRational;

// Todo: Distinguish between boolean and fo assignments as an optim?
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Assignment {
    pub term: Term,
    pub val: Value,
    reason: Reason,
    level: usize,
}

#[derive(PartialEq, Eq, Hash, Clone)]
enum Reason {
    Justified(Vec<usize>),
    Decision,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Variable(String),
    Value(Value),
    Plus(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Conj(Box<Term>, Box<Term>),
    // TODO: complete others
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Bool(bool),
    Rat(BigRational),
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

    pub(crate) fn negate(&self) -> _ {
        todo!()
    }
}

pub struct Trail {
    assignments: Vec<Assignment>,
    level: usize,
}

impl Trail {
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

    pub(crate) fn justification(&self, a: Assignment) -> Option<Vec<Assignment>> {
        todo!()
    }

    pub(crate) fn add_justified(&self, into_vec: Vec<Assignment>, term: _, negate: _) -> _ {
        todo!()
    }

    pub(crate) fn restrict(&self, arg1: usize) -> _ {
        todo!()
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
