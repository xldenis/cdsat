use std::ops::Index;

use num_rational::BigRational;

// Todo: Distinguish between boolean and fo assignments as an optim?
pub struct Assignment {
    term: Term,
    val: Value,
    reason: Reason,
}

enum Reason {
    Justified,
    Decision,
}

pub enum Term {
    Variable(String),
    Value(Value),
    Plus(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    // TODO: complete others
}

pub enum Value {
    Bool(bool),
    Rat(BigRational),
}

pub struct Trail(Vec<Assignment>);

impl Trail {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    // Checks if an assignment is unit and if so returns the term which would make it unit
    pub(crate) fn is_unit(&self, i: usize) -> Option<&Term> {
        todo!()
    }

    // Add a justified assignment to the trail
    pub(crate) fn add_justified(&self, lit: &Term, polarity: Value) {
        todo!()
    }

    pub(crate) fn restrict(&mut self, level: usize) {
    	todo!()
    }
}

impl Index<usize> for Trail {
    type Output = Assignment;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}


impl Term {
	// Checks if a term is of sort `bool`
    pub(crate) fn is_bool(&self) -> bool {
        todo!()
    }

    // Returns the polarity of a *boolean* term
    pub(crate) fn polarity(&self) -> bool {
        todo!()
    }
}
