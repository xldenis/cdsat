use ::std::ops::Index;
use creusot_contracts::derive::PartialEq;
use creusot_contracts::*;
use crate::theory::{self, Assign};
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
    Justified(Vec<usize>),
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
    type ModelTy = theory::Term;

    #[logic]
    fn model(self) -> Self::ModelTy {
        match self {
        	Term::Variable(v) => theory::Term::Variable(theory::Var(v.model())),
        	Term::Value(v) => theory::Term::Value(v.model()),
        	Term::Plus(l, r) => theory::Term::Plus(Box::new(l.model()), Box::new(r.model())),
        	Term::Eq(l, r) => theory::Term::Eq(Box::new(l.model()), Box::new(r.model())),
        	Term::Conj(l, r) => theory::Term::Conj(Box::new(l.model()), Box::new(r.model())),
        }
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
    type ModelTy = theory::Value;

    #[logic]
    fn model(self) -> Self::ModelTy {
        match self {
        	Value::Bool(b) => theory::Value::Bool(b),
        	Value::Rat(r) => theory::Value::Rat(0),
        }
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
    ghost: Ghost<theory::Trail>,
}

impl Trail {
	#[trusted]
    pub fn new(inputs: Vec<(Term, Value)>) -> Self {
        let mut assignments = Vec::new();
        for (term, val) in inputs {
            assignments.push(Assignment { term, val, reason: Reason::Input, level: 0 })
        }

        Trail { assignments, level: 0, ghost: Ghost::new(&theory::Trail::Empty) }
    }

    pub fn len(&self) -> usize {
        self.assignments.len()
    }

    #[predicate]
    pub fn invariant(self) -> bool {
    	pearlite! {
    		forall<i: Int> 0 <= i && i < (@self.assignments).len() ==>
    			{
    				let ass = (@self.assignments)[i];
    				let abs = self.abstract_assign(ass);

    				self.ghost.find(abs.to_pair()) == Some((abs, @ass.level)) 
    			}
    	}
    }

    #[logic]
    fn abstract_assign(self, a: Assignment) -> theory::Assign {
    	match a.reason {
    		Reason::Input => theory::Assign::Input(a.term.model(), a.val.model()),
    		Reason::Decision =>  theory::Assign::Decision(a.term.model(), a.val.model()),
    		Reason::Justified(_) =>  theory::Assign::Justified(Set::EMPTY, a.term.model(), a.val.model()),
    	}
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
        match self.index_of(a) {
            Some(i) => Some(&self[i]),
            None => None,
        }
    }

    pub(crate) fn index_of(&self, a: &Term) -> Option<usize> {
        let mut i = 0;
        while i < self.len() {
            if &self[i].term == a {
                return Some(i)
            }
            i += 1
        }

        return None
    }

    #[trusted]
    pub(crate) fn justification(&self, a: &Assignment) -> Option<Vec<usize>> {
        match &a.reason {
            Reason::Justified(v) => {
                let mut j = Vec::new();
                for i in v {
                    j.push(*i);
                }

                Some(j)
            }
            Reason::Decision => None,
            Reason::Input => None,
        }
    }

    pub(crate) fn add_justified(&mut self, into_vec: Vec<usize>, term: Term, val: Value) {
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