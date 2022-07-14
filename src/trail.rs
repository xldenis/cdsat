use crate::theory::{self, Assign};
use ::std::ops::Index;
use creusot_contracts::derive::{Clone, PartialEq};
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
    type ModelTy = AssignmentModel;

    #[logic]
    fn model(self) -> Self::ModelTy {
        pearlite! { AssignmentModel { term: @self.term, val: @self.val, reason: @self.reason, level: @self.level}}
    }
}

#[cfg(feature = "contracts")]
pub struct AssignmentModel {
    pub term: theory::Term,
    pub val: theory::Value,
    reason: ReasonModel,
    level: Int,
}

#[cfg_attr(not(feature = "contracts"), derive(Hash))]
#[derive(Clone, PartialEq, Eq)]
enum Reason {
    Justified(Vec<usize>),
    Decision,
    Input,
}

#[cfg(feature = "contracts")]
enum ReasonModel {
    Justified(Seq<usize>),
    Decision,
    Input
}

#[cfg(feature = "contracts")]
impl creusot_contracts::Model for Reason {
    type ModelTy = ReasonModel;

    #[logic]
    fn model(self) -> Self::ModelTy {
        match self {
            Reason::Justified(a1) => ReasonModel::Justified(a1.model()),
            Reason::Decision => ReasonModel::Decision,
            Reason::Input => ReasonModel::Input,
        }
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
            Term::Plus(l, r) => theory::Term::Plus(Box::new((*l).model()), Box::new((*r).model())),
            Term::Eq(l, r) => theory::Term::Eq(Box::new((*l).model()), Box::new((*r).model())),
            Term::Conj(l, r) => theory::Term::Conj(Box::new((*l).model()), Box::new((*r).model())),
        }
    }
}

#[cfg_attr(not(feature = "contracts"), derive(Hash))]
#[derive(Clone, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Rat(u64),
}

#[cfg(feature = "contracts")]
impl creusot_contracts::Model for Value {
    type ModelTy = theory::Value;

    #[logic]
    fn model(self) -> Self::ModelTy {
        match self {
            Value::Bool(b) => theory::Value::Bool(b),
            Value::Rat(r) => theory::Value::Rat(r.model()),
        }
    }
}

impl Value {
    #[trusted]
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

    #[trusted]
    pub(crate) fn negate(&self) -> Self {
        match self {
            Value::Bool(b) => Value::Bool(!b),
            _ => unreachable!(),
        }
    }
}

pub struct Trail {
    // todo make private
    pub assignments: Vec<Assignment>,
    level: usize,
    pub ghost: Ghost<theory::Trail>,
}

impl Trail {
    #[trusted]
    pub fn new(inputs: Vec<(Term, Value)>) -> Self {
        let mut assignments = Vec::new();
        for (term, val) in inputs {
            assignments.push(Assignment {
                term,
                val,
                reason: Reason::Input,
                level: 0,
            })
        }

        Trail {
            assignments,
            level: 0,
            ghost: Ghost::new(&theory::Trail::Empty),
        }
    }

    pub fn len(&self) -> usize {
        self.assignments.len()
    }

    #[predicate]
    pub fn unsat(self) -> bool {
        self.ghost.unsat()
    }

    #[predicate]
    pub fn sat(self) -> bool {
        self.ghost.sat()
    }

    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            self.abstract_relation() && self.ghost.sound() && self.ghost.invariant()
        }
    }

    // #[predicate]
    // pub fn abstract_relation(self) -> bool {
    //     pearlite! {
    //         forall<i: Int> 0 <= i && i < (@self.assignments).len() ==>
    //             {
    //                 let ass = (@self.assignments)[i];
    //                 self.ghost.find(ass.term_value()) == Some((self.abstract_assign(ass), @ass.level))
    //             }
    //     }
    // }

    // a weaker relation
    #[predicate]
    fn abstract_relation(self) -> bool {
        pearlite! {
            forall<i : Int> 0 <= i && i < (@self.assignments).len() ==> self.ghost.contains((@self.assignments)[i].term_value())
        }
    }

    #[logic]
    fn abstract_assign(self, a: Assignment) -> theory::Assign {
        match a.reason {
            Reason::Input => theory::Assign::Input(a.term.model(), a.val.model()),
            Reason::Decision => theory::Assign::Decision(a.term.model(), a.val.model()),
            Reason::Justified(just) => {
                theory::Assign::Justified(self.abstract_justification(just.model()), a.term.model(), a.val.model())
            }
        }
    }

    #[logic]
    #[variant(just.len())]
    #[requires(forall<i : _> 0 <= i && i < just.len() ==> @just[i] < (@self.assignments).len())]
    #[ensures(forall<a : _> result.contains(a) ==> exists<i : _> 0 <= i && i < (@self.assignments).len() && a == (@self.assignments)[i].term_value())]
    // #[ensures(forall<i : _ > 0 <= i && i < just.len() ==> result.contains()]
    pub fn abstract_justification(self, just: Seq<usize>) -> Set<(theory::Term, theory::Value)> {
        if just.len() == 0 {
            Set::EMPTY
        } else {
            let set = self.abstract_justification(just.subsequence(1, just.len()));
            let a = (self.assignments.model())[just[0].model()];
            set.insert((a.term.model(), a.val.model()))
        }
    }

    pub(crate) fn level(&self) -> usize {
        self.level
    }

    #[trusted]
    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    #[requires(self.ghost.acceptable(@term, @val))]
    #[ensures(self.ghost.impls(*(^self).ghost))]
    pub(crate) fn add_decision(&mut self, term: Term, val: Value) {
        self.level += 1;
        self.assignments.push(Assignment {
            term,
            val,
            reason: Reason::Decision,
            level: self.level,
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
                return Some(i);
            }
            i += 1
        }

        return None;
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
        self.assignments.push(Assignment {
            term,
            val,
            reason: Reason::Justified(into_vec),
            level: self.level,
        })
    }

    #[trusted]
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

    #[trusted]
    #[requires(forall<i : _> 0 <= i && i < (@assignments).len() ==> @(@assignments)[i] < (@self.assignments).len())]
    #[ensures(self.ghost.is_set_level(self.abstract_justification(@assignments), @result))]
    pub(crate) fn max_level(&self, assignments: &[usize]) -> usize {
        0
    }
}

impl Index<usize> for Trail {
    type Output = Assignment;

    #[trusted]
    fn index(&self, index: usize) -> &Self::Output {
        &self.assignments[index]
    }
}

impl Assignment {
    #[logic]
    fn term_value(self) -> (theory::Term, theory::Value) {
        (self.term.model(), self.val.model())
    }

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
