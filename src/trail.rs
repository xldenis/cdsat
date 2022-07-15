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
    #[requires((@self).is_bool())]
    pub fn bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Rat(_) => unreachable!(),
        }
    }

    #[ensures(result == (@self).is_bool())]
    fn is_bool(&self) -> bool {
        match self {
            Value::Bool(_) => true,
            Value::Rat(_) => false,
        }
    }

    #[requires((@self).is_bool())]
    #[ensures(@result == (@self).negate())]
    pub(crate) fn negate(&self) -> Self {
        match self {
            Value::Bool(b) => Value::Bool(!*b),
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
    // TODO: Allow ghost fields in types
    // TODO: Specify vec iter
    // TODO: Specify vec new
    #[trusted]
    #[ensures(result.invariant())]
    #[ensures(result.ghost.sound())]
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

    #[ensures(@result == (@self.assignments).len())]
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
            self.abstract_relation() && self.ghost.sound() && self.ghost.invariant() &&
            self.ghost.level() == @self.level && // should be for free
            @self.level <= (@self.assignments).len()
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
            (forall<i : Int> 0 <= i && i < (@self.assignments).len() ==> self.ghost.contains((@self.assignments)[i].term_value())) &&
            (forall<i : Int> 0 <= i && i < (@self.assignments).len() ==> self.ghost.level_of((@self.assignments)[i].term_value()) == @(@self.assignments)[i].level)
        }
    }

    #[logic]
    fn abstract_assign(&self, a: Assignment) -> theory::Assign {
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
    #[ensures(forall<a : _> result.contains(a) ==> exists<i : _> 0 <= i && i < just.len() && a == (@self.assignments)[@just[i]].term_value())]
    #[ensures(forall<i : _ > 0 <= i && i < just.len() ==> result.contains((@self.assignments)[@just[i]].term_value()))]
    // #[ensures(result.len() == just.len())]
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

    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    #[requires(self.ghost.acceptable(@term, @val))]
    #[ensures(self.ghost.impls(*(^self).ghost))]
    // unfold invariant
    pub(crate) fn add_decision(&mut self, term: Term, val: Value) {
        let assign = Assignment {
            term,
            val,
            reason: Reason::Decision,
            level: self.level,
        };
        self.assignments.push(assign);
        let abs : Ghost<theory::Assign> = ghost! { self.abstract_assign(assign) };
        self.ghost = ghost! { theory::Trail::Assign(abs.inner(), self.level.model(), Box::new(self.ghost.inner())) };
        self.level += 1;
    }

    pub(crate) fn get(&self, a: &Term) -> Option<&Assignment> {
        match self.index_of(a) {
            Some(i) => Some(&self[i]),
            None => None,
        }
    }

    #[ensures(forall<i : _> result == Some(i) ==> @i < (@self.assignments).len())]
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

    // what specification to give?
    // this is a method on the trail as planning for future forms of justification
    // which need information from the trail to determine the set of relevant clauses
    pub(crate) fn justification(&self, a: &Assignment) -> Option<Vec<usize>> {
        match &a.reason {
            Reason::Justified(v) => {
                Some(v.clone())
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
    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    #[ensures(*(^self).ghost == self.ghost.restrict(@level))]
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

    // #[trusted]
    #[requires(self.invariant())]
    #[requires(forall<i : _> 0 <= i && i < (@assignments).len() ==> @(@assignments)[i] < (@self.assignments).len())]
    #[ensures(self.ghost.is_set_level(self.abstract_justification(@assignments), @result))]
    pub(crate) fn max_level(&self, assignments: &[usize]) -> usize {
        if assignments.len() == 0 {
            return 0;
        }
        // proof_assert!(forall<i : Int> 0 <= i && i < (@self.assignments).len() ==> self.ghost.level_of((@self.assignments)[i].term_value()) == @(@self.assignments)[i].level);

        let mut max : usize = self.assignments[assignments[0]].level();
        let mut i : usize = 1;
        #[invariant(ix, @i <= (@assignments).len())]
        #[invariant(maxx, forall<j : Int> 0 <= j && j < @i ==> self.ghost.level_of((@self.assignments)[@(@assignments)[j]].term_value()) <= @max)]
        #[invariant(exists_max, exists<j : _> 0 <= j && j < @i && self.ghost.level_of((@self.assignments)[@(@assignments)[j]].term_value()) == @max)]
        while i < assignments.len() {
            let a = &self.assignments[assignments[i]];
            let level = a.level();
            if max < level {
                max = level;
            }
            i += 1;
        }

        max
    }
}

impl Index<usize> for Trail {
    type Output = Assignment;

    #[requires(@index < (@self.assignments).len())]
    fn index(&self, index: usize) -> &Self::Output {
        &self.assignments[index]
    }
}

impl Assignment {
    #[logic]
    fn term_value(self) -> (theory::Term, theory::Value) {
        (self.term.model(), self.val.model())
    }

    #[ensures(result == self.level)]
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
