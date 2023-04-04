use crate::theory::{self, Assign};
use ::std::ops::Index;
use creusot_contracts::{logic::*, vec, *};
use creusot_contracts::{Clone, PartialEq};
// use num_rational::BigRational;
//
#[cfg(not(creusot))]
struct FSet<T>(T);

// // Todo: Distinguish between boolean and fo assignments as an optim?
// #[cfg_attr(not(creusot), derive(Hash))]
#[cfg_attr(not(creusot), derive(Debug))]
#[derive(Clone, PartialEq, Eq)]
pub struct Assignment {
    // TODO: Make private
    pub term: Term,
    // TODO: Make private
    pub val: Value,
    reason: Reason,
    // TODO: Make private
    pub level: usize,
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Assignment {
    type ShallowModelTy = AssignmentModel;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { AssignmentModel { term: @self.term, val: @self.val, reason: @self.reason, level: @self.level}}
    }
}

#[cfg(creusot)]
impl creusot_contracts::DeepModel for Assignment {
    type DeepModelTy = AssignmentModel;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { AssignmentModel { term: @self.term, val: @self.val, reason: @self.reason, level: @self.level}}
    }
}

#[cfg(creusot)]
pub struct AssignmentModel {
    pub term: theory::Term,
    pub val: theory::Value,
    reason: ReasonModel,
    level: Int,
}

// #[cfg_attr(not(creusot), derive(Hash))]
#[cfg_attr(not(creusot), derive(Debug))]
#[derive(Clone, PartialEq, Eq)]
enum Reason {
    Justified(Vec<TrailIndex>),
    Decision,
    Input,
}

#[cfg(creusot)]
enum ReasonModel {
    Justified(Seq<TrailIndex>),
    Decision,
    Input,
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Reason {
    type ShallowModelTy = ReasonModel;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        match self {
            Reason::Justified(a1) => ReasonModel::Justified(a1.shallow_model()),
            Reason::Decision => ReasonModel::Decision,
            Reason::Input => ReasonModel::Input,
        }
    }
}

#[cfg(creusot)]
impl creusot_contracts::DeepModel for Reason {
    type DeepModelTy = ReasonModel;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Reason::Justified(a1) => ReasonModel::Justified(a1.shallow_model()),
            Reason::Decision => ReasonModel::Decision,
            Reason::Input => ReasonModel::Input,
        }
    }
}

#[cfg_attr(not(creusot), derive(Debug))]
#[derive(Clone, PartialEq, Eq)]
pub enum Sort {
    Boolean,
    Rational,
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Sort {
    type ShallowModelTy = theory::Sort;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        match self {
            Sort::Boolean => theory::Sort::Boolean,
            Sort::Rational => theory::Sort::Rational,
        }
    }
}

#[cfg(creusot)]
impl creusot_contracts::DeepModel for Sort {
    type DeepModelTy = theory::Sort;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Sort::Boolean => theory::Sort::Boolean,
            Sort::Rational => theory::Sort::Rational,
        }
    }
}

#[cfg_attr(not(creusot), derive(Debug))]
#[derive(Clone, PartialEq, Eq)]
pub enum Term {
    Variable(usize, Sort),
    Value(Value),
    Plus(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Conj(Box<Term>, Box<Term>),
    Neg(Box<Term>),
    Disj(Box<Term>, Box<Term>),
    Impl(Box<Term>, Box<Term>),
    // TODO: complete others
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Term {
    type ShallowModelTy = theory::Term;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        match self {
            Term::Variable(v, s) => {
                theory::Term::Variable(theory::Var(v.shallow_model(), s.shallow_model()))
            }
            Term::Value(v) => theory::Term::Value(v.shallow_model()),
            Term::Plus(l, r) => theory::Term::Plus(
                Box::new((*l).shallow_model()),
                Box::new((*r).shallow_model()),
            ),
            Term::Eq(l, r) => theory::Term::Eq(
                Box::new((*l).shallow_model()),
                Box::new((*r).shallow_model()),
            ),
            Term::Conj(l, r) => theory::Term::Conj(
                Box::new((*l).shallow_model()),
                Box::new((*r).shallow_model()),
            ),
            _ => theory::Term::Value(theory::Value::Bool(true)),
        }
    }
}

#[cfg(creusot)]
impl creusot_contracts::DeepModel for Term {
    type DeepModelTy = theory::Term;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Term::Variable(v, s) => {
                theory::Term::Variable(theory::Var(v.shallow_model(), s.shallow_model()))
            }
            Term::Value(v) => theory::Term::Value(v.shallow_model()),
            Term::Plus(l, r) => theory::Term::Plus(
                Box::new((*l).shallow_model()),
                Box::new((*r).shallow_model()),
            ),
            Term::Eq(l, r) => theory::Term::Eq(
                Box::new((*l).shallow_model()),
                Box::new((*r).shallow_model()),
            ),
            Term::Conj(l, r) => theory::Term::Conj(
                Box::new((*l).shallow_model()),
                Box::new((*r).shallow_model()),
            ),
            _ => theory::Term::Value(theory::Value::Bool(true)),
        }
    }
}

#[cfg_attr(not(creusot), derive(Debug))]
#[cfg_attr(not(creusot), derive(Hash))]
#[derive(Clone, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Rat(u64),
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for Value {
    type ShallowModelTy = theory::Value;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        match self {
            Value::Bool(b) => theory::Value::Bool(b),
            Value::Rat(r) => theory::Value::Rat(r.shallow_model()),
        }
    }
}

#[cfg(creusot)]
impl creusot_contracts::DeepModel for Value {
    type DeepModelTy = theory::Value;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Value::Bool(b) => theory::Value::Bool(b),
            Value::Rat(r) => theory::Value::Rat(r.shallow_model()),
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
    pub fn is_bool(&self) -> bool {
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

#[cfg_attr(not(creusot), derive(Debug))]
#[derive(PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub struct TrailIndex(usize, usize);

use ::std::cmp::Ordering;
use creusot_contracts::OrdLogic;
impl OrdLogic for TrailIndex {
    #[logic]
    fn cmp_log(self, rhs: Self) -> Ordering {
        match self.0.cmp_log(rhs.0) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => self.1.cmp_log(rhs.1),
        }
    }

    #[law]
    #[ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
    fn cmp_le_log(x: Self, y: Self) {}

    #[law]
    #[ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
    fn cmp_lt_log(x: Self, y: Self) {}
    #[law]
    #[ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
    fn cmp_ge_log(x: Self, y: Self) {}

    #[law]
    #[ensures(x.gt_log(y) == (x.cmp_log(y) == Ordering::Greater))]
    fn cmp_gt_log(x: Self, y: Self) {}

    #[law]
    #[ensures(x.cmp_log(x) == Ordering::Equal)]
    fn refl(x: Self) {}

    #[law]
    #[requires(x.cmp_log(y) == o)]
    #[requires(y.cmp_log(z) == o)]
    #[ensures(x.cmp_log(z) == o)]
    fn trans(x: Self, y: Self, z: Self, o: Ordering) {}

    #[law]
    #[requires(x.cmp_log(y) == Ordering::Less)]
    #[ensures(y.cmp_log(x) == Ordering::Greater)]
    fn antisym1(x: Self, y: Self) {}

    #[law]
    #[requires(x.cmp_log(y) == Ordering::Greater)]
    #[ensures(y.cmp_log(x) == Ordering::Less)]
    fn antisym2(x: Self, y: Self) {}

    #[law]
    #[ensures((x == y) == (x.cmp_log(y) == Ordering::Equal))]
    fn eq_cmp(x: Self, y: Self) {}
}

#[cfg(creusot)]
impl creusot_contracts::ShallowModel for TrailIndex {
    type ShallowModelTy = Self;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self
    }
}

#[cfg(creusot)]
impl creusot_contracts::DeepModel for TrailIndex {
    type DeepModelTy = Self;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}

impl TrailIndex {
    #[ensures(result == self.0)]
    pub fn level(&self) -> usize {
        self.0
    }

    #[logic]
    pub fn level_log(self) -> Int {
        self.0.shallow_model()
    }
}

type Justification = Vec<TrailIndex>;

pub struct Trail {
    // todo make private
    pub assignments: Vec<Vec<Assignment>>,
    pub level: usize,
    pub ghost: Ghost<theory::Trail>,
}

#[cfg(not(creusot))]
impl ::std::fmt::Debug for Trail {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        self.assignments.fmt(f)
    }
}

impl Trail {
    #[trusted]
    #[ensures(result.invariant())]
    #[ensures(result.ghost.sound())]
    pub fn new(inputs: Vec<(Term, Value)>) -> Self {
        let mut input = Vec::new();
        for (term, val) in inputs {
            input.push(Assignment {
                term,
                val,
                reason: Reason::Input,
                level: 0,
            })
        }

        let mut assignments = Vec::new();
        assignments.insert(0, input);

        Trail {
            assignments,
            level: 0,
            ghost: ghost! { theory::Trail::Empty },
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
            self.abstract_relation() && self.ghost.sound() && self.ghost.invariant()
            && self.ghost.level() == @self.level
            && @self.level == (@self.assignments).len() - 1
            // && pearlite! { forall<l : _> 0 <= l && l < (@self.assignments).len() ==> (@(@self.assignments)[l]).unique() }
            && pearlite! { forall<i : TrailIndex, j : TrailIndex> self.contains(i) ==> self.contains(j) ==> i != j ==> self.index_logic(i) != self.index_logic(j) }
            && self.justified_is_justified()
        }
    }

    #[predicate]
    fn justified_is_justified(self) -> bool {
        pearlite! {
            forall<ix : _> self.contains(ix) ==>
                match (@(@self.assignments)[@ix.0])[@ix.1].reason {
                    Reason::Justified(_) => self.ghost.is_justified(self.index_logic(ix)),
                    _ => true,
                }
        }
    }

    #[predicate]
    fn abstract_relation(self) -> bool {
        pearlite! {
            (forall<ix : _> self.contains(ix) ==> self.ghost.contains(self.index_logic(ix))) &&
            (forall<ix : _> self.contains(ix) ==> self.ghost.level_of(self.index_logic(ix)) == @ix.0) &&
            (forall<a : _> self.ghost.contains(a) ==> exists<ix : _> self.contains(ix) && ix.level_log() == self.ghost.level_of(a) && self.index_logic(ix) == a)
        }
    }

    #[predicate]
    pub fn contains(self, ix: TrailIndex) -> bool {
        pearlite! {
            @ix.0 < (@self.assignments).len() && @ix.1 < (@(@self.assignments)[@ix.0]).len()
        }
    }

    #[logic]
    fn abstract_assign(&self, a: Assignment) -> theory::Assign {
        match a.reason {
            Reason::Input => theory::Assign::Input(a.term.shallow_model(), a.val.shallow_model()),
            Reason::Decision => {
                theory::Assign::Decision(a.term.shallow_model(), a.val.shallow_model())
            }
            Reason::Justified(just) => theory::Assign::Justified(
                self.abstract_justification(just.shallow_model()),
                a.term.shallow_model(),
                a.val.shallow_model(),
            ),
        }
    }

    #[logic]
    #[variant(just.len())]
    #[ensures(result.len() == just.len())]
    #[requires(forall<i : _> 0 <= i && i < just.len() ==> self.contains(just[i]))]
    #[ensures(forall< a : _> result.contains(a) ==> exists<ix : _> self.contains(ix) && a == self.index_logic(ix))]
    #[ensures(forall< a : _> result.contains(a) ==> exists<ix : _> just.contains(ix) && a == self.index_logic(ix))]
    #[ensures(forall<i : _> 0 <= i && i < just.len() ==> result.contains(self.index_logic(just[i])))]
    pub fn abstract_justification(
        &self,
        just: Seq<TrailIndex>,
    ) -> FSet<(theory::Term, theory::Value)> {
        self.abs_just_inner(just, 0)
    }

    #[logic]
    #[variant(just.len() - ix)]
    #[requires(ix >= 0)]
    pub fn abs_just_inner(
        self,
        just: Seq<TrailIndex>,
        ix: Int,
    ) -> FSet<(theory::Term, theory::Value)> {
        if ix < just.len() {
            let set = self.abs_just_inner(just, ix + 1);
            let ix = just[ix];
            let a = (self.assignments.shallow_model())[ix.0.shallow_model()].shallow_model()
                [ix.1.shallow_model()];
            set.insert((a.term.shallow_model(), a.val.shallow_model()))
        } else {
            FSet::EMPTY
        }
    }

    pub(crate) fn level(&self) -> usize {
        self.level
    }

    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    #[requires(self.ghost.acceptable(@term, @val))]
    #[ensures(self.ghost.impls(*(^self).ghost))]
    #[trusted] // for arithmetic
    pub(crate) fn add_decision(&mut self, term: Term, val: Value) {
        self.assignments.len();
        self.level += 1;
        let assign = Assignment {
            term,
            val,
            reason: Reason::Decision,
            level: self.level,
        };
        self.assignments.push(vec![assign]);
    }

    pub(crate) fn index_of(&self, a: &Term) -> Option<TrailIndex> {
        let mut level = 0;
        for assignments in &self.assignments {
            let mut offset = 0;
            for asgn in assignments {
                if &asgn.term == a {
                    return Some(TrailIndex(level, offset));
                }
                offset += 1;
            }
            level += 1;
        }
        None
    }

    // what specification to give?
    // this is a method on the trail as planning for future forms of justification
    // which need information from the trail to determine the set of relevant clauses
    #[ensures(forall<i : _> 0 <= i && i < (@result).len() ==> self.contains((@result)[i]))]
    #[ensures(self.abstract_justification(@result) == self.ghost.justification(self.index_logic(a)))]
    #[ensures(forall<i : _> 0 <= i && i < (@result).len() ==> (@result)[i].level_log() <= a.level_log())]
    pub(crate) fn justification(&self, a: TrailIndex) -> Vec<TrailIndex> {
        match &self[a].reason {
            Reason::Justified(v) => v.clone(),
            Reason::Decision => Vec::new(),
            Reason::Input => Vec::new(),
        }
    }

    #[maintains((mut self).invariant())]
    #[requires((@val).is_bool())]
    #[requires(self.ghost.acceptable(@term, @val))]
    #[requires(forall<m : theory::Model> m.invariant() ==> m.satisfy_set(self.abstract_justification(@into_vec)) ==> m.satisfies((@term, @val)))]
    pub(crate) fn add_justified(&mut self, into_vec: Vec<TrailIndex>, term: Term, val: Value) {
        let level = self.max_level(&into_vec);
        let just: Ghost<FSet<(theory::Term, theory::Value)>> =
            ghost! { self.abstract_justification(into_vec.shallow_model()) };
        let a = Assignment {
            term,
            val,
            reason: Reason::Justified(into_vec),
            level,
        };
        self.assignments[level].push(a);
    }

    // #[trusted]
    #[maintains((mut self).invariant())]
    #[requires(@level <= @self.level)]
    #[ensures(*(^self).ghost == self.ghost.restrict(@level))]
    // Redundant but incredibly useful
    #[ensures(forall<ix : TrailIndex> ix.level_log() <= @level ==> self.contains(ix) ==> (^self).contains(ix))]
    #[ensures(forall<ix : TrailIndex> (^self).contains(ix) ==> self.index_logic(ix) == (^self).index_logic(ix))]
    pub(crate) fn restrict(&mut self, level: usize) {
        let old: Ghost<&mut Trail> = ghost! { self };

        #[invariant(x, forall<i : _> 0 <= i && i <= @self.level ==> (@self.assignments)[i] == (@old.assignments)[i])]
        #[invariant(abs_rel2, self.invariant())]
        #[invariant(proph_const, ^self == ^*old)]
        #[invariant(restrict, *self.ghost == old.ghost.restrict(@self.level))]
        #[invariant(l, self.level >= level)]
        while level < self.level {
            self.assignments.pop();
            self.level -= 1;
            self.ghost = ghost! { self.ghost.inner().restrict(self.level.shallow_model()) };
            proof_assert!(self.ghost.restrict_idempotent(@self.level, @self.level + 1); true);
        }
        proof_assert!(level == self.level);
        proof_assert!(
            self.ghost.inner() == old.inner().ghost.inner().restrict(level.shallow_model())
        );
        proof_assert!(old.ghost.restrict_sound(@level); true);
    }

    // #[trusted]
    #[requires(self.invariant())]
    #[ensures(self.ghost.set_level(self.abstract_justification(@assignments)) == @result)]
    pub(crate) fn max_level(&self, assignments: &[TrailIndex]) -> usize {
        if assignments.len() == 0 {
            return 0;
        }
        let mut max = 0;
        for ix in assignments {
            if ix.0 > max {
                max = ix.0
            }
        }
        max
    }

    #[logic]
    pub fn index_logic(self, ix: TrailIndex) -> (theory::Term, theory::Value) {
        pearlite! {
            (@(@self.assignments)[@ix.0])[@ix.1].term_value()
        }
    }

    pub(crate) fn indices(&mut self) -> IndexIterator<'_> {
        IndexIterator {
            trail: self,
            cur_ix: TrailIndex(0, 0),
        }
    }
}

/// Offers an iterator over all indices in the trail, while allowing new justified decisions to be added
///
pub struct IndexIterator<'a> {
    trail: &'a mut Trail,
    cur_ix: TrailIndex,
}

impl IndexIterator<'_> {
    pub fn add_justified(&mut self, just: Justification, term: Term, value: Value) {
        self.trail.add_justified(just, term, value)
    }

    pub fn trail(&self) -> &Trail {
        &self.trail
    }

    // Not an actual iterator impl because it crashes...
    #[trusted]
    pub fn next(&mut self) -> Option<TrailIndex> {
        if self.cur_ix.0 >= self.trail.assignments.len() {
            return None;
        };

        if self.cur_ix.1 < self.trail.assignments[self.cur_ix.0].len() {
            let res = self.cur_ix;
            self.cur_ix.1 += 1;
            return Some(res);
        }

        self.cur_ix.0 += 1;
        self.cur_ix.1 = 0;

        self.next()
    }
}

impl Index<TrailIndex> for Trail {
    type Output = Assignment;

    // #[requires(@index < (@self.assignments).len())]
    // #[ensures(*result == (@self.assignments)[@index])]
    #[requires(self.contains(index))]
    #[ensures(*result == (@(@self.assignments)[@index.0])[@index.1])]
    fn index(&self, index: TrailIndex) -> &Self::Output {
        &self.assignments[index.0][index.1]
    }
}

impl Assignment {
    #[logic]
    pub fn term_value(&self) -> (theory::Term, theory::Value) {
        (self.term.shallow_model(), self.val.shallow_model())
    }

    #[ensures(result == self.level)]
    pub(crate) fn level(&self) -> usize {
        self.level
    }

    #[ensures(result == (@self.val).is_bool())]
    pub(crate) fn is_bool(&self) -> bool {
        self.val.is_bool()
    }

    #[ensures(result != (@self.val).is_bool())]
    pub(crate) fn is_first_order(&self) -> bool {
        !self.is_bool()
    }

    #[ensures(result == (exists<j : _> self.reason == Reason::Justified(j)))]
    pub(crate) fn is_justified(&self) -> bool {
        matches!(self.reason, Reason::Justified(_))
    }

    #[ensures(result == (self.reason == Reason::Decision))]
    pub(crate) fn is_decision(&self) -> bool {
        self.reason == Reason::Decision
    }

    #[ensures(result == (self.reason == Reason::Input))]
    pub(crate) fn is_input(&self) -> bool {
        self.reason == Reason::Input
    }

    #[ensures(*result == self.val)]
    pub(crate) fn value(&self) -> &Value {
        &self.val
    }

    #[ensures(*result == self.term)]
    pub(crate) fn term(&self) -> &Term {
        &self.term
    }
}
