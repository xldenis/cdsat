use creusot_contracts::{logic::*, *};

pub enum Term {
    Variable(Var),
    Value(Value),
    Plus(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Conj(Box<Term>, Box<Term>),
    // TODO: complete others
}

impl Term {
    #[logic]
    pub fn sort(self) -> Sort {
        match self {
            Term::Variable(v) => v.1,
            Term::Value(v) => v.sort(),
            Term::Plus(_, _) => Sort::Rational,
            Term::Eq(_, _) => Sort::Boolean,
            Term::Conj(_, _) => Sort::Boolean,
        }
    }

    #[predicate]
    pub fn is_bool(self) -> bool {
        self.sort() == Sort::Boolean
    }
}

pub enum Sort {
    Rational,
    Boolean,
}

pub struct Var(pub Int, pub Sort);

type Rational = Int;

pub enum Value {
    Bool(bool),
    Rat(Rational),
}

impl Value {
    #[predicate]
    pub fn is_bool(self) -> bool {
        self.sort() == Sort::Boolean
    }

    #[logic]
    pub fn sort(self) -> Sort {
        match self {
            Value::Bool(_) => Sort::Boolean,
            Value::Rat(_) => Sort::Rational,
        }
    }

    #[logic]
    #[requires(self.is_bool())]
    #[ensures(result.is_bool())]
    pub fn negate(self) -> Self {
        match self {
            Value::Bool(b) => Value::Bool(!b),
            _ => self,
        }
    }

    #[logic]
    #[requires(self.is_bool())]
    #[ensures(self.negate().negate() == self)]
    fn negate_involutive(self) {}
}

pub enum Assign {
    Decision(Term, Value),
    Justified(FSet<(Term, Value)>, Term, Value),
    Input(Term, Value),
}

impl Assign {
    #[predicate]
    pub fn invariant(self) -> bool {
        match self {
            Assign::Decision(t, v) => t.sort() == v.sort(),
            Assign::Justified(_, t, v) => t.sort() == v.sort() && t.sort() == Sort::Boolean,
            Assign::Input(t, v) => t.sort() == v.sort(),
        }
    }

    #[logic]
    pub fn to_pair(self) -> (Term, Value) {
        match self {
            Assign::Decision(t, val) => (t, val),
            Assign::Input(t, val) => (t, val),
            Assign::Justified(_, t, val) => (t, val),
        }
    }

    #[predicate]
    pub fn justified_sound(self) -> bool {
        match self {
            Assign::Justified(just, t, val) => pearlite! {
              forall<m : Model> m.invariant() ==> m.satisfy_set(just) ==> m.satisfies((t, val))
            },
            _ => true,
        }
    }
}

pub struct Model(Mapping<Var, Value>);

impl Model {
    // Models are 'well-sorted'
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            forall<k : _, v : _> self.0.get(k) == v ==> k.1 == v.sort()
        }
    }

    #[logic]
    #[ensures(self.invariant() ==> result.sort() == t.sort())]
    fn interp(self, t: Term) -> Value {
        match t {
            Term::Variable(v) => self.0.get(v),
            Term::Value(v) => v,
            Term::Plus(l, r) => match (self.interp(*l), self.interp(*r)) {
                (Value::Rat(r1), Value::Rat(r2)) => Value::Rat(r1 + r2), // TODO: Define Rationals
                _ => Value::Rat(-1),
            },
            Term::Conj(l, r) => match (self.interp(*l), self.interp(*r)) {
                (Value::Bool(b1), Value::Bool(b2)) => Value::Bool(b1 && b2), // TODO: Define Rationals
                _ => Value::Bool(false),
            },
            Term::Eq(l, r) => Value::Bool(self.interp(*l) == self.interp(*r)),
        }
    }

    #[predicate]
    pub fn satisfies(self, v: (Term, Value)) -> bool {
        self.interp(v.0) == v.1
    }

    #[predicate]
    pub fn satisfy_set(self, v: FSet<(Term, Value)>) -> bool {
        pearlite! { forall<a : _> v.contains(a) ==> self.satisfies(a) }
    }

    #[predicate]
    pub fn entails(self, j: FSet<(Term, Value)>, c: (Term, Value)) -> bool {
        pearlite! { self.invariant() ==> self.satisfy_set(j) ==> self.satisfies(c) }
    }

    #[logic]
    #[requires(self.satisfy_set(just) ==> self.satisfies(a))]
    #[requires(!self.satisfy_set(cflct))]
    #[requires(cflct.contains(a))]
    #[ensures(!self.satisfy_set(cflct.remove(a).union(just)))]
    fn resolve_sound(
        self,
        cflct: FSet<(Term, Value)>,
        just: FSet<(Term, Value)>,
        a: (Term, Value),
    ) {
    }

    #[logic]
    #[requires(v.sort() == Sort::Boolean)]
    #[requires(t.sort() == Sort::Boolean)]
    #[requires(self.invariant())]
    #[ensures(self.satisfies((t, v)) || self.satisfies((t, v.negate())))]
    fn lemma(self, t: Term, v: Value) {
        match self.interp(t) {
            Value::Bool(_) => (),
            _ => (),
        }
    }
}

pub enum Trail {
    Empty,
    Assign(Assign, Int, Box<Trail>),
}

impl Trail {
    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn sound(self) -> bool {
        match self {
            Trail::Empty => true,
            Trail::Assign(a, _, tl) => tl.sound() && a.justified_sound(),
        }
    }

    #[predicate]
    pub fn is_set_level(self, s: FSet<(Term, Value)>, m: Int) -> bool {
        pearlite! {
            (s == FSet::EMPTY && m == 0) ||
            (exists<i : _> s.contains(i) && self.level_of(i) == m) &&
            (forall<i : _> s.contains(i) ==> self.level_of(i) <= m)
        }
    }

    #[logic]
    #[variant(s.len())]
    #[requires(self.invariant_nonneg())]
    #[ensures(forall<i : _> s.contains(i) ==> self.level_of(i) <= result)]
    #[ensures(s != FSet::EMPTY ==> exists<i : _> s.contains(i) && self.level_of(i) == result)]
    #[ensures(result >= 0)]
    #[ensures(result <= self.level())]
    pub fn set_level(self, s: FSet<(Term, Value)>) -> Int {
        if s.len() == 0 {
            0
        } else if s.len() == 1 {
            self.level_of(s.peek())
        } else {
            let a = s.peek();
            let rec = self.set_level(s.remove(a));
            if self.level_of(a) >= rec {
                self.level_of(a)
            } else {
                rec
            }
        }
    }

    #[logic]
    #[requires(self.invariant_nonneg())]
    #[requires(forall<j : _> set.contains(j) ==> self.level_of(j) <= self.level_of(elem))]
    #[ensures(self.set_level(set.insert(elem)) == self.level_of(elem))]
    pub fn set_level_max(self, set: FSet<(Term, Value)>, elem: (Term, Value)) {}

    #[logic]
    #[requires(self.invariant_nonneg())]
    #[requires(self.level_of(elem) < self.set_level(set))]
    #[ensures(self.set_level(set.insert(elem)) == self.set_level(set))]
    pub fn set_level_min(self, set: FSet<(Term, Value)>, elem: (Term, Value)) {}

    #[predicate]
    fn invariant_level(self) -> bool {
        match self {
            Trail::Empty => true,
            Trail::Assign(a, l, tl) => {
                tl.invariant_level()
                    && match a {
                        Assign::Input(_, _) => l == 0,
                        Assign::Decision(_, _) => tl.level() + 1 == l,
                        Assign::Justified(j, _, _) => tl.set_level(j) == l, // technically speaking we shouldn't need <= level
                    }
            }
        }
    }

    #[predicate]
    fn invariant_nonneg(self) -> bool {
        match self {
            Trail::Empty => true,
            Trail::Assign(a, l, tl) => tl.invariant_nonneg() && l >= 0 && l <= self.level(),
        }
    }

    #[predicate]
    fn invariant_assign(self) -> bool {
        match self {
            Trail::Empty => true,
            Trail::Assign(a, l, tl) => tl.invariant_assign() && a.invariant(),
        }
    }

    #[predicate]
    fn invariant_contains(self) -> bool {
        match self {
            Trail::Empty => true,
            Trail::Assign(a, l, tl) => {
                tl.invariant_contains()
                    && match a {
                        Assign::Justified(j, _, _) => {
                            pearlite! {
                              forall<a : (Term, Value)> j.contains(a) ==> tl.contains(a)
                            }
                        }
                        _ => true,
                    }
            }
        }
    }

    #[predicate]
    fn trail_unique(self) -> bool {
        match self {
            Trail::Empty => true,
            Trail::Assign(a, l, tl) => {
                let ap = a.to_pair();
                !tl.contains(ap)
                    && tl.trail_unique()
                    && if ap.1.is_bool() {
                        !tl.contains((ap.0, ap.1.negate()))
                    } else {
                        true
                    }
            }
        }
    }

    #[predicate]
    pub fn invariant(self) -> bool {
        self.invariant_level()
            && self.invariant_contains()
            && self.trail_unique()
            && self.invariant_nonneg()
            && self.invariant_assign()
    }

    #[predicate]
    pub fn acceptable(self, t: Term, val: Value) -> bool {
        !self.contains((t, val))
            && t.sort() == val.sort()
            && pearlite! { val.is_bool() ==> !self.contains((t, val.negate()))}
    }

    // TODO: While loops to ghost code
    #[logic]
    #[requires(self.invariant_nonneg())]
    #[ensures(result >= 0 && result <= self.level())]
    pub fn level_of(self, d: (Term, Value)) -> Int {
        match self.find(d) {
            Some((_, l)) => l,
            None => 0,
        }
    }

    #[predicate]
    #[ensures(self.invariant_assign() ==> result == true ==> d.0.sort() == d.1.sort())]
    pub fn contains(self, d: (Term, Value)) -> bool {
        match self.find(d) {
            Some(ix) => true,
            None => false,
        }
    }

    #[logic]
    #[requires(self.trail_unique())]
    #[requires(self.contains(d))]
    #[requires(d.1.is_bool())]
    #[ensures(!self.contains((d.0, d.1.negate())))]
    pub fn contains_inverse(self, d: (Term, Value)) {
        d.1.negate_involutive();
        match self {
            Trail::Empty => (),
            Trail::Assign(a, l, tl) => {
                if a.to_pair() == d {
                    ()
                } else {
                    tl.contains_inverse(d)
                }
            }
        }
    }

    #[logic]
    #[ensures(match result {
      Some((a, l)) => a.to_pair() == d,
      _ => true,
    })]
    #[ensures(self.invariant_nonneg() ==> forall<p : _> result == Some(p) ==> p.1 >= 0 && p.1 <= self.level())]
    #[ensures(self.invariant_assign() ==> forall<p : _> result == Some(p) ==> d.0.sort() == d.1.sort())]
    pub fn find(self, d: (Term, Value)) -> Option<(Assign, Int)> {
        match self {
            Trail::Empty => None,
            Trail::Assign(a, l, tl) => {
                if a.to_pair() == d {
                    Some((a, l))
                } else {
                    tl.find(d)
                }
            }
        }
    }

    #[logic]
    #[requires(self.is_justified(d))]
    #[requires(self.sound())]
    #[ensures(forall<m : Model> m.entails(result, d))]
    pub fn justification(self, d: (Term, Value)) -> FSet<(Term, Value)> {
        self.find_justified(d);
        match self.find(d) {
            Some((Assign::Justified(j, _, _), _)) => j,
            _ => FSet::EMPTY,
        }
    }

    #[predicate]
    pub fn is_justified(self, d: (Term, Value)) -> bool {
        match self.find(d) {
            Some((Assign::Justified(_, _, _), _)) => true,
            _ => false,
        }
    }

    #[predicate]
    pub fn is_decision(self, d: (Term, Value)) -> bool {
        match self.find(d) {
            Some((Assign::Decision(_, _), _)) => true,
            _ => false,
        }
    }

    #[predicate]
    pub fn is_input(self, d: (Term, Value)) -> bool {
        match self.find(d) {
            Some((Assign::Input(_, _), _)) => true,
            _ => false,
        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[ensures(result.invariant())]
    #[requires(level >= 0)]
    #[ensures(forall<a : _> self.contains(a) ==> self.level_of(a) <= level ==> result.contains(a) && result.level_of(a) == self.level_of(a))]
    #[ensures(forall<a : _> result.contains(a) ==> self.contains(a) && result.level_of(a) <= level && result.level_of(a) == self.level_of(a))]
    #[ensures(level >= self.level() ==> result == self)]
    #[ensures(forall<a : _> !self.contains(a) ==> !result.contains(a))]
    #[ensures(forall<m : _> self.satisfied_by(m) ==> result.satisfied_by(m))]
    #[ensures(self.level() >= level ==> result.level() == level)]
    #[ensures(self.level() < level ==> result.level() == self.level())]
    #[ensures(result.len() <= self.len())]
    pub fn restrict(self, level: Int) -> Self {
        match self {
            Trail::Empty => Trail::Empty,
            Trail::Assign(a, l, tl) => {
                let tl = tl.restrict(level);
                tl.count_bounds();
                if l <= level {
                    Trail::Assign(a, l, Box::new(tl))
                } else {
                    tl
                }
            }
        }
    }

    #[logic]
    #[ensures(result >= 0)]
    #[ensures(result <= self.len())]
    // #[ensures(self == Trail::Empty || result <= self.len())]
    pub fn level(self) -> Int {
        match self {
            Trail::Empty => 0,
            Trail::Assign(Assign::Decision(_, _), _, tl) => 1 + tl.level(),
            Trail::Assign(_, _, tl) => tl.level(),
        }
    }

    #[logic]
    // #[ensures]
    #[ensures(result >= 0)]
    pub fn len(self) -> Int {
        match self {
            Trail::Empty => 0,
            Trail::Assign(_, _, tl) => tl.len() + 1,
        }
    }

    #[logic]
    #[requires(self.sound())]
    #[requires(self.contains(kv))]
    #[ensures(forall<a : _, l : _> self.find(kv) == Some((a, l)) ==> a.justified_sound())]
    fn find_justified(self, kv: (Term, Value)) {
        match self {
            Trail::Empty => (),
            Trail::Assign(a, l, tl) => {
                if a.to_pair() == kv {
                    ()
                } else {
                    tl.find_justified(kv)
                }
            }
        }
    }

    #[predicate]
    fn satisfied_by(self, m: Model) -> bool {
        pearlite! { forall<a : _> self.contains(a) ==> m.satisfies(a) }
    }

    #[predicate]
    // #[ensures(self.restrict(0).unsat() ==> result)]
    pub fn unsat(self) -> bool {
        pearlite! { forall<m : Model> m.invariant() ==> self.restrict(0).satisfied_by(m) ==> false }
    }

    #[predicate]
    pub fn sat(self) -> bool {
        pearlite! { exists<m : _> self.satisfied_by(m) }
    }

    #[predicate]
    #[ensures(result ==> (rhs.unsat() ==> self.unsat()))]
    pub fn impls(self, rhs: Self) -> bool {
        pearlite! { forall<m : Model> m.invariant() ==> self.restrict(0).satisfied_by(m) ==> rhs.restrict(0).satisfied_by(m) }
    }

    // Lemmas

    #[logic]
    #[requires(self.sound())]
    #[ensures(self.restrict(level).sound())]
    pub fn restrict_sound(self, level: Int) {
        match self {
            Trail::Empty => (),
            Trail::Assign(a, l, tl) => {
                tl.restrict_sound(level);
            }
        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[ensures(forall< a: _> self.contains(a) ==> self.level_of(a) <= self.level())]
    fn count_bounds(self) -> () {
        match self {
            Trail::Empty => (),
            Trail::Assign(Assign::Input(_, _), _, tl) => tl.count_bounds(),
            Trail::Assign(Assign::Decision(_, _), _, tl) => tl.count_bounds(),
            Trail::Assign(Assign::Justified(_, _, _), _, tl) => tl.count_bounds(),
        }
    }

    #[logic]
    #[requires(level >= 0)]
    #[requires(self.invariant())]
    #[requires(self.contains(d))]
    #[requires(level < self.level_of(d))]
    #[ensures(!self.restrict(level).contains(d))]
    pub fn restrict_too_big(self, level: Int, d: (Term, Value)) {
        match self {
            Trail::Empty => (),
            Trail::Assign(a, l, tl) => {
                if a.to_pair() == d {
                    ()
                } else {
                    tl.restrict_too_big(level, d);
                }
            }
        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[requires(l1 >= 0 && l2 >= 0)]
    #[requires(l1 <= l2)]
    #[ensures(self.restrict(l1) == self.restrict(l2).restrict(l1))]
    pub fn restrict_idempotent(self, l1: Int, l2: Int) {
        match self {
            Trail::Empty => (),
            Trail::Assign(_, _, tl) => tl.restrict_idempotent(l1, l2),
        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[requires(self.contains(d))]
    #[requires(d.1.is_bool())]
    #[ensures(!self.contains((d.0, d.1.negate())))]
    fn trail_plausible(self, d: (Term, Value)) {
        match self {
            Trail::Empty => (),
            Trail::Assign(a, l, tl) => {
                if a.to_pair() == d {
                    ()
                } else {
                    tl.trail_plausible(d);
                }
            }
        }
    }
}

pub struct Normal(pub Trail);

impl Normal {
    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn sound(self) -> bool {
        self.0.sound()
    }

    // Γ ⟶ Γ,?A if A is an acceptable 𝒯ₖ-assignment for ℐₖ in Γ_𝒯ₖ for 1 ≤ k ≤ n
    #[predicate]
    #[requires((self.0).invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> (tgt.0).invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))]
    pub fn decide(self, t: Term, val: Value, tgt: Self) -> bool {
        self.0.acceptable(t, val)
            && tgt.0
                == Trail::Assign(
                    Assign::Decision(t, val),
                    self.0.level() + 1,
                    Box::new(self.0),
                )
    }

    // Γ ⟶ Γ, J⊢L, if ¬L ∉ Γ and L is l ← 𝔟 for some l ∈ ℬ
    #[predicate]
    #[requires((self.0).invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> (tgt.0).invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))]
    pub fn deduce(self, just: (FSet<(Term, Value)>, Term, Value), tgt: Self) -> bool {
        self.0.count_bounds();
        just.2.is_bool()
            && self.0.acceptable(just.1, just.2)
            && pearlite! { forall<j : _> just.0.contains(j) ==> self.0.contains(j) }
            && pearlite! { forall<m : Model> m.entails(just.0, (just.1, just.2)) }
            && tgt.0
                == Trail::Assign(
                    Assign::Justified(just.0, just.1, just.2),
                    self.0.set_level(just.0),
                    Box::new(self.0),
                )
    }

    // Γ ⟶ unsat, if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L}) = 0
    #[predicate]
    #[requires((self.0).invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> self.0.unsat())]
    pub fn fail(self, just: (FSet<(Term, Value)>, Term, Value)) -> bool {
        pearlite! { {
          let not_l = (just.1, just.2.negate());
          (forall<j : _> just.0.contains(j) ==> self.0.contains(j) ) &&
          !self.0.contains((just.1, just.2)) &&
          (forall<m : Model> m.entails(just.0, (just.1, just.2))) &&
          self.0.contains(not_l) &&
          self.0.level_of(not_l) == 0 && self.0.set_level(just.0) == 0
        } }
    }

    // Γ ⟶ unsat, if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L}) = 0
    #[predicate]
    #[requires((self.0).invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> self.0.unsat())]
    pub fn fail2(self, just: FSet<(Term, Value)>) -> bool {
        // need to know that if a model satisfies a trail then it satisfies a subset of the trail
        // from that we conclude that if the trail is sat just must be sat and since just is not sat: contradiction
        pearlite! { {
            (forall<j : _> just.contains(j) ==> self.0.contains(j) ) &&
            (forall<m : Model> m.satisfy_set(just) ==> false) &&
            self.0.set_level(just) == 0
        } }
    }

    // just : J |- L
    // Γ ⟶ ⟨ Γ; J ∪ {¬ L} ⟩ if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L }) > 0
    #[predicate]
    #[requires((self.0).invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> (tgt.0).invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))]
    pub fn conflict_solve(self, just: (FSet<(Term, Value)>, Term, Value), tgt: Conflict) -> bool {
        pearlite! { {
          let not_l = (just.1, just.2.negate());
          let conflict = just.0.insert(not_l);
          self.0.contains(not_l) &&
          (forall<j : _> just.0.contains(j) ==> self.0.contains(j) ) &&
          !self.0.contains((just.1, just.2)) &&
          (forall<m : Model> m.invariant() ==> m.entails(just.0, (just.1, just.2))) &&

          self.0.set_level(conflict) > 0 &&
          tgt == Conflict(self.0, conflict)
        } }
    }

    // just : J |- L
    // Γ ⟶ ⟨ Γ; J ∪ {¬ L} ⟩ if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L }) > 0
    #[predicate]
    #[requires((self.0).invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> (tgt.0).invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))]
    pub fn conflict_solve2(self, conflict: FSet<(Term, Value)>, tgt: Conflict) -> bool {
        pearlite! { {
          (forall<j : _> conflict.contains(j) ==> self.0.contains(j) ) &&
          (forall<m : Model> m.satisfy_set(conflict) ==> false) &&
          self.0.set_level(conflict) > 0 &&
          tgt == Conflict(self.0, conflict)
        } }
    }
}

pub struct Conflict(pub Trail, pub FSet<(Term, Value)>);

impl Conflict {
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! { self.0.set_level(self.1) > 0 && self.0.invariant() && forall<a : _> self.1.contains(a) ==> self.0.contains(a) }
    }

    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn sound(self) -> bool {
        pearlite! { self.0.sound() && (forall<m : Model> m.invariant() ==> m.satisfy_set(self.1) ==> false) }
    }

    #[logic]
    pub fn level(self) -> Int {
        self.0.set_level(self.1)
    }

    #[logic]
    #[requires(self.invariant())]
    #[requires(self.sound())]
    #[requires(self.1.contains(ass))]
    #[requires(ass.0.is_bool() && ass.1.is_bool())]
    #[ensures(forall<m : Model> m.invariant() ==> m.satisfy_set(self.1.remove(ass)) ==> m.satisfies((ass.0, ass.1.negate())))]
    pub fn learn_justified(self, ass: (Term, Value)) {
        Model(Mapping::cst(Value::Bool(false))).lemma(ass.0, ass.1);
    }

    // ⟨ Γ; { A } ⊔ E ⟩  ⇒ ⟨ Γ; E ∪ H ⟩ if H ⊢ A in Γ and H does not contain first-order decision A' with level_Γ(E ⊔ {A})
    #[logic]
    #[requires(self.invariant())]
    #[requires(self.sound())]
    #[requires(self.0.is_justified(a))]
    #[requires(self.1.contains(a))]
    #[requires(forall<j : _> self.0.justification(a).contains(j) && !j.1.is_bool() ==> self.0.level_of(j) < self.0.set_level(self.1))]
    #[ensures(result.invariant())]
    #[ensures(result.sound())]
    pub fn resolvef(self, a: (Term, Value)) -> Self {
        let just = self.0.justification(a);
        // Just need to load this
        Model(Mapping::cst(Value::Bool(false))).resolve_sound(self.1, just, a);
        Conflict(self.0, self.1.remove(a).union(just))
    }

    // ⟨ Γ; { A } ⊔ E ⟩  ⇒ ⟨ Γ; E ∪ H ⟩ if H ⊢ A in Γ and H does not contain first-order decision A' with level_Γ(E ⊔ {A})
    #[predicate]
    #[requires(self.invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> tgt.invariant())]
    #[ensures(result ==> tgt.sound())]
    pub fn resolve(self, a: (Term, Value), tgt: Self) -> bool {
        let just = self.0.justification(a);
        // Just need to load this
        Model(Mapping::cst(Value::Bool(false))).resolve_sound(self.1, just, a);
        self.0.is_justified(a)
            && pearlite! { (forall<a : _> just.contains(a) && !a.1.is_bool() ==> self.0.level_of(a) < self.0.set_level(self.1)) }
            && self.1.contains(a)
            && tgt == Conflict(self.0, self.1.remove(a).union(just))
    }

    // ⟨ Γ; { L } ⊔ E ⟩  ⇒ Γ≤m, E⊢¬L, if level_Γ(L) > m, where m = level_Γ(E)
    #[predicate]
    #[requires(self.invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> tgt.0.invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))]
    pub fn backjump(self, l: (Term, Value), tgt: Normal) -> bool {
        let e = self.1.remove(l);
        self.0.restrict_sound(self.0.set_level(e));
        self.0.restrict_too_big(self.0.set_level(e), l);
        self.0.trail_plausible(l);
        self.0.restrict_idempotent(0, self.0.set_level(e));
        l.1.negate_involutive();
        self.learn_justified(l);
        let restricted = self.0.restrict(self.0.set_level(e));
        self.1.contains(l)
            && l.1.is_bool()
            && l.0.is_bool()
            && self.0.level_of(l) > self.0.set_level(e)
            && tgt.0
                == Trail::Assign(
                    Assign::Justified(e, l.0, l.1.negate()),
                    restricted.set_level(e),
                    Box::new(restricted),
                )
    }

    // #[logic]
    // #[requires(self.invariant())]
    // #[requires(self.sound())]
    // #[requires(self.1.contains(l) && l.1.is_bool())]
    // #[requires(self.0.level_of(l) > self.0.set_level(self.1.remove(l)))]
    // #[ensures(result.0.invariant())]
    // #[ensures(result.sound())]
    // #[ensures(self.0.impls(result.0))]
    // pub fn backjump2(self, l: (Term, Value)) -> Normal {
    //     let e = self.1.remove(l);
    //     self.0.restrict_sound(self.0.set_level(e));
    //     self.0.restrict_too_big(self.0.set_level(e), l);
    //     self.0.trail_plausible(l);
    //     l.1.negate_involutive();
    //     let restricted = self.0.restrict(self.0.set_level(e));
    //     Normal(Trail::Assign(
    //         Assign::Justified(e, l.0, l.1.negate()),
    //         restricted.set_level(e),
    //         Box::new(restricted),
    //     ))
    // }

    // ⟨ Γ; { A } ⊔ E ⟩  ⇒ Γ≤m-1, if A is a first-order decision of level m > level_Γ(E)
    #[predicate]
    #[requires(self.invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> tgt.0.invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))]
    pub fn undo_clear(self, a: (Term, Value), tgt: Normal) -> bool {
        pearlite! { {
          let _ = self.0.restrict_sound(self.level() - 1);
          let _ = self.0.restrict_idempotent(0, self.level() - 1);
          let e = self.1.remove(a);
          self.1.contains(a) && !a.1.is_bool() && (exists<l : Int> l >= 0 && self.level() > l && self.0.is_set_level(e, l)) &&
          tgt.0 == self.0.restrict(self.level() - 1)
        } }
    }

    // ⟨ Γ; { L } ⊔ E ⟩  ⇒ Γ≤m-1,?¬L, if H ⊢L is in Γ, m = level_Γ(E) = level_Γ(L) and H contains first-order decision A' of level m
    #[predicate]
    #[requires(self.invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> tgt.0.invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))]
    pub fn undo_decide(self, l: (Term, Value), tgt: Normal) -> bool {
        pearlite! { {
          let _ = self.0.restrict_sound(self.level() - 1);
          self.0.restrict_too_big(self.level() - 1, l);
          self.0.trail_plausible(l);
          l.1.negate_involutive();
          let just = self.0.justification(l);
          let e = self.1.remove(l);
          let restr = self.0.restrict(self.level() - 1);
          self.0.is_justified(l) &&
          l.1.is_bool() &&
          (exists<a : _> just.contains(a) && !a.1.is_bool() && self.0.level_of(a) == self.level() ) &&
          self.level() == self.0.level_of(l) && tgt.0 == Trail::Assign(Assign::Decision(l.0, l.1.negate()), restr.level() + 1, Box::new(restr))
        } }
    }
}
