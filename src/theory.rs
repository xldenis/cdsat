use creusot_contracts::*;

pub enum Term {
    Variable(Var),
    Value(Value),
    Plus(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Conj(Box<Term>, Box<Term>),
    // TODO: complete others
}

pub struct Var(pub Int);

type Rational = Int;

pub enum Value {
    Bool(bool),
    Rat(Rational),
}

impl Value {
    #[predicate]
    fn is_bool(self) -> bool {
        match self {
            Value::Bool(_) => true,
            _ => false,
        }
    }

    #[logic]
    #[requires(self.is_bool())]
    #[ensures(result.is_bool())]
    fn negate(self) -> Self {
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
    Justified(Set<(Term, Value)>, Term, Value),
    Input(Term, Value),
}

impl Assign {
    #[logic]
    pub fn to_pair(self) -> (Term, Value) {
        match self {
            Assign::Decision(t, val) => (t, val),
            Assign::Input(t, val) => (t, val),
            Assign::Justified(_, t, val) => (t, val),
        }
    }

    #[predicate]
    fn justified_sound(self) -> bool {
        match self {
            Assign::Justified(just, t, val) => pearlite! {
              forall<m : Model> m.satisfy_set(just) ==> m.satisfies((t, val))
            },
            _ => true,
        }
    }
}

pub struct Model(Mapping<Var, Value>);

impl Model {
    #[logic]
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
    fn satisfies(self, v: (Term, Value)) -> bool {
        self.interp(v.0) == v.1
    }

    #[predicate]
    fn satisfy_set(self, v: Set<(Term, Value)>) -> bool {
        pearlite! { forall<a : _> v.contains(a) ==> self.satisfies(a) }
    }

    #[logic]
    #[requires(self.satisfy_set(just) ==> self.satisfies(a))]
    #[requires(!self.satisfy_set(cflct))]
    #[requires(cflct.contains(a))]
    #[ensures(!self.satisfy_set(cflct.remove(a).union(just)))]
    fn resolve_sound(self, cflct: Set<(Term, Value)>, just: Set<(Term, Value)>, a: (Term, Value)) {}
}

pub enum Trail {
    Empty,
    Assign(Assign, Int, Box<Trail>),
}

impl Trail {
    #[predicate]
    #[why3::attr = "inline:trivial"]
    fn sound(self) -> bool {
        match self {
            Trail::Empty => true,
            Trail::Assign(a, l, tl) => tl.sound() && a.justified_sound(),
        }
    }

    #[predicate]
    fn is_set_level(self, s: Set<(Term, Value)>, m: Int) -> bool {
        pearlite! {
          (exists<i : _> s.contains(i) && self.level(i) == m) &&
          (forall<i : _> s.contains(i) ==> self.level(i) <= m)
        }
    }

    #[predicate]
    fn invariant_level(self) -> bool {
        match self {
            Trail::Empty => true,
            Trail::Assign(a, l, tl) => {
                tl.invariant_level()
                    && match a {
                        Assign::Input(_, _) => l == 0,
                        Assign::Decision(_, _) => tl.count_decision() == l,
                        Assign::Justified(j, _, _) => tl.is_set_level(j, l),
                    }
            }
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
                              (forall<a : (Term, Value)> j.contains(a) ==>  tl.contains(a))
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
    fn invariant(self) -> bool {
        self.invariant_level() && self.invariant_contains() && self.trail_unique()
    }

    #[predicate]
    fn acceptable(self, t: Term, val: Value) -> bool {
        !self.contains((t, val)) && pearlite! { val.is_bool() ==> !self.contains((t, val.negate()))}
    }

    // TODO: While loops to ghost code
    #[logic]
    fn level(self, d: (Term, Value)) -> Int {
        match self.find(d) {
            Some((_, l)) => l,
            None => 0,
        }
    }

    #[predicate]
    fn contains(self, d: (Term, Value)) -> bool {
        match self.find(d) {
            Some(ix) => true,
            None => false,
        }
    }

    #[logic]
    #[ensures(match result {
      Some((a, l)) => a.to_pair() == d,
      _ => true,
    })]
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
    #[ensures(forall<m : Model> m.satisfy_set(result) ==> m.satisfies(d))]
    fn justification(self, d: (Term, Value)) -> Set<(Term, Value)> {
        self.find_justified(d);
        match self.find(d) {
            Some((Assign::Justified(j, _, _), _)) => j,
            _ => Set::EMPTY,
        }
    }

    #[predicate]
    fn is_justified(self, d: (Term, Value)) -> bool {
        match self.find(d) {
            Some((Assign::Justified(_, _, _), _)) => true,
            _ => false,
        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[ensures(result.invariant())]
    #[ensures(forall<a : _> self.contains(a) ==> self.level(a) <= level ==> result.contains(a) && result.level(a) == self.level(a))]
    #[ensures(forall<a : _> result.contains(a) ==> self.contains(a) && result.level(a) <= level)]
    #[ensures(level >= self.count_decision() ==> result == self)]
    #[ensures(forall<a : _> !self.contains(a) ==> !result.contains(a))]
    fn restrict(self, level: Int) -> Self {
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
    #[requires(self.sound())]
    #[ensures(self.restrict(level).sound())]
    fn restrict_sound(self, level: Int) {
        match self {
            Trail::Empty => (),
            Trail::Assign(a, l, tl) => {
                tl.restrict_sound(level);
            }
        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[ensures(forall< a: _> self.contains(a) ==> self.level(a) <= self.count_decision())]
    fn count_bounds(self) -> () {
        match self {
            Trail::Empty => (),
            Trail::Assign(Assign::Input(_, _), _, tl) => tl.count_bounds(),
            Trail::Assign(Assign::Decision(_, _), _, tl) => tl.count_bounds(),
            Trail::Assign(Assign::Justified(_, _, _), _, tl) => tl.count_bounds(),
        }
    }

    #[logic]
    #[ensures(result >= 1)]
    fn count_decision(self) -> Int {
        match self {
            Trail::Empty => 1,
            Trail::Assign(Assign::Decision(_, _), _, tl) => 1 + tl.count_decision(),
            Trail::Assign(_, _, tl) => tl.count_decision(),
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

    #[logic]
    #[requires(self.invariant())]
    #[requires(self.contains(d))]
    #[requires(level < self.level(d))]
    #[ensures(!self.restrict(level).contains(d))]
    fn restrict_too_big(self, level: Int, d: (Term, Value)) {
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
    fn restrict_idempotent(self, l1: Int, l2: Int) {
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

    #[predicate]
    fn satisfied_by(self, m: Model) -> bool {
        pearlite! { forall<a : _> self.contains(a) ==> m.satisfies(a) }
    }

    #[predicate]
    fn unsat(self) -> bool {
        pearlite! { forall<m : _> self.satisfied_by(m) ==> false }
    }

    #[predicate]
    fn sat(self) -> bool {
        pearlite! { exists<m : _> self.satisfied_by(m) }
    }

    #[predicate]
    fn impls(self, rhs: Self) -> bool {
        pearlite! { forall<m : Model> self.restrict(0).satisfied_by(m) ==> rhs.restrict(0).satisfied_by(m) }
    }
}

struct Normal(Trail);

impl Normal {
    #[predicate]
    #[why3::attr = "inline:trivial"]
    fn sound(self) -> bool {
        self.0.sound()
    }

    // Γ ⟶ Γ,?A if A is an acceptable 𝒯ₖ-assignment for ℐₖ in Γ_𝒯ₖ for 1 ≤ k ≤ n
    #[predicate]
    #[requires((self.0).invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> (tgt.0).invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))]
    fn decide(self, t: Term, val: Value, tgt: Self) -> bool {
        self.0.acceptable(t, val)
            && tgt.0
                == Trail::Assign(
                    Assign::Decision(t, val),
                    self.0.count_decision(),
                    Box::new(self.0),
                )
    }

    // Γ ⟶ Γ, J⊢L, if ¬L ∉ Γ and L is l ← 𝔟 for some l ∈ ℬ
    #[predicate]
    #[requires((self.0).invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> (tgt.0).invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))] // WRONG: GOES WRONG WAY
    fn deduce(self, just: (Set<(Term, Value)>, Term, Value), tgt: Self) -> bool {
        pearlite! { {
          let not_l = (just.1, just.2.negate());
          !self.0.contains(not_l) &&
          !self.0.contains((just.1, just.2)) &&
          just.2.is_bool() &&
          (forall<j : _> just.0.contains(j) ==> self.0.contains(j)) &&
          (forall<m : Model> m.satisfy_set(just.0) ==> m.satisfies((just.1, just.2))) &&
          exists<i : _> self.0.is_set_level(just.0, i) && tgt.0 == Trail::Assign(Assign::Justified(just.0, just.1, just.2), i, Box::new(self.0))
        } }
    }

    // Γ ⟶ unsat, if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L}) = 0
    #[predicate]
    #[requires((self.0).invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> self.0.unsat())]
    fn fail(self, just: (Set<(Term, Value)>, Term, Value)) -> bool {
        pearlite! { {
          let not_l = (just.1, just.2.negate());
          (forall<j : _> just.0.contains(j) ==> self.0.contains(j) ) &&
          !self.0.contains((just.1, just.2)) &&
          (forall<m : Model> m.satisfy_set(just.0) ==> m.satisfies((just.1, just.2))) &&
          self.0.contains(not_l) &&
          self.0.level(not_l) == 0 && self.0.is_set_level(just.0, 0)
        } }
    }

    // Γ ⟶ unsat, if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L}) = 0
    #[predicate]
    #[requires((self.0).invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> self.0.unsat())]
    fn fail2(self, just: Set<(Term, Value)>) -> bool {
        pearlite! { {
            (forall<j : _> just.0.contains(j) ==> self.0.contains(j) ) &&
            (forall<m : Model> m.satisfy_set(just.0) ==> false) &&
            self.0.is_set_level(just.0, 0)
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
    fn conflict_solve(self, just: (Set<(Term, Value)>, Term, Value), tgt: Conflict) -> bool {
        pearlite! { {
          let not_l = (just.1, just.2.negate());
          let conflict = just.0.insert(not_l);
          self.0.contains(not_l) &&
          (forall<j : _> just.0.contains(j) ==> self.0.contains(j) ) &&
          !self.0.contains((just.1, just.2)) &&
          (forall<m : Model> m.satisfy_set(just.0) ==> m.satisfies((just.1, just.2))) &&

          exists<l : Int> l > 0 && self.0.is_set_level(conflict, l) &&
          tgt == Conflict(self.0, conflict, l)
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
    fn conflict_solve2(self, conflict: Set<(Term, Value)>, tgt: Conflict) -> bool {
        pearlite! { {
          (forall<j : _> conlfict.0.contains(j) ==> self.0.contains(j) ) &&
          (forall<m : Model> m.satisfy_set(just.0) ==> false) &&
          exists<l : Int> l > 0 && self.0.is_set_level(conflict, l) &&
          tgt == Conflict(self.0, conflict, l)
        } }
    }
}

struct Conflict(Trail, Set<(Term, Value)>, Int);

impl Conflict {
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! { self.0.is_set_level(self.1, self.2) && self.0.invariant() && forall<a : _> self.1.contains(a) ==> self.0.contains(a) }
    }

    #[predicate]
    #[why3::attr = "inline:trivial"]
    fn sound(self) -> bool {
        pearlite! { self.0.sound() && (forall<m : Model> m.satisfy_set(self.1) ==> false) }
    }

    // ⟨ Γ; { A } ⊔ E ⟩  ⇒ ⟨ Γ; E ∪ H ⟩ if H ⊢ A in Γ and H does not contain first-order decision A' with level_Γ(E ⊔ {A})
    #[predicate]
    #[requires(self.invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> tgt.0.invariant())]
    #[ensures(result ==> tgt.sound())]
    fn resolve(self, a: (Term, Value), tgt: Self) -> bool {
        pearlite! { {
          let just = self.0.justification(a);
          // Just need to load this
          Model(Mapping::cst(Value::Bool(false))).resolve_sound(self.1, just, a);
          self.0.is_justified(a) &&
          (forall<a : _> just.contains(a) && !a.1.is_bool() ==> self.0.level(a) < self.2 ) &&
          self.1.contains(a) && tgt == Conflict(self.0, self.1.remove(a).union(just), self.2)
        } }
    }

    // ⟨ Γ; { L } ⊔ E ⟩  ⇒ Γ≤m, E⊢¬L, if level_Γ(L) > m, where m = level_Γ(E)
    #[predicate]
    #[requires(self.invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> tgt.0.invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))]
    fn backjump(self, l: (Term, Value), tgt: Normal) -> bool {
        pearlite! { {
          let e = self.1.remove(l);
          self.1.contains(l) && l.1.is_bool() &&
          self.0.level(l) > self.2 &&
          exists<i : Int> self.0.is_set_level(e, i) && tgt.0 == Trail::Assign(Assign::Justified(e, l.0, l.1.negate()), i, Box::new(self.0.restrict(self.2)))
        } }
    }

    // ⟨ Γ; { A } ⊔ E ⟩  ⇒ Γ≤m-1, if A is a first-order decision of level m > level_Γ(E)
    #[predicate]
    #[requires(self.invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> tgt.0.invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))]
    fn undo_clear(self, a: (Term, Value), tgt: Normal) -> bool {
        pearlite! { {
          let _ = self.0.restrict_sound(self.2 - 1);
          let _ = self.0.restrict_idempotent(0, self.2 - 1);
          let e = self.1.remove(a);
          self.1.contains(a) && !a.1.is_bool() && (exists<l : Int> l >= 0 && self.2 > l && self.0.is_set_level(e, l)) &&
          tgt.0 == self.0.restrict(self.2 - 1)
        } }
    }

    // ⟨ Γ; { L } ⊔ E ⟩  ⇒ Γ≤m-1,?¬L, if H ⊢L is in Γ, m = level_Γ(E) = level_Γ(L) and H contains first-order decision A' of level m
    #[predicate]
    #[requires(self.invariant())]
    #[requires(self.sound())]
    #[ensures(result ==> tgt.0.invariant())]
    #[ensures(result ==> tgt.sound())]
    #[ensures(result ==> self.0.impls(tgt.0))]
    fn undo_decide(self, l: (Term, Value), tgt: Normal) -> bool {
        pearlite! { {
          let _ = self.0.restrict_sound(self.2 - 1);
          self.0.restrict_too_big(self.2 - 1, l);
          self.0.trail_plausible(l);
          l.1.negate_involutive();
          let just = self.0.justification(l);
          let e = self.1.remove(l);
          let restr = self.0.restrict(self.2 - 1);
          self.0.is_justified(l) &&
          l.1.is_bool() &&
          (exists<a : _> just.contains(a) && !a.1.is_bool() && self.0.level(a) == self.2 ) &&
          self.2 == self.0.level(l) && tgt.0 == Trail::Assign(Assign::Decision(l.0, l.1.negate()), restr.count_decision(), Box::new(restr))
        } }
    }
}
