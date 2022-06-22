use creusot_contracts::*;

enum Term {
  Variable(Var),
  Value(Value),
  Plus(Box<Term>, Box<Term>, ),
  Eq(Box<Term>, Box<Term>, ),
  // TODO: complete others
}

struct Var(Int);

type Rational = Int;

enum Value { Bool(bool), Rat(Rational) }

impl Value {
  #[predicate]
  fn is_bool(self) -> bool {
    match self {
      Value::Bool(_) => true,
      _ => false
    }
  }

  #[logic]
  #[requires(self.is_bool())]
  fn negate(self) -> Self {
    match self {
      Value::Bool(b) => Value::Bool(!b),
      _ => self,
    }
  }
}

enum Assign {
  Decision(Term, Value),
  Justified(Set<(Term, Value)>, Term, Value),
  Input(Term, Value)
}

impl Assign {
  #[predicate]
  fn same(self, a: (Term, Value)) -> bool {
    pearlite! {{
      let (t, val) = a;
      match self {
        Assign::Decision(t2, val2) => t == t2 && val2 == val2,
        Assign::Input(t2, val2) => t == t2 && val2 == val2,
        Assign::Justified(_, t2, val2) => t == t2 && val2 == val2,
      }
    }}
  }
}

struct Model(Mapping<Var, Value>);

impl Model {
  #[logic]
  fn interp(self, t: Term) -> Value {
    match t {
      Term::Variable(v) => self.0.get(v),
      Term::Value(v) => v,
      Term::Plus(l, r) => match (self.interp(*l), self.interp(*r)) {
        (Value::Rat(r1), Value::Rat(r2)) => Value::Rat(r1 + r2), // TODO: Define Rationals
        _ => Value::Rat(-1)
      },
      Term::Eq(l, r) => Value::Bool(self.interp(*l) == self.interp(*r)),
    }
  }

  #[predicate]
  fn satisfies(self, v : (Term,Value)) -> bool {
    self.interp(v.0) == v.1
  }

  #[predicate]
  fn satisfy_set(self, v : Set<(Term,Value)>) -> bool {
    pearlite! { forall<a : _> v.contains(a) ==> self.satisfies(a) }
  }
}

struct Trail(Seq<(Assign, Int)>);

impl Trail {
  #[predicate]
  fn sound(self) -> bool {
    pearlite! {
      forall<i : Int> exists<just: _, t : _, val : _>
        (self.0)[i].0 == Assign::Justified(just, t, val) &&
          forall<m : Model> m.satisfy_set(just) ==> m.satisfies((t, val))
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
  fn invariant(self) -> bool {
    pearlite! {
      forall<i : _> {
        match self.0[i] {
          (Assign::Decision(_, _), l) => {
            count_decision(self.0.subsequence(0, i)) == l
          },
          (Assign::Input(_, _), l) => l == 0,
          (Assign::Justified(j, _, _), l) => {
            // Justifiant is in the trail
            (forall<k :_> j.contains(k) ==>
              exists<m : _> 0 <= m && m < i && (self.0)[m].0.same(k)
            ) &&
            // Level is the maximum is of the justifiant's levels
            !j.is_empty() && self.is_set_level(j, l)
          }
        }
      }
    }
  }

  // #[predicate]
  // fn acceptable(self, t: Term, val: Value) -> bool {
  //   false
  // }

  // TODO: While loops to ghost code
  #[logic]
  fn level(self, d: (Term, Value)) -> Int {
    match self.find(d) {
      Some(i) => (self.0)[i].1,
      None => 0,
    }
  }

  #[predicate]
  fn contains(self, d: (Term, Value)) -> bool {
    pearlite! { exists<i : _ > 0 <= i && i < self.0.len() && (self.0)[i].0.same(d) }
  }

  #[logic]
  #[variant(self.0.len())]
  fn find(self, d: (Term, Value)) -> Option<Int> {
    if self.0.len() == 0 {
      None
    } else if (self.0)[0].0.same(d) {
      Some(0)
    } else {
      match Trail(self.0.subsequence(1, self.0.len())).find(d) {
        Some(i) => Some(i + 1),
        None => None,
      }
    }
  }

  #[logic]
  fn justification(self, d: (Term, Value)) -> Set<(Term, Value)> {
    match self.find(d) {
      Some(i) => match (self.0)[i].0 {
        Assign::Justified(j, _, _) => j,
        _ => Set::EMPTY,
      }
      None => Set::EMPTY
    }
  }

  #[logic]
  fn is_justified(self, d: (Term, Value)) -> bool {
    match self.find(d) {
      Some(i) => match (self.0)[i].0 {
        Assign::Justified(_, _, _) => true,
        _ => false
      }
      _ => false,
    }
  }

  #[logic]
  #[variant(self.0.len())]
  fn restrict(self, level: Int) -> Self {
    if self.0 == Seq::EMPTY {
      Trail(Seq::EMPTY)
    } else {
      let assign = (self.0)[self.0.len() - 1];
      let restricted = Trail(self.0.subsequence(0, self.0.len() - 1)).restrict(level);
      if assign.1 <= level {
        Trail(restricted.0.push(assign))
      } else {
        restricted
      }
    }
  }

  #[logic]
  #[maintains(self.invariant())]
  #[ensures(exists<i : _> result.0 == self.0.push((Assign::Decision(a.0, a.1), i)))]
  fn push_decision(self, a : (Term, Value)) -> Self {
    Trail(self.0.push((Assign::Decision(a.0, a.1), 1 + count_decision(self.0))))
  }
  // #[logic]
  // fn push(self, a : Assign) -> Self {
  //   match a {
  //     Assign::Decision(_, _) => self,
  //     Assign::Justified(_, _, _) => self,
  //     _ => self
  //   }
  // }
}

#[logic]
#[variant(s.len())]
fn count_decision(s: Seq<(Assign, Int)>) -> Int {
  if s.len() == 0 {
    0
  } else {
    match s[0].0 {
      Assign::Decision(_, _) => 1 + count_decision(s.subsequence(1, s.len())),
      Assign::Justified(_, _, _) => count_decision(s.subsequence(1, s.len())),
      _ => 0
    }
  }
}

struct Normal(Trail);



impl Normal {
  #[predicate]
  fn sound(self) -> bool {
    self.0.sound()
  }

  // Γ ⟶ Γ,?A if A is an acceptable 𝒯ₖ-assignment for ℐₖ in Γ_𝒯ₖ for 1 ≤ k ≤ n
  #[predicate]
  #[requires(self.sound())]
  #[ensures(result ==> tgt.sound())]
  fn decide(self, t: Term, val: Value, tgt: Self) -> bool {
      // self.0.acceptable(t, val) &&
      tgt.0.0 == self.0.0.push((Assign::Decision(t, val), count_decision(self.0.0)))
  }

  // Γ ⟶ Γ, J⊢L, if ¬L ∉ Γ and L is l ← 𝔟 for some l ∈ ℬ
  #[predicate]
  #[requires(self.sound())]
  #[ensures(result ==> tgt.sound())]
  fn deduce(self, just: (Set<(Term, Value)>, Term, Value), tgt: Self) -> bool {
    pearlite!{ {
      let not_l = (just.1, just.2.negate());
      !self.0.contains(not_l) &&
      just.2.is_bool() &&
      (forall<m : Model> m.satisfy_set(just.0) ==> m.satisfies((just.1, just.2))) &&
      exists<i : _> tgt.0.0 == self.0.0.push((Assign::Justified(just.0, just.1, just.2), i))
    } }
  }

  // Γ ⟶ unsafe, if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L}) = 0
  #[predicate]
  #[requires(self.sound())]
  #[ensures(result ==> tgt.sound())]
  fn fail(self, just: (Set<(Term, Value)>, Term, Value), tgt: Self) -> bool {
    pearlite! { {
      let not_l = (just.1, just.2.negate());
      self.0.contains(not_l) &&
      self.0.level(not_l) == 0 && self.0.is_set_level(just.0, 0)
    } }
  }

  // just : J |- L
  // Γ ⟶ ⟨ Γ; J ∪ {¬ L} ⟩ if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L }) > 0
  #[predicate]
  #[requires(self.sound())]
  #[ensures(result ==> tgt.sound())]
  fn conflict_solve(self, just: (Set<(Term, Value)>, Term, Value), tgt: Conflict) -> bool {
    pearlite! { {
      let not_l = (just.1, just.2.negate());
      let conflict = just.0.insert(not_l);
      self.0.contains(not_l) &&
      exists<l : Int> l > 0 && self.0.is_set_level(conflict, l) &&
      tgt == Conflict(self.0, conflict, l)
    } }
  }
}

struct Conflict(Trail, Set<(Term, Value)>, Int);

impl Conflict {
  #[predicate]
  fn invariant(self) -> bool {
    pearlite! { self.0.is_set_level(self.1, self.2) }
  }

  #[predicate]
  fn sound(self) -> bool {
    pearlite! { self.0.sound() && (forall<m : Model> m.satisfy_set(self.1) ==> false) }
  }

  // ⟨ Γ; { A } ⊔ E ⟩  ⇒ ⟨ Γ; E ∪ H ⟩ if H ⊢ A in Γ and H does not contain first-order decision A' with level_Γ(E ⊔ {A})
  #[predicate]
  #[maintains(self.invariant())]
  #[requires(self.sound())]
  #[ensures(result ==> tgt.sound())]
  fn resolve(self, a: (Term, Value), tgt: Self) -> bool {
    pearlite! { {
      let just = self.0.justification(a);
      self.0.is_justified(a) &&
      (forall<a : _> just.contains(a) && !a.1.is_bool() ==> self.0.level(a) < self.2 ) &&
      self.1.contains(a) && tgt == Conflict(self.0, self.1.remove(a).union(just), self.2)
    } }
  }

  // ⟨ Γ; { L } ⊔ E ⟩  ⇒ Γ≤m, E⊢¬L, if level_\Gamma(L) > m, where m = level_\Gamma(E)
  #[predicate]
  #[maintains(self.invariant())]
  #[requires(self.sound())]
  #[ensures(result ==> tgt.sound())]
  fn backjump(self, l : (Term, Value), tgt: Normal) -> bool {
    pearlite! { {
      let e = self.1.remove(l);
      self.1.contains(l) && l.1.is_bool() &&
      self.0.level(l) > self.2 &&
      exists<i : Int> self.0.is_set_level(e, i) && tgt.0.0 == self.0.restrict(self.2).0.push((Assign::Justified(e, l.0, l.1.negate()), i))
    } }
  }

  // ⟨ Γ; { A } ⊔ E ⟩  ⇒ Γ≤m-1, if A is a first-order decision of level m > level_\Gamma(E)
  #[predicate]
  #[maintains(self.invariant())]
  #[requires(self.sound())]
  #[ensures(result ==> tgt.sound())]
  fn undo_clear(self, a : (Term, Value), tgt: Normal) -> bool {
    pearlite! { {
      let e = self.1.remove(a);
      self.1.contains(a) && !a.1.is_bool() && (exists<l : _> self.2 > l && self.0.is_set_level(e, l)) &&
      tgt.0 == self.0.restrict(self.2 - 1)
    } }
  }

  // ⟨ Γ; { L } ⊔ E ⟩  ⇒ Γ≤m-1,?¬L
  #[predicate]
  #[maintains(self.invariant())]
  #[requires(self.sound())]
  #[ensures(result ==> tgt.sound())]
  fn undo_decide(self, l : (Term, Value), tgt: Normal) -> bool {
    pearlite! { {
      let just = self.0.justification(l);
      let e = self.1.remove(l);
      (exists<a : _> just.contains(a) && !a.1.is_bool() && self.0.level(a) == self.2 ) &&
      self.2 == self.0.level(l) &&  tgt.0 == self.0.restrict(self.2 - 1).push_decision((l.0, l.1.negate()))
    } }
  }
}
fn main () {}
