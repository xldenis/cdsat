use creusot_contracts::*;

enum Term {
  Variable(Var),
  Value(Value),
  Plus(Box<Term>, Box<Term>, ),
  Eq(Box<Term>, Box<Term>, ),
  // TODO: complete others
}

struct Var(Int);

enum Value { Bool(bool), Rat(Int, Int) }

impl Value {
  #[predicate]
  fn is_bool(self) -> bool {
    pearlite! { matches!(self, Bool(_))}
  }

  #[logic]
  #[requires(self.is_bool())]
  fn negate(self) -> Self {
    match self {
      Bool(b) => Value::Bool(!b),
      _ => self,
    }
  }
}

enum Assign {
  Decision(Var, Value),
  // Should the justification be a set of assigns?
  Justified(Set<(Var, Value)>, Var, Value)
}

impl Assign {
  #[predicate]
  fn same(self, (var, val): (Var, Value)) -> bool {
    pearlite! {
      match self {
        Assign::Decision(var2, val2) => var == var2 && val2 == val2,
        Assign::Justified(_, var2, val2) => var == var2 && val2 == val2,
      }
    }
  }
}

struct Model(Mapping<Var, Value>);

impl Model {
  #[predicate]
  fn satisfies(self, v : (Var,Value)) -> bool {
    self.0.get(v.0) == v.1
  }

  #[predicate]
  fn satisfy_set(self, v : Set<(Var,Value)>) -> bool {
    pearlite! { forall<a : _> v.contains(a) ==> self.satisfies(a) }
  }
}

struct Trail(Seq<(Assign, Int)>);

impl Trail {
  #[predicate]
  fn sound(self) -> bool {
    pearlite! {
      forall<i : _> exists<just: _, var : _, val : _>
        self.0[i] == Assign::Justified(just, var, val) ==>
          forall<m : Model> m.satisfies(just) ==> m.satisfies((var, val))
    }
  }

  #[predicate]
  fn invariant(self) -> bool {
    pearlite! {
      forall<i : _> {
        match self.0[i] {
          (Assign::Decision(_, _), l) => {
            count_decisions(self.0.subsequence(0, i)) == l
          },
          (Assign::Justified(j, _, _), l) => {
            // Justifiant is in the trail
            (forall<k :_> 0 <= k && k < j.len() ==>
              exists<m : _> 0 <= m && m < i && self.0[m].same(j[k])
            ) &&
            // Level is the maximum is of the justifiant's levels
            (j.is_empty() && l == 0) ||
            (exists<k : _> j.contains(k) && self.level(k) == l) &&
            (forall<m : _> j.contains(m) ==> self.level(m) <= l)
          }
        }
      }
    }
  }

  #[predicate]
  fn acceptable(self, var: Var, val: Value) -> bool {
    false
  }

  // TODO: Add map and filter over `Seq` and `Set`
  #[logic]
  fn level(self, d: (Var, Value)) -> Int {
    pearlite! { absurd }
  }

  #[logic]
  fn level_set(self, d: Set<(Var, Value)>) -> Int {
    pearlite! { absurd }
  }

  #[predicate]
  fn contains(self, d: (Var, Value)) -> bool {
    pearlite! { exists<i : _ > 0 <= i && i < self.0.len() && self.0[i].same(d) }
  }

  fn find(self, d: (Var, Value)) -> Option<Int> {
    pearlite! { absurd }
  }

  fn justification(self, d: (Var, Value)) -> Option<Set<(Var, Value)>> {
    pearlite! { absurd }
  }
}

#[logic]
fn count_decision(s: Seq<Assign>) -> Int {
  if s.len() == 0 {
    0
  } else {
    match s[0] {
      Assign::Decision(_, _) => 1 + count_decision(s.subsequence(1, s.len())),
      Assign::Justified(_, _, _) => count_decision(s.subsequence(1, s.len())),
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
  fn decide(self, var: Var, val: Value, tgt: Self) -> bool {
      self.0.acceptable(var, val) &&
      tgt.0 == self.0.push(Assign::Decision(var, val))
  }

  #[predicate]
  fn deduce(self) -> bool {}

  #[predicate]
  fn fail(self) -> bool {}

  // just : J |- L
  // Γ ⟶ ⟨ Γ; J ∪ {¬ L} ⟩ if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L }) > 0
  #[predicate]
  fn conflict_solve(self, just: (Set<(Var, Value)>, Var, Value), tgt: Conflict) -> bool {
    pearlite! {
      let not_l = (just.1, just.2.negate());
      self.0.contains(not_l) &&
      (self.0.level(not_l) > 0 || exists<i : _> just.0.contains(i) && self.0.level(i) > 0) &&
      tgt == Conflict(self.0, just.0.add(not_l))
    }
  }
}

struct Conflict(Trail, Set<(Var, Value)>);

impl Conflict {
  #[predicate]
  fn sound(self) -> bool {
    pearlite! { self.0.sound() && (forall<m : Model> m.satisfies(self.1) ==> false) }
  }

  // ⟨ Γ; { A } ⊔ E ⟩  ⇒ ⟨ Γ; E ∪ H ⟩ if H ⊢ A in Γ and H does not contain first-order decision A' with level_Γ(E ⊔ {A})
  #[predicate]
  fn resolve(self, a: (Var, Value), tgt: Self) -> bool {
    pearlite! {
      let just = self.0.justification(a);
      let conf_level = self.0.level_set(self.1);
      (forall<a : _> just.contains(a) && !a.is_bool() ==> self.0.level(a) < conf_level ) &&
      self.1.contains(a) && tgt == Conflict(self.0, self.1.remove(a).union(just))
    }
  }

  // ⟨ Γ; { L } ⊔ E ⟩  ⇒ Γ≤m, E⊢¬L, if level_\Gamma(L) > m, where m = level_\Gamma(E)
  #[predicate]
  fn backjump(self, l : (Var, Value), tgt: Normal) -> bool {
    pearlite! {
      let e = self.1.remove(l);
      let m = self.0.level_set(e);
      self.1.contains(l) && l.1.is_bool() &&
      tgt.0 == self.0.restrict(m).push(Assign::Justified(e, l.0, l.1.negate()))
    }
  }

  // ⟨ Γ; { A } ⊔ E ⟩  ⇒ Γ≤m-1, if A is a first-order decision of level m > level_\Gamma(E)
  #[predicate]
  fn undo_clear(self, a : (Var, Value), tgt: Normal) -> bool {
    pearlite! {
      let e = self.1.remove(a);
      let m = self.0.level(a);
      self.1.contains(a) && !a.1.is_bool() && m > self.0.level_set(e) &&
      tgt.0 == self.0.restrict(m - 1)
    }
  }

  // ⟨ Γ; { L } ⊔ E ⟩  ⇒ Γ≤m-1,?¬L
  #[predicate]
  fn undo_decide(self, l : (Var, Value), tgt: Normal) -> bool {
    pearlite! {
      let just = self.0.justification(l);
      let e = self.1.remove(l);
      let m = self.0.level_set(e);
      (exists<a : _> just.contains(a) && !a.is_bool() && self.0.level(a) == m ) &&

      m == self.0.level(l) &&  tgt.0.restrict(m - 1).push(Assign::Decide((l.0, l.1.negate())))
    }
  }

}