use creusot_contracts::*;

enum Term {
    Variable(Var),
    Value(Value),
    Plus(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    // TODO: complete others
}

// TODO move these into stdlib
#[predicate]
fn filtered<T>(s: Seq<T>, t: Seq<T>) -> bool {
    pearlite! {
      forall<i : _> 0 <= i && i < t.len() ==>
        exists< j : _> i <= j && j < s.len() && t[i] == s[j]
    }
}

#[predicate]
fn unique<T>(s: Seq<T>) -> bool {
    pearlite! {
      forall<i : _, j : _> 0 <= i && i < s.len() ==> 0 <= j && j < s.len() ==>
        i != j ==> s[i] != s[j]
    }
}

struct Var(Int);

type Rational = Int;

enum Value {
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
    Input(Term, Value),
}

impl Assign {
    // Use to_pair
    #[predicate]
    fn same(self, a: (Term, Value)) -> bool {
        pearlite! {{
          let (t, val) = a;
          match self {
            Assign::Decision(t2, val2) => t == t2 && val == val2,
            Assign::Input(t2, val2) => t == t2 && val == val2,
            Assign::Justified(_, t2, val2) => t == t2 && val == val2,
          }
        }}
    }

    #[logic]
    #[ensures(self.same(result))]
    fn to_pair(self) -> (Term, Value) {
        match self {
            Assign::Decision(t, val) => (t, val),
            Assign::Input(t, val) => (t, val),
            Assign::Justified(_, t, val) => (t, val),
        }
    }

    #[predicate]
    fn justified_sound(self) -> bool {
        pearlite! {
          exists<just: _, t : _, val : _>
            self == Assign::Justified(just, t, val) &&
              forall<m : Model> m.satisfy_set(just) ==> m.satisfies((t, val))
        }
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
                _ => Value::Rat(-1),
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
}

enum Trail {
    Empty,
    Assign(Assign, Int, Box<Trail>),
}

impl Trail {
    #[predicate]
    #[why3::attr = "inline:trivial"]
    fn sound(self) -> bool {
        match self {
            Trail::Empty => true,
            Trail::Assign(a, l, tl) => {
                tl.sound()
                    && match a {
                        Assign::Justified(just, t, val) => a.justified_sound(),
                        _ => true,
                    }
            }
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
        true
        // pearlite! {
        //   forall<i : _, j :_>
        //     0 <= i && i < self.0.len() ==>
        //     0 <= j && j < self.0.len() ==>
        //     i != j ==>
        //     !(self.0)[i].0.same((self.0)[j].0.to_pair())
        //     // (self.0)[i].0.same((self.0)[j].0.to_pair()) ==> i == j
        //     //
        // }
    }

    #[predicate]
    fn invariant(self) -> bool {
        self.invariant_level() && self.invariant_contains() && self.trail_unique()
    }

    // #[logic]
    // #[requires(self.invariant())]
    // #[requires(!(self.0)[i].0.same((self.0)[j].0.to_pair()))]
    // #[ensures((self.0)[i] != (self.0)[j])]
    // fn omg(self, i: Int, j: Int) {}

    // // Need seq.FreeMonoid
    // #[logic]
    // #[requires(self.invariant())]
    // #[requires(self.0.len() > 0)]
    // #[ensures(Trail(self.0.subsequence(0, self.0.len() - 1)).invariant())]
    // fn invariant_mono(self) {}

    // #[logic]
    // #[requires(self.trail_unique())]
    // #[requires(self.is_set_level(j, l))]
    // #[ensures()]

    // #[predicate]
    // fn acceptable(self, t: Term, val: Value) -> bool {
    //   false
    // }

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
    // #[requires(d == d)]
    // #[ensures(forall<i : _> result == Some(i) ==>
    //   0 <= i && i < self.0.len() &&
    //   exists<a : Assign, l : _> a.same(d) && (self.0)[i] == (a, l)
    // )]
    fn find(self, d: (Term, Value)) -> Option<(Assign, Int)> {
        match self {
            Trail::Empty => None,
            Trail::Assign(a, l, tl) => {
                if a.same(d) {
                    Some((a, l))
                } else {
                    tl.find(d)
                }
            }
        }
    }

    #[logic]
    #[requires(self.is_justified(d))]
    // #[ensures(exists<i : _> (self.0)[i].0 == Assign::Justified(result, d.0, d.1) &&
    //   (self.sound() ==> (self.0)[i].0.justified_sound())
    //   )]
    fn justification(self, d: (Term, Value)) -> Set<(Term, Value)> {
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
    #[requires(self.trail_unique())]
    // #[ensures(unique(self))]
    fn trail_unique_unique(self) {
        // pearlite! { self.omg(0, 0) }
    }

    // #[logic]
    // #[requires(!self.contains(a.to_pair()))]
    // #[requires(self.invariant())]
    // #[ensures(self.invariant())]
    // fn push(self, a : Assign) -> Self {
    //   self
    // }

    #[logic]
    // #[variant(self.0.len())]
    #[requires(self.invariant())]
    #[ensures(result.invariant())]
    // #[ensures(filtered(self.0, result.0))]
    // #[ensures(result.0.len() <= self.0.len())]
    // // #[ensures(forall<i : _> 0 <= i && i < self.0.len() ==> (self.0)[i].1 <= level ==> exists<j : Int> 0 <= j && j <= i && j < result.0.len() && (result.0)[j] == (self.0)[i])]
    #[ensures(forall<a : _> self.contains(a) ==> self.level(a) <= level ==> result.contains(a) && result.level(a) == self.level(a))]
    #[ensures(level >= self.count_decision() ==> result == self)]
    // #[ensures(forall<a : _> result.contains(a) ==> self.contains(a))]
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
        // self.trail_unique_unique();
        // if self.0.len() == 0 {
        //   Trail(Seq::EMPTY)
        // } else {
        //   let assign = (self.0)[self.0.len() - 1];
        //   self.invariant_mono();
        //   let restricted = Trail(self.0.subsequence(0, self.0.len() - 1)).restrict(level);
        //   if assign.1 <= level {
        //     Trail(restricted.0.push(assign))
        //   } else {
        //     restricted
        //   }
        // }
    }

    #[logic]
    #[requires(self.sound())]
    #[ensures(self.restrict(level).sound())]
    fn restrict_sound(self, level: Int) {}

    #[logic]
    #[requires(self.invariant())]
    #[ensures(result.invariant())]
    #[requires(self.sound())]
    #[ensures(result.sound())]
    // #[ensures(exists<i : _> result.0 == self.0.push((Assign::Decision(a.0, a.1), i)))]
    fn push_decision(self, a: (Term, Value)) -> Self {
        self
        // Trail(self.0.push((Assign::Decision(a.0, a.1), 1 + count_decision(self.0))))
    }
    // #[logic]
    // fn push(self, a : Assign) -> Self {
    //   match a {
    //     Assign::Decision(_, _) => self,
    //     Assign::Justified(_, _, _) => self,
    //     _ => self
    //   }
    // }

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
    #[ensures(result >= 0)]
    fn count_decision(self) -> Int {
        match self {
            Trail::Empty => 0,
            Trail::Assign(Assign::Decision(_, _), _, tl) => 1 + tl.count_decision(),
            Trail::Assign(_, _, tl) => tl.count_decision(),
        }
    }
}

// #[logic]
// fn count_decision(s: Trail) -> Int {
// if s.len() == 0 {
//   0
// } else {
//   match s[0].0 {
//     Assign::Decision(_, _) => 1 + count_decision(s.subsequence(1, s.len())),
//     Assign::Justified(_, _, _) => count_decision(s.subsequence(1, s.len())),
//     _ => 0
//   }
// }
// 0

// }
// struct Normal(Trail);

// impl Normal {
//   #[predicate]
//   #[why3::attr="inline:trivial"]
//   fn sound(self) -> bool {
//     self.0.sound()
//   }

//   // Γ ⟶ Γ,?A if A is an acceptable 𝒯ₖ-assignment for ℐₖ in Γ_𝒯ₖ for 1 ≤ k ≤ n
//   #[predicate]
//   #[requires((self.0).invariant())]
//   #[requires(self.sound())]
//   #[ensures(result ==> (tgt.0).invariant())]
//   #[ensures(result ==> tgt.sound())]
//   fn decide(self, t: Term, val: Value, tgt: Self) -> bool {
//       // self.0.acceptable(t, val) &&
//       tgt.0.0 == self.0.0.push((Assign::Decision(t, val), count_decision(self.0.0)))
//   }

//   // Γ ⟶ Γ, J⊢L, if ¬L ∉ Γ and L is l ← 𝔟 for some l ∈ ℬ
//   #[predicate]
//   #[requires((self.0).invariant())]
//   #[requires(self.sound())]
//   #[ensures(result ==> (tgt.0).invariant())]
//   #[ensures(result ==> tgt.sound())]
//   fn deduce(self, just: (Set<(Term, Value)>, Term, Value), tgt: Self) -> bool {
//     pearlite!{ {
//       let not_l = (just.1, just.2.negate());
//       !self.0.contains(not_l) &&
//       just.2.is_bool() &&
//       (forall<m : Model> m.satisfy_set(just.0) ==> m.satisfies((just.1, just.2))) &&
//       exists<i : _> tgt.0.0 == self.0.0.push((Assign::Justified(just.0, just.1, just.2), i))
//     } }
//   }

//   // Γ ⟶ unsat, if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L}) = 0
//   #[predicate]
//   #[requires((self.0).invariant())]
//   #[requires(self.sound())]
//   #[ensures(result ==> (tgt.0).invariant())]
//   #[ensures(result ==> tgt.sound())]
//   fn fail(self, just: (Set<(Term, Value)>, Term, Value), tgt: Self) -> bool {
//     pearlite! { {
//       let not_l = (just.1, just.2.negate());
//       (forall<j : _> just.0.contains(j) ==> self.0.contains(j) ) &&
//       !self.0.contains((just.1, just.2)) &&
//       (forall<m : Model> m.satisfy_set(just.0) ==> m.satisfies((just.1, just.2))) &&
//       self.0.contains(not_l) &&
//       self.0.level(not_l) == 0 && self.0.is_set_level(just.0, 0)
//     } }
//   }

//   // just : J |- L
//   // Γ ⟶ ⟨ Γ; J ∪ {¬ L} ⟩ if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L }) > 0
//   #[predicate]
//   #[requires((self.0).invariant())]
//   #[requires(self.sound())]
//   #[ensures(result ==> (tgt.0).invariant())]
//   #[ensures(result ==> tgt.sound())]
//   fn conflict_solve(self, just: (Set<(Term, Value)>, Term, Value), tgt: Conflict) -> bool {
//     pearlite! { {
//       let not_l = (just.1, just.2.negate());
//       let conflict = just.0.insert(not_l);
//       self.0.contains(not_l) &&
//       (forall<j : _> just.0.contains(j) ==> self.0.contains(j) ) &&
//       !self.0.contains((just.1, just.2)) &&
//       (forall<m : Model> m.satisfy_set(just.0) ==> m.satisfies((just.1, just.2))) &&

//       exists<l : Int> l > 0 && self.0.is_set_level(conflict, l) &&
//       tgt == Conflict(self.0, conflict, l)
//     } }
//   }
// }

// struct Conflict(Trail, Set<(Term, Value)>, Int);

// impl Conflict {
//   #[predicate]
//   fn invariant(self) -> bool {
//     pearlite! { self.0.is_set_level(self.1, self.2) && self.0.invariant() }
//   }

//   #[predicate]
//   #[why3::attr="inline:trivial"]
//   fn sound(self) -> bool {
//     pearlite! { self.0.sound() && (forall<m : Model> m.satisfy_set(self.1) ==> false) }
//   }

//   // ⟨ Γ; { A } ⊔ E ⟩  ⇒ ⟨ Γ; E ∪ H ⟩ if H ⊢ A in Γ and H does not contain first-order decision A' with level_Γ(E ⊔ {A})
//   #[predicate]
//   #[requires(self.invariant())]
//   #[requires(tgt.invariant())]
//   #[requires(self.sound())]
//   #[ensures(result ==> tgt.0.invariant())]
//   #[ensures(result ==> tgt.sound())]
//   fn resolve(self, a: (Term, Value), tgt: Self) -> bool {
//     pearlite! { {
//       let just = self.0.justification(a);
//       self.0.is_justified(a) &&
//       (forall<a : _> just.contains(a) && !a.1.is_bool() ==> self.0.level(a) < self.2 ) &&
//       self.1.contains(a) && tgt == Conflict(self.0, self.1.remove(a).union(just), self.2)
//     } }
//   }

//   // ⟨ Γ; { L } ⊔ E ⟩  ⇒ Γ≤m, E⊢¬L, if level_\Gamma(L) > m, where m = level_\Gamma(E)
//   #[predicate]
//   #[requires(self.invariant())]
//   #[requires(self.sound())]
//   #[ensures(result ==> tgt.0.invariant())]
//   #[ensures(result ==> tgt.sound())]
//   fn backjump(self, l : (Term, Value), tgt: Normal) -> bool {
//     pearlite! { {
//       let e = self.1.remove(l);
//       self.1.contains(l) && l.1.is_bool() &&
//       self.0.level(l) > self.2 &&
//       exists<i : Int> self.0.is_set_level(e, i) && tgt.0.0 == self.0.restrict(self.2).0.push((Assign::Justified(e, l.0, l.1.negate()), i))
//     } }
//   }

//   // ⟨ Γ; { A } ⊔ E ⟩  ⇒ Γ≤m-1, if A is a first-order decision of level m > level_\Gamma(E)
//   #[predicate]
//   #[requires(self.invariant())]
//   #[requires(self.sound())]
//   #[ensures(result ==> tgt.0.invariant())]
//   #[ensures(result ==> tgt.sound())]
//   fn undo_clear(self, a : (Term, Value), tgt: Normal) -> bool {
//     pearlite! { {
//       let _ = self.0.restrict_sound(self.2 - 1);
//       let e = self.1.remove(a);
//       self.1.contains(a) && !a.1.is_bool() && (exists<l : _> self.2 > l && self.0.is_set_level(e, l)) &&
//       tgt.0 == self.0.restrict(self.2 - 1)
//     } }
//   }

//   // ⟨ Γ; { L } ⊔ E ⟩  ⇒ Γ≤m-1,?¬L
//   #[predicate]
//   #[requires(self.invariant())]
//   #[requires(self.sound())]
//   #[ensures(result ==> tgt.0.invariant())]
//   #[ensures(result ==> tgt.sound())]
//   fn undo_decide(self, l : (Term, Value), tgt: Normal) -> bool {
//     pearlite! { {
//       let _ = self.0.restrict_sound(self.2 - 1);

//       let just = self.0.justification(l);
//       let e = self.1.remove(l);
//       self.0.is_justified(l) &&
//       (exists<a : _> just.contains(a) && !a.1.is_bool() && self.0.level(a) == self.2 ) &&
//       self.2 == self.0.level(l) &&  tgt.0 == self.0.restrict(self.2 - 1).push_decision((l.0, l.1.negate()))
//     } }
//   }
// }
fn main() {}
