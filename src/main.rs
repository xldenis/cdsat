use creusot_contracts::*;

fn main() {}

struct Trail(Seq<Asgn>);
struct Term;

impl Term {
    #[logic]
    fn is_boolean(self) -> bool {
        false
    }

    #[logic]
    fn negate(self) -> Self {
        self
    }
}

enum Asgn {
    // ⊢?_k A
    Decision(ThIdx, (Term, Term)),
    // H ⊢_k A
    // The set of integers represents the set of assignment indices in the trail which justify this assignment
    // TODO: Should this be a set of assignments instead?
    Justified(Set<Int>, ThIdx, (Term, Term)),
}

impl Asgn {
    #[predicate]
    fn is_decision(self) -> bool {
        match self {
            Asgn::Decision(_, _,) => true,
            Asgn::Justified(_, _, _,) => false,
        }
    }

    #[logic]
    fn th_idx(self) -> ThIdx {
        match self {
            Asgn::Decision(i, _) => i,
            Asgn::Justified(_, i, _) => i,
        }
    }
}

// A struct containing all the theories
struct Theories {
    bool_th: (),
    lia_th: (),
}

// The index `k` for `T_k` in the paper
enum ThIdx {
    Bool,
    Lia,
}

impl Trail {
    // The level of an assignment is:
    // 1. 1 + the number of previous decisions for decisions
    // 2: The maximum of the levels of the justification for justified asignments
    #[logic]
    fn level(self, a: Asgn) -> Int {
        match a {
            Asgn::Decision(_, _) => { 0 }
            Asgn::Justified(_, _, _) => { 0 }
        }
    }

    // A justification is valid if all the clauses are in the trail. 
    #[predicate]
    fn valid_justification(self, just: Set<Int>) -> bool {
        false
    }

    #[predicate]
    fn contains(self, dec: (Term, Term)) -> bool {
        false
    }
 }

impl Theories {
    #[predicate]
    fn acceptable(self, choice: Asgn) -> bool {
        match choice.th_idx() {
            ThIdx::Bool => false,
            ThIdx::Lia => false,
        }
    }

    // Γ ⟶ Γ,?A if A is an acceptable 𝒯ₖ-assignment for ℐₖ in Γ_𝒯ₖ for 1 ≤ k ≤ n
    #[predicate]
    fn decide(self, init: Trail, tgt: Trail, choice: Asgn) -> bool {
        pearlite! {
            choice.is_decision() && tgt == Trail(init.0.push(choice)) && self.acceptable(choice)
        }
    }

    // Γ ⟶ Γ, J⊢L, if  ¬ L ∉ Γ and L is l ← 𝔟 for l ∈ ℬ
    #[predicate]
    fn deduce(self, init: Trail, tgt: Trail, just: Set<Int>, th: ThIdx, a: (Term, Term)) -> bool {
        pearlite! {
            tgt == Trail(init.0.push(Asgn::Justified(just, th, a))) &&
            init.valid_justification(just) &&
            !init.contains(a) &&
            a.1.is_boolean() && !init.contains((a.0, a.1.negate()))
        }
    }

    // Γ ⟶ unsafe if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L }) - 0
    #[predicate]
    fn fail(self, init: Trail, just: Set<Int>, th: ThIdx, a: (Term, Term)) -> bool {
        pearlite! {
             a.1.is_boolean() &&
            (forall<i : _> just.contains(i) ==> (init.level(init.0[i]) == 0) ) &&
            (exists< i : _ > init.contains((a.0, a.1.negate())) && init.level(init.0[i]) == 0)
        }
    }

    // Γ ⟶ Γ' if ¬ L ∈ Γ and level_Γ(J ∪ {¬ L }) > 0, ⟨ Γ; J ∪ {¬ L} ⟩ ⟹^* Γ'
    #[predicate]
    fn conflict_solve(self, init: Trail, tgt: Trail, just: Set<Int>, th: ThIdx, a: (Term, Term)) -> bool {
        pearlite! {
            (exists<i : _> just.contains(i) && init.level(init.0[i]) > 0) ||
            (exists< i : _ > init.contains((a.0, a.1.negate())) && init.level(init.0[i]) == 0 &&
                self.resolve(init, just.insert(i), tgt)
            )
        }
    }

    // TODO
    #[predicate]
    fn resolve(self, init: Trail, conflict: Set<Int>, tgt: Trail) -> bool {
        false
    }
}
