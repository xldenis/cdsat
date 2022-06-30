use crate::trail::*;

pub struct Solver {
    bool_th: BoolTheory,
}

impl Solver {
    pub fn solver(self, trail: &mut Trail) -> Answer {
        loop {
        	// Tracks if all theories are satisfied with the trail.
        	let mut satisfied = (false, false);
            loop {
            	// If a theory makes progress we reset the satisfaction
                match self.bool_th.extend(trail) {
                    ExtendResult::Deduction => satisfied = (false, false),
                    ExtendResult::Satisfied => satisfied.0 = true,
                    ExtendResult::Conflict(c) => self.resolve_conflict(trail, c),
                }
                break
            }

            // If after propagation every theory was satisfied then we have a model
            if satisfied == (true, true) {
            	return Answer::Sat;
            }

            // Make a decision
            self.bool_th.decide(trail);
        }
    }

    pub fn resolve_conflict(self, trail: &mut Trail, conflict: Vec<(Term, Value)>) {

    }
}

pub enum Answer {
    Sat,
    Unsat,
    Unknown,
}

enum ExtendResult {
    Conflict(Vec<(Term, Value)>),
    Deduction,
    Satisfied,
    Saturated,
}

struct BoolTheory;

impl BoolTheory {
    // Extend the trail with 1 or more deductions, or backtrack to a non-conflicting state
    // Returns `Fail` if we encounter a conflict at level 0
    // Return Satisfied if the trail is satisfactory to us
    fn extend(&self, tl: &mut Trail) -> ExtendResult {
        let i = 0;

        let mut res = ExtendResult::Satisfied;
        while i < tl.len() {
        	if tl[i].is_bool() {

        	}
        }

        res
    }

    fn decide(&self, tl: &mut Trail) {

    }
}
