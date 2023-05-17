#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]
#![allow(dead_code, unused_variables)]
pub mod concrete;
pub mod trail;

#[cfg(creusot)]
pub mod theory;

#[cfg(creusot)]
pub mod bag;

#[cfg(not(creusot))]
pub mod theory {
    pub struct Sort;
    pub struct Assign;
    pub struct Trail;
    pub struct Conflict;
    pub struct Term;
    pub struct Value;
}

use concrete::Solver;
use trail::{Term, Trail, Value};

use crate::{concrete::Answer, trail::Sort};

#[creusot_contracts::trusted]
fn main() {
    let mut trail = Trail::new(vec![(
        Term::Conj(
            Box::new(Term::Neg(Box::new(Term::Variable(0, Sort::Boolean)))),
            Box::new(Term::Variable(0, Sort::Boolean)),
        ),
        Value::Bool(true),
    )]);

    let mut solver = Solver::new();

    let res = solver.solver(&mut trail);

    assert!(matches!(res, Answer::Unsat));
}

#[cfg(test)]
mod tests {
    use crate::concrete::Solver;
    use crate::trail::{Term, Trail, Value};

    use crate::{concrete::Answer, trail::Sort};
    #[test]
    fn conjuction() {
        let mut trail = Trail::new(vec![
            (
                Term::Conj(
                    box Term::Variable(0, Sort::Boolean),
                    box Term::Variable(1, Sort::Boolean),
                ),
                Value::Bool(true),
            ),
        ]);

        let mut solver = Solver::new();

        let res = solver.solver(&mut trail);

        assert!(matches!(res, Answer::Sat));
    }

    #[test]
    fn a_not_a() {
        let mut trail = Trail::new(vec![
            (
                Term::Conj(
                    box Term::Neg(box Term::Variable(0, Sort::Boolean)),
                    box Term::Variable(0, Sort::Boolean),
                ),
                Value::Bool(true),
            ),
        ]);

        let mut solver = Solver::new();

        let res = solver.solver(&mut trail);

        assert!(matches!(res, Answer::Unsat));
    }
}
