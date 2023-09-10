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

    impl Term {
        fn var(ix: usize, sort: Sort) -> Self {
            Term::Variable(ix, sort)
        }

        fn val(v: Value) -> Self {
            Term::Value(v)
        }

        fn plus(a: Self, b: Self) -> Self {
            Term::Plus(Box::new(a), Box::new(b))
        }
    }

    impl Value {
        fn rat(a: i64, b: i64) -> Self {
            Value::Rat(Rational64::new(a, b))
        }
    }
    use num_rational::Rational64;

    use crate::concrete::Solver;
    use crate::trail::{Term, Trail, Value};

    use crate::{concrete::Answer, trail::Sort};
    #[test]
    fn conjuction() {
        let mut trail = Trail::new(vec![(
            Term::Conj(
                Box::new(Term::Variable(0, Sort::Boolean)),
                Box::new(Term::Variable(1, Sort::Boolean)),
            ),
            Value::Bool(true),
        )]);

        let mut solver = Solver::new();

        let res = solver.solver(&mut trail);

        assert!(matches!(res, Answer::Sat));
    }

    #[test]
    fn a_not_a() {
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

    #[test]
    fn a_lt_b() {
        let mut trail = Trail::new(vec![
            (Term::var(0, Sort::Rational), Value::rat(5, 1)),
            (Term::var(1, Sort::Rational), Value::rat(10, 1)),
            (
                Term::Lt(
                    Box::new(Term::var(0, Sort::Rational)),
                    Box::new(Term::var(1, Sort::Rational)),
                ),
                Value::Bool(true),
            ),
        ]);

        let mut solver = Solver::new();

        let res = solver.solver(&mut trail);

        assert!(matches!(res, Answer::Sat));
    }

    #[test]
    fn x_plus_5_lt_10() {
        let mut trail = Trail::new(vec![(
            Term::Lt(
                Box::new(Term::plus(
                    Term::var(0, Sort::Rational),
                    Term::val(Value::rat(5, 1)),
                )),
                Box::new(Term::val(Value::rat(10, 1))),
            ),
            Value::Bool(true),
        )]);

        let mut solver = Solver::new();

        let res = solver.solver(&mut trail);

        assert!(matches!(res, Answer::Sat));
    }
}
