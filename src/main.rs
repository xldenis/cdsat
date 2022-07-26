#![feature(box_syntax)]
#![feature(stmt_expr_attributes, proc_macro_hygiene)]
pub mod concrete;
pub mod trail;

#[cfg(feature = "contracts")]
pub mod theory;

#[cfg(not(feature = "contracts"))]
pub mod theory {
    pub struct Sort;
    pub struct Assign;
    pub struct Trail;
    pub struct Conflict;
    pub struct Term;
    pub struct Value;
}

// use concrete::Solver;
// use trail::{Term, Value, Trail};

// use crate::concrete::Answer;

fn main() {
    //     let mut trail = Trail::new(vec![(Term::Conj(box Term::Variable("A".into()), box Term::Variable("B".into())), Value::Bool(true))]);

    //     let mut solver = Solver::new();

    //     let res = solver.solver(&mut trail);

    //     assert!(matches!(res, Answer::Sat));
}
