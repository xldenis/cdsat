#![cfg_attr(not(creusot), feature(register_tool), register_tool(creusot))]
#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]
#![feature(min_specialization)]
#![allow(dead_code, unused_variables)]
#![feature(never_type, let_chains, btree_cursors)]
#![allow(unused_imports)]

pub mod bool;
pub mod concrete;
pub(crate) mod heap;
pub mod log;

#[macro_use]
pub mod ghost;

#[cfg(not(creusot))]
pub mod lra;

pub mod trail;

#[cfg(creusot)]
pub mod lra {
    pub struct LRATheory;

    use crate::{concrete::ExtendResult, trail::Trail};
    use creusot_contracts::*;

    impl LRATheory {
        #[trusted]
        #[maintains((mut tl).invariant())]
        #[ensures(match result {
            ExtendResult::Satisfied => true,
            ExtendResult::Decision(t, v) => (^tl).ghost.acceptable(t@, v@) && t@.well_sorted(),
            ExtendResult::Conflict(c) => {
                let conflict = (^tl).abstract_justification(c@);
                c@.len() > 0 &&
                // members of conflict area within the trail
                (forall<t : _> (c@).contains(t) ==> (^tl).contains(t)) &&
                // (forall<i : _> 0 <= i && i < (c@).len() ==> @(c@)[i] < (@(^tl).assignments).len()) &&
                (forall<m : crate::theory::Model> m.satisfy_set(conflict) ==> false)
            }
        })]
        #[ensures(tl.ghost.impls(*(^tl).ghost))]
        pub fn extend(&mut self, tl: &mut Trail) -> ExtendResult {
            todo!()
        }
    }
}

#[cfg(creusot)]
pub mod theory;

#[cfg(creusot)]
pub mod bag;

pub mod term;

#[cfg(not(creusot))]
pub mod theory {
    pub struct Sort;
    pub struct Assign;
    pub struct Trail;
    pub struct Conflict;
    pub struct Term;
    pub struct Value;
}

use std::{env::args, fs::File, io::BufReader, unimplemented};

use concrete::Solver;
use indexmap::IndexMap;
use num_rational::BigRational;
use smt2parser::{
    concrete::{Command, Symbol, SyntaxBuilder},
    visitors::*,
    CommandStream,
};
use term::{Sort, Term, Value};
use trail::Trail;

struct TermBuilder;

#[creusot_contracts::trusted]
fn term_to_term(vars: &IndexMap<Symbol, Sort>, t: smt2parser::concrete::Term) -> Term {
    use smt2parser::concrete::{QualIdentifier, Term as PT};
    match t {
        PT::Application { qual_identifier, arguments } => {
            let mut arguments =
                arguments.into_iter().map(|a| term_to_term(vars, a)).collect::<Vec<_>>();
            let ident = match qual_identifier {
                QualIdentifier::Simple { identifier } => identifier,
                QualIdentifier::Sorted { identifier, .. } => identifier,
            };
            let ident = match ident {
                Identifier::Simple { symbol: Symbol(st) } => st,
                _ => unimplemented!(),
            };

            let t = match &ident[..] {
                "+" => Term::plus(arguments.remove(0), arguments.remove(0)),
                "and" => Term::and(arguments.remove(0), arguments.remove(0)),
                "or" => Term::or(arguments.remove(0), arguments.remove(0)),
                "<" => Term::lt(arguments.remove(0), arguments.remove(0)),
                "=" => Term::eq_(arguments.remove(0), arguments.remove(0)),
                "*" => {
                    let Term::Value(Value::Rat(k)) = arguments.remove(0) else {panic!()};

                    Term::times(k.to_integer().try_into().unwrap(), arguments.remove(0))
                }
                "-" => {
                    if arguments.len() == 1 {
                        Term::times(BigRational::from_integer((-1).into()), arguments.remove(0))
                    } else {
                        Term::plus(
                            arguments.remove(0),
                            Term::times(
                                BigRational::from_integer((-1).into()),
                                arguments.remove(0),
                            ),
                        )
                    }
                }
                ">=" => Term::geq(arguments.remove(0), arguments.remove(0)),
                "<=" => Term::leq(arguments.remove(0), arguments.remove(0)),
                "not" => Term::not(arguments.remove(0)),
                s => unimplemented!("{s}"),
            };
            t
        }
        PT::Constant(c) => match c {
            smt2parser::concrete::Constant::Decimal(br) => Term::Value(Value::Rat(br)),
            smt2parser::concrete::Constant::Numeral(num) => {
                Term::Value(Value::Rat(BigRational::new(num.into(), 1.into())))
            }
            _ => unimplemented!(),
        },
        PT::QualIdentifier(qi) => {
            if qi.to_string() == "true" {
                Term::val(Value::true_())
            } else if qi.to_string() == "false" {
                Term::val(Value::Bool(false))
            } else {
                match qi {
                    QualIdentifier::Simple { identifier }
                    | QualIdentifier::Sorted { identifier, .. } => match identifier {
                        Identifier::Simple { symbol } | Identifier::Indexed { symbol, .. } => {
                            let pos = vars.get_index_of(&symbol).unwrap();
                            let sort = vars[&symbol].clone();
                            Term::var(pos, sort)
                        }
                    },
                }
            }
        }

        PT::Let { var_bindings, term } => unimplemented!("let"),
        PT::Forall { vars, term } => unimplemented!("quantifier"),
        PT::Exists { vars, term } => unimplemented!("quantifier"),
        PT::Match { term, cases } => unimplemented!("match"),
        PT::Attributes { term, attributes } => unimplemented!("attributes"),
    }
}

#[creusot_contracts::trusted]
fn to_assign(vars: &mut IndexMap<Symbol, Sort>, c: Command) -> Option<(Term, Value)> {
    match c {
        Command::Assert { term } => Some((term_to_term(vars, term), Value::true_())),
        Command::CheckSat => None,
        Command::SetLogic { symbol } => {
            if symbol.0 != "QF_LRA" {
                unimplemented!()
            } else {
                None
            }
        }
        Command::SetInfo { keyword, value } => unimplemented!(),
        Command::SetOption { keyword, value } => unimplemented!(),
        Command::DeclareConst { symbol, sort } => {
            if !vars.contains_key(&symbol) {
                let s = match sort {
                    smt2parser::concrete::Sort::Simple { identifier } => {
                        if identifier.to_string() == "Bool" {
                            Sort::Boolean
                        } else if identifier.to_string() == "Real" {
                            Sort::Rational
                        } else {
                            unimplemented!()
                        }
                    }
                    _ => unimplemented!(),
                };
                vars.insert(symbol, s);
            };
            None
        }
        Command::DeclareDatatype { symbol, datatype } => unimplemented!(),
        Command::DeclareDatatypes { datatypes } => unimplemented!(),
        Command::DeclareFun { symbol, parameters, sort } => unimplemented!(),
        Command::DeclareSort { symbol, arity } => unimplemented!(),
        Command::DefineFun { sig, term } => unimplemented!(),
        Command::DefineFunRec { sig, term } => unimplemented!(),
        Command::DefineFunsRec { funs } => unimplemented!(),
        Command::DefineSort { symbol, parameters, sort } => unimplemented!(),
        Command::Echo { message } => unimplemented!(),
        Command::Exit => unimplemented!(),
        Command::GetAssertions => unimplemented!(),
        Command::GetAssignment => unimplemented!(),
        Command::GetInfo { flag } => unimplemented!(),
        Command::GetModel => unimplemented!(),
        Command::GetOption { keyword } => unimplemented!(),
        Command::GetProof => unimplemented!(),
        Command::GetUnsatAssumptions => unimplemented!(),
        Command::GetUnsatCore => unimplemented!(),
        Command::GetValue { terms } => unimplemented!(),
        Command::Pop { level } => unimplemented!(),
        Command::Push { level } => unimplemented!(),
        Command::Reset => unimplemented!(),
        Command::ResetAssertions => unimplemented!(),
        Command::CheckSatAssuming { literals } => unimplemented!(),
    }
}

#[creusot_contracts::trusted]
fn main() -> std::io::Result<()> {
    env_logger::init();
    let mut input = BufReader::new(File::open(args().nth(1).expect("provide an input file"))?);
    let stream = CommandStream::new(&mut input, SyntaxBuilder, None);

    let commands = stream.collect::<Result<Vec<_>, _>>().expect("could not parse");

    let mut vars = IndexMap::new();
    let assignments =
        commands.into_iter().filter_map(|c| to_assign(&mut vars, c)).collect::<Vec<_>>();

    let mut solver = Solver::new();

    let mut trail = Trail::new(assignments);
    let res = solver.solver(&mut trail);

    println!("Answer = {res:?}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use num_rational::Rational64;

    use crate::{
        concrete::Solver,
        trail::{Trail},
        term::{Term, Value}
    };

    use crate::{concrete::Answer, term::Sort};
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
                Box::new(Term::plus(Term::var(0, Sort::Rational), Term::val(Value::rat(5, 1)))),
                Box::new(Term::val(Value::rat(10, 1))),
            ),
            Value::Bool(true),
        )]);

        let mut solver = Solver::new();

        let res = solver.solver(&mut trail);

        assert!(matches!(res, Answer::Sat));
    }
}
