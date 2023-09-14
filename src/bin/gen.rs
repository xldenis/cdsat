// use clap::Parser;
// use rand::{distributions::Uniform, prelude::Distribution, *};
fn main() { }
// #[derive(PartialEq, Eq, Clone, Copy, Debug)]
// enum Sort {
//     Bool,
//     Real,
// }

// struct Generator {
//     real_vars: usize,
//     bool_vars: usize,
// }

// #[derive(Parser, Debug)]
// struct Args {
//     #[arg(long, default_value_t = 10)]
//     max_bool: usize,
//     #[arg(long, default_value_t = 10)]
//     max_real: usize,
//     #[arg(long, default_value_t = 10)]
//     num_constraints: usize,
//     #[arg(long, default_value_t = 10)]
//     max_depth: usize,
// }

// // Generate an SMTLIB term of up to the given depth and sort
// // The allowed operators are `and`, `or`, `=`, `<`, and `plus`.
// // Variables are named x0, x1, ..., xn, their sort is stored at the corresponding index in the vector `vars`
// fn generate_term(vars: &Generator, depth: usize, sort: Sort) -> String {
//     let mut rng = thread_rng();
//     if depth == 0 {
//         if rng.gen()
//             && ((sort == Sort::Bool && vars.bool_vars > 0)
//                 || (sort == Sort::Real && vars.real_vars > 0))
//         {
//             generate_var(vars, sort)
//         } else {
//             generate_const(sort)
//         }
//     } else {
//         if sort == Sort::Bool {
//             // Pick a random number from the range 0, 6 which
//             let op = rng.gen_range(2..6);

//             match op {
//                 2 => {
//                     if vars.bool_vars == 0 {
//                         return generate_term(vars, depth, sort);
//                     }
//                     let subterm1 = generate_term(vars, rng.gen_range(0..depth), sort);
//                     let subterm2 = generate_term(vars, rng.gen_range(0..depth), sort);
//                     format!("(and {} {})", subterm1, subterm2)
//                 }
//                 3 => {
//                     if vars.bool_vars == 0 {
//                         return generate_term(vars, depth, sort);
//                     }
//                     let subterm1 = generate_term(vars, rng.gen_range(0..depth), sort);
//                     let subterm2 = generate_term(vars, rng.gen_range(0..depth), sort);
//                     format!("(or {} {})", subterm1, subterm2)
//                 }
//                 4 => {
//                     let sort1 =
//                         if rng.gen() || vars.real_vars == 0 { Sort::Bool } else { Sort::Real };
//                     // Create a `=` term with two subterms of the chosen sort
//                     let subterm1 = generate_term(vars, rng.gen_range(0..depth), sort1);
//                     let subterm2 = generate_term(vars, rng.gen_range(0..depth), sort1);
//                     format!("(= {} {})", subterm1, subterm2)
//                 }
//                 5 => {
//                     if vars.real_vars == 0 {
//                         return generate_term(vars, depth, sort);
//                     }
//                     let subterm1 = generate_term(vars, rng.gen_range(0..depth), Sort::Real);
//                     let subterm2 = generate_term(vars, rng.gen_range(0..depth), Sort::Real);
//                     format!("(< {} {})", subterm1, subterm2)
//                 }
//                 _ => panic!("Invalid operator"),
//             }
//         } else {
//             // pick a random number op
//             // if op = 0, pick a random real variable
//             // if op = 1, pick a random real constant
//             // if op = 2, create a `plus` term with two subterms of real sort

//             let op = rng.gen_range(0..3);
//             match op {
//                 0 => generate_var(vars, sort),
//                 1 => generate_const(sort),
//                 2 => {
//                     let subterm1 = generate_term(vars, rng.gen_range(0..depth), sort);
//                     let subterm2 = generate_term(vars, rng.gen_range(0..depth), sort);
//                     format!("(+ {} {})", subterm1, subterm2)
//                 }
//                 _ => panic!("Invalid operator"),
//             }
//         }
//     }
// }

// fn generate_var(vars: &Generator, sort: Sort) -> String {
//     let mut rng = thread_rng();

//     match sort {
//         Sort::Bool => format!("x{}", rng.gen_range(0..vars.bool_vars)),
//         Sort::Real => format!("y{}", rng.gen_range(0..vars.real_vars)),
//     }
// }

// fn generate_const(sort: Sort) -> String {
//     let mut rng = thread_rng();
//     if sort == Sort::Bool {
//         if rng.gen() {
//             "true".to_string()
//         } else {
//             "false".to_string()
//         }
//     } else {
//         rng.gen_range(0..100).to_string()
//     }
// }

// fn main() {
//     let args = Args::parse();
//     // Generate random SMTLIB instances from QF_LRA
//     // It should use NUM_VARS variables which are either boolean or real
//     // It should generate NUM_CONSTRAINTS assert commands
//     let mut rng = thread_rng();

//     let bool_vars = if args.max_bool > 0 { rng.gen_range(0..args.max_bool) } else { 0 };
//     let real_vars = if args.max_real > 0 { rng.gen_range(0..args.max_real) } else { 0 };

//     // Generate variables
//     for i in 0..bool_vars {
//         let _ = Sort::Bool;
//         println!("(declare-const x{} Bool)", i,);
//     }

//     for i in 0..real_vars {
//         let _ = Sort::Real;
//         println!("(declare-const y{} Real)", i,);
//     }

//     // Generate constraints using the function `generate_term`

//     let gen = Generator { real_vars, bool_vars };
//     let dist = Uniform::new(0, args.max_depth);
//     for _ in 0..args.num_constraints {
//         let depth = dist.sample(&mut rng);
//         let term = generate_term(&gen, depth, Sort::Bool);
//         if term == "false" {
//             continue;
//         };
//         println!("(assert {})", term);
//     }

//     println!("(check-sat)");
// }
