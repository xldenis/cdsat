// use std::{path, process::Command};
fn main() {}
// use quote::ToTokens;
// use syn::{visit::Visit, visit_mut::VisitMut, *};
// use
// fn main() -> std::io::Result<()> {
//     println!("cargo:rerun-if-changed=src/");
//     println!("cargo:rerun-if-changed=build.rs");
//     // Parse all files in the `src/**.rs` directory recursively using `syn`, and dump their contents into the `out/` directory.
//     let walker = walkdir::WalkDir::new("src");
//     for entry in walker {
//         let entry = entry.unwrap();
//         let path = entry.path();
//         if path.is_file() && path.extension().map(|e| e == "rs").unwrap_or(false) {
//             let contents = std::fs::read_to_string(path).unwrap();
//             let mut ast = parse_file(&contents).unwrap();
//             strip_file(&mut ast);
//             // Output to the same path but inside of `out/` instead of `src/`

//             let out_path = path::Path::new("stripped/").join(path.strip_prefix("src/").unwrap());
//             // Pretty print the ast to `out_path` creating the path if necessary
//             std::fs::create_dir_all(out_path.parent().unwrap()).unwrap();

//             // Pretty print using `syn` to_tokens
//             std::fs::File::create(&out_path)?;

//             std::fs::write(&out_path, format!("{}", ast.to_token_stream())).unwrap();

//             Command::new("rustfmt").arg(&out_path).spawn()?.wait()?;
//         }
//     }
//     Ok(())
// }

// struct Strip;

// fn spec_attribute(attr: &Attribute) -> bool {
//     attr.path().is_ident("variant")
//         || attr.path().is_ident("requires")
//         || attr.path().is_ident("ensures")
//         || attr.path().is_ident("trusted")
//         || attr.path().is_ident("maintains")
// }

// fn loop_attribute(attr: &Attribute) -> bool {
//     attr.path().is_ident("variant") || attr.path().is_ident("invariant")
// }

// impl VisitMut for Strip {
//     fn visit_item_fn_mut(&mut self, i: &mut ItemFn) {
//         i.attrs.retain(|attr| !spec_attribute(attr));

//         visit_mut::visit_item_fn_mut(self, i);
//     }

//     fn visit_impl_item_fn_mut(&mut self, i: &mut ImplItemFn) {
//         i.attrs.retain(|attr| !spec_attribute(attr));

//         visit_mut::visit_impl_item_fn_mut(self, i);
//     }

//     fn visit_file_mut(&mut self, i: &mut File) {
//         i.items.retain_mut(|item| match item {
//             Item::Fn(f) => !f
//                 .attrs
//                 .iter()
//                 .any(|attr| attr.path().is_ident("predicate") || attr.path().is_ident("logic")),
//             _ => true,
//         });
//         visit_mut::visit_file_mut(self, i)
//     }

//     fn visit_item_impl_mut(&mut self, i: &mut ItemImpl) {
//         i.items.retain_mut(|item| match item {
//             ImplItem::Fn(f) => !f
//                 .attrs
//                 .iter()
//                 .any(|attr| attr.path().is_ident("predicate") || attr.path().is_ident("logic")),
//             _ => true,
//         });
//         visit_mut::visit_item_impl_mut(self, i)
//     }

//     fn visit_expr_while_mut(&mut self, i: &mut ExprWhile) {
//         i.attrs.retain(|attr| !loop_attribute(attr));

//         visit_mut::visit_expr_while_mut(self, i);
//     }

//     fn visit_expr_for_loop_mut(&mut self, i: &mut ExprForLoop) {
//         i.attrs.retain(|attr| !loop_attribute(attr));

//         visit_mut::visit_expr_for_loop_mut(self, i);
//     }

//     fn visit_expr_loop_mut(&mut self, i: &mut ExprLoop) {
//         i.attrs.retain(|attr| !loop_attribute(attr));

//         visit_mut::visit_expr_loop_mut(self, i);
//     }

//     fn visit_block_mut(&mut self, i: &mut Block) {
//         // strip out any calls to `proof_assert!`
//         // and any calls to `gh!` in assignments or variable declarations
//         i.stmts.retain_mut(|stmt| match stmt {
//             Stmt::Expr(expr, _) => match expr {
//                 Expr::Assign(a) => {
//                     if let Expr::Macro(mac) = &*a.right {
//                         !mac.mac.path.is_ident("gh")
//                     } else {
//                         true
//                     }
//                 }
//                 _ => true,
//             },
//             Stmt::Local(l) => {
//                 if let Some(init) = &mut l.init {
//                     if let Expr::Macro(mac) = &*init.expr {
//                         !mac.mac.path.is_ident("gh")
//                     } else {
//                         true
//                     }
//                 } else {
//                     true
//                 }
//             }
//             Stmt::Macro(mac) => !mac.mac.path.is_ident("proof_assert"),
//             _ => true,
//         });

//         visit_mut::visit_block_mut(self, i);
//     }
// }

// fn strip_file(f: &mut File) {
//     // Remove any items that have the `#[predicate]` or `#[ghost]`  attribute
//     Strip.visit_file_mut(f)
// }
