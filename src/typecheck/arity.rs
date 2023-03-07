use std::collections::BTreeMap;
use std::mem;

use crate::ast::{self, Module};
use crate::log;
use crate::name::{ModulePath, ResolvedName, Source};
use crate::types::Type;

use super::Error;

#[derive(Debug, Default)]
pub(super) struct ArityChecker {
    /// All the currently assumed arities of type name uses.
    assumptions: BTreeMap<ResolvedName, Vec<usize>>,
}

impl ArityChecker {
    pub fn type_expr(&mut self, input: &ast::TypeExpr<ResolvedName>, assumed_arity: usize) {
        match input {
            ast::TypeExpr::Term(term) => self.type_term(term, assumed_arity),
            ast::TypeExpr::App(f, x) => {
                self.type_expr(f, assumed_arity + 1);
                self.type_expr(x, 0);
            }
            ast::TypeExpr::Arrow(a, b) => {
                self.type_expr(a, 0);
                self.type_expr(b, 0);
            }
        }
    }

    fn type_term(&mut self, input: &ast::TypeTerm<ResolvedName>, assumed_arity: usize) {
        match input {
            ast::TypeTerm::Var(name) | ast::TypeTerm::Concrete(name) => {
                self.assume_arity(*name, assumed_arity)
            }

            ast::TypeTerm::Unit => self.assume_arity(ResolvedName::builtin("()"), assumed_arity),

            ast::TypeTerm::Parens(expr) => self.type_expr(expr, assumed_arity),

            // The type in the list should have arity 0.
            ast::TypeTerm::Stream(expr) => self.type_expr(expr, 0),

            // Each of the types in the tuple should have arity 0.
            ast::TypeTerm::Tuple(exprs) => {
                for expr in exprs {
                    self.type_expr(expr, 0);
                }
            }
        }
    }

    fn assume_arity(&mut self, name: ResolvedName, arity: usize) {
        log::trace!(
            log::TYPECHECK,
            "    Assuming type name {} has arity {}",
            name,
            arity
        );
        self.assumptions
            .entry(name)
            .or_insert_with(|| Vec::with_capacity(1))
            .push(arity);
    }

    /// Checks all the assumptions are true within the given modules.
    pub fn finish(
        &mut self,
        modules: &BTreeMap<ModulePath, Module<ResolvedName, Type>>,
    ) -> Result<(), Error> {
        // Check that all the assumed arities match the arity from the type definitions.
        for (name, assumed_arities) in mem::take(&mut self.assumptions) {
            let actual_arity = match name.source {
                Source::Module(path) => modules[&path].type_definitions[&name].vars.len(),

                Source::Constructor(..) => unreachable!("constructors can't be used at type level"),

                Source::Local(_id) => {
                    // @Typeclasses: this code will need to change when implementing type classes

                    // Check that all the assumptions are for the same arity.
                    {
                        let mut iter = assumed_arities.iter();
                        // @Note: Safe unwrap:
                        // Whenever we add a Vec to the entry in arity_assumptions,
                        // we always push an element to the Vec straight afterwards.
                        // i.e., these Vecs are never empty.
                        let first = iter.next().unwrap();

                        let all_equal = iter.all(|x| x == first);

                        if !all_equal {
                            log::error!(
                                log::TYPECHECK,
                                "Not all uses of type variable {name} have the same arity!"
                            );
                            let mut arities = assumed_arities;
                            arities.sort();
                            arities.dedup();
                            return Err(Error::IncorrectArityTypeVariable(name, arities));
                        }
                    }

                    // Check that all the assumptions have arity of 0.
                    //
                    // @Typeclasses:
                    // Instead of checking that arity == 0,
                    // we'll have to check that the arity of the type variable (name)
                    // matches the definition of the type class.
                    // This will require a bunch more bookkeeping.
                    {
                        let all_zero = assumed_arities.iter().all(|x| x == &0);
                        if !all_zero {
                            // @Errors
                            log::error!(
                                log::TYPECHECK,
                                "Not all uses of type variable {name} have the arity 0!"
                            );
                            todo!()
                        }
                    }

                    continue;
                }

                // @Cleanup: we should never need to assume the arity of any builtin types,
                // so we should possibly change this whole match
                // into an if let Source::Module(path) = name.source
                Source::Builtin => match name.ident {
                    "Int" | "Float" | "String" | "Bool" | "()" => 0,
                    "IO" => 1,
                    _ => unreachable!("must have added new builtin types"),
                },

                // Type names can't come from foreign sources.
                Source::Foreign { .. } => unreachable!(),
            };

            log::trace!(
                log::TYPECHECK,
                "  Checking that all assumed arities of {name} matches the actual arity {actual_arity}"
            );

            for assumed_arity in assumed_arities {
                if assumed_arity != actual_arity {
                    return Err(Error::IncorrectArity(name, assumed_arity, actual_arity));
                }
            }
        }

        Ok(())
    }
}
