use std::collections::BTreeSet;

use crate::name::ResolvedName;
use crate::utils::display_iter;
use crate::{ast, log};

mod error;
pub use error::Error;

/// Resolves dependencies of definitions in the given module,
/// and returns a [`GenerationOrder`] representing the topological order of definitions,
/// such that:
///   - if generated in the order given,
///     definitions in the module will not cause any Lua errors;
///   - the [`GenerationOrder`] contains the [`ResolvedName`]s of all definitions in the module.
///
/// This function is implemented as a depth-first search.
/// See
/// [this wikipedia article](https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search)
/// for more details.
pub fn resolve<Ty>(module: &ast::Module<ResolvedName, Ty>) -> Result<GenerationOrder, Error> {
    let mut visitor = Visitor {
        module,
        finished: BTreeSet::new(),
        visited: BTreeSet::new(),
        ordered: Vec::new(),
    };

    for name in module.definitions.keys() {
        visitor.visit(*name)?;
    }

    log::trace!(
        log::RESOLVE,
        "Resolved dependencies for module {path}: {order:?}",
        path = module.path,
        order = visitor.ordered
    );

    Ok(GenerationOrder(visitor.ordered))
}

/// `GenerationOrder` represents an ordering of definitions in a module,
/// such that:
///   - if generated in the order given,
///     definitions in the module will not cause any Lua errors;
///   - the `GenerationOrder` contains the [`ResolvedName`]s of all definitions in the module.
#[derive(Debug)]
pub struct GenerationOrder(Vec<ResolvedName>);

impl IntoIterator for GenerationOrder {
    type Item = ResolvedName;

    type IntoIter = <Vec<ResolvedName> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// Used to keep track of which names have been visited during the depth-first-search.
#[derive(Debug)]
struct Visitor<'m, Ty> {
    /// Names which have been searched completely.
    finished: BTreeSet<ResolvedName>,

    /// Names which have been visited on this iteration of the main search loop.
    /// If a name is visited twice, that indicates a cycle.
    visited: BTreeSet<ResolvedName>,

    /// The order which is returned from [`resolve`],
    /// built up during the search.
    ordered: Vec<ResolvedName>,

    /// The module being resolved.
    module: &'m ast::Module<ResolvedName, Ty>,
}

impl<'m, Ty> Visitor<'m, Ty> {
    fn visit(&mut self, name: ResolvedName) -> Result<(), Error> {
        // If we've searched this branch already, we're done.
        if self.finished.contains(&name) {
            return Ok(());
        }

        // If we've visited this node already,
        // this is a cycle.
        // This is fine if the names will all be compiled into Lua functions,
        // but otherwise it's not allowed.
        if self.visited.contains(&name) {
            log::trace!(
                log::RESOLVE,
                "Found a dependency cycle: {}",
                display_iter(self.visited.iter())
            );
            // Find the smallest cycle by walking the cycle starting from this name.
            let mut minimal_cycle = BTreeSet::new();
            self.walk_cycle(&mut minimal_cycle, name);
            log::trace!(
                log::RESOLVE,
                "Found minimal dependency cycle: {}",
                display_iter(minimal_cycle.iter())
            );

            // Check if all the names define Lua functions.
            // @Lazy @Laziness: lazy values are okay too

            // Keep track of whether one of the names in the cycle has an explicit type.
            let mut any_explicit_type = false;

            for name in minimal_cycle.iter() {
                if let Some(defn) = self.module.definitions.get(name) {
                    // If the name has no arguments...
                    if defn.assignments[0].0.arg_count() == 0 {
                        // then it's an error.
                        return Err(Error::CyclicDependency(minimal_cycle));
                    }

                    any_explicit_type = defn.explicit_type.is_some() || any_explicit_type;
                }
            }

            // At least one of the functions has to have an explicit type,
            // otherwise we'll diverge in typechecking.
            //
            // @Note @Fixme: This is actually too restrictive.
            // It disallows functions like:
            //      foo 1 = True;
            //      foo x = bar (x-1);
            //
            //      bar 1 = False;
            //      bar x = foo (x-1);
            // It's clear that the type of both `foo` and `bar` is `Int -> Bool`;
            // yet this check rejects the mutual recursion.
            //
            // To allow the above definitions,
            // we might have to do some extra check during typechecking,
            // so that an unconditionally-recursive function
            // is given type `Void` or something similar.
            // This will actually make this case not an error at all.
            if !any_explicit_type {
                return Err(Error::CyclicDependencyWithoutExplicitType(minimal_cycle));
            }

            // If we're down here,
            // all the names are functions,
            // and so are okay to be generated in any order.
        } else {
            // If we're in here, we need to keep searching.
            self.visited.insert(name);

            // If the name is defined as a definition in this module...
            if let Some(defn) = self.module.definitions.get(&name) {
                // then recurse onto its dependencies.
                for dep in defn.dependencies() {
                    self.visit(dep)?;
                }
            }
        }

        self.visited.remove(&name);
        self.ordered.push(name);
        Ok(())
    }

    fn walk_cycle(&self, cycle: &mut BTreeSet<ResolvedName>, name: ResolvedName) {
        if cycle.contains(&name) {
            return;
        }

        if let Some(defn) = self.module.definitions.get(&name) {
            cycle.insert(name);
            for dep in defn.dependencies() {
                self.walk_cycle(cycle, dep);
            }
        }
    }
}

impl<Ty> ast::Definition<ResolvedName, Ty> {
    /// Returns a set of all the dependencies of the given definition.
    fn dependencies(&self) -> BTreeSet<ResolvedName> {
        let mut deps = BTreeSet::new();

        for (_lhs, expr) in self.assignments.iter() {
            expr.dependencies(&mut deps);
        }

        deps
    }
}

impl ast::Expr<ResolvedName> {
    /// Returns a set of all the dependencies of the given expression.
    fn dependencies(&self, deps: &mut BTreeSet<ResolvedName>) {
        use ast::*;
        match self {
            Expr::Term(Term::List(es)) | Expr::Term(Term::Tuple(es)) => {
                es.iter().for_each(|e| e.dependencies(deps));
            }
            Expr::Term(Term::Name(name)) => {
                deps.insert(*name);
            }
            Expr::Term(Term::Parens(e)) => e.dependencies(deps),
            Expr::Term(_) => (),

            Expr::App { func, argument } => {
                func.dependencies(deps);
                argument.dependencies(deps);
            }

            Expr::Binop { operator, lhs, rhs } => {
                deps.insert(*operator);
                lhs.dependencies(deps);
                rhs.dependencies(deps);
            }

            Expr::Let {
                definitions,
                in_expr,
            } => {
                let mut sub_deps = BTreeSet::new();

                in_expr.dependencies(&mut sub_deps);

                // Remove variables bound in the definitions
                for name in definitions.keys() {
                    // @Note: if .remove() returns false,
                    // the definition isn't referenced in the in_expr;
                    // therefore it's dead code.
                    // Maybe emit a warning about this.
                    sub_deps.remove(name);
                }

                deps.extend(sub_deps);
            }

            Expr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.dependencies(deps);
                then_expr.dependencies(deps);
                else_expr.dependencies(deps);
            }

            Expr::Case { expr, arms } => {
                // Always include the dependencies of the scrutinised expression.
                expr.dependencies(deps);

                for (arm_pat, arm_expr) in arms {
                    let mut sub_deps = BTreeSet::new();
                    arm_expr.dependencies(&mut sub_deps);

                    // Remove variables bound in the arm pattern
                    for name in arm_pat.names_bound() {
                        sub_deps.remove(&name);
                    }

                    deps.extend(sub_deps);
                }
            }

            Expr::Lambda { args, rhs } => {
                let mut sub_deps = BTreeSet::new();

                rhs.dependencies(&mut sub_deps);

                // Remove variables bound in the lambda LHS
                for pat in args.iter() {
                    for name in pat.names_bound() {
                        // @Note: if .remove() returns false,
                        // the definition isn't referenced in the in_expr;
                        // therefore it's dead code.
                        // Maybe emit a warning about this.
                        sub_deps.remove(&name);
                    }
                }

                deps.extend(sub_deps);
            }

            // Lua inline expressions can't depend on Huck values,
            // or at least we can't (i.e. won't) check inside Lua for dependencies;
            // so we do nothing.
            Expr::Lua(_) | Expr::UnsafeLua(_) => (),
        }
    }
}
