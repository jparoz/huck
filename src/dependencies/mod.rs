use std::collections::{BTreeMap, BTreeSet};

use crate::name::{ModulePath, ResolvedName, Source};
use crate::utils::display_iter;
use crate::{ast, log};

mod error;
pub use error::Error;

#[cfg(test)]
mod test;

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
pub fn resolve<Ty>(
    modules: &BTreeMap<ModulePath, ast::Module<ResolvedName, Ty>>,
) -> Result<BTreeMap<ModulePath, GenerationOrder>, Error> {
    log::trace!(log::RESOLVE, "Starting dependency resolution",);
    let mut resolver = Resolver {
        modules,
        finished: BTreeSet::new(),
        visited: Vec::new(),
        ordered: BTreeMap::new(),
    };

    for module in modules.values() {
        // Add an empty Vec to the map,
        // so that if the module is empty,
        // we give this module the empty order.
        resolver.ordered.entry(module.path).or_default();

        for name in module.definitions.keys() {
            resolver.visit(*name)?;
        }
    }

    log::trace!(
        log::RESOLVE,
        "Resolved all dependencies: {}",
        display_iter(resolver.ordered.values().flat_map(|x| x.0.iter()))
    );

    Ok(resolver.ordered)
}

/// `GenerationOrder` represents an ordering of definitions in a module,
/// such that:
///   - if generated in the order given,
///     definitions in the module will not cause any Lua errors;
///   - the `GenerationOrder` contains the [`ResolvedName`]s of all definitions in the module.
#[derive(Debug, Default)]
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
struct Resolver<'m, Ty> {
    /// Names which have been searched completely.
    finished: BTreeSet<ResolvedName>,

    /// Names which have been visited on this iteration of the main search loop.
    /// If a name is visited twice, that indicates a cycle.
    visited: Vec<ResolvedName>,

    /// The order which is returned from [`resolve`],
    /// built up during the search.
    ordered: BTreeMap<ModulePath, GenerationOrder>,

    /// The map of modules being resolved.
    modules: &'m BTreeMap<ModulePath, ast::Module<ResolvedName, Ty>>,
}

impl<'m, Ty> Resolver<'m, Ty> {
    fn visit(&mut self, name: ResolvedName) -> Result<(), Error> {
        log::trace!(log::RESOLVE, "  Visiting `{name}`");

        // We only want to visit definitions,
        // not type constructors and suchlike.
        if self.get_definition(&name).is_none() {
            log::trace!(log::RESOLVE, "    Dependency is not a definition: `{name}`");
            return Ok(());
        };

        // If we've searched this branch already, we're done.
        if self.finished.contains(&name) {
            log::trace!(
                log::RESOLVE,
                "    Already resolved dependencies for `{name}`"
            );
            return Ok(());
        }

        // If we've visited this node already,
        // this is a cycle.
        // This is fine if the names will all be compiled into Lua functions,
        // but otherwise it's not allowed.
        if self.visited.contains(&name) {
            log::trace!(
                log::RESOLVE,
                "    Found a dependency cycle within these names: {}",
                display_iter(self.visited.iter())
            );
            return self.resolve_cycle(name);
        }

        // If we're here, we need to keep searching.
        self.visited.push(name);

        // Recurse onto the definition's dependencies.
        if let Some(defn) = self.get_definition(&name) {
            for dep in defn.dependencies() {
                self.visit(dep)?;
            }
        }

        assert_eq!(self.visited.pop(), Some(name));

        log::trace!(log::RESOLVE, "    Finished visiting `{name}`");
        self.finished.insert(name);
        if let Source::Module(path) = name.source {
            self.ordered.entry(path).or_default().0.push(name);
        }

        Ok(())
    }

    fn resolve_cycle(&self, name: ResolvedName) -> Result<(), Error> {
        // self.visited contains a cycle,
        // and possibly some extra names which depend on the cycle.

        // Remove the names which depend on the cycle,
        // but are not part of the cycle.
        // @Note: safe unwrap: Before calling resolve_cycle,
        //        we detected that this name was in self.visited.
        let index = self.visited.iter().position(|n| n == &name).unwrap();
        let cycle = self.visited.split_at(index).1.to_vec();

        log::trace!(
            log::RESOLVE,
            "    Found minimal dependency cycle: {}",
            display_iter(cycle.iter())
        );

        // Check if all the names define Lua functions.
        // @Lazy @Laziness: lazy values are okay too

        for name in cycle.iter() {
            if let Source::Module(path) = name.source {
                if let Some(defn) = self
                    .modules
                    .get(&path)
                    .and_then(|module| module.definitions.get(name))
                {
                    // If the name has no arguments...
                    if defn.assignments[0].0.arg_count() == 0 {
                        // then it's an error.
                        return Err(Error::CyclicDependency(cycle));
                    }
                }
            }
        }

        // If we're down here,
        // all the names are functions,
        // and so are okay to be generated in any order.
        log::trace!(log::RESOLVE, "      Dependency cycle is okay to generate.");

        Ok(())
    }

    fn get_definition(&self, name: &ResolvedName) -> Option<&ast::Definition<ResolvedName, Ty>> {
        // If the name is defined as a definition in some module,
        if let Source::Module(path) = name.source {
            // Get the definition from the module.
            self.modules
                .get(&path)
                .and_then(|module| module.definitions.get(name))
        } else {
            None
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
            Expr::Term(Term::Stream(es)) | Expr::Term(Term::Tuple(es)) => {
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
