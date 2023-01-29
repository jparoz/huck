use std::mem;
use std::{collections::BTreeMap, time::Instant};

use crate::generatable_module::GeneratableModule;
use crate::module::{Module, ModulePath};
use crate::name::{ResolvedName, Source};
use crate::types::{self, Type, TypeScheme, TypeVarSet};
use crate::{ast, log};

mod constraint;
mod substitution;

use constraint::ConstraintGenerator;
use substitution::{ApplySub, Substitution};

#[cfg(test)]
mod test;

/// Manages typechecking of a group of modules.
#[derive(Debug, Default)]
pub struct Typechecker {
    /// The constraint generator.
    cg: ConstraintGenerator,

    /// These are type assumptions made about imported names,
    /// so need to be handled at Typechecker level rather than module level.
    assumptions: BTreeMap<ResolvedName, Vec<Type>>,
}

impl Typechecker {
    pub fn new() -> Self {
        Self::default()
    }

    /// Typechecks the given Huck context.
    pub fn typecheck(
        &mut self,
        mut modules: BTreeMap<ModulePath, Module<ResolvedName, ()>>,
    ) -> Result<BTreeMap<ModulePath, GeneratableModule>, Error> {
        // Start the timer to measure how long typechecking takes.
        let start_time = Instant::now();
        log::info!(log::TYPECHECK, "Typechecking all modules...");

        // Ensure the prelude is typechecked first.
        // Has to be done in this order
        // so that the implicit Prelude import statement
        // can be imported into other modules.
        let prelude_path = ModulePath("Prelude");
        let prelude = modules
            .remove(&prelude_path)
            .into_iter()
            .map(|m| (prelude_path, m));

        let mut gen_mods = BTreeMap::new();

        // for (module_path, module) in modules {
        for (module_path, module) in prelude.chain(modules.into_iter()) {
            log::trace!(log::TYPECHECK, "Typechecking: module {module_path};");
            // Set the new GeneratableModule's path.
            let mut gen_mod = GeneratableModule::new(module_path);

            // Generate constraints for each definition, while keeping track of inferred types
            for (name, defn) in module.definitions {
                let typ = self.cg.generate_definition(&defn);
                log::trace!(
                    log::TYPECHECK,
                    "Initial inferred type for {}: {}",
                    name,
                    typ
                );
                let typed_defn = {
                    let ast::Definition {
                        assignments,
                        explicit_type,
                        precedence,
                        typ: (),
                    } = defn;

                    ast::Definition {
                        assignments,
                        explicit_type,
                        precedence,
                        typ,
                    }
                };

                // @Note: guaranteed to be None,
                // because we're iterating over a BTreeMap.
                assert!(gen_mod.definitions.insert(name, typed_defn).is_none());
            }

            // Generate constraints for each type definition
            for (_name, ast_type_defn) in module.type_definitions {
                let type_defn = self.cg.generate_type_definition(ast_type_defn);

                for (constr_name, constr_defn) in type_defn.constructors.iter() {
                    gen_mod
                        .constructors
                        .insert(*constr_name, constr_defn.clone());
                }

                // @Note: guaranteed to be None,
                // because we're iterating over a BTreeMap.
                assert!(gen_mod
                    .type_definitions
                    .insert(type_defn.name, type_defn)
                    .is_none());
            }

            // Insert all imported names into the scope.
            for (path, names) in module.imports {
                log::trace!(
                    log::IMPORT,
                    "Inserting into scope of {module_path}: import {path} ({names:?})"
                );
                // @Todo @Errors: check for name clashes
                gen_mod.imports.entry(path).or_default().extend(names);
            }

            // Insert all (foreign) imported names into the scope.
            for (require_string, imports) in module.foreign_imports {
                for ast::ForeignImportItem {
                    foreign_name,
                    name,
                    type_scheme,
                    typ: (),
                } in imports
                {
                    log::trace!(
                        log::IMPORT,
                        "Inserting into scope of {module_path}: \
                         foreign import {require_string} ({foreign_name} as {name})"
                    );
                    // @Todo @Errors: check for name clashes
                    gen_mod
                        .foreign_imports
                        .entry(require_string)
                        .or_default()
                        .push(ast::ForeignImportItem {
                            foreign_name,
                            name,
                            // @XXX @Fixme: this throws away the type variables.
                            typ: self.cg.generate_type_scheme(&type_scheme).typ,
                            type_scheme,
                        });
                }
            }

            // Insert all foreign exports into the scope.
            gen_mod.foreign_exports.extend(module.foreign_exports);

            // If there is no explicit Prelude import already,
            // import everything in Prelude.
            let prelude_path = ModulePath("Prelude");
            if module_path != prelude_path {
                log::trace!(
                    log::IMPORT,
                    "Importing contents of Prelude into {module_path}"
                );
                let prelude_gm: &GeneratableModule = &gen_mods[&prelude_path];

                // @Todo @Checkme @Errors @Warn: name clashes
                gen_mod.imports.entry(prelude_path).or_default().extend(
                    prelude_gm
                        .definitions
                        .keys()
                        .chain(prelude_gm.constructors.keys()),
                );
            }

            // Polymorphically bind all top-level names.
            // If any assumptions were found to be imported,
            // their assumptions are promoted to Context level by this method.
            self.bind_all_module_level_assumptions(&gen_mod)?;

            // Add the GeneratableModule to the context.
            assert!(gen_mods.insert(module_path, gen_mod).is_none());
        }

        // Constrain any names which were promoted to the Context level (i.e. imported names).
        self.bind_all_context_level_assumptions(&gen_mods)?;

        // Solve the type constraints
        let soln = self.cg.solve()?;

        // @Todo: apply soln to the GeneratableModule directly,
        // after impl ApplySub for GeneratableModule
        // Apply the solution to each GeneratableModule.
        for module in gen_mods.values_mut() {
            log::info!(log::TYPECHECK, "module {}:", module.path);
            for (name, ref mut definition) in module.definitions.iter_mut() {
                definition.typ.apply(&soln);
                log::info!(
                    log::TYPECHECK,
                    "  Inferred type for {name} : {}",
                    definition.typ
                );
            }
        }

        log::info!(
            log::METRICS,
            "Typechecking completed, {:?} elapsed",
            start_time.elapsed()
        );

        Ok(gen_mods)
    }

    /// Binds all top level assumptions to the types found in their definition.
    ///
    /// If the name isn't defined in this module, check if it's imported;
    /// if it is, then this assumption is promoted to Context level
    /// by inserting it into the Context.
    fn bind_all_module_level_assumptions(
        &mut self,
        module: &GeneratableModule,
    ) -> Result<(), Error> {
        log::trace!(log::TYPECHECK, "Emitting constraints about assumptions:");

        let mut assumptions = BTreeMap::new();
        mem::swap(&mut assumptions, &mut self.cg.assumptions);

        for (assumed_name, assumed_types) in assumptions {
            if let Some(typ) = module.get_type(&assumed_name) {
                // This means that it was defined in this module.
                for assumed_type in assumed_types {
                    self.cg.implicit_instance(assumed_type, typ.clone());
                }
            } else if let Source::Foreign { require, .. } = assumed_name.source {
                // This means that the name was imported from a foreign (Lua) module;
                // this means that the Huck author gave an explicit type signature at the import.

                let imports = module
                    .foreign_imports
                    .get(require)
                    .expect("should already be resolved");

                for ast::ForeignImportItem { name, typ, .. } in imports {
                    if name == &assumed_name {
                        for assumed_type in assumed_types.iter() {
                            self.cg.explicit_instance(
                                assumed_type.clone(),
                                // @XXX @Cleanup: we're just replacing the type variables which are
                                // thrown away when inserting foreign imports into the scope.
                                typ.clone().generalize(&TypeVarSet::empty()),
                            );
                        }
                    }
                }
            } else if assumed_name.source == Source::Builtin {
                // @Cleanup: @DRY with Pattern::UnaryConstructor branch
                // in ConstraintGenerator::bind_pattern

                // This means that it's a compiler builtin.
                match assumed_name.ident {
                    "True" | "False" => assumed_types
                        .into_iter()
                        .for_each(|t| self.cg.equate(t, Type::Primitive(types::Primitive::Bool))),
                    _ => unreachable!("missing a compiler builtin type"),
                }
            } else {
                // This means that the name was imported from another Huck module;
                // so we need to resolve it at Context level later.
                // We do this by pushing it into self.assumptions (i.e. the Context)
                self.assumptions
                    .entry(assumed_name)
                    .or_default()
                    .extend(assumed_types);
            }
        }

        Ok(())
    }

    /// Binds all context-level assumptions (i.e. from imported names).
    //
    // @Note:
    // We used to do this in a similar way to bind_all_module_level_assumptions,
    // by iterating over self.assumptions and binding the names as they appear there.
    // However, this didn't catch the error where
    // an import was unused and also didn't exist in the imported module.
    // By instead iterating over each modules's imported names,
    // we ensure that all imports exist, whether they're used or not.
    fn bind_all_context_level_assumptions(
        &mut self,
        modules: &BTreeMap<ModulePath, GeneratableModule>,
    ) -> Result<(), Error> {
        log::trace!(
            log::TYPECHECK,
            "Emitting constraints about context-level assumptions:"
        );

        for module in modules.values() {
            for (import_path, import_names) in module.imports.iter() {
                // Find the inferred type.
                // @Note: this should be infallable,
                // because we've already confirmed everything exists in the resolve step.
                let import_module = modules
                    .get(import_path)
                    .expect("should already be resolved");

                for import_name in import_names {
                    let typ = import_module
                        .get_type(import_name)
                        .expect("should already be resolved and typechecked");

                    // If there are any assumptions about the variable, bind them.
                    if let Some(assumed_types) = self.assumptions.remove(import_name) {
                        // Constrain that the assumed types are instances of the inferred type.
                        for assumed_type in assumed_types {
                            self.cg.implicit_instance(assumed_type, typ.clone());
                        }
                    } else {
                        // @Todo @Errors @Warn: emit a warning for unused imports
                        if import_path != &ModulePath("Prelude") {
                            log::warn!(log::IMPORT, "unused: import {import_path} ({import_name})");
                        }
                    }
                }
            }
        }

        Ok(())
    }
}

impl Type {
    fn free_vars(&self) -> TypeVarSet {
        match self {
            Type::Concrete(_) | Type::Primitive(_) => TypeVarSet::empty(),

            Type::Var(var) => TypeVarSet::single(var.clone()),
            Type::Arrow(a, b) | Type::App(a, b) => a.free_vars().union(&b.free_vars()),
            Type::List(t) => t.free_vars(),
            Type::Tuple(v) => v
                .iter()
                .fold(TypeVarSet::empty(), |a, t| a.union(&t.free_vars())),
        }
    }

    /// Takes a Type and quantifies all free type variables, except the ones given in type_set.
    fn generalize(&self, type_set: &TypeVarSet) -> TypeScheme {
        TypeScheme {
            vars: self.free_vars().difference(type_set),
            typ: self.clone(),
        }
    }

    /// Finds the most general unifier for two types.
    fn unify(self, other: Self) -> Result<Substitution, Error> {
        let mut sub = Substitution::empty();

        let mut pairs = vec![(self, other)];

        while let Some((a, b)) = pairs.pop() {
            match (a, b) {
                (t1, t2) if t1 == t2 => (),
                (Type::Var(var), t) | (t, Type::Var(var)) => {
                    if t.free_vars().contains(&var) {
                        // @CheckMe
                        return Err(Error::CouldNotUnifyRecursive(t, Type::Var(var)));
                    } else {
                        let s = Substitution::single(var.clone(), t.clone());
                        for (a2, b2) in pairs.iter_mut() {
                            a2.apply(&s);
                            b2.apply(&s);
                        }
                        sub = sub.then(s);
                    }
                }
                (Type::List(t1), Type::List(t2)) => pairs.push((*t1, *t2)),
                (Type::Tuple(ts1), Type::Tuple(ts2)) => {
                    for (t1, t2) in ts1.into_iter().zip(ts2.into_iter()) {
                        pairs.push((t1, t2));
                    }
                }
                (Type::Arrow(a1, b1), Type::Arrow(a2, b2))
                | (Type::App(a1, b1), Type::App(a2, b2)) => {
                    pairs.push((*a1, *a2));
                    pairs.push((*b1, *b2));
                }
                (t1, t2) => return Err(Error::CouldNotUnify(t1, t2)),
            }
        }

        Ok(sub)
    }
}

impl TypeScheme {
    fn free_vars(&self) -> TypeVarSet {
        self.typ.free_vars().difference(&self.vars)
    }
}

/// An enum representing all possible type errors.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Could not unify type '{0}' with type '{1}'")]
    CouldNotUnify(Type, Type),

    #[error("Could not unify type '{0}' with type '{1}' (recursive type)")]
    CouldNotUnifyRecursive(Type, Type),
}
