use std::collections::BTreeMap;
use std::mem;
use std::path::Path;

use crate::ast::{Module, ModulePath, Name};
use crate::codegen::lua::is_lua_binop;
use crate::error::Error as HuckError;
use crate::parse::parse;
use crate::scope::Scope;
use crate::types::{ApplySub, ConstraintGenerator, Error as TypeError, Type};

/// Context is the structure which manages module imports.
/// It contains some modules, manages references between modules, and prepares for typechecking.
///
/// If multiple modules depend on one another (with or without cycles), they must be typechecked and
/// transpiled as part of the same Context.
#[derive(Debug, Default)]
pub struct Context {
    /// The file stem of each included file in the context, e.g. "foo" in "foo.hk".
    pub file_stems: BTreeMap<ModulePath, String>,

    /// Each Module in the context.
    /// For each entry in this map, a related entry will be generated in the other maps.
    pub modules: BTreeMap<ModulePath, Module>,

    /// Each Scope in the context.
    pub scopes: BTreeMap<ModulePath, Scope>,

    /// These are assumptions made about imported names,
    /// so need to be handled at Context level rather than Scope level.
    pub assumptions: BTreeMap<(ModulePath, Name), Vec<Type>>,
}

impl Context {
    /// Typechecks the given Huck context.
    pub fn typecheck(&mut self) -> Result<(), TypeError> {
        let mut cg = ConstraintGenerator::default();

        for (module_path, module) in self
            .modules
            .iter()
            .map(|(p, m)| (p.clone(), m.clone()))
            .collect::<Vec<(ModulePath, Module)>>()
        {
            log::trace!("Typechecking: module {module_path};");
            // Set the scope's module path.
            let mut scope = Scope::new(module_path);

            // Generate constraints for each definition, while keeping track of inferred types
            for (name, defn) in module.definitions {
                let typ = cg.generate_definition(&defn);
                log::trace!("Initial inferred type for {}: {}", name, typ);

                // @Note: guaranteed to be None,
                // because we're iterating over a BTreeMap.
                assert!(scope
                    .definitions
                    // @Cleanup: do we need to clone this much?
                    .insert(name, (typ, defn))
                    .is_none());
            }

            // Generate constraints for each type definition
            for (_name, ast_type_defn) in module.type_definitions {
                let type_defn = cg.generate_type_definition(&ast_type_defn);

                for (constr_name, constr_type) in type_defn.constructors.iter() {
                    scope
                        .constructors
                        .insert(constr_name.clone(), constr_type.clone());
                }

                // @Note: guaranteed to be None,
                // because we're iterating over a BTreeMap.
                assert!(scope
                    .type_definitions
                    .insert(type_defn.name.clone(), type_defn)
                    .is_none());
            }

            // Insert all imported names into the scope.
            for (path, names) in module.imports {
                for name in names {
                    log::trace!("Inserting into scope of {module_path}: import {path} ({name})");
                    // @Todo @Checkme: name clashes?
                    assert!(scope
                        .imports
                        .insert(name, (path, self.file_stems[&path].clone()))
                        .is_none());
                }
            }

            // Polymorphically bind all top-level names.
            // If any assumptions were found to be imported,
            // their assumptions are promoted to Context level by this method.
            self.bind_all_module_level_assumptions(&scope, &mut cg);

            // Add the scope to the context.
            assert!(self.scopes.insert(module_path, scope).is_none());
        }

        // Constrain any names which were promoted to the Context level (i.e. imported names).
        self.bind_all_context_level_assumptions(&mut cg);

        // Solve the type constraints
        let soln = cg.solve()?;

        // @Todo: apply soln to the Scope directly, after impl ApplySub for Scope
        // Apply the solution to each Scope.
        for scope in self.scopes.values_mut() {
            log::info!("module {}:", scope.module_path);
            for (name, (ref mut typ, _definition)) in scope.definitions.iter_mut() {
                typ.apply(&soln);
                log::info!("  Inferred type for {} : {}", name, typ);
            }
        }

        Ok(())
    }

    /// Binds all top level assumptions to the types found in their definition.
    ///
    /// If the name isn't defined in this module, check if it's imported;
    /// if it is, then this assumption is promoted to Context level
    /// by inserting it into the Context.
    pub fn bind_all_module_level_assumptions(
        &mut self,
        scope: &Scope,
        cg: &mut ConstraintGenerator,
    ) {
        log::trace!("Emitting constraints about assumptions:");

        let mut assumptions = BTreeMap::new();
        mem::swap(&mut assumptions, &mut cg.assumptions);

        for (name, assumed_types) in assumptions {
            if let Some(typ) = scope.get_type(&name) {
                for assumed_type in assumed_types {
                    cg.implicit_instance(assumed_type, typ.clone());
                }
            } else if let Some((path, _stem)) = scope.imports.get(&name) {
                self.assumptions
                    .entry((*path, name))
                    .or_default()
                    .extend(assumed_types);
            } else if is_lua_binop(name.as_str()) {
                // Do nothing. @XXX @Cleanup: don't do this
                // @Prelude
            } else if name.as_str() == "True" || name.as_str() == "False" {
                // @Prelude
                let bool_type = Type::Concrete("Bool".to_string());
                for assumed_type in assumed_types {
                    cg.equate(assumed_type, bool_type.clone());
                }
            } else {
                // If there is no inferred type for the name (i.e. it's not in scope),
                // then it's a scope error.
                // @Errors: Scope error
                panic!("scope error: {name}");
            }
        }
    }

    /// Binds all context-level assumptions (i.e. from imported names).
    fn bind_all_context_level_assumptions(&mut self, cg: &mut ConstraintGenerator) {
        log::trace!("Emitting constraints about context-level assumptions:",);

        let mut assumptions = BTreeMap::new();
        mem::swap(&mut assumptions, &mut self.assumptions);

        for ((path, name), mut assumed_types) in assumptions {
            let scope = self.scopes.get(&path).unwrap_or_else(|| {
                // @Todo @Cleanup: should we catch this earlier?
                // If we didn't find the scope,
                // then the module doesn't exist.
                // @Errors: Scope error (import from nonexistent module)
                panic!("scope error (import from nonexistent module): {path}");
            });

            let typ = scope.get_type(&name).unwrap_or_else(|| {
                // If we didn't find the name in the module found above,
                // then the module doesn't contain the name which was attempted to be imported.
                // @Errors: Scope error (import)
                panic!("scope error (import doesn't exist): {path}.{name}");
            });

            // @Checkme: is this the right constraint?
            // Constrain that the assumed types are equal to the inferred type.
            assumed_types.push(typ);
            cg.equate_all(assumed_types);
        }
    }

    pub fn include_string(&mut self, src: String, file_stem: String) -> Result<(), HuckError> {
        let src = leak_string(src);

        let module = parse(src)?;
        let path = module.path.unwrap_or_default();

        if let Some(existing_module) = self.modules.insert(path, module) {
            match existing_module.path {
                Some(path) => return Err(HuckError::MultipleModules(format!("{}", path))),
                None => {
                    // @Todo @Checkme: I suspect this is unreachable
                    return Err(HuckError::MultipleModules(
                        "Main (default when no name given)".to_string(),
                    ));
                }
            }
        }

        assert!(self.file_stems.insert(path, file_stem).is_none());

        Ok(())
    }

    pub fn include_file<P>(&mut self, path: P) -> Result<(), HuckError>
    where
        P: AsRef<Path>,
    {
        match path.as_ref().extension() {
            Some(ex) if ex == "hk" => (),
            Some(_) => log::warn!("unknown filetype included: {:?}", path.as_ref()),
            _ => log::warn!("file without extension included: {:?}", path.as_ref()),
        }

        let src = std::fs::read_to_string(&path)?;

        // Pass through the source string, as well as the filepath stem (converted to String).
        self.include_string(
            src,
            path.as_ref()
                .file_stem()
                .expect("there should be a file name")
                .to_os_string()
                .into_string()
                .expect("the file name should be utf8"),
        )
    }
}

/// Leak a string, returning a &'static str with its contents.
fn leak_string(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}