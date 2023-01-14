use std::collections::BTreeMap;
use std::mem;
use std::path::{Path, PathBuf};

use crate::ast::{Module, ModulePath, Name};
use crate::error::Error as HuckError;
use crate::log;
use crate::parse::parse;
use crate::scope::Scope;
use crate::types::{ApplySub, Error as TypeError, Type};
use crate::utils::leak_string;

mod constraint;

pub use constraint::{Constraint, ConstraintGenerator};

/// Context is the structure which manages module imports.
/// It contains some modules, manages references between modules, and prepares for typechecking.
///
/// If multiple modules depend on one another (with or without cycles), they must be typechecked and
/// transpiled as part of the same Context.
#[derive(Debug, Default)]
pub struct Context {
    /// The file path of each included file in the context.
    pub file_paths: BTreeMap<ModulePath, PathBuf>,

    /// Each Module in the context.
    /// For each entry in this map, a related entry will be generated in the other maps.
    modules: BTreeMap<ModulePath, Module>,

    /// The Prelude module.
    prelude: Option<(ModulePath, Module)>,

    /// Each Scope in the context.
    pub scopes: BTreeMap<ModulePath, Scope>,

    /// The constraint generator.
    cg: ConstraintGenerator,

    /// These are assumptions made about imported names,
    /// so need to be handled at Context level rather than Scope level.
    assumptions: BTreeMap<(ModulePath, Name), Vec<Type>>,
}

impl Context {
    pub fn new() -> Self {
        let mut ctx = Self::default();

        // Add the prelude to the Context by default.
        log::info!(log::IMPORT, "Adding Prelude to the context");
        // @Todo: move this to a file packaged with the compiler somehow,
        // rather than having it be included into the source like this.
        ctx.include_prelude(include_str!("../../huck/Prelude.hk"))
            .unwrap();

        ctx
    }

    /// Typechecks the given Huck context.
    pub fn typecheck(&mut self) -> Result<(), TypeError> {
        // First, typecheck the Prelude;
        // then all the other modules.
        // Has to be done in this order
        // so that the Prelude can be imported into other modules.
        for (module_path, module) in self
            .prelude
            .iter()
            // This changes from &(p, m) to (&p, &m)
            .map(|(p, m)| (p, m))
            .chain(self.modules.iter())
            .map(|(p, m)| (p.clone(), m.clone()))
            .collect::<Vec<(ModulePath, Module)>>()
        {
            log::trace!(log::TYPECHECK, "Typechecking: module {module_path};");
            // Set the scope's module path.
            let mut scope = Scope::new(module_path);

            // Generate constraints for each definition, while keeping track of inferred types
            for (name, defn) in module.definitions {
                let typ = self.cg.generate_definition(&defn);
                log::trace!(
                    log::TYPECHECK,
                    "Initial inferred type for {}: {}",
                    name,
                    typ
                );

                // @Note: guaranteed to be None,
                // because we're iterating over a BTreeMap.
                assert!(scope.definitions.insert(name, (typ, defn)).is_none());
            }

            // Generate constraints for each type definition
            for (_name, ast_type_defn) in module.type_definitions {
                let type_defn = self.cg.generate_type_definition(&ast_type_defn);

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
                    log::trace!(
                        log::IMPORT,
                        "Inserting into scope of {module_path}: import {path} ({name})"
                    );
                    // @Todo @Checkme: name clashes?
                    assert!(scope
                        .imports
                        .insert(name, (path, self.file_stem(path)))
                        .is_none());
                }
            }

            // Insert all (foreign) imported names into the scope.
            for (require_string, imports) in module.foreign_imports {
                for (lua_name, huck_name, ast_type_scheme) in imports {
                    log::trace!(
                        log::IMPORT,
                        "Inserting into scope of {module_path}: \
                         foreign import {require_string} ({lua_name} as {huck_name})"
                    );
                    // @Todo @Checkme: name clashes?
                    assert!(scope
                        .foreign_imports
                        .insert(
                            huck_name,
                            (
                                require_string,
                                lua_name,
                                self.cg.generate_type_scheme(&ast_type_scheme)
                            )
                        )
                        .is_none());
                }
            }

            // Insert all foreign exports into the scope.
            scope.foreign_exports.extend(module.foreign_exports);

            // If there is no explicit Prelude import already,
            // import everything in Prelude.
            let prelude_path = ModulePath("Prelude");
            if module_path != prelude_path {
                log::trace!(
                    log::IMPORT,
                    "Importing contents of Prelude into {module_path}"
                );
                let prelude_stem = self.file_stem(prelude_path);
                let prelude_scope = &self.scopes[&prelude_path];
                for name in prelude_scope
                    .definitions
                    .keys()
                    .chain(prelude_scope.constructors.keys())
                {
                    // @Todo @Checkme @Errors @Warn: name clashes?
                    assert!(scope
                        .imports
                        .insert(name.clone(), (prelude_path, prelude_stem.clone()))
                        .is_none());
                }
            }

            // Polymorphically bind all top-level names.
            // If any assumptions were found to be imported,
            // their assumptions are promoted to Context level by this method.
            self.bind_all_module_level_assumptions(&scope);

            // Add the scope to the context.
            assert!(self.scopes.insert(module_path, scope).is_none());
        }

        // Constrain any names which were promoted to the Context level (i.e. imported names).
        self.bind_all_context_level_assumptions();

        // Solve the type constraints
        let soln = self.cg.solve()?;

        // @Todo: apply soln to the Scope directly, after impl ApplySub for Scope
        // Apply the solution to each Scope.
        for scope in self.scopes.values_mut() {
            log::info!(log::TYPECHECK, "module {}:", scope.module_path);
            for (name, (ref mut typ, _definition)) in scope.definitions.iter_mut() {
                typ.apply(&soln);
                log::info!(log::TYPECHECK, "  Inferred type for {} : {}", name, typ);
            }
        }

        Ok(())
    }

    /// Binds all top level assumptions to the types found in their definition.
    ///
    /// If the name isn't defined in this module, check if it's imported;
    /// if it is, then this assumption is promoted to Context level
    /// by inserting it into the Context.
    pub fn bind_all_module_level_assumptions(&mut self, scope: &Scope) {
        log::trace!(log::TYPECHECK, "Emitting constraints about assumptions:");

        let mut assumptions = BTreeMap::new();
        mem::swap(&mut assumptions, &mut self.cg.assumptions);

        for (name, assumed_types) in assumptions {
            if let Some(typ) = scope.get_type(&name) {
                // This means that it was defined in this module.
                for assumed_type in assumed_types {
                    self.cg.implicit_instance(assumed_type, typ.clone());
                }
            } else if let Some((_require_string, _lua_name, type_scheme)) =
                scope.foreign_imports.get(&name)
            {
                // This means that the name was imported from a foreign (Lua) module;
                // this means that the Huck author gave an explicit type signature at the import.
                for assumed_type in assumed_types {
                    self.cg.explicit_instance(assumed_type, type_scheme.clone());
                }
            } else if let Some((path, _stem)) = scope.imports.get(&name) {
                // This means that the name was imported from another Huck module;
                // so we need to resolve it at Context level later.
                // We do this by pushing it into self.assumptions (i.e. the Context)
                self.assumptions
                    .entry((*path, name))
                    .or_default()
                    .extend(assumed_types);
            } else {
                // If there is no inferred type for the name (i.e. it's not in scope),
                // then it's a scope error.
                // @Errors: Scope error
                panic!("scope error: {name}");
            }
        }
    }

    /// Binds all context-level assumptions (i.e. from imported names).
    //
    // @Note:
    // We used to do this in a similar way to bind_all_module_level_assumptions,
    // by iterating over self.assumptions and binding the names as they appear there.
    // However, this didn't catch the error where
    // an import was unused and also didn't exist in the imported module.
    // By instead iterating over each scope's imported names,
    // we ensure that all imports exist, whether they're used or not.
    fn bind_all_context_level_assumptions(&mut self) {
        log::trace!(
            log::TYPECHECK,
            "Emitting constraints about context-level assumptions:"
        );

        for scope in self.scopes.values() {
            for (import_name, (import_path, _import_stem)) in scope.imports.iter() {
                // Find the inferred type.
                let import_scope = self.scopes.get(import_path).unwrap_or_else(|| {
                    // @Errors: Scope error (nonexistent module)
                    panic!("scope error (nonexistent module): {import_path}")
                });
                let typ = import_scope.get_type(import_name).unwrap_or_else(|| {
                    // @Errors: Scope error (nonexistent import)
                    panic!("scope error (imported name doesn't exist): {import_path}.{import_name}")
                });

                // If there are any assumptions about the variable, bind them.
                if let Some(assumed_types) =
                    // @Checkme: do we need to clone?
                    self
                        .assumptions
                        .remove(&(import_path.clone(), import_name.clone()))
                {
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

    /// Adds the given file to the Context.
    pub fn include_file<P>(&mut self, file_path: P) -> Result<(), HuckError>
    where
        P: AsRef<Path>,
    {
        match file_path.as_ref().extension() {
            Some(ex) if ex == "hk" => (),
            Some(_) => log::warn!(
                log::IMPORT,
                "unknown filetype included: {:?}",
                file_path.as_ref()
            ),
            _ => log::warn!(
                log::IMPORT,
                "file without extension included: {:?}",
                file_path.as_ref()
            ),
        }

        let src = std::fs::read_to_string(&file_path)?;
        let src = leak_string(src);

        self.include(src, Some(file_path.as_ref().to_path_buf()))
    }

    /// Adds the given string to the Context, treating it as anonymous input e.g. REPL input.
    pub fn include_string(&mut self, src: &'static str) -> Result<(), HuckError> {
        self.include(src, None)
    }

    /// Adds the given String to the Context as the Prelude.
    pub fn include_prelude(&mut self, src: &'static str) -> Result<(), HuckError> {
        let module = parse(src)?;
        log::trace!(log::PARSE, "Parsed module: {:?}", module);

        // @Errors: do a proper error instead of expect and asserts
        let module_path = module
            .path
            .expect("the prelude should have the module name Prelude");
        assert_eq!(module_path, ModulePath("Prelude"));
        assert!(
            self.prelude.replace((module_path, module)).is_none(),
            "can't define multiple preludes"
        );

        // Generate a PathBuf from the module path.
        let path_buf = Path::new("Prelude.hk").to_path_buf();
        assert!(self.file_paths.insert(module_path, path_buf).is_none());

        Ok(())
    }

    /// Actually includes the module in the Context.
    /// Called by [`include_file`][Context::include_file]
    /// and [`include_string`][Context::include_string].
    fn include(&mut self, src: &'static str, path_buf: Option<PathBuf>) -> Result<(), HuckError> {
        let module = parse(src)?;
        log::trace!(log::PARSE, "Parsed module: {:?}", module);
        let module_path = module.path.unwrap_or_default();

        if let Some(existing_module) = self.modules.insert(module_path, module) {
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

        // If there is no file path, generate one from the module path.
        let path_buf = if let Some(path_buf) = path_buf {
            path_buf
        } else {
            let mut path_buf = PathBuf::new();
            path_buf.push(format!("{}", module_path));
            path_buf.set_extension("hk");
            path_buf
        };

        // Insert the file path
        assert!(self.file_paths.insert(module_path, path_buf).is_none());

        Ok(())
    }

    /// Returns the file stem of the file path corresponding to the given module path.
    /// Panics if there is no file path stored in the Context corresponding to the given path.
    /// @XXX: doesn't panic, just punts
    fn file_stem(&mut self, path: ModulePath) -> String {
        // @XXX @Hack: this is just a punt
        // @Todo: do something smarter
        let mut xxx_path_buf = None;

        self.file_paths
            .get(&path)
            .unwrap_or_else(|| {
                xxx_path_buf = Some(format!("{}.hk", path).into());
                xxx_path_buf.as_ref().unwrap()
            })
            .file_stem()
            .expect("there should be a file name")
            .to_os_string()
            .into_string()
            .expect("the file name should be utf8")
    }
}
