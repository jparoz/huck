use std::collections::BTreeMap;
use std::mem;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::ast::{Module, ModulePath, Statement, UnresolvedName};
use crate::error::Error as HuckError;
use crate::generatable_module::GeneratableModule;
use crate::parse::parse;
use crate::resolve::ResolvedName;
use crate::types::{ApplySub, Error as TypeError, Type};
use crate::{codegen, log, resolve};

mod constraint;
use constraint::ConstraintGenerator;

pub use constraint::Constraint;

/// Context is the structure which manages module imports.
/// It contains some modules, manages references between modules, and prepares for typechecking.
///
/// If multiple modules depend on one another (with or without cycles), they must be typechecked and
/// transpiled as part of the same Context.
#[derive(Debug, Default)]
pub struct Context {
    /// The file path of each included file in the context.
    /// For each entry in this map, a related entry will be generated in the other maps.
    pub file_paths: BTreeMap<ModulePath, PathBuf>,

    /// The freshly parsed statement lists for each module.
    pub parsed: BTreeMap<ModulePath, Vec<Statement<UnresolvedName>>>,

    /// The constraint generator.
    cg: ConstraintGenerator,

    /// These are type assumptions made about imported names,
    /// so need to be handled at Context level rather than module level.
    // @Todo @Cleanup: change this to use ResolvedName
    assumptions: BTreeMap<(ModulePath, ResolvedName), Vec<Type>>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    /// Does every step necessary to take the added modules to compiled state.
    /// Returns a Vec of tuples of originating Huck file paths, and the resulting Lua as a String.
    //
    // @Future: we could incrementally process modules somehow,
    // rather than just having this monolithic all-or-nothing compile step.
    pub fn compile(mut self) -> Result<Vec<(PathBuf, String)>, HuckError> {
        // @Todo @Cleanup: Move lots of the state stored on Context to be variables here.

        // Post-parse processing
        // @XXX @Todo: don't clone
        let mut modules = self.post_parse(self.parsed.clone())?;

        // Resolve names
        let mut resolved_modules = BTreeMap::new();

        // Start with the prelude
        let prelude_path = ModulePath("Prelude");
        if let Some(unresolved_prelude) = modules.remove(&prelude_path) {
            let resolved_prelude = self.resolve(unresolved_prelude)?;
            resolved_modules.insert(prelude_path, resolved_prelude);
        }

        // @Todo: pass the prelude scope into resolve for the other modules,
        // so it can be automatically inserted into scope.
        // Or change the function signature of resolve to accept a &mut Scope,
        // instead of making a new one each time.

        // @Todo: Make all the `resolve_*` methods into methods on Scope

        for (path, module) in modules {
            let resolved_module = self.resolve(module)?;
            resolved_modules.insert(path, resolved_module);
        }

        // @Todo: check that qualified names were used properly
        // (i.e. check the `assumptions` field on each `Scope`)
        // Something like this should be the error (or maybe a new special variant):
        // Err(Error::NonexistentImport(path, UnresolvedName::Ident(ident)))

        // Typecheck
        let gen_mods = self.typecheck(resolved_modules)?;

        // Generate code
        let mut generated = Vec::new();

        // @Todo @Cleanup: move this into codegen (?)
        for (module_path, file_path) in self.file_paths {
            log::trace!(log::CODEGEN, "Generating code for module {module_path}");
            let lua = codegen::lua::generate(&gen_mods[&module_path])?;
            generated.push((file_path, lua));
        }

        Ok(generated)
    }

    /// Typechecks the given Huck context.
    // @Cleanup: not pub (? maybe needed in tests)
    pub fn typecheck(
        &mut self,
        mut modules: BTreeMap<ModulePath, Module<ResolvedName>>,
    ) -> Result<BTreeMap<ModulePath, GeneratableModule>, HuckError> {
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

                // @Note: guaranteed to be None,
                // because we're iterating over a BTreeMap.
                assert!(gen_mod.definitions.insert(name, (typ, defn)).is_none());
            }

            // Generate constraints for each type definition
            for (_name, ast_type_defn) in module.type_definitions {
                let type_defn = self.cg.generate_type_definition(&ast_type_defn);

                for (constr_name, constr_type) in type_defn.constructors.iter() {
                    gen_mod
                        .constructors
                        .insert(*constr_name, constr_type.clone());
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
                for name in names {
                    log::trace!(
                        log::IMPORT,
                        "Inserting into scope of {module_path}: import {path} ({name})"
                    );
                    // @Todo @Checkme: name clashes?
                    assert!(gen_mod
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
                    assert!(gen_mod
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
            gen_mod.foreign_exports.extend(module.foreign_exports);

            // If there is no explicit Prelude import already,
            // import everything in Prelude.
            let prelude_path = ModulePath("Prelude");
            if module_path != prelude_path {
                log::trace!(
                    log::IMPORT,
                    "Importing contents of Prelude into {module_path}"
                );
                let prelude_stem = self.file_stem(prelude_path);
                let prelude_gm: &GeneratableModule = &gen_mods[&prelude_path];
                for name in prelude_gm
                    .definitions
                    .keys()
                    .chain(prelude_gm.constructors.keys())
                {
                    // @Todo @Checkme @Errors @Warn: name clashes?
                    assert!(gen_mod
                        .imports
                        .insert(*name, (prelude_path, prelude_stem.clone()))
                        .is_none());
                }
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
            for (name, (ref mut typ, _definition)) in module.definitions.iter_mut() {
                typ.apply(&soln);
                log::info!(log::TYPECHECK, "  Inferred type for {name} : {typ}");
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
    pub fn bind_all_module_level_assumptions(
        &mut self,
        module: &GeneratableModule,
    ) -> Result<(), HuckError> {
        log::trace!(log::TYPECHECK, "Emitting constraints about assumptions:");

        let mut assumptions = BTreeMap::new();
        mem::swap(&mut assumptions, &mut self.cg.assumptions);

        for (name, assumed_types) in assumptions {
            if let Some(typ) = module.get_type(&name) {
                // This means that it was defined in this module.
                for assumed_type in assumed_types {
                    self.cg.implicit_instance(assumed_type, typ.clone());
                }
            } else if let Some((_require_string, _lua_name, type_scheme)) =
                module.foreign_imports.get(&name)
            {
                // This means that the name was imported from a foreign (Lua) module;
                // this means that the Huck author gave an explicit type signature at the import.
                for assumed_type in assumed_types {
                    self.cg.explicit_instance(assumed_type, type_scheme.clone());
                }
            } else if let Some((path, _stem)) = module.imports.get(&name) {
                // This means that the name was imported from another Huck module;
                // so we need to resolve it at Context level later.
                // We do this by pushing it into self.assumptions (i.e. the Context)
                self.assumptions
                    .entry((*path, name))
                    .or_default()
                    .extend(assumed_types);
            } else {
                // // If there is no inferred type for the name (i.e. it's not in scope),
                // // then it's a scope error.
                // return Err(resolve::Error::NotInScope(module.path, name).into());
                todo!() // @Fixme @XXX @Todo @Nocommit
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
    ) -> Result<(), HuckError> {
        log::trace!(
            log::TYPECHECK,
            "Emitting constraints about context-level assumptions:"
        );

        for module in modules.values() {
            for (import_name, (import_path, _import_stem)) in module.imports.iter() {
                // Find the inferred type.
                let import_module = modules.get(import_path).ok_or_else(|| {
                    HuckError::from(resolve::Error::NonexistentModule(*import_path))
                })?;
                let typ = import_module.get_type(import_name).ok_or_else(|| {
                    HuckError::from(
                        // @Fixme @XXX @Todo @Nocommit
                        resolve::Error::NonexistentImport(
                            *import_path,
                            // *import_name,
                            UnresolvedName::Ident("FAKE"),
                        ),
                    )
                })?;

                // If there are any assumptions about the variable, bind them.
                if let Some(assumed_types) = self.assumptions.remove(&(*import_path, *import_name))
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

        Ok(())
    }

    /// Adds the given file to the Context.
    pub fn include_file<P>(&mut self, file_path: P) -> Result<(), HuckError>
    where
        P: AsRef<Path>,
    {
        log::info!(
            log::IMPORT,
            "Adding {path} to the context",
            path = file_path.as_ref().display()
        );

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

    #[cfg(test)]
    /// Adds the given string to the Context, treating it as anonymous input e.g. REPL input.
    pub fn include_string(&mut self, src: &'static str) -> Result<(), HuckError> {
        self.include(src, None)
    }

    /// Actually includes the module in the Context.
    /// Called by [`include_file`][Context::include_file]
    /// and [`include_string`][Context::include_string].
    fn include(&mut self, src: &'static str, path_buf: Option<PathBuf>) -> Result<(), HuckError> {
        let (module_path, statements) = parse(src)?;
        log::trace!(log::PARSE, "Parsed module {module_path}: {statements:?}");

        if self.parsed.insert(module_path, statements).is_some() {
            return Err(HuckError::MultipleModules(format!("{}", module_path)));
        }

        // @Todo @Cleanup: don't do this, because there should always be a file path.
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

/// Leak a string, returning a &'static str with its contents.
fn leak_string(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}
