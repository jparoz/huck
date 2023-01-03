use std::collections::BTreeMap;
use std::path::Path;

use crate::ast::{Module, ModulePath};
use crate::error::Error as HuckError;
use crate::parse::parse;
use crate::scope::Scope;
use crate::types::{ApplySub, ConstraintGenerator, Error as TypeError};

/// Context is the structure which manages module imports.
/// It contains some modules, manages references between modules, and prepares for typechecking.
///
/// If multiple modules depend on one another (with or without cycles), they must be typechecked and
/// transpiled as part of the same Context.
#[derive(Debug, Default)]
pub struct Context<'file> {
    pub modules: BTreeMap<ModulePath<'file>, Module<'file>>,
    pub scopes: BTreeMap<ModulePath<'file>, Scope<'file>>,
}

impl<'file> Context<'file> {
    pub fn include_string(&mut self, src: String) -> Result<(), HuckError> {
        let src = leak_string(src);

        let module = parse(src)?;

        if let Some(existing_module) = self.modules.insert(module.path.unwrap_or_default(), module)
        {
            match existing_module.path {
                Some(path) => return Err(HuckError::MultipleModules(format!("{}", path))),
                None => {
                    return Err(HuckError::MultipleModules(
                        "Main (default when no name given)".to_string(),
                    ))
                }
            }
        }

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
        self.include_string(src)
    }

    /// Typechecks the given Huck context.
    pub fn typecheck(&mut self) -> Result<(), TypeError> {
        let mut cg = ConstraintGenerator::default();

        for (module_path, module) in self.modules.iter() {
            let mut scope = Scope::default();

            // Generate constraints for each definition, while keeping track of inferred types
            for (name, defn) in module.definitions.iter() {
                let typ = cg.generate_definition(defn);
                log::trace!("Initial inferred type for {}: {}", name, typ);

                // @Note: guaranteed to be None,
                // because we're iterating over a BTreeMap.
                assert!(scope
                    .definitions
                    // @Cleanup: do we need to clone this much?
                    .insert(name.clone(), (typ, defn.clone()))
                    .is_none());
            }

            // Generate constraints for each type definition
            for (_name, ast_type_defn) in module.type_definitions.iter() {
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

            // @Todo: generate constraints (assumptions?) for imports

            // Polymorphically bind all top-level variables.
            cg.bind_all_top_level_assumptions(&scope);

            // Add the scope to the context.
            assert!(self.scopes.insert(*module_path, scope).is_none());
        }

        // Solve the type constraints
        let soln = cg.solve()?;

        // @Todo: apply soln to the Scope directly, after impl ApplySub for Scope
        // Apply the solution to each Scope.
        for scope in self.scopes.values_mut() {
            for (name, (ref mut typ, _definition)) in scope.definitions.iter_mut() {
                typ.apply(&soln);
                log::info!("Inferred type for {} : {}", name, typ);
            }
        }

        Ok(())
    }
}

/// Leak a string, returning a &'static str with its contents.
fn leak_string(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}
