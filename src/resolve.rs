use std::collections::BTreeMap;
use std::time::Instant;

use crate::ast::{ForeignImportItem, LuaName, Module, ModulePath, Name, Statement};
use crate::log;
use crate::parse::precedence::{ApplyPrecedence, Precedence};

pub fn resolve(path: ModulePath, statements: Vec<Statement>) -> Result<Module, Error> {
    // Start the timer to measure how long resolution takes.
    let start_time = Instant::now();

    let mut module = Module {
        path,
        ..Module::default()
    };

    let mut precs = BTreeMap::new();

    // Process all parsed statements,
    // and insert them into the Module (and precs map).
    log::trace!(log::RESOLVE, "Processing parsed statements");
    for stat in statements {
        match stat {
            Statement::AssignmentWithoutType((lhs, expr)) => {
                module
                    .definitions
                    .entry(lhs.name().clone())
                    .or_default()
                    .assignments
                    .push((lhs, expr));
            }

            Statement::AssignmentWithType(ts, (lhs, expr)) => {
                let defn = module.definitions.entry(lhs.name().clone()).or_default();

                // If there was already an explicit for this name, that's an error.
                if let Some(previous_ts) = defn.explicit_type.replace(ts.clone()) {
                    return Err(Error::MultipleTypes(
                        lhs.name().clone(),
                        // @Cleanup: don't have this dodgy whitespace
                        format!("\n    {:?}\n    {:?}", ts, previous_ts),
                    ));
                }

                defn.assignments.push((lhs, expr));
            }

            Statement::TypeAnnotation(name, ts) => {
                // If there was already an explicit for this name, that's an error.
                if let Some(previous_ts) = module
                    .definitions
                    .entry(name.clone())
                    .or_default()
                    .explicit_type
                    .replace(ts.clone())
                {
                    return Err(Error::MultipleTypes(
                        name,
                        // @Cleanup @Errors: don't have this dodgy whitespace
                        format!("\n    {:?}\n    {:?}", ts, previous_ts),
                    ));
                }
            }

            Statement::Precedence(name, prec) => {
                precs.insert(name.clone(), prec);
                // If there was already a precedence for this name, that's an error.
                if let Some(previous_prec) = module
                    .definitions
                    .entry(name.clone())
                    .or_default()
                    .precedence
                    .replace(prec)
                {
                    return Err(Error::MultiplePrecs(name, prec, previous_prec));
                }
            }

            Statement::TypeDefinition(type_defn) => {
                if let Some(first_defn) = module
                    .type_definitions
                    .insert(type_defn.name.clone(), type_defn)
                {
                    return Err(Error::MultipleTypeDefinitions(first_defn.name));
                }
            }

            // @Todo: do some actual resolution
            Statement::Import(path, names) => module.imports.entry(path).or_default().extend(names),

            // @Todo: do some actual resolution
            Statement::ForeignImport(require_string, import_items) => module
                .foreign_imports
                .entry(require_string)
                .or_default()
                .extend(import_items.into_iter().map(|item| match item {
                    ForeignImportItem::SameName(name, ts) => {
                        (LuaName(name.as_str().to_string()), name, ts)
                    }
                    ForeignImportItem::Rename(lua_name, name, ts) => (lua_name, name, ts),
                })),

            Statement::ForeignExport(lua_lhs, expr) => module.foreign_exports.push((lua_lhs, expr)),
        }
    }

    // Modify the AST to take precedence statements into account.
    log::trace!(log::RESOLVE, "Applying precedence statements to the AST");
    for defn in module.definitions.values_mut() {
        defn.apply(&precs);
    }

    log::info!(
        log::METRICS,
        "Resolution completed, {:?} elapsed",
        start_time.elapsed()
    );

    Ok(module)
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    // @Cleanup @Errors: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple precedence declarations found for `{0}`:\n    {1:?}\n    {2:?}")]
    MultiplePrecs(Name, Precedence, Precedence),

    // @Cleanup @Errors: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple explicit type annotations found for `{0}`:{1}")]
    MultipleTypes(Name, String),

    // @Cleanup @Errors: this should print the source locations of the two definitions
    #[error("Multiple type definitions with the same name ({0})")]
    MultipleTypeDefinitions(Name),
}
