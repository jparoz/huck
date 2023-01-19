use std::collections::BTreeMap;
use std::time::Instant;

use crate::ast::{ForeignImportItem, LuaName, Module, ModulePath, Name, Statement};
use crate::context::Context;
use crate::log;
use crate::parse::precedence::{ApplyPrecedence, Precedence};

impl Context {
    pub fn resolve(&mut self) -> Result<(), Error> {
        // @Todo @XXX: don't clone
        for (path, mut statements) in self.parsed.clone() {
            // Start the timer to measure how long resolution takes.
            let start_time = Instant::now();

            let mut module = Module {
                path,
                ..Module::default()
            };

            let mut precs = BTreeMap::new();

            // Sort the statements so they're processed in the correct order.
            //
            // @Note @Important:
            // This relies on the (derived!) impl PartialOrd for Statement.
            {
                // @Note @Performance:
                // This could be really slow on big programs.
                // For now we just time it and log,
                // but one day we might need to optimise this a bit more carefully.
                let sort_time = Instant::now();
                statements.sort();
                log::trace!(
                    log::METRICS,
                    "Statement sort time in resolve: {:?}",
                    sort_time.elapsed()
                );
            }

            // Process all parsed statements,
            // and insert them into the Module (and precs map).
            log::trace!(log::RESOLVE, "Processing parsed statements");
            for stat in statements {
                match stat {
                    // @Todo: do some actual resolution
                    Statement::Import(path, names) => {
                        module.imports.entry(path).or_default().extend(names)
                    }

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

                    Statement::AssignmentWithoutType(mut assign) => {
                        // Modify this assignment to take precedence statements into account.
                        // @Note: we've already processed all the precedence statements,
                        //        because of the sorted processing order.
                        assign.apply(&precs);

                        module
                            .definitions
                            .entry(assign.0.name().clone())
                            .or_default()
                            .assignments
                            .push(assign);
                    }

                    Statement::AssignmentWithType(ts, mut assign) => {
                        // Modify this assignment to take precedence statements into account.
                        // @Note: we've already processed all the precedence statements,
                        //        because of the sorted processing order.
                        assign.apply(&precs);

                        let defn = module
                            .definitions
                            .entry(assign.0.name().clone())
                            .or_default();

                        // If there was already an explicit for this name, that's an error.
                        if let Some(previous_ts) = defn.explicit_type.replace(ts.clone()) {
                            return Err(Error::MultipleTypes(
                                assign.0.name().clone(),
                                // @Cleanup: don't have this dodgy whitespace
                                format!("\n    {:?}\n    {:?}", ts, previous_ts),
                            ));
                        }

                        defn.assignments.push(assign);
                    }

                    Statement::TypeAnnotation(name, ts) => {
                        // @Future @TypeBinops: handle precedence here as well

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

                    Statement::TypeDefinition(type_defn) => {
                        if let Some(first_defn) = module
                            .type_definitions
                            .insert(type_defn.name.clone(), type_defn)
                        {
                            return Err(Error::MultipleTypeDefinitions(first_defn.name));
                        }
                    }

                    Statement::ForeignExport(lua_lhs, expr) => {
                        module.foreign_exports.push((lua_lhs, expr))
                    }
                }
            }

            log::info!(
                log::METRICS,
                "Resolution completed, {:?} elapsed",
                start_time.elapsed()
            );

            self.modules.insert(path, module);
        }

        Ok(())
    }
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
