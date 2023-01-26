use std::collections::BTreeMap;
use std::time::Instant;

use crate::context::Context;
use crate::{ast, log};

impl Context {
    /// Takes the `Vec<Statement>` from parsing
    /// and turns it into a more coherent data structure.
    pub fn post_parse(
        &mut self,
        parsed: BTreeMap<ast::ModulePath, Vec<ast::Statement<ast::UnresolvedName>>>,
        // @Cleanup: not ast::Module (move to a new Rust mod called something like `module`)
    ) -> Result<BTreeMap<ast::ModulePath, ast::Module<ast::UnresolvedName>>, super::Error> {
        let mut modules = BTreeMap::new();

        for (path, mut statements) in parsed {
            // Start the timer to measure how long resolution takes.
            let start_time = Instant::now();

            let mut module = ast::Module::new(path);

            let mut precs = BTreeMap::new();

            // Sort the statements so they're processed in the correct order.
            // @Note @Performance:
            // This could be really slow on big programs.
            // For now we just time it and log,
            // but one day we might need to optimise this a bit more carefully.
            let sort_time = Instant::now();
            // @Note @Important:
            // This relies on the (derived!) impl PartialOrd for Statement.
            statements.sort();
            log::trace!(
                log::METRICS,
                "Statement sort time in resolve: {:?}",
                sort_time.elapsed()
            );

            // Process all parsed statements,
            // and insert them into the Module (and precs map).
            log::trace!(log::RESOLVE, "Processing parsed statements");
            for stat in statements {
                match stat {
                    // @Todo: do some actual resolution
                    ast::Statement::Import(path, names) => {
                        module.imports.entry(path).or_default().extend(names)
                    }

                    ast::Statement::QualifiedImport(path) => {
                        module.imports.entry(path).or_default();
                    }

                    // @Todo: do some actual resolution
                    ast::Statement::ForeignImport(require_string, import_items) => module
                        .foreign_imports
                        .entry(require_string)
                        .or_default()
                        .extend(import_items.into_iter().map(|item| match item {
                            ast::ForeignImportItem::SameName(name, ts) => {
                                (ast::ForeignName(name), ast::UnresolvedName::Ident(name), ts)
                            }
                            ast::ForeignImportItem::Rename(lua_name, name, ts) => {
                                (lua_name, name, ts)
                            }
                        })),

                    ast::Statement::Precedence(name, prec) => {
                        precs.insert(name, prec);
                        // If there was already a precedence for this name, that's an error.
                        if let Some(previous_prec) = module
                            .definitions
                            .entry(name)
                            .or_default()
                            .precedence
                            .replace(prec)
                        {
                            return Err(super::Error::MultiplePrecs(name, prec, previous_prec));
                        }
                    }

                    ast::Statement::AssignmentWithoutType(assign) => {
                        module
                            .definitions
                            .entry(*assign.0.name())
                            .or_default()
                            .assignments
                            .push(assign);
                    }

                    ast::Statement::AssignmentWithType(ts, assign) => {
                        let defn = module.definitions.entry(*assign.0.name()).or_default();

                        // If there was already an explicit for this name, that's an error.
                        if let Some(previous_ts) = defn.explicit_type.replace(ts.clone()) {
                            return Err(super::Error::MultipleTypes(
                                *assign.0.name(),
                                // @Cleanup: don't have this dodgy whitespace
                                format!("\n    {:?}\n    {:?}", ts, previous_ts),
                            ));
                        }

                        defn.assignments.push(assign);
                    }

                    ast::Statement::TypeAnnotation(name, ts) => {
                        // @Future @TypeBinops: handle precedence here as well

                        // If there was already an explicit for this name, that's an error.
                        if let Some(previous_ts) = module
                            .definitions
                            .entry(name)
                            .or_default()
                            .explicit_type
                            .replace(ts.clone())
                        {
                            return Err(super::Error::MultipleTypes(
                                name,
                                // @Cleanup @Errors: don't have this dodgy whitespace
                                format!("\n    {:?}\n    {:?}", ts, previous_ts),
                            ));
                        }
                    }

                    ast::Statement::TypeDefinition(type_defn) => {
                        if let Some(first_defn) =
                            module.type_definitions.insert(type_defn.name, type_defn)
                        {
                            return Err(super::Error::MultipleTypeDefinitions(first_defn.name));
                        }
                    }

                    ast::Statement::ForeignExport(lua_lhs, expr) => {
                        module.foreign_exports.push((lua_lhs, expr))
                    }
                }
            }

            log::info!(
                log::METRICS,
                "Post-parsing completed, {:?} elapsed",
                start_time.elapsed()
            );

            modules.insert(path, module);
        }

        Ok(modules)
    }
}
