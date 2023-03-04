use std::time::Instant;

use crate::name::{ModulePath, UnresolvedName};
use crate::{ast, log};

use super::Error;

impl ast::Module<UnresolvedName, ()> {
    /// Takes the `Vec<ast::Statement>` from parsing
    /// and turns it into a [`ast::Module`]
    /// as well as a map of [`Precedence`](crate::precedence::Precedence)s.
    pub fn from_statements(
        path: ModulePath,
        statements: Vec<ast::Statement<UnresolvedName, ()>>,
        // @Cleanup: maybe not parse error
    ) -> Result<Self, Error> {
        // Start the timer to measure how long post-parsing takes.
        let start_time = Instant::now();

        let mut module = ast::Module::new(path);

        // Process all parsed statements,
        // and insert them into the ast::Module.
        log::trace!(log::RESOLVE, "Processing parsed statements");
        for stat in statements {
            match stat {
                ast::Statement::Import(path, names) => {
                    module.imports.entry(path).or_default().extend(names)
                }

                ast::Statement::ForeignImport(require_string, import_items) => module
                    .foreign_imports
                    .entry(require_string)
                    .or_default()
                    .extend(import_items.into_iter()),

                ast::Statement::Precedence(name, prec) => {
                    // If there was already a precedence for this name, that's an error.
                    if let Some(previous_prec) = module.precedences.insert(name, prec) {
                        return Err(Error::MultiplePrecs(name, prec, previous_prec));
                    }
                }

                // @DRY @Cleanup: with/without type
                ast::Statement::AssignmentWithoutType(assign) => {
                    // Get the existing definition (if any).
                    let defn = module.definitions.entry(*assign.0.name()).or_default();

                    // Check that each assignment has the same number of arguments.
                    let num_args = assign.0.arg_count();
                    if defn
                        .assignments
                        .get(0)
                        .map(|assign| assign.0.arg_count() != num_args)
                        .unwrap_or(false)
                    {
                        return Err(Error::IncorrectArgumentCount(*assign.0.name()));
                    }

                    // Add the new assignment.
                    defn.assignments.push(assign);
                }

                // @DRY @Cleanup: with/without type
                ast::Statement::AssignmentWithType(ts, assign) => {
                    // Get the existing definition (if any).
                    let defn = module.definitions.entry(*assign.0.name()).or_default();

                    // If there was already an explicit for this name, that's an error.
                    if let Some(previous_ts) = defn.explicit_type.replace(ts.clone()) {
                        return Err(Error::MultipleTypeAnnotations(
                            *assign.0.name(),
                            // @Cleanup: don't have this dodgy whitespace
                            format!("\n    {:?}\n    {:?}", ts, previous_ts),
                        ));
                    }

                    // Check that each assignment has the same number of arguments.
                    let num_args = assign.0.arg_count();
                    if defn
                        .assignments
                        .get(0)
                        .map(|assign| assign.0.arg_count() != num_args)
                        .unwrap_or(false)
                    {
                        return Err(Error::IncorrectArgumentCount(*assign.0.name()));
                    }

                    // Add the new assignment.
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
                        return Err(Error::MultipleTypeAnnotations(
                            name,
                            // @Cleanup @Errors: don't have this dodgy whitespace
                            format!("\n    {:?}\n    {:?}", ts, previous_ts),
                        ));
                    }
                }

                ast::Statement::TypeDefinition(type_defn) => {
                    for constr_name in type_defn.constructors.keys() {
                        if let Some(existing_type_name) =
                            module.constructors.insert(*constr_name, type_defn.name)
                        {
                            return Err(Error::MultipleTypeConstructors(
                                *constr_name,
                                existing_type_name,
                                type_defn.name,
                            ));
                        }
                    }

                    if let Some(first_defn) =
                        module.type_definitions.insert(type_defn.name, type_defn)
                    {
                        return Err(Error::MultipleTypeDefinitions(first_defn.name));
                    }
                }

                ast::Statement::ForeignExport(lua_lhs, expr) => {
                    module.foreign_exports.push((lua_lhs, expr))
                }
            }
        }

        // Do some checks on the Definitions
        for (name, defn) in module.definitions.iter() {
            // Check that this Definition has at least one assignment
            if defn.assignments.is_empty() {
                return Err(Error::MissingAssignment(*name));
            }

            // Check that this Definition only has up to one unconditional branch
            if defn.assignments.len() > 1 {
                // Because we're in here, we have more than one branch.
                // Now we have to ensure that only one of them is unconditional.

                // If it defines a value (i.e. doesn't take arguments)
                if defn.assignments[0].0.arg_count() == 0 {
                    // This is bad, because a non-function can't have multiple values.
                    return Err(Error::MultipleUnconditionals(*name));
                }

                let mut found_unconditional = false;
                for (lhs, _) in defn.assignments.iter() {
                    if lhs.is_unconditional() {
                        // If we already found an unconditional, that's bad.
                        if found_unconditional {
                            return Err(Error::MultipleUnconditionals(*name));
                        }

                        found_unconditional = true;
                    }
                }
            }
        }

        log::info!(
            log::METRICS,
            "Post-parsing module {path} completed, {time:?} elapsed",
            time = start_time.elapsed(),
            path = module.path,
        );

        Ok(module)
    }
}
