use std::collections::BTreeMap;
use std::fmt::{self, Display};
use std::time::Instant;

use crate::name::UnresolvedName;
use crate::{ast, log, parse};

/// A `Module` is a dictionary of Huck function definitions.
/// This is produced from a `Vec<Statement>`,
/// by using the parsed precedence rules to reshape the AST,
/// and collecting statements referring to the same function
/// into a single `Definition` struct for each function name.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Module<Name> {
    pub path: ModulePath,
    pub definitions: BTreeMap<Name, ast::Definition<Name>>,

    pub type_definitions: BTreeMap<Name, ast::TypeDefinition<Name>>,

    /// Note that all the members of this field can also be found
    /// in the values of the `type_definitions` field.
    pub constructors: BTreeMap<Name, Vec<ast::TypeTerm<Name>>>,

    pub imports: BTreeMap<ModulePath, Vec<Name>>,
    pub foreign_imports: BTreeMap<&'static str, Vec<ast::ForeignImportItem<Name>>>,
    pub foreign_exports: Vec<(&'static str, ast::Expr<Name>)>,
}

impl<Name> Module<Name> {
    pub fn new(path: ModulePath) -> Self {
        Self {
            path,
            definitions: BTreeMap::new(),
            type_definitions: BTreeMap::new(),
            constructors: BTreeMap::new(),
            imports: BTreeMap::new(),
            foreign_imports: BTreeMap::new(),
            foreign_exports: Vec::new(),
        }
    }
}

impl Module<UnresolvedName> {
    /// Takes the `Vec<Statement>` from parsing
    /// and turns it into a `Module`.
    pub fn from_statements(
        path: ModulePath,
        statements: Vec<ast::Statement<UnresolvedName>>,
        // @Cleanup: maybe not parse error
    ) -> Result<Self, parse::Error> {
        // Start the timer to measure how long post-parsing takes.
        let start_time = Instant::now();

        let mut module = Module::new(path);

        // Process all parsed statements,
        // and insert them into the Module.
        log::trace!(log::RESOLVE, "Processing parsed statements");
        for stat in statements {
            match stat {
                ast::Statement::Import(path, names) => {
                    module.imports.entry(path).or_default().extend(names)
                }

                ast::Statement::QualifiedImport(path) => {
                    module.imports.entry(path).or_default();
                }

                ast::Statement::ForeignImport(require_string, import_items) => module
                    .foreign_imports
                    .entry(require_string)
                    .or_default()
                    .extend(import_items.into_iter()),

                ast::Statement::Precedence(name, prec) => {
                    // If there was already a precedence for this name, that's an error.
                    if let Some(previous_prec) = module
                        .definitions
                        .entry(name)
                        .or_default()
                        .precedence
                        .replace(prec)
                    {
                        return Err(parse::Error::MultiplePrecs(name, prec, previous_prec));
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
                        return Err(parse::Error::MultipleTypes(
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
                        return Err(parse::Error::MultipleTypes(
                            name,
                            // @Cleanup @Errors: don't have this dodgy whitespace
                            format!("\n    {:?}\n    {:?}", ts, previous_ts),
                        ));
                    }
                }

                ast::Statement::TypeDefinition(type_defn) => {
                    for (constr, types) in type_defn.constructors.iter().cloned() {
                        if module.constructors.insert(constr, types).is_some() {
                            return Err(parse::Error::MultipleTypeConstructors(constr));
                        }
                    }

                    if let Some(first_defn) =
                        module.type_definitions.insert(type_defn.name, type_defn)
                    {
                        return Err(parse::Error::MultipleTypeDefinitions(first_defn.name));
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

        Ok(module)
    }
}

/// A ModulePath is a path to a Huck module, as defined within that module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModulePath(pub &'static str);

impl Display for ModulePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
