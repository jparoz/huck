use std::collections::BTreeMap;
use std::fmt::{self, Display};

use crate::ast;

/// A Module is a dictionary of Huck function definitions.
/// This is produced from a Vec<Statement>,
/// by using the parsed precedence rules to reshape the AST,
/// and collecting statements referring to the same function
/// into a single Definition struct for each function name.
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

/// A ModulePath is a path to a Huck module, as defined within that module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModulePath(pub &'static str);

impl Display for ModulePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
