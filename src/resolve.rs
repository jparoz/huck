use std::collections::BTreeMap;
use std::time::Instant;

use crate::context::Context;
use crate::parse::precedence::{ApplyPrecedence, Precedence};
use crate::{ast, log};

/// A `ResolvedName` is a unique token, used in the compiler to uniquely identify a value.
/// After name resolution:
/// all names have been confirmed to exist,
/// and all references to a function have the same `ResolvedName`,
/// no matter where the references appear.
pub struct ResolvedName {
    source: ImportSource,
    ident: &'static str,
}

/// An `ImportSource` describes where to find an identifier, whether it's a Huck or foreign import.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum ImportSource {
    /// From a Huck module
    Module(ast::ModulePath),
    /// From a foreign (Lua) module
    Foreign {
        /// Includes the quotation marks
        require: &'static str,
        foreign_name: ast::ForeignName,
    },
    /// From e.g. a let binding
    /// Contains a unique ID,
    /// so that we can tell apart identically-named but different `ResolvedName`s.
    Local(usize),
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Identifier not in scope (module {0}): {1}")]
    NotInScope(ast::ModulePath, ast::Name),

    #[error("Module `{0}` doesn't exist")]
    NonexistentModule(ast::ModulePath),

    #[error("Identifier `{1}` doesn't exist in module `{0}`")]
    NonexistentImport(ast::ModulePath, ast::Name),

    // @Cleanup @Errors: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple precedence declarations found for `{0}`:\n    {1:?}\n    {2:?}")]
    MultiplePrecs(ast::Name, Precedence, Precedence),

    // @Cleanup @Errors: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple explicit type annotations found for `{0}`:{1}")]
    MultipleTypes(ast::Name, String),

    // @Cleanup @Errors: this should print the source locations of the two definitions
    #[error("Multiple type definitions with the same name ({0})")]
    MultipleTypeDefinitions(ast::Name),
}
