use crate::name::{ModulePath, UnresolvedName};
use crate::precedence::Precedence;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Nom error: {0}")]
    Nom(#[from] nom::error::Error<&'static str>),

    // @Errors: convert this into a parse error which exposes the underlying cause from Nom
    #[error("Leftover input: {0}")]
    Leftover(String),

    // @XXX @Fixme @Errors: we don't know for sure that the file is stem.hk
    #[error("Multiple modules defined with the same name: `{0}` (files '{1}.hk' and '{2}.hk')")]
    MultipleModules(ModulePath, String, String),

    // @Cleanup @Errors: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple precedence declarations found for `{0}`:\n    {1:?}\n    {2:?}")]
    MultiplePrecs(UnresolvedName, Precedence, Precedence),

    // @Cleanup @Errors: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple explicit type annotations found for `{0}`:{1}")]
    MultipleTypes(UnresolvedName, String),

    // @Cleanup @Errors: this should print the source locations of the two definitions
    #[error("Multiple type definitions with the same name ({0})")]
    MultipleTypeDefinitions(UnresolvedName),

    // @Cleanup @Errors: this should print the source locations of the two definitions
    #[error("Multiple type constructors with the same name ({0})")]
    MultipleTypeConstructors(UnresolvedName),

    // @Errors: this should print the thing which caused a Definition to be made
    #[error("No assignment defining the name `{0}`")]
    MissingAssignment(UnresolvedName),

    #[error("Incorrect number of function arguments in definition of `{0}`")]
    IncorrectArgumentCount(UnresolvedName),
}
