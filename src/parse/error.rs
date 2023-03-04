use crate::name::UnresolvedName;
use crate::precedence::Precedence;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    // @Errors: this should be caught as more specific errors, then this variant deleted
    #[error("Nom error: {0}")]
    Nom(#[from] nom::error::Error<&'static str>),

    // @Errors: this should be caught as more specific errors, then this variant deleted
    #[error("Leftover input: {0}")]
    Leftover(String),

    // @Cleanup @Errors: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple precedence declarations found for `{0}`:\n    {1:?}\n    {2:?}")]
    MultiplePrecs(UnresolvedName, Precedence, Precedence),

    // @Cleanup @Errors: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple explicit type annotations found for `{0}`:{1}")]
    MultipleTypeAnnotations(UnresolvedName, String),

    // @Cleanup @Errors: this should print the source locations of the two definitions
    #[error("Multiple type definitions with the same name ({0})")]
    MultipleTypeDefinitions(UnresolvedName),

    // @Cleanup @Errors: this should print the source locations of the two definitions
    #[error("Multiple type constructors with the same name `{0}` from types: `{1}`, `{2}`")]
    MultipleTypeConstructors(UnresolvedName, UnresolvedName, UnresolvedName),

    // @Errors: this should print the locations of the multiple unconditionals
    #[error("Multiple unconditional branches found in definition of `{0}`")]
    MultipleUnconditionals(UnresolvedName),

    // @Errors: this should print the thing which caused a Definition to be made
    #[error("No assignment defining the name `{0}`")]
    MissingAssignment(UnresolvedName),

    // @Errors: this should print the assignment with the wrong number of args
    #[error("Incorrect number of function arguments in definition of `{0}`")]
    IncorrectArgumentCount(UnresolvedName),
}
