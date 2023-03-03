use crate::name::{Ident, ModulePath, ResolvedName, Source};

#[derive(thiserror::Error, Debug)]
pub enum Error {
    // @Cleanup: duplicate of NonexistentName or something?
    #[error("Identifier not in scope (module {0}): {1}")]
    NotInScope(ModulePath, Ident),

    #[error("Imported `{0}` clashes with `{1}`")]
    ImportClash(ResolvedName, ResolvedName),

    #[error("Module `{0}` doesn't exist")]
    NonexistentModule(ModulePath),

    #[error("Variable `{0}` doesn't exist in module `{1}`")]
    NonexistentValueName(Ident, Source),

    #[error("Type `{0}` doesn't exist in module `{1}`")]
    NonexistentTypeName(Ident, Source),

    #[error("Type constructor `{0}` doesn't exist in module `{1}`")]
    NonexistentConstructorName(Ident, Source),

    #[error("Identifier `{0}` doesn't exist in module `{1}`")]
    NonexistentName(Ident, Source),

    #[error("Identifier `{0}` is bound twice in the same pattern in `{1}`")]
    DuplicateBinding(Ident, ResolvedName),

    #[error("Identifier `{0}` is bound twice in the same pattern in a lambda expression")]
    DuplicateBindingLambda(Ident),
}
