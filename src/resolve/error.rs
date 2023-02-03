use crate::module::ModulePath;
use crate::name::{ResolvedName, Source, UnresolvedName};

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Identifier not in scope (module {0}): {1}")]
    NotInScope(ModulePath, UnresolvedName),

    #[error("Module `{0}` doesn't exist")]
    NonexistentModule(ModulePath),

    #[error("Variable `{0}` doesn't exist in module `{1}`")]
    NonexistentValueName(&'static str, Source),

    #[error("Type `{0}` doesn't exist in module `{1}`")]
    NonexistentTypeName(&'static str, Source),

    #[error("Identifier `{0}` doesn't exist in module `{1}`")]
    NonexistentName(&'static str, Source),

    #[error("Identifier `{0}` is bound twice in the same pattern in `{1}`")]
    DuplicateBinding(UnresolvedName, ResolvedName),

    #[error("Identifier `{0}` is bound twice in the same pattern in a lambda expression")]
    DuplicateBindingLambda(UnresolvedName),
}
