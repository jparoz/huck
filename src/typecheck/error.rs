use crate::{name::ResolvedName, types::Type};

/// An enum representing all possible type errors.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Could not unify type '{0}' with type '{1}'")]
    CouldNotUnify(Type, Type),

    #[error("Could not unify type '{0}' with type '{1}' (recursive type)")]
    CouldNotUnifyRecursive(Type, Type),

    // @Errors: this name/message is probably not that helpful
    #[error("Usage of type `{0}` with incorrect arity {1} (actual arity {2})")]
    IncorrectArity(ResolvedName, usize, usize),
}
