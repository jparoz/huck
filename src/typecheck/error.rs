use crate::name::ResolvedName;
use crate::types::Type;
use crate::utils::debug_iter;

use super::Constraint;

/// An enum representing all possible type errors.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Could not unify type '{0}' with type '{1}'")]
    CouldNotUnify(Type, Type),

    #[error("Could not unify type '{0}' with type '{1}' (recursive type)")]
    CouldNotUnifyRecursive(Type, Type),

    // @Errors: this advice isn't super helpful
    #[error(
        "Could not solve the following type constraints: {}\n\
         Maybe try adding some more specific types to recursive definitions.",
        debug_iter(.0.iter())
    )]
    CouldNotSolveTypeConstraints(Vec<Constraint>),

    // @Errors: this name/message is probably not that helpful
    #[error("Usage of type `{0}` with incorrect arity {1} (actual arity {2})")]
    IncorrectArity(ResolvedName, usize, usize),
}
