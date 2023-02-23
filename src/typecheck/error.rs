use crate::name::ResolvedName;
use crate::types::Type;
use crate::utils::display_iter;

use super::ConstraintSet;

/// An enum representing all possible type errors.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error(
        "Could not unify type '{0}' with type '{1}', \
         while unifying type '{2}' with type '{3}'"
    )]
    CouldNotUnify(Type, Type, Type, Type),

    #[error(
        "Could not unify type '{0}' with type '{1}' (recursive type), \
         while unifying type '{2}' with type '{3}'"
    )]
    CouldNotUnifyRecursive(Type, Type, Type, Type),

    #[error(
        "Inferred type '{0}' could not be unified with explicit type '{1}', \
         while unifying type '{2}' with explicit type '{3}'"
    )]
    CouldNotUnifyExplicit(Type, Type, Type, Type),

    // @Errors: this advice isn't super helpful
    #[error(
        "Could not solve the following type constraints:\n\
         {0:?}\n\
         Maybe try adding some more specific types to recursive definitions."
    )]
    CouldNotSolveTypeConstraints(ConstraintSet),

    // @Errors: this name/message is probably not that helpful
    #[error("Usage of type `{0}` with incorrect arity {1} (actual arity {2})")]
    IncorrectArity(ResolvedName, usize, usize),

    // @Errors: this name/message is probably not that helpful
    #[error("Type variable `{0}` is used with multiple different arities: {}",
        display_iter(.1.iter())
        )]
    IncorrectArityTypeVariable(ResolvedName, Vec<usize>),
}
