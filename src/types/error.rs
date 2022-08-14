use super::Type;

/// An enum representing all possible type errors.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Could not unify type '{0}' with type '{1}'")]
    CouldNotUnify(Type, Type),

    #[error("Could not unify type '{0}' with type '{1}' (recursive type)")]
    CouldNotUnifyRecursive(Type, Type),

    #[error("Infinite type TODO")]
    InfiniteType,
}
