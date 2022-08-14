/// An enum representing all possible type errors.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Could not unify TODO")]
    CouldNotUnify,
    #[error("Infinite type TODO")]
    InfiniteType,
}
