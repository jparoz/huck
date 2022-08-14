/// An enum representing all possible type errors.
#[derive(Debug)]
pub enum Error {
    CouldNotUnify,
    InfiniteType,
}
