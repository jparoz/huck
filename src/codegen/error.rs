use crate::name::ResolvedName;

// @Errors: All these errors should ideally be caught before IR and codegen stages
#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Write error: {0}")]
    Write(#[from] std::fmt::Error),

    // @Errors: properly print the Vec
    // @Fixme: currently the Vec contains extra names (see its generation site), hence "within".
    #[error("Cyclic dependency detected within the following definitions: {0:?}")]
    CyclicDependency(Vec<ResolvedName>),
}
