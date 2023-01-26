pub mod lua;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Write error: {0}")]
    Write(#[from] std::fmt::Error),

    #[error("Incorrect number of function arguments in definition of function `{0}`")]
    IncorrectArgumentCount(String),

    // @Errors: properly print the Vec
    // @Fixme: currently the Vec contains extra names (see its generation site), hence "within".
    #[error("Cyclic dependency detected within the following definitions: {0:?}")]
    CyclicDependency(Vec<crate::resolve::ResolvedName>),
}
