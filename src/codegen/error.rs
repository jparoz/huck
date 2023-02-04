use crate::name::ResolvedName;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Write error: {0}")]
    Write(#[from] std::fmt::Error),

    // @Errors: properly print the Vec
    // @Fixme: currently the Vec contains extra names (see its generation site), hence "within".
    #[error("Cyclic dependency detected within the following definitions: {0:?}")]
    CyclicDependency(Vec<ResolvedName>),

    // @Errors: get the name of the duplicated definition
    #[error("Duplicate definitions found! Values: `{0:?}`")]
    DuplicateUnconditional(Vec<crate::ast::Expr<ResolvedName>>),
}
