use crate::name::ResolvedName;
use crate::utils::display_iter;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    // @Errors: this should have a hint of how to fix,
    // and mention that this doesn't apply to functions/lazy values
    #[error(
        "Cyclic dependency detected in the following definitions: {}",
        display_iter(.0.iter())
    )]
    CyclicDependency(Vec<ResolvedName>),
}
