use std::collections::BTreeSet;

use crate::name::ResolvedName;
use crate::utils::display_iter;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error(
        "Cyclic dependency detected in the following definitions: {}",
        display_iter(.0.iter())
    )]
    CyclicDependency(BTreeSet<ResolvedName>),

    #[error(
        "Cyclic dependency detected in the following definitions: {}\n\
         Mutually recursive functions are allowed, \
         but needs an explicit type somewhere in the cycle.",
        display_iter(.0.iter())
    )]
    CyclicDependencyWithoutExplicitType(BTreeSet<ResolvedName>),
}
