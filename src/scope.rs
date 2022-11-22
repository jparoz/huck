use std::collections::BTreeMap;

use crate::ast::{Assignment, Definition, Name};
use crate::types::TypeScheme;

#[derive(Debug)]
pub struct TypedDefinition<'file> {
    pub type_scheme: TypeScheme,
    pub definition: Definition<'file>,
}

impl<'file> TypedDefinition<'file> {
    pub fn new(type_scheme: TypeScheme, assignments: Vec<Assignment<'file>>) -> Self {
        TypedDefinition {
            type_scheme,
            definition: assignments,
        }
    }
}

#[derive(Debug)]
pub struct Scope<'file> {
    pub definitions: BTreeMap<Name, TypedDefinition<'file>>,
}

impl<'file> Scope<'file> {
    pub fn new() -> Self {
        Scope {
            definitions: BTreeMap::new(),
        }
    }
}
