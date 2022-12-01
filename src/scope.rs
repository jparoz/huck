use std::collections::BTreeMap;

use crate::ast::{Definition, Name};
use crate::types::TypeScheme;

#[derive(Debug, Clone)]
pub struct TypedDefinition<'file> {
    pub type_scheme: TypeScheme,
    pub definition: Definition<'file>,
}

impl<'file> TypedDefinition<'file> {
    pub fn new(type_scheme: TypeScheme, definition: Definition<'file>) -> Self {
        TypedDefinition {
            type_scheme,
            definition,
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
