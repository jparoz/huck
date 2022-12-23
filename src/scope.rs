use std::collections::BTreeMap;

use crate::ast::{Definition, Name};
use crate::types::{TypeDefinition, TypeScheme};

// @Todo @Cleanup: rename this, or sort out something better and less confusing
#[derive(Debug, Clone)]
pub struct TypedDefinition<'file> {
    pub type_scheme: TypeScheme,
    pub definition: Definition<'file>,
}

#[derive(Debug)]
pub struct Scope<'file> {
    pub definitions: BTreeMap<Name, TypedDefinition<'file>>,
    pub type_definitions: BTreeMap<Name, TypeDefinition>,
}

impl<'file> Scope<'file> {
    pub fn new() -> Self {
        Scope {
            definitions: BTreeMap::new(),
            type_definitions: BTreeMap::new(),
        }
    }

    pub fn contains(&self, name: &Name) -> bool {
        self.definitions.contains_key(name) || self.type_definitions.contains_key(name)
    }
}
