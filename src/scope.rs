use std::collections::HashMap;

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
    definitions: HashMap<Name, TypedDefinition<'file>>,
}

impl<'file> Scope<'file> {
    pub fn new() -> Self {
        Scope {
            definitions: HashMap::new(),
        }
    }

    pub fn get(&self, k: &Name) -> Option<&TypedDefinition> {
        self.definitions.get(k)
    }

    pub fn insert(&mut self, k: Name, v: TypedDefinition<'file>) -> Option<TypedDefinition<'file>> {
        self.definitions.insert(k, v)
    }

    pub fn contains_key(&self, k: &Name) -> bool {
        self.definitions.contains_key(k)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Name, &TypedDefinition)> {
        self.definitions.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&Name, &mut TypedDefinition<'file>)> {
        self.definitions.iter_mut()
    }
}
