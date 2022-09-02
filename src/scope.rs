use std::collections::HashMap;

use crate::ast::{Assignment, Name};
use crate::types::TypeScheme;

#[derive(Debug)]
pub struct Definition<'file> {
    pub type_scheme: TypeScheme,
    pub assignments: Vec<Assignment<'file>>,
}

impl<'file> Definition<'file> {
    pub fn new(type_scheme: TypeScheme, assignments: Vec<Assignment<'file>>) -> Self {
        Definition {
            type_scheme,
            assignments,
        }
    }
}

#[derive(Debug)]
pub struct Scope<'file> {
    definitions: HashMap<Name, Definition<'file>>,
}

impl<'file> Scope<'file> {
    pub fn new() -> Self {
        Scope {
            definitions: HashMap::new(),
        }
    }

    pub fn get(&self, k: &Name) -> Option<&Definition> {
        self.definitions.get(k)
    }

    pub fn insert(&mut self, k: Name, v: Definition<'file>) -> Option<Definition<'file>> {
        self.definitions.insert(k, v)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Name, &Definition)> {
        self.definitions.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&Name, &mut Definition<'file>)> {
        self.definitions.iter_mut()
    }
}
