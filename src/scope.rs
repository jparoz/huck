use std::collections::HashMap;

use crate::ast::Name;
use crate::types::TypeScheme;

#[derive(Debug)]
pub struct Definition {
    type_scheme: TypeScheme,
}

impl Definition {
    pub fn new(type_scheme: TypeScheme) -> Self {
        Definition { type_scheme }
    }
}

#[derive(Debug)]
pub struct Scope {
    definitions: HashMap<Name, Definition>,
}

impl Scope {
    pub fn new() -> Self {
        Scope {
            definitions: HashMap::new(),
        }
    }

    pub fn get(&self, k: &Name) -> Option<&Definition> {
        self.definitions.get(k)
    }

    pub fn insert(&mut self, k: Name, v: Definition) -> Option<Definition> {
        self.definitions.insert(k, v)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Name, &Definition)> {
        self.definitions.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&Name, &mut Definition)> {
        self.definitions.iter_mut()
    }
}
