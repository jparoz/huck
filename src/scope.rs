use std::collections::HashMap;
use std::fmt;

use crate::ast::Name;
use crate::types::TypeScheme;

#[derive(Debug)]
pub struct Scope {
    identifiers: HashMap<Name, TypeScheme>,
}

impl Scope {
    pub fn new() -> Self {
        Scope {
            identifiers: HashMap::new(),
        }
    }

    pub fn get(&self, k: &Name) -> Option<&TypeScheme> {
        self.identifiers.get(k)
    }

    pub fn insert(&mut self, k: Name, v: TypeScheme) -> Option<TypeScheme> {
        self.identifiers.insert(k, v)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Name, &TypeScheme)> {
        self.identifiers.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&Name, &mut TypeScheme)> {
        self.identifiers.iter_mut()
    }
}

impl fmt::Display for Scope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Scope:")?;
        for (name, type_scheme) in self.identifiers.iter() {
            writeln!(f, "    {} : {}", name, type_scheme)?;
        }
        Ok(())
    }
}
