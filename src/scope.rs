use std::collections::BTreeMap;

use crate::ast::{Definition, Name};
use crate::types::{Type, TypeDefinition};

#[derive(Debug, Default)]
pub struct Scope<'file> {
    pub definitions: BTreeMap<Name, (Type, Definition<'file>)>,

    pub type_definitions: BTreeMap<Name, TypeDefinition>,

    pub constructors: BTreeMap<Name, Type>,
}

impl<'file> Scope<'file> {
    pub fn contains(&self, name: &Name) -> bool {
        self.definitions.contains_key(name) || self.constructors.contains_key(name)
    }

    pub fn get_type(&self, name: &Name) -> Option<Type> {
        self.constructors
            .get(name)
            .cloned()
            .or_else(|| self.definitions.get(name).map(|(typ, _)| typ.clone()))
    }
}
