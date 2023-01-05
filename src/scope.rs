use std::collections::BTreeMap;

use crate::ast::{Definition, ModulePath, Name};
use crate::types::{Type, TypeDefinition};

#[derive(Debug, Default)]
pub struct Scope {
    pub module_path: ModulePath,
    pub definitions: BTreeMap<Name, (Type, Definition)>,
    pub type_definitions: BTreeMap<Name, TypeDefinition>,
    pub constructors: BTreeMap<Name, Type>,

    // Mapping from a name to its originating module's path and file stem.
    pub imports: BTreeMap<Name, (ModulePath, String)>,
}

impl Scope {
    pub fn new(module_path: ModulePath) -> Scope {
        Scope {
            module_path,
            ..Scope::default()
        }
    }

    pub fn contains(&self, name: &Name) -> bool {
        self.definitions.contains_key(name)
            || self.constructors.contains_key(name)
            || self.imports.contains_key(name)
    }

    pub fn get_type(&self, name: &Name) -> Option<Type> {
        self.constructors
            .get(name)
            .cloned()
            .or_else(|| self.definitions.get(name).map(|(typ, _)| typ.clone()))
    }
}
