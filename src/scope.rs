use std::collections::BTreeMap;

use crate::ast::{Definition, LuaName, ModulePath, Name};
use crate::types::{Type, TypeDefinition, TypeScheme};

#[derive(Debug, Default)]
pub struct Scope {
    pub module_path: ModulePath,
    pub definitions: BTreeMap<Name, (Type, Definition)>,
    pub type_definitions: BTreeMap<Name, TypeDefinition>,
    pub constructors: BTreeMap<Name, Type>,

    // Mapping from a name to its originating module's path and file stem.
    pub imports: BTreeMap<Name, (ModulePath, String)>,

    // Mapping from a name to its originating foreign module's require string,
    // the corresponding Lua name,
    // and the type scheme given at the import.
    pub foreign_imports: BTreeMap<Name, (&'static str, LuaName, TypeScheme)>,
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
            || self.foreign_imports.contains_key(name)
    }

    pub fn get_type(&self, name: &Name) -> Option<Type> {
        self.constructors
            .get(name)
            .cloned()
            .or_else(|| self.definitions.get(name).map(|(typ, _)| typ.clone()))
    }
}
