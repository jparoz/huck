use std::collections::BTreeMap;

use crate::ast::{Definition, Expr, ForeignName, ModulePath, Name};
use crate::types::{Type, TypeDefinition, TypeScheme};

/// This is the structure which represents a module
/// which has been typechecked and processed
/// to the point where it can have code generated from it.
/// If there are any optional steps in the compilation process,
/// they will probably take the rough shape of
/// a function: `GeneratableModule -> GeneratableModule`.
#[derive(Debug, Default)]
pub struct GeneratableModule {
    pub path: ModulePath,
    pub definitions: BTreeMap<Name, (Type, Definition)>,
    pub type_definitions: BTreeMap<Name, TypeDefinition>,
    pub constructors: BTreeMap<Name, Type>,

    /// Mapping from a name to its originating module's path and file stem.
    pub imports: BTreeMap<Name, (ModulePath, String)>,

    /// Mapping from a name to its originating foreign module's require string,
    /// the corresponding Lua name,
    /// and the type scheme given at the import.
    pub foreign_imports: BTreeMap<Name, (&'static str, ForeignName, TypeScheme)>,

    /// Vec of Lua assignments to make at the end of the module.
    pub foreign_exports: Vec<(&'static str, Expr)>,
}

impl GeneratableModule {
    pub fn new(module_path: ModulePath) -> GeneratableModule {
        GeneratableModule {
            path: module_path,
            ..GeneratableModule::default()
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

    pub fn get_path(&self, name: &Name) -> Option<ModulePath> {
        self.imports
            .get(name)
            .map(|(path, _)| *path)
            .or_else(|| self.definitions.get(name).map(|_| self.path))
            .or_else(|| self.constructors.get(name).map(|_| self.path))
    }
}
