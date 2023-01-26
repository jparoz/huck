use std::collections::BTreeMap;

use crate::ast::{Definition, Expr, ForeignName, ModulePath};
use crate::resolve::ResolvedName;
use crate::types::{Type, TypeDefinition, TypeScheme};

/// This is the structure which represents a module
/// which has been typechecked and processed
/// to the point where it can have code generated from it.
/// If there are any optional steps in the compilation process,
/// they will probably take the rough shape of
/// a function: `GeneratableModule -> GeneratableModule`.
// @Todo: Use the same base struct as ast::Module
#[derive(Debug)]
pub struct GeneratableModule {
    pub path: ModulePath,
    pub definitions: BTreeMap<ResolvedName, (Type, Definition<ResolvedName>)>,
    pub type_definitions: BTreeMap<ResolvedName, TypeDefinition>,
    pub constructors: BTreeMap<ResolvedName, Type>,

    /// Mapping from a name to its originating module's path and file stem.
    pub imports: BTreeMap<ResolvedName, (ModulePath, String)>,

    /// Mapping from a name to its originating foreign module's require string,
    /// the corresponding Lua name,
    /// and the type scheme given at the import.
    pub foreign_imports: BTreeMap<ResolvedName, (&'static str, ForeignName, TypeScheme)>,

    /// Vec of Lua assignments to make at the end of the module.
    pub foreign_exports: Vec<(&'static str, Expr<ResolvedName>)>,
}

impl GeneratableModule {
    pub fn new(module_path: ModulePath) -> GeneratableModule {
        GeneratableModule {
            path: module_path,
            definitions: BTreeMap::new(),
            type_definitions: BTreeMap::new(),
            constructors: BTreeMap::new(),
            imports: BTreeMap::new(),
            foreign_imports: BTreeMap::new(),
            foreign_exports: Vec::new(),
        }
    }

    pub fn contains(&self, name: &ResolvedName) -> bool {
        self.definitions.contains_key(name)
            || self.constructors.contains_key(name)
            || self.imports.contains_key(name)
            || self.foreign_imports.contains_key(name)
    }

    pub fn get_type(&self, name: &ResolvedName) -> Option<Type> {
        self.constructors
            .get(name)
            .cloned()
            .or_else(|| self.definitions.get(name).map(|(typ, _)| typ.clone()))
    }

    pub fn get_path(&self, name: &ResolvedName) -> Option<ModulePath> {
        self.imports
            .get(name)
            .map(|(path, _)| *path)
            .or_else(|| self.definitions.get(name).map(|_| self.path))
            .or_else(|| self.constructors.get(name).map(|_| self.path))
    }
}
