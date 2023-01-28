use std::collections::BTreeMap;

use crate::ast;
use crate::module::ModulePath;
use crate::name::ResolvedName;
use crate::types::{self, Type, TypeScheme};

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
    pub definitions: BTreeMap<ResolvedName, (Type, ast::Definition<ResolvedName>)>,
    pub type_definitions: BTreeMap<ResolvedName, types::TypeDefinition>,
    pub constructors: BTreeMap<ResolvedName, Type>,

    pub imports: BTreeMap<ModulePath, Vec<ResolvedName>>,

    /// Mapping from a foreign module's require string
    /// to information necessary to generate the import.
    //
    // @Todo:
    // pub foreign_imports:
    //     BTreeMap<&'static str, Vec<ast::ForeignImportItem<Name, types::TypeScheme>>>,
    pub foreign_imports: BTreeMap<&'static str, Vec<(ast::ForeignName, ResolvedName, TypeScheme)>>,
    /// Vec of Lua assignments to make at the end of the module.
    pub foreign_exports: Vec<(&'static str, ast::Expr<ResolvedName>)>,
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

    pub fn get_type(&self, name: &ResolvedName) -> Option<Type> {
        self.constructors
            .get(name)
            .cloned()
            .or_else(|| self.definitions.get(name).map(|(typ, _)| typ.clone()))
    }
}
