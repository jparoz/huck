use std::collections::BTreeMap;
use std::mem;

use crate::ast::Module;
use crate::file::{self, FileInfo};
use crate::name::{self, ModulePath, ResolvedName, UnresolvedName};
use crate::parse::parse;
use crate::precedence::{ApplyPrecedence, Precedence};
use crate::typecheck::typecheck;
use crate::{codegen, dependencies, ir};

use crate::error::Error as HuckError;

/// Does every step necessary to take the added modules to compiled state.
/// Takes a `Vec` of [`FileInfo`]s,
/// and returns a `Vec` of ([`FileInfo`], compiled Lua code).
//
// @Future: we could incrementally process modules somehow,
// rather than just having this monolithic all-or-nothing compile step.
pub fn compile(
    input_infos: Vec<FileInfo>,
) -> Result<BTreeMap<ModulePath, (FileInfo, String)>, HuckError> {
    // Record which module originated from which `FileInfo`.
    let mut infos = BTreeMap::new();

    // Parse all the files
    let mut parsed = Vec::new();
    for mut info in input_infos {
        let (module_path, statements) = parse(info.source)?;
        info.module_path = Some(module_path);

        if let Some(existing_info) = infos.insert(module_path, info) {
            Err(file::Error::MultipleModules(
                module_path,
                infos.remove(&module_path).unwrap().input,
                existing_info.input,
            ))?;
        }
        parsed.push((module_path, statements));
    }

    // Post-parse processing
    let mut parsed_modules = parsed
        .into_iter()
        .map(|(path, stats)| Ok((path, Module::from_statements(path, stats)?)))
        .collect::<Result<BTreeMap<ModulePath, Module<UnresolvedName, ()>>, HuckError>>()?;

    // Resolve names
    let mut resolver = name::Resolver::new();

    // Start with the prelude (if it's included)
    let prelude_path = ModulePath("Prelude");
    let mut prelude = None;
    if let Some(unresolved_prelude) = parsed_modules.remove(&prelude_path) {
        prelude = Some(resolver.resolve_module(unresolved_prelude, None)?);
    }

    // Then resolve all other modules.
    for module in parsed_modules.into_values() {
        resolver.resolve_module(module, prelude.clone())?;
    }

    // Check that any qualified names used actually exist.
    let mut resolved_modules = resolver.finish()?;

    // Apply operator precedences
    let precs: BTreeMap<ResolvedName, Precedence> = resolved_modules
        .values_mut()
        .flat_map(|module| mem::take(&mut module.precedences).into_iter())
        .collect();
    for module in resolved_modules.values_mut() {
        module.apply(&precs);
    }

    // Dependency resolution
    let mut generation_orders = dependencies::resolve(&resolved_modules)?;

    // Typecheck
    let typechecked_modules = typecheck(resolved_modules)?;

    // Convert from ast to ir
    let mut ir_modules: BTreeMap<ModulePath, ir::Module> = BTreeMap::new();
    for (module_path, module) in typechecked_modules.iter() {
        ir_modules.insert(*module_path, ir::Module::from(module.clone()));
    }

    // Generate code
    let mut generated = BTreeMap::new();
    for (module_path, module) in ir_modules {
        let lua = codegen::generate(
            module,
            generation_orders
                .remove(&module_path)
                .expect("should have found a generation order during dependency resolution"),
        );
        generated.insert(
            module_path,
            (
                infos
                    .remove(&module_path)
                    .expect("file info should exist for a generated file"),
                lua,
            ),
        );
    }
    Ok(generated)
}
