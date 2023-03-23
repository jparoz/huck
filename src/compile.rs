use std::collections::BTreeMap;
use std::mem;

use crate::ast::Module;
use crate::name::{self, ModulePath, ResolvedName};
use crate::parse::parse;
use crate::precedence::{ApplyPrecedence, Precedence};
use crate::typecheck::typecheck;
use crate::{codegen, dependencies, ir};

use crate::error::Error as HuckError;

/// Does every step necessary to take the added modules to compiled state.
/// Takes a `Vec` of `&'static str`s containing Huck code,
/// and returns a `Vec` of corresponding `String`s containing compiled Lua code.
//
// @Future: we could incrementally process modules somehow,
// rather than just having this monolithic all-or-nothing compile step.
pub fn compile(huck_srcs: Vec<&'static str>) -> Result<Vec<(ModulePath, String)>, HuckError> {
    // Parse all the files
    let mut parsed_modules = BTreeMap::new();
    for src in huck_srcs {
        let (module_path, statements) = parse(src)?;

        // Post-parse processing
        let module = Module::from_statements(module_path, statements)?;

        parsed_modules.insert(module_path, module);
    }

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
    let mut lua_outputs = Vec::new();
    for (module_path, module) in ir_modules {
        let lua = codegen::generate(
            module,
            generation_orders
                .remove(&module_path)
                .expect("should have found a generation order during dependency resolution"),
        );

        lua_outputs.push((module_path, lua));
    }
    Ok(lua_outputs)
}
