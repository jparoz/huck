use std::collections::BTreeMap;
use std::iter;

use crate::error::Error as HuckError;
use crate::module::{Module, ModulePath};
use crate::name::UnresolvedName;
use crate::parse::{self, parse};
use crate::precedence::ApplyPrecedence;
use crate::{codegen, resolve, typecheck};

/// Does every step necessary to take the added modules to compiled state.
/// Takes a `Vec` of (filepath stem, source code)
/// and returns a `Vec` of (filepath stem, compiled Lua code).
/// The filepath stems are given to Lua's `require` function.
//
// @Future: we could incrementally process modules somehow,
// rather than just having this monolithic all-or-nothing compile step.
pub fn compile(input: Vec<(String, &'static str)>) -> Result<Vec<(String, String)>, HuckError> {
    // Record which module originated from which stem.
    // This is used later in code generation.
    let mut module_stems = BTreeMap::new();

    // Parse all the files
    let mut parsed = Vec::new();
    for (stem, src) in input {
        let (module_path, statements) = parse(src)?;

        if let Some(existing_stem) = module_stems.insert(module_path, stem) {
            Err(parse::Error::MultipleModules(
                module_path,
                module_stems[&module_path].clone(),
                existing_stem,
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
    let mut resolved_modules = BTreeMap::new();
    let mut resolver = resolve::Resolver::new();

    // Start with the prelude...
    let prelude_path = ModulePath("Prelude");
    if let Some(unresolved_prelude) = parsed_modules.remove(&prelude_path) {
        let resolved_prelude = resolver.resolve(unresolved_prelude)?;
        resolved_modules.insert(prelude_path, resolved_prelude);
    }

    // Then resolve all other modules.
    for (path, module) in parsed_modules {
        let resolved_module = resolver.resolve(module)?;
        resolved_modules.insert(path, resolved_module);

        // Clear out the scope of variables defined in this module.
        // Possibly we should do this in a more thoughtful way.
        resolver.clear_scopes();
    }

    // Check that any qualified names used actually exist.
    resolver.check_assumptions(&resolved_modules)?;

    // Apply operator precedences
    let mut precs = BTreeMap::new();
    for module in resolved_modules.values() {
        for (name, defn) in module.definitions.iter() {
            precs.extend(iter::repeat(name).zip(defn.precedence.iter()));
        }
    }

    for module in resolved_modules.values_mut() {
        module.apply(&precs);
    }

    // Typecheck
    let mut typechecker = typecheck::Typechecker::new();
    let typechecked_modules = typechecker.typecheck(resolved_modules)?;

    // Generate code
    let mut generated = Vec::new();
    for (module_path, module) in typechecked_modules.iter() {
        let lua = codegen::generate(module, &module_stems)?;
        generated.push((module_stems[module_path].clone(), lua));
    }

    Ok(generated)
}
