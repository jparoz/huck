use std::collections::BTreeMap;
use std::iter;
use std::path::PathBuf;

use crate::ast::Module;
use crate::name::{self, ModulePath, UnresolvedName};
use crate::parse::{self, parse};
use crate::precedence::ApplyPrecedence;
use crate::typecheck::typecheck;
use crate::{codegen, dependencies, ir};

use crate::error::Error as HuckError;

/// Filesystem-related information used to compile a module from source.
#[derive(Debug, Clone)]
pub struct CompileInfo {
    /// A `String` which is given to Lua's `require` function.
    pub require: String,

    /// The Huck source code to be compiled.
    /// This must be a `&'static str`;
    /// it is suggested that you [leak](crate::read_to_leaked) the contents of the source file.
    pub source: &'static str,

    /// Path to the input file.
    /// A value of `None` means that there is no input file;
    /// the code came from some other source (e.g. tests, stdin).
    pub input: Option<PathBuf>,

    /// Path to the output file.
    /// A value of `None` means that there is no output file;
    /// the generated Lua code should be output to stdout.
    pub output: Option<PathBuf>,
}

/// Does every step necessary to take the added modules to compiled state.
/// Takes a `Vec` of [`CompileInfo`]s,
/// and returns a `Vec` of ([`CompileInfo`], compiled Lua code).
//
// @Future: we could incrementally process modules somehow,
// rather than just having this monolithic all-or-nothing compile step.
pub fn compile(
    input_infos: Vec<CompileInfo>,
) -> Result<BTreeMap<ModulePath, (CompileInfo, String)>, HuckError> {
    // Record which module originated from which `CompileInfo`.
    let mut infos = BTreeMap::new();

    // Parse all the files
    let mut parsed = Vec::new();
    for info in input_infos {
        let (module_path, statements) = parse(info.source)?;

        if let Some(existing_info) = infos.insert(module_path, info) {
            Err(parse::Error::MultipleModules(
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
    let mut precs = BTreeMap::new();
    for module in resolved_modules.values() {
        for (name, defn) in module.definitions.iter() {
            precs.extend(iter::repeat(name).zip(defn.precedence.iter()));
        }
    }

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
            &infos,
        );
        generated.insert(module_path, (infos[&module_path].clone(), lua));
    }
    Ok(generated)
}
