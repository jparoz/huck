use std::collections::BTreeMap;
use std::iter;
use std::path::{Path, PathBuf};

use crate::error::Error as HuckError;
use crate::module::{Module, ModulePath};
use crate::name::UnresolvedName;
use crate::parse::parse;
use crate::precedence::ApplyPrecedence;
use crate::{ast, codegen, log, resolve, typecheck};

/// Context is the structure which manages module imports.
/// It contains some modules, manages references between modules, and prepares for typechecking.
///
/// If multiple modules depend on one another (with or without cycles), they must be typechecked and
/// transpiled as part of the same Context.
#[derive(Debug, Default)]
pub struct Context {
    /// The file path of each included file in the context.
    /// For each entry in this map, a related entry will be generated in the other maps.
    pub file_paths: BTreeMap<ModulePath, PathBuf>,

    /// The freshly parsed statement lists for each module.
    pub parsed: BTreeMap<ModulePath, Vec<ast::Statement<UnresolvedName>>>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    /// Does every step necessary to take the added modules to compiled state.
    /// Returns a Vec of tuples of originating Huck file paths, and the resulting Lua as a String.
    //
    // @Future: we could incrementally process modules somehow,
    // rather than just having this monolithic all-or-nothing compile step.
    pub fn compile(self) -> Result<Vec<(PathBuf, String)>, HuckError> {
        // @Todo @Cleanup: Move lots of the state stored on Context to be variables here.

        // Post-parse processing
        // @XXX @Todo: don't clone
        let mut modules = self
            .parsed
            .clone()
            .into_iter()
            .map(|(path, stats)| Ok((path, Module::from_statements(path, stats)?)))
            .collect::<Result<BTreeMap<ModulePath, Module<UnresolvedName>>, HuckError>>()?;

        // Resolve names
        let mut resolved_modules = BTreeMap::new();
        let mut resolver = resolve::Resolver::new();

        // Start with the prelude...
        let prelude_path = ModulePath("Prelude");
        if let Some(unresolved_prelude) = modules.remove(&prelude_path) {
            let resolved_prelude = resolver.resolve(unresolved_prelude)?;
            resolved_modules.insert(prelude_path, resolved_prelude);
        }

        // Then resolve all other modules.
        for (path, module) in modules {
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
        let gen_mods = typechecker.typecheck(resolved_modules)?;

        // Generate code
        let mut generated = Vec::new();

        // @Todo @Cleanup: move this into codegen (?)
        for (module_path, file_path) in self.file_paths {
            log::trace!(log::CODEGEN, "Generating code for module {module_path}");
            let lua = codegen::generate(&gen_mods[&module_path])?;
            generated.push((file_path, lua));
        }

        Ok(generated)
    }

    /// Adds the given file to the Context.
    pub fn include_file<P>(&mut self, file_path: P) -> Result<(), HuckError>
    where
        P: AsRef<Path>,
    {
        log::info!(
            log::IMPORT,
            "Adding {path} to the context",
            path = file_path.as_ref().display()
        );

        match file_path.as_ref().extension() {
            Some(ex) if ex == "hk" => (),
            Some(_) => log::warn!(
                log::IMPORT,
                "unknown filetype included: {:?}",
                file_path.as_ref()
            ),
            _ => log::warn!(
                log::IMPORT,
                "file without extension included: {:?}",
                file_path.as_ref()
            ),
        }

        let src = std::fs::read_to_string(&file_path)?;
        let src = leak_string(src);

        self.include(src, Some(file_path.as_ref().to_path_buf()))
    }

    #[cfg(test)]
    /// Adds the given string to the Context, treating it as anonymous input e.g. REPL input.
    pub fn include_string(&mut self, src: &'static str) -> Result<(), HuckError> {
        self.include(src, None)
    }

    /// Actually includes the module in the Context.
    fn include(&mut self, src: &'static str, path_buf: Option<PathBuf>) -> Result<(), HuckError> {
        let (module_path, statements) = parse(src)?;
        log::trace!(log::PARSE, "Parsed module {module_path}: {statements:?}");

        if self.parsed.insert(module_path, statements).is_some() {
            return Err(HuckError::MultipleModules(format!("{}", module_path)));
        }

        // @Todo @Cleanup: don't do this, because there should always be a file path.
        // If there is no file path, generate one from the module path.
        let path_buf = if let Some(path_buf) = path_buf {
            path_buf
        } else {
            let mut path_buf = PathBuf::new();
            path_buf.push(format!("{}", module_path));
            path_buf.set_extension("hk");
            path_buf
        };

        // Insert the file path
        assert!(self.file_paths.insert(module_path, path_buf).is_none());

        Ok(())
    }

    /// Returns the file stem of the file path corresponding to the given module path.
    /// Panics if there is no file path stored in the Context corresponding to the given path.
    /// @XXX: doesn't panic, just punts
    pub fn file_stem(&mut self, path: ModulePath) -> String {
        // @XXX @Hack: this is just a punt
        // @Todo: do something smarter
        let mut xxx_path_buf = None;

        self.file_paths
            .get(&path)
            .unwrap_or_else(|| {
                xxx_path_buf = Some(format!("{}.hk", path).into());
                xxx_path_buf.as_ref().unwrap()
            })
            .file_stem()
            .expect("there should be a file name")
            .to_os_string()
            .into_string()
            .expect("the file name should be utf8")
    }
}

/// Leak a string, returning a &'static str with its contents.
fn leak_string(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}
