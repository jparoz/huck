use std::collections::BTreeMap;
use std::path::Path;

use crate::ast::{Module, ModulePath};
use crate::error::Error as HuckError;
use crate::parse::parse;

/// Context is the structure which manages module imports.
/// It contains some modules, manages references between modules, and prepares for typechecking.
///
/// If multiple modules depend on one another (with or without cycles), they must be typechecked and
/// transpiled as part of the same Context.
#[derive(Debug, Default)]
pub struct Context<'file> {
    pub modules: BTreeMap<ModulePath<'file>, Module<'file>>,
}

impl<'file> Context<'file> {
    pub fn include_string(&mut self, src: String) -> Result<(), HuckError> {
        let src = leak_string(src);

        let module = parse(src)?;

        if let Some(existing_module) = self.modules.insert(module.path.unwrap_or_default(), module)
        {
            match existing_module.path {
                Some(path) => return Err(HuckError::MultipleModules(format!("{}", path))),
                None => {
                    return Err(HuckError::MultipleModules(
                        "Main (default when no name given)".to_string(),
                    ))
                }
            }
        }

        Ok(())
    }

    pub fn include_file<P>(&mut self, path: P) -> Result<(), HuckError>
    where
        P: AsRef<Path>,
    {
        match path.as_ref().extension() {
            Some(ex) if ex == "hk" => (),
            Some(_) => log::warn!("unknown filetype included: {:?}", path.as_ref()),
            _ => log::warn!("file without extension included: {:?}", path.as_ref()),
        }

        let src = std::fs::read_to_string(&path)?;
        self.include_string(src)
    }
}

/// Leak a string, returning a &'static str with its contents.
fn leak_string(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}
