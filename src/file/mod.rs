use std::fs;
use std::path::{Path, PathBuf};

use crate::name::ModulePath;

mod error;
pub use error::Error;

#[cfg(test)]
mod test;

/// Converts a [`ModulePath`] into a [`PathBuf`],
/// the default filename for generated Lua files.
/// Note that the returned PathBuf is relative!
impl From<ModulePath> for PathBuf {
    fn from(module_path: ModulePath) -> Self {
        // Get the module path as a String.
        let name = format!("{}", module_path);

        // Convert all the `.`s in the string to directory separators,
        let mut path = convert_lua_dir_separators(&name);

        // and add the .lua extension.
        path.set_extension("lua");

        path
    }
}

/// Converts '.'s to the appropriate directory separators.
pub fn convert_lua_dir_separators(input: &str) -> PathBuf {
    let mut output = PathBuf::new();
    for segment in input.split('.') {
        output.push(segment);
    }
    output
}

/// Reads a file to a `String`, then leaks it.
// @Cleanup: not pub. See comment in finn.rs
pub fn read_to_leaked<P>(path: P) -> Result<&'static str, Error>
where
    P: AsRef<Path>,
{
    Ok(leak_string(fs::read_to_string(path)?))
}

/// Leak a string, returning a `&'static str` with its contents.
fn leak_string(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}

/// Write a slice to a `Path`,
/// while also creating directories as needed.
pub fn write<P, C>(path: P, slice: C) -> Result<(), Error>
where
    P: AsRef<Path>,
    C: AsRef<[u8]>,
{
    // Check that we're not trying to write to a directory.
    if path.as_ref().is_dir() {
        return Err(Error::InputFileWasDirectory(path.as_ref().to_path_buf()));
    }

    // Create the parent directory (recursively) if it doesn't exist.
    let dir = path
        .as_ref()
        .parent()
        .expect("root directory should have been caught by the InputFileWasDirectory error");
    if !dir.exists() {
        fs::create_dir_all(dir)?;
    }

    // Write the slice.
    Ok(fs::write(path, slice)?)
}
