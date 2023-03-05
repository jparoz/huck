use std::fs::create_dir_all;
use std::path::{Path, PathBuf};

use crate::log;
use crate::name::ModulePath;

mod error;
pub use error::Error;

#[cfg(test)]
mod test;

/// Filesystem-related information used to compile a Huck module from source.
#[derive(Debug, Clone)]
pub struct FileInfo {
    /// The Huck source code to be compiled.
    pub source: &'static str,

    /// The [`ModulePath`] of this module.
    /// This gets filled in at the parse step.
    pub module_path: Option<ModulePath>,

    /// Path to the input file.
    /// A value of `None` means that there is no input file;
    /// the code came from some other source (e.g. tests, stdin).
    pub input: Option<PathBuf>,

    /// Path to the chosen output file.
    /// A value of `None` means that the default should be used.
    pub output: Option<PathBuf>,

    /// If true,
    /// don't write to a file,
    /// write to stdout instead.
    pub stdout: bool,
}

impl FileInfo {
    /// Takes a file path, and loads the file into a format ready to be compiled.
    pub fn new<P>(path: P) -> Result<FileInfo, Error>
    where
        P: AsRef<Path>,
    {
        let mut input = path.as_ref().to_path_buf();

        // Check that it's not a directory
        if input.is_dir() {
            return Err(Error::InputFileWasDirectory(input));
        }

        // Try to convert the path into a relative path
        if input.is_absolute() {
            let cwd = std::env::current_dir()?;
            if let Ok(path) = input.strip_prefix(cwd) {
                input = path.to_path_buf()
            };
        }

        let source = read_to_leaked(path)?;

        Ok(FileInfo {
            source,
            module_path: None,
            input: Some(input),
            output: None,
            stdout: false,
        })
    }

    /// Writes a string to the `FileInfo`'s output filepath.
    pub fn write(&self, lua: &str) -> Result<(), Error> {
        // Check if we should write to stdout instead of a file.
        if self.stdout {
            log::info!(log::FILE, "Writing generated output to stdout");
            print!("{}", lua);
            return Ok(());
        }

        // Get the output file path,
        // or build it from the module path if not specifically set.
        let file_path = match self.output.clone() {
            Some(path) => path,
            None => {
                // @Todo @Cleanup: this whole thing should be overridable,
                // and probably have a different default
                // (e.g. in a single `output` folder,
                // instead of trying to put all the output files next to their inputs).
                let mut path = if let Some(mut input) = self.input.clone() {
                    input.pop();
                    input
                } else {
                    PathBuf::new()
                };

                let module_path_filepath: PathBuf = self
                    .module_path
                    .expect("should have found the module path before writing generated code")
                    .into();

                path.extend(&module_path_filepath);

                path
            }
        };

        // Create the parent directory (recursively) if it doesn't exist.
        let dir = file_path
            .parent()
            .expect("output filepaths shouldn't be the root directory");
        if !dir.exists() {
            create_dir_all(dir)?;
        }

        // Write the compiled Lua to a .lua file.
        log::info!(
            log::FILE,
            "Writing generated output to {}",
            file_path.display()
        );
        std::fs::write(file_path, lua).map_err(Error::IO)?;

        Ok(())
    }
}

/// Converts a [`ModulePath`] into a [`PathBuf`],
/// the default filename for generated Lua files.
/// Note that the returned PathBuf is relative!
impl From<ModulePath> for PathBuf {
    fn from(module_path: ModulePath) -> Self {
        let mut output = PathBuf::new();

        // Get the module path as a String.
        let name = format!("{}", module_path);

        // Convert all the `.`s in the string to directory separators,
        // and add the .lua extension.
        let mut iter = name.split('.').peekable();
        while let Some(segment) = iter.next() {
            if iter.peek().is_none() {
                // If this is the last segment,
                // it's the new filename.
                let mut new_name = segment.to_string();
                new_name.push_str(".lua");
                output.push(new_name);
            } else {
                // Otherwise, it's a subdirectory.
                output.push(segment);
            }
        }

        debug_assert!(iter.next().is_none());

        output
    }
}

/// Reads a file to a `String`, then leaks it.
fn read_to_leaked<P>(path: P) -> std::io::Result<&'static str>
where
    P: AsRef<Path>,
{
    Ok(leak_string(std::fs::read_to_string(path)?))
}

/// Leak a string, returning a `&'static str` with its contents.
fn leak_string(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}
