use std::fs::{create_dir_all, read_to_string};
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
    pub huck: Option<&'static str>,

    /// The Lua code which represents this module.
    /// If the module is a Huck module,
    /// then this will be filled when the code is compiled;
    /// if it's a Lua module,
    /// it will simply be copied to the output path.
    pub lua: Option<String>,

    /// The [`ModulePath`] of this module.
    /// This gets filled in at the parse step.
    pub module_path: Option<ModulePath>,

    /// Path to the input file.
    /// A value of `None` means that there is no input file;
    /// the code came from some other source (e.g. tests, stdin).
    pub input: Option<PathBuf>,

    /// Path to the chosen output file.
    /// A value of `None` means that the default should be used.
    pub output_file_path: Option<PathBuf>,

    /// Path to the chosen output directory.
    /// A value of `None` means that the default should be used.
    pub output_dir: Option<PathBuf>,

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

        // Check the file extension to see if it's
        // a Huck file which should be compiled,
        // or a Lua file which should simply be copied through to the output directory.
        match input.extension().map(|os| os.to_string_lossy()).as_deref() {
            // Lua file
            Some("lua") => {
                Ok(FileInfo {
                    huck: None,
                    lua: Some(read_to_string(path)?),

                    // Use the file stem as a pseudo-ModulePath
                    // @Errors: should have some more robust checks
                    module_path: Some(ModulePath(leak_string(
                        input.file_stem().unwrap().to_string_lossy().to_string(),
                    ))),

                    // Default to putting the code into an `output` directory
                    output_dir: Some(PathBuf::from("output")),

                    input: Some(input),
                    output_file_path: None,
                    stdout: false,
                })
            }

            // Huck file
            ext => {
                // Warn if the extension isn't .hk
                match ext {
                    Some(hk) if hk != "hk" => {
                        log::warn!(
                        log::FILE,
                        "Non-standard file extension `.{hk}` for file `{path}` (expected `.hk`); \
                         assuming the file is valid Huck",
                         path = path.as_ref().display())
                    }
                    None => {
                        log::warn!(
                            log::FILE,
                            "No file extension for file `{path}` (expected `.hk`); \
                             assuming the file is valid Huck",
                            path = path.as_ref().display()
                        )
                    }
                    _ => (),
                }

                Ok(FileInfo {
                    huck: Some(read_to_leaked(path)?),
                    lua: None,
                    module_path: None,
                    input: Some(input),
                    output_file_path: None,
                    // Default to putting the code into an `output` directory
                    output_dir: Some("output".into()),
                    stdout: false,
                })
            }
        }
    }

    /// Writes the `FileInfo`'s `lua` field to the `FileInfo`'s output filepath.
    pub fn write(&self) -> Result<(), Error> {
        // Assert that we have some Lua to write.
        self.lua
            .as_ref()
            .expect("lua should have been generated before writing a FileInfo");

        // Check if we should write to stdout instead of a file.
        if self.stdout {
            log::info!(log::FILE, "Writing generated output to stdout");
            print!("{}", self.lua.as_ref().unwrap());
            return Ok(());
        }

        // Get the output file path,
        // or build it from the module path if not specifically set.
        let file_path = if let Some(path) = self.output_file_path.clone() {
            path
        } else {
            let mut base_dir = if let Some(dir) = self.output_dir.clone() {
                // If a base output directory was specified,
                // use that.
                dir
            } else if let Some(mut input) = self.input.clone() {
                // If no base output directory was specified,
                // but there was an input file given,
                // put it in the same directory as the input file.
                input.pop();
                input
            } else {
                // Otherwise,
                // use a relative filepath
                // (i.e. put it in the current working directory).
                PathBuf::new()
            };

            let module_path_filepath: PathBuf = self
                .module_path
                .expect("should have found the module path before writing generated code")
                .into();

            base_dir.extend(&module_path_filepath);

            base_dir
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
        std::fs::write(file_path, self.lua.as_ref().unwrap()).map_err(Error::IO)?;

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
