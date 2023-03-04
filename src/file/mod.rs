use std::path::Path;

use crate::compile::CompileInfo;
use crate::log;

mod error;
pub use error::Error;

#[cfg(test)]
mod test;

/// Takes a file path, and loads the file into a format ready to be compiled.
pub fn load<P>(path: P) -> Result<CompileInfo, Error>
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

        input = if let Ok(path) = input.strip_prefix(cwd) {
            path.to_path_buf()
        } else {
            log::warn!(
                log::IMPORT,
                "File path {path} is not in the current working directory; \
                 compiled output will be placed in the current working directory instead.",
                path = input.display()
            );
            input.file_name().expect("can't compile '..'").into()
        };
    }

    // Remove the extension
    let mut stem_path = input.clone();
    stem_path.set_extension("");

    // Build the Lua require string (stem) by joining the components with a dot "."
    let mut require = String::new();
    let mut iter = stem_path.iter().peekable();
    while let Some(os_str) = iter.next() {
        require.push_str(
            &os_str
                .to_os_string()
                .into_string()
                .map_err(|_| Error::BadFilePath(format!("{}", path.as_ref().display())))?,
        );
        if iter.peek().is_some() {
            require.push('.');
        }
    }

    let mut output = stem_path.clone();
    output.set_extension("lua");

    let source = read_to_leaked(path)?;

    Ok(CompileInfo {
        require,
        source,
        input: Some(input),
        output: Some(output),
    })
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
