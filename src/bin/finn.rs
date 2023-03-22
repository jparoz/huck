use std::path::{Path, PathBuf};
use std::{env, fs, io};

fn main() -> Result<(), FinnError> {
    let cwd = env::current_dir()?;
    let manifest_path = discover_manifest(&cwd)?;

    println!("{}", manifest_path.display());

    Ok(())
}

/// Searches for a `finn.yaml` manifest file in the given directory,
/// and recursively its parents.
fn discover_manifest(start_dir: &Path) -> Result<PathBuf, FinnError> {
    for dir in start_dir.ancestors() {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();

            if !path.is_file() {
                continue;
            }

            if let Some(os_str) = path.file_name() {
                if os_str.to_string_lossy() == "finn.yaml" {
                    return Ok(path);
                }
            }
        }
    }
    Err(FinnError::ManifestNotFound)
}

#[derive(thiserror::Error, Debug)]
enum FinnError {
    #[error("IO error: {0}")]
    IO(#[from] io::Error),

    #[error("Manifest not found in the current directory or any of its ancestors")]
    ManifestNotFound,
}
