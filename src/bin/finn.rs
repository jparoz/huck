use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::{env, fs, io};

use log_crate as log;
use serde::{Deserialize, Serialize};

use huck::compile::compile;
use huck::error::Error as HuckError;
use huck::file;

fn main() -> Result<(), Error> {
    env_logger::Builder::new()
        .filter_level(log::LevelFilter::Trace)
        .format_timestamp(None)
        .init();

    let cwd = env::current_dir()?;
    let manifest_path = discover_manifest(&cwd)?;
    let mut project_root = manifest_path.clone();
    project_root.pop();

    log::info!("Found project manifest: {}", manifest_path.display());

    let manifest_contents = fs::read_to_string(manifest_path)?;
    let manifest: Manifest = serde_yaml::from_str(&manifest_contents)?;
    log::trace!("Parsed project manifest: {:?}", manifest);

    log::trace!("Source directory contents:");
    let source_dir = project_root.join(manifest.source).canonicalize()?;

    let (huck_files, lua_files) = find_files(&source_dir)?;

    log::trace!("Found Huck files:");
    for file in huck_files.iter() {
        log::trace!("{}", file.display());
    }
    log::trace!("Found Lua files:");
    for file in lua_files.iter() {
        log::trace!("{}", file.display());
    }

    log::warn!("@Todo: gather dependencies");

    // @Todo @Cleanup: do we really need to leak here?
    // In principle no;
    // but in practice,
    // not leaking here probably means that the lifetimes spam all the compilation process.
    let huck_srcs = huck_files
        .iter()
        .map(file::read_to_leaked)
        .collect::<Result<_, _>>()?;
    let compiled = compile(huck_srcs)?;

    let output_dir = project_root.join(manifest.output);

    // Write the compiled files
    for (path, lua) in compiled {
        // @Todo: normalize the Lua output files (? do here or elsewhere?)
        let output_path = output_dir.join(PathBuf::from(path));
        file::write(output_path, lua)?;
    }

    // Write the provided Lua files
    for file in lua_files {
        // Use the file stem as a pseudo-ModulePath
        // @Errors: should have some more robust checks
        let mut relative_path =
            file::convert_lua_dir_separators(&file.file_stem().unwrap().to_string_lossy());
        relative_path.set_extension("lua");
        let output_path = output_dir.join(relative_path);
        let lua = fs::read_to_string(file)?;

        file::write(output_path, lua)?;
    }

    Ok(())
}

/// Searches for a `finn.yaml` manifest file in the given directory,
/// and recursively its parents.
fn discover_manifest(start_dir: &Path) -> Result<PathBuf, Error> {
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
    Err(Error::ManifestNotFound)
}

/// Finds all `.hk` and `.lua` files in the given directory.
/// These are returned in `Vec`s of the Huck and the Lua files respectively.
fn find_files(dir: &Path) -> Result<(Vec<PathBuf>, Vec<PathBuf>), Error> {
    if !dir.is_dir() {
        return Err(Error::SourceDirNotDirectory);
    }

    fn go(
        dir: &Path,
        huck_files: &mut Vec<PathBuf>,
        lua_files: &mut Vec<PathBuf>,
    ) -> Result<(), Error> {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_dir() {
                go(&path, huck_files, lua_files)?;
            } else if let Some(ext) = path.extension() {
                if ext == "hk" {
                    huck_files.push(path);
                } else if ext == "lua" {
                    lua_files.push(path);
                }
            }
        }
        Ok(())
    }

    let mut huck_files = Vec::new();
    let mut lua_files = Vec::new();
    go(dir, &mut huck_files, &mut lua_files)?;
    Ok((huck_files, lua_files))
}

/// A struct describing a `finn` project manifest.
#[derive(Debug, Serialize, Deserialize)]
struct Manifest {
    name: String,
    version: semver::Version,

    /// The subdirectory containing Huck and Lua source files.
    #[serde(default = "default_source_path")]
    source: PathBuf,

    /// The target directory for compiled Lua files.
    #[serde(default = "default_output_path")]
    output: PathBuf,

    huck_version: semver::VersionReq,
    dependencies: HashMap<String, semver::VersionReq>,
}

fn default_source_path() -> PathBuf {
    PathBuf::from("src")
}

fn default_output_path() -> PathBuf {
    PathBuf::from("output")
}

#[derive(thiserror::Error, Debug)]
enum Error {
    #[error("Error compiling Huck code: {0}")]
    Huck(#[from] HuckError),

    #[error("File error: {0}")]
    File(#[from] huck::file::Error),

    #[error("IO error: {0}")]
    IO(#[from] io::Error),

    #[error("Deserialization error: {0}")]
    Serde(#[from] serde_yaml::Error),

    #[error("Manifest not found in the current directory or any of its ancestors")]
    ManifestNotFound,

    #[error("Source directory specified in finn.yaml is not a directory")]
    SourceDirNotDirectory,
}
