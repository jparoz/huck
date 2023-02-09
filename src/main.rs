mod ast;
mod codegen;
mod compile;
mod dependencies;
mod error;
mod ir;
mod log;
mod name;
mod parse;
mod precedence;
mod typecheck;
mod types;
mod utils;

#[cfg(test)]
mod test_common;

use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::time::Instant;

use clap::builder::TypedValueParser as _;
use clap::Parser;

use compile::{compile, CompileInfo};

use error::Error as HuckError;

/// Compiler for the Huck programming language
#[derive(Parser, Debug)]
#[command(
    version,
    about,
    arg_required_else_help(true),
    group(clap::ArgGroup::new("normalize-group").args(["normalize", "no-normalize"]))
    )]
struct Args {
    /// Use this file as the prelude
    #[arg(short = 'P', long, value_name = "FILE", value_hint = clap::ValueHint::DirPath,
        // @XXX @Cleanup: do this in a better way
        default_value = concat!(env!("CARGO_MANIFEST_DIR"), "/huck/Prelude.hk")
        )]
    prelude: PathBuf,

    /// Logging level
    #[arg(
        long,
        value_name = "LEVEL",
        default_value = "warn",
        value_parser = clap::builder::PossibleValuesParser::new(["error", "warn", "info", "debug", "trace", "off"])
                .map(|s| log_crate::LevelFilter::from_str(&s).unwrap()),
        )]
    log: log_crate::LevelFilter,

    // normalize
    #[arg(
        name = "normalize",
        default_value_t = true,
        long = "normalize",
        alias = "normalise",
        help = "Format Lua output using lua-format [default]",
        overrides_with_all = ["normalize", "no-normalize"]
    )]
    normalize: bool,

    /// Don't format Lua output
    #[arg(
        name = "no-normalize",
        long = "no-normalize",
        alias = "no-normalise",
        overrides_with_all = ["normalize", "no-normalize"]
    )]
    no_normalize: bool,

    /// Instead of writing file.hk's output to file.lua, print it to stdout
    #[arg(long)]
    write_to_stdout: Vec<PathBuf>,

    /// Input files to be included in compilation
    files: Vec<PathBuf>,
}

fn main() {
    do_main().unwrap_or_else(|e| {
        eprintln!("Compile error: {}", e);
        std::process::exit(1);
    });
}

fn do_main() -> Result<(), HuckError> {
    let compilation_start = Instant::now();

    let args = Args::parse();

    env_logger::Builder::new()
        .filter(None, args.log)
        .format_timestamp(None)
        .init();

    log::info!(
        log::METRICS,
        "Initialized compiler, {:?} elapsed",
        compilation_start.elapsed()
    );

    let mut to_compile = Vec::new();

    // Add the Prelude to the list to be compiled.
    to_compile.push(load(&args.prelude)?);

    // Add all the given files to the list to be compiled.
    for file in args.files.iter() {
        to_compile.push(load(file)?);
    }
    for file in args.write_to_stdout.iter() {
        let mut info = load(file)?;
        info.output = None;
        to_compile.push(info);
    }

    // We're done adding modules, so now we can compile.
    for (info, mut lua) in compile(to_compile)?.into_values() {
        if args.normalize && !args.no_normalize {
            lua = utils::normalize(&lua)?;
        }

        // Check if we should write to stdout instead of a file.
        if let Some(file_path) = info.output {
            // Write the compiled Lua to a .lua file.
            log::info!(
                log::CODEGEN,
                "Writing generated output to {}",
                file_path.display()
            );
            std::fs::write(file_path, lua)?;
        } else {
            // Write the compiled Lua to stdout.
            log::info!(log::CODEGEN, "Writing generated output to stdout");
            print!("{}", lua);
        }
    }

    log::info!(
        log::METRICS,
        "Compilation finished, total {:?} elapsed",
        compilation_start.elapsed()
    );

    Ok(())
}

/// Takes a file path, and loads the file into a format ready to be compiled.
fn load<P>(path: P) -> Result<CompileInfo, HuckError>
where
    P: AsRef<Path>,
{
    let mut input = path.as_ref().to_path_buf();

    // Check that it's not a directory
    if input.is_dir() {
        return Err(HuckError::InputFileWasDirectory(input));
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
                .map_err(|_| HuckError::BadFilePath(format!("{}", path.as_ref().display())))?,
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
