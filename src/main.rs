mod ast;
mod codegen;
mod compile;
mod error;
mod log;
mod module;
mod name;
mod parse;
mod precedence;
mod resolve;
mod typecheck;
mod types;

#[allow(dead_code)]
mod utils;

use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::time::Instant;

use clap::builder::TypedValueParser as _;
use clap::Parser;

use compile::compile;

use error::Error as HuckError;

/// Compiler for the Huck programming language
#[derive(Parser, Debug)]
#[command(version, about, arg_required_else_help(true))]
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
        default_value = "off",
        value_parser = clap::builder::PossibleValuesParser::new(["error", "warn", "info", "debug", "trace", "off"])
                .map(|s| log_crate::LevelFilter::from_str(&s).unwrap()),
        )]
    log: log_crate::LevelFilter,

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
    // to_compile.extend(args.files.iter().map(load).collect()?);
    for file in args.files.iter() {
        to_compile.push(load(file)?);
    }

    // We're done adding modules, so now we can compile.
    for (stem, lua) in compile(to_compile)? {
        // @Todo: make this optional via command line flag
        let lua = utils::normalize(&lua);

        // Write the compiled Lua to a .lua file.
        let mut file_path = PathBuf::from(stem);
        assert!(file_path.set_extension("lua"));
        log::info!(
            log::CODEGEN,
            "Writing generated output to {}",
            file_path.display()
        );
        std::fs::write(file_path, lua)?;
    }

    log::info!(
        log::METRICS,
        "Compilation finished, total {:?} elapsed",
        compilation_start.elapsed()
    );

    Ok(())
}

/// Takes a file path, and loads the file into a format ready to be compiled.
fn load<P>(path: P) -> Result<(String, &'static str), HuckError>
where
    P: AsRef<Path>,
{
    let mut path_buf = path.as_ref().to_path_buf();
    path_buf.set_extension("");
    let stem = path_buf
        .into_os_string()
        .into_string()
        .map_err(|_| HuckError::BadFilePath(format!("{}", path.as_ref().display())))?;
    let src = read_to_leaked(path)?;

    Ok((stem, src))
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
