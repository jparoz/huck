mod ast;
mod codegen;
mod compile;
mod dependencies;
mod error;
mod file;
mod ir;
mod log;
mod name;
mod parse;
mod precedence;
mod typecheck;
mod types;
mod utils;

use std::path::PathBuf;
use std::str::FromStr;
use std::time::Instant;

use clap::builder::TypedValueParser as _;
use clap::Parser;

use compile::compile;

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
    to_compile.push(file::load(&args.prelude)?);

    // Add all the given files to the list to be compiled.
    for file in args.files.iter() {
        to_compile.push(file::load(file)?);
    }
    for file in args.write_to_stdout.iter() {
        let mut info = file::load(file)?;
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
            std::fs::write(file_path, lua).map_err(file::Error::IO)?;
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
