use std::fs;
use std::path::PathBuf;
use std::str::FromStr;
use std::time::Instant;

use clap::builder::TypedValueParser as _;
use clap::Parser;

use huck::compile::compile;
use huck::file::{self, read_to_leaked};
use huck::{log, utils};

use huck::error::Error as HuckError;

/// Compiler for the Huck programming language
#[derive(Parser, Debug)]
#[command(
    version,
    about,
    arg_required_else_help(true),
    group(clap::ArgGroup::new("normalize-group").args(["normalize", "no-normalize"]))
    )]
struct Args {
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

    /// Change the output directory
    #[arg(long)]
    output_dir: Option<PathBuf>,

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

    let mut huck_srcs = Vec::new();
    let mut lua_files = Vec::new();

    // Add all the given files to the list to be compiled.
    for file in args.files.iter() {
        if let Some(ext) = file.extension() {
            if ext == "hk" {
                huck_srcs.push(read_to_leaked(file)?);
            } else if ext == "lua" {
                lua_files.push(file);
            }
        }
    }

    let output_dir = PathBuf::from("output");

    // We're done adding modules, so now we can compile.
    for (path, mut lua) in compile(huck_srcs)? {
        let output_path = output_dir.join(PathBuf::from(path));

        if args.normalize && !args.no_normalize {
            lua = utils::normalize(&lua)?;
        }

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
        let lua = fs::read_to_string(file).map_err(file::Error::IO)?;

        file::write(output_path, lua)?;
    }

    log::info!(
        log::METRICS,
        "Compilation finished, total {:?} elapsed",
        compilation_start.elapsed()
    );

    Ok(())
}
