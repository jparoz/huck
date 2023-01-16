mod ast;
mod codegen;
mod context;
mod error;
mod log;
mod parse;
mod scope;
mod types;

#[allow(dead_code)]
mod utils;

use std::path::PathBuf;
use std::time::Instant;

use clap::Parser;

use context::Context;
use error::Error as HuckError;

#[derive(Parser, Debug)]
struct Args {
    /// Use this file as the prelude
    #[arg(short = 'P', long, value_name = "FILE", value_hint = clap::ValueHint::DirPath,
        // @XXX @Cleanup: do this in a better way
        default_value = concat!(env!("CARGO_MANIFEST_DIR"), "/huck/Prelude.hk")
        )]
    prelude: PathBuf,

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
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .init();

    let compilation_start = Instant::now();

    let args = Args::parse();

    let mut context = Context::new();

    // Add the Prelude to the context.
    context.include_prelude(args.prelude)?;

    // Add all the given files to the Context.
    for filename in args.files {
        context.include_file(filename)?;
    }

    log::info!(
        log::METRICS,
        "Loaded and parsed all modules, {:?} elapsed",
        compilation_start.elapsed()
    );

    // Typecheck
    context.typecheck()?;

    // Generate code
    for (module_path, mut file_path) in context.file_paths {
        log::info!(log::CODEGEN, "Generating code for module {module_path}");
        let lua = codegen::lua::generate(&context.scopes[&module_path])?;
        let lua = utils::normalize(&lua);

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
