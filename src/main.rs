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

use std::io::{self, Read};

use context::Context;
use error::Error as HuckError;

use crate::utils::leak_string;

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

    let mut args = std::env::args();

    // Ignore executable name
    args.next();

    // Context::new() includes the Prelude from "huck/huck/Prelude.hk" by default.
    let mut context = Context::new();

    // Add all the given files to the Context.
    for filename in args {
        if filename == "-" {
            // stdin
            log::info!(log::IMPORT, "Adding <stdin> to the context");
            let mut contents = String::new();
            io::stdin().read_to_string(&mut contents).unwrap();
            context.include_string(leak_string(contents))?;
        } else {
            log::info!(log::IMPORT, "Adding {filename} to the context");
            context.include_file(filename)?;
        }
    }

    // Typecheck
    log::info!(log::TYPECHECK, "Typechecking");
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

    Ok(())
}
