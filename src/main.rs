mod ast;
mod codegen;
mod context;
mod error;
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
    env_logger::init();

    let mut args = std::env::args();

    // Ignore executable name
    args.next();

    // Context::default() includes the Prelude from "../huck/Prelude.hk" by default.
    let mut context = Context::default();

    // Add all the given files to the Context.
    for filename in args {
        if filename == "-" {
            // stdin
            log::info!("Adding <stdin> to the context");
            let mut contents = String::new();
            io::stdin().read_to_string(&mut contents).unwrap();
            context.include_string(leak_string(contents))?;
        } else {
            log::info!("Adding {filename} to the context");
            context.include_file(filename)?;
        }
    }

    // Typecheck
    log::info!("Typechecking");
    context.typecheck()?;

    // Generate code
    for (module_path, mut file_path) in context.file_paths {
        log::info!("Generating code for module {module_path}");
        let lua = codegen::lua::generate(&context.scopes[&module_path])?;
        let lua = utils::normalize(&lua);
        assert!(file_path.set_extension("lua"));

        log::info!("Writing generated output to {}", file_path.display());
        std::fs::write(file_path, lua)?;
    }

    Ok(())
}
