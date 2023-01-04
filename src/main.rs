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

    let mut context = Context::default();

    // Add all the given files to the Context.
    for filename in args {
        if filename == "-" {
            // stdin
            let mut contents = String::new();
            io::stdin().read_to_string(&mut contents).unwrap();

            // let lua = utils::transpile(contents)?;
            // println!("{}", lua);
            context.include_string(contents)?;
        } else {
            // utils::transpile_file(filename)?;
            context.include_file(filename)?;
        }
    }

    // Typecheck
    context.typecheck()?;

    // // @Todo @Fixme: generate code properly
    // for scope in context.scopes.values() {
    //     let lua = codegen::lua::generate(scope)?;
    //     println!("{}", lua); // @XXX
    // }

    Ok(())
}
