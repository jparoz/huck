mod ast;
mod codegen;
mod error;
mod parse;
mod scope;
mod types;

#[allow(dead_code)]
mod utils;

use std::io::{self, Read};

fn main() {
    env_logger::init();

    let mut args = std::env::args();

    // Ignore executable name
    args.next();

    for filename in args {
        if filename == "-" {
            // stdin
            let mut contents = String::new();
            io::stdin().read_to_string(&mut contents).unwrap();

            let lua = utils::transpile(&contents).unwrap_or_else(|e| {
                eprintln!("Compile error: {}", e);
                std::process::exit(1);
            });

            println!("{}", lua);
        } else {
            utils::transpile_file(filename).unwrap_or_else(|e| {
                eprintln!("Compile error: {}", e);
                std::process::exit(1);
            });
        }
    }
}
