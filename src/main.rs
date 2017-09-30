// For debugging purposes
#[allow(unused_macros)]
macro_rules! inspect {
    ($($e:expr),*) => {
        $(println!("{}: {:?}", stringify!($e), $e);)*
    }
}

mod error;
mod lex;
mod parse;
mod ast;

use parse::parse_module;

use std::fs::File;
use std::io::Read;
use std::process::exit;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let contents = {
        let mut file = File::open(&filename).unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents).unwrap();
        contents
    };

    let module = match parse_module(&filename, &contents) {
        Ok(module) => module,
        Err(errors) => {
            for err in errors {
                println!("{}", err);
            }
            exit(1)
        }
    };

    println!("{:?}", module); // @XXX
}
