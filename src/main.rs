mod error;
mod lex;
mod parse;
mod ast;

use parse::parse_module;

use std::fs::File;
use std::io::Read;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let contents = {
        let mut file = File::open(&filename).unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents).unwrap();
        contents
    };
    let module = parse_module(&filename, &contents).unwrap_or_else(|err| panic!("{}", err));
    println!("{:?}", module);
}
