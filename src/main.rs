extern crate nom;

mod ast;
mod error;
mod parse;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(&filename).unwrap();

    let parsed = parse::parse(&contents);
    println!("{:?}", parsed);
}
