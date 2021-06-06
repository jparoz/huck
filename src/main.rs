mod ast;
mod error;
mod parse;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(&filename).unwrap();

    let parsed = parse::parse(&contents).unwrap();
    for (name, defs) in parsed.assignments {
        println!("{:?}:", name);
        for (lhs, rhs) in defs {
            println!("    {:?} = {:?}", lhs, rhs);
        }
    }
}
