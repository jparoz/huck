mod ast;
mod error;
mod parse;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(&filename).unwrap();

    let mut parsed = parse::parse(&contents).unwrap();

    parsed.apply_precs(&std::collections::HashMap::new());

    for (_name, defs) in parsed.assignments {
        for (lhs, rhs) in defs {
            println!("{} = {};", lhs, rhs);
        }
        println!();
    }
}
