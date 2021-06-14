mod ast;
mod error;
mod parse;
mod precedence;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(&filename).unwrap();

    let mut parsed = parse::parse(&contents).unwrap();

    parsed.apply_precs(&std::collections::HashMap::new());

    for (name, defs) in parsed.assignments {
        println!("{}:", name);
        for (lhs, rhs) in defs {
            println!("    {:?} = {:?}", lhs, rhs);
        }
    }
}
