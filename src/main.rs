mod ast;
mod constraint;
mod error;
mod parse;
mod types;

use constraint::{ConstraintGenerator, GenerateConstraints};

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(&filename).unwrap();

    let mut parsed = parse::parse(&contents).unwrap();

    parsed.apply_precs(&std::collections::HashMap::new());

    let mut cg = ConstraintGenerator::new();

    for (name, defns) in parsed.assignments {
        for (lhs, expr) in defns.iter() {
            println!("{} = {};", lhs, expr);
        }
        let typ = defns.generate(&mut cg);
        println!("{} : {}", name, typ);
        println!();
    }

    println!("{}", cg);
}
