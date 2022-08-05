mod ast;
mod constraint;
mod error;
mod parse;
mod precedence;
mod types;

use constraint::{ConstraintGenerator, GenerateConstraints};
use precedence::ApplyPrecedence;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(&filename).unwrap();

    let mut parsed = parse::parse(&contents).unwrap();

    parsed.apply(&std::collections::HashMap::new());

    let mut cg = ConstraintGenerator::new();

    for (name, defns) in parsed.assignments {
        // Print type of defined function
        let typ = defns.generate(&mut cg);
        println!("{} : {}", name, typ);

        // Print parsed definitions
        for (lhs, expr) in defns.iter() {
            println!("{} = {};", lhs, expr);
        }

        println!();
    }

    // Print state of constraint generator
    println!("{}", cg);

    // Print solution substitution
    println!("Solution substitution: {:?}", cg.solve());
}
