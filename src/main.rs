mod ast;
mod constraint;
mod error;
mod parse;
mod precedence;
mod types;

use constraint::{ApplySub, ConstraintGenerator, GenerateConstraints};
use precedence::ApplyPrecedence;

fn main() {
    env_logger::init();

    let filename = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(&filename).unwrap();

    let mut parsed = parse::parse(&contents).unwrap();

    parsed.apply(&std::collections::HashMap::new());

    let mut cg = ConstraintGenerator::new();

    let mut types = Vec::new();

    for (name, defns) in parsed.assignments {
        // Print type of defined function
        let typ = defns.generate(&mut cg);
        println!("{} : {}", name, typ);
        types.push((name, typ));

        // Print parsed definitions
        for (lhs, expr) in defns.iter() {
            println!("{} = {};", lhs, expr);
        }

        println!();
    }

    // Print state of constraint generator
    println!("{}", cg);

    if let Some(soln) = cg.solve() {
        // Print solution substitution
        println!("Solution: {}", soln);

        for (name, typ) in types.iter_mut() {
            typ.apply(&soln);
            println!("{} : {}", name, typ);
        }
    } else {
        println!("No solution found!");
    }
}
