mod ast;
mod error;
mod parse;
mod precedence;
mod types;

use precedence::ApplyPrecedence;
use types::constraint::{ConstraintGenerator, GenerateConstraints};
use types::ApplySub;

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

    match cg.solve() {
        Ok(soln) => {
            // Print solution substitution
            println!("Solution: {}", soln);

            for (name, typ) in types.iter_mut() {
                typ.apply(&soln);
                println!("{} : {}", name, typ);
            }
        }
        Err(e) => {
            // @Todo: impl Display for Error
            println!("Type error: {:?}", e);
        }
    }
}
