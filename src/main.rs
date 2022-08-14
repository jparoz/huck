mod ast;
mod error;
mod parse;
mod precedence;
mod scope;
mod types;

use std::collections::HashMap;

use log::info;

use precedence::ApplyPrecedence;
use scope::Scope;
use types::constraint::{ConstraintGenerator, GenerateConstraints};
use types::ApplySub;

fn main() {
    env_logger::init();

    let filename = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(&filename).unwrap();

    let mut parsed = parse::parse(&contents).unwrap();

    // @Todo: get these precedences in the same way as the prelude is defined
    let precs = HashMap::new();
    parsed.apply(&precs);

    let mut cg = ConstraintGenerator::new();

    let mut types = Vec::new();

    for (name, defns) in parsed.assignments {
        // Print type of defined function
        let typ = defns.generate(&mut cg);

        types.push((name, typ));

        // // Print parsed definitions
        // for (lhs, expr) in defns.iter() {
        //     println!("{} = {};", lhs, expr);
        // }
        // println!();
    }

    // Print state of constraint generator
    // println!("{}", cg);

    let mut scope = Scope::new();

    match cg.solve() {
        Ok(soln) => {
            // Print solution substitution
            // println!("Solution: {}", soln);

            // @Cleanup: This should all be done in a more proper way
            // Apply the solution to the assumption set
            for typ in cg.assumptions.values_mut().flatten() {
                typ.apply(&soln);
            }

            info!("Constraint generator state: {}", cg);

            let assumption_vars = cg.assumption_vars();

            for (name, mut typ) in types.into_iter() {
                typ.apply(&soln);

                let type_scheme = typ.generalize(&assumption_vars);
                info!("Inferred type for {} : {}", name, type_scheme);
                scope.insert(name, type_scheme);
            }

            println!("{}", scope);

            println!("Assumptions:");
            for (name, vars) in cg.assumptions.iter() {
                for var in vars {
                    println!("    {} : {}", name, var);
                }
            }
        }
        Err(e) => {
            println!("Type error: {}", e);
        }
    }
}
