mod ast;
mod constraint;
mod error;
mod parse;
mod types;

use constraint::ConstraintGenerator;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(&filename).unwrap();

    let mut parsed = parse::parse(&contents).unwrap();

    parsed.apply_precs(&std::collections::HashMap::new());

    let mut constraint_generator = ConstraintGenerator::new();

    for (name, assigns) in parsed.assignments {
        for assign in assigns {
            let typ = constraint_generator.generate_assign(assign);
            println!("{} has type {}", name, typ);
        }
    }

    // for (_name, defs) in parsed.assignments {
    //     for (lhs, rhs) in defs {
    //         // println!("{} = {};", lhs, rhs);
    //         let typ = constraint_generator.generate(&rhs);
    //         println!("rhs of {} has type {}", lhs, typ);
    //     }
    //     println!();
    // }

    println!("{}", constraint_generator);
}
