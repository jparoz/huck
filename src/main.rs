mod ast;
mod codegen;
mod error;
mod parse;
mod precedence;
mod scope;
mod types;

use std::collections::HashMap;

use log::info;

use precedence::ApplyPrecedence;
use scope::{Scope, TypedDefinition};
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

    for (name, defns) in parsed.definitions {
        // Print type of defined function
        let typ = defns.generate(&mut cg);

        types.push((name, typ, defns));

        // // Print parsed definitions
        // for (lhs, expr) in defns.iter() {
        //     eprintln!("{} = {};", lhs, expr);
        // }
        // eprintln!();
    }

    // Print state of constraint generator
    // eprintln!("{}", cg);

    let mut scope = Scope::new();

    // Solve the type constraints
    let soln = cg.solve().unwrap_or_else(|e| {
        eprintln!("Type error: {}", e);
        std::process::exit(1);
    });

    // Print solution substitution
    // eprintln!("Solution: {}", soln);

    // @Cleanup: This should all be done in a more proper way
    // Apply the solution to the assumption set
    for typ in cg.assumptions.values_mut().flatten() {
        typ.apply(&soln);
    }

    info!("Constraint generator state: {}", cg);

    let assumption_vars = cg.assumption_vars();

    for (name, mut typ, assignments) in types.into_iter() {
        typ.apply(&soln);

        let type_scheme = typ.generalize(&assumption_vars);
        info!("Inferred type for {} : {}", name, type_scheme);
        let defn = TypedDefinition::new(type_scheme, assignments);
        scope.insert(name, defn);
    }

    eprintln!("Assumptions:");
    for (name, vars) in cg.assumptions.iter() {
        for var in vars {
            eprintln!("    {} : {}", name, var);
        }
    }

    // @Todo: optimisations go here

    // Generate code
    let lua = codegen::lua::Generate::generate(&scope);
    println!("{}", lua);
}
