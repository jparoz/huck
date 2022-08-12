mod ast;
mod constraint;
mod error;
mod parse;
mod precedence;
mod types;

use constraint::{ApplySub, ConstraintGenerator, GenerateConstraints};
use precedence::ApplyPrecedence;

// @XXX
use constraint::Constraint;
use types::{Primitive, Type, TypeVar, TypeVarSet};

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(&filename).unwrap();

    let mut parsed = parse::parse(&contents).unwrap();

    parsed.apply(&std::collections::HashMap::new());

    let mut cg = ConstraintGenerator::new();

    /*
    // Manually add the constraints from example 3

    cg.next_typevar_id = 10;

    // t5 = t1
    cg.constrain(Constraint::Equality(
        Type::Var(TypeVar(5)),
        Type::Var(TypeVar(1)),
    ));

    // t2 = Int -> t3
    cg.constrain(Constraint::Equality(
        Type::Var(TypeVar(2)),
        Type::Func(
            Box::new(Type::Prim(Primitive::Int)), // should be bool
            Box::new(Type::Var(TypeVar(3))),
        ),
    ));

    // t4 <={t5} t3
    cg.constrain(Constraint::ImplicitInstance(
        Type::Var(TypeVar(4)),
        Type::Var(TypeVar(3)),
        TypeVarSet::single(TypeVar(5)),
    ));

    // t2 <={t5} t1
    cg.constrain(Constraint::ImplicitInstance(
        Type::Var(TypeVar(2)),
        Type::Var(TypeVar(1)),
        TypeVarSet::single(TypeVar(5)),
    ));
    */

    let mut types: Vec<(ast::Name, Type)> = Vec::new();

    // /*
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
    // */
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
