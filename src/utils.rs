use std::collections::HashMap;

use crate::codegen;
use crate::parse::parse;
use crate::precedence::ApplyPrecedence;
use crate::scope::{Scope, TypedDefinition};
use crate::types::constraint::{ConstraintGenerator, GenerateConstraints};
use crate::types::ApplySub;

/// Takes Lua code as input, executes it using a Lua interpreter found in PATH,
/// and returns the contents of stdout in a String.
pub fn execute_lua(lua: &str) -> String {
    let output = std::process::Command::new("lua")
        .args([
            "-e",
            &format!("print(require('inspect')((function() {} end)()))", lua),
        ])
        .output()
        .unwrap();
    String::from_utf8(output.stdout).unwrap()
}

/// Takes some Huck and turns it into Lua, doing every step in between.
// @Todo: should return Result<String, HuckError>
pub fn transpile(huck: &str) -> String {
    let mut parsed = parse(huck).unwrap(); // @Todo: bad unwrap

    // @Todo: get these precedences in the same way as the prelude is defined
    let precs = HashMap::new();
    parsed.apply(&precs);

    let mut cg = ConstraintGenerator::new();

    let mut types = Vec::new();
    for (name, defns) in parsed.definitions {
        // Print type of defined function
        let typ = defns.generate(&mut cg);

        types.push((name, typ, defns));
    }

    let mut scope = Scope::new();

    // Solve the type constraints
    // @Todo: don't unwrap
    let soln = cg.solve().unwrap_or_else(|e| {
        eprintln!("Type error: {}", e);
        std::process::exit(1);
    });

    // @Cleanup: This should all be done in a more proper way
    // Apply the solution to the assumption set
    for typ in cg.assumptions.values_mut().flatten() {
        typ.apply(&soln);
    }

    let assumption_vars = cg.assumption_vars();
    for (name, mut typ, assignments) in types.into_iter() {
        typ.apply(&soln);

        let type_scheme = typ.generalize(&assumption_vars);
        // info!("Inferred type for {} : {}", name, type_scheme);
        let defn = TypedDefinition::new(type_scheme, assignments);
        scope.insert(name, defn);
    }

    // @Todo: optimisations go here

    // Generate code
    // @Todo: don't unwrap
    let lua = codegen::lua::generate(&scope).unwrap();

    // @Todo: call normalize

    lua
}

/// Takes some Lua and normalizes it into a consistent format.
pub fn normalize(lua: &str) -> String {
    todo!() // @Todo
}
