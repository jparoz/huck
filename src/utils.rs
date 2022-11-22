use std::collections::HashMap;
use std::io::Write;

use crate::codegen;
use crate::error::Error as HuckError;
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
pub fn transpile(huck: &str) -> Result<String, HuckError> {
    let mut parsed = parse(huck)?;

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
    let soln = cg.solve()?;

    // @Cleanup: This should all be done in a more proper way
    // Apply the solution to the assumption set
    for typ in cg.assumptions.values_mut().flatten() {
        typ.apply(&soln);
    }

    let assumption_vars = cg.assumption_vars();
    for (name, mut typ, assignments) in types.into_iter() {
        typ.apply(&soln);

        let type_scheme = typ.generalize(&assumption_vars);
        log::info!("Inferred type for {} : {}", name, type_scheme);
        let defn = TypedDefinition::new(type_scheme, assignments);
        scope.definitions.insert(name, defn);
    }

    // @Todo: optimisations go here

    // Generate code
    let lua = codegen::lua::generate(&scope)?;

    log::info!("Generated Lua code:\n{}", lua);

    Ok(normalize(&lua))
}

/// Takes some Lua and normalizes it into a consistent format.
pub fn normalize(lua: &str) -> String {
    // @Todo: don't use an external process (?)
    use std::process::*;
    let mut child = Command::new("lua-format")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    write!(child.stdin.take().unwrap(), "{}", lua).unwrap();
    let output = child.wait_with_output().unwrap();
    String::from_utf8(output.stdout)
        .unwrap()
        .replace("\n\n", "\n")
}
