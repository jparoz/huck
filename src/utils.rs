use std::io::Write;
use std::path::Path;

use crate::codegen;
use crate::context::Context;
use crate::error::Error as HuckError;

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

// @DRY
/// Takes a Huck filename file.hk, transpiles it into Lua, and writes it to file.lua
pub fn transpile_file<P>(path: P) -> Result<(), HuckError>
where
    P: AsRef<Path>,
{
    // Make a context with one file
    let mut context = Context::default();

    context.include_file(&path)?;

    log::trace!(
        "Parsed module: {:?}",
        context.modules.iter().next().unwrap()
    );

    // Typecheck
    context.typecheck()?;

    // @Future: optimisations go here

    // Generate code
    for scope in context.scopes.values() {
        let lua = codegen::lua::generate(scope)?;

        log::trace!("Generated Lua code:\n{}", lua);

        let lua = normalize(&lua);

        std::fs::write(path.as_ref().with_extension("lua"), lua)?;
    }

    Ok(())
}

// @DRY
/// Takes some Huck and turns it into Lua, doing every step in between.
pub fn transpile(huck: String) -> Result<String, HuckError> {
    // Make a context with one file
    let mut context = Context::default();

    // Parse
    context.include_string(huck, "utils.transpile".to_string())?; // @XXX

    log::trace!(
        "Parsed module: {:?}",
        context.modules.iter().next().unwrap()
    );

    // Typecheck
    context.typecheck()?;

    // @Future: optimisations go here

    // Generate code
    let scope = context.scopes.values().next().unwrap();

    let lua = codegen::lua::generate(scope)?;

    log::trace!("Generated Lua code:\n{}", lua);

    Ok(normalize(&lua))
}

/// Takes some Lua and normalizes it into a consistent format.
pub fn normalize(lua: &str) -> String {
    // @Cleanup: don't use an external process (?)
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
