use std::io::Write;
use std::path::Path;

use crate::codegen;
use crate::error::Error as HuckError;
use crate::parse::parse;
use crate::types::typecheck;

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

pub fn transpile_file<P>(path: P) -> Result<(), HuckError>
where
    P: AsRef<Path>,
{
    match path.as_ref().extension() {
        Some(ex) if ex == "hk" => (),
        Some(ex) => log::warn!("unknown filetype transpiled: {:?}", ex),
        _ => log::warn!("file without extension transpiled: {:?}", path.as_ref()),
    }

    let huck = std::fs::read_to_string(&path)?;

    let lua = transpile(&huck)?;

    std::fs::write(path.as_ref().with_extension("lua"), lua)?;

    Ok(())
}

/// Takes some Huck and turns it into Lua, doing every step in between.
pub fn transpile(huck: &str) -> Result<String, HuckError> {
    // Parse
    let parsed = parse(huck)?;

    // Typecheck
    let scope = typecheck(parsed)?;

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
