use crate::compile::{compile, CompileInfo};
use crate::error::Error as HuckError;
use crate::utils::{leak, normalize};

const PRELUDE_SRC: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/huck/Prelude.hk"));

/// Takes some Huck and turns it into Lua, doing every step in between.
pub fn transpile(huck: &'static str) -> Result<String, HuckError> {
    // Include the prelude
    let prelude_info = CompileInfo {
        require: "huck.Prelude".to_string(),
        source: PRELUDE_SRC,
        input: None,
        output: None,
    };

    // Include our module
    let module_info = CompileInfo {
        require: "Test".to_string(),
        source: leak!("module Test; {}", huck),
        input: None,
        output: None,
    };

    // Compile
    for (info, lua) in compile(vec![prelude_info, module_info.clone()])?.into_values() {
        if info.require == module_info.require {
            return normalize(&lua);
        }
    }
    unreachable!()
}

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
