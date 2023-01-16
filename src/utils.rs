use std::{io::Write, time::Instant};

use crate::log;

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

/// Takes some Lua and normalizes it into a consistent format.
pub fn normalize(lua: &str) -> String {
    // Time how long it takes to normalize the Lua
    let start_time = Instant::now();

    // @Cleanup: don't use an external process (?)
    use std::process::*;
    let mut child = Command::new("lua-format")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    write!(child.stdin.take().unwrap(), "{}", lua).unwrap();
    let output = child.wait_with_output().unwrap();

    let res = String::from_utf8(output.stdout)
        .unwrap()
        .replace("\n\n", "\n");

    log::info!(
        log::METRICS,
        "Normalized, {:?} elapsed",
        start_time.elapsed()
    );

    res
}
