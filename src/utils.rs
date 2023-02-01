use std::{io::Write, time::Instant};

use crate::error::Error as HuckError;
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
pub fn normalize(lua: &str) -> Result<String, HuckError> {
    // Time how long it takes to normalize the Lua
    let start_time = Instant::now();

    // @Cleanup: don't use an external process (?)
    use std::process::*;
    let mut child = Command::new("lua-format")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    write!(child.stdin.take().unwrap(), "{}", lua).unwrap();

    let output = child.wait_with_output().unwrap();

    if !output.status.success() {
        let stderr = String::from_utf8(output.stderr).expect("lua-format should have utf-8 stderr");
        return Err(HuckError::NormalizeFailed(stderr));
    }

    let res = String::from_utf8(output.stdout)
        .unwrap()
        .replace("\n\n", "\n");

    log::info!(
        log::METRICS,
        "Normalized, {:?} elapsed",
        start_time.elapsed()
    );

    Ok(res)
}

#[allow(unused_macros)]
macro_rules! unwrap_match {
    ($rhs:expr, $pat:pat => $bound:expr) => {
        match $rhs {
            $pat => $bound,
            _ => panic!(
                "Tried to unwrap_match {rhs} with pattern {pat}",
                rhs = $rhs,
                pat = stringify!($pat)
            ),
        }
    };
}
#[allow(unused_imports)]
pub(crate) use unwrap_match;

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn normalize_succeeds() {
        normalize(
            "function foo(bar)
            return baz    end",
        )
        .expect("normalize to accept and return valid Lua");
    }

    #[test]
    fn normalize_fails() {
        assert!(matches!(
            normalize("food = bard = banana"),
            Err(HuckError::NormalizeFailed(_))
        ))
    }
}
