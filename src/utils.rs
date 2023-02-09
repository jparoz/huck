use std::fmt::{Debug, Display};
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

/// Takes an iterator of `Display`-able things, and prints them out comma-separated.
pub fn display_iter<It: Display>(iter: impl Iterator<Item = It>) -> String {
    use std::fmt::Write;

    let mut s = String::new();

    let mut iter = iter.peekable();
    while let Some(it) = iter.next() {
        let _ = write!(s, "{}", it);
        if iter.peek().is_some() {
            let _ = write!(s, ", ");
        }
    }

    s
}

/// Takes an iterator of `Debug`-able things, and prints them out comma-separated.
pub fn debug_iter<It: Debug>(iter: impl Iterator<Item = It>) -> String {
    use std::fmt::Write;

    let mut s = String::new();

    let mut iter = iter.peekable();
    while let Some(it) = iter.next() {
        let _ = write!(s, "{:?}", it);
        if iter.peek().is_some() {
            let _ = write!(s, ", ");
        }
    }

    s
}

#[allow(unused_macros)]
macro_rules! unwrap_match {
    ($matched:expr, $pat:pat => $bound:expr) => {
        match $matched {
            $pat => $bound,
            _ => panic!(
                "Tried to unwrap_match {matched:?} with pattern {pat}",
                matched = $matched,
                pat = stringify!($pat)
            ),
        }
    };
}
#[allow(unused_imports)]
pub(crate) use unwrap_match;

/// Shorthand to assert that a value matches a pattern, with extra debug printing.
#[allow(unused_macros)]
macro_rules! assert_matches {
    ($val:expr, $($pat:tt)+) => {
        assert!(matches!(dbg!(&$val), $($pat)+))
    };
}
#[allow(unused_imports)]
pub(crate) use assert_matches;

/// Formats a string, then leaks the result.
#[allow(unused_macros)]
macro_rules! leak {
    ($fmt:literal, $($args:tt)+) => {
        Box::leak(format!($fmt, $($args)+).into_boxed_str())
    }
}
#[allow(unused_imports)]
pub(crate) use leak;

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn normalize_succeeds() {
        normalize(
            "function foo(bar)
            return baz    end",
        )
        .expect("normalize should accept and return valid Lua");
    }

    #[test]
    fn normalize_fails() {
        assert!(matches!(
            normalize("food = bard = banana"),
            Err(HuckError::NormalizeFailed(_))
        ))
    }
}
