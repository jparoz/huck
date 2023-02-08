use assert_cmd::prelude::*;

use std::process::Command;

#[test]
fn basic() {
    let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
    cmd.arg("examples/basic.hk").assert().success();
}
