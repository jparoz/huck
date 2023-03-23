use assert_cmd::prelude::*;

use std::process::Command;

#[test]
fn basic() {
    let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
    cmd.args([
        "examples/basic.hk",
        concat!(env!("HUCK_LIB_DIR"), "/Std/src/Prelude.hk"),
    ])
    .assert()
    .success();
}

#[test]
fn foo_and_bar() {
    let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
    cmd.args([
        "examples/foo.hk",
        "examples/bar.hk",
        concat!(env!("HUCK_LIB_DIR"), "/Std/src/Prelude.hk"),
    ])
    .assert()
    .success();
}

#[test]
fn uses_lua_library() {
    let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
    cmd.arg("examples/uses_lua.hk").assert().success();
}
