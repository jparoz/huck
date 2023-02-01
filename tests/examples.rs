use assert_cmd::prelude::*;
use predicates::prelude::*;

use std::process::Command;

#[test]
fn short() {
    let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
    cmd.args([
        "--write-to-stdout",
        "examples/short.hk",
        "examples/short.hk",
    ]);

    #[rustfmt::skip]
    let lua =
r#"local _HUCK = {}
_HUCK["&&"] = function(_HUCK_0)
    return function(_HUCK_1)
        if (_HUCK_0 == true) and (_HUCK_1 == true) then return true end
        return false
    end
end
return {["&&"] = _HUCK["&&"]}
"#;

    cmd.assert()
        .success()
        .stdout(predicate::function(|res: &str| res == lua));
}

#[test]
fn basic() {
    let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
    cmd.arg("examples/basic.hk").assert().success();
}
