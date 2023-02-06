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
        local val0 = _HUCK_0
        local val1 = _HUCK_1
        return (function()
            local _HUCK_2 = {val0, val1}
            if (#_HUCK_2 == 2) and (_HUCK_2[1] == true) and (_HUCK_2[2] == true) then
                return true
            end
            if (#_HUCK_2 == 2) then return false end
            error("Unmatched pattern")
        end)()
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
