use assert_cmd::prelude::*;

use std::process::Command;

fn assert_compiles_to(path: &str, lua: &str) {
    let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
    // @Todo: add this argument
    // cmd.arg("--write-to-stdout");
    cmd.arg(path);

    let output = cmd.spawn().unwrap().wait_with_output().unwrap();

    assert!(output.status.success());
    // assert_eq!(lua, &String::from_utf8(output.stdout).unwrap());
}

#[test]
fn short() {
    assert_compiles_to(
        "examples/short.hk",
        r#"local _HUCK = {}
_HUCK["&&"] = function(_HUCK_0)
    return function(_HUCK_1)
        if (_HUCK_0 == true) and (_HUCK_1 == true) then return true end
        return false
    end
end
return {["&&"] = _HUCK["&&"]}
"#,
    );
}
