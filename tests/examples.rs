use assert_cmd::prelude::*;
use predicates::prelude::*;

use std::process::Command;

fn assert_compiles_to(path: &str, lua: &str) {
    let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
    cmd.args(["--write-to-stdout", path, path]);

    cmd.assert()
        .success()
        .stdout(predicate::function(|res: &str| res == lua));
}

#[test]
fn short() {
    #[rustfmt::skip]
    assert_compiles_to("examples/short.hk",

r#"local _HUCK = {}
_HUCK["&&"] = function(_HUCK_0)
    return function(_HUCK_1)
        if (_HUCK_0 == true) and (_HUCK_1 == true) then return true end
        return false
    end
end
return {["&&"] = _HUCK["&&"]}
"#

);
}
