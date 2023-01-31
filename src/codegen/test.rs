use test_log::test;

use crate::compile::compile;
use crate::error::Error as HuckError;
use crate::utils::normalize;

const PRELUDE_SRC: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/huck/Prelude.hk"));

/// Takes some Huck and turns it into Lua, doing every step in between.
pub fn transpile(huck: &'static str) -> Result<String, HuckError> {
    // Include the prelude
    let prelude_stem = "Prelude".to_string();

    // Include our module
    let module = Box::leak(format!("module Test; {huck}").into_boxed_str());
    let module_stem = "test".to_string();

    // Compile
    for (stem, lua) in compile(vec![
        (prelude_stem, PRELUDE_SRC),
        (module_stem.clone(), module),
    ])? {
        if stem == module_stem {
            return Ok(normalize(&lua));
        }
    }
    unreachable!()
}

macro_rules! wrap {
    ($name:literal, $expr:literal) => {
        concat!(
            "local _HUCK = {}\n_HUCK[\"",
            $name,
            "\"] = ",
            $expr,
            "\nreturn {[\"",
            $name,
            "\"] = _HUCK[\"",
            $name,
            "\"]}",
        )
    };
}

#[test]
fn lambda_equals_function() {
    assert_eq!(
        transpile(r#"id = \a -> a;"#).unwrap(),
        transpile(r#"id a = a;"#).unwrap()
    )
}

#[test]
fn function_const() {
    assert_eq!(
        transpile(r#"const a b = a;"#).unwrap(),
        normalize(wrap!(
            "const",
            r#"
                function(_HUCK_0)
                    return function(_HUCK_1)
                        local a = _HUCK_0
                        local b = _HUCK_1
                        return a
                    end
                end
            "#
        ))
    )
}

#[test]
fn function_id() {
    assert_eq!(
        transpile(r#"id a = a;"#).unwrap(),
        normalize(wrap!(
            "id",
            r#"
                function(_HUCK_0)
                    local a = _HUCK_0
                    return a
                end
            "#
        ))
    )
}

#[test]
fn function_not() {
    assert_eq!(
        transpile(r#"not True = False; not False = True;"#).unwrap(),
        normalize(wrap!(
            "not",
            r#"
                function(_HUCK_0)
                    if (_HUCK_0 == true) then
                        return false
                    end
                    if (_HUCK_0 == false) then
                        return true
                    end
                    error("Unmatched pattern in function `Test.not`")
                end
            "#
        ))
    )
}

#[test]
fn function_and() {
    assert_eq!(
        transpile(r#"True && True = True; _a && _b = False;"#).unwrap(),
        normalize(wrap!(
            "&&",
            r#"
                function(_HUCK_0)
                    return function(_HUCK_1)
                        if (_HUCK_0 == true) and
                            (_HUCK_1 == true) then
                                return true
                            end
                            local _a = _HUCK_0
                            local _b = _HUCK_1
                            return false
                    end
                end
            "#
        ))
    )
}

#[test]
fn literal_list() {
    assert_eq!(
        transpile(r#"list = [1, 2, 3];"#).unwrap(),
        normalize(wrap!("list", "{1, 2, 3}"))
    )
}

#[test]
fn string_escape() {
    assert_eq!(
        transpile(r#"string = "Hello\nworld!\nThis is a quote: `\"`.";"#).unwrap(),
        normalize(wrap!(
            "string",
            r#""Hello\nworld!\nThis is a quote: `\"`.""#
        ))
    )
}

#[test]
fn tuple() {
    assert_eq!(
        transpile(r#"tuple = (1, "hi");"#).unwrap(),
        normalize(wrap!("tuple", r#"{1, "hi"}"#))
    )
}
