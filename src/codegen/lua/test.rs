use crate::codegen;
use crate::context::Context;
use crate::error::Error as HuckError;
use crate::utils::normalize;

/// Takes some Huck and turns it into Lua, doing every step in between.
pub fn transpile(huck: &'static str) -> Result<String, HuckError> {
    // Reset the unique ID counter to get consistent results
    codegen::lua::CodeGenerator::reset_unique();

    // Make a context with one file
    let mut context = Context::new();

    // Include the prelude
    context
        .include_file(concat!(env!("CARGO_MANIFEST_DIR"), "/huck/Prelude.hk"))
        .unwrap();

    // Include our module
    let huck = Box::leak(format!("module Test; {huck}").into_boxed_str());
    context.include_string(huck)?;

    // Compile
    let lua = &context.compile()?[0].1;

    Ok(normalize(lua))
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

// @Todo @XXX @Test: figure out a better way to test this post-Prelude
#[ignore]
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

// @Todo @XXX @Test: figure out a better way to test this post-Prelude
#[ignore]
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

// @Prelude
#[ignore]
#[test]
fn function_not() {
    assert_eq!(
        transpile(r#"not True = False; not False = True;"#).unwrap(),
        normalize(wrap!(
            "not",
            r#"
                function(_HUCK_0)
                    if (getmetatable(_HUCK_0).__variant == "True") then
                        return False
                    end
                    if (getmetatable(_HUCK_0).__variant == "False") then
                        return True
                    end
                    error("Unmatched pattern in function `not`")
                end
            "#
        ))
    )
}

// @Prelude
#[ignore]
#[test]
fn function_and() {
    assert_eq!(
        transpile(r#"True && True = True; _ && _ = False;"#).unwrap(),
        normalize(wrap!(
            "&&",
            r#"
                function(_HUCK_0)
                    return function(_HUCK_1)
                        if (getmetatable(_HUCK_0).__variant == "True") and
                            (getmetatable(_HUCK_1).__variant == "True") then
                                return True
                            end
                            local _ = _HUCK_0
                            local _ = _HUCK_1
                            return False
                    end
                end
            "#
        ))
    )
}

// @Todo @XXX @Test: figure out a better way to test this post-Prelude
#[ignore]
#[test]
fn literal_list() {
    assert_eq!(
        transpile(r#"list = [1, 2, 3];"#).unwrap(),
        normalize(wrap!("list", "{1, 2, 3}"))
    )
}

// @Todo @XXX @Test: figure out a better way to test this post-Prelude
#[ignore]
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

// @Todo @XXX @Test: figure out a better way to test this post-Prelude
#[ignore]
#[test]
fn tuple() {
    assert_eq!(
        transpile(r#"tuple = (1, "hi");"#).unwrap(),
        normalize(wrap!("tuple", r#"{1, "hi"}"#))
    )
}
