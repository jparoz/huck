use test_log::test;

use crate::utils::{normalize, test::transpile};

macro_rules! wrap {
    ($name:literal, $expr:literal) => {
        concat!(
            "local _Test = {}\n_Test[\"",
            $name,
            "\"] = ",
            $expr,
            "\nreturn {[\"",
            $name,
            "\"] = _Test[\"",
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
                function(...)
                    local _Test_0 = select(1, ...)
                    return function(...)
                        local _Test_1 = select(1, ...)
                        local a = _Test_0
                        local b = _Test_1
                        return a
                    end
                end
            "#
        ))
        .unwrap()
    )
}

#[test]
fn function_id() {
    assert_eq!(
        transpile(r#"id a = a;"#).unwrap(),
        normalize(wrap!(
            "id",
            r#"
                function(...)
                    local _Test_0 = select(1, ...)
                    local a = _Test_0
                    return a
                end
            "#
        ))
        .unwrap()
    )
}

#[test]
fn function_not() {
    assert_eq!(
        transpile(r#"not True = False; not False = True;"#).unwrap(),
        normalize(wrap!(
            "not",
            r#"
                function(...)
                    local _Test_0 = select(1, ...)
                    local _arg_0 = _Test_0
                    return (function()
                        local case = {_arg_0}
                        if (case[1] == true) then return false end
                        if (case[1] == false) then return true end
                        error("Unmatched pattern")
                    end)()
                end
            "#
        ))
        .unwrap()
    )
}

#[test]
fn function_and() {
    assert_eq!(
        transpile(r#"True && True = True; _ && _ = False;"#).unwrap(),
        normalize(wrap!(
            "&&",
            r#"
                function(...)
                    local _Test_0 = select(1, ...)
                    return function(...)
                        local _Test_1 = select(1, ...)
                        local _arg_0 = _Test_0
                        local _arg_1 = _Test_1
                        return (function()
                            local case = {_arg_0, _arg_1}
                            if (case[1] == true) and (case[2] == true) then
                                return true
                            end
                            return false
                        end)()
                    end
                end
            "#
        ))
        .unwrap()
    )
}

#[test]
fn function_backticks_defined() {
    assert_eq!(
        transpile(r#"foo x y = 1 + x + 2 + y;"#).unwrap(),
        transpile(r#"x `foo` y = 1 + x + 2 + y;"#).unwrap(),
    )
}

#[test]
fn function_backticks_used() {
    assert_eq!(
        transpile(r#"foo x y = 1 + x + 2 + y; bar = foo 3 4;"#).unwrap(),
        transpile(r#"foo x y = 1 + x + 2 + y; bar = 3 `foo` 4;"#).unwrap(),
    )
}

#[test]
fn literal_list() {
    assert_eq!(
        transpile(r#"list = [1, 2, 3];"#).unwrap(),
        normalize(wrap!("list", "{1, 2, 3}")).unwrap()
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
        .unwrap()
    )
}

#[test]
fn tuple() {
    assert_eq!(
        transpile(r#"tuple = (1, "hi");"#).unwrap(),
        normalize(wrap!("tuple", r#"{1, "hi"}"#)).unwrap()
    )
}
