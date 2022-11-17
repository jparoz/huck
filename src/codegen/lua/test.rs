use crate::utils::{normalize, transpile};

macro_rules! wrap_lua {
    ($lua:expr) => {{
        let mut lua = String::new();
        lua.push_str("local M = {}\n\n");
        lua.push_str(&$lua);
        lua.push_str("\n\nreturn M");
        lua
    }};
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
        normalize(&wrap_lua!(
            r#"
                M["const"] = function(_HUCK_0)
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
        normalize(&wrap_lua!(
            r#"
                M["id"] = function(_HUCK_0)
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
        normalize(&wrap_lua!(
            r#"
                M["not"] = function(_HUCK_0)
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
