use crate::utils::{normalize, transpile};

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
        normalize(
            r#"
                local _HUCK = {}
                _HUCK["const"] = function(_HUCK_0)
                    return function(_HUCK_1)
                        local a = _HUCK_0
                        local b = _HUCK_1
                        return a
                    end
                end
                return {["const"] = _HUCK["const"]}
            "#
        )
    )
}

#[test]
fn function_id() {
    assert_eq!(
        transpile(r#"id a = a;"#).unwrap(),
        normalize(
            r#"
                local _HUCK = {}
                _HUCK["id"] = function(_HUCK_0)
                    local a = _HUCK_0
                    return a
                end
                return {["id"] = _HUCK["id"]}
            "#
        )
    )
}

#[test]
fn function_not() {
    assert_eq!(
        transpile(r#"not True = False; not False = True;"#).unwrap(),
        normalize(
            r#"
                local _HUCK = {}
                _HUCK["not"] = function(_HUCK_0)
                    if (getmetatable(_HUCK_0).__variant == "True") then
                        return False
                    end
                    if (getmetatable(_HUCK_0).__variant == "False") then
                        return True
                    end
                    error("Unmatched pattern in function `not`")
                end
                return {["not"] = _HUCK["not"]}
            "#
        )
    )
}

#[test]
fn function_and() {
    assert_eq!(
        transpile(r#"True && True = True; _ && _ = False;"#).unwrap(),
        normalize(
            r#"
                local _HUCK = {}
                _HUCK["&&"] = function(_HUCK_0)
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
                return {["&&"] = _HUCK["&&"]}
            "#
        )
    )
}

#[test]
fn literal_list() {
    assert_eq!(
        transpile(r#"list = [1, 2, 3];"#).unwrap(),
        normalize(
            r#"
                local _HUCK = {}
                _HUCK["list"] = {1, 2, 3}
                return {["list"] = _HUCK["list"]}
            "#
        )
    )
}

#[test]
fn string_escape() {
    assert_eq!(
        transpile(r#"string = "Hello\nworld!\nThis is a quote: `\"`.";"#).unwrap(),
        normalize(
            r#"
                local _HUCK = {}
                _HUCK["string"] = "Hello\nworld!\nThis is a quote: `\"`."
                return {["string"] = _HUCK["string"]}
            "#
        )
    )
}

#[test]
fn tuple() {
    assert_eq!(
        transpile(r#"tuple = (1, "hi");"#).unwrap(),
        normalize(
            r#"
                local _HUCK = {}
                _HUCK["tuple"] = {1, "hi"}
                return {["tuple"] = _HUCK["tuple"]}
            "#
        )
    )
}
