use super::*;

#[test]
fn test_name() {
    assert_eq!(name("hello"), Ok(("", Name { name: "hello" })));
    assert!(matches!(name("+"), Err(_)));
}

#[test]
fn test_ws() {
    // assert_eq!(ws(tag("X"))("  X  X"), Ok(("  X", "X")));
}
