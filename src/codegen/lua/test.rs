use crate::utils::transpile;

#[test]
fn lambda_equals_function() {
    assert_eq!(transpile(r#"id = \a -> a;"#), transpile(r#"id a = a;"#))
}
