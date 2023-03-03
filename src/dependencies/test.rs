use crate::error::Error as HuckError;
use crate::utils::{assert_matches, test::transpile};

use super::Error as DependencyError;

#[test]
fn error_cyclic_dependency() {
    assert_matches!(
        transpile(
            r#"
            foo = bar;
            bar = foo;
        "#,
        ),
        Err(HuckError::DependencyResolution(
            DependencyError::CyclicDependency(_)
        ))
    )
}

#[test]
fn function_cyclic_dependency() {
    assert_matches!(
        transpile(
            r#"
                foo x = bar x;
                bar x = baz x;
                baz x = foo x;
            "#
        ),
        Ok(_)
    )
}
