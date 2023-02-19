use crate::error::Error as HuckError;
use crate::utils::{assert_matches, test::transpile};

use super::Error as DependencyError;

#[test]
fn value_mutually_recursive() {
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
