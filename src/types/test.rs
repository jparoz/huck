use crate::parse::parse;

use super::{
    constraint::{ConstraintGenerator, GenerateConstraints},
    substitution::ApplySub,
    Type,
};

fn typ(s: &str) -> Type {
    let parsed = parse(s).unwrap();

    assert!(parsed.definitions.len() == 1);
    let (_name, defns) = parsed.definitions.into_iter().next().unwrap();

    let mut cg = ConstraintGenerator::new();
    let mut typ = defns.generate(&mut cg);

    let soln = cg.solve().unwrap();
    typ.apply(&soln);

    typ
}

#[test]
fn tuple() {
    let the_typ = typ(r#"a = (1, "hi");"#);
    assert_eq!(the_typ, typ(r#"a = (3, "hello");"#));
    assert_ne!(the_typ, typ(r#"a = ("hello", 3);"#));
    assert_ne!(the_typ, typ(r#"a = (3, "hello", 1);"#));
}
