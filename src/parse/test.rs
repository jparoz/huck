use super::parse;

#[test]
fn binop_plus() {
    assert_eq!(
        parse(r#"val = 1 + 2;"#).unwrap(),
        parse(r#"val=1+2;"#).unwrap()
    )
}
