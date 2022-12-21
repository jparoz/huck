use std::collections::BTreeMap;

use crate::{ast, parse::parse};

#[test]
fn binop_plus() {
    assert_eq!(
        parse(r#"val = 1 + 2;"#).unwrap(),
        parse(r#"val=1+2;"#).unwrap()
    )
}

#[test]
fn unit() {
    assert_eq!(parse(r#"unit = ();"#).unwrap(), {
        let mut definitions: BTreeMap<ast::Name, ast::Definition> = BTreeMap::new();

        let name = ast::Name::Ident("unit".to_string());
        definitions
            .entry(name.clone())
            .or_default()
            .assignments
            .push((
                ast::Lhs::Func { name, args: vec![] },
                ast::Expr::Term(ast::Term::Unit),
            ));

        ast::Module {
            definitions,
            type_definitions: Vec::new(),
        }
    })
}

#[test]
fn apply_to_unit() {
    assert_eq!(parse(r#"applyToUnit f = f ();"#).unwrap(), {
        let mut definitions: BTreeMap<ast::Name, ast::Definition> = BTreeMap::new();

        let name = ast::Name::Ident("applyToUnit".to_string());
        definitions
            .entry(name.clone())
            .or_default()
            .assignments
            .push((
                ast::Lhs::Func {
                    name,
                    args: vec![ast::Pattern::Bind("f")],
                },
                ast::Expr::App {
                    func: Box::new(ast::Expr::Term(ast::Term::Name(ast::Name::Ident(
                        "f".to_string(),
                    )))),
                    argument: Box::new(ast::Expr::Term(ast::Term::Unit)),
                },
            ));

        ast::Module {
            definitions,
            type_definitions: Vec::new(),
        }
    })
}
