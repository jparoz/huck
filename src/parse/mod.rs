use nom::branch::alt;
use nom::bytes::complete::{escaped, is_not, tag};
use nom::character::complete::{anychar, char, hex_digit1, one_of, satisfy};
use nom::character::complete::{none_of, u8 as nom_u8};
use nom::combinator::{map, not, opt, peek, recognize, success, value, verify};
use nom::multi::{many0, many1, separated_list0, separated_list1};
use nom::number::complete::recognize_float;
use nom::sequence::tuple as nom_tuple;
use nom::sequence::{delimited, preceded, separated_pair, terminated};
use nom::IResult;

use std::collections::BTreeMap;
use std::time::Instant;

use crate::{ast::*, log};

pub mod precedence;
use precedence::{ApplyPrecedence, Associativity, Precedence};

#[cfg(test)]
mod test;

pub fn parse(input: &'static str) -> Result<Module, Error> {
    // Start the timer to measure how long parsing takes.
    let start_time = Instant::now();

    let module = match preceded(
        ws(success(())),
        nom_tuple((opt(module_declaration), many0(statement))),
    )(input)
    {
        Ok((leftover, (path, statements))) => {
            if !leftover.is_empty() {
                return Err(Error::Leftover(leftover.to_string()));
            }

            let mut module = Module {
                path,
                ..Module::default()
            };

            let mut precs = BTreeMap::new();

            // Process all parsed statements,
            // and insert them into the Module (and precs map).
            for stat in statements {
                match stat {
                    Statement::AssignmentWithoutType((lhs, expr)) => {
                        module
                            .definitions
                            .entry(lhs.name().clone())
                            .or_default()
                            .assignments
                            .push((lhs, expr));
                    }

                    Statement::AssignmentWithType(ts, (lhs, expr)) => {
                        let defn = module.definitions.entry(lhs.name().clone()).or_default();

                        // If there was already an explicit for this name, that's an error.
                        if let Some(previous_ts) = defn.explicit_type.replace(ts.clone()) {
                            return Err(Error::MultipleTypes(
                                lhs.name().clone(),
                                // @Cleanup: don't have this dodgy whitespace
                                format!("\n    {:?}\n    {:?}", ts, previous_ts),
                            ));
                        }

                        defn.assignments.push((lhs, expr));
                    }

                    Statement::TypeAnnotation(name, ts) => {
                        // If there was already an explicit for this name, that's an error.
                        if let Some(previous_ts) = module
                            .definitions
                            .entry(name.clone())
                            .or_default()
                            .explicit_type
                            .replace(ts.clone())
                        {
                            return Err(Error::MultipleTypes(
                                name,
                                // @Cleanup @Errors: don't have this dodgy whitespace
                                format!("\n    {:?}\n    {:?}", ts, previous_ts),
                            ));
                        }
                    }

                    Statement::Precedence(name, prec) => {
                        precs.insert(name.clone(), prec);
                        // If there was already a precedence for this name, that's an error.
                        if let Some(previous_prec) = module
                            .definitions
                            .entry(name.clone())
                            .or_default()
                            .precedence
                            .replace(prec)
                        {
                            return Err(Error::MultiplePrecs(name, prec, previous_prec));
                        }
                    }

                    Statement::TypeDefinition(type_defn) => {
                        if let Some(first_defn) = module
                            .type_definitions
                            .insert(type_defn.name.clone(), type_defn)
                        {
                            return Err(Error::MultipleTypeDefinitions(first_defn.name));
                        }
                    }

                    Statement::Import(path, names) => {
                        module.imports.entry(path).or_default().extend(names)
                    }

                    Statement::ForeignImport(require_string, import_items) => module
                        .foreign_imports
                        .entry(require_string)
                        .or_default()
                        .extend(import_items.into_iter().map(|item| match item {
                            ForeignImportItem::SameName(name, ts) => {
                                (LuaName(name.as_str().to_string()), name, ts)
                            }
                            ForeignImportItem::Rename(lua_name, name, ts) => (lua_name, name, ts),
                        })),

                    Statement::ForeignExport(lua_lhs, expr) => {
                        module.foreign_exports.push((lua_lhs, expr))
                    }
                }
            }

            // Modify the AST to take precedence statements into account.
            for defn in module.definitions.values_mut() {
                defn.apply(&precs);
            }

            module
        }
        Err(nom) => return Err(Error::Nom(nom.to_string())),
    };

    log::info!(
        log::METRICS,
        "Parsing module {} completed, {:?} elapsed",
        module.path.unwrap_or_default(),
        start_time.elapsed()
    );

    Ok(module)
}

fn module_declaration(input: &'static str) -> IResult<&'static str, ModulePath> {
    delimited(reserved("module"), module_path, semi)(input)
}

fn module_path(input: &'static str) -> IResult<&'static str, ModulePath> {
    map(
        ws(recognize(separated_list1(tag("."), module_path_segment))),
        ModulePath,
    )(input)
}

fn statement(input: &'static str) -> IResult<&'static str, Statement> {
    alt((
        // Assignment with inline type annotation
        map(assign_with_type, |(ts, assign)| {
            Statement::AssignmentWithType(ts, assign)
        }),
        // Assignment without inline type annotation
        map(assign, Statement::AssignmentWithoutType),
        // Standalone type annotation
        map(
            terminated(separated_pair(name, reserved_op(":"), type_scheme), semi),
            |(name, scheme)| Statement::TypeAnnotation(name, scheme),
        ),
        // Type definition
        map(
            nom_tuple((
                reserved("type"),
                constructor_lhs,
                reserved_op("="),
                separated_list1(ws(tag("|")), constructor_definition),
                semi,
            )),
            |(_, (name, vars), _, constructors, _)| {
                Statement::TypeDefinition(TypeDefinition {
                    name,
                    vars,
                    constructors,
                })
            },
        ),
        // Precedence declaration
        map(prec, |(name, prec)| Statement::Precedence(name, prec)),
        // Huck import statement
        map(
            delimited(
                reserved("import"),
                nom_tuple((module_path, tuple(name))),
                semi,
            ),
            |(path, names)| Statement::Import(path, names),
        ),
        // Foreign (Lua) import statement
        map(
            delimited(
                nom_tuple((reserved("foreign"), reserved("import"))),
                nom_tuple((string, tuple(foreign_import_item))),
                semi,
            ),
            |(require_string, import_items)| Statement::ForeignImport(require_string, import_items),
        ),
        // Foreign (Lua) export statement
        map(
            delimited(
                nom_tuple((reserved("foreign"), reserved("export"))),
                // @Fixme: this should probably do some attempt to parse a valid Lua prefixexp
                separated_pair(recognize(many1(none_of("="))), reserved_op("="), expr),
                semi,
            ),
            |(lhs, expr)| Statement::ForeignExport(lhs, expr),
        ),
    ))(input)
}

fn foreign_import_item(input: &'static str) -> IResult<&'static str, ForeignImportItem> {
    alt((
        map(
            // @Todo @Checkme: should this be name, or ws(var)?
            separated_pair(name, reserved_op(":"), type_scheme),
            |(name, ts)| ForeignImportItem::SameName(name, ts),
        ),
        map(
            nom_tuple((
                lua_name,
                reserved("as"),
                name,
                reserved_op(":"),
                type_scheme,
            )),
            |(lua_name, _, huck_name, _, ts)| ForeignImportItem::Rename(lua_name, huck_name, ts),
        ),
    ))(input)
}

fn assign_with_type(input: &'static str) -> IResult<&'static str, (TypeScheme, Assignment)> {
    terminated(
        map(
            nom_tuple((lhs, reserved_op(":"), type_scheme, reserved_op("="), expr)),
            |(lhs, _, ts, _, rhs)| (ts, (lhs, rhs)),
        ),
        semi,
    )(input)
}

fn assign(input: &'static str) -> IResult<&'static str, Assignment> {
    terminated(separated_pair(lhs, reserved_op("="), expr), semi)(input)
}

fn prec(input: &'static str) -> IResult<&'static str, (Name, Precedence)> {
    map(
        terminated(nom_tuple((associativity, ws(nom_u8), operator)), semi),
        |(assoc, prec, op)| (op, Precedence(assoc, prec)),
    )(input)
}

fn associativity(input: &'static str) -> IResult<&'static str, Associativity> {
    alt((
        value(Associativity::Left, reserved("infixl")),
        value(Associativity::Right, reserved("infixr")),
        value(Associativity::None, reserved("infix")),
    ))(input)
}

fn lhs(input: &'static str) -> IResult<&'static str, Lhs> {
    alt((
        map(nom_tuple((pattern, operator, pattern)), |(a, op, b)| {
            Lhs::Binop { a, op, b }
        }),
        map(nom_tuple((name, many0(pattern))), |(name, args)| {
            Lhs::Func { name, args }
        }),
    ))(input)
}

fn pattern(input: &'static str) -> IResult<&'static str, Pattern> {
    alt((
        map(ws(var), Pattern::Bind),
        map(list(pattern), Pattern::List),
        map(tuple(pattern), Pattern::Tuple),
        map(numeral, Pattern::Numeral),
        map(string, Pattern::String),
        map(
            parens(nom_tuple((upper_name, many1(pattern)))),
            |(constructor, args)| Pattern::Destructure { constructor, args },
        ),
        map(upper_name, Pattern::UnaryConstructor),
        value(Pattern::Unit, unit),
        parens(pattern_binop),
        parens(pattern),
    ))(input)
}

fn pattern_binop(input: &'static str) -> IResult<&'static str, Pattern> {
    map(
        nom_tuple((pattern, operator, alt((pattern_binop, pattern)))),
        |(lhs, operator, rhs)| Pattern::Binop {
            operator,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
    )(input)
}

fn expr(input: &'static str) -> IResult<&'static str, Expr> {
    alt((binop, app, let_in, if_then_else, case, lambda, lua_expr))(input)
}

fn type_scheme(input: &'static str) -> IResult<&'static str, TypeScheme> {
    map(
        nom_tuple((
            opt(preceded(
                reserved("forall"),
                terminated(many1(ws(var)), ws(tag("."))),
            )),
            type_expr,
        )),
        |(vars, typ)| {
            // @Errors: check that all the vars are unique

            TypeScheme {
                vars: vars.into_iter().flatten().collect(),
                typ,
            }
        },
    )(input)
}

fn type_expr(input: &'static str) -> IResult<&'static str, TypeExpr> {
    alt((
        // @Future @TypeBinops: type-level binops
        // Can possibly just modify the below line to use type_operator instead of reserved_op("->")
        map(
            nom_tuple((type_app, reserved_op("->"), type_expr)),
            |(f, _, x)| TypeExpr::Arrow(Box::new(f), Box::new(x)),
        ),
        type_app,
    ))(input)
}

fn type_app(input: &'static str) -> IResult<&'static str, TypeExpr> {
    map(many1(type_term), |ts| {
        ts.into_iter()
            .map(TypeExpr::Term)
            .reduce(|a, b| TypeExpr::App(Box::new(a), Box::new(b)))
            .unwrap() // safe unwrap because we're mapping over many1
    })(input)
}

fn type_term(input: &'static str) -> IResult<&'static str, TypeTerm> {
    alt((
        map(ws(upper_ident), TypeTerm::Concrete),
        map(ws(var), TypeTerm::Var),
        map(delimited(ws(tag("[")), type_expr, ws(tag("]"))), |t| {
            TypeTerm::List(Box::new(t))
        }),
        value(TypeTerm::Unit, unit),
        map(parens(type_expr), |t| TypeTerm::Parens(Box::new(t))),
        map(tuple(type_expr), TypeTerm::Tuple),
    ))(input)
}

fn binop(input: &'static str) -> IResult<&'static str, Expr> {
    map(nom_tuple((app, operator, expr)), |(lhs, operator, rhs)| {
        Expr::Binop {
            operator,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    })(input)
}

fn app(input: &'static str) -> IResult<&'static str, Expr> {
    map(many1(term), |ts| {
        ts.into_iter()
            .map(Expr::Term)
            .reduce(|a, b| Expr::App {
                func: Box::new(a),
                argument: Box::new(b),
            })
            .unwrap() // safe unwrap because we're mapping over many1
    })(input)
}

fn let_in(input: &'static str) -> IResult<&'static str, Expr> {
    map(
        nom_tuple((
            reserved("let"),
            separated_list1(semi, separated_pair(lhs, reserved_op("="), expr)),
            opt(semi),
            reserved("in"),
            expr,
        )),
        |(_, assigns, _, _, in_expr)| {
            let mut local_env: BTreeMap<Name, Vec<Assignment>> = BTreeMap::new();
            for (lhs, expr) in assigns {
                local_env
                    .entry(lhs.name().clone())
                    .or_default()
                    .push((lhs, expr));
            }
            Expr::Let {
                definitions: local_env,
                in_expr: Box::new(in_expr),
            }
        },
    )(input)
}

fn if_then_else(input: &'static str) -> IResult<&'static str, Expr> {
    map(
        nom_tuple((
            reserved("if"),
            expr,
            reserved("then"),
            expr,
            reserved("else"),
            expr,
        )),
        |(_, cond, _, then_expr, _, else_expr)| Expr::If {
            cond: Box::new(cond),
            then_expr: Box::new(then_expr),
            else_expr: Box::new(else_expr),
        },
    )(input)
}

fn case(input: &'static str) -> IResult<&'static str, Expr> {
    map(
        nom_tuple((
            reserved("case"),
            expr,
            reserved("of"),
            delimited(
                ws(tag("{")),
                terminated(separated_list1(semi, case_arm), opt(semi)),
                ws(tag("}")),
            ),
        )),
        |(_, expr, _, arms)| Expr::Case {
            expr: Box::new(expr),
            arms,
        },
    )(input)
}

fn case_arm(input: &'static str) -> IResult<&'static str, (Pattern, Expr)> {
    separated_pair(pattern, reserved_op("->"), expr)(input)
}

fn lambda(input: &'static str) -> IResult<&'static str, Expr> {
    map(
        nom_tuple((reserved_op("\\"), many1(pattern), reserved_op("->"), expr)),
        |(_, args, _, rhs)| Expr::Lambda {
            lhs: Lhs::Lambda { args },
            rhs: Box::new(rhs),
        },
    )(input)
}

fn lua_expr(input: &'static str) -> IResult<&'static str, Expr> {
    fn nested_braces(input: &'static str) -> IResult<&'static str, &'static str> {
        delimited(
            tag("{"),
            recognize(many0(alt((
                value((), nom_tuple((peek(tag("{")), nested_braces))),
                value((), nom_tuple((peek(not(tag("}"))), anychar))),
            )))),
            tag("}"),
        )(input)
    }

    alt((
        map(ws(preceded(reserved("lua"), ws(nested_braces))), Expr::Lua),
        map(
            ws(preceded(
                nom_tuple((reserved("unsafe"), reserved("lua"))),
                ws(nested_braces),
            )),
            Expr::UnsafeLua,
        ),
    ))(input)
}

fn term(input: &'static str) -> IResult<&'static str, Term> {
    alt((
        map(numeral, Term::Numeral),
        map(string, Term::String),
        map(list(expr), Term::List),
        map(name, Term::Name),
        value(Term::Unit, unit),
        map(parens(expr), |e| Term::Parens(Box::new(e))),
        map(tuple(expr), Term::Tuple),
    ))(input)
}

fn var(input: &'static str) -> IResult<&'static str, &'static str> {
    verify(
        recognize(nom_tuple((
            satisfy(is_var_start_char),
            many0(satisfy(is_name_char)),
        ))),
        |s| !is_reserved(s),
    )(input)
}

fn upper_ident(input: &'static str) -> IResult<&'static str, &'static str> {
    recognize(nom_tuple((
        satisfy(char::is_uppercase),
        many0(satisfy(is_name_char)),
    )))(input)
}

fn module_path_segment(input: &'static str) -> IResult<&'static str, &'static str> {
    recognize(nom_tuple((
        satisfy(char::is_uppercase),
        many0(satisfy(char::is_alphabetic)),
    )))(input)
}

fn name(input: &'static str) -> IResult<&'static str, Name> {
    ws(alt((
        map(var, |s| Name::Ident(s.to_string())),
        map(upper_ident, |s| Name::Ident(s.to_string())),
        parens(operator),
    )))(input)
}

fn upper_name(input: &'static str) -> IResult<&'static str, Name> {
    ws(map(upper_ident, |s| Name::Ident(s.to_string())))(input)
}

fn lua_name(input: &'static str) -> IResult<&'static str, LuaName> {
    ws(map(
        recognize(nom_tuple((
            satisfy(char::is_alphabetic),
            many0(satisfy(char::is_alphanumeric)),
        ))),
        |s: &'static str| LuaName(s.to_string()),
    ))(input)
}

/// Parses one term in a type constructor definition. e.g. in the following:
///     type Foo = Bar | Baz Int;
/// `constructor_definition` would parse either "Bar" or "Baz Int".
fn constructor_definition(input: &'static str) -> IResult<&'static str, ConstructorDefinition> {
    // @Future: type constructor binops
    nom_tuple((upper_name, many0(type_term)))(input)
}

fn constructor_lhs(input: &'static str) -> IResult<&'static str, (Name, Vec<&'static str>)> {
    nom_tuple((upper_name, many0(ws(var))))(input)
}

fn numeral(input: &'static str) -> IResult<&'static str, Numeral> {
    map(alt((numeral_positive, parens(numeral_negative))), |s| {
        if s.contains(&['.', 'e', 'E'][..]) {
            Numeral::Float(s)
        } else {
            Numeral::Int(s)
        }
    })(input)
}

fn numeral_string(input: &'static str) -> IResult<&'static str, &'static str> {
    ws(alt((
        recognize(nom_tuple((alt((tag("0x"), tag("0X"))), hex_digit1))),
        recognize(nom_tuple((
            alt((tag("0b"), tag("0B"))),
            many1(alt((char('0'), char('1')))),
        ))),
        preceded(not(tag("+")), recognize_float),
    )))(input)
}

fn numeral_positive(input: &'static str) -> IResult<&'static str, &'static str> {
    preceded(not(tag("-")), numeral_string)(input)
}

fn numeral_negative(input: &'static str) -> IResult<&'static str, &'static str> {
    recognize(nom_tuple((tag("-"), numeral_string)))(input)
}

fn string(input: &'static str) -> IResult<&'static str, &'static str> {
    // "hello, world"
    // @Note: includes the quotes
    ws(recognize(delimited(
        char('"'),
        map(
            opt(escaped(is_not("\\\""), '\\', one_of("\\\"'abfnrtv"))),
            |res| res.unwrap_or(""),
        ),
        char('"'),
    )))(input)
}

fn list<F, O>(inner: F) -> impl FnMut(&'static str) -> IResult<&'static str, Vec<O>>
where
    F: FnMut(&'static str) -> IResult<&'static str, O>,
{
    delimited(
        ws(tag("[")),
        separated_list0(ws(tag(",")), inner),
        ws(tag("]")),
    )
}

fn tuple<F, O>(inner: F) -> impl FnMut(&'static str) -> IResult<&'static str, Vec<O>>
where
    F: FnMut(&'static str) -> IResult<&'static str, O>,
{
    delimited(
        ws(tag("(")),
        separated_list1(ws(tag(",")), inner),
        ws(tag(")")),
    )
}

fn operator(input: &'static str) -> IResult<&'static str, Name> {
    map(
        verify(
            ws(recognize(alt((
                value((), many1(operator_char)),
                value((), delimited(char('`'), alt((var, upper_ident)), char('`'))),
            )))),
            |s| !is_reserved(s),
        ),
        |s| Name::Binop(s.to_string()),
    )(input)
}

fn operator_char(input: &'static str) -> IResult<&'static str, char> {
    one_of("=+-|!@#$%^&*:.,/~<>")(input)
}

fn semi(input: &'static str) -> IResult<&'static str, &'static str> {
    ws(tag(";"))(input)
}

fn unit(input: &'static str) -> IResult<&'static str, &'static str> {
    ws(tag("()"))(input)
}

fn comment(input: &'static str) -> IResult<&'static str, &'static str> {
    recognize(nom_tuple((
        tag("(*"),
        many0(alt((
            value((), nom_tuple((peek(tag("(*")), comment))),
            value((), nom_tuple((peek(not(tag("*)"))), anychar))),
        ))),
        tag("*)"),
    )))(input)
}

fn ws<F, O>(inner: F) -> impl FnMut(&'static str) -> IResult<&'static str, O>
where
    F: FnMut(&'static str) -> IResult<&'static str, O>,
{
    let space = satisfy(char::is_whitespace);

    let whitespace = many0(alt((value((), comment), value((), space))));

    terminated(inner, whitespace)
}

fn reserved(s: &'static str) -> impl FnMut(&'static str) -> IResult<&'static str, &'static str> {
    assert!(is_reserved(s));
    ws(terminated(tag(s), peek(not(satisfy(is_name_char)))))
}

fn reserved_op(s: &'static str) -> impl FnMut(&'static str) -> IResult<&'static str, &'static str> {
    assert!(is_reserved(s));
    ws(terminated(tag(s), peek(not(operator_char))))
}

fn parens<F, O>(inner: F) -> impl FnMut(&'static str) -> IResult<&'static str, O>
where
    F: FnMut(&'static str) -> IResult<&'static str, O>,
{
    delimited(ws(tag("(")), inner, ws(tag(")")))
}

fn is_name_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

fn is_var_start_char(c: char) -> bool {
    c.is_lowercase() || c == '_'
}

// @Note: In the definition of upper_ident, we assume there are no reserved words beginning with
// an uppercase letter.
fn is_reserved(word: &str) -> bool {
    matches!(
        word,
        "module"
            | "lazy"
            | "import"
            | "export"
            | "foreign"
            | "as"
            | "let"
            | "in"
            | "if"
            | "then"
            | "else"
            | "case"
            | "of"
            | "do"
            | "infix"
            | "infixl"
            | "infixr"
            | "forall"
            | "type"
            | "unsafe"
            | "lua"
            | "=>"
            | ","
            | "()"
            | "="
            | ":"
            | "\\"
            | "->"
            | "<-"
    )
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Nom error: {0}")]
    Nom(String),

    // @Todo @Errors: convert this into a parse error which exposes the underlying cause from Nom
    #[error("Leftover input: {0}")]
    Leftover(String),

    // @Cleanup @Errors: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple precedence declarations found for `{0}`:\n    {1:?}\n    {2:?}")]
    MultiplePrecs(Name, Precedence, Precedence),

    // @Cleanup @Errors: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple explicit type annotations found for `{0}`:{1}")]
    MultipleTypes(Name, String),

    // @Cleanup @Errors: this should print the source locations of the two definitions
    #[error("Multiple type definitions with the same name ({0})")]
    MultipleTypeDefinitions(Name),
}
