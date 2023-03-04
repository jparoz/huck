use nom::branch::alt;
use nom::bytes::complete::{escaped, is_not, tag};
use nom::character::complete::{anychar, char, digit1, hex_digit1, one_of, satisfy};
use nom::character::complete::{none_of, u8 as nom_u8};
use nom::combinator::{map, not, opt, peek, recognize, success, value, verify};
use nom::multi::{many0, many1, separated_list0, separated_list1};
use nom::number::complete::recognize_float;
use nom::sequence::tuple as nom_tuple;
use nom::sequence::{delimited, preceded, separated_pair, terminated};
use nom::{Finish, IResult};

use std::collections::BTreeMap;
use std::time::Instant;

use crate::name::{ModulePath, UnresolvedName};
use crate::precedence::{Associativity, Precedence};
use crate::{ast::*, log, types};

/// Functionality to take a list of parsed [`Statement`]s,
/// and turn it into a [`Module`].
mod post;

mod error;
pub use error::Error;

#[cfg(test)]
mod test;

pub fn parse(
    input: &'static str,
) -> Result<(ModulePath, Vec<Statement<UnresolvedName, ()>>), Error> {
    // Start the timer to measure how long parsing takes.
    let start_time = Instant::now();

    let (leftover, (path, statements)) = preceded(
        ws(success(())),
        nom_tuple((module_declaration, many0(statement))),
    )(input)
    .finish()?;

    if !leftover.is_empty() {
        return Err(Error::Leftover(leftover.to_string()));
    }

    log::trace!(log::PARSE, "Parsed module {path}: {statements:?}");

    log::info!(
        log::METRICS,
        "Parsing module {path} completed, {:?} elapsed",
        start_time.elapsed()
    );

    Ok((path, statements))
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

fn statement(input: &'static str) -> IResult<&'static str, Statement<UnresolvedName, ()>> {
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
            terminated(
                nom_tuple((
                    preceded(reserved("type"), constructor_lhs),
                    opt(preceded(
                        reserved_op("="),
                        separated_list1(ws(tag("|")), constructor_definition),
                    )),
                )),
                semi,
            ),
            |((name, vars), opt_constr_defns)| {
                let mut constructors = BTreeMap::new();
                for constr_defn in opt_constr_defns.unwrap_or_default() {
                    constructors.insert(constr_defn.name, constr_defn);
                }
                Statement::TypeDefinition(TypeDefinition {
                    name,
                    vars,
                    constructors,
                    typ: (),
                })
            },
        ),
        // Precedence declaration
        map(prec, |(name, prec)| Statement::Precedence(name, prec)),
        // Huck import statement
        import_statement,
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

fn import_statement(input: &'static str) -> IResult<&'static str, Statement<UnresolvedName, ()>> {
    alt((
        // Import with list of names
        map(
            delimited(
                reserved("import"),
                nom_tuple((module_path, tuple(import_item))),
                semi,
            ),
            |(path, items)| Statement::Import(path, items),
        ),
        // Qualified (i.e. empty)
        map(delimited(reserved("import"), module_path, semi), |path| {
            Statement::Import(path, vec![])
        }),
    ))(input)
}

fn import_item(input: &'static str) -> IResult<&'static str, ImportItem<UnresolvedName>> {
    alt((
        // Value name, possibly renamed with `as`
        import_value,
        // Type name, possibly renamed with `as`, and possibly with constructors (possibly renamed)
        import_type,
    ))(input)
}

fn import_value(input: &'static str) -> IResult<&'static str, ImportItem<UnresolvedName>> {
    map(
        alt((
            map(parens(operator), |op| (op, None)),
            nom_tuple((
                unqualified(lower_ident),
                opt(preceded(reserved("as"), unqualified(lower_ident))),
            )),
        )),
        |(name, as_name)| ImportItem::Value {
            name,
            ident: as_name.unwrap_or(name).ident(),
        },
    )(input)
}

fn import_type(input: &'static str) -> IResult<&'static str, ImportItem<UnresolvedName>> {
    map(
        nom_tuple((
            nom_tuple((
                unqualified(upper_ident),
                opt(preceded(reserved("as"), unqualified(upper_ident))),
            )),
            opt(tuple(nom_tuple((
                unqualified(upper_ident),
                opt(preceded(reserved("as"), unqualified(upper_ident))),
            )))),
            // @Future: (..) glob import syntax for constructors?
        )),
        |((name, as_name), opt_cons)| {
            let constructors = opt_cons
                .unwrap_or_default()
                .into_iter()
                .map(|(name, as_name)| (name, as_name.unwrap_or(name).ident()))
                .collect();
            ImportItem::Type {
                name,
                ident: as_name.unwrap_or(name).ident(),
                constructors,
            }
        },
    )(input)
}

fn foreign_import_item(
    input: &'static str,
) -> IResult<&'static str, ForeignImportItem<UnresolvedName, ()>> {
    alt((
        map(
            separated_pair(ws(lower_ident), reserved_op(":"), type_scheme),
            |(name, type_scheme)| ForeignImportItem {
                foreign_name: ForeignName(name),
                name: UnresolvedName::Unqualified(name),
                type_scheme,
                typ: (),
            },
        ),
        map(
            nom_tuple((
                lua_name,
                reserved("as"),
                name,
                reserved_op(":"),
                type_scheme,
            )),
            |(foreign_name, _, name, _, type_scheme)| ForeignImportItem {
                foreign_name,
                name,
                type_scheme,
                typ: (),
            },
        ),
    ))(input)
}

fn assign_with_type(
    input: &'static str,
) -> IResult<&'static str, (TypeScheme<UnresolvedName>, Assignment<UnresolvedName>)> {
    terminated(
        map(
            nom_tuple((lhs, reserved_op(":"), type_scheme, reserved_op("="), expr)),
            |(lhs, _, ts, _, rhs)| (ts, (lhs, rhs)),
        ),
        semi,
    )(input)
}

fn assign(input: &'static str) -> IResult<&'static str, Assignment<UnresolvedName>> {
    terminated(separated_pair(lhs, reserved_op("="), expr), semi)(input)
}

fn prec(input: &'static str) -> IResult<&'static str, (UnresolvedName, Precedence)> {
    map(
        terminated(nom_tuple((associativity, ws(nom_u8), operator)), semi),
        |(associativity, priority, op)| {
            (
                op,
                Precedence {
                    associativity,
                    priority,
                },
            )
        },
    )(input)
}

fn associativity(input: &'static str) -> IResult<&'static str, Associativity> {
    alt((
        value(Associativity::Left, reserved("infixl")),
        value(Associativity::Right, reserved("infixr")),
        value(Associativity::None, reserved("infix")),
    ))(input)
}

fn lhs(input: &'static str) -> IResult<&'static str, Lhs<UnresolvedName>> {
    alt((
        map(nom_tuple((pattern, operator, pattern)), |(a, op, b)| {
            Lhs::Binop { a, op, b }
        }),
        map(nom_tuple((name, many0(pattern))), |(name, args)| {
            Lhs::Func { name, args }
        }),
    ))(input)
}

fn pattern(input: &'static str) -> IResult<&'static str, Pattern<UnresolvedName>> {
    alt((
        pattern_underscore,
        map(ws(lower_ident), |v| {
            Pattern::Bind(UnresolvedName::Unqualified(v))
        }),
        map(list(pattern), Pattern::List),
        map(tuple(pattern), Pattern::Tuple),
        map(numeral_int, Pattern::Int),
        map(string, Pattern::String),
        parens(pattern_destructure),
        map(upper_name, Pattern::UnaryConstructor),
        value(Pattern::Unit, unit),
        parens(pattern_binop),
        parens(pattern),
    ))(input)
}

fn pattern_binop(input: &'static str) -> IResult<&'static str, Pattern<UnresolvedName>> {
    map(
        nom_tuple((pattern, operator, alt((pattern_binop, pattern)))),
        |(lhs, operator, rhs)| Pattern::Binop {
            operator,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
    )(input)
}

fn pattern_underscore(input: &'static str) -> IResult<&'static str, Pattern<UnresolvedName>> {
    map(
        ws(recognize(nom_tuple((
            char('_'),
            many0(satisfy(is_name_char)),
        )))),
        Pattern::Underscore,
    )(input)
}

fn pattern_destructure(input: &'static str) -> IResult<&'static str, Pattern<UnresolvedName>> {
    map(
        nom_tuple((upper_name, many1(pattern))),
        |(constructor, args)| Pattern::Destructure { constructor, args },
    )(input)
}

fn expr(input: &'static str) -> IResult<&'static str, Expr<UnresolvedName>> {
    alt((binop, app, let_in, if_then_else, case, lambda, lua_expr))(input)
}

fn type_scheme(input: &'static str) -> IResult<&'static str, TypeScheme<UnresolvedName>> {
    map(
        nom_tuple((
            opt(preceded(
                reserved("forall"),
                terminated(many1(ws(lower_name)), ws(tag("."))),
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

fn type_expr(input: &'static str) -> IResult<&'static str, TypeExpr<UnresolvedName>> {
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

fn type_app(input: &'static str) -> IResult<&'static str, TypeExpr<UnresolvedName>> {
    map(many1(type_term), |ts| {
        ts.into_iter()
            .map(TypeExpr::Term)
            .reduce(|a, b| TypeExpr::App(Box::new(a), Box::new(b)))
            .unwrap() // safe unwrap because we're mapping over many1
    })(input)
}

fn type_term(input: &'static str) -> IResult<&'static str, TypeTerm<UnresolvedName>> {
    alt((
        map(upper_name, TypeTerm::Concrete),
        map(unqualified(lower_ident), TypeTerm::Var),
        map(delimited(ws(tag("[")), type_expr, ws(tag("]"))), |t| {
            TypeTerm::List(Box::new(t))
        }),
        value(TypeTerm::Unit, unit),
        map(parens(type_expr), |t| TypeTerm::Parens(Box::new(t))),
        map(tuple(type_expr), TypeTerm::Tuple),
    ))(input)
}

fn binop(input: &'static str) -> IResult<&'static str, Expr<UnresolvedName>> {
    map(nom_tuple((app, operator, expr)), |(lhs, operator, rhs)| {
        Expr::Binop {
            operator,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    })(input)
}

fn app(input: &'static str) -> IResult<&'static str, Expr<UnresolvedName>> {
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

fn let_in(input: &'static str) -> IResult<&'static str, Expr<UnresolvedName>> {
    map(
        nom_tuple((
            reserved("let"),
            separated_list1(semi, separated_pair(lhs, reserved_op("="), expr)),
            opt(semi),
            reserved("in"),
            expr,
        )),
        |(_, assigns, _, _, in_expr)| {
            let mut local_env: BTreeMap<UnresolvedName, Vec<Assignment<UnresolvedName>>> =
                BTreeMap::new();
            for (lhs, expr) in assigns {
                local_env.entry(*lhs.name()).or_default().push((lhs, expr));
            }
            Expr::Let {
                definitions: local_env,
                in_expr: Box::new(in_expr),
            }
        },
    )(input)
}

fn if_then_else(input: &'static str) -> IResult<&'static str, Expr<UnresolvedName>> {
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

fn case(input: &'static str) -> IResult<&'static str, Expr<UnresolvedName>> {
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

fn case_arm(
    input: &'static str,
) -> IResult<&'static str, (Pattern<UnresolvedName>, Expr<UnresolvedName>)> {
    separated_pair(case_pattern, reserved_op("->"), expr)(input)
}

fn case_pattern(input: &'static str) -> IResult<&'static str, Pattern<UnresolvedName>> {
    alt((
        // Allow matching some patterns without parens,
        // including destructuring and negative ints.
        // This isn't ambiguous,
        // because the case can only have one expression being scrutinised.
        pattern_destructure,
        map(ws(negative(numeral_string_int)), Pattern::Int),
        pattern,
    ))(input)
}

fn lambda(input: &'static str) -> IResult<&'static str, Expr<UnresolvedName>> {
    map(
        nom_tuple((reserved_op("\\"), many1(pattern), reserved_op("->"), expr)),
        |(_, args, _, rhs)| Expr::Lambda {
            args,
            rhs: Box::new(rhs),
        },
    )(input)
}

fn lua_expr(input: &'static str) -> IResult<&'static str, Expr<UnresolvedName>> {
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

fn term(input: &'static str) -> IResult<&'static str, Term<UnresolvedName>> {
    alt((
        map(numeral, Term::Numeral),
        map(string, Term::String),
        map(list(expr), Term::List),
        map(name, Term::Name),
        value(Term::Unit, unit),
        typed_expr,
        map(parens(expr), |e| Term::Parens(Box::new(e))),
        map(tuple(expr), Term::Tuple),
    ))(input)
}

fn typed_expr(input: &'static str) -> IResult<&'static str, Term<UnresolvedName>> {
    map(
        parens(separated_pair(expr, reserved_op(":"), type_scheme)),
        |(expr, ts)| Term::TypedExpr(Box::new(expr), ts),
    )(input)
}

fn lower_ident(input: &'static str) -> IResult<&'static str, &'static str> {
    verify(
        recognize(nom_tuple((
            satisfy(char::is_lowercase),
            many0(satisfy(is_name_char)),
        ))),
        |s| !(is_reserved(s)),
    )(input)
}

fn upper_ident(input: &'static str) -> IResult<&'static str, &'static str> {
    recognize(nom_tuple((
        satisfy(char::is_uppercase),
        many0(satisfy(is_name_char)),
    )))(input)
}

fn ident(input: &'static str) -> IResult<&'static str, &'static str> {
    alt((lower_ident, upper_ident))(input)
}

fn name(input: &'static str) -> IResult<&'static str, UnresolvedName> {
    alt((qualified(ident), unqualified(ident), parens(operator)))(input)
}

fn qualified<F>(inner: F) -> impl FnMut(&'static str) -> IResult<&'static str, UnresolvedName>
where
    F: FnMut(&'static str) -> IResult<&'static str, &'static str>,
{
    ws(map(
        separated_pair(
            recognize(separated_list1(
                tag("."),
                preceded(
                    peek(nom_tuple((module_path_segment, tag("."), ident))),
                    module_path_segment,
                ),
            )),
            tag("."),
            inner,
        ),
        |(path, ident)| UnresolvedName::Qualified(ModulePath(path), ident),
    ))
}

fn unqualified<F>(inner: F) -> impl FnMut(&'static str) -> IResult<&'static str, UnresolvedName>
where
    F: FnMut(&'static str) -> IResult<&'static str, &'static str>,
{
    ws(map(inner, UnresolvedName::Unqualified))
}

fn module_path_segment(input: &'static str) -> IResult<&'static str, &'static str> {
    recognize(nom_tuple((
        satisfy(char::is_uppercase),
        many0(satisfy(char::is_alphabetic)),
    )))(input)
}

fn lower_name(input: &'static str) -> IResult<&'static str, UnresolvedName> {
    alt((qualified(lower_ident), unqualified(lower_ident)))(input)
}

fn upper_name(input: &'static str) -> IResult<&'static str, UnresolvedName> {
    alt((qualified(upper_ident), unqualified(upper_ident)))(input)
}

fn lua_name(input: &'static str) -> IResult<&'static str, ForeignName> {
    ws(map(
        recognize(nom_tuple((
            satisfy(char::is_alphabetic),
            many0(satisfy(char::is_alphanumeric)),
        ))),
        ForeignName,
    ))(input)
}

/// Parses one term in a type constructor definition. e.g. in the following:
///     type Foo = Bar | Baz Int;
/// `constructor_definition` would parse either "Bar" or "Baz Int".
fn constructor_definition(
    input: &'static str,
) -> IResult<&'static str, ConstructorDefinition<UnresolvedName, ()>> {
    alt((
        map(nom_tuple((type_term, operator, type_term)), |(a, op, b)| {
            ConstructorDefinition {
                name: op,
                args: vec![a, b],
                typ: (),
            }
        }),
        map(nom_tuple((upper_name, many0(type_term))), |(name, args)| {
            ConstructorDefinition {
                name,
                args,
                typ: (),
            }
        }),
    ))(input)
}

fn constructor_lhs(
    input: &'static str,
) -> IResult<&'static str, (UnresolvedName, types::TypeVarSet<UnresolvedName>)> {
    nom_tuple((upper_name, type_vars))(input)
}

fn type_vars(input: &'static str) -> IResult<&'static str, types::TypeVarSet<UnresolvedName>> {
    map(many0(ws(lower_name)), |vars| {
        let mut set = types::TypeVarSet::empty();
        for s in vars {
            let var = types::TypeVar::Explicit(s);
            set.insert(var);
        }
        set
    })(input)
}

fn numeral(input: &'static str) -> IResult<&'static str, Numeral> {
    map(
        ws(alt((
            positive(numeral_string),
            parens(negative(numeral_string)),
        ))),
        |s| {
            if s.contains(&['.', 'e', 'E'][..]) {
                Numeral::Float(s)
            } else {
                Numeral::Int(s)
            }
        },
    )(input)
}

fn numeral_int(input: &'static str) -> IResult<&'static str, &'static str> {
    ws(alt((
        positive(numeral_string_int),
        parens(negative(numeral_string_int)),
    )))(input)
}

fn positive<F>(inner: F) -> impl FnMut(&'static str) -> IResult<&'static str, &'static str>
where
    F: FnMut(&'static str) -> IResult<&'static str, &'static str>,
{
    preceded(not(tag("-")), inner)
}

fn negative<F>(inner: F) -> impl FnMut(&'static str) -> IResult<&'static str, &'static str>
where
    F: FnMut(&'static str) -> IResult<&'static str, &'static str>,
{
    recognize(nom_tuple((tag("-"), inner)))
}

fn numeral_string(input: &'static str) -> IResult<&'static str, &'static str> {
    alt((numeral_string_int, numeral_string_float))(input)
}

fn numeral_string_int(input: &'static str) -> IResult<&'static str, &'static str> {
    terminated(
        alt((
            recognize(nom_tuple((alt((tag("0x"), tag("0X"))), hex_digit1))),
            recognize(nom_tuple((
                alt((tag("0b"), tag("0B"))),
                many1(alt((char('0'), char('1')))),
            ))),
            digit1,
        )),
        not(tag(".")),
    )(input)
}

fn numeral_string_float(input: &'static str) -> IResult<&'static str, &'static str> {
    preceded(not(tag("+")), recognize_float)(input)
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

fn operator(input: &'static str) -> IResult<&'static str, UnresolvedName> {
    map(
        ws(alt((
            verify(recognize(many1(operator_char)), |s| !is_reserved(s)),
            delimited(char('`'), ident, char('`')),
        ))),
        UnresolvedName::Unqualified,
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
            | "|"
    )
}
