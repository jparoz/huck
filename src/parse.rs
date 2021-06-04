use nom::branch::alt;
use nom::bytes::complete::{escaped, is_not, tag};
use nom::character::complete::{char, hex_digit1, multispace0, one_of, satisfy};
use nom::combinator::{map, not, opt, recognize, success, verify};
use nom::multi::{many0, many1, separated_list0};
use nom::number::complete::recognize_float;
use nom::sequence::{delimited, preceded, separated_pair, terminated, tuple};
use nom::IResult;

use std::collections::HashMap;

use crate::ast::*;
use crate::error::*;

#[cfg(test)]
mod tests;

pub fn parse(input: &str) -> Result<Chunk> {
    match preceded(ws(success(())), chunk)(input) {
        Ok((leftover, c)) => {
            if !leftover.is_empty() {
                println!("WARNING: leftover:\n{:?}\n", leftover);
            }
            Ok(c)
        }
        Err(nom) => Err(Error::Nom(nom.to_string())),
    }
}

fn chunk(input: &str) -> IResult<&str, Chunk> {
    let (leftovers, assigns) = ws(many0(assign))(input)?;
    let mut env = HashMap::new();

    for (lhs, expr) in assigns {
        env.entry(lhs.name).or_insert(Vec::new()).push((lhs, expr));
    }

    Ok((leftovers, Chunk::new(env)))
}

fn assign(input: &str) -> IResult<&str, (Lhs, Expr)> {
    terminated(separated_pair(lhs, equals, expr), semi)(input)
}

fn lhs(input: &str) -> IResult<&str, Lhs> {
    map(tuple((name, many0(pattern))), |(name, args)| Lhs {
        name,
        args,
    })(input)
}

fn pattern(input: &str) -> IResult<&str, Pattern> {
    alt((
        map(name, Pattern::Var),
        map(list(pattern), Pattern::List),
        map(string, Pattern::String),
        map(
            parens(tuple((pattern, operator, pattern))),
            |(lhs, op, rhs)| Pattern::Destructure {
                constructor: op,
                args: vec![lhs, rhs],
            },
        ),
        map(
            parens(tuple((name, many0(pattern)))),
            |(constructor, args)| Pattern::Destructure { constructor, args },
        ),
    ))(input)
}

fn expr(input: &str) -> IResult<&str, Expr> {
    alt((binop, app))(input)
}

fn binop(input: &str) -> IResult<&str, Expr> {
    map(tuple((app, operator, expr)), |(lhs, operator, rhs)| {
        Expr::Binop {
            operator,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    })(input)
}

fn app(input: &str) -> IResult<&str, Expr> {
    map(tuple((term, many0(term))), |(t, ts)| {
        ts.into_iter()
            .map(Expr::Term)
            // @Note: why doesn't .reduce() work here?? Rust can't find the method
            // .reduce(|a, b| Expr::App {
            //     func: Box::new(a),
            //     argument: Box::new(b),
            // })
            // .unwrap() // safe unwrap because we're mapping over many1(term)
            .fold(Expr::Term(t), |a, b| Expr::App {
                func: Box::new(a),
                argument: Box::new(b),
            })
    })(input)
}

fn term(input: &str) -> IResult<&str, Term> {
    alt((
        map(numeral_positive, Term::Numeral),
        map(parens(numeral_negative), Term::Numeral),
        map(string, Term::String),
        map(list(expr), Term::List),
        map(name, Term::Name),
        map(parens(expr), |e| Term::Parens(Box::new(e))),
    ))(input)
}

fn name(input: &str) -> IResult<&str, Name> {
    ws(map(
        recognize(tuple((
            satisfy(is_name_start_char),
            many0(satisfy(is_name_char)),
        ))),
        Name,
    ))(input)
}

fn numeral(input: &str) -> IResult<&str, &str> {
    ws(alt((
        recognize(tuple((alt((tag("0x"), tag("0X"))), hex_digit1))),
        recognize(tuple((
            alt((tag("0b"), tag("0B"))),
            many1(alt((char('0'), char('1')))),
        ))),
        recognize_float,
    )))(input)
}

fn numeral_positive(input: &str) -> IResult<&str, &str> {
    preceded(not(tag("-")), numeral)(input)
}

fn numeral_negative(input: &str) -> IResult<&str, &str> {
    recognize(tuple((tag("-"), numeral)))(input)
}

fn string(input: &str) -> IResult<&str, &str> {
    // "hello, world"
    ws(recognize(delimited(
        char('"'),
        map(
            opt(escaped(is_not("\\\""), '\\', one_of("\\\"'abfnrtv"))),
            |res| res.unwrap_or(""),
        ),
        char('"'),
    )))(input)
}

fn list<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, Vec<O>>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(ws(tag("[")), separated_list0(comma, inner), ws(tag("]")))
}

fn operator(input: &str) -> IResult<&str, Name> {
    map(ws(recognize(many1(one_of("=+-|!@#$%^&*:./~")))), Name)(input)
}

fn equals(input: &str) -> IResult<&str, Name> {
    verify(operator, |name| name.0 == "=")(input)
}

fn semi(input: &str) -> IResult<&str, &str> {
    ws(tag(";"))(input)
}

fn comma(input: &str) -> IResult<&str, &str> {
    ws(tag(","))(input)
}

fn ws<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    // @Todo: comments

    // let short_comment = delimited(tag("--"), take_till(|c| c == '\n'), char('\n'));
    // let long_comment = preceded(tag("--"), long_string);

    // let comment = alt((long_comment, short_comment));

    // let whitespace = many0(alt((value((), multispace0), value((), comment))));
    let whitespace = multispace0;

    terminated(inner, whitespace)
}

fn parens<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(ws(tag("(")), inner, ws(tag(")")))
}

fn is_name_char(c: char) -> bool {
    is_name_start_char(c) || c.is_numeric() || c == '\''
}

fn is_name_start_char(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}
