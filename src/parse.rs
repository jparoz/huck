use nom::branch::alt;
use nom::bytes::complete::{escaped, is_not, tag};
use nom::character::complete::{char, digit1, hex_digit1, multispace0, one_of, satisfy};
use nom::combinator::{map, opt, recognize, success, verify};
use nom::multi::{many0, many1, separated_list0};
use nom::number::complete::recognize_float;
use nom::sequence::{delimited, preceded, separated_pair, terminated, tuple};
use nom::IResult;

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
    // println!("chunk"); // @DebugParsing
    let (leftovers, assigns) = ws(many0(assign))(input)?;

    Ok((leftovers, Chunk::new(assigns.into_iter().collect())))
}

fn assign(input: &str) -> IResult<&str, (Name, Expr)> {
    // println!("assign"); // @DebugParsing
    terminated(separated_pair(name, equals, expr), semi)(input)
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
    // println!("term"); // @DebugParsing
    alt((
        map(numeral, Term::Numeral),
        map(string, Term::String),
        map(list, Term::List),
        map(name, Term::Name),
        map(parens(expr), |e| Term::Parens(Box::new(e))),
    ))(input)
}

fn name(input: &str) -> IResult<&str, Name> {
    // println!("name"); // @DebugParsing
    ws(map(
        recognize(tuple((
            satisfy(is_name_start_char),
            many0(satisfy(is_name_char)),
        ))),
        Name,
    ))(input)
}

fn numeral(input: &str) -> IResult<&str, &str> {
    // println!("numeral"); // @DebugParsing
    ws(alt((
        recognize(tuple((alt((tag("0x"), tag("0X"))), hex_digit1))),
        recognize(tuple((
            alt((tag("0b"), tag("0B"))),
            many1(alt((char('0'), char('1')))),
        ))),
        recognize_float,
        digit1,
    )))(input)
}

fn string(input: &str) -> IResult<&str, &str> {
    // println!("string"); // @DebugParsing
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

fn list(input: &str) -> IResult<&str, Vec<Expr>> {
    // println!("list"); // @DebugParsing
    delimited(ws(tag("[")), separated_list0(comma, expr), ws(tag("]")))(input)
}

fn operator(input: &str) -> IResult<&str, &str> {
    // println!("operator"); // @DebugParsing
    ws(recognize(many1(one_of("=+-|!@#$%^&*:./~"))))(input)
}

fn equals(input: &str) -> IResult<&str, &str> {
    // println!("equals"); // @DebugParsing
    verify(operator, |s: &str| s == "=")(input)
}

fn semi(input: &str) -> IResult<&str, &str> {
    // println!("semi"); // @DebugParsing
    ws(tag(";"))(input)
}

fn comma(input: &str) -> IResult<&str, &str> {
    // println!("comma"); // @DebugParsing
    ws(tag(","))(input)
}

fn ws<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    // println!("ws"); // @DebugParsing
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
    // println!("parens"); // @DebugParsing
    delimited(ws(tag("(")), inner, ws(tag(")")))
}

fn is_name_char(c: char) -> bool {
    is_name_start_char(c) || c.is_numeric() || c == '\''
}

fn is_name_start_char(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}
