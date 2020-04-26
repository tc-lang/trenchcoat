#![warn(clippy::perf)]

use std::fmt::{self, Debug};
use std::io::prelude::*;

mod position;
mod reader;
use position::Position;
use reader::Reader;

#[derive(Debug)]
enum Token {
    Keyword(Keyword),
    TypeIdent(String),
    NameIdent(String),
    Oper(Oper),
    Punc(Punc),
    Num(String),
    Bracketed(Vec<(Position, Token)>),
    Curlied(Vec<(Position, Token)>),
    InvalidChar(char),
}

/*
impl Token {
    /// fmt_write writes "kind(value) " to the formatter.
    fn fmt_write(f: &mut fmt::Formatter, kind: &str, value: &str) -> Result<(), fmt::Error> {
        f.write_str(kind)?;
        f.write_str("(")?;
        f.write_str(&*value)?;
        f.write_str(") ")
    }

    /// fmt_vec calls `t.fmt(f)` for each t in ts.
    fn fmt_vec(f: &mut fmt::Formatter, ts: &[(Position, Token)]) -> Result<(), fmt::Error> {
        for (_, t) in ts {
            t.fmt(f)?;
        }
        Ok(())
    }
}

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use Token::*;
        match self {
            Keyword(kw) => Self::fmt_write(f, Keyword, fmt!("{:?}", kw)),
            TypeIdent(s) => Self::fmt_write(f, "Type", s),
            NameIdent(s) => Self::fmt_write(f, "Name", s),
            Oper(s) => Self::fmt_write(f, "Op", fmt!("{:?}", kw)),
            Punc(s) => {
                if s == "\n" {
                    f.write_str("\n")
                } else {
                    Self::fmt_write(f, "Punc", s)
                }
            }
            Num(s) => Self::fmt_write(f, "Num", s),
            Bracketed(ts) => {
                f.write_str("(")?;
                Self::fmt_vec(f, ts)?;
                f.write_str(") ")
            }
            Curlied(ts) => {
                f.write_str("{")?;
                Self::fmt_vec(f, ts)?;
                f.write_str("} ")
            }
            InvalidChar(_) => f.write_str("-INVALID CHAR-"),
        }
    }
}
*/

#[derive(Debug)]
enum Keyword {
    Fn,
    If,
    Let,
    Type,
    Match,
    Return,
}

impl Keyword {
    fn parse(keyword: &str) -> Option<Keyword> {
        use Keyword::*;
        match keyword {
            "fn" => Some(Fn),
            "if" => Some(If),
            "let" => Some(Let),
            "type" => Some(Type),
            "match" => Some(Match),
            "return" => Some(Return),
            _ => None,
        }
    }
}

#[derive(Debug)]
enum Oper {
    Add,
    Sub,
    Astrix,
    Div,
    Pow,
    Inc,
    Dec,
    Question,
    Dot, // I'm not going to define syntax for ranges
    Ref,
    Assign,
    Equals,
    LT,
    LTOrEqual,
    GT,
    GTOrEqual,
    Not,
    RightArrow,
    LeftArrow, // they're the wrong way round, deal with it.
    FuncArrow,
    Or,
    And,
}

impl Oper {
    fn parse(oper: String) -> Option<Oper> {
        use Oper::*;
        match &*oper {
            "+" => Some(Add),
            "-" => Some(Sub),
            "*" => Some(Astrix),
            "**" => Some(Pow),
            "/" => Some(Div),
            "++" => Some(Inc),
            "--" => Some(Dec),
            "." => Some(Dot),
            "&" => Some(Ref),
            "?" => Some(Question),
            "=" => Some(Assign),
            "==" => Some(Equals),
            "<" => Some(LT),
            "<=" => Some(LTOrEqual),
            ">" => Some(GT),
            "<=" => Some(GTOrEqual),
            "!" => Some(Not),
            "->" => Some(RightArrow),
            "<-" => Some(LeftArrow),
            "=>" => Some(FuncArrow),
            "||" => Some(Or),
            "&&" => Some(And),
            _ => None,
        }
    }
}

///returns true if `ch` is an operator character.
fn is_oper(ch: char) -> bool {
    (match ch {
        '+' | '-' | '=' | '/' | '*' | '.' | '<' | '>' => true,
        _ => false,
    }) || is_single_oper(ch) // it's a shame the match has to be in brackets :(
}
///returns true if `ch` is a 'single' operator character. A single operator char is one where
///multiple characters next to eachother compounds the operator rather than referring to a
///different operator.
///For example, `+` is not a single operator char since it is distinct from `++` whereas
///             `!` is a single operator char since `!!x` is equivilent to `!(!x)`.
fn is_single_oper(ch: char) -> bool {
    match ch {
        '?' | '!' | '&' | '*' => true,
        _ => false,
    }
}

#[derive(Debug)]
enum Punc {
    Comma,
    //Dot? This would have to be added as a special case to the operator parser
    Colon,
    SemiColon,
}

impl Punc {
    fn parse(punc: String) -> Option<Punc> {
        use Punc::*;
        match &*punc {
            "," => Some(Comma),
            ":" => Some(Colon),
            ";" => Some(SemiColon),
            _ => None,
        }
    }
}

fn is_whitespace(ch: char) -> bool {
    ch == ' ' || ch == '\t'
}

fn is_special_type(s: &str) -> bool {
    match s {
        "int" | "uint" | "bool" | "i8" | "u8" | "i16" | "u16" | "i32" | "u32" | "i64" | "u64"
        | "f32" | "f64" => true,
        _ => false,
    }
}

fn is_punc(ch: char) -> bool {
    (match ch {
        ':' => true,
        _ => false,
    }) || is_single_punc(ch)
}

/// for the distinction between single chars and normal chars, see the documentation for
/// `is_single_oper`.
fn is_single_punc(ch: char) -> bool {
    match ch {
        '\n' | ',' | ';' => true,
        _ => false,
    }
}

/// like s.skip(1), but returns the same type as was passed.
/// Is there a std lib way to do this?? I couldn't find it.
fn skip1<T: Iterator>(i: &mut T) -> &mut T {
    i.next();
    i
}

impl Token {
    /// consume forms the basis for most token parsing.
    /// It consumes a token described by `start`, `mid` and `term` from `s`.
    /// The token will:
    ///  1) start with a character, `c` where `start(c)` is true,
    ///  2) must only consist further of characters, `c`, for which `mid(c)` is true and
    ///  3) if a character, `c` has `term(c)` then that will be the final character.
    fn consume(
        start: impl Fn(char) -> bool,
        mid: impl Fn(char) -> bool,
        term: impl Fn(char) -> bool,
        cap: usize,
        s: &mut Reader<impl Iterator<Item = char>>,
    ) -> Option<String> {
        let mut out = String::with_capacity(cap);
        let c = *s.peek()?;
        if !start(c) {
            return None;
        }
        out.push(s.next()?);
        if term(c) {
            return Some(out);
        }
        loop {
            if let Some(&c) = s.peek() {
                if mid(c) {
                    out.push(s.next().unwrap());
                    if !term(c) {
                        continue;
                    }
                }
            }
            break;
        }
        Some(out)
    }

    /// parses a `Token::Oper`
    fn oper(s: &mut Reader<impl Iterator<Item = char>>) -> Option<Token> {
        Self::consume(is_oper, is_oper, is_single_oper, 2, s)
            .and_then(Oper::parse)
            .map(Token::Oper)
    }

    /// parses a `Token::Num`
    fn num(s: &mut Reader<impl Iterator<Item = char>>) -> Option<Token> {
        Self::consume(
            |c| c.is_ascii_digit(),
            |c| c.is_alphanumeric() || c == '_',
            |_| false,
            4,
            s,
        )
        .map(Token::Num)
    }

    /// parses a `Token::Punc`
    fn punc(s: &mut Reader<impl Iterator<Item = char>>) -> Option<Token> {
        Self::consume(is_punc, is_punc, is_single_punc, 2, s)
            .and_then(Punc::parse)
            .map(Token::Punc)
    }

    /// parses a `Token::NameIdent`, `Token::TypeIdent` or `Token::Keyword`
    fn name(s: &mut Reader<impl Iterator<Item = char>>) -> Option<Token> {
        enum FirstChar {
            Upper,
            Lower,
        }
        let mut out = String::with_capacity(8);
        let mut fc = FirstChar::Lower;
        let c = *s.peek()?;
        if c.is_ascii_uppercase() {
            fc = FirstChar::Upper;
        } else if !c.is_ascii_lowercase() && c != '_' {
            return None;
        }
        out.push(s.next()?);
        loop {
            if let Some(&c) = s.peek() {
                if c.is_ascii_alphanumeric() || c == '_' {
                    out.push(s.next().unwrap());
                    continue;
                }
            }
            break;
        }
        Some(if let FirstChar::Lower = fc {
            // is there a better way to do this?
            if let Some(keyword) = Keyword::parse(&*out) {
                Token::Keyword(keyword)
            } else if is_special_type(&*out) {
                Token::TypeIdent(out)
            } else {
                Token::NameIdent(out)
            }
        } else {
            Token::TypeIdent(out)
        })
    }

    /// parses a `Token::Bracketed` or a `Token::Curlied`
    fn block(s: &mut Reader<impl Iterator<Item = char>>) -> Option<Token> {
        match *s.peek()? {
            '(' => Some(Token::Bracketed(Self::parse(|c| c == ')', skip1(s)))),
            '{' => Some(Token::Curlied(Self::parse(|c| c == '}', skip1(s)))),
            _ => None,
        }
    }
    /// Parses 1 token from s. This discards leading whitespace. If stop returns true for the first
    /// non-whitespace character then it is consumed and None is returned.
    fn parse_next(
        stop: impl Fn(char) -> bool,
        s: &mut Reader<impl Iterator<Item = char>>,
    ) -> Option<(Position, Token)> {
        loop {
            let c = *s.peek()?;
            if is_whitespace(c) {
                s.next()?;
            } else if stop(c) {
                s.next()?;
                return None;
            } else {
                break;
            }
        }
        let pos = s.position();
        Self::num(s)
            .or_else(|| Self::name(s))
            .or_else(|| Self::punc(s))
            .or_else(|| Self::block(s))
            .or_else(|| Self::oper(s))
            .or_else(|| Some(Token::InvalidChar(s.next()?)))
            .map(|t| (pos, t))
    }

    /// Takes a Reader of chars and parses it to tokens.
    /// We might could have this return Iterator<Token>? Not sure how much of a benifit that
    /// would be.
    /// During parsing, if an invalid token is encountered it is given as a `TokenKind::InvalidChar`.
    /// Mismatched enclosing characters will result in
    fn parse(
        stop: impl Fn(char) -> bool + Copy, /* Max, what's best here? +Copy or passing a reference around? */
        s: &mut Reader<impl Iterator<Item = char>>,
    ) -> Vec<(Position, Token)> {
        let mut out = Vec::with_capacity(4096);
        loop {
            match Self::parse_next(stop, s) {
                Some(t) => out.push(t),
                None => return out,
            }
        }
    }
}

fn main() -> std::io::Result<()> {
    let s = "a bc def 123hi  var2; let a = (b+c) / 2".to_string();
    //let mut s = String::new();
    //std::fs::File::open("input")?.read_to_string(&mut s)?;
    println!(
        "{:?}",
        Token::Curlied(Token::parse(
            |_| false,
            &mut Reader::new(&mut s.chars().peekable())
        ))
    );
    Ok(())
}
