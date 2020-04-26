#![warn(clippy::perf)]

mod position;
mod reader;

#[derive(Debug)]
enum Token<'a> {
    Keyword(Keyword),
    TypeIdent(&'a str),
    NameIdent(&'a str),
    Oper(Oper),
    Punc(Punc),
    Num(&'a str),
    Parens(Vec<(usize, Token<'a>)>),
    Curlys(Vec<(usize, Token<'a>)>),
    Squares(Vec<(usize, Token<'a>)>),
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
    fn parse(oper: &str) -> Option<Oper> {
        use Oper::*;
        match oper {
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
            ">=" => Some(GTOrEqual),
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
    fn parse(punc: &str) -> Option<Punc> {
        use Punc::*;
        match punc {
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

fn first_char_from(s: &str, i: usize) -> Option<(char, usize)> {
    let mut ci = s.get(i..)?.char_indices();
    let (_, c) = ci.next()?;
    let (j, _) = ci.next().unwrap_or((s.len(), '0'));
    Some((c, i + j))
}

impl Token<'_> {
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
        s: &str,
    ) -> Option<(&str, usize)> {
        let (c, mut i) = first_char_from(s, 0)?;
        if !start(c) {
            return None;
        }
        if !term(c) {
            while let Some((c, j)) = first_char_from(s, i) {
                if !mid(c) {
                    break;
                }
                i = j;
                if term(c) {
                    break;
                }
            }
        }
        return Some((&s[..i], i));
    }

    /// parses a `Token::Oper`
    fn oper(s: &str) -> Option<(Token, usize)> {
        let (oper_str, i) = Self::consume(is_oper, is_oper, is_single_oper, s)?;
        Some((Token::Oper(Oper::parse(oper_str)?), i))
    }

    /// parses a `Token::Num`
    fn num(s: &str) -> Option<(Token, usize)> {
        let (n, i) = Self::consume(
            |c| c.is_ascii_digit(),
            |c| c.is_alphanumeric() || c == '_',
            |_| false,
            s,
        )?;
        Some((Token::Num(n), i))
    }

    /// parses a `Token::Punc`
    fn punc(s: &str) -> Option<(Token, usize)> {
        let (punc_str, i) = Self::consume(is_punc, is_punc, is_single_punc, s)?;
        Some((Token::Punc(Punc::parse(punc_str)?), i))
    }

    /// parses a `Token::NameIdent`, `Token::TypeIdent` or `Token::Keyword`
    fn name(s: &str) -> Option<(Token, usize)> {
        let (name, i) = Self::consume(
            |c| c.is_ascii_lowercase(),
            |c| c.is_ascii_alphanumeric() || c == '_',
            |_| false,
            s,
        )?;
        Some((
            if let Some(keyword) = Keyword::parse(name) {
                Token::Keyword(keyword)
            } else if is_special_type(name) {
                Token::TypeIdent(name)
            } else {
                Token::NameIdent(name)
            },
            i,
        ))
    }
    fn typ(s: &str) -> Option<(Token, usize)> {
        let (ident, i) = Self::consume(
            |c| c.is_ascii_uppercase(),
            |c| c.is_ascii_alphanumeric() || c == '_',
            |_| false,
            s,
        )?;
        Some((Token::TypeIdent(ident), i))
    }

    /// parses a `Token::Bracketed` or a `Token::Curlied`
    fn block(s: &str) -> Option<(Token, usize)> {
        let (c, i) = first_char_from(s, 0)?;
        match c {
            '(' => {
                let (blk, i) = Self::parse(|c| c == ')', s.get(i..)?);
                Some((Token::Parens(blk), i))
            }
            '{' => {
                let (blk, i) = Self::parse(|c| c == '}', s.get(i..)?);
                Some((Token::Curlys(blk), i))
            }
            '[' => {
                let (blk, i) = Self::parse(|c| c == ']', s.get(i..)?);
                Some((Token::Squares(blk), i))
            }
            _ => None,
        }
    }
    /// Parses 1 token from s. This discards leading whitespace. If stop returns true for the first
    /// non-whitespace character then it is consumed and None is returned.
    fn parse_next(stop: impl Fn(char) -> bool, s: &str) -> (Option<(usize, Token)>, usize) {
        let mut i = 0;
        loop {
            if let Some((c, j)) = first_char_from(s, i) {
                if is_whitespace(c) {
                    i = j;
                } else if stop(c) {
                    return (None, j);
                } else {
                    break;
                }
            } else {
                return (None, i);
            }
        }
        if let Some(s) = s.get(i..) {
            if let Some((t, l)) = Self::num(s)
                .or_else(|| Self::name(s))
                .or_else(|| Self::typ(s))
                .or_else(|| Self::punc(s))
                .or_else(|| Self::block(s))
                .or_else(|| Self::oper(s))
                .or_else(|| first_char_from(s, 0).map(|(c, i)| (Token::InvalidChar(c), i)))
            {
                return (Some((i, t)), i + l);
            }
        }
        return (None, i);
    }

    /// Takes a Reader of chars and parses it to tokens.
    /// We might could have this return Iterator<Token>? Not sure how much of a benifit that
    /// would be.
    /// During parsing, if an invalid token is encountered it is given as a `TokenKind::InvalidChar`.
    /// Mismatched enclosing characters will result in
    fn parse(
        stop: impl Fn(char) -> bool + Copy, /* Max, what's best here? +Copy or passing a reference around? */
        s: &str,
    ) -> (Vec<(usize, Token)>, usize) {
        let mut out = Vec::with_capacity(4096);
        let mut i = 0;
        while let Some((op, l)) = s.get(i..).map(|ss| Self::parse_next(stop, ss)) {
            i += l;
            if let Some(p) = op {
                out.push(p);
            } else {
                break;
            }
        }
        (out, i)
    }
}

fn main() -> std::io::Result<()> {
    let s = "a bc def 123hi  var2; let a = (b+c) / 2";
    //let mut s = String::new();
    //std::fs::File::open("input")?.read_to_string(&mut s)?;
    println!("{:?}", Token::parse(|_| false, s,));
    Ok(())
}
