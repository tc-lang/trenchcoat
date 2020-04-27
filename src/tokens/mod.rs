mod position;
mod reader;

pub fn tokenize(s: &str) -> Vec<Token> {
    Token::parse(|_| false, s).0
}

/// Produces all of the invalid tokens from a list, recursively
pub fn collect_invalid<'a>(tokens: &'a [Token<'a>]) -> Vec<&'a Token<'a>> {
    use TokenKind::*;

    // This is inefficient, but that's okay. We don't need this to be industrial grade right now.
    let mut invalids = Vec::new();
    for t in tokens {
        match &t.kind {
            Parens(ts) | Curlys(ts) | Squares(ts) => {
                invalids.extend_from_slice(&collect_invalid(&ts))
            }
            InvalidChar(_) => invalids.push(&t),
            _ => (),
        }
    }

    invalids
}

#[derive(Debug)]
pub struct Token<'a> {
    /// The starting position of the token in the bytes of the file
    byte_idx: usize,

    /// The content of the token
    kind: TokenKind<'a>,
}

#[derive(Debug)]
pub enum TokenKind<'a> {
    Keyword(Keyword),
    TypeIdent(&'a str),
    NameIdent(&'a str),
    Oper(Oper),
    Punc(Punc),
    Num(&'a str),
    Parens(Vec<Token<'a>>),
    Curlys(Vec<Token<'a>>),
    Squares(Vec<Token<'a>>),
    InvalidChar(char),
}

#[derive(Debug)]
pub enum Keyword {
    Fn,
    If,
    Let,
    Type,
    Return,
    Print,
}

impl Keyword {
    fn parse(keyword: &str) -> Option<Keyword> {
        use Keyword::*;
        match keyword {
            "fn" => Some(Fn),
            "if" => Some(If),
            "let" => Some(Let),
            "type" => Some(Type),
            "print" => Some(Print),
            "return" => Some(Return),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub enum Oper {
    Add,
    Sub,
    Star,
    Div,
    Ref,
    Assign,
    Equals,
    LT,
    LTOrEqual,
    GT,
    GTOrEqual,
    Not,
    RightArrow,
    Or,
    And,
}

impl Oper {
    fn parse(oper: &str) -> Option<Oper> {
        use Oper::*;
        match oper {
            "+" => Some(Add),
            "-" => Some(Sub),
            "*" => Some(Star),
            "/" => Some(Div),
            "&" => Some(Ref),
            "=" => Some(Assign),
            "==" => Some(Equals),
            "<" => Some(LT),
            "<=" => Some(LTOrEqual),
            ">" => Some(GT),
            ">=" => Some(GTOrEqual),
            "!" => Some(Not),
            "->" => Some(RightArrow),
            "||" => Some(Or),
            "&&" => Some(And),
            _ => None,
        }
    }
}

/// returns true if `ch` is an operator character.
fn is_oper(ch: char) -> bool {
    is_single_oper(ch)
        || match ch {
            '+' | '-' | '=' | '/' | '*' | '.' | '<' | '>' => true,
            _ => false,
        }
}

/// returns true if `ch` is a 'single' operator character. A single operator char is one where
/// multiple characters next to eachother compounds the operator rather than referring to a
/// different operator.
///
/// For example, `+` is not a single operator char since it is distinct from `++` whereas `!` is a
/// single operator char since `!!x` is equivilent to `!(!x)`.
fn is_single_oper(ch: char) -> bool {
    match ch {
        '!' | '*' => true,
        _ => false,
    }
}

#[derive(Debug)]
pub enum Punc {
    Dot,
    Comma,
    Colon,
    Semi,
}

impl Punc {
    fn parse(punc: &str) -> Option<Punc> {
        use Punc::*;
        match punc {
            "." => Some(Dot),
            "," => Some(Comma),
            ":" => Some(Colon),
            ";" => Some(Semi),
            _ => None,
        }
    }
}

fn is_whitespace(ch: char) -> bool {
    ch == ' ' || ch == '\t' || ch == '\n'
}

fn is_special_type(s: &str) -> bool {
    // Currently, we're only supporting `uint`s and `bool`s
    s == "uint" || s == "bool"
}

fn is_punc(ch: char) -> bool {
    match ch {
        '.' | ',' | ':' | ';' => true,
        _ => false,
    }
}

/// Produces the first character in `s[idx..]`, paired with its byte index in `s`
fn first_char_from(s: &str, idx: usize) -> Option<(char, usize)> {
    let mut char_idxs = s.get(idx..)?.char_indices();
    let (_, ch) = char_idxs.next()?;
    let (ch_len, _) = char_idxs.next().unwrap_or((s.len() - idx, '0'));
    Some((ch, idx + ch_len))
}

impl TokenKind<'_> {
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

    /// parses a `TokenKind::Oper`
    fn oper(s: &str) -> Option<(TokenKind, usize)> {
        let (oper_str, i) = Self::consume(is_oper, is_oper, is_single_oper, s)?;
        if oper_str == "." {
            return Some((TokenKind::Punc(Punc::Dot), i));
        }
        Some((TokenKind::Oper(Oper::parse(oper_str)?), i))
    }

    /// parses a `TokenKind::Num`
    fn num(s: &str) -> Option<(TokenKind, usize)> {
        let (n, i) = Self::consume(
            |c| c.is_ascii_digit(),
            |c| c.is_alphanumeric() || c == '_',
            |_| false,
            s,
        )?;
        Some((TokenKind::Num(n), i))
    }

    /// parses a `TokenKind::Punc`
    fn punc(s: &str) -> Option<(TokenKind, usize)> {
        let (punc_str, i) = Self::consume(is_punc, is_punc, is_punc, s)?;
        Some((TokenKind::Punc(Punc::parse(punc_str)?), i))
    }

    /// Attempts to parse any of `TokenKind::{NameIdent, TypeIdent, Keyword}`
    fn name(s: &str) -> Option<(TokenKind, usize)> {
        let (name, i) = Self::consume(
            |c| c.is_ascii_lowercase(),
            |c| c.is_ascii_alphanumeric() || c == '_',
            |_| false,
            s,
        )?;
        Some((
            if let Some(keyword) = Keyword::parse(name) {
                TokenKind::Keyword(keyword)
            } else if is_special_type(name) {
                TokenKind::TypeIdent(name)
            } else {
                TokenKind::NameIdent(name)
            },
            i,
        ))
    }

    /// Attempts to parse a `TokenKind::TypeIdent`
    fn typ(s: &str) -> Option<(TokenKind, usize)> {
        let (ident, i) = Self::consume(
            |c| c.is_ascii_uppercase(),
            |c| c.is_ascii_alphanumeric() || c == '_',
            |_| false,
            s,
        )?;
        Some((TokenKind::TypeIdent(ident), i))
    }

    /// parses a `Token::Bracketed` or a `Token::Curlied`
    fn block(s: &str) -> Option<(TokenKind, usize)> {
        let (c, i) = first_char_from(s, 0)?;
        // We always return i + 1 because we need to account for the trailing close delimeter
        match c {
            '(' => {
                let (blk, i) = Token::parse(|c| c == ')', s.get(i..)?);
                Some((TokenKind::Parens(blk), i + 1))
            }
            '{' => {
                let (blk, i) = Token::parse(|c| c == '}', s.get(i..)?);
                Some((TokenKind::Curlys(blk), i + 1))
            }
            '[' => {
                let (blk, i) = Token::parse(|c| c == ']', s.get(i..)?);
                Some((TokenKind::Squares(blk), i + 1))
            }
            _ => None,
        }
    }

    /// Parses a single token from `s`, discarding leading whitespace if any exists
    ///
    /// Iff `stop` returns true for the first non-whitespace character, it is consumed and `None`
    /// is returned.
    fn parse_next(stop: impl Fn(char) -> bool, s: &str) -> (Option<(usize, TokenKind)>, usize) {
        let mut start_idx = 0;
        loop {
            match first_char_from(s, start_idx) {
                None => return (None, start_idx),
                Some((ch, offset)) => {
                    if is_whitespace(ch) {
                        start_idx = offset;
                        continue;
                    }

                    if stop(ch) {
                        return (None, offset);
                    }

                    break;
                }
            }
        }

        let s = match s.get(start_idx..) {
            None => return (None, start_idx),
            Some(s) => s,
        };

        let parse_result = Self::num(s)
            .or_else(|| Self::name(s))
            .or_else(|| Self::typ(s))
            // We do operators before punctuation because '..' is an operator that could
            // alternatively be seen as two of the punctuation '.', which is not the correct
            // way of parsing it.
            .or_else(|| Self::oper(s))
            .or_else(|| Self::punc(s))
            .or_else(|| Self::block(s))
            .or_else(|| {
                first_char_from(s, 0).map(|(c, start_idx)| (TokenKind::InvalidChar(c), start_idx))
            });

        match parse_result {
            Some((token, offset)) => (Some((start_idx, token)), start_idx + offset),
            None => (None, start_idx),
        }
    }
}

impl Token<'_> {
    /// Takes a Reader of chars and parses it to tokens.
    /// We might could have this return Iterator<Token>? Not sure how much of a benifit that
    /// would be.
    /// During parsing, if an invalid token is encountered it is given as a `TokenKind::InvalidChar`.
    /// Mismatched enclosing characters will result in
    fn parse(stop: impl Fn(char) -> bool, s: &str) -> (Vec<Token>, usize) {
        let mut out = Vec::new();
        // Our byte index in the string
        let mut idx = 0;

        while let Some((parse_result, offset)) =
            s.get(idx..).map(|s| TokenKind::parse_next(&stop, s))
        {
            if let Some((byte_idx, kind)) = parse_result {
                let mut token = Token { byte_idx, kind };
                token.shift_idx(idx);
                out.push(token);

                idx += offset;
            } else {
                idx += offset;
                break;
            }
        }

        (out, idx)
    }

    /// Internally shifts all of the indices forwards by a given amount
    ///
    /// This is so that the indices given by the token may be absolute in their location within the
    /// file
    fn shift_idx(&mut self, amount: usize) {
        use TokenKind::{Curlys, Parens, Squares};

        self.byte_idx += amount;
        match &mut self.kind {
            Parens(ts) | Curlys(ts) | Squares(ts) => {
                for token in ts.iter_mut() {
                    token.shift_idx(amount);
                }
            }
            _ => (),
        }
    }
}
