use crate::errors::{self, PrettyError};
use ansi_term::Color::Red;
use std::fmt::{self, Display, Formatter};
use std::ops::Range;

pub mod auto_sep;

pub fn tokenize(input: &str) -> Vec<Token> {
    Token::parse(|_| false, input).0
}

/// Produces all of the invalid tokens from a list, recursively
pub fn collect_invalid<'a>(tokens: &'a [Token<'a>]) -> Vec<InvalidChar> {
    use TokenKind::{Curlys, Parens, Squares};

    // This is inefficient, but that's okay. We don't need this to be industrial grade right now.
    let mut invalids = Vec::new();
    for t in tokens {
        match &t.kind {
            Parens(ts) | Curlys(ts) | Squares(ts) => {
                invalids.extend_from_slice(&collect_invalid(&ts))
            }
            &TokenKind::InvalidChar(c) => {
                let byte_range = t.byte_idx..t.byte_idx + c.len_utf8();
                invalids.push(InvalidChar {
                    byte_range,
                    invalid: c,
                });
            }
            _ => (),
        }
    }

    invalids
}

/// Returns a comma-separated list of slices of the original given list, each paired with the
/// trailing comma, if it was in the middle of the list.
pub fn split_at_commas<'a>(
    tokens: &'a [Token<'a>],
) -> Vec<(&'a [Token<'a>], Option<&'a Token<'a>>)> {
    let mut out = Vec::with_capacity(tokens.len() / 2);
    let mut i = 0;

    for j in 0..tokens.len() {
        if let TokenKind::Punc(Punc::Comma) = tokens[j].kind {
            out.push((&tokens[i..j], Some(&tokens[j])));
            i = j + 1;
        }
    }
    if i < tokens.len() {
        out.push((&tokens[i..tokens.len()], None));
    }
    out
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token<'a> {
    /// The starting position of the token in the bytes of the file
    pub byte_idx: usize,

    /// The content of the token
    pub kind: TokenKind<'a>,
}

#[derive(Debug, Clone)]
pub struct InvalidChar {
    /// The range of bytes in the source file taken up by the character
    ///
    /// For most characters, this will have length exactly equal to one, but some may be longer.
    pub byte_range: Range<usize>,

    /// The character that was invalid
    pub invalid: char,
}

impl PrettyError for InvalidChar {
    fn pretty_format(&self, file_str: &str, file_name: &str) -> String {
        // The error message is going to be relatively simple here. It'll look something like:
        // ```
        // error: unexpected character '$'
        //  --> src/test_input.tc:5:11
        //   |
        // 5 |     print $foo;
        //   |           ^
        // ```

        // And now we finally write the message
        format!(
            "{}: unexpected character {:?}\n{}",
            Red.paint("error"),
            self.invalid,
            errors::context_lines(self.byte_range.clone(), file_str, file_name)
        )
    }
}

impl Token<'_> {
    /// Returns the range of bytes in the original source file corresponding to this token
    ///
    /// The return value will be None iff the token is fake.
    ///
    /// It should be noted that this function is currently not perfect; there isn't any way to
    /// track the end of parentheticals, so we just guess - it's usually correct, but will be off
    /// sometimes. That's left up to improvement down the road.
    pub fn byte_range(&self) -> Option<Range<usize>> {
        use TokenKind::{
            Curlys, Fake, InvalidChar, Keyword, NameIdent, Num, Oper, Parens, ProofLine, Punc,
            Squares, TypeIdent,
        };

        let start = self.byte_idx;

        match &self.kind {
            Keyword(kwd) => Some(start..start + kwd.len()),
            TypeIdent(s) | NameIdent(s) | Num(s) => Some(start..start + s.len()),
            Oper(op) => Some(start..start + op.len()),
            Punc(p) => Some(start..start + p.len()),
            Parens(ts) | Curlys(ts) | Squares(ts) | ProofLine(ts) => {
                let end = match ts.as_ref() as &[_] {
                    [] => start + 1,
                    [.., last] => (last as &Token).byte_range()?.end,
                };

                match self.kind {
                    ProofLine(_) => Some(start..end),
                    // We add 1 on everything else because they have closing delimeters not
                    // captured here - it's part of a best-effort attempt to span the correct
                    // amount
                    _ => Some(start..end + 1),
                }
            }
            InvalidChar(_) | Fake => None,
        }
    }
}

pub static FAKE_TOKEN: Token = Token {
    byte_idx: 0,
    kind: TokenKind::Fake,
};

#[derive(Debug, Clone, PartialEq)]
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
    ProofLine(Vec<Token<'a>>),
    InvalidChar(char),
    Fake,
}

macro_rules! exact {
    (
        $(#[$attrs:meta])*
        pub enum $tyname:ident {
            $($variant:ident => $lit:expr,)+
        }
    ) => {
        $(#[$attrs])*
        pub enum $tyname {
            $($variant,)+
        }

        impl $tyname {
            fn parse(this: &str) -> Option<$tyname> {
                match this {
                    $($lit => Some($tyname::$variant),)+
                    _ => None,
                }
            }

            /// Returns the length in bytes/chars
            fn len(&self) -> usize {
                match self {
                    $($tyname::$variant => $lit.len(),)+
                }
            }
        }

        impl Display for $tyname {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                match self {
                    $($tyname::$variant => write!(f, $lit),)+
                }
            }
        }
    }
}

exact! {
    #[derive(Debug, Copy, Clone, PartialEq)]
    pub enum Keyword {
        Fn => "fn",
        If => "if",
        Let => "let",
        Type => "type",
        Print => "print",
        Return => "return",
        Require => "require",
        Lemma => "lemma",
    }
}

exact! {
    #[derive(Debug, Copy, Clone, PartialEq)]
    pub enum Oper {
        Add => "+",
        Sub => "-",
        Star => "*",
        Div => "/",
        Ref => "&",
        Assign => "=",
        Equals => "==",
        Lt => "<",
        LtOrEqual => "<=",
        Gt => ">",
        GtOrEqual => ">=",
        Not => "!",
        RightArrow => "->",
        Implies => "=>",
        LongImplies => "==>",
        LongImpliedBy => "<==",
        Or => "||",
        And => "&&",
    }
}

impl Oper {
    /// returns true if newlines are allowed before this operator
    fn newline_prefix_allowed(self) -> bool {
        use Oper::*;
        match self {
            Add | Sub | Star | Div | Assign | Equals | Lt | LtOrEqual | Gt | GtOrEqual
            | RightArrow | Or | And => true,
            _ => false,
        }
    }

    /// returns true if newlines are allowed after this operator
    fn newline_postfix_allowed(self) -> bool {
        // right now, this is all of them
        true
    }
}

/// returns true if `ch` is an operator character.
fn is_oper(ch: char) -> bool {
    is_single_oper(ch)
        || match ch {
            '+' | '-' | '=' | '/' | '*' | '.' | '<' | '>' | '&' | '|' => true,
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

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Punc {
    Dot,
    Comma,
    Colon,
    Semi,
    Newline,
    Sep,
}

impl Punc {
    fn parse(punc: &str) -> Option<Punc> {
        use Punc::*;
        match punc {
            "." => Some(Dot),
            "," => Some(Comma),
            ":" => Some(Colon),
            ";" => Some(Semi),
            "\n" => Some(Newline),
            _ => None,
        }
    }

    fn len(&self) -> usize {
        // All punctuation has the smae length
        1
    }
}

fn is_whitespace(ch: char) -> bool {
    ch == ' ' || ch == '\t'
}

fn is_special_type(s: &str) -> bool {
    // Currently, we're only supporting `int`s, `uint`s and `bool`s
    s == "int" || s == "uint" || s == "bool"
}

fn is_punc(ch: char) -> bool {
    match ch {
        '.' | ',' | ':' | ';' | '\n' => true,
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
        Some((&s[..i], i))
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
            |c| c.is_ascii_lowercase() || c == '_',
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

    fn proof(s: &str) -> Option<(TokenKind, usize)> {
        let (proof_line, i) = Self::consume(|c| c == '#', |_| true, |c| c == '\n', s)?;
        // We parse the entire line as a set of tokens, excluding the first character, because it's
        // a `#` and is not used outside of distinguishing this line as for proof.
        //
        // We also exclude the final character, because it is always guaranteed to be a newline.
        let (mut tokens, _) = Token::parse(|_| false, &proof_line[1..proof_line.len() - 1]);
        // Shift them all by one to account for the leading '#'.
        tokens.iter_mut().for_each(|t| t.shift_idx(1));
        Some((TokenKind::ProofLine(tokens), i))
    }

    /// parses a `Token::Bracketed` or a `Token::Curlied`
    fn block(s: &str) -> Option<(TokenKind, usize)> {
        let (c, i) = first_char_from(s, 0)?;
        // We always return j + 1 because we need to account for the trailing close delimeter
        match c {
            '(' => {
                let (mut blk, j) = Token::parse(|c| c == ')', s.get(i..)?);
                blk.iter_mut().for_each(|t| t.shift_idx(i));
                Some((TokenKind::Parens(blk), j + 1))
            }
            '{' => {
                let (mut blk, j) = Token::parse(|c| c == '}', s.get(i..)?);
                blk.iter_mut().for_each(|t| t.shift_idx(i));
                Some((TokenKind::Curlys(blk), j + 1))
            }
            '[' => {
                let (mut blk, j) = Token::parse(|c| c == ']', s.get(i..)?);
                blk.iter_mut().for_each(|t| t.shift_idx(i));
                Some((TokenKind::Squares(blk), j + 1))
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
            .or_else(|| Self::proof(s))
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
                let mut token = Token { byte_idx: 0, kind };
                token.shift_idx(byte_idx + idx);
                // let mut token = Token { byte_idx, kind };
                // token.shift_idx(idx);
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
        use TokenKind::{Curlys, Parens, ProofLine, Squares};

        self.byte_idx += amount;
        match &mut self.kind {
            Parens(ts) | Curlys(ts) | Squares(ts) | ProofLine(ts) => {
                for token in ts.iter_mut() {
                    token.shift_idx(amount);
                }
            }
            _ => (),
        }
    }
}

impl Display for Punc {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Punc::*;
        match self {
            Dot => write!(f, "."),
            Comma => write!(f, ","),
            Colon => write!(f, ":"),
            Semi | Sep => write!(f, ";"),
            Newline => write!(f, "newline"),
        }
    }
}
