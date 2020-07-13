//! The second half of tokenizing
//!
//! The primary usage of this module is to take the output of [`crate::tokens`] and to construct
//! token trees from it.
//!
//! Token trees are a tree structure where certain matched characters (namely: parenthesis, square
//! brackets, and curly braces) are collapsed into a single node, where all of the children are
//! themselves nodes in the tree. This idea is primarily taken from Rust, which briefly mentions
//! them in [the reference](https://doc.rust-lang.org/stable/reference/tokens.html#delimiters).
//!
//! In addition to constructing token trees, the tokens here are additionally collapsed to be
//! independent of whitespace - each token may optionally have trailing whitespace or comments.
//!
//! Further details (e.g. how leading whitespace / comments at the start of a file are handled) can
//! be found in the description for the primary exported function from this module: [`file_tree`].
//!
//! [`crate::tokens`]: ../tokens/index.html
//! [`file_tree`]: fn.file_tree.html

use crate::error::{self, Builder as ErrorBuilder, ToError};
use crate::tokens;
pub use crate::tokens::{LiteralKind, SimpleToken};
use std::ops::Range;

// TODO: Document - gives the output of tokenizing the entire file.
pub fn file_tree<'a>(simple_tokens: &'a [SimpleToken<'a>]) -> FileTokenTree<'a> {
    // Trim any leading whitespace from the tokens
    use tokens::TokenKind::{BlockComment, LineComment, Whitespace};

    let n_leading_whitespace = simple_tokens
        .iter()
        .take_while(|t| match t.kind {
            Whitespace | LineComment | BlockComment => true,
            _ => false,
        })
        .count();

    let mut idx = n_leading_whitespace;
    let mut tokens = Vec::new();
    while idx < simple_tokens.len() {
        let (t, i) = Token::consume(&simple_tokens[idx..], None);
        tokens.push(t);
        idx += i;
    }

    FileTokenTree {
        leading_whitespace: &simple_tokens[..n_leading_whitespace],
        tokens,
    }
}

#[derive(Debug, Clone)]
pub struct FileTokenTree<'a> {
    pub leading_whitespace: &'a [SimpleToken<'a>],
    pub tokens: Vec<Token<'a>>,
}

#[derive(Debug, Clone)]
pub struct Token<'a> {
    trailing_whitespace: &'a [SimpleToken<'a>],
    // Note: `src` doesn't contain leading or trailing whitespace
    src: &'a [SimpleToken<'a>],
    pub kind: TokenKind<'a>,
}

#[derive(Debug, Clone)]
pub enum TokenKind<'a> {
    Punctuation(Punc),
    Tree {
        delim: Delim,
        leading_whitespace: &'a [SimpleToken<'a>],
        inner: Vec<Token<'a>>,
    },
    Keyword(Kwd),
    Literal(&'a str, LiteralKind),
    Ident(&'a str),
    Err(Error<'a>),
}

#[derive(Debug, Copy, Clone)]
pub enum Error<'a> {
    UnexpectedCloseDelim(SimpleToken<'a>),
    MismatchedCloseDelim {
        delim: Delim,
        first: SimpleToken<'a>,
        end: SimpleToken<'a>,
    },
    UnclosedDelim(Delim, &'a [SimpleToken<'a>]),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Delim {
    Parens,
    Squares,
    Curlies,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Punc {
    Semi,           // ";"
    Colon,          // ":"
    Comma,          // ","
    Dot,            // "."
    EqEq,           // "=="
    Eq,             // "="
    Le,             // "<="
    Lt,             // "<"
    Ge,             // ">="
    Gt,             // ">"
    AndAnd,         // "&&"
    And,            // "&"
    OrOr,           // "||"
    Pipe,           // "|"
    Not,            // "!"
    Plus,           // "+"
    Minus,          // "-"
    Star,           // "*"
    Slash,          // "/"
    RightArrow,     // "=>"
    ThinRightArrow, // "->"
    Question,       // "?"
}

macro_rules! keywords {
    (
        $vis:vis enum Kwd {
            $($str:literal => $variant:ident),* $(,)?
        }
    ) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq)]
        $vis enum Kwd {
            $($variant,)*
        }
        impl Kwd {
            fn try_from(ident: &str) -> Option<Kwd> {
                match ident {
                    $($str => Some(Kwd::$variant),)*
                    _ => None,
                }
            }
        }
        impl ToString for Kwd {
            fn to_string(&self) -> String {
                match self {
                    $(Kwd::$variant => $str.into(),)*
                }
            }
        }
    }
}

keywords!(pub enum Kwd {
    "fn" => Fn,
    "type" => Type,
    "import" => Import,
    "const" => Const,
    "let" => Let,
    "if" => If,
    "else" => Else,
    "for" => For,
    "while" => While,
    "match" => Match,
    "in" => In,
    "do" => Do,
    "loop" => Loop,
    "enum" => Enum,
    "alias" => Alias,
});

impl Delim {
    fn open_char(&self) -> char {
        match self {
            Delim::Parens => '(',
            Delim::Squares => '[',
            Delim::Curlies => '{',
        }
    }

    fn close_char(&self) -> char {
        match self {
            Delim::Parens => ')',
            Delim::Squares => ']',
            Delim::Curlies => '}',
        }
    }
}

impl<'a> Token<'a> {
    fn consume(
        tokens: &'a [SimpleToken<'a>],
        enclosing_delim: Option<SimpleToken<'a>>,
    ) -> (Token<'a>, usize) {
        use tokens::TokenKind::*;
        use Error::{MismatchedCloseDelim, UnexpectedCloseDelim};

        assert!(tokens.len() >= 1);

        macro_rules! punc {
            ($variant:ident, $len:expr) => {{
                (Ok(TokenKind::Punctuation(Punc::$variant)), $len)
            }};
        }

        let first = tokens[0];
        let kinds = tokens.iter().map(|t| t.kind).take(2).collect::<Vec<_>>();

        let (kind_res, consumed) = match &kinds as &[_] {
            // This is unreachable because of the assert statement at the top
            [] => unreachable!(),

            // And *this* can't happen because we're given that the first token will be
            // non-whitespace.
            [Whitespace, ..] | [LineComment, ..] | [BlockComment, ..] => unreachable!(),

            // Multi-token elements
            [OpenParen, ..] | [OpenCurly, ..] | [OpenSquare, ..] => {
                let (kind, consumed) = Token::consume_delim(tokens);
                (Ok(kind), consumed)
            }

            // Error cases - close delims should be handled by the caller
            [CloseParen, ..] | [CloseSquare, ..] | [CloseCurly, ..] => match enclosing_delim {
                Some(d) => (
                    Err(MismatchedCloseDelim {
                        delim: match d.kind {
                            OpenParen => Delim::Parens,
                            OpenSquare => Delim::Squares,
                            OpenCurly => Delim::Curlies,
                            _ => unreachable!(),
                        },
                        first: d,
                        end: first,
                    }),
                    1,
                ),
                None => (Err(UnexpectedCloseDelim(first)), 1),
            },

            // Some of the "complex" individual tokens
            [Literal(kind), ..] => (Ok(TokenKind::Literal(first.src, *kind)), 1),
            [Ident, ..] => match Kwd::try_from(first.src) {
                Some(kwd) => (Ok(TokenKind::Keyword(kwd)), 1),
                None => (Ok(TokenKind::Ident(first.src)), 1),
            },

            // And all of the punctuation
            [Semi, ..] => punc!(Semi, 1),
            [Colon, ..] => punc!(Colon, 1),
            [Comma, ..] => punc!(Comma, 1),
            [Dot, ..] => punc!(Dot, 1),
            [Eq, Eq, ..] => punc!(EqEq, 2),
            [Eq, Gt, ..] => punc!(RightArrow, 2),
            [Eq, ..] => punc!(Eq, 1),
            [Lt, Eq, ..] => punc!(Le, 2),
            [Lt, ..] => punc!(Lt, 1),
            [Gt, Eq, ..] => punc!(Ge, 2),
            [Gt, ..] => punc!(Gt, 1),
            [And, And, ..] => punc!(AndAnd, 2),
            [And, ..] => punc!(And, 1),
            [Pipe, Pipe, ..] => punc!(OrOr, 2),
            [Pipe, ..] => punc!(Pipe, 1),
            [Not, ..] => punc!(Not, 1),
            [Plus, ..] => punc!(Plus, 1),
            [Minus, Gt, ..] => punc!(ThinRightArrow, 2),
            [Minus, ..] => punc!(Minus, 1),
            [Star, ..] => punc!(Star, 1),
            [Slash, ..] => punc!(Slash, 1),
            [Question, ..] => punc!(Question, 1),
        };

        // We'll additionally consume any trailing whitespace.
        let trailing = tokens[consumed..]
            .iter()
            .take_while(|t| match t.kind {
                LineComment | BlockComment | Whitespace => true,
                _ => false,
            })
            .count();

        let token = Token {
            trailing_whitespace: &tokens[consumed..consumed + trailing],
            src: &tokens[..consumed],
            kind: match kind_res {
                Ok(kind) => kind,
                Err(err) => TokenKind::Err(err),
            },
        };

        (token, consumed + trailing)
    }

    fn consume_delim(tokens: &'a [SimpleToken<'a>]) -> (TokenKind<'a>, usize) {
        use tokens::TokenKind::{
            BlockComment, CloseCurly, CloseParen, CloseSquare, LineComment, OpenCurly, OpenParen,
            OpenSquare, Whitespace,
        };
        use Delim::{Curlies, Parens, Squares};
        use Error::UnclosedDelim;
        use TokenKind::Tree;

        assert!(tokens.len() >= 1);
        let (delim, close) = match tokens[0].kind {
            OpenParen => (Parens, CloseParen),
            OpenSquare => (Squares, CloseSquare),
            OpenCurly => (Curlies, CloseCurly),
            _ => panic!("unexpected initial delim token {:?}", tokens[0]),
        };

        // We'll consume all leading whitespace to guarantee that `consume` is called where the
        // first token isn't one
        let n_leading = tokens[1..]
            .iter()
            .take_while(|t| match t.kind {
                LineComment | BlockComment | Whitespace => true,
                _ => false,
            })
            .count();

        // All of the whitespace, +1 for the delimeter
        let mut consumed = n_leading + 1;
        let mut inner = Vec::new();
        loop {
            if consumed == tokens.len() {
                // This is an error; we got to EOF and the delimeter wasn't closed
                inner.push(Token {
                    kind: TokenKind::Err(UnclosedDelim(delim, tokens)),
                    // FIXME @max would you mind choosing sinsible values for these
                    src: &[],
                    trailing_whitespace: &[],
                });
                break;
            }

            if tokens[consumed].kind == close {
                // Increment to mark this token as consumed
                consumed += 1;
                break;
            }

            // TODO: Possibly handle mismatched closing delims better.
            // We could break here without consuming a mismatched closing delim and let our
            // container handle it. This makes errors in cases where a closing delim is missed much
            // nicer.

            let (t, c) = Token::consume(&tokens[consumed..], Some(tokens[0]));
            inner.push(t);
            consumed += c;
        }

        (
            Tree {
                delim,
                leading_whitespace: &tokens[1..1 + n_leading],
                inner,
            },
            consumed,
        )
    }

    fn collect_errors(&self, errors: &mut Vec<Error<'a>>) {
        if let TokenKind::Err(err) = &self.kind {
            errors.push(*err);
        } else if let TokenKind::Tree { inner, .. } = &self.kind {
            inner.iter().for_each(|tok| tok.collect_errors(errors));
        }
    }
}

impl<'a> FileTokenTree<'a> {
    pub fn collect_errors(&self) -> Vec<Error<'a>> {
        let mut errors = Vec::new();
        self.tokens
            .iter()
            .for_each(|tok| tok.collect_errors(&mut errors));
        errors
    }
}

impl<F: Fn(&str) -> Range<usize>> ToError<(F, &str)> for Error<'_> {
    fn to_error(self, aux: &(F, &str)) -> ErrorBuilder {
        use Error::*;

        let file_name: &str = aux.1;

        match self {
            UnexpectedCloseDelim(token) => {
                let range = (aux.0)(token.src);

                ErrorBuilder::new(format!("unexpected close delimeter '{}'", token.src))
                    .context(file_name, range.start)
                    .highlight(file_name, vec![range], error::ERR_COLOR)
            }
            MismatchedCloseDelim { delim, first, end } => {
                let end_range = (aux.0)(end.src);

                ErrorBuilder::new(format!(
                    "mismatched delimeter; expected '{}', found '{}'",
                    delim.open_char(),
                    end.src,
                ))
                .context(file_name, end_range.start)
                .highlight(file_name, vec![(aux.0)(first.src)], error::CTX_COLOR)
                .highlight(file_name, vec![end_range], error::ERR_COLOR)
            }
            UnclosedDelim(delim, src) => {
                let start = (aux.0)(src[0].src).start;
                let end = (aux.0)(src.last().unwrap().src).end;

                ErrorBuilder::new(format!(
                    "unclosed delimeter '{}'; expected '{}', found EOF",
                    delim.open_char(),
                    delim.close_char(),
                ))
                .context(file_name, start)
                .highlight(file_name, vec![start..end], error::ERR_COLOR)
            }
        }
    }
}
