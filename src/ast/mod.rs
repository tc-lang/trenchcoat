//! The production of the abstract syntax tree for a source file

use crate::tokens;
use crate::tokens::{Keyword, Token, TokenKind};

mod error;

pub use error::{Context as ErrorContext, Error, ErrorKind};

////////////////////////////////////////////////////////////////////////////////
// Top-level interface                                                        //
////////////////////////////////////////////////////////////////////////////////

pub fn try_parse<'a>(tokens: &'a [Token<'a>]) -> Result<Vec<Item<'a>>, Vec<Error<'a>>> {
    let mut items = Vec::new();

    // Our place in the list of tokens
    let mut idx = 0;

    while idx < tokens.len() {
        let item = Item::parse(tokens)?;
        idx += item.consumed();
        items.push(item);
    }

    Ok(items)
}

////////////////////////////////////////////////////////////////////////////////
// Type definitions                                                           //
////////////////////////////////////////////////////////////////////////////////

/// Most parsing functions return a ParsingRet.
#[derive(Debug)]
enum ParsingRet<'a, T> {
    /// The parse was succesful.
    Ok(T),

    /// The parse was unsuccesful, however the error wasn't too bad so a result is given to
    /// complete the token tree and parsing may continue. However no steps after parsing should be
    /// completed and the collected errors should be given.
    SoftErr(T, Vec<Error<'a>>),

    /// The programmer can't code. Parsing must now stop. They should feel bad.
    Err(Vec<Error<'a>>),
}

impl<'a, T> ParsingRet<'a, T> {
    /// Generates a `ParsingRet::Err` with only the error given.
    fn single_err(e: Error<'a>) -> ParsingRet<'a, T> {
        Self::Err(vec![e])
    }

    /// Generates a `ParsingRet::SoftErr` with the value the error given.
    fn single_soft_err(v: T, e: Error<'a>) -> ParsingRet<'a, T> {
        Self::SoftErr(v, vec![e])
    }

    /// Returns `Self::Ok(v)` if errs is empty or a `Self::SoftErr` otherwise.
    fn with_soft_errs(v: T, errs: Vec<Error<'a>>) -> ParsingRet<'a, T> {
        if errs.len() > 0 {
            Self::SoftErr(v, errs)
        } else {
            Self::Ok(v)
        }
    }
}

#[derive(Debug)]
pub struct Item<'a> {
    kind: ItemKind<'a>,
    source: &'a [Token<'a>],
}

#[derive(Debug)]
pub struct Stmt<'a> {
    kind: ExprKind<'a>,
    source: &'a [Token<'a>],
}

#[derive(Debug)]
pub struct Expr<'a> {
    kind: ExprKind<'a>,
    source: &'a [Token<'a>],
}

#[derive(Debug)]
pub struct Block<'a> {
    body: Vec<Stmt<'a>>,
}

/// A top-level item in the source
///
/// Currently only function declarations are supported.
#[derive(Debug)]
pub enum ItemKind<'a> {
    FnDecl {
        name: Ident<'a>,
        params: FnParams<'a>,
        body: Block<'a>,
        //tail: Option<Expr<'a>>,
    },
}

#[derive(Debug)]
pub struct Ident<'a> {
    name: &'a str,
    source: &'a Token<'a>,
}

pub type FnArgs<'a> = Vec<Expr<'a>>;
pub type FnParams<'a> = Vec<Ident<'a>>;

/// A semicolon-terminated statement
#[derive(Debug)]
pub enum StmtKind<'a> {
    /// A `let` statement binding a value given by the `Expr` to a variable name given by the
    /// identifier. For example: `let x = g(y);`
    Let(Ident<'a>, Expr<'a>),

    /// An assignemnt, e.g. `x = 4;`. In this example, 'x' would be the `Ident`, and '4' would be
    /// the `Expr`
    Assign(Ident<'a>, Expr<'a>),

    /// Printing a value, e.g. `print foo(1);`
    Print(Expr<'a>),

    /// The simple evaluation of a single expression, treated as a statement. This might be
    /// something like: `foo(bar(3));`, where `foo` and `bar` might have side effects.
    Eval(Expr<'a>),
}

#[derive(Debug)]
pub enum ExprKind<'a> {
    /// An expression representing a function call. The left-hand `Expr` is the function, and the
    /// right-hand `FnArgs` gives its arguments.
    FnCall(Box<Expr<'a>>, FnArgs<'a>),

    /// An expression produced from a binary operator. The elements of the tuple are placed as they
    /// would be in the source (i.e. the left-hand `Expr` is the left-hand argument to the
    /// operator). For example: `3 + 4`
    BinOp(Box<Expr<'a>>, BinOp, Box<Expr<'a>>),

    /// A prefix operator expression, e.g. `!f(x)` or `&y`
    PrefixOp(PrefixOp, Box<Expr<'a>>),

    /// An expression that simply references the value of a variable, e.g. `x` or `foo`.
    Named(Ident<'a>),

    /// A raw number, e.g. `420`
    Num(usize),

    /// A bracketed expression, using either curly-braces or parentheses. For example: `(x + y)` or
    /// `{ foo(x); y }`
    Bracket(Vec<Stmt<'a>>, Box<Expr<'a>>),
}

/// A binary operator
#[derive(Debug)]
pub enum BinOp {
    /// Addition: `+`
    Add,
    /// Subtraction: `-`
    Sub,
    /// Multiplication: `*`
    Mul,
    /// Division: `/`
    Div,
    /// Equality: `==`
    Eq,
    /// Less than: `<`
    Lt,
    /// Less than or equal to: `<=`
    Le,
    /// Greater than: `>`
    Gt,
    /// Greater than or equal to: `>=`
    Ge,
    /// Logical "or": `||`
    Or,
    /// Logical "and": `&&`
    And,
}

/// A prefix operator. This is currently lacking most of the prefix operators that will be added
/// later. This is intentional.
#[derive(Debug)]
pub enum PrefixOp {
    /// Unary not: `!`
    Not,
}

////////////////////////////////////////////////////////////////////////////////
// Implementations and other functions                                        //
//                                                                            //
// These are ordered by the required recusive depth from the top-level        //
// `try_parse` to reach them.                                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

//type FnDecl<'a> = (Ident<'a>, FnParams<'a>, Vec<Stmt<'a>>, Option<Expr<'a>>);

impl<'a> Item<'a> {
    /// Returns the number of tokens consumed to produce this type
    fn consumed(&self) -> usize {
        self.source.len()
    }

    /// Attempts to parse the set of tokens into an item, returning the number of tokens consumed
    /// if successful.
    fn parse(tokens: &'a [Token<'a>]) -> Option<ParsingRet<'a, Item<'a>>> {
        // Currently we're just parsing function declarations. This will be changed in the future
        Self::parse_fn_decl(tokens)
    }

    fn parse_block(tokens: &Vec<Token<'a>>) -> ParsingRet<'a, Block<'a>> {
        return ParsingRet::Ok(Block { body: vec![] });
        todo!()
    }

    /// Takes the token expected to be the function name and tries to parse it.
    fn parse_fn_name(token: Option<&'a Token<'a>>) -> ParsingRet<'a, Ident> {
        match token.map(|t| &t.kind) {
            Some(TokenKind::NameIdent(name)) => ParsingRet::Ok(Ident {
                name,
                source: token.unwrap(),
            }),
            Some(TokenKind::TypeIdent(name)) => ParsingRet::single_soft_err(
                Ident {
                    name,
                    source: token.unwrap(),
                },
                Error {
                    kind: ErrorKind::TypeIdent,
                    context: ErrorContext::FnName,
                    source: token,
                },
            ),
            Some(_) => ParsingRet::single_err(Error {
                kind: ErrorKind::ExpectingName,
                context: ErrorContext::FnName,
                source: token,
            }),
            None => ParsingRet::single_err(Error {
                kind: ErrorKind::EOF,
                context: ErrorContext::FnName,
                source: None,
            }),
        }
    }

    /// Takes the token expected to be the function params and tries to parse it.
    fn parse_fn_params(token: Option<&'a Token<'a>>) -> ParsingRet<'a, FnParams<'a>> {
        let tokens = match token.map(|t| &t.kind) {
            Some(TokenKind::Parens(tokens)) => tokens,
            Some(_) => {
                return ParsingRet::single_err(Error {
                    kind: ErrorKind::ExpectingParens,
                    context: ErrorContext::FnArgs,
                    source: token,
                })
            }
            None => {
                return ParsingRet::single_err(Error {
                    kind: ErrorKind::EOF,
                    context: ErrorContext::FnArgs,
                    source: None,
                })
            }
        };

        let params = tokens::split_at_commas(&tokens);
        let mut errors = Vec::new();
        let mut out = Vec::with_capacity(params.len());
        for a in params {
            if a.len() != 1 {
                errors.push(Error {
                    kind: ErrorKind::ExpectingName,
                    context: ErrorContext::FnArgs,
                    source: a.get(0),
                }); // TODO: improve this error
            } else {
                let a = &a[0];
                match a.kind {
                    TokenKind::NameIdent(name) => out.push(Ident { name, source: a }),
                    TokenKind::TypeIdent(name) => {
                        out.push(Ident { name, source: a });
                        errors.push(Error {
                            kind: ErrorKind::TypeIdent,
                            context: ErrorContext::FnArgs,
                            source: Some(a),
                        });
                    }
                    _ => errors.push(Error {
                        kind: ErrorKind::ExpectingName,
                        context: ErrorContext::FnArgs,
                        source: Some(a),
                    }),
                }
            }
        }
        ParsingRet::with_soft_errs(out, errors)
    }

    fn parse_fn_body(token: Option<&'a Token<'a>>) -> ParsingRet<'a, Block<'a>> {
        match token.map(|t| &t.kind) {
            Some(TokenKind::Curlys(tokens)) => Self::parse_block(tokens),
            Some(_) => ParsingRet::single_err(Error {
                kind: ErrorKind::ExpectingCurlys,
                context: ErrorContext::FnBody,
                source: token,
            }),
            None => ParsingRet::single_err(Error {
                kind: ErrorKind::EOF,
                context: ErrorContext::FnBody,
                source: token,
            }),
        }
    }

    fn parse_fn_decl(tokens: &'a [Token<'a>]) -> Option<ParsingRet<'a, Item<'a>>> {
        use ParsingRet::*;

        match tokens.get(0)?.kind {
            TokenKind::Keyword(Keyword::Fn) => (),
            _ => return None,
        }

        let mut errors = Vec::new();

        macro_rules! next {
            (try $f:expr) => {
                match $f {
                    Ok(v) => v,
                    SoftErr(v, errs) => {
                        errors.extend(errs);
                        v
                    }
                    Err(errs) => {
                        errors.extend(errs);
                        return Some(Err(errors));
                    }
                }
            };
        }

        let name = next!(try Self::parse_fn_name(tokens.get(1)));
        let params = next!(try Self::parse_fn_params(tokens.get(2)));
        let body = next!(try Self::parse_fn_body(tokens.get(3)));

        Some(ParsingRet::with_soft_errs(
            Item {
                kind: ItemKind::FnDecl { name, params, body },
                source: &tokens[0..4],
            },
            errors,
        ))
    }
}
