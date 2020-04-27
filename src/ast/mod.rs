//! The production of the abstract syntax tree for a source file

use crate::tokens;
use crate::tokens::{Keyword, Oper, Punc, Token, TokenKind};

mod error;

macro_rules! next {
    ($f:expr , $errors:expr) => {{
        use ParseRet::*;
        match $f {
            Ok(v) => v,
            SoftErr(v, errs) => {
                $errors.extend(errs);
                v
            }
            Err(errs) => {
                $errors.extend(errs);
                return Some(Err($errors));
            }
        }
    }};
}

pub use error::{Context as ErrorContext, Error, ErrorKind};

////////////////////////////////////////////////////////////////////////////////
// Top-level interface                                                        //
////////////////////////////////////////////////////////////////////////////////

pub fn try_parse<'a>(tokens: &'a [Token<'a>]) -> Result<Vec<Item<'a>>, Vec<Error<'a>>> {
    let mut items = Vec::new();
    let mut errors = Vec::new();

    // Our place in the list of tokens
    let mut idx = 0;

    while idx < tokens.len() {
        match Item::parse_top_level(&tokens[idx..]) {
            ParseRet::Err(err) => return Err(err),
            ParseRet::SoftErr(item, err) => {
                idx += item.consumed();
                items.push(item);
                errors.extend(err);
            }
            ParseRet::Ok(item) => {
                idx += item.consumed();
                items.push(item);
            }
        }
    }

    if errors.len() > 0 {
        Err(errors)
    } else {
        Ok(items)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Type definitions                                                           //
////////////////////////////////////////////////////////////////////////////////

/// Most parsing functions return a ParseRet.
#[derive(Debug)]
enum ParseRet<'a, T> {
    /// The parse was succesful.
    Ok(T),

    /// The parse was unsuccesful, however the error wasn't too bad so a result is given to
    /// complete the token tree and parsing may continue. However no steps after parsing should be
    /// completed and the collected errors should be given.
    SoftErr(T, Vec<Error<'a>>),

    /// The programmer can't code. Parsing must now stop. They should feel bad.
    Err(Vec<Error<'a>>),
}

impl<'a, T> ParseRet<'a, T> {
    /// Generates a `ParseRet::Err` with only the error given.
    fn single_err(e: Error<'a>) -> ParseRet<'a, T> {
        Self::Err(vec![e])
    }

    /// Generates a `ParseRet::SoftErr` with the value the error given.
    fn single_soft_err(v: T, e: Error<'a>) -> ParseRet<'a, T> {
        Self::SoftErr(v, vec![e])
    }

    /// Returns `Self::Ok(v)` if errs is empty or a `Self::SoftErr` otherwise.
    fn with_soft_errs(v: T, errs: Vec<Error<'a>>) -> ParseRet<'a, T> {
        if errs.len() > 0 {
            Self::SoftErr(v, errs)
        } else {
            Self::Ok(v)
        }
    }

    fn map<U>(self, f: impl Fn(T) -> U) -> ParseRet<'a, U> {
        match self {
            Self::Ok(v) => ParseRet::Ok(f(v)),
            Self::SoftErr(v, errs) => ParseRet::SoftErr(f(v), errs),
            Self::Err(errs) => ParseRet::Err(errs),
        }
    }

    fn change_errs(&mut self, f: impl Fn(&mut Error<'a>) -> ()) {
        let errs = match self {
            Self::Ok(_) => return,
            Self::SoftErr(_, errs) => errs,
            Self::Err(errs) => errs,
        };
        for e in errs {
            f(e);
        }
    }
    fn set_context(&mut self, new_ctx: ErrorContext) {
        self.change_errs(|e| e.context = new_ctx)
    }
}

#[derive(Debug)]
pub struct Item<'a> {
    kind: ItemKind<'a>,
    source: &'a [Token<'a>],
}

#[derive(Debug)]
pub struct Stmt<'a> {
    kind: StmtKind<'a>,
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
    Eval(ExprKind<'a>),
}

#[derive(Debug)]
pub enum ExprKind<'a> {
    Empty,

    /// An expression representing a function call. The left-hand `Expr` is the function, and the
    /// right-hand `FnArgs` gives its arguments.
    FnCall(Box<Expr<'a>>, FnArgs<'a>),

    /// An expression produced from a binary operator. The elements of the tuple are placed as they
    /// would be in the source (i.e. the left-hand `Expr` is the left-hand argument to the
    /// operator). For example: `3 + 4`
    BinOp(Box<Expr<'a>>, Oper, Box<Expr<'a>>),

    /// A prefix operator expression, e.g. `!f(x)` or `&y`
    PrefixOp(Oper, Box<Expr<'a>>),

    /// An expression that simply references the value of a variable, e.g. `x` or `foo`.
    Named(Ident<'a>),

    /// A raw number, e.g. `420`
    Num(usize),

    /// A bracketed expression, using either curly-braces or parentheses. For example: `(x + y)` or
    /// `{ foo(x); y }`
    Bracket(Vec<Stmt<'a>>, Box<Expr<'a>>),
}

/// A binary operator TODO: Maybe remove?
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

static binary_oper_precedence: &[&[Oper]] = &[
    &[Oper::Or, Oper::And],
    &[
        Oper::Equals,
        Oper::Lt,
        Oper::Gt,
        Oper::LtOrEqual,
        Oper::GtOrEqual,
    ],
    &[Oper::Add, Oper::Sub],
    &[Oper::Star, Oper::Div],
];
static prefix_opers: &[Oper] = &[Oper::Not];

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
    fn parse_top_level(tokens: &'a [Token<'a>]) -> ParseRet<'a, Item<'a>> {
        if let Some(pr) = Self::parse_fn_decl(tokens) {
            return pr;
        }
        ParseRet::single_err(Error {
            kind: ErrorKind::ExpectingKeyword,
            context: ErrorContext::TopLevel,
            source: tokens.get(0),
        })
    }

    /*fn parse_stmt(tokens: &'a [Token<'a>]) -> ParseRet<'a, Item<'a>> {

    }*/

    fn parse_block(tokens: &'a [Token<'a>]) -> ParseRet<'a, Block<'a>> {
        return Self::parse_stmt(tokens).map(|stmt| Block { body: vec![stmt] });
        return ParseRet::Ok(Block { body: vec![] });
        todo!()
    }

    fn parse_name(token: Option<&'a Token<'a>>) -> ParseRet<'a, Ident> {
        if let Some(token) = token {
            match token.kind {
                TokenKind::NameIdent(name) => ParseRet::Ok(Ident {
                    name,
                    source: token,
                }),
                TokenKind::TypeIdent(name) => ParseRet::single_soft_err(
                    Ident {
                        name,
                        source: token,
                    },
                    Error {
                        kind: ErrorKind::TypeIdent,
                        context: ErrorContext::UnknownName,
                        source: Some(token),
                    },
                ),
                _ => ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingName,
                    context: ErrorContext::UnknownName,
                    source: Some(token),
                }),
            }
        } else {
            ParseRet::single_err(Error {
                kind: ErrorKind::EOF,
                context: ErrorContext::UnknownName,
                source: None,
            })
        }
    }

    /// Takes the token expected to be the function name and tries to parse it.
    fn parse_fn_name(token: Option<&'a Token<'a>>) -> ParseRet<'a, Ident> {
        let mut ret = Self::parse_name(token);
        ret.set_context(ErrorContext::FnName);
        ret
    }

    fn parse_let_name(token: Option<&'a Token<'a>>) -> ParseRet<'a, Ident> {
        let mut ret = Self::parse_name(token);
        ret.set_context(ErrorContext::LetName);
        ret
    }

    /// Takes the token expected to be the function params and tries to parse it.
    fn parse_fn_params(token: Option<&'a Token<'a>>) -> ParseRet<'a, FnParams<'a>> {
        let tokens = if let Some(token) = token {
            if let TokenKind::Parens(tokens) = &token.kind {
                tokens
            } else {
                return ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingParens,
                    context: ErrorContext::FnArgs,
                    source: Some(token),
                });
            }
        } else {
            return ParseRet::single_err(Error {
                kind: ErrorKind::EOF,
                context: ErrorContext::FnArgs,
                source: None,
            });
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
        ParseRet::with_soft_errs(out, errors)
    }

    fn parse_fn_body(token: Option<&'a Token<'a>>) -> ParseRet<'a, Block<'a>> {
        if let Some(token) = token {
            if let TokenKind::Curlys(tokens) = &token.kind {
                Self::parse_block(&tokens)
            } else {
                ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingCurlys,
                    context: ErrorContext::FnBody,
                    source: Some(token),
                })
            }
        } else {
            ParseRet::single_err(Error {
                kind: ErrorKind::EOF,
                context: ErrorContext::FnBody,
                source: None,
            })
        }
    }

    fn parse_fn_decl(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Item<'a>>> {
        match tokens.get(0)?.kind {
            TokenKind::Keyword(Keyword::Fn) => (),
            _ => return None,
        }

        let mut errors = Vec::new();

        println!("{:?}", tokens.get(1));
        let name = next!(Self::parse_fn_name(tokens.get(1)), errors);
        let params = next!(Self::parse_fn_params(tokens.get(2)), errors);
        let body = next!(Self::parse_fn_body(tokens.get(3)), errors);

        Some(ParseRet::with_soft_errs(
            Item {
                kind: ItemKind::FnDecl { name, params, body },
                source: &tokens[0..4],
            },
            errors,
        ))
    }

    /*fn parse_let(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Item<'a>>> {
        match tokens.get(0)?.kind {
            TokenKind::Keyword(Keyword::Let) => {}
            _ => return None,
        }

        let mut errors = Vec::new();

        let name = next!(Self::parse_let_name(tokens.get(1), errors), errors);

        match tokens.get(2) {
            None => {
                return Some(ParseRet::single_err(Error {
                    kind: ErrorKind::EOF,
                    context: ErrorContext::LetEquals,
                    source: None,
                }))
            }
            Some(token) => match token.kind {
                TokenKind::Oper(Oper::Assign) => (),
                _ => {
                    return Some(ParseRet::single_err(Error {
                        kind: ErrorKind::ExpectingEquals,
                        context: ErrorContext::LetEquals,
                        source: None,
                    }))
                }
            },
        }
        todo!()
    }*/

    fn parse_stmt(tokens: &'a [Token<'a>]) -> ParseRet<'a, Stmt<'a>> {
        match Self::parse_expr(tokens) {
            None => ParseRet::single_err(Error {
                kind: ErrorKind::ExpectingStmt,
                context: ErrorContext::ParseStmt,
                source: tokens.get(0),
            }),
            Some(pr) => pr.map(|expr| Stmt {
                kind: StmtKind::Eval(expr.kind),
                source: expr.source,
            }),
        }
    }

    fn parse_expr(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        let mut tokens = tokens;
        let mut source = tokens;
        // the expression ends early if there's a semi-colon.
        for i in 0..tokens.len() {
            if let TokenKind::Punc(Punc::Semi) = tokens[i].kind {
                source = &tokens[..i + 1];
                tokens = &tokens[..i];
                break;
            }
        }

        if tokens.len() == 0 {
            return Some(ParseRet::Ok(Expr {
                kind: ExprKind::Empty,
                source: source,
            }));
        }

        Some(
            Self::parse_prefix_oper_expr(tokens)
                .or_else(|| Self::parse_bin_oper_expr(tokens))? // note this ?
                .map(|kind| Expr { kind, source }),
        )
    }

    fn parse_bin_oper_expr2(
        left_tokens: &'a [Token<'a>],
        op: Oper,
        right_tokens: &'a [Token<'a>],
    ) -> ParseRet<'a, ExprKind<'a>> {
        let left = Self::parse_expr(left_tokens);
        let right = Self::parse_expr(right_tokens);

        let mut errors = Vec::with_capacity(2);

        use ParseRet::{Err, Ok, SoftErr};
        macro_rules! unwrap {
            ($x:expr, $source:expr) => {
                match $x {
                    None => {
                        errors.push(Error{
                            kind: ErrorKind::ExpectingExpr,
                            context: ErrorContext::BinOperLeft, // TODO: Make left or right
                            source: $source.get(0), // we should probably put the operator token here if there's nothing on the left
                        });
                        Expr{ kind: ExprKind::Empty, source: $source }
                    },
                    Some(Err(errs)) => return Err(errs),
                    Some(SoftErr(exp, errs)) => {
                        errors.extend(errs);
                        //Expr{ kind: exp, source: $source }
                        exp
                    },
                    Some(Ok(exp)) => exp /*Expr{ kind: exp, source: $source }*/,
                }
            };
        }
        let left = unwrap!(left, left_tokens);
        let right = unwrap!(right, right_tokens);

        ParseRet::with_soft_errs(ExprKind::BinOp(Box::new(left), op, Box::new(right)), errors)
    }

    fn parse_bin_oper_expr(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, ExprKind<'a>>> {
        for ops in binary_oper_precedence {
            for i in 0..tokens.len() {
                let t = &tokens[i];
                for op in *ops {
                    let op = *op;
                    if t.kind == TokenKind::Oper(op) {
                        return Some(Self::parse_bin_oper_expr2(
                            &tokens[0..i],
                            op,
                            &tokens[i + 1..],
                        ));
                    }
                }
            }
        }
        None
    }

    fn parse_prefix_oper_expr(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, ExprKind<'a>>> {
        let first_token = tokens.get(0)?;
        for op in prefix_opers {
            if first_token.kind == TokenKind::Oper(*op) {
                return Self::parse_expr(&tokens[1..])
                    .map(|pr| pr.map(|e| e.kind))
                    .or_else(|| {
                        Some(ParseRet::single_soft_err(
                            ExprKind::Empty,
                            Error {
                                kind: ErrorKind::ExpectingExpr,
                                context: ErrorContext::BinOperLeft, // TODO: Make left or right
                                source: tokens.get(1).or_else(|| tokens.get(0)), // we should probably put the operator token here if there's nothing on the left
                            },
                        ))
                    });
            }
        }
        None
    }
}
