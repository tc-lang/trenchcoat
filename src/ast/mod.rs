//! The production of the abstract syntax tree for a source file

use crate::tokens::{self, Keyword, Oper, Punc, Token, TokenKind};
use std::convert::TryFrom;

mod error;
pub use error::{Context as ErrorContext, Error, ErrorKind};

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

////////////////////////////////////////////////////////////////////////////////
// Top-level interface                                                        //
////////////////////////////////////////////////////////////////////////////////

pub fn try_parse<'a>(tokens: &'a [Token<'a>]) -> Result<Vec<Item<'a>>, Vec<Error<'a>>> {
    let mut items = Vec::new();
    let mut errors = Vec::new();

    // Our place in the list of tokens
    let mut idx = 0;

    while idx < tokens.len() {
        if tokens[idx].kind == TokenKind::Punc(Punc::Sep) {
            idx += 1;
            continue;
        }
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

    if !errors.is_empty() {
        Err(errors)
    } else {
        Ok(items)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Type definitions                                                           //
////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub enum Node<'a> {
    Ident(&'a Ident<'a>),
    Item(&'a Item<'a>),
    Stmt(&'a Stmt<'a>),
    Expr(&'a Expr<'a>),
    Args(&'a FnArgs<'a>),
}

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

#[derive(Debug)]
pub struct Item<'a> {
    pub kind: ItemKind<'a>,
    pub source: &'a [Token<'a>],
}

#[derive(Debug, Clone)]
pub struct Stmt<'a> {
    pub kind: StmtKind<'a>,
    pub source: &'a [Token<'a>],
}

#[derive(Debug, Clone)]
pub struct Expr<'a> {
    pub kind: ExprKind<'a>,
    pub source: &'a [Token<'a>],
}

#[derive(Debug, Clone)]
pub struct Block<'a> {
    pub body: Vec<Stmt<'a>>,

    /// Sometimes blocks will contain a trailing expression
    /// This is boxed because an expression can contain a block so otherwise there'd be a cycle.
    pub tail: Box<Expr<'a>>,

    /// The source for a `Block` will always be a single token - either curlies or parens
    pub source: &'a Token<'a>,
}

/// A type expression - e.g. `int` or `bool`
#[derive(Debug, Clone)]
pub struct TypeExpr<'a> {
    pub kind: TypeExprKind,
    pub source: &'a [Token<'a>],
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

#[derive(Debug, Clone)]
pub struct Ident<'a> {
    pub name: &'a str,
    pub source: &'a Token<'a>,
}

pub type FnArgs<'a> = Vec<Expr<'a>>;
pub type FnParams<'a> = Vec<(Ident<'a>, TypeExpr<'a>)>;

/// A semicolon-terminated statement
#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum ExprKind<'a> {
    Empty,

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
    Num(isize),

    /// A bracketed expression, using either curly-braces or parentheses. For example: `(x + y)` or
    /// `{ foo(x); y }`
    Bracket(Block<'a>),
}

/// The kind of type expression
///
/// This is (currently) either a boolean or an integer, as those are the only two supported types.
#[derive(Debug, Clone)]
pub enum TypeExprKind {
    /// A boolean, written `bool`
    Bool,
    /// An integer, written `int`
    Int,
}

/// A binary operator TODO: Maybe remove?
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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

/// The precedence of each binary operator, sorted from lowest to greatest
///
/// Sub-slices consist of equal precedence operators. All prefix operators are higher precedence
/// than binary operators.
static BIN_OP_PRECEDENCE: &[&[BinOp]] = &[
    &[BinOp::Or, BinOp::And],
    &[BinOp::Eq, BinOp::Lt, BinOp::Gt, BinOp::Le, BinOp::Ge],
    &[BinOp::Add, BinOp::Sub],
    &[BinOp::Mul, BinOp::Div],
];

static PREFIX_OPS: &[Oper] = &[Oper::Not];

/// A prefix operator. This is currently lacking most of the prefix operators that will be added
/// later. This is intentional.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PrefixOp {
    /// Unary not: `!`
    Not,
}

////////////////////////////////////////////////////////////////////////////////
// Helper functions + boilerplate implementations                             //
////////////////////////////////////////////////////////////////////////////////

impl TryFrom<Oper> for PrefixOp {
    type Error = ();

    fn try_from(op: Oper) -> Result<PrefixOp, ()> {
        match op {
            Oper::Not => Ok(PrefixOp::Not),
            _ => Err(()),
        }
    }
}

impl TryFrom<Oper> for BinOp {
    type Error = ();

    fn try_from(op: Oper) -> Result<BinOp, ()> {
        use Oper::{Add, And, Div, Equals, Gt, GtOrEqual, Lt, LtOrEqual, Or, Star, Sub};
        match op {
            Or => Ok(BinOp::Or),
            And => Ok(BinOp::And),
            Equals => Ok(BinOp::Eq),
            Lt => Ok(BinOp::Lt),
            Gt => Ok(BinOp::Gt),
            LtOrEqual => Ok(BinOp::Le),
            GtOrEqual => Ok(BinOp::Ge),
            Add => Ok(BinOp::Add),
            Sub => Ok(BinOp::Sub),
            Star => Ok(BinOp::Mul),
            Div => Ok(BinOp::Div),
            _ => Err(()),
        }
    }
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
        match errs.is_empty() {
            true => Self::Ok(v),
            false => Self::SoftErr(v, errs),
        }
    }

    fn map<U>(self, f: impl Fn(T) -> U) -> ParseRet<'a, U> {
        use ParseRet::{Err, Ok, SoftErr};

        match self {
            Ok(v) => Ok(f(v)),
            SoftErr(v, errs) => SoftErr(f(v), errs),
            Err(errs) => Err(errs),
        }
    }

    /// Modifies any errors according to the given function
    fn change_errs(&mut self, f: impl Fn(&mut Error<'a>)) {
        match self {
            Self::Ok(_) => (),
            Self::SoftErr(_, errs) => errs.iter_mut().for_each(f),
            Self::Err(errs) => errs.iter_mut().for_each(f),
        }
    }

    /// Replaces the context on any errors with the given one
    fn with_context(mut self, new_ctx: ErrorContext) -> Self {
        self.change_errs(|e| e.context = new_ctx);
        self
    }
}

////////////////////////////////////////////////////////////////////////////////
// Implementations and other functions                                        //
//                                                                            //
// These are ordered by the required recusive depth from the top-level        //
// `try_parse` to reach them.                                                 //
////////////////////////////////////////////////////////////////////////////////

impl<'a> Item<'a> {
    /// Returns the number of tokens consumed to produce this type
    fn consumed(&self) -> usize {
        self.source.len()
    }

    /// Returns a `Node` containing `self`.
    pub fn node(&'a self) -> Node<'a> {
        Node::Item(self)
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
            source: tokens.first(),
        })
    }

    fn parse_fn_decl(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Item<'a>>> {
        match tokens.first()?.kind {
            TokenKind::Keyword(Keyword::Fn) => (),
            _ => return None,
        }

        let mut errors = Vec::new();

        println!("{:?}", tokens.get(1));
        let name = next!(
            Ident::parse(tokens.get(1)).with_context(ErrorContext::FnName),
            errors
        );
        let params = next!(parse_fn_params(tokens.get(2)), errors);
        let body = next!(
            Block::parse_curlies(tokens.get(3)).with_context(ErrorContext::FnBody),
            errors
        );

        Some(ParseRet::with_soft_errs(
            Item {
                kind: ItemKind::FnDecl { name, params, body },
                source: &tokens[0..4],
            },
            errors,
        ))
    }
}

impl<'a> Block<'a> {
    fn parse_body(tokens: &'a [Token<'a>]) -> ParseRet<'a, (Vec<Stmt<'a>>, Expr<'a>)> {
        let mut idx = 0;

        let mut errors = Vec::new();
        let mut stmts = Vec::new();
        let mut tail = Expr {
            kind: ExprKind::Empty,
            source: tokens, // FIXME - this probably doesn't matter since Empty will never error.
                            //       - if this is refactored, we can make it more sensible.
        };

        while idx < tokens.len() {
            let stmt = match Stmt::parse(&tokens[idx..]) {
                ParseRet::Ok(s) => s,
                ParseRet::SoftErr(s, es) => {
                    errors.extend_from_slice(&es);
                    s
                }
                ParseRet::Err(es) => {
                    // It could be that this is actually the end of the block, so we'll try to
                    // parse an expression here. If that fails, we'll return the original erorr we
                    // were given.
                    //
                    // The expression will only be vaid if it consumes all of the remaining tokens,
                    // but that will be the case for anything that isn't a soft error, so we're
                    // good.
                    //
                    // If the expression *is* valid, we'll return because it's the last thing - we
                    // can do this by simply breaking out of the loop
                    match Expr::parse(&tokens[idx..]) {
                        // expression parsing failed, so we'll go with the original statement
                        // parsing error and return
                        None | Some(ParseRet::Err(_)) => {
                            errors.extend_from_slice(&es);
                            return ParseRet::Err(errors);
                        }
                        Some(ParseRet::SoftErr(ex, ex_errs)) => {
                            tail = ex;
                            errors.extend_from_slice(&ex_errs);
                        }
                        Some(ParseRet::Ok(ex)) => tail = ex,
                    }

                    break;
                }
            };

            idx += stmt.consumed();
            stmts.push(stmt);
        }

        ParseRet::with_soft_errs((stmts, tail), errors)
    }

    fn parse_curlies(token: Option<&'a Token<'a>>) -> ParseRet<'a, Block<'a>> {
        use TokenKind::Curlys;

        let (token, inner_tokens) = match token {
            None => {
                return ParseRet::single_err(Error {
                    kind: ErrorKind::EOF,
                    context: ErrorContext::NoContext,
                    source: None,
                })
            }
            Some(t) => match &t.kind {
                Curlys(inner_tokens) => (t, inner_tokens),
                _ => {
                    return ParseRet::single_err(Error {
                        kind: ErrorKind::ExpectingCurlys,
                        context: ErrorContext::NoContext,
                        source: Some(t),
                    })
                }
            },
        };

        Block::parse_body(&inner_tokens).map(|(stmts, tail)| Block {
            body: stmts,
            tail: Box::new(tail),
            source: token,
        })
    }
}

impl<'a> Ident<'a> {
    /// Returns a `Node` containing `self`.
    pub fn node(&'a self) -> Node<'a> {
        Node::Ident(self)
    }

    fn parse(token: Option<&'a Token<'a>>) -> ParseRet<'a, Ident> {
        let token = match token {
            Some(t) => t,
            None => {
                return ParseRet::single_err(Error {
                    kind: ErrorKind::EOF,
                    context: ErrorContext::UnknownName,
                    source: None,
                })
            }
        };

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
    }
}

impl<'a> TypeExpr<'a> {
    /// Parses a type expression from the *complete* set of tokens given
    fn parse(tokens: &'a [Token<'a>]) -> ParseRet<'a, TypeExpr> {
        use ErrorContext::NoContext;
        use ErrorKind::ExpectingType;
        use ErrorKind::EOF;
        use TokenKind::TypeIdent;

        // In its current state, we'll only expect a single token for type expressions. This single
        // token should be a `TypeIdent`, which we'll then convert into a valid type expression.

        if tokens.is_empty() {
            return ParseRet::single_err(Error {
                kind: EOF,
                context: NoContext,
                source: None,
            });
        }

        // We'll try to parse the first token first, and then return an error if there's too many
        // tokens, instead of the other way around. This way, we can generate better error messages
        // by starting at the first problematic token

        let type_ident_str = match &tokens[0].kind {
            TypeIdent(s) => s,
            _ => {
                return ParseRet::single_err(Error {
                    kind: ExpectingType,
                    context: NoContext,
                    source: Some(&tokens[0]),
                })
            }
        };

        // FIXME: This is *really* unergonomic from an internal point of view. There should not be
        // two different identifier types produced by the **tokenizer**. Currently we have
        // redundant sources of truth in that "bool" and "int" are duplicated both here and in the
        // tokenizer module, so changing one of them might inadvertently break the other.
        let ty_kind = match type_ident_str {
            &"bool" => TypeExprKind::Bool,
            &"int" => TypeExprKind::Int,
            _ => panic!("unexpected TypeIdent"),
        };

        ParseRet::Ok(TypeExpr {
            kind: ty_kind,
            source: &tokens[0..1],
        })
    }
}

/// Takes the token expected to be the function params and tries to parse it.
fn parse_fn_params<'a>(token: Option<&'a Token<'a>>) -> ParseRet<'a, FnParams<'a>> {
    let tokens = match token {
        Some(t) => match &t.kind {
            TokenKind::Parens(tokens) => tokens,
            _ => {
                return ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingParens,
                    context: ErrorContext::FnArgs,
                    source: Some(t),
                })
            }
        },
        None => {
            return ParseRet::single_err(Error {
                kind: ErrorKind::EOF,
                context: ErrorContext::FnArgs,
                source: None,
            })
        }
    };

    let splits = tokens::split_at_commas(&tokens);
    let mut errors = Vec::new();
    let mut params = Vec::with_capacity(splits.len());
    for tokens in splits {
        match parse_single_param(tokens) {
            ParseRet::Ok(p) => params.push(p),
            ParseRet::SoftErr(p, es) => {
                errors.extend(es.into_iter().map(|e| e.with_context(ErrorContext::FnArgs)));
                params.push(p);
            }
            ParseRet::Err(es) => {
                errors.extend(es.into_iter().map(|e| e.with_context(ErrorContext::FnArgs)));
                return ParseRet::Err(errors);
            }
        }
    }

    ParseRet::with_soft_errs(params, errors)
}

/// Attempts to parse a set of tokens as a single function parameter, including name, colon, and
/// type expression
///
/// Valid function parameters could be: `x: int` or `p: bool`.
fn parse_single_param<'a>(tokens: &'a [Token<'a>]) -> ParseRet<'a, (Ident<'a>, TypeExpr<'a>)> {
    use tokens::{Punc::Colon, TokenKind::Punc};

    // This expects a sequence of the form
    //   NameIdent ":" TypeExpr
    // This expects exactly two tokens for the first two, and then parses the remaining tokens as a
    // type expression.

    let mut errors = Vec::new();

    // 1. NameIdent
    let name = match Ident::parse(tokens.first()) {
        ParseRet::Ok(ident) => ident,
        ParseRet::SoftErr(ident, es) => {
            errors.extend(es);
            ident
        }
        ParseRet::Err(es) => return ParseRet::Err(es),
    };

    // 2. ":"
    match tokens.get(1) {
        Some(t) if t.kind == Punc(Colon) => (),
        Some(t) => {
            errors.push(Error {
                kind: ErrorKind::ExpectingName,
                context: ErrorContext::FnArgs,
                source: Some(t),
            });

            return ParseRet::Err(errors);
        }
        None => {
            errors.push(Error {
                kind: ErrorKind::EOF,
                context: ErrorContext::FnArgs,
                source: None,
            });

            return ParseRet::Err(errors);
        }
    }

    // 3. TypeExpr
    let ty = match tokens.get(2..).map(TypeExpr::parse) {
        Some(ParseRet::Ok(ty)) => ty,
        Some(ParseRet::SoftErr(ty, es)) => {
            errors.extend(es);
            ty
        }
        Some(ParseRet::Err(es)) => {
            errors.extend(es);
            return ParseRet::Err(errors);
        }
        None => {
            errors.push(Error {
                kind: ErrorKind::EOF,
                context: ErrorContext::FnArgs,
                source: None,
            });
            return ParseRet::Err(errors);
        }
    };

    ParseRet::with_soft_errs((name, ty), errors)
}

impl<'a> Stmt<'a> {
    /// Returns a `Node` containing `self`.
    pub fn node(&'a self) -> Node<'a> {
        Node::Stmt(self)
    }

    /// Returns the number of tokens consumed to produce the statment
    fn consumed(&self) -> usize {
        self.source.len()
    }

    /// Extracts a statement as a prefix of the given tokens
    fn parse(tokens: &'a [Token<'a>]) -> ParseRet<'a, Self> {
        Stmt::parse_let(tokens)
            .or_else(|| Stmt::parse_print(tokens))
            .or_else(|| Stmt::parse_assign(tokens))
            .or_else(|| Stmt::parse_eval(tokens))
            .unwrap_or_else(|| {
                ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingStmt,
                    context: ErrorContext::ParseStmt,
                    source: tokens.first(),
                })
            })
    }

    fn parse_let(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Self>> {
        use tokens::{
            Keyword::Let,
            Oper::Assign,
            TokenKind::{Keyword, Oper},
        };
        use ErrorContext::{LetEquals, LetName};

        // A let statement is made up of a sequence of tokens that looks something like:
        //   "let" Ident "=" Expr ";"
        // We'll go through and get each piece in turn

        // 1. "let"
        match tokens.first()?.kind {
            Keyword(Let) => (),
            _ => return None,
        }

        // Because we saw the "let" keyword, we're fully expecting a let statement, so we'll produce
        // errors instead of just failing

        let mut errors = Vec::new();

        // 2. Ident
        let name = next!(Ident::parse(tokens.get(1)).with_context(LetName), errors);

        if tokens.len() <= 2 {
            errors.push(Error {
                kind: ErrorKind::EOF,
                context: LetEquals,
                source: None,
            });

            return Some(ParseRet::Err(errors));
        }

        // 3. "="
        match tokens[2].kind {
            Oper(Assign) => (),
            _ => {
                errors.push(Error {
                    kind: ErrorKind::ExpectingEquals,
                    context: LetEquals,
                    source: Some(&tokens[2]),
                });

                return Some(ParseRet::Err(errors));
            }
        }

        // 4. Expr ";"
        let expr = next!(
            Stmt::parse_terminated_expr(&tokens[3..]).unwrap_or_else(|| {
                ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingExpr,
                    context: ErrorContext::LetExpr,
                    source: tokens.get(3),
                })
                .with_context(ErrorContext::LetExpr)
            }),
            errors
        );

        // 3 for the first 3 bits, plus 1 for the trailing semicolon
        let consumed = 4 + expr.consumed();

        Some(ParseRet::with_soft_errs(
            Stmt {
                kind: StmtKind::Let(name, expr),
                source: &tokens[..consumed],
            },
            errors,
        ))
    }

    fn parse_print(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Self>> {
        use tokens::{Keyword::Print, TokenKind::Keyword};
        use ErrorContext::PrintExpr;

        // A print statement is made up of a sequence of tokens that looks something like:
        //   "print" Expr ";"

        // 1. "print"
        match tokens.first()?.kind {
            Keyword(Print) => (),
            _ => return None,
        }

        // "print" is unambiguous, so not having a following expression is a hard error

        // 2. Expr ";"

        let mut errors = Vec::new();
        let expr = next!(
            Stmt::parse_terminated_expr(&tokens[1..]).unwrap_or_else(|| {
                ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingExpr,
                    context: PrintExpr,
                    source: tokens.get(1),
                })
                .with_context(PrintExpr)
            }),
            errors
        );

        // 1 for 'print', 1 for the trailing semicolon
        let consumed = 2 + expr.consumed();

        Some(ParseRet::with_soft_errs(
            Stmt {
                kind: StmtKind::Print(expr),
                source: &tokens[..consumed],
            },
            errors,
        ))
    }

    fn parse_assign(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Self>> {
        use tokens::{Oper::Assign, TokenKind::Oper};
        use ErrorContext::{AssignExpr, AssignName};

        // An assignment statement is made up of a sequence of tokens that looks something like:
        //   Ident "=" Expr ";"

        // At the very minimum, we'll require `Ident "="` to determine that it's an assignment
        if tokens.len() < 2 {
            return None;
        }

        let mut errors = Vec::new();

        // 1. Ident
        let name = match Ident::parse(tokens.first()) {
            ParseRet::Ok(n) => n,
            ParseRet::SoftErr(n, es) => {
                errors.extend(es.into_iter().map(|e| e.with_context(AssignName)));
                n
            }
            // If it's a hard error, we'll just cancel - this probably isn't an assignment
            // statement
            ParseRet::Err(_) => return None,
        };

        // 2. "="
        match tokens[1].kind {
            Oper(Assign) => (),
            // Again, this probably isn't an assignment if there's no equals.
            _ => return None,
        }

        // 3. Expr ";"
        let expr = next!(
            Stmt::parse_terminated_expr(&tokens[2..]).unwrap_or_else(|| {
                ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingExpr,
                    context: AssignExpr,
                    source: tokens.get(2),
                })
                .with_context(AssignExpr)
            }),
            errors
        );

        // 2 for the first couple bits, plus 1 for the trailing semicolon
        let consumed = 3 + expr.consumed();

        Some(ParseRet::with_soft_errs(
            Stmt {
                kind: StmtKind::Assign(name, expr),
                source: &tokens[..consumed],
            },
            errors,
        ))
    }

    fn parse_eval(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Self>> {
        use StmtKind::Eval;

        Some(Stmt::parse_terminated_expr(tokens)?.map(|expr| {
            let consumed = expr.consumed() + 1;
            Stmt {
                kind: Eval(expr),
                source: &tokens[..consumed],
            }
        }))
    }

    /// Extracts a semicolon-terminated expression from a subset of the given tokens, returning the
    /// expression. The number of consumed tokens will always be equal to the number consumed by
    /// the expression, plus one.
    fn parse_terminated_expr(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        use tokens::{Punc::Sep, TokenKind::Punc};

        let sep_idx = tokens
            .iter()
            .enumerate()
            .find(|(_, t)| t.kind == Punc(Sep))
            .map(|(i, _)| i)?;
        Some(Expr::parse(&tokens[..sep_idx])?)
    }
}

impl<'a> Expr<'a> {
    /// Returns a `Node` containing `self`.
    pub fn node(&'a self) -> Node<'a> {
        Node::Expr(self)
    }

    /// Returns the number of tokens consumed to produce the expression
    fn consumed(&self) -> usize {
        self.source.len()
    }

    fn parse(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        if tokens.is_empty() {
            return Some(ParseRet::Ok(Expr {
                kind: ExprKind::Empty,
                source: tokens,
            }));
        }
        //TODO: We may want to merge the callable parts here since names are going to be much more
        // common than binary operators and are much cheaper to parse first.
        Self::parse_num_expr(tokens)
            .or_else(|| Self::parse_prefix_op_expr(tokens))
            .or_else(|| Self::parse_bin_op_expr(tokens))
            .or_else(|| Self::parse_callable(tokens))
    }

    fn parse_callable(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        Self::parse_name_expr(tokens).or_else(|| Self::parse_fn_call(tokens))
    }

    fn parse_name_expr(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        Some(ParseRet::Ok(Expr {
            kind: Self::parse_name(tokens)?,
            source: tokens,
        }))
    }

    fn parse_name(tokens: &'a [Token<'a>]) -> Option<ExprKind<'a>> {
        if tokens.len() != 1 {
            None
        } else if let TokenKind::NameIdent(name) = tokens[0].kind {
            Some(ExprKind::Named(Ident {
                name,
                source: &tokens[0],
            }))
        } else {
            None
        }
    }

    fn parse_num_expr(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        // A number is represented as a single token, and we expect to consume the entire set of
        // tokens
        if tokens.len() != 1 {
            return None;
        }

        match tokens[0].kind {
            TokenKind::Num(string) => match string.parse::<isize>() {
                Ok(n) => Some(ParseRet::Ok(Expr {
                    kind: ExprKind::Num(n),
                    source: tokens,
                })),

                // Because `TokenKind::Num` will only be composed of digits, we know that the
                // problem must have been due to the integer value being too large
                Err(_) => Some(ParseRet::single_soft_err(
                    Expr {
                        kind: ExprKind::Num(0),
                        source: tokens,
                    },
                    Error {
                        kind: ErrorKind::IntegerValueTooLarge,
                        context: ErrorContext::NoContext,
                        source: Some(&tokens[0]),
                    },
                )),
            },
            _ => None,
        }
    }

    //fn parse_all(expr_sources: &'a [&'a [Token<'a>]]) -> ParseRet<'a, Vec<Expr<'a>>> {
    fn parse_all(expr_sources: Vec<&'a [Token<'a>]>) -> ParseRet<'a, Vec<Expr<'a>>> {
        let mut errors = Vec::new();
        let mut out = Vec::with_capacity(expr_sources.len());
        for tokens in expr_sources.iter() {
            use ParseRet::{Err, Ok, SoftErr};
            match Self::parse(tokens) {
                Some(Ok(expr)) => out.push(expr),
                Some(SoftErr(expr, errs)) => {
                    out.push(expr);
                    errors.extend(errs);
                }
                Some(Err(errs)) => return Err(errs),
                None => {
                    return ParseRet::single_err(Error {
                        kind: ErrorKind::ExpectingExpr,
                        context: ErrorContext::ParseAll,
                        source: tokens.first(),
                    })
                }
            }
        }
        ParseRet::with_soft_errs(out, errors)
    }

    fn parse_fn_call(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        let args = match &tokens.last()?.kind {
            TokenKind::Parens(args) => args,
            _ => return None,
        };

        use ParseRet::{Err, Ok, SoftErr};
        let mut errors = Vec::new();

        let callee = &tokens[..tokens.len() - 1];
        let callee = match Self::parse_callable(callee)? {
            Ok(callee) => callee,
            SoftErr(callee, errs) => {
                errors = errs;
                callee
            }
            Err(errs) => return Some(Err(errs)),
        };

        let args = tokens::split_at_commas(&args);
        let args = match Self::parse_all(args) {
            Ok(args) => args,
            SoftErr(args, errs) => {
                errors.extend(errs);
                args
            }
            Err(errs) => return Some(Err(errs)),
        };

        Some(ParseRet::with_soft_errs(
            Expr {
                kind: ExprKind::FnCall(Box::new(callee), args),
                source: tokens,
            },
            errors,
        ))
    }

    fn parse_both_bin_exprs(
        left_tokens: &'a [Token<'a>],
        op: BinOp,
        right_tokens: &'a [Token<'a>],
    ) -> ParseRet<'a, ExprKind<'a>> {
        use ParseRet::{Err, Ok, SoftErr};

        // A helper macro for processing errors
        macro_rules! r#try {
            ($expr:expr, $source:expr, $errors:expr, $context:expr) => {
                match $expr {
                    None => {
                        $errors.push(Error {
                            kind: ErrorKind::ExpectingExpr,
                            context: $context,
                            source: $source.first(), // we should probably put the operator token here if there's nothing on the left
                        });
                        Expr{ kind: ExprKind::Empty, source: $source }
                    },
                    Some(Err(errs)) => return Err(errs),
                    Some(SoftErr(exp, errs)) => {
                        $errors.extend(errs);
                        exp
                    },
                    Some(Ok(exp)) if exp.consumed() == $source.len() => exp,
                    Some(Ok(exp)) => {
                        $errors.push(Error {
                            kind: ErrorKind::UnexpectedToken,
                            context: $context,
                            source: Some(&$source[exp.consumed()]),
                        });
                        exp
                    }
                }
            };
        }

        let mut errors = Vec::new();

        let left = r#try!(
            Expr::parse(left_tokens),
            left_tokens,
            errors,
            ErrorContext::BinOperLeft
        );
        let right = r#try!(
            Expr::parse(right_tokens),
            right_tokens,
            errors,
            ErrorContext::BinOperRight
        );

        ParseRet::with_soft_errs(ExprKind::BinOp(Box::new(left), op, Box::new(right)), errors)
    }

    fn parse_bin_op_expr(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        // FIXME: This algorithm is naive, and should be replaced by some version of the
        // shunting-yard algorithm.

        // Get all of the `BinOp` tokens from the list, with their indices
        let bin_op_indices = tokens
            .iter()
            .enumerate()
            .filter_map(|(i, t)| match t.kind {
                TokenKind::Oper(op) => match BinOp::try_from(op) {
                    Ok(bin_op) => Some((i, bin_op)),
                    Err(_) => None,
                },
                _ => None,
            })
            .rev() // since all operators are left-assiciative, we want to find the right-most operator first
            .collect::<Vec<_>>();

        for ops in BIN_OP_PRECEDENCE.iter() {
            for op in ops.iter() {
                // Check if there's a token that will give us the operator we want
                if let Some((idx, _)) = bin_op_indices.iter().find(|(_, o)| o == op) {
                    let kind =
                        Expr::parse_both_bin_exprs(&tokens[0..*idx], *op, &tokens[idx + 1..]);

                    return Some(kind.map(|k| Expr {
                        kind: k,
                        source: tokens,
                    }));
                }
            }
        }

        None
    }

    /// If successful, returns a `PrefixOp` expression
    fn parse_prefix_op_expr(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        if tokens.is_empty() {
            return None;
        }

        // Get the actual prefix operator associated with the first token
        let op = match tokens[0].kind {
            TokenKind::Oper(op) => match PrefixOp::try_from(op) {
                Ok(op) => op,
                Err(_) => return None,
            },
            _ => return None,
        };

        let rhs = match Expr::parse(&tokens[1..]) {
            Some(res) => res,
            None => {
                // We'll try to get the source to be start of the expression, but that won't be
                // posible if `tokens.len() == 1`. In that case, we'll just give the first token
                // instead.
                //
                // TODO: The correct response may be to leave this as `None`. Change pending
                // discussion.
                let source = tokens.get(1).unwrap_or_else(|| &tokens[0]);

                return Some(ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingExpr,
                    context: ErrorContext::PrefixOp,
                    source: Some(source),
                }));
            }
        };

        // maps the inner type in the `ParseRet`
        Some(rhs.map(|ex| {
            let source = &tokens[..ex.consumed() + 1];

            Expr {
                kind: ExprKind::PrefixOp(op, Box::new(ex)),
                source,
            }
        }))
    }
}
