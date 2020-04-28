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
    /// The source for a `Block` will always be a token
    source: &'a Token<'a>,
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
    Num(usize),

    /// A bracketed expression, using either curly-braces or parentheses. For example: `(x + y)` or
    /// `{ foo(x); y }`
    Bracket(Vec<Stmt<'a>>, Box<Expr<'a>>),
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
        let body = next!(Block::parse_fn_body(tokens.get(3)), errors);

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
    fn parse(tokens: &'a [Token<'a>]) -> ParseRet<'a, Vec<Stmt<'a>>> {
        return Stmt::parse(tokens).map(|stmt| vec![stmt]);
        //return Stmt::parse(tokens).map(|stmt| Block { body: vec![stmt], source: tokens[0] /*FIXME this is not the correct source*/, });
        // return ParseRet::Ok(Block { body: vec![] });
        todo!()
    }

    fn parse_fn_body(token: Option<&'a Token<'a>>) -> ParseRet<'a, Self> {
        if let Some(token) = token {
            if let TokenKind::Curlys(tokens) = &token.kind {
                Block::parse(&tokens).map(|stmts| Block {
                    body: stmts,
                    source: token,
                })
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
}

impl<'a> Ident<'a> {
    fn parse(token: Option<&'a Token<'a>>) -> ParseRet<'a, Ident> {
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
}

/// Takes the token expected to be the function params and tries to parse it.
fn parse_fn_params<'a>(token: Option<&'a Token<'a>>) -> ParseRet<'a, FnParams<'a>> {
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
                source: a.first(),
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

impl<'a> Stmt<'a> {
    /// Returns the number of tokens consumed to produce the statment
    fn consumed(&self) -> usize {
        self.source.len()
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

    fn parse(tokens: &'a [Token<'a>]) -> ParseRet<'a, Self> {
        Self::parse_expr_stmt(tokens).unwrap_or(ParseRet::single_err(Error {
            kind: ErrorKind::ExpectingStmt,
            context: ErrorContext::ParseStmt,
            source: tokens.first(),
        }))
    }

    fn parse_expr_stmt(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Stmt<'a>>> {
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
        Some(Expr::parse(tokens)?.map(|expr| Stmt {
            kind: StmtKind::Eval(expr),
            source,
        }))
    }
}

impl<'a> Expr<'a> {
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
        Some(ParseRet::Ok(Expr {
            kind: Self::parse_num(tokens)?,
            source: tokens,
        }))
    }

    fn parse_num(tokens: &'a [Token<'a>]) -> Option<ExprKind<'a>> {
        if tokens.len() != 1 {
            None
        } else if let TokenKind::Num(string) = tokens[0].kind {
            Some(ExprKind::Num(
                string.parse().unwrap(), // we're unwrapping here since we know that a Num token must be a valid usize
            ))
        } else {
            None
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
                        //Expr{ kind: exp, source: $source }
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
