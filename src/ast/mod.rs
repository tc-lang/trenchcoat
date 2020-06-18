//! The production of the abstract syntax tree for a source file

use crate::tokens::{self, Keyword, Oper, Punc, Token, TokenKind};
use crate::types::{self, Type};
use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::ops::{Deref, Range};

/// A helper macro for removing some of the boilerplate code that's present in the combinations of
/// parsers that's used here.
///
/// The two inputs to this macro are a `ParseRet<T>` and a `mut Vec<Error>`. This macro collects
/// any soft errors into the provided list, if they are present, and yields the inner value of type
/// `T`. If there are hard errors instead, the calling function returns the complete set of errors.
///
/// As such, the caller of this macro must be a function with return type `Result<T, Vec<Error>>`.
macro_rules! next {
    ($f:expr, $errors:expr, $wrap:expr) => {{
        use ParseRet::*;
        match $f {
            Ok(v) => v,
            SoftErr(v, errs) => {
                $errors.extend($wrap(errs));
                v
            }
            Err(errs) => {
                $errors.extend($wrap(errs));
                return Err($errors);
            }
        }
    }};
}

/// A helper macro for cleaning up boilerplate code.
///
/// This is nearly identical to `next!`, with the only difference being that this macro is for
/// callers that return an `Option<Result<T, Vec<Error>>>`, with the distinction being used to
/// signify whether the another AST node should be parsed instead.
macro_rules! next_option {
    ($f:expr, $errors:expr, $wrap:expr) => {{
        use ParseRet::*;
        match $f {
            Ok(v) => v,
            SoftErr(v, errs) => {
                $errors.extend($wrap(errs));
                v
            }
            Err(errs) => {
                $errors.extend(errs);
                return Some(Err($errors));
            }
        }
    }};
}

mod error;
pub mod proof;
mod u8_to_str;

pub use error::{Context as ErrorContext, Error, Kind as ErrorKind, Source as ErrorSource};
use proof::consume_proof_lines;
use u8_to_str::u8_to_str;

////////////////////////////////////////////////////////////////////////////////
// Top-level interface                                                        //
////////////////////////////////////////////////////////////////////////////////

/// Attempts to parse the entire token tree into the AST
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
            ParseRet::SoftErr(item, errs) => {
                idx += item.consumed();
                items.push(item);
                // We don't set EOF here because the item parser is given all of the remaining
                // tokens to use to parse with
                errors.extend(errs);
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

/// A single AST type, given so that
#[derive(Debug, Copy, Clone)]
pub enum Node<'a> {
    Ident(&'a Ident<'a>),
    Item(&'a Item<'a>),
    Stmt(&'a Stmt<'a>),
    Expr(&'a Expr<'a>),
    Args(&'a FnArgs<'a>),
    ProofStmt(&'a proof::Stmt<'a>),
    ProofCond(&'a proof::Condition<'a>),
}

/// Most parsing functions return a ParseRet.
#[derive(Debug)]
pub enum ParseRet<'a, T> {
    /// The parse was succesful.
    Ok(T),

    /// The parse was unsuccesful, however the error wasn't too bad so a result is given to
    /// complete the token tree and parsing may continue. However no steps after parsing should be
    /// completed and the collected errors should be given.
    SoftErr(T, Vec<Error<'a>>),

    /// The programmer can't code. Parsing must now stop. They should feel bad.
    /// This should be used when an error is encountered and parsing should stop - for example if
    /// it is likely that future errors will not be sensible.
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

/// A type expression - e.g. `int`, `bool`, `(int, int)` or `{x: int, y: uint}`.
#[derive(Debug, Clone)]
pub struct TypeExpr<'a> {
    pub typ: Type<'a>,
    pub source: &'a [Token<'a>],
}

/// Returns a type expression representing an empty struct (`{}`) with no source.
/// Used in places such as when a function doesn't specify it's return type.
pub fn empty_struct<'a>() -> TypeExpr<'a> {
    TypeExpr {
        typ: types::empty_struct(),
        source: &[],
    }
}

/// A top-level item in the source
///
/// Currently only function declarations are supported.
#[derive(Debug)]
pub enum ItemKind<'a> {
    FnDecl {
        /// The proof statments associated with a function declaration
        proof_stmts: Vec<proof::Stmt<'a>>,
        name: Ident<'a>,
        params: FnParams<'a>,
        return_type: TypeExpr<'a>,
        body: Block<'a>,
    },
}

#[derive(Debug, Clone)]
pub struct Ident<'a> {
    pub name: &'a str,
    /// The source of the identifier
    ///
    /// This is allowed to be an expression in order to account for temporary variables, which are
    /// always the result of an expression. In normal cases, however, the single token is a
    /// `NameIdent` token.
    pub source: IdentSource<'a>,
}

#[derive(Debug, Clone)]
pub enum IdentSource<'a> {
    Token(&'a Token<'a>),
    RefExpr(&'a Expr<'a>),
    Expr(Box<Expr<'a>>),
}

impl<'a> PartialEq for Ident<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}
impl<'a> Eq for Ident<'a> {}

impl<'a> PartialOrd for Ident<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<'a> Ord for Ident<'a> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(other.name)
    }
}

impl<'a> fmt::Display for Ident<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Clone)]
pub struct FnArgs<'a> {
    pub args: Vec<Expr<'a>>,
    /// The single `Parens` token containing the arguments to the function
    pub source: &'a Token<'a>,
}

#[derive(Debug, Clone)]
pub struct FnParams<'a> {
    pub params: Vec<(Ident<'a>, Type<'a>)>,
    /// The single `Parens` token containing the function parameters
    pub source: &'a Token<'a>,
}

impl<'a> Deref for FnArgs<'a> {
    type Target = Vec<Expr<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.args
    }
}

impl<'a> Deref for FnParams<'a> {
    type Target = Vec<(Ident<'a>, Type<'a>)>;

    fn deref(&self) -> &Self::Target {
        &self.params
    }
}

/// A statement
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

    /// A lemma proof statement. e.g. `# lemma x <= y+z`
    Lemma(proof::Stmt<'a>),
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

    /// Accessing a field using `.`
    /// For example, `point.x` or `(a + b).x`
    FieldAccess(Box<Expr<'a>>, Ident<'a>),

    /// A struct literal, for example:
    /// `{x: 10, y: 20}`
    Struct(Vec<(Ident<'a>, Expr<'a>)>),

    /// Represents an expression which failed to parse due to an error.
    Malformed,
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
    &[BinOp::Or],
    &[BinOp::And],
    &[BinOp::Eq, BinOp::Lt, BinOp::Gt, BinOp::Le, BinOp::Ge],
    &[BinOp::Add, BinOp::Sub],
    &[BinOp::Mul, BinOp::Div],
];

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

    pub fn unwrap(self) -> T {
        use ParseRet::{Err, Ok, SoftErr};
        match self {
            Ok(v) => v,
            SoftErr(_, errs) => panic!(format!("{:?}", errs)),
            Err(errs) => panic!(format!("{:?}", errs)),
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Error-tracking functions                                                   //
////////////////////////////////////////////////////////////////////////////////

impl<'a> Node<'a> {
    /// Returns the byte range in the source file corresponding to the entire text of the AST Node
    pub fn byte_range(&self) -> Range<usize> {
        fn join(lower: Range<usize>, upper: Range<usize>) -> Range<usize> {
            lower.start..upper.end
        }

        use Node::{Args, Expr, Ident, Item, ProofCond, ProofStmt, Stmt};

        match self {
            Ident(id) => match &id.source {
                IdentSource::Token(t) => t.byte_range().unwrap(),
                IdentSource::RefExpr(ex) => ex.node().byte_range(),
                IdentSource::Expr(ex) => ex.node().byte_range(),
            },
            Args(args) => args.source.byte_range().unwrap(),
            Item(it) => join(
                it.source[0].byte_range().unwrap(),
                it.source.last().unwrap().byte_range().unwrap(),
            ),
            Stmt(st) => join(
                st.source[0].byte_range().unwrap(),
                st.source.last().unwrap().byte_range().unwrap(),
            ),
            Expr(ex) => join(
                ex.source[0].byte_range().unwrap(),
                ex.source.last().unwrap().byte_range().unwrap(),
            ),
            ProofStmt(st) => join(
                st.source[0].byte_range().unwrap(),
                st.source.last().unwrap().byte_range().unwrap(),
            ),
            ProofCond(cond) => join(
                cond.source[0].byte_range().unwrap(),
                cond.source.last().unwrap().byte_range().unwrap(),
            ),
        }
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
    ///
    /// This function assumes that the set of tokens provided is non-empty.
    fn parse_top_level(tokens: &'a [Token<'a>]) -> ParseRet<'a, Item<'a>> {
        assert!(!tokens.is_empty());

        if let Some(pr) = Self::parse_fn_decl(tokens) {
            return pr;
        }

        ParseRet::single_err(Error {
            kind: ErrorKind::ExpectingKeyword,
            context: ErrorContext::TopLevel,
            source: ErrorSource::Single(&tokens[0]),
        })
    }

    fn parse_fn_decl(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Item<'a>>> {
        let mut errors = Vec::new();

        // First, we'll attempt to parse any preceeding proof statments
        //
        // This isn't great moving forward because - with more types of items - the same proof
        // lines could be parsed multiple times. A simple fix could be to skip those at the
        // beginning (by filtering for the number of proof lines) and then parsing those once the
        // rest of the function is done, but this isn't necessary at this time because there is
        // only one type of top-level item.
        let (consumed, ret) = consume_proof_lines(tokens);

        // No need to set EOF because `consume_proof_lines` does it for us
        let proof_stmts = next_option!(ret, errors, |errs| errs);

        let begin_decl_idx = consumed;
        match tokens.get(begin_decl_idx)?.kind {
            TokenKind::Keyword(Keyword::Fn) => (),
            _ => return None,
        }

        // Token indexes for each part
        let name_idx = begin_decl_idx + 1;
        let params_idx = begin_decl_idx + 2;
        let ret_typ_idx = begin_decl_idx + 3;
        // body_idx will be determined later

        // Function name (an identifier)
        let name = next_option!(
            tokens
                .get(name_idx)
                .map(Ident::parse)
                .unwrap_or_else(|| ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingName,
                    context: ErrorContext::FnName,
                    source: ErrorSource::EOF,
                }))
                .with_context(ErrorContext::FnName),
            errors,
            // No additional source here because it would *actually* be the end of the file
            |errs| errs
        );

        // Function parameters
        // Again: no additional source here because it would *actually* be the end of the file
        let params = next_option!(parse_fn_params(tokens.get(params_idx)), errors, |errs| errs);

        // Function return type
        let (return_type, ret_consumed) = match parse_fn_return_type(&tokens[ret_typ_idx..]) {
            // If no type is specified, we default to returning an empty struct
            None => (empty_struct(), 0),
            // No need to replace EOF because we consume all of the tokens
            Some(pr) => next_option!(pr, errors, |errs| errs),
        };

        // Function body, just 1 curly token.
        // This will later be replaced with a parser that may consume more tokens for the
        //  => ... syntax.
        let body_idx = ret_typ_idx + ret_consumed;
        let body = next_option!(
            Block::parse_curlies(tokens.get(body_idx)).with_context(ErrorContext::FnBody),
            errors,
            // No need to replace EOF because `parse_curlies` only gives EOF if given None, which
            // will only be true if we've exhausted the tokens we've given (thus it's still EOF)
            |errs| errs
        );

        Some(ParseRet::with_soft_errs(
            Item {
                kind: ItemKind::FnDecl {
                    proof_stmts,
                    name,
                    params,
                    return_type,
                    body,
                },
                source: &tokens[0..body_idx + 1],
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
            source: &[], // FIXME - this probably doesn't matter since Empty will never error.
                         //       - if this is refactored, we can make it more sensible.
                         // We could just give an empty slice? Since an empty tail has no source.
                         // Not super useful for working out where it came from though.
                         // But, it should never error.
        };

        while idx < tokens.len() {
            let stmt = match Stmt::parse(&tokens[idx..]) {
                ParseRet::Ok(s) => s,
                ParseRet::SoftErr(s, es) => {
                    // No need to set EOF becaues `Stmt::parse` is given all of the remaining
                    // tokens
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
                    match Expr::parse(&tokens[idx..], true) {
                        // expression parsing failed, so we'll go with the original statement
                        // parsing error and return
                        None | Some(ParseRet::Err(_)) => {
                            // No need to set EOF becaues `Expr::parse` is given all of the
                            // remaining tokens
                            errors.extend_from_slice(&es);
                            return ParseRet::Err(errors);
                        }
                        Some(ParseRet::SoftErr(ex, ex_errs)) => {
                            tail = ex;
                            // No need to set EOF becaues `Expr::parse` is given all of the
                            // remaining tokens
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

    /// Parses a curly block from the given token, if available
    ///
    /// The error sources will only have EOF if the given token is None.
    fn parse_curlies(token: Option<&'a Token<'a>>) -> ParseRet<'a, Block<'a>> {
        use TokenKind::Curlys;

        let (token, inner_tokens) = match token {
            None => {
                return ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingCurlys,
                    context: ErrorContext::NoContext,
                    source: ErrorSource::EOF,
                })
            }
            Some(t) => match &t.kind {
                Curlys(inner_tokens) => (t, inner_tokens),
                _ => {
                    return ParseRet::single_err(Error {
                        kind: ErrorKind::ExpectingCurlys,
                        context: ErrorContext::NoContext,
                        source: ErrorSource::Single(t),
                    })
                }
            },
        };

        let ret = Block::parse_body(&inner_tokens).map(|(stmts, tail)| Block {
            body: stmts,
            tail: Box::new(tail),
            source: token,
        });

        match ret {
            ParseRet::Ok(block) => ParseRet::Ok(block),
            ParseRet::SoftErr(block, errs) => {
                ParseRet::SoftErr(block, Error::set_eof(errs, ErrorSource::End(token)))
            }
            ParseRet::Err(errs) => ParseRet::Err(Error::set_eof(errs, ErrorSource::End(token))),
        }
    }
}

impl<'a> Ident<'a> {
    /// Returns a `Node` containing `self`.
    pub fn node(&'a self) -> Node<'a> {
        Node::Ident(self)
    }

    /// Parses an identifier from the single token given
    ///
    /// The errors sources will never be EOF
    fn parse(token: &'a Token<'a>) -> ParseRet<'a, Ident> {
        match token.kind {
            TokenKind::NameIdent(name) => ParseRet::Ok(Ident {
                name,
                source: IdentSource::Token(token),
            }),
            TokenKind::TypeIdent(name) => ParseRet::single_soft_err(
                Ident {
                    name,
                    source: IdentSource::Token(token),
                },
                Error {
                    kind: ErrorKind::TypeIdent,
                    context: ErrorContext::UnknownName,
                    source: ErrorSource::Single(token),
                },
            ),
            _ => ParseRet::single_err(Error {
                kind: ErrorKind::ExpectingName,
                context: ErrorContext::UnknownName,
                source: ErrorSource::Single(token),
            }),
        }
    }
}

impl<'a> Type<'a> {
    /// Gives a type from a type identifier.
    /// At the moment, this hard-codes "int", "uint" and "bool" although in the future it won't
    /// have to since these will be special types in the prelude but for now there is no way to
    /// resolve types!
    fn from_name(name: &'a str) -> Self {
        match name {
            "int" => Type::Int,
            "uint" => Type::UInt,
            "bool" => Type::Bool,
            _ => Type::Named(name),
        }
    }
}

impl<'a> Type<'a> {
    fn parse_struct(inner: &'a [Token<'a>]) -> ParseRet<'a, Type<'a>> {
        let fields = tokens::split_at_commas(inner);
        let mut struct_fields = Vec::with_capacity(fields.len());
        let mut errors = Vec::new();

        for field_tokens in fields.iter() {
            // FIXME: The wrapping function *should* provide the next token from the commas, but we
            // currently have no way of getting that.
            let field = next!(types::StructField::parse(field_tokens), errors, |errs| errs);
            struct_fields.push(field);
        }

        ParseRet::with_soft_errs(Type::Struct(struct_fields), errors)
    }
}

impl<'a> types::StructField<'a> {
    fn parse(tokens: &'a [Token<'a>]) -> ParseRet<'a, Self> {
        // Ensure we have the correct number of tokens
        match tokens.len() {
            0 => {
                return ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingIdent,
                    context: ErrorContext::Struct,
                    source: ErrorSource::EOF,
                })
            }
            1 | 2 => {
                return ParseRet::single_err(Error {
                    // FIXME this should have further cases to provide a good soft error
                    kind: ErrorKind::MalformedStructField,
                    context: ErrorContext::Struct,
                    source: ErrorSource::Range(tokens),
                });
            }
            _ => (),
        }

        let mut errors = Vec::new();

        // Fist the field name (an identifier)
        let name = next!(
            Ident::parse(&tokens[0]).with_context(ErrorContext::Struct),
            errors,
            // No need to set EOF because `Ident::parse` never gives it
            |errs| errs
        );

        // Check for the colon
        match &tokens[1].kind {
            TokenKind::Punc(Punc::Colon) => (),
            _ => {
                return ParseRet::single_err(
                    // FIXME this can probably be a soft error
                    Error {
                        kind: ErrorKind::ExpectingColon,
                        context: ErrorContext::Struct,
                        source: ErrorSource::Single(&tokens[1]),
                    },
                );
            }
        };

        // Finally the type expression.
        // We don't set eof here because it consumes the rest of the tokens we have - it's still an
        // EOF for us
        let type_expr = next!(TypeExpr::parse(&tokens[2..]), errors, |errs| errs);

        ParseRet::with_soft_errs(
            types::StructField {
                name,
                typ: type_expr.typ,
            },
            errors,
        )
    }
}

impl<'a> TypeExpr<'a> {
    /// Parses a type expression from the start of a list of tokens, without necessarily consuming
    /// all of them
    ///
    /// The number of tokens used can be checked with `TypeExpr::consumed`.
    fn parse(tokens: &'a [Token<'a>]) -> ParseRet<'a, TypeExpr<'a>> {
        use ErrorContext::NoContext;
        use ErrorKind::ExpectingType;
        use TokenKind::{Curlys, Parens, TypeIdent};

        if tokens.is_empty() {
            return ParseRet::single_err(Error {
                kind: ExpectingType,
                context: NoContext,
                source: ErrorSource::EOF,
            });
        }

        let mut errors = Vec::new();

        let typ = match &tokens[0].kind {
            TypeIdent(name) => TypeExpr {
                typ: Type::from_name(*name),
                source: &tokens[0..1],
            },
            Curlys(inner) | Parens(inner) => TypeExpr {
                typ: next!(Type::parse_struct(inner), errors, |errs| Error::set_eof(
                    errs,
                    ErrorSource::End(&tokens[0])
                )),
                source: &tokens[0..1],
            },
            _ => {
                return ParseRet::single_err(Error {
                    kind: ExpectingType,
                    context: NoContext,
                    source: ErrorSource::Single(&tokens[0]),
                })
            }
        };

        ParseRet::with_soft_errs(typ, errors)
    }

    /// returns the number of tokens in the source of self
    fn consumed(&self) -> usize {
        self.source.len()
    }
}

/// Takes the token expected to be the function params and tries to parse it.
///
/// This will return EOF as the source only if the token is `None`
fn parse_fn_params<'a>(token: Option<&'a Token<'a>>) -> ParseRet<'a, FnParams<'a>> {
    let tokens = match token {
        Some(t) => match &t.kind {
            TokenKind::Parens(tokens) => tokens,
            _ => {
                return ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingParens,
                    context: ErrorContext::FnParams,
                    source: ErrorSource::Single(t),
                })
            }
        },
        None => {
            return ParseRet::single_err(Error {
                kind: ErrorKind::ExpectingParens,
                context: ErrorContext::FnParams,
                source: ErrorSource::EOF,
            })
        }
    };

    let params_tokens = tokens::split_at_commas(&tokens);

    let mut errors = Vec::new();
    let mut params = Vec::with_capacity(params_tokens.len());

    for tokens in params_tokens {
        let param = next!(
            parse_single_param(tokens).with_context(ErrorContext::FnParams),
            errors,
            // FIXME: We currently can't construct the comma tokens between the parameters, but
            // that's what should go here to replace eof
            |errs| errs
        );
        params.push(param);
    }

    ParseRet::with_soft_errs(
        FnParams {
            params,
            source: token.unwrap(),
        },
        errors,
    )
}

/// Attempts to parse a set of tokens as a single function parameter, including name, colon, and
/// type expression
///
/// Valid function parameters could be: `x: int` or `p: bool`.
fn parse_single_param<'a>(tokens: &'a [Token<'a>]) -> ParseRet<'a, (Ident<'a>, Type<'a>)> {
    // At the moment, this is the same as struct field parsing.
    return types::StructField::parse(tokens)
        .map(|field| (field.name, field.typ))
        .with_context(ErrorContext::FnParam);
}

fn parse_fn_return_type<'a>(
    tokens: &'a [Token<'a>],
) -> Option<ParseRet<'a, (TypeExpr<'a>, usize)>> {
    if tokens.is_empty() {
        return None;
    }

    // Check for '->'
    match &tokens[0].kind {
        // TODO At the moment, RightArrow is being used as Punc. This may change to sometimes be
        // an Oper in the future so I've not changed its token kind. This needs discussion.
        TokenKind::Oper(Oper::RightArrow) => (),
        _ => return None,
    }

    // Parse the type
    // The amount consumed is the type + 1 (for the arrow)
    Some(
        // No need to set EOF here because these are given the rest of the tokens available
        TypeExpr::parse(&tokens[1..])
            .map(|typ| {
                let consumed = typ.consumed() + 1;
                (typ, consumed)
            })
            .with_context(ErrorContext::FnReturnType),
    )
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
            .or_else(|| Stmt::parse_lemma(tokens))
            .or_else(|| Stmt::parse_eval(tokens))
            .unwrap_or_else(|| {
                ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingStmt,
                    context: ErrorContext::ParseStmt,
                    source: tokens
                        .first()
                        .map(ErrorSource::Single)
                        .unwrap_or(ErrorSource::EOF),
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

        if tokens.len() <= 1 {
            return Some(ParseRet::single_err(Error {
                kind: ErrorKind::ExpectingName,
                context: ErrorContext::LetName,
                source: ErrorSource::EOF,
            }));
        }

        let mut errors = Vec::new();

        // 2. Ident
        let name = next_option!(
            Ident::parse(&tokens[1]).with_context(LetName),
            errors,
            // No need to set EOF because `Ident::parse` only consumes the single token
            |errs| errs
        );

        if tokens.len() <= 2 {
            errors.push(Error {
                kind: ErrorKind::ExpectingEquals,
                context: LetEquals,
                source: ErrorSource::EOF,
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
                    source: ErrorSource::Single(&tokens[2]),
                });

                return Some(ParseRet::Err(errors));
            }
        }

        // 4. Expr ";"
        let expr = next_option!(
            Stmt::parse_terminated_expr(&tokens[3..]).unwrap_or_else(|| {
                ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingExpr,
                    context: ErrorContext::LetExpr,
                    source: match &tokens[3..] {
                        [] => ErrorSource::EOF,
                        [range @ ..] => ErrorSource::Range(range),
                    },
                })
                .with_context(ErrorContext::LetExpr)
            }),
            errors,
            // We don't set EOF because the tokens go to the end of what we have available
            |errs| errs
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
        let expr = next_option!(
            Stmt::parse_terminated_expr(&tokens[1..]).unwrap_or_else(|| {
                ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingExpr,
                    context: PrintExpr,
                    source: match &tokens[1..] {
                        [] => ErrorSource::EOF,
                        [range @ ..] => ErrorSource::Range(range),
                    },
                })
                .with_context(PrintExpr)
            }),
            errors,
            // We don't set EOF because the tokens go to the end of what we have available
            |errs| errs
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
        let name = match Ident::parse(&tokens[0]) {
            ParseRet::Ok(n) => n,
            ParseRet::SoftErr(n, es) => {
                // No need to set EOF because `Ident::parse` doesn't give that as a source
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
        let expr = next_option!(
            Stmt::parse_terminated_expr(&tokens[2..]).unwrap_or_else(|| {
                ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingExpr,
                    context: AssignExpr,
                    source: match &tokens[2..] {
                        [] => ErrorSource::EOF,
                        [range @ ..] => ErrorSource::Range(range),
                    },
                })
                .with_context(AssignExpr)
            }),
            errors,
            // We don't set EOF because the tokens go to the end of what we have available
            |errs| errs
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

    fn parse_lemma(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Self>> {
        use proof::StmtKind::{Contract, Lemma, Malformed, Require};

        let first = tokens.get(0)?;
        let proof_line = match &first.kind {
            TokenKind::ProofLine(ts) => ts,
            _ => return None,
        };

        let mut errors = Vec::new();
        let proof_stmt = next_option!(proof::Stmt::parse(proof_line), errors, |errs| {
            Error::set_eof(errs, ErrorSource::End(first))
        })?;

        // Push an error if the proof statement has the wrong kind
        match &proof_stmt.kind {
            Lemma { .. } => (),
            Require { .. } | Contract { .. } => {
                errors.push(Error {
                    kind: ErrorKind::ExpectingLemma,
                    context: ErrorContext::FnBody,
                    source: ErrorSource::Single(first),
                });
            }
            Malformed => (),
        }
        Some(ParseRet::with_soft_errs(
            Stmt {
                kind: StmtKind::Lemma(proof_stmt),
                source: &tokens[..1],
            },
            errors,
        ))
    }

    fn parse_eval(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Self>> {
        use StmtKind::Eval;

        Some(Stmt::parse_terminated_expr(tokens)?.map(|expr| {
            // +1 for it being terminated
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

        Expr::parse(&tokens[..sep_idx], false).map(|ret| match ret {
            ParseRet::Ok(expr) => ParseRet::Ok(expr),
            ParseRet::SoftErr(expr, errs) => ParseRet::SoftErr(
                expr,
                Error::set_eof(errs, ErrorSource::Single(&tokens[sep_idx])),
            ),
            ParseRet::Err(errs) => {
                ParseRet::Err(Error::set_eof(errs, ErrorSource::Single(&tokens[sep_idx])))
            }
        })
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

    fn parse(tokens: &'a [Token<'a>], allow_empty: bool) -> Option<ParseRet<'a, Expr<'a>>> {
        if tokens.is_empty() {
            if allow_empty {
                return Some(ParseRet::Ok(Expr {
                    kind: ExprKind::Empty,
                    source: tokens,
                }));
            } else {
                return None;
            }
        }

        //TODO: We may want to merge the callable parts here since names are going to be much more
        // common than binary operators and are much cheaper to parse first.
        Self::parse_num_expr(tokens)
            .or_else(|| Self::parse_prefix_op_expr(tokens))
            .or_else(|| Self::parse_bin_op_expr(tokens))
            .or_else(|| Self::parse_callable(tokens))
    }

    fn parse_callable(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        Self::parse_name_expr(tokens)
            .or_else(|| Self::parse_field_access(tokens))
            .or_else(|| Self::parse_fn_call(tokens))
            .or_else(|| Self::parse_struct_expr(tokens))
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
                source: IdentSource::Token(&tokens[0]),
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
                        source: ErrorSource::Single(&tokens[0]),
                    },
                )),
            },
            _ => None,
        }
    }

    fn parse_all(expr_sources: Vec<&'a [Token<'a>]>) -> ParseRet<'a, Vec<Expr<'a>>> {
        use ParseRet::{Err, Ok, SoftErr};

        let mut errors = Vec::new();
        let mut out = Vec::with_capacity(expr_sources.len());

        for tokens in expr_sources.iter() {
            match Expr::parse(tokens, false) {
                Some(Ok(expr)) => out.push(expr),
                Some(SoftErr(expr, errs)) => {
                    out.push(expr);
                    // FIXME: We currently have no way of getting the tokens we need to replace EOF
                    // here - the argument to this function should be changed
                    errors.extend(errs);
                }
                Some(Err(errs)) => {
                    // FIXME: We currently have no way of getting the tokens we need to replace EOF
                    // here - the argument to this function should be changed
                    errors.extend(errs);
                    return Err(errors);
                }
                None => {
                    return ParseRet::single_err(Error {
                        kind: ErrorKind::ExpectingExpr,
                        context: ErrorContext::ParseAll,
                        source: match tokens {
                            // FIXME: We currently have no way of getting the tokens we need to
                            // replace EOF here - the argument to this function should be changed
                            [] => ErrorSource::EOF,
                            [range @ ..] => ErrorSource::Range(range),
                        },
                    });
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
                errors = Error::set_eof(errs, ErrorSource::Single(tokens.last().unwrap()));
                callee
            }
            Err(errs) => {
                return Some(Err(Error::set_eof(
                    errs,
                    ErrorSource::Single(tokens.last().unwrap()),
                )))
            }
        };

        let args = tokens::split_at_commas(&args);
        let args = match Self::parse_all(args) {
            Ok(args) => args,
            SoftErr(args, errs) => {
                // FIXME: We currently don't have the information to replace EOF here - that will
                // require a modification to `split_at_commas`.
                errors.extend(errs);
                args
            }
            Err(errs) => {
                errors.extend(errs);
                // FIXME: We currently don't have the information to replace EOF here - that will
                // require a modification to `split_at_commas`.
                return Some(Err(errors));
            }
        };

        Some(ParseRet::with_soft_errs(
            Expr {
                kind: ExprKind::FnCall(
                    Box::new(callee),
                    FnArgs {
                        args,
                        source: tokens.last().unwrap(),
                    },
                ),
                source: tokens,
            },
            errors,
        ))
    }

    fn parse_both_bin_exprs(
        left_tokens: &'a [Token<'a>],
        op: BinOp,
        op_token: &'a Token<'a>,
        right_tokens: &'a [Token<'a>],
    ) -> ParseRet<'a, ExprKind<'a>> {
        use ParseRet::{Err, Ok, SoftErr};

        // A helper macro for processing errors
        macro_rules! r#try {
            ($expr:expr, $source:expr, $errors:expr, $context:expr, $eof:expr,) => {
                match $expr {
                    None => {
                        $errors.push(Error {
                            kind: ErrorKind::ExpectingExpr,
                            context: $context,
                            // we should probably put the operator token here if there's nothing on
                            // the left
                            source: match $source {
                                [] => $eof,
                                [range @ ..] => ErrorSource::Range(range),
                            },
                        });
                        Expr {
                            kind: ExprKind::Empty,
                            source: $source,
                        }
                    }
                    Some(Err(errs)) => {
                        $errors.extend(Error::set_eof(errs, $eof));
                        return Err($errors);
                    }
                    Some(SoftErr(exp, errs)) => {
                        $errors.extend(Error::set_eof(errs, $eof));
                        exp
                    }
                    Some(Ok(exp)) if exp.consumed() == $source.len() => exp,
                    Some(Ok(exp)) => {
                        $errors.push(Error {
                            kind: ErrorKind::UnexpectedToken,
                            context: $context,
                            source: ErrorSource::Single(&$source[exp.consumed()]),
                        });
                        exp
                    }
                }
            };
        }

        let mut errors = Vec::new();

        let left = r#try!(
            Expr::parse(left_tokens, false),
            left_tokens,
            errors,
            ErrorContext::BinOperLeft,
            ErrorSource::Single(op_token),
        );
        let right = r#try!(
            Expr::parse(right_tokens, false),
            right_tokens,
            errors,
            ErrorContext::BinOperRight,
            ErrorSource::EOF,
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
                TokenKind::Oper(op) => op.try_into().ok().map(|op: BinOp| (i, op)),
                _ => None,
            })
            .rev() // since all operators are left-associative, we want to find the right-most operator first
            .collect::<Vec<_>>();

        for ops in BIN_OP_PRECEDENCE.iter() {
            for op in ops.iter() {
                // Check if there's a token that will give us the operator we want
                if let Some((idx, _)) = bin_op_indices.iter().find(|(_, o)| o == op) {
                    let kind = Expr::parse_both_bin_exprs(
                        &tokens[0..*idx],
                        *op,
                        &tokens[*idx],
                        &tokens[idx + 1..],
                    );

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

        let rhs = match Expr::parse(&tokens[1..], false) {
            // We don't need to set EOF here because it's already going to the end of the set of
            // tokens we have available.
            Some(res) => res,
            None => {
                return Some(ParseRet::single_err(Error {
                    kind: ErrorKind::ExpectingExpr,
                    context: ErrorContext::PrefixOp,
                    source: match &tokens[1..] {
                        [] => ErrorSource::EOF,
                        [range @ ..] => ErrorSource::Range(range),
                    },
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

    fn parse_field_access(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        let l = tokens.len();
        if l < 3 {
            return None;
        }

        // The second to last token should be a `.`
        match &tokens[l - 2].kind {
            TokenKind::Punc(Punc::Dot) => (),
            _ => return None,
        }

        let mut errors = Vec::new();
        let expr = next_option!(
            Expr::parse_callable(&tokens[..l - 2])?,
            errors,
            // We set EOF to be the second-to-last token
            |errs| Error::set_eof(errs, ErrorSource::Single(&tokens[l - 2]))
        );
        let name = next_option!(
            Ident::parse(&tokens[l - 1]),
            errors,
            // No need to set EOF because this *is* the last token - and `Ident::parse` doesn't
            // generate EOF sources
            |errs| errs
        );
        Some(ParseRet::with_soft_errs(
            Expr {
                kind: ExprKind::FieldAccess(Box::new(expr), name),
                source: tokens,
            },
            errors,
        ))
    }

    fn parse_struct_expr(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Expr<'a>>> {
        if tokens.len() != 1 {
            return None;
        }

        let inner = match &tokens[0].kind {
            TokenKind::Curlys(inner) | TokenKind::Parens(inner) => inner,
            _ => return None,
        };

        let fields = tokens::split_at_commas(inner);
        let mut struct_fields = Vec::with_capacity(fields.len());
        // Keep track of the unnamed field index.
        // FIXME
        // For now, unnamed indexes are u8. This is definitely fine for now, since a 256 tuple is
        // probably all we'll need! This approach is not permenant however.
        // We are also allowing unnamed fields to be separated by named fields. Again, we should
        // change how this works.
        let mut unnamed_idx: u8 = 0;
        let mut errors = Vec::new();

        for field in fields.iter() {
            let struct_field = match Expr::parse(field, false) {
                // A valid expression was found, so this is an unnamed field
                Some(expr) => {
                    // FIXME: We should actually set EOF here, but we don't currently have the
                    // information that we need to do so
                    let expr = next_option!(expr, errors, |errs| errs);
                    // Generate a name based on the index
                    let name = Ident {
                        name: u8_to_str(unnamed_idx),
                        source: IdentSource::Expr(Box::new(expr.clone())),
                    };
                    unnamed_idx += 1;
                    (name, expr)
                }
                // Not a valid expression, so try parse it as a named field.
                None => {
                    // We need at least 3 tokens: `<name> ':' <expr>`
                    if field.len() < 3 || field[1].kind != TokenKind::Punc(Punc::Colon) {
                        // FIXME: This error will be garbage if the user has accidentally written
                        // two commas in a row
                        return Some(ParseRet::single_soft_err(
                            Expr::malformed(field),
                            Error {
                                kind: ErrorKind::MalformedStructField,
                                context: ErrorContext::StructExpr,
                                source: ErrorSource::Range(field),
                            },
                        ));
                    }

                    // TODO maybe we should allow naming unnamed fields, for example
                    // { 1: "world", 0: "hello" } would be the same as { "hello", "world" }
                    // Something to consider.
                    //
                    // No need to set EOF because `Ident::parse` doesn't produce EOF
                    let name = next_option!(Ident::parse(&field[0]), errors, |errs| errs);

                    // Try to parse the expression
                    let expr_tokens = &field[2..];
                    let expr_pr = match Expr::parse(expr_tokens, false) {
                        Some(expr_pr) => expr_pr,
                        None => {
                            // Error if there was not an expression
                            // FIXME: This error will be garbage if the user has accidentally
                            // written a comma following the colon
                            errors.push(Error {
                                kind: ErrorKind::MalformedStructField,
                                context: ErrorContext::StructExpr,
                                source: ErrorSource::Range(&field[2..]),
                            });
                            return Some(ParseRet::with_soft_errs(
                                Expr::malformed(expr_tokens),
                                errors,
                            ));
                        }
                    };
                    // FIXME: This has the same issue as above; we need more information to be able
                    // to set EOF to what it should be
                    let expr = next_option!(expr_pr, errors, |errs| errs);

                    (name, expr)
                }
            };

            struct_fields.push(struct_field);
        }

        // Simplify single item tuple to ExprKind::Bracket or else the type is a Struct
        // FIXME We need to change a struct to contain blocks rather than expressions.
        let kind = if struct_fields.len() == 1 && struct_fields[0].0.name == "0" {
            ExprKind::Bracket(Block {
                body: Vec::new(),
                tail: Box::new(struct_fields[0].1.clone()),
                source: &tokens[0],
            })
        } else {
            ExprKind::Struct(struct_fields)
        };

        Some(ParseRet::with_soft_errs(
            Expr {
                kind,
                source: tokens,
            },
            errors,
        ))
    }
}

impl<'a> Expr<'a> {
    /// Returns a malformed expression with the given source
    fn malformed(source: &'a [Token<'a>]) -> Expr<'a> {
        Expr {
            kind: ExprKind::Malformed,
            source: source,
        }
    }
}
