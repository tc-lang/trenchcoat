//! Error definitions for ast parsing

use crate::tokens::Token;

/// Errors each have a kind and a context in which it occured. These can be combined with the
/// source token to create a hopefully ok error message.
/// The source may not be given in some error cases, for example when there's an unexpected EOF.
#[derive(Debug, Clone)]
pub struct Error<'a> {
    pub kind: ErrorKind,
    pub context: Context,
    pub source: Option<&'a Token<'a>>,
}

#[derive(Debug, Clone, Copy)]
pub enum ErrorKind {
    /// This error is generated when, during parsing, there are no more tokens when some are
    /// expected.
    EOF,
    /// This error is generated when a type ident is given where a name ident should have been.
    /// This didd contain a string, maybe useful for suggesting a valid name later on however now
    /// the Error type contains the token so it can be retrieved from that.
    TypeIdent,
    /// This error is generated when a NameIdent token was expected but another kind was given.
    ExpectingName,
    /// This error is generated when a Parens token was expected but another kind was given.
    ExpectingParens,
    /// This error is generated when a Curlys token was expected but another kind was given.
    ExpectingCurlys,
    ExpectingKeyword,
    ExpectingEquals,
    ExpectingExpr,
    ExpectingStmt,
    ExpectingType,
    ExpectingIdent,
    ExpectingComma,
    ExpectingTypeIdent,
    ExpectingColon,
    MalformedStructField,
    UnexpectedToken,

    /// An integer literal represents a value larger than `isize::MAX`, and so we cannot construct
    /// it
    IntegerValueTooLarge,
}

#[derive(Debug, Clone, Copy)]
pub enum Context {
    NoContext,
    UnknownName,
    TopLevel,
    FnName,
    FnParam,
    FnParams,
    FnReturnType,
    FnBody,
    LetName,
    LetEquals,
    LetExpr,
    PrintExpr,
    AssignName,
    AssignExpr,
    BinOperLeft,
    BinOperRight,
    PrefixOp,
    ParseStmt,
    ParseAll,
    Struct,
    StructExpr,
}

impl<'a> Error<'a> {
    pub fn with_context(self, ctx: Context) -> Self {
        Self {
            context: ctx,
            ..self
        }
    }
}
