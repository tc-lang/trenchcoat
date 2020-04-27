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

#[derive(Debug, Clone)]
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
    /// This error is generated when a Corlys token was expected but another kind was given.
    ExpectingCurlys,
}

#[derive(Debug, Clone)]
pub enum Context {
    FnName,
    FnArgs,
    FnBody,
}
