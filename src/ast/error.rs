//! Error definitions for ast parsing

use crate::errors::PrettyError;
use crate::tokens::Token;

/// Errors each have a kind and a context in which it occured. These can be combined with the
/// source token to create a hopefully ok error message.
#[derive(Debug, Clone)]
pub struct Error<'a> {
    pub kind: Kind,
    pub context: Context,
    pub source: Source<'a>,
}

/// The source for a parsing error; either a single token or a range
#[derive(Debug, Copy, Clone)]
pub enum Source<'a> {
    Single(&'a Token<'a>),
    Range(&'a [Token<'a>]),
    /// EOF gives the index of the token if the function producing the error was called with a
    /// slice of tokens. Whenever this may be the case, this should be accounted for and replaced
    /// with one of the other two
    EOF,
    /// Indicates that the source occured at the end of a block token - any of `Parens`, `Curlys`,
    /// or `ProofLine`.
    End(&'a Token<'a>),
}

#[derive(Debug, Clone, Copy)]
pub enum Kind {
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
    /// When a type is expected, the first token should be any of `TypeIdent`, `Parens`, or
    /// `Curlys`
    ExpectingType,
    ExpectingIdent,
    ExpectingColon,
    MalformedStructField,
    UnexpectedToken,

    /// An integer literal represents a value larger than `isize::MAX`, and so we cannot construct
    /// it
    IntegerValueTooLarge,

    /// An error resulting from proof statments. This occurs when two conditions were expected as
    /// part of a contract, but only one was given. It is possible that the user is missing the
    /// `require` keyword.
    SingleContractCondition,

    /// An error resulting from proof statments. This occurs when parsing a contract, which has
    /// conditions separated by `=>` tokens. There should only be two of these (so the value here
    /// will be ≥ 3)
    TooManyContractConditions(usize),

    /// A place where a proof condition expected to have a comparison operator but there was none
    /// found.
    CondWithoutCompareOp,

    /// A place where a proof condition has multiple comparison operators; e.g. `x < y < 5`
    ChainedComparison,

    /// A proof line was being parsed in a context where only lemmas are allowed
    ExpectingLemma,
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
    ProofStmt,
    ProofCond,
    ProofExpr,
}

impl<'a> Error<'a> {
    pub fn with_context(self, ctx: Context) -> Self {
        Self {
            context: ctx,
            ..self
        }
    }

    pub fn set_eof(mut errs: Vec<Self>, source: Source<'a>) -> Vec<Self> {
        errs.iter_mut().for_each(|e| {
            if let Source::EOF = e.source {
                e.source = source;
            }
        });
        errs
    }
}

impl PrettyError for Error<'_> {
    fn pretty_format(&self, file_str: &str, file_name: &str) -> String {
        todo!()
    }
}
