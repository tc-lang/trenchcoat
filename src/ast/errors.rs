//! Error types and messages for parsing into the AST

use crate::token_tree::{Delim, Kwd, Punc, Token, TokenKind};

#[derive(Debug, Clone)]
pub struct Error<'a> {
    pub kind: Kind<'a>,
    pub src: &'a [Token<'a>],
}

#[derive(Debug, Clone)]
// A placeholder error kind until we need more
pub enum Kind<'a> {
    Expecting {
        expecting: Expecting<'a>,
        // None for EOF
        found: Option<TokenKind<'a>>,
        context: ExpectingContext,
    },
    Unexpected,
    IllegalTopLevelKeyword {
        keyword: Kwd,
    },
}

#[derive(Debug, Clone)]
pub enum Expecting<'a> {
    Ident,
    Type,
    /// Either `{..}` or `if ...`
    ElseExpr,
    Expr,
    Token(TokenKind<'a>),
    Delim(Delim),
    OneOf(&'a [Expecting<'a>]),
}

impl<'a> Expecting<'a> {
    fn punc(punc: Punc) -> Expecting<'a> {
        Expecting::Token(TokenKind::Punctuation(punc))
    }
}

impl<'a> From<Punc> for Expecting<'a> {
    fn from(punc: Punc) -> Expecting<'a> {
        Expecting::punc(punc)
    }
}

#[derive(Debug, Clone)]
pub enum ExpectingContext {
    TopLevelKwd,

    FnName,
    FnParams,

    Expr,
    ExprPrefixOp,

    Else,

    StmtSep,

    StructFieldName,
    StructFieldColon,
    StructFieldComma,

    StructExprName,
    StructExprColon,
    StructExprComma,

    TupleExprName,
    TupleExprColon,
    TupleExprComma,

    Type,

    TypeDeclName,

    TupleCommaOrColon,

    ForName,
    ForEq,
    ForIn,
    ForBlock,
    ForElseBlock,

    LoopBlock,

    WhileBlock,
    WhileElseBlock,

    DoWhileBlock,
    DoWhileWhile,
    DoWhileElseBlock,

    MatchCurlies,
    MatchArrow,
    MatchComma,

    PatIdent,

    LetEq,

    ClosureParams,
    ClosureArrow,

    GenericParamComma,
    GenericParamColon,
    GenericParamName,

    CloseGenericParams,

    GenericArgComma,

    CloseGenericArgs,
}
