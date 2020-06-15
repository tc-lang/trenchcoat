//! Error definitions for ast parsing

use crate::ast::{Item, Node};
use crate::proof::{ProofResult, Requirement};
use crate::types::Type;

/// Errors each have a kind and a context in which it occured. These can be combined with the
/// source AST node to create a hopefully ok error message.
/// The source may not be given in some error cases, for example when there's an unexpected EOF.
#[derive(Debug, Clone)]
pub struct Error<'a> {
    pub kind: Kind<'a>,
    pub context: Context,
    /// In the future, we should make a source stack rather than just have 1 source.
    pub source: Node<'a>,
}

#[derive(Debug, Clone)]
pub enum Kind<'a> {
    ItemConflict(&'a Item<'a>, &'a Item<'a>),
    FunctionNotFound,
    FunctionMustBeName,
    IncorrectNumberOfArgs {
        n_given: usize,
        n_expected: usize,
    },
    VariableNotFound,
    AccessFieldOnNotStruct,
    TypeMismatch {
        expected: Vec<Type<'a>>,
        found: Type<'a>,
    },
    /// Indicates that the return identifier "_" appeared somewhere it isn't allowed
    MisplacedReturnIdent,
    /// Indicates that a certain feature is currently not allowed (even though it may be
    /// syntactically or otherwise valid)
    FeatureNotAllowed {
        description: &'static str,
    },
    /// A collection of proof requirements that didn't pass, along with their proof results.
    /// Note: The requirements are in terms of the variables in the calling scope.
    FailedProof(Vec<(ProofResult, Requirement<'a>)>),
}

#[derive(Debug, Clone, Copy)]
pub enum Context {
    TopLevel,
    ProofStmt,
    Expr,
    Assign,
    FnTail,
    FnArg,
    FieldAccess,
    BinOpTypeCheck,
}
