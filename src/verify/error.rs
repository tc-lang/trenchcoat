//! Error definitions for ast parsing

use crate::ast::{Item, Node};
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

    ReturnType,
    TypeMismatch {
        expected: Vec<Type<'a>>,
        found: Type<'a>,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum Context {
    NoContext,
    TopLevel,
    FnBody,
    Expr,
    Assign,
    FnTail,
    FnArg,
    FieldAccess,
    BinOpTypeCheck,
}

impl<'a> Error<'a> {
    pub fn with_context(self, ctx: Context) -> Self {
        Self {
            context: ctx,
            ..self
        }
    }
}
