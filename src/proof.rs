//! Verification for proof statments
//!
//! The high-level operations here are on functions and the global scope, taking the AST as input.
//! It is assumed here that the AST nodes given as input have passed through the checks in `verify`
//! without error.

use crate::ast::{self, proof, Ident};

/// Attempts to prove that the entire contents of the program is within the bounds specified by the
/// proof rules.
fn validate<'a>(top_level_items: &'a [ast::Item<'a>]) -> Vec<Error<'a>> {
    todo!()
}

pub enum Error<'a> {
    /// This error occurs when the return value is used as part of a precondition
    ReturnValInPrecondition {
        /// The return value used (this identifier will always be the implicit return, `_`)
        val: Ident<'a>,
        /// The proof statement in which the error occured
        stmt: &'a proof::Stmt<'a>,
    },

    /// A name used in a proof statement that is neither an argument nor the return parameter
    NameNotFound {
        /// The referenced name that could not be found
        name: Ident<'a>,
        /// The proof statment in which the error occured
        stmt: &'a proof::Stmt<'a>,
    },

    /// The return value of a function was used in a proof statement for a function that does not
    /// return a value
    UsedMissingReturn {
        /// A marker for where exactly the return value was used
        val: Ident<'a>,
        /// The containing function declaration, so we can reference it in an error message
        fn_decl: &'a ast::Item<'a>,
    },
}
