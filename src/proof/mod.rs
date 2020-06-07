//! Verification for proof statments
//!
//! The high-level operations here are on functions and the global scope, taking the AST as input.
//! It is assumed here that the AST nodes given as input have passed through the checks in `verify`
//! without error.

mod bound;
pub mod error;
mod expr;
mod graph;
mod int;
mod term;

#[cfg(test)]
mod tests;

use crate::ast::{self, Ident};
use error::Error;
use expr::Expr;

/// Attempts to prove that the entire contents of the program is within the bounds specified by the
/// proof rules.
fn validate<'a>(top_level_items: &'a [ast::Item<'a>]) -> Vec<Error<'a>> {
    todo!()
}

pub struct Requirement<'a>(bound::Relation<'a>);

/// A result from an attempt to prove something.
#[derive(Debug, PartialEq, Eq)]
pub enum ProofResult {
    /// The statement was false.
    False,
    /// The statement cannot be proven either true or false.
    Undetermined,
    /// The statement was true.
    True,
}

pub trait SimpleProver<'a> {
    /// Create a SimpleProver with the given requirements.
    fn new(reqs: Vec<Requirement<'a>>) -> Self;

    /// Try to prove `req`. This will assume that the requirements passed to `new` are true.
    fn prove(&self, req: &Requirement) -> ProofResult;
}

pub trait Prover<'a> {
    /// Create a Prover with the given requirements.
    fn new(reqs: Vec<Requirement<'a>>) -> Self;

    /// Try to prove `req`. This will assume that the requirements passed to `new` are true.
    fn prove(&mut self, req: &Requirement) -> ProofResult;

    /// Return a new prover whereby `x` is substituted for `expr` before proofs are made.
    /// `x` may refer to an identity which already exists, in which case the new `x` will be mapped
    /// to an expression involving the old `x`.
    ///
    /// For example,
    /// ```trenchcoat
    /// # x < 2
    /// fn f(x: Int) {
    ///     x = x+2
    /// }
    /// ```
    /// Then you might do `let prover2 = prover1.define(x, x+2)`
    /// then expressions passed to prover2 will map `x` in `prover2` to `x+2` in `prover1`.
    fn define(&'a self, x: Ident<'a>, expr: &'a Expr<'a>) -> Self;

    /// Create a new prover whereby `x` is treated as a new identifier even if `x` was an
    /// identifier in self.
    fn shadow(&self, x: Ident<'a>) -> Self;
}

/*

/// A utility type for implementing Prover with a SimpleProver
///
/// This creates a simple tree, the root of which is a SimpleProver created with some given bounds.
/// The childeren all store definitions and when asked to prove something, substitute their
/// definition before handing the proof on to their parent.
///
/// It does not yet implement the shadow method.
pub enum ScopedSimpleProver<'a, P: SimpleProver<'a>> {
    Root(P),
    Defn {
        x: Ident<'a>,
        expr: &'a Expr<'a>,

        parent: &'a ScopedSimpleProver<'a, P>,
    },
    Shadow {
        x: Ident<'a>,
        parent: &'a ScopedSimpleProver<'a, P>,
    },
}

impl<'a, P: SimpleProver<'a>> Prover<'a> for ScopedSimpleProver<'a, P> {
    fn new(reqs: Vec<Requirement<'a>>) -> Self {
        Self::Root(P::new(reqs))
    }

    fn prove(&self, req: &Requirement) -> ProofResult {
        use ScopedSimpleProver::{Defn, Root, Shadow};
        match self {
            Root(prover) => prover.prove(req),
            Defn { x, expr, parent } => parent.prove(&req.substitute(*x, expr)),
            Shadow { x, parent } => {
                // If the requirement to be proven requires something of x, then we can't prove it
                // since we know nothing about x!
                // Otherwise, hand it up.
                if req.variables().contains(x) {
                    ProofResult::Undetermined
                } else {
                    parent.prove(req)
                }
            }
        }
    }

    fn define(&'a self, x: Ident<'a>, expr: &'a Expr<'a>) -> Self {
        Self::Defn {
            x,
            expr,
            parent: self,
        }
    }

    fn shadow(&'a self, x: Ident<'a>) -> Self {
        Self::Shadow { x, parent: self }
    }
}

impl<'a, P: SimpleProver<'a>> ScopedSimpleProver<'a, P> {
    pub fn from(sp: P) -> Self {
        Self::Root(sp)
    }
}
*/
