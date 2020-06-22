use super::expr::Expr;
use super::{ProofResult, Requirement};
use crate::ast::Ident;

/// A dummy Prover - always gives a result of undetermined.
pub struct Prover;

impl<'a> super::Prover<'a> for Prover {
    fn new(_: &[Requirement<'a>]) -> Prover {
        Prover
    }
    fn prove(&self, _: &Requirement<'a>) -> ProofResult {
        ProofResult::Undetermined
    }
    fn define(&'a self, _: Ident<'a>, _: Expr<'a>) -> Prover {
        Prover
    }
    fn shadow(&'a self, _: Ident<'a>) -> Prover {
        Prover
    }
}
