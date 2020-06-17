//! Verification for proof statments
//!
//! The high-level operations here are on functions and the global scope, taking the AST as input.
//! It is assumed here that the AST nodes given as input have passed through the checks in `verify`
//! without error.

mod bound;
mod bound_group;
//pub mod bound_method;
pub mod expr;
pub mod fast_bound_method;
mod fast_optimiser;
pub mod graph;
pub mod int;
//mod optimiser;
mod term;

#[cfg(test)]
mod tests;

use crate::ast::{self, proof::Condition as AstCondition, Ident};
use bound::{Bound, DescriptiveBound, Relation, RelationKind};
pub use expr::Expr;
use std::fmt::{self, Display, Formatter};
use std::ops::Not;

#[derive(Debug, Clone)]
pub struct Requirement<'a> {
    relation: bound::Relation<'a>,
}

impl<'a> Requirement<'a> {
    /// Returns a Requirement which is true iff self is false.
    pub fn contra_positive(&self) -> Requirement<'a> {
        Requirement {
            relation: self.relation.contra_positive(),
        }
    }

    /// Returns a requirement with a simplified relation.
    pub fn simplify(&self) -> Requirement<'a> {
        Requirement {
            relation: self.relation.simplify(),
        }
    }

    /// Substitute `x` with `with` in self and return the result.
    pub fn substitute(&self, x: &Ident<'a>, with: &Expr<'a>) -> Requirement<'a> {
        Requirement {
            relation: self.relation.substitute(x, with),
        }
    }

    /// Perform an atomic substitution of a group, replacing each occurence of the identifiers with
    /// the paired expression.
    pub fn substitute_all(&self, subs: &[(&Ident<'a>, &Expr<'a>)]) -> Requirement<'a> {
        Requirement {
            relation: self.relation.substitute_all(subs),
        }
    }

    /// Returns a vector of the distinct variables the requirement applies to.
    pub fn variables(&self) -> Vec<Ident<'a>> {
        self.relation.variables()
    }

    /// Returns the bounds on `name` given by self.
    /// If no bounds are given or if they cannot be computed, None is returned.
    pub fn bounds_on(&self, name: &Ident<'a>) -> Option<Bound<'a>> {
        self.relation.bounds_on(name)
    }

    /// Returns bounds specified by self.
    /// The tuple contains the variable the bound is on and the bound itself.
    /// It may not return all bounds since some bounds cannot yet be calculated.
    fn bounds(&self) -> Vec<DescriptiveBound<'a>> {
        self.relation.bounds()
    }

    fn as_relation<'b>(&'b self) -> &'b Relation<'a> {
        &self.relation
    }

    /// Returns an expression that is >= 0 if and only if self is true.
    pub fn ge0(&self) -> Expr<'a> {
        match self.relation.kind {
            // left <= right
            // ==> 0 <= right-left
            RelationKind::Le => Expr::Sum(vec![
                self.relation.right.clone(),
                Expr::Neg(Box::new(self.relation.left.clone())),
            ]),
            // left >= right
            // ==> left-right >= 0
            RelationKind::Ge => Expr::Sum(vec![
                self.relation.left.clone(),
                Expr::Neg(Box::new(self.relation.right.clone())),
            ]),
        }
    }
}

impl<'a> From<&AstCondition<'a>> for Requirement<'a> {
    fn from(cond: &AstCondition<'a>) -> Requirement<'a> {
        use ast::proof::CompareOp::{Ge, Le};
        use ast::proof::ConditionKind::{Compound, Malformed, Simple};
        match &cond.kind {
            // lhs <= rhs => 0 <= rhs-lhs
            Simple { lhs, op: Le, rhs } => Requirement {
                relation: Relation {
                    left: Expr::from(lhs),
                    kind: RelationKind::Le,
                    right: Expr::from(rhs),
                },
            },

            // lhs >= rhs => lhs-rhs >= 0
            Simple { lhs, op: Ge, rhs } => Requirement {
                relation: Relation {
                    left: Expr::from(lhs),
                    kind: RelationKind::Ge,
                    right: Expr::from(rhs),
                },
            },

            Compound {
                lhs: _,
                op: _,
                rhs: _,
            } => todo!(),

            Malformed => panic!("cannot create requirement from malformed condition"),
        }
    }
}

/// A result from an attempt to prove something.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ProofResult {
    /// The statement was false.
    False,
    /// The statement cannot be proven either true or false.
    Undetermined,
    /// The statement was true.
    True,
}

impl Not for ProofResult {
    type Output = ProofResult;
    fn not(self) -> ProofResult {
        use ProofResult::{False, True, Undetermined};
        match self {
            True => False,
            Undetermined => Undetermined,
            False => True,
        }
    }
}

pub trait SimpleProver<'a> {
    /// Create a SimpleProver with the given requirements.
    fn new(reqs: Vec<Requirement<'a>>) -> Self;

    /// Try to prove `req`. This will assume that the requirements passed to `new` are true.
    fn prove(&self, req: &Requirement<'a>) -> ProofResult;
}

pub trait Prover<'a> {
    /// Create a Prover with the given requirements.
    fn new(reqs: Vec<Requirement<'a>>) -> Self;

    /// Try to prove `req`. This will assume that the requirements passed to `new` are true.
    fn prove(&self, req: &Requirement<'a>) -> ProofResult;

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
    fn define(&'a self, x: Ident<'a>, expr: Expr<'a>) -> Self;

    /// Create a new prover whereby `x` is treated as a new identifier even if `x` was an
    /// identifier in self.
    fn shadow(&'a self, x: Ident<'a>) -> Self;
}

/// A utility type for implementing Prover with a SimpleProver
///
/// This creates a simple tree, the root of which is a SimpleProver created with some given bounds.
/// The childeren all store definitions and when asked to prove something, substitute their
/// definition before handing the proof on to their parent.
///
/// It does not yet implement the shadow method.
#[derive(Debug)]
pub enum ScopedSimpleProver<'a, P: SimpleProver<'a>> {
    Root(P),
    Defn {
        x: Ident<'a>,
        expr: Expr<'a>,

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

    fn prove(&self, req: &Requirement<'a>) -> ProofResult {
        use ScopedSimpleProver::{Defn, Root, Shadow};
        match self {
            Root(prover) => prover.prove(req),
            Defn {
                ref x,
                expr,
                parent,
            } => parent.prove(&req.substitute(x, expr)),
            Shadow { ref x, parent } => {
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

    fn define(&'a self, x: Ident<'a>, expr: Expr<'a>) -> Self {
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

impl<'a> Display for Requirement<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(&self.relation, f)
    }
}

struct PrettyFormatter<'a, T: 'a> {
    fmt: &'a T,
    file_str: &'a str,
}

impl<'a, T: PrettyFormat<'a> + Sized> Display for PrettyFormatter<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.fmt.pretty_format(f, self.file_str)
    }
}

trait PrettyFormat<'a>: Sized {
    fn pretty_format(&'a self, f: &mut Formatter, file_str: &'a str) -> fmt::Result;

    fn pretty(&'a self, file_str: &'a str) -> PrettyFormatter<'a, Self> {
        PrettyFormatter {
            fmt: self,
            file_str,
        }
    }
}

impl<'a> Requirement<'a> {
    pub fn pretty(&'a self, file_str: &'a str) -> impl 'a + Display {
        PrettyFormatter {
            fmt: &self.relation,
            file_str,
        }
    }
}

impl Display for ProofResult {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use ProofResult::{False, True, Undetermined};
        write!(
            f,
            "{}",
            match self {
                True => "True",
                Undetermined => "Undetermined",
                False => "False",
            }
        )
    }
}
