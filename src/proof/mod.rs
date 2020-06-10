//! Verification for proof statments
//!
//! The high-level operations here are on functions and the global scope, taking the AST as input.
//! It is assumed here that the AST nodes given as input have passed through the checks in `verify`
//! without error.

mod bound;
mod bound_group;
mod bound_method;
pub mod error;
mod expr;
mod int;
mod optimiser;

#[cfg(test)]
mod tests;

use self::bound::{Bound, Relation, RelationKind};
use self::error::Error;
use self::expr::{Atom, Expr, ONE, ZERO};
use crate::ast::{self, proof::Condition as AstCondition, Ident};

use std::fmt;
use std::ops::Not;

/// Attempts to prove that the entire contents of the program is within the bounds specified by the
/// proof rules.
fn validate<'a>(top_level_items: &'a [ast::Item<'a>]) -> Vec<Error<'a>> {
    todo!()
}

/// Represents the requirement `ge0 >= 0`
/// All requirements can written in this form.
#[derive(Debug, Clone)]
pub struct Requirement<'a> {
    pub ge0: Expr<'a>,
}

impl<'a> Requirement<'a> {
    pub fn map_ge0(&self, f: impl Fn(&Expr<'a>) -> Expr<'a>) -> Requirement<'a> {
        Requirement { ge0: f(&self.ge0) }
    }

    /// Returns a Requirement which is true iff self is false.
    pub fn contra_positive(&self) -> Requirement<'a> {
        //  ¬(0 <= expr)
        // => 0 >  expr
        // => 0 <  -expr
        // => 0 <= -expr -1
        self.map_ge0(|expr| {
            Expr::Sum(vec![
                Expr::Neg(Box::new(expr.clone())),
                Expr::Neg(Box::new(ONE)),
            ])
        })
    }

    /// Returns a requirement with a simplified ge0 expression
    pub fn simplify(&self) -> Requirement<'a> {
        self.map_ge0(Expr::simplify)
    }

    /// Substitute `x` with `with` in self and return the result.
    pub fn substitute(&self, x: Ident<'a>, with: &Expr<'a>) -> Requirement<'a> {
        self.map_ge0(|expr| expr.substitute(x, with))
    }

    /// Returns a vector of the distinct variables the requirement applies to.
    pub fn variables(&self) -> Vec<Ident<'a>> {
        self.ge0.variables()
    }

    /// Returns the bounds on `name` given by self.
    /// If no bounds are given or if they cannot be computed, None is returned.
    pub fn bounds_on(&self, name: &Ident<'a>) -> Option<Bound<'a>> {
        let name_expr = Expr::Atom(Atom::Named(*name));
        Relation {
            left: self.ge0.single_x(&name_expr)?,
            relation: RelationKind::Ge,
            right: ZERO,
        }
        .bounds_on_unsafe(&name_expr)
    }

    /// Returns bounds specified by self.
    /// The tuple contains the variable the bound is on and the bound itself.
    /// It may not return all bounds since some bounds cannot yet be calculated.
    fn bounds(&self) -> Vec<(Ident<'a>, Bound<'a>)> {
        self.ge0
            .variables()
            .iter()
            .filter_map(|x| self.bounds_on(x).map(|bounds| (*x, bounds)))
            .collect()
    }

    fn as_relation(&self) -> Relation<'a> {
        Relation {
            left: self.ge0.clone(),
            relation: RelationKind::Ge,
            right: ZERO,
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
                ge0: Expr::Sum(vec![Expr::from(rhs), Expr::Neg(Box::new(Expr::from(lhs)))]),
            },

            // lhs >= rhs => lhs-rhs >= 0
            Simple { lhs, op: Ge, rhs } => Requirement {
                ge0: Expr::Sum(vec![Expr::from(lhs), Expr::Neg(Box::new(Expr::from(rhs)))]),
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
    fn prove(&self, req: &Requirement) -> ProofResult;
}

pub trait Prover<'a> {
    /// Create a Prover with the given requirements.
    fn new(reqs: Vec<Requirement<'a>>) -> Self;

    /// Try to prove `req`. This will assume that the requirements passed to `new` are true.
    fn prove(&self, req: &Requirement) -> ProofResult;

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
    fn shadow(&'a self, x: Ident<'a>) -> Self;
}

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

impl<'a> fmt::Display for Requirement<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "0 <= {}", self.ge0)
    }
}

impl fmt::Display for ProofResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
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
