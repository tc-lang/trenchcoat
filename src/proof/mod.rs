//! Verification for proof statments
//!
//! The high-level operations here are on functions and the global scope, taking the AST as input.
//! It is assumed here that the AST nodes given as input have passed through the checks in `verify`
//! without error.

pub mod error;
mod expr;
mod graph;
mod int;

#[cfg(test)]
mod tests;

use crate::ast::{self, proof::Condition as AstCondition, proof::Expr as AstExpr, Ident};
use error::Error;
use expr::Expr;
use std::marker::PhantomData;
use std::ops::Deref;

/// Attempts to prove that the entire contents of the program is within the bounds specified by the
/// proof rules.
fn validate<'a>(top_level_items: &'a [ast::Item<'a>]) -> Vec<Error<'a>> {
    todo!()
}

/// A term defined as the product of variables with a coefficient, e.g. 2*x*y, or -4*z
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Term {
    /// The variables in the product of the term
    vars: Vec<String>,
    /// The coefficient on the product of variables
    coef: i128,
}

impl Term {
    /// Simplifies an expression (as given by ast::proof) into a sorted list of terms, plus any
    /// constants (2nd element) and a term to multiply the entire right-hand side by, if any exists
    /// (3rd element)
    ///
    /// Note that this expands products, so `x*(1 + y)` will become `x*y + x`
    fn simplify_to_lists<'a>(expr: AstExpr<'a>) -> (Vec<Term>, i128, Option<AstExpr<'a>>) {
        // Our general strategy here is to call this recursively, distributing out multiplication
        // and using addition to join lists, as those are fundamentally the only two operations we
        // need to do

        use ast::proof::ArithOp::{Add, Div, Mul, Sub};
        use ast::proof::ExprKind::{Compound, Literal, Malformed, Named};

        match expr.kind {
            Malformed => panic!("cannot simplify malformed expression"),
            Named(ident) => (vec![Term::single_var(ident.name.into())], 0, None),
            Literal(i) => (Vec::new(), i as i128, None),
            Compound { lhs, op, rhs } => match op {
                Add => {
                    // These are both tuples of information
                    let lhs = Term::simplify_to_lists(*lhs);
                    let rhs = Term::simplify_to_lists(*rhs);

                    let (mut lhs, lhs_const, rhs, rhs_const, aggregate) =
                        Term::multiply_sides(lhs, rhs);

                    // Insert the elements of rhs into lhs, grouping like terms
                    for term in rhs {
                        match lhs.binary_search_by_key(&&term.vars, |t| &t.vars) {
                            Ok(i) => {
                                lhs[i].coef += term.coef;
                                if lhs[i].coef == 0 {
                                    lhs.remove(i);
                                }
                            }
                            Err(i) => lhs.insert(i, term),
                        }
                    }

                    // lhs.extend(rhs);
                    // lhs.sort();
                    (lhs, lhs_const + rhs_const, aggregate)
                }
                Div => {
                    // Division is purely a matter of multiplying *everything else* by the
                    // expression, so that's what we'll do, after converting the left-hand side
                    let (terms, constant, mul_expr) = Term::simplify_to_lists(*lhs);

                    let aggregate = match mul_expr {
                        None => Some(rhs.deref().clone()),
                        Some(ex) => Some(AstExpr {
                            kind: Compound {
                                lhs: Box::new(ex.clone()),
                                op: Mul,
                                rhs: rhs.clone(),
                            },
                            source: &[],
                        }),
                    };

                    (terms, constant, aggregate)
                }
                Mul => {
                    // lhs_mul_expr is the left-hand side's contribution to whatever expression
                    // should be cascaded up and have everything else multiplied by
                    let (lhs, lhs_const, lhs_mul_expr) = Term::simplify_to_lists(*lhs);
                    let (terms, constant, rhs_mul_expr) =
                        Term::mul_set_by_expr(lhs, lhs_const, rhs.deref().clone());

                    let aggregate = match (lhs_mul_expr, rhs_mul_expr) {
                        (Some(ex), None) | (None, Some(ex)) => Some(ex.clone()),
                        (None, None) => None,
                        (Some(l), Some(r)) => Some(AstExpr {
                            kind: Compound {
                                lhs: Box::new(l.clone()),
                                op: Mul,
                                rhs: Box::new(r.clone()),
                            },
                            source: &[],
                        }),
                    };

                    (terms, constant, aggregate)
                }
                // Subtraction is equivalent to addition of rhs * -1, so we'll just do that instead
                Sub => {
                    let new_expr = AstExpr {
                        kind: Compound {
                            lhs: lhs.clone(),
                            op: Add,
                            rhs: Box::new(AstExpr {
                                kind: Compound {
                                    lhs: rhs.clone(),
                                    op: Mul,
                                    rhs: Box::new(AstExpr {
                                        kind: Literal(-1),
                                        source: &[],
                                    }),
                                },
                                source: &[],
                            }),
                        },
                        source: &[],
                    };

                    Term::simplify_to_lists(new_expr)
                }
            },
        }
    }

    /// Groups two sides of expressions of the form Term* + C, where the other side mulitplied by
    /// *_mul - e.g. the right-hand side should be multiplied by lhs_mul. The aggregate expression
    /// from base required multiplications is returned
    ///
    /// The returned values are (in order) the left-hand side terms + constant, then right-hand
    /// side terms + constant, then aggregate required multiplication.
    fn multiply_sides<'a>(
        lhs: (Vec<Term>, i128, Option<AstExpr<'a>>),
        rhs: (Vec<Term>, i128, Option<AstExpr<'a>>),
    ) -> (Vec<Term>, i128, Vec<Term>, i128, Option<AstExpr<'a>>) {
        use ast::proof::ArithOp::Mul;
        use ast::proof::ExprKind::Compound;

        let (mut lhs, mut lhs_const, lhs_mul) = lhs;
        let (mut rhs, mut rhs_const, rhs_mul) = rhs;

        let mut lhs_mul = lhs_mul.map(|ex| ex.clone());
        let mut rhs_mul = rhs_mul.map(|ex| ex.clone());

        macro_rules! handle_mul {
            ($cur_side:ident, $cur_const:ident, $cur_mul:ident * $other_mul:ident) => {
                if let Some(expr) = $other_mul.as_ref().cloned() {
                    let (new_side, new_const, new_mul) =
                        Term::mul_set_by_expr($cur_side, $cur_const, expr);
                    $cur_side = new_side;
                    $cur_const = new_const;

                    $cur_mul = match ($cur_mul, new_mul) {
                        (Some(ex), None) => Some(ex.clone()),
                        (None, Some(ex)) => Some(ex.clone()),
                        (Some(l), Some(r)) => Some(AstExpr {
                            kind: Compound {
                                lhs: Box::new(l.clone()),
                                op: Mul,
                                rhs: Box::new(r.clone()),
                            },
                            source: &[],
                        }),
                        (None, None) => None,
                    };
                }

                $other_mul = None
            };
        }

        let mut current_left = true;
        while lhs_mul.is_some() || rhs_mul.is_some() {
            if current_left {
                handle_mul!(lhs, lhs_const, lhs_mul * rhs_mul);
            } else {
                handle_mul!(rhs, rhs_const, rhs_mul * lhs_mul);
            }

            current_left = !current_left;
        }

        let aggregate = match (lhs_mul, rhs_mul) {
            (Some(ex), None) | (None, Some(ex)) => Some(ex.clone()),
            (None, None) => None,
            (Some(l), Some(r)) => Some(AstExpr {
                kind: Compound {
                    lhs: Box::new(l.clone()),
                    op: Mul,
                    rhs: Box::new(r.clone()),
                },
                source: &[],
            }),
        };

        (lhs, lhs_const, rhs, rhs_const, aggregate)
    }

    /// returns the new terms, in addition to any constants generated and an expression to multiply
    /// everything else by
    fn mul_set_by_expr<'a>(
        mut terms: Vec<Term>,
        constant: i128,
        expr: AstExpr<'a>,
    ) -> (Vec<Term>, i128, Option<AstExpr<'a>>) {
        // Each of the terms are multiplied by the expression
        //
        // There are a few different options here.
        //
        // For literals or named values, we only need to multiply those out through all terms -
        // this is fairly trivial.
        //
        // For compound expressions, there are a few cases:
        // * If the expression is a product, we can just do each component of the product in
        //   sequence, via repeated calls to this function.
        // * Sums can be split, so that we clone the set of terms and call this function again with
        //   the two different parts of the sum
        // * Subtraction can be represented as (A + (-1*B)), so we split it into and
        //   multiplication, and then call this function again
        // * Division can't be multiplied out, so we instead return that all other values should be
        //   multiplied by the divisor (via the final return value in this function)

        use ast::proof::ArithOp::{Add, Div, Mul, Sub};
        use ast::proof::ExprKind::{Compound, Literal, Malformed, Named};

        match &expr.kind {
            Malformed => panic!("cannot simplify malformed expression"),
            Named(ident) => {
                // add the name to all terms, sort their var names individually, and then sort all
                // terms
                for t in terms.iter_mut() {
                    t.vars.push(ident.name.into());
                    t.vars.sort();
                }
                // Add the individual term corresponding to multiplying by the constant
                terms.push(Term {
                    vars: vec![ident.name.into()],
                    coef: constant,
                });
                terms.sort();

                // Everything has been merged into the list of terms
                (terms, 0, None)
            }
            &Literal(i) => {
                // Multiply each of the terms, re-sort (optimization: skip this), and return
                // re: optimization - the sorting should be fine to skip; it just relies on the
                // implementation of Ord for Term and the uniqueness of sets of terms
                let i = i as i128;
                terms.iter_mut().for_each(|t| t.coef *= i);
                terms.sort();
                (terms, constant * i, None)
            }
            Compound { .. } => todo!(),
        }
    }

    /// A helper constructor for syntactical ease in a couple places
    fn single_var(name: String) -> Term {
        Term {
            vars: vec![name],
            coef: 1,
        }
    }
}

/// Represents a requirement of the form `φ ≤ Γ + C`, where `φ` and `Γ` are defined by a sum of
/// terms (where each term is composed of at least one variable) and `C` is an integer constant.
pub struct Requirement<'a> {
    /// Equivalent to `φ` from above. These are sorted and simplified
    lhs: Vec<Term>,
    /// Equivalent to `Γ` from above
    rhs: Vec<Term>,
    /// The constant term (`C`) from above
    constant: i128,
    /// A marker in order to ensure compatibility with other versions by giving `Requirement` a
    /// lifetime.
    _marker: PhantomData<&'a ()>,
}

impl Requirement<'_> {
    /// Produce the requirement that would be formed after substituting in a certain expression for
    /// a variable
    fn substitute(&self, x: Ident, with: &Expr) -> Requirement {
        todo!()
    }
}

impl<'a, 'b> From<&AstCondition<'b>> for Requirement<'a> {
    fn from(cond: &AstCondition) -> Requirement<'a> {
        use ast::proof::CompareOp::{Ge, Le};
        use ast::proof::ConditionKind::{Compound, Malformed, Simple};

        match &cond.kind {
            Simple { lhs, op, rhs } => {
                // Re-order the sides so that we get our condition in terms of A <= B.
                // Shifting is not currently used, but will be (eventually) to account for
                // conditions using strict inequality (i.e. x < y instead of x <= y).
                //
                // The shift amount is the value added to the constant term in the requirement to
                // adjust for the conversion between `<` and `<=`.
                let (lhs, rhs, shift) = match op {
                    Le => (lhs, rhs, 0),
                    Ge => (rhs, lhs, 0),
                };

                // We'll redefine lhs and rhs to get them as a sorted list of terms and any
                // additional constant term
                let lhs = Term::simplify_to_lists(lhs.clone());
                let rhs = Term::simplify_to_lists(rhs.clone());

                // We explicitly discard the aggregate multiplier here because we don't need to
                // acccount for the multiplications - as long as both sides have done it, we're in
                // keeping with the statement of the requirement.
                let (lhs, lhs_shift, rhs, rhs_shift, _aggregate) = Term::multiply_sides(lhs, rhs);

                Requirement {
                    lhs,
                    rhs,
                    constant: shift - lhs_shift - rhs_shift,
                    _marker: PhantomData,
                }
            }

            Compound { lhs, op, rhs } => todo!(),
            Malformed => panic!("cannot create requirement from malformed condition"),
        }
    }
}

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
