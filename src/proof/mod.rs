//! Verification for proof statements
//!
//! The high-level operations here are on functions and the global scope, taking the AST as input.
//! It is assumed here that the AST nodes given as input have passed through the checks in `verify`
//! without error.

mod bound;
//mod bound_group;
pub mod bound_method;
pub mod expr;
pub mod graph;
pub mod int;
mod optimiser;
mod sign;
mod term;

#[cfg(test)]
mod tests;

use crate::ast::{self, proof::Condition as AstCondition, Ident};
use bound::{Relation, RelationKind};
pub use expr::Expr;
use std::fmt::{self, Display, Formatter};
use std::marker::PhantomData;
use std::ops::{Deref, Not};

/// The standard prover uses the graph method for normal proofs and the bound method for lemma
/// proofs.
pub type StandardSimpleProver<'a> =
    JointSimpleProver<'a, graph::Prover, bound_method::DefaultSimpleProver<'a>>;
/// Wrapped `StandardSimpleProver`
pub type StandardProver<'a, 'b> = ScopedSimpleProver<'a, 'b, StandardSimpleProver<'a>>;

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
    //pub fn bounds_on(&self, name: &Ident<'a>) -> Option<Bound<'a>> {
    //    self.relation.bounds_on(name)
    //}

    /// Returns bounds specified by self.
    /// The tuple contains the variable the bound is on and the bound itself.
    /// It may not return all bounds since some bounds cannot yet be calculated.
    //fn bounds(&self) -> Vec<DescriptiveBound<'a>> {
    //    self.relation.bounds()
    //}

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

/// The implementation of `From` here provides an intersection of requirements - i.e. one
/// "compound" requirement that requires each requirement individually.
///
/// This will panic if the ast condition has a `Compound { op: Or }` condition (those are difficult
/// to represent) or if there is a malformed condition.
impl<'a> From<&AstCondition<'a>> for Vec<Requirement<'a>> {
    fn from(cond: &AstCondition<'a>) -> Vec<Requirement<'a>> {
        use ast::proof::{
            CompareOp::{Ge, Le},
            ConditionKind::{Compound, Malformed, Simple},
            LogicOp::{And, Or},
        };

        match &cond.kind {
            Simple { lhs, op, rhs } => {
                let kind = match op {
                    Le => RelationKind::Le,
                    Ge => RelationKind::Ge,
                };

                vec![Requirement {
                    relation: Relation {
                        left: lhs.into(),
                        kind,
                        right: rhs.into(),
                    },
                }]
            }
            Compound { op: Or, .. } => unimplemented!(),
            Compound { lhs, op: And, rhs } => {
                let mut reqs = Vec::from(lhs.deref());
                reqs.extend(Vec::from(rhs.deref()));
                reqs
            }
            Malformed => panic!("cannot create requirements from malformed condition"),
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
    fn new(reqs: &[Requirement<'a>]) -> Self;

    /// Try to prove `proposition`. This will assume that the requirements passed to `new` are true.
    fn prove(&self, proposition: &Requirement<'a>) -> ProofResult;

    /// Like prove, but intended for proving lemmas. This may have a longer runtime and is
    /// hopefully capable of proving more.
    ///
    /// The default behaviour is to just use self.prove
    fn prove_lemma(&self, proposition: &Requirement<'a>) -> ProofResult {
        self.prove(proposition)
    }

    fn add_requirements(&mut self, reqs: &[Requirement<'a>]);
}

pub trait Prover<'a, 'b> {
    /// Create a Prover with the given requirements.
    fn new(reqs: &[Requirement<'a>]) -> Self;

    /// Try to prove `req`. This will assume that the requirements passed to `new` are true.
    fn prove(&self, req: &Requirement<'a>) -> ProofResult;

    /// Like prove, but intended for proving lemmas. This may have a longer runtime and is
    /// hopefully capable of proving more.
    ///
    /// The default behaviour is to just use self.prove
    fn prove_lemma(&self, req: &Requirement<'a>) -> ProofResult {
        self.prove(req)
    }

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
    fn define(&'b self, x: Ident<'a>, expr: Expr<'a>) -> Self;

    /// Create a new prover whereby `x` is treated as a new identifier even if `x` was an
    /// identifier in self.
    fn shadow(&'b self, x: Ident<'a>) -> Self;
}

/// A SimpleProver which uses P for standard proofs and LP for lemma proofs.
pub struct JointSimpleProver<'a, P: SimpleProver<'a>, LP: SimpleProver<'a>> {
    prover: P,
    lemma_prover: LP,

    lifetime: PhantomData<&'a ()>,
}

impl<'a, P: SimpleProver<'a>, LP: SimpleProver<'a>> SimpleProver<'a>
    for JointSimpleProver<'a, P, LP>
{
    fn new(reqs: &[Requirement<'a>]) -> Self {
        // TODO We could lazily generate provers (since prove_lemma isn't going to be used in
        // quite a few cases). This probably isn't super worthwhile because creating a bound prover
        // is pretty cheap.
        JointSimpleProver {
            prover: P::new(reqs.clone()),
            lemma_prover: LP::new(reqs),

            lifetime: PhantomData,
        }
    }

    fn prove(&self, prop: &Requirement<'a>) -> ProofResult {
        self.prover.prove(prop)
    }

    fn prove_lemma(&self, prop: &Requirement<'a>) -> ProofResult {
        self.lemma_prover.prove_lemma(prop)
    }

    fn add_requirements(&mut self, reqs: &[Requirement<'a>]) {
        self.prover.add_requirements(reqs);
        self.lemma_prover.add_requirements(reqs);
    }
}

/// A utility type for implementing Prover with a SimpleProver
///
/// This creates a simple tree, the root of which is a SimpleProver created with some given bounds.
/// The childeren all store definitions and when asked to prove something, substitute their
/// definition before handing the proof on to their parent.
#[derive(Debug)]
pub enum ScopedSimpleProver<'a, 'b, P: SimpleProver<'a>> {
    Root(P),
    Defn {
        x: Ident<'a>,
        expr: Expr<'a>,

        parent: &'b ScopedSimpleProver<'a, 'b, P>,
    },
    Shadow {
        x: Ident<'a>,
        parent: &'b ScopedSimpleProver<'a, 'b, P>,
    },
}

impl<'a, 'b, P: SimpleProver<'a>> Prover<'a, 'b> for ScopedSimpleProver<'a, 'b, P> {
    fn new(reqs: &[Requirement<'a>]) -> Self {
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

    fn prove_lemma(&self, req: &Requirement<'a>) -> ProofResult {
        use ScopedSimpleProver::{Defn, Root, Shadow};
        match self {
            Root(prover) => prover.prove_lemma(req),
            Defn {
                ref x,
                expr,
                parent,
            } => parent.prove_lemma(&req.substitute(x, expr)),
            Shadow { ref x, parent } => {
                // If the requirement to be proven requires something of x, then we can't prove it
                // since we know nothing about x!
                // Otherwise, hand it up.
                if req.variables().contains(x) {
                    ProofResult::Undetermined
                } else {
                    parent.prove_lemma(req)
                }
            }
        }
    }

    fn define(&'b self, x: Ident<'a>, expr: Expr<'a>) -> Self {
        Self::Defn {
            x,
            expr,
            parent: self,
        }
    }

    fn shadow(&'b self, x: Ident<'a>) -> Self {
        Self::Shadow { x, parent: self }
    }
}

impl<'a, 'b, P: SimpleProver<'a>> ScopedSimpleProver<'a, 'b, P> {
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
