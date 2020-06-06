use super::expr::Expr;
use std::fmt;

/// Represents a bound on something.
#[derive(Debug, Clone, PartialEq)]
pub enum Bound<'a> {
    /// The thing must be <= expr
    Le(Expr<'a>),
    /// The thing must be >= expr
    Ge(Expr<'a>),
}

/// Represents a relation between 2 expressions.
/// For example: left <= (RelationKind::Le) right
///
/// This can be used to rearrange various relations to get particular bounds.
#[derive(Debug, Clone)]
pub struct Relation<'a> {
    pub left: Expr<'a>,
    pub relation: RelationKind,
    pub right: Expr<'a>,
}

/// A kind of a Relation
#[derive(Debug, Clone, Copy)]
pub enum RelationKind {
    /// Less than or equal to (<=)
    Le,
    /// Greater than or equal to (>=)
    Ge,
}

impl<'a> Bound<'a> {
    /// Apply f to the bound expression and return the new bound.
    pub fn map(&self, f: impl Fn(&Expr<'a>) -> Expr<'a>) -> Bound<'a> {
        use Bound::{Ge, Le};
        match self {
            Ge(expr) => Ge(f(expr)),
            Le(expr) => Le(f(expr)),
        }
    }

    /// Call Expr::simplify on the bound expression
    pub fn simplify(&self) -> Bound<'a> {
        self.map(Expr::simplify)
    }
}

impl RelationKind {
    /// Returns the opposite kind - note that this IS NOT the contra-positive, but what you would
    /// change the relation to if you multiplied both sides by -1 or took their reciprocals.
    ///  Le.opposite() == Ge
    ///  Ge.opposite() == Le
    pub fn opposite(self) -> RelationKind {
        use RelationKind::{Ge, Le};
        match self {
            Le => Ge,
            Ge => Le,
        }
    }
}

impl<'a> Relation<'a> {
    /// Rearranges self to make `subject` the value of self.left.
    /// If this is not possible, None is returned.
    ///
    /// This method makes the following assumptions:
    /// - `subject` only occurs exactly once in self.left.
    ///    This can be achieved by using `self.left = self.left.single_x(subject)?`
    /// - `subject` does not occur in self.right
    pub fn rearrange_unsafe(&self, subject: &Expr<'a>) -> Relation<'a> {
        use Expr::{Neg, Prod, Recip, Sum};

        // We are done if self.left = subject
        if self.left.simplify_eq(subject) {
            return self.clone();
        }

        match &self.left {
            Sum(terms) => {
                // subject should occur only in 1 term of the sum by the assumptions.
                // x_idx will be the index of the term containing `subject`.
                let x_idx = terms
                    .iter()
                    .position(|term| term.contains(subject))
                    .unwrap();

                // We're going to rearrange the relation to contain just the subjects term on the
                // left, and subtract the remaining terms from the right.
                let new_left = terms[x_idx].clone();

                let mut other_terms = Vec::with_capacity(terms.len() - 1);
                other_terms.extend_from_slice(&terms[..x_idx]);
                other_terms.extend_from_slice(&terms[x_idx + 1..]);

                let new_right = Sum(vec![self.right.clone(), Neg(Box::new(Sum(other_terms)))]);

                Relation {
                    left: new_left,
                    relation: self.relation,
                    right: new_right,
                }
                .rearrange_unsafe(subject)
            }
            Prod(terms) => {
                // Also by assumption, `subject` will occur only in 1 term.
                // x_idx will be the index of the term containing `subject`.
                let x_idx = terms
                    .iter()
                    .position(|term| term.contains(subject))
                    .unwrap();

                // Like sum, we will rearrange the relation to contain just `subject`s term on the
                // left and divide through by the remaining terms.
                let new_left = terms[x_idx].clone();

                let mut other_terms = Vec::with_capacity(terms.len() - 1);
                other_terms.extend_from_slice(&terms[..x_idx]);
                other_terms.extend_from_slice(&terms[x_idx + 1..]);

                let new_right = Prod(vec![
                    self.right.clone(),
                    Recip(Box::new(Sum(other_terms)), {
                        // TODO Decide and document rounding directions
                        match self.relation {
                            RelationKind::Le => true,
                            RelationKind::Ge => false,
                        }
                    }),
                ]);

                Relation {
                    left: new_left,
                    relation: self.relation,
                    right: new_right,
                }
                .rearrange_unsafe(subject)
            }

            // Negate both sides to unwrap the Neg
            Neg(term) => Relation {
                left: *term.clone(),
                relation: self.relation.opposite(),
                right: Neg(Box::new(self.right.clone())),
            }
            .rearrange_unsafe(subject),

            // Recip both sides to unwrap this Recip
            Recip(term, rounding) => Relation {
                left: *term.clone(),
                relation: self.relation.opposite(),
                right: Recip(Box::new(self.right.clone()), todo!()),
            }
            .rearrange_unsafe(subject),

            // If we are left with an atom that is not subject, then something has gone wrong.
            // Very wrong, actually.
            Expr::Atom(_) => panic!("rearrange was left with atom != subject"),
        }
    }

    /// Returns the bounds on `target` given by self.
    /// This method makes the same assumptions as `rearrange_unsafe`
    pub fn bounds_on_unsafe(&self, target: &Expr<'a>) -> Bound<'a> {
        use RelationKind::{Ge, Le};
        match self.rearrange_unsafe(target) {
            Relation {
                left: _,
                relation: Le,
                right,
            } => Bound::Le(right),
            Relation {
                left: _,
                relation: Ge,
                right,
            } => Bound::Ge(right),
        }
    }
}

///////////////////////////////////////////////////////////////////////////////
////////                      Display Implementations                  ////////
///////////////////////////////////////////////////////////////////////////////

impl<'a> fmt::Display for Relation<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, self.relation, self.right)
    }
}

impl fmt::Display for RelationKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}",
            match self {
                RelationKind::Ge => ">=",
                RelationKind::Le => "<=",
            }
        )
    }
}

impl<'a> fmt::Display for Bound<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let (sign, expr) = match self {
            Bound::Le(expr) => ("<=", expr),
            Bound::Ge(expr) => (">=", expr),
        };
        write!(f, "{} {}", sign, expr)
    }
}
