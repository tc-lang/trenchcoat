use super::expr::{Atom, Expr, MINUS_ONE, ONE, ZERO};
use super::optimiser::bound_sub;
use crate::ast::Ident;
use std::fmt;

/// Represents a bound on something.
/// For example `<= 2` or `>= x+y`
#[derive(Debug, Clone, PartialEq)]
pub enum Bound<'a> {
    /// The thing must be <= expr
    Le(Expr<'a>),
    /// The thing must be >= expr
    Ge(Expr<'a>),
}

/// Represents a bound on a named variables.
/// Contains a bound and a specfic variable that the bound applies to.
/// For example `x <= 2` or `a >= x+y`
#[derive(Debug, Clone, PartialEq)]
pub struct DescriptiveBound<'a> {
    pub subject: Ident<'a>,
    pub bound: Bound<'a>,
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

    /// Call Expr::simplify on the bound expression and return the new bound
    pub fn simplify(&self) -> Bound<'a> {
        self.map(Expr::simplify)
    }

    /// Return the RelationKind if the bound expression was on the RHS of a relation.
    pub fn relation_kind(&self) -> RelationKind {
        match self {
            Bound::Le(_) => RelationKind::Le,
            Bound::Ge(_) => RelationKind::Ge,
        }
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
    pub fn rearrange_unsafe(&self, subject: Ident<'a>) -> Option<Relation<'a>> {
        use Expr::{Neg, Prod, Recip, Sum};

        // We are done if self.left = subject
        if let Expr::Atom(Atom::Named(x)) = self.left {
            if x == subject {
                return Some(self.clone());
            }
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
                let other_terms = Sum(other_terms);
                // We're going to divide by other_terms so we must check it's sign.
                // If it's negative, we should flip the relation.
                let new_relation = match other_terms.sign() {
                    Some(1) => self.relation,
                    Some(-1) => self.relation.opposite(),

                    // We can't determine the sign so we can't safely divide by it.
                    None => {
                        #[cfg(debug_assertions)]
                        println!("Dropping {} since sign is unknown.", other_terms);

                        return None;
                    }
                    // We can't divide by 0!
                    Some(0) => {
                        #[cfg(debug_assertions)]
                        println!("Dropping {} since it is 0.", other_terms);

                        return None;
                    }

                    Some(_) => panic!("invalid sign"),
                };

                let new_right = Prod(vec![
                    self.right.clone(),
                    Recip(Box::new(other_terms), {
                        // TODO Decide and document rounding directions
                        match new_relation {
                            RelationKind::Le => true,
                            RelationKind::Ge => false,
                        }
                    }),
                ]);

                Relation {
                    left: new_left,
                    relation: new_relation,
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
            Recip(term, _rounding) => Relation {
                left: *term.clone(),
                relation: self.relation.opposite(),
                // When you implement this todo, make sure you check the sign!
                // See Prod case for how it should be done.
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
    pub fn bounds_on_unsafe(&self, target: Ident<'a>) -> Option<Bound<'a>> {
        use RelationKind::{Ge, Le};
        Some(match self.rearrange_unsafe(target)? {
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
        })
    }

    /// Returns the bound on `name` given by self if it exists and can be computed.
    pub fn bounds_on(&self, name: Ident<'a>) -> Option<Bound<'a>> {
        // These will form the Relation that we will solve.
        // This must end up satisfying the preconditions on bounds_on_unsafe.
        let lhs;
        let relation;
        let rhs;

        let left_contains = self.left.variables().contains(&name);
        let right_contains = self.right.variables().contains(&name);

        if left_contains && right_contains {
            lhs = Expr::Sum(vec![
                self.left.clone(),
                Expr::Neg(Box::new(self.right.clone())),
            ])
            .simplify()
            .single_x(name)?;
            relation = self.relation;
            rhs = ZERO;
        } else if left_contains && !right_contains {
            lhs = self.left.simplify().single_x(name)?;
            relation = self.relation;
            rhs = self.right.clone();
        } else if !left_contains && right_contains {
            lhs = self.right.simplify().single_x(name)?;
            relation = self.relation.opposite();
            rhs = self.left.clone();
        } else {
            return None;
        }

        Relation {
            left: lhs,
            relation,
            right: rhs,
        }
        .bounds_on_unsafe(name)
    }

    /// Returns a list of all the bounds that can be computed from self.
    pub fn bounds(&self) -> Vec<DescriptiveBound<'a>> {
        self.variables()
            .iter()
            .filter_map(|x| {
                Some(DescriptiveBound {
                    subject: *x,
                    bound: self.bounds_on(*x)?,
                })
            })
            .collect()
    }

    /// Returns a Relation which is true iff self is false.
    pub fn contra_positive(&self) -> Relation<'a> {
        //   ¬(lhs <= rhs)
        // ==> lhs > rhs
        // ==> lhs-1 >= rhs
        //
        //   ¬(lhs >= rhs)
        // ==> lhs < rhs
        // ==> lhs+1 <= rhs
        let to_add = match self.relation {
            RelationKind::Le => MINUS_ONE,
            RelationKind::Ge => ONE,
        };
        Relation {
            left: Expr::Sum(vec![self.left.clone(), to_add]),
            relation: self.relation.opposite(),
            right: self.right.clone(),
        }
    }

    /// Returns Relation but with the left and right expressions simplified.
    pub fn simplify(&self) -> Relation<'a> {
        Relation {
            left: self.left.simplify(),
            relation: self.relation,
            right: self.right.simplify(),
        }
    }

    /// Substitute `x` with `with` in self and return the result.
    pub fn substitute(&self, x: Ident<'a>, with: &Expr<'a>) -> Relation<'a> {
        Relation {
            left: self.left.substitute(x, with),
            relation: self.relation,
            right: self.right.substitute(x, with),
        }
    }

    /// Perform an atomic substitution of a group, replacing each occurence of the identifiers with
    /// the paired expression.
    pub fn substitute_all(&self, subs: &[(Ident<'a>, &Expr<'a>)]) -> Relation<'a> {
        Relation {
            left: self.left.substitute_all(subs),
            relation: self.relation,
            right: self.right.substitute_all(subs),
        }
    }

    /// Returns a vector of the distinct variables this Relation contains.
    pub fn variables(&self) -> Vec<Ident<'a>> {
        let mut vars = self.left.variables();
        vars.extend(self.right.variables());
        vars.sort_unstable();
        vars.dedup();
        vars
    }
}

impl<'a> DescriptiveBound<'a> {
    /// Returns true iff the order that self and other are substituted does not matter.
    /// This is currently if they don't have the same subject or don't have the same relation kind.
    pub fn permutes_with(&self, other: &DescriptiveBound<'a>) -> bool {
        self.subject != other.subject || self.bound.relation_kind() != other.bound.relation_kind()
    }

    /// Simplifies the bound expression and returns the result.
    pub fn simplify(&self) -> DescriptiveBound<'a> {
        DescriptiveBound {
            subject: self.subject,
            bound: self.bound.simplify(),
        }
    }

    /// Try substituting sub in to self and return the result.
    pub fn sub(&self, sub: &DescriptiveBound<'a>) -> Option<DescriptiveBound<'a>> {
        bound_sub(self, &sub)
    }
}

pub fn bounds_on_ge0<'a>(expr_ge0: Expr<'a>, subject: Ident<'a>) -> Option<Bound<'a>> {
    Relation{
        left: expr_ge0.single_x(subject)?,
        relation: RelationKind::Ge,
        right: ZERO,
    }.bounds_on_unsafe(subject)
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

impl<'a> fmt::Display for DescriptiveBound<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{} {}", self.subject, self.bound)
    }
}
