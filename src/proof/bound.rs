use super::expr::{minus_one, one, zero, Atom, Expr};
use super::sign::Sign;
use super::PrettyFormat;
use crate::ast::Ident;
use std::fmt::{self, Display, Formatter};

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
/// Contain references to a bound and a specfic variable that the bound applies to.
/// For example `x <= 2` or `a >= x+y`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DescriptiveBound<'a, 'b> {
    pub subject: &'b Ident<'a>,
    pub bound: &'b Bound<'a>,
}

/// Represents a relation between 2 expressions.
/// For example: left <= (RelationKind::Le) right
///
/// This can be used to rearrange various relations to get particular bounds.
#[derive(Debug, Clone)]
pub struct Relation<'a> {
    pub left: Expr<'a>,
    pub kind: RelationKind,
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
    /// Returns the bound on `subject` given by `0 <= expr_ge0`
    /// This uses the `named_sign` callback to determine possible signs for named variables.
    pub fn from_ge0(
        expr_ge0: &Expr<'a>,
        subject: &Ident<'a>,
        named_sign: impl Fn(&Ident<'a>) -> Sign + Copy,
    ) -> Option<Bound<'a>> {
        Relation {
            left: expr_ge0.single_x(subject)?,
            kind: RelationKind::Ge,
            right: zero(),
        }
        .bounds_on_unsafe(subject, named_sign)
    }

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
    pub fn rearrange_unsafe(
        &self,
        subject: &Ident<'a>,
        named_sign: impl Fn(&Ident<'a>) -> Sign + Copy,
    ) -> Option<Relation<'a>> {
        use Expr::{Neg, Prod, Recip, Sum};

        // We are done if self.left = subject
        if let Expr::Atom(Atom::Named(ref x)) = self.left {
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
                    kind: self.kind,
                    right: new_right,
                }
                .rearrange_unsafe(subject, named_sign)
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
                let other_terms = Prod(other_terms);
                // We're going to divide by other_terms so we must check it's sign.
                // If it's negative, we should flip the relation.
                let new_kind = match other_terms.sign(named_sign) {
                    Sign::POSITIVE => self.kind,
                    Sign::NEGATIVE => self.kind.opposite(),
                    // We can't divide by 0!
                    Sign::ZERO => {
                        #[cfg(debug_assertions)]
                        println!("Dropping {} since it is 0.", other_terms);

                        return None;
                    }
                    // We can't determine the sign so we can't safely divide by it.
                    _ => {
                        #[cfg(debug_assertions)]
                        println!("Dropping {} since sign is unknown.", other_terms);

                        return None;
                    }
                };

                let new_right = Prod(vec![
                    self.right.clone(),
                    Recip(Box::new(other_terms), {
                        // TODO Decide and document rounding directions
                        match new_kind {
                            RelationKind::Le => true,
                            RelationKind::Ge => false,
                        }
                    }),
                ]);

                Relation {
                    left: new_left,
                    kind: new_kind,
                    right: new_right,
                }
                .rearrange_unsafe(subject, named_sign)
            }

            // Negate both sides to unwrap the Neg
            Neg(term) => Relation {
                left: (**term).clone(),
                kind: self.kind.opposite(),
                right: Neg(Box::new(self.right.clone())),
            }
            .rearrange_unsafe(subject, named_sign),

            // Recip both sides to unwrap this Recip
            Recip(term, _rounding) => Relation {
                left: (**term).clone(),
                kind: self.kind.opposite(),
                // When you implement this todo, make sure you check the sign!
                // See Prod case for how it should be done.
                right: Recip(Box::new(self.right.clone()), todo!()),
            }
            .rearrange_unsafe(subject, named_sign),

            // If we are left with an atom that is not subject, then something has gone wrong.
            // Very wrong, actually.
            Expr::Atom(_) => panic!("rearrange was left with atom != subject"),
        }
    }

    /// Returns the bounds on `target` given by self.
    /// This method makes the same assumptions as `rearrange_unsafe`
    pub fn bounds_on_unsafe(
        &self,
        target: &Ident<'a>,
        named_sign: impl Fn(&Ident<'a>) -> Sign + Copy,
    ) -> Option<Bound<'a>> {
        use RelationKind::{Ge, Le};
        Some(match self.rearrange_unsafe(target, named_sign)? {
            Relation {
                left: _,
                kind: Le,
                right,
            } => Bound::Le(right),
            Relation {
                left: _,
                kind: Ge,
                right,
            } => Bound::Ge(right),
        })
    }

    /// Returns the bound on `name` given by self if it exists and can be computed.
    pub fn bounds_on(
        &self,
        name: &Ident<'a>,
        named_sign: impl Fn(&Ident<'a>) -> Sign + Copy,
    ) -> Option<Bound<'a>> {
        // These will form the Relation that we will solve.
        // This must end up satisfying the preconditions on bounds_on_unsafe.
        let lhs;
        let kind;
        let rhs: Expr<'a>;

        let left_contains = self.left.variables().contains(&name);
        let right_contains = self.right.variables().contains(&name);

        if left_contains && right_contains {
            lhs = Expr::Sum(vec![
                self.left.clone(),
                Expr::Neg(Box::new(self.right.clone())),
            ])
            .simplify()
            .single_x(name)?;
            kind = self.kind;
            rhs = zero();
        } else if left_contains && !right_contains {
            lhs = self.left.simplify().single_x(name)?;
            kind = self.kind;
            rhs = self.right.clone();
        } else if !left_contains && right_contains {
            lhs = self.right.simplify().single_x(name)?;
            kind = self.kind.opposite();
            rhs = self.left.clone();
        } else {
            return None;
        }

        Relation {
            left: lhs,
            kind,
            right: rhs,
        }
        .bounds_on_unsafe(name, named_sign)
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
        let to_add = match self.kind {
            RelationKind::Le => minus_one(),
            RelationKind::Ge => one(),
        };
        Relation {
            left: Expr::Sum(vec![self.left.clone(), to_add]),
            kind: self.kind.opposite(),
            right: self.right.clone(),
        }
    }

    /// Returns Relation but with the left and right expressions simplified.
    pub fn simplify(&self) -> Relation<'a> {
        Relation {
            left: self.left.simplify(),
            kind: self.kind,
            right: self.right.simplify(),
        }
    }

    /// Substitute `x` with `with` in self and return the result.
    pub fn substitute(&self, x: &Ident<'a>, with: &Expr<'a>) -> Relation<'a> {
        Relation {
            left: self.left.substitute(x, with),
            kind: self.kind,
            right: self.right.substitute(x, with),
        }
    }

    /// Perform an atomic substitution of a group, replacing each occurence of the identifiers with
    /// the paired expression.
    pub fn substitute_all(&self, subs: &[(&Ident<'a>, &Expr<'a>)]) -> Relation<'a> {
        Relation {
            left: self.left.substitute_all(subs),
            kind: self.kind,
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

    /// Returns an expression that is >= 0 if and only if self is true.
    pub fn ge0(&self) -> Expr<'a> {
        match self.kind {
            // left <= right
            // ==> 0 <= right-left
            RelationKind::Le => Expr::Sum(vec![
                self.right.clone(),
                Expr::Neg(Box::new(self.left.clone())),
            ]),
            // left >= right
            // ==> left-right >= 0
            RelationKind::Ge => Expr::Sum(vec![
                self.left.clone(),
                Expr::Neg(Box::new(self.right.clone())),
            ]),
        }
    }
}

///////////////////////////////////////////////////////////////////////////////
////////                      Display Implementations                  ////////
///////////////////////////////////////////////////////////////////////////////

impl<'a> Display for Relation<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{} {} {}", self.left, self.kind, self.right)
    }
}

impl<'a> PrettyFormat<()> for Relation<'a> {
    fn pretty_format(&self, f: &mut Formatter, file_str: &str, _aux: &()) -> fmt::Result {
        let in_prod = false;

        write!(
            f,
            "{} {} {}",
            self.left.pretty(file_str, in_prod),
            self.kind,
            self.right.pretty(file_str, in_prod)
        )
    }
}

impl Display for RelationKind {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
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

impl<'a> Display for Bound<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let (sign, expr) = match self {
            Bound::Le(expr) => ("<=", expr),
            Bound::Ge(expr) => (">=", expr),
        };
        write!(f, "{} {}", sign, expr)
    }
}

impl<'a, 'b> Display for DescriptiveBound<'a, 'b> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{} {}", self.subject, self.bound)
    }
}
