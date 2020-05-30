//! Verification for proof statments
//!
//! The high-level operations here are on functions and the global scope, taking the AST as input.
//! It is assumed here that the AST nodes given as input have passed through the checks in `verify`
//! without error.

pub mod error;
pub mod examples;
mod expr;
mod int;
mod optimiser;
use self::error::Error;
use self::expr::{Atom, Expr, ONE, ZERO};
use self::int::Int;
use crate::ast::{self, Ident};
use std::fmt;

/// Attempts to prove that the entire contents of the program is within the bounds specified by the
/// proof rules.
fn validate<'a>(top_level_items: &'a [ast::Item<'a>]) -> Vec<Error<'a>> {
    todo!()
}

// !!!!! Requirements have had very little work. These data structures are likely to change and not
// !!!!! yet documented.
// !!!!! Please scroll down to Expr

/*
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Requirement<'a> {
    or: Vec<RequirementTerm<'a>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct RequirementTerm<'a> {
    and: Vec<Condition<'a>>,
}
*/

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum LogicExpr<'a> {
    Or(Vec<LogicExpr<'a>>),
    And(Vec<LogicExpr<'a>>),
    Not(Box<LogicExpr<'a>>),
    Condition(Condition<'a>),
}

impl<'a> LogicExpr<'a> {
    /*fn andify(&self) -> Requirement<'a> {
        use Requirement::{Or, And, Not, Condition, contra_positive};
        match self {
            Or(terms) => Not(Box::new(And(terms.iter().map(contra_positive).collect()))),
        }
    }

    fn contra_positive(&self) -> Requirement<'a> {
        use Requirement::{Or, And, Not, Condition, contra_positive};
        match self {
            Or(terms) => And(terms.iter().map(contra_positive).collect()),
            And(terms) => And(terms.iter().map(contra_positive).collect()),
        }
    }*/
    /*
    fn or_with(&mut self, req: Requirement<'a>) {
        self.or.extend(req.or);
    }
    fn and(&mut self, req: Requirement<'a>) -> Requirement<'a> {
        // let s = self
        // let r = req
        // s && ( r[0] || r[1] || r[2] || ...)
        // s && r[0] || s && r[1] || s && r[2] || ...
        let mut out = Requirement {
            or: Vec::with_capacity(self.or.len() * req.or.len()),
        };
        for term in req.or.iter() {
            out.or_with(self.and_term(term.clone()));
        }
        out
    }
    fn and_with_term(&mut self, term: RequirementTerm<'a>) {
        self.or
            .iter_mut()
            .for_each(|self_term| self_term.and_with(term.clone()));
    }
    fn and_term(&self, term: RequirementTerm<'a>) -> Requirement<'a> {
        let mut out = self.clone();
        out.and_with_term(term);
        out
    }
    */
}

/*
impl<'a> RequirementTerm<'a> {
    fn and_with(&mut self, term: RequirementTerm<'a>) {
        self.and.extend(term.and);
    }
    fn and_with_condition(&mut self, cond: Condition<'a>) {
        self.and.push(cond);
    }
}
*/

/// A Condition is a boolean condition.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Condition<'a> {
    /// True iff the expression evaluates to a non-negative value
    Ge0(Expr<'a>),
    /// Always true
    True,
    /// Always false
    False,
}

/// This will (maybe) be used later
#[derive(Debug, Clone)]
pub enum Bound<'a> {
    Le(Expr<'a>),
    Ge(Expr<'a>),
}

/// Represents a relation between 2 expressions.
/// For example: left <= (RelationKind::Le) right
#[derive(Debug, Clone)]
pub struct Relation<'a> {
    left: Expr<'a>,
    relation: RelationKind,
    right: Expr<'a>,
}

/// A kind of a Relation
#[derive(Debug, Clone, Copy)]
pub enum RelationKind {
    /// Less than or equal to (<=)
    Le,
    /// Greater than or equal to (>=)
    Ge,
}

impl<'a> Condition<'a> {
    /// Takes another condition and tries to combine it with self.
    /// If a single condition combination exists - i.e. self && other can be written as a single
    /// Condition, it is returned wrapped in a Some; otherwise, None is returned.
    fn and(&self, other: &Condition<'a>) -> Option<Condition<'a>> {
        use Condition::{False, Ge0, True};
        match self {
            False => Some(Condition::False),
            True => Some(other.clone()),
            Ge0(_) => todo!(),
        }
    }

    /// Returns a Condition which is true iff self is false.
    fn contra_positive(&self) -> Condition<'a> {
        use Condition::{False, Ge0, True};
        match self {
            True => False,
            False => True,
            //  ¬(0 <= expr)
            // => 0 > -expr
            // => 0 >= -expr -1
            Ge0(expr) => Ge0(Expr::Sum(vec![
                Expr::Neg(Box::new(expr.clone())),
                Expr::Neg(Box::new(ONE)),
            ])),
        }
    }

    fn bounds_on(&self, name: &Ident<'a>) -> Option<Bound<'a>> {
        use Condition::{False, Ge0, True};
        let name_expr = Expr::Atom(Atom::Named(*name));
        match self {
            True | False => None,
            Ge0(expr) => Relation {
                left: expr.single_x(&name_expr)?,
                relation: RelationKind::Ge,
                right: ZERO,
            }
            .bounds_on_unsafe(&name_expr),
        }
    }

    fn bounds(&'a self) -> Vec<(Ident<'a>, Bound<'a>)> {
        use Condition::{False, Ge0, True};
        match self {
            True | False => Vec::new(),
            Ge0(expr) => expr
                .variables()
                .iter()
                .filter_map(|x| self.bounds_on(x).map(|bounds| (*x, bounds)))
                .collect(),
        }
    }
}

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

impl<'a> Bound<'a> {
    /// Apply f to the bound expression
    fn map(&self, f: impl Fn(&Expr<'a>) -> Expr<'a>) -> Bound<'a> {
        use Bound::{Ge, Le};
        match self {
            Ge(expr) => Ge(f(expr)),
            Le(expr) => Le(f(expr)),
        }
    }

    /// Call Expr::simplify on the bound expression
    fn simplify(&self) -> Bound<'a> {
        self.map(Expr::simplify)
    }
}

impl RelationKind {
    /// Returns the opposite kind - note that this IS NOT the contra-positive, but what you would
    /// change the relation to if you multiplied both sides by -1 or took their reciprocals.
    fn opposite(self) -> RelationKind {
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
    fn rearrange_unsafe(&self, subject: &Expr<'a>) -> Option<Relation<'a>> {
        use Expr::{Neg, Prod, Recip, Sum};

        // We are done if self.left = subject
        if self.left.simplify_eq(subject) {
            return Some(self.clone());
        }

        match &self.left {
            Sum(terms) => {
                let x_idx = terms
                    .iter()
                    .position(|term| term.contains(subject))
                    .unwrap();

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
                let x_idx = terms
                    .iter()
                    .position(|term| term.contains(subject))
                    .unwrap();

                let new_left = terms[x_idx].clone();

                let mut other_terms = Vec::with_capacity(terms.len() - 1);
                other_terms.extend_from_slice(&terms[..x_idx]);
                other_terms.extend_from_slice(&terms[x_idx + 1..]);
                let new_right = Prod(vec![self.right.clone(), Recip(Box::new(Sum(other_terms)))]);

                Relation {
                    left: new_left,
                    relation: self.relation,
                    right: new_right,
                }
                .rearrange_unsafe(subject)
            }

            Neg(term) => Relation {
                left: *term.clone(),
                relation: self.relation.opposite(),
                right: Neg(Box::new(self.right.clone())),
            }
            .rearrange_unsafe(subject),

            Recip(term) => Relation {
                left: *term.clone(),
                relation: self.relation.opposite(),
                right: Recip(Box::new(self.right.clone())),
            }
            .rearrange_unsafe(subject),

            Expr::Atom(_) => todo!(),
        }
    }

    fn bounds_on_unsafe(&self, target: &Expr<'a>) -> Option<Bound<'a>> {
        use RelationKind::{Ge, Le};
        match self.rearrange_unsafe(target)? {
            Relation {
                left: _,
                relation: Le,
                right,
            } => Some(Bound::Le(right)),
            Relation {
                left: _,
                relation: Ge,
                right,
            } => Some(Bound::Ge(right)),
        }
    }
}

impl<'a> From<ast::proof::Condition<'a>> for Condition<'a> {
    fn from(pc: ast::proof::Condition<'a>) -> Condition<'a> {
        todo!()
    }
}
