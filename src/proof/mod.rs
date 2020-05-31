//! Verification for proof statments
//!
//! The high-level operations here are on functions and the global scope, taking the AST as input.
//! It is assumed here that the AST nodes given as input have passed through the checks in `verify`
//! without error.

mod bound;
pub mod error;
pub mod examples;
mod expr;
mod int;
mod optimiser;
use self::bound::{Bound, Relation, RelationKind};
use self::error::Error;
use self::expr::{Atom, Expr, ONE, ZERO};
use crate::ast::{self, Ident};

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

/*
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
            Ge0(expr) => Some(
                Relation {
                    left: expr.single_x(&name_expr)?,
                    relation: RelationKind::Ge,
                    right: ZERO,
                }
                .bounds_on_unsafe(&name_expr),
            ),
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

impl<'a> From<ast::proof::Condition<'a>> for Condition<'a> {
    fn from(pc: ast::proof::Condition<'a>) -> Condition<'a> {
        todo!()
    }
}
