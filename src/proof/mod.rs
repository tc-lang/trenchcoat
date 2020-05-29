//! Verification for proof statments
//!
//! The high-level operations here are on functions and the global scope, taking the AST as input.
//! It is assumed here that the AST nodes given as input have passed through the checks in `verify`
//! without error.

mod error;
mod int;
use self::error::Error;
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
enum Condition<'a> {
    /// True iff the expression evaluates to a non-negative value
    Ge0(Expr<'a>),
    /// Always true
    True,
    /// Always false
    False,
}

/// This will (maybe) be used later
#[derive(Debug, Clone)]
enum Bound<'a> {
    Le(Expr<'a>),
    Ge(Expr<'a>),
}

/// Represents a relation between 2 expressions.
/// For example: left <= (RelationKind::Le) right
#[derive(Debug, Clone)]
struct Relation<'a> {
    left: Expr<'a>,
    relation: RelationKind,
    right: Expr<'a>,
}

/// A kind of a Relation
#[derive(Debug, Clone, Copy)]
enum RelationKind {
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

/// An expression
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Expr<'a> {
    // NOTE The order of these variants matters for simplification.
    // Requirements of order:
    // - Neg is first
    // - Recip is second
    // - Prod is last
    // - Atom is before Prod
    // - This leaves only 1 place for Sum
    /// -e
    Neg(Box<Expr<'a>>),

    /// 1/e
    Recip(Box<Expr<'a>>),

    /// e[0] + e[1] + ...
    Sum(Vec<Expr<'a>>),

    Atom(Atom<'a>),

    /// e[0] * e[1] * ...
    Prod(Vec<Expr<'a>>),
}

/// An expression with the literal value 0
const ZERO: Expr = Expr::Atom(Atom::Literal(Int::ZERO));
/// An expression with the literal value 1
const ONE: Expr = Expr::Atom(Atom::Literal(Int::ONE));

impl<'a> fmt::Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use Expr::{Atom, Neg, Prod, Recip, Sum};
        match self {
            Atom(atom) => write!(f, "{}", atom),
            Neg(expr) => write!(f, "-({})", *expr),
            Recip(expr) => write!(f, "1/({})", *expr),
            Sum(terms) => write!(
                f,
                "{}",
                terms
                    .iter()
                    .map(|term| format!("{}", term))
                    .collect::<Vec<String>>()
                    .join(" + ")
            ),
            Prod(terms) => write!(
                f,
                "{}",
                terms
                    .iter()
                    .map(|term| format!("({})", term))
                    .collect::<Vec<String>>()
                    .join(" * ")
            ),
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

impl<'b, 'a: 'b> Expr<'a> {
    /// Returns true if the expressions are equal or if their simplified values are equal.
    /// This is a more reliable equals method since, in the standard implementation of ==,
    /// x + 2 != 2 + x whereas it would be equal with this definition.
    ///
    /// This is however much more expensive to compute since if 2 expressions aren't equal, they
    /// are always simplified.
    fn simplify_eq(&self, other: &Expr<'a>) -> bool {
        self.eq(other) || self.simplify() == other.simplify()
    }

    /// Returns a simplified version of self.
    /// The simplification rules have not yet been fully decided.
    /// Stable rules will be documented here with other rules documented in the code.
    ///
    /// - Sums and Products are flattened. (i.e.) x*(y*z) becomes x*y*z
    /// - Products do not directly contain Neg terms. Instead, they are lifted to enclose the
    ///   product.
    /// - Neg is distributed in sums. i.e. Neg(x+y+z) = Neg(x) + Neg(y) + Neg(z)
    /// - Recip is distributed in products. i.e. Recip(x*y*z) = Recip(x) * Recip(y) * Recip(z)
    /// - Neg(Neg(x)) becomes x
    /// - Recip(Recip(x)) becomes x
    /// - 0s are removed from sums.
    /// - 1s are removed from products.
    /// - Terms in sums and products are sorted.
    fn simplify(&self) -> Expr<'a> {
        use Expr::{Neg, Prod, Recip, Sum};
        match self {
            // Named atoms can't be simplified
            Expr::Atom(Atom::Named(_)) => self.clone(),

            // Convert negative literals in to Neg(<positive literal>)
            Expr::Atom(Atom::Literal(x)) => {
                if *x < Int::ZERO {
                    Neg(Box::new(Expr::Atom(Atom::Literal(-*x))))
                } else {
                    self.clone()
                }
            }

            Neg(expr) => match expr.simplify() {
                // -0 = 0
                ZERO => ZERO,
                Expr::Atom(_) => self.clone(),

                // -(-x) = x
                Neg(inner_expr) => *inner_expr,

                // -(a + b + c + ...) = (-a) + (-b) + (-c) + ...
                Sum(terms) => Sum(terms
                    .iter()
                    .map(|term| Neg(Box::new(term.clone())))
                    .collect())
                .simplify(),
                // TODO This calls simplify on the newly created sum to simplify new cases of
                // Neg(...), for example Neg(Neg(x)) = x.
                // Just calling simplify will also try to simplify the other, already simplified
                // terms though. This is inefficient but ok for now.
                new_expr => Neg(Box::new(new_expr)),
            },

            Sum(terms) => {
                let mut new_terms = terms
                    .iter()
                    // Simplify the terms
                    .map(|term| term.simplify())
                    // Remove 0s from the sum
                    .filter(|term| *term != ZERO)
                    // Flatten
                    .flat_map(|term| match term {
                        Sum(terms) => terms,
                        _ => vec![term],
                    })
                    .collect::<Vec<Expr>>();

                let re_simplify = Self::simplify_terms(Self::add_simplify, &mut new_terms);

                // Unwrap the sum if possible
                let res = match new_terms.len() {
                    0 => ZERO,                 // empty sum = 0
                    1 => new_terms[0].clone(), // a sum of just x = x
                    _ => Sum(new_terms),
                };

                if re_simplify {
                    res.simplify()
                } else {
                    res
                }
            }

            Prod(terms) => {
                let mut negatives = 0;

                let mut new_terms = terms
                    .iter()
                    // Simplify each term
                    .map(|term| term.simplify())
                    // Change all Negs in to just their positive terms and count the number of
                    // negatives. This will be used later to wrap the whole product in a Neg
                    // if there were an odd number.
                    //
                    // Note that the simplification above converts all negative literals in to
                    // Neg(Literal(<positive number>)) and removes Neg(Neg(...)) patterns.
                    .map(|term| {
                        if let Neg(inner_expr) = term {
                            negatives += 1;
                            *inner_expr
                        } else {
                            term
                        }
                    })
                    // Remove 1s from the product
                    .filter(|term| *term != ONE)
                    // Flatten
                    .flat_map(|term| match term {
                        Prod(terms) => terms,
                        _ => vec![term],
                    })
                    .collect::<Vec<Expr>>();

                // Now, we are going to multiply out products of sums.
                // To start, we'll find a sum.
                match new_terms.iter().position(|term| match term {
                    Sum(_) => true,
                    _ => false,
                }) {
                    // If there wasn't a sum then there's nothing to do.
                    None => (),
                    Some(sum_idx) => {
                        // Otherwise, we will remove the sum from new_terms and store the sums
                        // terms in sum_terms.
                        let sum_terms = match new_terms.remove(sum_idx) {
                            Sum(terms) => terms,
                            _ => panic!("sum is no longer sum"),
                        };
                        // Now, we multiply each term in the sum by the terms left over from the
                        // product!
                        let new_sum = sum_terms
                            .iter()
                            .map(|term| {
                                // Clone the terms to multiply with
                                let mut these_terms = new_terms.clone();
                                // Multiply with the current term in the sum
                                these_terms.push(term.clone());
                                // Produce the expression
                                if negatives % 2 == 1 {
                                    // Wrap the output in Neg if there were an odd number of
                                    // negative terms.
                                    Neg(Box::new(Prod(these_terms)))
                                } else {
                                    Prod(these_terms)
                                }
                            })
                            .collect();
                        // Simplify the resulting sum
                        return Sum(new_sum).simplify();
                    }
                }

                let re_simplify = Self::simplify_terms(Self::mul_simplify, &mut new_terms);

                // Unwrap the product if possible
                let new_expr = match new_terms.len() {
                    0 => ONE,                  // An empty product = 1
                    1 => new_terms[0].clone(), // A product of just x = x
                    _ => {
                        // A product containing a 0 = 0
                        if new_terms.contains(&ZERO) {
                            // We return now since there's no point wrapping 0 in Neg
                            return ZERO;
                        } else {
                            Prod(new_terms)
                        }
                    }
                };

                let res = if negatives % 2 == 1 {
                    // Wrap the output in Neg if there were an odd number of negative terms.
                    // Note that negative terms have all been converted to positive terms.
                    Neg(Box::new(new_expr))
                } else {
                    new_expr
                };

                if re_simplify {
                    res.simplify()
                } else {
                    res
                }
            }

            Recip(expr) => match expr.simplify() {
                // 1/(1/x) = x
                Recip(inner_expr) => *inner_expr,

                // 1/(-x) = -(1/x)
                Neg(inner_expr) => Neg(Box::new(Recip(inner_expr).simplify())),
                // TODO Similar to the TODO in some, calling simplify on the new expression could
                // be optimised. The same applies to the case below too.

                // 1/(a*b*c*...) = 1/a * 1/b * 1/c
                Prod(terms) => Prod(
                    terms
                        .iter()
                        .map(|term| Recip(Box::new(term.clone())).simplify())
                        .collect(),
                ),

                new_expr => Recip(Box::new(new_expr)),
            },
        }
    }

    /// Tries `simplify` on all pairs of terms, modifying `terms` if a simplification can be made.
    ///
    /// `simplify` must be a simplifier. A simplifier is a function that takes a pair of
    /// expressions and tries to combine them in to one.
    /// For example, a simplfier for Sum might combine x and -x to 0.
    /// If a simplifier returns Some(expr), then expr takes the place of both the expressions that
    /// were passed to it (expr is only inserted once, but both expressions passed are removed).
    /// Otherwise, if None is returned, no change is made.
    ///
    /// A simplifier may assume that there are no nested Prod or Sums and that their terms are
    /// sorted.
    ///
    /// This function assumes that there are no nested Prod or Sums (to allow simplifiers to make
    /// the same assumption).
    ///
    /// If a term is changed by a simplifier, `simplify` is tried again on it and all other
    /// (including previous) terms.
    ///
    /// It also sorts the terms to ensure that the simplifiers assumption that the terms
    /// are sorted is true. This sort is unstable.
    ///
    /// The bool returned indicates if simplifications were made.
    fn simplify_terms(
        simplify: impl Fn(&Expr<'a>, &Expr<'a>) -> Option<Expr<'a>>,
        terms: &mut Vec<Expr<'a>>,
    ) -> bool {
        // Ensure the terms are sorted since a simplifier is allowed to asssume that.
        terms.sort_unstable();

        // Track if terms was modified
        let mut modified = false;

        let mut i = 0;
        while i < terms.len() {
            // We have already checked this term with all previous terms, so we start at i+1
            let mut j = i + 1;
            while j < terms.len() {
                // Don't simplify a term with itself (a simplification can cause j == i)
                if i == j {
                    j += 1;
                    continue;
                }

                match simplify(&terms[i], &terms[j]) {
                    Some(new_term) => {
                        modified = true;

                        // Make the simplification
                        terms[i] = new_term;
                        terms.remove(j);
                        // If we removed a term before i, correct the index
                        if j <= i {
                            i -= 1;
                        }
                        // We should now try the new term with all previous terms too.
                        j = 0;

                        // FIXME We need to uphold that the vec is sorted to continue in this loop.
                        // For now, we will just simplify from the begining but this should be
                        // optimised later.
                        Self::simplify_terms(simplify, terms);
                        return true;
                    }

                    // If no simplification was made, advance j
                    None => j += 1,
                }
            }
            i += 1;
        }
        modified
    }

    /// Extracts a literal coefficient from this expression, or defaults to a coefficient of 1.
    /// For example,
    ///   2*x*y would yield (2, x*y),
    ///   5*x*1/y would yield (5, x*1/y),
    ///   x would yield (1, x),
    ///   -(2*x) would yield (-2, x).
    ///
    /// This assumes that the terms in any products in self are sorted and that there are no nested
    /// products - these assumptions can be made in the context of a simplifier.
    fn get_number_and_term(&self) -> (Int, Expr<'a>) {
        use Expr::{Neg, Prod};
        match self {
            // Allow for negative coefficients
            Neg(inner_expr) => {
                let (n, term) = inner_expr.get_number_and_term();
                (-n, term)
            }

            // Since the terms within the product are sorted and a product cannot contain another
            // product (simplifiers are allowed to assume no nested products), the literal will be
            // the last item in the product.
            Prod(terms) => terms
                .last()
                .and_then(|term| match term {
                    Expr::Atom(Atom::Literal(x)) => {
                        // This is x * (expr / x), i.e. x * (expr with x removed from the end)
                        Some((*x, Prod(terms[..terms.len() - 1].to_vec())))
                    }
                    _ => None,
                })
                // By default, it's just 1 * self
                .unwrap_or_else(|| (Int::ONE, self.clone())),

            //Again, the default case.
            _ => (Int::ONE, self.clone()),
        }
    }

    /// A simplifier that collects terms in addition.
    ///
    /// See also: simplify_terms
    fn add_collect(&self, other: &Expr<'a>) -> Option<Expr<'a>> {
        let (n1, expr1) = self.get_number_and_term();
        let (n2, expr2) = other.get_number_and_term();
        if expr1.simplify_eq(&expr2) {
            // (n1+n2) * expr1
            Some(Expr::Prod(vec![Expr::Atom(Atom::Literal(n1 + n2)), expr1]))
        } else {
            None
        }
    }

    /// A simplifier for addition.
    ///
    /// See also: simplify_terms
    fn add_simplify(&self, other: &Expr<'a>) -> Option<Expr<'a>> {
        if let Some(expr) = self.add_collect(other) {
            return Some(expr);
        }

        use Expr::Neg;
        match self {
            Neg(expr) => match &**expr {
                Expr::Atom(Atom::Literal(x)) => match other {
                    // -x + y = y-x for literals
                    Expr::Atom(Atom::Literal(y)) => {
                        let x = *x;
                        let y = *y;

                        let res = y - x;
                        if res < Int::ZERO {
                            // Keep literals positive
                            Some(Neg(Box::new(Expr::Atom(Atom::Literal(-res)))))
                        } else {
                            Some(Expr::Atom(Atom::Literal(res)))
                        }
                    }

                    Neg(other_expr) => match &**other_expr {
                        // -x + -y = -(x+y) for literals
                        Expr::Atom(Atom::Literal(y)) => {
                            Some(Neg(Box::new(Expr::Atom(Atom::Literal(*x + *y)))))
                        }
                        _ => None,
                    },

                    _ => None,
                },

                // -x + x = 0
                expr => {
                    if *other == *expr {
                        Some(ZERO)
                    } else {
                        None
                    }
                }
            },

            Expr::Atom(Atom::Literal(x)) => match other {
                // Calculate x+y for literals
                Expr::Atom(Atom::Literal(y)) => Some(Expr::Atom(Atom::Literal(*x + *y))),
                _ => None,
            },

            _ => None,
        }
    }

    /// A simplifier for multiplication.
    ///
    /// See also: simplify_terms
    fn mul_simplify(&self, other: &Expr<'a>) -> Option<Expr<'a>> {
        use Expr::Recip;
        match self {
            Recip(expr) => match &**expr {
                Expr::Atom(Atom::Literal(x)) => match other {
                    // (1/x) * y = y/x for literals if there's no rounding
                    Expr::Atom(Atom::Literal(y)) => {
                        let x = *x;
                        let y = *y;

                        let res = y / x;
                        // Only simplify if res is exact
                        if res * x == y {
                            Some(Expr::Atom(Atom::Literal(res)))
                        } else {
                            None
                        }
                    }

                    Recip(other_expr) => match &**other_expr {
                        // (1/x) * (1/y) = 1/(x*y) for literals
                        Expr::Atom(Atom::Literal(y)) => {
                            Some(Recip(Box::new(Expr::Atom(Atom::Literal((*x) * (*y))))))
                        }
                        _ => None,
                    },

                    _ => None,
                },

                // (1/x) * x = 1
                // TODO Consider 0s.
                // I think we shouldn't allow a possibly 0 value in a denominator but we must make
                // sure of that.
                expr => {
                    if *other == *expr {
                        Some(ONE)
                    } else {
                        None
                    }
                }
            },

            Expr::Atom(Atom::Literal(x)) => match other {
                // Calculate x*y for literals
                Expr::Atom(Atom::Literal(y)) => Some(Expr::Atom(Atom::Literal((*x) * (*y)))),
                _ => None,
            },

            _ => None,
        }
    }

    /*
    // FIXME Maybe min and max should return rationals?
    fn min_value(&self, bounds_on: &mut impl FnMut(Ident<'a>) -> Bounds<'a>) -> isize {
        use Expr::{Neg, Prod, Recip, Sum};
        match self {
            Sum(terms) => terms.iter().map(|term| term.min_value(bounds_on)).sum(),
            Neg(expr) => -expr.max_value(bounds_on),
            Prod(terms) => terms
                .iter()
                .map(|term| {
                    let min = term.min_value(bounds_on);
                    if min < 0 {
                        panic!("cannot yet handle negative terms")
                    }
                    min
                })
                .product(),
            Recip(expr) => {
                let min = expr.min_value(bounds_on);
                if min < 0 {
                    if min == -1 {
                        return -1;
                    }
                    if min == 0 {
                        panic!("/0");
                    }
                    return 0;
                }
                let max = expr.max_value(bounds_on);
                if max == 1 {
                    return 1;
                }
                if max == 0 {
                    panic!("/0");
                }
                return 0;
            }
            Expr::Atom(Atom::Literal(x)) => *x,
            Expr::Atom(Atom::Named(ident)) => bounds_on(*ident).Ge.min_value(bounds_on),
        }
    }

    fn max_value(&self, bounds_on: &mut impl FnMut(Ident<'a>) -> Bounds<'a>) -> isize {
        use Expr::{Neg, Prod, Recip, Sum};
        match self {
            Sum(terms) => terms.iter().map(|term| term.max_value(bounds_on)).sum(),
            Neg(expr) => -expr.min_value(bounds_on),
            Prod(terms) => terms
                .iter()
                .map(|term| {
                    let min = term.min_value(bounds_on);
                    if min < 0 {
                        panic!("cannot yet handle negative terms")
                    }
                    let max = term.max_value(bounds_on);
                    max
                })
                .product(),
            Recip(expr) => {
                let min = expr.min_value(bounds_on);
                if min < 0 {
                    return 1 / min; // FIXME Round correcly
                }
                let max = expr.max_value(bounds_on);
                return 1 / max;
            }
            Expr::Atom(Atom::Literal(x)) => *x,
            Expr::Atom(Atom::Named(ident)) => bounds_on(*ident).Ge.min_value(bounds_on),
        }
    }
    */

    /// Returns true iff self contains expr or a simplification of.
    fn contains(&self, expr: &Expr<'a>) -> bool {
        use Expr::{Neg, Prod, Recip, Sum};
        if self.simplify_eq(expr) {
            return true;
        }
        match self {
            Sum(terms) | Prod(terms) => terms.iter().find(|term| term.contains(expr)).is_some(),
            Neg(term) | Recip(term) => term.contains(expr),
            Expr::Atom(_) => false, // This will have been checked at the comparison at the start.
        }
    }

    /// Divides self by expr, returning the result.
    /// If it cannot be cleanly devided - i.e. if a term does not contain expr as a factor, None is
    /// returned.
    /// None is also returned if an instance of expr would be left in the resulting expr.
    ///
    /// FIXME This will work perfectly well with Atoms, which I think is all that will be required,
    /// however other expressions will not work as expected. The signature should either be changed
    /// or the behaviour corrected.
    fn factor(&self, expr: &Expr<'a>) -> Option<Expr<'a>> {
        use Expr::{Neg, Prod, Recip, Sum};

        // x/x = 1
        if self.simplify_eq(expr) {
            return Some(ONE);
        }

        match self {
            Sum(terms) => {
                let mut factored_terms = Vec::with_capacity(terms.len());
                // Call factor on each term of the sum, return None if one of the terms cannot be
                // factored.
                for term in terms {
                    factored_terms.push(term.factor(expr)?);
                }
                Some(Sum(factored_terms))
            }

            Prod(terms) => {
                let mut factored_terms = Vec::with_capacity(terms.len());

                // Here, we want to factor expr from the product, so we wish to divide just 1 term
                // by it - the rest should remain unchanged and should not contain expr.
                for idx in 0..terms.len() {
                    let term = &terms[idx];
                    // Try to factor this term.
                    match term.factor(expr) {
                        // If it didn't factor, we leave it as is.
                        None => factored_terms.push(term.clone()),

                        Some(factored) => {
                            // If it did factor, we want the factored term
                            factored_terms.push(factored);

                            // Then we want the remaining terms.
                            let remaining_terms = &terms[idx + 1..];
                            // These terms shouldn't contain expr though.
                            if remaining_terms
                                .iter()
                                .find(|term| term.contains(expr))
                                .is_some()
                            {
                                return None;
                            }
                            factored_terms.extend_from_slice(remaining_terms);

                            // We've been through all the terms.
                            break;
                        }
                    }
                }
                Some(Prod(factored_terms))
            }

            // We can take a factor directly out of a Neg
            Neg(term) => Some(Neg(Box::new(term.factor(expr)?))),

            // We can take the Recip factor out of a Recip
            Recip(term) => Some(Recip(Box::new(
                term.factor(&Recip(Box::new(expr.clone())))?,
            ))),

            // An Atom can't be factored. Note that if expr is this Atom then it would have been
            // handled earlier.
            Expr::Atom(_) => None,
        }
    }

    /// Returns an Expr equivilent to that of Expr, but with only a single occurence of `expr`.
    /// This is done primerily by factorisation.
    /// If expr cannot be rewritten with only a single occurence of `expr` then None is returned.
    fn single_x(&self, expr: &Expr<'a>) -> Option<Expr<'a>> {
        use Expr::{Neg, Prod, Recip, Sum};
        if self.simplify_eq(expr) {
            return Some(expr.clone());
        }
        match self {
            Sum(terms) => {
                let mut x_terms = Vec::new();
                let mut other_terms = Vec::new();
                for term in terms {
                    if term.contains(expr) {
                        x_terms.push(term.clone());
                    } else {
                        other_terms.push(term.clone());
                    }
                }
                if x_terms.len() == 1 {
                    Some(Sum(vec![x_terms[0].single_x(expr)?, Sum(other_terms)]))
                } else {
                    // So self = (x_terms) + (other_terms)
                    // Let's now try to take a factor of x out of x_terms to get
                    //    self = x*(factored_terms) + (other_terms)
                    let factored = Sum(x_terms).factor(expr)?;
                    Some(Sum(vec![
                        Prod(vec![expr.clone(), factored]),
                        Sum(other_terms),
                    ]))
                }
            }

            Prod(terms) => {
                let mut new_terms = terms.clone();
                let mut found_x = false;
                for term in new_terms.iter_mut() {
                    if term.contains(expr) {
                        if found_x {
                            return None;
                        }
                        found_x = true;
                        *term = term.single_x(expr)?;
                    }
                }
                Some(Prod(new_terms))
            }

            Neg(term) => Some(Neg(Box::new(term.single_x(expr)?))),
            Recip(term) => Some(Recip(Box::new(term.single_x(expr)?))),

            Expr::Atom(_) => None,
        }
    }

    /// Returns a vector of the atoms within the expression
    /// This list will returns duplicated atoms
    fn atoms(&'b self) -> Vec<&'b Atom<'a>> {
        match self {
            Expr::Neg(inner_expr) | Expr::Recip(inner_expr) => inner_expr.atoms(),
            Expr::Sum(terms) | Expr::Prod(terms) => {
                terms.iter().map(Self::atoms).flatten().collect()
            }
            Expr::Atom(atom) => vec![atom],
        }
    }

    /// Returns a list of named atoms within self. Duplicates are removed.
    fn variables(&'b self) -> Vec<Ident<'a>> {
        let mut vars = self
            .atoms()
            .iter()
            .filter_map(|atom| match atom {
                Atom::Literal(_) => None,
                Atom::Named(ident) => Some(*ident),
            })
            .collect::<Vec<Ident>>();
        vars.dedup();
        vars
    }

    fn exec(&self) -> Int {
        todo!()
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Atom<'a> {
    Named(Ident<'a>),
    Literal(Int),
}

impl<'a> fmt::Display for Atom<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Atom::Named(ident) => write!(f, "{}", ident.name),
            Atom::Literal(x) => write!(f, "{}", x),
        }
    }
}

impl<'a> From<ast::proof::Expr<'a>> for Expr<'a> {
    fn from(ast_expr: ast::proof::Expr<'a>) -> Expr<'a> {
        use ast::proof::ArithOp as Op;
        use ast::proof::ExprKind::{Compound, Literal, Malformed, Named};
        match ast_expr.kind {
            Named(ident) => Expr::Atom(Atom::Named(ident)),
            Literal(x) => Expr::Atom(Atom::Literal(Int::from(x as i128))),

            Compound {
                lhs,
                op: Op::Add,
                rhs,
            } => Expr::Sum(vec![Expr::from(*lhs), Expr::from(*rhs)]),

            Compound {
                lhs,
                op: Op::Sub,
                rhs,
            } => Expr::Sum(vec![
                Expr::from(*lhs),
                Expr::Neg(Box::new(Expr::from(*rhs))),
            ]),

            Compound {
                lhs,
                op: Op::Mul,
                rhs,
            } => Expr::Prod(vec![Expr::from(*lhs), Expr::from(*rhs)]),

            Compound {
                lhs,
                op: Op::Div,
                rhs,
            } => Expr::Prod(vec![
                Expr::from(*lhs),
                Expr::Recip(Box::new(Expr::from(*rhs))),
            ]),

            Malformed => panic!("malformed expression"),
        }
    }
}

impl<'a> From<ast::proof::Condition<'a>> for Condition<'a> {
    fn from(pc: ast::proof::Condition<'a>) -> Condition<'a> {
        todo!()
    }
}

pub fn examples() {
    /// Parse tokens into and Expr
    fn parse_expr<'a>(tokens: &'a [crate::tokens::Token<'a>]) -> Expr<'a> {
        match ast::proof::Expr::parse(tokens) {
            ast::ParseRet::Ok(expr) => Expr::from(expr),
            ast::ParseRet::Err(errs) | ast::ParseRet::SoftErr(_, errs) => {
                panic!(format!("{:?}", errs))
            }
        }
    }

    use crate::tokens::{tokenize, FAKE_TOKEN};

    // should simplify to 2*x*y
    let tokens = tokenize("y * x/y * 1/x * x * y + 2 + x + y + 3 - 5 - x*y + 2*x*y - 2*x - y + x");
    let mut expr = parse_expr(&tokens);
    println!("1.0) {}", expr);
    expr = expr.simplify();
    println!("1.1) {}", expr);

    let tokens = tokenize("x + z*x + x*y + 2*x + 3 - y");
    let mut expr = parse_expr(&tokens);
    println!("2.0) {}", expr);
    expr = expr.simplify();
    println!("2.1) {}", expr);
    let x = Expr::Atom(Atom::Named(Ident {
        name: "x",
        source: &FAKE_TOKEN,
    }));
    expr = expr.single_x(&x).unwrap();
    println!("2.2) {}", expr);
    let mut x_bounds = Relation {
        left: expr.clone(),
        relation: RelationKind::Le,
        right: ZERO,
    }
    .rearrange_unsafe(&x)
    .unwrap();
    x_bounds.right = x_bounds.right.simplify();
    println!("2.3) {}", x_bounds);

    let tokens = tokenize("1/x - y");
    let mut expr = parse_expr(&tokens);
    println!("3.0) {}", expr);
    expr = expr.simplify();
    println!("3.1) {}", expr);
    let x = Expr::Atom(Atom::Named(Ident {
        name: "x",
        source: &FAKE_TOKEN,
    }));

    expr = expr.single_x(&x).unwrap();
    println!("3.2) {}", expr);
    let mut x_bounds = Relation {
        left: expr.clone(),
        relation: RelationKind::Le,
        right: ZERO,
    }
    .rearrange_unsafe(&x)
    .unwrap();
    x_bounds.right = x_bounds.right.simplify();
    println!("3.3) {}", x_bounds);

    let tokens = tokenize("10 - 2*x - y/4");
    let expr = parse_expr(&tokens);
    let cond = Condition::Ge0(expr); // so 10 - 2*x - y/4 >= 0
    for (variable, bound) in cond.bounds() {
        println!("{} {}", variable, bound.simplify());
    }

    let tokens = tokenize("10 - x - y");
    let expr = parse_expr(&tokens);
    let cond = Condition::Ge0(expr); // so  10 - x - y >= 0  thus  x + y <= 10
    for (variable, bound) in cond.bounds() {
        println!("{} {}", variable, bound.simplify());
    }

    let mut given = cond.bounds();

    let tokens = tokenize("x");
    let expr = parse_expr(&tokens);
    let cond = Condition::Ge0(expr); // so x >= 0
    given.extend(cond.bounds());

    let tokens = tokenize("y");
    let expr = parse_expr(&tokens);
    let cond = Condition::Ge0(expr.clone()); // so y >= 0
    given.extend(cond.bounds());

    println!("Let's bound x+y");
    for (x, bound) in given.clone() {
        println!("Given {} {}", x, bound);
    }

    let tokens = tokenize("x+y");
    let expr = parse_expr(&tokens);
    let mini = Minimizer::new(given.clone(), expr.clone(), 10);
    for bound in mini {
        println!("x+y >= {}", bound.simplify());
    }

    let maxi = Maximizer::new(given.clone(), expr, 10);
    for bound in maxi {
        println!("x+y <= {}", bound.simplify());
    }

    given = given.iter().map(|(x, bound)| (*x, bound.simplify())).collect();

    println!("Let's bound 2*x+y");
    for (x, bound) in given.clone() {
        println!("Given {} {}", x, bound);
    }

    let tokens = tokenize("2*x+y");
    let expr = parse_expr(&tokens).simplify();
    let mini = Minimizer::new(given.clone(), expr.clone(), 10);
    for bound in mini {
        println!("2*x+y >= {}", bound.simplify());
    }

    let maxi = Maximizer::new(given, expr, 10);
    for bound in maxi {
        println!(
            "2*x+y <= {}",
            Maximizer::unbounded(&bound.simplify()).simplify()
        );
    }
}

use std::iter::Iterator;

struct Minimizer<'a> {
    solving: Expr<'a>,
    vars: Vec<Ident<'a>>,
    given: Vec<(Ident<'a>, Bound<'a>)>,
    i: usize,
    max_depth: usize,
    child: Option<Box<Minimizer<'a>>>,
}

struct Maximizer<'a> {
    solving: Expr<'a>,
    vars: Vec<Ident<'a>>,
    given: Vec<(Ident<'a>, Bound<'a>)>,
    i: usize,
    max_depth: usize,
    child: Option<Box<Maximizer<'a>>>,
}

impl<'a> Minimizer<'a> {
    fn new(given: Vec<(Ident<'a>, Bound<'a>)>, solve: Expr<'a>, max_depth: usize) -> Minimizer<'a> {
        let vars = solve.variables();
        Minimizer {
            solving: solve,
            vars,
            given,
            i: 0,
            max_depth,
            child: None,
        }
    }
}

impl<'a> Maximizer<'a> {
    fn new(given: Vec<(Ident<'a>, Bound<'a>)>, solve: Expr<'a>, max_depth: usize) -> Maximizer<'a> {
        let vars = solve.variables();
        Maximizer {
            solving: solve,
            vars,
            given,
            i: 0,
            max_depth,
            child: None,
        }
    }
}

macro_rules! optimizer_body {
    ($self:expr) => {{
        if let Some(child) = &mut $self.child {
            match child.next() {
                Some(x) => return Some(x),
                None => (),
            }
        }

        // Handle the maximum depth being reached - we just assume everything is unbounded.
        if $self.max_depth == 0 {
            // Since `i` has no use to the final child, we may as well use it to keep track of if
            // we've already given a bound.
            if $self.i != 0 {
                return None;
            }
            $self.i = 1;
            return Some($self.solving.clone());
        }

        let (x, bound) = loop {
            if $self.i >= $self.given.len() {
                $self.max_depth = 0;
                $self.i = 0;
                return $self.next();
            }

            let (x_ident, bound) = &$self.given[$self.i];
            if $self.vars.contains(x_ident) {
                break (Expr::Atom(Atom::Named(*x_ident)), bound);
            }
            $self.i += 1;
        };

        let mut new_given = $self.given.clone();
        new_given.remove($self.i);

        $self.i += 1;

        $self.child = Some(Box::new(Self::new(
            new_given,
            Self::sub_bound(&$self.solving, &x, bound).simplify(),
            $self.max_depth - 1,
        )));
        $self.next()
    }};
}

impl<'a> Iterator for Minimizer<'a> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        optimizer_body!(self)
    }
}
impl<'a> Iterator for Maximizer<'a> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        optimizer_body!(self)
    }
}

macro_rules! prod_optimise {
    ($terms:expr, $x:expr, $bound:expr, $Self:ty) => {{
        // We now want to minimize a product, for now, we will only simplify products in
        // the form: [expr]*literal0*literal1*... (the other expression is optional)
        // Where all the literals are non-negative.
        // Since the expression is simplified we are allowed to assume that all literals
        // are non-negative and that literals are the last terms.
        //
        // It is clear that the optimum of an expression with this form is
        // optimum(expr)*literal0*literal1*...
        //
        // Other forms would be more complex.
        let mut out = Vec::with_capacity($terms.len());
        for i in 0..$terms.len() {
            let term = &$terms[i];
            out.push(match term {
                Expr::Atom(Atom::Literal(x)) => {
                    if *x < Int::ZERO {
                        panic!("literal < 0")
                    } else {
                        // Just copy any literals
                        term.clone()
                    }
                }

                _ => {
                    // Only optimise if it's the first term.
                    // Any subsequent terms MUST be literals.
                    // (Also note that the first term cannot be a literal if another kind
                    // of expression exists since the bound expression is simplified).
                    if i == 0 {
                        Self::sub_bound(term, $x, $bound)
                    } else {
                        todo!()
                    }
                }
            });
        }
        Expr::Prod(out)
    }};
}

impl<'a> Minimizer<'a> {
    fn unbounded(expr: &Expr<'a>) -> Expr<'a> {
        match expr {
            Expr::Neg(inner_expr) => Expr::Neg(Box::new(Maximizer::unbounded(inner_expr))),
            Expr::Recip(inner_expr) => Expr::Recip(Box::new(Maximizer::unbounded(inner_expr))),
            Expr::Sum(terms) => Expr::Sum(terms.iter().map(Self::unbounded).collect()),
            Expr::Prod(_) => todo!(),
            Expr::Atom(Atom::Literal(_)) => expr.clone(),
            Expr::Atom(Atom::Named(_)) => Expr::Atom(Atom::Literal(-Int::Infinity)),
        }
    }

    fn sub_bound(expr: &Expr<'a>, x: &Expr<'a>, bound: &Bound<'a>) -> Expr<'a> {
        if expr.eq(x) {
            return match bound {
                Bound::Ge(bound_expr) => bound_expr.clone(),
                Bound::Le(_) => expr.clone(),
            };
        }
        match expr {
            Expr::Neg(inner_expr) => {
                Expr::Neg(Box::new(Maximizer::sub_bound(inner_expr, x, bound)))
            }
            Expr::Recip(inner_expr) => {
                Expr::Recip(Box::new(Maximizer::sub_bound(inner_expr, x, bound)))
            }
            Expr::Sum(terms) => Expr::Sum(
                terms
                    .iter()
                    .map(|term| Self::sub_bound(term, x, bound))
                    .collect(),
            ),
            Expr::Prod(terms) => prod_optimise!(terms, x, bound, Self),
            Expr::Atom(_) => expr.clone(),
        }
    }
}

impl<'a> Maximizer<'a> {
    fn unbounded(expr: &Expr<'a>) -> Expr<'a> {
        match expr {
            Expr::Neg(inner_expr) => Expr::Neg(Box::new(Minimizer::unbounded(inner_expr))),
            Expr::Recip(inner_expr) => Expr::Recip(Box::new(Minimizer::unbounded(inner_expr))),
            Expr::Sum(terms) => Expr::Sum(terms.iter().map(Self::unbounded).collect()),
            Expr::Prod(_) => todo!(),
            Expr::Atom(Atom::Literal(_)) => expr.clone(),
            Expr::Atom(Atom::Named(_)) => Expr::Atom(Atom::Literal(Int::Infinity)),
        }
    }
    fn sub_bound(expr: &Expr<'a>, x: &Expr<'a>, bound: &Bound<'a>) -> Expr<'a> {
        if expr.eq(x) {
            return match bound {
                Bound::Le(bound_expr) => bound_expr.clone(),
                Bound::Ge(_) => expr.clone(),
            };
        }
        match expr {
            Expr::Neg(inner_expr) => {
                Expr::Neg(Box::new(Minimizer::sub_bound(inner_expr, x, bound)))
            }
            Expr::Recip(inner_expr) => {
                Expr::Recip(Box::new(Minimizer::sub_bound(inner_expr, x, bound)))
            }
            Expr::Sum(terms) => Expr::Sum(
                terms
                    .iter()
                    .map(|term| Self::sub_bound(term, x, bound))
                    .collect(),
            ),
            Expr::Prod(terms) => prod_optimise!(terms, x, bound, Self),
            Expr::Atom(_) => expr.clone(),
        }
    }
}
