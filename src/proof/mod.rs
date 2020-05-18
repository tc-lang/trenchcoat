//! Verification for proof statments
//!
//! The high-level operations here are on functions and the global scope, taking the AST as input.
//! It is assumed here that the AST nodes given as input have passed through the checks in `verify`
//! without error.

mod error;
use self::error::Error;
use crate::ast::{self, Ident};

/// Attempts to prove that the entire contents of the program is within the bounds specified by the
/// proof rules.
fn validate<'a>(top_level_items: &'a [ast::Item<'a>]) -> Vec<Error<'a>> {
    todo!()
}

// !!!!! Requirements have had very little work. These data structures are likely to change and not
// !!!!! yet documented.
// !!!!! Please scroll down to Expr

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Requirement<'a> {
    or: Vec<RequirementTerm<'a>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct RequirementTerm<'a> {
    and: Vec<Condition<'a>>,
}

impl<'a> Requirement<'a> {
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
}

impl<'a> RequirementTerm<'a> {
    fn and_with(&mut self, term: RequirementTerm<'a>) {
        self.and.extend(term.and);
    }
    fn and_with_condition(&mut self, cond: Condition<'a>) {
        self.and.push(cond);
    }
}

/// A Condition is a boolean condition.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Condition<'a> {
    /*/// lhs <= rhs
    Le{
        lhs: Expr<'a>,
        rhs: Expr<'a>,
    },
    */
    /*
    /// lhs >= rhs
    Ge{
        lhs: Expr<'a>,
        rhs: Expr<'a>,
    },
    */
    /// True iff the expression evaluates to a non-negative value
    Ge0(Expr<'a>),
    /// Always true
    True,
    /// Always false
    False,
}

/// This will (maybe) be used later
enum Bound<'a> {
    Le(Expr<'a>),
    Ge(Expr<'a>),
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
    fn bounds_on(name: Ident<'a>) -> Option<Bound<'a>> {
        todo!()
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
const ZERO: Expr = Expr::Atom(Atom::Literal(0));
/// An expression with the literal value 1
const ONE: Expr = Expr::Atom(Atom::Literal(1));

impl<'a> std::fmt::Display for Expr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        use Expr::{Atom, Neg, Prod, Recip, Sum};
        match self {
            Atom(atom) => write!(f, "{}", atom),
            Neg(expr) => write!(f, "-{}", *expr),
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
                    .map(|term| format!("{}", term))
                    .collect::<Vec<String>>()
                    .join(" * ")
            ),
        }
    }
}

impl<'a> Expr<'a> {
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
                if *x < 0 {
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
    fn get_number_and_term(&self) -> (isize, Expr<'a>) {
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
                .unwrap_or_else(|| (1, self.clone())),

            //Again, the default case.
            _ => (1, self.clone()),
        }
    }

    /// A simplifier that collects terms in addition.
    ///
    /// See also: simplify_terms
    fn add_collect(&self, other: &Expr<'a>) -> Option<Expr<'a>> {
        let (n1, expr1) = self.get_number_and_term();
        let (n2, expr2) = other.get_number_and_term();
        if expr1 == expr2 {
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
                        if res < 0 {
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
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct SimpleExpr<'a> {
    terms: Vec<SimpleTerm<'a>>,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum SimpleTerm<'a> {
    Pos(SimpleFrac<'a>),
    Neg(SimpleFrac<'a>),
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct SimpleFrac<'a> {
    Numerator: Vec<Atom<'a>>,
    Denominator: Vec<Expr<'a>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Atom<'a> {
    Named(Ident<'a>),
    Literal(isize),
}

impl<'a> std::fmt::Display for Atom<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
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
            Literal(x) => Expr::Atom(Atom::Literal(x)),

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
    use crate::tokens::tokenize;
    // should simplify to 2*x*y
    let tokens = tokenize("y * x/y * 1/x * x * y + 2 + x + y + 3 - 5 - x*y + 2*x*y - 2*x - y + x");
    let ast_expr = match ast::proof::Expr::parse(&tokens) {
        ast::ParseRet::Ok(expr) => expr,
        _ => panic!("failed to parse example expression tokens"),
    };
    println!("{:?}", ast_expr);
    let mut expr = Expr::from(ast_expr);
    println!("{}", expr);
    expr = expr.simplify();
    println!("{}", expr);
}
