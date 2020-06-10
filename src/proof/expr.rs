use super::int::{EvalInt, Int, Rational};
use crate::ast::{self, Ident};
use std::fmt;

/// An expression
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Expr<'a> {
    // NOTE The order of these variants matters for simplification.
    // Places that assume the order of enums should be marked with `EXPR ORDER ASSUMED` to help
    // maintainability.
    // Requirements of order:
    // - Neg is first
    // - Recip is second
    // - Prod is last
    // - Atom is before Prod
    // - This leaves only 1 place for Sum
    /// -e
    Neg(Box<Expr<'a>>),

    /// 1/e
    Recip(Box<Expr<'a>>, bool),

    /// e[0] + e[1] + ...
    Sum(Vec<Expr<'a>>),

    Atom(Atom<'a>),

    /// e[0] * e[1] * ...
    Prod(Vec<Expr<'a>>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Atom<'a> {
    // NOTE Like the Expr enum, the order of these variants is assumed.
    // Places where this order is assumed should be marked with `ATOM ORDER ASSUMED` similar to
    // Expr.
    Named(Ident<'a>),
    Literal(Rational),
}

/// An expression with the literal value 0
pub const ZERO: Expr = Expr::Atom(Atom::Literal(Rational::ZERO));
/// An expression with the literal value 1
pub const ONE: Expr = Expr::Atom(Atom::Literal(Rational::ONE));

impl<'b, 'a: 'b> Expr<'a> {
    /// Returns true if the expressions are equal or if their simplified values are equal.
    /// This is a more reliable equals method since, in the standard implementation of ==,
    /// x + 2 != 2 + x whereas it would be equal with this definition.
    ///
    /// This is however much more expensive to compute since if 2 expressions aren't equal, they
    /// are always simplified.
    pub fn simplify_eq(&self, other: &Expr<'a>) -> bool {
        self.eq(other) || self.simplify() == other.simplify()
    }

    pub fn switch_rounding_mode(&self) -> Expr<'a> {
        match self {
            Expr::Recip(inner_expr, rounding_mode) => {
                Expr::Recip(inner_expr.clone(), !rounding_mode)
            }
            _ => self.clone(),
        }
    }

    pub fn switch_all_rounding_modes(&self) -> Expr<'a> {
        match self {
            Expr::Recip(inner_expr, rounding_mode) => Expr::Recip(
                Box::new(inner_expr.switch_all_rounding_modes()),
                !*rounding_mode,
            ),
            Expr::Sum(terms) => {
                Expr::Sum(terms.iter().map(Expr::switch_all_rounding_modes).collect())
            }
            Expr::Prod(terms) => {
                Expr::Prod(terms.iter().map(Expr::switch_all_rounding_modes).collect())
            }
            Expr::Neg(inner) => Expr::Neg(Box::new(inner.switch_all_rounding_modes())),
            Expr::Atom(_) => self.clone(),
        }
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
    /// - Terms in sums and products are sorted (as expressions, see the order of Expr and Atom).
    pub fn simplify(&self) -> Expr<'a> {
        let simplified = self.simplify_run();
        if *self != simplified {
            let simplified2 = simplified.simplify();
            if simplified2 == ZERO {
                //println!("{} -> 0", self);
            }
            if simplified != simplified2 {
                // If simplifying again gives us a different result, we should log the error since
                // we don't want this to happen.
                // There are cases where this can happen - these need to be fixed. After fixing,
                // this will be useful for debugging.
                /*println!(
                    "Dodgy simplification: {} -> {} -> {}",
                    self, simplified, simplified2
                );*/
                return simplified2;
            }
        }
        simplified
    }

    fn simplify_run(&self) -> Expr<'a> {
        use Expr::{Neg, Prod, Recip, Sum};
        match self {
            // Named atoms can't be simplified
            Expr::Atom(Atom::Named(_)) => self.clone(),

            // Convert negative literals in to Neg(<positive literal>)
            Expr::Atom(Atom::Literal(x)) => {
                if *x < Rational::ZERO {
                    Neg(Box::new(Expr::Atom(Atom::Literal(-*x))))
                } else {
                    self.clone()
                }
            }

            Neg(expr) => match expr.simplify() {
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
                new_expr => {
                    // -0 = 0
                    if new_expr == ZERO {
                        ZERO
                    } else {
                        Neg(Box::new(new_expr))
                    }
                }
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
                                // TODO
                                /*if let Expr::Neg(_) = term {
                                    these_terms = these_terms
                                        .iter()
                                        // TODO Swith just 1 or all?
                                        .map(Self::switch_rounding_mode)
                                        .collect();
                                }*/
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

            Recip(expr, rounding) => match expr.simplify() {
                // 1/(1/x) = x
                Recip(inner_expr, _) => *inner_expr,

                // 1/(-x) = -(1/x)
                Neg(inner_expr) => Neg(Box::new(Recip(inner_expr, *rounding).simplify())),
                // TODO Similar to the TODO in some, calling simplify on the new expression could
                // be optimised. The same applies to the case below too.

                // 1/(a*b*c*...) = 1/a * 1/b * 1/c
                Prod(terms) => Prod(
                    terms
                        .iter()
                        .map(|term| Recip(Box::new(term.clone()), *rounding).simplify())
                        .collect(),
                ),

                Expr::Atom(Atom::Literal(x)) => Expr::Atom(Atom::Literal(Rational::ONE / x)),

                new_expr => Recip(Box::new(new_expr), *rounding),
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
    fn get_number_and_term(&self) -> (Rational, Expr<'a>) {
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
                .unwrap_or_else(|| (Rational::ONE, self.clone())),

            //Again, the default case.
            _ => (Rational::ONE, self.clone()),
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
                        if res < Rational::ZERO {
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
            Recip(expr, rounding) => match &**expr {
                /*
                Expr::Atom(Atom::Literal(x)) => match other {
                    // (1/x) * y = y/x for literals if there's no rounding
                    Expr::Atom(Atom::Literal(y)) => {
                        let x = *x;
                        let y = *y;

                        // We can't simplify if we're are doing anything with 1/0
                        if x == Int::ZERO {
                            return None;
                        }
                        let res = y / x;
                        // Only simplify if res is exact
                        if res * x == y {
                            Some(Expr::Atom(Atom::Literal(res)))
                        } else {
                            let res = x / y;
                            if res * y == x {
                                Some(Expr::Recip(
                                    Box::new(Expr::Atom(Atom::Literal(res))),
                                    *rounding,
                                ))
                            } else {
                                None
                            }
                        }
                    }

                    Recip(other_expr, inner_rounding) => match &**other_expr {
                        // (1/x) * (1/y) = 1/(x*y) for literals
                        Expr::Atom(Atom::Literal(y)) => {
                            if *rounding == *inner_rounding {
                                Some(Recip(
                                    Box::new(Expr::Atom(Atom::Literal((*x) * (*y)))),
                                    *rounding,
                                ))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    },

                    _ => None,
                },
                */
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

    /// Returns true iff self contains expr or a simplification of.
    pub(super) fn contains(&self, expr: &Expr<'a>) -> bool {
        use Expr::{Neg, Prod, Recip, Sum};
        if self.simplify_eq(expr) {
            return true;
        }
        match self {
            Sum(terms) | Prod(terms) => terms.iter().find(|term| term.contains(expr)).is_some(),
            Neg(term) | Recip(term, _) => term.contains(expr),
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
            Recip(term, rounding) => Some(Recip(
                Box::new(term.factor(&Recip(Box::new(expr.clone()), *rounding))?),
                *rounding,
            )),

            // An Atom can't be factored. Note that if expr is this Atom then it would have been
            // handled earlier.
            Expr::Atom(_) => None,
        }
    }

    /// Returns an Expr equivilent to that of Expr, but with only a single occurence of `expr`.
    /// This is done primerily by factorisation.
    /// If expr cannot be rewritten with only a single occurence of `expr` then None is returned.
    pub fn single_x(&self, expr: &Expr<'a>) -> Option<Expr<'a>> {
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
            Recip(term, rounding) => Some(Recip(Box::new(term.single_x(expr)?), *rounding)),

            Expr::Atom(_) => None,
        }
    }

    /// Returns a vector of the atoms within the expression
    /// This list will returns duplicated atoms
    pub fn atoms(&'b self) -> Vec<&'b Atom<'a>> {
        match self {
            Expr::Neg(inner_expr) | Expr::Recip(inner_expr, _) => inner_expr.atoms(),
            Expr::Sum(terms) | Expr::Prod(terms) => {
                terms.iter().map(Self::atoms).flatten().collect()
            }
            Expr::Atom(atom) => vec![atom],
        }
    }

    /// Returns a list of named atoms within self. Duplicates are removed.
    pub fn variables(&'b self) -> Vec<Ident<'a>> {
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

    /// Substitute `x` with `with` in self and return the result.
    pub fn substitute(&self, x: Ident<'a>, with: &Expr<'a>) -> Expr<'a> {
        match self {
            Expr::Atom(Atom::Named(y)) => {
                if x == *y {
                    with.clone()
                } else {
                    self.clone()
                }
            }

            Expr::Atom(Atom::Literal(_)) => self.clone(),

            Expr::Sum(terms) => {
                Expr::Sum(terms.iter().map(|term| term.substitute(x, with)).collect())
            }
            Expr::Prod(terms) => {
                Expr::Prod(terms.iter().map(|term| term.substitute(x, with)).collect())
            }

            Expr::Neg(term) => Expr::Neg(Box::new(term.substitute(x, with))),
            Expr::Recip(term, rounding) => {
                Expr::Recip(Box::new(term.substitute(x, with)), *rounding)
            }
        }
    }

    /// Tries to evaluate self.
    /// This requires all atoms to be literals - None will be returned if this is not the case.
    /// It also assumes self is simplified. The behaviour of eval is undefined if the expression is
    /// not simplified.
    ///
    /// `div` is a function used for division. This can be used to determine the rounding
    /// direction.
    /// See also: `Self::eval2`
    //pub fn eval(&self, div: impl Fn(Int, Int) -> Int + Copy) -> Option<Int> {
    pub fn eval(&self) -> Option<EvalInt> {
        self.eval_rat().map(Rational::eval_floor)
    }

    /*
    /// Tries to evaluate self, rounding down for division.
    /// This calls `self.eval(Int::div_floor)`.
    pub fn eval_floor(&self) -> Option<Int> {
        self.eval(Int::div_floor)
    }

    /// Tries to evaluate self, rounding up for division.
    /// This calls `self.eval(Int::div_ceil)`.
    pub fn eval_ceil(&self) -> Option<Int> {
        self.eval(Int::div_ceil)
    }
    */

    /*
    /// This is an extension of `eval`. See there for the main documentation.
    ///
    /// `div1` and `div2` are used for division.
    /// `div1` is the primary choice but this is flipped for every Neg or Recip expression that the
    /// division occurs witihin.
    ///
    /// The purpose if this is to find a minimum or maximum values that will satisfy something by
    /// alternating between `Int::div_floor` and `Int::div_ceil`.
    ///
    /// See `eval_min` and `eval_max` which you are more likely to use.
    fn eval2(
        &self,
        //div1: impl Fn(Int, Int) -> Int + Copy,
        //div2: impl Fn(Int, Int) -> Int + Copy,
    ) -> Option<EvalInt> {
        match self {
            Expr::Neg(inner_expr) => Some(-inner_expr.eval2()?),
            Expr::Recip(inner_expr, false) => Some(EvalInt::ONE.div_floor(inner_expr.eval()?)),
            Expr::Recip(inner_expr, true) => Some(EvalInt::ONE.div_ceil(inner_expr.eval()?)),

            Expr::Sum(terms) => terms
                .iter()
                .map(|term| term.eval())
                .fold(Some(EvalInt::ZERO), |sum, term| Some(sum? + term?)),
            Expr::Prod(terms) => match terms.len() {
                0 => Some(EvalInt::ONE),
                1 => terms[0].eval(),
                2 => match (&terms[0], &terms[1]) {
                    (Expr::Recip(denominator, rounding), numerator) => Some(
                        //div1(*x, y)
                        if *rounding {
                            numerator.eval()?.div_ceil(denominator.eval()?)
                        } else {
                            numerator.eval()?.div_floor(denominator.eval()?)
                        },
                    ),
                    _ => None, //panic!(format!("eval expression is not simplified (case 2) {}", self)),
                },
                _ => None, //panic!("eval expression is not simplified (case 1)"),
            },

            Expr::Atom(Atom::Literal(x)) => Some((*x).into()),
            Expr::Atom(Atom::Named(_)) => None,
        }
    }
    */

    /// This is an extension of `eval`. See there for the main documentation.
    ///
    /// `div1` and `div2` are used for division.
    /// `div1` is the primary choice but this is flipped for every Neg or Recip expression that the
    /// division occurs witihin.
    ///
    /// The purpose if this is to find a minimum or maximum values that will satisfy something by
    /// alternating between `Int::div_floor` and `Int::div_ceil`.
    ///
    /// See `eval_min` and `eval_max` which you are more likely to use.
    fn eval_rat(
        &self,
        //div1: impl Fn(Int, Int) -> Int + Copy,
        //div2: impl Fn(Int, Int) -> Int + Copy,
    ) -> Option<Rational> {
        match self {
            Expr::Neg(inner_expr) => Some(-inner_expr.eval_rat()?),
            Expr::Recip(inner_expr, _) => Some(Rational::ONE / (inner_expr.eval_rat()?)),

            Expr::Sum(terms) => terms
                .iter()
                .map(|term| term.eval_rat())
                .fold(Some(Rational::ZERO), |sum, term| Some(sum? + term?)),
            Expr::Prod(terms) => terms
                .iter()
                .map(|term| term.eval_rat())
                .fold(Some(Rational::ONE), |sum, term| Some(sum? * term?)),

            Expr::Atom(Atom::Literal(x)) => Some((*x).into()),
            Expr::Atom(Atom::Named(_)) => None,
        }
    }

    fn group_recips(&self) -> Expr<'a> {
        fn get_recip_inner_expr<'a>(expr: &Expr<'a>) -> Option<(Expr<'a>, bool, Expr<'a>)> {
            match expr {
                Expr::Recip(inner, rounding) => Some((*inner.clone(), *rounding, ONE)),
                Expr::Prod(terms) => terms
                    .iter()
                    .enumerate()
                    .find_map(|(idx, term)| match term {
                        Expr::Recip(inner, rounding) => Some((*inner.clone(), *rounding, idx)),
                        _ => None,
                    })
                    .map(|(denom, rounding, idx)| {
                        (denom, rounding, {
                            let mut new_terms = terms.clone();
                            new_terms.remove(idx);
                            Expr::Prod(new_terms)
                        })
                    }),
                Expr::Neg(inner) => get_recip_inner_expr(inner)
                    .map(|(denom, rounding, expr)| (denom, rounding, Expr::Neg(Box::new(expr)))),
                // The expression is simplified so we don't need to bother checking sums since this
                // will only be called with a sums terms.
                Expr::Sum(_) | Expr::Atom(_) => None,
            }
        }

        let sum_terms = match self {
            Expr::Neg(inner) => return Expr::Neg(Box::new(inner.group_recips())),
            Expr::Recip(inner, rounding) => {
                return Expr::Recip(Box::new(inner.group_recips()), *rounding)
            }
            Expr::Prod(terms) => return Expr::Prod(terms.iter().map(Expr::group_recips).collect()),
            Expr::Atom(_) => return self.clone(),
            Expr::Sum(terms) => terms,
        };
        struct Meta<'a> {
            expr: Expr<'a>,
            denom: Option<(Expr<'a>, bool)>,
        }
        let mut sum_terms = sum_terms
            .iter()
            .map(|term| {
                let (denom, rounding, left) = match get_recip_inner_expr(term) {
                    Some(stuff) => stuff,
                    None => {
                        return Meta {
                            expr: term.clone(),
                            denom: None,
                        }
                    }
                };
                Meta {
                    expr: left,
                    denom: Some((denom, rounding)),
                }
            })
            .collect::<Vec<Meta>>();
        sum_terms.sort_unstable_by_key(|Meta { denom, .. }| denom.clone());
        let mut current_denom = match sum_terms.first() {
            Some(Meta { denom, .. }) => denom.clone(),
            None => return self.clone(),
        };
        let mut out = Vec::new();
        let mut current = Vec::new();
        for Meta { expr: term, denom } in sum_terms {
            if denom == current_denom {
                current.push(term);
            } else {
                match current_denom {
                    None => out.push(Expr::Sum(current)),
                    Some(denom) => out.push(Expr::Prod(vec![
                        Expr::Recip(Box::new(denom.0), denom.1),
                        Expr::Sum(current),
                    ])),
                }
                current = vec![term];
                current_denom = denom;
            }
        }
        match current_denom {
            None => out.push(Expr::Sum(current)),
            Some(denom) => out.push(Expr::Prod(vec![
                Expr::Recip(Box::new(denom.0), denom.1),
                Expr::Sum(current),
            ])),
        }
        match out.len() {
            0 => ZERO,
            1 => out[0].clone(),
            _ => Expr::Sum(out),
        }
    }

    /*
    /// Round in division to minimize the result.
    /// Calls `self.eval2(Int::div_floor, Int::div_ceil)`
    pub fn eval_min(&self) -> Option<Int> {
        self.eval2(Int::div_floor, Int::div_ceil)
    }

    /// Round in division to maximize the result.
    /// Calls `self.eval2(Int::div_ceil, Int::div_floor)`
    pub fn eval_max(&self) -> Option<Int> {
        self.eval2(Int::div_ceil, Int::div_floor)
    }
    */

    /// Returns an i8 with the same sign as the expression or None if this can't be determined.
    pub fn sign(&self) -> Option<i8> {
        match self {
            Expr::Neg(inner) => Some(-inner.sign()?),
            Expr::Recip(inner, _) => Some(inner.sign()?),
            Expr::Prod(terms) => terms.iter().map(Expr::sign).fold(Some(1), |sign, term_sign| Some(sign?*term_sign?)),
            Expr::Sum(terms) => terms.iter().map(Expr::sign).fold(Some(0), |sign, term_sign| match (sign?, term_sign?) {
                (0, term_sign) => Some(term_sign),
                (1, 1) => Some(1),
                (-1, -1) => Some(-1),
                _ => None,
            }),
            Expr::Atom(Atom::Literal(x)) => Some(x.sign_u8()),
            // TODO Add hooks for determining the sign of variables
            Expr::Atom(Atom::Named(_)) => None,
        }
    }
}

impl<'a> From<&ast::proof::Expr<'a>> for Expr<'a> {
    fn from(ast_expr: &ast::proof::Expr<'a>) -> Expr<'a> {
        use ast::proof::ArithOp as Op;
        use ast::proof::ExprKind::{Compound, Literal, Malformed, Named};
        match &ast_expr.kind {
            Named(ident) => Expr::Atom(Atom::Named(*ident)),
            Literal(x) => Expr::Atom(Atom::Literal(Rational::from(Int::from(*x as i128)))),

            Compound {
                lhs,
                op: Op::Add,
                rhs,
            } => Expr::Sum(vec![Expr::from(&**lhs), Expr::from(&**rhs)]),

            Compound {
                lhs,
                op: Op::Sub,
                rhs,
            } => Expr::Sum(vec![
                Expr::from(&**lhs),
                Expr::Neg(Box::new(Expr::from(&**rhs))),
            ]),

            Compound {
                lhs,
                op: Op::Mul,
                rhs,
            } => Expr::Prod(vec![Expr::from(&**lhs), Expr::from(&**rhs)]),

            Compound {
                lhs,
                op: Op::Div,
                rhs,
            } => Expr::Prod(vec![
                Expr::from(&**lhs),
                Expr::Recip(Box::new(Expr::from(&**rhs)), false),
            ]),

            Malformed => panic!("malformed expression"),
        }
    }
}

impl<'a> fmt::Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use Expr::{Atom, Neg, Prod, Recip, Sum};
        match self {
            Atom(atom) => write!(f, "{}", atom),
            Neg(expr) => write!(f, "-({})", *expr),
            Recip(expr, false) => write!(f, "1//({})", *expr),
            Recip(expr, true) => write!(f, "1/^({})", *expr),
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

impl<'a> fmt::Display for Atom<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Atom::Named(ident) => write!(f, "{}", ident.name),
            Atom::Literal(x) => write!(f, "{}", x),
        }
    }
}
