use super::int::{EvalInt, Int, Rational};
use super::sign::Sign;
use super::PrettyFormat;
use crate::ast::{self, Ident};
use std::fmt::{self, Display, Formatter};
use std::iter;
use std::ops::Deref;

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
    /// The bool represents the rounding direction:
    ///   Recip(x, false) = 1//x (round down)
    ///   Recip(x, true)  = 1/^x (round up)
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

/// Produces an expression with the literal value 0
///
/// This should have nearly no actual cost. It exists as a separate function because expressions
/// are invariant on `'a`, which means that `Expr<'static>` can't be used in place of `Expr<'a>`.
pub fn zero<'a>() -> Expr<'a> {
    Expr::Atom(Atom::Literal(Rational::ZERO))
}

/// Produces an expression with the literal value 1
///
/// This should have nearly no actual cost. It exists as a separate function because expressions
/// are invariant on `'a`, which means that `Expr<'static>` can't be used in place of `Expr<'a>`.
pub fn one<'a>() -> Expr<'a> {
    Expr::Atom(Atom::Literal(Rational::ONE))
}

/// Produces an expression with the literal value -1
///
/// This should have nearly no actual cost. It exists as a separate function because expressions
/// are invariant on `'a`, which means that `Expr<'static>` can't be used in place of `Expr<'a>`.
pub fn minus_one<'a>() -> Expr<'a> {
    Expr::Atom(Atom::Literal(Rational::MINUS_ONE))
}

enum SimplifyResult<'a> {
    None,
    Cancel,
    Combine(Expr<'a>),
}

impl<'a> std::ops::Neg for Expr<'a> {
    type Output = Expr<'a>;
    fn neg(self) -> Expr<'a> {
        Expr::Neg(Box::new(self))
    }
}
impl<'a> std::ops::Add for Expr<'a> {
    type Output = Expr<'a>;
    fn add(self, other: Expr<'a>) -> Expr<'a> {
        Expr::Sum(vec![self, other])
    }
}
impl<'a> std::ops::Sub for Expr<'a> {
    type Output = Expr<'a>;
    fn sub(self, other: Expr<'a>) -> Expr<'a> {
        self + -other
    }
}

impl<'b, 'a: 'b> Expr<'a> {
    /// Shorthand for `Expr::Recip(Box::new(self), rounding)`
    pub fn recip(self, rounding: bool) -> Expr<'a> {
        Expr::Recip(Box::new(self), rounding)
    }
    /// Shorthand for `Expr::Atom(Atom::Literal(x))`
    pub fn literal(x: Rational) -> Expr<'a> {
        Expr::Atom(Atom::Literal(x))
    }

    /// Returns a simplified version of self.
    /// The simplification rules have not yet been fully decided.
    /// Stable rules will be documented here with other rules documented in the code.
    ///
    /// - Sums and Products are flattened. (i.e.) x*(y*z) becomes x*y*z
    /// - Sums and Prods of 1 term are unwrapped to become just the term
    /// - Products do not directly contain Neg terms. Instead, they are lifted to enclose the
    ///   product.
    /// - Neg is distributed in sums. i.e. Neg(x+y+z) = Neg(x) + Neg(y) + Neg(z)
    /// - Recip is distributed in products. i.e. Recip(x*y*z) = Recip(x) * Recip(y) * Recip(z)
    /// - Neg(Neg(x)) becomes x
    /// - Recip(Recip(x)) becomes x
    /// - 0s are removed from sums
    /// - 1s are removed from products
    /// - Calculations between literals are performed. i.e. 1+2 becomes 3 or 4/2 becomes 2
    /// - Prods containing a 0 are simplified to 0
    /// - Terms in products are sorted (as expressions, see the order of Expr and Atom).
    /// - (Terms in sums are no longer sorted)
    pub fn simplify(&self) -> Expr<'a> {
        let simplified = self.simplify_run();
        #[cfg(feature = "expr-simplify-debug")]
        if *self != simplified {
            let simplified2 = simplified.simplify();
            if simplified != simplified2 {
                // If simplifying again gives us a different result, we should log the error
                // since we don't want this to happen.
                println!(
                    "Dodgy simplification: {} -> {} -> {}",
                    self, simplified, simplified2
                );
                return simplified2;
            }
        }
        simplified
    }

    /// Internally used by simplify.
    /// This should simplify the expression fully however for testing purposes it is called twice
    /// to ensure that the result does not change again.
    fn simplify_run(&self) -> Expr<'a> {
        use Expr::{Neg, Prod, Recip, Sum};
        match self {
            // Named atoms can't be simplified
            Expr::Atom(Atom::Named(_)) => self.clone(),

            // Convert negative literals in to Neg(<positive literal>)
            Expr::Atom(Atom::Literal(x)) => {
                if *x < Rational::ZERO {
                    -Expr::literal(-*x)
                } else {
                    self.clone()
                }
            }

            Sum(terms) => Expr::simplify_sum_terms(terms.iter()),
            Prod(terms) => Expr::simplify_prod_terms(terms.iter()),
            Neg(inner_expr) => Expr::simplify_neg_inner(inner_expr),
            Recip(inner_expr, rounding) => Expr::simplify_recip_inner(inner_expr, *rounding),
        }
    }

    fn simplify_neg_inner(inner_expr: &Expr<'a>) -> Expr<'a> {
        Expr::simplify_simplified_neg_inner(inner_expr.simplify())
    }

    fn simplify_simplified_neg_inner(inner_expr: Expr<'a>) -> Expr<'a> {
        use Expr::{Neg, Sum};
        match inner_expr {
            // -(-x) = x
            Neg(inner_expr) => *inner_expr,

            // -(a + b + c + ...) = (-a) + (-b) + (-c) + ...
            Sum(terms) => Expr::simplify_simplified_sum_terms(
                terms.into_iter().map(Expr::simplify_simplified_neg_inner),
            ),

            new_expr => {
                // -0 = 0
                if new_expr == zero() {
                    zero()
                } else {
                    Neg(Box::new(new_expr))
                }
            }
        }
    }

    fn simplify_recip_inner(inner_expr: &Expr<'a>, rounding: bool) -> Expr<'a> {
        Expr::simplify_simplified_recip_inner(inner_expr.simplify(), rounding)
    }

    fn simplify_simplified_recip_inner(inner_expr: Expr<'a>, rounding: bool) -> Expr<'a> {
        use Expr::{Neg, Prod, Recip};
        match inner_expr {
            // 1/(1/x) = x
            Recip(inner_expr, _) => *inner_expr,

            // 1/(-x) = -(1/x)
            Neg(inner_expr) => -Expr::simplify_simplified_recip_inner(*inner_expr, rounding),

            // 1/(a*b*c*...) = 1/a * 1/b * 1/c
            Prod(terms) => Expr::simplify_simplified_prod_terms(
                terms
                    .into_iter()
                    .map(|term| Expr::simplify_simplified_recip_inner(term, rounding)),
            ),

            Expr::Atom(Atom::Literal(x)) => Expr::literal(x.recip()),

            new_expr => Recip(Box::new(new_expr), rounding),
        }
    }

    fn simplify_sum_terms(terms: impl Iterator<Item = &'b Expr<'a>>) -> Expr<'a> {
        Expr::simplify_simplified_sum_terms(terms.map(Expr::simplify))
    }

    fn simplify_simplified_sum_terms(terms: impl Iterator<Item = Expr<'a>>) -> Expr<'a> {
        use Expr::Sum;
        let mut new_terms = terms
            // Remove 0s from the sum
            .filter(|term| *term != zero())
            // Flatten
            .flat_map(|term| match term {
                Sum(terms) => terms,
                _ => std::slice::from_ref(&term).to_vec(),
            })
            .collect::<Vec<Expr>>();

        // Collect terms and literals
        Self::simplify_terms_unsorted(Self::add_collect, &mut new_terms);

        // Unwrap the sum if possible
        let res = match new_terms.len() {
            0 => zero(),               // empty sum = 0
            1 => new_terms[0].clone(), // a sum of just x = x
            _ => Sum(new_terms),
        };

        res
    }

    fn simplify_prod_terms(terms: impl Iterator<Item = &'b Expr<'a>>) -> Expr<'a> {
        Expr::simplify_simplified_prod_terms(terms.map(Expr::simplify))
    }

    fn simplify_simplified_prod_terms(terms: impl Iterator<Item = Expr<'a>>) -> Expr<'a> {
        use Expr::{Neg, Prod, Sum};

        let mut negatives = 0;

        let new_terms_iter = terms
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
            .filter(|term| *term != one())
            // Flatten
            .flat_map(|term| match term {
                Prod(terms) => terms,
                _ => std::slice::from_ref(&term).to_vec(),
            });

        // Collect terms, but stop early if we find a 0.
        // (Turns out rust seems to always give 0 as the size hint but there's usually at least 2
        // terms - this causes collect to allocate a Vec of length 1, then 2, then 4 which is
        // ineffiecient. It's unlikely that we'll get a product of more than 4 terms and
        // overestimating the size isn't really a problem so we'll allocate enough space for 4
        // terms to start with)
        let mut new_terms = Vec::with_capacity(new_terms_iter.size_hint().0.min(4));
        for term in new_terms_iter {
            if term == zero() {
                return zero();
            }
            new_terms.push(term);
        }

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
                let new_sum = sum_terms.into_iter().map(|term| {
                    let these_terms = new_terms.clone().into_iter();
                    let these_terms = these_terms.chain(iter::once(term));
                    let prod = Expr::simplify_simplified_prod_terms(these_terms);
                    if negatives % 2 == 1 {
                        Expr::simplify_simplified_neg_inner(prod)
                    } else {
                        prod
                    }
                });
                // Simplify the resulting sum
                return Expr::simplify_simplified_sum_terms(new_sum);
            }
        }

        // Cancel and calculate literals
        Self::simplify_terms_unsorted(Self::mul_simplify, &mut new_terms);
        new_terms.sort_unstable();

        // Unwrap the product if possible
        let new_expr = match new_terms.len() {
            0 => one(),                // An empty product = 1
            1 => new_terms[0].clone(), // A product of just x = x
            _ => Prod(new_terms),
        };

        if negatives % 2 == 1 {
            // Wrap the output in Neg if there were an odd number of negative terms.
            // Note that negative terms have all been converted to positive terms.
            Neg(Box::new(new_expr))
        } else {
            new_expr
        }
    }

    /// Tries `simplify` on all pairs of terms, modifying `terms` if a simplification can be made.
    ///
    /// `simplify` must be a simplifier. A simplifier is a function that takes a pair of
    /// expressions and tries to combine them in to one or cancel them.
    /// For example, a simplfier for Sum might combine x and -x to 0.
    /// If a simplifier returns Combine(expr), then expr takes the place of both the expressions that
    /// were passed to it (expr is only inserted once, but both expressions passed are removed).
    /// Otherwise, if Cancel is returned, both terms are removed and not replaces;
    /// otherwise, if None is returned, no change is made.
    ///
    /// A simplifier may assume that there are no nested Prod or Sums.
    ///
    /// This function assumes that there are no nested Prod or Sums (to allow simplifiers to make
    /// the same assumption).
    fn simplify_terms_unsorted(
        simplify: impl Fn(&Expr<'a>, &Expr<'a>) -> SimplifyResult<'a>,
        terms: &mut Vec<Expr<'a>>,
    ) {
        let mut i = 0;
        'outer: while i < terms.len() {
            // We have already checked this term with all previous terms, so we start at i+1
            let mut j = i + 1;
            while j < terms.len() {
                use SimplifyResult::{Cancel, Combine, None};
                match simplify(&terms[i], &terms[j]) {
                    // If no simplification was made, advance j
                    None => j += 1,

                    Combine(new_term) => {
                        // Make the simplification
                        terms[i] = new_term;
                        // Remove the furthest right term to reduce shifting.
                        // Maybe we should simplify right to left?
                        terms.remove(j);
                    }

                    Cancel => {
                        // Make sure to remove j first as removing i would change the position of j
                        terms.remove(j);
                        terms.remove(i);
                        continue 'outer;
                    }
                }
            }
            i += 1;
        }
    }

    /// Extracts a literal coefficient from this expression, or defaults to a coefficient of 1.
    /// For example,
    ///   2*x*y would yield (2, x*y),
    ///   5*x*1/y would yield (5, x*1/y),
    ///   x would yield (1, x),
    ///   -(2*x) would yield (-2, x).
    ///   5 would yield (5, [])
    ///
    /// This assumes that the terms in any products in self are sorted and that there are no nested
    /// products - these assumptions can be made in the context of a simplifier.
    fn get_number_and_term<'c>(&'c self) -> (Rational, &'c [Expr<'a>]) {
        use Expr::{Neg, Prod};
        match self {
            // Allow for negative coefficients
            Neg(inner_expr) => {
                let (n, terms) = inner_expr.get_number_and_term();
                (-n, terms)
            }

            // EXPR ORDER ASSUMED, ATOM ORDER ASSUMED
            // Since the terms within the product are sorted and a product cannot contain another
            // product (simplifiers are allowed to assume no nested products), the literal will be
            // the last item in the product.
            // Also, since literals are combined in products, there will only be 1 literal.
            Prod(terms) => terms
                .last()
                .and_then(|term| match term {
                    Expr::Atom(Atom::Literal(x)) => {
                        // This is x * (expr / x), i.e. x * (expr with x removed from the end)
                        Some((*x, &terms[..terms.len() - 1]))
                    }
                    _ => None,
                })
                // By default, it's just 1 * self
                .unwrap_or_else(|| (Rational::ONE, &terms)),

            Expr::Atom(Atom::Literal(x)) => (*x, &[]),

            _ => (Rational::ONE, std::slice::from_ref(self)),
        }
    }

    /// A simplifier that collects terms in addition.
    ///
    /// See also: simplify_terms
    fn add_collect(&self, other: &Expr<'a>) -> SimplifyResult<'a> {
        use SimplifyResult::{Cancel, Combine, None};

        let (n1, terms1) = self.get_number_and_term();
        let (n2, terms2) = other.get_number_and_term();

        // We can't collect terms if they aren't the same term
        if terms1 != terms2 {
            return None;
        }

        // terms == terms1 == terms2
        let terms = terms1;

        let n = n1 + n2;

        // Canceling
        if n == Rational::ZERO {
            return Cancel;
        }

        // If we have nothing in the product then we're just a literal
        if terms.len() == 0 {
            if n.sign() == Sign::NEGATIVE {
                return Combine(-Expr::literal(-n));
            }
            return Combine(Expr::literal(n));
        }

        // To stay simplified, we mustn't return with a 1 in the product.
        if n == Rational::ONE {
            // We should also not have products of 1 term
            if terms1.len() == 1 {
                return Combine(terms1[0].clone());
            }
            return Combine(Expr::Prod(terms1.to_vec()));
        } else if n == -Rational::ONE {
            // We should also not have products of 1 term
            if terms1.len() == 1 {
                return Combine(-terms1[0].clone());
            }
            return Combine(-Expr::Prod(terms1.to_vec()));
        }

        // The returned terms will be the terms of the term and the coefficient (which must be last
        // to keep it simplified)
        let mut new_terms = Vec::with_capacity(terms.len() + 1);
        new_terms.extend_from_slice(terms);

        if n.sign() != Sign::NEGATIVE {
            new_terms.push(Expr::literal(n));
            Combine(Expr::Prod(new_terms))
        } else {
            // Hoist negatives to the outside of the product
            new_terms.push(Expr::literal(-n));
            Combine(-Expr::Prod(new_terms))
        }
    }

    /// A simplifier for multiplication.
    ///
    /// See also: simplify_terms
    fn mul_simplify(&self, other: &Expr<'a>) -> SimplifyResult<'a> {
        use Expr::Recip;
        use SimplifyResult::{Cancel, Combine, None};
        match (self, other) {
            (Recip(recip_expr, _), expr) | (expr, Recip(recip_expr, _)) => {
                // (1/x) * x = 1
                // TODO Consider 0s.
                // I think we shouldn't allow a possibly 0 value in a denominator but we must make
                // sure of that.
                if **recip_expr == *expr {
                    Cancel
                } else {
                    None
                }
            }

            (Expr::Atom(Atom::Literal(x)), Expr::Atom(Atom::Literal(y))) => {
                let z = (*x) * (*y);
                if z == Rational::ONE {
                    Cancel
                } else {
                    Combine(Expr::literal(z))
                }
            }

            _ => None,
        }
    }

    /// Returns true iff self contains `x`
    pub(super) fn contains(&self, x: &Ident<'a>) -> bool {
        use Expr::{Neg, Prod, Recip, Sum};
        match self {
            Sum(terms) | Prod(terms) => terms.iter().find(|term| term.contains(x)).is_some(),
            Neg(term) | Recip(term, _) => term.contains(x),
            Expr::Atom(Atom::Literal(_)) => false,
            Expr::Atom(Atom::Named(y)) => x.eq(y),
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
    fn factor(&self, x: &Ident<'a>) -> Option<Expr<'a>> {
        use Expr::{Neg, Prod, Recip, Sum};

        match self {
            Sum(terms) => {
                let mut factored_terms = Vec::with_capacity(terms.len());
                // Call factor on each term of the sum, return None if one of the terms cannot be
                // factored.
                for term in terms {
                    factored_terms.push(term.factor(x)?);
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
                    match term.factor(x) {
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
                                .find(|term| term.contains(x))
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
            Neg(term) => Some(Neg(Box::new(term.factor(x)?))),

            // We can take the Recip factor out of a Recip
            Recip(term, _rounding) => {
                if term.contains(x) {
                    todo!()
                } else {
                    Some(self.clone())
                }
            }

            // An Atom can't be factored. Note that if expr is this Atom then it would have been
            // handled earlier.
            Expr::Atom(Atom::Named(y)) => {
                if y == x {
                    Some(one())
                } else {
                    None
                }
            }
            Expr::Atom(_) => None,
        }
    }

    /// Returns an Expr equivilent to that of Expr, but with only a single occurence of `expr`.
    /// This is done primerily by factorisation.
    /// If expr cannot be rewritten with only a single occurence of `expr` then None is returned.
    pub fn single_x(&self, x: &Ident<'a>) -> Option<Expr<'a>> {
        use Expr::{Neg, Prod, Recip, Sum};
        match self {
            Sum(terms) => {
                let mut x_terms = Vec::with_capacity(terms.len());
                let mut other_terms = Vec::with_capacity(terms.len());
                for term in terms {
                    if term.contains(x) {
                        x_terms.push(term.clone());
                    } else {
                        other_terms.push(term.clone());
                    }
                }
                if x_terms.len() == 0 {
                    None
                } else if x_terms.len() == 1 {
                    Some(Sum(vec![x_terms[0].single_x(x)?, Sum(other_terms)]))
                } else {
                    // So self = (x_terms) + (other_terms)
                    // Let's now try to take a factor of x out of x_terms to get
                    //    self = x*(factored_terms) + (other_terms)
                    let factored = Sum(x_terms).factor(x)?;
                    Some(Sum(vec![
                        Prod(vec![Expr::Atom(Atom::Named(x.clone())), factored]),
                        Sum(other_terms),
                    ]))
                }
            }

            Prod(terms) => {
                let mut new_terms = terms.clone();
                let mut found_x = false;
                for term in new_terms.iter_mut() {
                    if term.contains(x) {
                        if found_x {
                            return None;
                        }
                        found_x = true;
                        *term = term.single_x(x)?;
                    }
                }
                if found_x {
                    Some(Prod(new_terms))
                } else {
                    None
                }
            }

            Neg(term) => Some(Neg(Box::new(term.single_x(x)?))),
            Recip(term, rounding) => Some(Recip(Box::new(term.single_x(x)?), *rounding)),

            Expr::Atom(Atom::Named(y)) => {
                if y == x {
                    Some(self.clone())
                } else {
                    None
                }
            }
            Expr::Atom(Atom::Literal(_)) => None,
        }
    }

    /// Calls cb with each of the variables in self.
    /// This will include duplicates.
    /// Use `self.variables` if you don't want duplicates.
    pub fn variables_duped_cb(&self, cb: &mut impl FnMut(Ident<'a>) -> ()) {
        match self {
            Expr::Neg(inner_expr) | Expr::Recip(inner_expr, _) => inner_expr.variables_duped_cb(cb),
            Expr::Sum(terms) | Expr::Prod(terms) => {
                for term in terms {
                    term.variables_duped_cb(cb);
                }
            }
            Expr::Atom(Atom::Named(x)) => cb(x.clone()),
            Expr::Atom(Atom::Literal(_)) => (),
        }
    }

    /// Returns a list of named atoms within self. Duplicates are removed.
    pub fn variables(&self) -> Vec<Ident<'a>> {
        let mut vars = Vec::with_capacity(4);
        self.variables_duped_cb(&mut |var| vars.push(var));
        vars.sort_unstable();
        vars.dedup();
        vars
    }

    /// Substitute `x` with `with` in self and return the result.
    pub fn substitute(&self, x: &Ident<'a>, with: &Expr<'a>) -> Expr<'a> {
        match self {
            Expr::Atom(Atom::Named(y)) => {
                if x == y {
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

    /// Perform an atomic substitution of a group, replacing each occurence of the identifiers with
    /// the paired expression.
    pub fn substitute_all(&self, subs: &[(&Ident<'a>, &Expr<'a>)]) -> Expr<'a> {
        match self {
            Expr::Atom(Atom::Named(x)) => match subs.iter().find(|(id, _)| id == &x) {
                Some((_, expr)) => <Expr as Clone>::clone(expr),
                None => self.clone(),
            },
            Expr::Atom(Atom::Literal(_)) => self.clone(),
            Expr::Sum(terms) => {
                Expr::Sum(terms.iter().map(|term| term.substitute_all(subs)).collect())
            }
            Expr::Prod(terms) => {
                Expr::Prod(terms.iter().map(|term| term.substitute_all(subs)).collect())
            }

            Expr::Neg(term) => Expr::Neg(Box::new(term.substitute_all(subs))),
            Expr::Recip(term, rounding) => {
                Expr::Recip(Box::new(term.substitute_all(subs)), *rounding)
            }
        }
    }

    /// Tries to evaluate self.
    /// This requires all atoms to be literals - None will be returned if this is not the case.
    /// It also assumes self is simplified. The behaviour of eval is undefined if the expression is
    /// not simplified.
    pub fn eval(&self) -> Option<EvalInt> {
        self.eval_rat().map(Rational::eval_floor)
    }

    /// This is an extension of `eval`. See there for the main documentation.
    /// This evalautes the expression and returns the Rational value rather than an EvalInt.
    pub fn eval_rat(&self) -> Option<Rational> {
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

    /// Returns an i8 with the same sign as the expression or None if this can't be determined.
    pub fn sign(&self, named_sign: impl Fn(&Ident<'a>) -> Sign + Copy) -> Sign {
        match self {
            Expr::Neg(inner) => -inner.sign(named_sign),
            Expr::Recip(inner, _) => inner.sign(named_sign),

            Expr::Prod(terms) => terms
                .iter()
                .map(|term| term.sign(named_sign))
                .fold(Sign::POSITIVE, std::ops::Mul::mul),

            // 0 signs do not effect the sign of a sum.
            // Otherwise, a sum has a sign of 1 iff all its terms have a sign of 1;
            // likewise, a sum has a sign of -1 iff all its terms have a sign of -1.
            Expr::Sum(terms) => terms
                .iter()
                .map(|term| term.sign(named_sign))
                .fold(Sign::ZERO, std::ops::Add::add),

            Expr::Atom(Atom::Literal(x)) => x.sign(),
            Expr::Atom(Atom::Named(x)) => named_sign(x),
        }
    }
}

impl<'a> From<&ast::proof::Expr<'a>> for Expr<'a> {
    fn from(ast_expr: &ast::proof::Expr<'a>) -> Expr<'a> {
        use ast::proof::ArithOp as Op;
        use ast::proof::ExprKind::{Compound, Literal, Malformed, Named};
        match &ast_expr.kind {
            Named(ident) => Expr::Atom(Atom::Named(ident.clone())),
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

impl<'a> From<Ident<'a>> for Expr<'a> {
    fn from(ident: Ident<'a>) -> Self {
        Expr::Atom(Atom::Named(ident))
    }
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
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

// A marker type for recording whether an expression is within a product
type InProd = bool;

impl<'a> PrettyFormat<InProd> for Expr<'a> {
    fn pretty_format(&self, f: &mut Formatter, file_str: &str, in_prod: &InProd) -> fmt::Result {
        use Expr::{Atom, Neg, Prod, Recip, Sum};

        match self {
            Atom(atom) => atom.pretty_format(f, file_str, in_prod),
            Neg(expr) => match expr.deref() {
                Sum(_) => write!(f, "-({})", expr.pretty(file_str, false)),
                _ => write!(f, "-{}", expr.pretty(file_str, true)),
            },
            Recip(expr, _) => match expr.deref() {
                Atom(_) => write!(f, "1/{}", expr.pretty(file_str, true)),
                _ => write!(f, "1/({})", expr.pretty(file_str, false)),
            },
            Sum(terms) => write!(
                f,
                "{}",
                terms
                    .iter()
                    .map(|term| format!("{}", term.pretty(file_str, false)))
                    .collect::<Vec<_>>()
                    .join(" + ")
            ),
            Prod(terms) => write!(
                f,
                "{}",
                terms
                    .iter()
                    .map(|term| match term {
                        Sum(_) => format!("({})", term.pretty(file_str, true)),
                        _ => format!("{}", term.pretty(file_str, true)),
                    })
                    .collect::<Vec<_>>()
                    .join("*")
            ),
        }
    }
}

impl<'a> Display for Atom<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Atom::Named(ident) => write!(f, "{}", ident.name),
            Atom::Literal(x) => write!(f, "{}", x),
        }
    }
}

impl<'a> PrettyFormat<InProd> for Atom<'a> {
    fn pretty_format(&self, f: &mut Formatter, file_str: &str, in_prod: &InProd) -> fmt::Result {
        use crate::ast::{ExprKind, IdentSource};
        match self {
            Atom::Named(ident) => {
                let ex_kind = match &ident.source {
                    IdentSource::Token(_) => None,
                    IdentSource::RefExpr(ex) => Some(&ex.kind),
                    IdentSource::Expr(ex) => Some(&ex.kind),
                };

                let raw = &file_str[ident.node().byte_range()];

                match ex_kind {
                    None | Some(ExprKind::Named(_)) | Some(ExprKind::Num(_)) => {
                        write!(f, "{}", raw)
                    }
                    _ if !in_prod => write!(f, "{}", raw),
                    _ => write!(f, "({})", raw),
                }
            }
            Atom::Literal(x) => write!(f, "{}", x),
        }
    }
}
