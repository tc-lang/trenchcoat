//! Terms, primarily used in the graph-based proving algorithm

use super::bound::RelationKind;
use super::expr::{self, Expr};
use super::int::Int;
use super::Requirement;
use gcd::Gcd;

/// A term defined as the product of variables with a coefficient, e.g. 2*x*y, or -4*z
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Term {
    /// The variables in the product of the term
    pub vars: Vec<String>,
    /// The coefficient on the product of variables
    pub coef: i128,
}

impl Term {
    /// Simplifies an expression (as given by ast::proof) into a sorted list of terms, plus any
    /// constants (2nd element) and a term to multiply the entire right-hand side by, if any exists
    /// (3rd element)
    ///
    /// Note that this expands products, so `x*(1 + y)` will become `x*y + x`
    pub fn simplify_to_lists<'a>(expr: Expr<'a>) -> (Vec<Term>, i128, Option<Expr<'a>>) {
        // Our general strategy here is to call this recursively, distributing out multiplication
        // and using addition to join lists, as those are fundamentally the only two operations we
        // need to do

        use expr::Atom::{Literal, Named};
        use Expr::{Atom, Neg, Prod, Recip, Sum};
        use Int::{Infinity, NegInfinity};

        match expr {
            Atom(Named(ident)) => (vec![Term::single_var(ident.name.into())], 0, None),
            Atom(Literal(Int::I(i))) => (vec![], i, None),
            Atom(Literal(Infinity)) | Atom(Literal(NegInfinity)) => {
                panic!("Infinite integer literals are disallowed");
            }
            // ---
            Recip(expr) => (vec![], 1, Some(*expr)),
            // ---
            Neg(expr) => {
                let ex = Prod(vec![*expr, Atom(Literal(Int::I(-1)))]);
                Term::simplify_to_lists(ex)
            }
            // ---
            // With sums, there's a small amount of complex logic required, so we'll only do that
            // on pairs of sums - as such, we'll convert len > 2 into a combination in terms of len
            // equal to 2. The other cases (len = 0 and len = 1) are simple to handle, so we do
            // those explicitly as well.
            Sum(exs) if exs.len() == 0 => (vec![], 0, None),
            Sum(mut exs) if exs.len() == 1 => Term::simplify_to_lists(exs.remove(0)),
            Sum(mut exs) if exs.len() != 2 => {
                let head = exs.remove(0);
                Term::simplify_to_lists(Sum(vec![head, Sum(exs)]))
            }
            // len() == 2:
            // This is the only complex case that is handled, and it is mostly dispatched to a
            // separate function
            Sum(mut exprs) => {
                let rhs = Term::simplify_to_lists(exprs.remove(1));
                let lhs = Term::simplify_to_lists(exprs.remove(0));

                Term::add_join(lhs, rhs)
            }
            // ---
            // Just like sums, we'll only really handle len = 2 for products
            Prod(exs) if exs.len() == 0 => (vec![], 1, None),
            Prod(mut exs) if exs.len() == 1 => Term::simplify_to_lists(exs.remove(0)),
            Prod(mut exs) if exs.len() != 2 => {
                let head = exs.remove(0);
                Term::simplify_to_lists(Prod(vec![head, Prod(exs)]))
            }
            // len == 2:
            Prod(mut exprs) => {
                // Essentially: exprs[0] * exprs[1]
                //          ==>     lhs  *  rhs

                // lhs_mul_expr is the left-hand side's contribution to whatever expression
                // should be cascaded up and have everything else multiplied by
                let (lhs, lhs_const, lhs_mul_expr) = Term::simplify_to_lists(exprs.remove(0));
                let (terms, constant, rhs_mul_expr) =
                    Term::mul_set_by_expr(lhs, lhs_const, exprs.remove(0));

                let aggregate = match (lhs_mul_expr, rhs_mul_expr) {
                    (Some(ex), None) | (None, Some(ex)) => Some(ex.clone()),
                    (None, None) => None,
                    (Some(l), Some(r)) => Some(Prod(vec![l, r])),
                };

                (terms, constant, aggregate)
            }
        }
    }

    /// Groups two sides of expressions of the form Term* + C, where the other side mulitplied by
    /// *_mul - e.g. the right-hand side should be multiplied by lhs_mul. The aggregate expression
    /// from base required multiplications is returned
    ///
    /// The returned values are (in order) the left-hand side terms + constant, then right-hand
    /// side terms + constant, then aggregate required multiplication.
    fn multiply_sides<'a>(
        lhs: (Vec<Term>, i128, Option<Expr<'a>>),
        rhs: (Vec<Term>, i128, Option<Expr<'a>>),
    ) -> (Vec<Term>, i128, Vec<Term>, i128, Option<Expr<'a>>) {
        let (mut lhs, mut lhs_const, mut lhs_mul) = lhs;
        let (mut rhs, mut rhs_const, mut rhs_mul) = rhs;

        let aggregate = match (&lhs_mul, &rhs_mul) {
            (Some(ex), None) | (None, Some(ex)) => Some(ex.clone()),
            (None, None) => None,
            (Some(l), Some(r)) => Some(Expr::Prod(vec![l.clone(), r.clone()])),
        };

        macro_rules! handle_mul {
            ($cur_side:ident, $cur_const:ident, $cur_mul:ident * $other_mul:ident) => {
                if let Some(expr) = $other_mul.as_ref().cloned() {
                    let (new_side, new_const, new_mul) =
                        Term::mul_set_by_expr($cur_side, $cur_const, expr);
                    $cur_side = new_side;
                    $cur_const = new_const;

                    $cur_mul = match ($cur_mul, new_mul) {
                        (Some(ex), None) | (None, Some(ex)) => Some(ex.clone()),
                        (None, None) => None,
                        (Some(l), Some(r)) => Some(Expr::Prod(vec![l.clone(), r.clone()])),
                    };
                }

                $other_mul = None
            };
        }

        let mut current_left = true;
        while lhs_mul.is_some() || rhs_mul.is_some() {
            if current_left {
                handle_mul!(lhs, lhs_const, lhs_mul * rhs_mul);
            } else {
                handle_mul!(rhs, rhs_const, rhs_mul * lhs_mul);
            }

            current_left = !current_left;
        }

        (lhs, lhs_const, rhs, rhs_const, aggregate)
    }

    /// returns the new terms, in addition to any constants generated and an expression to multiply
    /// everything else by
    fn mul_set_by_expr<'a>(
        mut terms: Vec<Term>,
        mut constant: i128,
        expr: Expr<'a>,
    ) -> (Vec<Term>, i128, Option<Expr<'a>>) {
        // Each of the terms are multiplied by the expression
        //
        // There are a few different options here.
        //
        // For literals or named values, we only need to multiply those out through all terms -
        // this is fairly trivial.
        //
        // For other types of expressions, there are a few cases:
        // * Sums can be split, so that we clone the set of terms and call this function again with
        //   the two different parts of the sum
        // * If the expression is a product, we can just do each component of the product in
        //   sequence, via repeated calls to this function.

        use expr::Atom::{Literal, Named};
        use Expr::{Atom, Neg, Prod, Recip, Sum};
        use Int::{Infinity, NegInfinity};

        match expr {
            Atom(Named(ident)) => {
                let var: String = ident.name.into();

                // Add the name to all terms, keeping them sorted, and then sort all terms
                for t in terms.iter_mut() {
                    let idx = t.vars.binary_search(&var).unwrap_or_else(|i| i);
                    t.vars.insert(idx, var.clone());
                }

                // Add the individual term corresponding to multiplying by the constant
                //
                // Because the terms are sorted lexicographically by the variables, we know that
                // it's *still* sorted. As such, when add a new term, we can preserve this fact by
                // inserting in the right place.
                if constant != 0 {
                    let term = Term {
                        vars: vec![var.clone()],
                        coef: constant,
                    };

                    let idx = terms.binary_search(&term).unwrap_or_else(|i| i);
                    terms.insert(idx, term);
                }

                // Everything has been merged into the list of terms, so we're done
                (terms, 0, None)
            }
            Atom(Literal(Int::I(i))) => {
                // Multiply each of the terms and return.
                //
                // We know that they'll still be sorted because the implementation of Ord for Term
                // is first based on the comparing variables, and we're guaranteed to have no
                // duplicate terms having the same variables but different coefficients.
                terms.iter_mut().for_each(|t| t.coef *= i);
                (terms, constant * i, None)
            }
            Atom(Literal(Infinity)) | Atom(Literal(NegInfinity)) => {
                panic!("Infinite integer literals are disallowed");
            }
            // ---
            Recip(expr) => (terms, constant, Some(*expr)),
            // ---
            Neg(expr) => {
                let ex = Prod(vec![*expr, Atom(Literal(Int::I(-1)))]);
                Term::mul_set_by_expr(terms, constant, ex)
            }
            // ---
            Sum(exs) if exs.len() == 0 => (vec![], 0, None),
            Sum(mut exs) if exs.len() == 1 => Term::mul_set_by_expr(terms, constant, exs.remove(0)),
            Sum(mut exs) => {
                // A*(x + y + ...) = A*(x + (y + ...))
                //                 = A*x + A*(y + ...)
                let head = exs.remove(0);
                let lhs = Term::mul_set_by_expr(terms.clone(), constant, head);
                let rhs = Term::mul_set_by_expr(terms, constant, Sum(exs));
                Term::add_join(lhs, rhs)
            }
            // ---
            Prod(exs) if exs.len() == 0 => (terms, constant, None),
            Prod(mut exs) if exs.len() == 1 => {
                Term::mul_set_by_expr(terms, constant, exs.remove(0))
            }
            Prod(exs) => {
                let mut agg = None;
                for expr in exs {
                    let (ts, cs, ag) = Term::mul_set_by_expr(terms, constant, expr);
                    terms = ts;
                    constant = cs;
                    agg = match (agg, ag) {
                        (Some(ex), None) | (None, Some(ex)) => Some(ex),
                        (None, None) => None,
                        (Some(Prod(mut es)), Some(r)) => {
                            es.push(r);
                            Some(Prod(es))
                        }
                        (Some(l), Some(r)) => Some(Prod(vec![l, r])),
                    };
                }
                (terms, constant, agg)
            }
        }
    }

    fn add_join<'a>(
        lhs: (Vec<Term>, i128, Option<Expr<'a>>),
        rhs: (Vec<Term>, i128, Option<Expr<'a>>),
    ) -> (Vec<Term>, i128, Option<Expr<'a>>) {
        let (mut lhs, lhs_const, rhs, rhs_const, aggregate) = Term::multiply_sides(lhs, rhs);

        // Insert the elements of rhs into lhs, grouping like terms
        for term in rhs {
            match lhs.binary_search_by_key(&&term.vars, |t| &t.vars) {
                Ok(i) => {
                    lhs[i].coef += term.coef;
                    if lhs[i].coef == 0 {
                        lhs.remove(i);
                    }
                }
                Err(i) => lhs.insert(i, term),
            }
        }

        (lhs, lhs_const + rhs_const, aggregate)
    }

    /// A helper constructor for syntactical ease in a couple places
    fn single_var(name: String) -> Term {
        Term {
            vars: vec![name],
            coef: 1,
        }
    }

    /// A helper function for dividing a set of terms by their greatest common divisor, returning
    /// that value and the updated terms
    ///
    /// If the list of terms is empty, the returned gcd will be one.
    pub fn div_gcd(mut terms: Vec<Term>) -> (Vec<Term>, u128) {
        if terms.is_empty() {
            return (terms, 1);
        }

        fn abs(x: i128) -> u128 {
            x.abs() as u128
        }

        let gcd = terms[1..]
            .iter()
            .map(|t| t.coef)
            .map(abs)
            .fold(abs(terms[0].coef), Gcd::gcd);

        for t in terms.iter_mut() {
            t.coef /= gcd as i128;
        }

        (terms, gcd)
    }
}

/// Represents an inequality of the form `φ ≤ Γ + C`, where `φ` and `Γ` are defined by a sum of
/// terms (where each term is composed of at least one variable) and `C` is an integer constant.
#[derive(Debug, Clone)]
pub struct Inequality {
    /// Equivalent to `φ` from above. These are sorted and simplified
    pub lhs: Vec<Term>,
    /// Equivalent to `Γ` from above
    pub rhs: Vec<Term>,
    /// The constant term (`C`) from above
    pub constant: i128,
}

impl Inequality {
    pub fn from_req<'a>(req: Requirement<'a>) -> (Inequality, Option<Expr<'a>>) {
        let req = req.0;
        // Re-order the sides so that we get our condition in terms of A <= B.
        // Shifting is not currently used, but will be (eventually) to account for
        // conditions using strict inequality (i.e. x < y instead of x <= y).
        //
        // The shift amount is the value added to the constant term in the inequality to adjust for
        // the conversion between `<` and `<=`.
        let (lhs, rhs, shift) = match req.relation {
            RelationKind::Le => (req.left, req.right, 0),
            RelationKind::Ge => (req.right, req.left, 0),
        };

        // Redefine lhs and rhs to get them as a sorted list of terms and any additional constant
        // term (both `lhs` and `rhs` are triples).
        let lhs = Term::simplify_to_lists(lhs);
        let rhs = Term::simplify_to_lists(rhs);

        let (lhs, lhs_shift, rhs, rhs_shift, aggregate) = Term::multiply_sides(lhs, rhs);

        let ineq = Inequality {
            lhs,
            rhs,
            constant: shift - lhs_shift + rhs_shift,
        };

        (ineq, aggregate)
    }

    /// Returns two things:
    ///  1. The original requirement, now as an inequality (per `from_req`), and
    ///  2. The stack of inequalities whose signs must be established to determine the direction of
    ///     the initial inequaltiy.
    ///
    /// This is because generating an `Inequality` from a `Requirement` may sometimes involve
    /// multiplying out denominators - this is to be expected. When those denominators are
    /// negative, however, we must flip the sides of the inequality. Without additional context, we
    /// have no way of determining what the sign of the denominators are in the general case, so we
    /// return a stack of inequalities satisfying the following:
    ///
    ///   The true parity of the original inequality is given by the overall parity of the
    ///   inequalities in the stack - i.e. if an odd number of inequalities in the stack are
    ///   negative, so too will be the original one.
    ///
    ///   Note that sign changes propagate back through the stack, so that the sign of an
    ///   inequality should be given by the same rule as above. This is typically calculated by
    ///   going backwards through the inequality and tracking a single `negated` value.
    ///
    /// For more information, see the `establish_stack` method on `graph::Prover`, which uses the
    /// stack given by this function.
    pub fn make_stack(req: Requirement) -> (Inequality, Vec<Inequality>) {
        let (ineq, mut agg) = Inequality::from_req(req);
        let mut stack: Vec<Inequality> = vec![];

        // Expand out all of the expressions into the stack
        while let Some(ex) = agg {
            let (terms, constant, aggregate) = Term::simplify_to_lists(ex);
            agg = aggregate;
            // We want to add the inequality that the terms are >= 0, so:
            //   terms >= 0  ==>  0 <= terms
            // so the terms go on the right-hand side, with nothing on the left.
            stack.push(Inequality {
                lhs: vec![],
                rhs: terms,
                constant,
            });
        }

        (ineq, stack)
    }

    /// Negates the inequality by swapping the left- and right-hand sides, leaving the constant
    /// unchanged.
    pub fn negate(mut self) -> Inequality {
        std::mem::swap(&mut self.lhs, &mut self.rhs);
        self
    }
}
