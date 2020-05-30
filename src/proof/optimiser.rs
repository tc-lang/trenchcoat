use super::ast::Ident;
use super::expr::{Atom, Expr};
use super::int::Int;
use super::Bound;
use std::iter::Iterator;

// TODO These types can probably be created with a macro to remove duplication.
//
// TODO Since we assume that expressions and bounds are given to the `new` functions simplified,
// perhaps we don't make that assumption and instead simplify them then. This would perhaps be less
// efficient but make mistakes less likely. (Wouldn't attributes for this be so nice? We could
// consider adding a phantom type to Expr and Bound also to garentee this.)

/// Minimizer is a type for generating upper bounds on an expression, given a set of requirements.
/// It can be constructed with `Minimizer::new`, see that documentation for more details.
pub struct Minimizer<'a> {
    /// The expression to find bounds on
    /// This must be simplified.
    solving: Expr<'a>,
    /// The variables in `solving` (as returned by `solving.variables()`
    vars: Vec<Ident<'a>>,
    /// The bounds we can assume to be true. Probably given by the function requirements/lemmas.
    given: Vec<(Ident<'a>, Bound<'a>)>,
    /// The index of the next substitution to make.
    i: usize,
    /// The maximum number of childeren, equivilent to the number of substitutions that will be
    /// made.
    max_depth: usize,
    /// An optional current child. This will be a minimizer created from making a substitution.
    child: Option<Box<Minimizer<'a>>>,
}

/// Maximizer is a type for generating lower bounds on an expression, given a set of requirements.
/// It can be constructed with `Maximizer::new`, see that documentation for more details.
pub struct Maximizer<'a> {
    /// For field documentation, see Minimizer.
    /// Note that expressions and bounds must be simplified.
    solving: Expr<'a>,
    vars: Vec<Ident<'a>>,
    given: Vec<(Ident<'a>, Bound<'a>)>,
    i: usize,
    max_depth: usize,
    child: Option<Box<Maximizer<'a>>>,
}

impl<'a> Minimizer<'a> {
    /// Returns a minimizer for `solve`.
    /// This minimizer will, using the known bounds given by `given`, iterate through expressions
    /// such that `solve` <= `expr` for any valid values of named atoms.
    /// The resulting expressions will have varying degrees of tightness.
    /// The iterator ends when no more bounds are available.
    ///
    /// The expression and bounds given are assumed to be simplified.
    ///
    /// The minimizer will make at most `max_depth` substitutions.
    /// This makes the worst case time complexity to generate all the bounds from the iterator:
    /// `n(n-1)...(n-(max_depth-1)) <= n^max_depth`
    /// Where `n = given.len()` although in almost all cases it will not be this bad since not all
    /// substitutions can be made at each stage. Also, the iterator will likely not be fully
    /// consumed.
    pub fn new(
        given: Vec<(Ident<'a>, Bound<'a>)>,
        solve: Expr<'a>,
        max_depth: usize,
    ) -> Minimizer<'a> {
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
    /// Returns a maximizer for `solve`.
    /// This maximizer will, using the known bounds given by `given`, iterate through expressions
    /// such that `solve` >= `expr` for any valid values of named atoms.
    /// The resulting expressions will have varying degrees of tightness.
    /// The iterator ends when no more bounds are available.
    ///
    /// The expression and bounds given are assumed to be simplified.
    ///
    /// The maximizer will make at most `max_depth` substitutions.
    /// This makes the worst case time complexity to generate all the bounds from the iterator:
    /// `n(n-1)...(n-(max_depth-1)) <= n^max_depth`
    /// Where `n = given.len()` although in almost all cases it will not be this bad since not all
    /// substitutions can be made at each stage. Also, the iterator will likely not be fully
    /// consumed.
    pub fn new(
        given: Vec<(Ident<'a>, Bound<'a>)>,
        solve: Expr<'a>,
        max_depth: usize,
    ) -> Maximizer<'a> {
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

/// Used to construct the body of the Iterator next method for Minimizer and Maximizer.
macro_rules! optimizer_next_body {
    ($self:expr) => {{
        // First, if we have a child, we want to iterate all the way through it.
        if let Some(child) = &mut $self.child {
            match child.next() {
                Some(x) => return Some(x),
                None => (),
            }
        }

        // If we've reached the maximum depth, we should not continue.
        if $self.max_depth == 0 {
            return None;
        }

        // Now we want to make another substitution.
        // We will find a variable with a bound that we can use.
        let (x, bound) = loop {
            // If there are no more substitutions to make, we can finish.
            // To do this, we'll mark this as the final child (see the early return case above) and
            // return the current expression since it is a bound of itself.
            if $self.i >= $self.given.len() {
                $self.max_depth = 0;
                return Some($self.solving.clone());
            }

            // Get the identity and the bound
            let (x_ident, bound) = &$self.given[$self.i];

            // We only need to make a substitution if the expression contains the variable.
            if $self.vars.contains(x_ident) {
                break (Expr::Atom(Atom::Named(*x_ident)), bound);
            }
            $self.i += 1;
        };

        // The child should not make the same substitution again.
        let mut new_given = $self.given.clone();
        new_given.remove($self.i);

        $self.i += 1;

        // Create the new child
        $self.child = Some(Box::new(Self::new(
            new_given,
            Self::sub_bound(&$self.solving, &x, bound).simplify(), // .simplify is important here
            $self.max_depth - 1,
        )));

        $self.next()
    }};
}

impl<'a> Iterator for Minimizer<'a> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        optimizer_next_body!(self)
    }
}
impl<'a> Iterator for Maximizer<'a> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        optimizer_next_body!(self)
    }
}

fn sub_bound_into<'a>(
    expr: &Expr<'a>,
    x: &Expr<'a>,
    bound: &Bound<'a>,
    self_sub: impl Fn(&Expr<'a>, &Expr<'a>, &Bound<'a>) -> Expr<'a>,
    sub_opposite: impl Fn(&Expr<'a>, &Expr<'a>, &Bound<'a>) -> Expr<'a>,
) -> Expr<'a> {
    match expr {
        // An atom has a fixed value if it was not `x`
        Expr::Atom(_) => expr.clone(),

        // An upper bound for -(...) is -(a lower bound for ...)
        Expr::Neg(inner_expr) => Expr::Neg(Box::new(sub_opposite(inner_expr, x, bound))),
        // An upper bound for 1/(...) is 1/(a lower bound for ...)
        Expr::Recip(inner_expr) => Expr::Recip(Box::new(sub_opposite(inner_expr, x, bound))),

        // A bound on a sum is the sum of the bounds of its terms.
        Expr::Sum(terms) => Expr::Sum(terms.iter().map(|term| self_sub(term, x, bound)).collect()),

        Expr::Prod(terms) => {
            // We now want to minimize a product, for now, we will only simplify products in
            // the form: [expr]*literal0*literal1*... (the other expression is optional)
            // Where all the literals are non-negative.
            // Since the expression is simplified we are allowed to assume that all literals
            // are non-negative and that literals are the last terms.
            // EXPR ORDER ASSUMED, ATOM ORDER ASSUMED
            //
            // It is clear that the optimum of an expression with this form is
            // optimum(expr)*literal0*literal1*...
            //
            // Other forms would be more complex.

            let mut out = Vec::with_capacity(terms.len());
            for i in 0..terms.len() {
                let term = &terms[i];
                out.push(match term {
                    // We will just copy literals.
                    // Note that we require only positive literals (which we should have if the
                    // expression is simplified).
                    Expr::Atom(Atom::Literal(x)) => {
                        if *x < Int::ZERO {
                            panic!("literal < 0")
                        } else {
                            term.clone()
                        }
                    }

                    _ => {
                        // Only optimise if it's the first term.
                        // Any subsequent terms MUST be literals.
                        // (Also note that the first term cannot be a literal if another kind
                        // of expression exists since the bound expression is simplified so literals
                        // will be the last terms in the product).
                        if i == 0 {
                            self_sub(term, x, bound)
                        } else {
                            todo!()
                        }
                    }
                });
            }
            Expr::Prod(out)
        }
    }
}

impl<'a> Minimizer<'a> {
    /// Not yet used
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

    /// Returns an upper bound on `expr` given a bound on `x`.
    /// This is done by making all apropriate substitutions.
    /// Note that the outputted expression isn't garenteed to be simplified.
    fn sub_bound(expr: &Expr<'a>, x: &Expr<'a>, bound: &Bound<'a>) -> Expr<'a> {
        // If the expression is x, then an upper bound is given directly.
        if expr.eq(x) {
            return match bound {
                Bound::Ge(bound_expr) => bound_expr.clone(),
                Bound::Le(_) => expr.clone(),
            };
        }
        sub_bound_into(expr, x, bound, Minimizer::sub_bound, Maximizer::sub_bound)
    }
}

impl<'a> Maximizer<'a> {
    /// Not yet used
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

    /// Returns a lower bound on `expr` given a bound on `x`.
    /// This is done by making all apropriate substitutions.
    /// Note that the outputted expression isn't garenteed to be simplified.
    fn sub_bound(expr: &Expr<'a>, x: &Expr<'a>, bound: &Bound<'a>) -> Expr<'a> {
        if expr.eq(x) {
            return match bound {
                Bound::Le(bound_expr) => bound_expr.clone(),
                Bound::Ge(_) => expr.clone(),
            };
        }
        sub_bound_into(expr, x, bound, Maximizer::sub_bound, Minimizer::sub_bound)
    }
}
