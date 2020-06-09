use super::ast::Ident;
use super::bound::{Bound, DescriptiveBound, Relation, RelationKind};
use super::bound_group::{BoundGroup, BoundRef, RequirementRef};
use super::expr::{self, Atom, Expr};
use super::int::{Int, Rational};
use std::iter::Iterator;

// TODO These types can probably be created with a macro to remove duplication.
//
// TODO Since we assume that expressions and bounds are given to the `new` functions simplified,
// perhaps we don't make that assumption and instead simplify them then. This would perhaps be less
// efficient but make mistakes less likely. (Wouldn't attributes for this be so nice? We could
// consider adding a phantom type to Expr and Bound also to garentee this.)

/// Minimizer is a type for generating lower bounds on an expression, given a set of requirements.
/// It can be constructed with `Minimizer::new`, see that documentation for more details.
///
/// Note that upper bounds should be rounded up when evaluated.
/// Rounding down will not lead to incorrect behaviour but can lead to loose bounds.
/// This is the behaviur of the int_bounds() method.
pub struct Minimizer<'a> {
    /// The expression to find bounds on
    /// This must be simplified.
    solving: Expr<'a>,
    /// The variables in `solving` (as returned by `solving.variables()`)
    /// Stored for fast lookup.
    vars: Vec<Ident<'a>>,

    /// The BoundGroup of the requirements that are assumed to be true.
    given: BoundGroup<'a>,
    /// A map of requirement id (from given) to whether or not a substitution had already been made
    /// from the requirement.
    tried: Vec<bool>,

    /// The permutation group that this node is permuting.
    /// None if this is a final node.
    permutation_group: Option<Vec<(DescriptiveBound<'a>, usize)>>,
    /// The index of the next bound in permutation_group to try and substitute.
    group_idx: usize,

    /// The maximum number of childeren.
    max_depth: usize,
    /// An optional current child. This will be a minimizer created from making a substitution.
    child: Option<Box<Minimizer<'a>>>,
}

/// Maximizer is a type for generating upper bounds on an expression, given a set of requirements.
/// It can be constructed with `Maximizer::new`, see that documentation for more details.
///
/// Note that lower bounds should be down up when evaluated.
/// This is the behaviur of the int_bounds() method.
pub struct Maximizer<'a> {
    solving: Expr<'a>,
    vars: Vec<Ident<'a>>,
    given: BoundGroup<'a>,
    tried: Vec<bool>,
    permutation_group: Option<Vec<(DescriptiveBound<'a>, usize)>>,
    group_idx: usize,
    max_depth: usize,
    child: Option<Box<Maximizer<'a>>>,
}

impl<'a: 'b, 'b> Minimizer<'a> {
    /// Returns a minimizer for `solve`.
    /// This minimizer will, using the known bounds given by `given`, iterate through expressions
    /// such that `solve` >= `expr` for any valid values of named atoms.
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
        solve: Expr<'a>,
        given: BoundGroup<'a>,
        tried: Vec<bool>,
        max_depth: usize,
    ) -> Minimizer<'a> {
        let vars = solve.variables();
        Minimizer {
            solving: solve,
            vars,
            given,
            tried,
            permutation_group: None,
            group_idx: 0,
            max_depth,
            child: None,
        }
    }

    pub fn new_root(solve: Expr<'a>, given: BoundGroup<'a>, max_depth: usize) -> Minimizer<'a> {
        // `tried` is initialized with every element false.
        let max_req_id = given.max_requirement_id();
        Self::new(solve, given, vec![false; max_req_id], max_depth)
    }

    /// Returns an iterator of evaluated bounds.
    /// So `solve >= x` for all x generated by this integer.
    pub fn int_bounds(
        self,
    ) -> std::iter::FilterMap<Self, fn(Expr<'a>) -> std::option::Option<Int>> {
        self.filter_map(|expr| Some(expr.eval()?.as_lower_bound()))
    }

    fn find_permutation_group(&mut self) {
        // Find the permutation group of the first bound that we've not yet subbed.
        self.permutation_group = self
            .given
            .iter()
            // BoundRef -> (BoundRef, requirement ID)
            .map(|bound| (bound, bound.requirement().unwrap().id()))
            // Filter requirements we've already used
            .filter(|(_, req)| !self.tried[*req])
            // (BoundRef, req ID) -> (BoundRef, subbed and simplified Expr, req ID)
            .filter_map(|(bound, req)| {
                Some((
                    bound,
                    Self::sub_bound(&self.solving, &*bound)?.simplify(),
                    req,
                ))
            })
            // Filter out subs that have no effect on the expression
            .filter(|(_, expr, _)| *expr != self.solving)
            .map(|(bound, _, _)| bound.permutation_group())
            .next()
            .map(|perm_grp| {
                perm_grp
                    .iter()
                    .map(|bound| ((**bound).clone(), bound.requirement().unwrap().id()))
                    .collect()
            });
    }
}

impl<'a: 'b, 'b> Maximizer<'a> {
    /// Returns a maximizer for `solve`.
    /// This maximizer will, using the known bounds given by `given`, iterate through expressions
    /// such that `solve` <= `expr` for any valid values of named atoms.
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
        solve: Expr<'a>,
        given: BoundGroup<'a>,
        tried: Vec<bool>,
        max_depth: usize,
    ) -> Maximizer<'a> {
        let vars = solve.variables();
        Maximizer {
            solving: solve,
            vars,
            given,
            tried,
            permutation_group: None,
            group_idx: 0,
            max_depth,
            child: None,
        }
    }

    pub fn new_root(solve: Expr<'a>, given: BoundGroup<'a>, max_depth: usize) -> Maximizer<'a> {
        // `tried` is initialized with every element false
        let max_req_id = given.max_requirement_id();
        Self::new(solve, given, vec![false; max_req_id], max_depth)
    }

    /// Returns an iterator of evaluated bounds.
    /// So `solve <= x` for all x generated by this integer.
    pub fn int_bounds(
        self,
    ) -> std::iter::FilterMap<Self, fn(Expr<'a>) -> std::option::Option<Int>> {
        self.filter_map(|expr| Some(expr.eval()?.as_upper_bound()))
    }

    fn find_permutation_group(&mut self) {
        // Find the permutation group of the first bound that we've not yet subbed.
        self.permutation_group = self
            .given
            .iter()
            // BoundRef -> (BoundRef, requirement ID)
            .map(|bound| (bound, bound.requirement().unwrap().id()))
            // Filter requirements we've already used
            .filter(|(_, req)| !self.tried[*req])
            // (BoundRef, req ID) -> (BoundRef, subbed and simplified Expr, req ID)
            .filter_map(|(bound, req)| {
                Some((
                    bound,
                    Self::sub_bound(&self.solving, &*bound)?.simplify(),
                    req,
                ))
            })
            // Filter out subs that have no effect on the expression
            //.filter(|(_, expr, _)| *expr != self.solving)
            .map(|(bound, _, _)| bound.permutation_group())
            .next()
            .map(|perm_grp| {
                perm_grp
                    .iter()
                    .map(|bound| ((**bound).clone(), bound.requirement().unwrap().id()))
                    .collect()
            });
    }
}

/// Used to construct the body of the Iterator next method for Minimizer and Maximizer.
/// The bounds we can assume to be true. Probably given by the function requirements/lemmas.
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
            println!("Bye");
            return None;
        }

        if $self.permutation_group.is_none() {
            $self.find_permutation_group();
            if $self.permutation_group.is_none() {
                $self.max_depth = 0;
                println!(
                    "YIELDING {} = {}",
                    $self.solving.clone(),
                    match $self.solving.eval() {
                        Some(x) => x,
                        None => Int::Infinity.into(),
                    }
                );
                return Some($self.solving.clone());
            }
        }
        let permutation_group = $self.permutation_group.as_ref()?;

        // Now we want to make another substitution.
        // We will find a variable with a bound that we can use.
        let (bound, requirement_id) = loop {
            println!("i: {}", $self.group_idx);
            // If there are no more substitutions to make, we can finish.
            // To do this, we'll mark this as the final child (see the early return case above) and
            // return the current expression since it is a bound of itself.
            if $self.group_idx >= permutation_group.len() {
                $self.max_depth = 0;
                println!(
                    "YIELDING {} = {}",
                    $self.solving.clone(),
                    match $self.solving.eval() {
                        Some(x) => x,
                        None => Int::Infinity.into(),
                    }
                );
                return Some($self.solving.clone());
            }

            let (ref bound, requirement_id) = permutation_group[$self.group_idx];

            if $self.tried[requirement_id] {
                println!("Already tried...");
                $self.group_idx += 1;
                continue;
            }

            $self.group_idx += 1;

            // We only need to make a substitution if the expression contains the variable.
            if $self.vars.contains(&bound.subject) {
                break (bound, requirement_id);
            }
            println!("{} doesn't include {}", $self.solving, bound.subject);
        };

        let mut new_tried = $self.tried.clone();
        new_tried[requirement_id] = true;

        println!("Subbing {}", bound);

        // Substitute the bound
        let new_expr = match Self::sub_bound(&$self.solving, &bound) {
            Some(expr) => expr.simplify(),
            None => return $self.next(),
        };

        println!("Solving: {} <== {}", &$self.solving, new_expr);

        println!("Making a child!");
        // Create the new child
        $self.child = Some(Box::new(Self::new(
            new_expr,
            $self.given.sub_bound(&bound),
            new_tried,
            $self.max_depth - 1,
        )));

        $self.next()
    }};
}

pub fn bound_sub<'a>(
    subber: impl Fn(&Expr<'a>, &DescriptiveBound<'a>) -> Option<Expr<'a>>,
    bound: &DescriptiveBound<'a>,
    sub_bound: &DescriptiveBound<'a>,
) -> Option<DescriptiveBound<'a>> {
    let x = Expr::Atom(Atom::Named(bound.subject));
    let (relation_kind, bound_expr) = match &bound.bound {
        Bound::Le(expr) => (RelationKind::Le, expr),
        Bound::Ge(expr) => (RelationKind::Ge, expr),
    };
    let new_bound_expr = match subber(bound_expr, sub_bound) {
        Some(expr) => expr,
        None => return Some(bound.clone()),
    };
    let lhs = Expr::Sum(vec![x.clone(), Expr::Neg(Box::new(new_bound_expr))]).simplify();
    if lhs
        .variables()
        .iter()
        .find(|var| **var == bound.subject)
        .is_none()
    {
        return None;
    }
    Some(DescriptiveBound {
        subject: bound.subject,
        bound: Relation {
            left: lhs.single_x(&x)?,
            relation: relation_kind,
            right: expr::ZERO,
        }
        .bounds_on_unsafe(&x)?
        .simplify(),
    })
}

fn bound_sub_all<'a>(
    subber: impl Fn(&Expr<'a>, &Expr<'a>, &Bound<'a>) -> Expr<'a>,
    x: Ident<'a>,
    bound: &Bound<'a>,
    sub_x: &Expr<'a>,
    sub_bound: &Bound<'a>,
) -> Vec<(Ident<'a>, Bound<'a>)> {
    let x = Expr::Atom(Atom::Named(x));
    let (relation_kind, bound_expr) = match bound {
        Bound::Le(expr) => (RelationKind::Le, expr),
        Bound::Ge(expr) => (RelationKind::Ge, expr),
    };
    let new_bound_expr = subber(bound_expr, sub_x, sub_bound);
    let lhs = Expr::Sum(vec![x.clone(), Expr::Neg(Box::new(new_bound_expr))]).simplify();
    lhs.variables()
        .iter()
        .filter_map(|var_ident| {
            let var = Expr::Atom(Atom::Named(var_ident.clone()));
            Some((
                *var_ident,
                Relation {
                    left: lhs.single_x(&var)?,
                    relation: relation_kind,
                    right: expr::ZERO,
                }
                .bounds_on_unsafe(&var)?
                .simplify(),
            ))
        })
        .collect()
}

impl<'a: 'b, 'b> Iterator for Minimizer<'a> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        println!(
            "\nMinimizer next on ({}) {}",
            self.group_idx,
            self.solving.clone()
        );
        optimizer_next_body!(self)
    }
}
impl<'a: 'b, 'b> Iterator for Maximizer<'a> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        println!(
            "\nMaximizer next on ({}) {}",
            self.group_idx,
            self.solving.clone()
        );
        optimizer_next_body!(self)
    }
}

fn sub_bound_into<'a>(
    expr: &Expr<'a>,
    bound: &DescriptiveBound<'a>,
    self_sub: impl Fn(&Expr<'a>, &DescriptiveBound<'a>) -> Option<Expr<'a>>,
    sub_opposite: impl Fn(&Expr<'a>, &DescriptiveBound<'a>) -> Option<Expr<'a>>,
) -> Option<Expr<'a>> {
    match expr {
        // An atom has a fixed value if it was not `x`
        Expr::Atom(_) => None,

        // An upper bound for -(...) is -(a lower bound for ...)
        Expr::Neg(inner_expr) => Some(Expr::Neg(Box::new(sub_opposite(inner_expr, bound)?))),
        // An upper bound for 1/(...) is 1/(a lower bound for ...)
        Expr::Recip(inner_expr, rounding) => Some(Expr::Recip(
            Box::new(sub_opposite(inner_expr, bound)?),
            *rounding,
        )),

        // A bound on a sum is the sum of the bounds of its terms.
        Expr::Sum(terms) => {
            // Try substituting into each term.
            let subbed_terms = terms
                .iter()
                .map(|term| self_sub(term, bound))
                .collect::<Vec<Option<Expr>>>();
            // If no terms had substitutions then return None.
            if subbed_terms.iter().all(Option::is_none) {
                return None;
            }
            // Otherwise, use the substituted terms and clone the ones without substitutions to
            // create the new terms.
            Some(Expr::Sum(
                subbed_terms
                    .iter()
                    .enumerate()
                    .map(|(i, term)| term.as_ref().unwrap_or_else(|| &terms[i]).clone())
                    .collect(),
            ))
        }

        Expr::Prod(terms) => {
            // We now want to minimize a product, for now, we will only simplify products in
            // the form: [expr]*literal0*literal1*... (expr is optional)
            // Where all the literals are non-negative (we can assume this since the expression is
            // simplified).
            // It is clear that the optimum of an expression with this form is
            // optimum(expr)*literal0*literal1*...
            // Other forms would be more complex. TODO Handle non-linear things!

            let mut out = Vec::with_capacity(terms.len());
            // This is to keep track of if we've made a substitution; if we've already made one
            // when we come to do another then we've encountered more than 1 non-literal expression
            // so we will return the expression we started with since we don't get have a valid
            // algorithm for this.
            let mut made_sub = false;
            for i in 0..terms.len() {
                let term = &terms[i];
                out.push(match term {
                    // We will just copy literals.
                    // Note that we require only positive literals (which we should have if the
                    // expression is simplified).
                    Expr::Atom(Atom::Literal(x)) => {
                        if *x < Rational::ZERO {
                            panic!("literal < 0")
                        } else {
                            term.clone()
                        }
                    }
                    // TODO Remove since we've got rationals
                    // We will also treat a recip of a literal as a literal since it's constant.
                    Expr::Recip(inner_expr, _) => match &**inner_expr {
                        Expr::Atom(Atom::Literal(x)) => {
                            if *x < Rational::ZERO {
                                panic!("literal < 0")
                            } else {
                                term.clone()
                            }
                        }

                        _ => {
                            // We can't handle non-linear things yet :(
                            // See the comment above
                            if made_sub {
                                return None;
                            }
                            made_sub = true;
                            self_sub(term, bound)?
                        }
                    },

                    _ => {
                        // We can't handle non-linear things yet :(
                        // See the comment above
                        if made_sub {
                            return None;
                        }
                        made_sub = true;
                        self_sub(term, bound)?
                    }
                });
            }
            Some(Expr::Prod(out))
        }
    }
}

impl<'a: 'b, 'b> Minimizer<'a> {
    /// Returns an upper bound on `expr` given a bound on `x`.
    /// This is done by making all apropriate substitutions.
    /// Note that the outputted expression isn't garenteed to be simplified.
    pub fn sub_bound(expr: &Expr<'a>, bound: &DescriptiveBound<'a>) -> Option<Expr<'a>> {
        // If the expression is x, then an upper bound is given directly.
        if *expr == Expr::Atom(Atom::Named(bound.subject)) {
            return match &bound.bound {
                Bound::Ge(bound_expr) => Some(bound_expr.clone()),
                Bound::Le(_) => None,
            };
        }
        sub_bound_into(expr, bound, Minimizer::sub_bound, Maximizer::sub_bound)
    }
}

impl<'a: 'b, 'b> Maximizer<'a> {
    /// Returns a lower bound on `expr` given a bound on `x`.
    /// This is done by making all apropriate substitutions.
    /// Note that the outputted expression isn't garenteed to be simplified.
    pub fn sub_bound(expr: &Expr<'a>, bound: &DescriptiveBound<'a>) -> Option<Expr<'a>> {
        if *expr == Expr::Atom(Atom::Named(bound.subject)) {
            return match &bound.bound {
                Bound::Le(bound_expr) => Some(bound_expr.clone()),
                Bound::Ge(_) => None,
            };
        }
        sub_bound_into(expr, bound, Maximizer::sub_bound, Minimizer::sub_bound)
    }
}
