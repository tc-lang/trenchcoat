pub mod options;

use self::options::Options;
use super::bound::{bounds_on_ge0, Bound, DescriptiveBound, Relation, RelationKind};
use super::expr::{self, Atom, Expr};
use super::int::Int;
use super::sign::Sign;
use crate::ast::Ident;
use crate::little_cache::Cache as LittleCache;

// TODO These types can probably be created with a macro to remove duplication.
//
// TODO Since we assume that expressions and bounds are given to the `new` functions simplified,
// perhaps we don't make that assumption and instead simplify them then. This would perhaps be less
// efficient but make mistakes less likely. (Wouldn't attributes for this be so nice? We could
// consider adding a phantom type to Expr and Bound also to garentee this.)

/// Also include a child where no substitution was made as the first child.
const NO_SUB_FIRST: bool = false;
/// Also include a child where no substitution was made as the last child.
const NO_SUB_LAST: bool = false;
/// Generate children lazily.
/// Results: This is slightly faster!
const LAZY_GENERATE_CHILDREN: bool = true;
/// Perform BFS rather than DFS
/// This cannot be done also with LAZY_GENERATE_CHILDREN
/// Results: This is slightly slower
const BFS: bool = false;
/// If true, only make substitutions that don't increase the number of variables.
// TODO const NO_MORE_VARIABLES: bool = false;

const TRY_NO_SUB: bool = NO_SUB_FIRST || NO_SUB_LAST;

/// Minimizer is a type for generating lower bounds on an expression, given a set of requirements.
/// It can be constructed with `Minimizer::new`, see that documentation for more details.
///
/// Note that upper bounds should be rounded up when evaluated.
/// Rounding down will not lead to incorrect behaviour but can lead to loose bounds.
/// This is the behaviur of the int_bounds() method.
pub struct Minimizer<'a, 'b, Opt: Options> {
    /// The expression to find bounds on
    /// This must be simplified.
    solving: Expr<'a>,

    /// The BoundGroup of the requirements that are assumed to be true.
    given_ge0: Vec<Expr<'a>>,

    /// The permutation group that this node is permuting.
    /// None if this is a final node.
    /// The tuple is (Bound, solving.sub(bound), requirement ID)
    permutation_group: Option<(Ident<'a>, Vec<(Bound<'a>, Expr<'a>, usize)>)>,
    /// The index in permutation_group of the next child to be generated.
    group_idx: usize,

    /// The current budget of this node.
    budget: isize,

    /// The currently generated direct children.
    children: Vec<Minimizer<'a, 'b, Opt>>,
    /// The index in self.children that we should next iterate on.
    child_idx: usize,
    /// The budget to be given to new children. This is used when they are lazily generated.
    child_budget: isize,

    generated: bool,

    /// Current state tracker
    state: BudgetState,
    is_final: bool,
    yielded_self: bool,

    sign_cache: &'b LittleCache<Ident<'a>, Sign>,

    options: Opt,
    //indent: String,
}

/// Maximizer is a type for generating upper bounds on an expression, given a set of requirements.
/// It can be constructed with `Maximizer::new`, see that documentation for more details.
///
/// Note that lower bounds should be down up when evaluated.
/// This is the behaviur of the int_bounds() method.
pub struct Maximizer<'a, 'b, Opt: Options> {
    solving: Expr<'a>,
    given_ge0: Vec<Expr<'a>>,
    permutation_group: Option<(Ident<'a>, Vec<(Bound<'a>, Expr<'a>, usize)>)>,
    group_idx: usize,
    budget: isize,
    child_idx: usize,
    children: Vec<Maximizer<'a, 'b, Opt>>,
    state: BudgetState,
    child_budget: isize,
    generated: bool,
    is_final: bool,
    yielded_self: bool,
    sign_cache: &'b LittleCache<Ident<'a>, Sign>,
    options: Opt,
    //indent: String,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum BudgetState {
    /// This node is still spending budget and potentially generating bounds.
    Working,
    /// This node has finished. It will not spend more budget and so self.remaining_budget can ve
    /// reclaimed.
    Finished,
    /// The node wants to continute but cannnot due to lack of budget.
    Stalved,
}

impl<'a, 'b, Opt: Options> Minimizer<'a, 'b, Opt> {
    /// Returns a minimizer for `solve`.
    /// This minimizer will, using the known bounds given by `given`, iterate through expressions
    /// such that `solve` >= `expr` for any valid values of named atoms.
    /// The resulting expressions will have varying degrees of tightness.
    /// The iterator ends when no more bounds are available.
    ///
    /// The expression and bounds given are assumed to be simplified.
    ///
    /// TODO Document time complexity with budget
    pub fn new(
        solve: Expr<'a>,
        given_ge0: Vec<Expr<'a>>,
        budget: isize,
        sign_cache: &'b LittleCache<Ident<'a>, Sign>,
        options: Opt,
        //indent: String,
    ) -> Minimizer<'a, 'b, Opt> {
        // This combination of settings isn't allowed
        assert!(!(BFS && LAZY_GENERATE_CHILDREN));

        Minimizer {
            solving: solve,
            given_ge0,
            permutation_group: None,
            group_idx: 0,
            budget,
            child_idx: 0,
            children: Vec::new(),
            state: BudgetState::Working,
            child_budget: 0,
            generated: false,
            is_final: false,
            yielded_self: false,
            sign_cache,
            options,
            //indent,
        }
    }

    /// Returns an iterator of evaluated bounds.
    /// So `solve >= x` for all x generated by this integer.
    pub fn int_bounds(
        self,
    ) -> std::iter::FilterMap<Self, fn(Expr<'a>) -> std::option::Option<Int>> {
        self.filter_map(|expr| Some(expr.eval()?.as_lower_bound()))
    }
}

impl<'a, 'b, Opt: Options> Maximizer<'a, 'b, Opt> {
    /// Returns a maximizer for `solve`.
    /// This maximizer will, using the known bounds given by `given`, iterate through expressions
    /// such that `solve` <= `expr` for any valid values of named atoms.
    /// The resulting expressions will have varying degrees of tightness.
    /// The iterator ends when no more bounds are available.
    ///
    /// The expression and bounds given are assumed to be simplified.
    ///
    /// TODO Document time complexity with budget
    pub fn new(
        solve: Expr<'a>,
        given_ge0: Vec<Expr<'a>>,
        budget: isize,
        sign_cache: &'b LittleCache<Ident<'a>, Sign>,
        options: Opt,
        //indent: String,
    ) -> Maximizer<'a, 'b, Opt> {
        // This combination of settings isn't allowed
        assert!(!(BFS && LAZY_GENERATE_CHILDREN));

        Maximizer {
            solving: solve,
            given_ge0,
            permutation_group: None,
            group_idx: 0,
            budget,
            child_idx: 0,
            children: Vec::new(),
            state: BudgetState::Working,
            child_budget: 0,
            generated: false,
            is_final: false,
            yielded_self: false,
            sign_cache,
            options,
            //indent,
        }
    }

    /// Returns an iterator of evaluated bounds.
    /// So `solve <= x` for all x generated by this integer.
    pub fn int_bounds(
        self,
    ) -> std::iter::FilterMap<Self, fn(Expr<'a>) -> std::option::Option<Int>> {
        self.filter_map(|expr| Some(expr.eval()?.as_upper_bound()))
    }
}

/// Budget methods for Minimizer and Maximizer
macro_rules! budget_impl {
    () => {
        /// Returns the current state of self
        fn state(&self) -> BudgetState {
            self.state
        }
        /// Returns the budget that self has remaining.
        /// This should be used when self has finished.
        fn remaining_budget(&self) -> isize {
            assert!(self.state == BudgetState::Finished);
            self.budget
        }
        /// Gives extra_budget to self
        /// A finished node cannot be given extra budget
        fn give(&mut self, extra_budget: isize) {
            debug_assert!(self.state != BudgetState::Finished);
            self.budget += extra_budget;
            // We might not be stavled anymore!
            // We'll go back to stalving on the next call to next if we've still not got enough.
            self.state = BudgetState::Working;
        }
    };
}

impl<'a, 'b, Opt: Options> Minimizer<'a, 'b, Opt> {
    budget_impl!();
}

impl<'a, 'b, Opt: Options> Maximizer<'a, 'b, Opt> {
    budget_impl!();
}

/// Substitutes `sub` to find an upper bound on all `ge0` entries except for `exclude` and return
/// the result.
///
/// The order of the result it ge0s[exclude+1..] ++ ge0s[..<excludes]
/// This is so that if this is passed to a child optimiser, the next requirement checked will be
/// the one after the one that has just been substituted (possibly reducing the number of failed
/// rearrangements).
fn ge0_sub_and_exclude<'a, Opt: Options, NS: Fn(&Ident<'a>) -> Sign + Copy>(
    ge0s: &[Expr<'a>],
    exclude: usize,
    sub: &DescriptiveBound<'a>,
    named_sign: NS,
) -> Vec<Expr<'a>> {
    ge0s[exclude + 1..]
        .iter()
        .chain(ge0s[..exclude].iter())
        .map(|expr| {
            Maximizer::<Opt>::sub_bound(expr, sub, named_sign).unwrap_or_else(|| expr.clone())
        })
        .map(|expr| expr.simplify())
        .collect()
}

// Methods on both Maximizer and Minimizer
macro_rules! find_pg_group_fn {
    () => {
        fn sign_of(&self, x: &Ident<'a>) -> Sign {
            if self.options.better_sign_handling() {
                self.sign_cache.get(x).unwrap_or(Sign::UNKNOWN)
            } else {
                Sign::UNKNOWN
            }
        }

        fn find_permutation_group(&mut self) {
            self.permutation_group = self
                .solving
                .variables()
                .iter()
                .flat_map(|var| {
                    self.given_ge0
                        .iter()
                        .enumerate()
                        .map(move |(idx, expr)| (idx, expr, var))
                        .filter_map(|(given_idx, expr, var)| {
                            Some((
                                given_idx,
                                bounds_on_ge0(expr, var, |x| self.sign_of(x))?.simplify(),
                                var,
                            ))
                        })
                        .filter_map(|(given_idx, bound, var)| {
                            let rv = Some((
                                var.clone(),
                                bound.clone(),
                                Self::sub_bound(
                                    &self.solving,
                                    &DescriptiveBound {
                                        subject: var.clone(),
                                        bound,
                                    },
                                    |x| self.sign_of(x),
                                )?
                                .simplify(),
                                given_idx,
                            ));
                            rv
                        })
                })
                .next()
                .map(|(var, top_bound, top_expr, top_given_idx)| {
                    (
                        var.clone(),
                        self.given_ge0
                            .iter()
                            .enumerate()
                            .filter_map(|(given_idx, ge0)| {
                                if given_idx == top_given_idx {
                                    Some((top_bound.clone(), top_expr.clone(), given_idx))
                                } else {
                                    if !ge0.contains(&var) {
                                        return None;
                                    }
                                    let bound =
                                        bounds_on_ge0(ge0, &var, |x| self.sign_of(x))?.simplify();
                                    Some((
                                        bound.clone(),
                                        Self::sub_bound(
                                            &self.solving,
                                            &DescriptiveBound {
                                                subject: var.clone(),
                                                bound,
                                            },
                                            |x| self.sign_of(x),
                                        )?
                                        .simplify(),
                                        given_idx,
                                    ))
                                }
                            })
                            .collect(),
                    )
                });
        }

        fn generate_children(&mut self) {
            debug_assert!(self.permutation_group.is_none());

            // If we don't have any budget then we can't do substitutions to work out the
            // permutation group. So we shouldn't try and we should mark ourselves as stalved.
            if self.budget <= 0 {
                self.state = BudgetState::Stalved;
                return;
            }

            // Find our permutation group
            self.find_permutation_group();

            if !NO_SUB_FIRST {
                self.generated = true;
            }

            // If there's nothing to sub in, we should now stop, so we go in to final mode.
            // (See the behaviour of the next method)
            if self.permutation_group.is_none() {
                self.is_final = true;
                return;
            }

            // n = total number of children
            let n =
                self.permutation_group.as_ref().unwrap().1.len() + if TRY_NO_SUB { 1 } else { 0 };
            let ni = n as isize;

            // For each (not no-sub) child, we made 1 substitution to solve and
            // self.given_ge0.len() subs to the given expressions. This is a total of
            // n*self.given_ge0.len()
            self.budget -= (ni - if TRY_NO_SUB { 1 } else { 0 }) * self.given_ge0.len() as isize;
            // Work out our budget per child
            self.child_budget = self.budget.max(0) / ni;
            // Subtract the total budget spent from our budget
            self.budget -= self.child_budget * ni;

            let mut children = Vec::with_capacity(n);

            if NO_SUB_FIRST {
                children.push(Self::new(
                    self.solving.clone(),
                    //self.given.exclude(100000, self.pg_id),
                    todo!(),
                    self.child_budget,
                    self.sign_cache,
                    self.options.clone(),
                ));
            }

            if !LAZY_GENERATE_CHILDREN {
                let (var, grp) = self.permutation_group.as_ref().unwrap();
                children.extend(grp.iter().map(|(bound, to_solve, req_id)| {
                    //Child::Node(Box::new(Self::new(
                    Self::new(
                        to_solve.clone(),
                        ge0_sub_and_exclude::<Opt, _>(
                            &self.given_ge0,
                            *req_id,
                            &DescriptiveBound {
                                subject: var.clone(),
                                bound: bound.clone(),
                            },
                            |x| self.sign_of(x),
                        ),
                        self.child_budget,
                        self.sign_cache,
                        self.options.clone(),
                    )
                }));
            }

            self.children = children;
        }

        fn generate_next_child(&mut self) -> bool {
            // This should only be used to lazily generate children
            assert!(LAZY_GENERATE_CHILDREN);

            let (var, bounds) = match self.permutation_group.as_ref() {
                Some(pg) => pg,
                None => return false,
            };

            if NO_SUB_LAST && self.group_idx == bounds.len() {
                todo!();
                self.group_idx += 1;

                /*self.children.push(Self::new(
                    self.solving.clone(),
                    self.given.exclude(100000, self.pg_id),
                    self.child_budget,
                ));*/

                return true;
            } else if self.group_idx >= bounds.len() {
                return false;
            }

            let (bound, to_solve, req_id) = &bounds[self.group_idx];

            self.group_idx += 1;

            self.children.push(Self::new(
                to_solve.clone(),
                ge0_sub_and_exclude::<Opt, _>(
                    &self.given_ge0,
                    *req_id,
                    &DescriptiveBound {
                        subject: var.clone(),
                        bound: bound.clone(),
                    },
                    |x| self.sign_of(x),
                ),
                self.child_budget,
                self.sign_cache,
                self.options.clone(),
            ));

            true
        }
    };
}

impl<'a, 'b, Opt: Options> Minimizer<'a, 'b, Opt> {
    find_pg_group_fn!();
}

impl<'a, 'b, Opt: Options> Maximizer<'a, 'b, Opt> {
    find_pg_group_fn!();
}

/// Used to construct the body of the Iterator next method for Minimizer and Maximizer.
/// The bounds we can assume to be true. Probably given by the function requirements/lemmas.
macro_rules! optimizer_next_body {
    ($self:expr) => {{
        loop {
            // Don't try the children if we know we're not working.
            if $self.state != BudgetState::Working {
                return None;
            }

            if $self.options.yield_all() && !$self.yielded_self {
                $self.yielded_self = true;
                return Some($self.solving.clone());
            }

            // If we are in final mode (see self.generate_children for how we get in this mode)
            // Then we should yield self.solving and then finish.
            if $self.is_final {
                $self.state = BudgetState::Finished;
                if $self.options.yield_all() {
                    return None;
                }
                return Some($self.solving.clone());
            }

            if NO_SUB_FIRST && $self.children.len() == 0 || !NO_SUB_FIRST && !$self.generated {
                $self.generate_children();
                // We could be stalving after this, so we should start the again.
                continue;
            }

            if BFS {
                let start_child_idx = $self.child_idx;
                loop {
                    match $self.children[$self.child_idx].next() {
                        Some(expr) => {
                            $self.child_idx = ($self.child_idx + 1) % $self.children.len();
                            return Some(expr);
                        }
                        None => (),
                    }
                    $self.child_idx = ($self.child_idx + 1) % $self.children.len();
                    if $self.child_idx == start_child_idx {
                        break;
                    }
                }
            } else {
                loop {
                    while $self.child_idx < $self.children.len() {
                        match $self.children[$self.child_idx].next() {
                            Some(expr) => return Some(expr),
                            None => (),
                        }
                        $self.child_idx += 1;
                    }
                    if !LAZY_GENERATE_CHILDREN || !$self.generate_next_child() {
                        break;
                    }
                }
            }

            // Count the number of remaining children and reclaim the budget of finished children.
            let mut remaining_children = 0;
            for child in &$self.children {
                match child.state() {
                    BudgetState::Finished => {
                        // This will subtract if they've gone over budget.
                        $self.budget += child.remaining_budget();
                    }
                    BudgetState::Stalved => {
                        remaining_children += 1;
                    }
                    BudgetState::Working => panic!("working child returned None"),
                }
            }

            // We've finished if all of our children have finished!
            if remaining_children == 0 {
                $self.state = BudgetState::Finished;
                $self.children = Vec::new();
                return None;
            }

            // Calculate any budget we can distribute to our children.
            let child_budget = $self.budget.max(0) / remaining_children;
            // Distribute it and continue if we have some.
            if child_budget > 0 {
                for child in &mut $self.children {
                    if child.state() == BudgetState::Stalved {
                        child.give(child_budget);
                    }
                }
                $self.budget -= child_budget * remaining_children;
                if !BFS {
                    // We must now start iterating from the start again
                    $self.child_idx = 0;
                }
                continue;
            }
            // Otherwise, we're stalved.
            $self.state = BudgetState::Stalved;
            return None;
        }
    }};
}

/// Substitutes sub_bound in to bound and returns the result.
/// This uses {Minimizer, Maximizer}::sub_bound
pub fn bound_sub<'a, Opt: Options, F: Fn(&Ident<'a>) -> Sign + Copy>(
    bound: &DescriptiveBound<'a>,
    sub_bound: &DescriptiveBound<'a>,
    named_sign: F,
) -> Option<DescriptiveBound<'a>> {
    let (relation_kind, new_bound_expr) = match &bound.bound {
        Bound::Le(expr) => (
            RelationKind::Le,
            Maximizer::<Opt>::sub_bound(expr, sub_bound, named_sign),
        ),
        Bound::Ge(expr) => (
            RelationKind::Ge,
            Minimizer::<Opt>::sub_bound(expr, sub_bound, named_sign),
        ),
    };
    // Unwrap new_bound_expr
    // If no substitution was made, just clone the existing bound.
    let new_bound_expr = match new_bound_expr {
        Some(expr) => expr,
        None => return Some(bound.clone()),
    };

    let x = Expr::Atom(Atom::Named(bound.subject.clone()));
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
        subject: bound.subject.clone(),
        bound: Relation {
            left: lhs.single_x(&bound.subject)?,
            kind: relation_kind,
            right: expr::zero(),
        }
        .bounds_on_unsafe(&bound.subject, named_sign)?
        .simplify(),
    })
}

impl<'a, 'b, Opt: Options> Iterator for Minimizer<'a, 'b, Opt> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        optimizer_next_body!(self)
    }
}
impl<'a, 'b, Opt: Options> Iterator for Maximizer<'a, 'b, Opt> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        optimizer_next_body!(self)
    }
}

/// Used internally by {Minimizer, Maximizer}::sub_bound
fn sub_bound_into<
    'a,
    SS: Fn(&Expr<'a>, &DescriptiveBound<'a>, NS) -> Option<Expr<'a>>,
    SO: Fn(&Expr<'a>, &DescriptiveBound<'a>, NS) -> Option<Expr<'a>>,
    NS: Fn(&Ident<'a>) -> Sign + Copy,
>(
    expr: &Expr<'a>,
    bound: &DescriptiveBound<'a>,
    self_sub: SS,
    sub_opposite: SO,
    named_sign: NS,
) -> Option<Expr<'a>> {
    match expr {
        // An atom has a fixed value if it was not `x`
        Expr::Atom(_) => None,

        // An upper bound for -(...) is -(a lower bound for ...)
        Expr::Neg(inner_expr) => Some(Expr::Neg(Box::new(sub_opposite(
            inner_expr, bound, named_sign,
        )?))),
        // An upper bound for 1/(...) is 1/(a lower bound for ...)
        Expr::Recip(inner_expr, rounding) => Some(Expr::Recip(
            Box::new(sub_opposite(inner_expr, bound, named_sign)?),
            *rounding,
        )),

        // A bound on a sum is the sum of the bounds of its terms.
        Expr::Sum(terms) => {
            // Try substituting into each term.
            let subbed_terms = terms
                .iter()
                .map(|term| self_sub(term, bound, named_sign))
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
            // We now want to minimize a product. Currently, we can do this if `x` is only in 1
            // term and the rest of the terms are known to be non-negative.
            // If this is the case, then subbed( a*b*c*x ) = a*b*c*subbed(x)

            // We'll start by copying the terms in to out - excluding the term which we can
            // substitute in to which we'll store in sub and then add back in later.
            // 
            // As mentioned above, we also can't handle multiple terms containing `x`
            let mut sub = None;
            let mut out = Vec::with_capacity(terms.len());
            for i in 0..terms.len() {
                let term = &terms[i];
                match self_sub(term, bound, named_sign) {
                    Some(subbed) => {
                        if sub.is_some() {
                            return None;
                        }
                        sub = Some(subbed);
                    }
                    None => out.push(term.clone()),
                }
            }
            // Return None now if we've not found anything to substitute!
            let sub = sub?;
            // Now check that the rest of the terms can't be negative
            for term in out.iter() {
                let sign = term.sign(named_sign);
                if sign.maybe_neg() {
                    // We might be able to do more here, but we've probably done enough.
                    return None;
                }
            }
            // Now push the substituted term
            out.push(sub);
            Some(Expr::Prod(out))
        }
    }
}

impl<'a, 'b, Opt: Options> Minimizer<'a, 'b, Opt> {
    /// Returns an upper bound on `expr` given a bound on `x`.
    /// This is done by making all apropriate substitutions.
    /// Note that the outputted expression isn't garenteed to be simplified.
    pub fn sub_bound(
        expr: &Expr<'a>,
        bound: &DescriptiveBound<'a>,
        named_sign: impl Fn(&Ident<'a>) -> Sign + Copy,
    ) -> Option<Expr<'a>> {
        // If the expression is x, then an upper bound is given directly.
        if expr == &Expr::Atom(Atom::Named(bound.subject.clone())) {
            return match &bound.bound {
                Bound::Ge(bound_expr) => Some(bound_expr.clone()),
                Bound::Le(_) => None,
            };
        }
        sub_bound_into(
            expr,
            bound,
            Minimizer::<Opt>::sub_bound,
            Maximizer::<Opt>::sub_bound,
            named_sign,
        )
    }
}

impl<'a, 'b, Opt: Options> Maximizer<'a, 'b, Opt> {
    /// Returns a lower bound on `expr` given a bound on `x`.
    /// This is done by making all apropriate substitutions.
    /// Note that the outputted expression isn't garenteed to be simplified.
    pub fn sub_bound(
        expr: &Expr<'a>,
        bound: &DescriptiveBound<'a>,
        named_sign: impl Fn(&Ident<'a>) -> Sign + Copy,
    ) -> Option<Expr<'a>> {
        if expr == &Expr::Atom(Atom::Named(bound.subject.clone())) {
            return match &bound.bound {
                Bound::Le(bound_expr) => Some(bound_expr.clone()),
                Bound::Ge(_) => None,
            };
        }
        sub_bound_into(
            expr,
            bound,
            Maximizer::<Opt>::sub_bound,
            Minimizer::<Opt>::sub_bound,
            named_sign,
        )
    }
}
