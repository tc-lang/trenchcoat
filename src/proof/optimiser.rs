use super::ast::Ident;
use super::bound::{Bound, DescriptiveBound, Relation, RelationKind};
use super::bound_group::BoundGroup;
use super::expr::{self, Atom, Expr};
use super::int::{Int, Rational};
use std::iter::Iterator;

// TODO These types can probably be created with a macro to remove duplication.
//
// TODO Since we assume that expressions and bounds are given to the `new` functions simplified,
// perhaps we don't make that assumption and instead simplify them then. This would perhaps be less
// efficient but make mistakes less likely. (Wouldn't attributes for this be so nice? We could
// consider adding a phantom type to Expr and Bound also to garentee this.)

const TRY_NO_SUB: bool = true;

/// Minimizer is a type for generating lower bounds on an expression, given a set of requirements.
/// It can be constructed with `Minimizer::new`, see that documentation for more details.
///
/// Note that upper bounds should be rounded up when evaluated.
/// Rounding down will not lead to incorrect behaviour but can lead to loose bounds.
/// This is the behaviur of the int_bounds() method.
#[derive(Clone)]
pub struct Minimizer<'a> {
    /// The expression to find bounds on
    /// This must be simplified.
    solving: Expr<'a>,
    /// The variables in `solving` (as returned by `solving.variables()`)
    /// Stored for fast lookup.
    vars: Vec<Ident<'a>>,

    /// The BoundGroup of the requirements that are assumed to be true.
    given: BoundGroup<'a>,

    /// The permutation group that this node is permuting.
    /// None if this is a final node.
    /// The tuple is (Bound, solving.sub(bound), requirement ID)
    permutation_group: Option<Vec<(DescriptiveBound<'a>, Expr<'a>, usize)>>,

    /// The current budget of this node.
    budget: isize,
    
    /// This nodes direct children.
    children: Vec<Child<'a, Minimizer<'a>>>,

    /// Current state tracker
    state: BudgetState,

    //indent: String,
}

/// Maximizer is a type for generating upper bounds on an expression, given a set of requirements.
/// It can be constructed with `Maximizer::new`, see that documentation for more details.
///
/// Note that lower bounds should be down up when evaluated.
/// This is the behaviur of the int_bounds() method.
#[derive(Clone)]
pub struct Maximizer<'a> {
    solving: Expr<'a>,
    vars: Vec<Ident<'a>>,
    given: BoundGroup<'a>,
    permutation_group: Option<Vec<(DescriptiveBound<'a>, Expr<'a>, usize)>>,
    budget: isize,
    children: Vec<Child<'a, Maximizer<'a>>>,
    state: BudgetState,
    //indent: String,
}

#[derive(Clone)]
enum Child<'a, T: Budget + Iterator<Item = Expr<'a>> + Clone> {
    Node(Box<T>),
    Final(Final<'a>),
}

/// A final node
#[derive(Clone)]
struct Final<'a> {
    expr: Expr<'a>,
    yielded: bool,
}

trait Budget {
    fn remaining_budget(&self) -> isize;
    fn state(&self) -> BudgetState;
    fn give(&mut self, extra_budget: isize);
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum BudgetState {
    Working,
    Finished,
    Stalved,
}

// Pass on iterator methods
impl<'a, T: Budget + Iterator<Item = Expr<'a>> + Clone> Iterator for Child<'a, T> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        match self {
            Child::Final(f) => f.next(),
            Child::Node(n) => n.next(),
        }
    }
}

impl<'a> Final<'a> {
    fn new(expr: Expr<'a>) -> Final<'a> {
        Final {
            expr,
            yielded: false,
        }
    }
}

impl<'a> Iterator for Final<'a> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        // Yield self.expr exactly once
        match self.yielded {
            false => {
                self.yielded = true;
                Some(self.expr.clone())
            },
            true => None,
        }
    }
}

impl<'a> Budget for Final<'a> {
    fn remaining_budget(&self) -> isize {
        // Final cannot hold a budget
        0
    }
    fn state(&self) -> BudgetState {
        // We've finished if we've yielded; otherwise we're working.
        match self.yielded {
            false => BudgetState::Working,
            true => BudgetState::Finished,
        }
    }
    fn give(&mut self, _extra_budget: isize) {
        panic!("Final node cannot accept extra budget");
    }
}

// Pass on Budget methods
impl<'a, T: Budget + Iterator<Item = Expr<'a>> + Clone> Budget for Child<'a, T> {
    fn state(&self) -> BudgetState {
        match self {
            Child::Node(node) => node.state(),
            Child::Final(f) => f.state(),
        }
    }
    fn remaining_budget(&self) -> isize {
        match self {
            Child::Node(node) => node.remaining_budget(),
            Child::Final(f) => f.remaining_budget(),
        }
    }
    fn give(&mut self, extra_budget: isize) {
        match self {
            Child::Node(node) => node.give(extra_budget),
            Child::Final(f) => f.give(extra_budget),
        }
    }
}

/// Budget implementation for Minimizer and Maximizer
macro_rules! budget_impl {
    () => {
        fn remaining_budget(&self) -> isize {
            self.budget
        }
        fn state(&self) -> BudgetState {
            self.state
        }
        fn give(&mut self, extra_budget: isize) {
            debug_assert!(self.state != BudgetState::Finished);
            self.budget += extra_budget;
            self.state = BudgetState::Working;
        }
    };
}

impl<'a> Budget for Minimizer<'a> {
    budget_impl!();
}

impl<'a> Budget for Maximizer<'a> {
    budget_impl!();
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
        budget: isize,
        //indent: String,
    ) -> Minimizer<'a> {
        let vars = solve.variables();
        Minimizer {
            solving: solve,
            vars,
            given,
            permutation_group: None,
            budget,
            children: Vec::new(),
            state: BudgetState::Working,
            //indent,
        }
    }

    pub fn new_root(solve: Expr<'a>, given: BoundGroup<'a>, budget: isize) -> Minimizer<'a> {
        Self::new(
            solve, given, budget,
            //" | ".to_string(),
        )
    }

    /// Returns an iterator of evaluated bounds.
    /// So `solve >= x` for all x generated by this integer.
    pub fn int_bounds(
        self,
    ) -> std::iter::FilterMap<Self, fn(Expr<'a>) -> std::option::Option<Int>> {
        self.filter_map(|expr| Some(expr.eval()?.as_lower_bound()))
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
        budget: isize,
        //indent: String,
    ) -> Maximizer<'a> {
        let vars = solve.variables();
        Maximizer {
            solving: solve,
            vars,
            given,
            permutation_group: None,
            budget,
            children: Vec::new(),
            state: BudgetState::Working,
            //indent,
        }
    }

    pub fn new_root(solve: Expr<'a>, given: BoundGroup<'a>, budget: isize) -> Maximizer<'a> {
        Self::new(
            solve, given, budget,
            //" | ".to_string(),
        )
    }

    /// Returns an iterator of evaluated bounds.
    /// So `solve <= x` for all x generated by this integer.
    pub fn int_bounds(
        self,
    ) -> std::iter::FilterMap<Self, fn(Expr<'a>) -> std::option::Option<Int>> {
        self.filter_map(|expr| Some(expr.eval()?.as_upper_bound()))
    }
}

// Methods on both Maximizer and Minimizer
macro_rules! find_pg_group_fn {
    () => {
        fn find_permutation_group(&mut self) -> usize {
            let mut pg_id = 0;
            // Find the permutation group of the first bound that we've not yet subbed.
            self.permutation_group = self
                .given
                .iter()
                // BoundRef -> (BoundRef, requirement ID)
                .map(|bound| (bound, bound.requirement().unwrap().id()))
                // Quick check before we try and substitute
                .filter(|(bound, _)| self.vars.contains(&bound.subject))
                .filter_map(|(bound, req)| {
                    Some((bound, Self::sub_bound(&self.solving, &*bound)?, req))
                })
                .map(|(bound, _, _)| bound.permutation_group())
                .next()
                .map(|perm_grp| {
                    pg_id = perm_grp[0].permutation_group_id();
                    perm_grp
                        .iter()
                        .filter_map(|bound| {
                            Some((
                                (**bound).clone(),
                                // FIXME We make the same substitution as above here, among others
                                Self::sub_bound(&self.solving, &*bound)?.simplify(),
                                bound.requirement().unwrap().id(),
                            ))
                        })
                        .collect()
                });
            pg_id
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
            let pg_id = self.find_permutation_group();
            
            // If there's nothing to sub in, we've reached a final node
            if self.permutation_group.is_none() {
                self.children = vec![Child::Final(Final::new(self.solving.clone()))];
                return;
            }

            // n = total number of children
            let n = 1 + self.permutation_group.as_ref().unwrap().len();
            let ni = n as isize;

            // We've already made n-1 expr to get the expressions
            self.budget -= ni-1;
            // Work out our budget per child
            let child_budget = self.budget.max(0) / n as isize;
            // Subtract the total budget spent from our budget
            self.budget -= child_budget * ni;

            let mut children = Vec::with_capacity(n);
            if TRY_NO_SUB {
                children.push(Child::Node(Box::new(Self::new(
                    self.solving.clone(),
                    self.given.exclude(100000, pg_id),
                    child_budget,
                ))));
            }
            children
                .extend(self.permutation_group.as_ref().unwrap().iter().map(
                    |(bound, to_solve, req_id)| {
                        Child::Node(Box::new(Self::new(
                            to_solve.clone(),
                            self.given.exclude(*req_id, pg_id).sub_bound(bound),
                            child_budget,
                        )))
                    },
                ));
            self.children = children;
        }
    };
}

impl<'a: 'b, 'b> Minimizer<'a> {
    find_pg_group_fn!();
}

impl<'a: 'b, 'b> Maximizer<'a> {
    find_pg_group_fn!();
}

/// Used to construct the body of the Iterator next method for Minimizer and Maximizer.
/// The bounds we can assume to be true. Probably given by the function requirements/lemmas.
macro_rules! optimizer_next_body {
    ($self:expr) => {{
        // Don't try the children if we know we're not working.
        if $self.state != BudgetState::Working {
            return None;
        }

        // We will always have at least 1 child, so no children means we need to generate them.
        // We could have 0 children if we are finished but the case above woul have returned early.
        if $self.children.len() == 0 {
            $self.generate_children();
            // We could be stalving after this, so we should start the function again.
            return $self.next();
        }

        // Iterate through all of our children.
        // TODO Don't call next on children we know are empty
        for child in &mut $self.children {
            match child.next() {
                Some(expr) => return Some(expr),
                None => (),
            }
        }

        // Kill the children that have finished and collect their remaining budgets.
        let mut remaining_children = Vec::<Child<_>>::with_capacity($self.children.len());
        for child in &$self.children {
            match child.state() {
                BudgetState::Finished => {
                    // This will subtract if they've gone over budget.
                    $self.budget += child.remaining_budget();
                }
                BudgetState::Stalved => {
                    remaining_children.push((*child).clone());
                }
                BudgetState::Working => panic!("working child returned None"),
            }
        }
        $self.children = remaining_children;

        // We've finished if all of our children have finished!
        if $self.children.len() == 0 {
            $self.state = BudgetState::Finished;
            return None;
        }

        // Calculate any budget we can distribute to our children.
        let child_budget = $self.budget / ($self.children.len() as isize);
        // Distribute it and continue if we have some.
        if child_budget > 0 {
            for child in &mut $self.children {
                child.give(child_budget);
            }
            $self.budget -= child_budget * ($self.children.len() as isize);
            return $self.next();
        }
        // Otherwise, we're stalved.
        $self.state = BudgetState::Stalved;
        return None;
    }};
}

/// Substitutes sub_bound in to bound and returns the result.
/// This uses {Minimizer, Maximizer}::sub_bound
pub fn bound_sub<'a>(
    bound: &DescriptiveBound<'a>,
    sub_bound: &DescriptiveBound<'a>,
) -> Option<DescriptiveBound<'a>> {
    let (relation_kind, new_bound_expr) = match &bound.bound {
        Bound::Le(expr) => (RelationKind::Le, Maximizer::sub_bound(expr, sub_bound)),
        Bound::Ge(expr) => (RelationKind::Ge, Minimizer::sub_bound(expr, sub_bound)),
    };
    // Unwrap new_bound_expr
    // If no substitution was made, just clone the existing bound.
    let new_bound_expr = match new_bound_expr {
        Some(expr) => expr,
        None => return Some(bound.clone()),
    };

    let x = Expr::Atom(Atom::Named(bound.subject));
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

impl<'a: 'b, 'b> Iterator for Minimizer<'a> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        optimizer_next_body!(self)
    }
}
impl<'a: 'b, 'b> Iterator for Maximizer<'a> {
    type Item = Expr<'a>;
    fn next(&mut self) -> Option<Expr<'a>> {
        optimizer_next_body!(self)
    }
}

/// Used internally by {Minimizer, Maximizer}::sub_bound
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
