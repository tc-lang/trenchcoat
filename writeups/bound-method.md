# The Bound Substitution Method for Proving Inequalities

## Contents
* [Introduction](#introduction)
* [Problem Definition](#problem-definition)
* [Naive Algorithm](#naive-algorithm)
  * Introduction
  * Input Format
  * Aim
  * Algorithm
  * Runtime
  * Budgeting
* [Specifics](#specifics)
* [Optimisations](#optimisations)
* [Current Method](#current-method)


## Introduction

This document describes the bound substitution proof algorithm and some of the reasoning behind it.

Firstly, a naive algorithm will be defined using bound substitution. Optimisations to this will be
proposed and these will form the basis of the current method which will be described at the end.


## Problem Definition

Given, is
- the *requirements* on the function: a set of inequalities which we can assume are true;
- the *proposition*: the inequality to prove or disprove.

The algorithm should determine whether the *proposition* is always *true*, always *false*, or
*undetermined* if they may or may not be true.

Since the algorithm cannot both be perfect and run in a sensible amount of time, an *undetermined*
result may be given if the result is true or false but the algorithm cannot determine this.


## Naive Algorithm

### Input Format

#### Requirements

This algorithm takes `DescriptiveBound`s as the input format for the requirements (what can be
assumed true).

```rust
struct DescriptiveBound {
	subject: Ident,
	bound: Bound,
}

enum Bound {
	Le(Expr),
	Ge(Expr),
}
```

Where `Expr` is a type representing an expression and `Ident` is a type representing a variable
identifier. These will be described in more detail later on.

`DescriptiveBound` represents a bound on a single variable, in terms of an expression (possibly
involving other variables).

An important invariant here is that the `bound` expression does not contain `subject` so that a
`DescriptiveBound` bounds its subject based only on other variables.

The input format of `DescriptiveBound`s is different to that of a set of inequalities as given by
the general problem. Before this algorithm is run, each requirement given is rearranged into a
set of bounds on each of it's variables.

For example, if the following set of requirements was given:
```
1) x + y ⩽ z
2) 3*y ⩽ 3 - z
```
the bounds created would be:
```
x ⩽ z - y                  (from 1)
y ⩽ z - x                  (from 1)
z ⩾ x + y                  (from 1)

y ⩽ (3 - z)/3 = 1 - z/3    (from 2)
z ⩽ 3 - 3*y                (from 2)
```

Of course, perfect rearrangement of any expression would be infeasible and changes of sign add to
this complexity. Rearrangement of linear inequalities and in fact most other common inequalities is
reasonably trivial and can be done in a good time complexity.

We will not go into the details of this algorithm yet, but note that if a requirement cannot be
rearranged to a target bound then it is simply dropped from the input. This means that results
which require more complex requirements (ones which cannot be rearranged) to prove will always give
*undetermined*. This is acceptable from the algorithm specification and important for keeping time
complexity minimal.

#### Proposition

The proposition will be given in the form of just an expression (type `Expr`) that is greater than
or equal to 0 if and only if the proposition is true.

i.e. if `solving` is the expression given for `proposition`, then
```
proposition ⇔ 0 ⩽ solving
```

The proposition will either have the form `lhs ⩽ rhs` or `lhs ⩾ rhs`, making this rearrangement
trivial.

### Aim

The aim is to make substitutions to show that either `solving ⩾ 0` (in which case the proposition
was true) or `solving < 0` (in which case the proposition was false). Any other result will lead to
an undetermined result.

### Algorithm

#### Bound Substituters

There are 2 bound substituters, a *maximizer* and a *minimizer*, each of which substitutes a
`DescriptiveBound` into an `Expr` to generate a new `Expr`:
- *Minimizer* finds a lower bound of the expression; a minimum value, given the bound.
- *Maximizer* finds an upper bound of the expression; a maximum value, given the bound.
These algorithms are fairly obvious but they will be described further in
[Specifics → Bound Substitution](#bound-substitution).

#### Proof Algorithm

```
/// Attempt to prove `proposition` given `requirements`
function prove(proposition: Relation, requirements [DescriptiveBound]) -> ProofResult {
	// Create solving such that proposition ⇔ solving ≥ 0, as described above.
	let solving = proposition.ge0()
	// Generate the bounds specified by requirements, as described above.
	let bounds = requirements.bounds()

	if is_greater_or_equal_to_0(solving, bounds) {
		return True
	} else if is_less_than_0(solving, bounds) {
		return False
	} else {
		return Undetermined
	}
}

/// Tries to prove `solving ≥ 0` given `bounds`.
function is_greater_or_equal_to_0(solving: Expr, bounds: [DescriptiveBound]) -> bool {
    // Test if this is directly true.
    // (Comparing expressions to 0 will be detailed later; it is not overly complex)
    if new_solving >= 0 {
	    return true
    }

    // Otherwise, make substitutions to try and prove the result.
	for bound in bounds {
		// Substitute this bound to create a lower bound for `solving`
		// Since new_solving ≤ solving, 0 ≤ new_solving ⇒ 0 ≤ solving
		let new_solving = Minimizer.sub(solving, bound)

		// Now try to prove `new_solving ≥ 0` given all the bounds we have not yet used.
		// If it is true, then, as above, `solving ≥ 0` is true.
		// Otherwise, the loop will try another substitution.
		if is_greater_or_equal_to_0(new_solving, bounds.exclude(bound)) {
			return true
		}
	}
	return false
}

/// Tries to prove `solving < 0` given `bounds`.
/// This is essentially the same as is_greater_equal_to_0 however with <0 comparisons and upper
/// bounds.
function is_less_than_0(solving: Expr, bounds: [DescriptiveBound]) -> bool {
    // Test if this is directly true.
    if new_solving < 0 {
	    return true
    }

    // Otherwise, make substitutions to try and prove the result.
	for bound in bounds {
		// Substitute this bound to create a lower bound for `solving`
		// Since new_solving ≥ solving, 0 > new_solving ⇒ 0 > solving
		let new_solving = Maximizer.sub(solving, bound)

		// Now try to prove `new_solving < 0` given all the bounds we have not yet used.
		// If it is true, then, as above, `solving < 0` is true.
		// Otherwise, the loop will try another substitution.
		if is_less_than_0(new_solving, bounds.exclude(bound)) {
			return true
		}
	}
	return false
}
```

The `is_ge_0` and `is_less_than_0` functions can also be thought of as constructing a tree, where
each function call is a node and each recursive call is a child. The `solving` value of a nodes
children would be the `solving` value of the parent each with a different substitution made.

A clear alternative algorithm from this model is a breadth first search approach. This will be
explored later on however (when paired with other optimisations) turns out not to be faster.

### Runtime

Thinking of the algorithm as a tree, it is clear that in the worst case, each child has
`len(bounds)` children and each child has one less bound. This makes the worst case number of nodes
*n!* where *n* is the number of starting bounds (which is notably very likely to be greater than the
number of requirements).

### Budgeting

One way to improve this worst-case runtime is to limit the depth of the tree it creates - i.e.
limiting the number of recursive calls.

If this is done, making the limit *m* recursive calls (or a tree depth of *m*+1), then the
worst-case runtime becomes:
`O( n (n-1) (n-2) ... (n-m) ) = O( n^(m+1) )`

The tree can still get incredibly wide if a lot of bounds are given, meaning that there is still
quite a long runtime despite it having a polynomial worst case.

This is also quite restrictive since it sets a hard limit on the number of requirements you can use
within a proof.  While there are many quite complex cases don't require making many substitutions,
there are also many that do - many simple cases, too. Take a long chain such as:
```
a ≤ b
b ≤ c
c ≤ d
d ≤ e
e ≤ f
```
The proof that `a ≤ f` is simple but yet requires 5 substitutions meaning that the depth limit would
have to be at least 5.


## Specifics

This section will go over the specifics of the main types and the algorithms used to manipulate
them.

The proof algorithms can be read without the details in this section so feel free to skip to
[Optimisations](#optimisations) if you are just looking for the big picture. Do however note that
these form the fundamental machinery behind the current method, hence the limitations of them as they
are currently implemented limits the capability of the proof method.

The scope of these algorithms is intentionally left reasonably simple. Whilst they are capable,
they could be significantly more capable with just a little more work. However more complexity leads
to more possible bugs, potentially worse time complexity and more to maintain.

Currently, the focus is on primarily proving linear inequalities for which these algorithms are
perfectly capable. This is considered okay since the vast majority of cases encountered will be
linear.

These types and algorithms can change with no effect on the proof algorithms. This makes adding
complexity, if required, very easy thus making this method relatively extensible in terms of what it
can solve (for example, currently only linear factors can be taken out whereas, if quadratics could
be factorised then quadratic inequalities could also be proven).

### Expr

Expressions are represented with:
```rust
enum Expr {
    /// -e
    Neg( &Expr ),

    /// 1/e
    /// The bool represents the rounding direction:
    ///   Recip(x, false) = 1//x (round down)
    ///   Recip(x, true)  = 1/^x (round up)
    Recip( &Expr, bool ),

    /// e[0] + e[1] + ...
    Sum( [Expr] ),

    Atom( Atom ),

    /// e[0] * e[1] * ...
    Prod( [Expr] ),
}

enum Atom {
    Named( Ident ),
    Literal( Integer /* Later Rational */ ),
}

struct Ident {
	name: String,
	// other fields ommited
	// equality and ordering is based purely on the `name` field
}
```

This representation can model any expression consisting of addition, subtraction, multiplication and
division which is a broad scope and not very limiting, at all, for the purpose of this proof system.

A notable omission is that of powers and roots. This, as discussed later, limits the proof systems
ability to tightly bound polynomials.

#### Simplification

The idea behind simplification is to put expressions into a form that make the algorithms that
manipulate them much simpler to write and also keeping the size of expressions minimal to improve
runtime and remove duplicated substitutions.

The simplification rules are heavily dependent on how the following algorithms are implemented and
hence will not be fully documented here.

Current rules include, but are not limited to:
- cancelling terms in sums and products (for example `x-x=0` or `x*1/x=1`),
- grouping like terms with literal coefficients (for example `x+3*x-2*x=2*x`),
- flattening sums and products (for example `a+(b+c)+d+(e)=a+b+c+d+e` or `a*(b*c)=a*b*c`),
- performing calculations on literals (for example `2+3=5` or `6/3=2`),
- removing double negation (for example `-(-x)=x`),
- sorting terms of sums and products (this is *really* useful).

The full rules for simplification and the implementation can be found in:
[src/proof/expr.rs](https://github.com/tc-lang/trenchcoat/blob/5b906009b62cb438d32300048fad46a2ebd10174/src/proof/expr.rs#L62)

#### Bound Substitution

There are 2 ways in which bounds can be substituted (as used earlier):
- *Minimizer* finds a lower bound; a minimum value.
- *Maximizer* finds an upper bound; a maximum value.

The algorithms for these are fairly trivial.

- If the input expression is just the variable being substituted, then:
  - if the expression is being *minimized* and the bound is a lower bound, the bound replaces
    the variable directly;
  - if the expression is being *maximized* and the bound is an upper bound, the bound replaces
    the variable directly;
  - else the variable is left as was.
- If the input expression is another variable, it is left as was;
- if the expression is a Neg or a Recip, then the bound is the opposite substituter applied to the
  inner expression, wrapped in Neg or Recip - for example a lower bound of `-x` is `-(upper bound on
  x)`;
- if the expression is a Sum, the terms of the sum are replaced by the substituter applied
  individually to each term - for example a lower bound of `a + b` is `(lower bound of a) + (lower
  bound of b)`;
- if the expression is a Prod, then the general process isn't trivial. For now, we just bound
  scalar multiples of a single non-literal expression that we can substitute into. This case is
  simple: `a*b*c*(expr)` can be replaced with `a*b*c*(subbed expr)` if `a`, `b` and `c` are all
  literals. This works for all linear cases, which is the current focus.
  There are simple methods to handle more cases although cases that require them don't seem to
  occur frequently and if they do, these methods can be easily added with very little modification
  to other code.
- If the expression is a literal or a product of literals, it is left as was;
- else the substitution failed and so a bound is not given.

For the full implementation, see [src/proof/fast_optimiser.rs](https://github.com/tc-lang/trenchcoat/blob/9826856639651b62676cba24e3456c971a42dfa3/src/proof/fast_optimiser.rs#L579).

Since this was written, the method for handling products has been improved to do fast checks on
signs of variables to allow it to prove more cases. This work is still in progress and this section
will be updated when complete. The link above links to an older implementation.

#### Rearranging

##### Relations

Rearrangement is done in terms of the `Relation` type:
```rust
struct Relation {
	left: Expr,
	kind: RelationKind,
	right: Expr,
}

enum RelationKind {
	/// Less than or equal to (<=)
	Le,
	/// Greater than or equal to (>=)
	Ge,
}
```

The method behind rearranging is based on the principle that if `x` occurs exactly once and only
in the left hand side of an inequality, then rearranging is more of an 'unwrapping' process, where
you apply the inverse of what's applied to the expression containing `x`.

So, a high level overview of the algorithm to rearrange `relation` to make `x` the subject:
- rewrite `relation` so that `x` occurs exactly once and only in the left hand side;
- 'unwrap' `x` in the LHS by applying inverses to both sides (this may flip the inequality).

For example:
```
3*x - y*x + z <= a*b
   { rewrite }
=> x*(3-y) + z <= a*b
   { inverse +z }
=> x*(3-y) <= a*b - z
   { inverse *(3-y) }
=> x <= (a*b - z) / (3 - y)
   Note that this will only occur if the sign of 3-y is known and if negative the relation would be
   flipped.
```

The implementation can be found at: [TODO]

##### Singling and Factoring

The process above depends on being able to rewrite a relation to only include `x` once.

The first stage of this is manipulating the relation so that `x` occurs only on the LHS. This is
simple as you can check which side(s) contains `x` and either leave the relation unchanged, flip
the relation, or subtract one entire side from both sides.

Rewriting the expression of the LHS to only include `x` once is the more complex aspect.

Below is a simple algorithm which is currently the one used. It succeeds only if `x` is linear, i.e.
it cannot handle `x*x` or `x*x + x`. In principle, it would be easy to extend to handle such cases,
although it would require adding powers and roots to Expr to allow for the unwrapping of expressions
such as `x³` or `(2*x+3)²`. Such an addition would add to complexity and is not currently deemed
necessary, but it is something to bear in mind as a potential improvement that may be made.

Note that the algorithms below assume that the expression is simplified, specifically, it assumes
that:
- Sums and Prods are flattened (i.e. they do not contain, as direct children, other Sums or Prods),

To factor `x` from an expression (returns `expr/x` if `x` can be cleanly factored or otherwise None):
- If the expression is `x`, the factored expression is 1;
- if the expression is another atom, it cannot be factored;
- if the expression is a literal, it cannot be factored;
- if the expression is a Neg, the factored expression is -(factored inner expression);
- if the expression is a Recip, the factored expression is 1/(inner expression factored with
  1/x);
- if the expression is a Sum, the factored expression is the sum of its terms, each factored;
- if the expression is a Prod, the expression can only be factored if exactly one term contains
  `x`. If so, then the factored expression is the product of the factored term containing `x` and
  the rest of the terms.

To rewrite an expression to contain `x` exactly once:
- If the expression is an Atom, leave it as was;
- if the expression is a literal, leave it as was;
- if the expression is a Neg, then rewrite inner expression to include exactly one `x` and wrap the
  result in a Neg;
- if the expression is a Recip, then rewrite inner expression to include exactly one `x` and wrap the
  result in a Recip;
- if the expression is a Sum, collect the terms containing `x` into `x_terms` and the other terms
  into `other_terms` then the singled expression is `x*factor(x_terms, x) + other_terms`;
- if the expression is a Prod and more than one term contains `x`, it cannot be rewritten;
- if the expression is a Prod and exactly one term contains `x`, it is rewritten as the product
  of the other terms and the term containing `x`, rewritten;
- if the expression is a Prod not containing `x`, leave it as was.

For more details, the implementation can be found at: [TODO]

#### Comparing with 0

Comparison with 0 can be done by evaluating the simplified expression.

If a variable is within the expression then it can't be evaluated. This is a perfectly valid way
of comparing expressions with 0 in the context of this algorithm since, if the expression contains
a variable, to have a known difference with 0, the variable must be bound in terms of a literal.

For example, if everything gets simplified to:
```
0 <= z + 2
```
For that to be true, you require -2 <= z.

If we have such a bound, or one which is tighter, it would be substituted and so the expression
could be evaluated at that node instead.

This doesn't require things to be explicitly bounded by literals since bounding a variable in terms
of another is the same as bounding their difference by 0.

Consider:
```
a <= b
```
If trying to prove:
```
a <= b+1
```
The expression to be bounded would be:
```
b-a+1
```
Substituting `b >= a` gives:
```
b-a+1 >= a-a+1 = 1
```
And hence the algorithm succeeds.

This emphasises that cancellation is an important aspect to simplification; otherwise, `a-a+1` would
not be simplified to remove the `a` making evaluation impossible.

#### Evaluation

Evaluation seems simple but is in fact an absolute pain because we need to simplify expressions...
But that changes division and therefore rounding order (since things get multiplied out and recips
reordered).

This section will be written up in more detail at a later stage because a good method for this has
not yet been properly decided. For now, evaluation is done with exact rational numbers and rounded
at the end. This is done in a way which cannot lead to an incorrect True/False result but can lead
to loose bounds making some True/False results undetermined. This isn't very common.

These rational numbers are also not kept in a simplified form. While algorithms such as the Binary
GCD Algorithm can be used to keep rational numbers simplified with O(n²) (where n is the maximum
number of bits) time complexity, this would be called quite often and for numerator and denominator
values to get high enough to cause performance problems, the number of variables and their values
would have to be unreasonably high - and if this is the case, the final system will not break,
since values will be unbounded but it will perform badly.

Though, some very basic simplification is carried out: for example, if the
numerator and denominator perfectly cancel or if one of them is 0.

#### Linear Only?

These algorithms are designed for general expressions as opposed to just linear expressions.

This can make the method much more powerful however it may not be necessary in the context
of proofs within programming languages. Various discussions have all led to the conclusion that
non-linear requirements are likely to be incredibly rare.

The algorithms above become much simpler and therefore a bit faster when you know that the
expressions are all linear and have a more appropriate representation for them; this is due to the
lack of having to do more allocation and having less things to check. This would likely be similar
(if not exactly) what can be seen in the graph based method.

This isn't to say that non-linear proofs should be removed. If the compiler cannot prove something,
it would have to be asserted using 'unsafe' features - where a statement is not verified.
Using such features would be prone to human error, especially in cases that are too complex for
the compiler.

This is to say that a faster version of the bounds method could be written, using a different
expression type specialized for linear inequalities. Likely, this would just require creating such
a type, since the bounds method algorithms can be generic. This method may be faster than the
existing bounds method (as will be described later) but slower than the graph method. It would
however be able to solve much more than the graph method (almost all linear inequalities) but
less than the existing bounds method which can also solve non-linear inequalities. It could act as
a middle ground both in terms of capability and performance.

More research will be done on this very soon.


## Optimisations

The naive algorithm described above is highly inefficient and, when budgeted, has clear rough edges.

This section will cover *some* of the possible optimisations that were considered before the current
algorithm was decided upon.

### Only Substitute Each Requirement Once

Making 2 substitutions from the same requirement in a row is equivalent to just making 1
substitution.

Consider the following example:
```
Prove: 0 <= x + 2*y
Requirement | Bounds
 0 <= x + y | x >= -y
            | y >= -x
```

```
				x + 2*y + z
              /            \
          {x >= -y}    {y >= -x}
             y+z          -x+z
              |
          {y >= -x}
            -x+z
```
Here, making the second substitution on the left child yielded the same result as making that
substitution to the root (as was done for the right child).

Generally, only one substitution per requirement needs to be made throughout the entire tree.

### When Order Matters

It's clear that the order in which you make substitutions matters if nothing else is done.

A simple example case is substituting:

1) `a ≤ b`
2) `c ≤ b`
3) `0 ≤ a`

In to `a-c+b` to find a lower bound.

If (1) `a ≤ b` is substituted first, then the lower bound returned is `a-c+a=2*a-c`; if (2) is
substituted next, then the returned bound is `2*a-b` and then the next substitution can only be (3)
`0 <= a` so `-b` is returned. Whereas if the substitutions are made in the opposite order, then (3)
→ `-c+b`; (2) → `-b+b=0` so a different lower bound is yielded.

In the later case, the bound method would have concluded that `c ≤ a+b` but the first case would
have yielded undetermined.

If bounds are substituted not only into the expression but also in to the other bounds, the order of
substitution no longer matters.

This causes another problem however; consider:
```
0 ≤ a
b ≤ a
1 ≤ b
```
There are 2 possible substitutions for `a` (`a ≥ 0` and `a ≥ b`). Once one is substituted, the other
one cannot be. In fact, this is the case exactly when a substitution is on the same variable and has
the same relation kind (whether it is an upper or lower bound).

This leads to the following lemma: If bounds are grouped into *permutation groups*, where bounds
are in the same group if and only if they have the same subject and the same relation kind (i.e.
they are both Le or Ge values), then the order in which you make substitutions within permutation
groups *does* matter but the order between permutation groups *does not*. (Note that this says
nothing about the choice of bounds to substitute.)

This means that if bounds are sorted into their *permutation groups*, an arbitrary order to
substitute each group in can be chosen and then the only bounds which must be permuted are those
within the same *permutation group*. This drastically reduces the breadth of the tree.

In the example above, the permutation groups would be:
```
a ≤ _ : [a ≤ b]
a ≥ _ : [a ≥ 0]
b ≤ _ : []
b ≥ _ : [b ≥ a, b ≥ c]
c ≤ _ : [c ≤ b]
c ≥ _ : []
```
This shows that the only substitutions that must be permuted with each other are `b ≥ a` and `b ≥ c`
\- the order of the rest does not matter.

Importantly, this does not hold if bounds are not also substituted into all other bounds. For a
simple counter example, choose the bounds:
```
a ≤ d
0 ≤ a
```
to minimize `a+d`.

If the `d ≥ _` permutation group is chosen first, `2*a` is given as a lower bound which then leads
to `0` whereas if the `a ≥ _` permutation group is chosen first, `d` is given as a lower bound which
then leads to `a` again. If `a ≥ 0` was also substituted into the `a ≤ b` requirement though, this
would have led to the same lower bound of `0`.

This almost\* doesn't change the capability of the algorithm.

### Greedily Making Substitutions

The above optimisation only makes a statement about the order of the substitutions, not the
substitutions that should be made.

It is in fact almost\* okay to make all substitutions we can if the permutation group optimisation
is also applied.

TODO: Elaborate (this is hard to prove though...)

### Almost\*

In a couple of cases above, I mentioned that they "almost\*" don't change the capability of the
algorithm.

This is because, when applied, these optimisations enforce that if a substitution for, say, `x` is
made it must also be made in all other cases where `x` pops up (since it's also substituted into
all bounds).

The naive algorithm had the ability to occasionally use different substitutions for the same
variable.

To illustrate this point, consider the following example:
```
TODO
```

This also demonstrates a limitation even of the naive algorithm; since `2*a=a+a` different
substitutions could be made for both those different values of `a`. Similarly for `a = a/2 + a/2`.
This is something that cannot be reasonably accounted for but since the naive algorithm doesn't make
substitutions to the bounds, the same variable could be reintroduced later on and a different bound
substituted making this possible in some cases. Applying the permutation group optimisation removes
the ability for this to happen.

In the tests written for the proof system, this only occurs once.

### Don't Calculate All the Bounds

A clear expense in the algorithm so far is that *all* the bounds given by *all* the requirements are
computed before the algorithm is run.

This is never necessary if only one bound is substituted per requirement and substitutions are made
greedily (as suggested earlier). It is also unlikely that all the requirements will be substituted
which makes even more of the bounds redundant.

Instead, only the bounds required can be computed.

Moreover, if substitutions are made to the requirements as well as the proposal (as discussed
above), keeping track of bounds individually requires the substitutions to be made to all of the
bounds - even though the bounds on a requirement are all derived from a single relation. It is much
cheaper to make the substitutions on the requirements (since there are less of them) and derive the
bounds when required.

Also, if bounds are stored as a single expression like the proposition (one where `0 ≤ expr ⇔
requirement`) then a substitution only needs to be made into one expression per requirement.


## Current Method

This section will describe the current method, based on the optimisations described above.

### Input Format

Each requirement (`req`) is converted to an expression (`expr`) such that `req ⇔ expr ≥ 0`.

As described earlier, this rearrangement is trivial.

The proposition to solve (`prop`) is given in the same format: `prop ⇔ solving ≥ 0`. This *ge0
expression* for the proposition will be referred to as `solving`.

### Algorithm

#### Bound Substituters

There are 2 bound substituters, a *maximizer* and a *minimizer*, each of which substitutes a
`DescriptiveBound` into an `Expr` to generate a new `Expr`:
- *Minimizer* finds a lower bound of the expression; a minimum value, given the bound.
- *Maximizer* finds an upper bound of the expression; a maximum value, given the bound.
Both of these were described in more detail in [Specifics → Bound Substitution](#bound-substitution)

#### Optimiser Trees

This is either a *minimizer tree*, in which case its subsituter is the *minimizer substituter*, or a
*maximizer tree*, in which case its subsituter is the *maximizer substituter*.

Each node has:
- solving: the expression to substitute bounds into;
- given: the list of requirements in the form proposed earlier (`given[i] ≥ 0 ⇔ requirement[i] ∀i`);
- its children.

(Where this is going: the `solving` value of each node in a *minimizer tree* will be a lower bound
of its parent; likewise for a *maximizer tree*, each node's `solving` value will be an upper bound of
its parent.)

The root node starts with `solving` created directly from the proposition and `given` created
directly from the requirements as described above.

If `solving` contains no variables, this node yields `solving` as a bound.

Otherwise, each node chooses a variable from `solving` (*x*) and tries to rearrange each of the
requirements (from it's *ge0 expression*) into a bound on *x*. If one is found, the rest of the
requirements are rearranged to make *x* the subject and bounds with the same relation kind are
collected to form a *permutation group* (as defined in the [Optimisations](#optimisations) section).
Otherwise, if none of the requirements specify a computable bound, a different variable is chosen
or, if no more choices can be made, the node yields `solving` as a bound.

It should be noted that the method for choosing variables does not particularly matter but the
chosen method here is to select variables in sorted order based on their names. This is due to the
method of removing duplicates from the variables searched and any other order would likely make very
little or no difference.

For each `bound` in the *permutation group*, a child is created.

The child's `given` values are created by using the *Maximizer substituter* to substitute the chosen
bound to produce upper bounds on the current node's own `given` values.

This produces a list of requirements such that `∀j ∃i 0 ≤ new_given[j] ⇐ 0 ≤ given[i] ∧ bound`.

This is due to the fact that `bound`, `0 ≤ given[i] ≤ new_given[j]`.

Then, the child's `solving` value is given by using the optimiser's own substituter on its `solving`
value and the chosen bound. Hence, for a *minimizer tree*, the child's `solving` value is a lower
bound and for a *maximizer tree* the child's solving value is an upper bound.

In the case of a *minimizer tree*, this gives: `0 ≤ new_solving ⇒ 0 ≤ solving`; in the case of a
*maximizer tree*, this gives: `new_solving < 0 ⇒ solving < 0` and so if the child yields a bound to
prove that its expression is the correct side of 0, it is also implied for all of its parents. This
fact forms the basis of the proof algorithm.

Moreover, the requirements given to the child are the requirements of the current node, excluding
the requirement that specified the bound being substituted. This stops the same requirement being
substituted more than once.

If the child's `solving` value is equal to it's parents, then the child is not created and another
variable is selected. If this is the case for one child (so perhaps the first child), it will be true
for all children and thus the rest shouldn't be generated. The algorithm on this node should
essentially start again, choosing another variable if one exists or yielding if not.

##### Optimiser Tree Example

TODO

#### Proof Algorithm

Using all of this, the proof algorithm is quite simple:

```
fn prove(proposition: Relation, requirements: [Relation]) -> ProofResult {
	// Convert the Relations to their ge0 expression as required.
	// Here, the ge0 method creates the ge0 expression as described before.
	let solving = proposition.ge0()
	let given = requirements.map( requirement => requirement.ge0() )

	// Create a minimizer tree with solving and given
	let minimizer = Minimizer.new(solving, given)

	// Loop over the yielded bounds and, if one is ≥ 0, the result is true.
	for lower_bound in minimizer {
		if lower_bound >= 0 {
			return True
		}
	}

	// Create a minimizer tree with solving and given
	let maximizer = Maximizer.new(solving, given)

	// Loop over the yielded bounds and, if one is < 0, the result is true.
	for upper_bound in maximizer {
		if upper_bound < 0 {
			return False
		}
	}

	// If the result was not proven true or false then it is undetermined.
	return Undetermined
}
```

#### Time Complexity

The running time is maximized when the permutation groups all have the same size. With *g*
permutation groups, they would have a size of *n*/*g*. The worst case number of nodes is therefore
(*n*/*g*)^*g*.

The value of *g* to maximize this is *g*=*n*/*e* so the worst case time complexity is
O(*e*^(*n*/*e*))

This is still not an acceptable time complexity.

#### Budgeting

Like the naive method, this time complexity isn't acceptable in most cases. To solve this, a
budgeting approach is taken to limit the amount of work the algorithm does before it fails. The
naive budgeting had various pitfalls which this method tries to avoid.

Each node in an optimiser tree is assigned a budget. This budget is, roughly speaking, the number of
substitutions it is allowed to make - although to make counting cheaper this isn't overly precise.

A node first spends its budget on making substitutions to the proposition and the requirements to
generate the values for its children. The budget spent is calculated as the number of children to be
created, multiplied by the number of requirements (this is approximately the number of substitutions
that would be made) and subtracted from the nodes budget. It then splits the remaining budget
equally between its children which each follow the same process.

The node does not attempt to generate their permutation group and children if they have no budget.
If they do have any budget, then they complete this process entirely even if this makes its budget
negative. This is to save complexity in this process as it happens quite frequently. In this case,
its children each receive no budget and when the node is given extra budget (see below) it does not
distribute any to its children until it has become positive again.

Budgets must also be recovered. For example, consider a chain:
```
a ≤ b
b ≤ c
c ≤ d
d ≤ e
e ≤ f

a ≤ z
```
and an attempt to prove that `a ≤ f`.

The minimizer tree for `f-a` would look like:
```
f-a  ≥ f-z
   \ ≥ f-b ≥ f-c ≥ f-d ≥ f-e ≥ 0
```
Here, the `f-z` child would use no budget since it makes no further substitutions whereas the `f-b`
child makes quite a few and so would spend its budget. If this budget was not high enough then the
`f-b` node may run out of budget even if the `f-z` node did not spend its. This can be solved.

If all of a node's children either finish or run out of budget, then the node collects the remaining
budget from all its finished children and distributes it evenly to the 'starved' children (the ones
which would like more budget).

When a child receives extra budget, it first clears any negative budget and then distributes the
amount of surplus evenly to its children.

This process repeats until either all nodes finish or there are no finished children to collect
budget from when the budget runs out.

Also, since budgets can only be spent in integer amounts, they will be stored as integers. If a node
cannot perfectly divide its budget between its children then it distributes the maximum possible,
even, amount to each node and retains the leftover budget. If extra budget is received, it will be
added to the retained budget and the new total distributed.

This approach allows budgeting to be effective for both keeping the depth of a wide tree shallow
and allowing a narrow tree to become deep.

#### Implementation

The implementation of this algorithm can be found in
[src/proof/fast_bound_method.rs](../src/proof/fast_bound_method.rs)

