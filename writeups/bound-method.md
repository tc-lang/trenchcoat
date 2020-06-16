The bounds substitution method for prooving inequalities

## General Problem

Given, is
- the requirements to the function: a set of inequalities which we can assume are true;
- the inequality to prove.

The algorithm should determine wether the inequality given to solve is:
- always true given that the requirements are true,
- always false given that the requirements are true,
- or 'undetermined' if they may or may not be true.

Since the algorithm cannot both be perfect and run in a sensible amount of time, an 'undetermined'
result may be given if the result is true or false but the algorithm cannot determine this.

## Nieve algorithm

### Introduction

This algorithm is a nieve approach based on the principles of bound substitution to solve the
problem described above.

The final bounds method is effectively a heavily optimised and restricted version of this
algorithm.

### Input Format

#### Requirements

This algorithm takes `DescriptivBound`s as the input format for the requirements (what can be
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

As you can see, a `DescriptiveBound` represents a bound on a single variable, in terms of an
expression possibly involving other variables.

An important invariant here is that the `bound` expression does not contain `subject`, so a
`DescriptiveBound` bounds its subject based only on other variables.

The input format of `DescriptiveBound`s is different to that of a set of inequalities as given by
the general problem. Before this algorithm is run, each requirement given is rearranged in to a
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

We will not go in to the details of this algorithm yet, but note that if a requirement cannot be
rearranged to a target bound then it is simply dropped from the input. This means that results
which require more complex requirements (ones which cannot be rearranged) to prove will always give
'undetermined'. This is acceptable from the algorithm specification and important for keeping time
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

The aim is to make substitutions to show that `solving` is either ⩾ 0 (in which case the
proposition was true) or < 0 (in which case the proposition was false). Any other result will lead
to an undetermined result.

### Algorithm

```
function is_true(solving: Expr, bounds: [DescriptiveBound]) -> bool {
	for bound in bounds {
		let new_solving = sub(solving, bound)
		if new_solving >= 0 {
			return true
		}
		return is_true(new_solving, bounds.exclude(bound))
	}
	return false
}

function is_false ...

function prove(proposition: Relation, given [DescriptiveBound]) -> ProofResult {
	let solving = proposition.ge0()
	let bounds = given.bounds()

	if is_true(solving, bounds) {
		return True
	} else if is_false(solving, bounds) {
		return False
	} else {
		return Undetermined
	}
}
```

### Runtime

n!

### Budgeting

One way to improve this worst-case running time is to limit the depth of the tree it creates - i.e.
limiting the number of recursive calls.

If this is done, then the worst-case running time becomes:
O( n (n-1) (n-2) ... (n-m) ) = O( n^m )

The bredth of the tree can still get incredibly high if a lot of bounds are given, meaning that
there is still quite a long runtime.

### Performance Pitfalls and Obvious Optimisations

We will now discuss the optimisations that can be made the nieve algorithm described above.

The nieve algorithm above is incredibly powerful in terms of the statements it can prove however
its time complexity makes it 

## Specifics

### Expr

Expressions are 

```rust

```

#### Simplification

The idea behind simplification is to put expressions in to a form that make the algorithms that
manipulate them much simpler to write.

The reasoning behind most of these desisions is probably faily obvious. Places in the code which
depend on particular rules are commented with what they assume.

#### Rearranging

##### Relations

The method behind rearranging is based on the principlele that if `x` occurs exactly once and only
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
   { inverse (3-y) }
=> x <= ((a*b) - z) / (3 - y)
   Note that this will only occur if the sign of 3-y is known and if negative the relation will be
   flipped.
```

##### Singling and Factoring

The process above depends on being able to rewrite a relation to only include `x` once.

The first stage of this is manipulating the relation so that `x` occurs only on the LHS. This is
simple as you can check which side(s) contains `x` and either leave the relation unchanged, flip
the relation, or subtract one entire side from both sides.

Rewriting the expression of the LHS to only include `x` once is the more complex aspect.

#### Comparing with 0

Comparison with 0 can be done by evaluating the expression!

If a variable is within the expression, then it cannot be evaluated. This is a perfectly valid way
of comparing expressions with 0 in the context of this algorithm since if the expression contains
a variable, to have a known difference with 0 it must be bound in terms of a literal.

For example, if everything gets simplified to:
```
0 <= z + 2
```
Then for that to be true, you require -2 <= z.

If we have such a bound, or one which is tigher, it would be substituted and so the expression
could be evaluated.

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
The expression that would be bounded would be:
```
b-a+1
```
Substituting `b >= a` gives:
```
b-a+1 >= a-a+1 = 1
```
And hence the alorithm succeds.

#### Evaluation

Evaluation seems simple but is in fact an absolute pain because we need to simplify expressions...
But that changes division order - since things get multiplied out and recips reordered.

This section will be written up at a later stage, since a good method for this has not yet been
properly decided. For now, evaluation is done with exact rational numbers and rounded at the end.
This is done in a way which cannot lead to an incorrect True/False result but can lead to loose
bounds making some True/False results undetermined. This isn't very common.

These rational numbers are also not kept in a simplified form. While algorithms such as the Binary
GCD Algorithm can be used to keep rational numbers simplfied with O(n^2) (where n is the maximum
number of bits) time complexity, this would be called quite often and for numerator and denominator
values to get high enough to cause performance problems, the number of variables and their values
would have to be unreasonably high - and if this is the case, the final system will not break,
since values will be unbounded but it will perform badly.

Some, basic simplification is done though - for example, if the numerator and denominator perfectly
cancel or if one of them is 0.

#### Linear Only?

These algorithms are designed for general expressions as opposed to just linear expressions.

This can make this proof method much more powerful however it may not be necessary in the context
of proofs within programming languages. Various discussions have all lead to the conclusion that
non-linear requirements are likely to be incredibly rare.

The algorithms above become much simpler and therefore, due to the lack of having to do more
allocation etc a bit faster when you know that the expressions are all linear and have a more
appropriate representation for them - similar to what can be seen in the graph based method.

This isn't to say that non-linear proofs should be removed. If the compiler cannot prove something,
then it would have to be asserted using 'unsafe' features - where a statement is not verified.
Using such features would be prone to human error, espeicially in cases that are too complex for
the compiler.

This is to say that a faster version of the bounds method could be written, using a different
expression type specialized for linear inequalities. This would likely just require creating such
a type, since the bounds method algorithms can be generic. This method may be faster than the
existing bounds method (as will be described later) but slower than the graph method. It would
however be able to solve much more than the graph method (almost all linear inequalities) but
less than the existing bounds method which can also solve non-linear inequalities. It could act as
a middle ground both in terms of capability and performance.

More research will be done on this very soon.

## Current Method

### Introduction

This section will describe the current method

