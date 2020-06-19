# Proof System Overview

Proof verification is done given `provers` which both boil down to implementation of:
```rust
trait SimpleProver<'a> {
    /// Create a SimpleProver with the given requirements.
    fn new(reqs: Vec<Requirement<'a>>) -> Self;

    /// Try to prove `proposition`. This will assume that the requirements passed to `new` are true.
    fn prove(&self, proposition: &Requirement<'a>) -> ProofResult;
}

pub enum ProofResult {
    /// The statement was false.
    False,
    /// The statement cannot be proven either true or false.
    Undetermined,
    /// The statement was true.
    True,
}
```

Effectively, the prove method must decide if `proposition` is or isn't true given the requirements
passed to `new`.

Currently there are two proof methods, the bound method and the graph method, both very different.

These are explained in detail in their respective documents:
- [Bound Method](bound-method.md)
- [Graph Method](graph-method.md)

### A Comparison

The bound method was developed on the premiss of starting with a powerful but expensive algorithm
that could prove almost all propositions, and then optimising and limiting it to create a method
that can still solve most cases.

In contrast, the graph method was developed as a simple and fast method that couldn't solve much but
then extended to prove common cases which it was unable to without increasing the time complexity to
unsuitable levels.

The result of this is two algorithms which both have a worst-case time complexity of O(n²) but
drastically different runtimes.

(The following results are based on the tests in [src/proof/tests.rs](../src/proof/tests.rs))

On my laptop, the times to complete the proof tests (averaged over 15 runs) are:
- Bound method: 209ms;
- Graph method: 51ms;

TODO: Further breakdown of test timings to include times for true/false/undetermined results.

It should be noted that this time also includes parsing and other tests, making the difference not
meaningful as a factor. It does, however, illustrate that the bounds method is significantly slower.

On the other hand, out of 786 tests:
- Bound method passes 768/786 > 97.7% of tests;
- Graph method passes 568/786 > 72.2% of tests;

Overall, the graph method is lightning fast and can prove the majority of propositions whereas the
bound method takes a noticeable amount of time but passes almost all the tests.

Given these results, our intention going forward is to use the graph method for quickly testing most
cases and the bound method for 'lemmas' - which are statements explicitly given by the programmer.
These are proven by the bound method and then can be used by the graph method. This gives us the
performance of the graph method but also the ability to prove almost anything and use the result.
This is super important. If something is true, but the compiler cannot show it, then the person
writing the code would have to bypass the proof system which means that those cases won't be
checked. This opens them up to all sorts of errors which otherwise couldn't occur. The less this
happens, the more successful we have been.

The bound method can also be used to find possible requirements that fix cases where tight enough
requirements aren't given. This is used in error messages to provide user hints.

Pending proper benchmarks, this approach might change.

