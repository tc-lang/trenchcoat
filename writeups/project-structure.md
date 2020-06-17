# Trenchcoat Project Structure

**Table of contents**
* [Overview](#overview)
* [Token Trees](#token-trees)
* [Parsing](#parsing)
* [Verification](#verification)
* [Execution](#execution)

## Overview

```
+-------------+                   
| Source code | --> Tokenizer ------>---+
+-------------+                         |
                                  +------------+
    +---------<-----  Parser  <-- | Token tree |
    |                             +------------+
+-------+                +---------------------------------+
|  AST  | --> Verify --> | [ Either TypeError ProofError ] |
+-------+                +---------------------------------+
    |                  +--------+
    \-------> Exec --> | Output |
                       +--------+
```

Generally, the flow of the program is fairly linear. Given a single file as input, the `tokens`
submodule produces a token tree (as described in the next section). Assuming that the tokenizing was
successful, the parser constructs the AST. This is in the appropriately-named submodule `ast`.

From this point, there are two processes that act on the AST. The first of these is general program
verification (housed in the submodule `verify`), which largely does three things: (1) ensuring all
names are in scope, (2) type-checking (using `src/types`), and (3) proof validation (using
`src/proof`). If there are no errors in verification, the AST will be interpreted directly by the
`exec` submodule.

## Token Trees

Token trees are a concept that is worth discussing briefly. The term seems to have originated within
Rust. Token trees are defined by requiring certain delimeters to always be matched with their
respective closing delimeter - e.g. `(` requires `)` and `{` requires `}`. The token tree itself is
then defined by treating tokens within parenthesized blocks as children of their containing
parenthesis token and all other token kinds as having no children.

This creates a structure that is easier for the parser module to work with. The following input, for
example:
```
let x = (a + b) - c;
```
becomes:
```
     --------- Root ----------
    /   /  /     |    \   \   \
"let" "x" "=" (     ) "-" "c" ";"
               / | \
            "a" "+" "b"
```

## Parsing

Most of the parsing operations are fairly standard, but there are a few things to note. Firstly,
"proof statements" exist outside of function bodies and are given their own submodule within `ast`
in order to separate those two implementations. Secondly, instead of using a shift-reduce parser,
most of the functions that produce AST types are given a set of tokens with which to parse the
entirety of that structure. For example, an expression (represented by the `Expr` type) might be
expected to construct an expression with the tokens `[``"``x``"``,` `"``+``"``,` `"``y``"``]`,
instead of consuming as much of the token tree as is necessary. This is also reflected in the
implementation of binary operator parsing; it is done with the same strategy as mentioned above,
which it has `O(n^2)` time complexity, instead of a more advanced method.

## Verification

As mentioned above, there are broadly three distinct properties that are checked during
verification. These all occur in a single pass, but will be described separately. The first is that
all variables and functions referenced are in scope (note that functions are special; they cannot be
considered first-class variables). Scoping is represented by a series of linked scope items - single
variables and their types. All top-level definitions are functions (and vice versa), so a separate
"top-level scope" is provided for accessing information about functions. Whenever a new variable is
defined (via the let keyword), the succeeding statements are verified with a new scope, created with
the addition of the variable definition.

```rust
struct Scope {
    item: Option<ScopeItem>,
    parent: Option<&Scope>,
    top_level: &HashMap<&str, Func>,
}
```

The second process is type-checking. Because there are no parameterized types, type checking (and
with it, type inference) is fairly simple; it is only operators (logical, comparison, and
arithmetic) and function calls that determine types. This is done directly. There is a pattern among
many of the functions in the `verify` module to - as one of the returned values - give the type that
an expression produces, which is recursively used to determine the type of each expression (which
includes variables).

For only those expressions that evaluate to integer types (either `Int` or `UInt`), the prover
tracks their relations, assigning temporary variable names where necessary, of the form `<n>`,
where `n` is a unique identifier. This is used in the prover via a process of variable definitions
to transform requirements. For example, given the statement `let x = y + 3`, the two definitions
given to the prover might be `<0>` as `y + 3`, followed by `x`  as `<0>`, because the right-hand
side of the assignment produces a single identifier to use to replace `x`. These definitions are
then expanded in reverse whenever something must be proven about a variable, so that the prover
interface need not account for definitions and re-definitions. The basic prover interface is wrapped
in two levels: once by `ScopedSimpleProver` in 'src/proof/mod.rs', and once again by `WrappedProver`
in 'src/verify/prover.rs'. These combine to provide the more complex usage needed for verification,
while allowing the proof algorithms (of which there are two) to stay simple.

The two algorithms for proof currently available are the "bounds" method and the "graph" method, and
can be switched between by the feature flags with the same name. Both of these are described in more
depth in their respective documents.

## Execution

Program execution is exceptionally simple; it operates directly on the AST. The executor expects
there to be a single `main` function to run, and simply keeps the current scope as a
linked-list-like structure of hashmaps from variable names to values. Some checks are performed at
runtime but these all lead to a panic (and therefore immediate termination) as opposed to a useful
error message which would have been generated during verification - those that are performed are
typically to assert that operands have the correct type (which is required to unwrap the value).

The `Value` type (see below) as used by the executor could be used in a way similar to many
dynamically-typed languages, but its flexibility is narrowed by the static verification provided
earlier in the pipeline.

```rust
enum Value {
    Unit,
    Bool(bool),
    Int(isize),
    Struct { fields: HashMap<String, Value> },
}
```

Note that the set of builtin types is minimal.
