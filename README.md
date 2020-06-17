# TrenchCoat

This repository houses the bulk of the work on the TrenchCoat language demo. This consists of a
rudimentary interpreter to follow the static analysis given as part of the language definition.
Currently, the basic demo procedure is to modify 'src/test\_input.tc' and build+run the project.
This is detailed further below.

## Usage

This project requires a working Rust compiler (and toolchain). That can be obtained at
[rustup.rs](https://rustup.rs/).

After installation, the project can be run with:
```
cargo run --features="<proof_method>"
```
where `<proof_method>` is either of `bounds` or `graph` - this determines which solver to use.

Unit testing is available through `cargo test --features="<proof_method>"`, just as above. It should
be noted that the prover tests partially serve to demonstrate the edges of the capabilities of each
prover. As such, there are expected failures. These tests can be found in
[src/proof/tests.rs](src/proof/tests.rs).

## More information

Much more information is available about the various pieces of this project:
* [Project structure & overview](writeups/project-structure.md)
* Provers:
  * [Overview](writeups/proof-overview.ms)
  * [Bound method in-depth](writeups/bound-method.md)
  * [Graph method in-depth](writeups/graph-method.md)

