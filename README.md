# TrenchCoat

This repository houses the bulk of the work on the Trenchcoat language demo. This consists of a
rudimentary interpreter to follow the static analysis given as part of the language definition.
Currently, the basic demo procedure is to modify 'src/test\_input.tc' and build+run the project.
This is detailed futher below.

## Usage

This project requires a working Rust compiler (and toolchain). That can be obtained at
[rustup.rs](#https://rustup.rs/).

After installation, the project can be run with:
```
cargo run --features="<proof_method>"
```
where `<proof_method>` is either of `bounds` or `graph` - this determines which solver to use.

Testing is available through `cargo test --features="<proof_method>"`, just as above. It should be
noted that the prover tests partially serve to demonstrate the edges of the capabilities of each
prover. As such, there are expected failures.

## More information

Much more information is available about the various pieces of this project:
* [Project structure & overview](writeups/project-structure.md)
* Provers:
  * [Bound method in-depth](writeups/bound-method.md)
  * [Graph method in-depth](writeups/graph-method.md)

