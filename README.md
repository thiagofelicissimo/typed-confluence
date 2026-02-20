# Confluence Techniques for Dependent Type Theory with Typed Conversion

This repository contains the formalization for the paper [Confluence Techniques for Dependent Type Theory with Typed Conversion](https://inria.hal.science/hal-05520710).

[See here for the rendered Rocq files.](https://thiagofelicissimo.github.io/typed-confluence/doc/)

### Building

You need the Rocq Prover 9.0.1 and Autosubst 2 OCaml (needs ocaml<5, recommended 4.14.2).
You can install them using
```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
```
from the root of this directory.
There will be warnings about the `opam` file that can be safely ignored.

Then to verify the proof, just use `make`:
```sh
make autosubst
make   # you may add -j JOBS to compile faster
```
