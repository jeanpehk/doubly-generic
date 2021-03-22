# Doubly-generic

A small library for arity-generic datatype-generic, or doubly-generic, programming in Coq.

## Background

Most of this is ideas combined from these papers:

Arity-Generic Datatype-Generic Programming (Weirich, Casinghino):
- https://dl.acm.org/doi/pdf/10.1145/1707790.1707799
- Considers doubly generic programming in Agda.
- Need to use --type-in-type to keep definitions simple. To this they offer universepolymorfism as a possible solution.

Polytypic Programming in Coq (Verbruggen, de Vries, Hughes):
- https://dl.acm.org/doi/pdf/10.1145/1411318.1411326
- Does not consider arity-genericity.
- Kind-indexed universe (like with W + C) -> could be extended to be doubly generic.
- Uses Coq.

Main outcome of this library:

- No exising implementation for doubly-generic programming in Coq.
- Usage of universepolymorfism to avoid --type-in-type.

Main caveats:

- Cumbersome to define functions with.
- Uses --impredicative-set.
- No datatype isomorphisms (check W + C).

## Build

Contains a simple Makefile for compiling:
```bash
$ make
```

Clean:
```bash
$ make clean
```

## Structure

### univ.v

A universe for doubly generic programming + interpretation functions.

### generic.v

A doubly-generic library.

### utils.v

Utilities. Includes e.g. a type for vectors and functions that
perform operations on them.

### examples.v

A few examples of using the library.

### proofs.v

A few proofs of the library.

