# Doubly-generic

Doubly-generic programming. Initial examples and tests.

Most of this is ideas combined from these papers:

Arity-Generic Datatype-Generic Programming (Weirich, Casinghino):
- https://dl.acm.org/doi/pdf/10.1145/1707790.1707799

Polytypic Programming in Coq (Verbruggen, de Vries, Hughes):
- https://dl.acm.org/doi/pdf/10.1145/1411318.1411326
- Does not consider arity-genericity.

compile:
```bash
$ make
```

clean:
```bash
$ make clean
```

## arity.v

Simple arity-generic map ala Fridlender + Indrika / Weirich + Casinghino.

## univ.v

A universe for generic programming + interpretation functions.

## generic.v

Trying out ideas for a generic library.

## utils.v

Utilities. Includes e.g. types for vectors, tuples and functions that
perform operations on them.

