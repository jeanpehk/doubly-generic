# Doubly-generic

A small library for arity-generic datatype-generic, or doubly-generic, programming in Coq.

## Example

Usage of a doubly-generic map with the library:

```coq
Compute ngmap 3 tprod
  _ _ _ _ (fun x y z => x + y + z)
  _ _ _ _ (fun x y z => andb (andb x y) z)
  (11,true) (2, true) (6, true).
```
```coq
  = (19, true)
```

Example generic definitions in [gmap.v](gmap.v), [ngmap.v](ngmap) and
[optngmap.v](optngmap.v), more examples of their usage in [examples.v](examples.v)

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

### examples.v

A few examples of using the library and it's generic types.

## proofs.v

A few proofs of the library.

