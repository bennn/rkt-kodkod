private
===

Implementation of `kodkod√2`.


In this directory:
---

- `ast.rkt` Abstract syntax data for Kodkod formulas
- `bitmatrix.rkt` implements `N`-dimensional boolean matrices (backed by sparse sequences)
- `bool.rkt` for building boolean circuits, does some automatic minimization
- `dimensions.rkt` represents matrix dimensions, only used by `bitmatrix`
- `environment.rkt` (untyped) map from symbols to values 
- `exceptions.rkt` for nice error messages
- `int-tree.rkt` red-black tree of integers
- `parameters.rkt` program-wide options to set & tweak
- `parser.rkt` from files & input ports to relational logic
- `predicates.rkt` assertions, contracts, and simple type definitions
- `sparse-sequence.rkt` sparse sequences, used to support `bitmatrix`
- `translate/` support for translating relational logic to CNF
- `translator.rkt` front-end for translating rel. logic to CNF
