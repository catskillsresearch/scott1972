# Provenance

This repository is a standalone Lean 4 formalization of Dana Scott's 1972
paper *Continuous Lattices* (LNM 274). It is not a thin wrapper and not a
reimplementation of an independent formalization.

Dana Scott did not participate in, review, or endorse this formalization.
The formalization was produced by Lars Warren Ericson without input from
Scott. The source paper is cited as literature only.

A cross-presentation equivalence package for Scott's 1972 / 1980 / 1982
material previously lived in
[`catskillsresearch/scott_models`](https://github.com/catskillsresearch/scott_models)
as Part IV. That monolith Palomar submission was withdrawn after a registration
process glitch. **This repository is submitted to Palomar on its own**, for
the 1972 paper alone, following the same Challenge / Solution pattern as
[`catskillsresearch/cardb`](https://github.com/catskillsresearch/cardb).

The compared Palomar claim is Scott's Theorem 4.4: the inverse limit `D_∞`
of the function-space tower is a continuous lattice homeomorphic to
`[D_∞ → D_∞]`. The compared `Homeomorph` names the source topologies exactly:
the product/subspace inverse-limit topology and the pointwise Pi topology on
the function space. The proof uses Scott's displayed `i∞`/`j∞` formulas. The
full §2–§4 development lives in `Scott1972/ContinuousLattice/*`.

Palomar reviews and, if registered, preserves a pinned commit of *this*
repository.
