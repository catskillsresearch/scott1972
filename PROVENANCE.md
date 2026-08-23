# Provenance

This repository is a standalone Lean 4 formalization of Dana Scott's 1972
paper *Continuous Lattices* (LNM 274). It is not a thin wrapper and not a
reimplementation of an independent formalization.

A cross-presentation equivalence package for Scott's 1972 / 1980 / 1982
material previously lived in
[`catskillsresearch/scott_models`](https://github.com/catskillsresearch/scott_models)
as Part IV. That monolith Palomar submission was withdrawn after a registration
process glitch. **This repository is submitted to Palomar on its own**, for
the 1972 paper alone, following the same Challenge / Solution pattern as
[`catskillsresearch/cardb`](https://github.com/catskillsresearch/cardb).

The compared Palomar claim is Scott's domain equation (Theorem 4.4): a
continuous lattice `D_∞` order-isomorphic to its function space
`[D_∞ → D_∞]`. The full §2–§4 development lives in `Scott1972/ContinuousLattice/*`;
`Challenge.lean` states only the headline theorem and the definitions it mentions.

Palomar reviews and, if registered, preserves a pinned commit of *this*
repository.
