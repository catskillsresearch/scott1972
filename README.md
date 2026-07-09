[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott1972/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott1972/actions/workflows/build.yml)
[![arXiv](https://img.shields.io/badge/arXiv-2606.30782-b31b1b.svg)](https://arxiv.org/abs/2606.30782)

# scott1972

Paper: [https://arxiv.org/abs/2606.30782](https://arxiv.org/abs/2606.30782)

Lean 4 formalization of Dana Scott's **1972** *Continuous Lattices* (LNM 274):
injective `T₀`-spaces, Scott topology, way-below, function spaces, inverse limits.

Standalone package — no dependency on the 1980/1982 formalizations. Part IV equivalence
theorems live in [`scott_models`](../scott_models).

## Build

```bash
lake exe cache get
lake build Scott1972
