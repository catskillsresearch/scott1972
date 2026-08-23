[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott1972/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott1972/actions/workflows/build.yml)
[![arXiv](https://img.shields.io/badge/arXiv-2606.30782-b31b1b.svg)](https://arxiv.org/abs/2606.30782)

# scott1972

Paper: [https://arxiv.org/abs/2606.30782](https://arxiv.org/abs/2606.30782)

Lean 4 formalization of Dana Scott's **1972** *Continuous Lattices* (LNM 274):
injective `T₀`-spaces, Scott topology, way-below, function spaces, inverse limits.

Standalone package — no dependency on the 1980/1982 formalizations. Cross-presentation
equivalence theorems live in [`scott_models`](../scott_models); this repo is submitted
to [Palomar](https://palomar-registry.org/about) on its own (see `PROVENANCE.md`).

The pin is `leanprover/lean4:v4.33.0` (same as [`qlambda`](../qlambda)).

## Files (Palomar)

| File | Role |
|---|---|
| `arxiv.md` | Formalization narrative and theorem inventory |
| `sources/ScottContinLatt1972.md` | OCR source text (Scott 1972 through Milner correction) |
| `Scott1972/` | Sorry-free formalization of the paper |
| `Challenge.lean` | Palomar statement of record: Theorem 4.4 + definitions |
| `Solution.lean` | Palomar solution module: imports `Scott1972/*` proofs |
| `comparator.json` | Comparator config for the compared theorem and definitions |
| `formalization.yaml` | Palomar / formalization.yaml v0.4 metadata |
| `PROVENANCE.md` | Standalone Palomar submission; relation to `scott_models` |

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `Scott1972`, `Challenge.lean`, and `Solution.lean`. Before a
Palomar submission, run:

```bash
bash scripts/compare_challenge_solution_types.sh
```

`Challenge.lean` imports only Mathlib and states `theorem_4_4` in the wording of
`sources/ScottContinLatt1972.md` (Theorem 4.4) with a deliberate `sorry`. The
explicit `Homeomorph` uses the product/subspace topology on the inverse limit
and Definition 3.1's pointwise Pi topology on its function space. The proof is
in `FunctionSpaceTower.lean`, imported by `Solution.lean`. Proposition 4.1
follows Scott's Proposition 3.8 + Lemma 3.9 + injectivity + Theorem 2.12 route;
Lemma 4.5 follows Scott's induction. The homeomorphism is built from Scott's
displayed formulas for `i∞` and `j∞`.
The compared theorem uses `propext`, `Classical.choice`, and `Quot.sound` only.
