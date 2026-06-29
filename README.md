# scott1972

Lean 4 formalization of Dana Scott's **1972** *Continuous Lattices* (LNM 274):
injective `T₀`-spaces, Scott topology, way-below, function spaces, inverse limits.

Standalone package — no dependency on the 1980/1982 formalizations. Part IV equivalence
theorems live in [`scott_models`](../scott_models).

## Build

```bash
lake exe cache get
lake build Scott1972
```

Pinned: Lean / mathlib **v4.30.0** (`lean-toolchain`).
