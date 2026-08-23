/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1972.ContinuousLattice.Constructions
import Scott1972.ContinuousLattice.FunctionSpaces
import Scott1972.ContinuousLattice.InverseLimits
import Scott1972.ContinuousLattice.FunctionSpaceTower

/-!
# Solution to the Challenge

The declaration `theorem_4_4` of `Challenge.lean`, proved in
`FunctionSpaceTower.lean`. Wording is that of Theorem 4.4 in
`sources/ScottContinLatt1972.md`. Importing the sorry-free development
supplies the compared definitions with the same names and types as in the
Challenge module.

The proof follows Scott's source-faithful route. Proposition 4.1 constructs
the product/subspace inverse limit as an injective space using Proposition
3.8 and Lemma 3.9, then applies Theorem 2.12. Theorem 4.4 uses Scott's displayed
maps \(i_\infty, j_\infty\); its explicit homeomorphism has the inverse-limit
product/subspace topology on the domain and Definition 3.1's pointwise Pi
topology on the function space.
-/
