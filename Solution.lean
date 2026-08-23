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

The declaration `exists_scott_domain_domain_equation` of `Challenge.lean`,
proved. Importing the sorry-free development supplies the definitions
(`ScottOpen`, `WayBelow`, `IsContinuousLattice`, `scottTopologicalSpace`,
`ScottMap`) with the same names and types as in the Challenge module.

The proof instantiates Scott's function-space tower at the Sierpiński
continuous lattice `Prop`, uses Proposition 3.13 for a base projection
`j₀ : [D₀ → D₀] → D₀`, forms the inverse limit `D_∞`, and applies
Theorem 4.4 (`theorem_4_4_orderIso`).
-/

namespace Scott1972.ContinuousLattice

private theorem towerType_isContinuousLattice (D₀ : CLat.{0})
    (h₀ : IsContinuousLattice D₀.carrier) :
    ∀ n, IsContinuousLattice (towerType D₀ n) := by
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih => exact theorem_3_3_isContinuousLattice ih ih

/-- **Scott 1972, §4 (Theorem 4.4, existential form).** -/
theorem exists_scott_domain_domain_equation :
    ∃ (D : Type) (_ : CompleteLattice D) (_ : @IsContinuousLattice D _),
      Nonempty (D ≃ ScottMap D D) := by
  classical
  let D₀ : CLat.{0} := ⟨Prop⟩
  have h₀ : IsContinuousLattice Prop := isContinuousLattice_prop
  obtain ⟨j₀⟩ := proposition_3_13 h₀
  have hTower := towerType_isContinuousLattice D₀ h₀
  have hCLinf : IsContinuousLattice (DInf D₀ j₀) :=
    proposition_4_1 (towerType D₀) (towerProj D₀ j₀) hTower
  refine ⟨DInf D₀ j₀, inferInstance, hCLinf, ⟨(theorem_4_4_orderIso D₀ j₀).toEquiv⟩⟩

end Scott1972.ContinuousLattice
