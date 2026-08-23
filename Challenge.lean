/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Homeomorph.Defs

/-!
# Scott 1972, Theorem 4.4 (Palomar statement of record)

Ground truth for the wording is
`sources/ScottContinLatt1972.md`. Theorem 4.4 there is:

> The inverse limit \(D_\infty\) of the recursively defined sequence
> \(\langle D_n, j_n \rangle_{n=0}^{\infty}\) of function spaces is not only a
> continuous lattice, but it is also homeomorphic to its own function space
> \([D_\infty \to D_\infty]\).

The sequence is the one defined just above that theorem: \(D = D_0\) a given
continuous lattice; \(D_1 = [D_0 \to D_0]\) with a chosen projection pair
\(i_0, j_0\) (Proposition 3.13); then recursively
\(D_{n+1} = [D_n \to D_n]\) and \(j_{n+1} = [j_n \to j_n]\) by Proposition 3.7.
Definition 3.1: \([X \to Y]\) is the space of continuous functions with the
product topology (pointwise convergence). Theorem 3.3: on continuous lattices
the lattice topology agrees with that product topology, so the homeomorphism
is for those topologies.

This file imports only Mathlib. The proofs live in `Scott1972/ContinuousLattice/*`
and are compared against this file by Comparator via `Solution.lean`.

## How to read this file

The definitions below are the vocabulary of the claim. A reader who wants to
check *what* has been proved should read this file and need not read the proof
development. `Solution.lean` imports the sorry-free library.
-/

namespace Scott1972.ContinuousLattice

open Set Topology

universe u

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

/-- **Scott 1972, §2.** `U` is *Scott-open* when it is an upper set and is
inaccessible by suprema of non-empty directed sets. -/
def ScottOpen (U : Set D) : Prop :=
  IsUpperSet U ∧
    ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → sSup S ∈ U → (S ∩ U).Nonempty

/-- **Scott 1972, §2.** The *way-below* relation: `x ≪ y` iff `y` lies in the
interior of the principal up-set `Set.Ici x` for the induced topology. -/
def WayBelow (x y : D) : Prop :=
  ∃ U : Set D, ScottOpen U ∧ y ∈ U ∧ U ⊆ Set.Ici x

@[inherit_doc] scoped infix:50 " ≪ " => WayBelow

/-- **Scott 1972, Definition 2.3.** A complete lattice is a *continuous lattice*
when every element is the supremum of the elements way below it. -/
def IsContinuousLattice (D : Type*) [CompleteLattice D] : Prop :=
  ∀ y : D, IsLUB {x | x ≪ y} y

/-- Scott's induced topology on a complete lattice. -/
@[reducible] noncomputable def scottTopologicalSpace : TopologicalSpace D :=
  Topology.scott D univ

/-- **Scott 1972, Definition 3.1.** `[X → Y]` is the space of continuous functions
\(f : X \to Y\). On continuous lattices, Theorem 3.3 identifies the lattice
topology with the product topology of 3.1; we take continuity for the induced
(lattice) topology. -/
def ScottMap (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] : Type _ :=
  { f : D → D' // @Continuous D D' scottTopologicalSpace scottTopologicalSpace f }

namespace ScottMap

instance : CoeFun (ScottMap D D') (fun _ => D → D') where
  coe f := f.1

/-- **Scott 1972, Theorem 3.3.** `[D → D']` is a complete lattice (pointwise
suprema). Deliberate Comparator hole; the proof is in `FunctionSpaces.lean`. -/
noncomputable instance instCompleteLattice : CompleteLattice (ScottMap D D') := by
  sorry

end ScottMap

/-- **Scott 1972, Definition 3.6.** A *retraction* of continuous lattices. -/
structure IsContinuousLatticeRetraction (D D' : Type*) [CompleteLattice D] [CompleteLattice D']
    where
  incl : ScottMap D D'
  retr : ScottMap D' D
  retr_incl : ∀ d, retr (incl d) = d

/-- **Scott 1972, Definition 3.6.** A *projection* of continuous lattices: a retract with
`i ∘ j ⊑ id`. -/
structure IsContinuousLatticeProjection (D D' : Type*) [CompleteLattice D] [CompleteLattice D']
    extends IsContinuousLatticeRetraction D D' where
  incl_retr_le : ∀ d, incl (retr d) ≤ d

/-- A complete lattice bundled with its instance, used to define the function-space tower by
recursion on `ℕ`. -/
structure CLat : Type (u + 1) where
  carrier : Type u
  [str : CompleteLattice carrier]

attribute [instance] CLat.str

/-- The tower `D₀, [D₀→D₀], [[D₀→D₀]→[D₀→D₀]], …` as bundled complete lattices. -/
noncomputable def towerCLat (D₀ : CLat.{u}) : ℕ → CLat.{u}
  | 0 => D₀
  | (n + 1) => ⟨ScottMap (towerCLat D₀ n).carrier (towerCLat D₀ n).carrier⟩

/-- The carrier `Dₙ` of the function-space tower. -/
def towerType (D₀ : CLat.{u}) (n : ℕ) : Type u := (towerCLat D₀ n).carrier

noncomputable instance towerCompleteLattice (D₀ : CLat.{u}) (n : ℕ) :
    CompleteLattice (towerType D₀ n) := (towerCLat D₀ n).str

/-- The projection tower `j_{n+1} = [j_n → j_n]`, anchored at a chosen base projection
`j₀ : [D₀ → D₀] → D₀`. Deliberate Comparator hole; the construction is in
`FunctionSpaceTower.lean`. -/
noncomputable def towerProj (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier)) :
    ∀ n, IsContinuousLatticeProjection (towerType D₀ n) (towerType D₀ (n + 1)) := by
  sorry

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- **Scott 1972, §4.** The inverse-limit compatibility condition
\(j_n(x_{n+1}) = x_n\). -/
def Compatible (x : ∀ n, D n) : Prop := ∀ n, (P n).retr (x (n + 1)) = x n

/-- **Scott 1972, §4.** The inverse limit is the subspace of the product consisting
of those sequences \(x = \langle x_n \rangle_{n=0}^{\infty}\) with
\(j_n(x_{n+1}) = x_n\). -/
abbrev InverseLimit : Type u := {x : ∀ n, D n // Compatible D P x}

/-- Inverse limits of complete lattices are complete lattices. Deliberate Comparator hole;
the proof is in `InverseLimits.lean`. -/
noncomputable instance instCompleteLattice : CompleteLattice (InverseLimit D P) := by
  sorry

end InverseLimit

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- **Scott 1972, §4.** The inverse limit \(D_\infty\) of
\(\langle D_n, j_n \rangle_{n=0}^{\infty}\). -/
abbrev DInf : Type u := InverseLimit (towerType D₀) (towerProj D₀ j₀)

/-- **Scott 1972, Definition 3.1 / Theorem 4.4.** The function space
\([D_\infty \to D_\infty]\). -/
abbrev DInfFn : Type u := ScottMap (DInf D₀ j₀) (DInf D₀ j₀)

/-- **Scott 1972, Theorem 4.4** (`sources/ScottContinLatt1972.md`):
*The inverse limit \(D_\infty\) of the recursively defined sequence
\(\langle D_n, j_n \rangle_{n=0}^{\infty}\) of function spaces is not only a
continuous lattice, but it is also homeomorphic to its own function space
\([D_\infty \to D_\infty]\).* -/
theorem theorem_4_4 (h₀ : IsContinuousLattice D₀.carrier) :
    @IsContinuousLattice (DInf D₀ j₀) inferInstance ∧
      Nonempty
        (@Homeomorph (DInf D₀ j₀) (DInfFn D₀ j₀)
          (@scottTopologicalSpace (DInf D₀ j₀) inferInstance)
          (@scottTopologicalSpace (DInfFn D₀ j₀)
            (@ScottMap.instCompleteLattice (DInf D₀ j₀) (DInf D₀ j₀)
              inferInstance inferInstance))) := by
  sorry

end LimitMaps

end Scott1972.ContinuousLattice
