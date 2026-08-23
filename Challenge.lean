/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.Hom.Basic

/-!
# Scott domain satisfying the domain equation (Palomar statement of record)

This is the statement of record for a Palomar submission. It states Scott's
**Theorem 4.4** headline: there exists a continuous lattice `D_∞` that is
isomorphic to its own function space `[D_∞ → D_∞]`.

The informal claim is the main result of Dana Scott's 1972 paper *Continuous
Lattices* (LNM 274): starting from a continuous lattice with a chosen projection
`j₀ : [D₀ → D₀] → D₀`, build the recursively defined function-space tower,
take its inverse limit `D_∞`, and prove `D_∞ ≅ [D_∞ → D_∞]`.

This file imports only Mathlib. The proofs live in `Scott1972/ContinuousLattice/*`
and are compared against this file by Comparator via `Solution.lean`.

## How to read this file

The definitions below are the vocabulary of the claim. A reader who wants to
check *what* has been proved should read this file and need not read the proof
development. `Solution.lean` imports the sorry-free library.
-/

namespace Scott1972.ContinuousLattice

open Set Topology

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

/-- Continuous maps between complete lattices with Scott's induced topologies. -/
def ScottMap (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] : Type _ :=
  { f : D → D' // @Continuous D D' scottTopologicalSpace scottTopologicalSpace f }

namespace ScottMap

instance : CoeFun (ScottMap D D') (fun _ => D → D') where
  coe f := f.1

@[ext]
theorem ext {f g : ScottMap D D'} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext h)

/-- Pointwise order on Scott maps (needed so `OrderIso` can see `LE`). -/
instance instPartialOrder : PartialOrder (ScottMap D D') where
  le f g := ∀ x, (f : D → D') x ≤ g x
  le_refl _ _ := le_refl _
  le_trans _ _ _ hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm _ _ hfg hgf := ScottMap.ext fun x => le_antisymm (hfg x) (hgf x)

end ScottMap

/-- **Scott 1972, §4 (Theorem 4.4, existential form).** There exists a
continuous lattice `D` isomorphic to its own function space `[D → D]`.
This is Scott's domain equation `D_∞ ≅ [D_∞ → D_∞]`. The proof constructs
an order isomorphism; the compared statement is the underlying equivalence
so Comparator does not depend on which `LE` instance Lean synthesizes. -/
theorem exists_scott_domain_domain_equation :
    ∃ (D : Type) (_ : CompleteLattice D) (_ : @IsContinuousLattice D _),
      Nonempty (D ≃ ScottMap D D) := by
  sorry

end Scott1972.ContinuousLattice
