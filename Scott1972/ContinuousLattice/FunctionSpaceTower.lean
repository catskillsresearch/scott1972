/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1972
-/

import Scott1972.ContinuousLattice.InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs

/-!
# The function-space tower and Theorem 4.4
(Scott 1972; wording from `sources/ScottContinLatt1972.md`)

Scott, just above Theorem 4.4: let \(D = D_0\) be a given continuous lattice; make
\(D_0\) a projection of \(D_1 = [D_0 \to D_0]\) by a pair \(i_0, j_0\) (Proposition 3.13);
define recursively \(D_{n+1} = [D_n \to D_n]\) and introduce \(i_{n+1}, j_{n+1}\) by
Proposition 3.7, so \(j_{n+1} = [j_n \to j_n]\).

**4.4 Theorem.** *The inverse limit \(D_\infty\) of the recursively defined sequence
\(\langle D_n, j_n \rangle_{n=0}^{\infty}\) of function spaces is not only a continuous
lattice, but it is also homeomorphic to its own function space \([D_\infty \to D_\infty]\).*
-/

namespace Scott1972.ContinuousLattice

universe u

/-- A complete lattice bundled with its instance, used to define the function-space tower by
recursion on `ℕ` (the type at level `n+1` depends on the lattice structure at level `n`). -/
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

@[simp] theorem towerType_zero (D₀ : CLat.{u}) : towerType D₀ 0 = D₀.carrier := rfl

/-- `D_{n+1}` is *definitionally* the function space `[Dₙ → Dₙ]`. -/
theorem towerType_succ (D₀ : CLat.{u}) (n : ℕ) :
    towerType D₀ (n + 1) = ScottMap (towerType D₀ n) (towerType D₀ n) := rfl

/-- View an element of `D_{n+1}` as the Scott map `[Dₙ → Dₙ]` it definitionally is. -/
def towerToMap {D₀ : CLat.{u}} {n : ℕ} (f : towerType D₀ (n + 1)) :
    ScottMap (towerType D₀ n) (towerType D₀ n) := f

/-- Apply an element of `D_{n+1}` as a function `Dₙ → Dₙ` (definitional via `towerType_succ`). -/
instance towerCoeFun {D₀ : CLat.{u}} {n : ℕ} :
    CoeFun (towerType D₀ (n + 1)) (fun _ => towerType D₀ n → towerType D₀ n) where
  coe f := towerToMap f

@[simp] theorem towerToMap_coe {D₀ : CLat.{u}} {n : ℕ} (f : towerType D₀ (n + 1))
    (x : towerType D₀ n) : towerToMap f x = f x := rfl

/-! ### Conjugation used in Scott's §4 limit formulas

Theorem 4.4 uses maps of the form `f ↦ post ∘ f ∘ pre`.  We bundle this operation as a Scott map;
its continuity follows because directed suprema in function spaces are computed pointwise
(Theorem 3.3). -/

section Conj

open Set

variable {Y Z W : Type u} [CompleteLattice Y] [CompleteLattice Z] [CompleteLattice W]

/-- Conjugation `f ↦ post ∘ f ∘ pre` as a bare function `[Y → Y] → [W → Z]`. -/
def conjMapFun (post : ScottMap Y Z) (pre : ScottMap W Y) (f : ScottMap Y Y) : ScottMap W Z :=
  post.comp (f.comp pre)

theorem conjMapFun_apply (post : ScottMap Y Z) (pre : ScottMap W Y) (f : ScottMap Y Y) (x : W) :
    conjMapFun post pre f x = post (f (pre x)) := rfl

theorem conjMap_preservesDirectedSup (post : ScottMap Y Z) (pre : ScottMap W Y) :
    PreservesDirectedSup (conjMapFun post pre) := by
  intro F hF hFdir
  apply ScottMap.ext
  intro x
  have hdir : DirectedOn (· ≤ ·) ((fun f : ScottMap Y Y => f (pre x)) '' F) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hFdir a ha b hb
    exact ⟨c (pre x), ⟨c, hc, rfl⟩, hac (pre x), hbc (pre x)⟩
  show post ((sSup F : ScottMap Y Y) (pre x)) = (sSup (conjMapFun post pre '' F) : ScottMap W Z) x
  rw [ScottMap.sSup_apply F (pre x), post.preservesDirectedSup_coe _ (hF.image _) hdir,
    ScottMap.sSup_apply, Set.image_image, Set.image_image]
  rfl

/-- Conjugation `f ↦ post ∘ f ∘ pre` as a Scott map `[Y → Y] → [W → Z]`. -/
noncomputable def conjMap (post : ScottMap Y Z) (pre : ScottMap W Y) :
    ScottMap (ScottMap Y Y) (ScottMap W Z) :=
  ⟨conjMapFun post pre, continuous_of_preservesDirectedSup (conjMap_preservesDirectedSup post pre)⟩

@[simp] theorem conjMap_apply (post : ScottMap Y Z) (pre : ScottMap W Y) (f : ScottMap Y Y) (x : W) :
    conjMap post pre f x = post (f (pre x)) := rfl

end Conj

/-- Continuity of the inner map `i ∘ f ∘ j`. -/
theorem functionSpaceInclFun_continuous {D D' : Type u}
    [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') (f : ScottMap D D) :
    @Continuous D' D' scottTopologicalSpace scottTopologicalSpace
      (fun x => P.incl (f (P.retr x))) :=
  @Continuous.congr D' D' scottTopologicalSpace scottTopologicalSpace
    (P.incl.comp (f.comp P.retr)).1 (fun x => P.incl (f (P.retr x)))
    (P.incl.comp (f.comp P.retr)).continuous (fun _ => rfl)

/-- The inclusion part of `[P → P]`, with its underlying function explicit. -/
def functionSpaceInclFun {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') (f : ScottMap D D) : ScottMap D' D' :=
  ⟨fun x => P.incl (f (P.retr x)), functionSpaceInclFun_continuous P f⟩

/-- Continuity, for the lattice Scott topologies on the function spaces, of
`f ↦ i ∘ f ∘ j`. -/
theorem functionSpaceInclFun_outer_continuous {D D' : Type u}
    [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    @Continuous (ScottMap D D) (ScottMap D' D')
      scottTopologicalSpace scottTopologicalSpace (functionSpaceInclFun P) := by
  exact @Continuous.congr (ScottMap D D) (ScottMap D' D')
    scottTopologicalSpace scottTopologicalSpace (conjMap P.incl P.retr).1
    (functionSpaceInclFun P) (conjMap P.incl P.retr).continuous
    (fun f => ScottMap.ext fun _ => rfl)

/-- Continuity of the inner map `j ∘ g ∘ i`. -/
theorem functionSpaceRetrFun_continuous {D D' : Type u}
    [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') (g : ScottMap D' D') :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace
      (fun x => P.retr (g (P.incl x))) :=
  @Continuous.congr D D scottTopologicalSpace scottTopologicalSpace
    (P.retr.comp (g.comp P.incl)).1 (fun x => P.retr (g (P.incl x)))
    (P.retr.comp (g.comp P.incl)).continuous (fun _ => rfl)

/-- The retraction part of `[P → P]`, with its underlying function explicit. -/
def functionSpaceRetrFun {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') (g : ScottMap D' D') : ScottMap D D :=
  ⟨fun x => P.retr (g (P.incl x)), functionSpaceRetrFun_continuous P g⟩

/-- Continuity, for the lattice Scott topologies on the function spaces, of
`g ↦ j ∘ g ∘ i`. -/
theorem functionSpaceRetrFun_outer_continuous {D D' : Type u}
    [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    @Continuous (ScottMap D' D') (ScottMap D D)
      scottTopologicalSpace scottTopologicalSpace (functionSpaceRetrFun P) := by
  exact @Continuous.congr (ScottMap D' D') (ScottMap D D)
    scottTopologicalSpace scottTopologicalSpace (conjMap P.retr P.incl).1
    (functionSpaceRetrFun P) (conjMap P.retr P.incl).continuous
    (fun g => ScottMap.ext fun _ => rfl)

/-- Retraction law for the diagonal Proposition 3.7 construction. -/
theorem functionSpaceRetrIncl {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    ∀ f, functionSpaceRetrFun P (functionSpaceInclFun P f) = f :=
  (proposition_3_7_projection P P).retr_incl

/-- Projection inequality for the diagonal Proposition 3.7 construction. -/
theorem functionSpaceInclRetrLe {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    ∀ g, functionSpaceInclFun P (functionSpaceRetrFun P g) ≤ g := by
  intro g
  exact ScottMap.le_def.mpr ((proposition_3_7_projection P P).incl_retr_le g)

/-- Scott's Proposition 3.7 construction specialized diagonally. -/
noncomputable def functionSpaceProjection
    {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    IsContinuousLatticeProjection (ScottMap D D) (ScottMap D' D') where
  incl := ⟨functionSpaceInclFun P, functionSpaceInclFun_outer_continuous P⟩
  retr := ⟨functionSpaceRetrFun P, functionSpaceRetrFun_outer_continuous P⟩
  retr_incl := functionSpaceRetrIncl P
  incl_retr_le := functionSpaceInclRetrLe P

/-- The projection tower from Scott's recursion immediately before Theorem 4.4:
`j_{n+1} = [j_n → j_n]`, anchored at `j₀ : [D₀ → D₀] → D₀`.

At each successor, the maps and projection laws are the diagonal specialization
`proposition_3_7_projection P P`.  `conjMap` supplies the outer Scott-continuity needed to bundle
those canonical maps as an `IsContinuousLatticeProjection`. -/
noncomputable def towerProj (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier)) :
    ∀ n, IsContinuousLatticeProjection (towerType D₀ n) (towerType D₀ (n + 1))
  | 0 => j₀
  | (n + 1) => functionSpaceProjection (towerProj D₀ j₀ n)

theorem towerProj_succ (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier)) (n : ℕ) :
    let P := towerProj D₀ j₀ n
    (towerProj D₀ j₀ (n + 1)).incl = conjMap P.incl P.retr ∧
      (towerProj D₀ j₀ (n + 1)).retr = conjMap P.retr P.incl := by
  exact ⟨rfl, rfl⟩

section Tower

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- **Scott 1972, recursion before Theorem 4.4 (from Proposition 3.7).**
`i_{n+1}(x) = iₙ ∘ x ∘ jₙ`. -/
theorem towerProj_succ_incl_apply (n : ℕ) (x : towerType D₀ (n + 1)) (y : towerType D₀ (n + 1)) :
    ((towerProj D₀ j₀ (n + 1)).incl x) y
      = (towerProj D₀ j₀ n).incl (x ((towerProj D₀ j₀ n).retr y)) := rfl

/-- **Scott 1972, recursion before Theorem 4.4 (from Proposition 3.7).**
`j_{n+1}(x') = jₙ ∘ x' ∘ iₙ`. -/
theorem towerProj_succ_retr_apply (n : ℕ) (x' : towerType D₀ (n + 2)) (y : towerType D₀ n) :
    ((towerProj D₀ j₀ (n + 1)).retr x') y
      = (towerProj D₀ j₀ n).retr (x' ((towerProj D₀ j₀ n).incl y)) := rfl

/-- **Scott 1972, §4 (application is preserved).** `iₙ(f(x)) = i_{n+1}(f)(iₙ(x))` for `f ∈ D_{n+1}`,
`x ∈ Dₙ`. The embeddings turn functional application into application one level up. -/
theorem towerProj_incl_apply (n : ℕ) (f : towerType D₀ (n + 1)) (x : towerType D₀ n) :
    (towerProj D₀ j₀ n).incl (f x)
      = ((towerProj D₀ j₀ (n + 1)).incl f) ((towerProj D₀ j₀ n).incl x) := by
  rw [towerProj_succ_incl_apply, (towerProj D₀ j₀ n).retr_incl]

end Tower

/-! ### Theorem 4.4(a): the limit maps `i_∞` and `j_∞`

We now wire the concrete inverse limit `D_∞` of the function-space tower and write down Scott's pair

```
i_∞(x) = ⨆ₙ (i_{n∞} ∘ x_{n+1} ∘ j_{∞n})      : D_∞ → [D_∞ → D_∞]
j_∞(f) = ⨆ₙ i_{(n+1)∞}(j_{∞n} ∘ f ∘ i_{n∞})  : [D_∞ → D_∞] → D_∞
```

Each summand is itself a Scott map (a composite of `conjMap`, `embInf`, `projInf`), so each of
`i_∞`, `j_∞` is a *supremum of Scott maps* and is therefore Scott-continuous automatically: by
Theorem 3.3 the function space `[A → B]` is a complete lattice in which suprema are computed
pointwise. No bespoke continuity argument is needed. -/

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- The inverse limit `D_∞` of the function-space tower `⟨Dₙ, jₙ⟩`. -/
abbrev DInf : Type u := InverseLimit (towerType D₀) (towerProj D₀ j₀)

/-- The function space `[D_∞ → D_∞]`. -/
abbrev DInfFn : Type u := ScottMap (DInf D₀ j₀) (DInf D₀ j₀)

/-- The `n`-th summand of `i_∞`: the Scott map `x ↦ i_{n∞} ∘ x_{n+1} ∘ j_{∞n}`, where `x_{n+1}` is
the `(n+1)`-st component of `x ∈ D_∞`. As a map `D_∞ → [D_∞ → D_∞]` it is the composite of the
component projection `j_{∞(n+1)}` with conjugation by `(i_{n∞}, j_{∞n})`. -/
noncomputable def iInfTerm (n : ℕ) : ScottMap (DInf D₀ j₀) (DInfFn D₀ j₀) :=
  (conjMap (embInf (towerType D₀) (towerProj D₀ j₀) n)
           (projInf (towerType D₀) (towerProj D₀ j₀) n)).comp
    (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1))

@[simp] theorem iInfTerm_apply (n : ℕ) (x z : DInf D₀ j₀) :
    (iInfTerm D₀ j₀ n x) z
      = embInf (towerType D₀) (towerProj D₀ j₀) n
          ((x.1 (n + 1)) ((projInf (towerType D₀) (towerProj D₀ j₀) n) z)) := rfl

/-- **Scott 1972, §4 (Theorem 4.4).** The embedding `i_∞ : D_∞ → [D_∞ → D_∞]`,
`i_∞(x) = ⨆ₙ i_{n∞} ∘ x_{n+1} ∘ j_{∞n}`. It is Scott-continuous because it is a supremum of the
Scott maps `iInfTerm n` (suprema in `[D_∞ → [D_∞ → D_∞]]` are computed pointwise). -/
noncomputable def embInfInf : ScottMap (DInf D₀ j₀) (DInfFn D₀ j₀) :=
  ⨆ n, iInfTerm D₀ j₀ n

/-- `i_∞` evaluated at `x` is the pointwise supremum of the summands `iInfTerm n x`. -/
theorem embInfInf_apply (x : DInf D₀ j₀) :
    embInfInf D₀ j₀ x = ⨆ n, iInfTerm D₀ j₀ n x := by
  show (sSup (Set.range (iInfTerm D₀ j₀)) : ScottMap _ _) x = _
  rw [ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
  rfl

/-- The `n`-th summand of `j_∞`: the Scott map `f ↦ i_{(n+1)∞}(j_{∞n} ∘ f ∘ i_{n∞})`. As a map
`[D_∞ → D_∞] → D_∞` it is conjugation by `(j_{∞n}, i_{n∞})` (landing in `D_{n+1}`) followed by the
embedding `i_{(n+1)∞}`. -/
noncomputable def jInfTerm (n : ℕ) : ScottMap (DInfFn D₀ j₀) (DInf D₀ j₀) :=
  (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)).comp
    (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
             (embInf (towerType D₀) (towerProj D₀ j₀) n))

@[simp] theorem jInfTerm_apply (n : ℕ) (f : DInfFn D₀ j₀) :
    jInfTerm D₀ j₀ n f
      = embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
          (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                   (embInf (towerType D₀) (towerProj D₀ j₀) n) f) := rfl

/-- **Scott 1972, §4 (Theorem 4.4).** The projection `j_∞ : [D_∞ → D_∞] → D_∞`,
`j_∞(f) = ⨆ₙ i_{(n+1)∞}(j_{∞n} ∘ f ∘ i_{n∞})`. Scott-continuous as a supremum of the Scott maps
`jInfTerm n`. -/
noncomputable def projInfInf : ScottMap (DInfFn D₀ j₀) (DInf D₀ j₀) :=
  ⨆ n, jInfTerm D₀ j₀ n

/-- `j_∞` evaluated at `f` is the supremum of the summands `jInfTerm n f`. -/
theorem projInfInf_apply (f : DInfFn D₀ j₀) :
    projInfInf D₀ j₀ f = ⨆ n, jInfTerm D₀ j₀ n f := by
  show (sSup (Set.range (jInfTerm D₀ j₀)) : ScottMap _ _) f = _
  rw [ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
  rfl

/-- `i_∞` is Scott-continuous (it is a bundled `ScottMap`). -/
theorem embInfInf_preservesDirectedSup :
    PreservesDirectedSup (embInfInf D₀ j₀ : DInf D₀ j₀ → DInfFn D₀ j₀) :=
  (proposition_2_5 _).mp (embInfInf D₀ j₀).continuous

/-- `j_∞` is Scott-continuous (it is a bundled `ScottMap`). -/
theorem projInfInf_preservesDirectedSup :
    PreservesDirectedSup (projInfInf D₀ j₀ : DInfFn D₀ j₀ → DInf D₀ j₀) :=
  (proposition_2_5 _).mp (projInfInf D₀ j₀).continuous

/-! ### Theorem 4.4(b): `j_∞ ∘ i_∞ = id` on `D_∞`

Scott's calculation (~lines 1290–1294): expand `j_∞(i_∞(x))` as a double sup, collapse the monotone
double limit to the diagonal using `projInf ∘ embInf = id` on each summand, then recognize `x` via
`inverseLimit_eq_iSup` (with a one-step index shift). -/

section Thm44b

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- Conjugation commutes with a supremum indexed by `ℕ` (the range is directed when `f` is monotone).
Since `conjMap post pre` is itself a Scott map, this is just preservation of directed suprema. -/
theorem conjMap_iSup (n : ℕ) (post : ScottMap (DInf D₀ j₀) (towerType D₀ n))
    (pre : ScottMap (towerType D₀ n) (DInf D₀ j₀))
    (f : ℕ → ScottMap (DInf D₀ j₀) (DInf D₀ j₀)) (hf : Monotone f) :
    conjMap post pre (⨆ m, f m) = ⨆ m, conjMap post pre (f m) := by
  have hdir : DirectedOn (· ≤ ·) (Set.range f) :=
    directedOn_range.2 fun a b => ⟨max a b, hf (le_max_left a b), hf (le_max_right a b)⟩
  have hne := Set.range_nonempty f
  rw [show (⨆ m, f m) = sSup (Set.range f) from sSup_range.symm,
    (conjMap post pre).preservesDirectedSup_coe (Set.range f) hne hdir, ← Set.range_comp]
  rfl

/-- The inverse-limit embedding commutes with a supremum in `D_{n+1}` (monotone ⇒ directed). -/
theorem embInf_succ_iSup (n : ℕ) (f : ℕ → towerType D₀ (n + 1)) (hf : Monotone f) :
    embInf (towerType D₀) (towerProj D₀ j₀) (n + 1) (⨆ m, f m) =
      ⨆ m, embInf (towerType D₀) (towerProj D₀ j₀) (n + 1) (f m) := by
  have hdir : DirectedOn (· ≤ ·) (Set.range f) :=
    directedOn_range.2 fun a b => ⟨max a b, hf (le_max_left a b), hf (le_max_right a b)⟩
  have hne := Set.range_nonempty f
  rw [show (⨆ m, f m) = sSup (Set.range f) from sSup_range.symm,
    (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)).preservesDirectedSup_coe
      (Set.range f) hne hdir, ← Set.range_comp]
  rfl

/-- **Diagonal simplification.** `conjMap (j_{∞n}, i_{n∞})` applied to the `n`-th summand of `i_∞`
recovers the component `x_{n+1}`. This is Proposition 3.7's equation
`j_{[·]} ∘ i_{[·]} = id`, diagonally specialized to the projection from Proposition 4.2. -/
theorem conj_iInfTerm_eq (n : ℕ) (x : DInf D₀ j₀) :
    conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
            (embInf (towerType D₀) (towerProj D₀ j₀) n)
            (iInfTerm D₀ j₀ n x) = x.1 (n + 1) :=
  (proposition_3_7_projection
      (proposition_4_2 (towerType D₀) (towerProj D₀ j₀) n)
      (proposition_4_2 (towerType D₀) (towerProj D₀ j₀) n)).retr_incl
    (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1) x)

/-- `i_{n∞}(yₙ) ⊑ y_{n+1}`: climbing one level and embedding stays below the next component. -/
theorem incl_projInf_le_projInf_succ (n : ℕ) (w : DInf D₀ j₀) :
    (towerProj D₀ j₀ n).incl (projInf (towerType D₀) (towerProj D₀ j₀) n w)
      ≤ projInf (towerType D₀) (towerProj D₀ j₀) (n + 1) w := by
  have h := (towerProj D₀ j₀ n).incl_retr_le
    (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1) w)
  rwa [show (towerProj D₀ j₀ n).retr (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1) w)
      = projInf (towerType D₀) (towerProj D₀ j₀) n w from w.2 n] at h

/-- `i_∞` is monotone in its summand index. -/
theorem iInfTerm_le_succ (x : DInf D₀ j₀) (m : ℕ) :
    iInfTerm D₀ j₀ m x ≤ iInfTerm D₀ j₀ (m + 1) x := by
  rw [ScottMap.le_def]
  intro z
  rw [iInfTerm_apply, iInfTerm_apply,
    ← embInf_succ (towerType D₀) (towerProj D₀ j₀) m
      (x.1 (m + 1) (projInf (towerType D₀) (towerProj D₀ j₀) m z))]
  refine embInf_monotone (towerType D₀) (towerProj D₀ j₀) (m + 1) ?_
  have hab : (towerProj D₀ j₀ m).incl (projInf (towerType D₀) (towerProj D₀ j₀) m z)
      ≤ projInf (towerType D₀) (towerProj D₀ j₀) (m + 1) z :=
    incl_projInf_le_projInf_succ D₀ j₀ m z
  calc (towerProj D₀ j₀ m).incl
          (x.1 (m + 1) (projInf (towerType D₀) (towerProj D₀ j₀) m z))
      = (towerProj D₀ j₀ m).incl
          (((towerProj D₀ j₀ (m + 1)).retr (x.1 (m + 2)))
            (projInf (towerType D₀) (towerProj D₀ j₀) m z)) := by
        rw [show ((towerProj D₀ j₀ (m + 1)).retr (x.1 (m + 2))) = x.1 (m + 1) from x.2 (m + 1)]
    _ = (towerProj D₀ j₀ m).incl
          ((towerProj D₀ j₀ m).retr
            (x.1 (m + 2) ((towerProj D₀ j₀ m).incl
              (projInf (towerType D₀) (towerProj D₀ j₀) m z)))) := by
        rw [towerProj_succ_retr_apply]
    _ ≤ x.1 (m + 2) ((towerProj D₀ j₀ m).incl
          (projInf (towerType D₀) (towerProj D₀ j₀) m z)) :=
        (towerProj D₀ j₀ m).incl_retr_le _
    _ ≤ x.1 (m + 2) (projInf (towerType D₀) (towerProj D₀ j₀) (m + 1) z) :=
        ScottMap.monotone (x.1 (m + 2)) hab

theorem iInfTerm_monotone (x : DInf D₀ j₀) : Monotone (fun m => iInfTerm D₀ j₀ m x) :=
  monotone_nat_of_le_succ (iInfTerm_le_succ D₀ j₀ x)

/-- A monotone double `iSup` over `ℕ × ℕ` equals the diagonal `iSup`. -/
theorem iSup₂_monotone_eq_diagonal {α : Type*} [CompleteLattice α] (f : ℕ → ℕ → α)
    (hfm : ∀ n, Monotone (f n)) (hfn : ∀ m, Monotone (fun n => f n m)) :
    ⨆ n, ⨆ m, f n m = ⨆ n, f n n := by
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun m => ?_
    have hk : n ≤ n ⊔ m := le_sup_left
    have hk' : m ≤ n ⊔ m := le_sup_right
    calc f n m ≤ f (n ⊔ m) m := hfn m hk
      _ ≤ f (n ⊔ m) (n ⊔ m) := hfm (n ⊔ m) hk'
      _ ≤ ⨆ n', f n' n' := le_iSup (fun n' => f n' n') (n ⊔ m)
  · refine iSup_le fun n => le_trans (le_iSup (f n) n) (le_iSup (fun n' => ⨆ m, f n' m) n)

/-- **Conjugation climbs the tower (one step).** Lifting `conjMap (j_{∞n}, i_{n∞}) f` along `i_{n+1}`
stays below `conjMap (j_{∞(n+1)}, i_{(n+1)∞}) f`. Both sides live in `D_{n+2}`; the inequality is the
algebraic content that makes the double sup defining `j_∞ ∘ i_∞` monotone in the level index `n`. -/
theorem conjMap_incl_le_conjMap_succ (n : ℕ) (f : DInfFn D₀ j₀) :
    (towerProj D₀ j₀ (n + 1)).incl
        (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                 (embInf (towerType D₀) (towerProj D₀ j₀) n) f)
      ≤ conjMap (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1))
                (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)) f := by
  refine ScottMap.le_def.mpr fun y => ?_
  calc (towerProj D₀ j₀ n).incl
          (projInf (towerType D₀) (towerProj D₀ j₀) n
            (f (embInf (towerType D₀) (towerProj D₀ j₀) n ((towerProj D₀ j₀ n).retr y))))
      ≤ (towerProj D₀ j₀ n).incl
          (projInf (towerType D₀) (towerProj D₀ j₀) n
            (f (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1) y))) := by
        refine (towerProj D₀ j₀ n).incl.monotone
          ((projInf (towerType D₀) (towerProj D₀ j₀) n).monotone (f.monotone ?_))
        rw [← embInf_succ (towerType D₀) (towerProj D₀ j₀) n ((towerProj D₀ j₀ n).retr y)]
        exact embInf_monotone (towerType D₀) (towerProj D₀ j₀) (n + 1)
          ((towerProj D₀ j₀ n).incl_retr_le y)
    _ ≤ projInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
          (f (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1) y)) :=
        incl_projInf_le_projInf_succ D₀ j₀ n
          (f (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1) y))

/-- `j_∞(i_∞(x)) = ⨆ₙ i_{(n+1)∞}(x_{n+1})`. -/
theorem projInfInf_embInfInf_eq (x : DInf D₀ j₀) :
    projInfInf D₀ j₀ (embInfInf D₀ j₀ x) = ⨆ n, embInf (towerType D₀) (towerProj D₀ j₀) (n + 1) (x.1 (n + 1)) := by
  rw [projInfInf_apply]
  set g := fun n m =>
    embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
      (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
               (embInf (towerType D₀) (towerProj D₀ j₀) n)
               (iInfTerm D₀ j₀ m x)) with hg
  have hmono (n : ℕ) : Monotone (fun m =>
      conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
              (embInf (towerType D₀) (towerProj D₀ j₀) n)
              (iInfTerm D₀ j₀ m x)) := fun a b hab =>
    (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
             (embInf (towerType D₀) (towerProj D₀ j₀) n)).monotone
      (ScottMap.le_def.mpr (iInfTerm_monotone D₀ j₀ x hab))
  have hinner (n : ℕ) : jInfTerm D₀ j₀ n (embInfInf D₀ j₀ x) = ⨆ m, g n m :=
    calc jInfTerm D₀ j₀ n (embInfInf D₀ j₀ x)
        = embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
            (⨆ m, conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                          (embInf (towerType D₀) (towerProj D₀ j₀) n)
                          (iInfTerm D₀ j₀ m x)) := by
          rw [jInfTerm_apply, embInfInf_apply,
            conjMap_iSup D₀ j₀ n (projInf (towerType D₀) (towerProj D₀ j₀) n)
              (embInf (towerType D₀) (towerProj D₀ j₀) n)
              (fun m => iInfTerm D₀ j₀ m x) (iInfTerm_monotone D₀ j₀ x)]
          rfl
      _ = ⨆ m, embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
              (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                       (embInf (towerType D₀) (towerProj D₀ j₀) n)
                       (iInfTerm D₀ j₀ m x)) :=
          embInf_succ_iSup D₀ j₀ n _ (hmono n)
      _ = ⨆ m, g n m := by simp only [hg]
  have g_mono_m (n : ℕ) : Monotone (g n) := by
    intro a b hab
    rw [hg]
    exact (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)).monotone
      ((conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                 (embInf (towerType D₀) (towerProj D₀ j₀) n)).monotone
        (ScottMap.le_def.mpr (iInfTerm_monotone D₀ j₀ x hab)))
  have g_mono_n_succ (m n : ℕ) : g n m ≤ g (n + 1) m := by
    rw [hg]
    dsimp only
    rw [← embInf_succ (towerType D₀) (towerProj D₀ j₀) (n + 1)
        (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                 (embInf (towerType D₀) (towerProj D₀ j₀) n)
                 (iInfTerm D₀ j₀ m x))]
    exact embInf_monotone (towerType D₀) (towerProj D₀ j₀) (n + 2)
      (conjMap_incl_le_conjMap_succ D₀ j₀ n (iInfTerm D₀ j₀ m x))
  have g_mono_n (m : ℕ) : Monotone (fun n => g n m) :=
    monotone_nat_of_le_succ (g_mono_n_succ m)
  have hin : (⨆ n, jInfTerm D₀ j₀ n (embInfInf D₀ j₀ x)) = ⨆ n, ⨆ m, g n m := by
    congr 1
    funext n
    exact hinner n
  rw [hin, iSup₂_monotone_eq_diagonal g g_mono_m g_mono_n]
  congr 1
  funext n
  rw [hg]
  dsimp only
  rw [conj_iInfTerm_eq D₀ j₀ n x]

/-- **Scott 1972, §4 (Theorem 4.4, first half).** `j_∞ ∘ i_∞ = id` on `D_∞`. -/
theorem projInfInf_comp_embInfInf :
    (projInfInf D₀ j₀).comp (embInfInf D₀ j₀) = ScottMap.idMap := by
  apply ScottMap.ext
  intro x
  have hmono : Monotone (fun k => embInf (towerType D₀) (towerProj D₀ j₀) k (x.1 k)) :=
    monotone_nat_of_le_succ (embInf_le_succ (towerType D₀) (towerProj D₀ j₀) x)
  rw [ScottMap.comp_apply, ScottMap.idMap_apply, projInfInf_embInfInf_eq D₀ j₀ x,
    Monotone.iSup_nat_add hmono 1]
  exact (inverseLimit_eq_iSup (towerType D₀) (towerProj D₀ j₀) x).symm

/-! ### Theorem 4.4(c): `i_∞ ∘ j_∞ = id` on `[D_∞ → D_∞]`

This is the converse half (Scott ~lines 1322–1335). The restrictions
`u_n = j_{∞n} ∘ f ∘ i_{n∞} ∈ D_{n+1}` satisfy the Lemma-4.5 recursion `j_{n+1}(u_{n+2}) = u_{n+1}`
(`towerProj_retr_conjMap_succ`), so Lemma 4.5 identifies the components of `j_∞(f)`. Expanding
`i_∞(j_∞(f))` then yields the approximation `⨆ₙ rₙ ∘ f ∘ rₙ` with `rₙ = i_{n∞} ∘ j_{∞n}`, and the
functional equation `id = ⨆ₙ rₙ` (via `inverseLimit_eq_iSup`) plus continuity of `f` collapse this
to `f`. -/

/-- **Step 1 (Lemma-4.5 recursion).** `j_{n+1}(j_{∞(n+1)} ∘ f ∘ i_{(n+1)∞}) = j_{∞n} ∘ f ∘ i_{n∞}`.
This is the equality counterpart of `conjMap_incl_le_conjMap_succ`; it is the hypothesis Lemma 4.5
needs to recognize `j_∞(f)` from its restrictions. -/
theorem towerProj_retr_conjMap_succ (n : ℕ) (f : DInfFn D₀ j₀) :
    (towerProj D₀ j₀ (n + 1)).retr
        (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1))
                 (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)) f)
      = conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                (embInf (towerType D₀) (towerProj D₀ j₀) n) f := by
  apply ScottMap.ext
  intro y
  show (towerProj D₀ j₀ n).retr
      (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
        (f (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
          ((towerProj D₀ j₀ n).incl y))))
    = projInf (towerType D₀) (towerProj D₀ j₀) n
        (f (embInf (towerType D₀) (towerProj D₀ j₀) n y))
  rw [embInf_succ (towerType D₀) (towerProj D₀ j₀) n y]
  exact (f (embInf (towerType D₀) (towerProj D₀ j₀) n y)).2 n

/-- **Scott 1972, §4 (Theorem 4.4, second half).** `i_∞ ∘ j_∞ = id` on `[D_∞ → D_∞]`. -/
theorem embInfInf_comp_projInfInf :
    (embInfInf D₀ j₀).comp (projInfInf D₀ j₀) = ScottMap.idMap := by
  apply ScottMap.ext
  intro f
  rw [ScottMap.comp_apply, ScottMap.idMap_apply]
  apply ScottMap.ext
  intro z
  -- `rₙ = i_{n∞} ∘ j_{∞n}`, the Proposition-4.2 approximation of the identity on `D_∞`.
  set r : ℕ → ScottMap (DInf D₀ j₀) (DInf D₀ j₀) :=
    fun n => (embInf (towerType D₀) (towerProj D₀ j₀) n).comp
              (projInf (towerType D₀) (towerProj D₀ j₀) n) with hr
  have hrw : ∀ n (w : DInf D₀ j₀), r n w
      = embInf (towerType D₀) (towerProj D₀ j₀) n
          (projInf (towerType D₀) (towerProj D₀ j₀) n w) := by
    intro n w
    simp only [hr, ScottMap.comp_apply]
  have hr_mono : ∀ (w : DInf D₀ j₀), Monotone (fun m => r m w) := by
    intro w
    refine monotone_nat_of_le_succ (fun m => ?_)
    show r m w ≤ r (m + 1) w
    rw [hrw, hrw]
    exact embInf_le_succ (towerType D₀) (towerProj D₀ j₀) w m
  -- The functional equation `id = ⨆ₙ rₙ` (remark following Proposition 4.2), pointwise.
  have hA : ∀ (w : DInf D₀ j₀), w = ⨆ m, r m w := by
    intro w
    have h1 : (⨆ m, r m w)
        = ⨆ m, embInf (towerType D₀) (towerProj D₀ j₀) m
                (projInf (towerType D₀) (towerProj D₀ j₀) m w) :=
      iSup_congr (fun m => hrw m w)
    rw [h1]
    exact inverseLimit_eq_iSup (towerType D₀) (towerProj D₀ j₀) w
  -- Evaluating a supremum of Scott maps `D_∞ → D_∞` at a point is pointwise.
  have hsup_apply : ∀ (g : ℕ → ScottMap (DInf D₀ j₀) (DInf D₀ j₀)) (w : DInf D₀ j₀),
      (⨆ n, g n) w = ⨆ n, g n w := by
    intro g w
    rw [show (⨆ n, g n) = sSup (Set.range g) from sSup_range.symm,
      ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
    rfl
  -- A Scott map commutes with a monotone `ℕ`-indexed supremum.
  have hcont : ∀ (g : ScottMap (DInf D₀ j₀) (DInf D₀ j₀)) (a : ℕ → DInf D₀ j₀),
      Monotone a → g (⨆ m, a m) = ⨆ m, g (a m) := by
    intro g a ha
    have hdir : DirectedOn (· ≤ ·) (Set.range a) :=
      directedOn_range.2 fun i j => ⟨max i j, ha (le_max_left i j), ha (le_max_right i j)⟩
    rw [show (⨆ m, a m) = sSup (Set.range a) from sSup_range.symm,
      g.preservesDirectedSup_coe (Set.range a) (Set.range_nonempty a) hdir,
      ← Set.range_comp, sSup_range]
    rfl
  -- `j_∞(f) = ⨆ₖ i_{(k+1)∞}(j_{∞k} ∘ f ∘ i_{k∞})`.
  have hpi : projInfInf D₀ j₀ f
      = ⨆ k, embInf (towerType D₀) (towerProj D₀ j₀) (k + 1)
          (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) k)
                   (embInf (towerType D₀) (towerProj D₀ j₀) k) f) := by
    rw [projInfInf_apply]
    exact iSup_congr (fun n => jInfTerm_apply D₀ j₀ n f)
  -- Lemma 4.5: the `(n+1)`-st component of `j_∞(f)` is the restriction `j_{∞n} ∘ f ∘ i_{n∞}`.
  have hcoord : ∀ n, (projInfInf D₀ j₀ f).1 (n + 1)
      = conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                (embInf (towerType D₀) (towerProj D₀ j₀) n) f := by
    intro n
    rw [hpi]
    exact lemma_4_5 (towerType D₀) (towerProj D₀ j₀)
      (fun k => conjMap (projInf (towerType D₀) (towerProj D₀ j₀) k)
                        (embInf (towerType D₀) (towerProj D₀ j₀) k) f)
      (fun m => towerProj_retr_conjMap_succ D₀ j₀ m f) n
  -- Evaluate `i_∞(j_∞(f))` pointwise as a sup of summands.
  have hev : embInfInf D₀ j₀ (projInfInf D₀ j₀ f) z
      = ⨆ n, (iInfTerm D₀ j₀ n (projInfInf D₀ j₀ f)) z := by
    rw [embInfInf_apply]
    exact hsup_apply (fun n => iInfTerm D₀ j₀ n (projInfInf D₀ j₀ f)) z
  -- Each summand is `rₙ (f (rₙ z))` (using `hcoord` and `conjMap`).
  have hterm : ∀ n, (iInfTerm D₀ j₀ n (projInfInf D₀ j₀ f)) z = r n (f (r n z)) := by
    intro n
    rw [hrw, hrw, iInfTerm_apply, hcoord n]
    rfl
  have hmono_frz : Monotone (fun m => f (r m z)) :=
    fun a b hab => f.monotone (hr_mono z hab)
  have hfm : ∀ n, Monotone (fun m => r n (f (r m z))) :=
    fun n _ _ hab => (r n).monotone (f.monotone (hr_mono z hab))
  have hfn : ∀ m, Monotone (fun n => r n (f (r m z))) :=
    fun m => hr_mono (f (r m z))
  -- The analytic step (Scott ~1326–1334): confine the lub via continuity of `f`, then collapse the
  -- monotone double sup to its diagonal.
  have hfz : f z = ⨆ n, r n (f (r n z)) :=
    calc f z = ⨆ k, r k (f z) := hA (f z)
      _ = ⨆ k, r k (f (⨆ m, r m z)) := by
            refine iSup_congr (fun k => ?_)
            rw [← hA z]
      _ = ⨆ k, r k (⨆ m, f (r m z)) := by
            refine iSup_congr (fun k => ?_)
            rw [hcont f (fun m => r m z) (hr_mono z)]
      _ = ⨆ k, ⨆ m, r k (f (r m z)) :=
            iSup_congr (fun k => hcont (r k) (fun m => f (r m z)) hmono_frz)
      _ = ⨆ n, r n (f (r n z)) :=
            iSup₂_monotone_eq_diagonal (fun n m => r n (f (r m z))) hfm hfn
  calc embInfInf D₀ j₀ (projInfInf D₀ j₀ f) z
      = ⨆ n, (iInfTerm D₀ j₀ n (projInfInf D₀ j₀ f)) z := hev
    _ = ⨆ n, r n (f (r n z)) := iSup_congr hterm
    _ = f z := hfz.symm

end Thm44b

/-! ### Theorem 4.4(d): `D_∞` is homeomorphic to `[D_∞ → D_∞]`

Scott's statement of Theorem 4.4 is the homeomorphism. The maps `i_∞` and `j_∞` from (b) and (c)
are mutually inverse and Scott-continuous (bundled `ScottMap`s), so they are that homeomorphism. -/

section Thm44d

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

theorem projInfInf_embInfInf (x : DInf D₀ j₀) :
    projInfInf D₀ j₀ (embInfInf D₀ j₀ x) = x := by
  have h := congrArg (fun g => g x) (projInfInf_comp_embInfInf D₀ j₀)
  simpa [ScottMap.comp_apply, ScottMap.idMap_apply] using h

theorem embInfInf_projInfInf (f : DInfFn D₀ j₀) :
    embInfInf D₀ j₀ (projInfInf D₀ j₀ f) = f := by
  have h := congrArg (fun g => g f) (embInfInf_comp_projInfInf D₀ j₀)
  simpa [ScottMap.comp_apply, ScottMap.idMap_apply] using h

theorem embInfInf_le_iff (x y : DInf D₀ j₀) :
    embInfInf D₀ j₀ x ≤ embInfInf D₀ j₀ y ↔ x ≤ y := by
  constructor
  · intro h
    have := (projInfInf D₀ j₀).monotone h
    rwa [projInfInf_embInfInf, projInfInf_embInfInf] at this
  · intro h; exact (embInfInf D₀ j₀).monotone h

/-- The inverse pair Scott writes down in the proof of Theorem 4.4:
`i_∞ = embInfInf` and `j_∞ = projInfInf` satisfy `j_∞ ∘ i_∞ = id` and `i_∞ ∘ j_∞ = id`. -/
theorem theorem_4_4_inverses :
    (projInfInf D₀ j₀).comp (embInfInf D₀ j₀) = ScottMap.idMap ∧
    (embInfInf D₀ j₀).comp (projInfInf D₀ j₀) = ScottMap.idMap :=
  ⟨projInfInf_comp_embInfInf D₀ j₀, embInfInf_comp_projInfInf D₀ j₀⟩

/-- Lattice isomorphism along the same pair `i_∞`, `j_∞`. Scott's abstract also says the spaces
are isomorphic; this is not the statement of Theorem 4.4 (that statement is the homeomorphism). -/
noncomputable def theorem_4_4_orderIso : OrderIso (DInf D₀ j₀) (DInfFn D₀ j₀) :=
  (Equiv.mk (embInfInf D₀ j₀) (projInfInf D₀ j₀)
      (projInfInf_embInfInf D₀ j₀) (embInfInf_projInfInf D₀ j₀)).toOrderIso
    (embInfInf D₀ j₀).monotone (projInfInf D₀ j₀).monotone

/-- The pair \(i_\infty, j_\infty\) from the proof of Theorem 4.4, first packaged using the
Scott lattice topologies on both sides.  Scott writes
`i∞(x) = ⨆ₙ (i_{n∞} ∘ x_{n+1} ∘ j_{∞n})` and
`j∞(f) = ⨆ₙ i_{(n+1)∞}(j_{∞n} ∘ f ∘ i_{n∞})`, and says
(`sources/ScottContinLatt1972.md`): “We can write down directly the pair of maps
`i∞, j∞` that provide the homeomorphism.”

This helper is deliberately distinct from the source-topology homeomorphism in the numbered
theorem below. -/
noncomputable def theorem_4_4_scottTopology_homeomorph :
    @Homeomorph (DInf D₀ j₀) (DInfFn D₀ j₀) scottTopologicalSpace scottTopologicalSpace :=
  @Homeomorph.mk (DInf D₀ j₀) (DInfFn D₀ j₀) scottTopologicalSpace scottTopologicalSpace
    (Equiv.mk (embInfInf D₀ j₀) (projInfInf D₀ j₀)
      (projInfInf_embInfInf D₀ j₀) (embInfInf_projInfInf D₀ j₀))
    (embInfInf D₀ j₀).continuous (projInfInf D₀ j₀).continuous

/-- Scott's Theorem 4.4 homeomorphism with the literal topologies used in the source:
the inverse-limit subspace topology from the Pi product on `D∞`, and Definition 3.1's
pointwise (equivalently Pi-induced) topology on `[D∞ → D∞]`.

The topology changes are the mathematical identifications supplied by Proposition 4.1 and
Theorem 3.3; the underlying maps remain Scott's displayed `i∞` and `j∞` formulas above. -/
noncomputable def theorem_4_4_sourceTopology_homeomorph
    (hTower : ∀ n, IsContinuousLattice (towerType D₀ n)) :
    @Homeomorph (DInf D₀ j₀) (DInfFn D₀ j₀)
      (inverseLimitTopology (towerType D₀) (towerProj D₀ j₀))
      (scottMapInducedPiTopology (DInf D₀ j₀) (DInf D₀ j₀)) := by
  have hDInf : IsContinuousLattice (DInf D₀ j₀) :=
    proposition_4_1 (towerType D₀) (towerProj D₀ j₀) hTower
  rw [← inverseLimit_scottTopology_eq_induced_pi
        (towerType D₀) (towerProj D₀ j₀) hTower,
      ← theorem_3_3_topology_induced_pi hDInf hDInf]
  exact theorem_4_4_scottTopology_homeomorph D₀ j₀

/-- **Scott 1972, Theorem 4.4** (`sources/ScottContinLatt1972.md`):
*The inverse limit \(D_\infty\) of the recursively defined sequence
\(\langle D_n, j_n \rangle_{n=0}^{\infty}\) of function spaces is not only a
continuous lattice, but it is also homeomorphic to its own function space
\([D_\infty \to D_\infty]\).*  Here “inverse limit” carries Scott's subspace
topology from the Pi product, while the function space carries Definition 3.1's
pointwise/Pi-induced topology. -/
theorem theorem_4_4 (h₀ : IsContinuousLattice D₀.carrier) :
    @IsContinuousLattice (DInf D₀ j₀) inferInstance ∧
      Nonempty
        (@Homeomorph (DInf D₀ j₀) (DInfFn D₀ j₀)
          (inverseLimitTopology (towerType D₀) (towerProj D₀ j₀))
          (scottMapInducedPiTopology (DInf D₀ j₀) (DInf D₀ j₀))) := by
  have hTower : ∀ n, IsContinuousLattice (towerType D₀ n) := by
    intro n
    induction n with
    | zero => exact h₀
    | succ n ih => exact theorem_3_3_isContinuousLattice ih ih
  refine ⟨proposition_4_1 (towerType D₀) (towerProj D₀ j₀) hTower, ?_⟩
  exact ⟨theorem_4_4_sourceTopology_homeomorph D₀ j₀ hTower⟩

end Thm44d

end LimitMaps

end Scott1972.ContinuousLattice
