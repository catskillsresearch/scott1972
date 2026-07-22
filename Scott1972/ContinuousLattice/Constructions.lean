/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1972
-/

import Scott1972.ContinuousLattice.MilnerCorrection
import Scott1972.ContinuousLattice.ScottMaps
import Scott1972.ContinuousLattice.Injective
import Mathlib.Order.Preorder.Finite

/-!
# Continuous lattice constructions (Scott 1972, §2.8–2.12)

The Milner correction (March 1972, pp. 135–136) is in `MilnerCorrection.lean`. Full proofs of
2.8–2.12 under `CoarserThanScottTopology` are the remaining 1972 items; the Sierpiński
injectivity base case (1.2) is already complete.

This file additionally proves Scott's first two example/closure results, the order-theoretic
content of Propositions 2.8 (finite lattices are continuous) and 2.9 (products of continuous
lattices are continuous). The accompanying topological claims of 2.9–2.10 ("the induced
topology agrees with the product / subspace topology") are the parts that require the Milner
correction and remain open.
-/

namespace Scott1972.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

/-- A non-empty **finite** directed set attains its supremum: `⊔S ∈ S`. A maximal element of
`S` (which exists by finiteness) is, by directedness, the greatest element, hence the
supremum. This is the order-theoretic heart of "finite ⟹ continuous" (Scott 1972, 2.8). -/
theorem directedOn_finite_sSup_mem {S : Set D} (hSfin : S.Finite) (hSne : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) : sSup S ∈ S := by
  obtain ⟨m, hm⟩ := hSfin.exists_maximal hSne
  have hub : m ∈ upperBounds S := by
    intro s hs
    obtain ⟨c, hcS, hmc, hsc⟩ := hSdir m hm.1 s hs
    exact hsc.trans (hm.2 hcS hmc)
  have hlub : IsLUB S m := ⟨hub, fun b hb => hb hm.1⟩
  rw [hlub.sSup_eq]
  exact hm.1

/-- **Scott 1972, Proposition 2.8.** A finite lattice is a continuous lattice. In a finite
lattice every principal up-set `Set.Ici y` is Scott-open (a non-empty directed set is finite,
so it attains its supremum), hence `y ≪ y`; therefore `y` is the supremum of `{x | x ≪ y}`. -/
theorem proposition_2_8 [Finite D] : IsContinuousLattice D := by
  intro y
  have hopen : ScottOpen (Set.Ici y) := by
    refine ⟨isUpperSet_Ici y, fun S hSne hSdir hmem => ?_⟩
    exact ⟨sSup S, directedOn_finite_sSup_mem (Set.toFinite S) hSne hSdir, hmem⟩
  have hyy : y ≪ y := wayBelow_self_iff_scottOpen_Ici.mpr hopen
  exact ⟨fun x hx => hx.le, fun b hb => hb hyy⟩

/-- **Scott 1972, Proposition 2.9(a) (order-theoretic content).** The Cartesian product of any
family of continuous lattices is a continuous lattice. (Part (b), that the induced topology of
the product agrees with the product topology, is `proposition_2_9_b` below; `proposition_2_9`
bundles the two.)

The key step is that if `a ≪ yᵢ` in the factor `Dᵢ`, then the cylinder element `[a]ⁱ`
(equal to `a` in coordinate `i` and `⊥` elsewhere) is way below `y` in the product: the
preimage `{z | zᵢ ∈ U}` of a Scott-open witness `U ⊆ Dᵢ` is Scott-open in the product
(suprema are computed coordinatewise). Any upper bound `b` of `{x | x ≪ y}` therefore
dominates every `[a]ⁱ`, so `a = ([a]ⁱ)ᵢ ≤ bᵢ`; ranging over `a ≪ yᵢ` and using continuity of
`Dᵢ` gives `yᵢ ≤ bᵢ` for all `i`, i.e. `y ≤ b`. -/
theorem proposition_2_9_a {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, IsContinuousLattice (E i)) : IsContinuousLattice (∀ i, E i) := by
  classical
  intro y
  refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
  rw [Pi.le_def]
  intro i
  rw [← (hE i).sSup_wayBelow (y i)]
  apply sSup_le
  intro a ha
  set e : (∀ j, E j) := Function.update (⊥ : ∀ j, E j) i a with he
  have hei : e i = a := by rw [he]; exact Function.update_self i a _
  have hcyl : e ≪ y := by
    obtain ⟨U, hU, hyiU, hUsub⟩ := ha
    refine ⟨{z : ∀ j, E j | z i ∈ U}, ?_, hyiU, ?_⟩
    · refine ⟨fun z w hzw hz => hU.1 (hzw i) hz, fun S hSne hSdir hmem => ?_⟩
      rw [Set.mem_setOf_eq, sSup_apply_eq_sSup_image] at hmem
      have hdir' : DirectedOn (· ≤ ·) (Function.eval i '' S) := by
        rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
        obtain ⟨h, hhS, hfh, hgh⟩ := hSdir f hf g hg
        exact ⟨Function.eval i h, ⟨h, hhS, rfl⟩, hfh i, hgh i⟩
      obtain ⟨t, htimg, htU⟩ := hU.2 (hSne.image _) hdir' hmem
      obtain ⟨f, hfS, rfl⟩ := htimg
      exact ⟨f, hfS, htU⟩
    · intro z hz
      rw [Set.mem_Ici, Pi.le_def]
      intro j
      rcases eq_or_ne j i with rfl | hji
      · rw [hei]; exact Set.mem_Ici.1 (hUsub hz)
      · rw [he, Function.update_of_ne hji]; exact bot_le
  have hle : e i ≤ b i := (hb hcyl) i
  rw [hei] at hle
  exact hle

/-! ### Proposition 2.9(b): the induced topology of a product is the product topology

Scott 1972, Proposition 2.9 also asserts that the Scott topology of the product `∏ᵢ Dᵢ` of
continuous lattices coincides with the topological product of the Scott topologies of the factors.
We prove the two inclusions:

* **Product ⊆ Scott** (`scottTopologicalSpace ≤ Pi.topologicalSpace`): every projection
  `eval i` preserves directed suprema (they are computed coordinatewise), hence is Scott-continuous,
  hence the Scott topology of the product is finer than each induced topology, i.e. finer than their
  infimum (the product topology).
* **Scott ⊆ Product** (`Pi.topologicalSpace ≤ scottTopologicalSpace`): given a Scott-open `U` and a
  point `z ∈ U`, the `↟a` basis (`exists_wayBelow_Ici_subset`) yields `a ≪ z` with `↑a ⊆ U`. A
  way-below element of a product has **finite support** (`wayBelow_finite_support`) and is
  way-below in each coordinate (`wayBelow_proj`); the resulting finite box
  `⋂_{i ∈ F} eval i ⁻¹' (↟aᵢ-neighbourhood of zᵢ)` is a product-open neighbourhood of `z` inside
  `↑a ⊆ U`. -/

/-- Plugging a value into a fixed coordinate, `v ↦ Function.update z i v`, preserves directed
suprema: away from `i` the result is the constant `z j`, and at `i` it is the identity. -/
theorem update_preservesDirectedSup {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, CompleteLattice (E i)] (z : ∀ i, E i) (i : ι) :
    PreservesDirectedSup (fun v : E i => Function.update z i v) := by
  intro T hTne _
  show Function.update z i (sSup T) = sSup ((fun v : E i => Function.update z i v) '' T)
  funext j
  rw [sSup_apply_eq_sSup_image, Set.image_image]
  rcases eq_or_ne j i with hji | hji
  · rw [hji, Function.update_self]
    have h : (fun v : E i => Function.eval i (Function.update z i v)) = id := by
      funext v; simp [Function.eval, Function.update_self]
    rw [h, Set.image_id]
  · rw [Function.update_of_ne hji]
    have h : (fun v : E i => Function.eval j (Function.update z i v)) = fun _ => z j := by
      funext v; simp [Function.eval, Function.update_of_ne hji]
    rw [h, hTne.image_const, sSup_singleton]

/-- A way-below relation in a product projects to each coordinate: if `a ≪ z` in `∏ᵢ Eᵢ` then
`aᵢ ≪ zᵢ`. The witnessing Scott-open neighbourhood of `zᵢ` is the preimage of a product Scott-open
witness under `v ↦ Function.update z i v`, which is Scott-open by `update_preservesDirectedSup`. -/
theorem wayBelow_proj {ι : Type*} {E : ι → Type*} [∀ i, CompleteLattice (E i)]
    {a z : ∀ i, E i} (h : a ≪ z) (i : ι) : a i ≪ z i := by
  classical
  obtain ⟨W, hW, hzW, hWsub⟩ := h
  refine ⟨(fun v : E i => Function.update z i v) ⁻¹' W, ?_, ?_, ?_⟩
  · exact scottOpen_preimage (update_preservesDirectedSup z i) hW
  · show Function.update z i (z i) ∈ W
    rw [Function.update_eq_self]; exact hzW
  · intro v hv
    have hav : a ≤ Function.update z i v := Set.mem_Ici.1 (hWsub hv)
    have := hav i
    rwa [Function.update_self] at this

/-- A way-below element of a product has finite support: if `a ≪ z` in `∏ᵢ Eᵢ` then `aⱼ = ⊥` for
all but finitely many `j`. The finite truncations `Z F = (fun j => if j ∈ F then z j else ⊥)` form a
directed family with supremum `z`; since `a ≪ z = ⊔_F Z F`, already `a ≤ Z F` for some finite `F`,
forcing `aⱼ = ⊥` off `F`. -/
theorem wayBelow_finite_support {ι : Type*} {E : ι → Type*} [∀ i, CompleteLattice (E i)]
    {a z : ∀ i, E i} (h : a ≪ z) : ∃ F : Finset ι, ∀ j ∉ F, a j = ⊥ := by
  classical
  set Z : Finset ι → (∀ j, E j) := fun F j => if j ∈ F then z j else ⊥ with hZ
  set 𝒵 : Set (∀ j, E j) := Set.range Z with h𝒵
  have hmono : Monotone Z := by
    intro F G hFG
    rw [Pi.le_def]; intro j
    simp only [hZ]
    by_cases hjF : j ∈ F
    · rw [if_pos hjF, if_pos (hFG hjF)]
    · rw [if_neg hjF]; exact bot_le
  have h𝒵ne : 𝒵.Nonempty := ⟨Z ∅, ∅, rfl⟩
  have h𝒵dir : DirectedOn (· ≤ ·) 𝒵 := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    exact ⟨Z (F ∪ G), ⟨F ∪ G, rfl⟩, hmono Finset.subset_union_left,
      hmono Finset.subset_union_right⟩
  have hsup : sSup 𝒵 = z := by
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨F, rfl⟩
      rw [Pi.le_def]; intro j
      simp only [hZ]
      by_cases hjF : j ∈ F
      · rw [if_pos hjF]
      · rw [if_neg hjF]; exact bot_le
    · rw [Pi.le_def]; intro j
      rw [sSup_apply_eq_sSup_image]
      refine le_sSup ⟨Z {j}, ⟨{j}, rfl⟩, ?_⟩
      simp [hZ, Function.eval]
  rw [← hsup] at h
  obtain ⟨d, hd𝒵, had⟩ := (wayBelow_sSup_iff h𝒵ne h𝒵dir).1 h
  obtain ⟨F, rfl⟩ := hd𝒵
  refine ⟨F, fun j hjF => ?_⟩
  have hj := had.le j
  simp only [hZ, if_neg hjF] at hj
  exact le_bot_iff.1 hj

/-- **Scott 1972, Proposition 2.9(b).** For a family of continuous lattices, the Scott topology of
the product coincides with the product of the Scott topologies of the factors. -/
theorem proposition_2_9_b {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, IsContinuousLattice (E i)) :
    (scottTopologicalSpace : TopologicalSpace (∀ i, E i)) =
      @Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace) := by
  classical
  have hprod : IsContinuousLattice (∀ i, E i) := proposition_2_9_a E hE
  apply le_antisymm
  · -- Product ⊆ Scott: projections preserve directed suprema, hence are Scott-continuous.
    refine le_iInf fun i => ?_
    rw [← continuous_iff_le_induced]
    exact continuous_of_preservesDirectedSup (fun _ _ _ => sSup_apply_eq_sSup_image)
  · -- Scott ⊆ Product: every Scott-open set is a union of finite product-open boxes.
    intro U hU
    rw [isOpen_iff_scottOpen] at hU
    rw [@isOpen_iff_forall_mem_open _ (@Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace))]
    intro z hz
    obtain ⟨a, haz, haIci⟩ := exists_wayBelow_Ici_subset hprod hU hz
    obtain ⟨F, hF⟩ := wayBelow_finite_support haz
    have hproj : ∀ i, a i ≪ z i := fun i => wayBelow_proj haz i
    choose V hVopen hzV hVsub using hproj
    refine ⟨⋂ i ∈ F, (fun w : ∀ j, E j => w i) ⁻¹' V i, ?_, ?_, ?_⟩
    · -- the box lies inside `↑a ⊆ U`
      intro w hw
      rw [Set.mem_iInter₂] at hw
      refine haIci (Set.mem_Ici.2 fun j => ?_)
      by_cases hjF : j ∈ F
      · exact Set.mem_Ici.1 (hVsub j (hw j hjF))
      · rw [hF j hjF]; exact bot_le
    · -- the box is product-open: a finite intersection of cylinders over Scott-open factors
      refine @isOpen_biInter_finset (∀ j, E j) ι
        (@Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace)) F
        (fun i => (fun w : ∀ j, E j => w i) ⁻¹' V i) (fun i _ => ?_)
      have hVi : @IsOpen (E i) scottTopologicalSpace (V i) := isOpen_iff_scottOpen.mpr (hVopen i)
      have hind : @IsOpen _
          (TopologicalSpace.induced (fun w : ∀ j, E j => w i) scottTopologicalSpace)
          ((fun w : ∀ j, E j => w i) ⁻¹' V i) :=
        (isOpen_induced_iff (t := scottTopologicalSpace)).mpr ⟨V i, hVi, rfl⟩
      exact iInf_le
        (fun i => TopologicalSpace.induced (fun w : ∀ j, E j => w i) scottTopologicalSpace) i _ hind
    · -- the box contains `z`
      rw [Set.mem_iInter₂]
      exact fun i _ => hzV i

/-- **Scott 1972, Proposition 2.9 (full statement).** The product of a family of continuous lattices
is again a continuous lattice (`proposition_2_9_a`) whose Scott topology agrees with the product
topology (`proposition_2_9_b`). -/
theorem proposition_2_9 {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, IsContinuousLattice (E i)) :
    IsContinuousLattice (∀ i, E i) ∧
      (scottTopologicalSpace : TopologicalSpace (∀ i, E i)) =
        @Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace) :=
  ⟨proposition_2_9_a E hE, proposition_2_9_b E hE⟩

/-! ### Proposition 2.11: continuous lattices are injective

The substance of Scott's Theorem 2.12. We give the explicit extension operator
`g(y) = ⊔_{V ∋ y open} ⊓ f''(e⁻¹V)` and prove (a) it extends `f` along an embedding `e`
(using continuity of `D` to interpolate from below) and (b) it is Scott-continuous (using the
`↟a` basis of the Scott topology). -/

section InjectiveExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]

/-- Scott's canonical extension of `f : X → E` along `e : X → Y` (Scott 1972, proof of 2.11):
`y ↦ ⊔ { ⊓ f''(e⁻¹V) : V an open neighbourhood of y }`. No topology on `E` is needed to *state*
the operator — it is purely order-theoretic. -/
def scottExtend (e : X → Y) (f : X → E) (y : Y) : E :=
  sSup {d | ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ d = sInf (f '' (e ⁻¹' V))}

theorem scottExtend_aux_nonempty (e : X → Y) (f : X → E) (y : Y) :
    {d | ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ d = sInf (f '' (e ⁻¹' V))}.Nonempty :=
  ⟨_, Set.univ, isOpen_univ, Set.mem_univ y, rfl⟩

/-- The defining family of `scottExtend` is directed: open neighbourhoods are closed under
intersection, and `⊓ f''(e⁻¹ ·)` is monotone in the neighbourhood (smaller set, larger inf). -/
theorem scottExtend_aux_directed (e : X → Y) (f : X → E) (y : Y) :
    DirectedOn (· ≤ ·) {d | ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ d = sInf (f '' (e ⁻¹' V))} := by
  rintro _ ⟨V₁, hV₁o, hyV₁, rfl⟩ _ ⟨V₂, hV₂o, hyV₂, rfl⟩
  refine ⟨sInf (f '' (e ⁻¹' (V₁ ∩ V₂))), ⟨V₁ ∩ V₂, hV₁o.inter hV₂o, ⟨hyV₁, hyV₂⟩, rfl⟩, ?_, ?_⟩
  · exact sInf_le_sInf (Set.image_mono (Set.preimage_mono Set.inter_subset_left))
  · exact sInf_le_sInf (Set.image_mono (Set.preimage_mono Set.inter_subset_right))

/-- The extension agrees with `f` on the (embedded) subspace. The `≤` direction is immediate
(`f x₀` is one of the values being met); the `≥` direction uses continuity of `E`: for each
`a ≪ f x₀` the Scott-open `↟a` pulls back along the continuous `f` and, by the embedding, to an
open `V ⊆ Y` on whose `e`-preimage `f ≥ a`, so `a ≤ ⊓ f''(e⁻¹V) ≤ g(e x₀)`. -/
theorem scottExtend_eq_of_continuous (hE : IsContinuousLattice E) (e : X → Y)
    (he : IsEmbedding e) (f : X → E) (hf : @Continuous X E _ scottTopologicalSpace f) (x₀ : X) :
    scottExtend e f (e x₀) = f x₀ := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro d ⟨V, hVo, hex₀V, rfl⟩
    exact sInf_le ⟨x₀, hex₀V, rfl⟩
  · rw [← hE.sSup_wayBelow (f x₀)]
    refine sSup_le fun a ha => ?_
    have hWopen : @IsOpen E scottTopologicalSpace {z : E | a ≪ z} :=
      isOpen_iff_scottOpen.mpr (scottOpen_wayBelow a)
    have hpre : IsOpen (f ⁻¹' {z : E | a ≪ z}) := continuous_def.mp hf _ hWopen
    rw [he.isInducing.isOpen_iff] at hpre
    obtain ⟨V, hVo, hVeq⟩ := hpre
    have hx₀V : x₀ ∈ e ⁻¹' V := by rw [hVeq]; exact ha
    refine le_trans ?_ (le_sSup ⟨V, hVo, hx₀V, rfl⟩)
    refine le_sInf ?_
    rintro w ⟨x, hxV, rfl⟩
    have hxW : x ∈ f ⁻¹' {z : E | a ≪ z} := by rw [← hVeq]; exact hxV
    exact (hxW : a ≪ f x).le

/-- The extension is Scott-continuous. For a Scott-open `U` and a point `y₀` with `g y₀ ∈ U`, the
basis lemma gives `a ≪ g y₀` with `↟a ⊆ U`; since `g y₀` is a directed supremum, `a ≪ ⊓ f''(e⁻¹V)`
for some open `V ∋ y₀`, and that value is `≤ g y'` for every `y' ∈ V`, so `V ⊆ g⁻¹U`. -/
theorem scottExtend_continuous (hE : IsContinuousLattice E) (e : X → Y) (f : X → E) :
    @Continuous Y E _ scottTopologicalSpace (scottExtend e f) := by
  letI : TopologicalSpace E := scottTopologicalSpace
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_scottOpen] at hU
  rw [isOpen_iff_forall_mem_open]
  intro y₀ hy₀
  have hgy₀U : scottExtend e f y₀ ∈ U := hy₀
  obtain ⟨a, haz, hasub⟩ := exists_wayBelow_subset hE hU hgy₀U
  obtain ⟨d, hd, had⟩ := (wayBelow_sSup_iff (scottExtend_aux_nonempty e f y₀)
    (scottExtend_aux_directed e f y₀)).1 haz
  obtain ⟨V, hVo, hy₀V, rfl⟩ := hd
  refine ⟨V, ?_, hVo, hy₀V⟩
  intro y' hy'V
  show scottExtend e f y' ∈ U
  refine hasub ?_
  show a ≪ scottExtend e f y'
  exact had.trans_le (le_sSup ⟨V, hVo, hy'V, rfl⟩)

/-- For a continuous `f' : Y → E` into a continuous lattice `E` (with its Scott topology), the
value `f' y` is reconstructed as the supremum over open neighbourhoods `U ∋ y` of the meets
`⊓ f''(U)`. This is the order-theoretic content behind the maximality clause of Proposition 3.8:
the `≤` direction interpolates from below using `f' y = ⊔ {a | a ≪ f' y}` and the openness of each
`f'⁻¹(↟a)`; the `≥` direction is immediate since `f' y ∈ f''(U)` whenever `y ∈ U`. -/
theorem continuous_eq_sSup_openInfs (hE : IsContinuousLattice E) {f' : Y → E}
    (hf' : @Continuous Y E _ scottTopologicalSpace f') (y : Y) :
    f' y = sSup {d | ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ d = sInf (f' '' U)} := by
  apply le_antisymm
  · rw [← hE.sSup_wayBelow (f' y)]
    refine sSup_le fun a ha => ?_
    have hWopen : @IsOpen E scottTopologicalSpace {z : E | a ≪ z} :=
      isOpen_iff_scottOpen.mpr (scottOpen_wayBelow a)
    have hpre : IsOpen (f' ⁻¹' {z : E | a ≪ z}) := continuous_def.mp hf' _ hWopen
    have hyU : y ∈ f' ⁻¹' {z : E | a ≪ z} := ha
    refine le_trans ?_ (le_sSup ⟨f' ⁻¹' {z : E | a ≪ z}, hpre, hyU, rfl⟩)
    refine le_sInf ?_
    rintro w ⟨z, hzU, rfl⟩
    exact (hzU : a ≪ f' z).le
  · refine sSup_le ?_
    rintro d ⟨U, _hUo, hyU, rfl⟩
    exact sInf_le ⟨y, hyU, rfl⟩

/-- **Maximality clause of Scott 1972, Proposition 3.8.** Any continuous solution `f'` of
`f' ∘ e = f` lies below `scottExtend e f`. Following Scott: expand `f'` via
`continuous_eq_sSup_openInfs`, restrict each meet from `U` to the embedded subspace `e(X) ∩ U`
(only enlarging the meet), and recognize the result as a defining term of `scottExtend`. -/
theorem scottExtend_maximal (hE : IsContinuousLattice E) (e : X → Y) {f : X → E} {f' : Y → E}
    (hf' : @Continuous Y E _ scottTopologicalSpace f') (h_ext : ∀ x, f' (e x) = f x) (y : Y) :
    f' y ≤ scottExtend e f y := by
  rw [continuous_eq_sSup_openInfs hE hf' y]
  refine sSup_le ?_
  rintro d ⟨U, hUo, hyU, rfl⟩
  refine le_trans ?_ (le_sSup ⟨U, hUo, hyU, rfl⟩)
  refine le_sInf ?_
  rintro w ⟨x, hxU, rfl⟩
  rw [← h_ext x]
  exact sInf_le ⟨e x, hxU, rfl⟩

/-- **Scott 1972, remark following 3.8.** `scottExtend e g` is also the maximal *sub*-solution: any
continuous `f'` with `f' ∘ e ⊑ g` satisfies `f' ⊑ scottExtend e g`. Same proof as
`scottExtend_maximal`, replacing the final equality `f' (e x) = f x` by the inequality
`f' (e x) ≤ g x`. -/
theorem scottExtend_maximal_le (hE : IsContinuousLattice E) (e : X → Y) {g : X → E} {f' : Y → E}
    (hf' : @Continuous Y E _ scottTopologicalSpace f') (h_le : ∀ x, f' (e x) ≤ g x) (y : Y) :
    f' y ≤ scottExtend e g y := by
  rw [continuous_eq_sSup_openInfs hE hf' y]
  refine sSup_le ?_
  rintro d ⟨U, hUo, hyU, rfl⟩
  refine le_trans ?_ (le_sSup ⟨U, hUo, hyU, rfl⟩)
  refine le_sInf ?_
  rintro w ⟨x, hxU, rfl⟩
  exact le_trans (sInf_le ⟨e x, hxU, rfl⟩) (h_le x)

/-- **Scott 1972, Proposition 3.8.** If `E` is a continuous lattice and `e : X → Y` a subspace
embedding, then for each continuous `f : X → E` the explicit formula `scottExtend e f` is the
*maximal extension* of `f` to `[Y → E]`: it is Scott-continuous (`scottExtend_continuous`), it
restricts to `f` along `e` (`scottExtend_eq_of_continuous`), and it dominates every continuous
solution of `f' ∘ e = f` (`scottExtend_maximal`). -/
theorem proposition_3_8 (hE : IsContinuousLattice E) (e : X → Y) (he : IsEmbedding e)
    (f : X → E) (hf : @Continuous X E _ scottTopologicalSpace f) :
    @Continuous Y E _ scottTopologicalSpace (scottExtend e f)
      ∧ (∀ x, scottExtend e f (e x) = f x)
      ∧ (∀ f' : Y → E, @Continuous Y E _ scottTopologicalSpace f' → (∀ x, f' (e x) = f x) →
          ∀ y, f' y ≤ scottExtend e f y) :=
  ⟨scottExtend_continuous hE e f,
   fun x => scottExtend_eq_of_continuous hE e he f hf x,
   fun f' hf' h_ext y => scottExtend_maximal hE e hf' h_ext y⟩

end InjectiveExtension

/-- **Scott 1972, Proposition 2.11.** Every continuous lattice is an injective space under its
induced (Scott) topology. The witness is `scottExtend`, which extends any continuous `f` along
any embedding `e` (`scottExtend_eq_of_continuous`) and is itself continuous
(`scottExtend_continuous`). -/
theorem proposition_2_11 {E : Type*} [CompleteLattice E] (hE : IsContinuousLattice E) :
    @IsInjectiveSpace E scottTopologicalSpace := by
  letI : TopologicalSpace E := scottTopologicalSpace
  intro X Y _ _ e he f
  exact ⟨⟨scottExtend e f, scottExtend_continuous hE e f⟩,
    fun x => scottExtend_eq_of_continuous hE e he f f.continuous x⟩

/-- The Sierpiński space `Prop` (Scott's `𝕆`) is a continuous lattice: it is a finite complete
lattice, so Proposition 2.8 applies. -/
theorem isContinuousLattice_prop : IsContinuousLattice Prop :=
  proposition_2_8

/-- The Scott topology on Scott's two-point space `𝕆 = Prop` is exactly the Sierpiński topology
(`generateFrom {{True}}`). The Scott-open sets of `Prop` are the upper sets `∅`, `{True}`, `univ`,
which are precisely the Sierpiński-open sets. This is the topological identification underlying
Theorem 2.12: the building block `𝕆` carries its Scott topology. -/
theorem scottTopology_prop :
    (scottTopologicalSpace : TopologicalSpace Prop) = sierpinskiSpace := by
  apply le_antisymm
  · -- `scott ≤ sierpinski`: the single Sierpiński sub-basic open `{True}` is Scott-open.
    show (scottTopologicalSpace : TopologicalSpace Prop) ≤ TopologicalSpace.generateFrom {{True}}
    apply le_generateFrom
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    rw [isOpen_iff_scottOpen]
    refine ⟨?_, ?_⟩
    · intro a b hab ha
      rw [Set.mem_singleton_iff] at ha ⊢
      exact le_antisymm le_top (ha ▸ hab)
    · intro S _ _ hmem
      rw [Set.mem_singleton_iff] at hmem
      have hex : ∃ p ∈ S, p := by rw [← sSup_Prop_eq, hmem]; trivial
      obtain ⟨p, hpS, hp⟩ := hex
      exact ⟨p, hpS, by rw [Set.mem_singleton_iff]; exact eq_true hp⟩
  · -- `sierpinski ≤ scott`: every Scott-open upper set of `Prop` is `∅`, `{True}`, or `univ`.
    rw [TopologicalSpace.le_def]
    intro U hU
    rw [isOpen_iff_scottOpen] at hU
    by_cases hT : True ∈ U
    · by_cases hF : False ∈ U
      · have hUuniv : U = Set.univ := by
          ext p
          simp only [Set.mem_univ, iff_true]
          by_cases hp : p
          · rwa [eq_true hp]
          · rwa [eq_false hp]
        rw [hUuniv]; exact isOpen_univ
      · have hUtrue : U = {True} := by
          ext p
          rw [Set.mem_singleton_iff]
          constructor
          · intro hpU
            by_cases hp : p
            · exact eq_true hp
            · exact absurd (eq_false hp ▸ hpU) hF
          · intro hp; rw [hp]; exact hT
        rw [hUtrue]; exact isOpen_singleton_true
    · have hUempty : U = ∅ := by
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hpU
        exact hT (hU.1 le_top hpU)
      rw [hUempty]; exact isOpen_empty

/-- A power of Scott's two-point space `𝕆 = Prop` is a continuous lattice: `Prop` is a continuous
lattice (`isContinuousLattice_prop`) and products of continuous lattices are continuous
(Proposition 2.9(a)). This is the order-theoretic content of "a Cartesian power of `𝕆` is a
continuous lattice", the construction Theorem 2.12 retracts onto. -/
theorem sierpinskiPower_isContinuousLattice (ι : Type*) : IsContinuousLattice (ι → Prop) :=
  proposition_2_9_a (fun _ => Prop) (fun _ => isContinuousLattice_prop)

/-- The Scott topology on a power `ι → 𝕆` of the Sierpiński space coincides with the product
(= Sierpiński power) topology. Combine Proposition 2.9(b) (the Scott topology of a product is the
product of the factors' Scott topologies) with `scottTopology_prop` (each factor's Scott topology
is the Sierpiński topology). -/
theorem scottTopology_sierpinskiPower (ι : Type*) :
    (scottTopologicalSpace : TopologicalSpace (ι → Prop)) =
      (inferInstance : TopologicalSpace (ι → Prop)) := by
  rw [proposition_2_9_b (fun _ => Prop) (fun _ => isContinuousLattice_prop)]
  show (@Pi.topologicalSpace ι (fun _ => Prop) (fun _ => scottTopologicalSpace)) =
    @Pi.topologicalSpace ι (fun _ => Prop) (fun _ => sierpinskiSpace)
  congr 1
  funext _
  exact scottTopology_prop

/-- **Scott 1972, Theorem 2.12 (forward direction).** Every continuous lattice is an injective
space under its Scott topology. This is the substantial half of the equivalence "injective
spaces = continuous lattices", and is exactly Proposition 2.11. -/
theorem theorem_2_12_forward {E : Type*} [CompleteLattice E] (hE : IsContinuousLattice E) :
    @IsInjectiveSpace E scottTopologicalSpace :=
  proposition_2_11 hE

/-- **Scott 1972, Theorem 2.12 (backward, Sierpiński base case).** `Prop` is a continuous
lattice (`isContinuousLattice_prop`), so its injectivity (Proposition 1.2) is an instance of the
equivalence. -/
theorem theorem_2_12_sierpinski_backward (_h : IsContinuousLattice Prop) : IsInjectiveSpace Prop :=
  proposition_1_2

/-- **Scott 1972, Theorem 2.12 (injectivity half, unconditional).** `Prop` is injective
(Sierpiński); the continuous-lattice half is now `isContinuousLattice_prop`. -/
theorem theorem_2_12_injective_half : IsInjectiveSpace Prop :=
  proposition_1_2

/-- The Sierpiński space `𝕆 = Prop` realizes the smallest case of Theorem 2.12: it is both
injective (1.2) and a continuous lattice (2.8). -/
theorem sierpinski_isInjective_and_isContinuousLattice :
    IsInjectiveSpace Prop ∧ IsContinuousLattice Prop :=
  ⟨proposition_1_2, isContinuousLattice_prop⟩

end Scott1972.ContinuousLattice
