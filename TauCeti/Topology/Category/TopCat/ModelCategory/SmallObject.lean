/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.WeakEquivalence
public import TauCeti.Topology.Homotopy.SerreFibration.Basic

import Mathlib.CategoryTheory.Limits.Types.Filtered
import TauCeti.Topology.Category.TopCat.Limits.Homotopy
import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Closed `T₁`-inclusions, strong deformation retracts, and smallness in `TopCat`

This file develops the point-set and smallness infrastructure for the cofibrantly generated
Quillen–Serre model structure on `TopCat`:

* A *closed `T₁`-inclusion* (`TauCeti.TopCat.isClosedT1Inclusion`) is a closed embedding
  `f : X ⟶ Y` such that every singleton `{y}` outside the range of `f` is closed in `Y`
  (Hovey, *Model Categories*, Definition 2.4.1). This class contains every closed embedding into
  a `T₁` space and is stable under composition, cobase change, coproducts, countable transfinite
  composition, and retracts.
* Along any sequential colimit of closed `T₁`-inclusions in `TopCat` — with no separation
  hypothesis on the initial space — every compact subset of the colimit lies in a single stage
  (`TauCeti.TopCat.exists_subset_range_ι_of_isCompact_of_isClosedT1Inclusion`), so every continuous
  map from a compact space factors uniquely through a single stage
  (`TauCeti.TopCat.exists_lift_of_compactSpace_of_isClosedT1Inclusion`). Consequently `Hom(A, -)`
  preserves such sequential colimits whenever `A` is compact, and every small family of closed
  `T₁`-inclusions with compact domains admits the small object argument at `ℵ₀`
  (`TauCeti.TopCat.isCardinalForSmallObjectArgument_aleph0_of_isClosedT1Inclusion`).
* The same compact-support factorization shows that a countable transfinite composition of closed
  `T₁`-inclusions that are weak homotopy equivalences is again a weak homotopy equivalence
  (`TauCeti.TopCat.transfiniteCompositionsOfShape_nat_le_weakEquivalences`).
* A *strong deformation retract* (`TauCeti.TopCat.strongDeformationRetracts`) is a morphism
  `i : A ⟶ B` admitting a retraction `r : B ⟶ A` with `i ≫ r = 𝟙 A` and a homotopy relative to
  the range of `i` from `id` to `i ∘ r`. This class is stable under coproducts and cobase change,
  consists of weak homotopy equivalences, and contains every cylinder bottom inclusion
  `ι₀ : X ⟶ X ⊗ I`.

Applied to the generating cofibrations `I` (disk boundary inclusions `∂𝔻 n ⟶ 𝔻 n`) and the
generating trivial cofibrations `J` (cylinder bottom inclusions `𝔻 n ⟶ 𝔻 n ⊗ I`), these results
establish `HasSmallObjectArgument` for both `I` and `J` and prove `J.rlp.llp ≤ weakEquivalences`.

## References

* M. Hovey, *Model Categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.4.
* D. Quillen, *Homotopical Algebra*, Lecture Notes in Mathematics 43, Springer, 1967, Chapter II,
  Section 3.
-/

public section

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra MonoidalCategory
  CartesianMonoidalCategory Topology Set
open scoped Topology.Homotopy

universe w u

namespace TauCeti.TopCat

/-! ### Closed `T₁`-inclusions -/

/-- A **closed `T₁`-inclusion** in `TopCat`: a closed embedding `f : X ⟶ Y` such that every point
of `Y` outside the range of `f` has a closed singleton. -/
def isClosedT1Inclusion : MorphismProperty TopCat.{u} :=
  fun _ _ f ↦ IsClosedEmbedding f ∧ ∀ y ∉ range f, IsClosed ({y} : Set _)

/-- Characterization of membership in `TauCeti.TopCat.isClosedT1Inclusion`. -/
@[simp]
theorem isClosedT1Inclusion_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    isClosedT1Inclusion f ↔ IsClosedEmbedding f ∧ ∀ y ∉ range f, IsClosed ({y} : Set Y) :=
  Iff.rfl

/-- Every closed embedding into a `T₁` space is a closed `T₁`-inclusion. -/
theorem isClosedT1Inclusion_of_t1Space {X Y : TopCat.{u}} [T1Space Y] {f : X ⟶ Y}
    (hf : IsClosedEmbedding f) : isClosedT1Inclusion f :=
  ⟨hf, fun _ _ ↦ isClosed_singleton⟩

/-- A closed `T₁`-inclusion is in particular a closed embedding. -/
theorem isClosedT1Inclusion_le_isClosedEmbedding :
    isClosedT1Inclusion.{u} ≤ isClosedEmbedding.{u} :=
  fun _ _ _ hf ↦ (isClosedEmbedding_iff _).2 hf.1

instance : isClosedT1Inclusion.{u}.IsMultiplicative where
  id_mem _ := ⟨IsClosedEmbedding.id, fun y hy ↦ (hy ⟨y, rfl⟩).elim⟩
  comp_mem {X Y Z} f g hf hg := by
    refine ⟨hg.1.comp hf.1, fun z hz ↦ ?_⟩
    by_cases hzg : z ∈ range g
    · obtain ⟨y, rfl⟩ := hzg
      have hy : y ∉ range f := fun ⟨x, hx⟩ ↦ hz ⟨x, by simp [hx]⟩
      simpa only [image_singleton] using hg.1.isClosedMap {y} (hf.2 y hy)
    · exact hg.2 z hzg

instance : isClosedT1Inclusion.{u}.RespectsIso :=
  respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦
    ⟨(TopCat.homeoOfIso (asIso f)).isClosedEmbedding, fun y hy ↦
      (hy ⟨(TopCat.homeoOfIso (asIso f)).symm y,
        (TopCat.homeoOfIso (asIso f)).apply_symm_apply y⟩).elim⟩

/-- In `TopCat`, the cobase change of a closed `T₁`-inclusion is a closed `T₁`-inclusion. -/
theorem isClosedT1Inclusion_of_isPushout {A A' B B' : TopCat.{u}} {f : A ⟶ A'} {g : A ⟶ B}
    {f' : B ⟶ B'} {g' : A' ⟶ B'} (sq : IsPushout g f f' g') (hf : isClosedT1Inclusion f) :
    isClosedT1Inclusion f' := by
  refine ⟨isClosedEmbedding_of_isPushout sq hf.1, fun y hy ↦ ?_⟩
  rw [isClosed_iff_of_isPushout sq]
  refine ⟨?_, ?_⟩
  · have hpre : f' ⁻¹' {y} = ∅ := by
      ext b
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact fun hb ↦ hy ⟨b, hb⟩
    rw [hpre]
    exact isClosed_empty
  · have sq_type := (forget TopCat).map_isPushout sq
    obtain ⟨b, rfl⟩ | ⟨a', rfl, ha'⟩ := Types.eq_or_eq_of_isPushout' sq_type y
    · exact (hy ⟨b, rfl⟩).elim
    · have sq' := (forget TopCat).map_isPushout sq.flip
      have : Mono ((forget TopCat).map f) := (mono_iff_injective _).2 hf.1.injective
      let e := IsColimit.coconePointUniqueUpToIso sq'.isColimit
        (Types.Pushout.isColimitCocone ((forget TopCat).map f) ((forget TopCat).map g))
      have he (x : A') : e.hom (g' x) =
          Types.Pushout.inl ((forget TopCat).map f) ((forget TopCat).map g) x :=
        ConcreteCategory.congr_hom
          (IsColimit.comp_coconePointUniqueUpToIso_hom sq'.isColimit
            (Types.Pushout.isColimitCocone ((forget TopCat).map f) ((forget TopCat).map g))
            WalkingSpan.left) x
      have hpre : g' ⁻¹' {g' a'} = {a'} := by
        ext x
        simp only [mem_preimage, mem_singleton_iff]
        refine ⟨fun hx ↦ ?_, fun hx ↦ hx ▸ rfl⟩
        have hq : Types.Pushout.inl ((forget TopCat).map f) ((forget TopCat).map g) x =
            Types.Pushout.inl ((forget TopCat).map f) ((forget TopCat).map g) a' := by
          rw [← he, ← he, hx]
        have hrel := (Types.Pushout.quot_mk_eq_iff _ _ _ _).1 hq
        rw [Types.Pushout.inl_rel'_inl_iff] at hrel
        exact hrel.resolve_right fun ⟨_, y₀, _, _, ha'eq⟩ ↦ ha' ⟨y₀, ha'eq.symm⟩
      change IsClosed (g' ⁻¹' {g' a'})
      rw [hpre]
      exact hf.2 a' ha'

instance : isClosedT1Inclusion.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hf := isClosedT1Inclusion_of_isPushout sq hf

/-- In `TopCat`, a coproduct of closed `T₁`-inclusions is a closed `T₁`-inclusion. -/
theorem isClosedT1Inclusion_sigmaMap {ι : Type w} {X₁ X₂ : ι → TopCat.{u}} [HasCoproduct X₁]
    [HasCoproduct X₂] (f : ∀ i, X₁ i ⟶ X₂ i) (hf : ∀ i, isClosedT1Inclusion (f i)) :
    isClosedT1Inclusion (Limits.Sigma.map f) := by
  refine ⟨isClosedEmbedding_sigmaMap f fun i ↦ (hf i).1, fun y hy ↦ ?_⟩
  have h₂ := isColimitOfHasCoproductOfPreservesColimit (forget TopCat) X₂
  obtain ⟨i, x, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit h₂ y
  have hx : x ∉ range (f i) := by
    rintro ⟨a, rfl⟩
    refine hy ⟨Sigma.ι X₁ i a, ?_⟩
    rw [← ConcreteCategory.comp_apply, Sigma.ι_map, ConcreteCategory.comp_apply]
    rfl
  rw [TopCat.isClosed_iff_of_isColimit _ (coproductIsCoproduct X₂)]
  rintro ⟨j⟩
  by_cases hji : j = i
  · subst hji
    have hpre : Sigma.ι X₂ j ⁻¹' {Sigma.ι X₂ j x} = {x} := by
      ext z
      simp only [mem_preimage, mem_singleton_iff]
      refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
      obtain ⟨_, hz⟩ := (Cofan.inj_apply_eq_iff_of_isColimit h₂ _ _).1 h
      exact hz.symm
    simpa [hpre] using (hf j).2 x hx
  · have hpre : Sigma.ι X₂ j ⁻¹' {Sigma.ι X₂ i x} = ∅ := by
      ext z
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨rfl, _⟩ := (Cofan.inj_apply_eq_iff_of_isColimit h₂ _ _).1 h
      exact hji rfl
    simp [hpre]

instance (J : Type w) : isClosedT1Inclusion.{u}.IsStableUnderCoproductsOfShape J :=
  IsStableUnderCoproductsOfShape.mk _ J fun _ _ _ _ f hf ↦ isClosedT1Inclusion_sigmaMap f hf

instance : IsStableUnderCoproducts.{w} isClosedT1Inclusion.{u} where

/-- A retract of a closed `T₁`-inclusion in `TopCat` is a closed `T₁`-inclusion. -/
theorem isClosedT1Inclusion_of_retract {X Y Z W : TopCat.{u}} {f : X ⟶ Y} {g : Z ⟶ W}
    (h : RetractArrow f g) (hg : isClosedT1Inclusion g) : isClosedT1Inclusion f := by
  have hrl (x : X) : h.r.left (h.i.left x) = x := ConcreteCategory.congr_hom h.retract_left x
  have hrr (y : Y) : h.r.right (h.i.right y) = y := ConcreteCategory.congr_hom h.retract_right y
  have hiw (x : X) : g (h.i.left x) = h.i.right (f x) := ConcreteCategory.congr_hom h.i_w x
  have hrw (z : Z) : f (h.r.left z) = h.r.right (g z) := ConcreteCategory.congr_hom h.r_w z
  have hinj : Function.Injective f := fun x₁ x₂ hx ↦ by
    rw [← hrl x₁, ← hrl x₂]
    congr 1
    exact hg.1.injective (by rw [hiw, hiw, hx])
  refine ⟨.of_continuous_injective_isClosedMap f.hom.continuous hinj fun S hS ↦ ?_, fun y hy ↦ ?_⟩
  · have hEq : f '' S = h.i.right ⁻¹' (g '' (h.r.left ⁻¹' S)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨h.i.left x, by rwa [mem_preimage, hrl], hiw x⟩
      · rintro ⟨z, hz, hzy⟩
        exact ⟨h.r.left z, hz, by rw [hrw, hzy, hrr]⟩
    rw [hEq]
    exact (hg.1.isClosedMap _ (hS.preimage h.r.left.hom.continuous)).preimage
      h.i.right.hom.continuous
  · have hiy : h.i.right y ∉ range g := fun ⟨z, hz⟩ ↦
      hy ⟨h.r.left z, by rw [hrw, hz, hrr]⟩
    have hEq : ({y} : Set Y) = h.i.right ⁻¹' {h.i.right y} := by
      ext y'
      simp only [mem_singleton_iff, mem_preimage]
      exact ⟨fun h' ↦ h' ▸ rfl, fun h' ↦ by rw [← hrr y', ← hrr y, h']⟩
    rw [hEq]
    exact (hg.2 _ hiy).preimage h.i.right.hom.continuous

instance : isClosedT1Inclusion.{u}.IsStableUnderRetracts where
  of_retract h hg := isClosedT1Inclusion_of_retract h hg

/-! ### Compact subsets of sequential colimits of closed `T₁`-inclusions -/

section Sequential

variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F}

/-- In a sequential colimit of closed `T₁`-inclusions in `TopCat`, a subset disjoint from stage `0`
that meets every stage in finitely many points is closed. No separation hypothesis on `F.obj 0` is
needed. -/
theorem isClosed_of_preimage_zero_empty_of_forall_finite
    (hF : ∀ n : ℕ, isClosedT1Inclusion (F.map (homOfLE n.le_succ))) (hc : IsColimit c)
    {S : Set c.pt} (hS0 : c.ι.app 0 ⁻¹' S = ∅) (hS : ∀ n, (c.ι.app n ⁻¹' S).Finite) :
    IsClosed S := by
  refine (TopCat.isClosed_iff_of_isColimit _ hc S).2 fun n ↦ ?_
  induction n with
  | zero =>
    rw [hS0]
    exact isClosed_empty
  | succ n ih =>
    have hw : F.map (homOfLE n.le_succ) ≫ c.ι.app (n + 1) = c.ι.app n := c.w (homOfLE n.le_succ)
    have hsplit : c.ι.app (n + 1) ⁻¹' S =
        (F.map (homOfLE n.le_succ) '' (c.ι.app n ⁻¹' S)) ∪
          ((c.ι.app (n + 1) ⁻¹' S) \ range (F.map (homOfLE n.le_succ))) := by
      ext y
      constructor
      · intro hy
        by_cases hyu : y ∈ range (F.map (homOfLE n.le_succ))
        · obtain ⟨x, rfl⟩ := hyu
          refine Or.inl ⟨x, ?_, rfl⟩
          simpa only [mem_preimage, ← ConcreteCategory.comp_apply, hw] using hy
        · exact Or.inr ⟨hy, hyu⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨hy, -⟩)
        · simpa only [mem_preimage, ← ConcreteCategory.comp_apply, hw] using hx
        · exact hy
    rw [hsplit]
    refine ((hF n).1.isClosedMap _ ih).union ?_
    have hfin : ((c.ι.app (n + 1) ⁻¹' S) \ range (F.map (homOfLE n.le_succ))).Finite :=
      (hS (n + 1)).sdiff
    rw [← biUnion_of_singleton ((c.ι.app (n + 1) ⁻¹' S) \ range (F.map (homOfLE n.le_succ)))]
    exact hfin.isClosed_biUnion fun y hy ↦ (hF n).2 y hy.2

/-- In a sequential colimit of closed `T₁`-inclusions in `TopCat`, the canonical map from stage `0`
to the colimit is a closed `T₁`-inclusion. -/
theorem isClosedT1Inclusion_ι_zero_of_isColimit
    (hF : ∀ n : ℕ, isClosedT1Inclusion (F.map (homOfLE n.le_succ))) (hc : IsColimit c) :
    isClosedT1Inclusion (c.ι.app 0) := by
  have hι_cl (n : ℕ) : IsClosedEmbedding (c.ι.app n) :=
    isClosedEmbedding_ι_of_isColimit_of_succ (fun k ↦ (hF k).1) hc n
  refine ⟨hι_cl 0, fun y hy ↦ isClosed_of_preimage_zero_empty_of_forall_finite hF hc ?_ fun n ↦ ?_⟩
  · ext x
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    exact fun hx ↦ hy ⟨x, hx⟩
  · exact (finite_singleton y).preimage (hι_cl n).injective.injOn

instance : isClosedT1Inclusion.{u}.IsStableUnderTransfiniteCompositionOfShape ℕ where
  le := by
    rintro X Y f ⟨h⟩
    rw [← h.fac, isClosedT1Inclusion.cancel_left_of_respectsIso]
    exact isClosedT1Inclusion_ι_zero_of_isColimit (fun n ↦ h.map_mem n (not_isMax n)) h.isColimit

/-- In a sequential colimit of closed `T₁`-inclusions in `TopCat`, a subset disjoint from stage `0`
that meets every stage in finitely many points is discrete. -/
theorem isDiscrete_of_preimage_zero_empty_of_forall_finite
    (hF : ∀ n : ℕ, isClosedT1Inclusion (F.map (homOfLE n.le_succ))) (hc : IsColimit c)
    {S : Set c.pt} (hS0 : c.ι.app 0 ⁻¹' S = ∅) (hS : ∀ n, (c.ι.app n ⁻¹' S).Finite) :
    IsDiscrete S :=
  isDiscrete_iff_forall_mem_exists_isClosed.2 fun t ht ↦
    ⟨t, isClosed_of_preimage_zero_empty_of_forall_finite hF hc
      (eq_empty_of_subset_empty (hS0 ▸ preimage_mono ht)) fun n ↦ (hS n).subset (preimage_mono ht),
      inter_eq_left.2 ht⟩

/-- In a sequential colimit of closed `T₁`-inclusions in `TopCat`, every compact subset lies in the
image of a single stage. No separation hypothesis on the stages is needed. -/
theorem exists_subset_range_ι_of_isCompact_of_isClosedT1Inclusion
    (hF : ∀ n : ℕ, isClosedT1Inclusion (F.map (homOfLE n.le_succ))) (hc : IsColimit c)
    {K : Set c.pt} (hK : IsCompact K) : ∃ n, K ⊆ range (c.ι.app n) := by
  have hι_cl (n : ℕ) : IsClosedEmbedding (c.ι.app n) :=
    isClosedEmbedding_ι_of_isColimit_of_succ (fun k ↦ (hF k).1) hc n
  by_contra! h
  have hmono {m n : ℕ} (hmn : m ≤ n) : range (c.ι.app m) ⊆ range (c.ι.app n) := by
    rw [← c.w (homOfLE hmn), TopCat.coe_comp]
    exact range_comp_subset_range _ _
  have hcover (p : c.pt) : ∃ n, p ∈ range (c.ι.app n) := by
    obtain ⟨n, y, rfl⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) p
    exact ⟨n, y, rfl⟩
  choose pt hptK hpt using fun n ↦ not_subset.1 (h n)
  choose next hnext using fun n ↦ hcover (pt n)
  have hlt (n : ℕ) : n < next n := by
    by_contra! hle
    exact hpt n (hmono hle (hnext n))
  let idx (k : ℕ) : ℕ := next^[k] 0
  have hidx_succ (k : ℕ) : idx (k + 1) = next (idx k) := Function.iterate_succ_apply' next k 0
  have hidx : StrictMono idx := strictMono_nat_of_lt_succ fun k ↦ hidx_succ k ▸ hlt (idx k)
  let x (k : ℕ) : c.pt := pt (idx k)
  have hx {k n : ℕ} (hk : x k ∈ range (c.ι.app n)) : idx k < n := by
    by_contra! hle
    exact hpt _ (hmono hle hk)
  have hle {j k : ℕ} (hjk : x j = x k) : k ≤ j :=
    Nat.lt_succ_iff.1 <| hidx.lt_iff_lt.1 <| hx <| hjk ▸ hidx_succ j ▸ hnext (idx j)
  have hinj : Function.Injective x := fun j k hjk ↦ le_antisymm (hle hjk.symm) (hle hjk)
  have h0 : c.ι.app 0 ⁻¹' range x = ∅ := by
    ext y
    simp only [mem_preimage, mem_range, mem_empty_iff_false, iff_false, not_exists]
    intro k hk
    exact absurd (hx ⟨y, hk.symm⟩) (Nat.not_lt_zero _)
  have hfin (n : ℕ) : (c.ι.app n ⁻¹' range x).Finite := by
    refine (((finite_Iio n).image x).preimage (hι_cl n).injective.injOn).subset ?_
    rintro y ⟨k, hk⟩
    exact ⟨k, (hidx.id_le k).trans_lt (hx ⟨y, hk.symm⟩), hk⟩
  have hcpt : IsCompact (range x) :=
    hK.of_isClosed_subset (isClosed_of_preimage_zero_empty_of_forall_finite hF hc h0 hfin)
      (range_subset_iff.2 fun k ↦ hptK _)
  exact infinite_range_of_injective hinj
    (hcpt.finite (isDiscrete_of_preimage_zero_empty_of_forall_finite hF hc h0 hfin))

/-- In a sequential colimit of closed `T₁`-inclusions in `TopCat`, every continuous map from a
compact space factors continuously through a single stage. -/
theorem exists_lift_of_compactSpace_of_isClosedT1Inclusion
    (hF : ∀ n : ℕ, isClosedT1Inclusion (F.map (homOfLE n.le_succ))) (hc : IsColimit c)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (g : C(X, c.pt)) :
    ∃ n, ∃ g' : C(X, F.obj n), (c.ι.app n).hom.comp g' = g := by
  have hι_cl (n : ℕ) : IsClosedEmbedding (c.ι.app n) :=
    isClosedEmbedding_ι_of_isColimit_of_succ (fun k ↦ (hF k).1) hc n
  obtain ⟨n, hn⟩ :=
    exists_subset_range_ι_of_isCompact_of_isClosedT1Inclusion hF hc (isCompact_range g.continuous)
  choose f hf using fun p ↦ hn ⟨p, rfl⟩
  have hfg : c.ι.app n ∘ f = g := funext hf
  exact ⟨n, ⟨f, (hι_cl n).isInducing.continuous_iff.2 (hfg ▸ g.continuous)⟩, ContinuousMap.ext hf⟩

/-- For any compact space `A`, the corepresentable functor `Hom(A, -)` preserves every sequential
colimit of closed `T₁`-inclusions in `TopCat`. -/
theorem preservesColimit_coyoneda_of_isClosedT1Inclusion
    (hF : ∀ n : ℕ, isClosedT1Inclusion (F.map (homOfLE n.le_succ)))
    (A : TopCat.{u}) [CompactSpace A] :
    PreservesColimit F (coyoneda.obj (Opposite.op A)) := by
  refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) ?_
  have hc := colimit.isColimit F
  have hι_cl (n : ℕ) : IsClosedEmbedding ((colimit.cocone F).ι.app n) :=
    isClosedEmbedding_ι_of_isColimit_of_succ (fun k ↦ (hF k).1) hc n
  refine Types.FilteredColimit.isColimitOf' _ _ (fun g ↦ ?_) (fun i g₁ g₂ h ↦ ?_)
  · obtain ⟨n, g', hg'⟩ := exists_lift_of_compactSpace_of_isClosedT1Inclusion hF hc g.hom
    exact ⟨n, TopCat.ofHom g', TopCat.ext fun x ↦ (ContinuousMap.congr_fun hg' x).symm⟩
  · refine ⟨i, 𝟙 i, TopCat.ext fun x ↦ (hι_cl i).injective ?_⟩
    simpa using ConcreteCategory.congr_hom h x

/-! ### Weak homotopy equivalences and sequential colimits -/

/-- In a sequential colimit of closed `T₁`-inclusions in `TopCat` whose transition maps are weak
homotopy equivalences, the canonical map from stage `0` to the colimit is a weak homotopy
equivalence. -/
theorem isWeakHomotopyEquivalence_ι_zero_of_isClosedT1Inclusion
    (hF : ∀ n : ℕ, isClosedT1Inclusion (F.map (homOfLE n.le_succ)))
    (hW : ∀ n : ℕ, (F.map (homOfLE n.le_succ)).hom.IsWeakHomotopyEquivalence)
    (hc : IsColimit c) : (c.ι.app 0).hom.IsWeakHomotopyEquivalence := by
  have hι_cl (n : ℕ) : IsClosedEmbedding (c.ι.app n) :=
    isClosedEmbedding_ι_of_isColimit_of_succ (fun k ↦ (hF k).1) hc n
  have hW0 (n : ℕ) : (F.map (homOfLE (Nat.zero_le n))).hom.IsWeakHomotopyEquivalence := by
    induction n with
    | zero =>
      have : F.map (homOfLE (Nat.zero_le 0)) = 𝟙 (F.obj 0) := F.map_id 0
      rw [this, TopCat.hom_id]
      exact ContinuousMap.IsWeakHomotopyEquivalence.id
    | succ n ih =>
      have hcomp : F.map (homOfLE (Nat.zero_le (n + 1))) =
          F.map (homOfLE (Nat.zero_le n)) ≫ F.map (homOfLE n.le_succ) := by
        rw [← F.map_comp]
        rfl
      rw [hcomp, TopCat.hom_comp]
      exact (hW n).comp ih
  refine ContinuousMap.isWeakHomotopyEquivalence_iff_joined.2 ⟨?_, ?_, fun k a ↦ ⟨?_, ?_⟩⟩
  · -- Surjectivity on path components.
    intro y
    obtain ⟨n, y', rfl⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) y
    obtain ⟨x, hx⟩ := (hW0 n).exists_joined y'
    refine ⟨x, ?_⟩
    have h0n : c.ι.app 0 x = c.ι.app n (F.map (homOfLE (Nat.zero_le n)) x) := by
      rw [← ConcreteCategory.comp_apply, c.w]
    rw [h0n]
    exact hx.map (c.ι.app n).hom.continuous
  · -- Injectivity on path components: a path in `c.pt` factors through some stage `n`.
    intro a b hab
    obtain ⟨n, γ', hγ'⟩ :=
      exists_lift_of_compactSpace_of_isClosedT1Inclusion hF hc hab.somePath.toContinuousMap
    have hγ0 : γ' 0 = F.map (homOfLE (Nat.zero_le n)) a := (hι_cl n).injective <| by
      have h0 := ContinuousMap.congr_fun hγ' 0
      dsimp at h0
      rw [h0, hab.somePath.source, ← ConcreteCategory.comp_apply, c.w]
    have hγ1 : γ' 1 = F.map (homOfLE (Nat.zero_le n)) b := (hι_cl n).injective <| by
      have h1 := ContinuousMap.congr_fun hγ' 1
      dsimp at h1
      rw [h1, hab.somePath.target, ← ConcreteCategory.comp_apply, c.w]
    exact (hW0 n).joined_iff.1 ⟨⟨γ', hγ0, hγ1⟩⟩
  · -- Injectivity on `π_{k+1}`: a homotopy of loops in `c.pt` factors through some stage `n`.
    intro u v huv
    induction u using Quotient.inductionOn with | h α => ?_
    induction v using Quotient.inductionOn with | h β => ?_
    obtain ⟨H⟩ := Quotient.exact huv
    obtain ⟨n, H', hH'⟩ :=
      exists_lift_of_compactSpace_of_isClosedT1Inclusion hF hc H.toContinuousMap
    have hι_eval (p : unitInterval × (Fin (k + 1) → unitInterval)) : c.ι.app n (H' p) = H p :=
      ContinuousMap.congr_fun hH' p
    let αn : Ω^ (Fin (k + 1)) (F.obj n) (F.map (homOfLE (Nat.zero_le n)) a) :=
      GenLoop.map (F.map (homOfLE (Nat.zero_le n))).hom rfl α
    let βn : Ω^ (Fin (k + 1)) (F.obj n) (F.map (homOfLE (Nat.zero_le n)) a) :=
      GenLoop.map (F.map (homOfLE (Nat.zero_le n))).hom rfl β
    have hαβ : GenLoop.Homotopic αn βn := by
      refine ⟨{
        toContinuousMap := H'
        map_zero_left := fun t ↦ (hι_cl n).injective <| by
          change c.ι.app n (H' (0, t)) = c.ι.app n (αn t)
          rw [hι_eval, H.apply_zero]
          change (GenLoop.map (c.ι.app 0).hom rfl α) t = c.ι.app n (αn t)
          rw [GenLoop.map_apply, GenLoop.map_apply]
          exact ConcreteCategory.congr_hom (c.w (homOfLE (Nat.zero_le n))).symm (α t)
        map_one_left := fun t ↦ (hι_cl n).injective <| by
          change c.ι.app n (H' (1, t)) = c.ι.app n (βn t)
          rw [hι_eval, H.apply_one]
          change (GenLoop.map (c.ι.app 0).hom rfl β) t = c.ι.app n (βn t)
          rw [GenLoop.map_apply, GenLoop.map_apply]
          exact ConcreteCategory.congr_hom (c.w (homOfLE (Nat.zero_le n))).symm (β t)
        prop' := fun s t ht ↦ (hι_cl n).injective <| by
          change c.ι.app n (H' (s, t)) = c.ι.app n (αn t)
          rw [hι_eval, H.eq_fst s ht]
          change (GenLoop.map (c.ι.app 0).hom rfl α) t = c.ι.app n (αn t)
          rw [GenLoop.map_apply, GenLoop.map_apply]
          exact ConcreteCategory.congr_hom (c.w (homOfLE (Nat.zero_le n))).symm (α t) }⟩
    exact ((hW0 n).bijective (k + 1) a).1 (Quotient.sound hαβ)
  · -- Surjectivity on `π_{k+1}`: a loop in `c.pt` factors through some stage `n`.
    intro u
    induction u using Quotient.inductionOn with | h γ => ?_
    obtain ⟨n, γ', hγ'⟩ :=
      exists_lift_of_compactSpace_of_isClosedT1Inclusion hF hc γ.val
    have hbase : c.ι.app n (F.map (homOfLE (Nat.zero_le n)) a) = c.ι.app 0 a := by
      rw [← ConcreteCategory.comp_apply, c.w]
    let γn : Ω^ (Fin (k + 1)) (F.obj n) (F.map (homOfLE (Nat.zero_le n)) a) :=
      ⟨γ', fun t ht ↦ (hι_cl n).injective <| by
        change ((c.ι.app n).hom.comp γ') t = _
        rw [ContinuousMap.congr_fun hγ' t, γ.2 t ht, hbase]⟩
    obtain ⟨v, hv⟩ := ((hW0 n).bijective (k + 1) a).2 ⟦γn⟧
    refine ⟨v, ?_⟩
    have hmap : HomotopyGroup.map (c.ι.app 0).hom rfl v =
        HomotopyGroup.map (c.ι.app n).hom hbase
          (HomotopyGroup.map (F.map (homOfLE (Nat.zero_le n))).hom rfl v) := by
      rw [HomotopyGroup.map_comp_apply]
      exact HomotopyGroup.map_congr (congrArg TopCat.Hom.hom (c.w (homOfLE (Nat.zero_le n))).symm)
        _ _ v
    rw [hmap, hv, HomotopyGroup.map_mk]
    exact congrArg Quotient.mk'' (Subtype.ext <| ContinuousMap.ext fun t ↦ by
      change (GenLoop.map (c.ι.app n).hom hbase γn) t = γ t
      rw [GenLoop.map_apply]
      exact ContinuousMap.congr_fun hγ' t)

/-- A countable transfinite composition of closed `T₁`-inclusions that are weak homotopy
equivalences is a weak homotopy equivalence. -/
theorem transfiniteCompositionsOfShape_nat_le_weakEquivalences :
    (isClosedT1Inclusion.{u} ⊓ weakEquivalences.{u}).transfiniteCompositionsOfShape ℕ ≤
      weakEquivalences.{u} := by
  rintro X Y f ⟨h⟩
  rw [mem_weakEquivalences_iff, ← h.fac, TopCat.hom_comp]
  have h0 := isWeakHomotopyEquivalence_ι_zero_of_isClosedT1Inclusion
    (fun n ↦ (h.map_mem n (not_isMax n)).1)
    (fun n ↦ (mem_weakEquivalences_iff _).1 (h.map_mem n (not_isMax n)).2) h.isColimit
  exact h0.comp (TopCat.homeoOfIso h.isoBot.symm).toHomotopyEquiv.isWeakHomotopyEquivalence

end Sequential

/-! ### The small object argument for closed `T₁`-inclusions with compact domains -/

section SmallObject

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

/-- Any small family `T` of closed `T₁`-inclusions with compact domains in `TopCat` satisfies
`IsCardinalForSmallObjectArgument T ℵ₀`. -/
theorem isCardinalForSmallObjectArgument_aleph0_of_isClosedT1Inclusion
    (T : MorphismProperty TopCat.{u}) [IsSmall.{u} T]
    (hT_compact : ∀ ⦃A B : TopCat.{u}⦄ (i : A ⟶ B), T i → CompactSpace A)
    (hT_cl : T ≤ isClosedT1Inclusion.{u}) :
    T.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : CompactSpace A := hT_compact i hi
    -- Reindex the `ℵ₀`-shaped cell complex along the order isomorphism `ℕ ≃o ℵ₀.ord.ToType`.
    let e : ℕ ≃o Cardinal.aleph0.{u}.ord.ToType :=
      ULift.orderIso.{u}.symm.trans
        (OrderIso.ofRelIsoLT (Nonempty.some (by simp [← Ordinal.type_eq])))
    have hcomp : ∀ n : ℕ, isClosedT1Inclusion
        ((e.equivalence.functor ⋙ hf.F).map (homOfLE n.le_succ)) := by
      intro n
      have h0 : e.equivalence.functor.obj n = e n := rfl
      have hsucc : e.equivalence.functor.obj (n + 1) = Order.succ (e n) := e.map_succ n
      have hnotmax : ¬ IsMax (e n) := fun h ↦
        absurd (e.le_iff_le.1 (h (e.monotone n.le_succ))) (Nat.not_succ_le_self n)
      have hmem : (coproducts.{u} T).pushouts (hf.F.map (homOfLE (Order.le_succ (e n)))) := by
        have h := (hf.attachCells (e n) hnotmax).pushouts_coproducts
        rwa [T.ofHoms_homFamily] at h
      have hcl : isClosedT1Inclusion (hf.F.map (homOfLE (Order.le_succ (e n)))) :=
        (pushouts_le_iff.2 (coproducts_le_iff.2 hT_cl)) _ hmem
      have heq : CategoryTheory.Arrow.mk ((e.equivalence.functor ⋙ hf.F).map (homOfLE n.le_succ)) ≅
          CategoryTheory.Arrow.mk (hf.F.map (homOfLE (Order.le_succ (e n)))) :=
        CategoryTheory.Arrow.isoMk (hf.F.mapIso (eqToIso h0)) (hf.F.mapIso (eqToIso hsucc)) (by
          dsimp
          rw [← hf.F.map_comp, ← hf.F.map_comp]
          rfl)
      exact (isClosedT1Inclusion.arrow_mk_iso_iff heq).2 hcl
    have : PreservesColimit (e.equivalence.functor ⋙ hf.F) (coyoneda.obj (Opposite.op A)) :=
      preservesColimit_coyoneda_of_isClosedT1Inclusion hcomp A
    exact Functor.Final.preservesColimit_of_comp e.equivalence.functor

/-- Any small family `T` of closed `T₁`-inclusions with compact domains in `TopCat` admits the
small object argument. -/
theorem hasSmallObjectArgument_of_isClosedT1Inclusion
    (T : MorphismProperty TopCat.{u}) [IsSmall.{u} T]
    (hT_compact : ∀ ⦃A B : TopCat.{u}⦄ (i : A ⟶ B), T i → CompactSpace A)
    (hT_cl : T ≤ isClosedT1Inclusion.{u}) :
    HasSmallObjectArgument.{u} T :=
  have := isCardinalForSmallObjectArgument_aleph0_of_isClosedT1Inclusion T hT_compact hT_cl
  ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

end SmallObject

/-! ### Strong deformation retracts -/

/-- The **strong deformation retracts** in `TopCat`: morphisms `i : A ⟶ B` admitting a retraction
`r : B ⟶ A` with `i ≫ r = 𝟙 A` and a homotopy relative to the range of `i` from `id B` to
`i ∘ r`. -/
def strongDeformationRetracts : MorphismProperty TopCat.{u} :=
  fun A B i ↦ ∃ r : B ⟶ A, i ≫ r = 𝟙 A ∧
    (ContinuousMap.id B).HomotopicRel (r ≫ i).hom (range i)

/-- Characterization of membership in `TauCeti.TopCat.strongDeformationRetracts`. -/
theorem strongDeformationRetracts_iff {A B : TopCat.{u}} (i : A ⟶ B) :
    strongDeformationRetracts i ↔ ∃ r : B ⟶ A, i ≫ r = 𝟙 A ∧
      (ContinuousMap.id B).HomotopicRel (r ≫ i).hom (range i) :=
  Iff.rfl

instance : strongDeformationRetracts.{u}.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ fun {f g} e ⟨r, hfr, ⟨H⟩⟩ ↦ by
    let eL := TopCat.homeoOfIso (Arrow.leftFunc.mapIso e)
    let eR := TopCat.homeoOfIso (Arrow.rightFunc.mapIso e)
    have hinvL : e.inv.left ≫ e.hom.left = 𝟙 g.left := congrArg CommaMorphism.left e.inv_hom_id
    have hcomp : g.hom ≫ e.inv.right ≫ r ≫ e.hom.left = 𝟙 g.left := by
      rw [← Category.assoc, ← e.inv.w, Category.assoc, ← Category.assoc f.hom, hfr,
        Category.id_comp, hinvL]
    refine ⟨e.inv.right ≫ r ≫ e.hom.left, hcomp, ⟨{
      toFun := fun p ↦ eR (H (p.1, eR.symm p.2))
      continuous_toFun := eR.continuous.comp
        (H.continuous.comp (continuous_fst.prodMk (eR.symm.continuous.comp continuous_snd)))
      map_zero_left := fun y ↦ by simp
      map_one_left := fun y ↦ by
        dsimp
        rw [H.apply_one]
        change eR ((r ≫ f.hom) (eR.symm y)) = ((e.inv.right ≫ r ≫ e.hom.left) ≫ g.hom) y
        rw [Category.assoc, Category.assoc, e.hom.w]
        rfl
      prop' := by
        rintro t _ ⟨a, rfl⟩
        have hfa : eR.symm (g.hom a) = f.hom (eL.symm a) := by
          apply eR.injective
          simp only [Homeomorph.apply_symm_apply]
          change g.hom a = (f.hom ≫ e.hom.right) (e.inv.left a)
          rw [← e.hom.w, ← ConcreteCategory.comp_apply, ← Category.assoc, hinvL, Category.id_comp]
        change eR (H (t, eR.symm (g.hom a))) = g.hom a
        rw [hfa, H.eq_fst t ⟨eL.symm a, rfl⟩, ContinuousMap.id_apply, ← hfa,
          eR.apply_symm_apply] }⟩⟩

/-- Every strong deformation retract is a weak homotopy equivalence. -/
theorem strongDeformationRetracts_le_weakEquivalences :
    strongDeformationRetracts.{u} ≤ weakEquivalences.{u} := by
  rintro A B i ⟨r, hir, hH⟩
  rw [mem_weakEquivalences_iff]
  have hri : Function.LeftInverse r.hom i.hom := fun a ↦ ConcreteCategory.congr_hom hir a
  have hH' : (i.hom.comp r.hom).Homotopic (ContinuousMap.id B) :=
    TopCat.hom_comp r i ▸ hH.homotopic.symm
  have heq := (ContinuousMap.HomotopyEquiv.ofDeformationRetraction i.hom r.hom
    hri hH').isWeakHomotopyEquivalence
  rwa [ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun] at heq

/-- The cylinder bottom inclusion `ι₀ : X ⟶ X ⊗ I` is a strong deformation retract. -/
theorem strongDeformationRetracts_ι₀ (X : TopCat.{u}) :
    strongDeformationRetracts (TopCat.ι₀ : X ⟶ X ⊗ TopCat.I) := by
  refine ⟨fst X TopCat.I, TopCat.ι₀_fst X, ⟨{
    toFun := fun p ↦ (p.2.1, TopCat.I.homeomorph.symm
      (unitInterval.symm p.1 * TopCat.I.homeomorph p.2.2))
    continuous_toFun := by
      refine Continuous.prodMk (continuous_fst.comp continuous_snd)
        (TopCat.I.homeomorph.symm.continuous.comp ?_)
      have h1 : Continuous fun p : unitInterval × ↑(X ⊗ TopCat.I) ↦ unitInterval.symm p.1 :=
        unitInterval.continuous_symm.comp continuous_fst
      have h2 : Continuous fun p : unitInterval × ↑(X ⊗ TopCat.I) ↦
          TopCat.I.homeomorph p.2.2 :=
        TopCat.I.homeomorph.continuous.comp (continuous_snd.comp continuous_snd)
      exact h1.mul h2
    map_zero_left := fun x ↦ by
      change (x.1, TopCat.I.homeomorph.symm (unitInterval.symm 0 * TopCat.I.homeomorph x.2)) = x
      exact Prod.ext rfl (by simp)
    map_one_left := fun x ↦ by
      change (x.1, TopCat.I.homeomorph.symm (unitInterval.symm 1 * TopCat.I.homeomorph x.2)) =
        (x.1, TopCat.I.homeomorph.symm 0)
      simp
    prop' := by
      rintro s _ ⟨x, rfl⟩
      change (x, TopCat.I.homeomorph.symm
        (unitInterval.symm s * TopCat.I.homeomorph (0 : TopCat.I.{u}))) =
        (x, TopCat.I.homeomorph.symm 0)
      simp }⟩⟩

/-- A coproduct of strong deformation retracts in `TopCat` is a strong deformation retract. -/
theorem strongDeformationRetracts_sigmaMap {ι : Type w} {X₁ X₂ : ι → TopCat.{u}}
    [HasCoproduct X₁] [HasCoproduct X₂] (f : ∀ i, X₁ i ⟶ X₂ i)
    (hf : ∀ i, strongDeformationRetracts (f i)) :
    strongDeformationRetracts (Limits.Sigma.map f) := by
  choose r hr hH using hf
  let H i := (hH i).some
  let R : ∐ X₂ ⟶ ∐ X₁ := Limits.Sigma.map r
  have hcomp : Limits.Sigma.map f ≫ R = 𝟙 (∐ X₁) := by
    apply Limits.Sigma.hom_ext
    intro i
    rw [Sigma.ι_map_assoc, Sigma.ι_map, ← Category.assoc, hr i, Category.id_comp, Category.comp_id]
  have hmap (i : ι) (x : X₂ i) :
      (R ≫ Limits.Sigma.map f) (Sigma.ι X₂ i x) = Sigma.ι X₂ i ((r i ≫ f i) x) := by
    dsimp only [R]
    rw [← ConcreteCategory.comp_apply, Sigma.ι_map_assoc, Sigma.ι_map]
    rfl
  let c := coproductIsCoproduct X₂
  let stage : ∀ j : Discrete ι,
      ((ContinuousMap.id ↑(∐ X₂)).comp ((Cofan.mk (∐ X₂) (Sigma.ι X₂)).ι.app j).hom).Homotopy
        ((R ≫ Limits.Sigma.map f).hom.comp ((Cofan.mk (∐ X₂) (Sigma.ι X₂)).ι.app j).hom)
    | ⟨i⟩ => ((ContinuousMap.Homotopy.refl (Sigma.ι X₂ i).hom).comp (H i).toHomotopy).cast
        (by ext x; rfl) (by ext x; exact (hmap i x).symm)
  have hstage : ∀ ⦃j₁ j₂ : Discrete ι⦄ (u : j₁ ⟶ j₂) (t : unitInterval)
      (x : (Discrete.functor X₂).obj j₁),
      stage j₂ (t, (Discrete.functor X₂).map u x) = stage j₁ (t, x) := by
    rintro ⟨i⟩ ⟨j⟩ u t x
    obtain rfl : i = j := Discrete.eq_of_hom u
    have hu : u = 𝟙 (Discrete.mk i) := Subsingleton.elim _ _
    subst hu
    simp
  let Hglue : (ContinuousMap.id ↑(∐ X₂)).Homotopy (R ≫ Limits.Sigma.map f).hom :=
    c.homotopyDesc stage hstage
  refine ⟨R, hcomp, ⟨{ Hglue with
    prop' := by
      rintro t _ ⟨y, rfl⟩
      obtain ⟨i, a, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit
        (isColimitOfHasCoproductOfPreservesColimit (forget TopCat) X₁) y
      have hfi : Limits.Sigma.map f (Sigma.ι X₁ i a) = Sigma.ι X₂ i (f i a) := by
        rw [← ConcreteCategory.comp_apply, Sigma.ι_map, ConcreteCategory.comp_apply]
      change Hglue (t, Limits.Sigma.map f (Sigma.ι X₁ i a)) =
        Limits.Sigma.map f (Sigma.ι X₁ i a)
      rw [hfi]
      have hev := c.homotopyDesc_apply_ι stage hstage ⟨i⟩ t (f i a)
      refine hev.trans ?_
      change Sigma.ι X₂ i (H i (t, f i a)) = Sigma.ι X₂ i (f i a)
      rw [(H i).eq_fst t ⟨a, rfl⟩, ContinuousMap.id_apply] }⟩⟩

instance (J : Type w) : strongDeformationRetracts.{u}.IsStableUnderCoproductsOfShape J :=
  IsStableUnderCoproductsOfShape.mk _ J fun _ _ _ _ f hf ↦ strongDeformationRetracts_sigmaMap f hf

instance : IsStableUnderCoproducts.{w} strongDeformationRetracts.{u} where

/-- In `TopCat`, the cobase change of a strong deformation retract is a strong deformation
retract. -/
theorem strongDeformationRetracts_of_isPushout {A A' B B' : TopCat.{u}} {f : A ⟶ A'} {g : A ⟶ B}
    {f' : B ⟶ B'} {g' : A' ⟶ B'} (sq : IsPushout g f f' g') (hf : strongDeformationRetracts f) :
    strongDeformationRetracts f' := by
  obtain ⟨r, hfr, ⟨H⟩⟩ := hf
  let R : B' ⟶ B := sq.desc (𝟙 B) (r ≫ g) (by rw [← Category.assoc, hfr, Category.id_comp,
    Category.comp_id])
  have hfR : f' ≫ R = 𝟙 B := sq.inl_desc _ _ _
  have hgR : g' ≫ R = r ≫ g := sq.inr_desc _ _ _
  have hRf' (b : B) : (R ≫ f') (f' b) = f' b := by
    rw [← ConcreteCategory.comp_apply, ← Category.assoc, hfR, Category.id_comp]
  have hRg' (a' : A') : (R ≫ f') (g' a') = g' ((r ≫ f) a') := by
    rw [← ConcreteCategory.comp_apply, ← Category.assoc, hgR, Category.assoc, sq.w,
      ← Category.assoc]
    rfl
  let c := sq.isColimit
  let stage : ∀ j : WalkingSpan,
      ((ContinuousMap.id B').comp (sq.cocone.ι.app j).hom).Homotopy
        ((R ≫ f').hom.comp (sq.cocone.ι.app j).hom)
    | .zero => (ContinuousMap.Homotopy.refl (g ≫ f').hom).cast
        (by ext a; rfl) (by ext a; exact (hRf' (g a)).symm)
    | .left => (ContinuousMap.Homotopy.refl f'.hom).cast
        (by ext b; rfl) (by ext b; exact (hRf' b).symm)
    | .right => ((ContinuousMap.Homotopy.refl g'.hom).comp H.toHomotopy).cast
        (by ext a'; rfl) (by ext a'; exact (hRg' a').symm)
  have hstage : ∀ ⦃i j : WalkingSpan⦄ (u : i ⟶ j) (t : unitInterval) (x : (span g f).obj i),
      stage j (t, (span g f).map u x) = stage i (t, x) := by
    intro i j u t x
    cases u with
    | id _ => rfl
    | init b =>
      cases b with
      | left => rfl
      | right =>
        change g' (H (t, f x)) = f' (g x)
        rw [H.eq_fst t ⟨x, rfl⟩]
        exact ConcreteCategory.congr_hom sq.w.symm x
  let Hglue : (ContinuousMap.id B').Homotopy (R ≫ f').hom := c.homotopyDesc stage hstage
  refine ⟨R, hfR, ⟨{ Hglue with
    prop' := by
      rintro t _ ⟨b, rfl⟩
      exact c.homotopyDesc_apply_ι stage hstage .left t b }⟩⟩

instance : strongDeformationRetracts.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hf := strongDeformationRetracts_of_isPushout sq hf

/-! ### Generating cofibrations and generating trivial cofibrations of `TopCat` -/

namespace modelCategoryQuillen

/-- The generating cofibrations of the Quillen–Serre model structure on `TopCat`: the disk boundary
inclusions `∂𝔻 n ⟶ 𝔻 n` for `n : ℕ`. -/
def I : MorphismProperty TopCat.{u} :=
  ofHoms TopCat.diskBoundaryInclusion.{u}

/-- The generating trivial cofibrations of the Quillen–Serre model structure on `TopCat`: the
cylinder bottom inclusions `ι₀ : 𝔻 n ⟶ 𝔻 n ⊗ I` for `n : ℕ`. -/
def J : MorphismProperty TopCat.{u} :=
  ofHoms fun n : ℕ ↦ (TopCat.ι₀ : TopCat.disk.{u} n ⟶ TopCat.disk n ⊗ TopCat.I)

/-- `I` is the morphism property generated by `TopCat.diskBoundaryInclusion`. -/
lemma I_eq_ofHoms : I.{u} = ofHoms TopCat.diskBoundaryInclusion.{u} := by rfl

/-- `J` is the morphism property generated by the cylinder bottom inclusions `𝔻 n ⟶ 𝔻 n ⊗ I`. -/
lemma J_eq_ofHoms :
    J.{u} = ofHoms fun n : ℕ ↦ (TopCat.ι₀ : TopCat.disk.{u} n ⟶ TopCat.disk n ⊗ TopCat.I) := by
  rfl

/-- Every disk boundary inclusion `∂𝔻 n ⟶ 𝔻 n` belongs to `I`. -/
lemma diskBoundaryInclusion_mem_I (n : ℕ) : I (TopCat.diskBoundaryInclusion.{u} n) :=
  ofHoms.mk n

/-- Every cylinder bottom inclusion `ι₀ : 𝔻 n ⟶ 𝔻 n ⊗ I` belongs to `J`. -/
lemma ι₀_disk_mem_J (n : ℕ) :
    J (TopCat.ι₀ : TopCat.disk.{u} n ⟶ TopCat.disk n ⊗ TopCat.I) :=
  ofHoms.mk n

/-- A morphism belongs to `I.rlp` if and only if it has the right lifting property with respect to
every disk boundary inclusion `∂𝔻 n ⟶ 𝔻 n`. -/
lemma mem_rlp_I_iff {E B : TopCat.{u}} {p : E ⟶ B} :
    I.{u}.rlp p ↔ ∀ n : ℕ, HasLiftingProperty (TopCat.diskBoundaryInclusion.{u} n) p :=
  ⟨fun h n ↦ h _ (diskBoundaryInclusion_mem_I n), by rintro h _ _ _ ⟨n⟩; exact h n⟩

/-- The right lifting class of `J` is `TauCeti.TopCat.serreFibrations`. -/
lemma rlp_J : J.{u}.rlp = serreFibrations.{u} := by
  ext X Y p
  rw [mem_serreFibrations_iff_hasLiftingProperty]
  exact ⟨fun h n ↦ h _ (ι₀_disk_mem_J n), by rintro h _ _ _ ⟨n⟩; exact h n⟩

/-- Every generating cofibration in `I` is a closed `T₁`-inclusion. -/
lemma I_le_isClosedT1Inclusion : I.{u} ≤ isClosedT1Inclusion.{u} := by
  rintro _ _ _ ⟨n⟩
  exact isClosedT1Inclusion_of_t1Space (isClosedEmbedding_diskBoundaryInclusion n)

/-- Every generating trivial cofibration in `J` is a closed `T₁`-inclusion. -/
lemma J_le_isClosedT1Inclusion : J.{u} ≤ isClosedT1Inclusion.{u} := by
  rintro _ _ _ ⟨n⟩
  have : T2Space (TopCat.disk.{u} n ⊗ TopCat.I : TopCat.{u}) :=
    inferInstanceAs (T2Space (TopCat.disk.{u} n × ULift unitInterval))
  have hinj : Function.Injective (TopCat.ι₀ : TopCat.disk.{u} n ⟶ TopCat.disk n ⊗ TopCat.I) :=
    fun x y h ↦ congrArg Prod.fst h
  exact isClosedT1Inclusion_of_t1Space
    ((TopCat.ι₀ : TopCat.disk.{u} n ⟶ TopCat.disk n ⊗ TopCat.I).hom.continuous.isClosedEmbedding
      hinj)

/-- Every generating trivial cofibration in `J` is a strong deformation retract. -/
lemma J_le_strongDeformationRetracts : J.{u} ≤ strongDeformationRetracts.{u} := by
  rintro _ _ _ ⟨n⟩
  exact strongDeformationRetracts_ι₀ (TopCat.disk.{u} n)

instance isSmall_I : MorphismProperty.IsSmall.{u} I.{u} := isSmall_ofHoms ..

instance isSmall_J : MorphismProperty.IsSmall.{u} J.{u} := isSmall_ofHoms ..

section SmallObjectInstances

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

/-- The disk boundary inclusions satisfy `IsCardinalForSmallObjectArgument` at `ℵ₀`. -/
instance isCardinalForSmallObjectArgument_I :
    I.{u}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} :=
  isCardinalForSmallObjectArgument_aleph0_of_isClosedT1Inclusion I.{u}
    (by rintro _ _ _ ⟨n⟩; infer_instance) I_le_isClosedT1Inclusion

/-- The disk boundary inclusions admit the small object argument. -/
instance hasSmallObjectArgument_I : HasSmallObjectArgument.{u} I.{u} :=
  ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

/-- The cylinder bottom inclusions of disks satisfy `IsCardinalForSmallObjectArgument` at `ℵ₀`. -/
instance isCardinalForSmallObjectArgument_J :
    J.{u}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} :=
  isCardinalForSmallObjectArgument_aleph0_of_isClosedT1Inclusion J.{u}
    (by rintro _ _ _ ⟨n⟩; infer_instance) J_le_isClosedT1Inclusion

/-- The cylinder bottom inclusions of disks admit the small object argument. -/
instance hasSmallObjectArgument_J : HasSmallObjectArgument.{u} J.{u} :=
  ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

/-- Every morphism in `J.rlp.llp` (that is, every retract of a relative `J`-cell complex) is a
weak homotopy equivalence. -/
theorem llp_rlp_J_le_weakEquivalences : J.{u}.rlp.llp ≤ weakEquivalences.{u} := by
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0 J.{u}, retracts_le_iff]
  refine le_trans (transfiniteCompositionsOfShape_monotone ℕ ?_)
    transfiniteCompositionsOfShape_nat_le_weakEquivalences
  refine le_inf ?_ ?_
  · exact pushouts_le_iff.2 (coproducts_le_iff.2 J_le_isClosedT1Inclusion)
  · exact le_trans (pushouts_le_iff.2 (coproducts_le_iff.2 J_le_strongDeformationRetracts))
      strongDeformationRetracts_le_weakEquivalences

end SmallObjectInstances

end modelCategoryQuillen

end TauCeti.TopCat
