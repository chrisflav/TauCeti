/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.Category
public import TauCeti.CategoryTheory.Dagger.Karoubi

/-!
# Orthogonal biproducts and dagger idempotent completeness for Hilbert spaces

This module realizes the finite orthogonal biproduct and dagger idempotent completeness interfaces
on `TauCeti.HilbertCat 𝕜` for any `RCLike` field `𝕜`:

* Finite orthogonal direct sums are given by `PiLp 2`, yielding
  `HasFiniteDaggerBiproducts (HilbertCat 𝕜)` and `HasBinaryDaggerBiproducts (HilbertCat 𝕜)`.
* Dagger projections on `X : HilbertCat 𝕜` coincide with Mathlib's `IsStarProjection`, and every
  dagger projection admits a canonical dagger splitting onto its closed range
  `(ConcreteCategory.hom p).range`, yielding `IsDaggerIdempotentComplete (HilbertCat 𝕜)`.
* Every bounded idempotent `e : X ⟶ X` has the same range as the orthogonal projection
  `(ConcreteCategory.hom e).range.starProjection`, so every idempotent in `HilbertCat 𝕜` is similar
  via an invertible morphism to a dagger projection. In particular, `HilbertCat 𝕜` is idempotent
  complete in the native sense and
  `DaggerKaroubi (HilbertCat 𝕜) ≌ Idempotents.Karoubi (HilbertCat 𝕜)`.
* On `EuclideanSpace ℂ (Fin 2)`, the oblique idempotent `(x, y) ↦ (x + y, 0)` has operator norm
  `√2`, is not self-adjoint, and admits no dagger splitting, while its algebraic retract
  `(x, y) ↦ x + y` also has norm `√2` and differs from the adjoint of the isometric inclusion
  `t ↦ (t, 0)` whose range projection is `(x, y) ↦ (x, 0)`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace TauCeti.HilbertCat

section FiniteDaggerBiproducts

variable {𝕜 : Type u} [RCLike 𝕜]

private def piLpSingleCLM {n : ℕ} (f : Fin n → HilbertCat.{u, v} 𝕜) (j : Fin n) :
    (f j : Type v) →L[𝕜] PiLp 2 (fun i => (f i : Type v)) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun i => (f i : Type v))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single 𝕜 (fun i => (f i : Type v)) j)

private theorem piLpSingleCLM_apply {n : ℕ} (f : Fin n → HilbertCat.{u, v} 𝕜) (j : Fin n)
    (x : f j) :
    piLpSingleCLM f j x = PiLp.single 2 j x := rfl

private theorem adjoint_piLpSingleCLM {n : ℕ} (f : Fin n → HilbertCat.{u, v} 𝕜) (j : Fin n) :
    ContinuousLinearMap.adjoint (piLpSingleCLM f j) =
      PiLp.proj 2 (fun i => (f i : Type v)) j := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [piLpSingleCLM_apply, PiLp.inner_apply, PiLp.proj_apply]
  rw [Fintype.sum_eq_single j]
  · rw [PiLp.single_eq_same]
  · intro i hi
    rw [PiLp.single_eq_of_ne 2 hi, inner_zero_right]

private def piLpBicone {n : ℕ} (f : Fin n → HilbertCat.{u, v} 𝕜) : Bicone f where
  pt := HilbertCat.of 𝕜 (PiLp 2 (fun i => (f i : Type v)))
  π j := ofHom (PiLp.proj 2 (fun i => (f i : Type v)) j)
  ι j := ofHom (piLpSingleCLM f j)
  ι_π j k := by
    apply ContinuousLinearMap.ext
    intro x
    by_cases h : j = k
    · subst h
      simp only [↓reduceDIte, eqToHom_refl]
      change (piLpSingleCLM f j x).ofLp j = x
      rw [piLpSingleCLM_apply, PiLp.single_eq_same]
    · simp only [h, ↓reduceDIte]
      change (piLpSingleCLM f j x).ofLp k = 0
      rw [piLpSingleCLM_apply, PiLp.single_eq_of_ne 2 (Ne.symm h)]

private theorem piLpBicone_isOrthogonal {n : ℕ} (f : Fin n → HilbertCat.{u, v} 𝕜) :
    (piLpBicone f).IsOrthogonal :=
  (Bicone.isOrthogonal_iff _).mpr fun j => adjoint_piLpSingleCLM f j

private theorem piLpBicone_total {n : ℕ} (f : Fin n → HilbertCat.{u, v} 𝕜) :
    ∑ j : Fin n, (piLpBicone f).π j ≫ (piLpBicone f).ι j = 𝟙 (piLpBicone f).pt := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  rw [sum_apply]
  change (∑ j : Fin n, piLpSingleCLM f j (x.ofLp j)).ofLp i = x.ofLp i
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · rw [piLpSingleCLM_apply, PiLp.single_eq_same]
  · intro j _ hj
    rw [piLpSingleCLM_apply, PiLp.single_eq_of_ne 2 hj.symm]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- `HilbertCat 𝕜` admits all finite orthogonal direct sums, realized by `PiLp 2`. -/
instance instHasFiniteDaggerBiproducts : HasFiniteDaggerBiproducts (HilbertCat.{u, v} 𝕜) where
  out _ := ⟨fun f => hasDaggerBiproduct_of_total (piLpBicone f) (piLpBicone_isOrthogonal f)
    (piLpBicone_total f)⟩

/-- `HilbertCat 𝕜` admits all binary orthogonal direct sums. -/
instance instHasBinaryDaggerBiproducts : HasBinaryDaggerBiproducts (HilbertCat.{u, v} 𝕜) :=
  hasBinaryDaggerBiproducts_of_finite_daggerBiproducts (HilbertCat.{u, v} 𝕜)

end FiniteDaggerBiproducts

section DaggerIdempotents

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Dagger projections on `HilbertCat 𝕜` are precisely Mathlib's star projections on continuous
linear endomorphisms. -/
theorem isDaggerProjection_iff_isStarProjection {X : HilbertCat.{u, v} 𝕜} (p : X ⟶ X) :
    IsDaggerProjection p ↔ IsStarProjection (ConcreteCategory.hom p) := by
  rw [isDaggerProjection_iff, isStarProjection_iff]
  rfl

/-- Canonical dagger splitting of a dagger projection on a Hilbert space onto its closed range. -/
def daggerSplittingOfProjection {X : HilbertCat.{u, v} 𝕜} {p : X ⟶ X}
    (hp : IsDaggerProjection p) : DaggerSplitting p := by
  have hstar : IsStarProjection (ConcreteCategory.hom p) :=
    (isDaggerProjection_iff_isStarProjection p).mp hp
  have hclosed : IsClosed ((ConcreteCategory.hom p).range : Set X) :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range hstar.isIdempotentElem
  have : CompleteSpace (ConcreteCategory.hom p).range := hclosed.completeSpace_coe
  have : (ConcreteCategory.hom p).range.HasOrthogonalProjection := .ofCompleteSpace _
  refine
    { obj := HilbertCat.of 𝕜 (ConcreteCategory.hom p).range
      hom := ofHom (ConcreteCategory.hom p).range.subtypeL
      isometry := ?_
      range := ?_ }
  · apply ContinuousLinearMap.ext
    intro v
    change (ConcreteCategory.hom p).range.subtypeL.adjoint (v : X) = v
    rw [Submodule.adjoint_subtypeL]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v
  · change (ConcreteCategory.hom p).range.subtypeL.comp
      (ConcreteCategory.hom p).range.subtypeL.adjoint = ConcreteCategory.hom p
    rw [Submodule.adjoint_subtypeL]
    rcases isStarProjection_iff_eq_starProjection_range.mp hstar with ⟨hproj, heq⟩
    have hsub : (ConcreteCategory.hom p).range.subtypeL.comp
        (ConcreteCategory.hom p).range.orthogonalProjectionOnto =
        (ConcreteCategory.hom p).range.starProjection := rfl
    rw [hsub]
    convert heq.symm

/-- Every dagger projection in `HilbertCat 𝕜` admits a dagger splitting. -/
instance instIsDaggerIdempotentComplete : IsDaggerIdempotentComplete (HilbertCat.{u, v} 𝕜) where
  daggerProjections_split _ _ hp := (daggerSplittingOfProjection hp).isDaggerSplit

/-- The orthogonal projection onto the closed range of an idempotent endomorphism `e` in
`HilbertCat 𝕜`. -/
def orthogonalProjectionOfIdempotent {X : HilbertCat.{u, v} 𝕜} {e : X ⟶ X} (he : e ≫ e = e) :
    X ⟶ X :=
  have : (ConcreteCategory.hom e).range.HasOrthogonalProjection :=
    ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range he
  ConcreteCategory.ofHom (C := HilbertCat 𝕜) (X := X) (Y := X)
    (ConcreteCategory.hom e).range.starProjection

/-- `orthogonalProjectionOfIdempotent he` is a dagger projection. -/
theorem isDaggerProjection_orthogonalProjectionOfIdempotent {X : HilbertCat.{u, v} 𝕜}
    {e : X ⟶ X} (he : e ≫ e = e) :
    IsDaggerProjection (orthogonalProjectionOfIdempotent he) := by
  have : (ConcreteCategory.hom e).range.HasOrthogonalProjection :=
    ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range he
  rw [isDaggerProjection_iff_isStarProjection]
  exact isStarProjection_starProjection

/-- `e ≫ orthogonalProjectionOfIdempotent he = e`, because `orthogonalProjectionOfIdempotent he`
fixes the range of `e` pointwise. -/
theorem comp_orthogonalProjectionOfIdempotent {X : HilbertCat.{u, v} 𝕜} {e : X ⟶ X}
    (he : e ≫ e = e) :
    e ≫ orthogonalProjectionOfIdempotent he = e := by
  have : (ConcreteCategory.hom e).range.HasOrthogonalProjection :=
    ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range he
  apply ContinuousLinearMap.ext
  intro x
  change (ConcreteCategory.hom e).range.starProjection (ConcreteCategory.hom e x) =
    ConcreteCategory.hom e x
  exact Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩

/-- `orthogonalProjectionOfIdempotent he ≫ e = orthogonalProjectionOfIdempotent he`, because `e`
acts as the identity on its own range. -/
theorem orthogonalProjectionOfIdempotent_comp {X : HilbertCat.{u, v} 𝕜} {e : X ⟶ X}
    (he : e ≫ e = e) :
    orthogonalProjectionOfIdempotent he ≫ e = orthogonalProjectionOfIdempotent he := by
  have : (ConcreteCategory.hom e).range.HasOrthogonalProjection :=
    ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range he
  apply ContinuousLinearMap.ext
  intro x
  change ConcreteCategory.hom e ((ConcreteCategory.hom e).range.starProjection x) =
    (ConcreteCategory.hom e).range.starProjection x
  rcases Submodule.starProjection_apply_mem (ConcreteCategory.hom e).range x with ⟨y, hy⟩
  rw [← hy]
  exact congrArg (fun f : X →L[𝕜] X => f y) he

/-- Every bounded idempotent on a Hilbert space is similar via an invertible morphism to a dagger
projection (namely `orthogonalProjectionOfIdempotent he`). -/
theorem exists_similar_daggerProjection {X : HilbertCat.{u, v} 𝕜} (e : X ⟶ X) (he : e ≫ e = e) :
    ∃ (p : X ⟶ X) (u : X ≅ X), IsDaggerProjection p ∧ u.inv ≫ e ≫ u.hom = p := by
  let p := orthogonalProjectionOfIdempotent he
  have hp : IsDaggerProjection p := isDaggerProjection_orthogonalProjectionOfIdempotent he
  refine ⟨p, sameRangeSimilarityIso he hp.idem (comp_orthogonalProjectionOfIdempotent he)
    (orthogonalProjectionOfIdempotent_comp he), hp, ?_⟩
  exact sameRangeSimilarityIso_inv_comp_comp_hom he hp.idem
    (comp_orthogonalProjectionOfIdempotent he) (orthogonalProjectionOfIdempotent_comp he)

/-- `HilbertCat 𝕜` is idempotent complete in the native sense, because every idempotent is similar
to a dagger projection and every dagger projection splits. -/
instance instIsIdempotentComplete : IsIdempotentComplete (HilbertCat.{u, v} 𝕜) :=
  isIdempotentComplete_of_exists_similar_projection fun _ e he =>
    exists_similar_daggerProjection e he

/-- The dagger Karoubi completion of `HilbertCat 𝕜` is equivalent to its native Karoubi
completion. -/
def daggerKaroubiEquivKaroubi :
    DaggerKaroubi (HilbertCat.{u, v} 𝕜) ≌ Idempotents.Karoubi (HilbertCat.{u, v} 𝕜) :=
  DaggerKaroubi.equivKaroubiOfExistsSimilarProjection fun e he =>
    exists_similar_daggerProjection e he

end DaggerIdempotents

section ObliqueIdempotentExample

/-- The isometric inclusion `ℂ ⟶ EuclideanSpace ℂ (Fin 2)` given by `t ↦ (t, 0)`. -/
def obliqueIncl :
    HilbertCat.of ℂ ℂ ⟶ HilbertCat.of ℂ (EuclideanSpace ℂ (Fin 2)) :=
  ofHom <|
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => ℂ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℂ (fun _ : Fin 2 => ℂ) 0)

/-- The oblique retraction `EuclideanSpace ℂ (Fin 2) ⟶ ℂ` given by `(x, y) ↦ x + y`. -/
def obliqueRetract :
    HilbertCat.of ℂ (EuclideanSpace ℂ (Fin 2)) ⟶ HilbertCat.of ℂ ℂ :=
  ofHom <|
    PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) 0 +
      PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) 1

/-- The oblique idempotent `(x, y) ↦ (x + y, 0)` on `EuclideanSpace ℂ (Fin 2)`. -/
def obliqueIdempotent :
    HilbertCat.of ℂ (EuclideanSpace ℂ (Fin 2)) ⟶ HilbertCat.of ℂ (EuclideanSpace ℂ (Fin 2)) :=
  obliqueRetract ≫ obliqueIncl

/-- The orthogonal projection `(x, y) ↦ (x, 0)` onto the first coordinate of
`EuclideanSpace ℂ (Fin 2)`. -/
def coordZeroProj :
    HilbertCat.of ℂ (EuclideanSpace ℂ (Fin 2)) ⟶ HilbertCat.of ℂ (EuclideanSpace ℂ (Fin 2)) :=
  dagger obliqueIncl ≫ obliqueIncl

/-- Evaluating `obliqueIncl` at coordinate `0` returns the input scalar. -/
@[simp] theorem obliqueIncl_apply_zero (t : ℂ) : (obliqueIncl t).ofLp 0 = t := by
  change (PiLp.single (β := fun _ : Fin 2 => ℂ) 2 (0 : Fin 2) t).ofLp 0 = t
  exact PiLp.single_eq_same (β := fun _ : Fin 2 => ℂ) 2 (0 : Fin 2) t

/-- Evaluating `obliqueIncl` at coordinate `1` returns `0`. -/
@[simp] theorem obliqueIncl_apply_one (t : ℂ) : (obliqueIncl t).ofLp 1 = 0 := by
  change (PiLp.single (β := fun _ : Fin 2 => ℂ) 2 (0 : Fin 2) t).ofLp 1 = 0
  exact PiLp.single_eq_of_ne (β := fun _ : Fin 2 => ℂ) 2 (by decide : (1 : Fin 2) ≠ 0) t

/-- Evaluating `obliqueRetract` sums the two coordinates. -/
@[simp] theorem obliqueRetract_apply (v : EuclideanSpace ℂ (Fin 2)) :
    obliqueRetract v = v.ofLp 0 + v.ofLp 1 := by
  unfold obliqueRetract
  rfl

/-- Evaluating `obliqueIdempotent` at coordinate `0` gives `v 0 + v 1`. -/
@[simp] theorem obliqueIdempotent_apply_zero (v : EuclideanSpace ℂ (Fin 2)) :
    (obliqueIdempotent v).ofLp 0 = v.ofLp 0 + v.ofLp 1 := by
  change (obliqueIncl (obliqueRetract v)).ofLp 0 = v.ofLp 0 + v.ofLp 1
  rw [obliqueIncl_apply_zero, obliqueRetract_apply]

/-- Evaluating `obliqueIdempotent` at coordinate `1` gives `0`. -/
@[simp] theorem obliqueIdempotent_apply_one (v : EuclideanSpace ℂ (Fin 2)) :
    (obliqueIdempotent v).ofLp 1 = 0 := by
  change (obliqueIncl (obliqueRetract v)).ofLp 1 = 0
  exact obliqueIncl_apply_one _

/-- The adjoint of `obliqueIncl` is projection onto coordinate `0`. -/
theorem dagger_obliqueIncl :
    dagger obliqueIncl = ofHom (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) 0) := by
  symm
  rw [dagger_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro v t
  rw [PiLp.inner_apply, Fin.sum_univ_two, ← hom_eq obliqueIncl, obliqueIncl_apply_zero,
    obliqueIncl_apply_one, inner_zero_right, add_zero]
  rfl

/-- Evaluating `coordZeroProj` at coordinate `0` returns `v 0`. -/
@[simp] theorem coordZeroProj_apply_zero (v : EuclideanSpace ℂ (Fin 2)) :
    (coordZeroProj v).ofLp 0 = v.ofLp 0 := by
  change (obliqueIncl ((dagger obliqueIncl) v)).ofLp 0 = v.ofLp 0
  rw [dagger_obliqueIncl, obliqueIncl_apply_zero]
  rfl

/-- Evaluating `coordZeroProj` at coordinate `1` returns `0`. -/
@[simp] theorem coordZeroProj_apply_one (v : EuclideanSpace ℂ (Fin 2)) :
    (coordZeroProj v).ofLp 1 = 0 := by
  change (obliqueIncl ((dagger obliqueIncl) v)).ofLp 1 = 0
  exact obliqueIncl_apply_one _

/-- `obliqueIncl` is a dagger isometry. -/
theorem isDaggerIsometry_obliqueIncl : IsDaggerIsometry obliqueIncl := by
  rw [isDaggerIsometry_iff, dagger_obliqueIncl]
  ext
  change (obliqueIncl 1).ofLp 0 = 1
  exact obliqueIncl_apply_zero 1

/-- `obliqueRetract` is a left inverse (categorical retraction) of `obliqueIncl`. -/
theorem obliqueIncl_comp_obliqueRetract :
    obliqueIncl ≫ obliqueRetract = 𝟙 (HilbertCat.of ℂ ℂ) := by
  ext
  change obliqueRetract (obliqueIncl 1) = 1
  rw [obliqueRetract_apply, obliqueIncl_apply_zero, obliqueIncl_apply_one, add_zero]

/-- `obliqueRetract ≫ obliqueIncl` recovers `obliqueIdempotent`. -/
theorem obliqueRetract_comp_obliqueIncl :
    obliqueRetract ≫ obliqueIncl = obliqueIdempotent := by
  unfold obliqueIdempotent
  rfl

/-- `obliqueIdempotent` is idempotent. -/
theorem obliqueIdempotent_idem :
    obliqueIdempotent ≫ obliqueIdempotent = obliqueIdempotent := by
  rw [obliqueIdempotent, Category.assoc, ← Category.assoc obliqueIncl,
    obliqueIncl_comp_obliqueRetract, Category.id_comp]

/-- `coordZeroProj` is a dagger projection. -/
theorem isDaggerProjection_coordZeroProj : IsDaggerProjection coordZeroProj :=
  IsDaggerProjection.of_isDaggerIsometry isDaggerIsometry_obliqueIncl

/-- The canonical dagger splitting of `coordZeroProj` via `obliqueIncl`. -/
@[expose] def coordZeroSplitting : DaggerSplitting coordZeroProj where
  obj := HilbertCat.of ℂ ℂ
  hom := obliqueIncl
  isometry := isDaggerIsometry_obliqueIncl.hom_dagger_id
  range := by unfold coordZeroProj; rfl

/-- `obliqueIdempotent` and `coordZeroProj` satisfy `e ≫ p = e` (same range). -/
theorem obliqueIdempotent_comp_coordZeroProj :
    obliqueIdempotent ≫ coordZeroProj = obliqueIdempotent := by
  ext v i
  fin_cases i
  · change (coordZeroProj (obliqueIdempotent v)).ofLp 0 = (obliqueIdempotent v).ofLp 0
    exact coordZeroProj_apply_zero _
  · change (coordZeroProj (obliqueIdempotent v)).ofLp 1 = (obliqueIdempotent v).ofLp 1
    rw [coordZeroProj_apply_one, obliqueIdempotent_apply_one]

/-- `obliqueIdempotent` and `coordZeroProj` satisfy `p ≫ e = p` (same range). -/
theorem coordZeroProj_comp_obliqueIdempotent :
    coordZeroProj ≫ obliqueIdempotent = coordZeroProj := by
  ext v i
  fin_cases i
  · change (obliqueIdempotent (coordZeroProj v)).ofLp 0 = (coordZeroProj v).ofLp 0
    rw [obliqueIdempotent_apply_zero, coordZeroProj_apply_zero, coordZeroProj_apply_one, add_zero]
  · change (obliqueIdempotent (coordZeroProj v)).ofLp 1 = (coordZeroProj v).ofLp 1
    rw [obliqueIdempotent_apply_one, coordZeroProj_apply_one]

/-- `obliqueIdempotent` is not self-adjoint. -/
theorem dagger_obliqueIdempotent_ne : dagger obliqueIdempotent ≠ obliqueIdempotent := by
  intro h
  let e₀ : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 0 1
  let e₁ : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 1 1
  have h1 : inner ℂ (dagger obliqueIdempotent e₀) e₁ = 1 := by
    rw [inner_dagger_left, PiLp.inner_apply, Fin.sum_univ_two, obliqueIdempotent_apply_zero,
      obliqueIdempotent_apply_one]
    simp [e₀, e₁]
  have h2 : inner ℂ (obliqueIdempotent e₀) e₁ = 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two, obliqueIdempotent_apply_zero,
      obliqueIdempotent_apply_one]
    simp [e₀, e₁]
  rw [h] at h1
  exact one_ne_zero (h1.symm.trans h2)

/-- `obliqueIdempotent` is not a dagger projection. -/
theorem not_isDaggerProjection_obliqueIdempotent : ¬ IsDaggerProjection obliqueIdempotent :=
  fun hp => dagger_obliqueIdempotent_ne hp.dagger_eq

/-- `obliqueIdempotent` admits no dagger splitting. -/
theorem not_isDaggerSplit_obliqueIdempotent : ¬ IsDaggerSplit obliqueIdempotent :=
  fun hs => not_isDaggerProjection_obliqueIdempotent hs.isDaggerProjection

/-- The algebraic retraction `obliqueRetract` differs from the adjoint `dagger obliqueIncl`. -/
theorem obliqueRetract_ne_dagger_obliqueIncl : obliqueRetract ≠ dagger obliqueIncl := by
  intro h
  let e₁ : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 1 1
  have hv : obliqueRetract e₁ = (dagger obliqueIncl) e₁ :=
    congrArg (fun f : HilbertCat.of ℂ (EuclideanSpace ℂ (Fin 2)) ⟶ HilbertCat.of ℂ ℂ => f e₁) h
  rw [dagger_obliqueIncl, obliqueRetract_apply] at hv
  change e₁.ofLp 0 + e₁.ofLp 1 = e₁.ofLp 0 at hv
  simp [e₁] at hv

/-- The comparison isomorphism between the algebraic splitting `(obliqueIncl, obliqueRetract)` and
`coordZeroSplitting` does not intertwine `obliqueRetract` with `dagger obliqueIncl`. -/
theorem retractIsoDaggerSplitting_oblique_not_intertwines :
    obliqueRetract ≫
      (retractIsoDaggerSplitting obliqueIncl obliqueRetract obliqueIncl_comp_obliqueRetract
        obliqueRetract_comp_obliqueIncl coordZeroSplitting obliqueIdempotent_comp_coordZeroProj
        coordZeroProj_comp_obliqueIdempotent).hom ≠ dagger obliqueIncl := by
  intro h
  have heq : obliqueIdempotent = coordZeroProj :=
    (retractIsoDaggerSplitting_comp_hom_iff obliqueIncl obliqueRetract
      obliqueIncl_comp_obliqueRetract obliqueRetract_comp_obliqueIncl coordZeroSplitting
      obliqueIdempotent_comp_coordZeroProj coordZeroProj_comp_obliqueIdempotent).mp h
  exact not_isDaggerProjection_obliqueIdempotent (heq ▸ isDaggerProjection_coordZeroProj)

/-- `obliqueIncl` preserves vector norms. -/
theorem norm_obliqueIncl_apply (t : ℂ) : ‖obliqueIncl t‖ = ‖t‖ :=
  PiLp.norm_single 2 (fun _ : Fin 2 => ℂ) 0 t

/-- The operator norm of `obliqueIncl` is `1`. -/
theorem norm_obliqueIncl : ‖obliqueIncl‖ = 1 := by
  have hsq : ‖obliqueIncl‖ ^ 2 = 1 := by
    rw [← norm_self_comp_dagger, isDaggerIsometry_obliqueIncl.hom_dagger_id]
    exact ContinuousLinearMap.norm_id
  nlinarith [norm_nonneg obliqueIncl]

/-- The operator norm of `coordZeroProj` is `1`. -/
theorem norm_coordZeroProj : ‖coordZeroProj‖ = 1 := by
  have h : ‖coordZeroProj‖ = ‖dagger obliqueIncl‖ ^ 2 := by
    rw [coordZeroProj, ← norm_self_comp_dagger, dagger_dagger]
  rw [h, norm_dagger, norm_obliqueIncl, one_pow]

/-- The operator norm of `obliqueRetract` is `√2`. -/
theorem norm_obliqueRetract : ‖obliqueRetract‖ = Real.sqrt 2 := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2) fun v => ?_
    change ‖obliqueRetract v‖ ≤ Real.sqrt 2 * ‖v‖
    rw [obliqueRetract_apply]
    have hnorm_sq : ‖v‖ ^ 2 = ‖v.ofLp 0‖ ^ 2 + ‖v.ofLp 1‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    have htri : ‖v.ofLp 0 + v.ofLp 1‖ ≤ ‖v.ofLp 0‖ + ‖v.ofLp 1‖ := norm_add_le _ _
    have hsq : ‖v.ofLp 0 + v.ofLp 1‖ ^ 2 ≤ (Real.sqrt 2 * ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hnorm_sq]
      nlinarith [sq_nonneg (‖v.ofLp 0‖ - ‖v.ofLp 1‖), norm_nonneg (v.ofLp 0 + v.ofLp 1)]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg v))).mp hsq
  · let w : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![(1 : ℂ), 1]
    have hw_sq : ‖w‖ ^ 2 = 2 := by
      rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
      change ‖(1 : ℂ)‖ ^ 2 + ‖(1 : ℂ)‖ ^ 2 = 2
      norm_num
    have hw_norm : ‖w‖ = Real.sqrt 2 := by
      rw [← Real.sqrt_sq (norm_nonneg w), hw_sq]
    have hval : ‖obliqueRetract w‖ = 2 := by
      rw [obliqueRetract_apply]
      change ‖(1 : ℂ) + 1‖ = 2
      norm_num
    have hle : 2 ≤ ‖obliqueRetract‖ * Real.sqrt 2 := by
      have h := ContinuousLinearMap.le_opNorm
        (f := (obliqueRetract : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ)) w
      change ‖obliqueRetract w‖ ≤ ‖obliqueRetract‖ * ‖w‖ at h
      rw [hval, hw_norm] at h
      exact h
    have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith

/-- The operator norm of `obliqueIdempotent` is `√2`. -/
theorem norm_obliqueIdempotent : ‖obliqueIdempotent‖ = Real.sqrt 2 := by
  have hnorm_eq : ∀ v : EuclideanSpace ℂ (Fin 2), ‖obliqueIdempotent v‖ = ‖obliqueRetract v‖ :=
    fun v => norm_obliqueIncl_apply (obliqueRetract v)
  rw [← norm_obliqueRetract]
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    change ‖obliqueIdempotent v‖ ≤ ‖obliqueRetract‖ * ‖v‖
    rw [hnorm_eq]
    exact ContinuousLinearMap.le_opNorm
      (f := (obliqueRetract : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ)) v
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    change ‖obliqueRetract v‖ ≤ ‖obliqueIdempotent‖ * ‖v‖
    rw [← hnorm_eq]
    exact ContinuousLinearMap.le_opNorm
      (f := (obliqueIdempotent : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))) v

end ObliqueIdempotentExample

end TauCeti.HilbertCat
