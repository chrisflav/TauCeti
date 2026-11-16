/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Submersion
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Recognizing diffeomorphisms through surjective submersions

A bijection commuting with two surjective `C^n` submersions out of a common boundaryless manifold
is a `C^n` diffeomorphism (`Equiv.diffeomorphOfSubmersions`). Smoothness in each direction is
detected after precomposing with the corresponding surjective submersion
(`Manifold.IsSubmersion.contMDiff_comp_iff`), so no separate continuity hypothesis on the bijection
is needed.

In particular, two smooth manifold structures on a common target for which the same surjection is a
`C^n` submersion are `C^n` diffeomorphic by the identity
(`ChartedSpace.exists_diffeomorph_apply_eq_self_of_isSubmersion`), and when they share the same
model they have the same maximal `C^n` atlas (`ChartedSpace.maximalAtlas_eq_of_isSubmersion`).
This is the submersion counterpart of `TauCeti.Geometry.Manifold.Immersion.Diffeomorph`.

## Main definitions and results

* `Equiv.diffeomorphOfSubmersions`: a bijection commuting with two surjective `C^n` submersions out
  of a boundaryless manifold is a `C^n` diffeomorphism.
* `ChartedSpace.exists_diffeomorph_apply_eq_self_of_isSubmersion`: two atlases making the same
  surjection a `C^n` submersion are `C^n` diffeomorphic by the identity.
* `ChartedSpace.maximalAtlas_eq_of_isSubmersion`: two `C^n` manifold atlases with the same model
  making the same surjection a `C^n` submersion have the same maximal `C^n` atlas.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 4.29 and
  Theorem 4.31 (characteristic property of surjective submersions and uniqueness of smooth
  structures).
-/

public section

open Function Manifold
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F V H G W : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [TopologicalSpace W]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 F G} {K : ModelWithCorners 𝕜 V W}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [cN : ChartedSpace G N] [TopologicalSpace P] [cP : ChartedSpace W P]
  {n : ℕ∞ω} {p : M → N} {q : M → P}

namespace Equiv

/-- A bijection commuting with two surjective `C^n` submersions out of a common boundaryless
manifold is a `C^n` diffeomorphism. No continuity, finite-dimensionality or separation hypotheses
are required. -/
def diffeomorphOfSubmersions (e : N ≃ P)
    (hp : IsSubmersion I J n p) (hp_surj : Surjective p)
    (hq : IsSubmersion I K n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) : N ≃ₘ^n⟮J, K⟯ P where
  toEquiv := e
  contMDiff_toFun := (hp.contMDiff_comp_iff hp_surj le_rfl).1 (h.symm ▸ hq.contMDiff)
  contMDiff_invFun := by
    refine (hq.contMDiff_comp_iff hq_surj le_rfl).1 ?_
    have h' : e.symm ∘ q = p := by
      ext x
      simpa only [Function.comp_apply, e.symm_apply_apply] using congrArg e.symm (congrFun h x).symm
    exact h'.symm ▸ hp.contMDiff

/-- Recognizing smoothness through surjective submersions does not change the underlying
bijection. -/
@[simp]
theorem diffeomorphOfSubmersions_toEquiv (e : N ≃ P)
    (hp : IsSubmersion I J n p) (hp_surj : Surjective p)
    (hq : IsSubmersion I K n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) : (e.diffeomorphOfSubmersions hp hp_surj hq hq_surj h).toEquiv = e :=
  (rfl)

/-- The diffeomorphism acts by the original bijection. -/
@[simp]
theorem diffeomorphOfSubmersions_apply (e : N ≃ P)
    (hp : IsSubmersion I J n p) (hp_surj : Surjective p)
    (hq : IsSubmersion I K n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) (x : N) : e.diffeomorphOfSubmersions hp hp_surj hq hq_surj h x = e x :=
  (rfl)

/-- The inverse diffeomorphism acts by the inverse bijection. -/
@[simp]
theorem diffeomorphOfSubmersions_symm_apply (e : N ≃ P)
    (hp : IsSubmersion I J n p) (hp_surj : Surjective p)
    (hq : IsSubmersion I K n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) (y : P) :
    (e.diffeomorphOfSubmersions hp hp_surj hq hq_surj h).symm y = e.symm y :=
  (rfl)

end Equiv

namespace ChartedSpace

omit cN in
/-- Two atlases on the same topological space are `C^n` diffeomorphic by the identity whenever the
same surjection from a boundaryless manifold is a `C^n` submersion for both atlases. -/
theorem exists_diffeomorph_apply_eq_self_of_isSubmersion (a : ChartedSpace G N)
    (b : ChartedSpace W N) (hp_surj : Surjective p)
    (ha : letI := a; IsSubmersion I J n p)
    (hb : letI := b; IsSubmersion I K n p) :
    ∃ e : @Diffeomorph 𝕜 _ _ _ _ _ _ _ _ _ _ _ J K N _ a N _ b n, ∀ x, e x = x :=
  ⟨Equiv.diffeomorphOfSubmersions (cN := a) (cP := b)
    (Equiv.refl _) ha hp_surj hb hp_surj rfl, fun _ ↦ rfl⟩

omit cN in
/-- Two `C^n` manifold atlases with the same model on a common topological space have the same
maximal `C^n` atlas whenever the same surjection from a boundaryless manifold is a `C^n` submersion
for both atlases. -/
theorem maximalAtlas_eq_of_isSubmersion (a b : ChartedSpace G N) (hp_surj : Surjective p)
    (hma : letI := a; IsManifold J n N) (hmb : letI := b; IsManifold J n N)
    (ha : letI := a; IsSubmersion I J n p) (hb : letI := b; IsSubmersion I J n p) :
    (letI := a; IsManifold.maximalAtlas J n N) = (letI := b; IsManifold.maximalAtlas J n N) := by
  have key {N₁ N₂ : Type _} [TopologicalSpace N₁] [ChartedSpace G N₁] [IsManifold J n N₁]
      [TopologicalSpace N₂] [ChartedSpace G N₂]
      (e : N₁ ≃ₘ^n⟮J, J⟯ N₂) (f : N₁ ≃ₜ N₂) (hf : ∀ x, e x = f x)
      {φ : OpenPartialHomeomorph N₂ G} (hφ : φ ∈ IsManifold.maximalAtlas J n N₂) :
      f.transOpenPartialHomeomorph φ ∈ IsManifold.maximalAtlas J n N₁ := by
    have hfs : ∀ y, e.symm y = f.symm y := fun y ↦
      f.injective (by rw [← hf, e.apply_symm_apply, f.apply_symm_apply])
    have heq : e.toPartialDiffeomorph.toOpenPartialHomeomorph.trans φ =
        f.transOpenPartialHomeomorph φ := by
      ext x
      · simp [hf]
      · simp [hfs]
      · simp [hf]
    exact heq ▸ e.toPartialDiffeomorph.trans_mem_maximalAtlas hφ
  obtain ⟨eab, heab⟩ := exists_diffeomorph_apply_eq_self_of_isSubmersion a b hp_surj ha hb
  obtain ⟨eba, heba⟩ := exists_diffeomorph_apply_eq_self_of_isSubmersion b a hp_surj hb ha
  ext φ
  have hrefl : (Homeomorph.refl N).transOpenPartialHomeomorph φ = φ := by
    ext x <;> simp
  exact ⟨fun hφ ↦ hrefl ▸ @key N N _ b hmb _ a eba (Homeomorph.refl N) heba φ hφ,
    fun hφ ↦ hrefl ▸ @key N N _ a hma _ b eab (Homeomorph.refl N) heab φ hφ⟩

end ChartedSpace
