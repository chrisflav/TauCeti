/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Submersion.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Recognizing diffeomorphisms and uniqueness of smooth structures through submersions

A bijection commuting with two surjective `C^n` submersions out of a common boundaryless manifold
is a `C^n` diffeomorphism (`Equiv.diffeomorphOfSubmersions`). Unlike the immersion counterpart
`Homeomorph.diffeomorphOfImmersions`, continuity of the bijection need not be assumed separately,
since smoothness descends along a surjective submersion
(`Manifold.IsSubmersion.contMDiff_comp_iff`). More generally, two surjective `C^n` submersions out
of a boundaryless manifold that have the same fibres are related by a unique `C^n` diffeomorphism
of their targets (`Manifold.IsSubmersion.existsUnique_diffeomorph_comp_eq`).

Applied to the identity of a topological space carrying two atlases, possibly with different models,
this shows that a surjective map out of a boundaryless manifold can be a `C^n` submersion for at
most one `C^n` manifold structure up to canonical diffeomorphism
(`ChartedSpace.exists_diffeomorph_apply_eq_self_of_isSubmersion`), and for a single model up to
equality of maximal atlases (`ChartedSpace.maximalAtlas_eq_of_isSubmersion`). This is the
uniqueness half of the quotient manifold theorem.

## Main declarations

* `Equiv.diffeomorphOfSubmersions`: a bijection intertwining two surjective `C^n` submersions out
  of a boundaryless manifold is a `C^n` diffeomorphism.
* `Manifold.IsSubmersion.existsUnique_diffeomorph_comp_eq`: surjective `C^n` submersions out of a
  boundaryless manifold with the same fibres differ on the target by a unique `C^n` diffeomorphism.
* `ChartedSpace.exists_diffeomorph_apply_eq_self_of_isSubmersion`: two atlases on one space making
  the same surjection out of a boundaryless manifold a `C^n` submersion are `C^n` diffeomorphic by
  the identity.
* `ChartedSpace.maximalAtlas_eq_of_isSubmersion`: when both atlases use the same model, their
  `C^n` maximal atlases coincide.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.31 (uniqueness of smooth quotient structures).
-/

public section

open Function
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F V H G W : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [TopologicalSpace W]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {K : ModelWithCorners 𝕜 V W} [K.Boundaryless]
  {M N P : Type*} [TopologicalSpace M] [cM : ChartedSpace H M]
  [TopologicalSpace N] [cN : ChartedSpace G N] [TopologicalSpace P] [ChartedSpace W P]
  {n : ℕ∞ω} {p : P → M} {q : P → N}

namespace Equiv

/-- A bijection commuting with two surjective `C^n` submersions out of a common boundaryless
manifold is a `C^n` diffeomorphism. Neither finite-dimensionality nor separation is needed. -/
def diffeomorphOfSubmersions (e : M ≃ N)
    (hp : Manifold.IsSubmersion K I n p) (hp_surj : Surjective p)
    (hq : Manifold.IsSubmersion K J n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) : M ≃ₘ^n⟮I, J⟯ N where
  toEquiv := e
  contMDiff_toFun := (hp.contMDiff_comp_iff hp_surj le_rfl).1 (h.symm ▸ hq.contMDiff)
  contMDiff_invFun := by
    refine (hq.contMDiff_comp_iff hq_surj le_rfl).1 ?_
    have h' : e.symm ∘ q = p := by
      ext z
      simpa only [comp_apply, e.symm_apply_apply] using congrArg e.symm (congrFun h z).symm
    exact h'.symm ▸ hp.contMDiff

/-- Recognizing smoothness through submersions preserves the underlying equivalence. -/
@[simp]
theorem diffeomorphOfSubmersions_toEquiv (e : M ≃ N)
    (hp : Manifold.IsSubmersion K I n p) (hp_surj : Surjective p)
    (hq : Manifold.IsSubmersion K J n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) : (e.diffeomorphOfSubmersions hp hp_surj hq hq_surj h).toEquiv = e := by
  ext x
  rfl

/-- The diffeomorphism acts by the original bijection. -/
@[simp]
theorem diffeomorphOfSubmersions_apply (e : M ≃ N)
    (hp : Manifold.IsSubmersion K I n p) (hp_surj : Surjective p)
    (hq : Manifold.IsSubmersion K J n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) (x : M) :
    e.diffeomorphOfSubmersions hp hp_surj hq hq_surj h x = e x :=
  (rfl)

/-- The inverse diffeomorphism acts by the inverse bijection. -/
@[simp]
theorem diffeomorphOfSubmersions_symm_apply (e : M ≃ N)
    (hp : Manifold.IsSubmersion K I n p) (hp_surj : Surjective p)
    (hq : Manifold.IsSubmersion K J n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) (y : N) :
    (e.diffeomorphOfSubmersions hp hp_surj hq hq_surj h).symm y = e.symm y :=
  (rfl)

end Equiv

namespace Manifold.IsSubmersion

/-- **Uniqueness of smooth quotient targets.** Two surjective `C^n` submersions out of a
boundaryless manifold that have the same fibres are related on their targets by a unique `C^n`
diffeomorphism. -/
theorem existsUnique_diffeomorph_comp_eq
    (hp : IsSubmersion K I n p) (hp_surj : Surjective p)
    (hq : IsSubmersion K J n q) (hq_surj : Surjective q)
    (hfib : ∀ x y, p x = p y ↔ q x = q y) :
    ∃! Φ : M ≃ₘ^n⟮I, J⟯ N, ⇑Φ ∘ p = q := by
  obtain ⟨g, ⟨hg, hgp⟩, hg_uniq⟩ :=
    hp.existsUnique_contMDiff_comp_eq hp_surj le_rfl hq.contMDiff fun x y h ↦ (hfib x y).1 h
  obtain ⟨g', ⟨hg', hg'q⟩, -⟩ :=
    hq.existsUnique_contMDiff_comp_eq hq_surj le_rfl hp.contMDiff fun x y h ↦ (hfib x y).2 h
  have hleft : LeftInverse g' g := by
    intro x
    obtain ⟨z, rfl⟩ := hp_surj x
    exact (congrArg g' (congrFun hgp z)).trans (congrFun hg'q z)
  have hright : RightInverse g' g := by
    intro y
    obtain ⟨z, rfl⟩ := hq_surj y
    exact (congrArg g (congrFun hg'q z)).trans (congrFun hgp z)
  refine ⟨{ toFun := g, invFun := g', left_inv := hleft, right_inv := hright,
            contMDiff_toFun := hg, contMDiff_invFun := hg' }, hgp, fun Ψ hΨ ↦ ?_⟩
  ext x
  exact congrFun (hg_uniq Ψ ⟨Ψ.contMDiff, hΨ⟩) x

end Manifold.IsSubmersion

namespace ChartedSpace

omit cM in
/-- Two atlases on the same topological space, possibly with different models, are `C^n`
diffeomorphic by the identity whenever the same surjective map out of a boundaryless manifold is a
`C^n` submersion for both atlases. -/
theorem exists_diffeomorph_apply_eq_self_of_isSubmersion
    (a : ChartedSpace H M) (b : ChartedSpace G M)
    (hp_surj : Surjective p)
    (ha : letI := a; Manifold.IsSubmersion K I n p)
    (hb : letI := b; Manifold.IsSubmersion K J n p) :
    ∃ e : @Diffeomorph 𝕜 _ _ _ _ _ _ _ _ _ _ _ I J M _ a M _ b n, ∀ x, e x = x :=
  ⟨Equiv.diffeomorphOfSubmersions (cM := a) (cN := b)
    (Equiv.refl M) ha hp_surj hb hp_surj rfl, fun _ ↦ rfl⟩

omit cM in
private theorem trans_mem_maximalAtlas {N' : Type*} [TopologicalSpace N'] [cN' : ChartedSpace H N']
    (cM' : ChartedSpace H M) (hM : letI := cM'; IsManifold I n M)
    (e : @Diffeomorph 𝕜 _ E _ _ E _ _ H _ H _ I I M _ cM' N' _ cN' n)
    {f : M ≃ₜ N'} (he : ∀ x, e x = f x)
    {φ : OpenPartialHomeomorph N' H} (hφ : φ ∈ IsManifold.maximalAtlas I n N') :
    f.toOpenPartialHomeomorph.trans φ ∈
      (letI := cM'; IsManifold.maximalAtlas I n M) := by
  let := cM'
  have := hM
  have hf : e.toHomeomorph = f := Homeomorph.ext he
  rw [← hf]
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · exact (contMDiffOn_of_mem_maximalAtlas hφ).comp e.contMDiff.contMDiffOn fun _ hx ↦ hx.2
  · exact e.symm.contMDiff.comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas hφ).mono Set.inter_subset_left)

omit cM in
/-- **Uniqueness of submersion quotient atlases.** Two `C^n` manifold structures on the same
topological space and model for which a common surjective map out of a boundaryless manifold is a
`C^n` submersion have the same `C^n` maximal atlas. -/
theorem maximalAtlas_eq_of_isSubmersion (a b : ChartedSpace H M)
    (haM : letI := a; IsManifold I n M) (hbM : letI := b; IsManifold I n M)
    (hp_surj : Surjective p)
    (ha : letI := a; Manifold.IsSubmersion K I n p)
    (hb : letI := b; Manifold.IsSubmersion K I n p) :
    (letI := a; IsManifold.maximalAtlas I n M) = (letI := b; IsManifold.maximalAtlas I n M) := by
  have hsub (c d : ChartedSpace H M) (hdM : letI := d; IsManifold I n M)
      (hc : letI := c; Manifold.IsSubmersion K I n p)
      (hd : letI := d; Manifold.IsSubmersion K I n p) :
      (letI := c; IsManifold.maximalAtlas I n M) ⊆
        (letI := d; IsManifold.maximalAtlas I n M) := by
    let e := Equiv.diffeomorphOfSubmersions (cM := d) (cN := c)
      (Equiv.refl M) hd hp_surj hc hp_surj rfl
    intro φ hφ
    have htrans : (Homeomorph.refl M).toOpenPartialHomeomorph.trans φ = φ := by
      ext x <;> simp
    exact htrans ▸
      trans_mem_maximalAtlas (cN' := c) d hdM e (f := Homeomorph.refl M) (fun _ ↦ rfl) hφ
  exact Set.Subset.antisymm (hsub a b hbM ha hb) (hsub b a haM hb ha)

end ChartedSpace

