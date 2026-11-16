/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import TauCeti.LinearAlgebra.Ray
import TauCeti.LinearAlgebra.RootSystem.Inversions.Length

/-!
# Rays and translates of Weyl orbits of weights

Two facts about the Weyl orbit `W λ` of a weight `λ` of a root pairing over a linearly ordered
field. When the Weyl group is finite, no two distinct weights of `W λ` lie in the same ray, so a
vector in `W λ` is determined by its direction. Adding a weight `χ` fixed by the Weyl group maps
`W λ` into `W (λ + χ)`, since `w λ + χ = w (λ + χ)`.

These are the hypotheses under which a path with velocities in `W λ` has a unique distinguished
presentation, and its central shift by `χ` has velocities in `W (λ + χ)`; see
`TauCeti/RepresentationTheory/LSPath/Distinguished.lean`.

Each Weyl orbit is stable under root reflections. For a root pairing over `ℤ`, an additive map
`f` from the weight lattice to a vector space carries
the reflection `s_i` in the root `αᵢ` to the reflection in `f αᵢ` along a linear form agreeing
with the coroot `αᵢ^∨`, so the image `f (W λ)` is stable under the latter. This is the hypothesis
under which the root operators preserve paths with velocities in `f (W λ)`; see
`TauCeti/RepresentationTheory/LSPath/OrbitStable.lean`. When `P` is finite and reduced with a base
`b`, every Weyl-group element acts on `f(M)` by a composition of linear reflections, so distinct
points of the realized orbit `f (W λ)` never lie in the same ray either.

## Main results

* `RootPairing.pairwise_not_sameRay_orbit_weylGroup`: when the Weyl group is finite, no two
  distinct weights of a Weyl orbit lie in the same ray.
* `RootPairing.mapsTo_add_orbit_weylGroup`: adding a Weyl-invariant weight `χ` maps `W λ` into
  `W (λ + χ)`.
* `RootPairing.mapsTo_preReflection_image_orbit_weylGroup`: the image `f (W λ)` of a Weyl orbit
  in a vector space is stable under the reflection in an image root `f αᵢ`, along a linear form
  agreeing with the coroot `αᵢ^∨`.
* `RootPairing.pairwise_not_sameRay_image_orbit_weylGroup` and
  `RootPairing.pairwise_not_sameRay_range_smul`: for a finite reduced root pairing over `ℤ` with a
  base, no two distinct points of the realized Weyl orbit `f (W λ)` lie in the same ray.
-/

public section

namespace RootPairing

section Field

variable {ι 𝕜 V N : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V] [AddCommGroup N] [Module 𝕜 N] (P : RootPairing ι 𝕜 V N)

/-- When the Weyl group is finite, no two distinct weights of a Weyl orbit lie in the same ray.
So a path with velocities in `W λ` has at most one distinguished presentation for `W λ`. -/
theorem pairwise_not_sameRay_orbit_weylGroup [Finite P.weylGroup] (lam : V) :
    (MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v :=
  fun _ hu _ hv huv h ↦ huv (h.eq_of_mem_orbit hu hv (Set.finite_range _))

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Adding a weight `χ` fixed by the Weyl group maps the Weyl orbit `W λ` to `W (λ + χ)`, since
`w λ + χ = w (λ + χ)`. So the central shift by `χ` transports paths with velocities in `W λ` to
paths with velocities in `W (λ + χ)`. -/
theorem mapsTo_add_orbit_weylGroup {χ : V} (hχ : ∀ w : P.weylGroup, w • χ = χ) (lam : V) :
    Set.MapsTo (· + χ) (MulAction.orbit P.weylGroup lam)
      (MulAction.orbit P.weylGroup (lam + χ)) := by
  rintro _ ⟨w, rfl⟩
  exact ⟨w, by simp only [smul_add, hχ]⟩

end Field

section CommRing

variable {ι R V N : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R V N)

/-- A Weyl orbit is stable under reflection in any root along its coroot. -/
theorem mapsTo_preReflection_orbit_weylGroup (i : ι) (lam : V) :
    Set.MapsTo (Module.preReflection (P.root i) (P.coroot' i))
      (MulAction.orbit P.weylGroup lam) (MulAction.orbit P.weylGroup lam) := by
  intro v hv
  simpa [P.reflection_apply, Module.preReflection_apply] using
    MulAction.mapsTo_smul_orbit (weylGroup.ofIdx P i) lam hv

end CommRing

section Realization

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N)
  [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] {f : M →+ V}

/-- An additive map `f` from the weight lattice intertwines the reflection `s_i` in the root `αᵢ`
with the reflection in the image root `f αᵢ` along a linear form `F` agreeing with the coroot
`αᵢ^∨` on the weight lattice. -/
theorem map_reflection_eq_preReflection (i : ι) {F : Module.Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (m : M) :
    f (P.reflection i m) = Module.preReflection (f (P.root i)) F (f m) := by
  simp [P.reflection_apply, Module.preReflection_apply, hF, Int.cast_smul_eq_zsmul]

/-- The image `f (W λ)` of a Weyl orbit under an additive map `f` from the weight lattice is
stable under the reflection in the image root `f αᵢ` along a linear form `F` agreeing with the
coroot `αᵢ^∨` on the weight lattice. -/
theorem mapsTo_preReflection_image_orbit_weylGroup (i : ι) {F : Module.Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    Set.MapsTo (Module.preReflection (f (P.root i)) F) (f '' MulAction.orbit P.weylGroup lam)
      (f '' MulAction.orbit P.weylGroup lam) := by
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  refine ⟨_, ⟨weylGroup.ofIdx P i * w, rfl⟩, ?_⟩
  dsimp only
  rw [mul_smul, weylGroup.ofIdx_smul, Equiv.reflection_smul,
    P.map_reflection_eq_preReflection i hF]

/-- Every Weyl-group element acts on the image of a realization `f` by a `𝕜`-linear endomorphism
built from the simple pre-reflections, whenever the height forms `F` agree with the simple coroots
on `f(M)`. -/
private theorem exists_linearMap_map_smul (b : P.Base) [Finite ι] [P.IsReduced]
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = (P.coroot' i m : 𝕜)) (w : P.weylGroup) :
    ∃ T : V →ₗ[𝕜] V, ∀ m : M, f (w • m) = T (f m) := by
  obtain ⟨l, rfl⟩ := TauCeti.exists_wordProd_eq P b w
  induction l with
  | nil => exact ⟨LinearMap.id, fun m ↦ by simp⟩
  | cons i l ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨(Module.preReflection (f (P.root i)) (F i)).comp T, fun m ↦ ?_⟩
    rw [TauCeti.wordProd_cons, mul_smul, weylGroup.ofIdx_smul, Equiv.reflection_smul,
      P.map_reflection_eq_preReflection i.1 (hF i), hT, LinearMap.comp_apply]

/-- **No two distinct points of a realized Weyl orbit lie in the same ray.** For a finite reduced
root pairing over `ℤ` with a base `b` and a realization `(f, F)` into a vector space over a linearly
ordered field `𝕜` whose height forms agree with the simple coroots on `f(M)`, distinct elements of
`f (W λ)` are never positively proportional. Neither injectivity of `f` nor spanning of the roots
is needed. -/
theorem pairwise_not_sameRay_image_orbit_weylGroup [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (b : P.Base) [Finite ι] [P.IsReduced] {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    (f '' MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  let _ := P.finite_weylGroup_of_base b
  rintro _ ⟨_, ⟨w₁, rfl⟩, rfl⟩ _ ⟨_, ⟨w₂, rfl⟩, rfl⟩ hne hsame
  apply hne
  dsimp only at hsame ⊢
  set g : P.weylGroup := w₂ * w₁⁻¹
  obtain ⟨T, hT⟩ := P.exists_linearMap_map_smul b hF g
  obtain ⟨T', hT'⟩ := P.exists_linearMap_map_smul b hF g⁻¹
  have hg₁ : f (w₂ • lam) = T (f (w₁ • lam)) := by
    have : g • (w₁ • lam) = w₂ • lam := by simp [g, ← mul_smul]
    rw [← this, hT]
  have hg₂ : f (w₁ • lam) = T' (f (w₂ • lam)) := by
    have : g⁻¹ • (w₂ • lam) = w₁ • lam := by simp [g, ← mul_smul]
    rw [← this, hT']
  by_cases h₁ : f (w₁ • lam) = 0
  · rw [hg₁, h₁, map_zero]
  by_cases h₂ : f (w₂ • lam) = 0
  · rw [hg₂, h₂, map_zero]
  obtain ⟨r, hr, hrv⟩ := hsame.exists_pos_left h₁ h₂
  have hpow (n : ℕ) : f (g ^ n • (w₁ • lam)) = r ^ n • f (w₁ • lam) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul, hT, ih, map_smul, ← hg₁, ← hrv, smul_smul, ← pow_succ]
  have hord := hpow (orderOf g)
  rw [pow_orderOf_eq_one, one_smul] at hord
  have hrpow : r ^ orderOf g = 1 :=
    smul_left_injective 𝕜 h₁ (by simpa only [one_smul] using hord.symm)
  have hr1 : r = 1 := (pow_eq_one_iff_of_nonneg hr.le (orderOf_pos g).ne').mp hrpow
  rw [← hrv, hr1, one_smul]

/-- Range-indexed form of `RootPairing.pairwise_not_sameRay_image_orbit_weylGroup`: no two distinct
points of `{f (w • λ) | w ∈ W}` lie in the same ray. -/
theorem pairwise_not_sameRay_range_smul [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (b : P.Base) [Finite ι] [P.IsReduced] {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  simpa only [MulAction.orbit, ← Set.range_comp, Function.comp_def] using
    P.pairwise_not_sameRay_image_orbit_weylGroup b hF lam

end Realization

end RootPairing
