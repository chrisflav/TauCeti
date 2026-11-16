/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.ExteriorPower

/-!
# Group representations on spaces of alternating maps

Given representations `ρ₁ : Representation R G M` and `ρ₂ : Representation R G N` of a group `G`,
the contragredient action on alternating maps `M [⋀^ι]→ₗ[R] N` is defined by
`(ρ₁.alternatingMap ρ₂ ι g ω) v = ρ₂ g (ω (fun i ↦ ρ₁ g⁻¹ (v i)))`.

In finite degree `Fin n`, `exteriorPower.alternatingMapLinearEquiv` identifies this representation
with `Representation.linHom (ρ₁.exteriorPower n) ρ₂`
(`Representation.alternatingMapEquivLinHom`), and hence identifies `G`-invariant alternating maps
with intertwining maps `⋀[R]^n M → N`
(`Representation.alternatingMapInvariantsEquivIntertwiningMap`).

## Main definitions

* `Representation.alternatingMap`: the contragredient representation on `M [⋀^ι]→ₗ[R] N`.
* `Representation.alternatingMapEquivLinHom`: equivalence with `linHom (ρ₁.exteriorPower n) ρ₂`.
* `Representation.alternatingMapInvariantsEquivIntertwiningMap`: identification of invariant
  alternating maps with `IntertwiningMap (ρ₁.exteriorPower n) ρ₂`.

## Main results

* `Representation.alternatingMap_apply`: evaluation formula for the action.
* `Representation.alternatingMap_curryLeft`: equivariance of interior products.
* `Representation.alternatingMap_compLinearMap`: equivariance of pullback along an intertwining map.
-/

public section

namespace Representation

section CommSemiring

variable {R G M N ι : Type*} [CommSemiring R] [Group G]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The contragredient representation of `G` on `M [⋀^ι]→ₗ[R] N` induced by representations `ρ₁` on
`M` and `ρ₂` on `N`: `(g • ω) v = ρ₂ g (ω (fun i ↦ ρ₁ g⁻¹ (v i)))`. -/
def alternatingMap (ρ₁ : Representation R G M) (ρ₂ : Representation R G N) (ι : Type*) :
    Representation R G (M [⋀^ι]→ₗ[R] N) where
  toFun g :=
    { toFun ω := (ρ₂ g).compAlternatingMap (ω.compLinearMap (ρ₁ g⁻¹))
      map_add' ω₁ ω₂ := by ext v; simp
      map_smul' r ω := by ext v; simp }
  map_one' := by
    ext ω v
    simp
  map_mul' g h := by
    ext ω v
    simp [mul_inv_rev]

/-- Evaluating the contragredient action on an alternating map. -/
@[simp]
theorem alternatingMap_apply (ρ₁ : Representation R G M) (ρ₂ : Representation R G N) (ι : Type*)
    (g : G) (ω : M [⋀^ι]→ₗ[R] N) (v : ι → M) :
    ρ₁.alternatingMap ρ₂ ι g ω v = ρ₂ g (ω fun i ↦ ρ₁ g⁻¹ (v i)) :=
  (rfl)

/-- Interior products are equivariant for the contragredient action on alternating maps. -/
theorem alternatingMap_curryLeft {n : ℕ} (ρ₁ : Representation R G M) (ρ₂ : Representation R G N)
    (g : G) (ω : M [⋀^Fin (n + 1)]→ₗ[R] N) (x : M) :
    (ρ₁.alternatingMap ρ₂ (Fin (n + 1)) g ω).curryLeft x =
      ρ₁.alternatingMap ρ₂ (Fin n) g (ω.curryLeft (ρ₁ g⁻¹ x)) := by
  ext v
  simp only [AlternatingMap.curryLeft_apply_apply, alternatingMap_apply]
  congr 2
  ext i
  refine Fin.cases ?_ ?_ i <;> simp

/-- Pulling back along a `G`-equivariant linear map intertwines the alternating-map actions. -/
theorem alternatingMap_compLinearMap {M' : Type*} [AddCommMonoid M'] [Module R M']
    {ρ₁' : Representation R G M'} {ρ₁ : Representation R G M} (ρ₂ : Representation R G N)
    (f : M' →ₗ[R] M) (hf : ∀ g x, f (ρ₁' g x) = ρ₁ g (f x)) (g : G) (ω : M [⋀^ι]→ₗ[R] N) :
    (ρ₁.alternatingMap ρ₂ ι g ω).compLinearMap f =
      ρ₁'.alternatingMap ρ₂ ι g (ω.compLinearMap f) := by
  ext v
  simp [hf]

end CommSemiring

section CommRing

variable {R G M N : Type*} [CommRing R] [Group G]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- In finite degree `Fin n`, `exteriorPower.alternatingMapLinearEquiv` identifies the
contragredient representation on `M [⋀^Fin n]→ₗ[R] N` with
`Representation.linHom (ρ₁.exteriorPower n) ρ₂`. -/
noncomputable def alternatingMapEquivLinHom (ρ₁ : Representation R G M)
    (ρ₂ : Representation R G N) (n : ℕ) :
    (ρ₁.alternatingMap ρ₂ (Fin n)).Equiv ((ρ₁.exteriorPower n).linHom ρ₂) :=
  .mk exteriorPower.alternatingMapLinearEquiv fun g ↦ by
    ext ω v
    simp [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Function.comp_def]

/-- The underlying linear equivalence of `alternatingMapEquivLinHom` is
`exteriorPower.alternatingMapLinearEquiv`. -/
@[simp]
theorem alternatingMapEquivLinHom_toLinearEquiv (ρ₁ : Representation R G M)
    (ρ₂ : Representation R G N) (n : ℕ) :
    (ρ₁.alternatingMapEquivLinHom ρ₂ n).toLinearEquiv = exteriorPower.alternatingMapLinearEquiv :=
  (rfl)

/-- `G`-invariant alternating maps `M [⋀^Fin n]→ₗ[R] N` correspond linearly to intertwining maps
`⋀[R]^n M → N` from the `n`-th exterior power of `ρ₁` to `ρ₂`. -/
noncomputable def alternatingMapInvariantsEquivIntertwiningMap (ρ₁ : Representation R G M)
    (ρ₂ : Representation R G N) (n : ℕ) :
    (ρ₁.alternatingMap ρ₂ (Fin n)).invariants ≃ₗ[R]
      IntertwiningMap (ρ₁.exteriorPower n) ρ₂ :=
  (LinearEquiv.ofSubmodules (ρ₁.alternatingMapEquivLinHom ρ₂ n).toLinearEquiv _ _ (by
    ext f
    simp only [Submodule.mem_map, mem_invariants]
    refine ⟨?_, fun hf ↦ ?_⟩
    · rintro ⟨ω, hω, rfl⟩ g
      have hcomm := LinearMap.congr_fun ((ρ₁.alternatingMapEquivLinHom ρ₂ n).isIntertwining' g) ω
      simpa [hω g] using hcomm.symm
    · refine ⟨(ρ₁.alternatingMapEquivLinHom ρ₂ n).symm f, fun g ↦ ?_, by simp⟩
      apply (ρ₁.alternatingMapEquivLinHom ρ₂ n).injective
      have hcomm := LinearMap.congr_fun ((ρ₁.alternatingMapEquivLinHom ρ₂ n).isIntertwining' g)
        ((ρ₁.alternatingMapEquivLinHom ρ₂ n).symm f)
      simp only [LinearMap.comp_apply, Equiv.coe_toLinearMap, Equiv.apply_symm_apply] at hcomm
      exact hcomm.trans ((hf g).trans
        ((ρ₁.alternatingMapEquivLinHom ρ₂ n).toLinearEquiv.apply_symm_apply f).symm))).trans
    (invariantsEquivIntertwiningMap (ρ₁.exteriorPower n) ρ₂)

/-- Evaluating the intertwining map attached to an invariant alternating map on a pure wedge. -/
@[simp]
theorem alternatingMapInvariantsEquivIntertwiningMap_apply_ιMulti (ρ₁ : Representation R G M)
    (ρ₂ : Representation R G N) (n : ℕ) (ω : (ρ₁.alternatingMap ρ₂ (Fin n)).invariants)
    (v : Fin n → M) :
    ρ₁.alternatingMapInvariantsEquivIntertwiningMap ρ₂ n ω (exteriorPower.ιMulti R n v) =
      ω.1 v := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti ω.1 v

end CommRing

end Representation
