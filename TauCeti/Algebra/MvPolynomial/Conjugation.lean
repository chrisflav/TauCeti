/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import TauCeti.LinearAlgebra.Complex.Conjugation
public import TauCeti.RingTheory.TensorProduct.MvPolynomial

/-!
# Coefficient conjugation, star evaluation, and real descent of multivariate polynomials

Changing coefficients of multivariate polynomials along `f : R →+* S` is `f`-semilinear
(`MvPolynomial.mapₛₗ`). Over a commutative star semiring `R`, coefficient conjugation is the
involutive ring endomorphism `MvPolynomial.map (starRingEnd R)`. No global `Star` instance is
registered on `MvPolynomial σ R`: polynomial rings in complex analysis and variational field theory
also carry conjugations that permute paired holomorphic/antiholomorphic or field/conjugate-field
generators rather than fixing every indeterminate.

Evaluating a multivariate polynomial in a commutative star `R`-algebra `A` commutes with `star`
after conjugating both the coefficients and the assigned coordinates (`MvPolynomial.star_aeval`).
When `R` has trivial star (for instance `ℝ` acting on a complex star algebra), evaluation commutes
with `star` by conjugating the coordinates alone (`MvPolynomial.star_aeval_of_trivialStar`).

Over `ℝ` and `ℂ`, Mathlib's complexification isomorphism
`MvPolynomial.algebraTensorAlgEquiv ℝ ℂ : ℂ ⊗[ℝ] MvPolynomial σ ℝ ≃ₐ[ℂ] MvPolynomial σ ℂ` and its
variable-restricted counterpart `MvPolynomial.supportedAlgebraTensorAlgEquiv` intertwine tensor
conjugation `TauCeti.tmulConj` with `MvPolynomial.map (starRingEnd ℂ)`. Consequently, the
polynomials over `ℂ` fixed by coefficient conjugation are precisely those with real coefficients,
equivalently the image of `MvPolynomial σ ℝ`.

## Main definitions

* `MvPolynomial.mapₛₗ`: `MvPolynomial.map f` bundled as an `f`-semilinear map.

## Main statements

* `MvPolynomial.map_smul`: `map f (r • p) = f r • map f p`.
* `MvPolynomial.map_starRingEnd_map_starRingEnd` and `MvPolynomial.map_starRingEnd_involutive`:
  coefficient conjugation is involutive over any commutative star semiring.
* `MvPolynomial.star_aeval`, `MvPolynomial.star_aeval_of_trivialStar`, `MvPolynomial.star_eval`:
  compatibility of `star` with polynomial evaluation.
* `MvPolynomial.algebraTensorAlgEquiv_tmulConj`,
  `MvPolynomial.conjugationOfComplexification_algebraTensorAlgEquiv`, and
  `MvPolynomial.coe_supportedAlgebraTensorAlgEquiv_tmulConj`: complexification intertwines
  `TauCeti.tmulConj` with `MvPolynomial.map (starRingEnd ℂ)`.
* `MvPolynomial.map_starRingEnd_complex_eq_self_iff` and
  `MvPolynomial.map_starRingEnd_complex_eq_self_iff_exists_real`: characterizations of the fixed
  locus of coefficient conjugation over `ℂ`.
-/

public section

open scoped TensorProduct

namespace MvPolynomial

section Semilinear

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S]

@[simp]
theorem map_smul (f : R →+* S) (r : R) (p : MvPolynomial σ R) :
    map f (r • p) = f r • map f p := by
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]

variable (σ) in
/-- `MvPolynomial.map f` bundled as an `f`-semilinear map. -/
noncomputable def mapₛₗ (f : R →+* S) : MvPolynomial σ R →ₛₗ[f] MvPolynomial σ S where
  toFun := map f
  map_add' := map_add (map f)
  map_smul' := map_smul f

@[simp]
theorem coe_mapₛₗ (f : R →+* S) : ⇑(mapₛₗ σ f) = ⇑(map f) := (rfl)

theorem mapₛₗ_apply (f : R →+* S) (p : MvPolynomial σ R) : mapₛₗ σ f p = map f p := (rfl)

end Semilinear

section StarRing

variable {σ R A : Type*} [CommSemiring R] [StarRing R]

@[simp]
theorem map_starRingEnd_map_starRingEnd (p : MvPolynomial σ R) :
    map (starRingEnd R) (map (starRingEnd R) p) = p := by
  have h : (starRingEnd R).comp (starRingEnd R) = RingHom.id R := RingHom.ext star_star
  rw [map_map, h, map_id]

theorem map_starRingEnd_involutive :
    Function.Involutive (map (starRingEnd R) : MvPolynomial σ R →+* MvPolynomial σ R) :=
  map_starRingEnd_map_starRingEnd

theorem mapₛₗ_starRingEnd_involutive :
    Function.Involutive (mapₛₗ σ (starRingEnd R)) :=
  map_starRingEnd_map_starRingEnd

@[simp]
theorem vars_map_starRingEnd (p : MvPolynomial σ R) :
    (map (starRingEnd R) p).vars = p.vars :=
  p.vars_map_of_injective (Function.Involutive.injective starRingEnd_self_apply)

@[simp]
theorem map_starRingEnd_mem_supported_iff {s : Set σ} {p : MvPolynomial σ R} :
    map (starRingEnd R) p ∈ supported R s ↔ p ∈ supported R s :=
  map_mem_supported_iff (Function.Involutive.injective starRingEnd_self_apply)

@[simp]
theorem map_starRingEnd_of_trivialStar [TrivialStar R] (p : MvPolynomial σ R) :
    map (starRingEnd R) p = p := by
  have h : starRingEnd R = RingHom.id R := RingHom.ext star_trivial
  rw [h, map_id]

/-- Evaluating a multivariate polynomial in a commutative star `R`-algebra and applying `star`
conjugates both the coefficients and the assigned coordinates. -/
theorem star_aeval [CommSemiring A] [StarRing A] [Algebra R A] [StarModule R A]
    (f : σ → A) (p : MvPolynomial σ R) :
    star (aeval f p) = aeval (fun i ↦ star (f i)) (map (starRingEnd R) p) := by
  have halg : (starRingEnd A).comp (algebraMap R A) =
      (algebraMap R A).comp (starRingEnd R) :=
    RingHom.ext fun r ↦ (algebraMap_star_comm r).symm
  rw [← starRingEnd_apply (R := A), aeval_def, eval₂_comp_right, eval₂_map, halg, ← eval₂_map,
    ← aeval_def]
  rfl

/-- Over a scalar semiring with trivial star, `star` of `MvPolynomial.aeval` conjugates only the
assigned coordinates. -/
theorem star_aeval_of_trivialStar [TrivialStar R] [CommSemiring A] [StarRing A] [Algebra R A]
    [StarModule R A] (f : σ → A) (p : MvPolynomial σ R) :
    star (aeval f p) = aeval (fun i ↦ star (f i)) p := by
  rw [star_aeval, map_starRingEnd_of_trivialStar]

/-- Applying `star` to `MvPolynomial.eval` conjugates both coefficients and coordinates. -/
theorem star_eval (f : σ → R) (p : MvPolynomial σ R) :
    star (eval f p) = eval (fun i ↦ star (f i)) (map (starRingEnd R) p) :=
  map_eval (starRingEnd R) f p

end StarRing

section Complex

variable {σ : Type*}

private theorem starRingEnd_comp_algebraMap_real_complex :
    (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = algebraMap ℝ ℂ :=
  RingHom.ext Complex.conj_ofReal

/-- Complexifying `MvPolynomial σ ℝ` intertwines tensor conjugation `TauCeti.tmulConj` with
coefficient conjugation `MvPolynomial.map (starRingEnd ℂ)`. -/
@[simp]
theorem algebraTensorAlgEquiv_tmulConj (u : ℂ ⊗[ℝ] MvPolynomial σ ℝ) :
    algebraTensorAlgEquiv ℝ ℂ (TauCeti.tmulConj (MvPolynomial σ ℝ) u) =
      map (starRingEnd ℂ) (algebraTensorAlgEquiv ℝ ℂ u) := by
  induction u using TensorProduct.inductionOn with
  | tmul c p =>
    rw [TauCeti.tmulConj_tmul, algebraTensorAlgEquiv_tmul, algebraTensorAlgEquiv_tmul, map_smul,
      map_map, starRingEnd_comp_algebraMap_real_complex]
  | add x y hx hy => simp [hx, hy]

@[simp]
theorem algebraTensorAlgEquiv_symm_map_starRingEnd (p : MvPolynomial σ ℂ) :
    (algebraTensorAlgEquiv ℝ ℂ).symm (map (starRingEnd ℂ) p) =
      TauCeti.tmulConj (MvPolynomial σ ℝ) ((algebraTensorAlgEquiv ℝ ℂ).symm p) := by
  apply (algebraTensorAlgEquiv ℝ ℂ).injective
  simp

/-- Transporting tensor conjugation along `MvPolynomial.algebraTensorAlgEquiv ℝ ℂ` yields
`MvPolynomial.mapₛₗ σ (starRingEnd ℂ)`. -/
theorem conjugationOfComplexification_algebraTensorAlgEquiv :
    LinearEquiv.conjugationOfComplexification (algebraTensorAlgEquiv (σ := σ) ℝ ℂ).toLinearEquiv =
      mapₛₗ σ (starRingEnd ℂ) :=
  (LinearEquiv.conjugationOfComplexification_unique _ _ fun q ↦ by
    simp [map_map, starRingEnd_comp_algebraMap_real_complex]).symm

/-- Complexifying `MvPolynomial.supported ℝ s` intertwines `TauCeti.tmulConj` with coefficient
conjugation on the ambient polynomial algebra. -/
@[simp]
theorem coe_supportedAlgebraTensorAlgEquiv_tmulConj (s : Set σ)
    (u : ℂ ⊗[ℝ] supported ℝ s) :
    (supportedAlgebraTensorAlgEquiv ℝ ℂ s (TauCeti.tmulConj (supported ℝ s) u) :
      MvPolynomial σ ℂ) =
      map (starRingEnd ℂ) (supportedAlgebraTensorAlgEquiv ℝ ℂ s u) := by
  induction u using TensorProduct.inductionOn with
  | tmul c p =>
    rw [TauCeti.tmulConj_tmul, coe_supportedAlgebraTensorAlgEquiv_tmul,
      coe_supportedAlgebraTensorAlgEquiv_tmul, map_smul, map_map,
      starRingEnd_comp_algebraMap_real_complex]
  | add x y hx hy => simp [hx, hy]

/-- A complex multivariate polynomial is fixed by coefficient conjugation if and only if every
coefficient has zero imaginary part. -/
theorem map_starRingEnd_complex_eq_self_iff (p : MvPolynomial σ ℂ) :
    map (starRingEnd ℂ) p = p ↔ ∀ m, (p.coeff m).im = 0 := by
  rw [MvPolynomial.ext_iff]
  refine forall_congr' fun m ↦ ?_
  rw [coeff_map, Complex.conj_eq_iff_im]

/-- A complex multivariate polynomial is fixed by coefficient conjugation if and only if it is the
image of a real multivariate polynomial. -/
theorem map_starRingEnd_complex_eq_self_iff_exists_real (p : MvPolynomial σ ℂ) :
    map (starRingEnd ℂ) p = p ↔ ∃ q : MvPolynomial σ ℝ, map (algebraMap ℝ ℂ) q = p := by
  have h := LinearEquiv.conjugationOfComplexification_eq_self_iff
    (algebraTensorAlgEquiv (σ := σ) ℝ ℂ).toLinearEquiv p
  rw [conjugationOfComplexification_algebraTensorAlgEquiv, coe_mapₛₗ] at h
  simpa using h

end Complex

end MvPolynomial
