/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Bochner integration and product dilations for additive Haar measures

Composing a function on a finite-dimensional real normed space with a continuous linear
automorphism `e : E ≃L[ℝ] E` preserves integrability between any set `s` and its image `e '' s`,
and multiplies the set integral against any additive Haar measure by `|det e|⁻¹`
(`MeasureTheory.Measure.integrableOn_comp_continuousLinearEquiv_iff`,
`MeasureTheory.Measure.setIntegral_comp_continuousLinearEquiv`,
`MeasureTheory.Measure.integral_comp_continuousLinearEquiv`). Unlike the general nonlinear
Jacobian formula `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`, no measurability
hypothesis on `s` is needed because `e` is a homeomorphism.

On a product `E × N` of finite-dimensional real normed spaces, the partial scalar multiplication
`(x, y) ↦ (x, a • y)` has determinant `a ^ finrank ℝ N`, so it multiplies every additive Haar
measure on `E × N` by `|a| ^ finrank ℝ N` on images (`addHaar_image_prod_smul_right`) and, when
`a ≠ 0`, rescales pushforwards and set integrals by `(|a| ^ finrank ℝ N)⁻¹`
(`map_addHaar_prod_smul_right`, `integrableOn_comp_prod_smul_right_iff`,
`setIntegral_comp_prod_smul_right`), and symmetrically in the first factor.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

section LinearEquiv

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Precomposing with a continuous linear automorphism `e` preserves `IntegrableOn` between any
set `s` and its image `e '' s` for any additive Haar measure. -/
theorem integrableOn_comp_continuousLinearEquiv_iff [TopologicalSpace G] [ESeminormedAddMonoid G]
    (e : E ≃L[ℝ] E) {g : E → G} {s : Set E} :
    IntegrableOn (fun x ↦ g (e x)) s μ ↔ IntegrableOn g (e '' s) μ := by
  have hdet : LinearMap.det (e : E →ₗ[ℝ] E) ≠ 0 := e.toLinearEquiv.isUnit_det'.ne_zero
  have hmap : μ.map e = ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| • μ :=
    map_linearMap_addHaar_eq_smul_addHaar μ hdet
  have hpos : ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| ≠ 0 :=
    ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hdet)) |>.ne'
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  nth_rw 1 [← Set.preimage_image_eq s e.injective]
  rw [← Function.comp_def, ← he.integrableOn_map_iff, IntegrableOn, hmap, restrict_smul,
    integrable_smul_measure hpos ENNReal.ofReal_ne_top]
  rfl

/-- Change of variables in a set integral along a continuous linear automorphism `e`: for any set
`s` and any additive Haar measure `μ`, `∫_s g(e x) dμ = |det e|⁻¹ • ∫_{e '' s} g dμ`. -/
theorem setIntegral_comp_continuousLinearEquiv [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃L[ℝ] E) (g : E → G) (s : Set E) :
    ∫ x in s, g (e x) ∂μ = |LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ • ∫ y in e '' s, g y ∂μ := by
  have hdet : LinearMap.det (e : E →ₗ[ℝ] E) ≠ 0 := e.toLinearEquiv.isUnit_det'.ne_zero
  have hmap : μ.map e = ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| • μ :=
    map_linearMap_addHaar_eq_smul_addHaar μ hdet
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  nth_rw 1 [← Set.preimage_image_eq s e.injective]
  rw [← he.setIntegral_map, hmap, restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

/-- Change of variables in a total Bochner integral along a continuous linear automorphism `e`:
`∫ g(e x) dμ = |det e|⁻¹ • ∫ g dμ`. -/
theorem integral_comp_continuousLinearEquiv [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃L[ℝ] E) (g : E → G) :
    ∫ x, g (e x) ∂μ = |LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ • ∫ y, g y ∂μ := by
  simpa [Set.image_univ_of_surjective e.surjective] using
    setIntegral_comp_continuousLinearEquiv μ e g Set.univ

end LinearEquiv

section ProdSmul

private theorem det_toLinearMap_prodMap_id_smul {E N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (a : ℝ) :
    LinearMap.det
      (((ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ N) :
        (E × N) →L[ℝ] E × N) : E × N →ₗ[ℝ] E × N) =
      a ^ Module.finrank ℝ N := by
  rw [ContinuousLinearMap.coe_prodMap, ContinuousLinearMap.coe_id,
    ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.coe_id, LinearMap.det_prodMap,
    LinearMap.det_id, one_mul, LinearMap.det_smul, LinearMap.det_id, mul_one]

private theorem det_toLinearMap_prodMap_smul_id {E N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (a : ℝ) :
    LinearMap.det
      (((a • ContinuousLinearMap.id ℝ E).prodMap (ContinuousLinearMap.id ℝ N) :
        (E × N) →L[ℝ] E × N) : E × N →ₗ[ℝ] E × N) =
      a ^ Module.finrank ℝ E := by
  rw [ContinuousLinearMap.coe_prodMap, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_id, ContinuousLinearMap.coe_id, LinearMap.det_prodMap,
    LinearMap.det_id, mul_one, LinearMap.det_smul, LinearMap.det_id, mul_one]

variable {E N G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup N] [NormedSpace ℝ N]
  [FiniteDimensional ℝ N] [MeasurableSpace N] [BorelSpace N]
  (μ : Measure (E × N)) [μ.IsAddHaarMeasure]

/-- Partial scalar multiplication `(x, y) ↦ (x, a • y)` in the second factor multiplies every
additive Haar measure on `E × N` by `|a| ^ finrank ℝ N`, for all `a : ℝ` (including `a = 0`). -/
theorem addHaar_image_prod_smul_right (a : ℝ) (s : Set (E × N)) :
    μ ((fun p : E × N ↦ (p.1, a • p.2)) '' s) =
      ENNReal.ofReal (|a| ^ Module.finrank ℝ N) * μ s := by
  have hcoe : ⇑((ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ N)) =
      fun p : E × N ↦ (p.1, a • p.2) := rfl
  rw [← hcoe, μ.addHaar_image_continuousLinearMap, det_toLinearMap_prodMap_id_smul, abs_pow]

/-- Partial scalar multiplication `(x, y) ↦ (a • x, y)` in the first factor multiplies every
additive Haar measure on `E × N` by `|a| ^ finrank ℝ E`, for all `a : ℝ` (including `a = 0`). -/
theorem addHaar_image_prod_smul_left (a : ℝ) (s : Set (E × N)) :
    μ ((fun p : E × N ↦ (a • p.1, p.2)) '' s) =
      ENNReal.ofReal (|a| ^ Module.finrank ℝ E) * μ s := by
  have hcoe : ⇑((a • ContinuousLinearMap.id ℝ E).prodMap (ContinuousLinearMap.id ℝ N)) =
      fun p : E × N ↦ (a • p.1, p.2) := rfl
  rw [← hcoe, μ.addHaar_image_continuousLinearMap, det_toLinearMap_prodMap_smul_id, abs_pow]

/-- For `a ≠ 0`, pushing an additive Haar measure on `E × N` forward along `(x, y) ↦ (x, a • y)`
rescales it by `(|a| ^ finrank ℝ N)⁻¹`. -/
theorem map_addHaar_prod_smul_right {a : ℝ} (ha : a ≠ 0) :
    μ.map (fun p : E × N ↦ (p.1, a • p.2)) =
      ENNReal.ofReal (|a| ^ Module.finrank ℝ N)⁻¹ • μ := by
  let S : (E × N) →L[ℝ] E × N :=
    (ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ N)
  have hcoe : ⇑(S : E × N →ₗ[ℝ] E × N) = fun p : E × N ↦ (p.1, a • p.2) := rfl
  have hdet : LinearMap.det (S : E × N →ₗ[ℝ] E × N) = a ^ Module.finrank ℝ N :=
    det_toLinearMap_prodMap_id_smul a
  rw [← hcoe, map_linearMap_addHaar_eq_smul_addHaar μ (by rw [hdet]; exact pow_ne_zero _ ha), hdet,
    abs_inv, abs_pow]

/-- For `a ≠ 0`, pushing an additive Haar measure on `E × N` forward along `(x, y) ↦ (a • x, y)`
rescales it by `(|a| ^ finrank ℝ E)⁻¹`. -/
theorem map_addHaar_prod_smul_left {a : ℝ} (ha : a ≠ 0) :
    μ.map (fun p : E × N ↦ (a • p.1, p.2)) =
      ENNReal.ofReal (|a| ^ Module.finrank ℝ E)⁻¹ • μ := by
  let S : (E × N) →L[ℝ] E × N :=
    (a • ContinuousLinearMap.id ℝ E).prodMap (ContinuousLinearMap.id ℝ N)
  have hcoe : ⇑(S : E × N →ₗ[ℝ] E × N) = fun p : E × N ↦ (a • p.1, p.2) := rfl
  have hdet : LinearMap.det (S : E × N →ₗ[ℝ] E × N) = a ^ Module.finrank ℝ E :=
    det_toLinearMap_prodMap_smul_id a
  rw [← hcoe, map_linearMap_addHaar_eq_smul_addHaar μ (by rw [hdet]; exact pow_ne_zero _ ha), hdet,
    abs_inv, abs_pow]

/-- For `a ≠ 0`, `(x, y) ↦ g (x, a • y)` is integrable on `s` against an additive Haar measure on
`E × N` if and only if `g` is integrable on `(fun p ↦ (p.1, a • p.2)) '' s`. -/
theorem integrableOn_comp_prod_smul_right_iff [TopologicalSpace G] [ESeminormedAddMonoid G]
    {a : ℝ} (ha : a ≠ 0) {g : E × N → G} {s : Set (E × N)} :
    IntegrableOn (fun p : E × N ↦ g (p.1, a • p.2)) s μ ↔
      IntegrableOn g ((fun p : E × N ↦ (p.1, a • p.2)) '' s) μ := by
  let S : (E × N) →L[ℝ] E × N :=
    (ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ N)
  have hdet : S.det ≠ 0 := by
    rw [ContinuousLinearMap.det, det_toLinearMap_prodMap_id_smul]
    exact pow_ne_zero _ ha
  have hcoe : ⇑(S.toContinuousLinearEquivOfDetNeZero hdet) = fun p : E × N ↦ (p.1, a • p.2) := by
    ext p <;> simp [S]
  have h := integrableOn_comp_continuousLinearEquiv_iff μ
    (S.toContinuousLinearEquivOfDetNeZero hdet) (g := g) (s := s)
  rwa [hcoe] at h

/-- For `a ≠ 0`, `(x, y) ↦ g (a • x, y)` is integrable on `s` against an additive Haar measure on
`E × N` if and only if `g` is integrable on `(fun p ↦ (a • p.1, p.2)) '' s`. -/
theorem integrableOn_comp_prod_smul_left_iff [TopologicalSpace G] [ESeminormedAddMonoid G]
    {a : ℝ} (ha : a ≠ 0) {g : E × N → G} {s : Set (E × N)} :
    IntegrableOn (fun p : E × N ↦ g (a • p.1, p.2)) s μ ↔
      IntegrableOn g ((fun p : E × N ↦ (a • p.1, p.2)) '' s) μ := by
  let S : (E × N) →L[ℝ] E × N :=
    (a • ContinuousLinearMap.id ℝ E).prodMap (ContinuousLinearMap.id ℝ N)
  have hdet : S.det ≠ 0 := by
    rw [ContinuousLinearMap.det, det_toLinearMap_prodMap_smul_id]
    exact pow_ne_zero _ ha
  have hcoe : ⇑(S.toContinuousLinearEquivOfDetNeZero hdet) = fun p : E × N ↦ (a • p.1, p.2) := by
    ext p <;> simp [S]
  have h := integrableOn_comp_continuousLinearEquiv_iff μ
    (S.toContinuousLinearEquivOfDetNeZero hdet) (g := g) (s := s)
  rwa [hcoe] at h

/-- For `a ≠ 0`, integrating `g (x, a • y)` over `s` against an additive Haar measure on `E × N`
multiplies the integral of `g` over `(fun p ↦ (p.1, a • p.2)) '' s` by `(|a| ^ finrank ℝ N)⁻¹`. -/
theorem setIntegral_comp_prod_smul_right [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a : ℝ} (ha : a ≠ 0) (g : E × N → G) (s : Set (E × N)) :
    ∫ p in s, g (p.1, a • p.2) ∂μ =
      (|a| ^ Module.finrank ℝ N)⁻¹ • ∫ q in (fun p : E × N ↦ (p.1, a • p.2)) '' s, g q ∂μ := by
  let S : (E × N) →L[ℝ] E × N :=
    (ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ N)
  have hdet : S.det ≠ 0 := by
    rw [ContinuousLinearMap.det, det_toLinearMap_prodMap_id_smul]
    exact pow_ne_zero _ ha
  have hcoe : ⇑(S.toContinuousLinearEquivOfDetNeZero hdet) = fun p : E × N ↦ (p.1, a • p.2) := by
    ext p <;> simp [S]
  have hlin :
      ((S.toContinuousLinearEquivOfDetNeZero hdet : (E × N) ≃L[ℝ] E × N) : E × N →ₗ[ℝ] E × N) =
        (S : E × N →ₗ[ℝ] E × N) := by
    ext p <;> simp [S]
  have h := setIntegral_comp_continuousLinearEquiv μ
    (S.toContinuousLinearEquivOfDetNeZero hdet) g s
  rwa [hcoe, hlin, det_toLinearMap_prodMap_id_smul, abs_pow] at h

/-- For `a ≠ 0`, integrating `g (a • x, y)` over `s` against an additive Haar measure on `E × N`
multiplies the integral of `g` over `(fun p ↦ (a • p.1, p.2)) '' s` by `(|a| ^ finrank ℝ E)⁻¹`. -/
theorem setIntegral_comp_prod_smul_left [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a : ℝ} (ha : a ≠ 0) (g : E × N → G) (s : Set (E × N)) :
    ∫ p in s, g (a • p.1, p.2) ∂μ =
      (|a| ^ Module.finrank ℝ E)⁻¹ • ∫ q in (fun p : E × N ↦ (a • p.1, p.2)) '' s, g q ∂μ := by
  let S : (E × N) →L[ℝ] E × N :=
    (a • ContinuousLinearMap.id ℝ E).prodMap (ContinuousLinearMap.id ℝ N)
  have hdet : S.det ≠ 0 := by
    rw [ContinuousLinearMap.det, det_toLinearMap_prodMap_smul_id]
    exact pow_ne_zero _ ha
  have hcoe : ⇑(S.toContinuousLinearEquivOfDetNeZero hdet) = fun p : E × N ↦ (a • p.1, p.2) := by
    ext p <;> simp [S]
  have hlin :
      ((S.toContinuousLinearEquivOfDetNeZero hdet : (E × N) ≃L[ℝ] E × N) : E × N →ₗ[ℝ] E × N) =
        (S : E × N →ₗ[ℝ] E × N) := by
    ext p <;> simp [S]
  have h := setIntegral_comp_continuousLinearEquiv μ
    (S.toContinuousLinearEquivOfDetNeZero hdet) g s
  rwa [hcoe, hlin, det_toLinearMap_prodMap_smul_id, abs_pow] at h

end ProdSmul

end MeasureTheory.Measure
