/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# Measures on the circle

This file defines the measure on `Circle` obtained from a nonnegative density on the unit circle
with respect to normalized arc length. For a circle-integrable density it is finite, and for a
measurable nonnegative density its integral is identified with Mathlib's `Real.circleAverage`.

It also records two general Fourier-moment properties of Borel measures on `Circle`: every
left-invariant measure integrates `(z : ℂ) ^ n` to its total mass at `n = 0` and to `0` at
`n ≠ 0`, and any finite Borel measure on `Circle` is determined by its integer power moments
`∫ z : Circle, (z : ℂ) ^ n ∂μ`.

## Main definitions and results

* `TauCeti.circleDensityMeasure`: normalized arc length weighted by a density.
* `TauCeti.isFiniteMeasure_circleDensityMeasure`: a circle-integrable density gives a finite
  measure.
* `TauCeti.integral_map_circleExp_of_restrict_Ioc`: integration against the pushforward along
  `Circle.exp` of a measure concentrated on `(a, a + 2π]`, for an arbitrary integrand.
* `TauCeti.integral_circleDensityMeasure`: for a nonnegative measurable density, integration
  against the weighted measure is a circle average.
* `TauCeti.circleAverage_sub_zpow`: the circle average of `(z - c) ^ n` is `1` for `n = 0` and
  `0` otherwise, the orthogonality relation of the characters of the circle.
* `MeasureTheory.integral_zpow_circle_of_isMulLeftInvariant`: against a left-invariant measure on
  `Circle`, the integral of `(z : ℂ) ^ n` is `(μ.real univ : ℂ)` for `n = 0` and `0` otherwise.
* `MeasureTheory.Measure.ext_of_forall_integral_zpow_eq`: a finite Borel measure on `Circle` is
  determined by its integer power moments `∫ z : Circle, (z : ℂ) ^ n ∂μ`.
-/

public section

noncomputable section

open Complex MeasureTheory Metric Real Set Filter
open scoped ENNReal

namespace TauCeti

/-- The measure on `Circle` with density `max φ 0` with respect to normalized arc length.

Negative values of `φ` are truncated to `0` by `ENNReal.ofReal`; for a nonnegative `φ` the density
is `φ` itself. -/
def circleDensityMeasure (φ : ℂ → ℝ) : Measure Circle :=
  ((volume.restrict (Ioc 0 (2 * π))).withDensity
    fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ))).map Circle.exp

/-- A measure on `Circle` given by a circle-integrable density with respect to normalized arc
length is finite. -/
theorem isFiniteMeasure_circleDensityMeasure {φ : ℂ → ℝ} (hφ : CircleIntegrable φ 0 1) :
    IsFiniteMeasure (circleDensityMeasure φ) := by
  have := isFiniteMeasure_withDensity_ofReal (hφ.1.const_mul (2 * π)⁻¹).hasFiniteIntegral
  unfold circleDensityMeasure
  infer_instance

/-- Integrating against the pushforward along `Circle.exp` of a measure on `ℝ` concentrated on an
interval `(a, a + 2π]` is integrating the composition with `Circle.exp`. No regularity is required
of the integrand `g`, since `Circle.exp` is a measurable embedding on that interval. -/
theorem integral_map_circleExp_of_restrict_Ioc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure ℝ} {a : ℝ} (hμ : μ.restrict (Ioc a (a + 2 * π)) = μ)
    (g : Circle → E) :
    ∫ z, g z ∂μ.map Circle.exp = ∫ θ, g (Circle.exp θ) ∂μ := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  have hexp : Circle.exp ∘ ((↑) : Ioc a (a + 2 * π) → ℝ) =
      AddCircle.homeomorphCircle' ∘ (AddCircle.measurableEquivIoc (2 * π) a).symm := by
    funext θ
    rw [Function.comp_apply, Function.comp_apply,
      (MeasurableEquiv.symm_apply_eq _).2 (AddCircle.equivIoc_coe_eq θ.2).symm,
      AddCircle.homeomorphCircle'_apply_mk]
  have he : MeasurableEmbedding (Circle.exp ∘ ((↑) : Ioc a (a + 2 * π) → ℝ)) := hexp ▸
    AddCircle.homeomorphCircle'.toMeasurableEquiv.measurableEmbedding.comp
      (AddCircle.measurableEquivIoc (2 * π) a).symm.measurableEmbedding
  have hμ' : (μ.comap Subtype.val).map ((↑) : Ioc a (a + 2 * π) → ℝ) = μ := by
    rw [map_comap_subtype_coe measurableSet_Ioc, hμ]
  calc ∫ z, g z ∂μ.map Circle.exp
      = ∫ z, g z ∂(μ.comap Subtype.val).map (Circle.exp ∘ ((↑) : Ioc a (a + 2 * π) → ℝ)) := by
        rw [← Measure.map_map Circle.exp.continuous.measurable measurable_subtype_coe, hμ']
    _ = ∫ θ, g (Circle.exp θ) ∂(μ.comap Subtype.val).map ((↑) : Ioc a (a + 2 * π) → ℝ) := by
        rw [he.integral_map, (MeasurableEmbedding.subtype_coe measurableSet_Ioc).integral_map]
        simp only [Function.comp_apply]
    _ = ∫ θ, g (Circle.exp θ) ∂μ := by rw [hμ']

/-- Integration against a measure on `Circle` with a nonnegative almost everywhere strongly
measurable density is the corresponding normalized circle average. No regularity is required of
the integrand `g`. -/
theorem integral_circleDensityMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℂ → ℝ}
    (hφ : AEStronglyMeasurable (fun θ ↦ φ (circleMap 0 1 θ)) (volume.restrict (Ioc 0 (2 * π))))
    (hφ₀ : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ φ z) (g : ℂ → E) :
    ∫ z : Circle, g z ∂circleDensityMeasure φ = circleAverage (fun ζ ↦ φ ζ • g ζ) 0 1 := by
  have hd : AEMeasurable (fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ)))
      (volume.restrict (Ioc 0 (2 * π))) :=
    (hφ.const_mul _).aemeasurable.ennreal_ofReal
  have hν : ((volume.restrict (Ioc 0 (2 * π))).withDensity
      fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ))).restrict (Ioc 0 (0 + 2 * π)) =
      (volume.restrict (Ioc 0 (2 * π))).withDensity
        fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ)) := by
    rw [zero_add, restrict_withDensity measurableSet_Ioc,
      Measure.restrict_restrict_of_subset subset_rfl]
  rw [circleDensityMeasure, integral_map_circleExp_of_restrict_Ioc hν (fun z ↦ g z),
    integral_withDensity_eq_integral_toReal_smul₀ hd
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top), circleAverage_def,
    intervalIntegral.integral_of_le (by positivity), ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun θ ↦ ?_)
  have h₀ : 0 ≤ (2 * π)⁻¹ * φ (circleMap 0 1 θ) :=
    mul_nonneg (by positivity) (hφ₀ _ (circleMap_mem_sphere 0 zero_le_one θ))
  simp only [ENNReal.toReal_ofReal h₀, smul_smul]
  simp [Circle.coe_exp, circleMap]

/-- **Orthogonality of the characters of the circle.** The normalized circle average of an
integer power `(z - c) ^ n` over a circle centred at `c` is `1` for `n = 0` and `0` otherwise. -/
@[simp] theorem circleAverage_sub_zpow {c : ℂ} {R : ℝ} (n : ℤ) :
    circleAverage (fun z ↦ (z - c) ^ n) c R = if n = 0 then 1 else 0 := by
  by_cases hR : R = 0
  · subst R
    simp only [circleAverage_zero, sub_self, zero_zpow_eq]
  split_ifs with hn
  · simp [hn, circleAverage_const]
  rw [← circleAverage_abs_radius, circleAverage_eq_circleIntegral (abs_ne_zero.mpr hR),
    circleIntegral.integral_congr (abs_nonneg R) (g := fun z ↦ (z - c) ^ (n - 1)) fun z hz ↦ ?_,
    circleIntegral.integral_sub_zpow_of_ne (by omega), smul_zero]
  have hz : z - c ≠ 0 := sub_ne_zero.mpr (ne_of_mem_sphere hz (abs_ne_zero.mpr hR))
  simp [zpow_sub_one₀ hz, mul_comm]

end TauCeti

namespace MeasureTheory

/-- Against any left-invariant Borel measure on `Circle`, the integral of `(z : ℂ) ^ n` is the
total mass `(μ.real univ : ℂ)` at `n = 0` and vanishes for `n ≠ 0`. -/
theorem integral_zpow_circle_of_isMulLeftInvariant {μ : Measure Circle} [μ.IsMulLeftInvariant]
    (n : ℤ) :
    ∫ z : Circle, (z : ℂ) ^ n ∂μ = if n = 0 then (μ.real univ : ℂ) else 0 := by
  split_ifs with hn
  · simp [hn, integral_const, Complex.real_smul]
  · have hw : ((Circle.exp (π / n) : Circle) : ℂ) ^ n ≠ 1 := by
      rw [← Circle.coe_zpow, ← Circle.exp_intCast_mul,
        mul_div_cancel₀ _ (Int.cast_ne_zero.mpr hn), Ne, Circle.coe_eq_one]
      exact Circle.exp_pi_ne_one
    have hinv := integral_mul_left_eq_self (μ := μ) (fun z : Circle ↦ (z : ℂ) ^ n)
      (Circle.exp (π / n))
    simp only [Circle.coe_mul, mul_zpow, integral_const_mul] at hinv
    exact (mul_eq_zero.mp (by linear_combination hinv)).resolve_left (sub_ne_zero.mpr hw)

open scoped CompactlySupported ComplexOrder in
/-- **Fourier moment determinacy on `Circle`.** Two finite Borel measures on `Circle` are equal as
soon as their integer power moments `∫ z : Circle, (z : ℂ) ^ n ∂μ` agree for every `n : ℤ`. -/
theorem Measure.ext_of_forall_integral_zpow_eq {μ ν : Measure Circle} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ n : ℤ, ∫ z : Circle, (z : ℂ) ^ n ∂μ = ∫ z : Circle, (z : ℂ) ^ n ∂ν) :
    μ = ν := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  let e : Circle ≃ₜ AddCircle (1 : ℝ) := (AddCircle.homeomorphCircle (T := 1) one_ne_zero).symm
  set μ' : Measure (AddCircle (1 : ℝ)) := μ.map e
  set ν' : Measure (AddCircle (1 : ℝ)) := ν.map e
  have hfourier (n : ℤ) (z : Circle) : fourier n (e z) = (z : ℂ) ^ n := by
    rw [fourier_apply, AddCircle.toCircle_zsmul, ← AddCircle.homeomorphCircle_apply one_ne_zero,
      Circle.coe_zpow]
    exact congrArg (fun w : Circle ↦ (w : ℂ) ^ n)
      ((AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z)
  have hmom (n : ℤ) : ∫ x, fourier n x ∂μ' = ∫ x, fourier n x ∂ν' := by
    rw [e.measurableEmbedding.integral_map, e.measurableEmbedding.integral_map]
    simpa only [hfourier] using h n
  -- The continuous functions on `AddCircle 1` whose `μ'`- and `ν'`-integrals agree form a closed
  -- submodule containing the Fourier characters, hence all of `C(AddCircle 1, ℂ)`.
  let S : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) :=
    (ContinuousMap.integralPositiveLinearMap (𝕜 := ℂ) μ').toLinearMap.eqLocus
      (ContinuousMap.integralPositiveLinearMap (𝕜 := ℂ) ν').toLinearMap
  have hS (f : C(AddCircle (1 : ℝ), ℂ)) : f ∈ S ↔ ∫ x, f x ∂μ' = ∫ x, f x ∂ν' := by simp [S]
  have hclosed : IsClosed (S : Set C(AddCircle (1 : ℝ), ℂ)) := by
    convert isClosed_eq (TauCeti.continuous_integral_continuousMap (E := ℂ) (μ := μ'))
      (TauCeti.continuous_integral_continuousMap (E := ℂ) (μ := ν')) using 1
    ext f
    exact hS f
  have hspan : Submodule.span ℂ (range (fourier (T := (1 : ℝ)))) ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    exact (hS _).2 (hmom n)
  have htop := (Submodule.span ℂ (range (fourier (T := (1 : ℝ))))).topologicalClosure_minimal
    hspan hclosed
  rw [span_fourier_closure_eq_top] at htop
  have hmap : μ' = ν' := by
    refine Measure.ext_of_integral_eq_on_compactlySupported fun g ↦ Complex.ofReal_injective ?_
    have hg := (hS _).1 (htop Submodule.mem_top : g.toContinuousMap.realToRCLike ℂ ∈ S)
    simpa [integral_complex_ofReal] using hg
  exact e.toMeasurableEquiv.map_measurableEquiv_injective hmap

end MeasureTheory
