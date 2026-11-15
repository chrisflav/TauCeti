/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Monotone
import TauCeti.Analysis.Asymptotics.Lemmas

/-!
# Cesàro averages of fixed-window increments of monotone functions

For a monotone real function `f : ℝ → ℝ` and a window width `h : ℝ`, translating the integral of
`f (t + h) - f t` over `[0, T]` collapses the interior cancellation to the boundary difference
`∫ t in T..(T + h), f t - ∫ t in 0..h, f t`. When `0 < h`, monotonicity traps
`∫ t in T..(T + h), f t` between `h * f T` and `h * f (T + h)`.

Consequently, if `f T / (T * g T) → c` as `T → ∞` for a scale `g` satisfying `T * g T → ∞` and
`g (T + h) / g T → 1`, the normalized Cesàro average
`(h * T)⁻¹ * (∫ t in 0..T, (f (t + h) - f t)) / g T` also converges to `c`, even when no pointwise
asymptotic holds for `f (T + h) - f T`. Specializing to `h = 1` and `g = Real.log` gives the
average unit-height zero-density limit for `L`-function counting functions.

## Main results

* `TauCeti.tendsto_log_add_div_log`: `Real.log (T + a) / Real.log T → 1` as `T → ∞`.
* `Monotone.integral_sub_comp_add_right`: exact boundary identity
  `∫ t in 0..T, (f (t + h) - f t) = (∫ t in T..(T + h), f t) - ∫ t in 0..h, f t`.
* `Monotone.mul_le_integral_add_right` and `Monotone.integral_add_right_le_mul`: monotonicity
  bounds `h * f T ≤ ∫ t in T..(T + h), f t ≤ h * f (T + h)` for `0 ≤ h`.
* `Monotone.tendsto_inv_mul_integral_sub_div`: Cesàro limit of `(f (t + h) - f t)` against a
  shift-invariant scale `g`.
* `Monotone.tendsto_inv_mul_integral_sub_div_log`: specialization to unit window `h = 1` and
  logarithmic scale `Real.log`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §9.4.
-/

public section

open Filter MeasureTheory Set intervalIntegral
open scoped Topology

namespace TauCeti

/-- Under any fixed additive shift `a`, `Real.log (T + a) / Real.log T → 1` as `T → ∞`. -/
theorem tendsto_log_add_div_log (a : ℝ) :
    Tendsto (fun T : ℝ ↦ Real.log (T + a) / Real.log T) atTop (𝓝 1) := by
  have h0 : Tendsto (fun T : ℝ ↦ 1 + (Real.log (T + a) - Real.log T) * (Real.log T)⁻¹)
      atTop (𝓝 (1 + 0 * 0)) :=
    tendsto_const_nhds.add ((Real.tendsto_log_comp_add_sub_log a).mul
      Real.tendsto_log_atTop.inv_tendsto_atTop)
  rw [mul_zero, add_zero] at h0
  refine h0.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hlog : Real.log T ≠ 0 := (Real.log_pos hT).ne'
  field_simp [hlog]
  ring

end TauCeti

namespace Monotone

variable {f g : ℝ → ℝ} {c h T : ℝ}

/-- Translating the integral of `f (t + h) - f t` over `[0, T]` leaves the upper window integral
minus the fixed lower window integral. -/
theorem integral_sub_comp_add_right (hf : Monotone f) (T h : ℝ) :
    ∫ t in (0 : ℝ)..T, (f (t + h) - f t) =
      (∫ t in T..(T + h), f t) - ∫ t in (0 : ℝ)..h, f t := by
  have hint : ∀ a b, IntervalIntegrable f volume a b := fun _ _ ↦ hf.intervalIntegrable
  have hint_shift : IntervalIntegrable (fun t ↦ f (t + h)) volume 0 T :=
    (hf.comp (monotone_id.add_const h)).intervalIntegrable
  rw [intervalIntegral.integral_sub hint_shift (hint 0 T),
    intervalIntegral.integral_comp_add_right f h, zero_add]
  have h₁ := intervalIntegral.integral_add_adjacent_intervals (hint 0 h) (hint h (T + h))
  have h₂ := intervalIntegral.integral_add_adjacent_intervals (hint 0 T) (hint T (T + h))
  linarith

/-- A monotone function integrated over `[T, T + h]` (`0 ≤ h`) is at least `h * f T`. -/
theorem mul_le_integral_add_right (hf : Monotone f) (T : ℝ) (hh : 0 ≤ h) :
    h * f T ≤ ∫ t in T..(T + h), f t := by
  have hconst : ∫ _ in T..(T + h), f T = h * f T := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
  rw [← hconst]
  exact intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
    hf.intervalIntegrable fun t ht ↦ hf ht.1

/-- A monotone function integrated over `[T, T + h]` (`0 ≤ h`) is at most `h * f (T + h)`. -/
theorem integral_add_right_le_mul (hf : Monotone f) (T : ℝ) (hh : 0 ≤ h) :
    ∫ t in T..(T + h), f t ≤ h * f (T + h) := by
  have hconst : ∫ _ in T..(T + h), f (T + h) = h * f (T + h) := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
  rw [← hconst]
  exact intervalIntegral.integral_mono_on (by linarith) hf.intervalIntegrable
    intervalIntegrable_const fun t ht ↦ hf ht.2

/-- **Cesàro average of fixed-window increments of a monotone function.** If `f` is monotone,
`0 < h`, `T * g T → ∞`, `g (T + h) / g T → 1`, and `f T / (T * g T) → c`, then
`(h * T)⁻¹ * (∫ t in 0..T, (f (t + h) - f t)) / g T → c` as `T → ∞`. -/
theorem tendsto_inv_mul_integral_sub_div (hf : Monotone f) (hh : 0 < h)
    (hg_top : Tendsto (fun T ↦ T * g T) atTop atTop)
    (hg_shift : Tendsto (fun T ↦ g (T + h) / g T) atTop (𝓝 1))
    (hlim : Tendsto (fun T ↦ f T / (T * g T)) atTop (𝓝 c)) :
    Tendsto (fun T ↦ (h * T)⁻¹ * (∫ t in (0 : ℝ)..T, (f (t + h) - f t)) / g T) atTop (𝓝 c) := by
  have hshift_top : Tendsto (fun T : ℝ ↦ T + h) atTop atTop :=
    tendsto_atTop_add_const_right atTop h tendsto_id
  have hratio_T : Tendsto (fun T : ℝ ↦ (T + h) / T) atTop (𝓝 1) := by
    simpa only [add_zero] using TauCeti.tendsto_add_div_add_atTop h (0 : ℝ)
  have hupper : Tendsto (fun T ↦ f (T + h) / (T * g T)) atTop (𝓝 c) := by
    have hprod : Tendsto (fun T ↦ (f (T + h) / ((T + h) * g (T + h))) * ((T + h) / T) *
        (g (T + h) / g T)) atTop (𝓝 (c * 1 * 1)) :=
      ((hlim.comp hshift_top).mul hratio_T).mul hg_shift
    rw [mul_one, mul_one] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (hg_top.comp hshift_top).eventually_gt_atTop 0] with T hT hTg
    have hTh : T + h ≠ 0 := by linarith
    have hgTh : g (T + h) ≠ 0 := fun h0 ↦ by simp [h0] at hTg
    field_simp [hT.ne', hTh, hgTh]
  have hmain : Tendsto (fun T ↦ (∫ t in T..(T + h), f t) / (h * (T * g T))) atTop (𝓝 c) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim hupper ?_ ?_
    · filter_upwards [hg_top.eventually_gt_atTop 0] with T hTg
      calc f T / (T * g T) = (h * f T) / (h * (T * g T)) :=
            (mul_div_mul_left _ _ hh.ne').symm
        _ ≤ (∫ t in T..(T + h), f t) / (h * (T * g T)) :=
            div_le_div_of_nonneg_right (hf.mul_le_integral_add_right T hh.le) (by positivity)
    · filter_upwards [hg_top.eventually_gt_atTop 0] with T hTg
      calc (∫ t in T..(T + h), f t) / (h * (T * g T))
          ≤ (h * f (T + h)) / (h * (T * g T)) :=
            div_le_div_of_nonneg_right (hf.integral_add_right_le_mul T hh.le) (by positivity)
        _ = f (T + h) / (T * g T) := mul_div_mul_left _ _ hh.ne'
  have hlower : Tendsto (fun T ↦ (∫ t in (0 : ℝ)..h, f t) / (h * (T * g T))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hg_top.const_mul_atTop hh)
  have hdiff := hmain.sub hlower
  rw [sub_zero] at hdiff
  refine hdiff.congr fun T ↦ ?_
  rw [hf.integral_sub_comp_add_right T h]
  ring

/-- **Cesàro average of unit-window increments with logarithmic normalization.** If `f` is monotone
and `f T / (T * Real.log T) → c` as `T → ∞`, then
`T⁻¹ * (∫ t in 0..T, (f (t + 1) - f t)) / Real.log T → c`. -/
theorem tendsto_inv_mul_integral_sub_div_log (hf : Monotone f)
    (hlim : Tendsto (fun T ↦ f T / (T * Real.log T)) atTop (𝓝 c)) :
    Tendsto (fun T ↦ T⁻¹ * (∫ t in (0 : ℝ)..T, (f (t + 1) - f t)) / Real.log T) atTop (𝓝 c) := by
  simpa only [one_mul] using hf.tendsto_inv_mul_integral_sub_div zero_lt_one
    (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop) (TauCeti.tendsto_log_add_div_log 1) hlim

end Monotone
