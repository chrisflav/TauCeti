/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.WindowAverage
public import TauCeti.NumberTheory.LFunctions.Zeros.Counting.Basic

/-!
# Asymptotic consequences of zero-counting formulas for completed L-functions

Once an exact or approximate formula for `d.zeroCountingFunction` is established at heights `t`
carrying no zeros of `d.completed` in `0 ≤ Re ρ ≤ 1`, right-continuity of `d.zeroCountingFunction`
and local finiteness of the divisor support pass any continuous upper bound on
`|(d.zeroCountingFunction t : ℝ) - main t|` directly to every height `T` with no loss in the error
bound.

From a Riemann–von Mangoldt estimate
`|(d.zeroCountingFunction T : ℝ) - (c * T * Real.log T + b * T)| ≤ C * Real.log T` for `T ≥ 2`,
three asymptotic consequences follow uniformly for any `AnalyticLFunctionData` record `d`:

1. `(d.zeroCountingFunction T : ℝ) / (T * Real.log T) → c` as `T → ∞`;
2. the normalized unit-window Cesàro average
   `T⁻¹ * (∫ t in 0..T, (N(t + 1) - N(t))) / Real.log T → c` as `T → ∞`;
3. when `0 < c`, `d.completed` has infinitely many zeros (points of positive divisor on `ℂ`).

## Main results

* `AnalyticLFunctionData.abs_zeroCountingFunction_sub_le_of_Ioo` — extends an error bound
  `|(d.zeroCountingFunction t : ℝ) - main t| ≤ err t` from zero-free heights in `(T, T + 1)` to `T`.
* `AnalyticLFunctionData.tendsto_zeroCountingFunction_div_mul_log_of_abs_sub_le` — leading
  asymptotic `N(T) / (T * log T) → c`.
* `AnalyticLFunctionData.tendsto_inv_mul_integral_sub_zeroCountingFunction_div_log` — unit-window
  Cesàro average limit `T⁻¹ * (∫_0^T (N(t + 1) - N(t)) dt) / log T → c`.
* `AnalyticLFunctionData.infinite_setOf_zero_lt_divisor_completed_of_tendsto` — infinitely many
  zeros of `d.completed` whenever `c > 0`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §9.4.
-/

public section

open Complex Filter Set
open scoped Topology

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable (d : AnalyticLFunctionData)

/-- **Right-limit extension across zero ordinates.** If `main` and `err` are right-continuous on
`(T, ∞)` at `T`, and `|(d.zeroCountingFunction t : ℝ) - main t| ≤ err t` holds at every
`t ∈ (T, T + 1)` where `d.completed` has no positive-divisor point in `0 ≤ Re ρ ≤ 1` at height `t`,
then `|(d.zeroCountingFunction T : ℝ) - main T| ≤ err T`. -/
theorem abs_zeroCountingFunction_sub_le_of_Ioo {main err : ℝ → ℝ} {T : ℝ}
    (hmain : ContinuousWithinAt main (Ioi T) T) (herr : ContinuousWithinAt err (Ioi T) T)
    (hbound : ∀ t ∈ Ioo T (T + 1),
      (∀ ρ ∈ Icc (0 : ℝ) 1 ×ℂ {t}, (MeromorphicOn.divisor d.completed univ ρ).toNat = 0) →
      |(d.zeroCountingFunction t : ℝ) - main t| ≤ err t) :
    |(d.zeroCountingFunction T : ℝ) - main T| ≤ err T := by
  let Z := (Icc (0 : ℝ) 1 ×ℂ Icc T (T + 1)) ∩
    Function.support (fun ρ ↦ (MeromorphicOn.divisor d.completed univ ρ).toNat)
  have hZ : Z.Finite :=
    zeroCount_support_finite_of_subset_reProdIm_Icc (subset_univ _) Subset.rfl
  let Y : Set ℝ := (Complex.im '' Z) \ {T}
  have hY_compl : Yᶜ ∈ 𝓝 T :=
    (hZ.image Complex.im).sdiff.isClosed.isOpen_compl.mem_nhds fun h ↦ h.2 rfl
  have heq : d.zeroCountingFunction =ᶠ[𝓝[>] T] fun _ ↦ d.zeroCountingFunction T :=
    (d.eventuallyEq_zeroCountingFunction_nhdsGE T).filter_mono
      (nhdsWithin_mono T Ioi_subset_Ici_self)
  have hev : ∀ᶠ t in 𝓝[>] T, |(d.zeroCountingFunction T : ℝ) - main t| ≤ err t := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : T < T + 1)),
      nhdsWithin_le_nhds hY_compl, heq] with t ht_gt ht_lt htY ht_eq
    rw [← ht_eq]
    refine hbound t ⟨ht_gt, ht_lt⟩ fun ρ hρ ↦ ?_
    by_contra hne
    have hρZ : ρ ∈ Z := ⟨⟨hρ.1, ht_gt.le.trans_eq (mem_singleton_iff.1 hρ.2).symm,
      (mem_singleton_iff.1 hρ.2).trans_le ht_lt.le⟩, hne⟩
    exact htY ⟨⟨ρ, hρZ, mem_singleton_iff.1 hρ.2⟩, ht_gt.ne'⟩
  exact le_of_tendsto_of_tendsto (continuousWithinAt_const.sub hmain).abs herr hev

/-- If `|(d.zeroCountingFunction T : ℝ) - (c * T * Real.log T + b * T)| ≤ C * Real.log T` for all
`T ≥ 2`, then `(d.zeroCountingFunction T : ℝ) / (T * Real.log T) → c` as `T → ∞`. -/
theorem tendsto_zeroCountingFunction_div_mul_log_of_abs_sub_le {c b C : ℝ}
    (h : ∀ T : ℝ, 2 ≤ T →
      |(d.zeroCountingFunction T : ℝ) - (c * T * Real.log T + b * T)| ≤ C * Real.log T) :
    Tendsto (fun T : ℝ ↦ (d.zeroCountingFunction T : ℝ) / (T * Real.log T)) atTop (𝓝 c) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hupper : Tendsto (fun T : ℝ ↦ |C| * T⁻¹ + |b| * (Real.log T)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_inv_atTop_zero).add
      (tendsto_const_nhds.mul Real.tendsto_log_atTop.inv_tendsto_atTop)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  have hT_pos : 0 < T := by linarith
  have hlog_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hprod_pos : 0 < T * Real.log T := mul_pos hT_pos hlog_pos
  have hsplit : (d.zeroCountingFunction T : ℝ) / (T * Real.log T) - c =
      ((d.zeroCountingFunction T : ℝ) - (c * T * Real.log T + b * T)) / (T * Real.log T) +
        b * (Real.log T)⁻¹ := by
    field_simp [hT_pos.ne', hlog_pos.ne']
    ring
  rw [Real.norm_eq_abs, hsplit]
  calc |((d.zeroCountingFunction T : ℝ) - (c * T * Real.log T + b * T)) / (T * Real.log T) +
        b * (Real.log T)⁻¹|
      ≤ |((d.zeroCountingFunction T : ℝ) - (c * T * Real.log T + b * T)) / (T * Real.log T)| +
          |b * (Real.log T)⁻¹| := abs_add_le _ _
    _ = |(d.zeroCountingFunction T : ℝ) - (c * T * Real.log T + b * T)| / (T * Real.log T) +
          |b| * (Real.log T)⁻¹ := by
        rw [abs_div, abs_of_pos hprod_pos, abs_mul, abs_inv, abs_of_pos hlog_pos]
    _ ≤ (|C| * Real.log T) / (T * Real.log T) + |b| * (Real.log T)⁻¹ := by
        gcongr
        exact (h T hT).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hlog_pos.le)
    _ = |C| * T⁻¹ + |b| * (Real.log T)⁻¹ := by
        congr 1
        field_simp [hT_pos.ne', hlog_pos.ne']

/-- If `(d.zeroCountingFunction T : ℝ) / (T * Real.log T) → c`, then the normalized Cesàro average
of unit-height zero increments also tends to `c`. -/
theorem tendsto_inv_mul_integral_sub_zeroCountingFunction_div_log {c : ℝ}
    (hlim : Tendsto (fun T : ℝ ↦ (d.zeroCountingFunction T : ℝ) / (T * Real.log T)) atTop (𝓝 c)) :
    Tendsto (fun T : ℝ ↦
      T⁻¹ * (∫ t in (0 : ℝ)..T,
        ((d.zeroCountingFunction (t + 1) : ℝ) - d.zeroCountingFunction t)) / Real.log T)
      atTop (𝓝 c) :=
  (Nat.mono_cast.comp d.monotone_zeroCountingFunction).tendsto_inv_mul_integral_sub_div_log hlim

/-- If `(d.zeroCountingFunction T : ℝ) / (T * Real.log T) → c` with `0 < c`, then `d.completed` has
infinitely many points of positive divisor on `ℂ`. -/
theorem infinite_setOf_zero_lt_divisor_completed_of_tendsto {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun T : ℝ ↦ (d.zeroCountingFunction T : ℝ) / (T * Real.log T)) atTop (𝓝 c)) :
    {s : ℂ | 0 < MeromorphicOn.divisor d.completed univ s}.Infinite := by
  intro hfin
  have hsupp : (univ ∩ Function.support
      (fun z ↦ (MeromorphicOn.divisor d.completed univ z).toNat)).Finite := by
    refine hfin.subset fun z ⟨_, hz⟩ ↦ ?_
    by_contra hle
    exact hz (Int.toNat_of_nonpos (not_lt.1 hle))
  have hM_tendsto :
      Tendsto (fun T : ℝ ↦ (zeroCount d.completed univ univ : ℝ) / (T * Real.log T))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop)
  have hle : c ≤ 0 := by
    refine le_of_tendsto_of_tendsto hlim hM_tendsto ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    have hpos : 0 < T * Real.log T := mul_pos (by linarith) (Real.log_pos (by linarith))
    refine div_le_div_of_nonneg_right ?_ hpos.le
    rw [d.zeroCountingFunction_def]
    exact_mod_cast zeroCount_mono (subset_univ _) hsupp
  linarith

end TauCeti.LFunctions.AnalyticLFunctionData
