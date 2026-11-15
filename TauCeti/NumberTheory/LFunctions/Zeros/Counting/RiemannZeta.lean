/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.Analysis.SpecialFunctions.Gamma.Log
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Zeros.Counting.Asymptotics
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.Contour.Argument.Rectangle.Variation
import TauCeti.Analysis.Contour.Curve.Concat
import TauCeti.Analysis.Meromorphic.Counting.Jensen
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds

/-!
# The Riemann–von Mangoldt formula for the Riemann zeta function

For `T > 0` not the ordinate of a zero of `completedRiemannZeta`, integrating the logarithmic
derivative of the entire completion `zetaEntireCompletion` around `[-1, 2] ×ℂ [0, T]` and using the
functional-equation and conjugation symmetries reduces the zero count `N(T)` to half the contour
variation along the two-segment path `zetaArgContour T` (`2 → 2 + iT → 1/2 + iT`). Splitting
`logDeriv zetaEntireCompletion` into its polar, `Γ_ℝ`, and `ζ` parts yields the exact formula
`N(T) = Im(logGamma (1/4 + iT/2)) / π - (T / 2π) log π + 1 + S(T)`, where `S(T) = zetaArgTerm T` is
`π⁻¹` times the argument variation of `riemannZeta` along `2 → 2 + iT → 1/2 + iT`.

Backlund's real-part root bound and Jensen's inequality on concentric discs around `2` give
`S(T) = O(log T)` off zero ordinates; Stirling's formula evaluates the `logGamma` main term; and
right-continuity of `N(T)` extends the resulting `O(log T)` formula across zero ordinates to every
`T ≥ 2`.

## Main definitions

* `TauCeti.LFunctions.zetaArgContour`: the piecewise-linear path `2 → 2 + iT → 1/2 + iT` on
  `[0, 2]`.
* `TauCeti.LFunctions.zetaArgTerm`: the argument-variation term `S(T)` along `zetaArgContour T`.

## Main results

* `TauCeti.LFunctions.zetaArgTerm_eq_sub_div_pi_of_arg_lift` and
  `TauCeti.LFunctions.exists_continuousOn_arg_lift_zetaArgContour`: `zetaArgTerm T` equals
  `(θ 2 - θ 0) / π` for every continuous argument lift `θ` of `ζ ∘ zetaArgContour T`, and the
  canonical lift with `θ 0 = 0` satisfies `|θ 1| < π / 2`.
* `TauCeti.LFunctions.exists_abs_zetaArgTerm_le_mul_log`: Backlund's bound `|S(T)| ≤ C * log T`.
* `TauCeti.LFunctions.riemannZetaData_zeroCountingFunction_eq_of_forall_ne_zero`: exact formula
  for `N(T)` at zero-free heights `T > 0`.
* `TauCeti.LFunctions.riemannVonMangoldt` and `TauCeti.LFunctions.riemannVonMangoldt_symmetric`:
  `N(T) = (T / 2π) log(T / 2πe) + O(log T)` and `N±(T) = (T / π) log(T / 2πe) + O(log T)` for all
  `T ≥ 2`.
* `TauCeti.LFunctions.tendsto_zeroCountingFunction_riemannZetaData_div_mul_log`,
  `TauCeti.LFunctions.tendsto_inv_mul_integral_sub_zeroCountingFunction_riemannZetaData_div_log`,
  `TauCeti.LFunctions.infinite_setOf_zero_lt_divisor_completedRiemannZeta`, and
  `TauCeti.LFunctions.infinite_nontrivialZeros_riemannZeta`: asymptotic density, unit-window Cesàro
  average, and infinitude of nontrivial zeros.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§9.2–9.4, Theorems 9.3–9.4.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §15.
-/

public section

open Complex ComplexConjugate Filter MeasureTheory Metric Set intervalIntegral
open scoped Real Topology

namespace TauCeti.LFunctions

private theorem intervalIntegrable_vertical {f : ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ y ∈ Icc (0 : ℝ) T, ContinuousAt f (2 + y * I)) :
    IntervalIntegrable (fun y : ℝ ↦ f (2 + y * I)) volume 0 T := by
  refine ContinuousOn.intervalIntegrable_of_Icc hT fun y hy ↦ ?_
  have h1 : ContinuousAt (fun y : ℝ ↦ (2 : ℂ) + y * I) y :=
    (by fun_prop : Continuous fun y : ℝ ↦ (2 : ℂ) + y * I).continuousAt
  exact (ContinuousAt.comp (g := f) (f := fun y : ℝ ↦ (2 : ℂ) + y * I)
    (hf y hy) h1).continuousWithinAt

private theorem intervalIntegrable_horizontal {f : ℂ → ℂ} {T : ℝ}
    (hf : ∀ x ∈ Icc (1 / 2 : ℝ) 2, ContinuousAt f (x + T * I)) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + T * I)) volume 2 (1 / 2) := by
  refine (ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (1 / 2 : ℝ) ≤ 2) fun x hx ↦ ?_).symm
  have h1 : ContinuousAt (fun x : ℝ ↦ (x : ℂ) + T * I) x :=
    (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) + T * I).continuousAt
  exact (ContinuousAt.comp (g := f) (f := fun x : ℝ ↦ (x : ℂ) + T * I)
    (hf x hx) h1).continuousWithinAt

/-! ### The half-rectangle contour `2 → 2 + iT → 1/2 + iT` and `S(T)` -/

/-- The two-segment contour `2 → 2 + iT → 1/2 + iT` on `[0, 2]`, traversing the vertical segment on
`[0, 1]` and the horizontal segment on `[1, 2]`. -/
noncomputable def zetaArgContour (T : ℝ) (t : ℝ) : ℂ :=
  if t ≤ 1 then AffineMap.lineMap (2 : ℂ) (2 + (T : ℂ) * I) t
  else AffineMap.lineMap (2 + (T : ℂ) * I) (1 / 2 + (T : ℂ) * I) (t - 1)

theorem zetaArgContour_def (T t : ℝ) :
    zetaArgContour T t =
      if t ≤ 1 then AffineMap.lineMap (2 : ℂ) (2 + (T : ℂ) * I) t
      else AffineMap.lineMap (2 + (T : ℂ) * I) (1 / 2 + (T : ℂ) * I) (t - 1) := (rfl)

@[simp]
theorem zetaArgContour_zero (T : ℝ) : zetaArgContour T 0 = 2 := by
  simp [zetaArgContour_def]

@[simp]
theorem zetaArgContour_one (T : ℝ) : zetaArgContour T 1 = 2 + (T : ℂ) * I := by
  simp [zetaArgContour_def]

@[simp]
theorem zetaArgContour_two (T : ℝ) : zetaArgContour T 2 = 1 / 2 + (T : ℂ) * I := by
  norm_num [zetaArgContour_def]

theorem zetaArgContour_of_le_one {T t : ℝ} (ht : t ≤ 1) :
    zetaArgContour T t = 2 + ((t * T : ℝ) : ℂ) * I := by
  rw [zetaArgContour_def, ite_eq_left ht, AffineMap.lineMap_apply_module']
  apply Complex.ext <;> simp

theorem zetaArgContour_of_one_lt {T t : ℝ} (ht : 1 < t) :
    zetaArgContour T t = ((2 - (3 / 2) * (t - 1) : ℝ) : ℂ) + (T : ℂ) * I := by
  rw [zetaArgContour_def, ite_eq_right (not_le.2 ht), AffineMap.lineMap_apply_module']
  apply Complex.ext <;> simp
  ring

theorem zetaArgContour_re_mem_Icc {T t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    (zetaArgContour T t).re ∈ Icc (1 / 2) 2 := by
  by_cases h1 : t ≤ 1
  · rw [zetaArgContour_of_le_one h1]
    norm_num
  · rw [zetaArgContour_of_one_lt (lt_of_not_ge h1)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, mem_Icc]
    constructor <;> linarith [ht.1, ht.2]

theorem zetaArgContour_ne_one (t : ℝ) {T : ℝ} (hT : 0 < T) : zetaArgContour T t ≠ 1 := by
  by_cases h1 : t ≤ 1
  · intro heq
    have hre := congrArg Complex.re heq
    rw [zetaArgContour_of_le_one h1] at hre
    norm_num at hre
  · intro heq
    have him := congrArg Complex.im heq
    rw [zetaArgContour_of_one_lt (lt_of_not_ge h1)] at him
    simp [hT.ne'] at him

/-- The half-rectangle contour `zetaArgContour T` is piecewise `C¹` on `[0, 2]`. -/
theorem isPiecewiseC1On_zetaArgContour (T : ℝ) :
    TauCeti.IsPiecewiseC1On (zetaArgContour T) 0 2 := by
  have h1 : ContDiff ℝ 1 (AffineMap.lineMap (2 : ℂ) (2 + (T : ℂ) * I) : ℝ → ℂ) :=
    AffineMap.contDiff_lineMap _ _
  have h2 : ContDiff ℝ 1
      (fun t : ℝ ↦ AffineMap.lineMap (2 + (T : ℂ) * I) (1 / 2 + (T : ℂ) * I) (t - 1)) :=
    (AffineMap.contDiff_lineMap (𝕜 := ℝ) (2 + (T : ℂ) * I) (1 / 2 + (T : ℂ) * I)).comp
      (contDiff_id.sub contDiff_const)
  exact TauCeti.IsPiecewiseC1On.if_le (.of_contDiffOn h1.contDiffOn) (.of_contDiffOn h2.contDiffOn)
    zero_le_one one_le_two (by simp)

/-- Contour integral of a function continuous along `zetaArgContour T` as the sum of the vertical
and horizontal edge integrals. -/
theorem integral_zetaArgContour {f : ℂ → ℂ} {T : ℝ}
    (hf : ContinuousOn f (zetaArgContour T '' Icc 0 2)) :
    ∫ t in (0 : ℝ)..2, deriv (zetaArgContour T) t • f (zetaArgContour T t) =
      I * (∫ y in (0 : ℝ)..T, f (2 + y * I)) +
        ∫ x in (2 : ℝ)..(1 / 2 : ℝ), f (x + T * I) := by
  let γ₁ : ℝ → ℂ := AffineMap.lineMap (2 : ℂ) (2 + (T : ℂ) * I)
  let γ₂ : ℝ → ℂ := fun t ↦ AffineMap.lineMap (2 + (T : ℂ) * I) (1 / 2 + (T : ℂ) * I) (t - 1)
  have hγ₁_cont : Continuous γ₁ := (AffineMap.contDiff_lineMap (𝕜 := ℝ) _ _ (n := 1)).continuous
  have hγ₂_cont : Continuous γ₂ :=
    ((AffineMap.contDiff_lineMap (𝕜 := ℝ) _ _ (n := 1)).comp
      (contDiff_id.sub contDiff_const)).continuous
  have hderiv₁ : deriv γ₁ = fun _ ↦ (2 + (T : ℂ) * I) - 2 :=
    funext fun _ ↦ AffineMap.hasDerivAt_lineMap.deriv
  have hderiv₂ : deriv γ₂ = fun _ ↦ (1 / 2 + (T : ℂ) * I) - (2 + (T : ℂ) * I) :=
    funext fun t ↦ ((AffineMap.hasDerivAt_lineMap.scomp t
      ((hasDerivAt_id t).sub_const 1)).congr_deriv (one_smul _ _)).deriv
  have hint₁ : IntervalIntegrable (fun t ↦ deriv γ₁ t • f (γ₁ t)) volume 0 1 := by
    simp_rw [hderiv₁, smul_eq_mul]
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one (continuousOn_const.mul ?_)
    refine hf.comp hγ₁_cont.continuousOn fun t ht ↦ ⟨t, ⟨ht.1, by linarith [ht.2]⟩, ?_⟩
    rw [zetaArgContour_def]; exact ite_eq_left ht.2
  have hint₂ : IntervalIntegrable (fun t ↦ deriv γ₂ t • f (γ₂ t)) volume 1 2 := by
    simp_rw [hderiv₂, smul_eq_mul]
    refine ContinuousOn.intervalIntegrable_of_Icc one_le_two (continuousOn_const.mul ?_)
    refine hf.comp hγ₂_cont.continuousOn fun t ht ↦ ⟨t, ⟨by linarith [ht.1], ht.2⟩, ?_⟩
    rcases eq_or_lt_of_le ht.1 with rfl | hlt
    · simp [γ₂, zetaArgContour_def]
    · rw [zetaArgContour_def]; exact ite_eq_right (not_le.2 hlt)
  rw [TauCeti.Contour.intervalIntegral_deriv_smul_eq_add_of_eqOn (f := f) (η := zetaArgContour T)
    (fun t ht ↦ by
      rw [uIoo_of_le zero_le_one] at ht; rw [zetaArgContour_def]; exact ite_eq_left ht.2.le)
    (fun t ht ↦ by
      rw [uIoo_of_le one_le_two] at ht; rw [zetaArgContour_def]; exact ite_eq_right (not_le.2 ht.1))
    hint₁ hint₂]
  congr 1
  · simp_rw [hderiv₁, intervalIntegral.integral_smul]
    simpa [γ₁, smul_eq_mul] using
      Complex.smul_integral_lineMap_of_re_eq f (u := (2 : ℂ)) (v := 2 + (T : ℂ) * I) (by simp)
  · simp_rw [hderiv₂, intervalIntegral.integral_smul, γ₂]
    have h21 : (2 : ℝ) - 1 = 1 := by norm_num
    rw [intervalIntegral.integral_comp_sub_right
      (fun s ↦ f (AffineMap.lineMap (2 + (T : ℂ) * I) (1 / 2 + (T : ℂ) * I) s)) 1, sub_self, h21]
    simpa using Complex.smul_integral_lineMap_of_im_eq f
      (u := 2 + (T : ℂ) * I) (v := 1 / 2 + (T : ℂ) * I) (by simp)

/-- The argument-variation remainder `S(T)` in the Riemann–von Mangoldt formula: `π⁻¹` times the
imaginary part of the logarithmic-derivative integral of `riemannZeta` along `zetaArgContour T`
(`2 → 2 + iT → 1/2 + iT`). -/
noncomputable def zetaArgTerm (T : ℝ) : ℝ :=
  Real.pi⁻¹ * (∫ t in (0 : ℝ)..2,
    deriv (zetaArgContour T) t • logDeriv riemannZeta (zetaArgContour T t)).im

theorem zetaArgTerm_def (T : ℝ) :
    zetaArgTerm T = Real.pi⁻¹ * (∫ t in (0 : ℝ)..2,
      deriv (zetaArgContour T) t • logDeriv riemannZeta (zetaArgContour T t)).im := (rfl)

private theorem zeta_ne_zero_on_zetaArgContour {T : ℝ}
    (hζ : ∀ x ∈ Icc (1 / 2 : ℝ) 2, riemannZeta (x + T * I) ≠ 0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 2) : riemannZeta (zetaArgContour T t) ≠ 0 := by
  by_cases h1 : t ≤ 1
  · refine riemannZeta_ne_zero_of_one_le_re ?_
    rw [zetaArgContour_of_le_one h1]
    norm_num
  · have hre := zetaArgContour_re_mem_Icc (T := T) ht
    rw [zetaArgContour_of_one_lt (lt_of_not_ge h1)] at hre ⊢
    simpa using hζ (2 - (3 / 2) * (t - 1)) (by simpa using hre)

/-- At a positive height `T` where `riemannZeta` has no zeros on `[1/2, 2] + iT`, `zetaArgTerm T`
equals `(θ 2 - θ 0) / π` for every continuous argument lift `θ` of `riemannZeta ∘ zetaArgContour T`
on `[0, 2]`. -/
theorem zetaArgTerm_eq_sub_div_pi_of_arg_lift {T : ℝ} (hT : 0 < T)
    (hζ : ∀ x ∈ Icc (1 / 2 : ℝ) 2, riemannZeta (x + T * I) ≠ 0)
    {θ : ℝ → ℝ} (hθ : ContinuousOn θ (Icc 0 2))
    (hlift : ∀ t ∈ Icc 0 2, riemannZeta (zetaArgContour T t) =
      (‖riemannZeta (zetaArgContour T t)‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))) :
    zetaArgTerm T = (θ 2 - θ 0) / π := by
  rw [zetaArgTerm_def, TauCeti.Contour.im_integral_deriv_smul_logDeriv_eq_sub_of_arg_lift
    (by norm_num : (0 : ℝ) ≤ 2) (isPiecewiseC1On_zetaArgContour T)
    (fun t _ ↦ analyticOn_riemannZeta _ (zetaArgContour_ne_one t hT))
    (fun t ht ↦ zeta_ne_zero_on_zetaArgContour hζ ht) hθ hlift]
  ring

/-- At a positive height `T` where `riemannZeta` has no zeros on `[1/2, 2] + iT`, the canonical
continuous argument lift `θ` along `zetaArgContour T` starts at `0`, stays in `(-π / 2, π / 2)` at
the corner `2 + iT`, and satisfies `zetaArgTerm T = θ 2 / π`. -/
theorem exists_continuousOn_arg_lift_zetaArgContour {T : ℝ} (hT : 0 < T)
    (hζ : ∀ x ∈ Icc (1 / 2 : ℝ) 2, riemannZeta (x + T * I) ≠ 0) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 2) ∧ θ 0 = 0 ∧ |θ 1| < π / 2 ∧
      (∀ t ∈ Icc 0 2, riemannZeta (zetaArgContour T t) =
        (‖riemannZeta (zetaArgContour T t)‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))) ∧
      zetaArgTerm T = θ 2 / π := by
  have hγ_cont : ContinuousOn (zetaArgContour T) (Icc 0 2) :=
    uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2) ▸ (isPiecewiseC1On_zetaArgContour T).continuousOn
  have hg_cont : ContinuousOn (fun t ↦ riemannZeta (zetaArgContour T t)) (Icc 0 2) := fun t ht ↦
    (analyticOn_riemannZeta _ (zetaArgContour_ne_one t hT)).continuousAt.comp_continuousWithinAt
      (hγ_cont t ht)
  obtain ⟨θ, hθ, hθ0, hlift⟩ := TauCeti.Contour.exists_continuousOn_arg_lift
    (by norm_num : (0 : ℝ) ≤ 2) hg_cont (fun t ht ↦ zeta_ne_zero_on_zetaArgContour hζ ht)
  have harg2 : Complex.arg (riemannZeta 2) = 0 := by
    have h2 : riemannZeta 2 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by simpa using riemannZeta_two
    rw [h2, Complex.arg_ofReal_of_nonneg (by positivity)]
  rw [zetaArgContour_zero, harg2] at hθ0
  have hθ_eq_arg : EqOn θ (fun t ↦ Complex.arg (riemannZeta (zetaArgContour T t))) (Icc 0 1) := by
    refine TauCeti.Contour.eqOn_of_continuousOn_arg_lift zero_le_one
      (fun t ht ↦ zeta_ne_zero_on_zetaArgContour hζ ⟨ht.1, by linarith [ht.2]⟩)
      (hθ.mono (Icc_subset_Icc_right one_le_two))
      (fun t ht ↦ hlift t ⟨ht.1, by linarith [ht.2]⟩) ?_ ?_ (by simp [hθ0, harg2])
    · intro t ht
      have hslit : riemannZeta (zetaArgContour T t) ∈ slitPlane := by
        refine TauCeti.riemannZeta_mem_slitPlane_of_two_le_re ?_
        rw [zetaArgContour_of_le_one ht.2]; norm_num
      exact (Complex.continuousAt_arg hslit).comp_continuousWithinAt
        (f := fun t ↦ riemannZeta (zetaArgContour T t))
        ((hg_cont.mono (Icc_subset_Icc_right one_le_two)) t ht)
    · intro t _
      rw [mul_comm Complex.I]
      exact (Complex.norm_mul_exp_arg_mul_I _).symm
  have hθ1 : |θ 1| < π / 2 := by
    have h1_eq := hθ_eq_arg (right_mem_Icc.2 zero_le_one)
    dsimp only at h1_eq
    have hre := TauCeti.one_div_three_lt_riemannZeta_re_of_two_le_re
      (s := 2 + (T : ℂ) * I) (by simp)
    rw [h1_eq, zetaArgContour_one, abs_arg_lt_pi_div_two_iff]
    exact Or.inl (by linarith)
  refine ⟨θ, hθ, hθ0, hθ1, hlift, ?_⟩
  rw [zetaArgTerm_eq_sub_div_pi_of_arg_lift hT hζ hθ hlift, hθ0, sub_zero]

/-! ### Backlund's `O(log T)` bound on `zetaArgTerm` -/

private noncomputable def backlundFactor (w : ℂ) : ℂ := 1 - (2 : ℂ) ^ (1 - w)

private noncomputable def backlundAux (T : ℝ) (z : ℂ) : ℂ :=
  backlundFactor (z + (T : ℂ) * I) * backlundFactor (z - (T : ℂ) * I) *
    ((riemannZeta (z + (T : ℂ) * I) + riemannZeta (z - (T : ℂ) * I)) / 2)

private theorem analyticOnNhd_backlundAux {T : ℝ} (hT : 2 ≤ T) :
    AnalyticOnNhd ℂ (backlundAux T) (closedBall (2 : ℂ) (7 / 4)) := by
  have hfac : Differentiable ℂ backlundFactor := fun w ↦ by
    refine differentiableAt_const 1 |>.sub ?_
    exact ((differentiableAt_const 1).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero)
  have hopen : DifferentiableOn ℂ (backlundAux T) (ball (2 : ℂ) (15 / 8)) := by
    intro z hz
    have him : |z.im| < 15 / 8 := by
      calc |z.im| = |(z - 2).im| := by simp
        _ ≤ ‖z - 2‖ := abs_im_le_norm _
        _ < 15 / 8 := mem_ball_iff_norm.1 hz
    have hne_pos : z + (T : ℂ) * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith [abs_lt.1 him]
    have hne_neg : z - (T : ℂ) * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith [abs_lt.1 him]
    have hd_pos : DifferentiableAt ℂ (fun w ↦ riemannZeta (w + (T : ℂ) * I)) z :=
      (differentiableAt_riemannZeta hne_pos).comp z (differentiableAt_id.add_const _)
    have hd_neg : DifferentiableAt ℂ (fun w ↦ riemannZeta (w - (T : ℂ) * I)) z :=
      (differentiableAt_riemannZeta hne_neg).comp z (differentiableAt_id.sub_const _)
    exact (((hfac.differentiableAt.comp z (differentiableAt_id.add_const _)).mul
      (hfac.differentiableAt.comp z (differentiableAt_id.sub_const _))).mul
      ((hd_pos.add hd_neg).div_const 2)).differentiableWithinAt
  exact (hopen.analyticOnNhd isOpen_ball).mono (closedBall_subset_ball (by norm_num))

private theorem norm_backlundAux_two_ge (T : ℝ) : 1 / 12 ≤ ‖backlundAux T 2‖ := by
  have hfac_ge : ∀ s : ℂ, s.re = 2 → (1 / 2 : ℝ) ≤ ‖backlundFactor s‖ := by
    intro s hs
    have hpow : ‖(2 : ℂ) ^ (1 - s)‖ = (1 / 2 : ℝ) := by
      have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
      rw [h2, Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
      simp [hs]; norm_num
    have htri := norm_sub_norm_le (1 : ℂ) ((2 : ℂ) ^ (1 - s))
    rw [norm_one, hpow] at htri
    rw [backlundFactor]; linarith
  have hconj : (2 : ℂ) - (T : ℂ) * I = conj ((2 : ℂ) + (T : ℂ) * I) := by
    apply Complex.ext <;> simp
  have hmid : (riemannZeta ((2 : ℂ) + (T : ℂ) * I) + riemannZeta ((2 : ℂ) - (T : ℂ) * I)) / 2 =
      (((riemannZeta ((2 : ℂ) + (T : ℂ) * I)).re : ℝ) : ℂ) := by
    rw [hconj, riemannZeta_conj, ← Complex.re_eq_add_conj]
  have hre_pos : (1 / 3 : ℝ) ≤ ‖(((riemannZeta ((2 : ℂ) + (T : ℂ) * I)).re : ℝ) : ℂ)‖ := by
    have hlt := TauCeti.one_div_three_lt_riemannZeta_re_of_two_le_re
      (s := (2 : ℂ) + (T : ℂ) * I) (by simp)
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact hlt.le
  rw [backlundAux, hmid, norm_mul, norm_mul, mul_assoc]
  have h1 := hfac_ge ((2 : ℂ) + (T : ℂ) * I) (by simp)
  have h2 := hfac_ge ((2 : ℂ) - (T : ℂ) * I) (by simp)
  have h23 : (1 / 6 : ℝ) ≤ ‖backlundFactor (2 - (T : ℂ) * I)‖ *
      ‖(((riemannZeta (2 + (T : ℂ) * I)).re : ℝ) : ℂ)‖ :=
    (by norm_num : (1 / 6 : ℝ) = (1 / 2) * (1 / 3)).trans_le
      (mul_le_mul h2 hre_pos (by norm_num) (norm_nonneg _))
  exact (by norm_num : (1 / 12 : ℝ) = (1 / 2) * (1 / 6)).trans_le
    (mul_le_mul h1 h23 (by norm_num) (norm_nonneg _))

private theorem norm_backlundFactor_and_mul_zeta_le {z w : ℂ} {T : ℝ}
    (hre : 1 / 4 ≤ z.re) (hw_re : w.re = z.re) (hw_im : 1 / 4 ≤ |w.im|) (hw_norm : ‖w‖ ≤ 3 * T) :
    ‖backlundFactor w‖ ≤ 3 ∧ ‖backlundFactor w * riemannZeta w‖ ≤ 12 * T := by
  have hw_ne : w ≠ 1 := fun h ↦ by subst h; norm_num at hw_im
  have hpow : ‖(2 : ℂ) ^ (1 - w)‖ ≤ 2 := by
    have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [h2, Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
    simpa using Real.rpow_le_rpow_of_exponent_le one_le_two
      (by simp [hw_re]; linarith : (1 - w).re ≤ 1)
  refine ⟨?_, ?_⟩
  · calc ‖1 - (2 : ℂ) ^ (1 - w)‖ ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ (1 - w)‖ := norm_sub_le _ _
      _ ≤ 1 + 2 := by rw [norm_one]; linarith
      _ = 3 := by norm_num
  · calc ‖backlundFactor w * riemannZeta w‖
        ≤ ‖w‖ / w.re := TauCeti.norm_one_sub_two_cpow_mul_riemannZeta_le (by linarith) hw_ne
      _ ≤ (3 * T) / (1 / 4) :=
        div_le_div₀ ((norm_nonneg w).trans hw_norm) hw_norm (by norm_num) (by rwa [hw_re])
      _ = 12 * T := by ring

private theorem norm_backlundAux_sphere_le {T : ℝ} (hT : 2 ≤ T) {z : ℂ}
    (hz : z ∈ sphere (2 : ℂ) (7 / 4)) : ‖backlundAux T z‖ ≤ 36 * T := by
  have hz_norm : ‖z - 2‖ = 7 / 4 := mem_sphere_iff_norm.1 hz
  have hre_ge : 1 / 4 ≤ z.re := by
    have hle : |(z - 2).re| ≤ 7 / 4 := (abs_re_le_norm (z - 2)).trans_eq hz_norm
    simp only [sub_re, re_ofNat] at hle
    linarith [(abs_le.1 hle).1]
  have him_le : |z.im| ≤ 7 / 4 := by
    calc |z.im| = |(z - 2).im| := by simp
      _ ≤ ‖z - 2‖ := abs_im_le_norm _
      _ = 7 / 4 := hz_norm
  have hnorm_z : ‖z‖ ≤ 15 / 4 := by
    calc ‖z‖ = ‖(z - 2) + 2‖ := by ring_nf
      _ ≤ ‖z - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ = 15 / 4 := by rw [hz_norm]; norm_num
  have hT_pos : 0 < T := by linarith
  have hnorm_pos : ‖z + (T : ℂ) * I‖ ≤ 3 * T := by
    calc ‖z + (T : ℂ) * I‖ ≤ ‖z‖ + ‖(T : ℂ) * I‖ := norm_add_le _ _
      _ = ‖z‖ + T := by simp [abs_of_pos hT_pos]
      _ ≤ 3 * T := by linarith
  have hnorm_neg : ‖z - (T : ℂ) * I‖ ≤ 3 * T := by
    calc ‖z - (T : ℂ) * I‖ ≤ ‖z‖ + ‖(T : ℂ) * I‖ := norm_sub_le _ _
      _ = ‖z‖ + T := by simp [abs_of_pos hT_pos]
      _ ≤ 3 * T := by linarith
  have him_pos : 1 / 4 ≤ |(z + (T : ℂ) * I).im| := by
    have h1 : (z + (T : ℂ) * I).im = z.im + T := by simp
    rw [h1]
    exact (by linarith [(abs_le.1 him_le).1] : 1 / 4 ≤ z.im + T).trans (le_abs_self _)
  have him_neg : 1 / 4 ≤ |(z - (T : ℂ) * I).im| := by
    have h1 : (z - (T : ℂ) * I).im = z.im - T := by simp
    rw [h1, ← abs_neg]
    exact (by linarith [(abs_le.1 him_le).2] : 1 / 4 ≤ -(z.im - T)).trans (le_abs_self _)
  have hpos := norm_backlundFactor_and_mul_zeta_le (T := T) hre_ge (w := z + (T : ℂ) * I)
    (by simp) him_pos hnorm_pos
  have hneg := norm_backlundFactor_and_mul_zeta_le (T := T) hre_ge (w := z - (T : ℂ) * I)
    (by simp) him_neg hnorm_neg
  set A := backlundFactor (z + (T : ℂ) * I) * riemannZeta (z + (T : ℂ) * I)
  set B := backlundFactor (z - (T : ℂ) * I)
  set C := backlundFactor (z + (T : ℂ) * I)
  set D := backlundFactor (z - (T : ℂ) * I) * riemannZeta (z - (T : ℂ) * I)
  have hrewrite : backlundAux T z = (A * B + C * D) / 2 := by
    simp only [backlundAux, A, B, C, D]; ring
  rw [hrewrite, norm_div, RCLike.norm_ofNat]
  have hsum : ‖A * B + C * D‖ ≤ ‖A‖ * ‖B‖ + ‖C‖ * ‖D‖ := by
    simpa only [norm_mul] using norm_add_le (A * B) (C * D)
  have hmul₁ : ‖A‖ * ‖B‖ ≤ (12 * T) * 3 := mul_le_mul hpos.2 hneg.1 (norm_nonneg _) (by linarith)
  have hmul₂ : ‖C‖ * ‖D‖ ≤ 3 * (12 * T) := mul_le_mul hpos.1 hneg.2 (norm_nonneg _) (by norm_num)
  linarith

private theorem exists_finset_re_riemannZeta_eq_zero_card_le {T : ℝ} (hT : 2 ≤ T) :
    ∃ S : Finset ℝ,
      (∀ x ∈ Ioo (1 / 2 : ℝ) 2, (riemannZeta (x + T * I)).re = 0 → x ∈ S) ∧
      (S.card : ℝ) ≤ (10 / Real.log (7 / 6)) * Real.log T := by
  classical
  have hG2_ge := norm_backlundAux_two_ge T
  have hG2_ne : backlundAux T 2 ≠ 0 := norm_pos_iff.1 (by linarith)
  have hsub : ((fun x : ℝ ↦ (x : ℂ)) '' Ioo (1 / 2 : ℝ) 2) ⊆ closedBall (2 : ℂ) (3 / 2) := by
    rintro _ ⟨x, hx, rfl⟩
    have hcast : (x : ℂ) - 2 = ((x - 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [mem_closedBall_iff_norm, hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨Z, hZ_mem, hZ_card⟩ := (analyticOnNhd_backlundAux hT).exists_finset_eq_zero_card_le
    (r := 3 / 2) (R := 7 / 4) (M := 36 * T) (by norm_num) (by norm_num) (by linarith) hG2_ne
    (fun z hz ↦ norm_backlundAux_sphere_le hT hz) hsub
  refine ⟨Z.image Complex.re, fun x hx hre0 ↦ ?_, ?_⟩
  · have hconj : (x : ℂ) - (T : ℂ) * I = conj ((x : ℂ) + (T : ℂ) * I) := by
      apply Complex.ext <;> simp
    have hG0 : backlundAux T x = 0 := by
      simp only [backlundAux, hconj, riemannZeta_conj, ← Complex.re_eq_add_conj, hre0,
        ofReal_zero, mul_zero]
    exact Finset.mem_image.2 ⟨(x : ℂ), hZ_mem (x : ℂ) (mem_image_of_mem _ hx) hG0, ofReal_re x⟩
  · have h432 : 36 * T / ‖backlundAux T 2‖ ≤ T ^ 10 := by
      have hdiv : 36 * T / ‖backlundAux T 2‖ ≤ 432 * T :=
        (div_le_div_of_nonneg_left (by linarith) (by norm_num) hG2_ge).trans_eq (by ring)
      have hpow : (432 : ℝ) ≤ T ^ 9 :=
        (by norm_num : (432 : ℝ) ≤ 2 ^ 9).trans (pow_le_pow_left₀ zero_le_two hT 9)
      exact hdiv.trans ((mul_le_mul_of_nonneg_right hpow (by linarith)).trans_eq (by ring))
    have hlog_num : Real.log (36 * T / ‖backlundAux T 2‖) ≤ 10 * Real.log T :=
      (Real.log_le_log (div_pos (by linarith) (norm_pos_iff.2 hG2_ne)) h432).trans_eq
        (by rw [Real.log_pow]; norm_num)
    have hlog_den : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
    have hrat : (7 / 4 : ℝ) / (3 / 2) = 7 / 6 := by norm_num
    rw [hrat] at hZ_card
    calc ((Z.image Complex.re).card : ℝ) ≤ (Z.card : ℝ) := Nat.cast_le.2 Finset.card_image_le
      _ ≤ Real.log (36 * T / ‖backlundAux T 2‖) / Real.log (7 / 6) := hZ_card
      _ ≤ (10 * Real.log T) / Real.log (7 / 6) := div_le_div_of_nonneg_right hlog_num hlog_den.le
      _ = (10 / Real.log (7 / 6)) * Real.log T := by ring

private theorem abs_im_vertical_logDeriv_riemannZeta_le {T : ℝ} (hT : 0 ≤ T) :
    |(I * ∫ y in (0 : ℝ)..T, logDeriv riemannZeta (2 + y * I)).im| ≤ π := by
  have hhas : ∀ y ∈ uIcc (0 : ℝ) T,
      HasDerivAt (fun y : ℝ ↦ Complex.log (riemannZeta (2 + y * I)))
        (I * logDeriv riemannZeta (2 + y * I)) y := by
    intro y _
    have ha := (differentiableAt_riemannZeta (s := 2 + (y : ℂ) * I)
      (by intro h; have := congrArg Complex.re h; norm_num at this)).hasDerivAt
    have hinner : HasDerivAt (fun y : ℝ ↦ (2 : ℂ) + (y : ℂ) * I) I y := by
      simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (2 : ℂ)
    have hslit : riemannZeta (2 + (y : ℂ) * I) ∈ slitPlane :=
      TauCeti.riemannZeta_mem_slitPlane_of_two_le_re (by norm_num)
    exact ((Complex.hasDerivAt_log hslit).comp y (ha.scomp y hinner)).congr_deriv
      (by simp only [logDeriv_apply, smul_eq_mul]; ring)
  have hint : IntervalIntegrable (fun y : ℝ ↦ I * logDeriv riemannZeta (2 + y * I)) volume 0 T := by
    refine (intervalIntegrable_vertical hT fun y _ ↦ ?_).const_mul I
    have ha := analyticOn_riemannZeta (2 + (y : ℂ) * I)
      (by intro h; have := congrArg Complex.re h; norm_num at this)
    exact (ha.deriv.div ha (riemannZeta_ne_zero_of_one_le_re (by norm_num))).continuousAt
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ ↦ Complex.log (riemannZeta (2 + y * I))) hhas hint]
  simp only [ofReal_zero, zero_mul, add_zero, sub_im, log_im]
  have hre1 := TauCeti.one_div_three_lt_riemannZeta_re_of_two_le_re
    (s := 2 + (T : ℂ) * I) (by simp)
  have hre2 := TauCeti.one_div_three_lt_riemannZeta_re_of_two_le_re (s := 2) (by norm_num)
  have h1 : |Complex.arg (riemannZeta (2 + (T : ℂ) * I))| < π / 2 :=
    abs_arg_lt_pi_div_two_iff.2 (Or.inl (by linarith))
  have h2 : |Complex.arg (riemannZeta 2)| < π / 2 :=
    abs_arg_lt_pi_div_two_iff.2 (Or.inl (by linarith))
  rw [abs_le]
  constructor <;> linarith [abs_lt.1 h1, abs_lt.1 h2]

/-- **Backlund's bound on `S(T)`.** There is an absolute constant `C` such that for every `T ≥ 2`
where `riemannZeta` has no zeros on `[1/2, 2] + iT`, `|zetaArgTerm T| ≤ C * Real.log T`. -/
theorem exists_abs_zetaArgTerm_le_mul_log :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (∀ x ∈ Icc (1 / 2 : ℝ) 2, riemannZeta (x + T * I) ≠ 0) →
      |zetaArgTerm T| ≤ C * Real.log T := by
  refine ⟨10 / Real.log (7 / 6) + 2 / Real.log 2, fun T hT hζ ↦ ?_⟩
  have hT_pos : 0 < T := by linarith
  have hcont_ld : ContinuousOn (logDeriv riemannZeta) (zetaArgContour T '' Icc 0 2) := by
    rintro _ ⟨t, ht, rfl⟩
    have ha := analyticOn_riemannZeta _ (zetaArgContour_ne_one t hT_pos)
    exact (ha.deriv.div ha (zeta_ne_zero_on_zetaArgContour hζ ht)).continuousAt.continuousWithinAt
  obtain ⟨S, hS_mem, hS_card⟩ := exists_finset_re_riemannZeta_eq_zero_card_le hT
  have hhoriz : |(∫ x in (2 : ℝ)..(1 / 2 : ℝ), logDeriv riemannZeta (x + T * I)).im| ≤
      (S.card + 1 : ℝ) * π := by
    let γ : ℝ → ℂ := fun x ↦ (x : ℂ) + (T : ℂ) * I
    have hderiv_γ : deriv γ = fun _ ↦ (1 : ℂ) :=
      funext fun x ↦ (((hasDerivAt_id x).ofReal_comp).add_const ((T : ℂ) * I)).deriv
    have hbound := TauCeti.Contour.abs_im_integral_deriv_smul_logDeriv_le_mul_pi_of_re_eq_zero_mem
      (γ := γ) (f := riemannZeta) (by norm_num : (1 / 2 : ℝ) ≤ 2) (by fun_prop)
      (by rw [hderiv_γ]; exact continuous_const)
      (fun x _ ↦ analyticOn_riemannZeta _
        (by intro h; have := congrArg Complex.im h; simp [γ, hT_pos.ne'] at this))
      (fun x hx ↦ hζ x hx) (fun x hx h0 ↦ hS_mem x hx h0)
    simp only [hderiv_γ, one_smul, γ] at hbound
    rwa [intervalIntegral.integral_symm, neg_im, abs_neg]
  rw [zetaArgTerm_def, integral_zetaArgContour hcont_ld, add_im, abs_mul, abs_inv,
    abs_of_pos Real.pi_pos]
  have hsum : |(I * ∫ y in (0 : ℝ)..T, logDeriv riemannZeta (2 + y * I)).im +
      (∫ x in (2 : ℝ)..(1 / 2 : ℝ), logDeriv riemannZeta (x + T * I)).im| ≤
      ((S.card : ℝ) + 2) * π :=
    (abs_add_le _ _).trans ((add_le_add (abs_im_vertical_logDeriv_riemannZeta_le hT_pos.le)
      hhoriz).trans_eq (by ring))
  have htwo_le : (2 : ℝ) ≤ (2 / Real.log 2) * Real.log T := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    calc (2 : ℝ) = (2 / Real.log 2) * Real.log 2 := by field_simp [hlog2.ne']
      _ ≤ (2 / Real.log 2) * Real.log T :=
        mul_le_mul_of_nonneg_left (Real.log_le_log zero_lt_two hT) (by positivity)
  calc π⁻¹ * |(I * ∫ y in (0 : ℝ)..T, logDeriv riemannZeta (2 + y * I)).im +
        (∫ x in (2 : ℝ)..(1 / 2 : ℝ), logDeriv riemannZeta (x + T * I)).im|
      ≤ π⁻¹ * (((S.card : ℝ) + 2) * π) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 Real.pi_pos.le)
    _ = (S.card : ℝ) + 2 := by field_simp [Real.pi_ne_zero]
    _ ≤ (10 / Real.log (7 / 6)) * Real.log T + (2 / Real.log 2) * Real.log T :=
        add_le_add hS_card htwo_le
    _ = (10 / Real.log (7 / 6) + 2 / Real.log 2) * Real.log T := by ring

/-! ### Exact formula for `N(T)` off zero ordinates (Titchmarsh Theorem 9.3) -/

private theorem mem_Ioo_of_mem_rectangle_of_zero_lt_divisor {T : ℝ} (hT : 0 < T)
    (hord : ∀ ρ ∈ Icc (0 : ℝ) 1 ×ℂ {T},
      (MeromorphicOn.divisor completedRiemannZeta univ ρ).toNat = 0)
    {s : ℂ} (hs : s ∈ Rectangle (-1 : ℂ) (2 + (T : ℂ) * I))
    (hpos : 0 < MeromorphicOn.divisor completedRiemannZeta univ s) :
    s ∈ Ioo (0 : ℝ) 1 ×ℂ Ioo (0 : ℝ) T := by
  obtain ⟨hs_re, hs_im_ne⟩ :=
    re_mem_Ioo_and_im_ne_zero_of_zero_lt_divisor_completedRiemannZeta hpos
  rw [mem_rectangle_iff (by norm_num) (by simp [hT.le])] at hs
  simp only [neg_re, one_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_self, add_zero, neg_im, one_im, neg_zero, add_im, im_ofNat, mul_im,
    zero_add] at hs
  refine ⟨hs_re, lt_of_le_of_ne hs.2.1 hs_im_ne.symm, ?_⟩
  rcases lt_or_eq_of_le hs.2.2 with hlt | heq
  · exact hlt
  · exfalso
    have h0 := hord s ⟨Ioo_subset_Icc_self hs_re, heq⟩
    omega

private theorem zeroCount_zetaEntireCompletion_rectangle_eq {T : ℝ} (hT : 0 < T)
    (hord : ∀ ρ ∈ Icc (0 : ℝ) 1 ×ℂ {T},
      (MeromorphicOn.divisor completedRiemannZeta univ ρ).toNat = 0) :
    (∀ s ∈ frontier (Rectangle (-1 : ℂ) (2 + (T : ℂ) * I)), zetaEntireCompletion s ≠ 0) ∧
      zeroCount zetaEntireCompletion univ (Rectangle (-1 : ℂ) (2 + (T : ℂ) * I)) =
        riemannZetaData.zeroCountingFunction T ∧
      ∀ x ∈ Icc (1 / 2 : ℝ) 2, riemannZeta (x + T * I) ≠ 0 := by
  have hre : (-1 : ℂ).re ≤ (2 + (T : ℂ) * I).re := by norm_num
  have him : (-1 : ℂ).im ≤ (2 + (T : ℂ) * I).im := by simp [hT.le]
  refine ⟨fun s hs h0 ↦ ?_, ?_, fun x hx h0 ↦ ?_⟩
  · have hs_rect := (isClosed_rectangle _ _).frontier_subset hs
    have hIoo := mem_Ioo_of_mem_rectangle_of_zero_lt_divisor hT hord hs_rect
      (zetaEntireCompletion_eq_zero_iff.1 h0)
    refine hs.2 ?_
    rw [interior_rectangle hre him]
    simp only [mem_reProdIm, mem_Ioo, neg_re, one_re, add_re, re_ofNat, mul_re, ofReal_re, I_re,
      mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, neg_im, one_im, neg_zero, add_im,
      im_ofNat, mul_im, zero_add]
    exact ⟨⟨by linarith [hIoo.1.1], by linarith [hIoo.1.2]⟩, hIoo.2⟩
  · rw [← riemannZetaData_entireCompletion,
      riemannZetaData_hasMeromorphicContinuation.zeroCount_entireCompletion,
      riemannZetaData_completed, riemannZetaData.zeroCountingFunction_def,
      riemannZetaData_completed]
    have hsub : Icc (0 : ℝ) 1 ×ℂ Ioc (0 : ℝ) T ⊆ Rectangle (-1 : ℂ) (2 + (T : ℂ) * I) := by
      intro z hz; rw [mem_rectangle_iff hre him]
      simp only [neg_re, one_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_self, add_zero, neg_im, one_im, neg_zero, add_im, im_ofNat, mul_im,
        zero_add]
      exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2.1.le, hz.2.2⟩
    have hfin : (Rectangle (-1 : ℂ) (2 + (T : ℂ) * I) ∩ Function.support
        (fun z ↦ (MeromorphicOn.divisor completedRiemannZeta univ z).toNat)).Finite := by
      rw [Rectangle, uIcc_of_le hre, uIcc_of_le him]
      exact zeroCount_support_finite_of_subset_reProdIm_Icc (subset_univ _) Subset.rfl
    refine ((zeroCount_eq_iff_of_subset hsub hfin).2 fun z ⟨hz_rect, hz_not⟩ ↦ ?_).symm
    by_contra hne
    have hpos : 0 < MeromorphicOn.divisor completedRiemannZeta univ z := by
      by_contra hle; exact hne (Int.toNat_of_nonpos (not_lt.1 hle))
    have hIoo := mem_Ioo_of_mem_rectangle_of_zero_lt_divisor hT hord hz_rect hpos
    exact hz_not ⟨Ioo_subset_Icc_self hIoo.1, hIoo.2.1, hIoo.2.2.le⟩
  · by_cases hx1 : 1 ≤ x
    · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hx1) h0
    · have htriv : ¬∃ n : ℕ, (x : ℂ) + (T : ℂ) * I = -2 * ((n : ℂ) + 1) := by
        rintro ⟨n, hn⟩; have := congrArg Complex.im hn; simp [hT.ne'] at this
      have hne1 : (x : ℂ) + (T : ℂ) * I ≠ 1 := by
        intro h; have := congrArg Complex.im h; simp [hT.ne'] at this
      have hdiv := TauCeti.zero_lt_divisor_completedRiemannZeta_iff.2 ⟨h0, htriv, hne1⟩
      have h0' := hord ((x : ℂ) + (T : ℂ) * I)
        ⟨⟨by simp; linarith [hx.1], by simp; linarith⟩, by simp⟩
      omega

private theorem integral_neg_one_half_eq_neg_conj {f : ℂ → ℂ} {T : ℝ}
    (hsym : ∀ z : ℂ, f (1 - conj z) = -conj (f z)) :
    ∫ x : ℝ in (-1 : ℝ)..(1 / 2 : ℝ), f (x + T * I) =
      -conj (∫ x : ℝ in (1 / 2 : ℝ)..2, f (x + T * I)) := by
  have hcov := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ ↦ f (((1 - u : ℝ) : ℂ) + (T : ℂ) * I)) (1 : ℝ) (a := -1) (b := 1 / 2)
  have hlhs : (fun x : ℝ ↦ f (((1 - (1 - x) : ℝ) : ℂ) + (T : ℂ) * I)) =
      fun x : ℝ ↦ f ((x : ℂ) + (T : ℂ) * I) := funext fun x ↦ by ring_nf
  have hrhs : (fun u : ℝ ↦ f (((1 - u : ℝ) : ℂ) + (T : ℂ) * I)) =
      fun u : ℝ ↦ -conj (f ((u : ℂ) + (T : ℂ) * I)) := funext fun u ↦ by
    have hid : ((1 - u : ℝ) : ℂ) + (T : ℂ) * I = 1 - conj ((u : ℂ) + (T : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hid, hsym]
  rw [hlhs, hrhs] at hcov
  have hcov' : ∫ x in (-1 : ℝ)..(1 / 2 : ℝ), f ((x : ℂ) + (T : ℂ) * I) =
      ∫ x in (1 / 2 : ℝ)..2, -conj (f ((x : ℂ) + (T : ℂ) * I)) := by
    convert hcov using 2 <;> norm_num
  rw [hcov', intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj]

private theorem im_integral_rectBoundary_logDeriv_zetaEntireCompletion {T : ℝ}
    (hfr : ∀ s ∈ frontier (Rectangle (-1 : ℂ) (2 + (T : ℂ) * I)), zetaEntireCompletion s ≠ 0) :
    (∫ t in (0 : ℝ)..4, deriv (rectBoundary (-1 : ℂ) (2 + (T : ℂ) * I)) t •
        logDeriv zetaEntireCompletion (rectBoundary (-1 : ℂ) (2 + (T : ℂ) * I) t)).im =
      2 * ((I * ∫ y in (0 : ℝ)..T, logDeriv zetaEntireCompletion (2 + y * I)).im +
        (∫ x in (2 : ℝ)..(1 / 2 : ℝ), logDeriv zetaEntireCompletion (x + T * I)).im) := by
  set f : ℂ → ℂ := logDeriv zetaEntireCompletion
  have hf_cont : ContinuousOn f (frontier (Rectangle (-1 : ℂ) (2 + (T : ℂ) * I))) := fun s hs ↦
    ((differentiable_zetaEntireCompletion.analyticAt s).deriv.div
      (differentiable_zetaEntireCompletion.analyticAt s) (hfr s hs)).continuousAt.continuousWithinAt
  have hsym : ∀ z : ℂ, f (1 - conj z) = -conj (f z) := fun z ↦ by
    simp only [f, logDeriv_zetaEntireCompletion_one_sub, logDeriv_zetaEntireCompletion_conj]
  have hbot : (∫ x : ℝ in (-1 : ℝ)..2, f x).im = 0 := conj_eq_iff_im.1 <| by
    rw [← intervalIntegral.intervalIntegral_conj]
    exact intervalIntegral.integral_congr fun x _ ↦ by
      simp [f, ← logDeriv_zetaEntireCompletion_conj]
  have hleft : ∫ y : ℝ in (0 : ℝ)..T, f (-1 + y * I) =
      -conj (∫ y : ℝ in (0 : ℝ)..T, f (2 + y * I)) := by
    have hcongr : (fun y : ℝ ↦ f (-1 + y * I)) = fun y : ℝ ↦ -conj (f (2 + y * I)) :=
      funext fun y ↦ by
        have hid : (-1 : ℂ) + y * I = 1 - conj (2 + y * I) := by
          apply Complex.ext <;> simp; ring
        rw [hid, hsym]
    rw [hcongr, intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj]
  have htop_int : ∀ a b : ℝ, -1 ≤ a → a ≤ b → b ≤ 2 →
      IntervalIntegrable (fun x : ℝ ↦ f (x + T * I)) volume a b := fun a b ha hab hb ↦ by
    refine ContinuousOn.intervalIntegrable_of_Icc hab (hf_cont.comp (by fun_prop) fun x hx ↦ ?_)
    rw [frontier_rectangle]
    refine Or.inl ⟨?_, Or.inr (by simp)⟩
    rw [uIcc_of_le (by norm_num : (-1 : ℂ).re ≤ (2 + (T : ℂ) * I).re)]
    exact ⟨by simp; linarith [hx.1], by simp; linarith [hx.2]⟩
  have htop_split := (intervalIntegral.integral_add_adjacent_intervals
    (htop_int (-1) (1 / 2) le_rfl (by norm_num) (by norm_num))
    (htop_int (1 / 2) 2 (by norm_num) (by norm_num) le_rfl)).symm
  rw [Complex.integral_rectBoundary hf_cont]
  have hre_neg1 : (-1 : ℂ).re = -1 := by norm_num
  have him_neg1 : (-1 : ℂ).im = 0 := by norm_num
  have hre_w : (2 + (T : ℂ) * I).re = 2 := by simp
  have him_w : (2 + (T : ℂ) * I).im = T := by simp
  rw [hre_neg1, him_neg1, hre_w, him_w]
  simp only [ofReal_zero, zero_mul, add_zero, ofReal_ofNat, ofReal_neg, ofReal_one, smul_eq_mul]
  rw [hleft, htop_split, integral_neg_one_half_eq_neg_conj hsym,
    intervalIntegral.integral_symm (2 : ℝ) (1 / 2 : ℝ)]
  simp only [sub_im, add_im, neg_im, mul_im, I_re, zero_mul, I_im, one_mul, zero_add, neg_re,
    conj_re, conj_im, hbot]
  ring

private theorem integral_zetaArgContour_eq_sub_of_hasDerivAt {F f : ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hderiv_v : ∀ y ∈ uIcc (0 : ℝ) T, HasDerivAt F (f (2 + y * I)) (2 + y * I))
    (hcont_v : ∀ y ∈ Icc (0 : ℝ) T, ContinuousAt f (2 + y * I))
    (hderiv_h : ∀ x ∈ Icc (1 / 2 : ℝ) 2, HasDerivAt F (f (x + T * I)) (x + T * I))
    (hcont_h : ∀ x ∈ Icc (1 / 2 : ℝ) 2, ContinuousAt f (x + T * I)) :
    I * (∫ y in (0 : ℝ)..T, f (2 + y * I)) + ∫ x in (2 : ℝ)..(1 / 2 : ℝ), f (x + T * I) =
      F (1 / 2 + T * I) - F 2 := by
  have hvert : I * (∫ y in (0 : ℝ)..T, f (2 + y * I)) = F (2 + T * I) - F 2 := by
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ ↦ F (2 + y * I))
        (fun y hy ↦ by
          have hinner : HasDerivAt (fun y : ℝ ↦ (2 : ℂ) + (y : ℂ) * I) I y := by
            simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (2 : ℂ)
          exact ((hderiv_v y hy).scomp y hinner).congr_deriv (by simp [mul_comm I]))
        ((intervalIntegrable_vertical hT hcont_v).const_mul I)]
    simp
  have hhoriz : ∫ x in (2 : ℝ)..(1 / 2 : ℝ), f (x + T * I) = F (1 / 2 + T * I) - F (2 + T * I) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ ↦ F (x + T * I))
      (fun x hx ↦ by
        rw [uIcc_comm, uIcc_of_le (by norm_num)] at hx
        have hinner : HasDerivAt (fun x : ℝ ↦ (x : ℂ) + (T : ℂ) * I) 1 x := by
          simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((T : ℂ) * I)
        exact ((hderiv_h x hx).scomp x hinner).congr_deriv (one_smul _ _))
      (intervalIntegrable_horizontal hcont_h)]
    push_cast; rfl
  rw [hvert, hhoriz]
  ring

private theorem im_integral_zetaArgContour_logDeriv_polar {T : ℝ} (hT : 0 < T) :
    (I * (∫ y in (0 : ℝ)..T, logDeriv (fun z : ℂ ↦ z * (z - 1)) (2 + y * I)) +
      ∫ x in (2 : ℝ)..(1 / 2 : ℝ), logDeriv (fun z : ℂ ↦ z * (z - 1)) (x + T * I)).im = π := by
  let P : ℂ → ℂ := fun z ↦ Complex.log z + Complex.log (z - 1)
  set p : ℂ → ℂ := logDeriv (fun z : ℂ ↦ z * (z - 1))
  have hp_deriv : ∀ z : ℂ, z ∈ slitPlane → z - 1 ∈ slitPlane → HasDerivAt P (p z) z := by
    intro z hz0 hz1
    have hd := (Complex.hasDerivAt_log hz0).add (((hasDerivAt_id z).sub_const 1).clog hz1)
    have hp_eq : p z = z⁻¹ + (z - 1)⁻¹ := by
      simp only [p]
      rw [logDeriv_fun_mul (f := fun w : ℂ ↦ w) (g := fun w : ℂ ↦ w - 1) z
        (slitPlane_ne_zero hz0) (slitPlane_ne_zero hz1) differentiableAt_id
        (differentiableAt_id.sub_const 1)]
      simp [logDeriv_apply]
    exact hd.congr_deriv (by rw [hp_eq]; simp)
  have hp_cont : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → ContinuousAt p z := fun z hz0 hz1 ↦ by
    have ha : AnalyticAt ℂ (fun w : ℂ ↦ w * (w - 1)) z :=
      analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
    exact (ha.deriv.div ha (mul_ne_zero hz0 (sub_ne_zero.2 hz1))).continuousAt
  rw [integral_zetaArgContour_eq_sub_of_hasDerivAt (F := P) hT.le
    (fun y _ ↦ hp_deriv _ (mem_slitPlane_iff.2 (Or.inl (by norm_num)))
      (mem_slitPlane_iff.2 (Or.inl (by norm_num))))
    (fun y _ ↦ hp_cont _ (by intro h; have := congrArg Complex.re h; norm_num at this)
      (by intro h; have := congrArg Complex.re h; norm_num at this))
    (fun x _ ↦ hp_deriv _ (mem_slitPlane_iff.2 (Or.inr (by simp [hT.ne'])))
      (mem_slitPlane_iff.2 (Or.inr (by simp [hT.ne']))))
    (fun x _ ↦ hp_cont _ (by intro h; have := congrArg Complex.im h; simp [hT.ne'] at this)
      (by intro h; have := congrArg Complex.im h; simp [hT.ne'] at this))]
  have hP2_im : (P 2).im = 0 := by
    have h21 : (2 : ℂ) - 1 = 1 := by norm_num
    simp only [P, h21, log_one, add_zero, log_im]
    exact Complex.arg_ofReal_of_nonneg (x := 2) zero_le_two
  have harg_pos := arg_eq_pi_div_two_sub_arctan_of_im_pos
    (w := (1 / 2 : ℂ) + (T : ℂ) * I) (by simpa using hT)
  have harg_neg := arg_eq_pi_div_two_sub_arctan_of_im_pos
    (w := (1 / 2 : ℂ) + (T : ℂ) * I - 1) (by simpa using hT)
  simp only [add_re, one_div, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self', mul_re,
    ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, inv_im,
    im_ofNat, neg_zero, zero_div, mul_im, zero_add, sub_re, one_re, sub_im, one_im, sub_zero]
    at harg_pos harg_neg
  have hneg_ratio : ((2 : ℝ)⁻¹ - 1) / T = -((2 : ℝ)⁻¹ / T) := by ring
  rw [sub_im, hP2_im, sub_zero]
  simp only [P, add_im, log_im, one_div]
  rw [harg_pos, harg_neg, hneg_ratio, Real.arctan_neg]
  ring

private theorem im_integral_zetaArgContour_logDeriv_Gammaℝ {T : ℝ} (hT : 0 < T) :
    (I * (∫ y in (0 : ℝ)..T, logDeriv Gammaℝ (2 + y * I)) +
      ∫ x in (2 : ℝ)..(1 / 2 : ℝ), logDeriv Gammaℝ (x + T * I)).im =
      (TauCeti.logGamma (1 / 4 + ((T / 2 : ℝ) : ℂ) * I)).im - T / 2 * Real.log π := by
  let Φ : ℂ → ℂ := fun z ↦ TauCeti.logGamma (z / 2) - (Real.log π : ℂ) / 2 * z
  have hΦ_deriv : ∀ z : ℂ, 0 < z.re → HasDerivAt Φ (logDeriv Gammaℝ z) z := by
    intro z hz
    have hslit : z / 2 ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by simp; linarith))
    have hL : HasDerivAt TauCeti.logGamma (digamma (z / 2)) (z / 2) := by
      rw [← TauCeti.deriv_logGamma hslit]
      exact (TauCeti.differentiableOn_logGamma.differentiableAt
        (isOpen_slitPlane.mem_nhds hslit)).hasDerivAt
    have hd := (hL.comp z ((hasDerivAt_id z).div_const 2)).sub
      ((hasDerivAt_id z).const_mul ((Real.log π : ℂ) / 2))
    have hpoles : ∀ n : ℕ, z ≠ -(2 * (n : ℂ)) := fun n hn ↦ by
      have := congrArg Complex.re hn; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [Complex.logDeriv_Gammaℝ hpoles]
    exact hd.congr_deriv (by simp; ring)
  rw [integral_zetaArgContour_eq_sub_of_hasDerivAt (F := Φ) hT.le
    (fun y _ ↦ hΦ_deriv _ (by norm_num))
    (fun y _ ↦
      (Complex.analyticAt_logDeriv_Gammaℝ (Gammaℝ_ne_zero_of_re_pos (by norm_num))).continuousAt)
    (fun x hx ↦ hΦ_deriv _ (by simp; linarith [hx.1]))
    (fun x hx ↦ (Complex.analyticAt_logDeriv_Gammaℝ
      (Gammaℝ_ne_zero_of_re_pos (by simp; linarith [hx.1]))).continuousAt)]
  have hΦ2_im : (Φ 2).im = 0 := by
    have hlg1 : TauCeti.logGamma 1 = 0 := by
      simpa using TauCeti.logGamma_ofReal (x := 1) zero_lt_one
    simp [Φ, hlg1]
  have hhalf : ((1 / 2 : ℂ) + (T : ℂ) * I) / 2 = 1 / 4 + ((T / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [sub_im, hΦ2_im, sub_zero]
  dsimp only [Φ]
  rw [hhalf]
  simp only [sub_im, mul_im, div_ofNat_re, ofReal_re, div_ofNat_im, ofReal_im, zero_div, add_re,
    one_div, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self', I_re, mul_zero, I_im, mul_one,
    add_zero, add_im, inv_im, im_ofNat, neg_zero, zero_add]
  ring

private theorem split_vertical_logDeriv_zetaEntireCompletion {T : ℝ} (hT : 0 < T) :
    ∫ y in (0 : ℝ)..T, logDeriv zetaEntireCompletion (2 + y * I) =
      (∫ y in (0 : ℝ)..T, logDeriv (fun z : ℂ ↦ z * (z - 1)) (2 + y * I)) +
      (∫ y in (0 : ℝ)..T, logDeriv Gammaℝ (2 + y * I)) +
      ∫ y in (0 : ℝ)..T, logDeriv riemannZeta (2 + y * I) := by
  have hcongr : EqOn (fun y : ℝ ↦ logDeriv zetaEntireCompletion (2 + y * I))
      (fun y : ℝ ↦ (logDeriv (fun z : ℂ ↦ z * (z - 1)) (2 + y * I) +
        logDeriv Gammaℝ (2 + y * I)) + logDeriv riemannZeta (2 + y * I)) (uIcc 0 T) := fun y _ ↦
    logDeriv_zetaEntireCompletion (by norm_num)
      (by intro h; have := congrArg Complex.re h; norm_num at this)
      (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  have hint_p := intervalIntegrable_vertical hT.le (f := logDeriv (fun z : ℂ ↦ z * (z - 1)))
    fun y _ ↦ by
      have ha : AnalyticAt ℂ (fun w : ℂ ↦ w * (w - 1)) (2 + (y : ℂ) * I) :=
        analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
      exact (ha.deriv.div ha (mul_ne_zero
        (by intro h; have := congrArg Complex.re h; norm_num at this)
        (sub_ne_zero.2 (by intro h; have := congrArg Complex.re h; norm_num at this)))).continuousAt
  have hint_g := intervalIntegrable_vertical hT.le (f := logDeriv Gammaℝ) fun y _ ↦
    (Complex.analyticAt_logDeriv_Gammaℝ (Gammaℝ_ne_zero_of_re_pos (by norm_num))).continuousAt
  have hint_z := intervalIntegrable_vertical hT.le (f := logDeriv riemannZeta) fun y _ ↦ by
    have ha := analyticOn_riemannZeta (2 + (y : ℂ) * I)
      (by intro h; have := congrArg Complex.re h; norm_num at this)
    exact (ha.deriv.div ha (riemannZeta_ne_zero_of_one_le_re (by norm_num))).continuousAt
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_add (hint_p.add hint_g) hint_z,
    intervalIntegral.integral_add hint_p hint_g]

private theorem split_horizontal_logDeriv_zetaEntireCompletion {T : ℝ} (hT : 0 < T)
    (hζ_ne : ∀ x ∈ Icc (1 / 2 : ℝ) 2, riemannZeta (x + T * I) ≠ 0) :
    ∫ x in (2 : ℝ)..(1 / 2 : ℝ), logDeriv zetaEntireCompletion (x + T * I) =
      (∫ x in (2 : ℝ)..(1 / 2 : ℝ), logDeriv (fun z : ℂ ↦ z * (z - 1)) (x + T * I)) +
      (∫ x in (2 : ℝ)..(1 / 2 : ℝ), logDeriv Gammaℝ (x + T * I)) +
      ∫ x in (2 : ℝ)..(1 / 2 : ℝ), logDeriv riemannZeta (x + T * I) := by
  have hcongr : EqOn (fun x : ℝ ↦ logDeriv zetaEntireCompletion (x + T * I))
      (fun x : ℝ ↦ (logDeriv (fun z : ℂ ↦ z * (z - 1)) (x + T * I) +
        logDeriv Gammaℝ (x + T * I)) + logDeriv riemannZeta (x + T * I)) (uIcc 2 (1 / 2)) := by
    intro x hx; rw [uIcc_comm, uIcc_of_le (by norm_num)] at hx
    exact logDeriv_zetaEntireCompletion (by simp; linarith [hx.1])
      (by intro h; have := congrArg Complex.im h; simp [hT.ne'] at this) (hζ_ne x hx)
  have hint_p := intervalIntegrable_horizontal (T := T) (f := logDeriv (fun z : ℂ ↦ z * (z - 1)))
    fun x _ ↦ by
      have ha : AnalyticAt ℂ (fun w : ℂ ↦ w * (w - 1)) ((x : ℂ) + (T : ℂ) * I) :=
        analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
      have hne0 : (x : ℂ) + (T : ℂ) * I ≠ 0 := by
        intro h; have := congrArg Complex.im h; simp [hT.ne'] at this
      have hne1 : (x : ℂ) + (T : ℂ) * I ≠ 1 := by
        intro h; have := congrArg Complex.im h; simp [hT.ne'] at this
      exact (ha.deriv.div ha (mul_ne_zero hne0 (sub_ne_zero.2 hne1))).continuousAt
  have hint_g := intervalIntegrable_horizontal (T := T) (f := logDeriv Gammaℝ) fun x hx ↦
    (Complex.analyticAt_logDeriv_Gammaℝ
      (Gammaℝ_ne_zero_of_re_pos (by simp; linarith [hx.1]))).continuousAt
  have hint_z := intervalIntegrable_horizontal (T := T) (f := logDeriv riemannZeta) fun x hx ↦ by
    have ha := analyticOn_riemannZeta ((x : ℂ) + (T : ℂ) * I)
      (by intro h; have := congrArg Complex.im h; simp [hT.ne'] at this)
    exact (ha.deriv.div ha (hζ_ne x hx)).continuousAt
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_add (hint_p.add hint_g) hint_z,
    intervalIntegral.integral_add hint_p hint_g]

/-- **Exact zero-counting formula off zero ordinates (Titchmarsh, Theorem 9.3).** For `0 < T` such
that `completedRiemannZeta` has no zeros on `0 ≤ Re ρ ≤ 1` at height `Im ρ = T`,
`N(T) = Im(logGamma (1/4 + iT/2)) / π - (T / 2π) log π + 1 + S(T)`. -/
theorem riemannZetaData_zeroCountingFunction_eq_of_forall_ne_zero {T : ℝ} (hT : 0 < T)
    (hord : ∀ ρ ∈ Icc (0 : ℝ) 1 ×ℂ {T},
      (MeromorphicOn.divisor completedRiemannZeta univ ρ).toNat = 0) :
    (riemannZetaData.zeroCountingFunction T : ℝ) =
      (TauCeti.logGamma (1 / 4 + ((T / 2 : ℝ) : ℂ) * I)).im / π -
        T / (2 * π) * Real.log π + 1 + zetaArgTerm T := by
  obtain ⟨hfr_ne, hcount_eq, hζ_ne⟩ := zeroCount_zetaEntireCompletion_rectangle_eq hT hord
  have hana : AnalyticOnNhd ℂ zetaEntireCompletion univ :=
    fun z _ ↦ differentiable_zetaEntireCompletion.analyticAt z
  have harg := TauCeti.Contour.argumentPrinciple_rectBoundary_zeroCount
    (by norm_num : (-1 : ℂ).re ≤ (2 + (T : ℂ) * I).re)
    (by simp [hT.le] : (-1 : ℂ).im ≤ (2 + (T : ℂ) * I).im)
    isOpen_univ (subset_univ _) hana.meromorphicOn (fun x _ ↦ hana x (mem_univ x))
    (fun x hx ↦
      (hana x (mem_univ x)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 (hfr_ne x hx))
    (fun x _ ↦ MeromorphicOn.AnalyticOnNhd.divisor_nonneg hana x)
  have him_rect := congrArg Complex.im harg
  rw [hcount_eq] at him_rect
  have hrhs : ((2 : ℂ) * π * I * (riemannZetaData.zeroCountingFunction T : ℂ)).im =
      2 * π * (riemannZetaData.zeroCountingFunction T : ℝ) := by simp
  rw [hrhs, im_integral_rectBoundary_logDeriv_zetaEntireCompletion hfr_ne,
    split_vertical_logDeriv_zetaEntireCompletion hT,
    split_horizontal_logDeriv_zetaEntireCompletion hT hζ_ne] at him_rect
  have hcont_ld : ContinuousOn (logDeriv riemannZeta) (zetaArgContour T '' Icc 0 2) := by
    rintro _ ⟨t, ht, rfl⟩
    have ha := analyticOn_riemannZeta _ (zetaArgContour_ne_one t hT)
    exact (ha.deriv.div ha
      (zeta_ne_zero_on_zetaArgContour hζ_ne ht)).continuousAt.continuousWithinAt
  have hzeta_int : (I * (∫ y in (0 : ℝ)..T, logDeriv riemannZeta (2 + y * I)) +
      ∫ x in (2 : ℝ)..(1 / 2 : ℝ), logDeriv riemannZeta (x + T * I)).im = π * zetaArgTerm T := by
    rw [← integral_zetaArgContour hcont_ld, zetaArgTerm_def]
    field_simp [Real.pi_ne_zero]
  have hp_val := im_integral_zetaArgContour_logDeriv_polar hT
  have hg_val := im_integral_zetaArgContour_logDeriv_Gammaℝ hT
  simp only [mul_add, add_im] at him_rect hp_val hg_val hzeta_int
  have hgoal : 2 * π * (riemannZetaData.zeroCountingFunction T : ℝ) =
      2 * π * ((TauCeti.logGamma (1 / 4 + ((T / 2 : ℝ) : ℂ) * I)).im / π -
        T / (2 * π) * Real.log π + 1 + zetaArgTerm T) := by
    have hmul : 2 * π * ((TauCeti.logGamma (1 / 4 + ((T / 2 : ℝ) : ℂ) * I)).im / π -
        T / (2 * π) * Real.log π + 1 + zetaArgTerm T) =
      2 * (TauCeti.logGamma (1 / 4 + ((T / 2 : ℝ) : ℂ) * I)).im - T * Real.log π +
        2 * π + 2 * (π * zetaArgTerm T) := by
      field_simp [Real.pi_ne_zero]
    rw [hmul]
    linarith
  exact mul_left_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero) hgoal

/-! ### Stirling approximation of the archimedean main term and `riemannVonMangoldt` -/

private theorem abs_im_logGamma_quarter_sub_stirling_le {t : ℝ} (ht1 : 1 ≤ t) :
    |(TauCeti.logGamma (1 / 4 + (t : ℂ) * I)).im - (t * Real.log t - t - π / 8)| ≤
      2 / (1 - Real.cos (π / 4)) ^ 3 + 1 := by
  have ht0 : 0 < t := by linarith
  set w : ℂ := 1 / 4 + (t : ℂ) * I
  have hw_re : w.re = 1 / 4 := by simp [w]
  have hw_im : w.im = t := by simp [w]
  have hw0 : w ≠ 0 := fun h ↦ ht0.ne' (by rw [← hw_im, h, zero_im])
  have hw_ge : t ≤ ‖w‖ := by simpa [hw_im, abs_of_pos ht0] using abs_im_le_norm w
  have hw_le : ‖w‖ ≤ 1 / 4 + t := by
    simpa [hw_re, hw_im, abs_of_pos ht0] using norm_le_abs_re_add_abs_im w
  have harg : w.arg = π / 2 - Real.arctan ((1 / 4) / t) := by
    simpa [hw_re, hw_im] using arg_eq_pi_div_two_sub_arctan_of_im_pos (w := w) (by rwa [hw_im])
  have hatan_nn : 0 ≤ Real.arctan ((1 / 4) / t) :=
    Real.arctan_nonneg.2 (div_nonneg (by norm_num) ht0.le)
  have hatan_le : Real.arctan ((1 / 4) / t) ≤ π / 4 :=
    Real.arctan_one ▸ Real.arctan_mono (div_le_one_of_le₀ (by linarith) ht0.le)
  set K : ℝ := 2 / (1 - Real.cos (π / 4)) ^ 3
  have hK : 0 ≤ K := div_nonneg zero_le_two (pow_nonneg (sub_nonneg.2 (Real.cos_le_one _)) 3)
  have hS : |(TauCeti.logGamma w).im - (t * Real.log ‖w‖ - (1 / 4) * w.arg - t)| ≤ K := by
    have hsec : |w.arg| ≤ π - π / 4 := by rw [harg, abs_le]; constructor <;> linarith [Real.pi_pos]
    have him := (abs_im_le_norm _).trans
      (TauCeti.norm_logGamma_sub_stirling_le (by positivity) (by linarith [Real.pi_pos]) hsec hw0)
    refine le_trans (le_of_eq (congrArg abs ?_))
      (him.trans (div_div 2 _ ‖w‖ ▸ div_le_self hK (ht1.trans hw_ge)))
    simp only [sub_im, add_im, mul_im, sub_re, one_div, inv_re, re_ofNat, normSq_ofNat,
      div_self_mul_self', log_re, log_im, inv_im, im_ofNat, neg_zero, zero_div, sub_zero,
      ofReal_im, add_zero, hw_re, hw_im]; ring
  have hlog_nn : 0 ≤ t * (Real.log ‖w‖ - Real.log t) :=
    mul_nonneg ht0.le (sub_nonneg.2 (Real.log_le_log ht0 hw_ge))
  have hlog_le : t * (Real.log ‖w‖ - Real.log t) ≤ 1 / 4 := by
    rw [← Real.log_div (ht0.trans_le hw_ge).ne' ht0.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos (ht0.trans_le hw_ge) ht0)
    have h2 : ‖w‖ / t - 1 ≤ (1 / 4) / t :=
      div_sub_one ht0.ne' (a := ‖w‖) ▸ div_le_div_of_nonneg_right (by linarith) ht0.le
    exact (mul_le_mul_of_nonneg_left (h1.trans h2) ht0.le).trans_eq (by field_simp [ht0.ne'])
  have hsplit : (TauCeti.logGamma w).im - (t * Real.log t - t - π / 8) =
      ((TauCeti.logGamma w).im - (t * Real.log ‖w‖ - (1 / 4) * w.arg - t)) +
        t * (Real.log ‖w‖ - Real.log t) + (1 / 4) * Real.arctan ((1 / 4) / t) := by
    rw [harg]; ring
  have hatan_mul_nn : 0 ≤ (1 / 4) * Real.arctan ((1 / 4) / t) := mul_nonneg (by norm_num) hatan_nn
  rw [hsplit]
  refine (abs_add_three _ _ _).trans ?_
  rw [abs_of_nonneg hlog_nn, abs_of_nonneg hatan_mul_nn]
  linarith [hS, hlog_le, hatan_le, Real.pi_lt_d2]

private theorem abs_archimedeanMainTerm_sub_le {T : ℝ} (hT : 2 ≤ T) :
    |((TauCeti.logGamma (1 / 4 + ((T / 2 : ℝ) : ℂ) * I)).im / π -
        T / (2 * π) * Real.log π + 1) -
      T / (2 * π) * Real.log (T / (2 * π * Real.exp 1))| ≤
      (2 / (1 - Real.cos (π / 4)) ^ 3 + 1) / π + 1 := by
  set t : ℝ := T / 2 with ht_def
  have hS := abs_im_logGamma_quarter_sub_stirling_le (t := t) (by linarith)
  have hlog_eq : Real.log (T / (2 * π * Real.exp 1)) =
      Real.log (T / 2) - Real.log π - 1 := by
    have hexp : 0 < Real.exp 1 := Real.exp_pos 1
    have hdiv : T / (2 * π * Real.exp 1) = (T / 2) / (π * Real.exp 1) := by ring
    rw [hdiv, Real.log_div (div_pos (by linarith) two_pos).ne' (by positivity),
      Real.log_mul Real.pi_ne_zero hexp.ne', Real.log_exp]
    ring
  have hident : ((TauCeti.logGamma (1 / 4 + (t : ℂ) * I)).im / π -
        T / (2 * π) * Real.log π + 1) -
      T / (2 * π) * Real.log (T / (2 * π * Real.exp 1)) =
      ((TauCeti.logGamma (1 / 4 + (t : ℂ) * I)).im - (t * Real.log t - t - π / 8)) / π +
        7 / 8 := by
    rw [hlog_eq, ← ht_def]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hident]
  calc _ ≤ |(TauCeti.logGamma (1 / 4 + (t : ℂ) * I)).im - (t * Real.log t - t - π / 8)| / π +
          7 / 8 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_div, abs_of_pos Real.pi_pos, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 8)]
    _ ≤ (2 / (1 - Real.cos (π / 4)) ^ 3 + 1) / π + 7 / 8 := by gcongr
    _ ≤ (2 / (1 - Real.cos (π / 4)) ^ 3 + 1) / π + 1 := by linarith

/-- **The Riemann–von Mangoldt formula for `ζ` (Titchmarsh, Theorem 9.4).** The number `N(T)` of
zeros of `completedRiemannZeta` in `0 ≤ Re s ≤ 1`, `0 < Im s ≤ T`, counted with multiplicity,
satisfies `N(T) = (T / 2π) log(T / 2πe) + O(log T)` for all `T ≥ 2`. -/
theorem riemannVonMangoldt :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      |(zeroCount completedRiemannZeta univ (Icc (0 : ℝ) 1 ×ℂ Ioc (0 : ℝ) T) : ℝ) -
          T / (2 * π) * Real.log (T / (2 * π * Real.exp 1))| ≤ C * Real.log T := by
  obtain ⟨C_S, hC_S⟩ := exists_abs_zetaArgTerm_le_mul_log
  set C_A : ℝ := (2 / (1 - Real.cos (π / 4)) ^ 3 + 1) / π + 1
  have hC_A_nn : 0 ≤ C_A := by
    have : 0 ≤ 1 - Real.cos (π / 4) := sub_nonneg.2 (Real.cos_le_one _)
    positivity
  set C : ℝ := |C_S| + C_A / Real.log 2
  refine ⟨C, fun T hT ↦ ?_⟩
  rw [← riemannZetaData_completed, ← riemannZetaData.zeroCountingFunction_def]
  refine riemannZetaData.abs_zeroCountingFunction_sub_le_of_Ioo
    (main := fun t ↦ t / (2 * π) * Real.log (t / (2 * π * Real.exp 1)))
    (err := fun t ↦ C * Real.log t) ?_ ?_ fun t ht hord ↦ ?_
  · have hT0 : 0 < T := by linarith
    have hpos : T / (2 * π * Real.exp 1) ≠ 0 :=
      (div_pos hT0 (mul_pos (mul_pos two_pos Real.pi_pos) (Real.exp_pos 1))).ne'
    exact ((continuous_id.div_const _).continuousAt.mul
      ((continuousAt_id.div_const _).log hpos)).continuousWithinAt
  · exact (continuousAt_const.mul
      (Real.continuousAt_log (by linarith : T ≠ 0))).continuousWithinAt
  · rw [riemannZetaData_completed] at hord
    have ht2 : 2 ≤ t := le_trans hT ht.1.le
    have ht0 : 0 < t := by linarith
    obtain ⟨-, -, hζ_ne⟩ := zeroCount_zetaEntireCompletion_rectangle_eq ht0 hord
    have hsplit : ((TauCeti.logGamma (1 / 4 + ((t / 2 : ℝ) : ℂ) * I)).im / π -
        t / (2 * π) * Real.log π + 1 + zetaArgTerm t) -
        t / (2 * π) * Real.log (t / (2 * π * Real.exp 1)) =
      (((TauCeti.logGamma (1 / 4 + ((t / 2 : ℝ) : ℂ) * I)).im / π -
        t / (2 * π) * Real.log π + 1) -
        t / (2 * π) * Real.log (t / (2 * π * Real.exp 1))) + zetaArgTerm t := by ring
    rw [riemannZetaData_zeroCountingFunction_eq_of_forall_ne_zero ht0 hord, hsplit]
    have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hCA_log : C_A ≤ (C_A / Real.log 2) * Real.log t := by
      calc C_A = (C_A / Real.log 2) * Real.log 2 := by field_simp [hlog2.ne']
        _ ≤ (C_A / Real.log 2) * Real.log t :=
          mul_le_mul_of_nonneg_left (Real.log_le_log zero_lt_two ht2) (div_nonneg hC_A_nn hlog2.le)
    refine (abs_add_le _ _).trans ?_
    have hS := (hC_S t ht2 hζ_ne).trans (mul_le_mul_of_nonneg_right (le_abs_self C_S) hlog_pos.le)
    have hA := (abs_archimedeanMainTerm_sub_le ht2).trans hCA_log
    exact (add_le_add hA hS).trans_eq (by simp only [C]; ring)

private theorem zeroCount_completedRiemannZeta_Ico_neg_eq_Ioc {T : ℝ} :
    zeroCount completedRiemannZeta univ (Icc 0 1 ×ℂ Ico (-T) 0) =
      zeroCount completedRiemannZeta univ (Icc 0 1 ×ℂ Ioc 0 T) := by
  have hconj_div : ∀ z : ℂ, (MeromorphicOn.divisor completedRiemannZeta univ (conj z)).toNat =
      (MeromorphicOn.divisor completedRiemannZeta univ z).toNat := by
    intro z
    have hd := riemannZetaData_hasMeromorphicContinuation.divisor_dual_entireCompletion_conj z
    rw [riemannZetaData_dual] at hd
    rw [← riemannZetaData_completed,
      ← riemannZetaData_hasMeromorphicContinuation.toNat_divisor_entireCompletion,
      ← riemannZetaData_hasMeromorphicContinuation.toNat_divisor_entireCompletion, hd]
  let e : ℂ ≃ ℂ := Complex.conjCLE.toLinearEquiv.toEquiv
  have he : ∀ z : ℂ, e z = conj z := fun _ ↦ rfl
  rw [zeroCount_def, zeroCount_def, finsum_mem_def, finsum_mem_def, ← finsum_comp_equiv e]
  refine finsum_congr fun z ↦ ?_
  have hmem : e z ∈ Icc (0 : ℝ) 1 ×ℂ Ico (-T) 0 ↔ z ∈ Icc (0 : ℝ) 1 ×ℂ Ioc 0 T := by
    simp only [he, mem_reProdIm, conj_re, conj_im, mem_Ico, mem_Ioc]
    exact and_congr_right' ⟨fun ⟨_h1, _h2⟩ ↦ ⟨by linarith, by linarith⟩,
      fun ⟨_h1, _h2⟩ ↦ ⟨by linarith, by linarith⟩⟩
  by_cases hz : z ∈ Icc (0 : ℝ) 1 ×ℂ Ioc 0 T
  · rw [indicator_of_mem (hmem.2 hz), indicator_of_mem hz, he, hconj_div z]
  · rw [indicator_of_notMem (mt hmem.1 hz), indicator_of_notMem hz]

private theorem toNat_divisor_completedRiemannZeta_eq_zero_of_im_eq_zero {z : ℂ} (hz : z.im = 0) :
    (MeromorphicOn.divisor completedRiemannZeta univ z).toNat = 0 := by
  by_contra hne
  have hpos : 0 < MeromorphicOn.divisor completedRiemannZeta univ z := by
    by_contra hle; exact hne (Int.toNat_of_nonpos (not_lt.1 hle))
  exact (re_mem_Ioo_and_im_ne_zero_of_zero_lt_divisor_completedRiemannZeta hpos).2 hz

/-- Since `completedRiemannZeta` is conjugation-symmetric and has no real zeros, the symmetric zero
count `N±(T)` on `[-T, T]` is twice the one-sided zero count `N(T)` at every height `T : ℝ`. -/
theorem riemannZetaData_symmetricZeroCountingFunction (T : ℝ) :
    riemannZetaData.symmetricZeroCountingFunction T =
      2 * riemannZetaData.zeroCountingFunction T := by
  rcases lt_trichotomy T 0 with hneg | rfl | hpos
  · rw [riemannZetaData.symmetricZeroCountingFunction_of_neg hneg,
      riemannZetaData.zeroCountingFunction_of_nonpos hneg.le, mul_zero]
  · rw [riemannZetaData.symmetricZeroCountingFunction_zero,
      riemannZetaData.zeroCountingFunction_zero, mul_zero, riemannZetaData_completed]
    have hsub0 : Icc (0 : ℝ) 1 ×ℂ ({0} : Set ℝ) ⊆ Icc 0 1 ×ℂ Icc 0 0 := fun z hz ↦
      ⟨hz.1, by simp [mem_singleton_iff.1 hz.2]⟩
    exact (zeroCount_eq_zero_iff
      (zeroCount_support_finite_of_subset_reProdIm_Icc (subset_univ _) hsub0)).2 fun z hz ↦
        toNat_divisor_completedRiemannZeta_eq_zero_of_im_eq_zero (mem_singleton_iff.1 hz.2)
  · rw [riemannZetaData.symmetricZeroCountingFunction_def, riemannZetaData.zeroCountingFunction_def,
      riemannZetaData_completed]
    have hunion : (Icc (0 : ℝ) 1 ×ℂ Icc (-T) 0) ∪ (Icc (0 : ℝ) 1 ×ℂ Ioc 0 T) =
        Icc (0 : ℝ) 1 ×ℂ Icc (-T) T := by
      ext z; simp only [mem_union, mem_reProdIm, mem_Icc, mem_Ioc]
      exact ⟨fun h ↦ h.elim (fun ⟨hr, h1, h2⟩ ↦ ⟨hr, h1, h2.trans hpos.le⟩)
          fun ⟨hr, _, h2⟩ ↦ ⟨hr, by linarith, h2⟩,
        fun ⟨hr, h1, h2⟩ ↦ (le_or_gt z.im 0).imp (⟨hr, h1, ·⟩) (⟨hr, ·, h2⟩)⟩
    have hdisj : Disjoint (Icc (0 : ℝ) 1 ×ℂ Icc (-T) 0) (Icc (0 : ℝ) 1 ×ℂ Ioc 0 T) :=
      disjoint_left.2 fun z hz1 hz2 ↦ not_lt_of_ge hz1.2.2 hz2.2.1
    have hsub_pos : Icc (0 : ℝ) 1 ×ℂ Ioc (0 : ℝ) T ⊆ Icc 0 1 ×ℂ Icc 0 T :=
      fun _ hz ↦ ⟨hz.1, hz.2.1.le, hz.2.2⟩
    have hsub_neg : Icc (0 : ℝ) 1 ×ℂ Ico (-T) 0 ⊆ Icc 0 1 ×ℂ Icc (-T) 0 :=
      fun _ hz ↦ ⟨hz.1, hz.2.1, hz.2.2.le⟩
    have hfin_neg := zeroCount_support_finite_of_subset_reProdIm_Icc (f := completedRiemannZeta)
      (σ₁ := 0) (σ₂ := 1) (t₁ := -T) (t₂ := 0) (subset_univ _) Subset.rfl
    have hfin_pos := zeroCount_support_finite_of_subset_reProdIm_Icc (f := completedRiemannZeta)
      (subset_univ _) hsub_pos
    have hopen_eq : zeroCount completedRiemannZeta univ (Icc 0 1 ×ℂ Ico (-T) 0) =
        zeroCount completedRiemannZeta univ (Icc 0 1 ×ℂ Icc (-T) 0) :=
      (zeroCount_eq_iff_of_subset hsub_neg hfin_neg).2 fun z ⟨hz_in, hz_out⟩ ↦
        toNat_divisor_completedRiemannZeta_eq_zero_of_im_eq_zero
          (le_antisymm hz_in.2.2 (not_lt.1 fun hlt ↦ hz_out ⟨hz_in.1, hz_in.2.1, hlt⟩))
    rw [← hunion, zeroCount_union hdisj hfin_neg hfin_pos, ← hopen_eq,
      zeroCount_completedRiemannZeta_Ico_neg_eq_Ioc, two_mul]

/-- Symmetric form of the Riemann–von Mangoldt formula for `ζ`: the number `N±(T)` of zeros of
`completedRiemannZeta` in `0 ≤ Re s ≤ 1`, `-T ≤ Im s ≤ T`, counted with multiplicity, satisfies
`N±(T) = (T / π) log(T / 2πe) + O(log T)` for all `T ≥ 2`. -/
theorem riemannVonMangoldt_symmetric :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      |(zeroCount completedRiemannZeta univ (Icc (0 : ℝ) 1 ×ℂ Icc (-T) T) : ℝ) -
          T / π * Real.log (T / (2 * π * Real.exp 1))| ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := riemannVonMangoldt
  refine ⟨2 * C, fun T hT ↦ ?_⟩
  have hsym := riemannZetaData_symmetricZeroCountingFunction T
  rw [riemannZetaData.symmetricZeroCountingFunction_def,
    riemannZetaData.zeroCountingFunction_def, riemannZetaData_completed] at hsym
  have hcast : (zeroCount completedRiemannZeta univ (Icc (0 : ℝ) 1 ×ℂ Icc (-T) T) : ℝ) -
      T / π * Real.log (T / (2 * π * Real.exp 1)) =
      2 * ((zeroCount completedRiemannZeta univ (Icc (0 : ℝ) 1 ×ℂ Ioc (0 : ℝ) T) : ℝ) -
        T / (2 * π) * Real.log (T / (2 * π * Real.exp 1))) := by
    rw [hsym, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hcast, abs_mul, abs_of_nonneg zero_le_two]
  linarith [hC T hT]

/-! ### Asymptotic density, unit-window Cesàro average, and infinitude of zeros -/

/-- **Leading zero-density asymptotic for `ζ`.** As `T → ∞`,
`(riemannZetaData.zeroCountingFunction T : ℝ) / (T * Real.log T) → 1 / (2 * π)`. -/
theorem tendsto_zeroCountingFunction_riemannZetaData_div_mul_log :
    Tendsto (fun T : ℝ ↦ (riemannZetaData.zeroCountingFunction T : ℝ) / (T * Real.log T))
      atTop (𝓝 (1 / (2 * π))) := by
  obtain ⟨C, hC⟩ := riemannVonMangoldt
  refine riemannZetaData.tendsto_zeroCountingFunction_div_mul_log_of_abs_sub_le
    (b := -(1 + Real.log (2 * π)) / (2 * π)) (C := C) fun T hT ↦ ?_
  have hT0 : 0 < T := by linarith
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  have hmain : T / (2 * π) * Real.log (T / (2 * π * Real.exp 1)) =
      (1 / (2 * π)) * T * Real.log T + (-(1 + Real.log (2 * π)) / (2 * π)) * T := by
    rw [Real.log_div hT0.ne' (by positivity),
      Real.log_mul (by positivity) hexp.ne', Real.log_exp]
    ring
  rw [riemannZetaData.zeroCountingFunction_def, riemannZetaData_completed, ← hmain]
  exact hC T hT

/-- **Unit-window Cesàro average of zero increments for `ζ`.** As `T → ∞`,
`T⁻¹ * (∫ t in 0..T, (N(t + 1) - N(t))) / Real.log T → 1 / (2 * π)`. -/
theorem tendsto_inv_mul_integral_sub_zeroCountingFunction_riemannZetaData_div_log :
    Tendsto (fun T : ℝ ↦
      T⁻¹ * (∫ t in (0 : ℝ)..T,
        ((riemannZetaData.zeroCountingFunction (t + 1) : ℝ) -
          riemannZetaData.zeroCountingFunction t)) / Real.log T)
      atTop (𝓝 (1 / (2 * π))) :=
  riemannZetaData.tendsto_inv_mul_integral_sub_zeroCountingFunction_div_log
    tendsto_zeroCountingFunction_riemannZetaData_div_mul_log

/-- `completedRiemannZeta` has infinitely many zeros on `ℂ`. -/
theorem infinite_setOf_zero_lt_divisor_completedRiemannZeta :
    {s : ℂ | 0 < MeromorphicOn.divisor completedRiemannZeta univ s}.Infinite := by
  rw [← riemannZetaData_completed]
  exact riemannZetaData.infinite_setOf_zero_lt_divisor_completed_of_tendsto (by positivity)
    tendsto_zeroCountingFunction_riemannZetaData_div_mul_log

/-- `riemannZeta` has infinitely many nontrivial zeros in the open critical strip `0 < Re s < 1`. -/
theorem infinite_nontrivialZeros_riemannZeta :
    {s : ℂ | riemannZeta s = 0 ∧ s.re ∈ Ioo 0 1}.Infinite := by
  refine infinite_setOf_zero_lt_divisor_completedRiemannZeta.mono fun s hs ↦ ?_
  exact ⟨(TauCeti.zero_lt_divisor_completedRiemannZeta_iff.1 hs).1,
    (re_mem_Ioo_and_im_ne_zero_of_zero_lt_divisor_completedRiemannZeta hs).1⟩

end TauCeti.LFunctions
