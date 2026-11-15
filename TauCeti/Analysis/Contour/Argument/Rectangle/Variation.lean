/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Argument.Rectangle.Divisor
public import TauCeti.Analysis.Contour.Argument.Variation
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Argument variation around a rectangle

For `f` meromorphic on an open neighbourhood `U` of a rectangle `Rectangle z w` (`z.re ≤ w.re`,
`z.im ≤ w.im`) and analytic and nonvanishing on its frontier, the boundary values
`t ↦ f (rectBoundary z w t)` on `[0, 4]` avoid `0` and admit a continuous real argument lift `θ`.
For every such lift, `(θ 4 - θ 0) / (2 * π)` equals `divisorCount f U (Rectangle z w)`, and equals
`zeroCount f U (Rectangle z w)` when `f` has no poles in the rectangle.

## Main results

* `TauCeti.Contour.exists_continuousOn_arg_lift_rectBoundary` — existence of a continuous argument
  lift of `f ∘ rectBoundary z w` on `[0, 4]` starting at `Complex.arg (f z)`.
* `TauCeti.Contour.sub_div_two_pi_eq_divisorCount_of_arg_lift_rectBoundary` — for any continuous
  argument lift `θ` on `[0, 4]`, `(θ 4 - θ 0) / (2 * π) = divisorCount f U (Rectangle z w)`.
* `TauCeti.Contour.sub_div_two_pi_eq_zeroCount_of_arg_lift_rectBoundary` — the corresponding
  `zeroCount` identity when `0 ≤ divisor f U` on the rectangle.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§9.2–9.3.
-/

public section

open Set Complex
open scoped Real

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ} {θ : ℝ → ℝ}

/-- If `f` is analytic and nonvanishing on `frontier (Rectangle z w)`, then
`t ↦ f (rectBoundary z w t)` admits a continuous argument lift on `[0, 4]` starting at
`Complex.arg (f z)`. -/
theorem exists_continuousOn_arg_lift_rectBoundary
    (hreg : ∀ x ∈ frontier (Rectangle z w), AnalyticAt ℂ f x)
    (hne : ∀ x ∈ frontier (Rectangle z w), f x ≠ 0) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 4) ∧ θ 0 = Complex.arg (f z) ∧
      ∀ t ∈ Icc 0 4, f (rectBoundary z w t) =
        (‖f (rectBoundary z w t)‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ)) := by
  have hγ_cont : ContinuousOn (rectBoundary z w) (Icc 0 4) :=
    Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 4) ▸ (isPiecewiseC1On_rectBoundary z w).continuousOn
  have hcont : ContinuousOn (fun t ↦ f (rectBoundary z w t)) (Icc 0 4) := fun t ht ↦
    (hreg _ (rectBoundary_mem_frontier t)).continuousAt.comp_continuousWithinAt (hγ_cont t ht)
  obtain ⟨θ, hθ, hθ0, hlift⟩ := exists_continuousOn_arg_lift (by norm_num : (0 : ℝ) ≤ 4) hcont
    (fun t _ ↦ hne _ (rectBoundary_mem_frontier t))
  rw [rectBoundary_zero] at hθ0
  exact ⟨θ, hθ, hθ0, hlift⟩

/-- **Argument-variation principle on a rectangle.** For `f` meromorphic on an open neighbourhood
`U ⊇ Rectangle z w` (`z.re ≤ w.re`, `z.im ≤ w.im`), analytic and nonvanishing on the frontier, and
any continuous argument lift `θ` of `f ∘ rectBoundary z w` on `[0, 4]`,
`(θ 4 - θ 0) / (2 * π) = divisorCount f U (Rectangle z w)`. -/
theorem sub_div_two_pi_eq_divisorCount_of_arg_lift_rectBoundary
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hU : IsOpen U) (hRU : Rectangle z w ⊆ U) (hf : MeromorphicOn f U)
    (hreg : ∀ x ∈ frontier (Rectangle z w), AnalyticAt ℂ f x)
    (hne : ∀ x ∈ frontier (Rectangle z w), f x ≠ 0)
    (hθ : ContinuousOn θ (Icc 0 4))
    (hlift : ∀ t ∈ Icc 0 4, f (rectBoundary z w t) =
      (‖f (rectBoundary z w t)‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))) :
    (θ 4 - θ 0) / (2 * π) = (divisorCount f U (Rectangle z w) : ℝ) := by
  have hfr : ∀ x ∈ frontier (Rectangle z w), meromorphicOrderAt f x = 0 := fun x hx ↦
    (hreg x hx).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 (hne x hx)
  have him_eq := im_integral_deriv_smul_logDeriv_eq_sub_of_arg_lift (by norm_num : (0 : ℝ) ≤ 4)
    (isPiecewiseC1On_rectBoundary z w)
    (fun t _ ↦ hreg _ (rectBoundary_mem_frontier t))
    (fun t _ ↦ hne _ (rectBoundary_mem_frontier t)) hθ hlift
  rw [argumentPrinciple_rectBoundary_divisor hre him hU hRU hf hreg hfr] at him_eq
  have h2pi : (2 * π : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  rw [div_eq_iff h2pi, ← him_eq]
  simp [mul_comm]

/-- **Argument-variation zero count on a rectangle.** When `f` has nonnegative divisor throughout
`Rectangle z w`, `(θ 4 - θ 0) / (2 * π) = zeroCount f U (Rectangle z w)` for every continuous
argument lift `θ` on `[0, 4]`. -/
theorem sub_div_two_pi_eq_zeroCount_of_arg_lift_rectBoundary
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hU : IsOpen U) (hRU : Rectangle z w ⊆ U) (hf : MeromorphicOn f U)
    (hreg : ∀ x ∈ frontier (Rectangle z w), AnalyticAt ℂ f x)
    (hne : ∀ x ∈ frontier (Rectangle z w), f x ≠ 0)
    (hnonneg : ∀ x ∈ Rectangle z w, 0 ≤ MeromorphicOn.divisor f U x)
    (hθ : ContinuousOn θ (Icc 0 4))
    (hlift : ∀ t ∈ Icc 0 4, f (rectBoundary z w t) =
      (‖f (rectBoundary z w t)‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))) :
    (θ 4 - θ 0) / (2 * π) = (zeroCount f U (Rectangle z w) : ℝ) := by
  rw [sub_div_two_pi_eq_divisorCount_of_arg_lift_rectBoundary hre him hU hRU hf hreg hne hθ hlift,
    divisorCount_eq_zeroCount hnonneg, Int.cast_natCast]

end TauCeti.Contour
