/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Iterated derivatives of entire functions of one complex variable

This file records that every iterated derivative of a complex differentiable function
`g : ℂ → E` is again complex differentiable (`Differentiable.iteratedDeriv`), the iterated form of
Mathlib's `Differentiable.deriv`, and that an entire function whose iterated derivatives all vanish
at a single point is identically zero (`Differentiable.eq_zero_of_forall_iteratedDeriv_eq_zero`).
It also computes the norms of the real iterated derivatives of the powers `z ^ m`
(`TauCeti.Complex.norm_iteratedFDeriv_pow`).
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An iterated derivative of a complex differentiable function `g : ℂ → E` is complex
differentiable. This is the iterated form of `Differentiable.deriv`. -/
theorem Differentiable.iteratedDeriv {g : ℂ → E} (hg : Differentiable ℂ g) (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k g) :=
  (hg.contDiff (n := ⊤)).differentiable_iteratedDeriv k (by simp)

/-- **Identity principle for entire functions of one complex variable.** An entire function
`g : ℂ → E` into a complete normed space whose iterated derivatives at a point `z₀` all vanish is
identically zero. -/
theorem Differentiable.eq_zero_of_forall_iteratedDeriv_eq_zero {g : ℂ → E}
    (hg : Differentiable ℂ g) {z₀ : ℂ} (h : ∀ k : ℕ, _root_.iteratedDeriv k g z₀ = 0) : g = 0 := by
  have han : AnalyticOnNhd ℂ g Set.univ := fun z _ ↦ hg.analyticAt z
  have htop : analyticOrderAt g z₀ = ⊤ := ENat.eq_top_iff_forall_ge.2 fun n ↦
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han z₀ trivial)).2 fun k _ ↦ h k
  funext z
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ trivial
    (analyticOrderAt_eq_top.1 htop) trivial

namespace TauCeti.Complex

/-- The real iterated derivatives of `z ^ m` have the norms of the complex ones:
`‖D^k (z ^ m)‖ = m (m - 1) ⋯ (m - k + 1) ‖z‖ ^ (m - k)`. -/
theorem norm_iteratedFDeriv_pow (k m : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ m) z‖ = m.descFactorial k * ‖z‖ ^ (m - k) := by
  have h : ContDiffAt ℂ k (fun w : ℂ => w ^ m) z := by fun_prop
  rw [← h.restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_pow, norm_mul, norm_pow, Complex.norm_natCast]

end TauCeti.Complex
