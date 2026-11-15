/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import TauCeti.Analysis.Contour.Argument.Lift
public import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.Analysis.Contour.Winding.SegmentSum
import TauCeti.Topology.Circle.Degree

/-!
# Argument variation along a curve and Backlund's real-part root bound

Along a piecewise-`C¹` curve `γ : ℝ → ℂ` on `[a, b]` on which `f : ℂ → ℂ` is analytic and
nowhere zero, the composite `f ∘ γ` admits a continuous real argument lift `θ` satisfying
`f (γ t) = ‖f (γ t)‖ * exp (I * θ t)` on `[a, b]`. Any two continuous argument lifts differ by an
integer multiple of `2π`, so the argument variation `θ b - θ a` is independent of the choice of
lift and equals the imaginary part of the logarithmic-derivative integral
`∫ t in a..b, deriv γ t • logDeriv f (γ t)`, while the real part is `log ‖f (γ b)‖ - log ‖f (γ a)‖`.

When `g : ℝ → ℂ` is nonvanishing on `[a, b]` and its real part vanishes at most on a finite set `S`
inside `(a, b)`, splitting `[a, b]` at the points of `S` places `g` inside an open half-plane on
each open subinterval, where the argument changes by at most `π`. Hence
`|(∫ t in a..b, deriv g t / g t).im| ≤ (S.card + 1) * π`. Combined with Jensen's bound on the
number of zeros of an analytic continuation of `Re f`, this is Backlund's method for bounding the
argument variation `S(T)` of an `L`-function on a horizontal segment.

## Main results

* `TauCeti.Contour.exists_int_eq_add_of_continuousOn_arg_lift` and
  `TauCeti.Contour.sub_eq_sub_of_continuousOn_arg_lift` — two continuous argument lifts on `[a, b]`
  differ by a constant multiple of `2π`, so `θ₁ b - θ₁ a = θ₂ b - θ₂ a`.
* `TauCeti.Contour.exists_continuousOn_arg_lift` — existence of a continuous argument lift of a
  nowhere-zero continuous curve `g : ℝ → ℂ` on `[a, b]` starting at `Complex.arg (g a)`.
* `TauCeti.Contour.integral_deriv_smul_logDeriv_eq_log_norm_sub_add_I_mul_sub_of_arg_lift` and
  `TauCeti.Contour.im_integral_deriv_smul_logDeriv_eq_sub_of_arg_lift` — the logarithmic-derivative
  integral along a piecewise-`C¹` curve decomposes into the log-modulus difference and `I` times
  the variation of any continuous argument lift.
* `TauCeti.Contour.abs_im_integral_deriv_div_le_pi_of_re_ne_zero` — if `(g t).re ≠ 0` on `(a, b)`,
  the imaginary part of `∫_a^b g' / g` has absolute value at most `π`.
* `TauCeti.Contour.abs_im_integral_deriv_div_le_mul_pi_of_re_eq_zero_mem` and
  `TauCeti.Contour.abs_im_integral_deriv_smul_logDeriv_le_mul_pi_of_re_eq_zero_mem` — Backlund's
  piecewise half-plane bound `(|S| + 1) * π` in terms of a finite set covering the interior zeros
  of the real part.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§9.3–9.4.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §§12, 16.
-/

public section

open Complex MeasureTheory Set intervalIntegral Filter
open scoped Interval Real Topology

namespace TauCeti.Contour

section ArgLift

variable {g γ : ℝ → ℂ} {f : ℂ → ℂ} {θ θ₁ θ₂ : ℝ → ℝ} {a b : ℝ}

/-- Two continuous argument lifts of a nowhere-zero function on `[a, b]` differ by a constant
integer multiple of `2π`. -/
theorem exists_int_eq_add_of_continuousOn_arg_lift (hne : ∀ t ∈ Icc a b, g t ≠ 0)
    (hθ₁ : ContinuousOn θ₁ (Icc a b))
    (hlift₁ : ∀ t ∈ Icc a b, g t = (‖g t‖ : ℂ) * Complex.exp (Complex.I * (θ₁ t : ℂ)))
    (hθ₂ : ContinuousOn θ₂ (Icc a b))
    (hlift₂ : ∀ t ∈ Icc a b, g t = (‖g t‖ : ℂ) * Complex.exp (Complex.I * (θ₂ t : ℂ))) :
    ∃ m : ℤ, ∀ t ∈ Icc a b, θ₁ t = θ₂ t + m * (2 * π) := by
  have : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  have hexp : ∀ t : Icc a b, Circle.exp (θ₁ t) = Circle.exp (θ₂ t) := by
    intro t
    have hnorm : ((‖g t‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne t t.2))
    have hmul : ((‖g t‖ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ₁ t : ℂ)) =
        ((‖g t‖ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ₂ t : ℂ)) := by
      rw [← hlift₁ t t.2, ← hlift₂ t t.2]
    apply Subtype.ext
    simpa only [Circle.coe_exp, mul_comm Complex.I] using mul_left_cancel₀ hnorm hmul
  obtain ⟨m, hm⟩ := Circle.exists_int_forall_eq_add_of_exp_eq
    hθ₁.domRestrict hθ₂.domRestrict hexp
  exact ⟨m, fun t ht ↦ hm ⟨t, ht⟩⟩

/-- Two continuous argument lifts of a nowhere-zero function on `[a, b]` (`a ≤ b`) with the same
initial value at `a` agree everywhere on `[a, b]`. -/
theorem eqOn_of_continuousOn_arg_lift (hab : a ≤ b) (hne : ∀ t ∈ Icc a b, g t ≠ 0)
    (hθ₁ : ContinuousOn θ₁ (Icc a b))
    (hlift₁ : ∀ t ∈ Icc a b, g t = (‖g t‖ : ℂ) * Complex.exp (Complex.I * (θ₁ t : ℂ)))
    (hθ₂ : ContinuousOn θ₂ (Icc a b))
    (hlift₂ : ∀ t ∈ Icc a b, g t = (‖g t‖ : ℂ) * Complex.exp (Complex.I * (θ₂ t : ℂ)))
    (ha : θ₁ a = θ₂ a) : EqOn θ₁ θ₂ (Icc a b) := by
  obtain ⟨m, hm⟩ := exists_int_eq_add_of_continuousOn_arg_lift hne hθ₁ hlift₁ hθ₂ hlift₂
  have hm0 : (m : ℝ) * (2 * π) = 0 := by linarith [hm a (left_mem_Icc.2 hab)]
  intro t ht
  linarith [hm t ht]

/-- The total argument variation `θ b - θ a` on `[a, b]` (`a ≤ b`) is the same for every continuous
argument lift `θ`. -/
theorem sub_eq_sub_of_continuousOn_arg_lift (hab : a ≤ b) (hne : ∀ t ∈ Icc a b, g t ≠ 0)
    (hθ₁ : ContinuousOn θ₁ (Icc a b))
    (hlift₁ : ∀ t ∈ Icc a b, g t = (‖g t‖ : ℂ) * Complex.exp (Complex.I * (θ₁ t : ℂ)))
    (hθ₂ : ContinuousOn θ₂ (Icc a b))
    (hlift₂ : ∀ t ∈ Icc a b, g t = (‖g t‖ : ℂ) * Complex.exp (Complex.I * (θ₂ t : ℂ))) :
    θ₁ b - θ₁ a = θ₂ b - θ₂ a := by
  obtain ⟨m, hm⟩ := exists_int_eq_add_of_continuousOn_arg_lift hne hθ₁ hlift₁ hθ₂ hlift₂
  linarith [hm a (left_mem_Icc.2 hab), hm b (right_mem_Icc.2 hab)]

/-- Every nowhere-zero continuous function `g : ℝ → ℂ` on `[a, b]` (`a ≤ b`) admits a continuous
argument lift starting at `Complex.arg (g a)`. -/
theorem exists_continuousOn_arg_lift (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hne : ∀ t ∈ Icc a b, g t ≠ 0) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc a b) ∧ θ a = Complex.arg (g a) ∧
      ∀ t ∈ Icc a b, g t = (‖g t‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ)) := by
  obtain ⟨N, s, -, hs0, -, hs_mono, -, hs_avoid, -, hcont, hlift⟩ :=
    exists_continuousOn_arg_lift_with_partition (w := 0) hab hg hne
  refine ⟨_, hcont, ?_, fun t ht ↦ by simpa only [sub_zero] using hlift t ht⟩
  rw [sum_im_log_segRatio_eq_zero_of_le hs_mono (fun j hj ↦ hs_avoid j hj.le) hs0.ge,
    sub_zero, add_zero]

/-- **Logarithmic-derivative integral in terms of a continuous argument lift.** For a piecewise-`C¹`
curve `γ` on `[a, b]` (`a ≤ b`), `f` analytic and nonvanishing along `γ`, and any continuous
argument lift `θ` of `f ∘ γ` on `[a, b]`,
`∫ t in a..b, deriv γ t • logDeriv f (γ t) = (log ‖f (γ b)‖ - log ‖f (γ a)‖) + I * (θ b - θ a)`. -/
theorem integral_deriv_smul_logDeriv_eq_log_norm_sub_add_I_mul_sub_of_arg_lift
    (hab : a ≤ b) (hγ : IsPiecewiseC1On γ a b)
    (hf : ∀ t ∈ Icc a b, AnalyticAt ℂ f (γ t)) (hne : ∀ t ∈ Icc a b, f (γ t) ≠ 0)
    (hθ : ContinuousOn θ (Icc a b))
    (hlift : ∀ t ∈ Icc a b, f (γ t) = (‖f (γ t)‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))) :
    ∫ t in a..b, deriv γ t • logDeriv f (γ t) =
      ((Real.log ‖f (γ b)‖ - Real.log ‖f (γ a)‖ : ℝ) : ℂ) +
        Complex.I * ((θ b - θ a : ℝ) : ℂ) := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  have hγ_cont : ContinuousOn γ (Icc a b) := hu ▸ hγ.continuousOn
  have hg_cont : ContinuousOn (fun t ↦ f (γ t)) (Icc a b) := fun t ht ↦
    (hf t ht).continuousAt.comp_continuousWithinAt (hγ_cont t ht)
  obtain ⟨N, s, -, hs0, hsN, hs_mono, -, hs_avoid, h_slit, hθ₀, hlift₀⟩ :=
    exists_continuousOn_arg_lift_with_partition (w := 0) hab hg_cont hne
  obtain ⟨P, hPc, hPd⟩ := hγ.exists_countable_differentiableAt
  have hint := intervalIntegrable_deriv_smul_logDeriv hγ (hu ▸ hf) (hu ▸ hne)
  have hfun : (fun t ↦ deriv γ t • logDeriv f (γ t)) =
      fun t ↦ (deriv γ t * deriv f (γ t)) / (f (γ t) - 0) :=
    funext fun t ↦ by simp [smul_eq_mul, logDeriv_apply, mul_div_assoc]
  have hdiff : ∀ t ∈ Ioo a b \ P,
      HasDerivAt (fun t ↦ f (γ t)) (deriv γ t * deriv f (γ t)) t := by
    intro t ht
    have htu : t ∈ Ioo (min a b) (max a b) \ P := by
      rwa [min_eq_left hab, max_eq_right hab]
    simpa only [Function.comp_def, smul_eq_mul] using
      ((hf t (Ioo_subset_Icc_self ht.1)).differentiableAt.hasDerivAt).scomp t (hPd t htu).hasDerivAt
  have hint_eq := integral_deriv_div_sub_eq_log_norm_add_I_mul_sum_log_im hPc hs0 hsN hs_mono
    hg_cont hdiff h_slit (hfun ▸ hint)
  have hsub := sub_eq_sub_of_continuousOn_arg_lift hab hne hθ hlift hθ₀
    (fun t ht ↦ by simpa only [sub_zero] using hlift₀ t ht)
  rw [sum_im_log_segRatio_eq_zero_of_le hs_mono (fun j hj ↦ hs_avoid j hj.le) hs0.ge,
    sum_im_log_segRatio_eq_sum_of_le hs_mono hsN.le, add_zero, add_sub_cancel_left] at hsub
  rw [hfun, hint_eq]
  simp [hsub]

/-- The imaginary part of `∫ t in a..b, deriv γ t • logDeriv f (γ t)` along a piecewise-`C¹` curve
is `θ b - θ a` for any continuous argument lift `θ` of `f ∘ γ`. -/
theorem im_integral_deriv_smul_logDeriv_eq_sub_of_arg_lift
    (hab : a ≤ b) (hγ : IsPiecewiseC1On γ a b)
    (hf : ∀ t ∈ Icc a b, AnalyticAt ℂ f (γ t)) (hne : ∀ t ∈ Icc a b, f (γ t) ≠ 0)
    (hθ : ContinuousOn θ (Icc a b))
    (hlift : ∀ t ∈ Icc a b, f (γ t) = (‖f (γ t)‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))) :
    (∫ t in a..b, deriv γ t • logDeriv f (γ t)).im = θ b - θ a := by
  rw [integral_deriv_smul_logDeriv_eq_log_norm_sub_add_I_mul_sub_of_arg_lift
    hab hγ hf hne hθ hlift]
  simp

/-- The real part of `∫ t in a..b, deriv γ t • logDeriv f (γ t)` along a piecewise-`C¹` curve is
`Real.log ‖f (γ b)‖ - Real.log ‖f (γ a)‖`. -/
theorem re_integral_deriv_smul_logDeriv_eq_log_norm_sub
    (hab : a ≤ b) (hγ : IsPiecewiseC1On γ a b)
    (hf : ∀ t ∈ Icc a b, AnalyticAt ℂ f (γ t)) (hne : ∀ t ∈ Icc a b, f (γ t) ≠ 0) :
    (∫ t in a..b, deriv γ t • logDeriv f (γ t)).re =
      Real.log ‖f (γ b)‖ - Real.log ‖f (γ a)‖ := by
  have hγ_cont : ContinuousOn γ (Icc a b) := uIcc_of_le hab ▸ hγ.continuousOn
  have hg_cont : ContinuousOn (fun t ↦ f (γ t)) (Icc a b) := fun t ht ↦
    (hf t ht).continuousAt.comp_continuousWithinAt (hγ_cont t ht)
  obtain ⟨θ, hθ, -, hlift⟩ := exists_continuousOn_arg_lift hab hg_cont hne
  rw [integral_deriv_smul_logDeriv_eq_log_norm_sub_add_I_mul_sub_of_arg_lift
    hab hγ hf hne hθ hlift]
  simp

/-- Along a closed piecewise-`C¹` curve `γ` (`γ a = γ b`) on which `f` is analytic and
nonvanishing, the winding number of `f ∘ γ` about `0` equals `(θ b - θ a) / (2 * π)` for any
continuous argument lift `θ` of `f ∘ γ`. -/
theorem windingNumber_comp_eq_sub_div_two_pi_of_closed_of_arg_lift
    (hab : a ≤ b) (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (hf : ∀ t ∈ Icc a b, AnalyticAt ℂ f (γ t)) (hne : ∀ t ∈ Icc a b, f (γ t) ≠ 0)
    (hθ : ContinuousOn θ (Icc a b))
    (hlift : ∀ t ∈ Icc a b, f (γ t) = (‖f (γ t)‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))) :
    windingNumber (f ∘ γ) a b 0 = (((θ b - θ a) / (2 * π) : ℝ) : ℂ) := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  rw [windingNumber_comp_eq_integral_logDeriv hγ (hu ▸ hf) (hu ▸ hne),
    integral_deriv_smul_logDeriv_eq_log_norm_sub_add_I_mul_sub_of_arg_lift hab hγ hf hne hθ hlift,
    hclosed, sub_self, Complex.ofReal_zero, zero_add]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp [hpi, Complex.I_ne_zero]

end ArgLift

section Backlund

variable {g : ℝ → ℂ} {a b : ℝ}

/-- If `g` is continuous with continuous derivative and nonvanishing on `[a, b]` (`a ≤ b`) and
`0 < (g t).re` on `(a, b)`, then `|(∫ t in a..b, deriv g t / g t).im| ≤ π`. Rotating `g` by `I`
places it in the closed upper half-plane on `[a, b]` and in the slit plane on `(a, b)`. -/
theorem abs_im_integral_deriv_div_le_pi_of_re_pos (hab : a ≤ b)
    (hg_cont : ContinuousOn g (Icc a b))
    (hg_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ g t)
    (hg_deriv_cont : ContinuousOn (deriv g) (Icc a b))
    (hg_ne : ∀ t ∈ Icc a b, g t ≠ 0)
    (hre_pos : ∀ t ∈ Ioo a b, 0 < (g t).re) :
    |(∫ t in a..b, deriv g t / g t).im| ≤ π := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp [Real.pi_nonneg]
  have hre_nn : ∀ t ∈ Icc a b, 0 ≤ (g t).re := by
    intro t ht
    have hcl : t ∈ closure (Ioo a b) := by rwa [closure_Ioo hab'.ne]
    have : (𝓝[Ioo a b] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      ((Complex.continuous_re.comp_continuousOn hg_cont t ht).mono Ioo_subset_Icc_self)
      (eventually_nhdsWithin_of_forall fun x hx ↦ (hre_pos x hx).le)
  let h : ℝ → ℂ := fun t ↦ Complex.I * g t
  have hderiv : deriv h = fun t ↦ Complex.I * deriv g t :=
    funext fun _ ↦ deriv_const_mul_field Complex.I
  have hquot : (fun t ↦ deriv h t / h t) = fun t ↦ deriv g t / g t :=
    funext fun t ↦ by rw [hderiv]; exact mul_div_mul_left _ _ Complex.I_ne_zero
  have hh_im : ∀ t ∈ Icc a b, 0 ≤ (h t).im := fun t ht ↦ by
    simpa [h] using hre_nn t ht
  have hftc :=
    intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_im_nonneg_of_le
      (g := h) (h := h) hab (continuousOn_const.mul hg_cont)
      (fun t ht ↦ (hg_diff t ht).const_mul Complex.I)
      (hderiv ▸ continuousOn_const.mul hg_deriv_cont)
      (fun t ht ↦ mul_ne_zero Complex.I_ne_zero (hg_ne t ht)) hh_im
      (fun t ht ↦ Complex.mem_slitPlane_iff.2 (Or.inr (by simpa [h] using (hre_pos t ht).ne')))
      (fun _ _ ↦ rfl) rfl rfl
  rw [← hquot, hftc.2, Complex.sub_im, Complex.log_im, Complex.log_im, abs_le]
  have ha0 : 0 ≤ Complex.arg (h a) := Complex.arg_nonneg_iff.2 (hh_im a (left_mem_Icc.2 hab))
  have hb0 : 0 ≤ Complex.arg (h b) := Complex.arg_nonneg_iff.2 (hh_im b (right_mem_Icc.2 hab))
  have haπ : Complex.arg (h a) ≤ π := Complex.arg_le_pi (h a)
  have hbπ : Complex.arg (h b) ≤ π := Complex.arg_le_pi (h b)
  constructor <;> linarith

/-- If `g` is continuous with continuous derivative and nonvanishing on `[a, b]` (`a ≤ b`) and
`(g t).re ≠ 0` on `(a, b)`, then `|(∫ t in a..b, deriv g t / g t).im| ≤ π`. -/
theorem abs_im_integral_deriv_div_le_pi_of_re_ne_zero (hab : a ≤ b)
    (hg_cont : ContinuousOn g (Icc a b))
    (hg_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ g t)
    (hg_deriv_cont : ContinuousOn (deriv g) (Icc a b))
    (hg_ne : ∀ t ∈ Icc a b, g t ≠ 0)
    (hre_ne : ∀ t ∈ Ioo a b, (g t).re ≠ 0) :
    |(∫ t in a..b, deriv g t / g t).im| ≤ π := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp [Real.pi_nonneg]
  have hre_cont : ContinuousOn (fun t ↦ (g t).re) (Ioo a b) :=
    (Complex.continuous_re.comp_continuousOn hg_cont).mono Ioo_subset_Icc_self
  set c := (a + b) / 2 with hc_def
  have hc : c ∈ Ioo a b := ⟨by linarith, by linarith⟩
  rcases lt_or_gt_of_ne (hre_ne c hc) with hc_neg | hc_pos
  · have hneg : ∀ t ∈ Ioo a b, 0 < (-g t).re := by
      intro t ht
      simp only [Complex.neg_re, Left.neg_pos_iff]
      by_contra hnot
      rw [not_lt] at hnot
      obtain ⟨x, hx, hx0⟩ := isPreconnected_Ioo.intermediate_value hc ht hre_cont
        ⟨hc_neg.le, hnot⟩
      exact hre_ne x hx hx0
    have hquot : (fun t ↦ deriv (-g) t / (-g) t) = fun t ↦ deriv g t / g t :=
      funext fun t ↦ by rw [deriv.neg, Pi.neg_apply, neg_div_neg_eq]
    rw [← hquot]
    exact abs_im_integral_deriv_div_le_pi_of_re_pos hab hg_cont.neg
      (fun t ht ↦ (hg_diff t ht).neg) (by simpa [deriv.neg] using hg_deriv_cont.neg)
      (fun t ht ↦ neg_ne_zero.2 (hg_ne t ht)) hneg
  · refine abs_im_integral_deriv_div_le_pi_of_re_pos hab hg_cont hg_diff hg_deriv_cont hg_ne ?_
    intro t ht
    by_contra hnot
    rw [not_lt] at hnot
    obtain ⟨x, hx, hx0⟩ := isPreconnected_Ioo.intermediate_value ht hc hre_cont
      ⟨hnot, hc_pos.le⟩
    exact hre_ne x hx hx0

private theorem card_filter_lt_add_card_filter_gt_add_one_le {S : Finset ℝ} {c : ℝ}
    [DecidablePred (· < c)] [DecidablePred (c < ·)] (hcS : c ∈ S) :
    (S.filter (· < c)).card + (S.filter (c < ·)).card + 1 ≤ S.card := by
  classical
  have hdisj : Disjoint (S.filter (· < c)) (S.filter (c < ·)) :=
    Finset.disjoint_left.2 fun x hx₁ hx₂ ↦
      lt_asymm (Finset.mem_filter.1 hx₁).2 (Finset.mem_filter.1 hx₂).2
  have hsub : S.filter (· < c) ∪ S.filter (c < ·) ⊆ S.erase c := fun x hx ↦ by
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Finset.mem_erase.2 ⟨(Finset.mem_filter.1 hx).2.ne, (Finset.mem_filter.1 hx).1⟩
    · exact Finset.mem_erase.2 ⟨(Finset.mem_filter.1 hx).2.ne', (Finset.mem_filter.1 hx).1⟩
  have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨c, hcS⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hcS] at hle
  omega

/-- **Backlund's real-part root bound.** If `g` is continuous with continuous derivative and
nonvanishing on `[a, b]` (`a ≤ b`) and every `t ∈ (a, b)` with `(g t).re = 0` belongs to the
finite set `S`, then `|(∫ t in a..b, deriv g t / g t).im| ≤ (S.card + 1) * π`. -/
theorem abs_im_integral_deriv_div_le_mul_pi_of_re_eq_zero_mem (hab : a ≤ b)
    (hg_cont : ContinuousOn g (Icc a b))
    (hg_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ g t)
    (hg_deriv_cont : ContinuousOn (deriv g) (Icc a b))
    (hg_ne : ∀ t ∈ Icc a b, g t ≠ 0) {S : Finset ℝ}
    (hS : ∀ t ∈ Ioo a b, (g t).re = 0 → t ∈ S) :
    |(∫ t in a..b, deriv g t / g t).im| ≤ (S.card + 1 : ℝ) * π := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, S.card = n := ⟨S.card, rfl⟩
  induction n using Nat.strong_induction_on generalizing a b S with
  | _ n ih =>
    by_cases hroot : ∃ c ∈ Ioo a b, c ∈ S
    · obtain ⟨c, ⟨hac, hcb⟩, hcS⟩ := hroot
      let S₁ := S.filter (· < c)
      let S₂ := S.filter (c < ·)
      have hcard : S₁.card + S₂.card + 1 ≤ n :=
        hn ▸ card_filter_lt_add_card_filter_gt_add_one_le hcS
      have hint : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
          IntervalIntegrable (fun t ↦ deriv g t / g t) volume x y := fun x y hax hxy hyb ↦
        ((hg_deriv_cont.div hg_cont hg_ne).mono
          (uIcc_of_le hxy ▸ Icc_subset_Icc hax hyb)).intervalIntegrable
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hint a c le_rfl hac.le hcb.le) (hint c b hac.le hcb.le le_rfl)
      have h₁ := ih S₁.card (by omega) hac.le (hg_cont.mono (Icc_subset_Icc_right hcb.le))
        (fun t ht ↦ hg_diff t ⟨ht.1, ht.2.trans hcb⟩)
        (hg_deriv_cont.mono (Icc_subset_Icc_right hcb.le))
        (fun t ht ↦ hg_ne t ⟨ht.1, ht.2.trans hcb.le⟩)
        (fun t ht h0 ↦ Finset.mem_filter.2 ⟨hS t ⟨ht.1, ht.2.trans hcb⟩ h0, ht.2⟩) rfl
      have h₂ := ih S₂.card (by omega) hcb.le (hg_cont.mono (Icc_subset_Icc_left hac.le))
        (fun t ht ↦ hg_diff t ⟨hac.trans ht.1, ht.2⟩)
        (hg_deriv_cont.mono (Icc_subset_Icc_left hac.le))
        (fun t ht ↦ hg_ne t ⟨hac.le.trans ht.1, ht.2⟩)
        (fun t ht h0 ↦ Finset.mem_filter.2 ⟨hS t ⟨hac.trans ht.1, ht.2⟩ h0, ht.1⟩) rfl
      have hcard_real : (S₁.card + 1 : ℝ) + (S₂.card + 1 : ℝ) ≤ (S.card + 1 : ℝ) := by
        exact_mod_cast (by omega : S₁.card + 1 + (S₂.card + 1) ≤ S.card + 1)
      rw [← hsplit, Complex.add_im]
      calc |(∫ t in a..c, deriv g t / g t).im + (∫ t in c..b, deriv g t / g t).im|
          ≤ |(∫ t in a..c, deriv g t / g t).im| + |(∫ t in c..b, deriv g t / g t).im| :=
            abs_add_le _ _
        _ ≤ (S₁.card + 1 : ℝ) * π + (S₂.card + 1 : ℝ) * π := add_le_add h₁ h₂
        _ = ((S₁.card + 1 : ℝ) + (S₂.card + 1 : ℝ)) * π := (add_mul _ _ _).symm
        _ ≤ (S.card + 1 : ℝ) * π := mul_le_mul_of_nonneg_right hcard_real Real.pi_nonneg
    · have hne : ∀ t ∈ Ioo a b, (g t).re ≠ 0 := fun t ht h0 ↦ hroot ⟨t, ht, hS t ht h0⟩
      have h1 : (1 : ℝ) * π ≤ (S.card + 1 : ℝ) * π :=
        mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) S.card]) Real.pi_nonneg
      exact (abs_im_integral_deriv_div_le_pi_of_re_ne_zero hab hg_cont hg_diff
        hg_deriv_cont hg_ne hne).trans (by simpa using h1)

/-- **Backlund's bound along a `C¹` curve.** For a differentiable curve `γ : ℝ → ℂ` with continuous
derivative, `f` analytic and nonvanishing along `γ` on `[a, b]` (`a ≤ b`), and `S : Finset ℝ`
containing every `t ∈ (a, b)` with `(f (γ t)).re = 0`,
`|(∫ t in a..b, deriv γ t • logDeriv f (γ t)).im| ≤ (S.card + 1) * π`. -/
theorem abs_im_integral_deriv_smul_logDeriv_le_mul_pi_of_re_eq_zero_mem
    {γ : ℝ → ℂ} {f : ℂ → ℂ} (hab : a ≤ b)
    (hγ_diff : Differentiable ℝ γ) (hγ_deriv : Continuous (deriv γ))
    (hf : ∀ t ∈ Icc a b, AnalyticAt ℂ f (γ t)) (hne : ∀ t ∈ Icc a b, f (γ t) ≠ 0)
    {S : Finset ℝ} (hS : ∀ t ∈ Ioo a b, (f (γ t)).re = 0 → t ∈ S) :
    |(∫ t in a..b, deriv γ t • logDeriv f (γ t)).im| ≤ (S.card + 1 : ℝ) * π := by
  let g : ℝ → ℂ := fun t ↦ f (γ t)
  have hg_hasDeriv : ∀ t ∈ Icc a b, HasDerivAt g (deriv γ t * deriv f (γ t)) t := fun t ht ↦ by
    simpa only [g, Function.comp_def, smul_eq_mul] using
      ((hf t ht).differentiableAt.hasDerivAt).scomp t (hγ_diff t).hasDerivAt
  have hg_cont : ContinuousOn g (Icc a b) := fun t ht ↦
    (hf t ht).continuousAt.comp_continuousWithinAt (hγ_diff.continuous.continuousWithinAt)
  have hg_deriv_eq : EqOn (deriv g) (fun t ↦ deriv γ t * deriv f (γ t)) (Icc a b) :=
    fun t ht ↦ (hg_hasDeriv t ht).deriv
  have hg_deriv_cont : ContinuousOn (deriv g) (Icc a b) := by
    refine ContinuousOn.congr ?_ hg_deriv_eq
    refine hγ_deriv.continuousOn.mul fun t ht ↦ ?_
    exact (hf t ht).deriv.continuousAt.comp_continuousWithinAt hγ_diff.continuous.continuousWithinAt
  have hcongr : ∫ t in a..b, deriv γ t • logDeriv f (γ t) = ∫ t in a..b, deriv g t / g t := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hab] at ht
    rw [hg_deriv_eq ht, smul_eq_mul, logDeriv_apply, mul_div_assoc]
  rw [hcongr]
  exact abs_im_integral_deriv_div_le_mul_pi_of_re_eq_zero_mem hab hg_cont
    (fun t ht ↦ (hg_hasDeriv t (Ioo_subset_Icc_self ht)).differentiableAt)
    hg_deriv_cont hne hS

end Backlund

end TauCeti.Contour
