/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Integral
public import TauCeti.MeasureTheory.Integral.Circle.Haar
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Poisson and Herglotz–Riesz integrals on the additive circle

Parametrizing the unit circle by `AddCircle.toCircle` turns normalized Haar integration on
`AddCircle T` (for any positive period `T`) into the unit-circle average. Consequently, integrating
boundary data on `AddCircle T` against `poissonKernel 0 w ∘ AddCircle.toCircle` produces the Poisson
extension on the open unit disk without passing through angular coordinates on `(−π, π]`.

This file develops the additive-circle Poisson and Herglotz–Riesz integrals:
* `TauCeti.circlePoissonIntegral` and `TauCeti.circleHerglotzRieszIntegral`;
* compatibility with `Real.circleAverage` and `TauCeti.planarPoissonIntegral`, preservation of
  constants, positivity, monotonicity, and the quadratic Jensen/Cauchy–Schwarz inequality
  `‖P[f](w)‖ ^ 2 ≤ P[‖f‖ ^ 2](w)` on the open unit disk;
* holomorphy of `circleHerglotzRieszIntegral` and harmonicity of real `circlePoissonIntegral` away
  from the unit circle;
* evaluation on nonnegative and nonpositive Fourier modes (`w ^ n` and `conj w ^ n`), and uniform
  convergence of the rescaled kernels `t ↦ poissonKernel 0 (r⁻¹ * w) (toCircle t)` as `r → 1`.

## References

* P. L. Duren, *Theory of Hᵖ Spaces*, Academic Press (1970), Chapter 1.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), Chapter 11.
-/

public section

noncomputable section

namespace TauCeti

open Complex Filter InnerProductSpace MeasureTheory Metric Real Set Topology
open scoped ENNReal

section PoissonIntegral

variable {T : ℝ} [Fact (0 < T)] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Poisson integral on the open unit disk of boundary data on `AddCircle T`, integrated
against normalized Haar measure. -/
def circlePoissonIntegral (f : AddCircle T → E) (w : ℂ) : E :=
  ∫ t : AddCircle T, poissonKernel 0 w (AddCircle.toCircle t) • f t ∂AddCircle.haarAddCircle

/-- Unfolded form of `circlePoissonIntegral`. -/
theorem circlePoissonIntegral_def (f : AddCircle T → E) (w : ℂ) :
    circlePoissonIntegral f w =
      ∫ t : AddCircle T, poissonKernel 0 w (AddCircle.toCircle t) • f t ∂AddCircle.haarAddCircle :=
  (rfl)

/-- Boundary functions equal almost everywhere for Haar measure have identical Poisson integrals. -/
theorem circlePoissonIntegral_congr_ae {f₁ f₂ : AddCircle T → E}
    (h : f₁ =ᵐ[AddCircle.haarAddCircle] f₂) (w : ℂ) :
    circlePoissonIntegral f₁ w = circlePoissonIntegral f₂ w :=
  integral_congr_ae (h.mono fun _ ht ↦ by dsimp only; rw [ht])

omit [Fact (0 < T)] in
/-- For `w` off the unit circle, `t ↦ poissonKernel 0 w (toCircle t)` is continuous on
`AddCircle T`. -/
@[fun_prop]
theorem continuous_poissonKernel_toCircle {w : ℂ} (hw : w ∉ sphere (0 : ℂ) 1) :
    Continuous fun t : AddCircle T ↦ poissonKernel 0 w (AddCircle.toCircle t) := by
  refine (continuousOn_poissonKernel (c := 0) hw).comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle) fun t ↦ ?_
  simp

/-- Away from the unit circle, multiplying Haar-integrable data by the Poisson kernel preserves
integrability. -/
theorem integrable_poissonKernel_smul {f : AddCircle T → E}
    (hf : Integrable f AddCircle.haarAddCircle) {w : ℂ} (hw : w ∉ sphere (0 : ℂ) 1) :
    Integrable (fun t : AddCircle T ↦ poissonKernel 0 w (AddCircle.toCircle t) • f t)
      AddCircle.haarAddCircle := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_poissonKernel_toCircle (T := T) hw).continuousOn
  refine Integrable.mono' (hf.norm.const_mul C)
    ((continuous_poissonKernel_toCircle hw).aestronglyMeasurable.smul hf.aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC t (mem_univ t)) (norm_nonneg _)

/-- The Poisson integral of zero is identically zero. -/
@[simp]
theorem circlePoissonIntegral_zero (w : ℂ) :
    circlePoissonIntegral (fun _ : AddCircle T ↦ (0 : E)) w = 0 := by
  simp [circlePoissonIntegral_def]

/-- At the origin the Poisson kernel equals `1` on the circle, so `circlePoissonIntegral` reduces
to the Haar average. -/
@[simp]
theorem circlePoissonIntegral_eval_zero (f : AddCircle T → E) :
    circlePoissonIntegral f 0 = ∫ t : AddCircle T, f t ∂AddCircle.haarAddCircle := by
  rw [circlePoissonIntegral_def]
  congr 1
  funext t
  simp [poissonKernel_def]

/-- Pulling ambient data on `ℂ` back along `AddCircle.toCircle` identifies `circlePoissonIntegral`
with the unit-circle average against `poissonKernel 0 w`. -/
theorem circlePoissonIntegral_comp_toCircle (g : ℂ → E) (w : ℂ) :
    circlePoissonIntegral (fun t : AddCircle T ↦ g (AddCircle.toCircle t)) w =
      circleAverage (poissonKernel 0 w • g) 0 1 := by
  simpa only [circlePoissonIntegral_def, Complex.ofReal_one, one_mul, add_zero,
    Pi.smul_apply'] using
    AddCircle.integral_haarAddCircle_comp_toCircle (T := T) (poissonKernel 0 w • g) 0 1

/-- For real ambient data on `ℂ`, `circlePoissonIntegral` after `AddCircle.toCircle` agrees with
`planarPoissonIntegral` on the unit disk. -/
theorem circlePoissonIntegral_comp_toCircle_eq_planarPoissonIntegral (g : ℂ → ℝ) (w : ℂ) :
    circlePoissonIntegral (fun t : AddCircle T ↦ g (AddCircle.toCircle t)) w =
      planarPoissonIntegral g 0 1 w :=
  (circlePoissonIntegral_comp_toCircle g w).trans (planarPoissonIntegral_def g 0 1 w).symm

/-- On the open unit disk, the Poisson kernel has total mass `1` against normalized Haar measure. -/
@[simp]
theorem integral_haarAddCircle_poissonKernel {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (∫ t : AddCircle T, poissonKernel 0 w (AddCircle.toCircle t) ∂AddCircle.haarAddCircle) = 1 := by
  have h := circlePoissonIntegral_comp_toCircle_eq_planarPoissonIntegral
    (T := T) (fun _ : ℂ ↦ (1 : ℝ)) w
  rw [planarPoissonIntegral_const (by simpa using hw), circlePoissonIntegral_def] at h
  simpa only [smul_eq_mul, mul_one] using h

/-- Inside the open unit disk, the Poisson integral reproduces constant boundary data. -/
@[simp]
theorem circlePoissonIntegral_const [CompleteSpace E] {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (a : E) :
    circlePoissonIntegral (fun _ : AddCircle T ↦ a) w = a := by
  rw [circlePoissonIntegral_def, integral_smul_const, integral_haarAddCircle_poissonKernel hw,
    one_smul]

/-- The Poisson integral commutes with real scalar multiplication. -/
@[simp]
theorem circlePoissonIntegral_smul (c : ℝ) (f : AddCircle T → E) (w : ℂ) :
    circlePoissonIntegral (c • f) w = c • circlePoissonIntegral f w := by
  simp only [circlePoissonIntegral_def, Pi.smul_apply, smul_comm _ c, integral_smul]

/-- Away from the unit circle, `circlePoissonIntegral` is additive on Haar-integrable data. -/
theorem circlePoissonIntegral_add {f₁ f₂ : AddCircle T → E}
    (hf₁ : Integrable f₁ AddCircle.haarAddCircle) (hf₂ : Integrable f₂ AddCircle.haarAddCircle)
    {w : ℂ} (hw : w ∉ sphere (0 : ℂ) 1) :
    circlePoissonIntegral (f₁ + f₂) w =
      circlePoissonIntegral f₁ w + circlePoissonIntegral f₂ w := by
  simp only [circlePoissonIntegral_def, Pi.add_apply, smul_add]
  exact integral_add (integrable_poissonKernel_smul hf₁ hw) (integrable_poissonKernel_smul hf₂ hw)

/-- Almost-everywhere nonnegative real data have nonnegative Poisson integral on the open unit
disk. -/
theorem circlePoissonIntegral_nonneg {f : AddCircle T → ℝ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1)
    (hf : 0 ≤ᵐ[AddCircle.haarAddCircle] f) :
    0 ≤ circlePoissonIntegral f w := by
  rw [circlePoissonIntegral_def]
  refine integral_nonneg_of_ae (hf.mono fun t ht ↦ mul_nonneg ?_ ht)
  exact poissonKernel_nonneg (by simpa using (mem_ball_zero_iff.mp hw).le)

/-- On the open unit disk, `circlePoissonIntegral` is monotone with respect to almost-everywhere
inequalities between integrable functions. -/
theorem circlePoissonIntegral_mono {f₁ f₂ : AddCircle T → ℝ}
    (hf₁ : Integrable f₁ AddCircle.haarAddCircle) (hf₂ : Integrable f₂ AddCircle.haarAddCircle)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hle : f₁ ≤ᵐ[AddCircle.haarAddCircle] f₂) :
    circlePoissonIntegral f₁ w ≤ circlePoissonIntegral f₂ w := by
  have hw' : w ∉ sphere (0 : ℂ) 1 := disjoint_right.mp sphere_disjoint_ball hw
  rw [circlePoissonIntegral_def, circlePoissonIntegral_def]
  refine integral_mono_ae (integrable_poissonKernel_smul hf₁ hw')
    (integrable_poissonKernel_smul hf₂ hw') (hle.mono fun t ht ↦ ?_)
  exact mul_le_mul_of_nonneg_left ht
    (poissonKernel_nonneg (by simpa using (mem_ball_zero_iff.mp hw).le))

/-- **Quadratic Jensen / Cauchy–Schwarz inequality for the Poisson integral.** For square-integrable
boundary data `f` and `w` in the open unit disk, the squared norm of `circlePoissonIntegral f w` is
at most the Poisson integral of `t ↦ ‖f t‖ ^ 2`. -/
theorem norm_circlePoissonIntegral_sq_le {f : AddCircle T → E}
    (hf : MemLp f 2 AddCircle.haarAddCircle) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ‖circlePoissonIntegral f w‖ ^ 2 ≤ circlePoissonIntegral (fun t ↦ ‖f t‖ ^ 2) w := by
  have hw' : w ∉ sphere (0 : ℂ) 1 := disjoint_right.mp sphere_disjoint_ball hw
  have hf1 : Integrable f AddCircle.haarAddCircle := hf.integrable one_le_two
  have hf2 : Integrable (fun t ↦ ‖f t‖ ^ 2) AddCircle.haarAddCircle := hf.integrable_norm_pow
    two_ne_zero
  set P : AddCircle T → ℝ := fun t ↦ poissonKernel 0 w (AddCircle.toCircle t)
  have hP_nonneg (t : AddCircle T) : 0 ≤ P t :=
    poissonKernel_nonneg (by simpa using (mem_ball_zero_iff.mp hw).le)
  set c : ℝ := circlePoissonIntegral (fun t ↦ ‖f t‖) w with hc_def
  have hnorm_le : ‖circlePoissonIntegral f w‖ ≤ c := by
    calc ‖circlePoissonIntegral f w‖
        ≤ ∫ t, ‖P t • f t‖ ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
      _ = c := by
        rw [hc_def, circlePoissonIntegral_def]
        refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
        dsimp only
        rw [norm_smul, Real.norm_of_nonneg (hP_nonneg t), smul_eq_mul]
  have hsq_le : ‖circlePoissonIntegral f w‖ ^ 2 ≤ c ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
  -- Expand the nonnegative integral `∫ P t * (‖f t‖ - c) ^ 2 ≥ 0`.
  have hPf2 : Integrable (fun t ↦ P t * ‖f t‖ ^ 2) AddCircle.haarAddCircle :=
    integrable_poissonKernel_smul hf2 hw'
  have hPf1 : Integrable (fun t ↦ P t * ‖f t‖) AddCircle.haarAddCircle :=
    integrable_poissonKernel_smul hf1.norm hw'
  have hPc : Integrable (fun t ↦ P t * c ^ 2) AddCircle.haarAddCircle :=
    integrable_poissonKernel_smul (integrable_const (c ^ 2)) hw'
  have hnonneg : 0 ≤ ∫ t, P t * (‖f t‖ - c) ^ 2 ∂AddCircle.haarAddCircle :=
    integral_nonneg fun t ↦ mul_nonneg (hP_nonneg t) (sq_nonneg _)
  have hexpand : (∫ t, P t * (‖f t‖ - c) ^ 2 ∂AddCircle.haarAddCircle) =
      circlePoissonIntegral (fun t ↦ ‖f t‖ ^ 2) w - c ^ 2 := by
    have hfun (t : AddCircle T) : P t * (‖f t‖ - c) ^ 2 =
        (P t * ‖f t‖ ^ 2 - (2 * c) * (P t * ‖f t‖)) + P t * c ^ 2 := by
      ring
    have hdiff : Integrable (fun t ↦ P t * ‖f t‖ ^ 2 - 2 * c * (P t * ‖f t‖))
        AddCircle.haarAddCircle := hPf2.sub (hPf1.const_mul (2 * c))
    simp_rw [hfun]
    rw [integral_add hdiff hPc,
      integral_sub hPf2 (hPf1.const_mul (2 * c)), integral_const_mul, integral_mul_const,
      integral_haarAddCircle_poissonKernel hw]
    simp only [hc_def, circlePoissonIntegral_def, P, smul_eq_mul]
    ring
  linarith

end PoissonIntegral

/-! ### Herglotz–Riesz holomorphy and Poisson harmonicity -/

section Harmonic

variable {T : ℝ} [Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Herglotz–Riesz integral on `AddCircle T` against normalized Haar measure. -/
def circleHerglotzRieszIntegral (f : AddCircle T → F) (w : ℂ) : F :=
  ∫ t : AddCircle T, herglotzRieszKernel 0 w (AddCircle.toCircle t) • f t ∂AddCircle.haarAddCircle

/-- Unfolded form of `circleHerglotzRieszIntegral`. -/
theorem circleHerglotzRieszIntegral_def (f : AddCircle T → F) (w : ℂ) :
    circleHerglotzRieszIntegral f w =
      ∫ t : AddCircle T,
        herglotzRieszKernel 0 w (AddCircle.toCircle t) • f t ∂AddCircle.haarAddCircle :=
  (rfl)

/-- Differentiating `circleHerglotzRieszIntegral` under the Haar integral at any pole `w` off the
unit circle. -/
theorem hasDerivAt_circleHerglotzRieszIntegral {f : AddCircle T → F}
    (hf : Integrable f AddCircle.haarAddCircle) {w : ℂ} (hw : w ∉ sphere (0 : ℂ) 1) :
    HasDerivAt (circleHerglotzRieszIntegral f)
      (∫ t : AddCircle T,
        (2 * (AddCircle.toCircle t : ℂ) / ((AddCircle.toCircle t : ℂ) - w) ^ 2) • f t
          ∂AddCircle.haarAddCircle) w := by
  have hne1 : ‖w‖ ≠ 1 := by simpa [mem_sphere_zero_iff_norm] using hw
  set d : ℝ := |1 - ‖w‖| / 2 with hd_def
  have hd : 0 < d := half_pos (abs_pos.mpr (sub_ne_zero.mpr hne1.symm))
  have hdist : ∀ x ∈ ball w d, ∀ t : AddCircle T, d ≤ ‖(AddCircle.toCircle t : ℂ) - x‖ := by
    intro x hx t
    have hx' : ‖x - w‖ < d := mem_ball_iff_norm.mp hx
    have hzt : ‖(AddCircle.toCircle t : ℂ)‖ = 1 := Circle.norm_coe _
    have htri1 : 1 - ‖w‖ - ‖x - w‖ ≤ ‖(AddCircle.toCircle t : ℂ) - x‖ := by
      have h1 := norm_sub_norm_le (AddCircle.toCircle t : ℂ) x
      have h2 := norm_add_le w (x - w)
      rw [add_sub_cancel] at h2
      linarith
    have htri2 : ‖w‖ - 1 - ‖x - w‖ ≤ ‖(AddCircle.toCircle t : ℂ) - x‖ := by
      have h1 := norm_sub_norm_le x (AddCircle.toCircle t : ℂ)
      have h2 := norm_add_le x (w - x)
      rw [add_sub_cancel, norm_sub_rev] at h2
      rw [norm_sub_rev] at h1
      linarith
    rcases le_or_gt ‖w‖ 1 with hw1 | hw1
    · have habs : |1 - ‖w‖| = 1 - ‖w‖ := abs_of_nonneg (sub_nonneg.mpr hw1)
      linarith [hd_def, habs]
    · have habs : |1 - ‖w‖| = ‖w‖ - 1 := by
        rw [abs_of_neg (sub_neg.mpr hw1), neg_sub]
      linarith [hd_def, habs]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := ball w d)
    (F := fun x t ↦ herglotzRieszKernel 0 x (AddCircle.toCircle t) • f t)
    (F' := fun x t ↦ (2 * (AddCircle.toCircle t : ℂ) / ((AddCircle.toCircle t : ℂ) - x) ^ 2) • f t)
    (bound := fun t ↦ (2 / d ^ 2) * ‖f t‖)
    (ball_mem_nhds w hd) ?_ ?_ ?_ ?_ ?_ ?_).2
  · refine Eventually.of_forall fun x ↦ ?_
    have hc : Measurable fun t : AddCircle T ↦ herglotzRieszKernel 0 x (AddCircle.toCircle t) := by
      simp only [herglotzRieszKernel_def, sub_zero]
      fun_prop
    exact hc.aestronglyMeasurable.smul hf.aestronglyMeasurable
  · have hK : Continuous fun t : AddCircle T ↦
        herglotzRieszKernel 0 w (AddCircle.toCircle t) := by
      refine (continuousOn_herglotzRieszKernel_sphere (c := 0) (R := 1)
        (by simpa using hw)).comp_continuous
        (continuous_subtype_val.comp AddCircle.continuous_toCircle) fun t ↦ ?_
      simp
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuousOn
    refine Integrable.mono' (hf.norm.const_mul C)
      (hK.aestronglyMeasurable.smul hf.aestronglyMeasurable) ?_
    filter_upwards with t
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC t (mem_univ t)) (norm_nonneg _)
  · have hc : Measurable fun t : AddCircle T ↦
        2 * (AddCircle.toCircle t : ℂ) / ((AddCircle.toCircle t : ℂ) - w) ^ 2 := by
      fun_prop
    exact hc.aestronglyMeasurable.smul hf.aestronglyMeasurable
  · refine Eventually.of_forall fun t x hx ↦ ?_
    rw [norm_smul, norm_div, norm_mul, Circle.norm_coe, mul_one, Complex.norm_ofNat, norm_pow]
    gcongr
    exact hdist x hx t
  · exact hf.norm.const_mul _
  · refine Eventually.of_forall fun t x hx ↦ ?_
    have hsub : (AddCircle.toCircle t : ℂ) - x ≠ 0 :=
      norm_pos_iff.mp (hd.trans_le (hdist x hx t))
    have hderiv : HasDerivAt (fun z ↦ herglotzRieszKernel 0 z (AddCircle.toCircle t))
        (2 * (AddCircle.toCircle t : ℂ) / ((AddCircle.toCircle t : ℂ) - x) ^ 2) x := by
      have h := ((hasDerivAt_id' x).const_add (AddCircle.toCircle t : ℂ)).div
        ((hasDerivAt_id' x).const_sub (AddCircle.toCircle t : ℂ)) hsub
      simpa [herglotzRieszKernel_def, sub_zero, sub_sub, ← two_mul, Pi.div_def] using h
    exact hderiv.smul_const (f t)

/-- The Herglotz–Riesz integral of Haar-integrable data is holomorphic away from the unit circle. -/
theorem differentiableOn_circleHerglotzRieszIntegral {f : AddCircle T → F}
    (hf : Integrable f AddCircle.haarAddCircle) :
    DifferentiableOn ℂ (circleHerglotzRieszIntegral f) (sphere (0 : ℂ) 1)ᶜ :=
  fun _ hw ↦ (hasDerivAt_circleHerglotzRieszIntegral hf hw).differentiableAt.differentiableWithinAt

/-- When the target is complete, the Herglotz–Riesz integral of Haar-integrable data is complex
analytic away from the unit circle. -/
theorem analyticOnNhd_circleHerglotzRieszIntegral [CompleteSpace F] {f : AddCircle T → F}
    (hf : Integrable f AddCircle.haarAddCircle) :
    AnalyticOnNhd ℂ (circleHerglotzRieszIntegral f) (sphere (0 : ℂ) 1)ᶜ :=
  (differentiableOn_circleHerglotzRieszIntegral hf).analyticOnNhd isClosed_sphere.isOpen_compl

/-- For real Haar-integrable data, the Poisson integral is the real part of the Herglotz–Riesz
integral away from the unit circle. -/
theorem re_circleHerglotzRieszIntegral {g : AddCircle T → ℝ}
    (hg : Integrable g AddCircle.haarAddCircle) {w : ℂ} (hw : w ∉ sphere (0 : ℂ) 1) :
    (circleHerglotzRieszIntegral (fun t ↦ (g t : ℂ)) w).re = circlePoissonIntegral g w := by
  have hgc : Integrable (fun t ↦ (g t : ℂ)) AddCircle.haarAddCircle :=
    Complex.ofRealCLM.integrable_comp hg
  have hK : Continuous fun t : AddCircle T ↦
      herglotzRieszKernel 0 w (AddCircle.toCircle t) := by
    refine (continuousOn_herglotzRieszKernel_sphere (c := 0) (R := 1)
      (by simpa using hw)).comp_continuous
      (continuous_subtype_val.comp AddCircle.continuous_toCircle) fun t ↦ ?_
    simp
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuousOn
  have hint : Integrable
      (fun t : AddCircle T ↦ herglotzRieszKernel 0 w (AddCircle.toCircle t) • (g t : ℂ))
      AddCircle.haarAddCircle := by
    refine Integrable.mono' (hgc.norm.const_mul C)
      (hK.aestronglyMeasurable.smul hgc.aestronglyMeasurable) ?_
    filter_upwards with t
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC t (mem_univ t)) (norm_nonneg _)
  rw [circleHerglotzRieszIntegral_def, ← Complex.reCLM_apply,
    ← Complex.reCLM.integral_comp_comm hint, circlePoissonIntegral_def]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp [poissonKernel_eq_re_herglotzRieszKernel, Complex.mul_re]

/-- The Poisson integral of Haar-integrable real boundary data is harmonic away from the unit
circle. -/
theorem harmonicOnNhd_circlePoissonIntegral {g : AddCircle T → ℝ}
    (hg : Integrable g AddCircle.haarAddCircle) :
    HarmonicOnNhd (circlePoissonIntegral g) (sphere (0 : ℂ) 1)ᶜ := by
  have hH : AnalyticOnNhd ℂ (circleHerglotzRieszIntegral fun t ↦ (g t : ℂ)) (sphere (0 : ℂ) 1)ᶜ :=
    analyticOnNhd_circleHerglotzRieszIntegral (Complex.ofRealCLM.integrable_comp hg)
  intro w hw
  have heq : circlePoissonIntegral g =ᶠ[𝓝 w]
      fun z ↦ (circleHerglotzRieszIntegral (fun t ↦ (g t : ℂ)) z).re := by
    filter_upwards [isClosed_sphere.isOpen_compl.mem_nhds hw] with z hz
    exact (re_circleHerglotzRieszIntegral hg hz).symm
  exact (harmonicAt_congr_nhds heq).mpr (hH w hw).harmonicAt_re

/-- The Poisson integral of Haar-integrable real boundary data is harmonic on the open unit disk. -/
theorem harmonicOnNhd_ball_circlePoissonIntegral {g : AddCircle T → ℝ}
    (hg : Integrable g AddCircle.haarAddCircle) :
    HarmonicOnNhd (circlePoissonIntegral g) (ball (0 : ℂ) 1) :=
  (harmonicOnNhd_circlePoissonIntegral hg).mono
    fun _ hw ↦ disjoint_right.mp sphere_disjoint_ball hw

end Harmonic

/-! ### Fourier modes and rescaled Poisson kernels -/

section FourierAndRescaling

variable {T : ℝ} [Fact (0 < T)]

/-- On the open unit disk, the Poisson integral of a nonnegative Fourier mode `fourier n` is the
holomorphic monomial `w ^ n`. -/
@[simp]
theorem circlePoissonIntegral_fourier_nat {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (n : ℕ) :
    circlePoissonIntegral (fourier (T := T) (n : ℤ)) w = w ^ n := by
  have hfun : (fourier (T := T) (n : ℤ) : AddCircle T → ℂ) =
      fun t ↦ ((AddCircle.toCircle t : ℂ) ^ n) := by
    funext t
    rw [fourier_apply, natCast_zsmul, AddCircle.toCircle_nsmul, Circle.coe_pow]
  rw [hfun, circlePoissonIntegral_comp_toCircle (fun z : ℂ ↦ z ^ n)]
  exact (differentiable_id.pow n).diffContOnCl.circleAverage_poissonKernel_smul hw

/-- On the open unit disk, the Poisson integral of a nonpositive Fourier mode `fourier (-n)` is the
antiholomorphic monomial `conj w ^ n`. -/
@[simp]
theorem circlePoissonIntegral_fourier_neg_nat {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (n : ℕ) :
    circlePoissonIntegral (fourier (T := T) (-(n : ℤ))) w = (starRingEnd ℂ w) ^ n := by
  have hconj : (fourier (T := T) (-(n : ℤ)) : AddCircle T → ℂ) =
      fun t ↦ starRingEnd ℂ (fourier (T := T) (n : ℤ) t) := by
    funext t
    rw [fourier_apply, fourier_apply, neg_zsmul, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]
  have hw' : w ∉ sphere (0 : ℂ) 1 := disjoint_right.mp sphere_disjoint_ball hw
  have hint := integrable_poissonKernel_smul
    ((fourier (T := T) (n : ℤ)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) hw'
  calc circlePoissonIntegral (fourier (T := T) (-(n : ℤ))) w
      = ∫ t : AddCircle T,
          starRingEnd ℂ (poissonKernel 0 w (AddCircle.toCircle t) • fourier (T := T) (n : ℤ) t)
            ∂AddCircle.haarAddCircle := by
        rw [circlePoissonIntegral_def, hconj]
        refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
        simp [Complex.real_smul]
    _ = starRingEnd ℂ (circlePoissonIntegral (fourier (T := T) (n : ℤ)) w) := by
        have hcomm := Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hint
        simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
          circlePoissonIntegral_def] using hcomm
    _ = (starRingEnd ℂ w) ^ n := by
        rw [circlePoissonIntegral_fourier_nat hw, map_pow]

/-- For a fixed interior point `w` of the open unit disk, the rescaled Poisson kernels
`t ↦ poissonKernel 0 (r⁻¹ * w) (toCircle t)` converge uniformly on `AddCircle T` to
`t ↦ poissonKernel 0 w (toCircle t)` as `r → 1`. -/
theorem tendstoUniformly_poissonKernel_inv_mul {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    TendstoUniformly
      (fun (r : ℝ) (t : AddCircle T) ↦ poissonKernel 0 ((r : ℂ)⁻¹ * w) (AddCircle.toCircle t))
      (fun t : AddCircle T ↦ poissonKernel 0 w (AddCircle.toCircle t)) (𝓝 1) := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  set r₀ : ℝ := (‖w‖ + 1) / 2 with hr₀_def
  have hr₀_pos : 0 < r₀ := by positivity
  have hr₀_lt : r₀ < 1 := by linarith [hr₀_def]
  have hwr₀ : ‖w‖ < r₀ := by linarith [hr₀_def]
  set K : Set (ℝ × AddCircle T) := Icc r₀ 2 ×ˢ univ
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_univ
  let G : ℝ × AddCircle T → ℝ := fun p ↦
    (1 - ‖((p.1⁻¹ : ℝ) : ℂ) * w‖ ^ 2) /
      ‖(AddCircle.toCircle p.2 : ℂ) - ((p.1⁻¹ : ℝ) : ℂ) * w‖ ^ 2
  have hG_eq (p : ℝ × AddCircle T) :
      G p = poissonKernel 0 ((p.1 : ℂ)⁻¹ * w) (AddCircle.toCircle p.2) := by
    simp [G, poissonKernel_def]
  have hinv_cont : ContinuousOn (fun p : ℝ × AddCircle T ↦ ((p.1⁻¹ : ℝ) : ℂ)) K :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuous_fst.continuousOn.inv₀ fun p hp ↦ (hr₀_pos.trans_le hp.1.1).ne')
  have hcircle_cont : ContinuousOn (fun p : ℝ × AddCircle T ↦ (AddCircle.toCircle p.2 : ℂ)) K :=
    (continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp continuous_snd)).continuousOn
  have hG_cont : ContinuousOn G K := by
    refine ContinuousOn.div
      (continuousOn_const.sub (((hinv_cont.mul continuousOn_const).norm).pow 2))
      (((hcircle_cont.sub (hinv_cont.mul continuousOn_const)).norm).pow 2)
      fun p hp ↦ ?_
    have hp1 : r₀ ≤ p.1 := hp.1.1
    have hp_pos : 0 < p.1 := hr₀_pos.trans_le hp1
    have hlt : ‖((p.1⁻¹ : ℝ) : ℂ) * w‖ < ‖(AddCircle.toCircle p.2 : ℂ)‖ := by
      rw [Circle.norm_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
        abs_of_pos hp_pos, inv_mul_lt_iff₀ hp_pos, mul_one]
      exact hwr₀.trans_le hp1
    have hsub_pos : 0 < ‖(AddCircle.toCircle p.2 : ℂ) - ((p.1⁻¹ : ℝ) : ℂ) * w‖ := by
      have htri := norm_sub_norm_le (AddCircle.toCircle p.2 : ℂ) (((p.1⁻¹ : ℝ) : ℂ) * w)
      linarith
    exact pow_ne_zero 2 hsub_pos.ne'
  have hunif :=
    Metric.uniformContinuousOn_iff.mp (hK_compact.uniformContinuousOn_of_continuous hG_cont)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδG⟩ := hunif ε hε
  have hev1 : ∀ᶠ r : ℝ in 𝓝 1, r ∈ Icc r₀ 2 :=
    Icc_mem_nhds hr₀_lt (by norm_num : (1 : ℝ) < 2)
  have hev2 : ∀ᶠ r : ℝ in 𝓝 1, dist r 1 < δ := Metric.ball_mem_nhds 1 hδ
  filter_upwards [hev1, hev2] with r hrK hrδ t
  have h1K : ((1 : ℝ), t) ∈ K := ⟨⟨hr₀_lt.le, by norm_num⟩, mem_univ t⟩
  have hrK' : (r, t) ∈ K := ⟨hrK, mem_univ t⟩
  have hdist : dist ((1 : ℝ), t) (r, t) < δ := by
    simpa [Prod.dist_eq, dist_comm] using hrδ
  have hval := hδG (1, t) h1K (r, t) hrK' hdist
  simpa [hG_eq] using hval

end FourierAndRescaling

end TauCeti

end
