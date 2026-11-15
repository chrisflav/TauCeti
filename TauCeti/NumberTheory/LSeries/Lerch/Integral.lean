/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand
public import TauCeti.NumberTheory.LSeries.Lerch.Differential

import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Lerch zeta integral and slit-plane continuation in `z`

For `z ∈ ℂ \ [1, ∞)` (`1 - z ∈ Complex.slitPlane`), `0 < s.re`, and `0 < c.re`, the Laplace–Mellin
zeta integral

`lerchIntegral z s c`
`= (Gamma s)⁻¹ * ∫ t in Ioi 0, t ^ (s - 1) * exp (-(c * t)) / (1 - z * exp (-t))`

converges absolutely and defines a jointly holomorphic function of `(z, s, c)`. On compact subsets
of `{z | 1 - z ∈ slitPlane}`, the denominator `1 - z * exp (-t)` stays uniformly bounded away from
zero for all `t ≥ 0` because `exp (-t) ∈ [0, 1]` and `Complex.slitPlane` is star-convex at `1`.
Combining this lower bound with real Gamma majorants and Mathlib's Mellin differentiability theorem
justifies joint continuity and partial complex differentiability in all three parameters, and
Osgood's lemma upgrades these to joint analyticity.

On the overlap `‖z‖ < 1`, `0 < s.re`, `0 < c.re`, expanding `(1 - z * exp (-t))⁻¹` as a geometric
series and interchanging sum and integral against
`Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos` shows
`lerchIntegral z s c = lerchSeries z s c`, providing the analytic continuation of `lerchSeries` in
`z` from the open unit disc across the unit circle to the cut plane `ℂ \ [1, ∞)`.
By the identity principle along `u ↦ 1 - u` on the star-convex domain `Complex.slitPlane`, both the
`c`-shift functional identity and the weight-one polylogarithm relation
`z * Φ(z, 1, 1) = -log (1 - z)` extend to all `z` with `1 - z ∈ Complex.slitPlane`.

## Main definitions and results

* `TauCeti.exists_le_norm_one_sub_mul_exp_neg`: uniform positive lower bound on
  `‖1 - z * exp (-t)‖` for `t ≥ 0` and `z` in a compact subset of `{z | 1 - z ∈ slitPlane}`.
* `TauCeti.lerchIntegrand`, `TauCeti.lerchIntegral`: the Lerch zeta integrand and integral.
* `TauCeti.integrableOn_lerchIntegrand`: integrability on `Ioi 0` for `1 - z ∈ slitPlane`,
  `0 < s.re`, `0 < c.re`.
* `TauCeti.hasDerivAt_lerchIntegral_right`: slit-plane `s`-raising relation
  `∂_c lerchIntegral z s c = -s * lerchIntegral z (s + 1) c`.
* `TauCeti.analyticOnNhd_lerchIntegral`, `TauCeti.differentiableOn_lerchIntegral`,
  `AnalyticAt.lerchIntegral`: joint holomorphy on `1 - z ∈ slitPlane`, `0 < s.re`, `0 < c.re`.
* `TauCeti.lerchIntegral_eq_lerchSeries`: agreement with `lerchSeries` on `‖z‖ < 1`, `0 < s.re`,
  `0 < c.re`.
* `TauCeti.lerchIntegral_shift`, `TauCeti.mul_lerchIntegral_one_one`: slit-plane continuation of
  the `c`-shift identity and `z * lerchIntegral z 1 1 = Polylog.polylog 1 z`.

## References

* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function I. Zeta integrals*,
  Forum Math. **24** (2012), 1–48, §1 (1.2) and §3.
-/

public section

open Asymptotics Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace TauCeti

/-! ### Definition and integrability of the Lerch zeta integral -/

/-- On any compact subset `K ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane}`, the denominator
`1 - z * exp (-t)` is bounded below in norm by a uniform positive constant for all `t ≥ 0`. -/
theorem exists_le_norm_one_sub_mul_exp_neg {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane}) :
    ∃ δ > 0, ∀ z ∈ K, ∀ t : ℝ, 0 ≤ t → δ ≤ ‖1 - z * Complex.exp (-(t : ℂ))‖ := by
  obtain ⟨δ, hδ, h⟩ := Polylog.exists_le_norm_one_sub_ofReal_mul hK hKΩ
  refine ⟨δ, hδ, fun z hz t ht => ?_⟩
  have hmem : Real.exp (-t) ∈ Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  have heq : (1 : ℂ) - Real.exp (-t) * z = 1 - z * Complex.exp (-(t : ℂ)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_neg, mul_comm]
  simpa only [heq] using h z hz (Real.exp (-t)) hmem

/-- The integrand `t ^ (s - 1) * exp (-(c * t)) / (1 - z * exp (-t))` of the Lerch zeta integral on
`(0, ∞)`. -/
noncomputable def lerchIntegrand (z s c : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * Complex.exp (-(c * t)) / (1 - z * Complex.exp (-(t : ℂ)))

@[simp]
theorem lerchIntegrand_apply (z s c : ℂ) (t : ℝ) :
    lerchIntegrand z s c t =
      (t : ℂ) ^ (s - 1) * Complex.exp (-(c * t)) / (1 - z * Complex.exp (-(t : ℂ))) :=
  (rfl)

/-- The Lerch zeta integral
`Φ(z, s, c) = (Gamma s)⁻¹ * ∫ t in Ioi 0, t ^ (s - 1) * exp (-(c * t)) / (1 - z * exp (-t))`,
which analytically continues `lerchSeries z s c` in `z` to the cut plane
`{z : ℂ | 1 - z ∈ Complex.slitPlane}` for `0 < s.re` and `0 < c.re`. -/
noncomputable def lerchIntegral (z s c : ℂ) : ℂ :=
  (Complex.Gamma s)⁻¹ * ∫ t in Ioi (0 : ℝ), lerchIntegrand z s c t

theorem lerchIntegral_def (z s c : ℂ) :
    lerchIntegral z s c = (Complex.Gamma s)⁻¹ * ∫ t in Ioi (0 : ℝ), lerchIntegrand z s c t :=
  (rfl)

/-- Unnormalized Laplace–Mellin integral `∫ t in Ioi 0, lerchIntegrand z s c t`. -/
private noncomputable def rawLerchIntegral (z s c : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), lerchIntegrand z s c t

private lemma norm_lerchIntegrand (z s c : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖lerchIntegrand z s c t‖ =
      t ^ (s.re - 1) * Real.exp (-c.re * t) / ‖1 - z * Complex.exp (-(t : ℂ))‖ := by
  rw [lerchIntegrand, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp

private lemma measurable_lerchIntegrand (z s c : ℂ) : Measurable (lerchIntegrand z s c) := by
  unfold lerchIntegrand
  fun_prop

private lemma integrable_lerchGammaMajorant {σ γ : ℝ} (hσ : 0 < σ) (hγ : 0 < γ) :
    Integrable (fun t : ℝ => t ^ (σ - 1) * Real.exp (-γ * t)) (volume.restrict (Ioi 0)) := by
  simpa only [IntegrableOn, Real.rpow_one] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ - 1) (b := γ) (by linarith) one_pos hγ

/-- For `1 - z ∈ Complex.slitPlane`, `0 < s.re`, and `0 < c.re`, `lerchIntegrand z s c` is Bochner
integrable on `Ioi 0`. -/
theorem integrableOn_lerchIntegrand {z s c : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hs : 0 < s.re)
    (hc : 0 < c.re) : IntegrableOn (lerchIntegrand z s c) (Ioi 0) := by
  obtain ⟨δ, hδ, hbound⟩ := exists_le_norm_one_sub_mul_exp_neg isCompact_singleton
    (singleton_subset_iff.mpr hz)
  refine ((integrable_lerchGammaMajorant hs hc).const_mul δ⁻¹).mono'
    (measurable_lerchIntegrand z s c).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_lerchIntegrand z s c ht, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ (hbound z rfl t ht.le)) (by positivity)

/-! ### Parametric derivatives and joint holomorphy of `lerchIntegral` -/

/-- Simultaneous local parameter bounds on a closed polydisc around `(z₀, s₀, c₀)` in the Lerch
integral domain. -/
private lemma exists_nhds_lerchIntegrand_bounds {z₀ s₀ c₀ : ℂ}
    (hz₀ : 1 - z₀ ∈ Complex.slitPlane) (hs₀ : 0 < s₀.re) (hc₀ : 0 < c₀.re) :
    ∃ r > 0, ∃ δ > 0,
      (∀ z ∈ closedBall z₀ r, 1 - z ∈ Complex.slitPlane ∧
        ∀ t : ℝ, 0 ≤ t → δ ≤ ‖1 - z * Complex.exp (-(t : ℂ))‖) ∧
      (∀ s ∈ ball s₀ r, s₀.re / 2 < s.re ∧ s.re < 3 * s₀.re / 2) ∧
      (∀ c ∈ ball c₀ r, c₀.re / 2 < c.re) := by
  have hopen_z : IsOpen {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
    isOpen_slitPlane.preimage (continuous_const.sub continuous_id')
  obtain ⟨rz, hrz, hball_z⟩ := Metric.isOpen_iff.mp hopen_z z₀ hz₀
  let r : ℝ := min (rz / 2) (min (s₀.re / 2) (c₀.re / 2))
  have hr : 0 < r := lt_min (half_pos hrz) (lt_min (half_pos hs₀) (half_pos hc₀))
  have hr_rz : r ≤ rz / 2 := min_le_left _ _
  have hr_s : r ≤ s₀.re / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr_c : r ≤ c₀.re / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub_z : closedBall z₀ r ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane} := fun z hz =>
    hball_z (mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (by linarith)))
  obtain ⟨δ, hδ, hδK⟩ := exists_le_norm_one_sub_mul_exp_neg (isCompact_closedBall z₀ r) hsub_z
  refine ⟨r, hr, δ, hδ, fun z hz => ⟨hsub_z hz, hδK z hz⟩, fun s hs => ?_, fun c hc => ?_⟩
  · have h := (abs_re_le_norm (s - s₀)).trans_lt (by simpa [mem_ball, dist_eq_norm] using hs)
    rw [sub_re, abs_lt] at h
    exact ⟨by linarith, by linarith⟩
  · have h := (abs_re_le_norm (c - c₀)).trans_lt (by simpa [mem_ball, dist_eq_norm] using hc)
    rw [sub_re, abs_lt] at h
    linarith

private lemma continuousAt_rawLerchIntegral {v : Fin 3 → ℂ} (hv0 : 1 - v 0 ∈ Complex.slitPlane)
    (hv1 : 0 < (v 1).re) (hv2 : 0 < (v 2).re) :
    ContinuousAt (fun w : Fin 3 → ℂ => rawLerchIntegral (w 0) (w 1) (w 2)) v := by
  obtain ⟨r, hr, δ, hδ, hzB, hsB, hcB⟩ := exists_nhds_lerchIntegrand_bounds hv0 hv1 hv2
  have hb1 := integrable_lerchGammaMajorant (half_pos hv1) (half_pos hv2)
  have hb2 := integrable_lerchGammaMajorant (by positivity : 0 < 3 * (v 1).re / 2) (half_pos hv2)
  have hbound_int : Integrable
      (fun t : ℝ => δ⁻¹ * ((t ^ ((v 1).re / 2 - 1) + t ^ (3 * (v 1).re / 2 - 1)) *
        Real.exp (-((v 2).re / 2) * t))) (volume.restrict (Ioi 0)) :=
    ((hb1.add hb2).const_mul δ⁻¹).congr
      (Eventually.of_forall fun t => by simp only [Pi.add_apply]; ring)
  have hball : ball v r ∈ 𝓝 v := ball_mem_nhds v hr
  refine continuousAt_of_dominated (bound := fun t : ℝ =>
    δ⁻¹ * ((t ^ ((v 1).re / 2 - 1) + t ^ (3 * (v 1).re / 2 - 1)) *
      Real.exp (-((v 2).re / 2) * t))) ?_ ?_ hbound_int ?_
  · filter_upwards [hball] with w _
    exact (measurable_lerchIntegrand (w 0) (w 1) (w 2)).aestronglyMeasurable
  · filter_upwards [hball] with w hw
    have hw0 : w 0 ∈ closedBall (v 0) r :=
      mem_closedBall.mpr ((dist_le_pi_dist w v 0).trans (mem_ball.mp hw).le)
    have hw1 : w 1 ∈ ball (v 1) r :=
      mem_ball.mpr ((dist_le_pi_dist w v 1).trans_lt (mem_ball.mp hw))
    have hw2 : w 2 ∈ ball (v 2) r :=
      mem_ball.mpr ((dist_le_pi_dist w v 2).trans_lt (mem_ball.mp hw))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [norm_lerchIntegrand (w 0) (w 1) (w 2) ht, div_eq_inv_mul]
    have hden : (‖1 - w 0 * Complex.exp (-(t : ℂ))‖)⁻¹ ≤ δ⁻¹ :=
      inv_anti₀ hδ ((hzB (w 0) hw0).2 t ht.le)
    have hrpow : t ^ ((w 1).re - 1) ≤ t ^ ((v 1).re / 2 - 1) + t ^ (3 * (v 1).re / 2 - 1) := by
      rcases le_total t 1 with ht1 | ht1
      · exact (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith [(hsB (w 1) hw1).1])).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
      · exact (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith [(hsB (w 1) hw1).2])).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))
    have hexp : Real.exp (-(w 2).re * t) ≤ Real.exp (-((v 2).re / 2) * t) :=
      Real.exp_le_exp.mpr (by nlinarith [hcB (w 2) hw2])
    exact mul_le_mul hden (mul_le_mul hrpow hexp (by positivity) (by positivity))
      (by positivity) (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    have hden_ne : 1 - v 0 * Complex.exp (-(t : ℂ)) ≠ 0 := fun h => by
      have := (hzB (v 0) (mem_closedBall_self hr.le)).2 t ht.le
      rw [h, norm_zero] at this
      linarith
    have hc1 : ContinuousAt (fun w : Fin 3 → ℂ => (t : ℂ) ^ (w 1 - 1)) v :=
      continuousAt_const.cpow ((continuous_apply 1).continuousAt.sub continuousAt_const)
        (Or.inl (by simpa using ht))
    have hc2 : ContinuousAt (fun w : Fin 3 → ℂ => Complex.exp (-(w 2 * t))) v :=
      (((continuous_apply 2).continuousAt.mul continuousAt_const).neg).cexp
    have hc3 : ContinuousAt (fun w : Fin 3 → ℂ => 1 - w 0 * Complex.exp (-(t : ℂ))) v :=
      continuousAt_const.sub ((continuous_apply 0).continuousAt.mul continuousAt_const)
    exact (hc1.mul hc2).div hc3 hden_ne

private lemma hasDerivAt_rawLerchIntegral_left {z s c : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    (hs : 0 < s.re) (hc : 0 < c.re) :
    HasDerivAt (fun w => rawLerchIntegral w s c)
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-((c + 1) * t)) /
        (1 - z * Complex.exp (-(t : ℂ))) ^ 2) z := by
  obtain ⟨r, hr, δ, hδ, hzB, _, _⟩ := exists_nhds_lerchIntegrand_bounds hz hs hc
  have hmajor : Integrable (fun t : ℝ => (δ ^ 2)⁻¹ * (t ^ (s.re - 1) * Real.exp (-c.re * t)))
      (volume.restrict (Ioi 0)) := (integrable_lerchGammaMajorant hs hc).const_mul (δ ^ 2)⁻¹
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (t : ℂ) ^ (s - 1) * Complex.exp (-((c + 1) * t)) / (1 - w * Complex.exp (-(t : ℂ))) ^ 2
  have hmeas : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun w => lerchIntegrand w s c)
    (F' := F') (ball_mem_nhds z hr)
    (Eventually.of_forall fun w => (measurable_lerchIntegrand w s c).aestronglyMeasurable)
    (integrableOn_lerchIntegrand hz hs hc) hmeas ?_ hmajor ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    have hw_cb : w ∈ closedBall z r := ball_subset_closedBall hw
    have hden : δ ^ 2 ≤ ‖1 - w * Complex.exp (-(t : ℂ))‖ ^ 2 :=
      pow_le_pow_left₀ hδ.le ((hzB w hw_cb).2 t ht.le) 2
    have hexp_le : Real.exp (-(c.re + 1) * t) ≤ Real.exp (-c.re * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    dsimp only [F']
    rw [norm_div, norm_pow, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp,
      div_eq_inv_mul]
    have hre : (-((c + 1) * t)).re = -(c.re + 1) * t := by simp [add_mul]
    rw [hre]
    exact mul_le_mul (inv_anti₀ (pow_pos hδ 2) hden)
      (mul_le_mul_of_nonneg_left hexp_le (by positivity)) (by positivity) (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    have hden_ne : 1 - w * Complex.exp (-(t : ℂ)) ≠ 0 := fun h => by
      have := (hzB w (ball_subset_closedBall hw)).2 t ht.le
      rw [h, norm_zero] at this
      linarith
    have hd_sub : HasDerivAt (fun u : ℂ => 1 - u * Complex.exp (-(t : ℂ)))
        (-Complex.exp (-(t : ℂ))) w := by
      simpa using ((hasDerivAt_id' w).mul_const (Complex.exp (-(t : ℂ)))).const_sub (1 : ℂ)
    dsimp only [lerchIntegrand]
    refine (((hasDerivAt_const w ((t : ℂ) ^ (s - 1) * Complex.exp (-(c * t)))).div
      hd_sub hden_ne)).congr_deriv ?_
    dsimp only [F']
    have hexp : Complex.exp (-(c * t)) * Complex.exp (-(t : ℂ)) =
        Complex.exp (-((c + 1) * t)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [zero_mul, zero_sub, mul_neg, neg_neg, mul_assoc, hexp]

/-- Differentiability of `rawLerchIntegral z · c` in the Mellin exponent `s` via Mathlib's
`mellin_differentiableAt_of_isBigO_rpow_exp`. -/
private lemma differentiableAt_rawLerchIntegral_mid {z s c : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    (hs : 0 < s.re) (hc : 0 < c.re) :
    DifferentiableAt ℂ (fun w => rawLerchIntegral z w c) s := by
  obtain ⟨δ, hδ, hbound⟩ := exists_le_norm_one_sub_mul_exp_neg isCompact_singleton
    (singleton_subset_iff.mpr hz)
  let f : ℝ → ℂ := fun t => Complex.exp (-(c * t)) / (1 - z * Complex.exp (-(t : ℂ)))
  have hden_ne (t : ℝ) (ht : 0 ≤ t) : 1 - z * Complex.exp (-(t : ℂ)) ≠ 0 := fun h => by
    have := hbound z rfl t ht
    rw [h, norm_zero] at this
    linarith
  have hf_cont : ContinuousOn f (Ici 0) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => hden_ne t ht
  have hf_le (t : ℝ) (ht : 0 ≤ t) : ‖f t‖ ≤ δ⁻¹ * Real.exp (-c.re * t) := by
    dsimp only [f]
    rw [norm_div, Complex.norm_exp, div_eq_inv_mul]
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, ← neg_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ (hbound z rfl t ht)) (by positivity)
  have hf_top : f =O[atTop] fun t => Real.exp (-c.re * t) :=
    IsBigO.of_bound δ⁻¹ <| (eventually_ge_atTop (0 : ℝ)).mono fun t ht => by
      simpa [Real.norm_of_nonneg (Real.exp_pos _).le] using hf_le t ht
  have hf_bot : f =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) :=
    IsBigO.of_bound δ⁻¹ <| eventually_of_mem self_mem_nhdsWithin fun t (ht : 0 < t) => by
      have hexp1 : Real.exp (-c.re * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      simpa using (hf_le t ht.le).trans (mul_le_of_le_one_right (inv_nonneg.mpr hδ.le) hexp1)
  have hmellin : (fun w => rawLerchIntegral z w c) = mellin f :=
    funext fun w => by simp only [rawLerchIntegral, lerchIntegrand, mellin, f, smul_eq_mul,
      mul_div_assoc]
  rw [hmellin]
  exact mellin_differentiableAt_of_isBigO_rpow_exp hc
    ((hf_cont.mono Ioi_subset_Ici_self).locallyIntegrableOn measurableSet_Ioi) hf_top hf_bot hs

private lemma hasDerivAt_rawLerchIntegral_right {z s c : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    (hs : 0 < s.re) (hc : 0 < c.re) :
    HasDerivAt (fun w => rawLerchIntegral z s w) (-rawLerchIntegral z (s + 1) c) c := by
  unfold rawLerchIntegral
  obtain ⟨r, hr, δ, hδ, hzB, _, hcB⟩ := exists_nhds_lerchIntegrand_bounds hz hs hc
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have hmajor : Integrable (fun t : ℝ => δ⁻¹ * (t ^ s.re * Real.exp (-(c.re / 2) * t)))
      (volume.restrict (Ioi 0)) := by
    simpa using (integrable_lerchGammaMajorant hs1 (half_pos hc)).const_mul δ⁻¹
  let F' : ℂ → ℝ → ℂ := fun w t => -lerchIntegrand z (s + 1) w t
  have hmeas : AEStronglyMeasurable (F' c) (volume.restrict (Ioi 0)) :=
    Measurable.aestronglyMeasurable (by dsimp only [F', lerchIntegrand]; fun_prop)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun w => lerchIntegrand z s w)
    (F' := F') (ball_mem_nhds c hr)
    (Eventually.of_forall fun w => (measurable_lerchIntegrand z s w).aestronglyMeasurable)
    (integrableOn_lerchIntegrand hz hs hc) hmeas ?_ hmajor ?_).2.congr_deriv ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    dsimp only [F']
    rw [norm_neg, norm_lerchIntegrand z (s + 1) w ht, div_eq_inv_mul]
    have hre1 : (s + 1).re - 1 = s.re := by simp
    rw [hre1]
    have hden : (‖1 - z * Complex.exp (-(t : ℂ))‖)⁻¹ ≤ δ⁻¹ :=
      inv_anti₀ hδ ((hzB z (mem_closedBall_self hr.le)).2 t ht.le)
    have hexp : Real.exp (-w.re * t) ≤ Real.exp (-(c.re / 2) * t) :=
      Real.exp_le_exp.mpr (by nlinarith [hcB w hw])
    exact mul_le_mul hden (mul_le_mul_of_nonneg_left hexp (by positivity))
      (by positivity) (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w _
    have hexp : HasDerivAt (fun u : ℂ => Complex.exp (-(u * t)))
        (Complex.exp (-(w * t)) * -(t : ℂ)) w := by
      simpa using (((hasDerivAt_id' w).mul_const (t : ℂ)).neg).cexp
    dsimp only [lerchIntegrand]
    refine ((hexp.const_mul ((t : ℂ) ^ (s - 1))).div_const
      (1 - z * Complex.exp (-(t : ℂ)))).congr_deriv ?_
    have ht_pow : (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ s := by
      simpa [sub_add_cancel] using
        (Complex.cpow_add (s - 1) 1 (Complex.ofReal_ne_zero.mpr ht.ne')).symm
    dsimp only [F', lerchIntegrand]
    rw [add_sub_cancel_right, ← ht_pow]
    ring
  · simp [F', integral_neg]

/-- Slit-plane `s`-raising relation for `lerchIntegral`: for `1 - z ∈ Complex.slitPlane`,
`0 < s.re`, and `0 < c.re`,
`HasDerivAt (lerchIntegral z s ·) (-s * lerchIntegral z (s + 1) c) c`. -/
theorem hasDerivAt_lerchIntegral_right {z s c : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    (hs : 0 < s.re) (hc : 0 < c.re) :
    HasDerivAt (fun w => lerchIntegral z s w) (-s * lerchIntegral z (s + 1) c) c := by
  have hs0 : s ≠ 0 := by intro rfl; simp at hs
  have hraw := (hasDerivAt_rawLerchIntegral_right hz hs hc).const_mul (Complex.Gamma s)⁻¹
  refine hraw.congr_deriv ?_
  unfold lerchIntegral rawLerchIntegral
  rw [Complex.Gamma_add_one s hs0, mul_inv]
  have hs_inv : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
  linear_combination ((Complex.Gamma s)⁻¹ * ∫ t in Ioi (0 : ℝ), lerchIntegrand z (s + 1) c t)
    * hs_inv

/-- Joint analyticity of `lerchIntegral` at any `v : Fin 3 → ℂ` with `1 - v 0 ∈ Complex.slitPlane`,
`0 < (v 1).re`, and `0 < (v 2).re`, proved via Osgood's lemma. -/
theorem analyticAt_lerchIntegral_pi {v : Fin 3 → ℂ} (hv0 : 1 - v 0 ∈ Complex.slitPlane)
    (hv1 : 0 < (v 1).re) (hv2 : 0 < (v 2).re) :
    AnalyticAt ℂ (fun w : Fin 3 → ℂ => lerchIntegral (w 0) (w 1) (w 2)) v := by
  let S : Set (Fin 3 → ℂ) :=
    {w | 1 - w 0 ∈ Complex.slitPlane ∧ 0 < (w 1).re ∧ 0 < (w 2).re}
  have hS : IsOpen S :=
    (Complex.isOpen_slitPlane.preimage (f := fun w : Fin 3 → ℂ => 1 - w 0) (by fun_prop)).inter
      ((isOpen_lt (f := fun _ : Fin 3 → ℂ => (0 : ℝ)) (g := fun w => (w 1).re)
        continuous_const (by fun_prop)).inter
        (isOpen_lt (f := fun _ : Fin 3 → ℂ => (0 : ℝ)) (g := fun w => (w 2).re)
          continuous_const (by fun_prop)))
  have hraw : AnalyticAt ℂ (fun w : Fin 3 → ℂ => rawLerchIntegral (w 0) (w 1) (w 2)) v := by
    have hcont : ContinuousOn (fun w : Fin 3 → ℂ => rawLerchIntegral (w 0) (w 1) (w 2)) S :=
      fun w hw => (continuousAt_rawLerchIntegral hw.1 hw.2.1 hw.2.2).continuousWithinAt
    refine hcont.analyticAt_of_differentiableAt_update (hS.mem_nhds ⟨hv0, hv1, hv2⟩) ?_
    intro w hw i
    fin_cases i
    · simpa using (hasDerivAt_rawLerchIntegral_left hw.1 hw.2.1 hw.2.2).differentiableAt
    · simpa using differentiableAt_rawLerchIntegral_mid hw.1 hw.2.1 hw.2.2
    · simpa using (hasDerivAt_rawLerchIntegral_right hw.1 hw.2.1 hw.2.2).differentiableAt
  have hgamma : AnalyticAt ℂ (fun w : Fin 3 → ℂ => (Complex.Gamma (w 1))⁻¹) v := by
    have h1 := Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ
      (v 1) (mem_univ (v 1))
    simpa only [Function.comp_def, one_div] using
      h1.comp (f := fun w : Fin 3 → ℂ => w 1)
        ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt v)
  exact hgamma.mul hraw

end TauCeti

/-- Simultaneous analytic substitution into the three arguments of `TauCeti.lerchIntegral`. -/
theorem AnalyticAt.lerchIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g h : E → ℂ} {p : E} (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hh : AnalyticAt ℂ h p) (hfp : 1 - f p ∈ Complex.slitPlane) (hgp : 0 < (g p).re)
    (hhp : 0 < (h p).re) :
    AnalyticAt ℂ (fun q => TauCeti.lerchIntegral (f q) (g q) (h q)) p := by
  have ha : AnalyticAt ℂ (fun q => ![f q, g q, h q]) p := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    fin_cases i
    · simpa using hf
    · simpa using hg
    · simpa using hh
  exact (TauCeti.analyticAt_lerchIntegral_pi (v := ![f p, g p, h p]) hfp hgp hhp).comp
    (f := fun q => ![f q, g q, h q]) ha

namespace TauCeti

/-- Joint analyticity of `lerchIntegral` on
`{p : ℂ × ℂ × ℂ | 1 - p.1 ∈ Complex.slitPlane ∧ 0 < p.2.1.re ∧ 0 < p.2.2.re}`. -/
theorem analyticOnNhd_lerchIntegral :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => lerchIntegral p.1 p.2.1 p.2.2)
      {p : ℂ × ℂ × ℂ | 1 - p.1 ∈ Complex.slitPlane ∧ 0 < p.2.1.re ∧ 0 < p.2.2.re} :=
  fun _ hp => analyticAt_fst.lerchIntegral (analyticAt_fst.comp analyticAt_snd)
    (analyticAt_snd.comp analyticAt_snd) hp.1 hp.2.1 hp.2.2

/-- Joint complex differentiability of `lerchIntegral` on
`{p : ℂ × ℂ × ℂ | 1 - p.1 ∈ Complex.slitPlane ∧ 0 < p.2.1.re ∧ 0 < p.2.2.re}`. -/
theorem differentiableOn_lerchIntegral :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => lerchIntegral p.1 p.2.1 p.2.2)
      {p : ℂ × ℂ × ℂ | 1 - p.1 ∈ Complex.slitPlane ∧ 0 < p.2.1.re ∧ 0 < p.2.2.re} :=
  analyticOnNhd_lerchIntegral.differentiableOn

/-! ### Overlap agreement with `lerchSeries` and slit-plane continuation identities -/

private lemma summable_integral_norm_lerchSeries_integrand {z s c : ℂ} (hz : ‖z‖ < 1)
    (hs : 0 < s.re) (hc : 0 < c.re) :
    Summable fun n : ℕ =>
      ∫ t in Ioi (0 : ℝ), ‖z ^ n * ((t : ℂ) ^ (s - 1) * Complex.exp (-((n + c) * t)))‖ := by
  have hnc_re (n : ℕ) : 0 < ((n : ℂ) + c).re := by simp; linarith
  have hbase_int := integrable_lerchGammaMajorant hs hc
  set C : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * Real.exp (-c.re * t)
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n => ?_) ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right C)
  rw [← integral_const_mul]
  refine integral_mono_ae
    ((Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs (hnc_re n)).const_mul (z ^ n)).norm
    (hbase_int.const_mul (‖z‖ ^ n)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  have hre : (-(((n : ℂ) + c) * t)).re ≤ -c.re * t := by
    simp only [neg_re, mul_re, add_re, natCast_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    nlinarith
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre) (by positivity)) (by positivity)

/-- On the overlap `‖z‖ < 1`, `0 < s.re`, `0 < c.re`, `lerchIntegral z s c` equals
`lerchSeries z s c`. -/
theorem lerchIntegral_eq_lerchSeries {z s c : ℂ} (hz : ‖z‖ < 1) (hs : 0 < s.re) (hc : 0 < c.re) :
    lerchIntegral z s c = lerchSeries z s c := by
  let F : ℕ → ℝ → ℂ := fun n t => z ^ n * ((t : ℂ) ^ (s - 1) * Complex.exp (-((n + c) * t)))
  have hnc_re (n : ℕ) : 0 < ((n : ℂ) + c).re := by simp; linarith
  have hF_int (n : ℕ) : Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) :=
    (Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs (hnc_re n)).const_mul (z ^ n)
  have hpt : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ∑' n : ℕ, F n t = lerchIntegrand z s c t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    have hze : ‖z * Complex.exp (-(t : ℂ))‖ < 1 := by
      rw [norm_mul, Complex.norm_exp, neg_re, ofReal_re]
      exact (mul_le_of_le_one_right (norm_nonneg z)
        (Real.exp_le_one_iff.mpr (by linarith))).trans_lt hz
    calc ∑' n : ℕ, F n t
        = (t : ℂ) ^ (s - 1) * Complex.exp (-(c * t)) *
            ∑' n : ℕ, (z * Complex.exp (-(t : ℂ))) ^ n := by
          rw [← tsum_mul_left]
          refine tsum_congr fun n => ?_
          have hexp : Complex.exp (-(((n : ℂ) + c) * t)) =
              Complex.exp (-(c * t)) * Complex.exp (-(t : ℂ)) ^ n := by
            rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; ring
          dsimp only [F]
          rw [hexp, mul_pow]; ring
      _ = lerchIntegrand z s c t := by
          rw [tsum_geometric_of_norm_lt_one hze, lerchIntegrand, div_eq_mul_inv]
  have hint_eq : ∫ t in Ioi (0 : ℝ), lerchIntegrand z s c t =
      Complex.Gamma s * lerchSeries z s c := by
    rw [← integral_congr_ae hpt, ← integral_tsum_of_summable_integral_norm hF_int
      (summable_integral_norm_lerchSeries_integrand hz hs hc), lerchSeries_def, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have hnc0 : (n : ℂ) + c ≠ 0 := fun h => by have := hnc_re n; rw [h] at this; simp at this
    dsimp only [F]
    rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs (hnc_re n),
      Complex.cpow_def_of_ne_zero hnc0, mul_comm (Complex.log _) (-s), lerchSeriesTerm_apply]
    ring
  rw [lerchIntegral, hint_eq, inv_mul_cancel_left₀ (Complex.Gamma_ne_zero_of_re_pos hs)]

/-- Slit-plane continuation of the `c`-shift identity: for `1 - z ∈ Complex.slitPlane`,
`0 < s.re`, and `0 < c.re`,
`lerchIntegral z s c = exp (-s * log c) + z * lerchIntegral z s (c + 1)`. -/
theorem lerchIntegral_shift {z s c : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hs : 0 < s.re)
    (hc : 0 < c.re) :
    lerchIntegral z s c = Complex.exp (-s * Complex.log c) + z * lerchIntegral z s (c + 1) := by
  have hc1 : 0 < (c + 1).re := by simp; linarith
  have hanL : AnalyticOnNhd ℂ (fun u => lerchIntegral (1 - u) s c) Complex.slitPlane :=
    fun _ hu => (analyticAt_const.sub analyticAt_id).lerchIntegral analyticAt_const
      analyticAt_const (by simpa using hu) hs hc
  have hanR : AnalyticOnNhd ℂ
      (fun u => Complex.exp (-s * Complex.log c) + (1 - u) * lerchIntegral (1 - u) s (c + 1))
      Complex.slitPlane :=
    fun _ hu => analyticAt_const.add ((analyticAt_const.sub analyticAt_id).mul
      ((analyticAt_const.sub analyticAt_id).lerchIntegral analyticAt_const analyticAt_const
        (by simpa using hu) hs hc1))
  have hev : (fun u => lerchIntegral (1 - u) s c) =ᶠ[𝓝 (1 : ℂ)]
      fun u => Complex.exp (-s * Complex.log c) + (1 - u) * lerchIntegral (1 - u) s (c + 1) := by
    filter_upwards [ball_mem_nhds (1 : ℂ) one_pos] with u hu
    have hu1 : ‖1 - u‖ < 1 := by simpa [mem_ball, dist_eq_norm', norm_sub_rev] using hu
    rw [lerchIntegral_eq_lerchSeries hu1 hs hc, lerchIntegral_eq_lerchSeries hu1 hs hc1,
      lerchSeries_shift hu1 s c]
  have hconn := (Complex.starConvex_one_slitPlane.isPathConnected
    Complex.one_mem_slitPlane).isConnected.isPreconnected
  simpa [sub_sub_cancel] using
    hanL.eqOn_of_preconnected_of_eventuallyEq hanR hconn Complex.one_mem_slitPlane hev hz

/-- Slit-plane continuation of the weight-one polylogarithm bridge: for every `z ∈ ℂ` with
`1 - z ∈ Complex.slitPlane`, `z * lerchIntegral z 1 1 = Polylog.polylog 1 z = -log (1 - z)`. -/
theorem mul_lerchIntegral_one_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * lerchIntegral z 1 1 = Polylog.polylog 1 z := by
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  have hanL : AnalyticOnNhd ℂ (fun u => (1 - u) * lerchIntegral (1 - u) 1 1) Complex.slitPlane :=
    fun _ hu => (analyticAt_const.sub analyticAt_id).mul
      ((analyticAt_const.sub analyticAt_id).lerchIntegral analyticAt_const analyticAt_const
        (by simpa using hu) h1 h1)
  have hanR : AnalyticOnNhd ℂ (fun u => Polylog.polylog 1 (1 - u)) Complex.slitPlane := by
    rw [show (fun u : ℂ => Polylog.polylog 1 (1 - u)) = fun u : ℂ => -Complex.log u from
      funext fun u => by simp [Polylog.polylog_one]]
    exact fun _ hu => (analyticAt_id.clog hu).neg
  have hev : (fun u => (1 - u) * lerchIntegral (1 - u) 1 1) =ᶠ[𝓝 (1 : ℂ)]
      fun u => Polylog.polylog 1 (1 - u) := by
    filter_upwards [ball_mem_nhds (1 : ℂ) one_pos] with u hu
    have hu1 : ‖1 - u‖ < 1 := by simpa [mem_ball, dist_eq_norm', norm_sub_rev] using hu
    rw [lerchIntegral_eq_lerchSeries hu1 h1 h1, mul_lerchSeries_one_one hu1]
  have hconn := (Complex.starConvex_one_slitPlane.isPathConnected
    Complex.one_mem_slitPlane).isConnected.isPreconnected
  simpa [sub_sub_cancel] using
    hanL.eqOn_of_preconnected_of_eventuallyEq hanR hconn Complex.one_mem_slitPlane hev hz

end TauCeti
