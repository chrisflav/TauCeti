/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.Analysis.Complex.TaylorSeries
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Circle.Haar

/-!
# Parseval's identity for Taylor series on circles

For a holomorphic function `f : ℂ → ℂ` on an open disk `Metric.ball c R` and any radius `|r| < R`,
restricting `f` to the circle `t ↦ r * toCircle t + c` expands `f` in the orthonormal Fourier modes
of `UnitAddCircle`. Parseval's identity therefore equates the squared circle mean of `f` on
`sphere c |r|` with the weighted Taylor coefficient sum:

`circleAverage (fun w ↦ ‖f w‖ ^ 2) c r =`
`  ∑' n : ℕ, ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ ^ 2 * r ^ (2 * n)`.

From this identity we deduce:
* monotonicity of radial `L²` means `r ↦ circleAverage (fun w ↦ ‖f w‖ ^ 2) c r` on `[0, R)`;
* square-summability of the rescaled Taylor coefficients `(n ! : ℂ)⁻¹ * iteratedDeriv n f c * R ^ n`
  whenever all interior radial `L²` means on `[0, R)` are bounded above (for instance by the value
  at `c` of a real harmonic majorant of `‖f ·‖ ^ 2`).

## References

* P. L. Duren, *Theory of Hᵖ Spaces*, Academic Press (1970), Chapter 1.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), Theorem 10.26 and §17.6.
-/

public section

noncomputable section

namespace TauCeti

open Complex Filter InnerProductSpace MeasureTheory Metric Nat Real Set Topology
open scoped ENNReal

/-- If `f` is holomorphic on `ball c R` and `|r| < R`, then the Taylor terms of `f` at radius `|r|`
are absolutely summable. -/
private theorem summable_norm_taylorCoeff_mul_pow {f : ℂ → ℂ} {c : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (hr : |r| < R) :
    Summable fun n : ℕ ↦ ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c * (r : ℂ) ^ n‖ := by
  set ρ : ℝ := (|r| + R) / 2 with hρ_def
  have hρ_pos : 0 < ρ := by linarith [abs_nonneg r, hρ_def]
  have hrρ : |r| < ρ := by linarith [hρ_def]
  have hρR : ρ < R := by linarith [hρ_def]
  have hz : c + (ρ : ℂ) ∈ ball c R := by
    rw [mem_ball, dist_self_add_left, Complex.norm_real, Real.norm_of_nonneg hρ_pos.le]
    exact hρR
  have hsum : HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (ρ : ℂ) ^ n) (f (c + ρ)) := by
    convert Complex.hasSum_taylorSeries_on_ball hf hz using 1
    funext n
    simp only [add_sub_cancel_left, smul_eq_mul]
    ring
  have htend : Tendsto (fun n : ℕ ↦ ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c * (ρ : ℂ) ^ n‖)
      atTop (𝓝 0) := by
    simpa using hsum.summable.tendsto_atTop_zero.norm
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp htend).2 1 zero_lt_one)
  let M : ℝ := max 1 (∑ k ∈ Finset.range N, ‖(k ! : ℂ)⁻¹ * iteratedDeriv k f c * (ρ : ℂ) ^ k‖)
  have hq0 : 0 ≤ |r| / ρ := div_nonneg (abs_nonneg r) hρ_pos.le
  have hq1 : |r| / ρ < 1 := (div_lt_one hρ_pos).mpr hrρ
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left M)
  have hMn : ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c * (ρ : ℂ) ^ n‖ ≤ M := by
    by_cases hn : n < N
    · exact (Finset.single_le_sum
        (f := fun k : ℕ ↦ ‖(k ! : ℂ)⁻¹ * iteratedDeriv k f c * (ρ : ℂ) ^ k‖)
        (fun _ _ ↦ norm_nonneg _) (Finset.mem_range.mpr hn)).trans (le_max_right _ _)
    · exact (hN n (le_of_not_gt hn)).le.trans (le_max_left _ _)
  calc ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c * (r : ℂ) ^ n‖
      = ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c * (ρ : ℂ) ^ n‖ * (|r| / ρ) ^ n := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg hρ_pos.le,
          div_pow |r| ρ n, mul_assoc _ (ρ ^ n), mul_div_cancel₀ _ (pow_ne_zero n hρ_pos.ne')]
    _ ≤ M * (|r| / ρ) ^ n :=
        mul_le_mul_of_nonneg_right hMn (pow_nonneg hq0 n)

/-- **Parseval's identity on circles (`HasSum` form).** For a holomorphic function `f : ℂ → ℂ` on
`ball c R` and any radius `|r| < R`, the squared Taylor terms weighted by `r ^ (2 * n)` sum to the
circle average of `‖f ·‖ ^ 2` on `sphere c |r|`. -/
theorem hasSum_norm_sq_taylorCoeff_mul_pow {f : ℂ → ℂ} {c : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (hr : |r| < R) :
    HasSum (fun n : ℕ ↦ ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ ^ 2 * r ^ (2 * n))
      (circleAverage (fun w ↦ ‖f w‖ ^ 2) c r) := by
  let a : ℕ → ℂ := fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (r : ℂ) ^ n
  have ha_sum : Summable fun n : ℕ ↦ ‖a n‖ := summable_norm_taylorCoeff_mul_pow hf hr
  let g : ℕ → C(AddCircle (1 : ℝ), ℂ) := fun n ↦ a n • fourier (T := 1) (n : ℤ)
  have hg : Summable g := by
    refine Summable.of_norm_bounded ha_sum fun n ↦ ?_
    rw [norm_smul, fourier_norm, mul_one]
  -- Pointwise on `AddCircle 1`, `∑' n, g n` evaluates `f` along the parametrized circle.
  have hg_eval (t : AddCircle (1 : ℝ)) :
      (∑' n : ℕ, g n) t = f ((r : ℂ) * (AddCircle.toCircle t : ℂ) + c) := by
    let z : ℂ := (r : ℂ) * (AddCircle.toCircle t : ℂ) + c
    have hz : z ∈ ball c R := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_right, norm_mul, Circle.norm_coe, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      exact hr
    refine (ContinuousMap.tsum_apply hg t).symm.trans ?_
    rw [← Complex.taylorSeries_eq_on_ball' hz hf]
    congr 1
    funext n
    simp only [g, a, z, ContinuousMap.smul_apply, smul_eq_mul, fourier_apply, natCast_zsmul,
      AddCircle.toCircle_nsmul, Circle.coe_pow, add_sub_cancel_right, mul_pow]
    ring
  let L : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
    ContinuousMap.toLp 2 (AddCircle.haarAddCircle (T := 1)) ℂ
  let F₂ := L (∑' n : ℕ, g n)
  -- Identify the Fourier coordinates of `F₂` in `ℓ²(ℤ)`.
  have hcoord (k : ℤ) :
      (fourierBasis (T := 1)).repr F₂ k =
        if 0 ≤ k then a k.toNat else 0 := by
    have hF₂ : F₂ = ∑' n : ℕ, a n • fourierBasis (T := 1) (n : ℤ) := by
      dsimp only [F₂]
      rw [L.map_tsum hg]
      congr 1
      funext n
      simp [L, g, coe_fourierBasis]
    have hg_L2 : Summable fun n : ℕ ↦ a n • fourierBasis (T := 1) (n : ℤ) := by
      refine Summable.of_norm_bounded ha_sum fun n ↦ ?_
      rw [norm_smul, (fourierBasis (T := 1)).orthonormal.1 (n : ℤ), mul_one]
    rw [hF₂, HilbertBasis.repr_apply_apply, ← innerSL_apply_apply ℂ,
      ContinuousLinearMap.map_tsum _ hg_L2]
    by_cases hk : 0 ≤ k
    · obtain ⟨n, hnk⟩ := Int.eq_ofNat_of_zero_le hk
      subst hnk
      rw [ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast,
        tsum_eq_single n fun m hm ↦ ?_]
      · rw [innerSL_apply_apply, inner_smul_right,
          inner_self_eq_one_of_norm_eq_one ((fourierBasis (T := 1)).orthonormal.1 (n : ℤ)),
          mul_one]
      · have hnm : (n : ℤ) ≠ (m : ℤ) := Int.ofNat_inj.ne.mpr hm.symm
        rw [innerSL_apply_apply, inner_smul_right,
          (orthonormal_iff_ite.mp (fourierBasis (T := 1)).orthonormal (n : ℤ) (m : ℤ)).trans
            (ite_eq_right hnm), mul_zero]
    · rw [ite_eq_right hk]
      convert tsum_zero with m
      have hkm : k ≠ (m : ℤ) := by omega
      rw [innerSL_apply_apply, inner_smul_right,
        (orthonormal_iff_ite.mp (fourierBasis (T := 1)).orthonormal k (m : ℤ)).trans
          (ite_eq_right hkm), mul_zero]
  -- Equate `‖F₂‖ ^ 2` on one side with the circle average and on the other with the `ℓ²` norm sum.
  have hF₂_norm : ‖F₂‖ ^ 2 = circleAverage (fun w ↦ ‖f w‖ ^ 2) c r := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    calc (∫ t, ‖F₂ t‖ ^ 2 ∂AddCircle.haarAddCircle)
        = ∫ t : AddCircle (1 : ℝ), ‖f ((r : ℂ) * (AddCircle.toCircle t : ℂ) + c)‖ ^ 2
            ∂AddCircle.haarAddCircle := by
          refine integral_congr_ae ?_
          filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
            (AddCircle.haarAddCircle (T := 1)) (∑' n : ℕ, g n)] with t ht
          dsimp only [F₂, L] at ht ⊢
          rw [ht, hg_eval t]
      _ = circleAverage (fun w ↦ ‖f w‖ ^ 2) c r :=
          AddCircle.integral_haarAddCircle_comp_toCircle (T := 1) (fun w ↦ ‖f w‖ ^ 2) c r
  have hlp := (lp.memℓp ((fourierBasis (T := 1)).repr F₂)).summable (by norm_num)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hlp
  have hhasSum_int : HasSum (fun k : ℤ ↦ ‖(fourierBasis (T := 1)).repr F₂ k‖ ^ 2) (‖F₂‖ ^ 2) := by
    have hnorm := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ((fourierBasis (T := 1)).repr F₂)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] at hnorm
    rw [hnorm]
    exact hlp.hasSum
  have hhasSum_nat : HasSum (fun n : ℕ ↦ ‖a n‖ ^ 2) (‖F₂‖ ^ 2) := by
    have hinj : Function.Injective (fun n : ℕ ↦ (n : ℤ)) := Int.ofNat_injective
    have hsupp : ∀ k : ℤ, k ∉ Set.range (fun n : ℕ ↦ (n : ℤ)) →
        ‖(fourierBasis (T := 1)).repr F₂ k‖ ^ 2 = 0 := by
      intro k hk
      have hkneg : ¬ 0 ≤ k := fun h0 ↦ hk ⟨k.toNat, Int.toNat_of_nonneg h0⟩
      simp [hcoord k, hkneg]
    have hcomp := (hinj.hasSum_iff hsupp).mpr hhasSum_int
    refine hcomp.congr_fun fun n ↦ ?_
    simp [hcoord (n : ℤ)]
  rw [← hF₂_norm]
  refine hhasSum_nat.congr_fun fun n ↦ ?_
  simp only [a, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, mul_pow, pow_mul r 2 n, ← pow_mul |r| n 2, mul_comm n 2, pow_mul |r| 2 n, sq_abs]
  ring

/-- **Parseval's identity on circles (`tsum` form).** For `f : ℂ → ℂ` holomorphic on `ball c R`
and `|r| < R`, the circle average of `‖f ·‖ ^ 2` on `sphere c |r|` equals the weighted sum of
squared Taylor coefficients. -/
theorem circleAverage_norm_sq_eq_tsum {f : ℂ → ℂ} {c : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (hr : |r| < R) :
    circleAverage (fun w ↦ ‖f w‖ ^ 2) c r =
      ∑' n : ℕ, ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ ^ 2 * r ^ (2 * n) :=
  (hasSum_norm_sq_taylorCoeff_mul_pow hf hr).tsum_eq.symm

/-- For a holomorphic function `f : ℂ → ℂ` on `ball c R`, the radial `L²` means
`r ↦ circleAverage (fun w ↦ ‖f w‖ ^ 2) c r` are monotone nondecreasing on `[0, R)`. -/
theorem circleAverage_norm_sq_mono {f : ℂ → ℂ} {c : ℂ} {R r₁ r₂ : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (hr₁ : 0 ≤ r₁) (hr₁₂ : r₁ ≤ r₂) (hr₂ : r₂ < R) :
    circleAverage (fun w ↦ ‖f w‖ ^ 2) c r₁ ≤ circleAverage (fun w ↦ ‖f w‖ ^ 2) c r₂ := by
  have h₁ : |r₁| < R := by rw [abs_of_nonneg hr₁]; exact hr₁₂.trans_lt hr₂
  have h₂ : |r₂| < R := by rw [abs_of_nonneg (hr₁.trans hr₁₂)]; exact hr₂
  exact hasSum_le
    (fun n ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr₁ hr₁₂ (2 * n)) (sq_nonneg _))
    (hasSum_norm_sq_taylorCoeff_mul_pow hf h₁)
    (hasSum_norm_sq_taylorCoeff_mul_pow hf h₂)

/-- A real harmonic majorant `u` of `g` on `ball c R` bounds every interior circle mean of `g` by
its value `u c` at the center. -/
theorem circleAverage_le_of_harmonicOnNhd {g u : ℂ → ℝ} {c : ℂ} {R r : ℝ}
    (hg : ContinuousOn g (ball c R)) (hu : HarmonicOnNhd u (ball c R))
    (hmajor : ∀ w ∈ ball c R, g w ≤ u w) (hr : |r| < R) :
    circleAverage g c r ≤ u c := by
  have hsub : closedBall c |r| ⊆ ball c R := closedBall_subset_ball hr
  have hus := hu.mono hsub
  rw [← hus.circleAverage_eq (R := r)]
  exact circleAverage_mono
    (hg.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable'
    (hus.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
    fun w hw ↦ hmajor w (hsub (sphere_subset_closedBall hw))

/-- If `f : ℂ → ℂ` is holomorphic on `ball c R` (`0 < R`) and its radial `L²` means on `[0, R)` are
bounded above by `B`, then the weighted squared Taylor coefficients at radius `R` are summable and
their sum is at most `B`. -/
theorem summable_and_tsum_norm_sq_taylorCoeff_le_of_circleAverage_le {f : ℂ → ℂ} {c : ℂ}
    {R B : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hB : ∀ r ∈ Ico 0 R, circleAverage (fun w ↦ ‖f w‖ ^ 2) c r ≤ B) :
    Summable (fun n : ℕ ↦ ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ ^ 2 * R ^ (2 * n)) ∧
      (∑' n : ℕ, ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ ^ 2 * R ^ (2 * n)) ≤ B := by
  have hfin : ∀ s : Finset ℕ,
      ∑ n ∈ s, ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ ^ 2 * R ^ (2 * n) ≤ B := by
    intro s
    have hcont : Continuous fun r : ℝ ↦
        ∑ n ∈ s, ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ ^ 2 * r ^ (2 * n) := by
      fun_prop
    refine le_of_tendsto ((hcont.tendsto R).mono_left (nhdsWithin_le_nhds (s := Iio R))) ?_
    filter_upwards [Ioo_mem_nhdsLT hR] with r hr
    have hr0 : 0 < r := hr.1
    have hr' : |r| < R := by rw [abs_of_pos hr0]; exact hr.2
    have hsum := hasSum_norm_sq_taylorCoeff_mul_pow hf hr'
    exact (sum_le_hasSum s (fun _ _ ↦ by positivity) hsum).trans (hB r ⟨hr0.le, hr.2⟩)
  have hnonneg : ∀ n : ℕ, 0 ≤ ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ ^ 2 * R ^ (2 * n) :=
    fun _ ↦ by positivity
  have hsummable : Summable fun n : ℕ ↦ ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ ^ 2 * R ^ (2 * n) :=
    summable_of_sum_le hnonneg hfin
  exact ⟨hsummable, hsummable.tsum_le_of_sum_le hfin⟩

end TauCeti

end
