/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.AddCircle
public import TauCeti.Analysis.Fourier.Hardy.RadialMean

/-!
# Poisson representation and least harmonic majorants for Hardy functions

Every boundary Hardy element `x : HardySpace` gives rise to two extensions on the open unit disk:

1. Its holomorphic power-series extension `x.diskFunction`, which agrees on `Metric.ball 0 1` with
   the Poisson integral of the boundary `L²` class `x`
   (`TauCeti.HardySpace.diskFunction_eq_circlePoissonIntegral`).
2. The real harmonic extension `x.harmonicMajorant`, defined as the Poisson integral of the squared
   boundary modulus `t ↦ ‖x t‖ ^ 2`.

By Jensen's inequality for the circle Poisson kernel, `x.harmonicMajorant` majorizes
`w ↦ ‖x.diskFunction w‖ ^ 2` on `Metric.ball 0 1`, and its value at `0` is `‖x‖ ^ 2`. Conversely,
combining the Poisson integral formula on concentric interior closed disks `Metric.closedBall 0 r`
with radial `L¹` convergence of `t ↦ ‖x.diskFunction (r * toCircle t)‖ ^ 2` to `t ↦ ‖x t‖ ^ 2`
shows that `x.harmonicMajorant` is the **pointwise least** real harmonic majorant of
`w ↦ ‖x.diskFunction w‖ ^ 2` on the open unit disk
(`TauCeti.HardySpace.harmonicMajorant_le_of_harmonicOnNhd`).

## Main declarations

* `TauCeti.HardySpace.diskFunction_eq_circlePoissonIntegral`: on `Metric.ball 0 1`,
  `x.diskFunction` equals `circlePoissonIntegral x`.
* `TauCeti.HardySpace.tendsto_integral_abs_norm_sq_diskFunction_sub`: radial `L¹` convergence of
  `‖x.diskFunction (r * toCircle ·)‖ ^ 2` to `‖x ·‖ ^ 2` as `r → 1⁻`.
* `TauCeti.HardySpace.harmonicMajorant`: the Poisson integral of `t ↦ ‖x t‖ ^ 2`.
* `TauCeti.HardySpace.harmonicOnNhd_harmonicMajorant`,
  `TauCeti.HardySpace.norm_diskFunction_sq_le_harmonicMajorant`,
  `TauCeti.HardySpace.harmonicMajorant_zero`: harmonicity, majorization, and evaluation at `0`.
* `TauCeti.HardySpace.harmonicMajorant_le_of_harmonicOnNhd`: pointwise minimality among all real
  harmonic majorants on `Metric.ball 0 1`.
* `TauCeti.HardySpace.harmonicMajorant_hardyBasis` and
  `TauCeti.HardySpace.harmonicMajorant_hardyBasis_zero_add_one`: explicit formulas for monomials
  and for `1 + z`.

## References

* P. L. Duren, *Theory of Hᵖ Spaces*, Academic Press (1970), Chapter 1.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990).
-/

public section

noncomputable section

open Complex Filter InnerProductSpace MeasureTheory Metric Set Topology
open scoped ENNReal

namespace TauCeti.HardySpace

section General

variable (x : HardySpace)

/-- On the open unit disk, the holomorphic disk function of a boundary Hardy element `x` agrees
with the Poisson integral of its boundary `L²` representative. -/
theorem diskFunction_eq_circlePoissonIntegral {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    x.diskFunction w =
      circlePoissonIntegral (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) w := by
  have hw' : w ∉ sphere (0 : ℂ) 1 := disjoint_right.mp sphere_disjoint_ball hw
  let K : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun t ↦ (poissonKernel 0 w (AddCircle.toCircle t) : ℂ),
      Complex.continuous_ofReal.comp (continuous_poissonKernel_toCircle hw')⟩
  let K₂ : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
    ContinuousMap.toLp 2 (AddCircle.haarAddCircle (T := 1)) ℂ K
  let L : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) →L[ℂ] ℂ := innerSL ℂ K₂
  have hL (g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
      L g = circlePoissonIntegral g w := by
    dsimp only [L, K₂]
    rw [innerSL_apply_apply, L2.inner_def, circlePoissonIntegral_def]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
      (AddCircle.haarAddCircle (T := 1)) K] with t ht
    rw [RCLike.inner_apply, ht]
    simp [K, Complex.real_smul, mul_comm]
  have hsum := (L.comp hardySubmodule.subtypeL).hasSum (hardyBasis.hasSum_repr x)
  have hsum' : HasSum
      (fun n : ℕ ↦ fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n * w ^ n)
      (circlePoissonIntegral (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) w) := by
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hL x] at hsum
    refine hsum.congr_fun fun n ↦ ?_
    rw [ContinuousLinearMap.comp_apply, map_smul, map_smul, Submodule.subtypeL_apply,
      coe_hardyBasis, hardyBasis_repr, hL, smul_eq_mul]
    congr 1
    rw [coe_fourierBasis,
      circlePoissonIntegral_congr_ae (coeFn_fourierLp (T := 1) 2 (n : ℤ)),
      circlePoissonIntegral_fourier_nat hw n]
  exact (x.hasSum_diskFunction (mem_ball_zero_iff.mp hw)).unique hsum'

/-- The squared moduli of the circle restrictions `t ↦ x.diskFunction (r * toCircle t)` converge in
`L¹` to the squared boundary modulus `t ↦ ‖x t‖ ^ 2` as `r → 1⁻`. -/
theorem tendsto_integral_abs_norm_sq_diskFunction_sub :
    Tendsto (fun r : ℝ ↦
      ∫ t : AddCircle (1 : ℝ),
        |‖x.diskFunction (r * AddCircle.toCircle t)‖ ^ 2 -
          ‖(x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t‖ ^ 2|
        ∂AddCircle.haarAddCircle) (𝓝[<] 1) (𝓝 0) := by
  let μ := AddCircle.haarAddCircle (T := 1)
  let f : AddCircle (1 : ℝ) → ℂ := (x : Lp ℂ 2 μ)
  let g : ℝ → AddCircle (1 : ℝ) → ℂ := fun r t ↦ x.diskFunction (r * AddCircle.toCircle t)
  let d : ℝ → ℝ := fun r ↦ (eLpNorm (g r - f) 2 μ).toReal
  have hf : MemLp f 2 μ := Lp.memLp (x : Lp ℂ 2 μ)
  have hd_tendsto : Tendsto d (𝓝[<] 1) (𝓝 0) := by
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp x.tendsto_eLpNorm_diskFunction_sub
    rw [ENNReal.toReal_zero] at h0
    exact h0
  have hub_tendsto : Tendsto (fun r : ℝ ↦ d r * (d r + 2 * ‖x‖)) (𝓝[<] 1) (𝓝 0) := by
    simpa using hd_tendsto.mul (hd_tendsto.add tendsto_const_nhds)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub_tendsto ?_ ?_
  · exact Eventually.of_forall fun _ ↦ integral_nonneg fun _ ↦ abs_nonneg _
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with r hr
    have hr' : |r| < 1 := abs_lt.mpr hr
    have hg_cont : Continuous (g r) := by
      have hparam : Continuous fun t : AddCircle (1 : ℝ) ↦ (r : ℂ) * (AddCircle.toCircle t : ℂ) :=
        by fun_prop
      refine x.analyticOnNhd_diskFunction.continuousOn.comp_continuous hparam fun t ↦ ?_
      rw [mem_ball_zero_iff, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact hr'
    have hg_mem : MemLp (g r) 2 μ :=
      (Lp.memLp (ContinuousMap.toLp 2 μ ℂ ⟨g r, hg_cont⟩)).ae_eq
        (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ ⟨g r, hg_cont⟩)
    let A : Lp ℝ 2 μ := (hg_mem.sub hf).norm.toLp _
    let B : Lp ℝ 2 μ := (hg_mem.norm.add hf.norm).toLp _
    have hA_norm : ‖A‖ = d r := by
      dsimp only [A, d]
      rw [Lp.norm_toLp, eLpNorm_norm _ (hg_mem.sub hf).aestronglyMeasurable]
    have hB_norm : ‖B‖ ≤ d r + 2 * ‖x‖ := by
      let V : Lp ℝ 2 μ := hf.norm.toLp _
      have hV : ‖V‖ = ‖x‖ := by
        dsimp only [V]
        rw [Lp.norm_toLp, eLpNorm_norm _ hf.aestronglyMeasurable, ← Lp.norm_def,
          Submodule.norm_coe]
      have hle := Lp.norm_le_add_of_ae_norm_le (f := B) (g := A) (h := V) (a := 1) (b := 2)
        zero_le_one zero_le_two ?_
      · simpa only [one_mul, hA_norm, hV] using hle
      · filter_upwards [(hg_mem.norm.add hf.norm).coeFn_toLp, (hg_mem.sub hf).norm.coeFn_toLp,
          hf.norm.coeFn_toLp] with t hBt hAt hVt
        dsimp only [B, A, V]
        rw [hBt, hAt, hVt, Pi.add_apply, Pi.sub_apply,
          Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
          Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (norm_nonneg _)]
        have htri := norm_add_le (g r t - f t) (f t)
        rw [sub_add_cancel] at htri
        linarith
    have hint_le :
        (∫ t : AddCircle (1 : ℝ), |‖g r t‖ ^ 2 - ‖f t‖ ^ 2| ∂μ) ≤ ⟪A, B⟫_ℝ := by
      rw [L2.inner_def]
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ abs_nonneg _)
        (L2.integrable_inner A B) ?_
      filter_upwards [(hg_mem.sub hf).norm.coeFn_toLp,
        (hg_mem.norm.add hf.norm).coeFn_toLp] with t hAt hBt
      dsimp only [A, B]
      rw [RCLike.inner_apply, RCLike.conj_to_real, hAt, hBt, Pi.add_apply, Pi.sub_apply, mul_comm]
      have hsum_nonneg : 0 ≤ ‖g r t‖ + ‖f t‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
      have hsq : ‖g r t‖ ^ 2 - ‖f t‖ ^ 2 = (‖g r t‖ - ‖f t‖) * (‖g r t‖ + ‖f t‖) := by ring
      rw [hsq, abs_mul, abs_of_nonneg hsum_nonneg]
      exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le (g r t) (f t)) hsum_nonneg
    exact hint_le.trans ((real_inner_le_norm A B).trans
      (by rw [hA_norm]; exact mul_le_mul_of_nonneg_left hB_norm ENNReal.toReal_nonneg))

/-- The canonical Poisson extension of the squared boundary modulus `t ↦ ‖x t‖ ^ 2`. On the open
unit disk it is the pointwise least real harmonic majorant of `w ↦ ‖x.diskFunction w‖ ^ 2`. -/
def harmonicMajorant : ℂ → ℝ :=
  circlePoissonIntegral fun t : UnitAddCircle ↦
    ‖(x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t‖ ^ 2

/-- `HardySpace.harmonicMajorant` is the circle Poisson integral of the squared boundary modulus. -/
theorem harmonicMajorant_def (w : ℂ) :
    x.harmonicMajorant w =
      circlePoissonIntegral
        (fun t : UnitAddCircle ↦ ‖(x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t‖ ^ 2) w :=
  (rfl)

private theorem integrable_norm_sq_coe :
    Integrable (fun t : UnitAddCircle ↦ ‖(x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t‖ ^ 2)
      AddCircle.haarAddCircle :=
  (Lp.memLp (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))).integrable_norm_pow two_ne_zero

/-- The canonical harmonic majorant of `x` is harmonic on the open unit disk. -/
theorem harmonicOnNhd_harmonicMajorant : HarmonicOnNhd x.harmonicMajorant (ball (0 : ℂ) 1) :=
  harmonicOnNhd_ball_circlePoissonIntegral x.integrable_norm_sq_coe

/-- On the open unit disk, `x.harmonicMajorant` is nonnegative. -/
theorem harmonicMajorant_nonneg {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    0 ≤ x.harmonicMajorant w :=
  circlePoissonIntegral_nonneg hw (Eventually.of_forall fun _ ↦ sq_nonneg _)

/-- On the open unit disk, `x.harmonicMajorant` majorizes `w ↦ ‖x.diskFunction w‖ ^ 2`. -/
theorem norm_diskFunction_sq_le_harmonicMajorant {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ‖x.diskFunction w‖ ^ 2 ≤ x.harmonicMajorant w := by
  rw [x.diskFunction_eq_circlePoissonIntegral hw, harmonicMajorant_def]
  exact norm_circlePoissonIntegral_sq_le
    (Lp.memLp (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) hw

/-- Evaluating `x.harmonicMajorant` at the origin recovers `‖x‖ ^ 2`. -/
@[simp]
theorem harmonicMajorant_zero : x.harmonicMajorant 0 = ‖x‖ ^ 2 := by
  rw [harmonicMajorant_def, circlePoissonIntegral_eval_zero, Lp.integral_norm_sq_eq_norm_sq,
    Submodule.norm_coe]

/-- **Pointwise least harmonic majorant.** Every real harmonic function `u` on the open unit disk
that majorizes `w ↦ ‖x.diskFunction w‖ ^ 2` satisfies `x.harmonicMajorant w ≤ u w` at every point
`w` of the open unit disk. -/
theorem harmonicMajorant_le_of_harmonicOnNhd {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (hmajor : ∀ z ∈ ball (0 : ℂ) 1, ‖x.diskFunction z‖ ^ 2 ≤ u z)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    x.harmonicMajorant w ≤ u w := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  set r₀ : ℝ := (‖w‖ + 1) / 2 with hr₀_def
  have hr₀_pos : 0 < r₀ := by positivity
  have hr₀_lt : r₀ < 1 := by linarith [hr₀_def]
  have hwr₀ : ‖w‖ < r₀ := by linarith [hr₀_def]
  let μ := AddCircle.haarAddCircle (T := 1)
  let b : AddCircle (1 : ℝ) → ℝ := fun t ↦ ‖(x : Lp ℂ 2 μ) t‖ ^ 2
  have hb : Integrable b μ := x.integrable_norm_sq_coe
  let K : ℝ → AddCircle (1 : ℝ) → ℝ := fun r t ↦
    poissonKernel 0 ((r : ℂ)⁻¹ * w) (AddCircle.toCircle t)
  let K₁ : AddCircle (1 : ℝ) → ℝ := fun t ↦ poissonKernel 0 w (AddCircle.toCircle t)
  let br : ℝ → AddCircle (1 : ℝ) → ℝ := fun r t ↦
    ‖x.diskFunction ((r : ℂ) * AddCircle.toCircle t)‖ ^ 2
  have hbr_cont {r : ℝ} (hr_pos : 0 < r) (hr1 : r < 1) : Continuous (br r) := by
    have hparam : Continuous fun t : AddCircle (1 : ℝ) ↦ (r : ℂ) * (AddCircle.toCircle t : ℂ) :=
      by fun_prop
    refine ((x.analyticOnNhd_diskFunction.continuousOn.comp_continuous hparam
      fun t ↦ ?_).norm).pow 2
    rw [mem_ball_zero_iff, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr_pos.le]
    exact hr1
  let I : ℝ → ℝ := fun r ↦ ∫ t : AddCircle (1 : ℝ), K r t * br r t ∂μ
  -- First piece: `∫ K r t * (br r t - b t) → 0` using a uniform kernel bound on `(r₀, 1)` and `L¹`
  -- convergence of `br r` to `b`.
  have hpiece1 : Tendsto (fun r : ℝ ↦ ∫ t : AddCircle (1 : ℝ), K r t * (br r t - b t) ∂μ)
      (𝓝[<] 1) (𝓝 0) := by
    set C₀ : ℝ := 1 / (1 - ‖w‖ / r₀) ^ 2 with hC₀_def
    have hgap_pos : 0 < 1 - ‖w‖ / r₀ := sub_pos.mpr ((div_lt_one hr₀_pos).mpr hwr₀)
    have hzero : Tendsto (fun r : ℝ ↦ C₀ * ∫ t : AddCircle (1 : ℝ), |br r t - b t| ∂μ)
        (𝓝[<] 1) (𝓝 0) := by
      simpa using x.tendsto_integral_abs_norm_sq_diskFunction_sub.const_mul C₀
    refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
        (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_)
    filter_upwards [Ioo_mem_nhdsLT hr₀_lt] with r hr
    have hr_pos : 0 < r := hr₀_pos.trans hr.1
    have hwr : ‖w‖ / r ≤ ‖w‖ / r₀ :=
      div_le_div_of_nonneg_left (norm_nonneg w) hr₀_pos hr.1.le
    have hK_le (t : AddCircle (1 : ℝ)) : |K r t| ≤ C₀ := by
      have hnorm_rw : ‖(r : ℂ)⁻¹ * w‖ = ‖w‖ / r := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr_pos.le, div_eq_inv_mul]
      have hK_nonneg : 0 ≤ K r t := by
        refine poissonKernel_nonneg ?_
        rw [sub_zero, sub_zero, Circle.norm_coe, hnorm_rw]
        exact hwr.trans ((div_lt_one hr₀_pos).mpr hwr₀).le
      have hK_def : K r t = poissonKernel 0 ((r : ℂ)⁻¹ * w) (AddCircle.toCircle t) := rfl
      rw [abs_of_nonneg hK_nonneg, hK_def, poissonKernel_def, sub_zero, sub_zero,
        Circle.norm_coe, hnorm_rw, hC₀_def]
      have hden : 1 - ‖w‖ / r₀ ≤ ‖(AddCircle.toCircle t : ℂ) - (r : ℂ)⁻¹ * w‖ := by
        have htri := norm_sub_norm_le (AddCircle.toCircle t : ℂ) ((r : ℂ)⁻¹ * w)
        rw [Circle.norm_coe, hnorm_rw] at htri
        linarith
      refine div_le_div₀ zero_le_one (by nlinarith [sq_nonneg (‖w‖ / r)]) (by positivity)
        (pow_le_pow_left₀ hgap_pos.le hden 2)
    have habs_int : Integrable (fun t : AddCircle (1 : ℝ) ↦ |br r t - b t|) μ :=
      (((hbr_cont hr_pos hr.2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).sub hb).abs
    rw [Real.norm_eq_abs, ← integral_const_mul]
    refine abs_integral_le_integral_abs.trans
      (integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ abs_nonneg _)
        (habs_int.const_mul C₀) (Eventually.of_forall fun t ↦ ?_))
    dsimp only
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK_le t) (abs_nonneg _)
  -- Second piece: `∫ (K r t - K₁ t) * b t → 0` by uniform convergence of the rescaled kernel.
  have hpiece2 : Tendsto (fun r : ℝ ↦ ∫ t : AddCircle (1 : ℝ), (K r t - K₁ t) * b t ∂μ)
      (𝓝[<] 1) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set δ : ℝ := ε / (‖x‖ ^ 2 + 1) with hδ_def
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hunif := (Metric.tendstoUniformly_iff.mp
      (tendstoUniformly_poissonKernel_inv_mul (T := 1) hw) δ hδ).filter_mono
        (nhdsWithin_le_nhds (s := Iio 1))
    filter_upwards [hunif] with r hr
    rw [Real.dist_0_eq_abs]
    have hle : |∫ t : AddCircle (1 : ℝ), (K r t - K₁ t) * b t ∂μ| ≤
        ∫ t : AddCircle (1 : ℝ), δ * b t ∂μ := by
      refine abs_integral_le_integral_abs.trans
        (integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ abs_nonneg _)
          (hb.const_mul δ) (Eventually.of_forall fun t ↦ ?_))
      have hbt : 0 ≤ b t := sq_nonneg _
      dsimp only
      rw [abs_mul, abs_of_nonneg hbt]
      have hdist : |K r t - K₁ t| < δ := by
        simpa [K, K₁, Real.dist_eq, abs_sub_comm] using hr t
      exact mul_le_mul_of_nonneg_right hdist.le hbt
    have hb_int_eq : (∫ t, b t ∂μ) = ‖x‖ ^ 2 := by
      dsimp only [b]
      rw [Lp.integral_norm_sq_eq_norm_sq, Submodule.norm_coe]
    have hint_eq : (∫ t : AddCircle (1 : ℝ), δ * b t ∂μ) = δ * ‖x‖ ^ 2 := by
      rw [integral_const_mul, hb_int_eq]
    have hlt : δ * ‖x‖ ^ 2 < ε := by
      rw [hδ_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [sq_nonneg ‖x‖]
    exact (hle.trans_eq hint_eq).trans_lt hlt
  -- Combine both pieces to show `I r → x.harmonicMajorant w`.
  have hI_tendsto : Tendsto I (𝓝[<] 1) (𝓝 (x.harmonicMajorant w)) := by
    have hsum := hpiece1.add hpiece2
    rw [add_zero] at hsum
    have hw' : w ∉ sphere (0 : ℂ) 1 := disjoint_right.mp sphere_disjoint_ball hw
    have hK₁b : Integrable (fun t : AddCircle (1 : ℝ) ↦ K₁ t * b t) μ := by
      simpa only [K₁, smul_eq_mul] using integrable_poissonKernel_smul hb hw'
    have hlim := hsum.add (tendsto_const_nhds (x := x.harmonicMajorant w))
    rw [zero_add] at hlim
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hr₀_lt] with r hr
    have hr_pos : 0 < r := hr₀_pos.trans hr.1
    have hwr_sphere : (r : ℂ)⁻¹ * w ∉ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hr_pos.le, ← div_eq_inv_mul]
      exact ((div_lt_one hr_pos).mpr (hwr₀.trans hr.1)).ne
    have hbr_int : Integrable (br r) μ :=
      (hbr_cont hr_pos hr.2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hK_br : Integrable (fun t : AddCircle (1 : ℝ) ↦ K r t * br r t) μ := by
      simpa only [K, smul_eq_mul] using integrable_poissonKernel_smul hbr_int hwr_sphere
    have hK_b : Integrable (fun t : AddCircle (1 : ℝ) ↦ K r t * b t) μ := by
      simpa only [K, smul_eq_mul] using integrable_poissonKernel_smul hb hwr_sphere
    have h1 : Integrable (fun t : AddCircle (1 : ℝ) ↦ K r t * (br r t - b t)) μ := by
      convert hK_br.sub hK_b using 1
      funext t
      dsimp only [Pi.sub_apply]
      ring
    have h2 : Integrable (fun t : AddCircle (1 : ℝ) ↦ (K r t - K₁ t) * b t) μ := by
      convert hK_b.sub hK₁b using 1
      funext t
      dsimp only [Pi.sub_apply]
      ring
    have h12 : Integrable
        (fun t : AddCircle (1 : ℝ) ↦ K r t * (br r t - b t) + (K r t - K₁ t) * b t) μ :=
      h1.add h2
    have hm : x.harmonicMajorant w = ∫ t : AddCircle (1 : ℝ), K₁ t * b t ∂μ := by
      simp [harmonicMajorant_def, circlePoissonIntegral_def, K₁, b, μ]
    rw [hm, ← integral_add h1 h2, ← integral_add h12 hK₁b]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    ring
  -- Finally bound `I r ≤ u w` on `Ioo r₀ 1` by the Poisson integral formula on `closedBall 0 r`.
  refine le_of_tendsto hI_tendsto ?_
  filter_upwards [Ioo_mem_nhdsLT hr₀_lt] with r hr
  have hr_pos : 0 < r := hr₀_pos.trans hr.1
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
  have hwr : w ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr (hwr₀.trans hr.1)
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball hr.2
  have hus : HarmonicOnNhd u (closedBall (0 : ℂ) r) := hu.mono hsub
  have hI_eq : I r =
      Real.circleAverage (poissonKernel 0 w • fun z ↦ ‖x.diskFunction z‖ ^ 2) 0 r := by
    rw [← AddCircle.integral_haarAddCircle_comp_toCircle (T := 1)
      (poissonKernel 0 w • fun z ↦ ‖x.diskFunction z‖ ^ 2) 0 r]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    dsimp only [K, br, Pi.smul_apply, smul_eq_mul]
    rw [add_zero]
    have hscale := poissonKernel_inv_mul_sub (c := 0) (a := w)
      (z := (r : ℂ) * (AddCircle.toCircle t : ℂ)) (q := (r : ℂ)) hr_ne
    simp only [sub_zero, inv_mul_cancel_left₀ hr_ne] at hscale
    rw [hscale]
    rfl
  rw [hI_eq, ← hus.circleAverage_poissonKernel_smul hwr]
  have hw_not_sphere : w ∉ sphere (0 : ℂ) |r| := by
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr_pos]
    exact (hwr₀.trans hr.1).ne
  have hK_sphere : ContinuousOn (poissonKernel 0 w) (sphere (0 : ℂ) |r|) :=
    continuousOn_poissonKernel hw_not_sphere
  have hsub' : closedBall (0 : ℂ) |r| ⊆ ball (0 : ℂ) 1 := by
    rwa [abs_of_pos hr_pos]
  refine Real.circleAverage_mono
    (hK_sphere.smul ((x.analyticOnNhd_diskFunction.continuousOn.mono
      (sphere_subset_closedBall.trans hsub')).norm.pow 2)).circleIntegrable'
    (hK_sphere.smul (hus.continuousOn.mono
      (by rw [abs_of_pos hr_pos]; exact sphere_subset_closedBall))).circleIntegrable'
    fun z hz ↦ ?_
  have hK_nonneg : 0 ≤ poissonKernel 0 w z := by
    refine poissonKernel_nonneg ?_
    rw [sub_zero, sub_zero, mem_sphere_zero_iff_norm.mp hz, abs_of_pos hr_pos]
    exact (hwr₀.trans hr.1).le
  exact mul_le_mul_of_nonneg_left (hmajor z (hsub' (sphere_subset_closedBall hz))) hK_nonneg

end General

/-! ### Explicit least harmonic majorants -/

section Examples

/-- The least harmonic majorant of the zero Hardy element vanishes everywhere. -/
@[simp]
theorem harmonicMajorant_zero_elem (w : ℂ) : (0 : HardySpace).harmonicMajorant w = 0 := by
  rw [harmonicMajorant_def]
  have hae : (fun t : UnitAddCircle ↦
      ‖((0 : HardySpace) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t‖ ^ 2) =ᵐ[
        AddCircle.haarAddCircle]
      fun _ : UnitAddCircle ↦ (0 : ℝ) := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (AddCircle.haarAddCircle (T := 1))] with t ht
    rw [Submodule.coe_zero, ht, Pi.zero_apply, norm_zero, sq, mul_zero]
  rw [circlePoissonIntegral_congr_ae hae, circlePoissonIntegral_zero]

/-- On the open unit disk, every Hardy basis monomial `hardyBasis n` (`w ↦ w ^ n`) has constant
least harmonic majorant `1` — in particular for `n ≥ 1`, its value `1` at `0` strictly exceeds
`‖(hardyBasis n).diskFunction 0‖ ^ 2 = 0`. -/
@[simp]
theorem harmonicMajorant_hardyBasis (n : ℕ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (hardyBasis n).harmonicMajorant w = 1 := by
  rw [harmonicMajorant_def]
  have hae : (fun t : UnitAddCircle ↦
      ‖(hardyBasis n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t‖ ^ 2) =ᵐ[
        AddCircle.haarAddCircle]
      fun _ : UnitAddCircle ↦ (1 : ℝ) := by
    filter_upwards [coeFn_fourierLp (T := 1) 2 (n : ℤ)] with t ht
    rw [coe_hardyBasis, coe_fourierBasis, ht, fourier_apply, Circle.norm_coe, one_pow]
  rw [circlePoissonIntegral_congr_ae hae, circlePoissonIntegral_const hw 1]

/-- On the open unit disk, the least harmonic majorant of `hardyBasis 0 + hardyBasis 1`
(whose disk function is `w ↦ 1 + w`) is `w ↦ 2 + 2 * w.re`. -/
theorem harmonicMajorant_hardyBasis_zero_add_one {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (hardyBasis 0 + hardyBasis 1).harmonicMajorant w = 2 + 2 * w.re := by
  rw [harmonicMajorant_def]
  have hae : (fun t : AddCircle (1 : ℝ) ↦
      ‖((hardyBasis 0 + hardyBasis 1 : HardySpace) :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t‖ ^ 2) =ᵐ[AddCircle.haarAddCircle]
      fun t : AddCircle (1 : ℝ) ↦
        (2 : ℝ) + (2 : ℝ) * (fourier (T := 1) ((1 : ℕ) : ℤ) t).re := by
    filter_upwards [Lp.coeFn_add (hardyBasis 0 : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))
        (hardyBasis 1),
      coeFn_fourierLp (T := 1) 2 ((0 : ℕ) : ℤ),
      coeFn_fourierLp (T := 1) 2 ((1 : ℕ) : ℤ)] with t hadd h0 h1
    rw [Submodule.coe_add, hadd, Pi.add_apply, coe_hardyBasis, coe_hardyBasis,
      coe_fourierBasis, h0, h1]
    have hf0 : fourier (T := 1) ((0 : ℕ) : ℤ) t = 1 := by simp [fourier_apply]
    have hnorm1 : Complex.normSq (fourier (T := 1) ((1 : ℕ) : ℤ) t) = 1 := by
      rw [← Complex.sq_norm, fourier_apply, Circle.norm_coe, one_pow]
    rw [Complex.normSq_apply] at hnorm1
    rw [hf0, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add]
    linarith
  have hw' : w ∉ sphere (0 : ℂ) 1 := disjoint_right.mp sphere_disjoint_ball hw
  have hre_cont : Continuous fun t : AddCircle (1 : ℝ) ↦
      (fourier (T := 1) ((1 : ℕ) : ℤ) t).re :=
    Complex.continuous_re.comp (fourier (T := 1) ((1 : ℕ) : ℤ)).continuous
  have hre_int : Integrable
      (fun t : AddCircle (1 : ℝ) ↦ (fourier (T := 1) ((1 : ℕ) : ℤ) t).re)
      AddCircle.haarAddCircle :=
    hre_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre_poisson : circlePoissonIntegral
      (fun t : AddCircle (1 : ℝ) ↦ (fourier (T := 1) ((1 : ℕ) : ℤ) t).re) w = w.re := by
    have hf_int : Integrable (fourier (T := 1) ((1 : ℕ) : ℤ) : AddCircle (1 : ℝ) → ℂ)
        AddCircle.haarAddCircle :=
      (fourier (T := 1) ((1 : ℕ) : ℤ)).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hint := integrable_poissonKernel_smul hf_int hw'
    have hcomm := Complex.reCLM.integral_comp_comm hint
    dsimp only [Complex.reCLM_apply] at hcomm
    calc circlePoissonIntegral
          (fun t : AddCircle (1 : ℝ) ↦ (fourier (T := 1) ((1 : ℕ) : ℤ) t).re) w
        = (circlePoissonIntegral (fourier (T := 1) ((1 : ℕ) : ℤ)) w).re := by
          rw [circlePoissonIntegral_def, circlePoissonIntegral_def, ← hcomm]
          refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
          simp [Complex.real_smul]
      _ = w.re := by rw [circlePoissonIntegral_fourier_nat hw 1, pow_one]
  rw [circlePoissonIntegral_congr_ae hae]
  have hconst_int : Integrable (fun _ : AddCircle (1 : ℝ) ↦ (2 : ℝ)) AddCircle.haarAddCircle :=
    integrable_const 2
  have hadd_eq :
      (fun t : AddCircle (1 : ℝ) ↦ (2 : ℝ) + (2 : ℝ) * (fourier (T := 1) ((1 : ℕ) : ℤ) t).re) =
        (fun _ ↦ (2 : ℝ)) + (2 : ℝ) • fun t ↦ (fourier (T := 1) ((1 : ℕ) : ℤ) t).re := by
    funext t
    simp [smul_eq_mul]
  rw [hadd_eq, circlePoissonIntegral_add hconst_int (hre_int.smul 2) hw',
    circlePoissonIntegral_const hw 2, circlePoissonIntegral_smul 2, hre_poisson, smul_eq_mul]

/-- For `hardyBasis 0 + hardyBasis 1` (`w ↦ 1 + w`), the gap between the least harmonic majorant
and the squared modulus at an interior point `w` is `1 - ‖w‖ ^ 2`. -/
theorem harmonicMajorant_hardyBasis_zero_add_one_sub_norm_sq {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (hardyBasis 0 + hardyBasis 1).harmonicMajorant w -
      ‖(hardyBasis 0 + hardyBasis 1).diskFunction w‖ ^ 2 = 1 - ‖w‖ ^ 2 := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  rw [harmonicMajorant_hardyBasis_zero_add_one hw,
    diskFunction_add (hardyBasis 0) (hardyBasis 1) hw1,
    diskFunction_hardyBasis, diskFunction_hardyBasis, pow_zero, pow_one]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add]
  ring

end Examples

end TauCeti.HardySpace

end
