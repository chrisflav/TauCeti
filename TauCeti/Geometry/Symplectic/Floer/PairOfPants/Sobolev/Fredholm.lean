/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.CoreParametrix
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.End.Parametrix
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm

import TauCeti.Analysis.Fredholm.CompactPerturbation
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace

/-!
# Linearized Floer operators on the pair of pants are Fredholm on `W^{1,2}`

Let `H_q` be jointly `C²` period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, with
value in a finite-dimensional symplectic vector space `(V, ω)`, and let `(J, K_s, K_t)` be Floer
data on `S` which far out on each end, beyond a height `R₁`, are cylindrical,
`J(φ'_q(s, t)) = J_q(t)` for `C¹` families `J_q`, with `(K_s, K_t)` the pair-of-pants perturbation
of `H`. Let `u` be a `C¹` map on `S`, solve the Floer equation beyond `R₁` on each end, and
have ends converging to nondegenerate one-periodic orbits `x_q` of `H_q`, with `J_q` compatible with
`ω` along `x_q`. On all of `S`, `J` is `C¹` and compatible along `u`, and `K_s`, `K_t` are `C²`
along `u`.

The file `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm` shows that the
conformal Sobolev realization `D_u : W^{1,2}_0(S, V) → L²(S, V)`
(`TauCeti.SymplecticForm.floerConformalSobolevOperator`) has finite-dimensional kernel and closed
range. This file proves that `D_u` has finite-codimensional range, hence is Fredholm, when the
stationary cylinder operators at the three asymptotic orbits are invertible.

## Parametrix construction

The right parametrix `P : L²(S, V) → W^{1,2}_0(S, V)` is spliced from four pieces using a smooth
partition of unity `β₀ + ∑ q, β_q = 1` on `ℝ × ℝ`, where `β_q` is supported in the end `q` past a
height `R₀` and `β₀` is compactly supported in `S`:

* On each end `q`, transferring the right inverse `Q_q` of the end model along `φ'_q` with cutoff
  `β_q` (`TauCeti.Floer.endTransfer`) produces `D_u (P_q h) = β_q h + K_q h + E_q h` with `K_q`
  compact and `‖E_q‖ ≤ 1 / 6` once `R₀ ≥ T₀ q`
  (`exists_forall_exists_isCompactOperator_jetOperator_floerConformalJetCoeff_endTransfer`).
  Because `‖w - c_q‖ ‖dβ_q(w)‖` and `‖w - c_q‖ √ρ(w) |β_q(w)|` admit a bound independent of `R₀`,
  the tolerance `1 / 6` is fixed before `R₀` is chosen.
* On the compact core `tsupport β₀ ⊆ S`, the local interior parametrix
  (`TauCeti.ConformalSobolev.exists_jetOperator_firstOrderJetCoeff_comp_eq_smul_add`) supplies
  `P₀` with `D_u (P₀ h) = β₀ h + K₀ h + E₀ h`, `K₀` compact and `‖E₀‖ ≤ 1 / 4`.

Summing the four pieces gives `D_u ∘ P - 1 = K + E` with `K` compact and `‖E‖ ≤ 3 / 4 < 1`.
Inverting `1 + E` via Neumann series yields an exact right parametrix `P (1 + E)⁻¹` modulo compact
operators, so `range D_u` has finite codimension by
`ContinuousLinearMap.cofg_range_of_isCompactOperator_comp_sub_one`. Combined with
`finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants`, this proves `D_u.IsFredholm`.

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `isFredholm_floerConformalSobolevOperator_pairOfPants_of_isInvertible`: `D_u` is Fredholm when
  the stationary cylinder operators at the three asymptotic orbits are invertible.
* `isFredholm_floerConformalSobolevOperator_pairOfPants_of_frame`: the same when each
  `J_q(t, x_q t)` admits a unitary frame and `H_q` is `C³`.
* `isFredholm_floerConformalSobolevOperator_pairOfPants`: on a complex inner product space with
  `ω = Im ⟪·, ·⟫`, `D_u` is Fredholm for every compatible family `J` that is `C²` along the
  asymptotic orbits, with `C³` Hamiltonians.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Real ContinuousLinearMap
  TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal NNReal Topology Manifold

namespace TauCeti

section ParametrixCriteria

/-- An operator with a right parametrix up to a compact operator and an error of norm `< 1` has
finite-codimensional range: composing on the right with `(1 + E)⁻¹` turns the error into a
compact perturbation of `1`. -/
private theorem cofg_range_of_isCompactOperator_comp_sub_one_add {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (D : E →L[ℝ] F) {P : F →L[ℝ] E} {K E_op : F →L[ℝ] F}
    (hD : D.comp P - 1 = K + E_op) (hK : IsCompactOperator K) (hE : ‖E_op‖ < 1) :
    D.range.CoFG := by
  let u := Units.oneSub (-E_op) (by rwa [norm_neg])
  have hu : (u : F →L[ℝ] F) = 1 + E_op := by
    rw [Units.val_oneSub, sub_neg_eq_add]
  let S' : F →L[ℝ] E := P.comp (↑u⁻¹ : F →L[ℝ] F)
  refine D.cofg_range_of_isCompactOperator_comp_sub_one (S := S') ?_
  have h1 : D.comp P = (1 + E_op) + K := by
    have hD' := congrArg (· + (1 : F →L[ℝ] F)) hD
    simpa only [sub_add_cancel] using hD'.trans (by abel)
  have hcomp : D.comp S' - 1 = K.comp (↑u⁻¹ : F →L[ℝ] F) := by
    calc D.comp S' - 1
        = (D.comp P).comp (↑u⁻¹ : F →L[ℝ] F) - 1 := by
          simp [S', ContinuousLinearMap.comp_assoc]
      _ = ((1 + E_op) + K).comp (↑u⁻¹ : F →L[ℝ] F) - 1 := by rw [h1]
      _ = (↑u : F →L[ℝ] F).comp (↑u⁻¹ : F →L[ℝ] F) +
            K.comp (↑u⁻¹ : F →L[ℝ] F) - 1 := by
          rw [hu, ContinuousLinearMap.add_comp]
      _ = 1 + K.comp (↑u⁻¹ : F →L[ℝ] F) - 1 := by
          rw [← ContinuousLinearMap.mul_def, Units.mul_inv]
      _ = K.comp (↑u⁻¹ : F →L[ℝ] F) := by abel
  rw [hcomp]
  exact hK.comp_clm _

end ParametrixCriteria

namespace Floer

section EndCoordDerivative

/-- The signed longitudinal coordinate `(positiveEndCoord q ·).1` has derivative bounded by
`‖w - c_q‖⁻¹` away from the end center `c_q`. -/
private theorem norm_fderiv_fst_positiveEndCoord_le (q : Puncture) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
      ‖fderiv ℝ (fun w ↦ (positiveEndCoord q w).1) z‖ ≤ 1 := by
  let g : ℝ × ℝ → ℂ := fun w ↦ Complex.equivRealProdCLM.symm w - q.endCenter
  let c : ℝ := -(q.endSign / (4 * π))
  let d : ℝ := q.endSign * Real.log ‖q.endScale‖ / (2 * π)
  have hgz : g z ≠ 0 := sub_ne_zero.2 hz
  have hnorm_pos : 0 < ‖g z‖ := norm_pos_iff.2 hgz
  have hev : (fun w ↦ (positiveEndCoord q w).1) =ᶠ[𝓝 z]
      fun w ↦ c * Real.log (‖g w‖ ^ 2) + d := by
    filter_upwards [(isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous
      continuous_const).mem_nhds hz] with w hw
    have hgw : 0 < ‖g w‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
    rw [fst_positiveEndCoord, re_endCoord, norm_div, Real.log_div hgw.ne'
      (norm_ne_zero_iff.2 q.endScale_ne_zero), Real.log_pow]
    simp only [Nat.cast_ofNat, g, c, d]
    ring
  let symm : ℝ × ℝ →L[ℝ] ℂ := Complex.equivRealProdCLM.symm
  have hg : HasFDerivAt g symm z := symm.hasFDerivAt.sub_const q.endCenter
  have hsq : HasFDerivAt (fun w ↦ ‖g w‖ ^ 2) ((2 • innerSL ℝ (g z)).comp symm) z :=
    (hasStrictFDerivAt_norm_sq (g z)).hasFDerivAt.comp z hg
  have hlog : HasFDerivAt (fun w ↦ Real.log (‖g w‖ ^ 2))
      ((‖g z‖ ^ 2)⁻¹ • ((2 • innerSL ℝ (g z)).comp symm)) z :=
    hsq.log (pow_ne_zero 2 hnorm_pos.ne')
  have hfull : HasFDerivAt (fun w ↦ c * Real.log (‖g w‖ ^ 2) + d)
      (c • ((‖g z‖ ^ 2)⁻¹ • ((2 • innerSL ℝ (g z)).comp symm))) z :=
    (hlog.const_mul c).add_const d
  rw [hev.fderiv_eq, hfull.fderiv]
  have hsymm (v : ℝ × ℝ) : ‖symm v‖ ≤ 2 * ‖v‖ := by
    have heq : symm v = (v.1 : ℂ) + (v.2 : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [symm]
    rw [heq]
    calc ‖(v.1 : ℂ) + (v.2 : ℂ) * Complex.I‖
        ≤ ‖(v.1 : ℂ)‖ + ‖(v.2 : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |v.1| + |v.2| := by simp [Complex.norm_real]
      _ ≤ ‖v‖ + ‖v‖ := add_le_add (by simpa [Real.norm_eq_abs] using norm_fst_le v)
          (by simpa [Real.norm_eq_abs] using norm_snd_le v)
      _ = 2 * ‖v‖ := by ring
  have hc_abs : |c| = 1 / (4 * π) := by
    have hsign : |q.endSign| = 1 := by
      rcases q.endSign_eq_one_or_eq_neg_one with h | h <;> simp [h]
    simp only [c, abs_neg, abs_div, hsign, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]
  have hsymm_norm : ‖symm‖ ≤ 2 := ContinuousLinearMap.opNorm_le_bound _ zero_le_two hsymm
  have hop : ‖c • ((‖g z‖ ^ 2)⁻¹ • ((2 • innerSL ℝ (g z)).comp symm))‖ ≤
      (π * ‖g z‖)⁻¹ := by
    have h2n : ‖(2 : ℕ) • innerSL ℝ (g z)‖ = 2 * ‖g z‖ := by
      rw [two_nsmul, ← two_smul ℝ, norm_smul, Real.norm_eq_abs, abs_of_pos two_pos,
        innerSL_apply_norm]
    have hcomp : ‖((2 : ℕ) • innerSL ℝ (g z)).comp symm‖ ≤ (2 * ‖g z‖) * 2 :=
      (opNorm_comp_le _ _).trans (by
        rw [h2n]
        exact mul_le_mul_of_nonneg_left hsymm_norm (by positivity))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, hc_abs, Real.norm_eq_abs, abs_inv, abs_pow,
      abs_of_pos hnorm_pos]
    calc (1 / (4 * π)) * ((‖g z‖ ^ 2)⁻¹ * ‖((2 : ℕ) • innerSL ℝ (g z)).comp symm‖)
        ≤ (1 / (4 * π)) * ((‖g z‖ ^ 2)⁻¹ * ((2 * ‖g z‖) * 2)) := by gcongr
      _ = (π * ‖g z‖)⁻¹ := by
          have hgz_ne : ‖g z‖ ≠ 0 := hnorm_pos.ne'
          have hpi_ne : π ≠ 0 := pi_ne_zero
          field_simp
          ring
  calc ‖g z‖ * ‖c • ((‖g z‖ ^ 2)⁻¹ • ((2 • innerSL ℝ (g z)).comp symm))‖
      ≤ ‖g z‖ * (π * ‖g z‖)⁻¹ := mul_le_mul_of_nonneg_left hop hnorm_pos.le
    _ = π⁻¹ := by
        rw [mul_inv, mul_comm π⁻¹ ‖g z‖⁻¹, ← mul_assoc, mul_inv_cancel₀ hnorm_pos.ne', one_mul]
    _ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [two_le_pi])

end EndCoordDerivative

section PlaneCutoff

/-- The smooth end cutoff `β_q` on all of `ℝ × ℝ`, extended across `c_q` by `0` at `q = ∞` and
`1` at `q = 0, 1`. For `0 ≤ R₀`, it is globally `C^2` on `ℝ × ℝ`. -/
private def endPlaneCutoff (R₀ : ℝ) (q : Puncture) (z : ℝ × ℝ) : ℝ :=
  if Complex.equivRealProdCLM.symm z = q.endCenter then
    (if q = inf then 0 else 1)
  else
    Real.smoothTransition (2 * ((positiveEndCoord q z).1 - R₀) - 1)

private theorem endPlaneCutoff_of_ne (R₀ : ℝ) {q : Puncture} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    endPlaneCutoff R₀ q z = Real.smoothTransition (2 * ((positiveEndCoord q z).1 - R₀) - 1) :=
  by simp [endPlaneCutoff, hz]

private theorem endPlaneCutoff_eq_zero_of_le {R₀ : ℝ} {q : Puncture} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter)
    (h : (positiveEndCoord q z).1 ≤ R₀) : endPlaneCutoff R₀ q z = 0 := by
  rw [endPlaneCutoff_of_ne R₀ hz]
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem endPlaneCutoff_eq_one_of_le {R₀ : ℝ} {q : Puncture} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter)
    (h : R₀ + 1 ≤ (positiveEndCoord q z).1) : endPlaneCutoff R₀ q z = 1 := by
  rw [endPlaneCutoff_of_ne R₀ hz]
  exact Real.smoothTransition.one_of_one_le (by linarith)

private theorem endPlaneCutoff_eventuallyEq_zero_of_inf {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z = inf.endCenter) :
    endPlaneCutoff R₀ inf =ᶠ[𝓝 z] 0 := by
  have hmem : {w : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm w‖ < 2} ∈ 𝓝 z := by
    refine (isOpen_lt Complex.equivRealProdCLM.symm.continuous.norm continuous_const).mem_nhds ?_
    simp [hz, endCenter_inf]
  filter_upwards [hmem] with w hw
  by_cases hwc : Complex.equivRealProdCLM.symm w = inf.endCenter
  · simp [endPlaneCutoff, hwc]
  · have hw0 : Complex.equivRealProdCLM.symm w ≠ 0 := by simpa [endCenter_inf] using hwc
    have hle : (positiveEndCoord inf w).1 ≤ 0 := by
      by_contra! hpos
      have h2 := (lt_fst_positiveEndCoord_inf_iff hw0).1 hpos
      rw [mul_zero, Real.exp_zero, mul_one] at h2
      linarith
    exact endPlaneCutoff_eq_zero_of_le hwc (hle.trans hR₀)

private theorem endPlaneCutoff_eventuallyEq_one_of_ne_inf (R₀ : ℝ) {q : Puncture} (hq : q ≠ inf)
    {z : ℝ × ℝ} (hz : Complex.equivRealProdCLM.symm z = q.endCenter) :
    endPlaneCutoff R₀ q =ᶠ[𝓝 z] 1 := by
  set δ : ℝ := Real.exp (-(2 * π * (R₀ + 1))) / 2
  have hδ : 0 < δ := by positivity
  have hmem : {w : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm w - q.endCenter‖ < δ} ∈ 𝓝 z := by
    refine (isOpen_lt (Complex.equivRealProdCLM.symm.continuous.sub continuous_const).norm
      continuous_const).mem_nhds ?_
    simpa [hz] using hδ
  filter_upwards [hmem] with w hw
  by_cases hwc : Complex.equivRealProdCLM.symm w = q.endCenter
  · simp [endPlaneCutoff, hwc, hq]
  · have hre : R₀ + 1 ≤ (q.endCoord (Complex.equivRealProdCLM.symm w)).re :=
      le_re_endCoord_of_norm_sub_endCenter_le hq hwc hw.le
    have hle : R₀ + 1 ≤ (positiveEndCoord q w).1 := by
      rwa [fst_positiveEndCoord, endSign_eq_one hq, one_mul]
    exact endPlaneCutoff_eq_one_of_le hwc hle

private theorem contDiff_endPlaneCutoff {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (q : Puncture) :
    ContDiff ℝ 2 (endPlaneCutoff R₀ q) := by
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  by_cases hz : Complex.equivRealProdCLM.symm z = q.endCenter
  · by_cases hq : q = inf
    · subst hq
      exact contDiffAt_const.congr_of_eventuallyEq (endPlaneCutoff_eventuallyEq_zero_of_inf hR₀ hz)
    · exact contDiffAt_const.congr_of_eventuallyEq
        (endPlaneCutoff_eventuallyEq_one_of_ne_inf R₀ hq hz)
  · have hev : endPlaneCutoff R₀ q =ᶠ[𝓝 z]
        fun w ↦ Real.smoothTransition (2 * ((positiveEndCoord q w).1 - R₀) - 1) := by
      filter_upwards [(isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous
        continuous_const).mem_nhds hz] with w hw
      exact endPlaneCutoff_of_ne R₀ hw
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact Real.smoothTransition.contDiff.contDiffAt.comp z
      ((contDiffAt_const.mul ((contDiffAt_fst_positiveEndCoord q hz).sub contDiffAt_const)).sub
        contDiffAt_const)

private theorem tsupport_endPlaneCutoff_subset {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (q : Puncture)
    {z : ℝ × ℝ} (hz : z ∈ tsupport (endPlaneCutoff R₀ q))
    (hzc : Complex.equivRealProdCLM.symm z ≠ q.endCenter) : z ∈ thricePuncturedSphereReal := by
  by_contra hnot
  rw [mem_thricePuncturedSphereReal_iff, not_and_or, not_not, not_not] at hnot
  have hneg : (positiveEndCoord q z).1 < 0 := by
    by_cases hq : q = inf
    · subst hq
      have h1 : Complex.equivRealProdCLM.symm z = 1 :=
        hnot.resolve_left (by simpa [endCenter_inf] using hzc)
      rw [fst_positiveEndCoord, endSign_inf, neg_one_mul, h1, neg_lt_zero]
      exact re_endCoord_inf_one_pos
    · rw [fst_positiveEndCoord, endSign_eq_one hq, one_mul]
      exact re_endCoord_lt_zero hq hnot hzc
  have hev : endPlaneCutoff R₀ q =ᶠ[𝓝 z] 0 := by
    have hcont := continuousAt_fst_positiveEndCoord q hzc
    have hopen := (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).mem_nhds
      hzc
    filter_upwards [hopen, hcont.eventually (Iio_mem_nhds (hneg.trans_le hR₀))] with w hwc hwlt
    exact endPlaneCutoff_eq_zero_of_le hwc hwlt.le
  exact (notMem_tsupport_iff_eventuallyEq.2 hev) hz

private theorem exists_bound_endPlaneCutoff :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {R₀ : ℝ}, 0 ≤ R₀ → ∀ (q : Puncture) (z : ℝ × ℝ),
      Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      |endPlaneCutoff R₀ q z| ≤ B ∧
        ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
          (√(cylindricalWeight z) * |endPlaneCutoff R₀ q z|) ≤ B ∧
        ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
          ‖fderiv ℝ (endPlaneCutoff R₀ q) z‖ ≤ B := by
  obtain ⟨Mψ, hMψ⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ 0)
  set B : ℝ := max (Real.sqrt 5) (max 1 (2 * Mψ))
  refine ⟨B, le_max_of_le_right (le_max_left _ _), fun {R₀} hR₀ q z hzc ↦ ?_⟩
  have hB1 : 1 ≤ B := le_max_of_le_right (le_max_left _ _)
  have hB5 : Real.sqrt 5 ≤ B := le_max_left _ _
  have hBM : 2 * Mψ ≤ B := le_max_of_le_right (le_max_right _ _)
  have h1 : |endPlaneCutoff R₀ q z| ≤ B := by
    rw [endPlaneCutoff_of_ne R₀ hzc]
    exact (Real.smoothTransition.abs_le_one _).trans hB1
  have h2 : ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
      (√(cylindricalWeight z) * |endPlaneCutoff R₀ q z|) ≤ B := by
    by_cases hpos : 0 < (positiveEndCoord q z).1
    · obtain ⟨h0, h1'⟩ := q.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos
        (by simpa only [fst_positiveEndCoord] using hpos)
      have hzS : z ∈ thricePuncturedSphereReal := mem_thricePuncturedSphereReal_iff.2 ⟨h0, h1'⟩
      have hsq : ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2 *
          cylindricalWeight z ≤ 5 :=
        norm_sub_endCenter_sq_mul_cylindricalWeight_le q hzS hpos.le
      have hsqrt : ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
          √(cylindricalWeight z) ≤ Real.sqrt 5 := by
        have := Real.sqrt_le_sqrt hsq
        rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
      have habs : |endPlaneCutoff R₀ q z| ≤ 1 := by
        rw [endPlaneCutoff_of_ne R₀ hzc]
        exact Real.smoothTransition.abs_le_one _
      calc ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
            (√(cylindricalWeight z) * |endPlaneCutoff R₀ q z|)
          = (‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * √(cylindricalWeight z)) *
              |endPlaneCutoff R₀ q z| := by ring
        _ ≤ Real.sqrt 5 * 1 :=
            mul_le_mul hsqrt habs (abs_nonneg _) (Real.sqrt_nonneg _)
        _ ≤ B := by linarith
    · rw [endPlaneCutoff_eq_zero_of_le hzc ((not_lt.1 hpos).trans hR₀), abs_zero, mul_zero,
        mul_zero]
      linarith
  have h3 : ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
      ‖fderiv ℝ (endPlaneCutoff R₀ q) z‖ ≤ B := by
    have hev : endPlaneCutoff R₀ q =ᶠ[𝓝 z]
        fun w ↦ Real.smoothTransition (2 * ((positiveEndCoord q w).1 - R₀) - 1) := by
      filter_upwards [(isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous
        continuous_const).mem_nhds hzc] with w hw
      exact endPlaneCutoff_of_ne R₀ hw
    have hfderiv : fderiv ℝ (endPlaneCutoff R₀ q) z =
        deriv Real.smoothTransition (2 * ((positiveEndCoord q z).1 - R₀) - 1) •
          (2 : ℝ) • fderiv ℝ (fun w ↦ (positiveEndCoord q w).1) z := by
      rw [hev.fderiv_eq]
      exact ((((contDiffAt_fst_positiveEndCoord q hzc (n := 1)).differentiableAt
        one_ne_zero).hasFDerivAt.sub_const R₀).const_mul 2 |>.sub_const 1).smoothTransition.fderiv
    rw [hfderiv, norm_smul, norm_smul]
    have hdψ : ‖deriv Real.smoothTransition (2 * ((positiveEndCoord q z).1 - R₀) - 1)‖ ≤ Mψ :=
      hMψ _
    have h2n : ‖(2 : ℝ)‖ = 2 := by norm_num
    rw [h2n]
    have hcoord := norm_fderiv_fst_positiveEndCoord_le q hzc
    calc ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
          (‖deriv Real.smoothTransition (2 * ((positiveEndCoord q z).1 - R₀) - 1)‖ *
            (2 * ‖fderiv ℝ (fun w ↦ (positiveEndCoord q w).1) z‖))
        = (2 * ‖deriv Real.smoothTransition (2 * ((positiveEndCoord q z).1 - R₀) - 1)‖) *
            (‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
              ‖fderiv ℝ (fun w ↦ (positiveEndCoord q w).1) z‖) := by ring
      _ ≤ (2 * Mψ) * 1 := by
          refine mul_le_mul (by linarith) hcoord (by positivity) (by positivity)
      _ ≤ B := by linarith
  exact ⟨h1, h2, h3⟩

private theorem endPlaneCutoff_positiveEndChart_eq_zero {T₀ R₀ : ℝ}
    (hTR : T₀ ≤ R₀) (q : Puncture) {ζ : ℝ × ℝ} (hζ : ζ.1 ≤ T₀) :
    endPlaneCutoff R₀ q (positiveEndChart q ζ) = 0 :=
  endPlaneCutoff_eq_zero_of_le (equivRealProdCLM_symm_positiveEndChart_ne_endCenter q ζ)
    (by rw [fst_positiveEndCoord_positiveEndChart]; exact hζ.trans hTR)

private theorem fderiv_endPlaneCutoff_positiveEndChart_eq_zero {T₀ R₀ : ℝ} (hTR : T₀ ≤ R₀)
    (q : Puncture) {ζ : ℝ × ℝ} (hζ : ζ.1 ≤ T₀ ∨ R₀ + 1 ≤ ζ.1) :
    fderiv ℝ (endPlaneCutoff R₀ q) (positiveEndChart q ζ) = 0 := by
  have hzc := equivRealProdCLM_symm_positiveEndChart_ne_endCenter q ζ
  have hev : endPlaneCutoff R₀ q =ᶠ[𝓝 (positiveEndChart q ζ)]
      fun w ↦ Real.smoothTransition (2 * ((positiveEndCoord q w).1 - R₀) - 1) := by
    filter_upwards [(isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous
      continuous_const).mem_nhds hzc] with w hw
    exact endPlaneCutoff_of_ne R₀ hw
  have hfderiv : fderiv ℝ (endPlaneCutoff R₀ q) (positiveEndChart q ζ) =
      deriv Real.smoothTransition
        (2 * ((positiveEndCoord q (positiveEndChart q ζ)).1 - R₀) - 1) •
        (2 : ℝ) • fderiv ℝ (fun w ↦ (positiveEndCoord q w).1) (positiveEndChart q ζ) := by
    rw [hev.fderiv_eq]
    exact ((((contDiffAt_fst_positiveEndCoord q hzc (n := 1)).differentiableAt
      one_ne_zero).hasFDerivAt.sub_const R₀).const_mul 2 |>.sub_const 1).smoothTransition.fderiv
  rw [hfderiv, fst_positiveEndCoord_positiveEndChart]
  rcases hζ with hle | hge
  · rw [Real.smoothTransition.deriv_of_nonpos (by linarith), zero_smul]
  · rw [Real.smoothTransition.deriv_of_one_le (by linarith), zero_smul]

/-- The core cutoff `1 - ∑ q, endPlaneCutoff R₀ q`, smooth and compactly supported in `S`. -/
private def corePlaneCutoff (R₀ : ℝ) (z : ℝ × ℝ) : ℝ :=
  1 - ∑ q : Puncture, endPlaneCutoff R₀ q z

private theorem corePlaneCutoff_add_sum_endPlaneCutoff (R₀ : ℝ) (z : ℝ × ℝ) :
    corePlaneCutoff R₀ z + ∑ q : Puncture, endPlaneCutoff R₀ q z = 1 :=
  sub_add_cancel 1 _

private theorem contDiff_corePlaneCutoff {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ContDiff ℝ 2 (corePlaneCutoff R₀) :=
  contDiff_const.sub (ContDiff.sum fun q _ ↦ contDiff_endPlaneCutoff hR₀ q)

private theorem tsupport_corePlaneCutoff_subset {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    tsupport (corePlaneCutoff R₀) ⊆
      Complex.equivRealProdCLM.symm ⁻¹' ThricePuncturedSphere.truncation (R₀ + 1) := by
  refine (isCompact_preimage_truncation (R₀ + 1)).isClosed.closure_subset_iff.2 fun z hz ↦ ?_
  by_contra hnot
  apply hz
  by_cases hzS : z ∈ thricePuncturedSphereReal
  · obtain ⟨q, hq⟩ := exists_lt_fst_positiveEndCoord_of_notMem_truncation hzS hnot
    have hsum : ∑ r : Puncture, endPlaneCutoff R₀ r z = 1 := by
      rw [Finset.sum_eq_single q]
      · exact endPlaneCutoff_eq_one_of_le
          (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hzS) q) hq.le
      · intro r _ hrq
        exact endPlaneCutoff_eq_zero_of_le
          (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hzS) r)
          ((fst_positiveEndCoord_nonpos_of_ne hrq.symm (by linarith)).trans hR₀)
      · intro h; exact absurd (Finset.mem_univ q) h
    simp [corePlaneCutoff, hsum]
  · rw [mem_thricePuncturedSphereReal_iff, not_and_or, not_not, not_not] at hzS
    have huniv : (Finset.univ : Finset Puncture) = {zero, one, inf} := by decide
    rcases hzS with hz0 | hz1
    · have h0 : endPlaneCutoff R₀ zero z = 1 := by simp [endPlaneCutoff, hz0]
      have hinf : endPlaneCutoff R₀ inf z = 0 := by simp [endPlaneCutoff, hz0]
      have h1 : endPlaneCutoff R₀ one z = 0 := by
        have hne : Complex.equivRealProdCLM.symm z ≠ one.endCenter := by
          rw [hz0, endCenter_one]; norm_num
        refine endPlaneCutoff_eq_zero_of_le hne ?_
        rw [fst_positiveEndCoord, endSign_one, one_mul]
        exact (re_endCoord_lt_zero (by decide) (Or.inl hz0) hne).le.trans hR₀
      have hsum : ∑ r : Puncture, endPlaneCutoff R₀ r z = 1 := by
        rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_singleton, h0, h1, hinf]
        norm_num
      rw [corePlaneCutoff, hsum, sub_self]
    · have h1 : endPlaneCutoff R₀ one z = 1 := by simp [endPlaneCutoff, hz1]
      have hinf : endPlaneCutoff R₀ inf z = 0 := by
        have hne : Complex.equivRealProdCLM.symm z ≠ inf.endCenter := by
          rw [hz1, endCenter_inf]; exact one_ne_zero
        refine endPlaneCutoff_eq_zero_of_le hne ?_
        rw [fst_positiveEndCoord, endSign_inf, neg_one_mul, hz1]
        linarith [re_endCoord_inf_one_pos]
      have h0 : endPlaneCutoff R₀ zero z = 0 := by
        have hne : Complex.equivRealProdCLM.symm z ≠ zero.endCenter := by
          rw [hz1, endCenter_zero]; exact one_ne_zero
        refine endPlaneCutoff_eq_zero_of_le hne ?_
        rw [fst_positiveEndCoord, endSign_zero, one_mul]
        exact (re_endCoord_lt_zero (by decide) (Or.inr hz1) hne).le.trans hR₀
      have hsum : ∑ r : Puncture, endPlaneCutoff R₀ r z = 1 := by
        rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_singleton, h0, h1, hinf]
        norm_num
      rw [corePlaneCutoff, hsum, sub_self]

private theorem hasCompactSupport_corePlaneCutoff {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    HasCompactSupport (corePlaneCutoff R₀) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_preimage_truncation (R₀ + 1))
    (subset_closure.trans (tsupport_corePlaneCutoff_subset hR₀))

end PlaneCutoff

end Floer

namespace SymplecticForm

open Floer ConformalSobolev

section IsInvertible

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The linearized Floer operator on the pair of pants is Fredholm when its end models are
invertible.** Under the hypotheses of
`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants`, if in
addition the stationary cylinder operator `∂s + J_q(t, x_q t) (∂t - dX_{H'_q(t)}(x_q t))` on each
end `q` is invertible from `W^{1,2}(ℝ × S¹, V)` to `L²(ℝ × S¹, V)`, then the conformal Sobolev
realization `D_u : W^{1,2}_0(S, V) → L²(S, V)` is Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_pairOfPants_of_isInvertible (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hinv : ∀ q, (stationarySobolevOperator (fun t ↦ Je q t (x q t))
      fun t ↦ fderiv ℝ
        (ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (x q t)).IsInvertible) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm := by
  set S := thricePuncturedSphereReal
  set ρ := cylindricalWeight
  set Jclm : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  set D := ω.floerConformalSobolevOperator S ρ Jclm Ks Kt u
  have hker : FiniteDimensional ℝ (LinearMap.ker (D : H1 V S ρ →ₗ[ℝ] Lp V 2 (volume.restrict S))) :=
    ω.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants hH hHs hX hx hnd hJe hJex
      hJeq hK hJ hKs hKt hu hc hF hux hδ
  have hxc (q : Puncture) : Continuous (x q) :=
    continuous_iff_continuousAt.2 fun t ↦ (hx q t).continuousAt
  have hM : MemLp (ω.floerConformalJetCoeff ρ Jclm Ks Kt u) ∞ (volume.restrict S) :=
    ω.memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn hH hHs
      (fun q ↦ (hxc q).continuousOn) hJe hJeq hK hJ hKs hKt hu hF hux hδ
  obtain ⟨B, hB1, hB⟩ := exists_bound_endPlaneCutoff
  have hB_pos : 0 < B := by linarith
  -- Choose the uniform tolerance `1 / (6 * B)` before fixing the cutoff height `R₀`.
  set ε_end : ℝ := 1 / (6 * B)
  have hε_end : 0 < ε_end := by positivity
  set T : ℝ := max R₁ 2
  have hend_pt (q : Puncture) {ζ : ℝ × ℝ} (hζ : T ≤ ζ.1) :
      positiveEndChart q ζ ∈ S ∧ R₁ ≤ (positiveEndCoord q (positiveEndChart q ζ)).1 := by
    rw [fst_positiveEndCoord_positiveEndChart]
    exact ⟨positiveEndChart_mem_thricePuncturedSphereReal (by linarith [le_max_right R₁ 2]),
      (le_max_left R₁ 2).trans hζ⟩
  have hQ_raw : ∀ q : Puncture, ∃ Q : Lp V 2 StripSobolev.stripMeasure →L[ℝ] CylinderSobolev.H1 V,
      ∃ T₀ : ℝ, ∀ {β : ℝ × ℝ → ℝ} {B' T₁ : ℝ}, ContDiff ℝ 1 β →
        (∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ q.endCenter → z ∈ S) →
        (∀ z, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
          |β z| ≤ B' ∧ ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * (√(ρ z) * |β z|) ≤ B' ∧
            ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * ‖fderiv ℝ β z‖ ≤ B') →
        (∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ → β (positiveEndChart q ζ) = 0) →
        (∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → fderiv ℝ β (positiveEndChart q ζ) = 0) →
        ∃ K E : Lp V 2 StripSobolev.stripMeasure →L[ℝ] Lp V 2 StripSobolev.stripMeasure,
          IsCompactOperator K ∧ ‖E‖ ≤ B' * ε_end ∧ ∀ h, ((positiveEndChartLp q).symm (jetOperator
            (volume.restrict S) (ω.floerConformalJetCoeff ρ Jclm Ks Kt u)
            (endTransfer q β (Q h))) : ℝ × ℝ → V) =ᵐ[StripSobolev.stripMeasure]
            fun ζ ↦ β (positiveEndChart q ζ) • h ζ + K h ζ + E h ζ := fun q ↦ by
    obtain ⟨Q, hQ⟩ :=
      ω.exists_forall_exists_isCompactOperator_jetOperator_floerConformalJetCoeff_endTransfer hH
        (hHs q) (hJe q) (fun ζ hζ ↦ hJeq q ζ ((le_max_left R₁ 2).trans hζ))
        (fun ζ hζ ↦ hK q _ (hend_pt q hζ).1 (hend_pt q hζ).2)
        (fun ζ hζ ↦ (hu _ (hend_pt q hζ).1).differentiableAt one_ne_zero)
        (fun ζ hζ ↦ hF q _ (hend_pt q hζ).1 (hend_pt q hζ).2)
        hM (hxc q) (hux q) (hδ q) (hinv q)
    obtain ⟨T₀, hT₀⟩ := hQ ε_end hε_end
    exact ⟨Q, T₀, hT₀⟩
  choose Q T₀ hT₀ using hQ_raw
  set R₀ : ℝ := max 2 (max (T₀ zero) (max (T₀ one) (T₀ inf)))
  have hR₀0 : 0 ≤ R₀ := by linarith [le_max_left 2 (max (T₀ zero) (max (T₀ one) (T₀ inf)))]
  have hTR (q : Puncture) : T₀ q ≤ R₀ := by
    cases q
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  -- Build the end pieces `P_q` for `β_q = endPlaneCutoff R₀ q`.
  have hEndPiece : ∀ q : Puncture,
      ∃ (Pq : Lp V 2 (volume.restrict S) →L[ℝ] H1 V S ρ)
        (Kq Eq : Lp V 2 (volume.restrict S) →L[ℝ] Lp V 2 (volume.restrict S)),
        IsCompactOperator Kq ∧ ‖Eq‖ ≤ (1 / 6 : ℝ) ∧
        ∀ h, (D (Pq h) : ℝ × ℝ → V) =ᵐ[volume.restrict S]
          fun z ↦ endPlaneCutoff R₀ q z • h z + Kq h z + Eq h z := fun q ↦ by
    obtain ⟨K_st, E_st, hK_st, hE_st, hid_st⟩ := hT₀ q
      ((contDiff_endPlaneCutoff hR₀0 q).of_le one_le_two)
      (fun _ hz hzc ↦ tsupport_endPlaneCutoff_subset hR₀0 q hz hzc)
      (hB hR₀0 q)
      (fun _ hζ ↦ endPlaneCutoff_positiveEndChart_eq_zero (hTR q) q hζ)
      (fun _ hζ ↦ fderiv_endPlaneCutoff_positiveEndChart_eq_zero (hTR q) q hζ)
    set eqv : Lp V 2 StripSobolev.stripMeasure ≃ₗᵢ[ℝ] Lp V 2 (volume.restrict S) :=
      positiveEndChartLp q
    let eqvCLM : Lp V 2 StripSobolev.stripMeasure →L[ℝ] Lp V 2 (volume.restrict S) :=
      eqv.toLinearIsometry.toContinuousLinearMap
    let eqvSymmCLM : Lp V 2 (volume.restrict S) →L[ℝ] Lp V 2 StripSobolev.stripMeasure :=
      eqv.symm.toLinearIsometry.toContinuousLinearMap
    let transf : CylinderSobolev.H1 V →L[ℝ] H1 V S ρ :=
      ((endTransfer q (endPlaneCutoff R₀ q)).comp (CylinderSobolev.H1 V).subtypeL).codRestrict
        (H1 V S ρ) fun x ↦ endTransfer_mem_H1 q (contDiff_endPlaneCutoff hR₀0 q)
          (fun _ hz hzc ↦ tsupport_endPlaneCutoff_subset hR₀0 q hz hzc) (hB hR₀0 q) x.property
    let Pq : Lp V 2 (volume.restrict S) →L[ℝ] H1 V S ρ := transf ∘L Q q ∘L eqvSymmCLM
    let Kq : Lp V 2 (volume.restrict S) →L[ℝ] Lp V 2 (volume.restrict S) :=
      eqvCLM ∘L K_st ∘L eqvSymmCLM
    let Eq : Lp V 2 (volume.restrict S) →L[ℝ] Lp V 2 (volume.restrict S) :=
      eqvCLM ∘L E_st ∘L eqvSymmCLM
    refine ⟨Pq, Kq, Eq, (hK_st.clm_comp eqvCLM).comp_clm eqvSymmCLM, ?_, fun h ↦ ?_⟩
    · have hE_le : ‖Eq‖ ≤ ‖E_st‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg E_st)
        fun h ↦ by
          change ‖eqv (E_st (eqv.symm h))‖ ≤ ‖E_st‖ * ‖h‖
          rw [eqv.norm_map]
          exact (E_st.le_opNorm _).trans (by rw [eqv.symm.norm_map])
      have hBε : B * ε_end = 1 / 6 := by
        simp only [ε_end]
        field_simp [hB_pos.ne']
      exact hE_le.trans (hE_st.trans_eq hBε)
    · have hdiff : D (Pq h) - Kq h - Eq h =
          eqv (eqv.symm (D (Pq h)) - K_st (eqv.symm h) - E_st (eqv.symm h)) := by
        simp only [map_sub, LinearIsometryEquiv.apply_symm_apply]
        rfl
      have hae_diff : (eqv (eqv.symm (D (Pq h)) - K_st (eqv.symm h) - E_st (eqv.symm h)) :
          ℝ × ℝ → V) =ᵐ[volume.restrict S] fun z ↦ endPlaneCutoff R₀ q z • h z := by
        have hstep1 := coeFn_positiveEndChartLp q
          (eqv.symm (D (Pq h)) - K_st (eqv.symm h) - E_st (eqv.symm h))
        have hstep2 := (quasiMeasurePreserving_endBandCoord q).ae (hid_st (eqv.symm h))
        have hstep3 := (quasiMeasurePreserving_endBandCoord q).ae
          (coeFn_positiveEndChartLp_symm q h)
        filter_upwards [hstep1, hstep2, hstep3,
          (quasiMeasurePreserving_endBandCoord q).ae (Lp.coeFn_sub
            (eqv.symm (D (Pq h)) - K_st (eqv.symm h)) (E_st (eqv.symm h))),
          (quasiMeasurePreserving_endBandCoord q).ae (Lp.coeFn_sub
            (eqv.symm (D (Pq h))) (K_st (eqv.symm h))),
          ae_restrict_mem isOpen_thricePuncturedSphereReal.measurableSet]
          with z hz1 hz2 hz3 hsub1 hsub2 hzS
        have hD_eq : eqv.symm (D (Pq h)) = eqv.symm (jetOperator
            (volume.restrict S) (ω.floerConformalJetCoeff ρ Jclm Ks Kt u)
            (endTransfer q (endPlaneCutoff R₀ q) (Q q (eqv.symm h)))) := by
          dsimp only [D, Pq, eqvSymmCLM]
          rw [floerConformalSobolevOperator_def]
          rfl
        have hval : (eqv.symm (D (Pq h)) - K_st (eqv.symm h) - E_st (eqv.symm h))
            (endBandCoord q z) =
            endPlaneCutoff R₀ q (positiveEndChart q (endBandCoord q z)) •
              ((eqv.symm h : Lp V 2 StripSobolev.stripMeasure) (endBandCoord q z)) := by
          rw [hsub1, Pi.sub_apply, hsub2, Pi.sub_apply, hD_eq, hz2]
          abel
        rw [hz1, hval, hz3, positiveEndChart_endBandCoord q
          (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hzS) q), smul_smul, smul_smul,
          mul_right_comm _ (endPlaneCutoff R₀ q z) _,
          inv_mul_cancel₀ (positiveEndChartScale_pos q (endBandCoord q z)).ne', one_mul]
      rw [← hdiff] at hae_diff
      filter_upwards [hae_diff, Lp.coeFn_sub (D (Pq h) - Kq h) (Eq h),
        Lp.coeFn_sub (D (Pq h)) (Kq h)] with z hz hs1 hs2
      have hz' : D (Pq h) z - Kq h z - Eq h z = endPlaneCutoff R₀ q z • h z := by
        simpa only [hs1, hs2, Pi.sub_apply] using hz
      calc D (Pq h) z = D (Pq h) z - Kq h z - Eq h z + Kq h z + Eq h z := by abel
        _ = endPlaneCutoff R₀ q z • h z + Kq h z + Eq h z := by rw [hz']
  choose Pq Kq Eq hKq hEq hidq using hEndPiece
  -- Build the interior core piece `P₀` for `β₀ = corePlaneCutoff R₀`.
  set Jop : ℝ × ℝ → V →L[ℝ] V := fun z ↦ Jclm z (u z)
  set Cop : ℝ × ℝ → V →L[ℝ] V :=
    fun z ↦ (√(ρ z))⁻¹ • ω.floerLinearizationCoeff Jclm Ks Kt u z
  have hcoeff : (fun z ↦ firstOrderJetCoeff (Jop z) (Cop z)) =
      ω.floerConformalJetCoeff ρ Jclm Ks Kt u := by
    funext z
    exact (ω.floerConformalJetCoeff_def ρ Jclm Ks Kt u z).symm
  have hM' : MemLp (fun z ↦ firstOrderJetCoeff (Jop z) (Cop z)) ∞ (volume.restrict S) := by
    rw [hcoeff]
    exact hM
  have hJop_cont : ContinuousOn Jop S := fun z hz ↦
    ((hJ z hz).continuousAt.comp₂ continuousAt_id (hu z hz).continuousAt).continuousWithinAt
  have hJop_sq : ∀ z ∈ S, (Jop z).comp (Jop z) = -ContinuousLinearMap.id ℝ V := fun z _ ↦ by
    ext v
    simp [Jop, Jclm, AlmostComplexStructure.apply_apply]
  obtain ⟨P₀, K₀, E₀, hK₀, hE₀, hid₀⟩ :=
    exists_jetOperator_firstOrderJetCoeff_comp_eq_smul_add isWeight_cylindricalWeight
      (J := Jop) (C := Cop) hM' hJop_cont hJop_sq (contDiff_corePlaneCutoff hR₀0)
      (hasCompactSupport_corePlaneCutoff hR₀0) ((tsupport_corePlaneCutoff_subset hR₀0).trans
        (preimage_truncation_subset_thricePuncturedSphereReal (R₀ + 1)))
      (by norm_num : (0 : ℝ) < 1 / 4)
  -- Assemble the spliced parametrix `P = P₀ + ∑ q, P_q`.
  let P : Lp V 2 (volume.restrict S) →L[ℝ] H1 V S ρ := P₀ + ∑ q : Puncture, Pq q
  let K : Lp V 2 (volume.restrict S) →L[ℝ] Lp V 2 (volume.restrict S) :=
    K₀ + ∑ q : Puncture, Kq q
  let E_op : Lp V 2 (volume.restrict S) →L[ℝ] Lp V 2 (volume.restrict S) :=
    E₀ + ∑ q : Puncture, Eq q
  have hK_compact : IsCompactOperator K := by
    refine hK₀.add ?_
    refine Finset.sum_induction Kq (fun T ↦ IsCompactOperator T)
      (fun _ _ ha hb ↦ ha.add hb) isCompactOperator_zero fun q _ ↦ hKq q
  have hE_norm : ‖E_op‖ < 1 := by
    have hsum_le : ‖∑ q : Puncture, Eq q‖ ≤ ∑ q : Puncture, ‖Eq q‖ := norm_sum_le _ _
    have hq_le : ∑ q : Puncture, ‖Eq q‖ ≤ ∑ _ : Puncture, (1 / 6 : ℝ) :=
      Finset.sum_le_sum fun q _ ↦ hEq q
    have hcard : (Finset.univ : Finset Puncture).card = 3 := by decide
    have h3 : ∑ _ : Puncture, (1 / 6 : ℝ) = 1 / 2 := by
      simp [Finset.sum_const, hcard]; norm_num
    calc ‖E_op‖ ≤ ‖E₀‖ + ‖∑ q : Puncture, Eq q‖ := norm_add_le _ _
      _ ≤ 1 / 4 + 1 / 2 := add_le_add hE₀ (hsum_le.trans (hq_le.trans_eq h3))
      _ < 1 := by norm_num
  have hDP : D.comp P - 1 = K + E_op := by
    refine ContinuousLinearMap.ext fun h ↦ Lp.ext ?_
    have hcoe_P : D (P h) = D (P₀ h) + ∑ q : Puncture, D (Pq q h) := by
      simp [P, map_add, map_sum]
    have hcoe_lhs := (Lp.coeFn_sub (D (P h)) h)
    have hcoe_rhs := Lp.coeFn_add (K h) (E_op h)
    have hcoe_K : (K h : ℝ × ℝ → V) =ᵐ[volume.restrict S]
        fun z ↦ K₀ h z + ∑ q : Puncture, Kq q h z := by
      have h1 := Lp.coeFn_add (K₀ h) ((∑ q : Puncture, Kq q) h)
      have h2 : (((∑ q : Puncture, Kq q) h : Lp V 2 (volume.restrict S)) : ℝ × ℝ → V) =ᵐ[
          volume.restrict S] fun z ↦ ∑ q : Puncture, Kq q h z := by
        rw [sum_apply]
        exact (Lp.coeFn_finsetSum Finset.univ fun q ↦ Kq q h).trans (.of_forall fun _ ↦ rfl)
      filter_upwards [h1, h2] with z hz1 hz2
      simp only [K, add_apply, hz1, Pi.add_apply, hz2]
    have hcoe_E : (E_op h : ℝ × ℝ → V) =ᵐ[volume.restrict S]
        fun z ↦ E₀ h z + ∑ q : Puncture, Eq q h z := by
      have h1 := Lp.coeFn_add (E₀ h) ((∑ q : Puncture, Eq q) h)
      have h2 : (((∑ q : Puncture, Eq q) h : Lp V 2 (volume.restrict S)) : ℝ × ℝ → V) =ᵐ[
          volume.restrict S] fun z ↦ ∑ q : Puncture, Eq q h z := by
        rw [sum_apply]
        exact (Lp.coeFn_finsetSum Finset.univ fun q ↦ Eq q h).trans (.of_forall fun _ ↦ rfl)
      filter_upwards [h1, h2] with z hz1 hz2
      simp only [E_op, add_apply, hz1, Pi.add_apply, hz2]
    have hcoe_sumD : (((∑ q : Puncture, D (Pq q h) : Lp V 2 (volume.restrict S)) : ℝ × ℝ → V))
        =ᵐ[volume.restrict S] fun z ↦ ∑ q : Puncture, D (Pq q h) z :=
      (Lp.coeFn_finsetSum Finset.univ fun q ↦ D (Pq q h)).trans (.of_forall fun _ ↦ rfl)
    filter_upwards [hcoe_lhs, hcoe_rhs, hcoe_K, hcoe_E, Lp.coeFn_add (D (P₀ h))
        (∑ q : Puncture, D (Pq q h)), hcoe_sumD, hid₀ h,
      ae_all_iff.2 fun q : Puncture ↦ hidq q h]
      with z hzl hzr hzK hzE hzadd hzsum hz0 hzq
    have hD0_eq : (D (P₀ h) : ℝ × ℝ → V) z =
        corePlaneCutoff R₀ z • h z + K₀ h z + E₀ h z := by
      have hD0 : D (P₀ h) = jetOperator (volume.restrict S)
          (fun z ↦ firstOrderJetCoeff (Jop z) (Cop z)) (P₀ h) := by
        dsimp only [D]
        rw [floerConformalSobolevOperator_def, ContinuousLinearMap.comp_apply,
          Submodule.subtypeL_apply, hcoeff]
      simpa only [hD0] using hz0
    have hsum_q : (∑ q : Puncture, D (Pq q h) z) =
        ∑ q : Puncture, (endPlaneCutoff R₀ q z • h z + Kq q h z + Eq q h z) :=
      Finset.sum_congr rfl fun q _ ↦ hzq q
    rw [sub_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self,
      hzl, Pi.sub_apply, hcoe_P, hzadd, Pi.add_apply, hzsum, hD0_eq, hsum_q]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_smul]
    rw [add_apply, hzr, Pi.add_apply, hzK, hzE]
    have hpart : corePlaneCutoff R₀ z • h z +
        (∑ q : Puncture, endPlaneCutoff R₀ q z) • h z = h z := by
      rw [← add_smul, corePlaneCutoff_add_sum_endPlaneCutoff, one_smul]
    calc corePlaneCutoff R₀ z • h z + K₀ h z + E₀ h z +
          ((∑ q : Puncture, endPlaneCutoff R₀ q z) • h z +
            ∑ q : Puncture, Kq q h z + ∑ q : Puncture, Eq q h z) - h z
        = (corePlaneCutoff R₀ z • h z + (∑ q : Puncture, endPlaneCutoff R₀ q z) • h z) - h z +
            (K₀ h z + ∑ q : Puncture, Kq q h z + (E₀ h z + ∑ q : Puncture, Eq q h z)) := by abel
      _ = K₀ h z + ∑ q : Puncture, Kq q h z + (E₀ h z + ∑ q : Puncture, Eq q h z) := by
          rw [hpart, sub_self, zero_add]
  have hcoker : FiniteDimensional ℝ (Lp V 2 (volume.restrict S) ⧸
      LinearMap.range (D : H1 V S ρ →ₗ[ℝ] Lp V 2 (volume.restrict S))) :=
    cofg_range_of_isCompactOperator_comp_sub_one_add D hDP hK_compact hE_norm
  exact ContinuousLinearMap.IsFredholm.of_finite_ker_coker D hker hcoker

end IsInvertible

section Frame

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The linearized Floer operator on the pair of pants is Fredholm in unitary frames on the
ends.** Let `H_q` be jointly `C³` period-one Hamiltonians on the three ends, with `x_q`
nondegenerate one-periodic orbits of `H'_q`, and let the limit structures `J_q(t, x_q t)` admit
`C²` one-periodic unitary frames `Φ_q : ℝ → F →L[ℝ] V`. Then the conformal Sobolev realization
`D_u : W^{1,2}_0(S, V) → L²(S, V)` is Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_pairOfPants_of_frame (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hxp : ∀ q, Periodic (x q) 1)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    {Φ : Puncture → ℝ → F →L[ℝ] V} (hΦ : ∀ q, ContDiff ℝ 2 (Φ q))
    (hΦp : ∀ q, Periodic (Φ q) 1) (hΦi : ∀ q t, (Φ q t).IsInvertible)
    (hΦω : ∀ q t v w, ω (Φ q t v) (Φ q t w) = (inner ℂ v w).im)
    (hΦJ : ∀ q t v, Je q t (x q t) (Φ q t v) = Φ q t (Complex.I • v))
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm := by
  refine ω.isFredholm_floerConformalSobolevOperator_pairOfPants_of_isInvertible hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hX hx hnd hJe
    (fun q t ↦ ω.compatible_of_isInvertible_of_forall_eq_im_inner (hΦi q t) (hΦω q t) (hΦJ q t))
    hJeq hK hJ hKs hKt hu hc hF hux hδ fun q ↦ ?_
  have hst := ω.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_frame (hX q)
    (contDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
    (hx q) (hxp q) (hΦ q) (hΦp q) (hΦi q) (hΦω q) (hΦJ q) (hnd q)
  rw [floerSobolevOperator_def, floerJetCoeff_eq_stationaryJetCoeff ω (Je q)
    (positiveEndHamiltonian H q) (hx q), ← Floer.stationarySobolevOperator_def] at hst
  exact hst

end Frame

section Compatible

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The linearized Floer operator on the pair of pants is Fredholm.** Let `F` be a
finite-dimensional complex inner product space with symplectic form `ω = Im ⟪·, ·⟫`, let `H_q` be
jointly `C³` period-one Hamiltonians on the three ends, and let `x_q` be one-periodic orbits of
`H'_q` starting at nondegenerate fixed points of the time-one maps. Let `(J, K_s, K_t)` be Floer
data on `S = ℂ ∖ {0, 1}` compatible with `ω` along `u` and equal beyond `R₁` on each end to
cylindrical structures `J_q(t)` (which are `C²` along `x_q`) and the pair-of-pants perturbation.
If `u` is `C¹` on `S`, solves the Floer equation beyond `R₁` on each end, and converges uniformly on
each end to `x_q` with slice defect tending uniformly to zero, then the conformal Sobolev
realization `D_u : W^{1,2}_0(S, F) → L²(S, F)` is Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_pairOfPants (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    {H : Puncture → ℝ → F → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → F}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hxp : ∀ q, Periodic (x q) 1)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, F)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F}
    {Je : Puncture → ℝ → F → AlmostComplexStructure F} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × F ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJx : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJx₂ : ∀ q, ContDiff ℝ 2 fun t ↦ (Je q t (x q t)).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt : ℝ × ℝ → F → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → F}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] F))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  refine ω.isFredholm_floerConformalSobolevOperator_pairOfPants_of_isInvertible hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hX hx hnd hJe hJx hJeq hK hJ hKs hKt hu hc hF hux hδ
    fun q ↦ ?_
  have hJep : Periodic (fun t ↦ Je q t (x q t)) 1 := fun t ↦ by
    have h1 : J (positiveEndChart q (R₁, t)) = Je q (t + 1) := by
      simpa [positiveEndChart_add_one] using hJeq q (R₁, t + 1) le_rfl
    have h2 : J (positiveEndChart q (R₁, t)) = Je q t := hJeq q (R₁, t) le_rfl
    change Je q (t + 1) (x q (t + 1)) = Je q t (x q t)
    rw [← h1, h2, hxp q t]
  have hst := ω.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_compatible
    (hX q) (contDiff_uncurry_positiveEndHamiltonian (hHs q))
    (periodic_positiveEndHamiltonian (hH q)) (hx q) (hxp q)
    (J₀ := AlmostComplexStructure.ofComplexModule F)
    (ω.apply_ofComplexModule_eq_inner hω)
    (Φ := .refl ℝ F) (fun v ↦ by simp [AlmostComplexStructure.ofComplexModule_apply])
    hω (hJx q) (hJx₂ q) hJep (hnd q)
  rw [floerSobolevOperator_def, floerJetCoeff_eq_stationaryJetCoeff ω (Je q)
    (positiveEndHamiltonian H q) (hx q), ← Floer.stationarySobolevOperator_def] at hst
  exact hst

end Compatible

end SymplecticForm

end TauCeti
