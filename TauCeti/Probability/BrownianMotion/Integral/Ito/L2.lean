/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.Integral.Stopping
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.ContinuousStopping

/-!
# The `L²` Brownian Itô integral process

This file develops the `L²` theory of the Brownian Itô integral specification
`TauCeti.IsItoIntegral` for integrands in `TauCeti.BrownianIntegrable`.

First, we identify the finite-horizon `L²` integral `IsFilteredPreBrownianReal.l2Integral` on any
finite-grid `TauCeti.Finance.simpleHolding` with its elementary gain process
`TauCeti.Finance.simpleGains`. From this bridge we prove that every `IsItoIntegral` of a
`BrownianIntegrable` integrand agrees almost surely at each time `T` with `hW.l2Integral T`,
yielding the Itô covariance and isometry formulas, zero expectation, and the martingale property
for any strongly adapted Itô integral.

Second, combining global `L²` approximation by elementary integrands with continuous martingale
completion (`MeasureTheory.exists_continuous_martingale_of_cauchySeq_Lp`), we construct a strongly
predictable, almost surely continuous martingale Itô integral for every `BrownianIntegrable`
integrand against an almost surely continuous filtered pre-Brownian motion.

Finally, we establish the `L²` stopping identity: stopping a strongly adapted Itô integral of a
`BrownianIntegrable` integrand `H` at any stopping time `τ` yields an Itô integral of the stopped
integrand `1_{[0, τ]} H`, proved by elementary dyadic stopping and right-continuous martingale
stopping (`MeasureTheory.Martingale.tendsto_eLpNorm_stoppedProcess_dyadicCeilTime`).

## Main declarations

* `TauCeti.BrownianIntegrable.memLp_timeMeasure` and `memLp_predictableMeasure`: membership in
  the finite-horizon time-product and predictable `L²` spaces.
* `TauCeti.Probability.IsFilteredPreBrownianReal.coeFn_l2Integral_simpleHolding`: identification
  of `hW.l2Integral T` on finite-grid simple holdings with `Finance.simpleGains`.
* `TauCeti.IsItoIntegral.ae_eq_l2Integral`: fixed-time identification of any `IsItoIntegral` with
  `hW.l2Integral`.
* `TauCeti.IsItoIntegral.integral_mul_eq` and `integral_sq_eq`: Itô covariance and Itô isometry.
* `TauCeti.IsItoIntegral.martingale`: every strongly adapted Itô integral of a
  `BrownianIntegrable` integrand is a martingale.
* `TauCeti.BrownianIntegrable.exists_isItoIntegral`: existence of a strongly predictable
  martingale Itô integral for every `BrownianIntegrable` integrand.
* `TauCeti.IsItoIntegral.stoppedProcess_of_brownianIntegrable`: stopping identity for
  `BrownianIntegrable` integrands at arbitrary stopping times on a raw filtration.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H H₁ H₂ I I₁ I₂ : ℝ≥0 → Ω → ℝ}

/-! ### `L²` space bridges for `BrownianIntegrable` -/

/-- A `BrownianIntegrable` integrand belongs to `L²((timeMeasure T).prod P)` on every finite
horizon `T`. -/
theorem BrownianIntegrable.memLp_timeMeasure (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 ((Probability.timeMeasure T).prod P) := by
  simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hH.memLp T

/-- A `BrownianIntegrable` integrand belongs to `L²(ℱ.predictableMeasure P T)` on every finite
horizon `T`. -/
theorem BrownianIntegrable.memLp_predictableMeasure (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 (ℱ.predictableMeasure P T) :=
  (ℱ.memLp_predictableMeasure_iff P hH.isStronglyPredictable T 2).mpr (hH.memLp_timeMeasure T)

end TauCeti

/-! ### Identification of `l2Integral` on elementary holdings -/

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

private def singleIndicator (s t : ℝ≥0) (ξ : Ω → ℝ) : ℝ≥0 × Ω → ℝ :=
  fun p ↦ (Ioc s t).indicator (fun _ ↦ ξ p.2) p.1

private theorem singleIndicator_eq_simpleHolding (s t : ℝ≥0) (ξ : Ω → ℝ) :
    singleIndicator s t ξ =
      Function.uncurry (Finance.simpleHolding (fun i ↦ if i = 0 then s else t) 1 (fun _ ↦ ξ)) := by
  ext ⟨u, ω⟩
  simp [singleIndicator, Finance.simpleHolding_def]

private theorem isStronglyPredictable_singleIndicator {s t : ℝ≥0} {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    StronglyMeasurable[ℱ.predictable] (singleIndicator s t ξ) := by
  rw [singleIndicator_eq_simpleHolding]
  exact Finance.isStronglyPredictable_simpleHolding fun i hi ↦ by
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst hi0
    simpa using hξ

private theorem memLp_singleIndicator_predictableMeasure [SFinite P] {s t : ℝ≥0} {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) (T : ℝ≥0) :
    MemLp (singleIndicator s t ξ) 2 (ℱ.predictableMeasure P T) := by
  rw [singleIndicator_eq_simpleHolding]
  exact Finance.memLp_simpleHolding_predictableMeasure
    (fun i hi ↦ by have hi0 : i = 0 := Nat.lt_one_iff.mp hi; subst hi0; simpa using hξ)
    (fun _ _ ↦ hξ₂) T

private theorem simpleFunc_stronglyMeasurable {s : ℝ≥0} (φ : @SimpleFunc Ω (ℱ s) ℝ) :
    StronglyMeasurable[ℱ s] φ :=
  @SimpleFunc.stronglyMeasurable Ω ℝ (ℱ s) _ φ

private theorem simpleFunc_memLp_two [IsFiniteMeasure P] {s : ℝ≥0} (φ : @SimpleFunc Ω (ℱ s) ℝ) :
    MemLp φ 2 P :=
  (memLp_top_of_bound ((simpleFunc_stronglyMeasurable φ).mono (ℱ.le s)).aestronglyMeasurable
    (∑ c ∈ @SimpleFunc.range Ω ℝ (ℱ s) φ, ‖c‖) (Eventually.of_forall fun ω ↦
      Finset.single_le_sum (f := fun c : ℝ ↦ ‖c‖) (fun _ _ ↦ norm_nonneg _)
        (@SimpleFunc.mem_range_self Ω ℝ (ℱ s) φ ω))).mono_exponent le_top

private theorem eLpNorm_singleIndicator_le [IsFiniteMeasure P] (s t T : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    eLpNorm (singleIndicator s t ξ) 2 (ℱ.predictableMeasure P T) ≤
      (Probability.timeMeasure T (Ioc s t)) ^ (1 / 2 : ℝ) * eLpNorm ξ 2 P := by
  have hpred := isStronglyPredictable_singleIndicator (t := t) hξ
  rw [ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hpred]
  have hm : AEStronglyMeasurable (singleIndicator s t ξ) ((Probability.timeMeasure T).prod P) :=
    (hpred.mono ℱ.predictable_le_prod).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hm,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
      (hξ.mono (ℱ.le s)).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hlint : ∫⁻ p, ‖singleIndicator s t ξ p‖ₑ ^ 2 ∂(Probability.timeMeasure T).prod P =
      Probability.timeMeasure T (Ioc s t) * ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂P := by
    rw [lintegral_prod _ (hm.eNorm.pow_const 2)]
    have hinner (u : ℝ≥0) :
        ∫⁻ ω, ‖singleIndicator s t ξ (u, ω)‖ₑ ^ 2 ∂P =
          (Ioc s t).indicator (fun _ ↦ ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂P) u := by
      by_cases hu : u ∈ Ioc s t <;> simp [singleIndicator, hu]
    simp_rw [hinner]
    rw [lintegral_indicator_const measurableSet_Ioc, mul_comm]
  rw [hlint, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

private theorem coeFn_l2Integral_singleIndicator_simpleFunc [IsFiniteMeasure P]
    (hW : IsFilteredPreBrownianReal ℱ W P) (T s t : ℝ≥0) (φ : @SimpleFunc Ω (ℱ s) ℝ) :
    hW.l2Integral T ((memLp_singleIndicator_predictableMeasure (P := P)
        (simpleFunc_stronglyMeasurable φ) (simpleFunc_memLp_two φ) T).toLp
        (singleIndicator s t φ)) =ᵐ[P]
      fun ω ↦ φ ω * (W (max s (min t T)) ω - W s ω) := by
  refine @SimpleFunc.induction Ω ℝ (ℱ s) _
    (fun φ ↦ hW.l2Integral T ((memLp_singleIndicator_predictableMeasure (P := P)
      (simpleFunc_stronglyMeasurable φ) (simpleFunc_memLp_two φ) T).toLp
      (singleIndicator s t φ)) =ᵐ[P]
      fun ω ↦ φ ω * (W (max s (min t T)) ω - W s ω)) ?_ ?_ φ
  · intro c A hA
    let ψ : @SimpleFunc Ω (ℱ s) ℝ :=
      @SimpleFunc.piecewise Ω ℝ (ℱ s) A hA (@SimpleFunc.const Ω ℝ (ℱ s) c)
        (@SimpleFunc.const Ω ℝ (ℱ s) 0)
    have hmem := memLp_singleIndicator_predictableMeasure (P := P) (t := t)
      (simpleFunc_stronglyMeasurable ψ) (simpleFunc_memLp_two ψ) T
    have htoLp : hmem.toLp (singleIndicator s t ⇑ψ) =
        indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
          (measure_ne_top _ _) c := by
      let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
      apply Lp.ext
      filter_upwards [hmem.coeFn_toLp,
        indicatorConstLp_coeFn (p := 2) (c := c)
          (hs := measurableSet_predictable_Ioc_prod s t hA) (hμs := measure_ne_top _ _)]
        with p hp hind
      rw [hp, hind]
      by_cases hu : p.1 ∈ Ioc s t <;> by_cases hω : p.2 ∈ A <;>
        simp [singleIndicator, ψ, SimpleFunc.piecewise_apply, hu, hω]
    rw [htoLp]
    filter_upwards [hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T s t hA c] with ω hω
    by_cases hωA : ω ∈ A <;> simpa [ψ, SimpleFunc.piecewise_apply, hωA] using hω
  · intro f g _ ihf ihg
    have hmf := memLp_singleIndicator_predictableMeasure (P := P) (t := t)
      (simpleFunc_stronglyMeasurable f) (simpleFunc_memLp_two f) T
    have hmg := memLp_singleIndicator_predictableMeasure (P := P) (t := t)
      (simpleFunc_stronglyMeasurable g) (simpleFunc_memLp_two g) T
    have hsum (hfg : MemLp (singleIndicator s t ⇑(f + g)) 2 (ℱ.predictableMeasure P T)) :
        hfg.toLp (singleIndicator s t ⇑(f + g)) =
        hmf.toLp (singleIndicator s t f) + hmg.toLp (singleIndicator s t g) := by
      let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
      apply Lp.ext
      filter_upwards [hfg.coeFn_toLp,
        Lp.coeFn_add (hmf.toLp (singleIndicator s t f)) (hmg.toLp (singleIndicator s t g)),
        hmf.coeFn_toLp, hmg.coeFn_toLp] with p hp hadd hpf hpg
      rw [hp, hadd, Pi.add_apply, hpf, hpg]
      by_cases hu : p.1 ∈ Ioc s t <;> simp [singleIndicator, hu]
    rw [hsum, map_add]
    filter_upwards [Lp.coeFn_add (hW.l2Integral T (hmf.toLp (singleIndicator s t f)))
      (hW.l2Integral T (hmg.toLp (singleIndicator s t g))), ihf, ihg] with ω hadd hfω hgω
    rw [hadd, Pi.add_apply, hfω, hgω, FunLike.coe_add, Pi.add_apply, add_mul]

private theorem coeFn_l2Integral_singleIndicator [IsFiniteMeasure P]
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s t : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    hW.l2Integral T
        ((memLp_singleIndicator_predictableMeasure hξ hξ₂ T).toLp (singleIndicator s t ξ)) =ᵐ[P]
      fun ω ↦ ξ ω * (W (max s (min t T)) ω - W s ω) := by
  have hξ_trim : MemLp (m0 := ℱ s) ξ 2 (P.trim (ℱ.le s)) := by
    rw [MemLp, eLpNorm_trim (ℱ.le s) hξ]
    exact hξ₂.eLpNorm_lt_top
  have hex (k : ℕ) : ∃ φ : @SimpleFunc Ω (ℱ s) ℝ,
      eLpNorm (ξ - ⇑φ) 2 P < ((k : ℝ≥0∞) + 1)⁻¹ := by
    have hlt : ∃ φ : @SimpleFunc Ω (ℱ s) ℝ,
        eLpNorm (ξ - ⇑φ) 2 (P.trim (ℱ.le s)) < ((k : ℝ≥0∞) + 1)⁻¹ ∧
          MemLp (m0 := ℱ s) (⇑φ) 2 (P.trim (ℱ.le s)) := by
      let : MeasurableSpace Ω := ℱ s
      exact hξ_trim.exists_simpleFunc_eLpNorm_sub_lt (by norm_num)
        (ENNReal.inv_ne_zero.mpr (by simp : ((k : ℝ≥0∞) + 1) ≠ ∞))
    obtain ⟨φ, hφlt, -⟩ := hlt
    refine ⟨φ, ?_⟩
    rwa [eLpNorm_trim (ℱ.le s) (hξ.sub (simpleFunc_stronglyMeasurable φ))] at hφlt
  choose φ hφ using hex
  have hφ_lim : Tendsto (fun k ↦ eLpNorm (ξ - ⇑(φ k)) 2 P) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
      (fun _ ↦ zero_le) (fun k ↦ (hφ k).le)
  let fξ := (memLp_singleIndicator_predictableMeasure (P := P) (t := t) hξ hξ₂ T).toLp
    (singleIndicator s t ξ)
  let fφ (k : ℕ) :=
    (memLp_singleIndicator_predictableMeasure (P := P) (t := t)
      (simpleFunc_stronglyMeasurable (φ k)) (simpleFunc_memLp_two (P := P) (φ k)) T).toLp
      (singleIndicator s t (φ k))
  have hf_lim : Tendsto fφ atTop (𝓝 fξ) := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k ↦ singleIndicator s t (φ k)) _
      (singleIndicator s t ξ)]
    have hbound (k : ℕ) : eLpNorm (singleIndicator s t (φ k) - singleIndicator s t ξ) 2
        (ℱ.predictableMeasure P T) ≤
        (Probability.timeMeasure T (Ioc s t)) ^ (1 / 2 : ℝ) * eLpNorm (ξ - ⇑(φ k)) 2 P := by
      have hsub : singleIndicator s t (φ k) - singleIndicator s t ξ =
          -(singleIndicator s t (ξ - ⇑(φ k))) := by
        ext ⟨u, ω⟩
        by_cases hu : u ∈ Ioc s t <;> simp [singleIndicator, hu]
      rw [hsub, eLpNorm_neg]
      exact eLpNorm_singleIndicator_le s t T (hξ.sub (simpleFunc_stronglyMeasurable (φ k)))
    have hmul : Tendsto (fun k ↦ (Probability.timeMeasure T (Ioc s t)) ^ (1 / 2 : ℝ) *
        eLpNorm (ξ - ⇑(φ k)) 2 P) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hφ_lim
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
      (fun _ ↦ zero_le) hbound
  have hLHS : Tendsto (fun k ↦ hW.l2Integral T (fφ k)) atTop (𝓝 (hW.l2Integral T fξ)) :=
    (hW.l2Integral T).continuous.tendsto fξ |>.comp hf_lim
  let Δ (ω : Ω) : ℝ := W (max s (min t T)) ω - W s ω
  have hmem_rhs : MemLp (fun ω ↦ ξ ω * Δ ω) 2 P :=
    hW.memLp_mul_sub (le_max_left s (min t T)) hξ hξ₂
  have hmem_φ (k : ℕ) : MemLp (fun ω ↦ φ k ω * Δ ω) 2 P :=
    hW.memLp_mul_sub (le_max_left s (min t T)) (simpleFunc_stronglyMeasurable (φ k))
      (simpleFunc_memLp_two (φ k))
  have hRHS_lim : Tendsto (fun k ↦ (hmem_φ k).toLp (fun ω ↦ φ k ω * Δ ω)) atTop
      (𝓝 (hmem_rhs.toLp (fun ω ↦ ξ ω * Δ ω))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq (k : ℕ) : ‖(hmem_φ k).toLp (fun ω ↦ φ k ω * Δ ω) -
        hmem_rhs.toLp (fun ω ↦ ξ ω * Δ ω)‖ ^ 2 =
        (∫ ω, ((ξ - ⇑(φ k)) ω) ^ 2 ∂P) * ((max s (min t T) : ℝ≥0) - (s : ℝ)) := by
      have hmem_d : MemLp (fun ω ↦ (ξ - ⇑(φ k)) ω * Δ ω) 2 P :=
        hW.memLp_mul_sub (le_max_left s (min t T))
          (hξ.sub (simpleFunc_stronglyMeasurable (φ k)))
          (hξ₂.sub (simpleFunc_memLp_two (φ k)))
      have hdiff : (hmem_φ k).toLp (fun ω ↦ φ k ω * Δ ω) -
          hmem_rhs.toLp (fun ω ↦ ξ ω * Δ ω) =
          -(hmem_d.toLp (fun ω ↦ (ξ - ⇑(φ k)) ω * Δ ω)) := by
        apply Lp.ext
        filter_upwards [Lp.coeFn_sub ((hmem_φ k).toLp _) (hmem_rhs.toLp _),
          (hmem_φ k).coeFn_toLp, hmem_rhs.coeFn_toLp,
          Lp.coeFn_neg (hmem_d.toLp _), hmem_d.coeFn_toLp] with ω h1 h2 h3 h4 h5
        rw [h1, Pi.sub_apply, h2, h3, h4, Pi.neg_apply, h5, Pi.sub_apply]
        ring
      rw [hdiff, norm_neg, MemLp.norm_toLp_sq]
      simpa only [Real.norm_eq_abs, sq_abs] using
        hW.integral_sq_mul_sub (le_max_left s (min t T))
          (hξ.sub (simpleFunc_stronglyMeasurable (φ k)))
    have hint_lim : Tendsto (fun k ↦ ∫ ω, ((ξ - ⇑(φ k)) ω) ^ 2 ∂P) atTop (𝓝 0) := by
      have hnorm : Tendsto (fun k ↦ (eLpNorm (ξ - ⇑(φ k)) 2 P).toReal) atTop (𝓝 0) := by
        simpa only [Function.comp_def, ENNReal.toReal_zero] using
          (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hφ_lim
      have heq (k : ℕ) :
          ∫ ω, ((ξ - ⇑(φ k)) ω) ^ 2 ∂P = (eLpNorm (ξ - ⇑(φ k)) 2 P).toReal ^ 2 := by
        have hsq' := (hξ₂.sub (simpleFunc_memLp_two (φ k))).norm_toLp_sq
        rw [Lp.norm_toLp] at hsq'
        simpa only [Real.norm_eq_abs, sq_abs] using hsq'.symm
      simp_rw [heq]
      simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hnorm.pow 2
    have hsq_lim : Tendsto (fun k ↦ ‖(hmem_φ k).toLp (fun ω ↦ φ k ω * Δ ω) -
        hmem_rhs.toLp (fun ω ↦ ξ ω * Δ ω)‖ ^ 2) atTop (𝓝 0) := by
      simp_rw [hsq]
      simpa only [zero_mul] using hint_lim.mul_const _
    simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using
      (Real.continuous_sqrt.tendsto 0).comp hsq_lim
  have heq_k (k : ℕ) : hW.l2Integral T (fφ k) = (hmem_φ k).toLp (fun ω ↦ φ k ω * Δ ω) := by
    apply Lp.ext
    exact (coeFn_l2Integral_singleIndicator_simpleFunc hW T s t (φ k)).trans
      (hmem_φ k).coeFn_toLp.symm
  have heq_lim : hW.l2Integral T fξ = hmem_rhs.toLp (fun ω ↦ ξ ω * Δ ω) :=
    tendsto_nhds_unique hLHS (by simpa only [heq_k] using hRHS_lim)
  rw [heq_lim]
  exact hmem_rhs.coeFn_toLp

/-- On any finite-grid simple holding with square-integrable left-measurable heights, the
finite-horizon `L²` Brownian integral agrees almost surely with the elementary gain process. -/
theorem coeFn_l2Integral_simpleHolding (hW : IsFilteredPreBrownianReal ℱ W P)
    {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (T : ℝ≥0) :
    letI := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
    hW.l2Integral T ((Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
        (Function.uncurry (Finance.simpleHolding τ n a))) =ᵐ[P]
      Finance.simpleGains τ n a W T := by
  let := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let term (i : ℕ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    if hi : i < n then
      (memLp_singleIndicator_predictableMeasure (ha i hi) (ha₂ i hi) T).toLp
        (singleIndicator (τ i) (τ (i + 1)) (a i))
    else 0
  have hsum : (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
      (Function.uncurry (Finance.simpleHolding τ n a)) = ∑ i ∈ range n, term i := by
    apply Lp.ext
    have hcoe := Lp.coeFn_finsetSum (s := range n) term
    have hterms : ∀ i ∈ range n, (term i : ℝ≥0 × Ω → ℝ) =ᵐ[ℱ.predictableMeasure P T]
        singleIndicator (τ i) (τ (i + 1)) (a i) := by
      intro i hi
      simp only [term, mem_range.mp hi, dite_true]
      exact MemLp.coeFn_toLp _
    filter_upwards [(Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).coeFn_toLp,
      hcoe.trans (eventuallyEq_sum hterms)] with p hp hsp
    rcases p with ⟨t, ω⟩
    rw [hp, hsp]
    simp only [Function.uncurry_apply_pair, Finance.simpleHolding_def, singleIndicator,
      Finset.sum_apply]
  rw [hsum, map_sum]
  have hcoe_int := Lp.coeFn_finsetSum (s := range n) (fun i ↦ hW.l2Integral T (term i))
  have hinterm : ∀ i ∈ range n, (hW.l2Integral T (term i) : Ω → ℝ) =ᵐ[P]
      fun ω ↦ a i ω * (W (min (τ (i + 1)) T) ω - W (min (τ i) T) ω) := by
    intro i hi
    have hilt : i < n := mem_range.mp hi
    have hle : τ i ≤ τ (i + 1) :=
      hτ (mem_Iic.mpr hilt.le) (mem_Iic.mpr (Nat.succ_le_of_lt hilt)) (Nat.le_succ i)
    simp only [term, hilt, dite_true]
    filter_upwards [coeFn_l2Integral_singleIndicator hW T (τ i) (τ (i + 1)) (ha i hilt)
      (ha₂ i hilt)] with ω hω
    rw [hω]
    by_cases hTi : τ i ≤ T
    · rw [min_eq_left hTi, max_eq_right (le_min hle hTi)]
    · have hTlt : T ≤ τ i := (lt_of_not_ge hTi).le
      rw [min_eq_right hTlt, min_eq_right (hTlt.trans hle), max_eq_left hTlt, sub_self, sub_self]
  filter_upwards [hcoe_int.trans (eventuallyEq_sum hinterm)] with ω hω
  simpa only [Finance.simpleGains_def, Finset.sum_apply] using hω

end TauCeti.Probability.IsFilteredPreBrownianReal

/-! ### Identification, Itô isometry, martingale property, and existence in `L²` -/

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H H₁ H₂ I I₁ I₂ : ℝ≥0 → Ω → ℝ}

/-- Turn `L²((timeMeasure t).prod P)` convergence of predictable processes into convergence in
probability of pathwise square-energy integrals on `(0, t]`. -/
private theorem tendsto_measure_energy_of_tendsto_eLpNorm [SFinite P]
    {L : ℕ → ℝ≥0 → Ω → ℝ} (hL : ∀ n, IsStronglyPredictable ℱ (L n))
    (hH : IsStronglyPredictable ℱ H) (t : ℝ≥0)
    (hlim : Tendsto (fun n ↦ eLpNorm (fun p ↦ L n p.1 p.2 - H p.1 p.2) 2
      ((Probability.timeMeasure t).prod P)) atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n ↦ P {ω | ε ≤
      ∫⁻ s, ‖L n s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
  intro ε hε
  have hmeas_E (n : ℕ) : Measurable (fun ω ↦
      ∫⁻ s, ‖L n s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) :=
    ((((hL n).sub hH).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2).lintegral_prod_left'
  have hmean : Tendsto (fun n ↦ ∫⁻ ω, ∫⁻ s, ‖L n s ω - H s ω‖ₑ ^ 2
      ∂Probability.timeMeasure t ∂P) atTop (𝓝 0) := by
    have heq (n : ℕ) : (∫⁻ ω, ∫⁻ s, ‖L n s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t ∂P) =
        eLpNorm (fun p ↦ L n p.1 p.2 - H p.1 p.2) 2 ((Probability.timeMeasure t).prod P) ^ 2 := by
      have hm : Measurable (fun p : ℝ≥0 × Ω ↦ ‖L n p.1 p.2 - H p.1 p.2‖ₑ ^ 2) :=
        (((hL n).sub hH).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
      rw [← lintegral_lintegral_swap hm.aemeasurable, ← lintegral_prod _ hm.aemeasurable]
      have haesm : AEStronglyMeasurable (fun p : ℝ≥0 × Ω ↦ L n p.1 p.2 - H p.1 p.2)
          ((Probability.timeMeasure t).prod P) :=
        (((hL n).sub hH).mono ℱ.predictable_le_prod).aestronglyMeasurable
      have hpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) haesm
      simpa only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] using hpow.symm
    simp_rw [heq, sq]
    simpa only [mul_zero] using ENNReal.Tendsto.mul hlim (Or.inr (by simp)) hlim (Or.inr (by simp))
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hmean.eventually (eventually_lt_nhds ENNReal.zero_lt_top)] with n hn
    symm
    have hae := ae_lt_top (hmeas_E n) hn.ne
    exact measure_mono_null (fun ω (hω : ∞ ≤ _) ↦ hω.not_gt) hae
  · have hdiv : Tendsto (fun n ↦ (∫⁻ ω, ∫⁻ s, ‖L n s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t ∂P) / ε) atTop (𝓝 0) := by
      simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hmean (Or.inr hε.ne')
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
      (fun _ ↦ zero_le) fun n ↦ meas_ge_le_lintegral_div (hmeas_E n).aemeasurable hε.ne' hεtop

/-- Package `BrownianIntegrable.exists_seq_simpleHolding_tendsto_eLpNorm` as a sequence of
`ElementaryIntegrand`s. -/
private theorem BrownianIntegrable.exists_seq_elementaryIntegrand [IsFiniteMeasure P]
    (hH : BrownianIntegrable ℱ P H) :
    ∃ K : ℕ → ElementaryIntegrand ℱ, ∀ T : ℝ≥0,
      Tendsto (fun m ↦ eLpNorm (fun p ↦ (K m).toProcess p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) := by
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  refine ⟨fun m ↦ ⟨n m, τ m, (hτ m).monotoneOn, a m, ha m, fun i hi ↦ ⟨C m, hb m i hi⟩⟩,
    fun T ↦ ?_⟩
  simpa only [ElementaryIntegrand.toProcess_def] using hlim T

/-- The `L²` distance between an elementary integral and the `L²` Brownian integral of a
`BrownianIntegrable` integrand equals the time-product `L²` distance of their integrands. -/
private theorem eLpNorm_elementaryIntegral_sub_l2Integral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (K : ElementaryIntegrand ℱ) (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    eLpNorm (K.integral W T -
        (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) : Ω → ℝ)) 2 P =
      eLpNorm (fun p ↦ K.toProcess p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure T).prod P) := by
  have : IsProbabilityMeasure P := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hKint : hW.l2Integral T ((K.brownianIntegrable.memLp_predictableMeasure T).toLp
      (Function.uncurry K.toProcess)) =ᵐ[P] K.integral W T := by
    have h := hW.coeFn_l2Integral_simpleHolding K.mono K.stronglyMeasurable
      (fun _ hi ↦ K.memLp_height hi 2) T
    have htoLp : (K.brownianIntegrable.memLp_predictableMeasure T).toLp
        (Function.uncurry K.toProcess) =
        (Finance.memLp_simpleHolding_predictableMeasure (P := P) K.stronglyMeasurable
          (fun _ hi ↦ K.memLp_height (P := P) hi 2) T).toLp
          (Function.uncurry (Finance.simpleHolding K.grid K.n K.height)) := by
      apply Lp.ext
      filter_upwards [(K.brownianIntegrable.memLp_predictableMeasure T).coeFn_toLp,
        (Finance.memLp_simpleHolding_predictableMeasure (P := P) K.stronglyMeasurable
          (fun _ hi ↦ K.memLp_height (P := P) hi 2) T).coeFn_toLp] with p hp₁ hp₂
      rw [hp₁, hp₂, ElementaryIntegrand.toProcess_def]
    rw [htoLp, ElementaryIntegrand.integral_def]
    exact h
  have hnorm : eLpNorm (K.integral W T -
      (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) : Ω → ℝ)) 2 P =
      edist (hW.l2Integral T ((K.brownianIntegrable.memLp_predictableMeasure T).toLp
        (Function.uncurry K.toProcess)))
        (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))) := by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae (hKint.symm.sub EventuallyEq.rfl)
  rw [hnorm, (hW.l2Integral T).isometry.edist_eq, Lp.edist_def]
  have h1 := eLpNorm_congr_ae (μ := ℱ.predictableMeasure P T) (p := 2)
    (((K.brownianIntegrable.memLp_predictableMeasure T).coeFn_toLp).sub
      ((hH.memLp_predictableMeasure T).coeFn_toLp))
  rw [h1, ℱ.predictableMeasure_def,
    eLpNorm_trim ℱ.predictable_le_prod (K.isStronglyPredictable.sub hH.isStronglyPredictable)]
  exact eLpNorm_congr_ae (Eventually.of_forall fun ⟨_, _⟩ ↦ rfl)

/-- Every Itô integral of a `BrownianIntegrable` integrand agrees almost surely at each time `T`
with the finite-horizon `L²` Brownian integral `hW.l2Integral T`. -/
theorem IsItoIntegral.ae_eq_l2Integral (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    I T =ᵐ[P] hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  have : IsProbabilityMeasure P := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hK⟩ := hH.exists_seq_elementaryIntegrand
  have hEL := tendsto_measure_energy_of_tendsto_eLpNorm (fun m ↦ (K m).isStronglyPredictable)
    hH.isStronglyPredictable T (hK T)
  have hML : TendstoInMeasure P (fun m ↦ (K m).integral W T) atTop
      (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    simp_rw [eLpNorm_elementaryIntegral_sub_l2Integral hW (K _) hH T]
    exact hK T
  exact hI.ae_eq_of_approx hW hEL hML

/-- Every Itô integral of a `BrownianIntegrable` integrand is square integrable at every time. -/
theorem IsItoIntegral.memLp_two (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hI.ae_eq_l2Integral hW hH t).symm

/-- **Itô covariance identity.** For two `BrownianIntegrable` integrands `H₁` and `H₂`, the
expected product of their Itô integrals at time `t` equals the time-product integral of
`H₁ * H₂` on `(0, t]`. -/
theorem IsItoIntegral.integral_mul_eq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH₁ : BrownianIntegrable ℱ P H₁) (hH₂ : BrownianIntegrable ℱ P H₂)
    (hI₁ : IsItoIntegral ℱ P W H₁ I₁) (hI₂ : IsItoIntegral ℱ P W H₂ I₂) (t : ℝ≥0) :
    ∫ ω, I₁ t ω * I₂ t ω ∂P =
      ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂(Probability.timeMeasure t).prod P := by
  let f₁ := (hH₁.memLp_predictableMeasure t).toLp (Function.uncurry H₁)
  let f₂ := (hH₂.memLp_predictableMeasure t).toLp (Function.uncurry H₂)
  have hinner : ⟪hW.l2Integral t f₁, hW.l2Integral t f₂⟫_ℝ = ⟪f₁, f₂⟫_ℝ :=
    (hW.l2Integral t).inner_map_map f₁ f₂
  rw [L2.inner_def, L2.inner_def] at hinner
  have hLHS : ∫ ω, I₁ t ω * I₂ t ω ∂P =
      ∫ ω, ⟪hW.l2Integral t f₁ ω, hW.l2Integral t f₂ ω⟫_ℝ ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hI₁.ae_eq_l2Integral hW hH₁ t, hI₂.ae_eq_l2Integral hW hH₂ t] with ω h₁ h₂
    simp only [h₁, h₂, RCLike.inner_apply, conj_trivial, mul_comm, f₁, f₂]
  have hRHS : ∫ p, ⟪f₁ p, f₂ p⟫_ℝ ∂ℱ.predictableMeasure P t =
      ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂(Probability.timeMeasure t).prod P := by
    have hpred : StronglyMeasurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ H₁ p.1 p.2 * H₂ p.1 p.2) :=
      hH₁.isStronglyPredictable.mul hH₂.isStronglyPredictable
    rw [← ℱ.integral_predictableMeasure P hpred t]
    refine integral_congr_ae ?_
    filter_upwards [(hH₁.memLp_predictableMeasure t).coeFn_toLp,
      (hH₂.memLp_predictableMeasure t).coeFn_toLp] with p hp₁ hp₂
    rcases p with ⟨s, ω⟩
    simp only [RCLike.inner_apply, conj_trivial, f₁, f₂, hp₁, hp₂, Function.uncurry_apply_pair,
      mul_comm]
  rw [hLHS, hinner, hRHS]

/-- **Itô isometry.** The second moment of any Itô integral of a `BrownianIntegrable` integrand
at time `t` equals its expected square energy on `(0, t]`. -/
theorem IsItoIntegral.integral_sq_eq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(Probability.timeMeasure t).prod P := by
  simpa only [sq] using hI.integral_mul_eq hW hH hH hI t

/-- Every Itô integral of a `BrownianIntegrable` integrand has expectation zero at every time. -/
theorem IsItoIntegral.integral_eq_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    ∫ ω, I t ω ∂P = 0 := by
  rw [integral_congr_ae (hI.ae_eq_l2Integral hW hH t)]
  exact hW.integral_l2Integral t _

/-- Every strongly adapted Itô integral of a `BrownianIntegrable` integrand against a filtered
pre-Brownian motion is a martingale. Neither path continuity of `W` nor usual conditions on `ℱ`
are required. -/
theorem IsItoIntegral.martingale (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hadapt : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hK⟩ := hH.exists_seq_elementaryIntegrand
  refine martingale_of_tendsto_eLpNorm_one (fun m ↦ (K m).martingale_integral hW.martingale)
    hadapt fun t ↦ TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm
      (p := 2) (by norm_num) ?_
  have heq (m : ℕ) : eLpNorm ((K m).integral W t - I t) 2 P =
      eLpNorm (fun p ↦ (K m).toProcess p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure t).prod P) := by
    rw [← eLpNorm_elementaryIntegral_sub_l2Integral hW (K m) hH t]
    exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (hI.ae_eq_l2Integral hW hH t))
  simp_rw [heq]
  exact hK t

/-- **Existence of the `L²` Brownian Itô integral.** Every `BrownianIntegrable` integrand against
an almost surely continuous filtered pre-Brownian motion admits a strongly predictable, almost
surely continuous martingale Itô integral on the original raw filtration. -/
theorem BrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hK⟩ := hH.exists_seq_elementaryIntegrand
  have hmart (m : ℕ) : Martingale ((K m).integral W) ℱ P := (K m).martingale_integral hW.martingale
  have hcontK (m : ℕ) : ∀ᵐ ω ∂P, Continuous (fun t ↦ (K m).integral W t ω) :=
    (K m).ae_continuous_integral hcont
  have hmem (m : ℕ) (t : ℝ≥0) : MemLp ((K m).integral W t) 2 P := by
    rw [ElementaryIntegrand.integral_def]
    exact (Lp.memLp _).ae_eq (hW.coeFn_l2Integral_simpleHolding (K m).mono (K m).stronglyMeasurable
      (fun _ hi ↦ (K m).memLp_height hi 2) t)
  have hcau (t : ℝ≥0) : CauchySeq (fun m ↦ (hmem m t).toLp ((K m).integral W t)) := by
    refine Tendsto.cauchySeq
      (x := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))) ?_
    rw [← Lp.toLp_coeFn
      (hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))) (Lp.memLp _),
      Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun m ↦ (K m).integral W t) (fun m ↦ hmem m t)
      (hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))) (Lp.memLp _)]
    simp_rw [eLpNorm_elementaryIntegral_sub_l2Integral hW (K _) hH t]
    exact hK t
  obtain ⟨I, hImart, hIpred, hIlim, -, ⟨_, -, hIpath⟩⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2) hmart hcontK hmem hcau
  refine ⟨I, ⟨hH.isStronglyPredictable, hIpath.mono fun _ h ↦ h.1, fun t ↦ ⟨K, ?_, ?_⟩⟩,
    hIpred, hImart⟩
  · exact tendsto_measure_energy_of_tendsto_eLpNorm (fun m ↦ (K m).isStronglyPredictable)
      hH.isStronglyPredictable t (hK t)
  · exact tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) (hIlim t).2

/-! ### Stopping identity for `BrownianIntegrable` integrands -/

private theorem continuous_stoppedProcess {f : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hf : Continuous fun t ↦ f t ω) :
    Continuous fun t ↦ stoppedProcess f τ t ω := by
  cases h : τ ω with
  | top =>
    have heq : (fun t : ℝ≥0 ↦ stoppedProcess f τ t ω) = fun t ↦ f t ω := by
      ext t
      rw [stoppedProcess_eq_of_le (by rw [h]; exact le_top)]
    rw [heq]
    exact hf
  | coe a =>
    have heq : (fun t : ℝ≥0 ↦ stoppedProcess f τ t ω) = fun t ↦ f (min t a) ω := by
      ext t
      rw [stoppedProcess, h, ← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe]
    rw [heq]
    exact hf.comp (continuous_id.min continuous_const)

private theorem dyadic_step_le_iff {k m : ℕ} {u : WithTop ℝ≥0} {s : ℝ≥0}
    (hs : s ∈ Ioc ((m : ℝ≥0) / 2 ^ k) (((m + 1 : ℕ) : ℝ≥0) / 2 ^ k)) :
    (s : WithTop ℝ≥0) ≤ dyadicCeilTime k u ↔
      (((m : ℝ≥0) / 2 ^ k : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime k u := by
  constructor
  · intro h
    exact (WithTop.coe_lt_coe.mpr hs.1).trans_le h
  · intro h
    cases u with
    | top =>
      rw [dyadicCeilTime_top]
      exact le_top
    | coe x =>
      rw [dyadicCeilTime_coe] at h ⊢
      rw [WithTop.coe_lt_coe, div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ≥0) < 2 ^ k),
        Nat.cast_lt] at h
      rw [WithTop.coe_le_coe]
      refine hs.2.trans (div_le_div_of_nonneg_right ?_ (by positivity))
      exact_mod_cast Nat.succ_le_of_lt h

/-- Elementary dyadic stopping: given an elementary integrand `K`, a stopping time `τ`, a dyadic
mesh `2⁻ᵏ`, and a horizon `T`, there is an elementary integrand `K'` agreeing on `(0, T]` with
`1_{[0, σ]} K` (where `σ = dyadicCeilTime k ∘ τ`) whose elementary integral at `T` equals
`stoppedProcess (K.integral W) σ T` pointwise for every integrator `W`. -/
private theorem exists_elementaryIntegrand_stopped_dyadicCeilTime (K : ElementaryIntegrand ℱ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (k : ℕ) (T : ℝ≥0) :
    ∃ K' : ElementaryIntegrand ℱ,
      (∀ s ∈ Ioc 0 T, ∀ ω, K'.toProcess s ω =
        if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then K.toProcess s ω else 0) ∧
      ∀ (W : ℝ≥0 → Ω → ℝ) (ω : Ω),
        K'.integral W T ω =
          stoppedProcess (K.integral W) (fun ω ↦ dyadicCeilTime k (τ ω)) T ω := by
  classical
  let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (τ ω)
  have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime k
  let d : ℕ → ℝ≥0 := fun m ↦ (m : ℝ≥0) / 2 ^ k
  let N : ℕ := ⌊T * 2 ^ k⌋₊ + 1
  have hTN : T < d N := by
    simp only [d, N]
    rw [lt_div_iff₀ (by positivity)]
    exact_mod_cast Nat.lt_floor_add_one (T * 2 ^ k)
  let S : Finset (ℕ × ℕ) := range K.n ×ˢ range N
  let l : ℕ × ℕ → ℝ≥0 := fun p ↦ max (K.grid p.1) (d p.2)
  let u : ℕ × ℕ → ℝ≥0 := fun p ↦ min (min (K.grid (p.1 + 1)) (d (p.2 + 1))) T
  let b : ℕ × ℕ → Ω → ℝ := fun p ω ↦
    if (d p.2 : WithTop ℝ≥0) < σ ω then K.height p.1 ω else 0
  have hb_meas : ∀ p ∈ S, StronglyMeasurable[ℱ (l p)] (b p) := by
    intro p hp
    have hi : p.1 < K.n := mem_range.mp (mem_product.mp hp).1
    have hset : MeasurableSet[ℱ (l p)] {ω | (d p.2 : WithTop ℝ≥0) < σ ω} := by
      have h1 : MeasurableSet[ℱ (d p.2)] {ω | (d p.2 : WithTop ℝ≥0) < σ ω} := by
        simpa only [compl_ofPred, not_le] using (hσ (d p.2)).compl
      exact ℱ.mono (le_max_right _ _) _ h1
    exact ((K.stronglyMeasurable p.1 hi).mono (ℱ.mono (le_max_left _ _))).ite hset
      stronglyMeasurable_const
  obtain ⟨M, r, c, -, hr, hc_meas, hc_bound, hhold, hgain⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ S l u b hb_meas
  have hbounded : ∀ j < M, ∃ C : ℝ, ∀ ω, ‖c j ω‖ ≤ C := by
    intro j hj
    choose CK hCK using fun i : Fin K.n ↦ K.bounded i.1 i.2
    refine ⟨∑ p ∈ S, if hp : p.1 < K.n then CK ⟨p.1, hp⟩ else 0, fun ω ↦
      (hc_bound j hj ω).trans (sum_le_sum fun p hp ↦ ?_)⟩
    have hi : p.1 < K.n := mem_range.mp (mem_product.mp hp).1
    simp only [hi, dite_true, b]
    split_ifs
    · exact hCK ⟨p.1, hi⟩ ω
    · simp only [norm_zero]
      exact (norm_nonneg _).trans (hCK ⟨p.1, hi⟩ ω)
  let K' : ElementaryIntegrand ℱ := ⟨M, r, hr.monotoneOn, c, hc_meas, hbounded⟩
  refine ⟨K', ?_, ?_⟩
  · intro s hs ω
    rw [ElementaryIntegrand.toProcess_def, hhold s ω, Finset.sum_product]
    rw [ElementaryIntegrand.toProcess_def, Finance.simpleHolding_def]
    have hpart : ∃ m < N, s ∈ Ioc (d m) (d (m + 1)) := by
      let m := ⌈s * 2 ^ k⌉₊ - 1
      have hpos : 0 < ⌈s * 2 ^ k⌉₊ := Nat.ceil_pos.mpr (mul_pos hs.1 (by positivity))
      have hm_lt : m < N := by
        have h1 : ⌈s * 2 ^ k⌉₊ ≤ ⌊T * 2 ^ k⌋₊ + 1 := by
          rw [Nat.ceil_le]
          have h2 : T * 2 ^ k ≤ ((⌊T * 2 ^ k⌋₊ + 1 : ℕ) : ℝ≥0) := by
            push_cast
            exact (Nat.lt_floor_add_one (T * 2 ^ k)).le
          exact (mul_le_mul_of_nonneg_right hs.2 (by positivity)).trans h2
        omega
      refine ⟨m, hm_lt, ?_, ?_⟩
      · simp only [d]
        rw [div_lt_iff₀ (by positivity)]
        have hlt : m < ⌈s * 2 ^ k⌉₊ := by omega
        exact not_le.mp fun hle ↦ hlt.not_ge (Nat.ceil_le.mpr hle)
      · simp only [d]
        rw [le_div_iff₀ (by positivity)]
        have heq : m + 1 = ⌈s * 2 ^ k⌉₊ := by omega
        rw [heq]
        exact Nat.le_ceil (s * 2 ^ k)
    obtain ⟨m₀, hm₀, hsm₀⟩ := hpart
    have hdisj (m : ℕ) (hm : m ≠ m₀) : s ∉ Ioc (d m) (d (m + 1)) := by
      rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne hm with hlt | hgt
      · have hle : d (m + 1) ≤ d m₀ :=
          div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) (by positivity)
        exact hsm₀.1.not_ge (h2.trans hle)
      · have hle : d (m₀ + 1) ≤ d m :=
          div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hgt) (by positivity)
        exact h1.not_ge (hsm₀.2.trans hle)
    have hite_sum : (if (s : WithTop ℝ≥0) ≤ σ ω then
        ∑ j ∈ range K.n, (Ioc (K.grid j) (K.grid (j + 1))).indicator (fun _ ↦ K.height j ω) s
        else 0) =
        ∑ j ∈ range K.n, if (s : WithTop ℝ≥0) ≤ σ ω then
          (Ioc (K.grid j) (K.grid (j + 1))).indicator (fun _ ↦ K.height j ω) s else 0 := by
      split_ifs <;> simp
    rw [hite_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_eq_single_of_mem m₀ (mem_range.mpr hm₀)]
    · have hmem : s ∈ Ioc (l (i, m₀)) (u (i, m₀)) ↔ s ∈ Ioc (K.grid i) (K.grid (i + 1)) := by
        simp only [Set.mem_Ioc, l, u, max_lt_iff, le_min_iff, hs.2, and_true, hsm₀.1, hsm₀.2]
      have hiff : (s : WithTop ℝ≥0) ≤ σ ω ↔ (d m₀ : WithTop ℝ≥0) < σ ω :=
        dyadic_step_le_iff (u := τ ω) hsm₀
      by_cases hsi : s ∈ Ioc (K.grid i) (K.grid (i + 1))
      · simp only [Set.indicator_of_mem (hmem.mpr hsi), Set.indicator_of_mem hsi, b, hiff]
      · simp [hmem, hsi]
    · intro m _ hm
      refine indicator_of_notMem (fun hmem ↦ hdisj m hm ?_) _
      simp only [Set.mem_Ioc, l, u, max_lt_iff, le_min_iff] at hmem
      exact ⟨hmem.1.2, hmem.2.1.2⟩
  · intro W ω
    rw [ElementaryIntegrand.integral_def, hgain W T ω, Finset.sum_product]
    cases htω : min (T : WithTop ℝ≥0) (σ ω) with
    | top =>
      exact absurd htω (ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top T)))
    | coe tω =>
      have htω_coe : (tω : WithTop ℝ≥0) = min (T : WithTop ℝ≥0) (σ ω) := htω.symm
      have htω_le_T : tω ≤ T := WithTop.coe_le_coe.mp (htω_coe ▸ min_le_left _ _)
      have htω_le_N : tω ≤ d N := htω_le_T.trans hTN.le
      have hstop : stoppedProcess (K.integral W) σ T ω = K.integral W tω ω := by
        rw [stoppedProcess, htω, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
      rw [hstop, ElementaryIntegrand.integral_def, Finance.simpleGains_def]
      refine sum_congr rfl fun i hi ↦ ?_
      have hi_lt : i < K.n := mem_range.mp hi
      have hgrid : K.grid i ≤ K.grid (i + 1) :=
        K.mono (mem_Iic.mpr hi_lt.le) (mem_Iic.mpr (Nat.succ_le_of_lt hi_lt)) (Nat.le_succ i)
      let f : ℝ≥0 → ℝ≥0 := fun x ↦ max (min (K.grid i) tω) (min (min (K.grid (i + 1)) x) tω)
      have hterm (m : ℕ) :
          (if l (i, m) ≤ u (i, m) then
            b (i, m) ω * (W (min (u (i, m)) T) ω - W (min (l (i, m)) T) ω) else 0) =
          K.height i ω * (W (f (d (m + 1))) ω - W (f (d m)) ω) := by
        have hd_le : d m ≤ d (m + 1) :=
          div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ m) (by positivity)
        by_cases hdm : (d m : WithTop ℝ≥0) < σ ω
        · have hmin_eq : min (d (m + 1)) tω = min (d (m + 1)) T := by
            rcases le_total (T : WithTop ℝ≥0) (σ ω) with hTσ | hσT
            · have : tω = T := WithTop.coe_injective (htω_coe.trans (min_eq_left hTσ))
              rw [this]
            · have htω_eq : (tω : WithTop ℝ≥0) = σ ω := htω_coe.trans (min_eq_right hσT)
              have hd1_le : d (m + 1) ≤ tω := by
                rw [← WithTop.coe_le_coe, htω_eq]
                exact (dyadic_step_le_iff (k := k) (m := m) (u := τ ω)
                  ⟨div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self m) (by positivity),
                    le_rfl⟩).mpr hdm
              rw [min_eq_left hd1_le, min_eq_left (hd1_le.trans htω_le_T)]
          have hu_eq : u (i, m) = min (min (K.grid (i + 1)) (d (m + 1))) tω := by
            simp only [u, min_assoc, hmin_eq]
          by_cases hlu : l (i, m) ≤ u (i, m)
          · have huT : min (u (i, m)) T = u (i, m) := min_eq_left (min_le_right _ _)
            have hlT : min (l (i, m)) T = l (i, m) :=
              min_eq_left (hlu.trans (min_le_right _ _))
            have ha_le_t : K.grid i ≤ tω :=
              (le_max_left _ _).trans (hlu.trans (hu_eq ▸ min_le_right _ _))
            have hdm_le_t' : d m ≤ tω :=
              (le_max_right _ _).trans (hlu.trans (hu_eq ▸ min_le_right _ _))
            have hdm_le_b : d m ≤ K.grid (i + 1) :=
              (le_max_right _ _).trans (hlu.trans (hu_eq ▸
                (min_le_left _ _).trans (min_le_left _ _)))
            have hfc : f (d m) = l (i, m) := by
              simp only [f, l, min_eq_left ha_le_t, min_eq_right hdm_le_b, min_eq_left hdm_le_t']
            have hfd : f (d (m + 1)) = u (i, m) := by
              simp only [f, ← hu_eq, min_eq_left ha_le_t,
                max_eq_right ((le_max_left _ _).trans hlu)]
            simp only [hlu, ite_true, b, hdm, huT, hlT, hfc, hfd]
          · have hnot : f (d (m + 1)) = f (d m) := by
              have hlt : min (min (K.grid (i + 1)) (d (m + 1))) tω < max (K.grid i) (d m) :=
                hu_eq ▸ lt_of_not_ge hlu
              rcases lt_max_iff.mp hlt with h1 | h2
              · have hle1 : min (min (K.grid (i + 1)) (d (m + 1))) tω ≤ min (K.grid i) tω :=
                  le_min h1.le (min_le_right _ _)
                have hle0 : min (min (K.grid (i + 1)) (d m)) tω ≤ min (K.grid i) tω :=
                  (min_le_min_right tω (min_le_min_left _ hd_le)).trans hle1
                simp only [f, max_eq_left hle1, max_eq_left hle0]
              · have hlt' : min (K.grid (i + 1)) tω < d m := by
                  have : min (min (K.grid (i + 1)) tω) (d (m + 1)) < d m := by
                    simpa only [min_right_comm] using h2
                  rcases min_lt_iff.mp this with h | h
                  · exact h
                  · exact absurd h hd_le.not_gt
                have hmin0 : min (min (K.grid (i + 1)) (d m)) tω = min (K.grid (i + 1)) tω := by
                  rw [min_right_comm, min_eq_left hlt'.le]
                have hmin1 : min (min (K.grid (i + 1)) (d (m + 1))) tω =
                    min (K.grid (i + 1)) tω := by
                  rw [min_right_comm, min_eq_left (hlt'.le.trans hd_le)]
                simp only [f, hmin0, hmin1]
            simp only [hlu, ite_false, hnot, sub_self, mul_zero]
        · have ht_le_dm : tω ≤ d m := by
            have hσ_le : σ ω ≤ d m := not_lt.mp hdm
            exact WithTop.coe_le_coe.mp (htω_coe ▸ (min_le_right _ _).trans hσ_le)
          have hmin0 : min (min (K.grid (i + 1)) (d m)) tω = min (K.grid (i + 1)) tω := by
            rw [min_right_comm, min_eq_left (min_le_right _ _ |>.trans ht_le_dm)]
          have hmin1 : min (min (K.grid (i + 1)) (d (m + 1))) tω = min (K.grid (i + 1)) tω := by
            rw [min_right_comm, min_eq_left (min_le_right _ _ |>.trans (ht_le_dm.trans hd_le))]
          have hfeq : f (d (m + 1)) = f (d m) := by simp only [f, hmin0, hmin1]
          simp only [b, hdm, ite_false, zero_mul, ite_self, hfeq, sub_self, mul_zero]
      simp_rw [hterm]
      rw [← mul_sum, Finset.sum_range_sub (fun m ↦ W (f (d m)) ω) N]
      have hf0 : f (d 0) = min (K.grid i) tω := by simp [f, d]
      have hfN : f (d N) = min (K.grid (i + 1)) tω := by
        have h1 : min (min (K.grid (i + 1)) (d N)) tω = min (K.grid (i + 1)) tω := by
          rw [min_right_comm, min_eq_left (min_le_right _ _ |>.trans htω_le_N)]
        rw [show f (d N) = max (min (K.grid i) tω) (min (min (K.grid (i + 1)) (d N)) tω) from rfl,
          h1, max_eq_right (min_le_min_right tω hgrid)]
      rw [hf0, hfN]

/-- **Stopping identity for `L²` Brownian Itô integrals.** Stopping a strongly adapted Itô
integral of a `BrownianIntegrable` integrand `H` at any stopping time `τ` yields an Itô integral
of `1_{[0, τ]} H`. Neither path continuity of `W` nor usual conditions on `ℱ` are required. -/
theorem IsItoIntegral.stoppedProcess_of_brownianIntegrable
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hadapt : StronglyAdapted ℱ I) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (stoppedProcess I τ) := by
  have : IsProbabilityMeasure P := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  have hImart : Martingale I ℱ P := hI.martingale hW hH hadapt
  have hHτ : BrownianIntegrable ℱ P (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) :=
    hH.ite_le hτ
  -- Step 1: Identify the dyadically stopped integral at each mesh `k` and horizon `T`.
  have hdyadic (T : ℝ≥0) (k : ℕ) :
      stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T =ᵐ[P]
        hW.l2Integral T (((hH.ite_le (hτ.dyadicCeilTime k)).memLp_predictableMeasure T).toLp
          (Function.uncurry fun t ω ↦
            if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then H t ω else 0)) := by
    let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (τ ω)
    have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime k
    obtain ⟨K, hK⟩ := hH.exists_seq_elementaryIntegrand
    choose K' hK'proc hK'int using fun m ↦
      exists_elementaryIntegrand_stopped_dyadicCeilTime (K m) hτ k T
    let Hσ : ℝ≥0 → Ω → ℝ := fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0
    have hHσ : BrownianIntegrable ℱ P Hσ := hH.ite_le hσ
    have hK'_eLp : Tendsto (fun m ↦ eLpNorm (fun p ↦ (K' m).toProcess p.1 p.2 - Hσ p.1 p.2) 2
        ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hK T)
        (fun _ ↦ zero_le) fun m ↦ eLpNorm_mono_ae
          ((((K' m).isStronglyPredictable.sub hHσ.isStronglyPredictable).mono
            ℱ.predictable_le_prod).aestronglyMeasurable) ?_
      have hae : ∀ᵐ p : ℝ≥0 × Ω ∂(Probability.timeMeasure T).prod P, p.1 ∈ Ioc 0 T :=
        (Measure.quasiMeasurePreserving_fst (μ := Probability.timeMeasure T) (ν := P)).ae
          (Probability.ae_mem_Ioc_timeMeasure T)
      filter_upwards [hae] with p hp
      rw [hK'proc m p.1 hp p.2]
      dsimp only [Hσ, σ]
      split_ifs <;> simp
    have hK'_int_to_l2 : Tendsto (fun m ↦ eLpNorm ((K' m).integral W T -
        (hW.l2Integral T ((hHσ.memLp_predictableMeasure T).toLp (Function.uncurry Hσ)) : Ω → ℝ))
        2 P) atTop (𝓝 0) := by
      simp_rw [eLpNorm_elementaryIntegral_sub_l2Integral hW (K' _) hHσ T]
      exact hK'_eLp
    have hK'_int_to_stop : Tendsto (fun m ↦ eLpNorm ((K' m).integral W T -
        stoppedProcess I σ T) 2 P) atTop (𝓝 0) := by
      have hK_I (m : ℕ) : eLpNorm ((K m).integral W T - I T) 2 P =
          eLpNorm (fun p ↦ (K m).toProcess p.1 p.2 - H p.1 p.2) 2
            ((Probability.timeMeasure T).prod P) := by
        rw [← eLpNorm_elementaryIntegral_sub_l2Integral hW (K m) hH T]
        exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (hI.ae_eq_l2Integral hW hH T))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hK T)
        (fun _ ↦ zero_le) fun m ↦ ?_
      rw [← hK_I m]
      have hdiff_mart : Martingale (fun t ω ↦ (K m).integral W t ω - I t ω) ℱ P :=
        ((K m).martingale_integral hW.martingale).sub hImart
      have hρ := (isStoppingTime_const ℱ T).min hσ
      have hcount : (range (fun ω ↦ min (T : WithTop ℝ≥0) (σ ω))).Countable :=
        ((countable_singleton (T : WithTop ℝ≥0)).mono range_const_subset).range_min
          (countable_range_dyadicCeilTime τ k)
      have hcond := hdiff_mart.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
        hρ (fun _ ↦ min_le_left _ _) hcount
      have hsub_eq : ((K' m).integral W T - stoppedProcess I σ T) =
          stoppedValue (fun t ω ↦ (K m).integral W t ω - I t ω)
            (fun ω ↦ min (T : WithTop ℝ≥0) (σ ω)) := by
        ext ω
        simp only [Pi.sub_apply, hK'int m W ω, stoppedProcess_eq_stoppedValue_apply,
          stoppedValue, σ]
      rw [hsub_eq, eLpNorm_congr_ae hcond]
      exact eLpNorm_condExp_le_eLpNorm _ (by norm_num)
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hK'_int_to_stop)
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hK'_int_to_l2)
  -- Step 2: Pass `k → ∞` in `L²(P)` on both sides to identify `stoppedProcess I τ T`.
  have hstop_ae (T : ℝ≥0) : stoppedProcess I τ T =ᵐ[P]
      hW.l2Integral T ((hHτ.memLp_predictableMeasure T).toLp
        (Function.uncurry fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)) := by
    have hLHS : Tendsto (fun k ↦ eLpNorm
        (stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T - stoppedProcess I τ T) 2 P)
        atTop (𝓝 0) :=
      hImart.tendsto_eLpNorm_stoppedProcess_dyadicCeilTime
        (hI.ae_continuous.mono fun _ hω ↦ hω.isRightContinuous) hτ T (by norm_num) (by norm_num)
        (hI.memLp_two hW hH T)
    have hH_lim : Tendsto (fun k ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦
          (if (p.1 : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ p.2) then H p.1 p.2 else 0) -
          (if (p.1 : WithTop ℝ≥0) ≤ τ p.2 then H p.1 p.2 else 0)) 2
        ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) := by
      refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
        (Eventually.of_forall fun k ↦
          ((hH.ite_le (hτ.dyadicCeilTime k)).memLp_timeMeasure T).aestronglyMeasurable)
        (hH.memLp_timeMeasure T)
        (Eventually.of_forall fun k ↦ Eventually.of_forall fun p ↦ ?_)
        (Eventually.of_forall fun p ↦ ?_)
      · dsimp only [Function.uncurry]
        rw [ENNReal.coe_one, one_mul]
        split_ifs with h1 h2 <;> simp
      · by_cases hle : (p.1 : WithTop ℝ≥0) ≤ τ p.2
        · have hall (k : ℕ) : (p.1 : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ p.2) :=
            hle.trans (le_dyadicCeilTime k (τ p.2))
          exact tendsto_const_nhds.congr fun k ↦ by simp only [hle, hall k, ite_true]
        · have hlt : τ p.2 < p.1 := lt_of_not_ge hle
          have hev : ∀ᶠ k in atTop, dyadicCeilTime k (τ p.2) < p.1 :=
            (tendsto_dyadicCeilTime (τ p.2)).eventually (eventually_lt_nhds hlt)
          refine tendsto_const_nhds.congr' (hev.mono fun k hk ↦ ?_)
          simp only [hle, hk.not_ge, ite_false]
    have hRHS : Tendsto (fun k ↦ eLpNorm
        (stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T -
          (hW.l2Integral T ((hHτ.memLp_predictableMeasure T).toLp
            (Function.uncurry fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)) : Ω → ℝ))
        2 P) atTop (𝓝 0) := by
      have heq (k : ℕ) : eLpNorm
          (stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T -
            (hW.l2Integral T ((hHτ.memLp_predictableMeasure T).toLp
              (Function.uncurry fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)) :
              Ω → ℝ)) 2 P =
          eLpNorm (fun p : ℝ≥0 × Ω ↦
            (if (p.1 : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ p.2) then H p.1 p.2 else 0) -
            (if (p.1 : WithTop ℝ≥0) ≤ τ p.2 then H p.1 p.2 else 0)) 2
          ((Probability.timeMeasure T).prod P) := by
        let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
        have hnorm : eLpNorm
            (stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T -
              (hW.l2Integral T ((hHτ.memLp_predictableMeasure T).toLp
                (Function.uncurry fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)) :
                Ω → ℝ)) 2 P =
            edist (hW.l2Integral T
                (((hH.ite_le (hτ.dyadicCeilTime k)).memLp_predictableMeasure T).toLp
                  (Function.uncurry fun t ω ↦
                    if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then H t ω else 0)))
              (hW.l2Integral T ((hHτ.memLp_predictableMeasure T).toLp
                (Function.uncurry fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0))) := by
          rw [Lp.edist_def]
          exact eLpNorm_congr_ae ((hdyadic T k).sub EventuallyEq.rfl)
        rw [hnorm, (hW.l2Integral T).isometry.edist_eq, Lp.edist_def]
        have h1 := eLpNorm_congr_ae (μ := ℱ.predictableMeasure P T) (p := 2)
          ((((hH.ite_le (hτ.dyadicCeilTime k)).memLp_predictableMeasure T).coeFn_toLp).sub
            ((hHτ.memLp_predictableMeasure T).coeFn_toLp))
        rw [h1, ℱ.predictableMeasure_def,
          eLpNorm_trim ℱ.predictable_le_prod
            ((hH.ite_le (hτ.dyadicCeilTime k)).isStronglyPredictable.sub
              hHτ.isStronglyPredictable)]
        exact eLpNorm_congr_ae (Eventually.of_forall fun ⟨_, _⟩ ↦ rfl)
      simp_rw [heq]
      exact hH_lim
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hLHS)
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hRHS)
  -- Step 3: Conclude `IsItoIntegral` for `H^τ` and `stoppedProcess I τ`.
  obtain ⟨K, hK⟩ := hHτ.exists_seq_elementaryIntegrand
  refine ⟨hHτ.isStronglyPredictable, hI.ae_continuous.mono fun _ hω ↦ continuous_stoppedProcess hω,
    fun T ↦ ⟨K, ?_, ?_⟩⟩
  · exact tendsto_measure_energy_of_tendsto_eLpNorm (fun m ↦ (K m).isStronglyPredictable)
      hHτ.isStronglyPredictable T (hK T)
  · refine (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (f := fun m ↦ (K m).integral W T)
      (g := (hW.l2Integral T ((hHτ.memLp_predictableMeasure T).toLp
        (Function.uncurry fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)) : Ω → ℝ))
      ?_).congr_right (hstop_ae T).symm
    simp_rw [eLpNorm_elementaryIntegral_sub_l2Integral hW (K _) hHτ T]
    exact hK T

end TauCeti
