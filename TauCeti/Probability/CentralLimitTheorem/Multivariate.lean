/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.CovarianceBilin
public import TauCeti.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.CramerWold
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Topology.Instances.Matrix
import TauCeti.Probability.CentralLimitTheorem.Lindeberg
import TauCeti.Probability.Independence.InfinitePi

/-!
# Multivariate Lindeberg–Feller and central limit theorems

This file establishes the multivariate Lindeberg–Feller theorem for triangular arrays of row-wise
independent centred random vectors, together with the multivariate central limit theorem for i.i.d.
sequences and finite product samples (`Measure.pi`).

Both theorems are proved first in basis-free form on any finite-dimensional real inner product
space `E`, and then specialized to `EuclideanSpace ℝ κ` with `TauCeti.covMatrix` and Mathlib's
`ProbabilityTheory.multivariateGaussian`. Singular limiting covariance matrices are allowed
throughout; in the Euclidean Lindeberg–Feller theorem, positive semidefiniteness of the limiting
covariance matrix `S` is deduced from convergence of the row covariance sums.

## Main results

* `TauCeti.tendstoInDistribution_sum_of_lindeberg_of_hasGaussianLaw`: basis-free multivariate
  Lindeberg–Feller theorem on a finite-dimensional real inner product space.
* `TauCeti.tendstoInDistribution_sum_of_lindeberg`: multivariate Lindeberg–Feller theorem in
  `EuclideanSpace ℝ κ` with limiting law `multivariateGaussian 0 S`.
* `TauCeti.tendstoInDistribution_inv_sqrt_smul_sum_sub`: basis-free multivariate central limit
  theorem for an i.i.d. sequence with finite second moment.
* `TauCeti.tendstoInDistribution_inv_sqrt_smul_sum_sub_euclidean`: multivariate central limit
  theorem in `EuclideanSpace ℝ κ` with limiting law
  `multivariateGaussian 0 (covMatrix (μ.map (X 0)))`.
* `TauCeti.tendstoInDistribution_inv_sqrt_smul_sum_sub_pi` and
  `TauCeti.tendstoInDistribution_inv_sqrt_smul_sum_sub_pi_euclidean`: i.i.d. sample forms on
  `Fin n → α` under `Measure.pi (fun _ : Fin n ↦ P)`.

## Implementation notes

The multivariate Lindeberg–Feller theorem reduces to the scalar Lindeberg–Feller theorem in
`TauCeti.Probability.CentralLimitTheorem.Lindeberg` by applying Lévy's continuity theorem
(`MeasureTheory.TendstoInDistribution.of_tendsto_charFun`) to each scalar projection `⟪·, t⟫`.
The multivariate i.i.d. central limit theorem applies Mathlib's Cramér–Wold device
(`MeasureTheory.TendstoInDistribution.of_inner`) directly to Mathlib's scalar central limit
theorem (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`). The `Measure.pi`
sample form is deduced from the sequence form by identifying `Measure.pi (fun _ : Fin n ↦ P)` with
the prefix marginal of `Measure.infinitePi (fun _ : ℕ ↦ P)`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998,
  Proposition 2.17 (p. 16) and Proposition 2.27 (p. 20).
* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Section 29.

## Tags

central limit theorem, multivariate central limit theorem, Lindeberg–Feller, Cramér–Wold
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Real RealInnerProductSpace Topology Matrix

namespace TauCeti

private lemma hasLaw_inner_of_hasGaussianLaw {E Ω' : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω'] {μ' : Measure Ω'} {Z : Ω' → E}
    (hZ : HasGaussianLaw Z μ') (hZ0 : ∫ ω', Z ω' ∂μ' = 0) (t : E) :
    HasLaw (fun ω' ↦ ⟪Z ω', t⟫) (gaussianReal 0 Var[fun ω' ↦ ⟪Z ω', t⟫; μ'].toNNReal) μ' := by
  have hG := hZ.map_fun (innerSL ℝ t)
  have h0 : ∫ ω', ⟪t, Z ω'⟫ ∂μ' = 0 := by
    rw [integral_inner hZ.integrable, hZ0, inner_zero_right]
  refine ⟨(continuous_id.inner continuous_const).measurable.comp_aemeasurable hZ.aemeasurable, ?_⟩
  have hmap := hG.map_eq_gaussianReal
  simp only [innerSL_apply_apply, h0] at hmap
  simpa only [real_inner_comm t] using hmap

/-! ### Multivariate Lindeberg–Feller theorem -/

section Lindeberg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : (n : ℕ) → Measure (Ω n)}
  {ι : ℕ → Type*} [∀ n, Fintype (ι n)] {Y : (n : ℕ) → ι n → Ω n → E}

/-- A vector Lindeberg condition implies the scalar Lindeberg condition for every linear
projection `⟪·, t⟫`. -/
private lemma tendsto_sum_indicator_inner_sq_of_lindeberg
    (hL2 : ∀ n i, MemLp (Y n i) 2 (μ n))
    (hlind : ∀ ε > 0, Tendsto
      (fun n ↦ ∑ i, ∫ ω in {ω | ε < ‖Y n i ω‖}, ‖Y n i ω‖ ^ 2 ∂(μ n)) atTop (𝓝 0))
    (t : E) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ ∑ i, (μ n)[{ω | ε ≤ |⟪Y n i ω, t⟫|}.indicator fun ω ↦ ⟪Y n i ω, t⟫ ^ 2])
      atTop (𝓝 0) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [not_le.mpr hε]
  have : 0 < ‖t‖ := norm_pos_iff.mpr ht
  set ε' : ℝ := ε / (2 * ‖t‖)
  have hε' : 0 < ε' := by positivity
  refine squeeze_zero (fun n ↦ Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦
      Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) ω) (fun n ↦ ?_)
    (by simpa only [mul_zero] using (hlind ε' hε').const_mul (‖t‖ ^ 2))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hs : NullMeasurableSet {ω | ε' < ‖Y n i ω‖} (μ n) :=
    (hL2 n i).aestronglyMeasurable.norm.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi
  have hnorm2 : Integrable (fun ω ↦ ‖Y n i ω‖ ^ 2) (μ n) :=
    (memLp_two_iff_integrable_sq_norm (hL2 n i).aestronglyMeasurable).1 (hL2 n i)
  have hrhs : Integrable
      (fun ω ↦ ‖t‖ ^ 2 * ({ω | ε' < ‖Y n i ω‖}.indicator fun ω ↦ ‖Y n i ω‖ ^ 2) ω) (μ n) :=
    (hnorm2.indicator₀ hs).const_mul (‖t‖ ^ 2)
  have hle (ω : Ω n) : ({ω | ε ≤ |⟪Y n i ω, t⟫|}.indicator fun ω ↦ ⟪Y n i ω, t⟫ ^ 2) ω ≤
      ‖t‖ ^ 2 * ({ω | ε' < ‖Y n i ω‖}.indicator fun ω ↦ ‖Y n i ω‖ ^ 2) ω := by
    by_cases hω : ε ≤ |⟪Y n i ω, t⟫|
    · have hcs : |⟪Y n i ω, t⟫| ≤ ‖Y n i ω‖ * ‖t‖ := abs_real_inner_le_norm (Y n i ω) t
      have hmem : ε' < ‖Y n i ω‖ := by rw [div_lt_iff₀ (by positivity)]; linarith
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hmem]
      calc ⟪Y n i ω, t⟫ ^ 2 = |⟪Y n i ω, t⟫| ^ 2 := (sq_abs _).symm
        _ ≤ (‖Y n i ω‖ * ‖t‖) ^ 2 := by gcongr
        _ = ‖t‖ ^ 2 * ‖Y n i ω‖ ^ 2 := by ring
    · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) ω)
  have hlhs : Integrable
      (fun ω ↦ ({ω | ε ≤ |⟪Y n i ω, t⟫|}.indicator fun ω ↦ ⟪Y n i ω, t⟫ ^ 2) ω) (μ n) := by
    have hsm : AEStronglyMeasurable (fun ω ↦ ⟪Y n i ω, t⟫) (μ n) :=
      ((innerSL ℝ t).continuous.comp_aestronglyMeasurable (hL2 n i).aestronglyMeasurable).congr
        (.of_forall fun ω ↦ real_inner_comm (Y n i ω) t)
    have hs1 : NullMeasurableSet {ω | ε ≤ |⟪Y n i ω, t⟫|} (μ n) :=
      hsm.norm.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici
    refine hrhs.mono' ((hsm.pow 2).indicator₀ hs1) (.of_forall fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) ω)]
    exact hle ω
  rw [← integral_indicator₀ hs, ← integral_const_mul]
  exact integral_mono hlhs hrhs hle

/-- **Multivariate Lindeberg–Feller central limit theorem** on a finite-dimensional real inner
product space. Let `Y n i`, `i : ι n`, be a triangular array of row-wise independent centred
square-integrable random vectors on probability spaces `(Ω n, μ n)`, and let `Z` be a centred
Gaussian random vector on `(Ω', μ')`. If for every `t : E` the row variances
`∑ i, Var[⟪Y n i, t⟫; μ n]` converge to `Var[⟪Z, t⟫; μ']`, and the vector Lindeberg condition
`∑ i, ∫ ω in {ω | ε < ‖Y n i ω‖}, ‖Y n i ω‖ ^ 2 ∂(μ n) → 0` holds for every `ε > 0`, then
`∑ i, Y n i` converges in distribution to `Z`. -/
theorem tendstoInDistribution_sum_of_lindeberg_of_hasGaussianLaw
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [∀ n, IsProbabilityMeasure (μ n)]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → E}
    (hindep : ∀ n, iIndepFun (Y n) (μ n))
    (hL2 : ∀ n i, MemLp (Y n i) 2 (μ n))
    (hmean : ∀ n i, ∫ ω, Y n i ω ∂(μ n) = 0)
    (hvar : ∀ t : E, Tendsto (fun n ↦ ∑ i, Var[fun ω ↦ ⟪Y n i ω, t⟫; μ n]) atTop
      (𝓝 Var[fun ω' ↦ ⟪Z ω', t⟫; μ']))
    (hlind : ∀ ε > 0, Tendsto
      (fun n ↦ ∑ i, ∫ ω in {ω | ε < ‖Y n i ω‖}, ‖Y n i ω‖ ^ 2 ∂(μ n)) atTop (𝓝 0))
    (hZ : HasGaussianLaw Z μ') (hZ0 : ∫ ω', Z ω' ∂μ' = 0) :
    TendstoInDistribution (fun n ω ↦ ∑ i, Y n i ω) atTop Z μ μ' := by
  have hmS (n : ℕ) : AEMeasurable (fun ω ↦ ∑ i, Y n i ω) (μ n) :=
    Finset.aemeasurable_fun_sum _ fun i _ ↦ (hL2 n i).aestronglyMeasurable.aemeasurable
  refine TendstoInDistribution.of_tendsto_charFun hmS hZ.aemeasurable fun t ↦ ?_
  have hXindep (n : ℕ) : iIndepFun (fun i ω ↦ ⟪Y n i ω, t⟫) (μ n) :=
    (hindep n).comp (fun _ x ↦ ⟪x, t⟫) fun _ ↦ (continuous_id.inner continuous_const).measurable
  have hXL2 (n : ℕ) (i : ι n) : MemLp (fun ω ↦ ⟪Y n i ω, t⟫) 2 (μ n) :=
    ((innerSL ℝ t).comp_memLp' (hL2 n i)).ae_eq (.of_forall fun ω ↦ real_inner_comm (Y n i ω) t)
  have hX0 (n : ℕ) (i : ι n) : (μ n)[fun ω ↦ ⟪Y n i ω, t⟫] = 0 := by
    simp_rw [real_inner_comm t]
    rw [integral_inner ((hL2 n i).integrable one_le_two), hmean n i, inner_zero_right]
  have hscal := (hasLaw_inner_of_hasGaussianLaw hZ hZ0 t).tendstoInDistribution_sum_of_lindeberg
    hXindep hXL2 hX0 (by simpa only [Real.coe_toNNReal _ (variance_nonneg _ _)] using hvar t)
    fun ε hε ↦ tendsto_sum_indicator_inner_sq_of_lindeberg hL2 hlind t hε
  rw [charFun_map_eq_charFun_map_inner_one hZ.aemeasurable]
  refine (hscal.tendsto_charFun 1).congr fun n ↦ ?_
  rw [charFun_map_eq_charFun_map_inner_one (hmS n)]
  simp_rw [sum_inner]

end Lindeberg

/-- **Multivariate Lindeberg–Feller central limit theorem** in `EuclideanSpace ℝ κ`. Let
`Y n i`, `i : ι n`, be a triangular array of row-wise independent centred square-integrable random
vectors on `(Ω n, μ n)`. If the summed covariance matrices `∑ i, covMatrix ((μ n).map (Y n i))`
converge to `S` and the Lindeberg condition
`∑ i, ∫ ω in {ω | ε < ‖Y n i ω‖}, ‖Y n i ω‖ ^ 2 ∂(μ n) → 0` holds for every `ε > 0`, then
`∑ i, Y n i` converges in distribution to a centred multivariate Gaussian random vector with
covariance matrix `S`. Singular limiting covariance matrices are allowed, and positive
semidefiniteness of `S` is deduced from convergence of the row covariance sums. -/
theorem tendstoInDistribution_sum_of_lindeberg
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : (n : ℕ) → Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)] {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {Y : (n : ℕ) → ι n → Ω n → EuclideanSpace ℝ κ}
    (hindep : ∀ n, iIndepFun (Y n) (μ n))
    (hL2 : ∀ n i, MemLp (Y n i) 2 (μ n))
    (hmean : ∀ n i, ∫ ω, Y n i ω ∂(μ n) = 0)
    {S : Matrix κ κ ℝ}
    (hcov : Tendsto (fun n ↦ ∑ i, covMatrix ((μ n).map (Y n i))) atTop (𝓝 S))
    (hlind : ∀ ε > 0, Tendsto
      (fun n ↦ ∑ i, ∫ ω in {ω | ε < ‖Y n i ω‖}, ‖Y n i ω‖ ^ 2 ∂(μ n)) atTop (𝓝 0))
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → EuclideanSpace ℝ κ} (hZ : HasLaw Z (multivariateGaussian 0 S) μ') :
    TendstoInDistribution (fun n ω ↦ ∑ i, Y n i ω) atTop Z μ μ' := by
  have hmap (n : ℕ) (i : ι n) : MemLp id 2 ((μ n).map (Y n i)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (hL2 n i).aestronglyMeasurable.aemeasurable).2
      (hL2 n i)
  have hS : S.PosSemidef := isClosed_setOfPred_posSemidef.mem_of_tendsto hcov <|
    .of_forall fun n ↦ (Matrix.PosSemidef.addSubmonoid κ ℝ).sum_mem fun i _ ↦
      posSemidef_covMatrix _ (hmap n i)
  refine tendstoInDistribution_sum_of_lindeberg_of_hasGaussianLaw hindep hL2 hmean (fun t ↦ ?_)
    hlind hZ.hasGaussianLaw (by rw [hZ.integral_eq, integral_id_multivariateGaussian])
  have hvar_Y (n : ℕ) (i : ι n) :
      Var[fun ω ↦ ⟪Y n i ω, t⟫; μ n] = t.ofLp ⬝ᵥ covMatrix ((μ n).map (Y n i)) *ᵥ t.ofLp := by
    have hv := covarianceBilin_self (hmap n i) t
    rw [variance_map (by fun_prop) (hL2 n i).aestronglyMeasurable.aemeasurable] at hv
    simp_rw [Function.comp_def, real_inner_comm _ t] at hv
    rw [← hv, covarianceBilin_eq_covMatrix _ (hmap n i)]
    simp [PiLp.inner_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm]
  have hvar_Z : Var[fun ω' ↦ ⟪Z ω', t⟫; μ'] = t.ofLp ⬝ᵥ S *ᵥ t.ofLp := by
    have hv := covarianceBilin_self (μ := multivariateGaussian 0 S) IsGaussian.memLp_two_id t
    rw [← hZ.map_eq, variance_map (by fun_prop) hZ.aemeasurable] at hv
    simp_rw [Function.comp_def, real_inner_comm _ t] at hv
    rw [← hv, hZ.map_eq, covarianceBilin_multivariateGaussian hS]
  have hcont : Continuous fun A : Matrix κ κ ℝ ↦ t.ofLp ⬝ᵥ A *ᵥ t.ofLp := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  rw [hvar_Z]
  refine ((hcont.tendsto S).comp hcov).congr fun n ↦ ?_
  simp only [Function.comp_def, hvar_Y, Matrix.sum_mulVec, dotProduct_sum]

/-! ### Multivariate central limit theorem for i.i.d. sequences -/

/-- **Multivariate central limit theorem** on a finite-dimensional real inner product space. Let
`X : ℕ → Ω → E` be an i.i.d. sequence of square-integrable random vectors and let `Z` be a centred
Gaussian random vector with the same covariance bilinear form as `X 0`. Then
`(√n)⁻¹ • ∑ i ∈ Finset.range n, (X i - E[X 0])` converges in distribution to `Z`. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hL2 : MemLp (X 0) 2 μ)
    (hZ : HasGaussianLaw Z μ') (hZ0 : ∫ ω', Z ω' ∂μ' = 0)
    (hZcov : covarianceBilin (μ'.map Z) = covarianceBilin (μ.map (X 0))) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, (X i ω - ∫ ω', X 0 ω' ∂μ))
      atTop Z (fun _ ↦ μ) μ' := by
  have hmX (n : ℕ) : AEMeasurable
      (fun ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, (X i ω - ∫ ω', X 0 ω' ∂μ)) μ :=
    (Finset.aemeasurable_fun_sum _ fun i _ ↦ (hident i).aemeasurable_fst.sub_const _).const_smul _
  refine TendstoInDistribution.of_inner hZ.aemeasurable hmX fun t ↦ ?_
  have hmap0 : MemLp id 2 (μ.map (X 0)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hL2.aestronglyMeasurable.aemeasurable).2 hL2
  have hmapZ : MemLp id 2 (μ'.map Z) := hZ.isGaussian_map.memLp_two_id
  have hvar_eq : Var[fun ω' ↦ ⟪Z ω', t⟫; μ'] = Var[fun ω ↦ ⟪X 0 ω, t⟫; μ] := by
    have hvZ := covarianceBilin_self hmapZ t
    have hv0 := covarianceBilin_self hmap0 t
    have hm_inner : Measurable fun u : E ↦ ⟪t, u⟫ :=
      (continuous_const.inner continuous_id).measurable
    rw [variance_map hm_inner.aemeasurable hZ.aemeasurable] at hvZ
    rw [variance_map hm_inner.aemeasurable hL2.aestronglyMeasurable.aemeasurable] at hv0
    simp_rw [Function.comp_def, real_inner_comm _ t] at hvZ hv0
    rw [← hvZ, ← hv0, hZcov]
  have hZt : HasLaw (fun ω' ↦ ⟪Z ω', t⟫)
      (gaussianReal 0 Var[fun ω ↦ ⟪X 0 ω, t⟫; μ].toNNReal) μ' :=
    hvar_eq ▸ hasLaw_inner_of_hasGaussianLaw hZ hZ0 t
  have hXL2 : MemLp (fun ω ↦ ⟪X 0 ω, t⟫) 2 μ :=
    ((innerSL ℝ t).comp_memLp' hL2).ae_eq (.of_forall fun ω ↦ real_inner_comm (X 0 ω) t)
  have hscal := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun i ω ↦ ⟪X i ω, t⟫) hZt hXL2
    (hindep.comp (fun _ x ↦ ⟪x, t⟫) fun _ ↦ (continuous_id.inner continuous_const).measurable)
    fun i ↦ (hident i).comp (continuous_id.inner continuous_const).measurable
  refine hscal.congr (fun n ↦ .of_forall fun ω ↦ ?_) (.of_forall fun _ ↦ rfl)
  dsimp only
  rw [inner_smul_left, RCLike.conj_to_real, sum_inner]
  simp only [inner_sub_left, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have hmean_t : ⟪∫ ω', X 0 ω' ∂μ, t⟫ = ∫ ω', ⟪X 0 ω', t⟫ ∂μ := by
    rw [real_inner_comm t, ← integral_inner (hL2.integrable one_le_two)]
    exact integral_congr_ae (.of_forall fun ω' ↦ real_inner_comm (X 0 ω') t)
  rw [hmean_t]

/-- **Multivariate central limit theorem** in `EuclideanSpace ℝ κ`. For an i.i.d. sequence
`X : ℕ → Ω → EuclideanSpace ℝ κ` with finite second moment,
`(√n)⁻¹ • ∑ i ∈ Finset.range n, (X i - E[X 0])` converges in distribution to the centred
multivariate Gaussian law with covariance matrix `covMatrix (μ.map (X 0))`. The covariance matrix
need not be invertible. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum_sub_euclidean
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X : ℕ → Ω → EuclideanSpace ℝ κ} {Z : Ω' → EuclideanSpace ℝ κ}
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hL2 : MemLp (X 0) 2 μ)
    (hZ : HasLaw Z (multivariateGaussian 0 (covMatrix (μ.map (X 0)))) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, (X i ω - ∫ ω', X 0 ω' ∂μ))
      atTop Z (fun _ ↦ μ) μ' := by
  have hmap : MemLp id 2 (μ.map (X 0)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hL2.aestronglyMeasurable.aemeasurable).2 hL2
  refine tendstoInDistribution_inv_sqrt_smul_sum_sub hindep hident hL2 hZ.hasGaussianLaw
    (by rw [hZ.integral_eq, integral_id_multivariateGaussian]) ?_
  ext x y
  rw [hZ.map_eq, covarianceBilin_multivariateGaussian (posSemidef_covMatrix _ hmap),
    covarianceBilin_eq_covMatrix _ hmap]
  simp [PiLp.inner_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm]

/-! ### Multivariate central limit theorem for product samples -/

/-- **Multivariate central limit theorem for i.i.d. samples** on `Fin n → α` under the product law
`Measure.pi (fun _ : Fin n ↦ P)`. For any square-integrable `s : α → E` into a finite-dimensional
real inner product space `E` and any centred Gaussian `Z` with the same covariance bilinear form as
`P.map s`, `(√n)⁻¹ • ∑ i : Fin n, (s (x i) - E[s])` converges in distribution to `Z`. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum_sub_pi
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {α Ω' : Type*} [MeasurableSpace α] [MeasurableSpace Ω']
    {P : Measure α} [IsProbabilityMeasure P] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {s : α → E} {Z : Ω' → E}
    (hs : MemLp s 2 P)
    (hZ : HasGaussianLaw Z μ') (hZ0 : ∫ ω', Z ω' ∂μ' = 0)
    (hZcov : covarianceBilin (μ'.map Z) = covarianceBilin (P.map s)) :
    TendstoInDistribution
      (fun (n : ℕ) (x : Fin n → α) ↦ (Real.sqrt n)⁻¹ • ∑ i : Fin n, (s (x i) - ∫ y, s y ∂P))
      atTop Z (fun n ↦ Measure.pi fun _ : Fin n ↦ P) μ' := by
  set Q : Measure (ℕ → α) := Measure.infinitePi fun _ : ℕ ↦ P
  set X : ℕ → (ℕ → α) → E := fun i ω ↦ s (ω i)
  have hsm : AEMeasurable s P := hs.aestronglyMeasurable.aemeasurable
  have hindep : iIndepFun X Q :=
    (TauCeti.Probability.iIndepFun_eval_infinitePi (fun _ : ℕ ↦ P)).comp₀ (fun _ ↦ s)
      (fun i ↦ (measurable_pi_apply i).aemeasurable)
      (fun i ↦ by rwa [Measure.infinitePi_map_eval])
  have hmp (i : ℕ) : MeasurePreserving (fun ω : ℕ → α ↦ ω i) Q P :=
    measurePreserving_eval_infinitePi (fun _ : ℕ ↦ P) i
  have hmap_i (i : ℕ) : Q.map (X i) = P.map s := by
    rw [← (hmp i).map_eq, AEMeasurable.map_map_of_aemeasurable
      (by rw [(hmp i).map_eq]; exact hsm) (hmp i).measurable.aemeasurable]
    rfl
  have hident (i : ℕ) : IdentDistrib (X i) (X 0) Q Q :=
    ⟨hsm.comp_quasiMeasurePreserving (hmp i).quasiMeasurePreserving,
      hsm.comp_quasiMeasurePreserving (hmp 0).quasiMeasurePreserving, by rw [hmap_i i, hmap_i 0]⟩
  have hL2 : MemLp (X 0) 2 Q := hs.comp_measurePreserving (hmp 0)
  have hmean0 : ∫ ω, X 0 ω ∂Q = ∫ y, s y ∂P := by
    rw [← (hmp 0).map_eq, integral_map (hmp 0).measurable.aemeasurable
      (by rw [(hmp 0).map_eq]; exact hs.aestronglyMeasurable)]
  have hseq := tendstoInDistribution_inv_sqrt_smul_sum_sub hindep hident hL2 hZ hZ0
    (by rw [hmap_i 0]; exact hZcov)
  have hm_pi (n : ℕ) : AEMeasurable
      (fun x : Fin n → α ↦ (Real.sqrt n)⁻¹ • ∑ i : Fin n, (s (x i) - ∫ y, s y ∂P))
      (Measure.pi fun _ : Fin n ↦ P) :=
    (Finset.aemeasurable_fun_sum _ fun i _ ↦
      (hsm.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ P) i)).sub_const _).const_smul _
  refine ⟨hm_pi, hZ.aemeasurable, ?_⟩
  refine hseq.tendsto.congr fun n ↦ Subtype.ext ?_
  dsimp only
  have hr_meas : Measurable (fun (ω : ℕ → α) (i : Fin n) ↦ ω i.1) :=
    measurable_pi_iff.2 fun i ↦ measurable_pi_apply i.1
  have hr_map : Q.map (fun (ω : ℕ → α) (i : Fin n) ↦ ω i.1) = Measure.pi fun _ : Fin n ↦ P := by
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  rw [← hr_map, AEMeasurable.map_map_of_aemeasurable
    (by rw [hr_map]; exact hm_pi n) hr_meas.aemeasurable]
  congr 1
  ext ω
  simp only [Function.comp_def, hmean0, X]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ s (ω k) - ∫ y, s y ∂P)]

/-- **Multivariate central limit theorem for i.i.d. samples** into `EuclideanSpace ℝ κ`. For any
square-integrable `s : α → EuclideanSpace ℝ κ` under a probability measure `P`, the standardized
sample sum `(√n)⁻¹ • ∑ i : Fin n, (s (x i) - E[s])` under `Measure.pi (fun _ : Fin n ↦ P)`
converges in distribution to the centred multivariate Gaussian law with covariance matrix
`covMatrix (P.map s)`. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum_sub_pi_euclidean
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {α Ω' : Type*} [MeasurableSpace α] [MeasurableSpace Ω']
    {P : Measure α} [IsProbabilityMeasure P] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {s : α → EuclideanSpace ℝ κ} {Z : Ω' → EuclideanSpace ℝ κ}
    (hs : MemLp s 2 P)
    (hZ : HasLaw Z (multivariateGaussian 0 (covMatrix (P.map s))) μ') :
    TendstoInDistribution
      (fun (n : ℕ) (x : Fin n → α) ↦ (Real.sqrt n)⁻¹ • ∑ i : Fin n, (s (x i) - ∫ y, s y ∂P))
      atTop Z (fun n ↦ Measure.pi fun _ : Fin n ↦ P) μ' := by
  have hmap : MemLp id 2 (P.map s) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hs.aestronglyMeasurable.aemeasurable).2 hs
  refine tendstoInDistribution_inv_sqrt_smul_sum_sub_pi hs hZ.hasGaussianLaw
    (by rw [hZ.integral_eq, integral_id_multivariateGaussian]) ?_
  ext x y
  rw [hZ.map_eq, covarianceBilin_multivariateGaussian (posSemidef_covMatrix _ hmap),
    covarianceBilin_eq_covMatrix _ hmap]
  simp [PiLp.inner_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm]

end TauCeti
