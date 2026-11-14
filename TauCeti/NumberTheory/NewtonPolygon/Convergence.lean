/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Radius
public import TauCeti.RingTheory.PowerSeries.Radius.Convergence

/-!
# Convergence of power series in valued extensions and Newton slopes

Fix a real additive valuation `v` on a normed division ring `K` and a base `b > 1` with
`‖x‖ = b ^ (-(v x).untop₀)` for nonzero `x`. At the radius `b ^ σ`, restrictedness of a power
series `f = ∑ aₙ Xⁿ` is the valuation decay condition that for every intercept `c`, eventually
`c + σ n ≤ v(aₙ)` (`PowerSeries.isRestricted_rpow_iff`). In a complete ultrametric target `A` over
`K` with a multiplicative norm and norm-preserving scalar multiplication, summability of
`∑ aₙ • xⁿ` at a point `x : A` of norm `b ^ σ` is therefore equivalent to this same asymptotic
valuation condition (`PowerSeries.summable_smul_pow_iff_eventually_le_addValuation_coeff`).

Comparing the convergence-point radius `PowerSeries.convergencePointRadius A f` with the
Newton-polygon formula for `PowerSeries.radius f` separates what depends on the coefficients from
what depends on the value group of `A`:

* in every target `A` with a multiplicative norm and norm-preserving scalar multiplication,
  `f.convergencePointRadius A ≤ b ^ λ`, where `λ = liminf_{n → ∞} v(aₙ) / n`
  (`PowerSeries.convergencePointRadius_le_exp_linearGrowthInf`);
* in a complete densely normed extension `L` (such as `ℂ_[p]`),
  `f.convergencePointRadius L = b ^ λ`, and for admissible series with infinitely many nonzero
  coefficients it is `b` raised to the supremum of the finite slopes of the Newton polygon
  (`PowerSeries.convergencePointRadius_eq_exp_linearGrowthInf`,
  `PowerSeries.convergencePointRadius_eq_exp_iSup_unitSlope_newtonPolygon`).

## Main results

* `PowerSeries.isRestricted_rpow_iff` and
  `PowerSeries.summable_smul_pow_iff_eventually_le_addValuation_coeff`: valuation criteria for
  restrictedness at `b ^ σ` and convergence at a point of norm `b ^ σ`.
* `PowerSeries.convergencePointRadius_le_exp_linearGrowthInf`,
  `PowerSeries.convergencePointRadius_eq_exp_linearGrowthInf`, and
  `PowerSeries.convergencePointRadius_eq_exp_iSup_unitSlope_newtonPolygon`: linear-growth and
  Newton-polygon formulas for the convergence-point radius.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 6 §§1–2.
-/

public section

open Filter LinearGrowth TauCeti
open scoped NNReal ENNReal Topology

namespace PowerSeries

variable {K : Type*} [NormedDivisionRing K] (f : K⟦X⟧)
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Valuation criterion for restrictedness.** A series `f = ∑ aₙ Xⁿ` is restricted at the radius
`b ^ σ` if and only if for every real intercept `c`, eventually `c + σ * n ≤ v (aₙ)`. -/
theorem isRestricted_rpow_iff (σ : ℝ) :
    f.IsRestricted (b ^ σ) ↔
      ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, ((c + σ * n : ℝ) : WithTop ℝ) ≤ v (coeff n f) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  rw [isRestricted_iff']
  refine ⟨fun hf c ↦ ?_, fun h ↦ Metric.tendsto_nhds.mpr fun ε hε ↦ ?_⟩
  · have hmem : Set.Iic (b ^ (-c)) ∈ 𝓝 (0 : ℝ) :=
      Iic_mem_nhds (Real.rpow_pos_of_pos hb0 (-c))
    filter_upwards [hf.eventually hmem] with n hn
    exact (norm_coeff_mul_rpow_pow_le_iff f v hb hv n σ c).mp hn
  · -- Choose `c` with `b ^ (-c) = ε / 2 < ε`.
    set c := -Real.logb b (ε / 2)
    have hpow : b ^ (-c) = ε / 2 := by
      rw [neg_neg, Real.rpow_logb hb0 hb.ne' (half_pos hε)]
    filter_upwards [h c] with n hn
    have hle : ‖coeff n f‖ * (b ^ σ) ^ n ≤ ε / 2 :=
      hpow ▸ (norm_coeff_mul_rpow_pow_le_iff f v hb hv n σ c).mpr hn
    have hnonneg : 0 ≤ ‖coeff n f‖ * (b ^ σ) ^ n :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (Real.rpow_nonneg hb0.le σ) n)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    exact hle.trans_lt (half_lt_self hε)

/-- **Valuation criterion for pointwise convergence.** In a complete ultrametric target `A` over
`K` with a multiplicative norm and norm-preserving scalar multiplication, `∑ aₙ • xⁿ` is summable at
a point `x` of norm `b ^ σ` if and only if for every `c : ℝ`, eventually `c + σ * n ≤ v (aₙ)`. -/
theorem summable_smul_pow_iff_eventually_le_addValuation_coeff {A : Type*} [SeminormedRing A]
    [Module K A] [NormSMulClass K A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
    {x : A} {σ : ℝ} (hx : ‖x‖ = b ^ σ) :
    (Summable fun n ↦ coeff n f • x ^ n) ↔
      ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, ((c + σ * n : ℝ) : WithTop ℝ) ≤ v (coeff n f) := by
  rw [summable_smul_pow_iff_isRestricted, hx, isRestricted_rpow_iff f v hb hv σ]

/-- In any target `A` with a multiplicative norm and norm-preserving scalar multiplication, the
convergence-point radius of `f` is bounded above by `b ^ λ`, where `λ = liminf v(aₙ) / n`. -/
theorem convergencePointRadius_le_exp_linearGrowthInf (A : Type*) [SeminormedRing A]
    [SMulZeroClass K A] [NormSMulClass K A] [NormMulClass A] :
    f.convergencePointRadius A ≤
      EReal.exp ((linearGrowthInf fun n ↦ (v (coeff n f)).toEReal) * Real.log b) :=
  convergencePointRadius_le_radius.trans_eq (radius_eq_exp_linearGrowthInf f v hb hv)

/-- **Convergence-point radius from coefficient growth.** In a complete densely normed field `L`
over `K`, the convergence-point radius of `f` is `b ^ λ`, where `λ = liminf v(aₙ) / n`. -/
theorem convergencePointRadius_eq_exp_linearGrowthInf (L : Type*) [DenselyNormedField L]
    [Module K L] [NormSMulClass K L] [CompleteSpace L] :
    f.convergencePointRadius L =
      EReal.exp ((linearGrowthInf fun n ↦ (v (coeff n f)).toEReal) * Real.log b) := by
  rw [convergencePointRadius_eq_radius, radius_eq_exp_linearGrowthInf f v hb hv]

/-- **Convergence-point radius from Newton slopes.** In a complete densely normed field `L` over
`K`, for admissible coefficient heights with infinitely many nonzero coefficients, the
convergence-point radius of `f` is `b` raised to the supremum of the finite Newton slopes. -/
theorem convergencePointRadius_eq_exp_iSup_unitSlope_newtonPolygon (L : Type*)
    [DenselyNormedField L] [Module K L] [NormSMulClass K L] [CompleteSpace L]
    (hf : IsAdmissible fun n ↦ v (coeff n f)) (hinf : {n | coeff n f ≠ 0}.Infinite) :
    f.convergencePointRadius L = EReal.exp ((⨆ i : finiteEdges (f.newtonPolygon v),
      (unitSlope (f.newtonPolygon v) i : EReal)) * Real.log b) := by
  rw [convergencePointRadius_eq_radius,
    radius_eq_exp_iSup_unitSlope_newtonPolygon f v hb hv hf hinf]

end PowerSeries
