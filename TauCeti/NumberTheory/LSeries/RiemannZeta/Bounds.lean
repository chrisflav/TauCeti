/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.SumCoeff

/-!
# Explicit bounds on the Riemann zeta function

On `Re s > 0`, `s ≠ 1`, the partial-summation integral of the alternating Dirichlet series
`η(s) = (1 - 2 ^ (1 - s)) ζ(s)`, whose partial sums take only the values `0` and `1`, yields the
explicit bound `‖(1 - 2 ^ (1 - s)) ζ(s)‖ ≤ ‖s‖ / s.re`.

On `Re s > 1`, peeling off the `n = 1` term from `ζ(s) = ∑_{n ≥ 1} n ^ (-s)` bounds the tail norm
`‖ζ(s) - 1‖` by `(ζ(s.re)).re - 1`. Since `σ ↦ (ζ(σ)).re` is antitone on `(1, ∞)` and
`ζ(2) = π² / 6 < 5 / 3`, on `Re s ≥ 2` we have `‖ζ(s) - 1‖ < 2 / 3`, `1 / 3 < (ζ(s)).re`, and
`ζ(s) ∈ Complex.slitPlane`.

## Main results

* `TauCeti.norm_one_sub_two_cpow_mul_riemannZeta_le`: `‖(1 - 2 ^ (1 - s)) ζ(s)‖ ≤ ‖s‖ / s.re` for
  `0 < s.re` and `s ≠ 1`.
* `TauCeti.riemannZeta_re_antitoneOn_Ioi`: `σ ↦ (ζ(σ)).re` is antitone on `(1, ∞)`.
* `TauCeti.norm_riemannZeta_sub_one_le`: `‖ζ(s) - 1‖ ≤ (ζ(s.re)).re - 1` for `1 < s.re`.
* `TauCeti.two_sub_riemannZeta_re_le_riemannZeta_re`: `2 - (ζ(s.re)).re ≤ (ζ(s)).re` for `1 < s.re`.
* `TauCeti.norm_riemannZeta_sub_one_lt_two_div_three_of_two_le_re`,
  `TauCeti.one_div_three_lt_riemannZeta_re_of_two_le_re`, and
  `TauCeti.riemannZeta_mem_slitPlane_of_two_le_re`: quantitative bounds on `Re s ≥ 2`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§9.3–9.4.
-/

public section

open Complex Set

namespace TauCeti

/-- On `Re s > 0`, `s ≠ 1`, the alternating zeta product `(1 - 2 ^ (1 - s)) ζ(s)` has norm at most
`‖s‖ / s.re`. -/
theorem norm_one_sub_two_cpow_mul_riemannZeta_le {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    ‖(1 - 2 ^ (1 - s)) * riemannZeta s‖ ≤ ‖s‖ / s.re := by
  rw [one_sub_two_cpow_mul_riemannZeta_eq_mul_integral hs hs₁]
  have h1 : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (k + 1)‖ ≤ (1 : ℝ) :=
    fun n ↦ by simpa using LSeries.norm_sum_Icc_neg_one_pow_add_one_le (R := ℂ) n
  simpa using TauCeti.LSeries.norm_mul_integral_le_of_bound
    (fun k ↦ (-1 : ℂ) ^ (k + 1)) h1 hs

/-- On `(1, ∞)`, the real Dirichlet series `σ ↦ (ζ(σ)).re` is antitone. -/
theorem riemannZeta_re_antitoneOn_Ioi :
    AntitoneOn (fun σ : ℝ ↦ (riemannZeta σ).re) (Ioi 1) := by
  intro x hx y hy hxy
  dsimp only
  have hsum_x := hasSum_nat_add_one_rpow_neg_riemannZeta_re hx
  have hsum_y := hasSum_nat_add_one_rpow_neg_riemannZeta_re hy
  rw [← hsum_x.tsum_eq, ← hsum_y.tsum_eq]
  exact hsum_y.summable.tsum_le_tsum
    (fun n ↦ Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)])
      (neg_le_neg hxy))
    hsum_x.summable

/-- On `Re s > 1`, the Dirichlet tail `ζ(s) - 1` has norm at most `(ζ(s.re)).re - 1`. -/
theorem norm_riemannZeta_sub_one_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s - 1‖ ≤ (riemannZeta s.re).re - 1 := by
  let u : ℕ → ℂ := fun n ↦ 1 / ((n : ℂ) + 1) ^ s
  let v : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) ^ (-s.re)
  have hnorm : ∀ n : ℕ, ‖u n‖ = v n := fun n ↦ by
    simp only [u, v]
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, norm_div, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos hpos, one_div,
      Real.rpow_neg hpos.le]
  have hv : HasSum v (riemannZeta s.re).re := hasSum_nat_add_one_rpow_neg_riemannZeta_re hs
  have hu_sum : Summable u := Summable.of_norm (by simpa only [hnorm] using hv.summable)
  have hu : HasSum u (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact hu_sum.hasSum
  have hu1 : HasSum (fun n ↦ u (n + 1)) (riemannZeta s - 1) := by
    simpa [u] using (hasSum_nat_add_iff' 1).2 hu
  have hv1 : HasSum (fun n ↦ v (n + 1)) ((riemannZeta s.re).re - 1) := by
    simpa [v] using (hasSum_nat_add_iff' 1).2 hv
  rw [← hu1.tsum_eq, ← hv1.tsum_eq]
  exact (norm_tsum_le_tsum_norm (by simpa only [hnorm] using hv1.summable)).trans_eq
    (tsum_congr fun n ↦ hnorm (n + 1))

/-- On `Re s > 1`, `(ζ(s)).re ≥ 2 - (ζ(s.re)).re`. -/
theorem two_sub_riemannZeta_re_le_riemannZeta_re {s : ℂ} (hs : 1 < s.re) :
    2 - (riemannZeta s.re).re ≤ (riemannZeta s).re := by
  have h1 : 1 - (riemannZeta s).re ≤ ‖riemannZeta s - 1‖ := by
    calc 1 - (riemannZeta s).re = (1 - riemannZeta s).re := by simp
      _ ≤ ‖1 - riemannZeta s‖ := Complex.re_le_norm _
      _ = ‖riemannZeta s - 1‖ := norm_sub_rev _ _
  linarith [norm_riemannZeta_sub_one_le hs]

/-- On `Re s ≥ 2`, `‖ζ(s) - 1‖ < 2 / 3`, since `ζ(2) = π² / 6` and `π < 3.15`. -/
theorem norm_riemannZeta_sub_one_lt_two_div_three_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ < 2 / 3 := by
  have hs1 : 1 < s.re := by linarith
  have hle : (riemannZeta s.re).re ≤ (riemannZeta (2 : ℝ)).re :=
    riemannZeta_re_antitoneOn_Ioi (by norm_num : (2 : ℝ) ∈ Ioi 1) hs1 hs
  have hζ2 : (riemannZeta (2 : ℝ)).re = Real.pi ^ 2 / 6 := by
    have h2 : riemannZeta (2 : ℝ) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
      simpa using riemannZeta_two
    rw [h2, ofReal_re]
  have hpi : Real.pi ^ 2 < 10 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d2]
  linarith [norm_riemannZeta_sub_one_le hs1]

/-- On `Re s ≥ 2`, `1 / 3 < (ζ(s)).re`. -/
theorem one_div_three_lt_riemannZeta_re_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    1 / 3 < (riemannZeta s).re := by
  have h1 : 1 - (riemannZeta s).re ≤ ‖riemannZeta s - 1‖ := by
    calc 1 - (riemannZeta s).re = (1 - riemannZeta s).re := by simp
      _ ≤ ‖1 - riemannZeta s‖ := Complex.re_le_norm _
      _ = ‖riemannZeta s - 1‖ := norm_sub_rev _ _
  linarith [norm_riemannZeta_sub_one_lt_two_div_three_of_two_le_re hs]

/-- On `Re s ≥ 2`, `ζ(s)` has positive real part and therefore lies in `Complex.slitPlane`. -/
theorem riemannZeta_mem_slitPlane_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    riemannZeta s ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2
    (Or.inl (by linarith [one_div_three_lt_riemannZeta_re_of_two_le_re hs]))

end TauCeti
