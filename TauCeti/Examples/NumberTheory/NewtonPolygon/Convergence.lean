/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Convergence
public import TauCeti.NumberTheory.Padics.Complex.Valuation
public import TauCeti.NumberTheory.Padics.LogGauge
import TauCeti.NumberTheory.Padics.Basic

/-!
# Explicit `ℚ_[p]` versus `ℂ_[p]` convergence-point radius comparison

Concrete instances of discrete-norm rounding and dense-norm restoration of the convergence-point
radius over `ℚ_[p]` and `ℂ_[p]`:

* Over `ℚ_[p]`, whose nonzero norms are the integer powers `{p ^ m | m : ℤ}`, any power series of
  intrinsic radius `p ^ t` with `t ∉ ℤ` has convergence-point radius `p ^ ⌊t⌋` in `ℚ_[p]`
  (`convergencePointRadius_padic_eq_ofReal_zpow_floor`).
* For `k ≠ 0`, the series `∑ₙ p ^ ⌈n / k⌉ Xⁿ` over `ℚ_[p]` has lower linear valuation growth
  `1 / k` and intrinsic radius `p ^ (1 / k)`
  (`linearGrowthInf_padicRealValuation_mk_pow_ceil_div`, `radius_mk_pow_ceil_div_padic`).
* Specialising to `k = 2`, the series `∑ₙ p ^ ⌈n / 2⌉ Xⁿ` has intrinsic radius `√p`,
  convergence-point radius `1` in `ℚ_[p]`, and convergence-point radius `√p` in `ℂ_[p]`, witnessing
  strict inequality `f.convergencePointRadius ℚ_[p] < f.radius` over a discretely normed base field
  (`radius_mk_pow_ceil_div_two_padic`, `convergencePointRadius_padic_mk_pow_ceil_div_two`,
  `convergencePointRadius_padicComplex_mk_pow_ceil_div_two`,
  `convergencePointRadius_padic_lt_radius_mk_pow_ceil_div_two`).

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 6 §§1–2.
-/

public section

open Filter LinearGrowth PowerSeries TauCeti
open scoped NNReal ENNReal

namespace TauCeti.NewtonPolygonConvergenceExample

variable {p : ℕ} [Fact p.Prime]

/-- Over `ℚ_[p]`, a power series of radius `p ^ t` for a non-integer real `t` has convergence-point
radius `p ^ ⌊t⌋` in `ℚ_[p]`. -/
theorem convergencePointRadius_padic_eq_ofReal_zpow_floor {f : ℚ_[p]⟦X⟧} {t : ℝ}
    (ht : ∀ m : ℤ, (m : ℝ) ≠ t) (hr : f.radius = ENNReal.ofReal ((p : ℝ) ^ t)) :
    f.convergencePointRadius ℚ_[p] = ENNReal.ofReal ((p : ℝ) ^ ⌊t⌋) := by
  have hrange := Padic.range_norm_sdiff_singleton_zero p
  exact convergencePointRadius_eq_ofReal_zpow_floor (mod_cast (Fact.out : p.Prime).one_lt)
    hrange.subset ht ((hrange.symm.subset ⟨⌊t⌋, rfl⟩).1) hr

/-- For `k ≠ 0`, the coefficient valuations of `∑ₙ p ^ ⌈n / k⌉ Xⁿ` over `ℚ_[p]` have lower linear
growth `1 / k`. -/
theorem linearGrowthInf_padicRealValuation_mk_pow_ceil_div {k : ℕ} (hk : k ≠ 0) :
    (linearGrowthInf fun n : ℕ ↦
      (padicRealValuation p (coeff n (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / k⌉₊))).toEReal) =
        ((1 / (k : ℝ) : ℝ) : EReal) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hval : ∀ m : ℕ, padicRealValuation p ((p : ℚ_[p]) ^ m) = ((m : ℝ) : WithTop ℝ) := fun m ↦ by
    simp [(padicRealValuation p).map_pow]
  apply le_antisymm
  · rw [← linearGrowthInf_const_mul_self (a := ((1 / (k : ℝ) : ℝ) : EReal))]
    refine linearGrowthInf_le_of_eventually_le (b := (1 : EReal)) (EReal.coe_ne_top 1)
      (Eventually.of_forall fun n ↦ ?_)
    rw [coeff_mk, hval, WithTop.toEReal_coe, ← EReal.coe_natCast,
      ← EReal.coe_mul, ← EReal.coe_one, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hlt := (Nat.ceil_lt_add_one (div_nonneg n.cast_nonneg hk_pos.le)).le
    linarith [one_div_mul_eq_div (k : ℝ) (n : ℝ)]
  · refine le_linearGrowthInf_of_affine_le (c := 0) fun n ↦ ?_
    rw [coeff_mk, hval, WithTop.coe_le_coe, zero_add, one_div_mul_eq_div]
    exact Nat.le_ceil _

/-- For `k ≠ 0`, the series `∑ₙ p ^ ⌈n / k⌉ Xⁿ` over `ℚ_[p]` has intrinsic radius
`ENNReal.ofReal (p ^ (1 / k))`. -/
theorem radius_mk_pow_ceil_div_padic {k : ℕ} (hk : k ≠ 0) :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / k⌉₊).radius =
      ENNReal.ofReal ((p : ℝ) ^ (1 / (k : ℝ))) :=
  radius_eq_ofReal_rpow _ (padicRealValuation p) (mod_cast (Fact.out : p.Prime).one_lt)
    (fun _ hx ↦ norm_eq_rpow_neg_padicRealValuation hx)
    (linearGrowthInf_padicRealValuation_mk_pow_ceil_div hk)

variable (p) in
/-- **Intrinsic radius of `∑ₙ p ^ ⌈n / 2⌉ Xⁿ`.** Over `ℚ_[p]`, the series `∑ₙ p ^ ⌈n / 2⌉ Xⁿ` has
intrinsic radius `√p`. -/
theorem radius_mk_pow_ceil_div_two_padic :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).radius = ENNReal.ofReal √p := by
  simpa [Real.sqrt_eq_rpow] using radius_mk_pow_ceil_div_padic (p := p) (k := 2) two_ne_zero

variable (p) in
/-- **Convergence-point radius of `∑ₙ p ^ ⌈n / 2⌉ Xⁿ` in `ℚ_[p]`.** Because `ℚ_[p]` contains no
element of norm strictly between `1` and `p`, the convergence-point radius in `ℚ_[p]` is `1`. -/
theorem convergencePointRadius_padic_mk_pow_ceil_div_two :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).convergencePointRadius ℚ_[p] = 1 := by
  have hnot_int : ∀ m : ℤ, (m : ℝ) ≠ (1 / 2 : ℝ) := by
    intro m hm
    have hmul : (2 * m : ℤ) = (1 : ℤ) := by
      exact_mod_cast (by linarith : (2 : ℝ) * m = 1)
    omega
  have hrad := radius_mk_pow_ceil_div_padic (p := p) (k := 2) two_ne_zero
  simp only [Nat.cast_ofNat] at hrad
  have hfloor : ⌊(1 / 2 : ℝ)⌋ = 0 :=
    Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [convergencePointRadius_padic_eq_ofReal_zpow_floor hnot_int hrad, hfloor, zpow_zero,
    ENNReal.ofReal_one]

variable (p) in
/-- **Convergence-point radius of `∑ₙ p ^ ⌈n / 2⌉ Xⁿ` in `ℂ_[p]`.** Passing to `ℂ_[p]` restores
the full intrinsic radius `√p`. -/
theorem convergencePointRadius_padicComplex_mk_pow_ceil_div_two :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).convergencePointRadius ℂ_[p] =
      ENNReal.ofReal √p := by
  rw [convergencePointRadius_eq_radius, radius_mk_pow_ceil_div_two_padic]

variable (p) in
/-- For `∑ₙ p ^ ⌈n / 2⌉ Xⁿ` over `ℚ_[p]`, the convergence-point radius in `ℚ_[p]` is strictly
smaller than the intrinsic radius. -/
theorem convergencePointRadius_padic_lt_radius_mk_pow_ceil_div_two :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).convergencePointRadius ℚ_[p] <
      (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).radius := by
  rw [convergencePointRadius_padic_mk_pow_ceil_div_two, radius_mk_pow_ceil_div_two_padic,
    ← ENNReal.ofReal_one]
  have hp1 : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have hsqrt : 1 < √p := (Real.lt_sqrt zero_le_one).mpr (by simpa using hp1)
  exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hsqrt)).mpr hsqrt

end TauCeti.NewtonPolygonConvergenceExample
