/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# The regularized hypergeometric function `₀F₁`

Mathlib defines the regularized hypergeometric function `Complex.regularizedHGFun a b` as the sum
of its power series. This file records that series as a `HasSum` statement and develops the
function `₀F₁(; b; z) = ∑ zⁿ / (n! Γ(b + n))`, the case `a = 0`, `b = {b}`, which underlies the
Bessel and Airy functions.

For every complex `b`, Mathlib provides the contiguous relation
`₀F₁(; b; z) = b ₀F₁(; b + 1; z) + z ₀F₁(; b + 2; z)`.
For real `b` and real `y` the value is real, given by the real series `∑ yⁿ / (n! Γ(b + n))`;
it is jointly continuous in `(b, y)` and has derivative `₀F₁(; b + 1; y)` in `y`.
The product of two `₀F₁` functions at the same argument is a `₂F₃` function at `4z` (DLMF 16.12.1),
needed in particular to expand quadratic combinations of Bessel and Airy functions into single
power series. Because `1 / Γ` vanishes at the poles of `Γ`, the series and regularized product
identities hold for all complex parameters without pole exclusions.

## Main results

* `Complex.hasSum_regularizedHGFun` — the power series of `regularizedHGFun a b` converges to it
  everywhere when `a.card ≤ b.card`, absolutely by `Complex.summable_norm_regularizedHGFun`.
* `Complex.hasSum_deriv_regularizedHGFun` — the termwise differentiated series converges to the
  derivative.
* `Complex.regularizedHGFunCoeff_one_singleton` — the coefficients `1 / Γ(b + n)` of the Kummer
  function `𝐌(1, b, z) = ∑ zⁿ / Γ(b + n)`.
* `Complex.hasSum_regularizedHGFun_zero_singleton_ofReal_re` — the real series of `₀F₁` at real
  arguments.
* `Complex.continuous_regularizedHGFun_zero_singleton_ofReal_re` — joint continuity in `(b, y)`.
* `Complex.hasDerivAt_regularizedHGFun_zero_singleton_ofReal_re` — the derivative in `y`.
* `Complex.sum_antidiagonal_regularizedHGFunCoeff_zero_singleton_mul` and
  `Complex.hasSum_regularizedHGFun_zero_singleton_mul` — the Cauchy convolution of `₀F₁`
  coefficients and Maclaurin series of `₀F₁(; b; z) ₀F₁(; c; z)`.
* `Complex.inv_Gamma_mul_regularizedHGFun_zero_singleton_mul` and
  `Complex.regularizedHGFun_zero_singleton_mul` — the `₂F₃` product formula DLMF 16.12.1.
-/

public section

noncomputable section

open Filter Set
open scoped Nat Topology

namespace Complex

/-- The coefficients of `₀F₁(; b; z)` are `1 / (n! Γ(b + n))`. -/
@[simp]
theorem regularizedHGFunCoeff_zero_singleton (b : ℂ) (n : ℕ) :
    regularizedHGFunCoeff 0 {b} n = (n ! * Gamma (b + n))⁻¹ := by
  simp [regularizedHGFunCoeff]

/-- At zero argument and a real parameter, the real part of `₀F₁(; b; 0)` is `1 / Γ(b)`,
including the poles of `Γ`, where its inverse vanishes. -/
theorem regularizedHGFun_zero_singleton_ofReal_zero_re (b : ℝ) :
    (regularizedHGFun 0 {(b : ℂ)} 0).re = (Real.Gamma b)⁻¹ := by
  have h : regularizedHGFun 0 {(b : ℂ)} 0 = (((Real.Gamma b)⁻¹ : ℝ) : ℂ) := by
    rw [ofReal_inv, ← Gamma_ofReal]
    simp
  rw [h, ofReal_re]

/-- When there are at most as many upper as lower parameters, the regularized hypergeometric
series converges to `regularizedHGFun a b z` at every `z`. -/
theorem hasSum_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    HasSum (fun n => regularizedHGFunCoeff a b n * z ^ n) (regularizedHGFun a b z) := by
  have := (regularizedHGFunSeries a b).hasSum (x := z)
    (by simp [radius_regularizedHGFunSeries_eq_top h])
  simpa [regularizedHGFun, regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    mul_comm] using this

/-- When there are at most as many upper as lower parameters, the regularized hypergeometric
series converges absolutely at every `z`. -/
theorem summable_norm_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    Summable fun n => ‖regularizedHGFunCoeff a b n * z ^ n‖ := by
  have := (regularizedHGFunSeries a b).summable_norm_apply (x := z)
    (by simp [radius_regularizedHGFunSeries_eq_top h])
  simpa [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using this

/-- When there are at most as many upper as lower parameters, the derivative of
`regularizedHGFun a b` is the sum of its termwise differentiated power series. -/
theorem hasSum_deriv_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    HasSum (fun n : ℕ => ((n : ℂ) + 1) * regularizedHGFunCoeff a b (n + 1) * z ^ n)
      (deriv (regularizedHGFun a b) z) := by
  set R : ℝ := ‖z‖ + 1
  have hfun : regularizedHGFun a b = fun w => ∑' n, regularizedHGFunCoeff a b n * w ^ n :=
    funext fun w => (hasSum_regularizedHGFun h w).tsum_eq.symm
  have hd := hasSum_deriv_of_summable_norm (summable_norm_regularizedHGFun h (R : ℂ))
    (F := fun n w => regularizedHGFunCoeff a b n * w ^ n) (U := Metric.ball 0 R)
    (fun n => ((differentiable_pow n).const_mul _).differentiableOn) Metric.isOpen_ball
    (fun n w hw => ?_) (z := z) (by simp [R])
  · rw [hfun]
    convert (hasSum_nat_add_iff' 1).mpr hd using 1
    · ext n
      simp only [deriv_const_mul_field', deriv_pow_field, add_tsub_cancel_right]
      push_cast
      ring
    · simp
  · rw [Metric.mem_ball, dist_zero_right] at hw
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    gcongr

/-- The coefficients of the Kummer function `𝐌(1, b, z) = ₁F₁(1; b; z) / Γ(b)` are
`1 / Γ(b + n)`. -/
@[simp]
theorem regularizedHGFunCoeff_one_singleton (b : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {1} {b} n = (Gamma (b + n))⁻¹ := by
  simpa [regularizedHGFunCoeff] using div_mul_cancel_left₀ (Nat.cast_ne_zero.2 n.factorial_ne_zero)
    (Gamma (b + n))

/-- The complex-valued `₀F₁` series at real parameters and arguments sums to its regularized
hypergeometric value. -/
theorem hasSum_ofReal_regularizedHGFun_zero_singleton (b y : ℝ) :
    HasSum (fun n : ℕ => ((y ^ n / (n ! * Real.Gamma (b + n)) : ℝ) : ℂ))
      (regularizedHGFun 0 {(b : ℂ)} y) := by
  convert hasSum_regularizedHGFun (a := 0) (b := {(b : ℂ)}) (by simp) (y : ℂ) with n
  push_cast [← Gamma_ofReal, regularizedHGFunCoeff_zero_singleton]
  ring

/-- At real arguments, `₀F₁(; b; y)` is real. -/
@[simp]
theorem regularizedHGFun_zero_singleton_ofReal_im (b y : ℝ) :
    (regularizedHGFun 0 {(b : ℂ)} y).im = 0 := by
  refine (hasSum_im (hasSum_ofReal_regularizedHGFun_zero_singleton b y)).unique ?_
  simpa only [ofReal_im] using hasSum_zero

/-- At real arguments, `₀F₁(; b; y)` is the sum of the real series `∑ yⁿ / (n! Γ(b + n))`. -/
theorem hasSum_regularizedHGFun_zero_singleton_ofReal_re (b y : ℝ) :
    HasSum (fun n : ℕ => y ^ n / (n ! * Real.Gamma (b + n)))
      (regularizedHGFun 0 {(b : ℂ)} y).re := by
  simpa only [ofReal_re] using hasSum_re (hasSum_ofReal_regularizedHGFun_zero_singleton b y)

/-- The real part of `₀F₁(; b; y)` is jointly continuous in the real parameter `b` and the real
argument `y`. -/
theorem continuous_regularizedHGFun_zero_singleton_ofReal_re :
    Continuous fun p : ℝ × ℝ => (regularizedHGFun 0 {(p.1 : ℂ)} p.2).re := by
  have heq : (fun p : ℝ × ℝ => (regularizedHGFun 0 {(p.1 : ℂ)} p.2).re) =
      fun p => ∑' n : ℕ, p.2 ^ n * ((n ! : ℝ)⁻¹ * (Real.Gamma (p.1 + n))⁻¹) := by
    ext p
    simp_rw [← mul_inv, ← div_eq_mul_inv]
    exact (hasSum_regularizedHGFun_zero_singleton_ofReal_re p.1 p.2).tsum_eq.symm
  rw [heq, continuous_iff_continuousAt]
  rintro ⟨b₀, y₀⟩
  obtain ⟨C, hC⟩ := Real.exists_abs_inv_Gamma_le (b₀ - 1)
  set R := |y₀| + 1
  have hmem : (b₀, y₀) ∈ Ioi (b₀ - 1) ×ˢ Ioo (-R) R :=
    ⟨by simp, by constructor <;> linarith [neg_abs_le y₀, le_abs_self y₀]⟩
  refine (continuousOn_tsum (u := fun n => C * (R ^ n / n !)) (fun n => ?_)
    ((Real.summable_pow_div_factorial R).mul_left C) (fun n p hp => ?_)).continuousAt
    ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
  · exact (continuous_snd.pow n).mul (continuous_const.mul
      (Real.continuous_inv_Gamma.comp (continuous_fst.add continuous_const))) |>.continuousOn
  · obtain ⟨hb, hy⟩ := hp
    have hy' : |p.2| ≤ R := (abs_lt.2 hy).le
    have hG := hC (p.1 + n) (by simp only [mem_Ioi] at hb; linarith [n.cast_nonneg (α := ℝ)])
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_inv, Nat.abs_cast]
    calc |p.2| ^ n * ((n ! : ℝ)⁻¹ * |(Real.Gamma (p.1 + n))⁻¹|)
        ≤ R ^ n * ((n ! : ℝ)⁻¹ * C) := by gcongr
      _ = C * (R ^ n / n !) := by ring

/-- The derivative of `₀F₁(; b; y)` in a real argument `y` is `₀F₁(; b + 1; y)`. -/
theorem hasDerivAt_regularizedHGFun_zero_singleton_ofReal_re (b y : ℝ) :
    HasDerivAt (fun y : ℝ => (regularizedHGFun 0 {(b : ℂ)} y).re)
      (regularizedHGFun 0 {(b : ℂ) + 1} y).re y := by
  have heq : (fun y : ℝ => (regularizedHGFun 0 {(b : ℂ)} y).re) =
      fun y => ∑' n : ℕ, y ^ n / (n ! * Real.Gamma (b + n)) :=
    funext fun y => (hasSum_regularizedHGFun_zero_singleton_ofReal_re b y).tsum_eq.symm
  obtain ⟨C, hC⟩ := Real.exists_abs_inv_Gamma_le b
  set R := |y| + 1
  have hu : Summable fun n : ℕ => C * (n * R ^ (n - 1) / n !) := by
    refine (summable_nat_add_iff 1).1 ?_
    convert (Real.summable_pow_div_factorial R).mul_left C using 2 with n
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have hd := hasDerivAt_tsum_of_isPreconnected (y₀ := 0) (y := y) hu isOpen_Ioo
    isPreconnected_Ioo (t := Ioo (-R) R)
    (g := fun n y => y ^ n / (n ! * Real.Gamma (b + n)))
    (g' := fun n y => n * y ^ (n - 1) / (n ! * Real.Gamma (b + n)))
    (fun n y _ => (hasDerivAt_pow n y).div_const _) (fun n z hz => ?_)
    ⟨by linarith [abs_nonneg y], by linarith [abs_nonneg y]⟩
    (hasSum_regularizedHGFun_zero_singleton_ofReal_re b 0).summable
    ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  · rw [heq]
    convert hd using 1
    refine (HasSum.tsum_eq ?_).symm
    rw [← hasSum_nat_add_iff' 1]
    convert hasSum_regularizedHGFun_zero_singleton_ofReal_re (b + 1) y using 1
    · ext n
      have hadd : b + (n + 1 : ℝ) = b + 1 + n := by ring
      rw [Nat.factorial_succ]
      push_cast
      rw [hadd]
      field_simp
    · simp
  · have hz' : |z| ≤ R := (abs_lt.2 hz).le
    have hG := hC (b + n) (by linarith [n.cast_nonneg (α := ℝ)])
    rw [Real.norm_eq_abs, div_eq_mul_inv, mul_inv, abs_mul, abs_mul, abs_mul, abs_pow, abs_inv,
      Nat.abs_cast, Nat.abs_cast]
    calc (n : ℝ) * |z| ^ (n - 1) * ((n ! : ℝ)⁻¹ * |(Real.Gamma (b + n))⁻¹|)
        ≤ n * R ^ (n - 1) * ((n ! : ℝ)⁻¹ * C) := by gcongr
      _ = C * (n * R ^ (n - 1) / n !) := by ring

/-- The Cauchy convolution of the coefficients of `₀F₁(; b; ·)` and `₀F₁(; c; ·)` is
`(b + c + k - 1)_k / (k! Γ(b + k) Γ(c + k))`, holding for all `b, c : ℂ` including at poles of `Γ`.
-/
theorem sum_antidiagonal_regularizedHGFunCoeff_zero_singleton_mul (b c : ℂ) (k : ℕ) :
    ∑ ij ∈ Finset.antidiagonal k,
      regularizedHGFunCoeff 0 {b} ij.1 * regularizedHGFunCoeff 0 {c} ij.2 =
      (ascPochhammer ℂ k).eval (b + c + k - 1) /
        (k ! * Gamma (b + k) * Gamma (c + k)) := by
  have hterm (ij : ℕ × ℕ) (hij : ij ∈ Finset.antidiagonal k) :
      regularizedHGFunCoeff 0 {b} ij.1 * regularizedHGFunCoeff 0 {c} ij.2 =
        ((k.choose ij.1 : ℂ) * ((ascPochhammer ℂ ij.1).eval (c + ij.2) *
          (ascPochhammer ℂ ij.2).eval (b + ij.1))) *
          (k ! * Gamma (b + k) * Gamma (c + k))⁻¹ := by
    have hk : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
    have hchoose : (k.choose ij.1 : ℂ) * ij.1 ! * ij.2 ! = k ! := by
      have hnat : k.choose ij.1 * ij.1 ! * ij.2 ! = k ! := by
        simpa [← hk] using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right ij.1 ij.2)
      exact_mod_cast hnat
    have hfac : (ij.1 ! : ℂ)⁻¹ * (ij.2 ! : ℂ)⁻¹ = (k.choose ij.1 : ℂ) * (k ! : ℂ)⁻¹ := by
      have hi : (ij.1 ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ij.1.factorial_ne_zero
      have hj : (ij.2 ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ij.2.factorial_ne_zero
      have hk0 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
      field_simp
      linear_combination -hchoose
    have hbG : (Gamma (b + ij.1))⁻¹ =
        (ascPochhammer ℂ ij.2).eval (b + ij.1) * (Gamma (b + k))⁻¹ := by
      simpa [← hk, Nat.cast_add, add_assoc] using
        inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add_natCast (b + ij.1) ij.2
    have hcG : (Gamma (c + ij.2))⁻¹ =
        (ascPochhammer ℂ ij.1).eval (c + ij.2) * (Gamma (c + k))⁻¹ := by
      have hck : c + ij.2 + ij.1 = c + k := by rw [← hk]; push_cast; ring
      simpa [hck] using inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add_natCast (c + ij.2) ij.1
    simp only [regularizedHGFunCoeff_zero_singleton, mul_inv]
    calc (ij.1 ! : ℂ)⁻¹ * (Gamma (b + ij.1))⁻¹ * ((ij.2 ! : ℂ)⁻¹ * (Gamma (c + ij.2))⁻¹)
        = ((ij.1 ! : ℂ)⁻¹ * (ij.2 ! : ℂ)⁻¹) * (Gamma (b + ij.1))⁻¹ * (Gamma (c + ij.2))⁻¹ := by
          ring
      _ = (k.choose ij.1 : ℂ) * ((ascPochhammer ℂ ij.1).eval (c + ij.2) *
            (ascPochhammer ℂ ij.2).eval (b + ij.1)) *
            ((k ! : ℂ)⁻¹ * (Gamma (b + k))⁻¹ * (Gamma (c + k))⁻¹) := by
          rw [hfac, hbG, hcG]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    TauCeti.sum_antidiagonal_choose_mul_ascPochhammer_eval (Commute.all c b) k]
  have hcb : c + b + k - 1 = b + c + k - 1 := by ring
  rw [hcb, div_eq_mul_inv]

/-- **Maclaurin series for the product of two regularized `₀F₁` functions (DLMF 16.12.1).**
For all complex parameters `b, c` and argument `z` (including at nonpositive-integer poles of `Γ`,
where `1 / Γ` vanishes),
`₀F₁(; b; z) ₀F₁(; c; z) = ∑_{k=0}^∞ (b + c + k - 1)_k z^k / (k! Γ(b + k) Γ(c + k))`. -/
theorem hasSum_regularizedHGFun_zero_singleton_mul (b c z : ℂ) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval (b + c + k - 1) * z ^ k /
      (k ! * Gamma (b + k) * Gamma (c + k)))
      (regularizedHGFun 0 {b} z * regularizedHGFun 0 {c} z) := by
  set f : ℕ → ℂ := fun n => regularizedHGFunCoeff 0 {b} n * z ^ n
  set g : ℕ → ℂ := fun n => regularizedHGFunCoeff 0 {c} n * z ^ n
  have hf : Summable fun n => ‖f n‖ := summable_norm_regularizedHGFun (by simp) z
  have hg : Summable fun n => ‖g n‖ := summable_norm_regularizedHGFun (by simp) z
  have hcauchy : HasSum (fun k => ∑ ij ∈ Finset.antidiagonal k, f ij.1 * g ij.2)
      (regularizedHGFun 0 {b} z * regularizedHGFun 0 {c} z) := by
    rw [← (hasSum_regularizedHGFun (a := 0) (b := {b}) (by simp) z).tsum_eq,
      ← (hasSum_regularizedHGFun (a := 0) (b := {c}) (by simp) z).tsum_eq,
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm.hasSum
  refine hcauchy.congr_fun fun k => ?_
  have hpow (ij : ℕ × ℕ) (hij : ij ∈ Finset.antidiagonal k) :
      f ij.1 * g ij.2 =
        (regularizedHGFunCoeff 0 {b} ij.1 * regularizedHGFunCoeff 0 {c} ij.2) * z ^ k := by
    have hzk : z ^ ij.1 * z ^ ij.2 = z ^ k := by rw [← pow_add, Finset.mem_antidiagonal.mp hij]
    dsimp only [f, g]
    linear_combination regularizedHGFunCoeff 0 {b} ij.1 * regularizedHGFunCoeff 0 {c} ij.2 * hzk
  rw [Finset.sum_congr rfl hpow, ← Finset.sum_mul,
    sum_antidiagonal_regularizedHGFunCoeff_zero_singleton_mul, div_mul_eq_mul_div]

/-- **Product of two regularized `₀F₁` functions (DLMF 16.12.1, regularized form).**
For all complex parameters `b, c` and argument `z`,
`(Γ(b + c - 1))⁻¹ ₀F₁(; b; z) ₀F₁(; c; z) = ₂F₃((b + c - 1)/2, (b + c)/2; b, c, b + c - 1; 4z)`.
Because `1 / Γ` vanishes at the nonpositive-integer poles of `Γ`, this holds without any
parameter hypotheses. -/
theorem inv_Gamma_mul_regularizedHGFun_zero_singleton_mul (b c z : ℂ) :
    (Gamma (b + c - 1))⁻¹ * (regularizedHGFun 0 {b} z * regularizedHGFun 0 {c} z) =
      regularizedHGFun {(b + c - 1) / 2, (b + c) / 2} {b, c, b + c - 1} (4 * z) := by
  refine ((hasSum_regularizedHGFun_zero_singleton_mul b c z).mul_left
    (Gamma (b + c - 1))⁻¹).unique ?_
  convert hasSum_regularizedHGFun (a := {(b + c - 1) / 2, (b + c) / 2})
    (b := {b, c, b + c - 1}) (by simp) (4 * z) using 1
  ext k
  have hG := inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add_natCast (b + c - 1) k
  have hmul : (ascPochhammer ℂ k).eval (b + c - 1) *
      (ascPochhammer ℂ k).eval (b + c + k - 1) =
      (ascPochhammer ℂ (2 * k)).eval (b + c - 1) := by
    have hshift : b + c + k - 1 = b + c - 1 + k := by ring
    simpa [Polynomial.eval_mul, Polynomial.eval_comp, two_mul, hshift] using
      congrArg (Polynomial.eval (b + c - 1)) (ascPochhammer_mul (S := ℂ) k k)
  have hdup := TauCeti.ascPochhammer_two_mul_eval (by norm_num : (2 : ℂ) ≠ 0) k (b + c - 1)
  have hhalf : (b + c - 1 + 1) / 2 = (b + c) / 2 := by ring
  rw [hhalf] at hdup
  rw [hG, regularizedHGFunCoeff]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, div_eq_mul_inv, mul_inv, mul_pow]
  calc (ascPochhammer ℂ k).eval (b + c - 1) * (Gamma (b + c - 1 + k))⁻¹ *
        ((ascPochhammer ℂ k).eval (b + c + k - 1) * z ^ k *
          ((k ! : ℂ)⁻¹ * (Gamma (b + k))⁻¹ * (Gamma (c + k))⁻¹))
      = ((ascPochhammer ℂ k).eval (b + c - 1) * (ascPochhammer ℂ k).eval (b + c + k - 1)) *
          z ^ k * ((k ! : ℂ)⁻¹ * (Gamma (b + k))⁻¹ * (Gamma (c + k))⁻¹ *
            (Gamma (b + c - 1 + k))⁻¹) := by ring
    _ = (ascPochhammer ℂ k).eval ((b + c - 1) / 2) *
          (ascPochhammer ℂ k).eval ((b + c) / 2) *
          ((k ! : ℂ)⁻¹ * ((Gamma (b + k))⁻¹ * ((Gamma (c + k))⁻¹ *
            (Gamma (b + c - 1 + k))⁻¹))) * (4 ^ k * z ^ k) := by
        rw [hmul, hdup]; ring

/-- **Product of two regularized `₀F₁` functions (DLMF 16.12.1).**
When `Γ(b + c - 1) ≠ 0` (i.e., `b + c - 1` is not a nonpositive integer),
`₀F₁(; b; z) ₀F₁(; c; z) = Γ(b + c - 1) ₂F₃((b + c - 1)/2, (b + c)/2; b, c, b + c - 1; 4z)`. -/
theorem regularizedHGFun_zero_singleton_mul {b c : ℂ} (h : Gamma (b + c - 1) ≠ 0) (z : ℂ) :
    regularizedHGFun 0 {b} z * regularizedHGFun 0 {c} z =
      Gamma (b + c - 1) *
        regularizedHGFun {(b + c - 1) / 2, (b + c) / 2} {b, c, b + c - 1} (4 * z) := by
  rw [← inv_Gamma_mul_regularizedHGFun_zero_singleton_mul, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

end Complex
