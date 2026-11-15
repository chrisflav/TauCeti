/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import TauCeti.Analysis.SpecialFunctions.Gamma.Multiplication
import TauCeti.Topology.Algebra.InfiniteSum.Constructions

/-!
# Products of Airy functions: `Ai² + Bi²` and its integral representation

This file gives the hypergeometric `₂F₃` decomposition, single Maclaurin series, and Laplace-type
integral representation (DLMF 9.11.4) of the sum of squares `Ai(z)² + Bi(z)²` for every complex
argument `z`:

$$
\operatorname{Ai}(z)^2 + \operatorname{Bi}(z)^2 =
  \pi^{-3/2} \int_0^\infty \exp\!\left(z t - \frac{t^3}{12}\right) t^{-1/2}\,dt.
$$

On the real axis `Ai(x)² + Bi(x)²` is the squared Airy modulus `M(x)²`, and the positivity of the
integrand at real arguments makes the nonvanishing and monotonicity properties of `M(x)²` manifest,
while providing the Laplace kernel needed for definite integrals of Airy products. Across the
complex plane, the three `₀F₁` product subseries indexed by the residue classes modulo `3` combine
into the single everywhere-convergent power series

$$
\operatorname{Ai}(z)^2 + \operatorname{Bi}(z)^2 =
  \pi^{-3/2} \sum_{m=0}^\infty \frac{12^{(m + 1/2)/3}\,\Gamma((m + 1/2)/3)}{3\,m!}\,z^m.
$$

## Main results

* `TauCeti.airyAi_sq_add_airyBi_sq_eq_regularizedHGFun`: expression of `Ai(z)² + Bi(z)²` as a
  linear combination of three regularized `₂F₃` functions at `4 z³ / 9`.
* `TauCeti.integrableOn_cexp_mul_sub_div_mul_cpow_Ioi`: Bochner integrability of
  `t ↦ exp(z t - t³ / 12) t^{-1/2}` on `(0, ∞)` for every `z : ℂ`.
* `TauCeti.airyAi_sq_add_airyBi_sq_eq_integral`: DLMF 9.11.4,
  `Ai(z)² + Bi(z)² = π^{-3/2} ∫₀^∞ exp(z t - t³ / 12) t^{-1/2} dt`.
* `TauCeti.hasSum_airyAi_sq_add_airyBi_sq`: the everywhere-convergent Maclaurin series of
  `Ai(z)² + Bi(z)²`.
* `TauCeti.four_mul_airyAi_zero_sq`: the value at `z = 0`,
  `4 Ai(0)² = π^{-3/2} 12^{1/6} Γ(1/6) / 3`.

## References

* NIST Digital Library of Mathematical Functions, §§9.11(ii), 16.12,
  <https://dlmf.nist.gov/9.11>, <https://dlmf.nist.gov/16.12>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 11.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped Nat Real Topology

namespace TauCeti

/-! ### Quadratic hypergeometric decomposition of `Ai² + Bi²` -/

private theorem airyAi_sq_add_airyBi_sq_decomp (z : ℂ) :
    airyAi z ^ 2 + airyBi z ^ 2 =
      4 * (3 : ℂ) ^ (-4 / 3 : ℂ) *
        (regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) *
          regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)) +
      4 * (3 : ℂ) ^ (-2 : ℂ) * z *
        (regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) *
          regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) +
      4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2 *
        (regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) *
          regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) := by
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have hc₀ : ((3 : ℂ) ^ (-2 / 3 : ℂ)) ^ 2 + ((3 : ℂ) ^ (-1 / 6 : ℂ)) ^ 2 =
      4 * (3 : ℂ) ^ (-4 / 3 : ℂ) := by
    have h₁ : (-2 / 3 : ℂ) + (-2 / 3 : ℂ) = -4 / 3 := by norm_num
    have h₂ : (-1 / 6 : ℂ) + (-1 / 6 : ℂ) = -4 / 3 + 1 := by norm_num
    rw [sq, sq, ← cpow_add _ _ h3, ← cpow_add _ _ h3, h₁, h₂, cpow_add _ _ h3, cpow_one]
    ring
  have hc₁ : -2 * ((3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (-4 / 3 : ℂ)) +
      2 * ((3 : ℂ) ^ (-1 / 6 : ℂ) * (3 : ℂ) ^ (-5 / 6 : ℂ)) = 4 * (3 : ℂ) ^ (-2 : ℂ) := by
    have h₁ : (-2 / 3 : ℂ) + (-4 / 3 : ℂ) = -2 := by norm_num
    have h₂ : (-1 / 6 : ℂ) + (-5 / 6 : ℂ) = -2 + 1 := by norm_num
    rw [← cpow_add _ _ h3, ← cpow_add _ _ h3, h₁, h₂, cpow_add _ _ h3, cpow_one]
    ring
  have hc₂ : ((3 : ℂ) ^ (-4 / 3 : ℂ)) ^ 2 + ((3 : ℂ) ^ (-5 / 6 : ℂ)) ^ 2 =
      4 * (3 : ℂ) ^ (-8 / 3 : ℂ) := by
    have h₁ : (-4 / 3 : ℂ) + (-4 / 3 : ℂ) = -8 / 3 := by norm_num
    have h₂ : (-5 / 6 : ℂ) + (-5 / 6 : ℂ) = -8 / 3 + 1 := by norm_num
    rw [sq, sq, ← cpow_add _ _ h3, ← cpow_add _ _ h3, h₁, h₂, cpow_add _ _ h3, cpow_one]
    ring
  rw [airyAi_def, airyBi_def]
  set U := regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)
  set V := regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)
  linear_combination U ^ 2 * hc₀ + z * U * V * hc₁ + z ^ 2 * V ^ 2 * hc₂

/-- Expression of `Ai(z)² + Bi(z)²` in terms of three regularized `₂F₃` functions at `4 z³ / 9`,
indexed by the three residue classes modulo `3` (cf. DLMF 16.12.1). -/
theorem airyAi_sq_add_airyBi_sq_eq_regularizedHGFun (z : ℂ) :
    airyAi z ^ 2 + airyBi z ^ 2 =
      4 * (3 : ℂ) ^ (-4 / 3 : ℂ) * Gamma (1 / 3) *
        regularizedHGFun {1 / 6, 2 / 3} {2 / 3, 2 / 3, 1 / 3} (4 * z ^ 3 / 9) +
      4 * (3 : ℂ) ^ (-2 : ℂ) * z *
        regularizedHGFun {1 / 2, 1} {2 / 3, 4 / 3, 1} (4 * z ^ 3 / 9) +
      4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * Gamma (5 / 3) * z ^ 2 *
        regularizedHGFun {5 / 6, 4 / 3} {4 / 3, 4 / 3, 5 / 3} (4 * z ^ 3 / 9) := by
  have h₀ := regularizedHGFun_zero_singleton_mul (b := (2 / 3 : ℂ)) (c := (2 / 3 : ℂ))
    (Gamma_ne_zero_of_re_pos (by norm_num)) (z ^ 3 / 9)
  have h₁ := regularizedHGFun_zero_singleton_mul (b := (2 / 3 : ℂ)) (c := (4 / 3 : ℂ))
    (Gamma_ne_zero_of_re_pos (by norm_num)) (z ^ 3 / 9)
  have h₂ := regularizedHGFun_zero_singleton_mul (b := (4 / 3 : ℂ)) (c := (4 / 3 : ℂ))
    (Gamma_ne_zero_of_re_pos (by norm_num)) (z ^ 3 / 9)
  norm_num [Gamma_one, mul_div_assoc] at h₀ h₁ h₂
  rw [airyAi_sq_add_airyBi_sq_decomp, h₀, h₁, h₂]
  norm_num [mul_div_assoc]
  ring

/-! ### Gamma duplication–triplication identity for the Maclaurin coefficients -/

private def airyProductTerm (z : ℂ) (m : ℕ) : ℂ :=
  (π : ℂ) ^ (-3 / 2 : ℂ) *
    ((12 : ℂ) ^ (((m : ℂ) + 1 / 2) / 3) * Gamma (((m : ℂ) + 1 / 2) / 3) / (3 * m !)) *
    z ^ m

private theorem airyProduct_rpow_aux (m : ℕ) :
    4 * (3 : ℝ) ^ (-(2 * (m : ℝ) + 4) / 3) * 3 =
      π ^ (-3 / 2 : ℝ) * (12 : ℝ) ^ (((m : ℝ) + 1 / 2) / 3) *
        ((2 : ℝ) ^ (1 - 2 * (((m : ℝ) + 1 / 2) / 3)) * √π) *
        (2 * π * (3 : ℝ) ^ (1 / 2 - 3 * (((m : ℝ) + 1) / 3))) := by
  set s : ℝ := ((m : ℝ) + 1 / 2) / 3
  set t : ℝ := ((m : ℝ) + 1) / 3
  have h12 : (12 : ℝ) ^ s = (2 : ℝ) ^ (2 * s) * (3 : ℝ) ^ s := by
    have h12eq : (12 : ℝ) = (2 : ℝ) ^ (2 : ℝ) * 3 := by norm_num
    rw [h12eq, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul zero_le_two]
  have h2 : (2 : ℝ) ^ (2 * s) * (2 : ℝ) ^ (1 - 2 * s) * 2 = 4 := by
    rw [← Real.rpow_add two_pos]
    norm_num
  have hπ : π ^ (-3 / 2 : ℝ) * √π * π = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos, ← Real.rpow_add_one Real.pi_ne_zero]
    norm_num
  have h3exp : -(2 * (m : ℝ) + 4) / 3 + 1 = s + (1 / 2 - 3 * t) := by ring
  have h3pow : (3 : ℝ) ^ (-(2 * (m : ℝ) + 4) / 3) * 3 =
      (3 : ℝ) ^ s * (3 : ℝ) ^ (1 / 2 - 3 * t) := by
    rw [← Real.rpow_add_one (by positivity), ← Real.rpow_add three_pos, h3exp]
  calc 4 * (3 : ℝ) ^ (-(2 * (m : ℝ) + 4) / 3) * 3
      = 4 * ((3 : ℝ) ^ s * (3 : ℝ) ^ (1 / 2 - 3 * t)) * 1 := by rw [← h3pow]; ring
    _ = ((2 : ℝ) ^ (2 * s) * (2 : ℝ) ^ (1 - 2 * s) * 2) *
          ((3 : ℝ) ^ s * (3 : ℝ) ^ (1 / 2 - 3 * t)) *
          (π ^ (-3 / 2 : ℝ) * √π * π) := by rw [h2, hπ]
    _ = π ^ (-3 / 2 : ℝ) * (12 : ℝ) ^ s * ((2 : ℝ) ^ (1 - 2 * s) * √π) *
          (2 * π * (3 : ℝ) ^ (1 / 2 - 3 * t)) := by rw [h12]; ring

private theorem airyProductCoeff_real (m : ℕ) :
    4 * (3 : ℝ) ^ (-(2 * (m : ℝ) + 4) / 3) * Real.Gamma ((2 * (m : ℝ) + 1) / 3) /
      (Real.Gamma (((m : ℝ) + 2) / 3) *
        (Real.Gamma (((m : ℝ) + 1) / 3) * Real.Gamma (((m : ℝ) + 2) / 3) *
          Real.Gamma (((m : ℝ) + 3) / 3))) =
      π ^ (-3 / 2 : ℝ) * (12 : ℝ) ^ (((m : ℝ) + 1 / 2) / 3) *
        Real.Gamma (((m : ℝ) + 1 / 2) / 3) / (3 * m !) := by
  set s : ℝ := ((m : ℝ) + 1 / 2) / 3
  set t : ℝ := ((m : ℝ) + 1) / 3
  have hs2 : (2 * (m : ℝ) + 1) / 3 = 2 * s := by ring
  have hsh : ((m : ℝ) + 2) / 3 = s + 1 / 2 := by ring
  have ht1' : ((m : ℝ) + 2) / 3 = t + 1 / 3 := by ring
  have ht2 : ((m : ℝ) + 3) / 3 = t + 2 / 3 := by ring
  have ht3 : 3 * t = (m : ℝ) + 1 := by ring
  have hdup := Real.Gamma_mul_Gamma_add_half s
  have htri : Real.Gamma t * Real.Gamma (t + 1 / 3) * Real.Gamma (t + 2 / 3) =
      2 * π * (3 : ℝ) ^ (1 / 2 - 3 * t) * m ! := by
    have hp := Real.prod_Gamma_add_div (m := 3) (by norm_num) t
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one, zero_div, add_zero] at hp
    have hexp : ((3 : ℝ) - 1) / 2 = 1 := by norm_num
    have hGm : Real.Gamma (3 * t) = m ! := by rw [ht3, Real.Gamma_nat_eq_factorial]
    rw [hexp, Real.rpow_one, hGm] at hp
    exact hp
  have hd₁ : 0 < Real.Gamma (s + 1 / 2) *
      (Real.Gamma t * Real.Gamma (t + 1 / 3) * Real.Gamma (t + 2 / 3)) :=
    mul_pos (Real.Gamma_pos_of_pos (by positivity))
      (mul_pos (mul_pos (Real.Gamma_pos_of_pos (by positivity))
        (Real.Gamma_pos_of_pos (by positivity))) (Real.Gamma_pos_of_pos (by positivity)))
  rw [hs2, ht2]
  nth_rw 1 [hsh]
  rw [ht1', div_eq_div_iff hd₁.ne' (by positivity), htri]
  linear_combination
    -π ^ (-3 / 2 : ℝ) * (12 : ℝ) ^ s * (2 * π * (3 : ℝ) ^ (1 / 2 - 3 * t) * m !) * hdup +
      Real.Gamma (2 * s) * m ! * airyProduct_rpow_aux m

private theorem subseries_term_eq {b c : ℝ} (hu : 0 < b + c - 1) (r k : ℕ) (z : ℂ) :
    4 * (3 : ℂ) ^ (-(2 * (r : ℂ) + 4) / 3) * z ^ r *
        ((ascPochhammer ℂ k).eval ((b : ℂ) + c + k - 1) * (z ^ 3 / 9) ^ k /
          (k ! * Gamma (b + k) * Gamma (c + k))) =
      Complex.ofReal
        (4 * (3 : ℝ) ^ (-(2 * ((k * 3 + r : ℕ) : ℝ) + 4) / 3) *
          Real.Gamma (b + c + 2 * k - 1) /
          (k ! * Real.Gamma (b + c + k - 1) * Real.Gamma (b + k) * Real.Gamma (c + k))) *
        z ^ (k * 3 + r) := by
  have heval : (ascPochhammer ℂ k).eval ((b : ℂ) + c + k - 1) =
      Complex.ofReal (Real.Gamma (b + c + 2 * k - 1) / Real.Gamma (b + c + k - 1)) := by
    have hre : 0 < ((b : ℂ) + c + k - 1).re := by simp; linarith [Nat.cast_nonneg (α := ℝ) k]
    rw [← Gamma_add_nat_div_Gamma_eq _ (ne_neg_natCast_of_re_pos hre)]
    have ha₁ : (b : ℂ) + c + k - 1 + k = ((b + c + 2 * k - 1 : ℝ) : ℂ) := by push_cast; ring
    have ha₂ : (b : ℂ) + c + k - 1 = ((b + c + k - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [ha₁, ha₂, Gamma_ofReal, Gamma_ofReal, ← ofReal_div]
  have h3r : (3 : ℂ) ^ (-(2 * (r : ℂ) + 4) / 3) * ((9 : ℂ) ^ k)⁻¹ =
      Complex.ofReal ((3 : ℝ) ^ (-(2 * ((k * 3 + r : ℕ) : ℝ) + 4) / 3)) := by
    have h9 : ((9 : ℝ) ^ k)⁻¹ = (3 : ℝ) ^ (-2 * (k : ℝ)) := by
      have h9eq : (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [← Real.rpow_natCast, h9eq, ← Real.rpow_mul (by positivity),
        ← Real.rpow_neg (by positivity)]
      ring_nf
    have hexp : -(2 * (r : ℝ) + 4) / 3 + (-2 * (k : ℝ)) =
        -(2 * ((k * 3 + r : ℕ) : ℝ) + 4) / 3 := by push_cast; ring
    rw [← hexp, Real.rpow_add three_pos, ofReal_mul, ofReal_cpow (by positivity), ← h9]
    push_cast; rfl
  have hzb : (b : ℂ) + k = ((b + k : ℝ) : ℂ) := by push_cast; ring
  have hzc : (c : ℂ) + k = ((c + k : ℝ) : ℂ) := by push_cast; ring
  have hpowz : z ^ r * (z ^ 3) ^ k = z ^ (k * 3 + r) := by
    rw [← pow_mul, mul_comm 3 k, ← pow_add, add_comm]
  rw [heval, hzb, hzc, Gamma_ofReal, Gamma_ofReal, div_pow, div_eq_mul_inv ((z ^ 3) ^ k)]
  calc 4 * (3 : ℂ) ^ (-(2 * (r : ℂ) + 4) / 3) * z ^ r *
        (Complex.ofReal (Real.Gamma (b + c + 2 * k - 1) / Real.Gamma (b + c + k - 1)) *
          ((z ^ 3) ^ k * ((9 : ℂ) ^ k)⁻¹) /
          (k ! * Complex.ofReal (Real.Gamma (b + k)) * Complex.ofReal (Real.Gamma (c + k))))
      = 4 * ((3 : ℂ) ^ (-(2 * (r : ℂ) + 4) / 3) * ((9 : ℂ) ^ k)⁻¹) *
          (Complex.ofReal (Real.Gamma (b + c + 2 * k - 1) / Real.Gamma (b + c + k - 1)) /
            Complex.ofReal (k ! * Real.Gamma (b + k) * Real.Gamma (c + k))) *
          (z ^ r * (z ^ 3) ^ k) := by push_cast; ring
    _ = Complex.ofReal
          (4 * (3 : ℝ) ^ (-(2 * ((k * 3 + r : ℕ) : ℝ) + 4) / 3) *
            Real.Gamma (b + c + 2 * k - 1) /
            (k ! * Real.Gamma (b + c + k - 1) * Real.Gamma (b + k) * Real.Gamma (c + k))) *
          z ^ (k * 3 + r) := by
        rw [h3r, hpowz]; push_cast; simp only [div_eq_mul_inv, mul_inv]; ring

private theorem ofReal_airyProductCoeff (z : ℂ) (m : ℕ) :
    Complex.ofReal (π ^ (-3 / 2 : ℝ) * (12 : ℝ) ^ (((m : ℝ) + 1 / 2) / 3) *
      Real.Gamma (((m : ℝ) + 1 / 2) / 3) / (3 * m !)) * z ^ m = airyProductTerm z m := by
  unfold airyProductTerm
  rw [ofReal_div, ofReal_mul, ofReal_mul, ofReal_cpow Real.pi_pos.le,
    ofReal_cpow (by positivity), ← Gamma_ofReal]
  push_cast
  ring

private theorem airyProduct_term_mul_three (k : ℕ) (z : ℂ) :
    4 * (3 : ℂ) ^ (-4 / 3 : ℂ) *
      ((ascPochhammer ℂ k).eval ((2 / 3 : ℂ) + 2 / 3 + k - 1) * (z ^ 3 / 9) ^ k /
        (k ! * Gamma (2 / 3 + k) * Gamma (2 / 3 + k))) = airyProductTerm z (k * 3 + 0) := by
  have hs := subseries_term_eq (b := 2 / 3) (c := 2 / 3) (by norm_num) 0 k z
  have hlhs : 4 * (3 : ℂ) ^ (-4 / 3 : ℂ) *
      ((ascPochhammer ℂ k).eval ((2 / 3 : ℂ) + 2 / 3 + k - 1) * (z ^ 3 / 9) ^ k /
        (k ! * Gamma (2 / 3 + k) * Gamma (2 / 3 + k))) =
      4 * (3 : ℂ) ^ (-(2 * ((0 : ℕ) : ℂ) + 4) / 3) * z ^ 0 *
        ((ascPochhammer ℂ k).eval (((2 / 3 : ℝ) : ℂ) + (2 / 3 : ℝ) + k - 1) * (z ^ 3 / 9) ^ k /
          (k ! * Gamma ((2 / 3 : ℝ) + k) * Gamma ((2 / 3 : ℝ) + k))) := by
    push_cast; norm_num
  rw [hlhs, hs, ← ofReal_airyProductCoeff z (k * 3 + 0), ← airyProductCoeff_real (k * 3 + 0)]
  congr 2
  rw [← Real.Gamma_nat_eq_factorial k]
  have a₁ : (2 / 3 : ℝ) + 2 / 3 + 2 * k - 1 = (2 * ((k * 3 + 0 : ℕ) : ℝ) + 1) / 3 := by
    push_cast; ring
  have a₂ : (k : ℝ) + 1 = (((k * 3 + 0 : ℕ) : ℝ) + 3) / 3 := by push_cast; ring
  have a₃ : (2 / 3 : ℝ) + 2 / 3 + k - 1 = (((k * 3 + 0 : ℕ) : ℝ) + 1) / 3 := by push_cast; ring
  have a₄ : (2 / 3 : ℝ) + k = (((k * 3 + 0 : ℕ) : ℝ) + 2) / 3 := by push_cast; ring
  rw [a₁, a₂, a₃, a₄]; ring

private theorem airyProduct_term_mul_three_add_one (k : ℕ) (z : ℂ) :
    4 * (3 : ℂ) ^ (-2 : ℂ) * z *
      ((ascPochhammer ℂ k).eval ((2 / 3 : ℂ) + 4 / 3 + k - 1) * (z ^ 3 / 9) ^ k /
        (k ! * Gamma (2 / 3 + k) * Gamma (4 / 3 + k))) = airyProductTerm z (k * 3 + 1) := by
  have hs := subseries_term_eq (b := 2 / 3) (c := 4 / 3) (by norm_num) 1 k z
  have hlhs : 4 * (3 : ℂ) ^ (-2 : ℂ) * z *
      ((ascPochhammer ℂ k).eval ((2 / 3 : ℂ) + 4 / 3 + k - 1) * (z ^ 3 / 9) ^ k /
        (k ! * Gamma (2 / 3 + k) * Gamma (4 / 3 + k))) =
      4 * (3 : ℂ) ^ (-(2 * ((1 : ℕ) : ℂ) + 4) / 3) * z ^ 1 *
        ((ascPochhammer ℂ k).eval (((2 / 3 : ℝ) : ℂ) + (4 / 3 : ℝ) + k - 1) * (z ^ 3 / 9) ^ k /
          (k ! * Gamma ((2 / 3 : ℝ) + k) * Gamma ((4 / 3 : ℝ) + k))) := by
    push_cast; norm_num
  rw [hlhs, hs, ← ofReal_airyProductCoeff z (k * 3 + 1), ← airyProductCoeff_real (k * 3 + 1)]
  congr 2
  rw [← Real.Gamma_nat_eq_factorial k]
  have a₁ : (2 / 3 : ℝ) + 4 / 3 + 2 * k - 1 = (2 * ((k * 3 + 1 : ℕ) : ℝ) + 1) / 3 := by
    push_cast; ring
  have a₂ : (k : ℝ) + 1 = (((k * 3 + 1 : ℕ) : ℝ) + 2) / 3 := by push_cast; ring
  have a₃ : (2 / 3 : ℝ) + 4 / 3 + k - 1 = (((k * 3 + 1 : ℕ) : ℝ) + 2) / 3 := by push_cast; ring
  have a₄ : (2 / 3 : ℝ) + k = (((k * 3 + 1 : ℕ) : ℝ) + 1) / 3 := by push_cast; ring
  have a₅ : (4 / 3 : ℝ) + k = (((k * 3 + 1 : ℕ) : ℝ) + 3) / 3 := by push_cast; ring
  rw [a₁, a₂, a₃, a₄, a₅]; ring

private theorem airyProduct_term_mul_three_add_two (k : ℕ) (z : ℂ) :
    4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2 *
      ((ascPochhammer ℂ k).eval ((4 / 3 : ℂ) + 4 / 3 + k - 1) * (z ^ 3 / 9) ^ k /
        (k ! * Gamma (4 / 3 + k) * Gamma (4 / 3 + k))) = airyProductTerm z (k * 3 + 2) := by
  have hs := subseries_term_eq (b := 4 / 3) (c := 4 / 3) (by norm_num) 2 k z
  have hlhs : 4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2 *
      ((ascPochhammer ℂ k).eval ((4 / 3 : ℂ) + 4 / 3 + k - 1) * (z ^ 3 / 9) ^ k /
        (k ! * Gamma (4 / 3 + k) * Gamma (4 / 3 + k))) =
      4 * (3 : ℂ) ^ (-(2 * ((2 : ℕ) : ℂ) + 4) / 3) * z ^ 2 *
        ((ascPochhammer ℂ k).eval (((4 / 3 : ℝ) : ℂ) + (4 / 3 : ℝ) + k - 1) * (z ^ 3 / 9) ^ k /
          (k ! * Gamma ((4 / 3 : ℝ) + k) * Gamma ((4 / 3 : ℝ) + k))) := by
    push_cast; norm_num
  rw [hlhs, hs, ← ofReal_airyProductCoeff z (k * 3 + 2), ← airyProductCoeff_real (k * 3 + 2)]
  congr 2
  rw [← Real.Gamma_nat_eq_factorial k]
  have a₁ : (4 / 3 : ℝ) + 4 / 3 + 2 * k - 1 = (2 * ((k * 3 + 2 : ℕ) : ℝ) + 1) / 3 := by
    push_cast; ring
  have a₂ : (k : ℝ) + 1 = (((k * 3 + 2 : ℕ) : ℝ) + 1) / 3 := by push_cast; ring
  have a₃ : (4 / 3 : ℝ) + 4 / 3 + k - 1 = (((k * 3 + 2 : ℕ) : ℝ) + 3) / 3 := by push_cast; ring
  have a₄ : (4 / 3 : ℝ) + k = (((k * 3 + 2 : ℕ) : ℝ) + 2) / 3 := by push_cast; ring
  rw [a₁, a₂, a₃, a₄]; ring

private theorem hasSum_airyAi_sq_add_airyBi_sq_blocks (z : ℂ) :
    HasSum (fun k : ℕ => ∑ r : Fin 3, airyProductTerm z (k * 3 + r))
      (airyAi z ^ 2 + airyBi z ^ 2) := by
  have h₀ := (hasSum_regularizedHGFun_zero_singleton_mul (2 / 3) (2 / 3) (z ^ 3 / 9)).mul_left
    (4 * (3 : ℂ) ^ (-4 / 3 : ℂ))
  have h₁ := (hasSum_regularizedHGFun_zero_singleton_mul (2 / 3) (4 / 3) (z ^ 3 / 9)).mul_left
    (4 * (3 : ℂ) ^ (-2 : ℂ) * z)
  have h₂ := (hasSum_regularizedHGFun_zero_singleton_mul (4 / 3) (4 / 3) (z ^ 3 / 9)).mul_left
    (4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2)
  rw [airyAi_sq_add_airyBi_sq_decomp]
  refine ((h₀.add h₁).add h₂).congr_fun fun k => ?_
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [← airyProduct_term_mul_three, ← airyProduct_term_mul_three_add_one,
    ← airyProduct_term_mul_three_add_two]

/-! ### Bochner integrability and termwise Gamma integration -/

/-- For every `z : ℂ`, the integrand `t ↦ exp(z t - t³ / 12) t^{-1/2}` of DLMF 9.11.4 is Bochner
integrable on `(0, ∞)`. -/
theorem integrableOn_cexp_mul_sub_div_mul_cpow_Ioi (z : ℂ) :
    IntegrableOn (fun t : ℝ => cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (Ioi 0) := by
  have hg : IntegrableOn
      (fun t : ℝ => Real.exp (z.re ^ 2 / 2 + 11) *
        (t ^ (-1 / 2 : ℝ) * Real.exp (-(1 / 24 : ℝ) * t ^ (3 : ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ContinuousAt.continuousWithinAt ?_)
      measurableSet_Ioi
    refine ContinuousAt.mul (by fun_prop) ?_
    exact (continuousAt_cpow_const (ofReal_mem_slitPlane.mpr ht)).comp
      continuous_ofReal.continuousAt
  refine hg.mono' hmeas ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) => ?_)
  have hre : (z * t - (t : ℂ) ^ 3 / 12).re = z.re * t - t ^ 3 / 12 := by
    simp [sub_re, mul_re, div_ofNat_re, pow_three]
  have hcub : z.re * t - t ^ 3 / 12 ≤ (z.re ^ 2 / 2 + 11) + (-(1 / 24 : ℝ) * t ^ 3) := by
    have h₁ : 0 ≤ (t - 8) ^ 2 * (t + 4) := by positivity
    have h₂ : 0 ≤ (z.re - t) ^ 2 := sq_nonneg _
    linarith
  rw [norm_mul, norm_exp, hre, norm_cpow_eq_rpow_re_of_pos ht]
  have hhalf : (-1 / 2 : ℂ).re = -1 / 2 := by norm_num
  rw [hhalf, Real.rpow_ofNat]
  calc Real.exp (z.re * t - t ^ 3 / 12) * t ^ (-1 / 2 : ℝ)
      ≤ Real.exp ((z.re ^ 2 / 2 + 11) + (-(1 / 24 : ℝ) * t ^ 3)) * t ^ (-1 / 2 : ℝ) := by gcongr
    _ = Real.exp (z.re ^ 2 / 2 + 11) * (t ^ (-1 / 2 : ℝ) * Real.exp (-(1 / 24 : ℝ) * t ^ 3)) := by
      rw [Real.exp_add]; ring

private theorem integral_airyProductSeriesTerm (z : ℂ) (m : ℕ) :
    (π : ℂ) ^ (-3 / 2 : ℂ) *
      (∫ t in Ioi (0 : ℝ), (z ^ m / m !) *
        Complex.ofReal (t ^ ((m : ℝ) - 1 / 2) * Real.exp (-(1 / 12 : ℝ) * t ^ (3 : ℝ)))) =
      airyProductTerm z m := by
  have hint := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 3) (q := (m : ℝ) - 1 / 2)
    (b := 1 / 12) (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by norm_num)
  have hq : ((m : ℝ) - 1 / 2 + 1) / 3 = ((m : ℝ) + 1 / 2) / 3 := by ring
  have hb : (1 / 12 : ℝ) ^ (-((m : ℝ) - 1 / 2 + 1) / 3) =
      (12 : ℝ) ^ (((m : ℝ) + 1 / 2) / 3) := by
    have hinv : (1 / 12 : ℝ) = (12 : ℝ)⁻¹ := by norm_num
    have hexp : -((m : ℝ) - 1 / 2 + 1) / 3 = -(((m : ℝ) + 1 / 2) / 3) := by ring
    rw [hinv, hexp, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  have hr : IntegrableOn
      (fun t : ℝ => t ^ ((m : ℝ) - 1 / 2) * Real.exp (-(1 / 12 : ℝ) * t ^ (3 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by norm_num) (by norm_num)
  have hof : (∫ t in Ioi (0 : ℝ),
        Complex.ofReal (t ^ ((m : ℝ) - 1 / 2) * Real.exp (-(1 / 12 : ℝ) * t ^ (3 : ℝ)))) =
      Complex.ofReal
        (∫ t in Ioi (0 : ℝ), t ^ ((m : ℝ) - 1 / 2) * Real.exp (-(1 / 12 : ℝ) * t ^ (3 : ℝ))) :=
    Complex.ofRealCLM.integral_comp_comm hr
  rw [integral_const_mul, hof, hint, hb, hq]
  unfold airyProductTerm
  rw [ofReal_mul, ofReal_mul, ofReal_cpow (by positivity), ← Gamma_ofReal]
  push_cast
  ring

private theorem hasSum_airyProductSeriesBound (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasSum
      (fun m : ℕ => (‖z‖ ^ m / m !) *
        (t ^ ((m : ℝ) - 1 / 2) * Real.exp (-(1 / 12 : ℝ) * t ^ (3 : ℝ))))
      (Real.exp (‖z‖ * t - t ^ 3 / 12) * t ^ (-1 / 2 : ℝ)) := by
  have hexp_r := NormedSpace.expSeries_div_hasSum_exp (‖z‖ * t)
  rw [← Real.exp_eq_exp_ℝ] at hexp_r
  have h := hexp_r.mul_right (Real.exp (-(t ^ 3 / 12)) * t ^ (-1 / 2 : ℝ))
  have hsum : Real.exp (‖z‖ * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ (-1 / 2 : ℝ)) =
      Real.exp (‖z‖ * t - t ^ 3 / 12) * t ^ (-1 / 2 : ℝ) := by
    rw [← mul_assoc, ← Real.exp_add, sub_eq_add_neg]
  rw [hsum] at h
  refine h.congr_fun fun m => ?_
  have hexp_arg : -(1 / 12 : ℝ) * t ^ 3 = -(t ^ 3 / 12) := by ring
  simp only [mul_pow, Real.rpow_ofNat, hexp_arg, sub_eq_add_neg, Real.rpow_add ht,
    Real.rpow_natCast, neg_div]
  ring

private theorem hasSum_airyProductSeriesIntegrand (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasSum
      (fun m : ℕ => (z ^ m / m !) *
        Complex.ofReal (t ^ ((m : ℝ) - 1 / 2) * Real.exp (-(1 / 12 : ℝ) * t ^ (3 : ℝ))))
      (cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) := by
  have hexp_c := NormedSpace.expSeries_div_hasSum_exp (z * t)
  rw [← Complex.exp_eq_exp_ℂ] at hexp_c
  have h := hexp_c.mul_right (cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ (-1 / 2 : ℂ))
  have hsum : cexp (z * t) * (cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ (-1 / 2 : ℂ)) =
      cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) := by
    rw [← mul_assoc, ← Complex.exp_add, sub_eq_add_neg]
  rw [hsum] at h
  refine h.congr_fun fun m => ?_
  have hcpow : (t : ℂ) ^ (-1 / 2 : ℂ) = Complex.ofReal (t ^ (-1 / 2 : ℝ)) := by
    simpa using (ofReal_cpow ht.le (-1 / 2 : ℝ)).symm
  have hexp : cexp (-((t : ℂ) ^ 3 / 12)) =
      Complex.ofReal (Real.exp (-(1 / 12 : ℝ) * t ^ (3 : ℝ))) := by
    rw [Real.rpow_ofNat, ofReal_exp]
    congr 1; push_cast; ring
  have hpow_r : t ^ ((m : ℝ) - 1 / 2) = t ^ m * t ^ (-1 / 2 : ℝ) := by
    rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_natCast, neg_div]
  rw [mul_pow, hcpow, hexp, hpow_r, ofReal_mul, ofReal_mul, ofReal_pow]
  ring

private theorem hasSum_airyProductTerm_integral (z : ℂ) :
    HasSum (airyProductTerm z)
      ((π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) := by
  set F : ℕ → ℝ → ℂ := fun m t => (z ^ m / m !) *
    Complex.ofReal (t ^ ((m : ℝ) - 1 / 2) * Real.exp (-(1 / 12 : ℝ) * t ^ (3 : ℝ)))
  set bound : ℕ → ℝ → ℝ := fun m t => (‖z‖ ^ m / m !) *
    (t ^ ((m : ℝ) - 1 / 2) * Real.exp (-(1 / 12 : ℝ) * t ^ (3 : ℝ)))
  have hF_meas (m : ℕ) : AEStronglyMeasurable (F m) (volume.restrict (Ioi 0)) := by
    have hr : IntegrableOn
        (fun t : ℝ => t ^ ((m : ℝ) - 1 / 2) * Real.exp (-(1 / 12 : ℝ) * t ^ (3 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by norm_num) (by norm_num)
    exact ((Complex.ofRealCLM.integrable_comp hr).const_mul (z ^ m / m !)).aestronglyMeasurable
  have h_bound (m : ℕ) : ∀ᵐ t ∂volume.restrict (Ioi 0), ‖F m t‖ ≤ bound m t :=
    (ae_restrict_mem measurableSet_Ioi).mono fun t (_ : 0 < t) => by
      have hpos : 0 ≤ t ^ ((m : ℝ) - 1 / 2) * Real.exp (-(1 / 12 : ℝ) * t ^ (3 : ℝ)) := by
        positivity
      dsimp only [F, bound]
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
        Real.norm_of_nonneg hpos]
  have h_dom : IntegrableOn (fun t : ℝ => ∑' m, bound m t) (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_cexp_mul_sub_div_mul_cpow_Ioi (‖z‖ : ℂ)).norm
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    have hre : ((‖z‖ : ℂ) * t - (t : ℂ) ^ 3 / 12).re = ‖z‖ * t - t ^ 3 / 12 := by
      simp [sub_re, mul_re, div_ofNat_re, pow_three]
    have hhalf : (-1 / 2 : ℂ).re = -1 / 2 := by norm_num
    rw [(hasSum_airyProductSeriesBound z ht).tsum_eq, norm_mul, norm_exp, hre,
      norm_cpow_eq_rpow_re_of_pos ht, hhalf]
  have hdom_sum := MeasureTheory.hasSum_integral_of_dominated_convergence bound hF_meas h_bound
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ ht =>
      (hasSum_airyProductSeriesBound z ht).summable)
    h_dom ((ae_restrict_mem measurableSet_Ioi).mono fun _ ht =>
      hasSum_airyProductSeriesIntegrand z ht)
  exact (hdom_sum.mul_left ((π : ℂ) ^ (-3 / 2 : ℂ))).congr_fun fun m =>
    (integral_airyProductSeriesTerm z m).symm

/-! ### Main theorems: DLMF 9.11.4, Maclaurin series, and value at `0` -/

/-- **DLMF 9.11.4: integral representation of `Ai(z)² + Bi(z)²`.**
For every `z : ℂ`,
`Ai(z)² + Bi(z)² = π^{-3/2} ∫₀^∞ exp(z t - t³ / 12) t^{-1/2} dt`. -/
theorem airyAi_sq_add_airyBi_sq_eq_integral (z : ℂ) :
    airyAi z ^ 2 + airyBi z ^ 2 =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) := by
  have hblocks : HasSum (fun k : ℕ => ∑ r : Fin 3, airyProductTerm z (k * 3 + r))
      ((π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) := by
    simpa [Function.comp_def] using
      ((Nat.divModEquiv 3).symm.hasSum_iff.mpr
        (hasSum_airyProductTerm_integral z)).sum_fiberwise_of_fintype
  exact (hasSum_airyAi_sq_add_airyBi_sq_blocks z).unique hblocks

/-- **Maclaurin series of `Ai(z)² + Bi(z)²`.**
For every `z : ℂ`,
`Ai(z)² + Bi(z)² = ∑_{m=0}^∞ π^{-3/2} (12^{(m + 1/2)/3} Γ((m + 1/2)/3) / (3 m!)) z^m`. -/
theorem hasSum_airyAi_sq_add_airyBi_sq (z : ℂ) :
    HasSum (fun m : ℕ =>
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ((12 : ℂ) ^ (((m : ℂ) + 1 / 2) / 3) * Gamma (((m : ℂ) + 1 / 2) / 3) / (3 * m !)) *
        z ^ m)
      (airyAi z ^ 2 + airyBi z ^ 2) := by
  rw [airyAi_sq_add_airyBi_sq_eq_integral]
  exact hasSum_airyProductTerm_integral z

/-- Evaluation of DLMF 9.11.4 at `z = 0`:
`4 Ai(0)² = π^{-3/2} 12^{1/6} Γ(1/6) / 3`. -/
theorem four_mul_airyAi_zero_sq :
    4 * airyAi 0 ^ 2 =
      (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ (1 / 6 : ℂ) * Gamma (1 / 6) / 3 := by
  have hsum : airyAi 0 ^ 2 + airyBi 0 ^ 2 =
      (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ (1 / 6 : ℂ) * Gamma (1 / 6) / 3 := by
    have h0 : HasSum (airyProductTerm 0) (airyProductTerm 0 0) :=
      hasSum_single 0 fun m hm => by simp [airyProductTerm, zero_pow hm]
    have hval := (hasSum_airyAi_sq_add_airyBi_sq 0).unique h0
    rw [hval]
    unfold airyProductTerm
    norm_num [mul_div_assoc]
    ring
  have hBi : airyAi 0 ^ 2 + airyBi 0 ^ 2 = 4 * airyAi 0 ^ 2 := by
    have h3 : ((3 : ℂ) ^ (-1 / 6 : ℂ)) ^ 2 = 3 * ((3 : ℂ) ^ (-2 / 3 : ℂ)) ^ 2 := by
      have hne : (3 : ℂ) ≠ 0 := by norm_num
      have h₁ : (-1 / 6 : ℂ) + (-1 / 6 : ℂ) = 1 + ((-2 / 3 : ℂ) + (-2 / 3 : ℂ)) := by norm_num
      rw [sq, sq, ← cpow_add _ _ hne, ← cpow_add _ _ hne, h₁, cpow_add _ _ hne, cpow_one]
    rw [airyAi_zero, airyBi_zero, div_pow, div_pow, h3]
    ring
  rw [← hBi, hsum]

end TauCeti
