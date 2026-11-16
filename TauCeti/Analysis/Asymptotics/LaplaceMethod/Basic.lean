/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.Analysis.Contour.Residue.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.PowerSeries.Binomial
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Laplace coefficients and their residue representation

This file defines the Laplace coefficients `Asymptotics.laplaceCoeff` arising in Laplace's method
(DLMF §2.3(iii), formulas 2.3.15–2.3.18; Olver 1997, Chapter 3, §7), establishes their basic
linearity and branch-shift properties, proves the explicit low-order formulas for `b₀`, `b₁`, and
`b₂` (DLMF 2.3.17), and proves the holomorphic residue representation (DLMF 2.3.18).

The local inversion expansion (DLMF 2.3.16) is in
`TauCeti.Analysis.Asymptotics.LaplaceMethod.LocalInverse`, and the integral asymptotics on
`(a, ∞)` and `(a, b)` (DLMF 2.3.13–2.3.15) are in
`TauCeti.Analysis.Asymptotics.LaplaceMethod.RealLine`.

## Main definitions

* `Asymptotics.laplaceCoeff`: the Laplace coefficients
  `bₛ = μ⁻¹ [Xˢ] (Q * P^{-(λ + s)/μ})` (DLMF 2.3.15–2.3.17), with branch fixed by a logarithm `ℓ`
  of the constant term of `P`.

## Main results

* `Asymptotics.laplaceCoeff_zero`, `Asymptotics.laplaceCoeff_one`, `Asymptotics.laplaceCoeff_two`:
  explicit formulas for `b₀`, `b₁`, `b₂` (DLMF 2.3.17).
* `Asymptotics.laplaceCoeff_one_left`, `Asymptotics.laplaceCoeff_one_one`: specialization to
  `P = 1` and `P = Q = 1`.
* `Asymptotics.laplaceCoeff_add_two_pi_mul_I`: monodromy under shifting the logarithm `ℓ` by
  `2πi`.
* `Asymptotics.laplaceCoeff_eq_residue`: residue representation
  `bₛ = μ⁻¹ res_{t = a} [(t - a)^{-s - 1} Q̂(t) exp(-(λ + s) L(t) / μ)]` for holomorphic data
  with local logarithm `L` (DLMF 2.3.18).

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.3(iii),
  <https://dlmf.nist.gov/2.3.iii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 3, §7.
-/

public section

noncomputable section

open Complex Filter Topology PowerSeries
open scoped Real Nat

namespace Asymptotics

private theorem constantCoeff_C_cexp_neg_mul_sub_one {ℓ : ℂ} {P : ℂ⟦X⟧}
    (hP : constantCoeff P = cexp ℓ) :
    constantCoeff (C (cexp (-ℓ)) * P - 1) = 0 := by
  rw [map_sub, map_mul, constantCoeff_C, hP, map_one, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, sub_self]

/-! ### The Laplace coefficients `laplaceCoeff` (DLMF 2.3.15–2.3.17) -/

/-- The Laplace coefficients `bₛ = μ⁻¹ [Xˢ] (Q * P^{-(λ + s)/μ})` appearing in Laplace's method
(DLMF 2.3.15–2.3.18), where `p(t) - p(a) ~ (t - a)^μ P(t - a)`, `q(t) ~ (t - a)^{λ - 1} Q(t - a)`,
and `ℓ` is the chosen logarithm of the constant term of `P`. -/
def laplaceCoeff (μ : ℝ) (lam ℓ : ℂ) (P Q : ℂ⟦X⟧) (s : ℕ) : ℂ :=
  (μ : ℂ)⁻¹ * PowerSeries.coeff s
    (Q * (PowerSeries.C (cexp (-(lam + s) / μ * ℓ)) *
      (PowerSeries.binomialSeries ℂ (-(lam + s) / μ)).subst
        (PowerSeries.C (cexp (-ℓ)) * P - 1)))

/-- Unfolding lemma for `Asymptotics.laplaceCoeff`. -/
theorem laplaceCoeff_def (μ : ℝ) (lam ℓ : ℂ) (P Q : ℂ⟦X⟧) (s : ℕ) :
    laplaceCoeff μ lam ℓ P Q s =
      (μ : ℂ)⁻¹ * PowerSeries.coeff s
        (Q * (PowerSeries.C (cexp (-(lam + s) / μ * ℓ)) *
          (PowerSeries.binomialSeries ℂ (-(lam + s) / μ)).subst
            (PowerSeries.C (cexp (-ℓ)) * P - 1))) := (rfl)

/-- The Laplace coefficients vanish when `Q = 0`. -/
@[simp]
theorem laplaceCoeff_zero_right (μ : ℝ) (lam ℓ : ℂ) (P : ℂ⟦X⟧) (s : ℕ) :
    laplaceCoeff μ lam ℓ P 0 s = 0 := by
  simp [laplaceCoeff_def]

/-- The Laplace coefficients are additive in `Q`. -/
theorem laplaceCoeff_add_right (μ : ℝ) (lam ℓ : ℂ) (P Q₁ Q₂ : ℂ⟦X⟧) (s : ℕ) :
    laplaceCoeff μ lam ℓ P (Q₁ + Q₂) s =
      laplaceCoeff μ lam ℓ P Q₁ s + laplaceCoeff μ lam ℓ P Q₂ s := by
  simp [laplaceCoeff_def, add_mul, map_add, mul_add]

/-- The Laplace coefficients are `ℂ`-homogeneous in `Q`. -/
theorem laplaceCoeff_C_mul_right (μ : ℝ) (lam ℓ c : ℂ) (P Q : ℂ⟦X⟧) (s : ℕ) :
    laplaceCoeff μ lam ℓ P (C c * Q) s = c * laplaceCoeff μ lam ℓ P Q s := by
  simp only [laplaceCoeff_def, mul_assoc, coeff_C_mul]
  ring

/-- Shifting the logarithm `ℓ` of `constantCoeff P` by `2πi` multiplies the `s`-th Laplace
coefficient by `exp (-((λ + s) / μ) * 2πi)`. -/
theorem laplaceCoeff_add_two_pi_mul_I (μ : ℝ) (lam ℓ : ℂ) (P Q : ℂ⟦X⟧) (s : ℕ) :
    laplaceCoeff μ lam (ℓ + 2 * π * I) P Q s =
      cexp (-(lam + s) / μ * (2 * π * I)) * laplaceCoeff μ lam ℓ P Q s := by
  have hneg : cexp (-(ℓ + 2 * π * I)) = cexp (-ℓ) := by
    rw [neg_add, Complex.exp_add, Complex.exp_neg (2 * π * I), exp_two_pi_mul_I, inv_one, mul_one]
  rw [laplaceCoeff_def, laplaceCoeff_def, hneg, mul_add, Complex.exp_add, map_mul C]
  have hre :
      Q * (C (cexp (-(lam + ↑s) / ↑μ * ℓ)) * C (cexp (-(lam + ↑s) / ↑μ * (2 * ↑π * I))) *
        (binomialSeries ℂ (-(lam + ↑s) / ↑μ)).subst (C (cexp (-ℓ)) * P - 1)) =
      C (cexp (-(lam + ↑s) / ↑μ * (2 * ↑π * I))) *
        (Q * (C (cexp (-(lam + ↑s) / ↑μ * ℓ)) *
          (binomialSeries ℂ (-(lam + ↑s) / ↑μ)).subst (C (cexp (-ℓ)) * P - 1))) := by ring
  rw [hre, coeff_C_mul]
  ring

/-- When `P = 1` with `ℓ = 0`, the Laplace coefficients are simply `μ⁻¹ * coeff s Q`. -/
@[simp]
theorem laplaceCoeff_one_left (μ : ℝ) (lam : ℂ) (Q : ℂ⟦X⟧) (s : ℕ) :
    laplaceCoeff μ lam 0 1 Q s = (μ : ℂ)⁻¹ * coeff s Q := by
  rw [laplaceCoeff_def]
  simp [subst_zero_eq_C_constantCoeff]

/-- Check for `P = 1`, `Q = 1`, `ℓ = 0`: `b₀ = μ⁻¹` and `bₛ = 0` for `s ≥ 1`. -/
theorem laplaceCoeff_one_one (μ : ℝ) (lam : ℂ) (s : ℕ) :
    laplaceCoeff μ lam 0 1 1 s = if s = 0 then (μ : ℂ)⁻¹ else 0 := by
  rw [laplaceCoeff_one_left, coeff_one]
  split_ifs <;> simp

/-- DLMF 2.3.17: explicit formula for `b₀`. -/
theorem laplaceCoeff_zero {μ : ℝ} {lam ℓ : ℂ} {P Q : ℂ⟦X⟧} (hP : constantCoeff P = cexp ℓ) :
    laplaceCoeff μ lam ℓ P Q 0 =
      constantCoeff Q * cexp (-(lam / μ) * ℓ) / (μ : ℂ) := by
  have hU0 := constantCoeff_C_cexp_neg_mul_sub_one hP
  rw [laplaceCoeff_def, coeff_zero_eq_constantCoeff, map_mul, map_mul, constantCoeff_C,
    constantCoeff_binomialSeries_subst hU0]
  simp only [Nat.cast_zero, add_zero, neg_div, mul_one]
  ring

private theorem coeff_one_binomialSeries_subst {ℓ r : ℂ} {P : ℂ⟦X⟧}
    (hP : constantCoeff P = cexp ℓ) :
    coeff 1 ((binomialSeries ℂ r).subst (C (cexp (-ℓ)) * P - 1)) =
      r * (cexp (-ℓ) * coeff 1 P) := by
  rw [coeff_one_subst (constantCoeff_C_cexp_neg_mul_sub_one hP)]
  simp [mul_comm]

private theorem coeff_two_binomialSeries_subst {ℓ r : ℂ} {P : ℂ⟦X⟧}
    (hP : constantCoeff P = cexp ℓ) :
    coeff 2 ((binomialSeries ℂ r).subst (C (cexp (-ℓ)) * P - 1)) =
      r * (cexp (-ℓ) * coeff 2 P) + r * (r - 1) / 2 * (cexp (-ℓ) * coeff 1 P) ^ 2 := by
  set U : ℂ⟦X⟧ := C (cexp (-ℓ)) * P - 1
  have hU0 : constantCoeff U = 0 := constantCoeff_C_cexp_neg_mul_sub_one hP
  have hU1 : coeff 1 U = cexp (-ℓ) * coeff 1 P := by simp [U]
  have hU2 : coeff 2 U = cexp (-ℓ) * coeff 2 P := by simp [U]
  have hU2_sq : coeff 2 (U ^ 2) = (coeff 1 U) ^ 2 := by
    rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
    simp [coeff_zero_eq_constantCoeff, hU0, sq]
  have hch2 : Ring.choose r 2 = r * (r - 1) / 2 := by
    rw [Ring.choose_eq_smul]
    simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
      Polynomial.smeval_X, Polynomial.smeval_one, Nat.factorial, div_eq_inv_mul]
  have h2ne : (2 : ℕ) ≠ 0 := Nat.succ_ne_zero 1
  rw [coeff_subst_eq_sum_range _ hU0, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [pow_zero, pow_one, binomialSeries_coeff, smul_eq_mul, mul_one, Ring.choose_zero_right,
    Ring.choose_one_right, hch2, coeff_one, h2ne, ite_false, hU2, hU2_sq, hU1]
  ring

/-- DLMF 2.3.17: explicit formula for `b₁`. -/
theorem laplaceCoeff_one {μ : ℝ} (hμ : μ ≠ 0) {lam ℓ : ℂ} {P Q : ℂ⟦X⟧}
    (hP : constantCoeff P = cexp ℓ) :
    laplaceCoeff μ lam ℓ P Q 1 =
      cexp (-((lam + 1) / μ) * ℓ) *
        (coeff 1 Q / μ - (lam + 1) * coeff 1 P * constantCoeff Q / (μ ^ 2 * cexp ℓ)) := by
  have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ
  have hexp : cexp ℓ ≠ 0 := exp_ne_zero ℓ
  have hU0 := constantCoeff_C_cexp_neg_mul_sub_one hP
  rw [laplaceCoeff_def, coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp only [Nat.cast_one, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    coeff_zero_eq_constantCoeff, coeff_C_mul,
    constantCoeff_binomialSeries_subst hU0, coeff_one_binomialSeries_subst hP]
  simp only [Complex.exp_neg, neg_div]
  field_simp [hμc, hexp]
  ring

/-- DLMF 2.3.17: explicit formula for `b₂`. -/
theorem laplaceCoeff_two {μ : ℝ} (hμ : μ ≠ 0) {lam ℓ : ℂ} {P Q : ℂ⟦X⟧}
    (hP : constantCoeff P = cexp ℓ) :
    laplaceCoeff μ lam ℓ P Q 2 =
      cexp (-((lam + 2) / μ) * ℓ) *
        (coeff 2 Q / μ -
          (lam + 2) * (coeff 1 P * coeff 1 Q + coeff 2 P * constantCoeff Q) / (μ ^ 2 * cexp ℓ) +
          (lam + 2) * (lam + μ + 2) * coeff 1 P ^ 2 * constantCoeff Q /
            (2 * μ ^ 3 * cexp ℓ ^ 2)) := by
  have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ
  have hexp : cexp ℓ ≠ 0 := exp_ne_zero ℓ
  have hU0 := constantCoeff_C_cexp_neg_mul_sub_one hP
  rw [laplaceCoeff_def, coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.sum_antidiagonal_succ]
  simp only [Nat.cast_ofNat, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    coeff_zero_eq_constantCoeff, coeff_C_mul,
    constantCoeff_binomialSeries_subst hU0, coeff_one_binomialSeries_subst hP,
    coeff_two_binomialSeries_subst hP]
  simp only [Complex.exp_neg, neg_div]
  field_simp [hμc, hexp]
  ring

/-! ### Residue representation (DLMF 2.3.18) -/

private theorem iteratedDeriv_mul_div_factorial {a : ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) (n : ℕ) :
    iteratedDeriv n (fun t ↦ f t * g t) a / (n.factorial : ℂ) =
      coeff n ((PowerSeries.mk fun k ↦ iteratedDeriv k f a / (k.factorial : ℂ)) *
        (PowerSeries.mk fun k ↦ iteratedDeriv k g a / (k.factorial : ℂ))) := by
  have hmul_fn : (fun t ↦ f t * g t) = f * g := rfl
  rw [hmul_fn, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div, coeff_mul]
  simp only [coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦
    (iteratedDeriv i f a / (i.factorial : ℂ)) * (iteratedDeriv j g a / (j.factorial : ℂ)))]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hch : (n.choose k : ℂ) * (k.factorial : ℂ) * ((n - k).factorial : ℂ) =
      (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]
  rw [← hch]; ring

/-- For a holomorphic logarithm `L` of `Phat` near `a` with `L a = ℓ`, the formal Taylor series of
`t ↦ exp (r * L t)` at `a` equals
`C (exp (r * ℓ)) * (binomialSeries ℂ r).subst (C (exp (-ℓ)) * P - 1)`. -/
private theorem taylor_cexp_mul_eq_binomialSeries_subst {Phat L : ℂ → ℂ} {a ℓ r : ℂ}
    (hL : AnalyticAt ℂ L a) (hexp : ∀ᶠ t in 𝓝 a, cexp (L t) = Phat t) (hLa : L a = ℓ) :
    (PowerSeries.mk fun n ↦ iteratedDeriv n (fun t ↦ cexp (r * L t)) a / (n.factorial : ℂ)) =
      C (cexp (r * ℓ)) * (binomialSeries ℂ r).subst
        (C (cexp (-ℓ)) *
          (PowerSeries.mk fun n ↦ iteratedDeriv n Phat a / (n.factorial : ℂ)) - 1) := by
  let taylor (f : ℂ → ℂ) : ℂ⟦X⟧ :=
    PowerSeries.mk fun n ↦ iteratedDeriv n f a / (n.factorial : ℂ)
  have ht_const : ∀ f : ℂ → ℂ, constantCoeff (taylor f) = f a := fun f ↦ by
    simp [taylor, ← coeff_zero_eq_constantCoeff_apply]
  have ht_congr : ∀ {f g : ℂ → ℂ}, f =ᶠ[𝓝 a] g → taylor f = taylor g := fun h ↦ by
    ext n; simp [taylor, h.iteratedDeriv_eq n]
  have ht_cmul : ∀ (c : ℂ) (f : ℂ → ℂ), taylor (fun t ↦ c * f t) = C c * taylor f := fun c f ↦ by
    ext n; simp only [taylor, coeff_mk, coeff_C_mul, iteratedDeriv_const_mul_field, mul_div_assoc]
  have ht_mul : ∀ {f g : ℂ → ℂ}, AnalyticAt ℂ f a → AnalyticAt ℂ g a →
      taylor (fun t ↦ f t * g t) = taylor f * taylor g := fun hf hg ↦ by
    ext n; rw [coeff_mk]; exact iteratedDeriv_mul_div_factorial hf hg n
  have ht_deriv : ∀ f : ℂ → ℂ, d⁄dX (taylor f) = taylor (deriv f) := fun f ↦ by
    ext n
    simp only [taylor, coeff_derivative, coeff_mk, iteratedDeriv_succ', Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [(by exact_mod_cast Nat.succ_ne_zero n : ((n : ℂ) + 1) ≠ 0)]
  set P : ℂ⟦X⟧ := taylor Phat
  set U : ℂ⟦X⟧ := C (cexp (-ℓ)) * P - 1 with hU_def
  set E : ℂ → ℂ := fun t ↦ cexp (r * L t)
  set S : ℂ⟦X⟧ := C (cexp (r * ℓ)) * (binomialSeries ℂ r).subst U
  set Sinv : ℂ⟦X⟧ := C (cexp ((-r) * ℓ)) * (binomialSeries ℂ (-r)).subst U with hSinv_def
  have hP_an : AnalyticAt ℂ Phat a := (analyticAt_cexp.comp hL).congr hexp
  have hE_an : AnalyticAt ℂ E a := analyticAt_cexp.comp (analyticAt_const.mul hL)
  have hP0 : constantCoeff P = cexp ℓ := by rw [ht_const, ← hexp.self_of_nhds, hLa]
  have hU0 : constantCoeff U = 0 := constantCoeff_C_cexp_neg_mul_sub_one hP0
  have hP_unit : IsUnit P :=
    isUnit_iff_constantCoeff.mpr (by rw [hP0]; exact (exp_ne_zero ℓ).isUnit)
  -- `taylor E` satisfies `Y' * P = C r * Y * P'`.
  have hode_E : d⁄dX (taylor E) * P = C r * taylor E * d⁄dX P := by
    have hE' : deriv E =ᶠ[𝓝 a] fun t ↦ r * E t * deriv L t :=
      hL.eventually_analyticAt.mono fun t ht ↦ by
        rw [(by simpa [E] using (ht.differentiableAt.hasDerivAt.const_mul r).cexp :
          HasDerivAt E (cexp (r * L t) * (r * deriv L t)) t).deriv]; ring
    have hP' : deriv Phat =ᶠ[𝓝 a] fun t ↦ Phat t * deriv L t :=
      (hexp.eventually_nhds.and hL.eventually_analyticAt).mono fun t ⟨hte, ht⟩ ↦ by
        rw [← Filter.EventuallyEq.deriv_eq hte, ht.differentiableAt.hasDerivAt.cexp.deriv,
          hte.self_of_nhds]
    have hmul : (fun t ↦ deriv E t * Phat t) =ᶠ[𝓝 a] fun t ↦ r * (E t * deriv Phat t) :=
      (hE'.and hP').mono fun _ ⟨h1, h2⟩ ↦ by dsimp only; rw [h1, h2]; ring
    rw [ht_deriv, ht_deriv, ← ht_mul hE_an.deriv hP_an, ht_congr hmul, ht_cmul,
      ht_mul hE_an hP_an.deriv, mul_assoc]
  -- `Sinv` satisfies `Sinv' * P = C (-r) * Sinv * P'` and `S * Sinv = 1`.
  have hSSinv : S * Sinv = 1 := by
    have h1 : C (cexp (r * ℓ)) * C (cexp ((-r) * ℓ)) = 1 := by
      rw [← map_mul, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, map_one]
    linear_combination ((binomialSeries ℂ r).subst U * (binomialSeries ℂ (-r)).subst U) * h1 +
      binomialSeries_subst_mul_neg (R := ℂ) (r := r) hU0
  have hSinv' : d⁄dX Sinv * P = C (-r) * Sinv * d⁄dX P := by
    have hdU : d⁄dX U = C (cexp (-ℓ)) * d⁄dX P := by
      rw [hU_def, map_sub, derivative_one, sub_zero,
        Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul]
    have hmul1 : (binomialSeries ℂ (-r - 1)).subst U * (C (cexp (-ℓ)) * P) =
        (binomialSeries ℂ (-r)).subst U := by
      rw [← (by simp [U] : (1 + U : ℂ⟦X⟧) = C (cexp (-ℓ)) * P),
        ← binomialSeries_one_subst (R := ℂ) hU0, ← binomialSeries_add_subst hU0, sub_add_cancel]
    rw [hSinv_def, Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul,
      derivative_binomialSeries_subst hU0, hdU, Algebra.smul_def, algebraMap_eq]
    linear_combination C (-r) * C (cexp ((-r) * ℓ)) * d⁄dX P * hmul1
  -- Therefore `taylor E * Sinv` has zero derivative and constant term `1`, so `taylor E = S`.
  have hZ' : d⁄dX (taylor E * Sinv) = 0 := by
    refine hP_unit.mul_left_eq_zero.mp ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_mul]
    linear_combination taylor E * hSinv' + Sinv * hode_E +
      taylor E * Sinv * d⁄dX P * (map_neg (C (R := ℂ)) r)
  have hZ0 : constantCoeff (taylor E * Sinv) = 1 := by
    rw [map_mul, ht_const, map_mul, constantCoeff_C, constantCoeff_binomialSeries_subst hU0]
    simp [E, hLa, ← Complex.exp_add]
  have hZ : taylor E * Sinv = 1 :=
    PowerSeries.derivative.ext (by rw [hZ', derivative_one]) (by rw [hZ0, map_one])
  linear_combination S * hZ - taylor E * hSSinv

/-- **DLMF 2.3.18 (Residue form of the Laplace coefficients).** If `Phat`, `Qhat`, and `L` are
analytic at `a` with `exp (L t) = Phat t` near `a` and `L a = ℓ`, then the `s`-th Laplace
coefficient of their Taylor series at `a` equals
`μ⁻¹ * res_{t = a} [(t - a)^{-s - 1} Qhat(t) exp(-(λ + s) L(t) / μ)]`. -/
theorem laplaceCoeff_eq_residue {Phat Qhat L : ℂ → ℂ} {a ℓ lam : ℂ} {μ : ℝ} (s : ℕ)
    (hQ : AnalyticAt ℂ Qhat a) (hL : AnalyticAt ℂ L a)
    (hexp : ∀ᶠ t in 𝓝 a, cexp (L t) = Phat t) (hLa : L a = ℓ) :
    laplaceCoeff μ lam ℓ
        (PowerSeries.mk fun n ↦ iteratedDeriv n Phat a / (n.factorial : ℂ))
        (PowerSeries.mk fun n ↦ iteratedDeriv n Qhat a / (n.factorial : ℂ)) s =
      (μ : ℂ)⁻¹ * TauCeti.Contour.residue
        (fun t ↦ (t - a) ^ (-(s : ℤ) - 1) * Qhat t * cexp (-((lam + s) / μ) * L t)) a := by
  set r : ℂ := -(lam + s) / μ
  have hE_an : AnalyticAt ℂ (fun t ↦ cexp (r * L t)) a :=
    analyticAt_cexp.comp (analyticAt_const.mul hL)
  have hg : AnalyticAt ℂ (fun t ↦ Qhat t * cexp (r * L t)) a := hQ.mul hE_an
  have hcongr :
      (fun t ↦ (t - a) ^ (-(s : ℤ) - 1) * Qhat t * cexp (-((lam + s) / μ) * L t))
        =ᶠ[𝓝[≠] a] fun t ↦ (Qhat t * cexp (r * L t)) / (t - a) ^ (s + 1) :=
    Filter.Eventually.of_forall fun t ↦ by
      dsimp only
      rw [(by simp [r, neg_div] : -((lam + s) / μ) = r),
        (by push_cast; ring : -(s : ℤ) - 1 = -((s + 1 : ℕ) : ℤ)),
        zpow_neg, zpow_natCast, div_eq_inv_mul]; ring
  rw [TauCeti.Contour.residue_congr_nhdsNE hcongr,
    TauCeti.Contour.residue_div_sub_pow_of_analyticAt hg s, laplaceCoeff_def]
  congr 1
  rw [iteratedDeriv_mul_div_factorial hQ hE_an s,
    taylor_cexp_mul_eq_binomialSeries_subst (r := r) hL hexp hLa]

end Asymptotics
