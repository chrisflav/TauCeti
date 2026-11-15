/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DedekindSum
public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.Data.Int.MulPred
import TauCeti.Data.Int.Sign
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.RingTheory.Coprime.Lemmas

/-!
# Explicit Dedekind-sum and Kronecker-symbol formulas for the eta multiplier

`TauCeti.ModularForm.etaMultiplier` is the 24th root of unity `ε(γ)` in the transformation law
`η(γ τ) = ε(γ) √(c τ + d) η(τ)` on the upper half-plane, with the principal square root. This file
proves its two classical closed-form evaluations on `SL(2, ℤ)`:

* **Dedekind's formula** (Apostol, Theorem 3.4): for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0`,
  `ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`, where `s(d, c)` is the Dedekind sum
  `TauCeti.dedekindSum d c` (and `-1/4` converts Apostol's branch `√(-i(c τ + d))` to the
  principal root `√(c τ + d)`). Extending through `ε(-γ) = i ε(γ)` gives the companion formula for
  `c < 0` and the unified `c ≠ 0` formula in terms of `sign(c)` and `|c|`.
* **The Kronecker-symbol formula** (Strömberg, Remark 2.5, equation (2.5)): for `γ = (a b; c d)`
  with `c > 0` and `e(x) = exp(2π i x)`,
  * `ε(γ) = (d / c) e(((a + d) c - b d (c² - 1) - 3 c) / 24)` when `c` is odd;
  * `ε(γ) = (c / d) e(((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)` when `c` is even,
  where `(· / ·)` is `TauCeti.kroneckerSym`. Unlike the Dedekind-sum expression, this form makes
  the quadratic Dirichlet character of eta quotients on `Γ₀(N)` explicit.

Combining `ε(γ)²⁴ = 1` with Dedekind's formula yields Rademacher's integrality property that
`(a + d) / c - 12 s(d, c)` is an integer whenever `c > 0` and `γ ∈ SL(2, ℤ)`, and comparing the
two formulas at odd `c > 0` recovers the Dedekind–Jacobi congruence
`12 c s(d, c) ≡ c + 1 - 2 (d / c) (mod 8)` (Rademacher and Grosswald, Chapter 3, Theorem 2).

## Main results

* `TauCeti.ModularForm.etaMultiplier_of_c_pos`, `TauCeti.ModularForm.eta_smul_of_c_pos`:
  Dedekind's formula for `ε(γ)` and `η(γ τ)` when `c > 0`, and
  `TauCeti.ModularForm.etaMultiplier_of_c_pos_eq_cexp_sum_fract`, its unfolded fractional-part
  form over `ℝ`.
* `TauCeti.ModularForm.etaMultiplier_of_c_neg`, `TauCeti.ModularForm.etaMultiplier_of_c_ne_zero`:
  the Dedekind-sum formula for `c < 0` and for arbitrary `c ≠ 0`.
* `TauCeti.ModularForm.exists_int_eq_add_div_sub_twelve_mul_dedekindSum`: integrality of
  `(a + d) / c - 12 s(d, c)` for `γ ∈ SL(2, ℤ)` with `c > 0`.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_c_pos_of_odd`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_c_pos_of_even`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_c_pos`: the Kronecker-symbol formula for
  `c > 0` (odd, even, and unified), with negative-`c` companions
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_c_neg_of_odd` and
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_c_neg_of_even`.
* `TauCeti.exists_int_twelve_mul_dedekindSum_and_modEq_eight`: for coprime `d` and odd `c > 0`,
  `12 c s(d, c)` is an integer congruent to `c + 1 - 2 (d / c)` modulo `8`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., GTM 41,
  Theorem 3.4.
* H. Rademacher and E. Grosswald, *Dedekind Sums*, Carus Mathematical Monographs 16, Chapters 3–4.
* F. Strömberg, *Computation of Maass waveforms with nontrivial multiplier systems*, Math. Comp.
  77 (2008), 2375–2416, Remark 2.5, equation (2.5).
-/

public section

open Complex Finset ModularGroup
open scoped UpperHalfPlane Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Dedekind's formula for the eta multiplier -/

/-- The Dedekind-sum exponential `exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`, used locally in the
Euclidean induction for `etaMultiplier_of_c_pos`. -/
private noncomputable def dedekindExp (γ : SL(2, ℤ)) : ℂ :=
  cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
    TauCeti.dedekindSum (γ 1 1) (γ 1 0) - 1 / 4))

private theorem dedekindExp_mul_T_zpow (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) (n : ℤ) :
    dedekindExp (γ * T ^ n) = cexp (π * I * n / 12) * dedekindExp γ := by
  have hc' : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc
  rw [dedekindExp, dedekindExp, Matrix.SpecialLinearGroup.mul_T_zpow_apply_zero,
    Matrix.SpecialLinearGroup.mul_T_zpow_apply_zero, Matrix.SpecialLinearGroup.mul_T_zpow_apply_one,
    TauCeti.dedekindSum_self_mul_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

private theorem dedekindExp_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1) :
    dedekindExp (γ * S) = cexp (-(π * I / 4)) * dedekindExp γ := by
  have hc' : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
  have hd' : (γ 1 1 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hd.ne'
  -- Dedekind reciprocity matches `(γ S)` against `γ` up to `a d - b c = 1`.
  have hrec := congrArg (Rat.cast : ℚ → ℂ)
    (TauCeti.dedekindSum_add_dedekindSum hd hc (γ.isCoprime_row 1).symm)
  push_cast at hrec
  rw [dedekindExp, dedekindExp, Matrix.SpecialLinearGroup.mul_S_apply_zero,
    Matrix.SpecialLinearGroup.mul_S_apply_zero, Matrix.SpecialLinearGroup.mul_S_apply_one,
    TauCeti.dedekindSum_neg, Rat.cast_neg, sub_neg_eq_add, ← Complex.exp_add]
  congr 1
  have hsum : (TauCeti.dedekindSum (γ 1 0) (γ 1 1) : ℂ) =
      ((γ 1 1 : ℂ) ^ 2 + (γ 1 0 : ℂ) ^ 2 + 1) / (12 * γ 1 1 * γ 1 0) - 1 / 4 -
        TauCeti.dedekindSum (γ 1 1) (γ 1 0) := by
    linear_combination hrec
  rw [Int.cast_neg, hsum]
  field_simp
  linear_combination -4 * γ.intCast_fin_two_mul_sub_mul_eq_one (R := ℂ)

/-- **Dedekind's formula for the eta multiplier** (Apostol, Theorem 3.4): for
`γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0`,
`ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`, where `s(d, c)` is the Dedekind sum
`TauCeti.dedekindSum d c`. -/
theorem etaMultiplier_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ =
      cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
        TauCeti.dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) := by
  suffices ∀ (n : ℕ) (γ : SL(2, ℤ)), 0 < γ 1 0 → (γ 1 0).natAbs = n →
      etaMultiplier γ = dedekindExp γ from this (γ 1 0).natAbs γ hc rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro γ hc hn
    by_cases hc1 : γ 1 0 = 1
    · rw [etaMultiplier_of_c_eq_one γ hc1, dedekindExp, hc1, TauCeti.dedekindSum_one_right]
      simp
    have hc_gt : 1 < γ 1 0 := by omega
    -- Reduce `d` modulo `c` by right translation, then invert by `S` to decrease `c`.
    set q : ℤ := γ 1 1 / γ 1 0
    set γ₁ : SL(2, ℤ) := γ * T ^ (-q)
    have hγ₁_c : γ₁ 1 0 = γ 1 0 := Matrix.SpecialLinearGroup.mul_T_zpow_apply_zero γ (-q) 1
    have hγ₁_d : γ₁ 1 1 = γ 1 1 % γ 1 0 := by
      rw [Matrix.SpecialLinearGroup.mul_T_zpow_apply_one, Int.emod_def]
      ring
    have hd₁_pos : 0 < γ₁ 1 1 := hγ₁_d ▸ (γ.isCoprime_row 1).symm.emod_pos_of_one_lt hc_gt
    have hd₁_lt : γ₁ 1 1 < γ 1 0 := hγ₁_d ▸ Int.emod_lt_of_pos _ hc
    have hS_c : 0 < (γ₁ * S) 1 0 := by rwa [Matrix.SpecialLinearGroup.mul_S_apply_zero]
    have hS_lt : ((γ₁ * S) 1 0).natAbs < n := by
      rw [← hn, Matrix.SpecialLinearGroup.mul_S_apply_zero]
      omega
    have hS_eq := ih ((γ₁ * S) 1 0).natAbs hS_lt (γ₁ * S) hS_c rfl
    rw [etaMultiplier_mul_S γ₁ hd₁_pos, dedekindExp_mul_S γ₁ (hγ₁_c ▸ hc) hd₁_pos] at hS_eq
    have hγ₁_eq : etaMultiplier γ₁ = dedekindExp γ₁ :=
      mul_left_cancel₀ (Complex.exp_ne_zero _) hS_eq
    have hγ_restore : γ = γ₁ * T ^ q := by simp [γ₁, mul_assoc]
    rw [hγ_restore, etaMultiplier_mul_T_zpow, dedekindExp_mul_T_zpow _ (hγ₁_c ▸ hc.ne'), hγ₁_eq]

/-- **Dedekind's functional equation for `η` at `c > 0`** (Apostol, Theorem 3.4):
`η(γ τ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4)) √(c τ + d) η(τ)` on the upper half-plane,
with the principal square root. -/
theorem eta_smul_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ : ℍ) :
    η (γ • τ : ℍ) =
      cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
        TauCeti.dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) *
      Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ := by
  rw [eta_smul, etaMultiplier_of_c_pos γ hc]

/-- Dedekind's formula for `ε(γ)` at `c > 0` with the Dedekind sum written out explicitly in terms
of real fractional parts `Int.fract`. -/
theorem etaMultiplier_of_c_pos_eq_cexp_sum_fract (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ =
      cexp (π * I * (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * γ 1 0) -
        ∑ r ∈ Ioo 0 (γ 1 0), ((r : ℂ) / γ 1 0) *
          (((Int.fract (((γ 1 1 * r : ℤ) : ℝ) / γ 1 0) : ℝ) : ℂ) - 1 / 2) - 1 / 4)) := by
  have hsum : (TauCeti.dedekindSum (γ 1 1) (γ 1 0) : ℂ) =
      ∑ r ∈ Ioo 0 (γ 1 0), ((r : ℂ) / γ 1 0) *
        (((Int.fract (((γ 1 1 * r : ℤ) : ℝ) / γ 1 0) : ℝ) : ℂ) - 1 / 2) := by
    rw [← ofReal_ratCast, (γ.isCoprime_row 1).symm.cast_dedekindSum (α := ℝ)]
    push_cast
    rfl
  rw [etaMultiplier_of_c_pos γ hc, hsum]
  push_cast
  rfl

/-- Dedekind's formula for the eta multiplier when `c < 0`: since `ε(γ) = i ε(-γ)`,
`ε(γ) = exp(π i ((a + d) / (12 c) + s(d, -c) + 1/4))`. -/
theorem etaMultiplier_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier γ =
      cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) +
        TauCeti.dedekindSum (γ 1 1) (-γ 1 0) + 1 / 4)) := by
  have hc' : 0 < (-γ) 1 0 := by simpa using neg_pos.mpr hc
  have hneg : etaMultiplier γ = cexp (π / 2 * I) * etaMultiplier (-γ) := by
    simpa only [exp_pi_div_two_mul_I, neg_neg] using etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [hneg, etaMultiplier_of_c_pos (-γ) hc', ← Complex.exp_add]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, TauCeti.dedekindSum_neg,
    Rat.cast_neg, Int.cast_neg]
  congr 1
  have hc₀ : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne
  field_simp
  ring

/-- Unified Dedekind-sum formula for `ε(γ)` whenever `c ≠ 0` (Rademacher and Grosswald, *Dedekind
Sums*, Chapter 4, equation (69)). -/
theorem etaMultiplier_of_c_ne_zero (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    etaMultiplier γ =
      cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
        (γ 1 0).sign * TauCeti.dedekindSum (γ 1 1) |γ 1 0| - (γ 1 0).sign / 4)) := by
  rcases hc.lt_or_gt with hlt | hgt
  · rw [etaMultiplier_of_c_neg γ hlt, Int.sign_eq_neg_one_of_neg hlt, abs_of_neg hlt]
    push_cast
    ring_nf
  · rw [etaMultiplier_of_c_pos γ hgt, Int.sign_eq_one_of_pos hgt, abs_of_pos hgt]
    push_cast
    ring_nf

/-- **Rademacher's integrality property**: for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0`, the
rational number `(a + d) / c - 12 s(d, c)` is an integer, as `ε(γ)²⁴ = 1`. -/
theorem exists_int_eq_add_div_sub_twelve_mul_dedekindSum (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    ∃ m : ℤ, (m : ℚ) = ((γ 0 0 + γ 1 1 : ℤ) : ℚ) / γ 1 0 -
      12 * TauCeti.dedekindSum (γ 1 1) (γ 1 0) := by
  have h24 := etaMultiplier_pow_twentyFour γ
  rw [etaMultiplier_of_c_pos γ hc, ← Complex.exp_nat_mul] at h24
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h24
  have hrat : ((((n + 3 : ℤ) : ℚ) : ℂ)) =
      ((((γ 0 0 + γ 1 1 : ℤ) : ℚ) / γ 1 0 -
        12 * TauCeti.dedekindSum (γ 1 1) (γ 1 0) : ℚ) : ℂ) := by
    refine mul_right_cancel₀ Complex.two_pi_I_ne_zero ?_
    have hn' : (24 : ℂ) * (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
        TauCeti.dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) = n * (2 * π * I) := by
      simpa using hn
    push_cast
    linear_combination -hn'
  exact ⟨n + 3, Rat.cast_injective hrat⟩

/-! ### The Kronecker-symbol formula for the eta multiplier -/

/-- The integer phase `(a + d) c - b d (c² - 1) - 3 c` in the odd-`c` Kronecker formula. -/
private def kroneckerPhaseOdd (γ : SL(2, ℤ)) : ℤ :=
  (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0

/-- The odd-`c` Kronecker expression for `ε(γ)`, used locally in the Euclidean induction. -/
private noncomputable def kroneckerOddExpr (γ : SL(2, ℤ)) : ℂ :=
  TauCeti.kroneckerSym (γ 1 1) (γ 1 0) * cexp (2 * π * I * (kroneckerPhaseOdd γ : ℂ) / 24)

private theorem kroneckerOddExpr_mul_T_zpow (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hodd : Odd (γ 1 0))
    (n : ℤ) :
    kroneckerOddExpr (γ * T ^ n) = cexp (π * I * n / 12) * kroneckerOddExpr γ := by
  -- Match the Kronecker symbols `(d + c n / c) = (d / c)` via Jacobi periodicity.
  have hsym : TauCeti.kroneckerSym ((γ * T ^ n) 1 1) ((γ * T ^ n) 1 0) =
      TauCeti.kroneckerSym (γ 1 1) (γ 1 0) := by
    rw [Matrix.SpecialLinearGroup.mul_T_zpow_apply_zero,
      Matrix.SpecialLinearGroup.mul_T_zpow_apply_one]
    set c : ℕ := (γ 1 0).toNat
    have hc_eq : (c : ℤ) = γ 1 0 := Int.toNat_of_nonneg hc.le
    have hc_odd : Odd c := (Int.odd_natCast c).mp (hc_eq ▸ hodd)
    rw [← hc_eq, TauCeti.kroneckerSym_eq_jacobiSym _ hc_odd,
      TauCeti.kroneckerSym_eq_jacobiSym _ hc_odd]
    exact jacobiSym.mod_left' (by rw [add_comm, Int.add_mul_emod_self_left])
  -- Match the phase polynomial modulo `24`, using `a d - b c = 1` and `24 ∣ c (c² - 1)`.
  have hphase : kroneckerPhaseOdd (γ * T ^ n) ≡ kroneckerPhaseOdd γ + n [ZMOD 24] := by
    rw [Int.modEq_iff_dvd]
    obtain ⟨k, hk⟩ := Int.twentyFour_dvd_mul_sq_sub_one_of_odd hodd
    refine ⟨k * n * (γ 0 0 * n + 2 * γ 0 1), ?_⟩
    simp only [kroneckerPhaseOdd, Matrix.SpecialLinearGroup.mul_T_zpow_apply_zero,
      Matrix.SpecialLinearGroup.mul_T_zpow_apply_one]
    linear_combination (γ 1 0 ^ 2 - 1) * n * γ.fin_two_mul_sub_mul_eq_one +
      n * (γ 0 0 * n + 2 * γ 0 1) * hk
  have hexp : cexp (2 * π * I * (kroneckerPhaseOdd (γ * T ^ n) : ℂ) / 24) =
      cexp (2 * π * I * ((kroneckerPhaseOdd γ + n : ℤ) : ℂ) / 24) := by
    simpa using Complex.exp_two_pi_mul_I_mul_intCast_div_congr hphase
  rw [kroneckerOddExpr, kroneckerOddExpr, hsym, hexp, mul_left_comm (cexp _), ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem kroneckerOddExpr_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hodd_c : Odd (γ 1 0))
    (hd : 0 < γ 1 1) (hodd_d : Odd (γ 1 1)) :
    kroneckerOddExpr (γ * S) = cexp (-(π * I / 4)) * kroneckerOddExpr γ := by
  set c : ℕ := (γ 1 0).toNat
  set d : ℕ := (γ 1 1).toNat
  have hc_eq : (c : ℤ) = γ 1 0 := Int.toNat_of_nonneg hc.le
  have hd_eq : (d : ℤ) = γ 1 1 := Int.toNat_of_nonneg hd.le
  have hc_odd : Odd c := (Int.odd_natCast c).mp (hc_eq ▸ hodd_c)
  have hd_odd : Odd d := (Int.odd_natCast d).mp (hd_eq ▸ hodd_d)
  -- Quadratic reciprocity and its first supplement relate `(-c / d)` to `(d / c)`.
  have hsym : (TauCeti.kroneckerSym (-γ 1 0) (γ 1 1) : ℂ) =
      ((-1 : ℂ) ^ (d / 2 + c / 2 * (d / 2))) * TauCeti.kroneckerSym (γ 1 1) (γ 1 0) := by
    have hJ : TauCeti.kroneckerSym (-γ 1 0) (γ 1 1) =
        (-1) ^ (d / 2 + c / 2 * (d / 2)) * TauCeti.kroneckerSym (γ 1 1) (γ 1 0) := by
      rw [← hc_eq, ← hd_eq, TauCeti.kroneckerSym_eq_jacobiSym _ hd_odd,
        TauCeti.kroneckerSym_eq_jacobiSym _ hc_odd, jacobiSym.neg _ hd_odd,
        ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hd_odd),
        jacobiSym.quadratic_reciprocity hc_odd hd_odd, ← mul_assoc, ← pow_add]
    exact_mod_cast hJ
  have hc_u : γ 1 0 = 2 * ((c / 2 : ℕ) : ℤ) + 1 := by
    have := Nat.div_add_mod c 2
    have := Nat.odd_iff.mp hc_odd
    omega
  have hd_v : γ 1 1 = 2 * ((d / 2 : ℕ) : ℤ) + 1 := by
    have := Nat.div_add_mod d 2
    have := Nat.odd_iff.mp hd_odd
    omega
  have hsign_phase : (12 * ((d / 2 + c / 2 * (d / 2) : ℕ) : ℤ) : ℤ) =
       3 * (γ 1 0 + 1) * (γ 1 1 - 1) := by
    rw [hc_u, hd_v]
    push_cast
    ring
  -- The quadratic-reciprocity sign and the phase difference cancel identically via `a d - b c = 1`.
  have hpoly : kroneckerPhaseOdd (γ * S) + 3 * (γ 1 0 + 1) * (γ 1 1 - 1) =
      kroneckerPhaseOdd γ - 3 := by
    simp only [kroneckerPhaseOdd, Matrix.SpecialLinearGroup.mul_S_apply_zero,
      Matrix.SpecialLinearGroup.mul_S_apply_one]
    linear_combination -γ 1 0 * γ 1 1 * γ.fin_two_mul_sub_mul_eq_one
  rw [kroneckerOddExpr, kroneckerOddExpr, Matrix.SpecialLinearGroup.mul_S_apply_zero,
    Matrix.SpecialLinearGroup.mul_S_apply_one, hsym, ← exp_pi_mul_I, ← Complex.exp_nat_mul,
    mul_assoc, mul_left_comm (cexp _), ← Complex.exp_add, mul_left_comm (cexp _),
    ← Complex.exp_add]
  congr 2
  have hsign' := congrArg (Int.cast : ℤ → ℂ) hsign_phase
  have hpoly' := congrArg (Int.cast : ℤ → ℂ) hpoly
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_one,
    Int.cast_ofNat] at hsign' hpoly' ⊢
  linear_combination (π : ℂ) * I / 12 * hsign' + 2 * (π : ℂ) * I / 24 * hpoly'

private theorem kroneckerOddExpr_mul_S_inv (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hodd_c : Odd (γ 1 0))
    (hd : γ 1 1 < 0) (hodd_d : Odd (-γ 1 1)) :
    kroneckerOddExpr (γ * S⁻¹) = cexp (π * I / 4) * kroneckerOddExpr γ := by
  set c : ℕ := (γ 1 0).toNat
  set m : ℕ := (-γ 1 1).toNat
  have hc_eq : (c : ℤ) = γ 1 0 := Int.toNat_of_nonneg hc.le
  have hm_eq : (m : ℤ) = -γ 1 1 := Int.toNat_of_nonneg (neg_nonneg.mpr hd.le)
  have hc_odd : Odd c := (Int.odd_natCast c).mp (hc_eq ▸ hodd_c)
  have hm_odd : Odd m := (Int.odd_natCast m).mp (hm_eq ▸ hodd_d)
  -- Quadratic reciprocity relates `(c / -d)` to `(d / c) = (-m / c)`.
  have hsym : (TauCeti.kroneckerSym (γ 1 0) (-γ 1 1) : ℂ) =
      ((-1 : ℂ) ^ (c / 2 + c / 2 * (m / 2))) * TauCeti.kroneckerSym (γ 1 1) (γ 1 0) := by
    have hJ : TauCeti.kroneckerSym (γ 1 0) (-γ 1 1) =
        (-1) ^ (c / 2 + c / 2 * (m / 2)) * TauCeti.kroneckerSym (γ 1 1) (γ 1 0) := by
      have hd_neg : γ 1 1 = -(m : ℤ) := by omega
      have hsq : ((-1 : ℤ) ^ (c / 2)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        simp
      rw [← hc_eq, ← hm_eq, hd_neg, TauCeti.kroneckerSym_eq_jacobiSym _ hm_odd,
        TauCeti.kroneckerSym_eq_jacobiSym _ hc_odd, jacobiSym.neg _ hc_odd,
        ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hc_odd),
        jacobiSym.quadratic_reciprocity hc_odd hm_odd, pow_add]
      linear_combination -((-1 : ℤ) ^ (c / 2 * (m / 2)) * jacobiSym (m : ℤ) c) * hsq
    exact_mod_cast hJ
  have hc_u : γ 1 0 = 2 * ((c / 2 : ℕ) : ℤ) + 1 := by
    have := Nat.div_add_mod c 2
    have := Nat.odd_iff.mp hc_odd
    omega
  have hm_v : γ 1 1 = -(2 * ((m / 2 : ℕ) : ℤ) + 1) := by
    have := Nat.div_add_mod m 2
    have := Nat.odd_iff.mp hm_odd
    omega
  have hsign_phase : (12 * ((c / 2 + c / 2 * (m / 2) : ℕ) : ℤ) : ℤ) =
      3 * (γ 1 0 - 1) * (1 - γ 1 1) := by
    rw [hc_u, hm_v]
    push_cast
    ring
  -- The difference between the two phases is `-6 (c - 1)(d - 1)`, a multiple of `24`.
  have hphase : kroneckerPhaseOdd (γ * S⁻¹) + 3 * (γ 1 0 - 1) * (1 - γ 1 1) ≡
      kroneckerPhaseOdd γ + 3 [ZMOD 24] := by
    rw [Int.modEq_iff_dvd]
    have hdiff : (kroneckerPhaseOdd γ + 3) -
        (kroneckerPhaseOdd (γ * S⁻¹) + 3 * (γ 1 0 - 1) * (1 - γ 1 1)) =
        6 * (γ 1 0 - 1) * (γ 1 1 - 1) := by
      simp only [kroneckerPhaseOdd, Matrix.SpecialLinearGroup.mul_S_inv_apply_zero,
        Matrix.SpecialLinearGroup.mul_S_inv_apply_one]
      linear_combination γ 1 0 * γ 1 1 * γ.fin_two_mul_sub_mul_eq_one
    rw [hdiff]
    obtain ⟨k, hk⟩ := hodd_c
    obtain ⟨l, hl⟩ := hodd_d
    have hd_l : γ 1 1 = -(2 * l + 1) := by omega
    refine ⟨-k * (l + 1), ?_⟩
    rw [hk, hd_l]
    ring
  have hexp_lhs : ((-1 : ℂ) ^ (c / 2 + c / 2 * (m / 2))) *
      cexp (2 * π * I * (kroneckerPhaseOdd (γ * S⁻¹) : ℂ) / 24) =
      cexp (2 * π * I *
        ((kroneckerPhaseOdd (γ * S⁻¹) + 3 * (γ 1 0 - 1) * (1 - γ 1 1) : ℤ) : ℂ) / 24) := by
    rw [← exp_pi_mul_I, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    have hsign' := congrArg (Int.cast : ℤ → ℂ) hsign_phase
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_one,
      Int.cast_ofNat] at hsign' ⊢
    linear_combination (π : ℂ) * I / 12 * hsign'
  have hexp_congr : cexp (2 * π * I *
      ((kroneckerPhaseOdd (γ * S⁻¹) + 3 * (γ 1 0 - 1) * (1 - γ 1 1) : ℤ) : ℂ) / 24) =
      cexp (2 * π * I * ((kroneckerPhaseOdd γ + 3 : ℤ) : ℂ) / 24) := by
    simpa using Complex.exp_two_pi_mul_I_mul_intCast_div_congr hphase
  rw [kroneckerOddExpr, kroneckerOddExpr, Matrix.SpecialLinearGroup.mul_S_inv_apply_zero,
    Matrix.SpecialLinearGroup.mul_S_inv_apply_one, hsym, mul_assoc,
    mul_left_comm ((-1 : ℂ) ^ _), hexp_lhs, hexp_congr, mul_left_comm (cexp _),
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The Kronecker-symbol formula for the eta multiplier at odd `c > 0`** (Strömberg, Remark 2.5,
equation (2.5)): for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0` odd,
`ε(γ) = (d / c) exp(2π i ((a + d) c - b d (c² - 1) - 3 c) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_of_c_pos_of_odd (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hodd : Odd (γ 1 0)) :
    etaMultiplier γ =
      TauCeti.kroneckerSym (γ 1 1) (γ 1 0) *
        cexp (2 * π * I *
          (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) /
          24) := by
  suffices ∀ (n : ℕ) (γ : SL(2, ℤ)), 0 < γ 1 0 → Odd (γ 1 0) → (γ 1 0).natAbs = n →
      etaMultiplier γ = kroneckerOddExpr γ from this (γ 1 0).natAbs γ hc hodd rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro γ hc hodd hn
    by_cases hc1 : γ 1 0 = 1
    · rw [etaMultiplier_of_c_eq_one γ hc1, kroneckerOddExpr, kroneckerPhaseOdd, hc1,
        TauCeti.kroneckerSym_one_right]
      simp only [Int.cast_one, one_mul, one_pow, sub_self, mul_zero, sub_zero, mul_one]
      congr 1
      push_cast
      ring
    have hc_gt : 1 < γ 1 0 := by omega
    set r : ℤ := γ 1 1 % γ 1 0
    have hr_pos : 0 < r := (γ.isCoprime_row 1).symm.emod_pos_of_one_lt hc_gt
    have hr_lt : r < γ 1 0 := Int.emod_lt_of_pos _ hc
    -- Choose the shifted remainder `r` or `r - c` that is odd, so the recursive denominator stays
    -- odd and positive of smaller absolute value.
    rcases Int.even_or_odd r with hr_even | hr_odd
    · set q : ℤ := γ 1 1 / γ 1 0 + 1
      set γ₁ : SL(2, ℤ) := γ * T ^ (-q)
      have hγ₁_c : γ₁ 1 0 = γ 1 0 := Matrix.SpecialLinearGroup.mul_T_zpow_apply_zero γ (-q) 1
      have hγ₁_d : γ₁ 1 1 = r - γ 1 0 := by
        rw [Matrix.SpecialLinearGroup.mul_T_zpow_apply_one]
        have := Int.mul_ediv_add_emod (γ 1 1) (γ 1 0)
        linarith
      have hd₁_neg : γ₁ 1 1 < 0 := by omega
      have hd₁_odd : Odd (-γ₁ 1 1) := by
        rw [hγ₁_d, neg_sub]
        exact hodd.sub_even hr_even
      have hSi_c : 0 < (γ₁ * S⁻¹) 1 0 := by
        rw [Matrix.SpecialLinearGroup.mul_S_inv_apply_zero]
        omega
      have hSi_odd : Odd ((γ₁ * S⁻¹) 1 0) := by
        rwa [Matrix.SpecialLinearGroup.mul_S_inv_apply_zero]
      have hSi_lt : ((γ₁ * S⁻¹) 1 0).natAbs < n := by
        rw [← hn, Matrix.SpecialLinearGroup.mul_S_inv_apply_zero]
        omega
      have hSi_eq := ih ((γ₁ * S⁻¹) 1 0).natAbs hSi_lt (γ₁ * S⁻¹) hSi_c hSi_odd rfl
      rw [etaMultiplier_mul_S_inv γ₁ (hγ₁_c ▸ hc),
        kroneckerOddExpr_mul_S_inv γ₁ (hγ₁_c ▸ hc) (hγ₁_c ▸ hodd) hd₁_neg hd₁_odd] at hSi_eq
      have hγ₁_eq : etaMultiplier γ₁ = kroneckerOddExpr γ₁ :=
        mul_left_cancel₀ (Complex.exp_ne_zero _) hSi_eq
      have hγ_restore : γ = γ₁ * T ^ q := by simp [γ₁, mul_assoc]
      rw [hγ_restore, etaMultiplier_mul_T_zpow,
        kroneckerOddExpr_mul_T_zpow _ (hγ₁_c ▸ hc) (hγ₁_c ▸ hodd), hγ₁_eq]
    · set q : ℤ := γ 1 1 / γ 1 0
      set γ₁ : SL(2, ℤ) := γ * T ^ (-q)
      have hγ₁_c : γ₁ 1 0 = γ 1 0 := Matrix.SpecialLinearGroup.mul_T_zpow_apply_zero γ (-q) 1
      have hγ₁_d : γ₁ 1 1 = r := by
        rw [Matrix.SpecialLinearGroup.mul_T_zpow_apply_one]
        have := Int.mul_ediv_add_emod (γ 1 1) (γ 1 0)
        linarith
      have hd₁_pos : 0 < γ₁ 1 1 := hγ₁_d ▸ hr_pos
      have hd₁_odd : Odd (γ₁ 1 1) := hγ₁_d ▸ hr_odd
      have hS_c : 0 < (γ₁ * S) 1 0 := by rwa [Matrix.SpecialLinearGroup.mul_S_apply_zero]
      have hS_odd : Odd ((γ₁ * S) 1 0) := by rwa [Matrix.SpecialLinearGroup.mul_S_apply_zero]
      have hS_lt : ((γ₁ * S) 1 0).natAbs < n := by
        rw [← hn, Matrix.SpecialLinearGroup.mul_S_apply_zero, hγ₁_d]
        omega
      have hS_eq := ih ((γ₁ * S) 1 0).natAbs hS_lt (γ₁ * S) hS_c hS_odd rfl
      rw [etaMultiplier_mul_S γ₁ hd₁_pos,
        kroneckerOddExpr_mul_S γ₁ (hγ₁_c ▸ hc) (hγ₁_c ▸ hodd) hd₁_pos hd₁_odd] at hS_eq
      have hγ₁_eq : etaMultiplier γ₁ = kroneckerOddExpr γ₁ :=
        mul_left_cancel₀ (Complex.exp_ne_zero _) hS_eq
      have hγ_restore : γ = γ₁ * T ^ q := by simp [γ₁, mul_assoc]
      rw [hγ_restore, etaMultiplier_mul_T_zpow,
        kroneckerOddExpr_mul_T_zpow _ (hγ₁_c ▸ hc) (hγ₁_c ▸ hodd), hγ₁_eq]

/-- **The Kronecker-symbol formula for the eta multiplier at even `c > 0`** (Strömberg, Remark 2.5,
equation (2.5)): for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0` even,
`ε(γ) = (c / d) exp(2π i ((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_of_c_pos_of_even (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (heven : Even (γ 1 0)) :
    etaMultiplier γ =
      TauCeti.kroneckerSym (γ 1 0) (γ 1 1) *
        cexp (2 * π * I *
          (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
            3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  -- Since `a d - b c = 1` and `c` is even, `d` is odd and nonzero, so a single `S` or `S⁻¹` step
  -- reduces to the odd-`c` formula.
  have hodd_d : Odd (γ 1 1) := by
    by_contra hd_not_odd
    have hd_even : Even (γ 1 1) := Int.not_odd_iff_even.mp hd_not_odd
    exact (by decide : ¬ IsUnit (2 : ℤ))
      ((γ.isCoprime_row 1).symm.isUnit_of_dvd'
        (even_iff_two_dvd.mp hd_even) (even_iff_two_dvd.mp heven))
  have hd_ne : γ 1 1 ≠ 0 := fun h0 ↦ Int.not_odd_zero (h0 ▸ hodd_d)
  rcases hd_ne.lt_or_gt with hd_neg | hd_pos
  · have hSi_c : 0 < (γ * S⁻¹) 1 0 := by
      rw [Matrix.SpecialLinearGroup.mul_S_inv_apply_zero]
      omega
    have hSi_odd : Odd ((γ * S⁻¹) 1 0) := by
      rw [Matrix.SpecialLinearGroup.mul_S_inv_apply_zero]
      exact hodd_d.neg
    have hSi := etaMultiplier_eq_kroneckerSym_of_c_pos_of_odd (γ * S⁻¹) hSi_c hSi_odd
    rw [etaMultiplier_mul_S_inv γ hc] at hSi
    simp only [Matrix.SpecialLinearGroup.mul_S_inv_apply_zero,
      Matrix.SpecialLinearGroup.mul_S_inv_apply_one] at hSi
    -- For `c > 0`, `(c / d) = (c / -1) (c / -d) = (c / -d)`.
    have hsym : TauCeti.kroneckerSym (γ 1 0) (-γ 1 1) = TauCeti.kroneckerSym (γ 1 0) (γ 1 1) := by
      have hd_split : γ 1 1 = (-1) * (-γ 1 1) := by ring
      conv_rhs => rw [hd_split]
      rw [TauCeti.kroneckerSym_mul_right _ (by decide) (by omega),
        TauCeti.kroneckerSym_neg_one_right, ite_eq_right (by omega), one_mul]
    have hpoly : ((-γ 0 1 + γ 1 0) * (-γ 1 1) - γ 0 0 * γ 1 0 * ((-γ 1 1) ^ 2 - 1) -
        3 * (-γ 1 1) : ℤ) =
        ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1) + 3 := by
      linear_combination -γ 1 0 * γ 1 1 * γ.fin_two_mul_sub_mul_eq_one
    refine mul_left_cancel₀ (Complex.exp_ne_zero (π * I / 4)) ?_
    rw [hSi, hsym, hpoly, mul_left_comm (cexp _), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · have hS_c : 0 < (γ * S) 1 0 := by rwa [Matrix.SpecialLinearGroup.mul_S_apply_zero]
    have hS_odd : Odd ((γ * S) 1 0) := by rwa [Matrix.SpecialLinearGroup.mul_S_apply_zero]
    have hS := etaMultiplier_eq_kroneckerSym_of_c_pos_of_odd (γ * S) hS_c hS_odd
    rw [etaMultiplier_mul_S γ hd_pos] at hS
    simp only [Matrix.SpecialLinearGroup.mul_S_apply_zero,
      Matrix.SpecialLinearGroup.mul_S_apply_one] at hS
    set d : ℕ := (γ 1 1).toNat
    have hd_eq : (d : ℤ) = γ 1 1 := Int.toNat_of_nonneg hd_pos.le
    have hd_odd : Odd d := (Int.odd_natCast d).mp (hd_eq ▸ hodd_d)
    have hsym : (TauCeti.kroneckerSym (-γ 1 0) (γ 1 1) : ℂ) =
        ((-1 : ℂ) ^ (d / 2)) * TauCeti.kroneckerSym (γ 1 0) (γ 1 1) := by
      have hJ : TauCeti.kroneckerSym (-γ 1 0) (γ 1 1) =
          (-1) ^ (d / 2) * TauCeti.kroneckerSym (γ 1 0) (γ 1 1) := by
        rw [← hd_eq, TauCeti.kroneckerSym_eq_jacobiSym _ hd_odd,
          TauCeti.kroneckerSym_eq_jacobiSym _ hd_odd, jacobiSym.neg _ hd_odd,
          ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hd_odd)]
      exact_mod_cast hJ
    have hhalf_d : (12 * ((d / 2 : ℕ) : ℤ) : ℤ) = 6 * (γ 1 1 - 1) := by
      have := Nat.div_add_mod d 2
      have := Nat.odd_iff.mp hd_odd
      omega
    have hpoly : ((γ 0 1 + -γ 1 0) * γ 1 1 - -γ 0 0 * -γ 1 0 * (γ 1 1 ^ 2 - 1) -
        3 * γ 1 1 : ℤ) + 6 * (γ 1 1 - 1) =
        ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1) - 3 := by
      linear_combination -γ 1 0 * γ 1 1 * γ.fin_two_mul_sub_mul_eq_one
    refine mul_left_cancel₀ (Complex.exp_ne_zero (-(π * I / 4))) ?_
    rw [hS, hsym, ← exp_pi_mul_I, ← Complex.exp_nat_mul, mul_assoc, mul_left_comm (cexp _),
      ← Complex.exp_add, mul_left_comm (cexp _), ← Complex.exp_add]
    congr 2
    have hhalf' := congrArg (Int.cast : ℤ → ℂ) hhalf_d
    have hpoly' := congrArg (Int.cast : ℤ → ℂ) hpoly
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_neg,
      Int.cast_pow, Int.cast_one, Int.cast_ofNat] at hhalf' hpoly' ⊢
    linear_combination (π : ℂ) * I / 12 * hhalf' + 2 * (π : ℂ) * I / 24 * hpoly'

/-- **Unified Kronecker-symbol formula for the eta multiplier at `c > 0`** (Strömberg, Remark 2.5,
equation (2.5)). -/
theorem etaMultiplier_eq_kroneckerSym_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ =
      if Odd (γ 1 0) then
        TauCeti.kroneckerSym (γ 1 1) (γ 1 0) *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) /
            24)
      else
        TauCeti.kroneckerSym (γ 1 0) (γ 1 1) *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
              3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  by_cases hodd : Odd (γ 1 0)
  · rw [ite_eq_left hodd, etaMultiplier_eq_kroneckerSym_of_c_pos_of_odd γ hc hodd]
  · rw [ite_eq_right hodd,
      etaMultiplier_eq_kroneckerSym_of_c_pos_of_even γ hc (Int.not_odd_iff_even.mp hodd)]

/-- The Kronecker-symbol formula for `ε(γ)` when `c < 0` and `c` is odd, obtained from `-γ` via
`ε(γ) = i ε(-γ)`. -/
theorem etaMultiplier_eq_kroneckerSym_of_c_neg_of_odd (γ : SL(2, ℤ)) (hc : γ 1 0 < 0)
    (hodd : Odd (γ 1 0)) :
    etaMultiplier γ =
      TauCeti.kroneckerSym (-γ 1 1) (-γ 1 0) *
        cexp (2 * π * I *
          (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
             3 * γ 1 0 + 6 : ℤ) : ℂ) / 24) := by
  have hc' : 0 < (-γ) 1 0 := by simpa using neg_pos.mpr hc
  have hodd' : Odd ((-γ) 1 0) := by simpa using hodd.neg
  have hneg : etaMultiplier γ = cexp (π / 2 * I) * etaMultiplier (-γ) := by
    simpa only [exp_pi_div_two_mul_I, neg_neg] using etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [hneg, etaMultiplier_eq_kroneckerSym_of_c_pos_of_odd (-γ) hc' hodd',
    mul_left_comm (cexp _), ← Complex.exp_add]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  congr 2
  push_cast
  ring

/-- The Kronecker-symbol formula for `ε(γ)` when `c < 0` and `c` is even, obtained from `-γ` via
`ε(γ) = i ε(-γ)`. -/
theorem etaMultiplier_eq_kroneckerSym_of_c_neg_of_even (γ : SL(2, ℤ)) (hc : γ 1 0 < 0)
    (heven : Even (γ 1 0)) :
    etaMultiplier γ =
      TauCeti.kroneckerSym (-γ 1 0) (-γ 1 1) *
        cexp (2 * π * I *
          (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) -
            3 * γ 1 1 + 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  have hc' : 0 < (-γ) 1 0 := by simpa using neg_pos.mpr hc
  have heven' : Even ((-γ) 1 0) := by simpa using heven.neg
  have hneg : etaMultiplier γ = cexp (π / 2 * I) * etaMultiplier (-γ) := by
    simpa only [exp_pi_div_two_mul_I, neg_neg] using etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [hneg, etaMultiplier_eq_kroneckerSym_of_c_pos_of_even (-γ) hc' heven',
    mul_left_comm (cexp _), ← Complex.exp_add]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  congr 2
  push_cast
  ring

end TauCeti.ModularForm

namespace TauCeti

/-- **The Dedekind–Jacobi congruence** (Rademacher and Grosswald, *Dedekind Sums*, Chapter 3,
Theorem 2): for coprime integers `d` and odd `c > 0`, `12 c s(d, c)` is an integer congruent to
`c + 1 - 2 (d / c)` modulo `8`. -/
theorem exists_int_twelve_mul_dedekindSum_and_modEq_eight {d c : ℤ} (hc : 0 < c) (hodd : Odd c)
    (hdc : IsCoprime d c) :
    ∃ k : ℤ, (k : ℚ) = 12 * c * dedekindSum d c ∧
      k ≡ c + 1 - 2 * kroneckerSym d c [ZMOD 8] := by
  have ⟨a, b₀, hab⟩ := hdc
  set b : ℤ := -b₀
  have hdet : a * d - b * c = 1 := by linear_combination hab
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by simp [Matrix.det_fin_two, hdet]⟩
  obtain ⟨m, hm⟩ := ModularForm.exists_int_eq_add_div_sub_twelve_mul_dedekindSum γ hc
  set k : ℤ := a + d - c * m
  have hk_rat : (k : ℚ) = 12 * c * dedekindSum d c := by
    have hc' : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
    have hm' : (m : ℚ) = (a + d : ℚ) / c - 12 * dedekindSum d c := by simpa [γ] using hm
    push_cast [k]
    field_simp [hc'] at hm' ⊢
    linear_combination -hm'
  refine ⟨k, hk_rat, ?_⟩
  -- Compare Dedekind's formula and the Kronecker-symbol formula at `γ`.
  have h1 := ModularForm.etaMultiplier_of_c_pos γ hc
  have h2 := ModularForm.etaMultiplier_eq_kroneckerSym_of_c_pos_of_odd γ hc hodd
  simp only [γ, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1 h2
  have hm_c : ((a : ℂ) + d) / (12 * c) - dedekindSum d c - 1 / 4 = ((m - 3 : ℤ) : ℂ) / 12 := by
    have hm' := congrArg (Rat.cast : ℚ → ℂ) (by simpa [γ] using hm)
    push_cast at hm' ⊢
    linear_combination -hm' / 12
  rw [hm_c] at h1
  set s : ℤ := kroneckerSym d c
  have hs_cases : s = 1 ∨ s = -1 := by
    rcases kroneckerSym_trichotomy d c with hs0 | hs1 | hs1
    · exfalso
      exact (kroneckerSym_eq_zero_iff.mp hs0) (Int.isCoprime_iff_gcd_eq_one.mp hdc)
    · exact .inl hs1
    · exact .inr hs1
  have hs_exp : (s : ℂ) = cexp (2 * π * I * ((6 * (1 - s) : ℤ) : ℂ) / 24) := by
    rcases hs_cases with hs1 | hs1 <;> rw [hs1]
    · simp
    · have harg : 2 * (π : ℂ) * I * ((6 * (1 - (-1 : ℤ)) : ℤ) : ℂ) / 24 = π * I := by
        push_cast
        ring
      rw [harg, exp_pi_mul_I]
      norm_num
  rw [hs_exp, ← Complex.exp_add] at h2
  obtain ⟨t, ht⟩ := Complex.exp_eq_exp_iff_exists_int.mp (h1.symm.trans h2)
  have ht_int : m - 3 = 6 * (1 - s) + ((a + d) * c - b * d * (c ^ 2 - 1) - 3 * c) + 24 * t := by
    have ht_c : ((m - 3 : ℤ) : ℂ) =
        ((6 * (1 - s) + ((a + d) * c - b * d * (c ^ 2 - 1) - 3 * c) + 24 * t : ℤ) : ℂ) := by
      refine mul_right_cancel₀ Complex.two_pi_I_ne_zero ?_
      push_cast at ht ⊢
      linear_combination 24 * ht
    exact_mod_cast ht_c
  -- Multiply the phase relation by `c` and reduce modulo `8` using `c = 2 u + 1`.
  rw [Int.modEq_iff_dvd]
  have hcm : c * m = a + d - k := by omega
  have hdiff : c + 1 - 2 * s - k =
      (a + d - b * d * c) * (c ^ 2 - 1) - 3 * c * (c - 1) + c + 1 +
        6 * (1 - s) * c - 2 * s + 24 * c * t := by
    linear_combination c * ht_int - hcm
  rw [hdiff]
  obtain ⟨u, rfl⟩ := hodd
  obtain ⟨v, hv⟩ := Int.even_mul_succ_self u
  rcases hs_cases with hs1 | hs1
  · refine ⟨(a + d - b * d * (2 * u + 1)) * v - v - u ^ 2 + 3 * (2 * u + 1) * t, ?_⟩
    rw [hs1]
    linear_combination 4 * (a + d - b * d * (2 * u + 1) - 1) * hv
  · refine ⟨(a + d - b * d * (2 * u + 1)) * v - v - u ^ 2 + 3 * u + 2 +
        3 * (2 * u + 1) * t, ?_⟩
    rw [hs1]
    linear_combination 4 * (a + d - b * d * (2 * u + 1) - 1) * hv

end TauCeti
