/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Discriminant
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.Complex.UpperHalfPlane.Sqrt
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-!
# The transformation of the Dedekind eta function under `SL(2, ℤ)`

This file proves the two generator laws of Mathlib's Dedekind eta function
`η(τ) = e^{2π i τ / 24} ∏_{n ≥ 1} (1 - qⁿ)` and its transformation under an arbitrary
`γ = (a b; c d) ∈ SL(2, ℤ)`:
* the translation law `η(τ + 1) = e^{π i / 12} η(τ)`, valid on all of `ℂ`;
* the inversion law `η(-1/τ) = √(-i τ) η(τ)` on the upper half-plane, with the principal
  square root, positive at `τ = i`; this is Mathlib's `ModularForm.eta_comp_eq_csqrt_I_inv`
  rewritten, since on the upper half-plane `√(-i τ) = (√i)⁻¹ √τ`;
* the eta multiplier `ε(γ)`, a 24th root of unity with `η(γ τ) = ε(γ) √(c τ + d) η(τ)` on the
  upper half-plane, with the principal square root.

The existence of `ε(γ)` is proved without the Euclidean algorithm. The 24th power of
`τ ↦ η(γ τ) / (√(c τ + d) η(τ))` is `1` by the level-one modularity of `Δ = η²⁴`. This
quotient is continuous on the connected upper half-plane, because `c τ + d` is constant when
`c = 0` and otherwise avoids the real axis. So it is constant.

For `γ = (a b; c d)` with `d > 0`, right multiplication by `S` multiplies the
eta multiplier by `exp(-π i / 4)`. At `τ = i`, the new automorphy factor `-c + d i`
lies in the upper half-plane, controlling the principal square root. Together with the
translation laws, this is the inversion step in the Euclidean calculation of the multiplier.
The initial case `c = 1` has the explicit value `exp(π i ((a + d) / 12 - 1/4))`.

## Main definitions

* `TauCeti.ModularForm.etaMultiplier γ`: the eta multiplier `ε(γ)`.

## Main results

* `TauCeti.ModularForm.eta_add_one`, `TauCeti.ModularForm.eta_add_intCast`: the translation law.
* `TauCeti.ModularForm.eta_neg_one_div`: the inversion law with the root `√(-i τ)`.
* `TauCeti.ModularForm.eta_smul`: `η(γ τ) = ε(γ) √(c τ + d) η(τ)` for `γ ∈ SL(2, ℤ)`.
* `TauCeti.ModularForm.etaMultiplier_pow_twentyFour`: `ε(γ)²⁴ = 1`.
* `TauCeti.ModularForm.etaMultiplier_eq_of_eta_smul_eq`: `ε(γ)` is determined by the
  transformation law at a single point.
* `TauCeti.ModularForm.etaMultiplier_T_zpow`, `TauCeti.ModularForm.etaMultiplier_S`,
  `TauCeti.ModularForm.etaMultiplier_neg_one`: `ε(Tⁿ) = e^{π i n / 12}`, `ε(S) = e^{-π i / 4}`
  and `ε(-1) = -i`.
* `TauCeti.ModularForm.etaMultiplier_mul_T_zpow`, `TauCeti.ModularForm.etaMultiplier_T_zpow_mul`:
  `ε(γ Tⁿ) = ε(Tⁿ γ) = e^{π i n / 12} ε(γ)`.
* `TauCeti.ModularForm.etaMultiplier_mul_S`, `TauCeti.ModularForm.etaMultiplier_mul_S_inv`:
  `ε(γ S) = e^{-π i / 4} ε(γ)` when `d > 0` and `ε(γ S⁻¹) = e^{π i / 4} ε(γ)` when `c > 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_eq_one`,
  `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero`: the explicit multiplier when `c = 1` and when
  `c = 0`.
* `TauCeti.ModularForm.etaMultiplier_neg_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_neg_of_c_neg`,
  `TauCeti.ModularForm.etaMultiplier_inv_of_c_ne_zero_or_d_pos`: negation and inversion laws.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, Theorems 3.1
  and 3.4.
-/

public section

open Complex ModularGroup
open scoped UpperHalfPlane
open scoped Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### The two generator laws -/

/-- **The translation law of `η`**: `η(τ + n) = e^{π i n / 12} η(τ)` for every integer `n`. -/
theorem eta_add_intCast (τ : ℂ) (n : ℤ) : η (τ + n) = cexp (π * I * n / 12) * η τ := by
  have hq (m : ℕ) : _root_.ModularForm.eta_q m (τ + n) = _root_.ModularForm.eta_q m τ := by
    have harg : 2 * π * I * (m + 1) * (τ + n) =
        2 * π * I * (m + 1) * τ + ((m + 1) * n : ℤ) * (2 * π * I) := by
      push_cast
      ring
    simp only [_root_.ModularForm.eta_q_eq_cexp]
    rw [harg, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  have hexp : Function.Periodic.qParam 24 (τ + n) =
      cexp (π * I * n / 12) * Function.Periodic.qParam 24 τ := by
    simp only [Function.Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [_root_.ModularForm.eta, hq, hexp, mul_assoc]

/-- **The translation law of `η`**: `η(τ + 1) = e^{π i / 12} η(τ)`. -/
theorem eta_add_one (τ : ℂ) : η (τ + 1) = cexp (π * I / 12) * η τ := by
  simpa using eta_add_intCast τ 1

/-- **The inversion law of `η`**: `η(-1/τ) = √(-i τ) η(τ)` on the upper half-plane, with the
principal square root, which is positive at `τ = i`. -/
theorem eta_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) :
    η (-1 / τ) = Complex.sqrt (-I * τ) * η τ := by
  rw [Complex.sqrt_neg_I_mul hτ, mul_assoc]
  simpa using _root_.ModularForm.eta_comp_eq_csqrt_I_inv hτ

/-! ### The eta multiplier -/

/-- The automorphy factor `c τ + d` of `γ ∈ SL(2, ℤ)` does not vanish on the upper half-plane. -/
private theorem denom_ne_zero' (γ : SL(2, ℤ)) (τ : ℍ) : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by
  simpa [UpperHalfPlane.denom] using UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ

private theorem sqrt_denom_mul_eta_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ ≠ 0 :=
  mul_ne_zero (Complex.sqrt_eq_zero_iff.not.2 (denom_ne_zero' γ τ))
    (_root_.ModularForm.eta_ne_zero τ.2)

/-- `Δ(γ τ) = (c τ + d)¹² Δ(τ)` for `γ ∈ SL(2, ℤ)`, in terms of `η`. -/
private theorem eta_smul_pow_twentyFour (γ : SL(2, ℤ)) (τ : ℍ) :
    η (γ • τ : ℍ) ^ 24 = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 12 * η τ ^ 24 := by
  have h := SlashInvariantForm.slash_action_eqn' CuspForm.discriminant
    (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ) (MonoidHom.mem_range.2 ⟨γ, rfl⟩) τ
  rw [MulAction.compHom_smul_def]
  simpa [_root_.ModularForm.discriminant] using h

/-- The quotient `η(γ τ) / (√(c τ + d) η(τ))`, constant in `τ` by `etaQuotient_eq`. -/
private noncomputable def etaQuotient (γ : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  η (γ • τ : ℍ) / (Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ)

private theorem etaQuotient_pow_twentyFour (γ : SL(2, ℤ)) (τ : ℍ) :
    etaQuotient γ τ ^ 24 = 1 := by
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero τ.2
  have hs : Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 24 = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 12 :=
    (pow_mul _ 2 12).trans (congrArg (· ^ 12) (Complex.sq_sqrt _))
  rw [etaQuotient, div_pow, mul_pow, hs,
    eta_smul_pow_twentyFour, div_self (mul_ne_zero (pow_ne_zero _ (denom_ne_zero' γ τ))
      (pow_ne_zero _ hη))]

private theorem continuous_etaQuotient (γ : SL(2, ℤ)) : Continuous (etaQuotient γ) := by
  have hη : Continuous fun τ : ℍ ↦ η τ := continuous_iff_continuousAt.2 fun τ ↦
    (_root_.ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet τ.2).continuousAt.comp
      UpperHalfPlane.continuous_coe.continuousAt
  have hγ : Continuous fun τ : ℍ ↦ γ • τ := by
    simp_rw [MulAction.compHom_smul_def]
    exact continuous_const_smul _
  have hs : Continuous fun τ : ℍ ↦ Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) := by
    simpa using UpperHalfPlane.continuous_sqrt_ofReal_mul_add (γ 1 0) (γ 1 1)
  exact (hη.comp hγ).div (hs.mul hη) (sqrt_denom_mul_eta_ne_zero γ)

/-- The quotient `η(γ τ) / (√(c τ + d) η(τ))` is independent of `τ`: it is a continuous function
on the connected upper half-plane with values in the finite set of 24th roots of unity. -/
private theorem etaQuotient_eq (γ : SL(2, ℤ)) (τ τ' : ℍ) :
    etaQuotient γ τ = etaQuotient γ τ' := by
  let R : Set ℂ := ((Polynomial.nthRoots 24 (1 : ℂ)).toFinset : Set ℂ)
  refine isPreconnected_univ.constant_of_mapsTo (Finset.finite_toSet _).isDiscrete
    (continuous_etaQuotient γ).continuousOn (T := R) (fun σ _ ↦ ?_) (Set.mem_univ τ)
    (Set.mem_univ τ')
  simpa [R, Polynomial.mem_nthRoots] using etaQuotient_pow_twentyFour γ σ

/-- **The eta multiplier** `ε(γ)` of `γ = (a b; c d) ∈ SL(2, ℤ)`: the constant with
`η(γ τ) = ε(γ) √(c τ + d) η(τ)` on the upper half-plane, with the principal square root
(`eta_smul`). It is a 24th root of unity (`etaMultiplier_pow_twentyFour`). -/
noncomputable def etaMultiplier (γ : SL(2, ℤ)) : ℂ :=
  etaQuotient γ UpperHalfPlane.I

/-- **The transformation law of `η` under `SL(2, ℤ)`**: for `γ = (a b; c d)`,
`η(γ τ) = ε(γ) √(c τ + d) η(τ)` on the upper half-plane, with the principal square root. -/
theorem eta_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    η (γ • τ : ℍ) = etaMultiplier γ * Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ := by
  rw [etaMultiplier, ← etaQuotient_eq γ τ, etaQuotient, mul_assoc,
    div_mul_cancel₀ _ (sqrt_denom_mul_eta_ne_zero γ τ)]

/-- The eta multiplier is a 24th root of unity. -/
theorem etaMultiplier_pow_twentyFour (γ : SL(2, ℤ)) : etaMultiplier γ ^ 24 = 1 :=
  etaQuotient_pow_twentyFour γ _

/-- The eta multiplier is determined by the transformation law of `η` at a single point. -/
theorem etaMultiplier_eq_of_eta_smul_eq {γ : SL(2, ℤ)} {ε : ℂ} {τ : ℍ}
    (h : η (γ • τ : ℍ) = ε * Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ) :
    etaMultiplier γ = ε := by
  rw [eta_smul, mul_assoc, mul_assoc] at h
  exact mul_right_cancel₀ (sqrt_denom_mul_eta_ne_zero γ τ) h

/-- `ε(1) = 1`. -/
@[simp]
theorem etaMultiplier_one : etaMultiplier 1 = 1 :=
  etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) (by simp)

/-- `ε(-1) = -i`: the identity transformation with the automorphy factor `-1`, whose
principal root is `i`. -/
@[simp]
theorem etaMultiplier_neg_one : etaMultiplier (-1) = -I := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  simp [Complex.sqrt_neg_one]

/-- `ε(Tⁿ) = e^{π i n / 12}`, by the translation law. -/
@[simp]
theorem etaMultiplier_T_zpow (n : ℤ) : etaMultiplier (T ^ n) = cexp (π * I * n / 12) := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  rw [coe_T_zpow_smul_eq, eta_add_intCast]
  simp [coe_T_zpow]

/-- `ε(T) = e^{π i / 12}`, by the translation law. -/
@[simp]
theorem etaMultiplier_T : etaMultiplier T = cexp (π * I / 12) := by
  simpa using etaMultiplier_T_zpow 1

/-- `ε(S) = e^{-π i / 4}` for `S = (0 -1; 1 0)`, with the root `√τ` of the automorphy factor `τ`,
by the inversion law. -/
@[simp]
theorem etaMultiplier_S : etaMultiplier S = cexp (-(π * I / 4)) := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have hS : ((S • UpperHalfPlane.I : ℍ) : ℂ) = -1 / (UpperHalfPlane.I : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [neg_div]
  rw [hS, eta_neg_one_div (by simp), Complex.sqrt_neg_I_mul (by simp), Complex.sqrt_I_eq_exp,
    ← Complex.exp_neg]
  simp [coe_S]

/-- `ε(γ Tⁿ) = e^{π i n / 12} ε(γ)`: right translation by `Tⁿ` replaces `τ` by `τ + n`. -/
theorem etaMultiplier_mul_T_zpow (γ : SL(2, ℤ)) (n : ℤ) :
    etaMultiplier (γ * T ^ n) = cexp (π * I * n / 12) * etaMultiplier γ := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have hτ : 0 < ((UpperHalfPlane.I : ℂ) + n).im := by simp
  have h := eta_smul γ ⟨(UpperHalfPlane.I : ℂ) + n, hτ⟩
  have hsmul : (γ * T ^ n) • UpperHalfPlane.I = γ • (⟨(UpperHalfPlane.I : ℂ) + n, hτ⟩ : ℍ) := by
    rw [mul_smul]
    congr 1
    ext
    exact coe_T_zpow_smul_eq _
  have hentry0 : (γ * T ^ n) 1 0 = γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  have hentry1 : (γ * T ^ n) 1 1 = γ 1 0 * n + γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hsmul, h, hentry0, hentry1]
  simp only [eta_add_intCast, Int.cast_add, Int.cast_mul]
  rw [mul_add, add_assoc]
  ring

/-- `ε(γ T) = e^{π i / 12} ε(γ)`. -/
theorem etaMultiplier_mul_T (γ : SL(2, ℤ)) :
    etaMultiplier (γ * T) = cexp (π * I / 12) * etaMultiplier γ := by
  simpa using etaMultiplier_mul_T_zpow γ 1

/-- `ε(Tⁿ γ) = e^{π i n / 12} ε(γ)`: left translation by `Tⁿ` replaces `γ τ` by `γ τ + n`. -/
theorem etaMultiplier_T_zpow_mul (γ : SL(2, ℤ)) (n : ℤ) :
    etaMultiplier (T ^ n * γ) = cexp (π * I * n / 12) * etaMultiplier γ := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  rw [mul_smul, coe_T_zpow_smul_eq, eta_add_intCast, eta_smul, T_pow_mul_apply_one]
  ring

/-- `ε(T γ) = e^{π i / 12} ε(γ)`. -/
theorem etaMultiplier_T_mul (γ : SL(2, ℤ)) :
    etaMultiplier (T * γ) = cexp (π * I / 12) * etaMultiplier γ := by
  simpa using etaMultiplier_T_zpow_mul γ 1

/-- Right inversion multiplies the eta multiplier by `exp(-π i / 4)` when the
lower-right entry is positive. No sign condition on the lower-left entry is needed. -/
theorem etaMultiplier_mul_S (γ : SL(2, ℤ)) (hd : 0 < γ 1 1) :
    etaMultiplier (γ * S) = cexp (-(π * I / 4)) * etaMultiplier γ := by
  have hentry0 : (γ * S) 1 0 = γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hentry1 : (γ * S) 1 1 = -γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hpos : 0 < ((γ 1 1 : ℂ) * I - γ 1 0).im := by
    simpa using (Int.cast_pos.mpr hd : (0 : ℝ) < γ 1 1)
  have hroot := Complex.sqrt_neg_I_mul hpos
  have hrotate : -I * ((γ 1 1 : ℂ) * I - γ 1 0) = (γ 1 0 : ℂ) * I + γ 1 1 := by
    ring_nf
    simp
  rw [hrotate, Complex.sqrt_I_eq_exp, ← Complex.exp_neg] at hroot
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have hfixed : S • UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_S_smul]
    simp
  rw [mul_smul, hfixed, eta_smul, hentry0, hentry1]
  simp only [UpperHalfPlane.coe_I, Int.cast_neg, ← sub_eq_add_neg]
  rw [hroot]
  ring

/-- If the lower-left entry is `1`, the eta multiplier is
`exp(π i ((a + d) / 12 - 1/4))`. This is the initial case of its Dedekind-sum formula. -/
theorem etaMultiplier_of_c_eq_one (γ : SL(2, ℤ)) (hc : γ 1 0 = 1) :
    etaMultiplier γ = cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / 12 - 1 / 4)) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_one] at hdet
  have hfactor : γ = T ^ (γ 0 0) * S * T ^ (γ 1 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, coe_S,
        Matrix.mul_apply, Fin.sum_univ_two, hc]
    omega
  rw [congrArg etaMultiplier hfactor, etaMultiplier_mul_T_zpow,
    etaMultiplier_T_zpow_mul, etaMultiplier_S,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- The eta multiplier never vanishes. -/
theorem etaMultiplier_ne_zero (γ : SL(2, ℤ)) : etaMultiplier γ ≠ 0 := by
  intro h
  have h24 := etaMultiplier_pow_twentyFour γ
  rw [h, zero_pow (by decide)] at h24
  exact zero_ne_one h24

/-- The eta multiplier has unit complex norm. -/
@[simp]
theorem norm_etaMultiplier (γ : SL(2, ℤ)) : ‖etaMultiplier γ‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 24 ≠ 0)).mp ?_
  rw [← norm_pow, etaMultiplier_pow_twentyFour, norm_one]

/-- The complex conjugate of the eta multiplier is its multiplicative inverse. -/
@[simp]
theorem conj_etaMultiplier (γ : SL(2, ℤ)) :
    (starRingEnd ℂ) (etaMultiplier γ) = (etaMultiplier γ)⁻¹ := by
  rw [Complex.inv_def, normSq_eq_norm_sq, norm_etaMultiplier, one_pow, inv_one, ofReal_one,
    mul_one]

/-- Right multiplication by `S⁻¹` multiplies the eta multiplier by `exp(π i / 4)` when the
lower-left entry is positive: `(γ S⁻¹) S = γ` has positive lower-right entry `c`. -/
theorem etaMultiplier_mul_S_inv (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier (γ * S⁻¹) = cexp (π * I / 4) * etaMultiplier γ := by
  have hd : 0 < (γ * S⁻¹) 1 1 := by rwa [Matrix.SpecialLinearGroup.mul_S_inv_apply_one]
  have hS := etaMultiplier_mul_S (γ * S⁻¹) hd
  rw [inv_mul_cancel_right] at hS
  rw [hS, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

/-- Negating `γ` multiplies the eta multiplier by `i` when `c > 0`: at `τ = i`, the automorphy
factor `c i + d` lies in the open upper half-plane, so `√(-c i - d) = -i √(c i + d)`. -/
theorem etaMultiplier_neg_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier (-γ) = I * etaMultiplier γ := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have him : 0 < ((γ 1 0 : ℂ) * I + γ 1 1).im := by
    simpa using (Int.cast_pos.mpr hc : (0 : ℝ) < γ 1 0)
  have hneg : ((-γ 1 0 : ℤ) : ℂ) * I + (-γ 1 1 : ℤ) = -((γ 1 0 : ℂ) * I + γ 1 1) := by
    push_cast
    ring
  rw [SL_neg_smul, eta_smul]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, UpperHalfPlane.coe_I, hneg,
    Complex.sqrt_neg_of_im_pos him]
  ring_nf
  simp

/-- Negating `γ` multiplies the eta multiplier by `-i` when `c < 0`. -/
theorem etaMultiplier_neg_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier (-γ) = -I * etaMultiplier γ := by
  have hc' : 0 < (-γ) 1 0 := by simpa using neg_pos.mpr hc
  have h := etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [neg_neg] at h
  rw [h, ← mul_assoc]
  simp

/-- Upper-triangular matrices in `SL(2, ℤ)` with positive lower-right entry are powers `Tᵇ`, so
their eta multiplier is `e^{π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_pos (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : 0 < γ 1 1) :
    etaMultiplier γ = cexp (π * I * γ 0 1 / 12) := by
  rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hT | hT
  · rw [congrArg etaMultiplier hT, etaMultiplier_T_zpow]
  · exfalso
    have hd1 : γ 1 1 = -1 := by
      rw [hT]
      simp [coe_T_zpow]
    omega

/-- Upper-triangular matrices in `SL(2, ℤ)` with negative lower-right entry have the form `-T⁻ᵇ`,
so their eta multiplier is `-i e^{-π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_neg (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : γ 1 1 < 0) :
    etaMultiplier γ = -I * cexp (-(π * I * γ 0 1 / 12)) := by
  rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hT | hT
  · exfalso
    have hd1 : γ 1 1 = 1 := by
      rw [hT]
      simp [coe_T_zpow]
    omega
  · have hd1 : γ 1 1 = -1 := by
      rw [hT]
      simp [coe_T_zpow]
    refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
    have hsmul : ((γ • UpperHalfPlane.I : ℍ) : ℂ) = (UpperHalfPlane.I : ℂ) + (-γ 0 1 : ℤ) := by
      conv_lhs => rw [hT]
      rw [SL_neg_smul, coe_T_zpow_smul_eq]
    rw [hsmul, eta_add_intCast, hc, hd1]
    simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_neg, Int.cast_one,
      Complex.sqrt_neg_one, mul_neg, neg_div]
    ring_nf
    simp

/-- When `c = 0`, `γ = ±T^{±b}`, and the eta multiplier is `e^{π i b / 12}` if `d > 0` and
`-i e^{-π i b / 12}` if `d < 0`. -/
theorem etaMultiplier_of_c_eq_zero (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) :
    etaMultiplier γ =
      if 0 < γ 1 1 then cexp (π * I * γ 0 1 / 12) else -I * cexp (-(π * I * γ 0 1 / 12)) := by
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  rw [hc, mul_zero, sub_zero] at hdet
  by_cases hd : 0 < γ 1 1
  · rw [ite_eq_left hd, etaMultiplier_of_c_eq_zero_of_d_pos γ hc hd]
  · have hd' : γ 1 1 < 0 := by
      rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨_, hd1⟩ | ⟨_, hd1⟩ <;> omega
    rw [ite_eq_right hd, etaMultiplier_of_c_eq_zero_of_d_neg γ hc hd']

/-- Away from the upper-triangular matrices with `d < 0` (where `c i + d = -1` lies on the branch
cut of `Complex.sqrt`), the eta multiplier respects matrix inversion: `ε(γ⁻¹) = ε(γ)⁻¹`. -/
theorem etaMultiplier_inv_of_c_ne_zero_or_d_pos {γ : SL(2, ℤ)} (h : γ 1 0 ≠ 0 ∨ 0 < γ 1 1) :
    etaMultiplier γ⁻¹ = (etaMultiplier γ)⁻¹ := by
  let z : ℂ := (γ 1 0 : ℂ) * I + γ 1 1
  have hz_def : z = (γ 1 0 : ℂ) * I + γ 1 1 := rfl
  have hz₀ : z ≠ 0 := by simpa [hz_def] using denom_ne_zero' γ UpperHalfPlane.I
  have harg : z.arg ≠ π := by
    rw [Ne, Complex.arg_eq_pi_iff]
    rintro ⟨hre, him⟩
    have hc0 : γ 1 0 = 0 := by exact_mod_cast (by simpa [hz_def] using him : (γ 1 0 : ℝ) = 0)
    have hd0 : γ 1 1 < 0 := by exact_mod_cast (by simpa [hz_def] using hre : (γ 1 1 : ℝ) < 0)
    rcases h with hc | hd
    · exact hc hc0
    · exact hd.not_gt hd0
  -- The automorphy factor of `γ⁻¹` at `γ • i` is `(c i + d)⁻¹`.
  have hdenom : (γ⁻¹ 1 0 : ℂ) * (γ • UpperHalfPlane.I : ℍ) + γ⁻¹ 1 1 = z⁻¹ := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, Matrix.SpecialLinearGroup.inv_apply_one_zero,
      Matrix.SpecialLinearGroup.inv_apply_one_one]
    simp only [UpperHalfPlane.coe_I, algebraMap_int_eq, Int.coe_castRingHom, ofReal_intCast,
      Int.cast_neg, hz_def]
    have hz₀' : (γ 1 0 : ℂ) * I + γ 1 1 ≠ 0 := hz₀
    field_simp
    linear_combination γ.intCast_fin_two_mul_sub_mul_eq_one (R := ℂ)
  have h1 := eta_smul γ⁻¹ (γ • UpperHalfPlane.I)
  rw [inv_smul_smul, eta_smul γ UpperHalfPlane.I, UpperHalfPlane.coe_I, hdenom,
    Complex.sqrt_inv harg, ← hz_def] at h1
  have hη : η I ≠ 0 := _root_.ModularForm.eta_ne_zero UpperHalfPlane.I.2
  have hsqrt : Complex.sqrt z ≠ 0 := Complex.sqrt_eq_zero_iff.not.mpr hz₀
  have hprod : etaMultiplier γ⁻¹ * etaMultiplier γ = 1 := by
    refine mul_right_cancel₀ hη ?_
    calc
      etaMultiplier γ⁻¹ * etaMultiplier γ * η I
          = etaMultiplier γ⁻¹ * (Complex.sqrt z)⁻¹ *
              (etaMultiplier γ * Complex.sqrt z * η I) := by
            linear_combination -etaMultiplier γ⁻¹ * etaMultiplier γ * η I * inv_mul_cancel₀ hsqrt
      _ = 1 * η I := by rw [← h1, one_mul]
  exact eq_inv_of_mul_eq_one_left hprod

/-- When `c ≠ 0`, `ε(γ⁻¹) = ε(γ)⁻¹`. -/
theorem etaMultiplier_inv_of_c_ne_zero (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    etaMultiplier γ⁻¹ = (etaMultiplier γ)⁻¹ :=
  etaMultiplier_inv_of_c_ne_zero_or_d_pos (.inl hc)

/-- On the branch cut `c = 0` and `d < 0` (so `γ = -T⁻ᵇ`), `ε(γ⁻¹) = -ε(γ)⁻¹`. -/
theorem etaMultiplier_inv_of_c_eq_zero_of_d_neg (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : γ 1 1 < 0) :
    etaMultiplier γ⁻¹ = -(etaMultiplier γ)⁻¹ := by
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  rw [hc, mul_zero, sub_zero] at hdet
  have ha : γ 0 0 < 0 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨_, hd1⟩ | ⟨ha1, _⟩ <;> omega
  have hinv_c : (γ⁻¹ : SL(2, ℤ)) 1 0 = 0 := by simp [hc]
  have hinv_d : (γ⁻¹ : SL(2, ℤ)) 1 1 < 0 := by simpa using ha
  have hexp : cexp (-(π * I * -(γ 0 1 : ℂ) / 12)) = cexp (π * I * γ 0 1 / 12) := by
    congr 1; ring
  rw [etaMultiplier_of_c_eq_zero_of_d_neg γ⁻¹ hinv_c hinv_d,
    etaMultiplier_of_c_eq_zero_of_d_neg γ hc hd, Matrix.SpecialLinearGroup.inv_apply_zero_one,
    Int.cast_neg, hexp, mul_inv_rev, ← Complex.exp_neg, neg_neg, inv_neg, inv_I]
  ring

end TauCeti.ModularForm
