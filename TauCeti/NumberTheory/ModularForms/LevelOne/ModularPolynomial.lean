/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import TauCeti.NumberTheory.ModularForms.LevelOne.CyclicIsogenyPolynomial
public import TauCeti.NumberTheory.ModularForms.LevelOne.WeaklyHolomorphic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.NumberTheory.Cyclotomic.Aut
import TauCeti.RingTheory.HahnSeries.Map

/-!
# The modular polynomials `Φ_n` and integrality of `j` at imaginary quadratic points

For a positive integer `n`, the polynomial over the cyclic `n`-isogenies of the modular invariant,

  `cyclicIsogenyPolynomial n j τ = ∏_{(a b; 0 d)} (X - j((a τ + b) / d))`,

has holomorphic `SL(2, ℤ)`-invariant coefficients
(`TauCeti.ModularForm.cyclicIsogenyPolynomial_smul` and
`TauCeti.ModularForm.mdifferentiable_coeff_cyclicIsogenyPolynomial`). This file computes the
width-`n` Laurent `q`-expansions of the factors `j((a τ + b) / d)`, shows that the coefficients of
the product have rational integer `q`-expansions, and deduces from the level-one weakly holomorphic
structure theorem (`TauCeti.ModularForm.exists_aeval_j_eq`) that there is a unique polynomial
`modularPolynomial n : ℤ[X][X]` — monic of degree `#(primitiveReps n)` — whose specialization along
`Y ↦ j(τ)` is `cyclicIsogenyPolynomial n j τ`.

In width `n`, writing `q_n = exp(2 π i τ / n)` and `ζ_n = exp(2 π i / n)`, each representative
`A = (a b; 0 d)` with `a d = n` satisfies `q_1(A τ) = ζ_n^{a b} q_n^{a²}`, so `j(A τ)` has Laurent
series `∑_{m ≥ -1} c_m ζ_n^{a b m} q_n^{a² m}` with coefficients in `ℤ[ζ_n]`, where `c_m ∈ ℤ` are
the Laurent `q`-coefficients of `j`. Lifting these series to the cyclotomic field
`CyclotomicField n ℚ`, an automorphism `σ ∈ Gal(ℚ(ζ_n) / ℚ)` sends `ζ_n` to `ζ_n^r` with
`gcd(r, n) = 1` and permutes the primitive representatives by `(a b; 0 d) ↦ (a, r b mod d; 0, d)`.
The elementary symmetric polynomials of the lifted series are therefore both integral over `ℤ` and
`Gal(ℚ(ζ_n) / ℚ)`-invariant, hence have coefficients in `ℤ`.

When `n` is not a square, no primitive representative `(a b; 0 d)` of determinant `n` can have
`a² = n` (since `a d = n` would force `a = d`), so in width `n` the series of `j(τ)` (of order
`-n` and leading coefficient `1`) and `j(A τ)` (of order `-a²` and root-of-unity leading
coefficient) never cancel in leading order. Consequently the diagonal specialization
`Φ_n(X, X) = (modularPolynomial n).eval X : ℤ[X]` is nonzero of positive degree and its leading
coefficient is `±1` (`IsUnit`). Every imaginary quadratic point `τ ∈ ℍ` (satisfying
`a τ² + b τ + c = 0` with `a, b, c ∈ ℤ`, `a ≠ 0`) is fixed by an explicit primitive integer matrix
of nonsquare determinant `m² + m` or `m² + 2 m`, so `j(τ)` is a root of `Φ_n(X, X)` up to sign and
is therefore an algebraic integer (`isIntegral_j_of_quadratic`).

## Main definitions

* `TauCeti.ModularForm.modularPolynomial n`: the classical modular polynomial `Φ_n ∈ ℤ[X][X]`,
  monic in the outer variable, characterized by
  `(modularPolynomial n).map ↑(aeval (j τ)) = cyclicIsogenyPolynomial n j τ`.

## Main results

* `TauCeti.ModularForm.monic_modularPolynomial`, `TauCeti.ModularForm.natDegree_modularPolynomial`:
  `modularPolynomial n` is monic of degree `(primitiveReps (n : ℤ)).card`.
* `TauCeti.ModularForm.map_aeval_j_modularPolynomial`,
  `TauCeti.ModularForm.eq_modularPolynomial_iff`: characterization and uniqueness of `Φ_n`.
* `TauCeti.ModularForm.aevalAeval_j_modularPolynomial_eq_zero`,
  `TauCeti.ModularForm.aevalAeval_j_modularPolynomial_eq_zero_symm`,
  `TauCeti.ModularForm.aevalAeval_j_scaleGL_modularPolynomial_eq_zero`: `Φ_n(j(τ), j(A τ)) = 0`
  and `Φ_n(j(A τ), j(τ)) = 0` for every primitive matrix `A` of determinant `n`, and in particular
  `Φ_n(j(τ), j(n τ)) = 0` and `Φ_n(j(n τ), j(τ)) = 0`.
* `TauCeti.ModularForm.isUnit_leadingCoeff_eval_X_modularPolynomial`,
  `TauCeti.ModularForm.natDegree_eval_X_modularPolynomial_pos`: for nonsquare `n`, the diagonal
  polynomial `Φ_n(X, X) = (modularPolynomial n).eval X` has positive degree and unit (`±1`) leading
  coefficient in `ℤ`.
* `TauCeti.ModularForm.isIntegral_j_of_quadratic`: at any point `τ ∈ ℍ` satisfying a nontrivial
  integral quadratic equation `a τ² + b τ + c = 0`, the value `j(τ)` is an algebraic integer.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §11.C (integrality of the modular
  polynomial via `ℚ(ζ_m)`) and §11.D (leading coefficient `±1` of `Φ_m(X, X)` for nonsquare `m` and
  algebraic integrality of singular moduli).
* S. Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 5, §§2–3.
-/

open Complex Filter Function Matrix Polynomial Topology UpperHalfPlane
open FixedDetMatrices
open scoped MatrixGroups Manifold

local notation "𝕢" => Function.Periodic.qParam

namespace TauCeti.ModularForm

/-! ### Entries and Möbius action of upper-triangular representatives -/

noncomputable section RepsEntries

variable {n : ℕ} [NeZero n] {A : FixedDetMatrix (Fin 2) ℤ n}

private def repA (A : FixedDetMatrix (Fin 2) ℤ n) : ℕ := (A.1 0 0).natAbs
private def repB (A : FixedDetMatrix (Fin 2) ℤ n) : ℕ := (A.1 0 1).natAbs
private def repD (A : FixedDetMatrix (Fin 2) ℤ n) : ℕ := (A.1 1 1).natAbs

private theorem rep_entries (hA : A ∈ reps (n : ℤ)) :
    A.1 0 0 = repA A ∧ A.1 0 1 = repB A ∧ A.1 1 0 = 0 ∧ A.1 1 1 = repD A ∧
      0 < repA A ∧ 0 < repD A ∧ repB A < repD A ∧ repA A * repD A = n := by
  obtain ⟨h₁₀, h₀₀, h₀₁, h₁₁⟩ := hA
  have hmul := apply_zero_zero_mul_apply_one_one h₁₀
  have hn : (0 : ℤ) < n := Int.natCast_pos.2 (NeZero.pos n)
  have hd_pos : 0 < A.1 1 1 := pos_of_mul_pos_right (hmul.symm ▸ hn) h₀₀.le
  have ha : (repA A : ℤ) = A.1 0 0 := by rw [repA]; exact Int.natAbs_of_nonneg h₀₀.le
  have hb : (repB A : ℤ) = A.1 0 1 := by rw [repB]; exact Int.natAbs_of_nonneg h₀₁
  have hd : (repD A : ℤ) = A.1 1 1 := by rw [repD]; exact Int.natAbs_of_nonneg hd_pos.le
  refine ⟨ha.symm, hb.symm, h₁₀, hd.symm, ?_, ?_, ?_, ?_⟩
  · exact Nat.cast_pos.mp (ha ▸ h₀₀)
  · exact Nat.cast_pos.mp (hd ▸ hd_pos)
  · rw [abs_of_nonneg h₀₁, abs_of_pos hd_pos, ← hb, ← hd] at h₁₁
    exact Int.ofNat_lt.mp h₁₁
  · exact Nat.cast_injective (R := ℤ) (by rw [Nat.cast_mul, ha, hd, hmul])

private def repA2PNat (hA : A ∈ reps (n : ℤ)) : ℕ+ :=
  ⟨repA A ^ 2, pow_pos (rep_entries hA).2.2.2.2.1 2⟩

@[simp]
private theorem coe_repA2PNat (hA : A ∈ reps (n : ℤ)) :
    (repA2PNat hA : ℕ) = repA A ^ 2 :=
  rfl

private def natPNat (n : ℕ) [NeZero n] : ℕ+ :=
  ⟨n, NeZero.pos n⟩

@[simp]
private theorem coe_natPNat : (natPNat n : ℕ) = n :=
  rfl

private theorem coe_toGLReal_smul_of_mem_reps (hA : A ∈ reps (n : ℤ)) (τ : ℍ) :
    ((toGLReal (NeZero.ne (n : ℤ)) A • τ : ℍ) : ℂ) =
      ((repA A : ℂ) * τ + repB A) / repD A := by
  obtain ⟨ha, hb, hc, hd, -, -, -, -⟩ := rep_entries hA
  have hdet : 0 < ((toGLReal (NeZero.ne (n : ℤ)) A).det : ℝ) := by
    rw [det_toGLReal]
    exact_mod_cast NeZero.pos n
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, toGLReal_apply, Complex.ofReal_intCast]
  rw [ha, hb, hc, hd]
  simp

/-- In width `1`, the `q`-parameter at `(a τ + b) / d` (`a d = n`) factors as
`ζ_n^{a b} q_n^{a²}`. -/
private theorem qParam_one_toGLReal_smul (hA : A ∈ reps (n : ℤ)) (τ : ℍ) :
    𝕢 1 ((toGLReal (NeZero.ne (n : ℤ)) A • τ : ℍ) : ℂ) =
      𝕢 (n : ℝ) 1 ^ (repA A * repB A) * 𝕢 (n : ℝ) τ ^ (repA A ^ 2) := by
  obtain ⟨-, -, -, -, ha_pos, hd_pos, -, had⟩ := rep_entries hA
  have ha0 : (repA A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
  have hd0 : (repD A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
  have had' : (repA A : ℂ) * repD A = n := by exact_mod_cast had
  rw [coe_toGLReal_smul_of_mem_reps hA]
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add,
    Complex.ofReal_natCast, Complex.ofReal_one]
  congr 1
  rw [← had']
  push_cast
  field_simp
  ring

private theorem analyticAt_cuspFunction_qParam_pow_mul_j_smul (hA : A ∈ reps (n : ℤ)) :
    AnalyticAt ℂ (cuspFunction (n : ℝ)
      fun τ : ℍ ↦ 𝕢 (n : ℝ) τ ^ (repA A ^ 2) * j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) 0 := by
  obtain ⟨-, -, hc, -, -, hd_pos, -, had⟩ := rep_entries hA
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  set hn := NeZero.ne (n : ℤ)
  set ζ := 𝕢 (n : ℝ) (1 : ℂ) ^ (repA A * repB A)
  have hζ : ζ ≠ 0 := pow_ne_zero _ (Function.Periodic.qParam_ne_zero _)
  have hG_eq : (fun τ : ℍ ↦ 𝕢 (n : ℝ) τ ^ (repA A ^ 2) * j (toGLReal hn A • τ)) =
      fun τ : ℍ ↦ ζ⁻¹ * (𝕢 1 ((toGLReal hn A • τ : ℍ) : ℂ) * j (toGLReal hn A • τ)) := by
    funext τ
    rw [qParam_one_toGLReal_smul hA, ← mul_assoc, inv_mul_cancel_left₀ hζ]
  have hj_per : Periodic ((fun τ : ℍ ↦ j (toGLReal hn A • τ)) ∘ ofComplex) (n : ℝ) := by
    rw [TauCeti.UpperHalfPlane.periodic_comp_ofComplex_iff]
    intro τ
    have hsmul : ((toGLReal hn A • ((n : ℝ) +ᵥ τ) : ℍ) : ℂ) =
        ((toGLReal hn A • τ : ℍ) : ℂ) + ((repA A ^ 2 : ℕ) : ℂ) * 1 := by
      have hd0 : (repD A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
      have had' : (repA A : ℂ) * repD A = n := by exact_mod_cast had
      rw [coe_toGLReal_smul_of_mem_reps hA, coe_toGLReal_smul_of_mem_reps hA, coe_vadd,
        Complex.ofReal_natCast, ← had']
      push_cast
      field_simp
      ring
    calc j (toGLReal hn A • ((n : ℝ) +ᵥ τ))
        = (j ∘ ofComplex) ((toGLReal hn A • ((n : ℝ) +ᵥ τ) : ℍ) : ℂ) := by
          rw [Function.comp_apply, ofComplex_apply]
      _ = (j ∘ ofComplex) (((toGLReal hn A • τ : ℍ) : ℂ) + ((repA A ^ 2 : ℕ) : ℂ) * 1) := by
          rw [hsmul]
      _ = (j ∘ ofComplex) ((toGLReal hn A • τ : ℍ) : ℂ) :=
          (periodic_j_comp_ofComplex.nat_mul (repA A ^ 2)) _
      _ = j (toGLReal hn A • τ) := by rw [Function.comp_apply, ofComplex_apply]
  have hper : Periodic ((fun τ : ℍ ↦
      𝕢 (n : ℝ) τ ^ (repA A ^ 2) * j (toGLReal hn A • τ)) ∘ ofComplex) (n : ℝ) := fun z ↦ by
    simpa only [Function.comp_apply] using congrArg₂ (fun a b ↦ a ^ (repA A ^ 2) * b)
      (TauCeti.UpperHalfPlane.periodic_qParam_comp_ofComplex (h := (n : ℝ)) z) (hj_per z)
  refine UpperHalfPlane.analyticAt_cuspFunction_zero hn_pos hper ?_ ?_
  · exact ((Function.Periodic.differentiable_qParam.mdifferentiable.comp mdifferentiable_coe).pow
      _).mul (j_mdifferentiable.comp
        (mdifferentiable_toGLReal_smul (Int.natCast_pos.2 (NeZero.pos n)) A))
  · rw [hG_eq]
    have h10 : (toGLReal hn A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
      rw [toGLReal_apply, hc, Int.cast_zero]
    exact ((tendsto_qParam_mul_j_atImInfty.comp
      (UpperHalfPlane.tendsto_smul_atImInfty h10)).const_mul ζ⁻¹).isBigO_one ℝ

private theorem meromorphicAt_cuspFunction_j_toGLReal_smul (hA : A ∈ reps (n : ℤ)) :
    MeromorphicAt (cuspFunction (n : ℝ) fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) 0 :=
  UpperHalfPlane.meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul
    (analyticAt_cuspFunction_qParam_pow_mul_j_smul hA)

private theorem qExpansion_qParam_pow_mul_j_smul_coeff (hA : A ∈ reps (n : ℤ)) (k : ℕ) :
    (qExpansion (n : ℝ)
      (fun τ : ℍ ↦ 𝕢 (n : ℝ) τ ^ (repA A ^ 2) * j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).coeff k =
      if repA A ^ 2 ∣ k then
        𝕢 (n : ℝ) 1 ^ ((repA A * repB A : ℤ) * ((k / repA A ^ 2 : ℕ) - 1)) *
          (qExpansion 1 fun τ : ℍ ↦ 𝕢 1 τ * j τ).coeff (k / repA A ^ 2)
      else 0 := by
  obtain ⟨-, -, -, -, ha_pos, -, -, -⟩ := rep_entries hA
  have ha2 : 0 < repA A ^ 2 := pow_pos ha_pos 2
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  set c : ℕ → ℂ := fun k ↦
    if repA A ^ 2 ∣ k then
      𝕢 (n : ℝ) 1 ^ ((repA A * repB A : ℤ) * ((k / repA A ^ 2 : ℕ) - 1)) *
        (qExpansion 1 fun τ : ℍ ↦ 𝕢 1 τ * j τ).coeff (k / repA A ^ 2)
    else 0
  refine (TauCeti.UpperHalfPlane.qExpansion_coeff_unique hn_pos
    (analyticAt_cuspFunction_qParam_pow_mul_j_smul hA) (c := c) (fun τ ↦ ?_) k).symm
  have hζ0 : 𝕢 (n : ℝ) (1 : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hsum := (hasSum_qExpansion_qParam_mul_j (toGLReal (NeZero.ne (n : ℤ)) A • τ)).mul_left
    (𝕢 (n : ℝ) 1 ^ (repA A * repB A))⁻¹
  have hval : (𝕢 (n : ℝ) 1 ^ (repA A * repB A))⁻¹ *
      (𝕢 1 ((toGLReal (NeZero.ne (n : ℤ)) A • τ : ℍ) : ℂ) *
        j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      𝕢 (n : ℝ) τ ^ (repA A ^ 2) * j (toGLReal (NeZero.ne (n : ℤ)) A • τ) := by
    rw [qParam_one_toGLReal_smul hA, ← mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hζ0)]
  rw [hval] at hsum
  have hinj : Injective fun m : ℕ ↦ repA A ^ 2 * m := fun _ _ h ↦ Nat.eq_of_mul_eq_mul_left ha2 h
  refine (hinj.hasSum_iff fun x hx ↦ ?_).mp (hsum.congr_fun fun m ↦ ?_)
  · have hnd : ¬ repA A ^ 2 ∣ x := fun ⟨m, hm⟩ ↦ hx ⟨m, hm.symm⟩
    simp [c, hnd]
  · simp only [Function.comp_apply, c, smul_eq_mul, dvd_mul_right, ↓reduceIte]
    rw [Nat.mul_div_cancel_left m ha2, qParam_one_toGLReal_smul hA,
      mul_pow, ← pow_mul, ← pow_mul]
    have hz : (𝕢 (n : ℝ) (1 : ℂ) ^ (repA A * repB A))⁻¹ *
        (𝕢 (n : ℝ) 1 ^ (repA A * repB A * m)) =
        𝕢 (n : ℝ) 1 ^ (((repA A : ℤ) * repB A) * ((m : ℤ) - 1)) := by
      rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hζ0]
      congr 1
      push_cast
      ring
    calc 𝕢 (n : ℝ) 1 ^ (((repA A : ℤ) * repB A) * ((m : ℤ) - 1)) *
          (qExpansion 1 fun τ : ℍ ↦ 𝕢 1 τ * j τ).coeff m * 𝕢 (n : ℝ) τ ^ (repA A ^ 2 * m)
        = ((𝕢 (n : ℝ) 1 ^ (repA A * repB A))⁻¹ * 𝕢 (n : ℝ) 1 ^ (repA A * repB A * m)) *
          (qExpansion 1 fun τ : ℍ ↦ 𝕢 1 τ * j τ).coeff m * 𝕢 (n : ℝ) τ ^ (repA A ^ 2 * m) := by
          rw [hz]
      _ = _ := by ring

end RepsEntries

/-! ### Cyclotomic lift of the `q`-expansions and Galois invariance -/

noncomputable section CyclotomicLift

variable {n : ℕ} [NeZero n]

local instance : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
  CyclotomicField.isCyclotomicExtension n ℚ

/-- The `m`-th Laurent `q`-coefficient of `j`, chosen as an integer (`0` for `m < -1`). -/
private def jIntCoeff (m : ℤ) : ℤ :=
  (exists_laurentQExpansion_j_coeff_eq_intCast m).choose

private theorem cast_jIntCoeff (m : ℤ) :
    (jIntCoeff m : ℂ) = (UpperHalfPlane.laurentQExpansion 1 j).coeff m :=
  (exists_laurentQExpansion_j_coeff_eq_intCast m).choose_spec.symm

private theorem jIntCoeff_of_lt_neg_one {m : ℤ} (hm : m < -1) : jIntCoeff m = 0 := by
  apply Int.cast_injective (α := ℂ)
  rw [cast_jIntCoeff, Int.cast_zero]
  have h : ((m : ℤ) : WithTop ℤ) < ((-1 : ℤ) : WithTop ℤ) := WithTop.coe_lt_coe.mpr hm
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop (by simpa using h)

/-- The Laurent series `∑_{m ≥ -1} c_m ζ_n^{e m} X^m` over `CyclotomicField n ℚ`. -/
private def jTwistLaurent (n : ℕ) [NeZero n] (e : ℤ) :
    LaurentSeries (CyclotomicField n ℚ) :=
  HahnSeries.ofSuppBddBelow
    (fun m : ℤ ↦ IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ (e * m) *
      (jIntCoeff m : CyclotomicField n ℚ))
    ⟨-1, fun m hm ↦ by
      by_contra! hlt
      exact hm (by simp [jIntCoeff_of_lt_neg_one hlt])⟩

@[simp]
private theorem coeff_jTwistLaurent (e m : ℤ) :
    (jTwistLaurent n e).coeff m =
      IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ (e * m) *
        (jIntCoeff m : CyclotomicField n ℚ) :=
  rfl

/-- The lift to `LaurentSeries (CyclotomicField n ℚ)` of the width-`n` Laurent `q`-expansion of
`j(A τ)` for `A ∈ reps n`: `jTwistLaurent n (a b)` expanded along `X ↦ X^{a²}`. -/
private def jRepLaurent {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    LaurentSeries (CyclotomicField n ℚ) :=
  LaurentSeries.expand (CyclotomicField n ℚ) (repA2PNat hA)
    (jTwistLaurent n ((repA A : ℤ) * repB A))

private theorem isIntegral_zeta_zpow (m : ℤ) :
    IsIntegral ℤ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ m) := by
  refine IsIntegral.of_pow (NeZero.pos n) ?_
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
    (IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)).zpow_eq_one, _root_.one_zpow]
  exact isIntegral_one

private theorem isIntegral_coeff_jRepLaurent {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) (k : ℤ) :
    IsIntegral ℤ ((jRepLaurent hA).coeff k) := by
  by_cases hk : ((repA2PNat hA : ℕ) : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [jRepLaurent, LaurentSeries.coeff_expand_mul, coeff_jTwistLaurent]
    exact (isIntegral_zeta_zpow _).mul (isIntegral_intCast _)
  · rw [jRepLaurent, LaurentSeries.coeff_expand_of_not_dvd (repA2PNat hA) _ hk]
    exact isIntegral_zero

/-- The complex embedding of `CyclotomicField n ℚ` sending `zeta` to `exp(2 π i / n) = 𝕢 n 1`. -/
private def cyclotomicToComplex (n : ℕ) [NeZero n] : CyclotomicField n ℚ →+* ℂ :=
  ((IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)).existsUnique_algHom_apply_eq
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))
    (Complex.isPrimitiveRoot_exp n (NeZero.ne n))).choose.toRingHom

private theorem cyclotomicToComplex_zeta :
    cyclotomicToComplex n (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)) =
      𝕢 (n : ℝ) (1 : ℂ) := by
  have h :=
    ((IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)).existsUnique_algHom_apply_eq
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))
      (Complex.isPrimitiveRoot_exp n (NeZero.ne n))).choose_spec.1
  rw [cyclotomicToComplex, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  simpa [Function.Periodic.qParam] using h

private theorem map_jRepLaurent_eq_laurentQExpansion {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) :
    HahnSeries.mapRingHom (cyclotomicToComplex n) (jRepLaurent hA) =
      UpperHalfPlane.laurentQExpansion (n : ℝ)
        fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ) := by
  obtain ⟨-, -, -, -, ha_pos, -, -, -⟩ := rep_entries hA
  set a2 : ℕ := repA A ^ 2
  have ha2 : 0 < a2 := pow_pos ha_pos 2
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  rw [UpperHalfPlane.laurentQExpansion_eq_of_analyticAt_qParam_pow_mul hn_pos
    (analyticAt_cuspFunction_qParam_pow_mul_j_smul hA)]
  ext k
  rw [HahnSeries.mapRingHom_apply, HahnSeries.map_coeff, HahnSeries.coeff_single_mul, one_mul,
    PowerSeries.coeff_coe]
  by_cases hk : ((repA2PNat hA : ℕ) : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [jRepLaurent, LaurentSeries.coeff_expand_mul, coeff_jTwistLaurent, map_mul, map_zpow₀,
      cyclotomicToComplex_zeta, map_intCast, cast_jIntCoeff, coe_repA2PNat]
    have hsub : (a2 : ℤ) * m - -(a2 : ℤ) = (a2 : ℤ) * (m + 1) := by ring
    rw [hsub]
    rcases lt_or_ge (m + 1) 0 with hm | hm
    · have hm' : m < -1 := by omega
      have hneg : (a2 : ℤ) * (m + 1) < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast ha2) hm
      have h0 : (UpperHalfPlane.laurentQExpansion 1 j).coeff m = 0 := by
        rw [← cast_jIntCoeff, jIntCoeff_of_lt_neg_one hm', Int.cast_zero]
      simp [hneg, h0]
    · lift m + 1 to ℕ using hm with u hu
      have hm_eq : m = (u : ℤ) - 1 := by omega
      have hnn : ¬ ((a2 * u : ℕ) : ℤ) < 0 := not_lt.mpr (Nat.cast_nonneg _)
      simp only [← Nat.cast_mul, hnn, ↓reduceIte, Int.natAbs_natCast,
        hm_eq, laurentQExpansion_j_coeff_natCast_sub_one]
      dsimp only [a2]
      rw [qExpansion_qParam_pow_mul_j_smul_coeff hA]
      simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left u (pow_pos ha_pos 2),
        Nat.cast_mul]
  · rw [jRepLaurent, LaurentSeries.coeff_expand_of_not_dvd (repA2PNat hA) _ hk, map_zero]
    split_ifs with hlt
    · rfl
    · rw [qExpansion_qParam_pow_mul_j_smul_coeff hA]
      refine (ite_eq_right_iff.mpr fun ⟨u, hu⟩ ↦ (hk ?_).elim).symm
      have hnn : 0 ≤ k - -(a2 : ℤ) := not_lt.mp hlt
      have heq : k + a2 = (a2 : ℤ) * u := by
        have hz := congrArg (Nat.cast : ℕ → ℤ) hu
        rw [Int.natAbs_of_nonneg hnn, Nat.cast_mul] at hz
        linarith
      exact ⟨(u : ℤ) - 1, by rw [coe_repA2PNat]; linear_combination heq⟩

/-- Multiplication of the upper-right entry modulo `d` on the sigma parametrization of `reps n`. -/
private def mulModSigma (u : (ZMod n)ˣ)
    (x : Σ p : ↥(n : ℤ).natAbs.divisorsAntidiagonal, Fin p.1.2) :
    Σ p : ↥(n : ℤ).natAbs.divisorsAntidiagonal, Fin p.1.2 :=
  ⟨x.1, ⟨((u : ZMod n).val * x.2.1) % x.1.1.2,
    Nat.mod_lt _ (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal x.1.2))⟩⟩

private theorem mulModSigma_inv_left (u : (ZMod n)ˣ)
    (x : Σ p : ↥(n : ℤ).natAbs.divisorsAntidiagonal, Fin p.1.2) :
    mulModSigma u⁻¹ (mulModSigma u x) = x := by
  obtain ⟨⟨⟨a, d⟩, hp⟩, ⟨b, hb⟩⟩ := x
  have had : a * d = n := by simpa using (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hdvd : d ∣ n := ⟨a, (mul_comm a d).symm ▸ had.symm⟩
  have hval : (((u⁻¹ : (ZMod n)ˣ) : ZMod n).val * (u : ZMod n).val) % n = 1 % n := by
    have h1 : (((((u⁻¹ : (ZMod n)ˣ) : ZMod n).val * (u : ZMod n).val : ℕ) : ZMod n)) =
        ((1 : ℕ) : ZMod n) := by
      push_cast
      simp
    have h1' := congrArg ZMod.val h1
    rwa [ZMod.val_natCast, ZMod.val_natCast] at h1'
  have hmod_d : (((u⁻¹ : (ZMod n)ˣ) : ZMod n).val * (u : ZMod n).val) % d = 1 % d := by
    rw [← Nat.mod_mod_of_dvd _ hdvd, hval, Nat.mod_mod_of_dvd _ hdvd]
  refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
  change (((u⁻¹ : (ZMod n)ˣ) : ZMod n).val * (((u : ZMod n).val * b) % d)) % d = b
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, hmod_d, ← Nat.mul_mod,
    one_mul, Nat.mod_eq_of_lt hb]

private def mulModSigmaEquiv (u : (ZMod n)ˣ) :
    (Σ p : ↥(n : ℤ).natAbs.divisorsAntidiagonal, Fin p.1.2) ≃
      Σ p : ↥(n : ℤ).natAbs.divisorsAntidiagonal, Fin p.1.2 where
  toFun := mulModSigma u
  invFun := mulModSigma u⁻¹
  left_inv := mulModSigma_inv_left u
  right_inv x := by simpa using mulModSigma_inv_left u⁻¹ x

/-- The permutation of `reps n` induced by `u ∈ (ZMod n)ˣ`, multiplying `b` by `u` modulo `d`. -/
private def permRep (u : (ZMod n)ˣ) : reps (n : ℤ) ≃ reps (n : ℤ) :=
  (repsEquiv (NeZero.ne (n : ℤ))).trans <|
    (mulModSigmaEquiv u).trans (repsEquiv (NeZero.ne (n : ℤ))).symm

private theorem permRep_inv_apply (u : (ZMod n)ˣ) (A : reps (n : ℤ)) :
    permRep u⁻¹ (permRep u A) = A := by
  simp only [permRep, mulModSigmaEquiv, Equiv.trans_apply, Equiv.coe_fn_mk,
    Equiv.apply_symm_apply, mulModSigma_inv_left, Equiv.symm_apply_apply]

private theorem permRep_entries (u : (ZMod n)ˣ) (A : reps (n : ℤ)) :
    (permRep u A).1.1 =
      !![(repA A.1 : ℤ), (((u : ZMod n).val * repB A.1) % repD A.1 : ℕ); 0, (repD A.1 : ℤ)] := by
  have hsign : (n : ℤ).sign = 1 := Int.sign_natCast_of_ne_zero (NeZero.ne n)
  rw [permRep, Equiv.trans_apply, Equiv.trans_apply, coe_repsEquiv_symm_apply]
  have hfst := coe_repsEquiv_apply_fst (NeZero.ne (n : ℤ)) A
  have h1 : (repsEquiv (NeZero.ne (n : ℤ)) A).1.1.1 = repA A.1 := congrArg Prod.fst hfst
  have h2 : (repsEquiv (NeZero.ne (n : ℤ)) A).1.1.2 = repD A.1 := congrArg Prod.snd hfst
  have h3 : (repsEquiv (NeZero.ne (n : ℤ)) A).2.1 = repB A.1 :=
    coe_repsEquiv_apply_snd (NeZero.ne (n : ℤ)) A
  simp only [mulModSigmaEquiv, Equiv.coe_fn_mk, mulModSigma, h1, h2, h3, hsign, one_mul]

private theorem isPrimitive_of_permRep (u : (ZMod n)ˣ) (A : reps (n : ℤ))
    (h : IsPrimitive (permRep u A).1.1) : IsPrimitive A.1.1 := by
  obtain ⟨ha, hb, hc, hd, -, -, -, -⟩ := rep_entries A.2
  set r : ℕ := (u : ZMod n).val
  set q : ℕ := (r * repB A.1) / repD A.1
  let L : Matrix (Fin 2) (Fin 2) ℤ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) ℤ :=
    { toFun M := !![M 0 0, (r : ℤ) * M 0 1 - (q : ℤ) * M 1 1; M 1 0, M 1 1]
      map_add' M N := by ext i j; fin_cases i <;> fin_cases j <;> simp; ring
      map_smul' c M := by
        ext i j
        fin_cases i <;> fin_cases j <;> dsimp [Matrix.smul_apply, smul_eq_mul]; ring }
  have hLA : L A.1.1 = (permRep u A).1.1 := by
    have hdiv : (((r * repB A.1) % repD A.1 : ℕ) : ℤ) =
        (r : ℤ) * repB A.1 - (q : ℤ) * repD A.1 := by
      have hz := congrArg (Nat.cast : ℕ → ℤ) (Nat.mod_add_div (r * repB A.1) (repD A.1))
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul] at hz
      change (((r * repB A.1) % repD A.1 : ℕ) : ℤ) + (repD A.1 : ℤ) * q = (r : ℤ) * repB A.1 at hz
      linarith
    rw [permRep_entries]
    ext i j
    fin_cases i <;> fin_cases j
    · dsimp [L]; exact ha
    · dsimp [L]; rw [hb, hd, ← hdiv]; push_cast; rfl
    · dsimp [L]; exact hc
    · dsimp [L]; exact hd
  exact IsPrimitive.of_map (g := L) (hLA.symm ▸ h)

private theorem isPrimitive_permRep_iff (u : (ZMod n)ˣ) (A : reps (n : ℤ)) :
    IsPrimitive (permRep u A).1.1 ↔ IsPrimitive A.1.1 :=
  ⟨isPrimitive_of_permRep u A, fun h ↦
    isPrimitive_of_permRep u⁻¹ (permRep u A) ((permRep_inv_apply u A).symm ▸ h)⟩

/-- An automorphism `σ ∈ Gal(CyclotomicField n ℚ/ℚ)` sends `jRepLaurent` at `A` to `jRepLaurent`
at `permRep u A`, where `σ(ζ_n) = ζ_n^u`. -/
private theorem map_gal_jRepLaurent (σ : Gal(CyclotomicField n ℚ/ℚ)) (A : reps (n : ℤ)) :
    HahnSeries.mapRingHom (σ : CyclotomicField n ℚ →+* CyclotomicField n ℚ) (jRepLaurent A.2) =
      jRepLaurent (permRep
        (IsCyclotomicExtension.autEquivPow (CyclotomicField n ℚ)
          (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)) σ) A).2 := by
  set hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  set u := IsCyclotomicExtension.autEquivPow (CyclotomicField n ℚ) hirr σ
  set ζ := IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  have hσζ : σ ζ = ζ ^ (u : ZMod n).val :=
    IsCyclotomicExtension.autEquivPow_spec (CyclotomicField n ℚ) hirr σ
  obtain ⟨-, -, -, -, -, -, -, had⟩ := rep_entries A.2
  have hB := permRep_entries u A
  have ha_eq : repA (permRep u A).1 = repA A.1 := by
    rw [repA, hB]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Int.natAbs_natCast]
  have hb_eq : repB (permRep u A).1 = ((u : ZMod n).val * repB A.1) % repD A.1 := by
    rw [repB, hB]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Int.natAbs_natCast]
  have hp' : repA2PNat (permRep u A).2 = repA2PNat A.2 :=
    Subtype.ext (congrArg (· ^ 2) ha_eq)
  ext k
  rw [HahnSeries.mapRingHom_apply, HahnSeries.map_coeff]
  by_cases hk : ((repA2PNat A.2 : ℕ) : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [jRepLaurent, jRepLaurent, hp', LaurentSeries.coeff_expand_mul,
      LaurentSeries.coeff_expand_mul, coeff_jTwistLaurent, coeff_jTwistLaurent, ha_eq, hb_eq,
      map_mul, map_zpow₀, RingHom.coe_coe, hσζ, map_intCast, ← zpow_natCast, ← _root_.zpow_mul]
    congr 1
    set r : ℕ := (u : ZMod n).val
    set b' : ℕ := (r * repB A.1) % repD A.1
    set q : ℕ := (r * repB A.1) / repD A.1
    have hdiv : (r : ℤ) * repB A.1 = b' + (repD A.1 : ℤ) * q := by
      have hz := congrArg (Nat.cast : ℕ → ℤ) (Nat.mod_add_div (r * repB A.1) (repD A.1))
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul] at hz
      change (b' : ℤ) + (repD A.1 : ℤ) * q = (r : ℤ) * repB A.1 at hz
      linarith
    have hexp : (r : ℤ) * ((repA A.1 * repB A.1) * m) =
        (repA A.1 * b' : ℤ) * m + (n : ℤ) * (q * m) := by
      have had' : (repA A.1 : ℤ) * repD A.1 = n := by exact_mod_cast had
      linear_combination (repA A.1 : ℤ) * m * hdiv + (q : ℤ) * m * had'
    have hζn : ζ ^ ((n : ℤ) * (q * m)) = 1 := by
      rw [_root_.zpow_mul, hζ.zpow_eq_one, _root_.one_zpow]
    rw [hexp, zpow_add₀ (hζ.ne_zero (NeZero.ne n)), hζn, mul_one]
  · rw [jRepLaurent, jRepLaurent, hp', LaurentSeries.coeff_expand_of_not_dvd (repA2PNat A.2) _ hk,
      LaurentSeries.coeff_expand_of_not_dvd (repA2PNat A.2) _ hk, map_zero]

/-- The lifted cyclic-isogeny polynomial over `LaurentSeries (CyclotomicField n ℚ)`. -/
private def liftedIsogenyPoly (n : ℕ) [NeZero n] :
    Polynomial (LaurentSeries (CyclotomicField n ℚ)) :=
  ∏ A ∈ (primitiveReps (n : ℤ)).attach,
    (X - C (jRepLaurent (mem_primitiveReps.mp A.2).1))

private theorem map_gal_liftedIsogenyPoly (σ : Gal(CyclotomicField n ℚ/ℚ)) :
    (liftedIsogenyPoly n).map
      (HahnSeries.mapRingHom (σ : CyclotomicField n ℚ →+* CyclotomicField n ℚ)) =
      liftedIsogenyPoly n := by
  classical
  set hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  set u := IsCyclotomicExtension.autEquivPow (CyclotomicField n ℚ) hirr σ
  have hstep (A : {A // A ∈ primitiveReps (n : ℤ)}) :
      HahnSeries.mapRingHom (σ : CyclotomicField n ℚ →+* CyclotomicField n ℚ)
        (jRepLaurent (mem_primitiveReps.mp A.2).1) =
        jRepLaurent (permRep u ⟨A.1, (mem_primitiveReps.mp A.2).1⟩).2 :=
    map_gal_jRepLaurent σ ⟨A.1, (mem_primitiveReps.mp A.2).1⟩
  let e : {A // A ∈ primitiveReps (n : ℤ)} ≃ {A // A ∈ primitiveReps (n : ℤ)} :=
    { toFun A := ⟨(permRep u ⟨A.1, (mem_primitiveReps.mp A.2).1⟩).1,
        mem_primitiveReps.mpr ⟨(permRep u _).2,
          (isPrimitive_permRep_iff u ⟨A.1, (mem_primitiveReps.mp A.2).1⟩).mpr
            (mem_primitiveReps.mp A.2).2⟩⟩
      invFun A := ⟨(permRep u⁻¹ ⟨A.1, (mem_primitiveReps.mp A.2).1⟩).1,
        mem_primitiveReps.mpr ⟨(permRep u⁻¹ _).2,
          (isPrimitive_permRep_iff u⁻¹ ⟨A.1, (mem_primitiveReps.mp A.2).1⟩).mpr
            (mem_primitiveReps.mp A.2).2⟩⟩
      left_inv A := by
        apply Subtype.ext
        dsimp only
        exact congrArg Subtype.val (permRep_inv_apply u ⟨A.1, (mem_primitiveReps.mp A.2).1⟩)
      right_inv A := by
        apply Subtype.ext
        dsimp only
        have h := permRep_inv_apply u⁻¹ ⟨A.1, (mem_primitiveReps.mp A.2).1⟩
        rw [inv_inv] at h
        exact congrArg Subtype.val h }
  unfold liftedIsogenyPoly
  rw [Polynomial.map_prod, ← Finset.univ_eq_attach, ← Equiv.prod_comp e
    (fun B ↦ X - C (jRepLaurent (mem_primitiveReps.mp B.2).1))]
  refine Finset.prod_congr rfl fun A _ ↦ ?_
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hstep A, e]

private theorem isIntegral_coeff_liftedIsogenyPoly (k : ℕ) (m : ℤ) :
    IsIntegral ℤ (((liftedIsogenyPoly n).coeff k).coeff m) := by
  set K := CyclotomicField n ℚ
  set O := (integralClosure ℤ K).toSubring
  have hj (A : {A // A ∈ primitiveReps (n : ℤ)}) :
      ∃ f : LaurentSeries O,
        HahnSeries.mapRingHom O.subtype f = jRepLaurent (mem_primitiveReps.mp A.2).1 :=
    HahnSeries.mem_map_rangeS.mpr fun g ↦
      ⟨⟨_, isIntegral_coeff_jRepLaurent (mem_primitiveReps.mp A.2).1 g⟩, rfl⟩
  let P : Polynomial (LaurentSeries O) :=
    ∏ A ∈ (primitiveReps (n : ℤ)).attach, (X - C (hj A).choose)
  have hP : P.map (HahnSeries.mapRingHom O.subtype) = liftedIsogenyPoly n := by
    rw [liftedIsogenyPoly, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun A _ ↦ ?_
    simp [(hj A).choose_spec]
  rw [← hP, Polynomial.coeff_map, HahnSeries.mapRingHom_apply, HahnSeries.map_coeff]
  exact ((P.coeff k).coeff m).2

private theorem coeff_liftedIsogenyPoly_mem_range_intCast (k : ℕ) (m : ℤ) :
    ((liftedIsogenyPoly n).coeff k).coeff m ∈
      Set.range (Int.cast : ℤ → CyclotomicField n ℚ) := by
  have := IsCyclotomicExtension.isGalois {n} ℚ (CyclotomicField n ℚ)
  refine (isIntegral_coeff_liftedIsogenyPoly k m).mem_range_ratCast_iff.mp ?_
  change _ ∈ Set.range (algebraMap ℚ (CyclotomicField n ℚ))
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  have h := congrArg (fun Q ↦ (Q.coeff k).coeff m) (map_gal_liftedIsogenyPoly (n := n) σ)
  simpa [HahnSeries.mapRingHom_apply] using h

end CyclotomicLift

/-! ### Width-`1` meromorphy and construction of `modularPolynomial` -/

noncomputable section ModularPolynomialHelpers

/-- Functions on `ℍ` whose width-`h` cusp function is meromorphic at `0`, bundled as a subring so
that `laurentQExpansion h` acts on polynomials over them as a ring homomorphism. -/
private def meromorphicCuspSubring (h : ℝ) : Subring (ℍ → ℂ) where
  carrier := {f | MeromorphicAt (cuspFunction h f) 0}
  mul_mem' := UpperHalfPlane.meromorphicAt_cuspFunction_mul
  one_mem' := UpperHalfPlane.meromorphicAt_cuspFunction_const 1
  add_mem' := UpperHalfPlane.meromorphicAt_cuspFunction_add
  zero_mem' := UpperHalfPlane.meromorphicAt_cuspFunction_const 0
  neg_mem' := UpperHalfPlane.meromorphicAt_cuspFunction_neg

private def laurentQExpansionSubringHom (h : ℝ) :
    meromorphicCuspSubring h →+* LaurentSeries ℂ where
  toFun f := UpperHalfPlane.laurentQExpansion h f.1
  map_one' := UpperHalfPlane.laurentQExpansion_one h
  map_mul' f g := UpperHalfPlane.laurentQExpansion_mul f.2 g.2
  map_zero' := UpperHalfPlane.laurentQExpansion_zero h
  map_add' f g := UpperHalfPlane.laurentQExpansion_add f.2 g.2

/-- For a finite product `∏ i ∈ s, (X - C (g i τ))` whose factors have cusp functions meromorphic
at `0`, every coefficient has a cusp function meromorphic at `0` with Laurent `q`-expansion equal
to the corresponding coefficient of `∏ i ∈ s, (X - C (laurentQExpansion h (g i)))`. -/
private theorem meromorphicAt_and_laurentQExpansion_coeff_prod_X_sub_C {ι : Type*} {h : ℝ}
    (s : Finset ι) (g : ι → ℍ → ℂ)
    (hg : ∀ i ∈ s, MeromorphicAt (cuspFunction h (g i)) 0) (k : ℕ) :
    MeromorphicAt (cuspFunction h fun τ ↦ (∏ i ∈ s, (X - C (g i τ))).coeff k) 0 ∧
      UpperHalfPlane.laurentQExpansion h (fun τ ↦ (∏ i ∈ s, (X - C (g i τ))).coeff k) =
        (∏ i ∈ s, (X - C (UpperHalfPlane.laurentQExpansion h (g i)))).coeff k := by
  let P : Polynomial (meromorphicCuspSubring h) :=
    ∏ i ∈ s.attach, (X - C ⟨g i.1, hg i.1 i.2⟩)
  have hfun : (fun τ ↦ (∏ i ∈ s, (X - C (g i τ))).coeff k) = (P.coeff k).1 := by
    funext τ
    let ev : meromorphicCuspSubring h →+* ℂ :=
      (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ).comp (meromorphicCuspSubring h).subtype
    have hmap : P.map ev = ∏ i ∈ s, (X - C (g i τ)) := by
      rw [← Finset.prod_attach s]
      simp [P, Polynomial.map_prod, ev]
    simpa [ev] using (congrArg (fun Q ↦ Q.coeff k) hmap).symm
  have hL : P.map (laurentQExpansionSubringHom h) =
      ∏ i ∈ s, (X - C (UpperHalfPlane.laurentQExpansion h (g i))) := by
    rw [← Finset.prod_attach s]
    simp [P, Polynomial.map_prod, laurentQExpansionSubringHom]
  rw [hfun, ← hL, Polynomial.coeff_map]
  exact ⟨(P.coeff k).2, rfl⟩

/-- A holomorphic `1`-periodic function on `ℍ` whose width-`n` cusp function is meromorphic at `0`
also has a width-`1` cusp function meromorphic at `0`. -/
private theorem meromorphicAt_cuspFunction_one_of_nat {n : ℕ} [NeZero n] {f : ℍ → ℂ}
    (hf : MDiff f) (hfper : Periodic (f ∘ ofComplex) (1 : ℝ))
    (hmer : MeromorphicAt (cuspFunction (n : ℝ) f) 0) :
    MeromorphicAt (cuspFunction 1 f) 0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ,
      ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction (n : ℝ) f) 0 := by
    cases meromorphicOrderAt (cuspFunction (n : ℝ) f) 0 using WithTop.recTopCoe with
    | top => exact ⟨0, le_top⟩
    | coe m => exact ⟨(-m).toNat, WithTop.coe_le_coe.mpr (by omega)⟩
  have hnk : ((-(n * k : ℕ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction (n : ℝ) f) 0 := by
    refine le_trans (WithTop.coe_le_coe.mpr ?_) hk
    have : 1 ≤ n := NeZero.pos n
    push_cast
    nlinarith
  have han_n := UpperHalfPlane.analyticAt_cuspFunction_qParam_pow_mul hmer hnk
  have hG_eq : (fun τ : ℍ ↦ 𝕢 (n : ℝ) τ ^ (n * k) * f τ) = fun τ : ℍ ↦ 𝕢 1 τ ^ k * f τ := by
    funext τ
    rw [pow_mul, show (n : ℝ) = (n : ℕ) * (1 : ℝ) by simp,
      TauCeti.Periodic.qParam_nat_mul_pow (NeZero.ne n)]
  rw [hG_eq] at han_n
  set G : ℍ → ℂ := fun τ ↦ 𝕢 1 τ ^ k * f τ
  have hGper : Periodic (G ∘ ofComplex) (1 : ℝ) := fun z ↦ by
    simpa only [Function.comp_apply, G] using congrArg₂ (fun a b ↦ a ^ k * b)
      (TauCeti.UpperHalfPlane.periodic_qParam_comp_ofComplex (h := (1 : ℝ)) z) (hfper z)
  have hGper_n : Periodic (G ∘ ofComplex) (n : ℝ) := by simpa using hGper.nat_mul n
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hGbdd : IsBoundedAtImInfty G :=
    (((han_n.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hn_pos)).congr
      fun τ ↦ eq_cuspFunction τ hn_pos.ne' hGper_n).isBigO_one ℝ)
  have hGhol : MDiff G :=
    ((Function.Periodic.differentiable_qParam.mdifferentiable.comp mdifferentiable_coe).pow k).mul
      hf
  exact UpperHalfPlane.meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul
    (UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hGper hGhol hGbdd)

private theorem aevalAeval_eq_eval_map_aeval {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (x y : A) (p : R[X][X]) :
    p.aevalAeval x y = (p.map ↑(aeval x : R[X] →ₐ[R] A)).eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Polynomial.map_add, eval_add, hp, hq]
  | monomial k q =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aevalAeval_C, aevalAeval_Y,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eval_mul, eval_C, eval_pow, eval_X, RingHom.coe_coe]

private theorem isPrimitive_adjugate {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : IsPrimitive M) :
    IsPrimitive M.adjugate := by
  let L : Matrix (Fin 2) (Fin 2) ℤ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) ℤ :=
    { toFun := Matrix.adjugate
      map_add' A B := by ext i j; fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two] <;> ring
      map_smul' c A := by
        rw [adjugate_fin_two, adjugate_fin_two]
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] }
  have hLM : L M.adjugate = M := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [L, adjugate_fin_two]
  exact IsPrimitive.of_map (g := L) (hLM.symm ▸ hM)

end ModularPolynomialHelpers

public noncomputable section ModularPolynomial

/-- Each coefficient of `cyclicIsogenyPolynomial n j` is a polynomial in `j` with integer
coefficients. -/
theorem exists_aeval_j_eq_coeff_cyclicIsogenyPolynomial (n : ℕ) [NeZero n] (k : ℕ) :
    ∃ P : ℤ[X], ∀ τ : ℍ, aeval (j τ) P = (cyclicIsogenyPolynomial n j τ).coeff k := by
  set fk : ℍ → ℂ := fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k
  have hfk_prod : fk = fun τ ↦ (∏ A ∈ primitiveReps (n : ℤ),
      (X - C (j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))).coeff k := by
    funext τ
    dsimp only [fk]
    rw [cyclicIsogenyPolynomial_def]
  have hhol : MDiff fk := mdifferentiable_coeff_cyclicIsogenyPolynomial j_mdifferentiable k
  have hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), fk (γ • τ) = fk τ := fun γ τ ↦
    congrArg (fun P ↦ P.coeff k) (cyclicIsogenyPolynomial_smul j_smul_SL2Z γ τ)
  have hper : Periodic (fk ∘ ofComplex) (1 : ℝ) :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
      rw [← modular_T_smul]
      exact hinv _ τ
  obtain ⟨hmer_n, hlaur_n⟩ := meromorphicAt_and_laurentQExpansion_coeff_prod_X_sub_C
    (h := (n : ℝ)) (primitiveReps (n : ℤ))
    (fun A τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))
    (fun A hA ↦ meromorphicAt_cuspFunction_j_toGLReal_smul (mem_primitiveReps.mp hA).1) k
  rw [← hfk_prod] at hmer_n hlaur_n
  have hmer_1 : MeromorphicAt (cuspFunction 1 fk) 0 :=
    meromorphicAt_cuspFunction_one_of_nat hhol hper hmer_n
  refine exists_aeval_j_eq hhol hinv hmer_1 fun m _ ↦ ?_
  have hexp : UpperHalfPlane.laurentQExpansion (n : ℝ) fk =
      LaurentSeries.expand ℂ (natPNat n) (UpperHalfPlane.laurentQExpansion 1 fk) := by
    simpa [coe_natPNat] using
      UpperHalfPlane.laurentQExpansion_pnat_mul (h := 1) hper hmer_1 (natPNat n)
  have hcoeff_eq : (UpperHalfPlane.laurentQExpansion 1 fk).coeff m =
      (UpperHalfPlane.laurentQExpansion (n : ℝ) fk).coeff ((n : ℤ) * m) := by
    rw [hexp]
    exact (LaurentSeries.coeff_expand_mul (natPNat n) _ m).symm
  have hpoly_map : ((liftedIsogenyPoly n).map
      (HahnSeries.mapRingHom (cyclotomicToComplex n))) =
      ∏ A ∈ primitiveReps (n : ℤ),
        (X - C (UpperHalfPlane.laurentQExpansion (n : ℝ)
          fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))) := by
    rw [liftedIsogenyPoly, Polynomial.map_prod, ← Finset.prod_attach (primitiveReps (n : ℤ))]
    refine Finset.prod_congr rfl fun A _ ↦ ?_
    simp [map_jRepLaurent_eq_laurentQExpansion (mem_primitiveReps.mp A.2).1]
  obtain ⟨z, hz⟩ := coeff_liftedIsogenyPoly_mem_range_intCast (n := n) k ((n : ℤ) * m)
  refine ⟨z, ?_⟩
  rw [hcoeff_eq]
  change (z : ℂ) = (UpperHalfPlane.laurentQExpansion (n : ℝ) fk).coeff ((n : ℤ) * m)
  rw [hlaur_n, ← hpoly_map, Polynomial.coeff_map, HahnSeries.mapRingHom_apply,
    HahnSeries.map_coeff, ← hz, map_intCast]

/-- **The modular polynomial `Φ_n ∈ ℤ[X][X]`** of level `n ≥ 1`. Specializing its coefficients at
`j(τ)` yields `cyclicIsogenyPolynomial n j τ = ∏_{(a b; 0 d)} (X - j((a τ + b) / d))`. -/
def modularPolynomial (n : ℕ) [NeZero n] : ℤ[X][X] :=
  ∑ k ∈ Finset.range ((primitiveReps (n : ℤ)).card + 1),
    monomial k (exists_aeval_j_eq_coeff_cyclicIsogenyPolynomial n k).choose

variable {n : ℕ} [NeZero n]

/-- Evaluating the `k`-th coefficient of `modularPolynomial n` at `j(τ)` gives the `k`-th
coefficient of `cyclicIsogenyPolynomial n j τ`. -/
@[simp]
theorem aeval_coeff_modularPolynomial_j (k : ℕ) (τ : ℍ) :
    aeval (j τ) ((modularPolynomial n).coeff k) = (cyclicIsogenyPolynomial n j τ).coeff k := by
  rw [modularPolynomial, Polynomial.finsetSum_coeff]
  simp only [coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq']
  by_cases hk : k < (primitiveReps (n : ℤ)).card + 1
  · simp only [Finset.mem_range.mpr hk, ↓reduceIte]
    exact (exists_aeval_j_eq_coeff_cyclicIsogenyPolynomial n k).choose_spec τ
  · simp only [Finset.mem_range.not.mpr hk, ↓reduceIte, map_zero]
    refine (coeff_eq_zero_of_natDegree_lt ?_).symm
    rw [natDegree_cyclicIsogenyPolynomial]
    omega

/-- **Specialization of `modularPolynomial n` at `j(τ)`.** Mapping the coefficients of `Φ_n` along
`aeval (j τ)` gives `cyclicIsogenyPolynomial n j τ`. -/
@[simp]
theorem map_aeval_j_modularPolynomial (τ : ℍ) :
    (modularPolynomial n).map ↑(aeval (j τ) : ℤ[X] →ₐ[ℤ] ℂ) = cyclicIsogenyPolynomial n j τ := by
  ext k
  rw [Polynomial.coeff_map, RingHom.coe_coe]
  exact aeval_coeff_modularPolynomial_j k τ

/-- **Uniqueness of `modularPolynomial n`.** It is the only polynomial in `ℤ[X][X]` whose
specialization along `aeval (j τ)` is `cyclicIsogenyPolynomial n j τ` for every `τ ∈ ℍ`. -/
theorem eq_modularPolynomial_iff {Φ : ℤ[X][X]} :
    Φ = modularPolynomial n ↔
      ∀ τ : ℍ, Φ.map ↑(aeval (j τ) : ℤ[X] →ₐ[ℤ] ℂ) = cyclicIsogenyPolynomial n j τ := by
  refine ⟨fun h τ ↦ h ▸ map_aeval_j_modularPolynomial τ, fun h ↦ ?_⟩
  have hcoeff : ∀ k, Φ.coeff k = (modularPolynomial n).coeff k := fun k ↦
    aeval_j_injective Int.cast_injective (funext fun τ ↦ by
      simpa using congrArg (fun P ↦ P.coeff k) (h τ))
  ext k m
  rw [hcoeff k]

private theorem coeff_card_modularPolynomial :
    (modularPolynomial n).coeff (primitiveReps (n : ℤ)).card = 1 := by
  refine aeval_j_injective Int.cast_injective (funext fun τ ↦ ?_)
  dsimp only
  rw [aeval_coeff_modularPolynomial_j, ← natDegree_cyclicIsogenyPolynomial (n := n) j τ,
    ← leadingCoeff, (monic_cyclicIsogenyPolynomial j τ).leadingCoeff, map_one]

private theorem coeff_modularPolynomial_of_lt {k : ℕ} (hk : (primitiveReps (n : ℤ)).card < k) :
    (modularPolynomial n).coeff k = 0 := by
  rw [modularPolynomial, Polynomial.finsetSum_coeff]
  simp only [coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq']
  have hk' : k ∉ Finset.range ((primitiveReps (n : ℤ)).card + 1) := by
    rw [Finset.mem_range]
    omega
  simp only [hk', ↓reduceIte]

variable (n) in
/-- **The degree of `modularPolynomial n`** is the number of primitive upper-triangular
representatives of determinant `n`. -/
@[simp]
theorem natDegree_modularPolynomial :
    (modularPolynomial n).natDegree = (primitiveReps (n : ℤ)).card := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    exact fun k hk ↦ coeff_modularPolynomial_of_lt hk
  · rw [coeff_card_modularPolynomial]
    exact one_ne_zero

variable (n) in
/-- **`modularPolynomial n` is monic** in the outer variable. -/
theorem monic_modularPolynomial : (modularPolynomial n).Monic := by
  rw [Monic, leadingCoeff, natDegree_modularPolynomial, coeff_card_modularPolynomial]

/-- For every primitive integer matrix `A` of determinant `n` and every `τ ∈ ℍ`, `j(A τ)` is a root
of `Φ_n` specialized at `j(τ)`. -/
theorem isRoot_map_aeval_j_modularPolynomial {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : IsPrimitive A.1) (τ : ℍ) :
    ((modularPolynomial n).map ↑(aeval (j τ) : ℤ[X] →ₐ[ℤ] ℂ)).IsRoot
      (j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
  rw [map_aeval_j_modularPolynomial]
  exact isRoot_cyclicIsogenyPolynomial j_smul_SL2Z hA τ

/-- **Vanishing of `Φ_n(j(τ), j(A τ))`** for every primitive matrix `A` of determinant `n`. -/
theorem aevalAeval_j_modularPolynomial_eq_zero {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : IsPrimitive A.1) (τ : ℍ) :
    (modularPolynomial n).aevalAeval (j τ) (j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) = 0 := by
  rw [aevalAeval_eq_eval_map_aeval]
  exact isRoot_map_aeval_j_modularPolynomial hA τ

/-- **Symmetric vanishing `Φ_n(j(A τ), j(τ)) = 0`** for every primitive matrix `A` of determinant
`n`, proved via the adjugate matrix of `A`. -/
theorem aevalAeval_j_modularPolynomial_eq_zero_symm {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : IsPrimitive A.1) (τ : ℍ) :
    (modularPolynomial n).aevalAeval (j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) (j τ) = 0 := by
  let A' : FixedDetMatrix (Fin 2) ℤ n :=
    ⟨Matrix.adjugate A.1, by simp [Matrix.det_adjugate, A.2]⟩
  have hsmul : toGLReal (NeZero.ne (n : ℤ)) A' • (toGLReal (NeZero.ne (n : ℤ)) A • τ) = τ := by
    rw [← mul_smul]
    set g := toGLReal (NeZero.ne (n : ℤ)) A' * toGLReal (NeZero.ne (n : ℤ)) A
    have hdet : 0 < (g.det : ℝ) := by
      rw [map_mul, Units.val_mul, det_toGLReal, det_toGLReal]
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      exact mul_pos hn_pos hn_pos
    have hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![(n : ℝ), 0; 0, (n : ℝ)] := by
      have hmul : Matrix.adjugate A.1 * A.1 = (n : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [Matrix.adjugate_mul, A.2]
      have hmap : (A'.1.map (Int.cast : ℤ → ℝ)) * (A.1.map (Int.cast : ℤ → ℝ)) =
          ((Matrix.adjugate A.1 * A.1).map (Int.cast : ℤ → ℝ)) :=
        (Matrix.map_mul (f := Int.castRingHom ℝ) (L := Matrix.adjugate A.1) (M := A.1)).symm
      rw [Units.val_mul, coe_toGLReal, coe_toGLReal, hmap, hmul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_one,
          mul_zero, Int.cast_natCast, Int.cast_zero, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one,
          Fin.reduceEq, ↓reduceIte]
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hg, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_natCast,
      Complex.ofReal_zero, add_zero, zero_mul, zero_add]
    exact mul_div_cancel_left₀ (τ : ℂ) hn0
  have h := aevalAeval_j_modularPolynomial_eq_zero (A := A') (isPrimitive_adjugate hA)
    (toGLReal (NeZero.ne (n : ℤ)) A • τ)
  rwa [hsmul] at h

/-- **Classical modular equation `Φ_n(j(τ), j(n τ)) = 0`.** -/
theorem aevalAeval_j_scaleGL_modularPolynomial_eq_zero (τ : ℍ) :
    (modularPolynomial n).aevalAeval (j τ) (j (scaleGL n • τ)) = 0 := by
  rw [aevalAeval_eq_eval_map_aeval, map_aeval_j_modularPolynomial]
  exact isRoot_cyclicIsogenyPolynomial_scaleGL_smul (n := n) j_smul_SL2Z τ

/-- **Symmetric modular equation `Φ_n(j(n τ), j(τ)) = 0`.** -/
theorem aevalAeval_j_scaleGL_modularPolynomial_eq_zero_symm (τ : ℍ) :
    (modularPolynomial n).aevalAeval (j (scaleGL n • τ)) (j τ) = 0 := by
  let D := TraceFormulaMatrix.diagonal (n : ℤ) 1 (mul_one _)
  have hD : toGLReal (NeZero.ne (n : ℤ)) D = scaleGL n := by
    refine Units.ext ?_
    rw [coe_toGLReal, coe_scaleGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D]
  rw [← hD]
  exact aevalAeval_j_modularPolynomial_eq_zero_symm
    (isPrimitive_def.2 ⟨(entryAddMonoidHom ℤ 1 1).toIntLinearMap, by simp [D]⟩) τ

/-- Evaluating the diagonal specialization `(modularPolynomial n).eval X` at `z` agrees with
`aevalAeval z z (modularPolynomial n)`. -/
theorem aeval_eval_X_modularPolynomial {A : Type*} [CommRing A] (z : A) :
    aeval z ((modularPolynomial n).eval X) = (modularPolynomial n).aevalAeval z z := by
  have h (p : ℤ[X][X]) : aeval z (p.eval X) = p.aevalAeval z z := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [eval_add, map_add, map_add, hp, hq]
    | monomial k q =>
      rw [← C_mul_X_pow_eq_monomial, eval_mul, eval_C, eval_pow, eval_X,
        map_mul, map_pow, aeval_X, map_mul, map_pow, aevalAeval_C, aevalAeval_Y]
  exact h (modularPolynomial n)

end ModularPolynomial

/-! ### The diagonal polynomial `Φ_n(X, X)` for nonsquare `n` -/

noncomputable section DiagonalHelpers

variable {n : ℕ} [NeZero n]

private theorem nonempty_primitiveReps : (primitiveReps (n : ℤ)).Nonempty := by
  refine ⟨TraceFormulaMatrix.diagonal (n : ℤ) 1 (mul_one _), mem_primitiveReps.mpr ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [NeZero.pos n]
  · exact isPrimitive_def.2 ⟨(entryAddMonoidHom ℤ 1 1).toIntLinearMap, by simp⟩

private theorem orderTop_and_leadingCoeff_laurentQExpansion_j_smul {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) :
    (UpperHalfPlane.laurentQExpansion (n : ℝ)
        fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)).orderTop =
        ((-(repA A : ℤ) ^ 2 : ℤ) : WithTop ℤ) ∧
      (UpperHalfPlane.laurentQExpansion (n : ℝ)
        fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)).leadingCoeff =
        𝕢 (n : ℝ) 1 ^ (-((repA A * repB A : ℕ) : ℤ)) := by
  rw [← map_jRepLaurent_eq_laurentQExpansion hA, jRepLaurent]
  let f := HahnSeries.mapRingHom (cyclotomicToComplex n)
    (jTwistLaurent n ((repA A : ℤ) * repB A))
  have hexp : HahnSeries.mapRingHom (cyclotomicToComplex n)
      (LaurentSeries.expand (CyclotomicField n ℚ) (repA2PNat hA)
        (jTwistLaurent n ((repA A : ℤ) * repB A))) =
      LaurentSeries.expand ℂ (repA2PNat hA) f := by
    ext k
    by_cases hk : ((repA2PNat hA : ℕ) : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hk
      rw [HahnSeries.mapRingHom_apply, HahnSeries.map_coeff, LaurentSeries.coeff_expand_mul,
        LaurentSeries.coeff_expand_mul]
      dsimp only [f]
      rw [HahnSeries.mapRingHom_apply, HahnSeries.map_coeff]
    · simp [f, LaurentSeries.coeff_expand_of_not_dvd (repA2PNat hA) _ hk]
  rw [hexp]
  have hf_neg1 : f.coeff (-1) = 𝕢 (n : ℝ) 1 ^ (-((repA A * repB A : ℕ) : ℤ)) := by
    dsimp only [f]
    rw [HahnSeries.mapRingHom_apply, HahnSeries.map_coeff, coeff_jTwistLaurent, map_mul,
      map_zpow₀, cyclotomicToComplex_zeta, map_intCast, cast_jIntCoeff,
      laurentQExpansion_j_coeff_neg_one, mul_one]
    congr 1
    push_cast
    ring
  have hf_ne : f.coeff (-1) ≠ 0 :=
    hf_neg1 ▸ zpow_ne_zero _ (Function.Periodic.qParam_ne_zero _)
  have hord : f.orderTop = ((-1 : ℤ) : WithTop ℤ) :=
    HahnSeries.orderTop_eq_of_le ((HahnSeries.mem_support f (-1)).mpr hf_ne) fun m hm ↦ by
      by_contra! hlt
      exact (HahnSeries.mem_support f m).mp hm (by simp [f, jIntCoeff_of_lt_neg_one hlt])
  have hf0 : f ≠ 0 := fun h ↦ hf_ne (by simp [h])
  have hf_ord : f.order = -1 :=
    WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero hf0).trans hord)
  refine ⟨?_, ?_⟩
  · rw [LaurentSeries.orderTop_expand, hord, ← WithTop.coe_nsmul, nsmul_eq_mul, coe_repA2PNat]
    exact WithTop.coe_eq_coe.mpr (by push_cast; ring)
  · rw [LaurentSeries.leadingCoeff_expand, HahnSeries.leadingCoeff_eq, hf_ord, hf_neg1]

private theorem orderTop_and_leadingCoeff_laurentQExpansion_j_pow (k : ℕ) :
    (UpperHalfPlane.laurentQExpansion 1 j ^ k).orderTop = ((-(k : ℤ) : ℤ) : WithTop ℤ) ∧
      (UpperHalfPlane.laurentQExpansion 1 j ^ k).leadingCoeff = 1 := by
  set J := UpperHalfPlane.laurentQExpansion 1 j
  have hJ_ord : J.orderTop = ((-1 : ℤ) : WithTop ℤ) := orderTop_laurentQExpansion_j
  have hJ1 : J.leadingCoeff = 1 := by
    have hJ0 : J ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [hJ_ord]; simp)
    have ho : J.order = -1 := WithTop.coe_injective
      ((HahnSeries.order_eq_orderTop_of_ne_zero hJ0).trans hJ_ord)
    rw [HahnSeries.leadingCoeff_eq, ho, laurentQExpansion_j_coeff_neg_one]
  induction k with
  | zero => exact ⟨HahnSeries.orderTop_one, HahnSeries.leadingCoeff_one⟩
  | succ k ih =>
    rw [pow_succ, HahnSeries.orderTop_mul, HahnSeries.leadingCoeff_mul, ih.1, ih.2,
      hJ_ord, hJ1, mul_one, ← WithTop.coe_add]
    exact ⟨WithTop.coe_eq_coe.mpr (by omega), rfl⟩

private theorem orderTop_and_leadingCoeff_laurentQExpansion_aeval_j {P : ℤ[X]} (hP : P ≠ 0) :
    (UpperHalfPlane.laurentQExpansion 1 fun τ : ℍ ↦ aeval (j τ) P).orderTop =
        ((-(P.natDegree : ℤ) : ℤ) : WithTop ℤ) ∧
      (UpperHalfPlane.laurentQExpansion 1 fun τ : ℍ ↦ aeval (j τ) P).leadingCoeff =
        (P.leadingCoeff : ℂ) := by
  set L := UpperHalfPlane.laurentQExpansion 1 fun τ : ℍ ↦ aeval (j τ) P
  set J := UpperHalfPlane.laurentQExpansion 1 j
  have hJ_lt : ∀ (k : ℕ) {m : ℤ}, m < -(k : ℤ) → (J ^ k).coeff m = 0 := fun k m hm ↦
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [(orderTop_and_leadingCoeff_laurentQExpansion_j_pow k).1]
      exact WithTop.coe_lt_coe.mpr hm)
  have hJ_top : ∀ k : ℕ, (J ^ k).coeff (-(k : ℤ)) = 1 := fun k ↦ by
    obtain ⟨hord, hlc⟩ := orderTop_and_leadingCoeff_laurentQExpansion_j_pow k
    have h0 : J ^ k ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [hord]; simp)
    have ho : (J ^ k).order = -(k : ℤ) :=
      WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero h0).trans hord)
    rwa [HahnSeries.leadingCoeff_eq, ho] at hlc
  have hL_coeff : ∀ m : ℤ, L.coeff m =
      ∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k : ℂ) * (J ^ k).coeff m := fun m ↦ by
    rw [show L = _ from Polynomial.laurentQExpansion_aeval_j P, eval₂_eq_sum_range,
      HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [eq_intCast, ← HahnSeries.single_zero_intCast, HahnSeries.coeff_single_mul,
      sub_zero, J]
  have hL_lt : ∀ m < -(P.natDegree : ℤ), L.coeff m = 0 := fun m hm ↦ by
    rw [hL_coeff]
    exact Finset.sum_eq_zero fun k hk ↦ by
      rw [Finset.mem_range] at hk
      rw [hJ_lt k (by omega), mul_zero]
  have hL_top : L.coeff (-(P.natDegree : ℤ)) = (P.leadingCoeff : ℂ) := by
    rw [hL_coeff, Finset.sum_range_succ, add_eq_right.mpr]
    · rw [hJ_top, mul_one, Polynomial.leadingCoeff]
    · exact Finset.sum_eq_zero fun k hk ↦ by
        rw [Finset.mem_range] at hk
        rw [hJ_lt k (by omega), mul_zero]
  have hL_ne : L.coeff (-(P.natDegree : ℤ)) ≠ 0 :=
    hL_top ▸ Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP)
  have hord : L.orderTop = ((-(P.natDegree : ℤ) : ℤ) : WithTop ℤ) :=
    HahnSeries.orderTop_eq_of_le ((HahnSeries.mem_support L _).mpr hL_ne) fun m hm ↦ by
      by_contra! hlt
      exact (HahnSeries.mem_support L m).mp hm (hL_lt m hlt)
  have hL0 : L ≠ 0 := fun h ↦ hL_ne (by simp [h])
  have hL_ord : L.order = -(P.natDegree : ℤ) :=
    WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero hL0).trans hord)
  exact ⟨hord, HahnSeries.leadingCoeff_eq.trans (hL_ord ▸ hL_top)⟩

omit [NeZero n] in
private theorem meromorphicAt_cuspFunction_nat_j :
    MeromorphicAt (cuspFunction (n : ℝ) j) 0 := by
  simpa using UpperHalfPlane.meromorphicAt_cuspFunction_nat_mul (h := 1)
    periodic_j_comp_ofComplex meromorphicAt_cuspFunction_j n

private theorem orderTop_and_leadingCoeff_laurentQExpansion_nat_j :
    (UpperHalfPlane.laurentQExpansion (n : ℝ) j).orderTop = ((-(n : ℤ) : ℤ) : WithTop ℤ) ∧
      (UpperHalfPlane.laurentQExpansion (n : ℝ) j).leadingCoeff = 1 := by
  have hJn : UpperHalfPlane.laurentQExpansion (n : ℝ) j =
      LaurentSeries.expand ℂ (natPNat n) (UpperHalfPlane.laurentQExpansion 1 j) := by
    simpa [coe_natPNat] using UpperHalfPlane.laurentQExpansion_pnat_mul (h := 1)
      periodic_j_comp_ofComplex meromorphicAt_cuspFunction_j (natPNat n)
  obtain ⟨hord1, hlc1⟩ := orderTop_and_leadingCoeff_laurentQExpansion_j_pow 1
  rw [pow_one] at hord1 hlc1
  refine ⟨?_, ?_⟩
  · rw [hJn, LaurentSeries.orderTop_expand, hord1, ← WithTop.coe_nsmul, nsmul_eq_mul, coe_natPNat]
    exact WithTop.coe_eq_coe.mpr (by ring)
  · rw [hJn, LaurentSeries.leadingCoeff_expand, hlc1]

private theorem orderTop_and_norm_leadingCoeff_add_of_ne {x y : LaurentSeries ℂ}
    (hne : x.orderTop ≠ y.orderTop) (hx_ord : x.orderTop < 0) (hy_ord : y.orderTop < 0)
    (hx_norm : ‖x.leadingCoeff‖ = 1) (hy_norm : ‖y.leadingCoeff‖ = 1) :
    (x + y).orderTop < 0 ∧ ‖(x + y).leadingCoeff‖ = 1 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [HahnSeries.orderTop_add_eq_left hlt, HahnSeries.leadingCoeff_add_eq_left hlt]
    exact ⟨hx_ord, hx_norm⟩
  · rw [add_comm, HahnSeries.orderTop_add_eq_left hgt, HahnSeries.leadingCoeff_add_eq_left hgt]
    exact ⟨hy_ord, hy_norm⟩

private theorem orderTop_and_norm_leadingCoeff_diagFactor (hn : ¬ IsSquare n)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    let D := UpperHalfPlane.laurentQExpansion (n : ℝ) j -
      UpperHalfPlane.laurentQExpansion (n : ℝ) fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)
    D.orderTop < 0 ∧ ‖D.leadingCoeff‖ = 1 := by
  intro D
  obtain ⟨-, -, -, -, ha_pos, -, -, had⟩ := rep_entries hA
  have ha2_ne : (-(n : ℤ) : ℤ) ≠ -(repA A : ℤ) ^ 2 := fun heq ↦ hn <| by
    have : repA A ^ 2 = n := by exact_mod_cast neg_injective heq.symm
    have : repA A = repD A := Nat.eq_of_mul_eq_mul_left ha_pos (by linarith [sq (repA A)])
    exact ⟨repA A, by linarith⟩
  obtain ⟨h1_ord, h1_lead⟩ := orderTop_and_leadingCoeff_laurentQExpansion_nat_j (n := n)
  obtain ⟨h2_ord, h2_lead⟩ := orderTop_and_leadingCoeff_laurentQExpansion_j_smul hA
  rw [show D = _ + -_ from sub_eq_add_neg _ _]
  refine orderTop_and_norm_leadingCoeff_add_of_ne ?_ ?_ ?_ ?_ ?_
  · rw [HahnSeries.orderTop_neg, h1_ord, h2_ord]
    exact WithTop.coe_injective.ne ha2_ne
  · rw [h1_ord]
    exact WithTop.coe_lt_coe.mpr (neg_neg_of_pos (Int.natCast_pos.mpr (NeZero.pos n)))
  · rw [HahnSeries.orderTop_neg, h2_ord]
    exact WithTop.coe_lt_coe.mpr (neg_neg_of_pos (pow_pos (Int.natCast_pos.mpr ha_pos) 2))
  · rw [h1_lead, norm_one]
  · rw [HahnSeries.leadingCoeff_neg, h2_lead, norm_neg, norm_zpow,
      Function.Periodic.norm_qParam]
    simp only [Complex.one_im, mul_zero, zero_div, Real.exp_zero, _root_.one_zpow]

private theorem laurentQExpansion_nat_aeval_eval_X_modularPolynomial :
    UpperHalfPlane.laurentQExpansion (n : ℝ)
        (fun τ : ℍ ↦ aeval (j τ) ((modularPolynomial n).eval X)) =
      ∏ A ∈ primitiveReps (n : ℤ),
        (UpperHalfPlane.laurentQExpansion (n : ℝ) j -
          UpperHalfPlane.laurentQExpansion (n : ℝ)
            fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
  have hQ_fun : (fun τ : ℍ ↦ aeval (j τ) ((modularPolynomial n).eval X)) =
      ∏ A ∈ primitiveReps (n : ℤ),
        (j - fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
    funext τ
    rw [aeval_eval_X_modularPolynomial, aevalAeval_eq_eval_map_aeval,
      map_aeval_j_modularPolynomial, cyclicIsogenyPolynomial_def, eval_prod]
    simp [Finset.prod_apply]
  rw [hQ_fun, UpperHalfPlane.laurentQExpansion_prod]
  · exact Finset.prod_congr rfl fun A hA ↦ UpperHalfPlane.laurentQExpansion_sub
      meromorphicAt_cuspFunction_nat_j
      (meromorphicAt_cuspFunction_j_toGLReal_smul (mem_primitiveReps.mp hA).1)
  · exact fun A hA ↦ UpperHalfPlane.meromorphicAt_cuspFunction_sub
      meromorphicAt_cuspFunction_nat_j
      (meromorphicAt_cuspFunction_j_toGLReal_smul (mem_primitiveReps.mp hA).1)

private theorem withTop_add_lt_zero {a b : WithTop ℤ} (ha : a < 0) (hb : b < 0) : a + b < 0 := by
  cases a using WithTop.recTopCoe with
  | top => simp at ha
  | coe x =>
    cases b using WithTop.recTopCoe with
    | top => simp at hb
    | coe y =>
      rw [← WithTop.coe_add]
      exact WithTop.coe_lt_coe.mpr (add_neg (WithTop.coe_lt_coe.mp ha) (WithTop.coe_lt_coe.mp hb))

private theorem eval_X_modularPolynomial_laurent_props (hn : ¬ IsSquare n) :
    let L₁ := UpperHalfPlane.laurentQExpansion 1
      fun τ : ℍ ↦ aeval (j τ) ((modularPolynomial n).eval X)
    L₁.orderTop < 0 ∧ ‖L₁.leadingCoeff‖ = 1 := by
  intro L₁
  set Q : ℤ[X] := (modularPolynomial n).eval X
  have hLn_exp : UpperHalfPlane.laurentQExpansion (n : ℝ) (fun τ : ℍ ↦ aeval (j τ) Q) =
      LaurentSeries.expand ℂ (natPNat n) L₁ := by
    have hper : Periodic ((fun τ : ℍ ↦ aeval (j τ) Q) ∘ ofComplex) (1 : ℝ) :=
      UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
        rw [← modular_T_smul, j_smul_SL2Z]
    simpa [coe_natPNat] using UpperHalfPlane.laurentQExpansion_pnat_mul (h := 1) hper
      (Polynomial.meromorphicAt_cuspFunction_aeval_j Q) (natPNat n)
  have hprod_props : ∀ s ⊆ primitiveReps (n : ℤ), s.Nonempty →
      (∏ A ∈ s, (UpperHalfPlane.laurentQExpansion (n : ℝ) j -
        UpperHalfPlane.laurentQExpansion (n : ℝ)
          fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).orderTop < 0 ∧
      ‖(∏ A ∈ s, (UpperHalfPlane.laurentQExpansion (n : ℝ) j -
        UpperHalfPlane.laurentQExpansion (n : ℝ)
          fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).leadingCoeff‖ = 1 := by
    classical
    intro s hs hne
    induction hne using Finset.Nonempty.cons_induction with
    | singleton a =>
      simpa using orderTop_and_norm_leadingCoeff_diagFactor hn
        (mem_primitiveReps.mp (hs (Finset.mem_singleton_self a))).1
    | cons a t _ _ ih =>
      obtain ⟨hDa_ord, hDa_norm⟩ := orderTop_and_norm_leadingCoeff_diagFactor hn
        (mem_primitiveReps.mp (hs (Finset.mem_cons_self a t))).1
      obtain ⟨ht_ord, ht_norm⟩ := ih (Finset.cons_subset.mp hs).2
      rw [Finset.prod_cons, HahnSeries.orderTop_mul, HahnSeries.leadingCoeff_mul, norm_mul,
        hDa_norm, ht_norm, mul_one]
      exact ⟨withTop_add_lt_zero hDa_ord ht_ord, rfl⟩
  obtain ⟨hord_n, hnorm_n⟩ := hprod_props (primitiveReps (n : ℤ)) Finset.Subset.rfl
    nonempty_primitiveReps
  rw [← laurentQExpansion_nat_aeval_eval_X_modularPolynomial, hLn_exp,
    LaurentSeries.orderTop_expand] at hord_n
  rw [← laurentQExpansion_nat_aeval_eval_X_modularPolynomial, hLn_exp,
    LaurentSeries.leadingCoeff_expand] at hnorm_n
  refine ⟨?_, hnorm_n⟩
  cases h : L₁.orderTop using WithTop.recTopCoe with
  | top =>
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    simp [h, coe_natPNat, hm, succ_nsmul] at hord_n
  | coe k =>
    rw [h, ← WithTop.coe_nsmul, nsmul_eq_mul, coe_natPNat] at hord_n
    have hk : (n : ℤ) * k < 0 := WithTop.coe_lt_coe.mp hord_n
    have hn_pos : (0 : ℤ) < n := Int.natCast_pos.mpr (NeZero.pos n)
    exact WithTop.coe_lt_coe.mpr (neg_of_mul_neg_right hk hn_pos.le)

end DiagonalHelpers

public noncomputable section Diagonal

variable {n : ℕ} [NeZero n]

/-- For nonsquare `n`, the diagonal polynomial `(modularPolynomial n).eval X` is nonzero. -/
theorem eval_X_modularPolynomial_ne_zero (hn : ¬ IsSquare n) :
    (modularPolynomial n).eval X ≠ 0 := by
  intro h0
  obtain ⟨hord, -⟩ := eval_X_modularPolynomial_laurent_props hn
  simp [h0] at hord

/-- For nonsquare `n`, the diagonal polynomial `(modularPolynomial n).eval X` has positive
degree. -/
theorem natDegree_eval_X_modularPolynomial_pos (hn : ¬ IsSquare n) :
    0 < ((modularPolynomial n).eval X).natDegree := by
  have hne := eval_X_modularPolynomial_ne_zero hn
  obtain ⟨hord_eq, -⟩ := orderTop_and_leadingCoeff_laurentQExpansion_aeval_j hne
  obtain ⟨hord_lt, -⟩ := eval_X_modularPolynomial_laurent_props hn
  rw [hord_eq] at hord_lt
  have : -(((modularPolynomial n).eval X).natDegree : ℤ) < 0 := WithTop.coe_lt_coe.mp hord_lt
  omega

/-- **Kronecker's leading-coefficient theorem for `Φ_n(X, X)`.** When `n` is not a square, the
leading coefficient of `(modularPolynomial n).eval X` in `ℤ` is `±1` (`IsUnit`). -/
theorem isUnit_leadingCoeff_eval_X_modularPolynomial (hn : ¬ IsSquare n) :
    IsUnit ((modularPolynomial n).eval X).leadingCoeff := by
  have hne := eval_X_modularPolynomial_ne_zero hn
  obtain ⟨-, hlead⟩ := orderTop_and_leadingCoeff_laurentQExpansion_aeval_j hne
  obtain ⟨-, hnorm⟩ := eval_X_modularPolynomial_laurent_props hn
  rw [hlead, Complex.norm_intCast] at hnorm
  exact Int.isUnit_iff_abs_eq.mpr (by exact_mod_cast hnorm)

/-- Any root of `(modularPolynomial n).eval X` in a ring `A` for nonsquare `n` is integral over
`ℤ`. -/
theorem isIntegral_of_aeval_eval_X_modularPolynomial_eq_zero (hn : ¬ IsSquare n)
    {A : Type*} [Ring A] {z : A}
    (hz : aeval z ((modularPolynomial n).eval X) = 0) : IsIntegral ℤ z := by
  set Q : ℤ[X] := (modularPolynomial n).eval X
  let u : ℤˣ := (isUnit_leadingCoeff_eval_X_modularPolynomial hn).unit
  refine ⟨C (↑u⁻¹ : ℤ) * Q, ?_, ?_⟩
  · rw [Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact Units.inv_mul u
  · rw [← aeval_def, map_mul, hz, mul_zero]

end Diagonal

/-! ### Algebraic integrality of `j` at imaginary quadratic points -/

noncomputable section ImaginaryQuadraticHelpers

private theorem disc_neg_of_quadratic {τ : ℍ} {a b c : ℤ} (ha : 0 < a)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + (c : ℂ) = 0) :
    b ^ 2 - 4 * a * c < 0 := by
  have hre_im : (τ : ℂ) = τ.re + τ.im * Complex.I := τ.re_add_im.symm
  have him0 := congrArg Complex.im hτ
  have hre0 := congrArg Complex.re hτ
  rw [hre_im] at him0 hre0
  simp only [sq, add_mul, mul_add, Complex.add_im, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.zero_im, Complex.add_re, Complex.mul_re, Complex.zero_re] at him0 hre0
  have him' : (2 * (a : ℝ) * τ.re + b) * τ.im = 0 := by linarith
  have hx : 2 * (a : ℝ) * τ.re + b = 0 := (mul_eq_zero.mp him').resolve_right τ.im_pos.ne'
  have hre' : (a : ℝ) * (τ.re * τ.re - τ.im * τ.im) + b * τ.re + c = 0 := by linarith
  have hdisc_real : ((b : ℝ) ^ 2 - 4 * a * c) = -4 * (a : ℝ) ^ 2 * τ.im ^ 2 := by
    linear_combination (2 * (a : ℝ) * τ.re + b) * hx - 4 * (a : ℝ) * hre'
  have hneg : ((b : ℝ) ^ 2 - 4 * a * c) < 0 := by
    rw [hdisc_real]
    have hpos : 0 < (a : ℝ) ^ 2 * τ.im ^ 2 :=
      mul_pos (sq_pos_of_pos (Int.cast_pos.mpr ha)) (sq_pos_of_pos τ.im_pos)
    linarith
  exact_mod_cast hneg

private theorem exists_primitive_pos_quad {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + (c : ℂ) = 0) :
    ∃ a' b' c' : ℤ, 0 < a' ∧ IsPrimitive ![a', b', c'] ∧ b' ^ 2 - 4 * a' * c' < 0 ∧
      (a' : ℂ) * (τ : ℂ) ^ 2 + (b' : ℂ) * (τ : ℂ) + (c' : ℂ) = 0 := by
  let v : Fin 3 → ℤ := if 0 < a then ![a, b, c] else ![-a, -b, -c]
  have hv0 : 0 < v 0 := by dsimp [v]; split_ifs with h <;> simp <;> omega
  have hv_ne : v ≠ 0 := fun hv ↦ by simp [hv] at hv0
  have hv_eq : (v 0 : ℂ) * (τ : ℂ) ^ 2 + (v 1 : ℂ) * (τ : ℂ) + (v 2 : ℂ) = 0 := by
    dsimp [v]
    split_ifs
    · exact hτ
    · push_cast; linear_combination -hτ
  obtain ⟨d, w, hd, hw, hvw⟩ := exists_eq_zsmul_isPrimitive hv_ne
  have hvw0 : v 0 = d * w 0 := by simpa using congrFun hvw 0
  have hvw1 : v 1 = d * w 1 := by simpa using congrFun hvw 1
  have hvw2 : v 2 = d * w 2 := by simpa using congrFun hvw 2
  have ha' : 0 < w 0 := pos_of_mul_pos_right (hvw0 ▸ hv0) hd.le
  have hw_eq : (w 0 : ℂ) * (τ : ℂ) ^ 2 + (w 1 : ℂ) * (τ : ℂ) + (w 2 : ℂ) = 0 := by
    apply mul_left_cancel₀ (Int.cast_ne_zero.mpr hd.ne' : (d : ℂ) ≠ 0)
    rw [mul_zero]
    linear_combination hv_eq - ((τ : ℂ) ^ 2 * (by exact_mod_cast hvw0 : (v 0 : ℂ) = d * w 0)) -
      ((τ : ℂ) * (by exact_mod_cast hvw1 : (v 1 : ℂ) = d * w 1)) -
      (by exact_mod_cast hvw2 : (v 2 : ℂ) = d * w 2)
  have hw_eta : ![w 0, w 1, w 2] = w := by ext i; fin_cases i <;> rfl
  exact ⟨w 0, w 1, w 2, ha', hw_eta ▸ hw, disc_neg_of_quadratic ha' hw_eq, hw_eq⟩

private theorem not_isSquare_of_lt_succ_sq {n m : ℕ} (h1 : m ^ 2 < n) (h2 : n < (m + 1) ^ 2) :
    ¬ IsSquare n := by
  rintro ⟨s, rfl⟩
  rcases le_or_gt s m with hle | hgt
  · linarith [Nat.mul_le_mul hle hle, sq m]
  · linarith [Nat.mul_le_mul hgt hgt, sq (m + 1)]

private theorem exists_nonsquare_det_quadMatrix {a b c : ℤ} (hdisc : b ^ 2 - 4 * a * c < 0) :
    ∃ (k : ℤ) (n : ℕ), 0 < n ∧ ¬ IsSquare n ∧
      (!![k - b, -c; a, k] : Matrix (Fin 2) (Fin 2) ℤ).det = n := by
  set q : ℤ := b / 2
  rcases Int.emod_two_eq_zero_or_one b with hr | hr
  · have hb : b = 2 * q := by linarith [Int.emod_add_mul_ediv b 2]
    have h4 : 4 * (q ^ 2 - a * c) < 0 := by
      have : 4 * (q ^ 2 - a * c) = b ^ 2 - 4 * a * c := by rw [hb]; ring
      linarith
    have hm_pos : 0 < a * c - q ^ 2 := by omega
    lift a * c - q ^ 2 to ℕ using hm_pos.le with m hm
    have hm0 : 0 < m := by omega
    refine ⟨q + m, m ^ 2 + m, by positivity,
      not_isSquare_of_lt_succ_sq (m := m) (by linarith) (by ring_nf; linarith), ?_⟩
    rw [Matrix.det_fin_two_of, hb]
    push_cast
    linarith
  · have hb : b = 2 * q + 1 := by linarith [Int.emod_add_mul_ediv b 2]
    have h4 : 4 * (q ^ 2 + q - a * c) + 1 < 0 := by
      have : 4 * (q ^ 2 + q - a * c) + 1 = b ^ 2 - 4 * a * c := by rw [hb]; ring
      linarith
    have hm_pos : 0 < a * c - q ^ 2 - q := by omega
    lift a * c - q ^ 2 - q to ℕ using hm_pos.le with m hm
    have hm0 : 0 < m := by omega
    refine ⟨q + m + 1, m ^ 2 + 2 * m, by positivity,
      not_isSquare_of_lt_succ_sq (m := m) (by linarith) (by ring_nf; linarith), ?_⟩
    rw [Matrix.det_fin_two_of, hb]
    push_cast
    linarith

private theorem exists_nonsquare_fixedDetMatrix_smul_eq {τ : ℍ} {a b c : ℤ}
    (ha : 0 < a) (hw : IsPrimitive ![a, b, c]) (hdisc : b ^ 2 - 4 * a * c < 0)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + (c : ℂ) = 0) :
    ∃ (n : ℕ) (hn0 : NeZero n) (A : FixedDetMatrix (Fin 2) ℤ n),
      ¬ IsSquare n ∧ IsPrimitive A.1 ∧ toGLReal (NeZero.ne (n : ℤ)) A • τ = τ := by
  obtain ⟨k, n, hn_pos, hn_sq, hdet⟩ := exists_nonsquare_det_quadMatrix hdisc
  have hn0 : NeZero n := ⟨hn_pos.ne'⟩
  let A : FixedDetMatrix (Fin 2) ℤ n := ⟨!![k - b, -c; a, k], hdet⟩
  have hprim : IsPrimitive A.1 := by
    let L : Matrix (Fin 2) (Fin 2) ℤ →ₗ[ℤ] (Fin 3 → ℤ) :=
      { toFun N := ![N 1 0, N 1 1 - N 0 0, -N 0 1]
        map_add' M N := by ext i; fin_cases i <;> simp <;> ring
        map_smul' r M := by ext i; fin_cases i <;> simp; ring }
    have hLA : L A.1 = ![a, b, c] := by ext i; fin_cases i <;> simp [L, A]
    exact IsPrimitive.of_map (g := L) (hLA.symm ▸ hw)
  refine ⟨n, hn0, A, hn_sq, hprim, ?_⟩
  apply UpperHalfPlane.ext
  have hdet_real : 0 < ((toGLReal (NeZero.ne (n : ℤ)) A).det : ℝ) := by
    rw [det_toGLReal]
    exact_mod_cast hn_pos
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet_real]
  have hden : (a : ℂ) * τ + k ≠ 0 := fun h0 ↦ by
    have him := congrArg Complex.im h0
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      add_zero, Complex.zero_im, UpperHalfPlane.coe_im] at him
    linarith [mul_pos (Int.cast_pos.mpr ha) τ.im_pos]
  have hA00 : A.1 0 0 = k - b := rfl
  have hA01 : A.1 0 1 = -c := rfl
  have hA10 : A.1 1 0 = a := rfl
  have hA11 : A.1 1 1 = k := rfl
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, toGLReal_apply, hA00, hA01, hA10, hA11]
  rw [div_eq_iff (by push_cast at hden ⊢; exact hden)]
  push_cast
  linear_combination -hτ

end ImaginaryQuadraticHelpers

public noncomputable section ImaginaryQuadratic

/-- **Algebraic integrality of `j` at imaginary quadratic points.** If `τ ∈ ℍ` satisfies
`a τ² + b τ + c = 0` with `a, b, c ∈ ℤ` and `a ≠ 0`, then `j(τ)` is an algebraic integer. -/
theorem isIntegral_j_of_quadratic {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + (c : ℂ) = 0) :
    IsIntegral ℤ (j τ) := by
  obtain ⟨a', b', c', ha', hw, hdisc, hτ'⟩ := exists_primitive_pos_quad ha hτ
  obtain ⟨n, _, A, hn_sq, hprim, hfix⟩ :=
    exists_nonsquare_fixedDetMatrix_smul_eq ha' hw hdisc hτ'
  have hroot := aevalAeval_j_modularPolynomial_eq_zero hprim τ
  rw [hfix, ← aeval_eval_X_modularPolynomial] at hroot
  exact isIntegral_of_aeval_eval_X_modularPolynomial_eq_zero hn_sq hroot

end ImaginaryQuadratic

end TauCeti.ModularForm
