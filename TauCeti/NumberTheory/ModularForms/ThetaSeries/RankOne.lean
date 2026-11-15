/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Functoriality
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Rank-one theta series

The theta series of `ℤ ∙ 1 ⊆ ℝ` is Mathlib's `jacobiTheta`, with exponent `π i n² τ`. More
generally, for any nonzero `c ∈ ℝ`, the theta series of `c ℤ` is `jacobiTheta (c² τ)`
(`ZLattice.thetaSeries_span_singleton`); in particular the theta series of `√2 ℤ` is
`jacobiTheta (2 τ)`. The period-two expansion of `Θ_ℤ` has constant coefficient one, coefficient two
at each positive square, and zero elsewhere, counting the two signs of a nonzero integer as in
Mathlib's `hasSum_nat_jacobiTheta`.

This file also records the rank-one counterexample `L = ½ ℤ ⊆ ℝ` (`span ℤ {(2⁻¹ : ℝ)}`) showing
that `ZLattice.IsIntegral.thetaSeries_dual_eq_sum` requires integrality: its dual is
`L^∨ = 2 ℤ < ½ ℤ` (`ZLattice.dual_span_inv_two`, `ZLattice.dual_span_inv_two_lt`), so its
discriminant group `L^∨ ⧸ (L ∩ L^∨)` is trivial
(`ZLattice.subsingleton_discriminantGroup_span_inv_two`), and `∑_{γ ∈ A_L} θ_γ = Θ_{½ℤ}` while
`Θ_{L^∨} = Θ_{2ℤ}`, which differ strictly on the imaginary axis
(`ZLattice.re_thetaSeries_span_two_lt_span_inv_two`,
`ZLattice.thetaSeries_dual_span_inv_two_apply_I_ne_sum`).

The comparison reindexes by `LinearEquiv.toSpanNonzeroSingleton`; the analytic series and its
positive-square summation formula are Mathlib's `jacobiTheta` and `hasSum_nat_jacobiTheta`.
For the lattice theta-series convention see Serre, *A Course in Arithmetic*, Ch. VII §6,
and Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

open Complex Function Submodule
open UpperHalfPlane (qExpansion)
open scoped Real UpperHalfPlane Pointwise

namespace ZLattice

/-- The theta series of the integer lattice, with exponent `π i n² τ`, is Jacobi's theta
function. -/
theorem thetaSeries_span_one (τ : ℍ) :
    thetaSeries (span ℤ {1} : Submodule ℤ ℝ) τ = jacobiTheta τ := by
  rw [thetaSeries_apply, jacobiTheta,
    ← (LinearEquiv.toSpanNonzeroSingleton ℤ ℝ 1 one_ne_zero).toEquiv.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp [Real.norm_eq_abs, sq_abs]

/-- For `c ≠ 0`, the theta series of the rank-one lattice `c ℤ ⊆ ℝ` is Jacobi's theta function at
`c² τ`. -/
theorem thetaSeries_span_singleton {c : ℝ} (hc : c ≠ 0) (τ : ℍ) :
    thetaSeries (span ℤ {c} : Submodule ℤ ℝ) τ = jacobiTheta ((c ^ 2 : ℝ) * (τ : ℂ)) := by
  have hspan : (span ℤ {c} : Submodule ℤ ℝ) = c • span ℤ {1} := by simp [smul_span]
  rw [hspan, thetaSeries_smul _ hc, thetaSeries_span_one]
  simp [Complex.real_smul]

/-- Scaling the integer lattice by `√2` gives Jacobi's theta function at `2τ`. -/
theorem thetaSeries_sqrt_two_smul_span_one (τ : ℍ) :
    thetaSeries (Real.sqrt 2 • (span ℤ {1} : Submodule ℤ ℝ)) τ = jacobiTheta (2 * (τ : ℂ)) := by
  rw [thetaSeries_smul _ (Real.sqrt_ne_zero'.mpr two_pos), thetaSeries_span_one]
  congr 1
  simp [Complex.real_smul]

/-- The period-two coefficients of the rank-one lattice theta series, explicitly supported at
the squares. -/
theorem qExpansion_two_thetaSeries_span_one_coeff (m : ℕ) :
    (qExpansion 2 (thetaSeries (span ℤ {1} : Submodule ℤ ℝ))).coeff m =
      if m = 0 then 1 else if IsSquare m then 2 else 0 := by
  rw [isUnimodular_span_one.isIntegral.qExpansion_two_thetaSeries_coeff,
    representationNumber_span_one]
  split_ifs <;> norm_num

/-- The lattice theta series has the period-two square-supported power series, so its terms
have exactly the same multiplicities as Jacobi's positive-square expansion. -/
theorem hasSum_thetaSeries_span_one_qParam (τ : ℍ) :
    HasSum (fun m : ℕ ↦
      (if m = 0 then 1 else if IsSquare m then 2 else 0 : ℂ) * Periodic.qParam 2 τ ^ m)
      (thetaSeries (span ℤ {1} : Submodule ℤ ℝ) τ) := by
  classical
  simpa only [representationNumber_span_one, smul_eq_mul, Nat.cast_ite, Nat.cast_one,
    Nat.cast_ofNat, Nat.cast_zero] using
    isUnimodular_span_one.isIntegral.hasSum_thetaSeries_qParam_two τ

/-! ### The non-integral lattice `½ ℤ` -/

/-- The dual of `½ ℤ ⊆ ℝ` is `2 ℤ`. -/
@[simp]
theorem dual_span_inv_two :
    dual (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) = span ℤ {(2 : ℝ)} := by
  rw [dual_span_singleton (by norm_num), inv_inv]

/-- The lattice `2 ℤ ⊆ ℝ` is a proper sublattice of `½ ℤ`. -/
theorem span_two_lt_span_inv_two :
    (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) < span ℤ {(2⁻¹ : ℝ)} := by
  refine lt_of_le_of_ne ?_ fun h ↦ ?_
  · rw [span_singleton_le_iff_mem, mem_span_singleton]
    exact ⟨4, by norm_num⟩
  · have hmem : (2⁻¹ : ℝ) ∈ (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) :=
      h ▸ mem_span_singleton_self (2⁻¹ : ℝ)
    obtain ⟨n, hn⟩ := mem_span_singleton.mp hmem
    have h4 : (4 : ℝ) * n = 1 := by rw [zsmul_eq_mul] at hn; linarith
    have h4' : 4 * n = 1 := by exact_mod_cast h4
    omega

/-- For `L = ½ ℤ ⊆ ℝ`, the dual lattice `L^∨ = 2 ℤ` is strictly contained in `L`. -/
theorem dual_span_inv_two_lt :
    dual (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) < span ℤ {(2⁻¹ : ℝ)} :=
  dual_span_inv_two ▸ span_two_lt_span_inv_two

/-- The discriminant group of `½ ℤ ⊆ ℝ` is trivial because its dual `2 ℤ` lies inside `½ ℤ`. -/
theorem subsingleton_discriminantGroup_span_inv_two :
    Subsingleton (DiscriminantGroup (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ)) :=
  subsingleton_discriminantGroup_iff.mpr dual_span_inv_two_lt.le

/-- Zero is the unique element of `DiscriminantGroup (½ ℤ)`. -/
noncomputable instance instUniqueDiscriminantGroupSpanInvTwo :
    Unique (DiscriminantGroup (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ)) :=
  have := subsingleton_discriminantGroup_span_inv_two
  uniqueOfSubsingleton 0

/-- On the imaginary axis, `(Θ_{2ℤ}(τ)).re < (Θ_{½ℤ}(τ)).re`. -/
theorem re_thetaSeries_span_two_lt_span_inv_two {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) τ).re <
      (thetaSeries (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) τ).re :=
  re_thetaSeries_strictMono span_two_lt_span_inv_two hτ

/-- At `τ = i`, the theta series of `2 ℤ` and `½ ℤ` take distinct values. -/
theorem thetaSeries_span_two_apply_I_ne :
    thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) UpperHalfPlane.I ≠
      thetaSeries (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) UpperHalfPlane.I :=
  fun h ↦ (re_thetaSeries_span_two_lt_span_inv_two (by simp)).ne (congrArg re h)

/-- For `L = ½ ℤ ⊆ ℝ`, the dual coset sum formula `Θ_{L^∨}(i) = ∑_{γ ∈ A_L} θ_γ(i)` fails because
`L` is not integral: the left-hand side is `Θ_{2ℤ}(i)` while the right-hand side is `Θ_{½ℤ}(i)`. -/
theorem thetaSeries_dual_span_inv_two_apply_I_ne_sum :
    thetaSeries (dual (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ)) UpperHalfPlane.I ≠
      ∑ γ : DiscriminantGroup (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ),
        thetaCosetClass (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) γ UpperHalfPlane.I :=
  thetaSeries_dual_ne_sum_of_not_isIntegral_of_re_eq_zero not_isIntegral_span_inv_two (by simp)

/-- For `L = ½ ℤ ⊆ ℝ`, `Θ_{L^∨}` does not equal `∑_{γ ∈ A_L} θ_γ`. -/
theorem thetaSeries_dual_span_inv_two_ne_sum :
    thetaSeries (dual (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ)) ≠
      ∑ γ : DiscriminantGroup (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ),
        thetaCosetClass (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) γ :=
  mt (thetaSeries_dual_eq_sum_iff_isIntegral _).mp not_isIntegral_span_inv_two

end ZLattice
