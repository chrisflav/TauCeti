/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Entry bounds for inverses of upper-unitriangular matrices

For an upper-unitriangular matrix `g` on a finite linearly ordered index type `m` of cardinality
`n`, the strictly upper-triangular matrix `1 - g` satisfies `(1 - g) ^ n = 0`, so the inverse of `g`
in the upper-unitriangular group is the truncated geometric series `∑ k < n, (1 - g) ^ k`
(`TauCeti.UpperUnitriangularGroup.coe_inv_eq_geom_sum`).

Over a strictly ordered ring, a uniform bound `|g i j| ≤ B` strictly above the diagonal therefore
bounds every strictly superdiagonal entry of `g⁻¹` by `∑ k ∈ [1, n), n ^ (k - 1) * B ^ k`
(`TauCeti.UpperUnitriangularGroup.abs_inv_apply_le`). In ranks zero and one this bound is `0`, and
in rank two it specializes to the sharp bound `B`.

## References

* A. Borel, *Introduction aux groupes arithmétiques*, Hermann, 1969, §1.5.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.UpperUnitriangularGroup

section Ring

variable {m R : Type*} [Fintype m] [LinearOrder m] [Ring R]

/-- The matrix of the inverse of an upper-unitriangular group element `g` is the truncated
geometric series `∑ k < card m, (1 - g) ^ k`. -/
theorem coe_inv_eq_geom_sum (g : upperUnitriangularGroup m R) :
    (((g⁻¹ : upperUnitriangularGroup m R) : GL m R) : Matrix m m R) =
      ∑ k ∈ Finset.range (Fintype.card m), (1 - ((g : GL m R) : Matrix m m R)) ^ k := by
  let x : Matrix m m R := 1 - ((g : GL m R) : Matrix m m R)
  have hxtri : x.IsUpperTriangular :=
    Matrix.blockTriangular_one.sub (isUpperTriangular g)
  have hxdiag : ∀ i, x i i = 0 := fun i ↦ by
    simp [x]
  have hxpow : x ^ Fintype.card m = 0 :=
    Matrix.pow_card_eq_zero_of_isUpperTriangular_of_diag_eq_zero hxtri hxdiag
  have hmul : ((g : GL m R) : Matrix m m R) * ∑ k ∈ Finset.range (Fintype.card m), x ^ k = 1 := by
    have hg : ((g : GL m R) : Matrix m m R) = 1 - x := by simp [x]
    rw [hg, mul_neg_geom_sum, hxpow, sub_zero]
  calc (((g⁻¹ : upperUnitriangularGroup m R) : GL m R) : Matrix m m R)
      = (((g : GL m R)⁻¹ : GL m R) : Matrix m m R) *
          (((g : GL m R) : Matrix m m R) * ∑ k ∈ Finset.range (Fintype.card m), x ^ k) := by
        rw [hmul, Matrix.mul_one]
        rfl
    _ = ((((g : GL m R)⁻¹ * (g : GL m R) : GL m R) : Matrix m m R)) *
          ∑ k ∈ Finset.range (Fintype.card m), x ^ k := by
        rw [Units.val_mul, Matrix.mul_assoc]
    _ = ∑ k ∈ Finset.range (Fintype.card m), x ^ k := by
        rw [inv_mul_cancel, Units.val_one, Matrix.one_mul]

end Ring

section OrderedRing

variable {m R : Type*} [Fintype m] [LinearOrder m]
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

private theorem abs_pow_succ_apply_le {X : Matrix m m R} {B : R} (hB : 0 ≤ B)
    (hX : ∀ i j, |X i j| ≤ B) (k : ℕ) (i j : m) :
    |(X ^ (k + 1)) i j| ≤ (Fintype.card m : R) ^ k * B ^ (k + 1) := by
  induction k generalizing i j with
  | zero => simpa using hX i j
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    calc |∑ l, (X ^ (k + 1)) i l * X l j|
        ≤ ∑ l, |(X ^ (k + 1)) i l * X l j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |(X ^ (k + 1)) i l| * |X l j| := by simp only [abs_mul]
      _ ≤ ∑ _l : m, ((Fintype.card m : R) ^ k * B ^ (k + 1)) * B := by
          refine Finset.sum_le_sum fun l _ ↦ mul_le_mul (ih i l) (hX l j) (abs_nonneg _) ?_
          positivity
      _ = (Fintype.card m : R) ^ (k + 1) * B ^ (k + 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
            ← pow_succ', mul_assoc, ← pow_succ]

/-- If every entry of an upper-unitriangular matrix `g` strictly above the diagonal has absolute
value at most `B`, then every entry of `g⁻¹` strictly above the diagonal has absolute value at
most `∑ k ∈ Finset.Ico 1 (card m), (card m) ^ (k - 1) * B ^ k`. -/
theorem abs_inv_apply_le (g : upperUnitriangularGroup m R) {B : R}
    (hg : ∀ i j, i < j → |((g : GL m R) : Matrix m m R) i j| ≤ B) {i j : m} (hij : i < j) :
    |(((g⁻¹ : upperUnitriangularGroup m R) : GL m R) : Matrix m m R) i j| ≤
      ∑ k ∈ Finset.Ico 1 (Fintype.card m), (Fintype.card m : R) ^ (k - 1) * B ^ k := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg i j hij)
  let x : Matrix m m R := 1 - ((g : GL m R) : Matrix m m R)
  have hx (a b : m) : |x a b| ≤ B := by
    rcases lt_trichotomy a b with hab | rfl | hba
    · simpa [x, Matrix.one_apply_ne hab.ne] using hg a b hab
    · simp [x, hB]
    · simp [x, Matrix.one_apply_ne hba.ne', isUpperTriangular g hba, hB]
  have hpos : 1 ≤ Fintype.card m := Fintype.card_pos_iff.mpr ⟨i⟩
  rw [coe_inv_eq_geom_sum g, Matrix.sum_apply,
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hpos]
  simp only [pow_zero, Matrix.one_apply_ne hij.ne, zero_add]
  calc |∑ k ∈ Finset.Ico 1 (Fintype.card m), (x ^ k) i j|
      ≤ ∑ k ∈ Finset.Ico 1 (Fintype.card m), |(x ^ k) i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico 1 (Fintype.card m), (Fintype.card m : R) ^ (k - 1) * B ^ k := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        rcases k with _ | k'
        · simp at hk
        · simpa using abs_pow_succ_apply_le hB hx k' i j

end OrderedRing

end TauCeti.UpperUnitriangularGroup
