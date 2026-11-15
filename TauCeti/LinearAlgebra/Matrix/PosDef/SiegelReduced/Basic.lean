/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Fin.Tuple.Sort
import TauCeti.Analysis.Matrix.LDL

/-!
# Siegel-reduced positive-definite matrices

A square matrix `B` on a finite linearly ordered index type `ι` over an ordered commutative ring is
`C`-*Siegel reduced* (`Matrix.IsSiegelReduced B C`) when:
1. `|B i j| < C * B i i` for all `i, j`;
2. `B i i < C * B j j` whenever `i < j`;
3. `(∏ i, B i i) < C * B.det`.

For positive-definite real symmetric matrices (or more generally matrices with nonnegative diagonal
entries), `C`-Siegel reducedness forces `1 < C`, positive diagonal entries, and positive
determinant, is monotone in `C`, and is invariant under positive scalar multiplication and hence
under determinant-one normalization `det(B) ^ (-1 / n) • B`.

Two quantitative estimates control basis changes of Siegel-reduced positive-definite matrices:
* `Matrix.PosDef.sq_mul_diag_le_mul_dotProduct_mulVec`: if `(∏ i, B i i) ≤ D * B.det`, then every
  real vector `x` and index `k` satisfy `x k ^ 2 * B k k ≤ D * (x ⬝ᵥ B *ᵥ x)`. Applying Mathlib's
  `LDL` decomposition after swapping `k` to the top index bounds `B k k` by `D` times the last `LDL`
  pivot while `(Lᵀ *ᵥ x)_{last} = x_{last}`.
* `Matrix.exists_perm_submatrix_isSiegelReduced`: if `B` is `C'`-Siegel reduced and an invertible
  change of basis `A ∈ GL_n(ℝ)` has controlled Hadamard ratio `(∏ i, B' i i) ≤ C * B'.det` on
  `B' = Aᵀ * B * A`, then sorting the diagonal of `B'` produces a `C''`-Siegel reduced matrix for a
  constant `C'' > 1` depending only on `C`, `C'`, and `A`. Re-sorting is essential: swapping the
  coordinates of `diag(1, N)` satisfies the determinant bound with `C = 2` for every `N ≥ 2` while
  requiring `C'' > N` without sorting.

## References

* A. Borel, *Introduction aux groupes arithmétiques*, Hermann, 1969, §1–§2.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, 2nd ed.,
  Cambridge University Press, 2023, §4.2, pp. 205–208.
* B. Bakker, B. Klingler, and J. Tsimerman, *Tame topology of arithmetic quotients and algebraicity
  of Hodge loci*, J. Amer. Math. Soc. 33 (2020), 917–939, §4.5, Definition 4.11.
-/

public section

open scoped Matrix MatrixGroups

namespace Matrix

section OrderedCommRing

variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R] [LinearOrder R]

/-- A square matrix `B` on a finite linearly ordered index type `ι` is `C`-*Siegel reduced* when
every entry in row `i` is strictly bounded in absolute value by `C * B i i`, the diagonal grows at
most up to the factor `C`, and the product of the diagonal entries is strictly less than
`C * B.det`. -/
def IsSiegelReduced (B : Matrix ι ι R) (C : R) : Prop :=
  (∀ i j, |B i j| < C * B i i) ∧ (∀ i j, i < j → B i i < C * B j j) ∧
    (∏ i, B i i) < C * B.det

/-- Unfolding `Matrix.IsSiegelReduced` into its three defining inequalities. -/
theorem isSiegelReduced_def {B : Matrix ι ι R} {C : R} :
    B.IsSiegelReduced C ↔
      (∀ i j, |B i j| < C * B i i) ∧ (∀ i j, i < j → B i i < C * B j j) ∧
        (∏ i, B i i) < C * B.det :=
  Iff.rfl

namespace IsSiegelReduced

/-- Off-diagonal (and diagonal) row bound of a `C`-Siegel reduced matrix. -/
theorem abs_apply_lt {B : Matrix ι ι R} {C : R} (h : B.IsSiegelReduced C) (i j : ι) :
    |B i j| < C * B i i :=
  h.1 i j

/-- Quasi-monotonicity of the diagonal of a `C`-Siegel reduced matrix. -/
theorem diag_lt_of_lt {B : Matrix ι ι R} {C : R} (h : B.IsSiegelReduced C) {i j : ι}
    (hij : i < j) : B i i < C * B j j :=
  h.2.1 i j hij

/-- Hadamard-type determinant lower bound of a `C`-Siegel reduced matrix. -/
theorem prod_diag_lt {B : Matrix ι ι R} {C : R} (h : B.IsSiegelReduced C) :
    (∏ i, B i i) < C * B.det :=
  h.2.2

section StrictOrdered

variable [IsStrictOrderedRing R]

/-- Every `C`-Siegel reduced matrix with nonnegative diagonal entries has `0 < B i i`. -/
theorem diag_pos {B : Matrix ι ι R} {C : R} (h : B.IsSiegelReduced C)
    (hdiag : ∀ i, 0 ≤ B i i) (i : ι) : 0 < B i i := by
  rcases (hdiag i).eq_or_lt with h0 | hpos
  · have hlt := h.abs_apply_lt i i
    simp [← h0] at hlt
  · exact hpos

/-- Every `C`-Siegel reduced matrix with nonnegative diagonal entries satisfies `1 < C`, including
when `ι` is empty. -/
theorem one_lt {B : Matrix ι ι R} {C : R} (h : B.IsSiegelReduced C)
    (hdiag : ∀ i, 0 ≤ B i i) : 1 < C := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · have hlt := h.prod_diag_lt
    simpa using hlt
  · have hpos := h.diag_pos hdiag i₀
    have hlt := h.abs_apply_lt i₀ i₀
    rw [abs_of_pos hpos] at hlt
    exact (lt_mul_iff_one_lt_left hpos).mp hlt

/-- Every `C`-Siegel reduced matrix with nonnegative diagonal entries has positive determinant. -/
theorem det_pos {B : Matrix ι ι R} {C : R} (h : B.IsSiegelReduced C)
    (hdiag : ∀ i, 0 ≤ B i i) : 0 < B.det := by
  have hprod : 0 ≤ ∏ i, B i i := Finset.prod_nonneg fun i _ ↦ hdiag i
  have hC : 0 < C := zero_lt_one.trans (h.one_lt hdiag)
  exact pos_of_mul_pos_right (hprod.trans_lt h.prod_diag_lt) hC.le

/-- Monotonicity of `IsSiegelReduced` in the reduction constant `C` for matrices with nonnegative
diagonal entries. -/
theorem mono {B : Matrix ι ι R} {C C' : R} (h : B.IsSiegelReduced C)
    (hdiag : ∀ i, 0 ≤ B i i) (hCC' : C ≤ C') : B.IsSiegelReduced C' := by
  refine ⟨fun i j ↦ (h.abs_apply_lt i j).trans_le (mul_le_mul_of_nonneg_right hCC' (hdiag i)),
    fun i j hij ↦ (h.diag_lt_of_lt hij).trans_le (mul_le_mul_of_nonneg_right hCC' (hdiag j)),
    h.prod_diag_lt.trans_le (mul_le_mul_of_nonneg_right hCC' (h.det_pos hdiag).le)⟩

end StrictOrdered

end IsSiegelReduced

/-- Reindexing along an order isomorphism preserves `C`-Siegel reducedness. -/
@[simp]
theorem _root_.OrderIso.isSiegelReduced_submatrix_iff {ι' : Type*} [Fintype ι'] [LinearOrder ι']
    (e : ι' ≃o ι) {B : Matrix ι ι R} {C : R} :
    (B.submatrix e e).IsSiegelReduced C ↔ B.IsSiegelReduced C := by
  have hprod : (∏ i, B (e i) (e i)) = ∏ i, B i i := Equiv.prod_comp e.toEquiv fun i ↦ B i i
  have hdet : (B.submatrix e e).det = B.det := det_submatrix_equiv_self e.toEquiv B
  refine ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩,
    fun ⟨h1, h2, h3⟩ ↦
      ⟨fun i j ↦ h1 (e i) (e j), fun i j hij ↦ h2 (e i) (e j) (e.lt_iff_lt.mpr hij),
        by simpa [hprod, hdet] using h3⟩⟩
  · simpa using h1 (e.symm i) (e.symm j)
  · simpa using h2 (e.symm i) (e.symm j) (e.symm.lt_iff_lt.mpr hij)
  · simpa [hprod, hdet] using h3

/-- On an empty index type, a matrix is `C`-Siegel reduced if and only if `1 < C`. -/
@[simp]
theorem isSiegelReduced_of_isEmpty [IsEmpty ι] {B : Matrix ι ι R} {C : R} :
    B.IsSiegelReduced C ↔ 1 < C := by
  simp [IsSiegelReduced]

section BasicProperties

variable [IsStrictOrderedRing R]

/-- The identity matrix on any finite linearly ordered index type is `C`-Siegel reduced if and only
if `1 < C`. -/
@[simp]
theorem isSiegelReduced_one {C : R} : (1 : Matrix ι ι R).IsSiegelReduced C ↔ 1 < C := by
  refine ⟨fun h ↦ h.one_lt fun i ↦ by simp, fun hC ↦ ⟨fun i j ↦ ?_, fun i j _ ↦ ?_, ?_⟩⟩
  · rcases eq_or_ne i j with rfl | hij <;> simp [*, zero_lt_one.trans hC]
  · simpa using hC
  · simpa using hC

/-- On a nonempty index type, the zero matrix is never Siegel reduced. -/
@[simp]
theorem not_isSiegelReduced_zero [Nonempty ι] (C : R) :
    ¬ (0 : Matrix ι ι R).IsSiegelReduced C := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  intro h
  have := h.abs_apply_lt i₀ i₀
  simp at this

/-- Scaling a matrix by a positive scalar preserves `C`-Siegel reducedness. -/
theorem isSiegelReduced_smul_iff {B : Matrix ι ι R} {a C : R} (ha : 0 < a) :
    (a • B).IsSiegelReduced C ↔ B.IsSiegelReduced C := by
  have hapow : 0 < a ^ Fintype.card ι := pow_pos ha _
  have hprod : (∏ i, (a • B) i i) = a ^ Fintype.card ι * ∏ i, B i i := by
    simp_rw [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  refine ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩,
    fun ⟨h1, h2, h3⟩ ↦ ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩⟩
  · have h := h1 i j
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      abs_mul, abs_of_pos ha, mul_left_comm C a] at h
    exact lt_of_mul_lt_mul_left h ha.le
  · have h := h2 i j hij
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm C a] at h
    exact lt_of_mul_lt_mul_left h ha.le
  · rw [hprod, det_smul, mul_left_comm C (a ^ Fintype.card ι)] at h3
    exact lt_of_mul_lt_mul_left h3 hapow.le
  · rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      abs_mul, abs_of_pos ha, mul_left_comm C a]
    exact mul_lt_mul_of_pos_left (h1 i j) ha
  · rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm C a]
    exact mul_lt_mul_of_pos_left (h2 i j hij) ha
  · rw [hprod, det_smul, mul_left_comm C (a ^ Fintype.card ι)]
    exact mul_lt_mul_of_pos_left h3 hapow

/-- On a nonempty index type, the negative of a positive-definite matrix over a strictly ordered
commutative ring is not `C`-Siegel reduced for any `C ≥ 0`. -/
theorem PosDef.not_isSiegelReduced_neg [Nonempty ι] [StarRing R] {B : Matrix ι ι R}
    (hB : B.PosDef) {C : R} (hC : 0 ≤ C) :
    ¬ (-B).IsSiegelReduced C := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  intro h
  have hpos : 0 < B i₀ i₀ := hB.diag_pos
  have hlt := h.abs_apply_lt i₀ i₀
  rw [Matrix.neg_apply, abs_neg, abs_of_pos hpos, mul_neg] at hlt
  nlinarith

end BasicProperties

end OrderedCommRing

/-- A `1 × 1` positive-definite matrix over a strictly ordered commutative ring is `C`-Siegel
reduced if and only if `1 < C`. -/
theorem PosDef.isSiegelReduced_fin_one_iff {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [StarRing R] {B : Matrix (Fin 1) (Fin 1) R}
    (hB : B.PosDef) {C : R} : B.IsSiegelReduced C ↔ 1 < C := by
  have h0 : 0 < B 0 0 := hB.diag_pos
  have hB_eq : B = B 0 0 • (1 : Matrix (Fin 1) (Fin 1) R) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hB_eq, isSiegelReduced_smul_iff h0, isSiegelReduced_one]

section Real

/-- Normalizing a positive-definite real matrix by `det(B) ^ (-1 / card ι)` preserves `C`-Siegel
reducedness. -/
theorem PosDef.isSiegelReduced_det_rpow_neg_inv_smul_iff {ι : Type*} [Fintype ι] [LinearOrder ι]
    {B : Matrix ι ι ℝ} (hB : B.PosDef) {C : ℝ} :
    (B.det ^ (-(Fintype.card ι : ℝ)⁻¹) • B).IsSiegelReduced C ↔ B.IsSiegelReduced C :=
  isSiegelReduced_smul_iff (Real.rpow_pos_of_pos hB.det_pos _)

/-- Normalizing a positive-definite real matrix by `det(B) ^ (-1 / card ι)` produces a matrix of
determinant `1` (including on an empty index type, via `0⁻¹ = 0`). -/
theorem PosDef.det_det_rpow_neg_inv_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hB : B.PosDef) :
    (B.det ^ (-(Fintype.card ι : ℝ)⁻¹) • B).det = 1 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [det_smul, ← Real.rpow_natCast (B.det ^ _), ← Real.rpow_mul hB.det_pos.le,
      neg_mul, inv_mul_cancel₀ hn, Real.rpow_neg_one, inv_mul_cancel₀ hB.det_pos.ne']

/-- `diag(1, 4)` is `2`-Siegel reduced, whereas `diag(4, 1)` (unsorted diagonal) and
`diag(1, 1 / 4)` (its inverse) are not. -/
theorem isSiegelReduced_diagonal_fin_two_examples :
    (diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ).IsSiegelReduced 2 ∧
      ¬ (diagonal ![4, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsSiegelReduced 2 ∧
      ¬ (diagonal ![1, 1 / 4] : Matrix (Fin 2) (Fin 2) ℝ).IsSiegelReduced 2 := by
  refine ⟨⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩, fun h ↦ ?_, fun h ↦ ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num [diagonal]
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢; norm_num
  · norm_num [det_diagonal, Fin.prod_univ_two]
  · have hlt := h.diag_lt_of_lt (show (0 : Fin 2) < 1 by decide)
    norm_num at hlt
  · have hlt := h.diag_lt_of_lt (show (0 : Fin 2) < 1 by decide)
    norm_num at hlt

/-- For a positive-definite real matrix on `Fin (m + 1)` with `(∏ i, B i i) ≤ D * B.det`, every
diagonal entry is bounded by `D` times the corresponding `LDL` pivot. -/
private theorem ldl_diag_le_mul_diagEntries {m : ℕ}
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hB : B.PosDef) {D : ℝ}
    (hD : (∏ i, B i i) ≤ D * B.det) (l : Fin (m + 1)) :
    B l l ≤ D * LDL.diagEntries hB l := by
  set L := LDL.lower hB
  set d := LDL.diagEntries hB
  have hd_pos (i : Fin (m + 1)) : 0 < d i := LDL.diagEntries_pos hB i
  have hB_eq : B = L * diagonal d * Lᵀ := by
    simpa [L, d, LDL.diag] using (LDL.lower_conj_diag hB).symm
  have hd_le (i : Fin (m + 1)) : d i ≤ B i i := by
    have hsum : B i i = ∑ j, L i j ^ 2 * d j := by
      rw [hB_eq, Matrix.mul_assoc, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Matrix.diagonal_mul, Matrix.transpose_apply]
      ring
    rw [hsum]
    calc d i = L i i ^ 2 * d i := by simp [L, LDL.lower_apply_diag]
      _ ≤ ∑ j, L i j ^ 2 * d j :=
          Finset.single_le_sum (fun j _ ↦ mul_nonneg (sq_nonneg _) (hd_pos j).le)
            (Finset.mem_univ i)
  have hdet : B.det = ∏ i, d i := by
    have hLdet : L.det = 1 := by
      rw [det_of_isLowerTriangular L (LDL.isLowerTriangular_lower hB)]
      exact Finset.prod_eq_one fun i _ ↦ LDL.lower_apply_diag hB i
    rw [hB_eq, det_mul, det_mul, det_transpose, hLdet, one_mul, mul_one, det_diagonal]
  have herase_pos : 0 < ∏ i ∈ Finset.univ.erase l, d i := Finset.prod_pos fun i _ ↦ hd_pos i
  have herase_le : (∏ i ∈ Finset.univ.erase l, d i) ≤ ∏ i ∈ Finset.univ.erase l, B i i :=
    Finset.prod_le_prod₀ (fun i _ ↦ (hd_pos i).le) (fun i _ ↦ hd_le i)
  refine le_of_mul_le_mul_right ?_ herase_pos
  calc B l l * (∏ i ∈ Finset.univ.erase l, d i)
      ≤ B l l * (∏ i ∈ Finset.univ.erase l, B i i) :=
        mul_le_mul_of_nonneg_left herase_le hB.diag_pos.le
    _ = ∏ i, B i i := Finset.mul_prod_erase Finset.univ (fun i ↦ B i i) (Finset.mem_univ l)
    _ ≤ D * B.det := hD
    _ = D * d l * (∏ i ∈ Finset.univ.erase l, d i) := by
        rw [hdet, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ l), mul_assoc]

/-- Helper on `Fin (m + 1)`: the last diagonal entry of a positive-definite matrix is bounded by
`D` times the last `LDL` pivot, and `LDL` bounds the quadratic form from below by that pivot. -/
private theorem sq_last_mul_diag_le_mul_dotProduct_mulVec {m : ℕ}
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hB : B.PosDef) {D : ℝ}
    (hD : (∏ i, B i i) ≤ D * B.det) (y : Fin (m + 1) → ℝ) :
    y (Fin.last m) ^ 2 * B (Fin.last m) (Fin.last m) ≤ D * (y ⬝ᵥ B *ᵥ y) := by
  set L := LDL.lower hB
  set d := LDL.diagEntries hB
  set l := Fin.last m
  have hB_eq : B = L * diagonal d * Lᵀ := by
    simpa [L, d, LDL.diag] using (LDL.lower_conj_diag hB).symm
  have hDpos : 0 < D :=
    pos_of_mul_pos_left ((Finset.prod_pos fun _ _ ↦ hB.diag_pos).trans_le hD) hB.det_pos.le
  have hpivot : B l l ≤ D * d l := ldl_diag_le_mul_diagEntries hB hD l
  have hLy : (Lᵀ *ᵥ y) l = y l := by
    rw [mulVec, dotProduct, Finset.sum_eq_single l]
    · simp [L, LDL.lower_apply_diag]
    · intro j _ hjl
      have h0 : L j l = 0 := LDL.isLowerTriangular_lower hB ((Fin.le_last j).lt_of_ne hjl)
      simp [h0]
    · simp
  have hquad : d l * y l ^ 2 ≤ y ⬝ᵥ B *ᵥ y := by
    have hsum : y ⬝ᵥ B *ᵥ y = ∑ i, d i * (Lᵀ *ᵥ y) i ^ 2 := by
      calc y ⬝ᵥ B *ᵥ y
          = y ⬝ᵥ L *ᵥ (diagonal d *ᵥ (Lᵀ *ᵥ y)) := by
              rw [hB_eq, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]
        _ = (Lᵀ *ᵥ y) ⬝ᵥ (diagonal d *ᵥ (Lᵀ *ᵥ y)) := by
              rw [dotProduct_mulVec, ← mulVec_transpose]
        _ = ∑ i, d i * (Lᵀ *ᵥ y) i ^ 2 := by
              simp only [dotProduct, mulVec_diagonal]
              exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsum, ← hLy]
    exact Finset.single_le_sum
      (fun i _ ↦ mul_nonneg (LDL.diagEntries_pos hB i).le (sq_nonneg _)) (Finset.mem_univ l)
  calc y l ^ 2 * B l l ≤ y l ^ 2 * (D * d l) := mul_le_mul_of_nonneg_left hpivot (sq_nonneg _)
    _ = D * (d l * y l ^ 2) := by ring
    _ ≤ D * (y ⬝ᵥ B *ᵥ y) := mul_le_mul_of_nonneg_left hquad hDpos.le

/-- **Lower bound of a positive-definite quadratic form by its diagonal and Hadamard ratio.**
If `B` is a positive-definite real matrix with `(∏ i, B i i) ≤ D * B.det`, then every vector `x`
and index `k` satisfy `x k ^ 2 * B k k ≤ D * (x ⬝ᵥ B *ᵥ x)`. -/
theorem PosDef.sq_mul_diag_le_mul_dotProduct_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hB : B.PosDef) {D : ℝ} (hD : (∏ i, B i i) ≤ D * B.det)
    (x : ι → ℝ) (k : ι) :
    x k ^ 2 * B k k ≤ D * (x ⬝ᵥ B *ᵥ x) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos_iff.mpr ⟨k⟩).ne'
  let e₀ : ι ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hm
  let e : Fin (m + 1) ≃ ι := (Equiv.swap (Fin.last m) (e₀ k)).trans e₀.symm
  have he_last : e (Fin.last m) = k := by simp [e]
  have hB' : (B.submatrix e e).PosDef := hB.submatrix e.injective
  have hD' : (∏ i, (B.submatrix e e) i i) ≤ D * (B.submatrix e e).det := by
    dsimp only [submatrix_apply]
    rwa [show (∏ i, B (e i) (e i)) = ∏ i, B i i from Equiv.prod_comp e fun i ↦ B i i,
      det_submatrix_equiv_self e B]
  have hquad : (x ∘ e) ⬝ᵥ (B.submatrix e e) *ᵥ (x ∘ e) = x ⬝ᵥ B *ᵥ x := by
    simp only [dotProduct, mulVec, submatrix_apply, Function.comp_apply]
    exact (Equiv.sum_comp e fun i ↦ x i * ∑ j, B i (e j) * x (e j)).trans
      (Finset.sum_congr rfl fun i _ ↦ congrArg (x i * ·) (Equiv.sum_comp e fun j ↦ B i j * x j))
  simpa [he_last, hquad] using sq_last_mul_diag_le_mul_dotProduct_mulVec hB' hD' (x ∘ e)

/-- **Transferring off-diagonal bounds across a change of basis.** Let `B` be a positive-definite
real matrix with `|B a b| ≤ C' * B a a`, `B a a ≤ C' * B b b` for `a < b`, and
`(∏ a, B a a) ≤ C' * B.det`. For vectors `u, v` and an index `k` such that `u a = 0` for all
`k < a`, one has
`|u ⬝ᵥ B *ᵥ v| * u k ^ 2 ≤ C' ^ 3 * (∑ a, |u a|) * (∑ b, |v b|) * (u ⬝ᵥ B *ᵥ u)`. -/
theorem PosDef.abs_dotProduct_mulVec_mul_sq_le {ι : Type*} [Fintype ι] [LinearOrder ι]
    {B : Matrix ι ι ℝ} (hB : B.PosDef) {C' : ℝ}
    (hoff : ∀ a b, |B a b| ≤ C' * B a a) (hdiag : ∀ a b, a < b → B a a ≤ C' * B b b)
    (hdet : (∏ a, B a a) ≤ C' * B.det) (u v : ι → ℝ) (k : ι) (hk : ∀ a, k < a → u a = 0) :
    |u ⬝ᵥ B *ᵥ v| * u k ^ 2 ≤
      C' ^ 3 * (∑ a, |u a|) * (∑ b, |v b|) * (u ⬝ᵥ B *ᵥ u) := by
  have hBkk : 0 < B k k := hB.diag_pos
  have hC' : 1 ≤ C' :=
    le_of_mul_le_mul_right (by simpa [abs_of_pos hBkk] using hoff k k) hBkk
  have hterm (a b : ι) : |u a * (B a b * v b)| ≤ |u a| * |v b| * (C' ^ 2 * B k k) := by
    rw [abs_mul, abs_mul]
    rcases lt_trichotomy a k with hak | rfl | hka
    · have hBab : |B a b| ≤ C' ^ 2 * B k k :=
        calc |B a b| ≤ C' * B a a := hoff a b
          _ ≤ C' * (C' * B k k) := mul_le_mul_of_nonneg_left (hdiag a k hak) (zero_le_one.trans hC')
          _ = C' ^ 2 * B k k := by ring
      calc |u a| * (|B a b| * |v b|) = |u a| * |v b| * |B a b| := by ring
        _ ≤ |u a| * |v b| * (C' ^ 2 * B k k) :=
          mul_le_mul_of_nonneg_left hBab (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · have hBkb : |B a b| ≤ C' ^ 2 * B a a :=
        calc |B a b| ≤ C' * B a a := hoff a b
          _ = 1 * (C' * B a a) := (one_mul _).symm
          _ ≤ C' * (C' * B a a) := mul_le_mul_of_nonneg_right hC' (by positivity)
          _ = C' ^ 2 * B a a := by ring
      calc |u a| * (|B a b| * |v b|) = |u a| * |v b| * |B a b| := by ring
        _ ≤ |u a| * |v b| * (C' ^ 2 * B a a) :=
          mul_le_mul_of_nonneg_left hBkb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · simp [hk a hka]
  have hsum : |u ⬝ᵥ B *ᵥ v| ≤ C' ^ 2 * (∑ a, |u a|) * (∑ b, |v b|) * B k k := by
    rw [dotProduct]
    calc |∑ a, u a * (B *ᵥ v) a|
        ≤ ∑ a, |u a * (B *ᵥ v) a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, |u a * (B a b * v b)| := by
          refine Finset.sum_le_sum fun a _ ↦ ?_
          rw [mulVec, dotProduct, Finset.mul_sum]
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, |u a| * |v b| * (C' ^ 2 * B k k) :=
          Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ hterm a b
      _ = C' ^ 2 * (∑ a, |u a|) * (∑ b, |v b|) * B k k := by
          trans ∑ a, (|u a| * (∑ b, |v b|) * (C' ^ 2 * B k k))
          · refine Finset.sum_congr rfl fun a _ ↦ ?_
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          · rw [← Finset.sum_mul, ← Finset.sum_mul]
            ring
  have hlow := hB.sq_mul_diag_le_mul_dotProduct_mulVec hdet u k
  calc |u ⬝ᵥ B *ᵥ v| * u k ^ 2
      ≤ (C' ^ 2 * (∑ a, |u a|) * (∑ b, |v b|) * B k k) * u k ^ 2 :=
        mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
    _ = C' ^ 2 * (∑ a, |u a|) * (∑ b, |v b|) * (u k ^ 2 * B k k) := by ring
    _ ≤ C' ^ 2 * (∑ a, |u a|) * (∑ b, |v b|) * (C' * (u ⬝ᵥ B *ᵥ u)) := by
        refine mul_le_mul_of_nonneg_left hlow ?_
        positivity
    _ = C' ^ 3 * (∑ a, |u a|) * (∑ b, |v b|) * (u ⬝ᵥ B *ᵥ u) := by ring

/-- Every column of an invertible matrix on a finite linearly ordered index type has a largest
row index with a nonzero entry. -/
private theorem exists_col_max_nonzero {n : ℕ} (A : GL (Fin n) ℝ) :
    ∃ k : Fin n → Fin n,
      (∀ i, (A : Matrix (Fin n) (Fin n) ℝ) (k i) i ≠ 0) ∧
      (∀ i a, k i < a → (A : Matrix (Fin n) (Fin n) ℝ) a i = 0) := by
  classical
  have hcol_ne (i : Fin n) :
      (Finset.univ.filter fun a : Fin n ↦ (A : Matrix (Fin n) (Fin n) ℝ) a i ≠ 0).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hzero : (A : Matrix (Fin n) (Fin n) ℝ) *ᵥ Pi.single i 1 = 0 := by
      ext a
      have ha : (A : Matrix (Fin n) (Fin n) ℝ) a i = 0 := by
        by_contra hne
        have : a ∈ (∅ : Finset (Fin n)) := hemp ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ a, hne⟩
        simp at this
      simp [mulVec_single, ha]
    have h1 : (Pi.single i (1 : ℝ)) = 0 :=
      mulVec_injective_of_isUnit A.isUnit (by simpa using hzero)
    simpa using congrFun h1 i
  refine ⟨fun i ↦
    (Finset.univ.filter fun a : Fin n ↦ (A : Matrix (Fin n) (Fin n) ℝ) a i ≠ 0).max' (hcol_ne i),
    fun i ↦ (Finset.mem_filter.mp (Finset.max'_mem _ (hcol_ne i))).2,
    fun i a hka ↦ ?_⟩
  by_contra hne
  exact not_le_of_gt hka (Finset.le_max' _ a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hne⟩))

/-- **Basis change with determinant control and diagonal sorting.** Given `A ∈ GL_n(ℝ)` and
constants `C, C' : ℝ`, there is a constant `C'' > 1` depending only on `C`, `C'`, and `A` such that
for every positive-definite `C'`-Siegel reduced matrix `B` whose pullback `B' = Aᵀ * B * A`
satisfies `(∏ i, B' i i) ≤ C * B'.det`, the permutation `σ` sorting the diagonal of `B'` makes
`B'.submatrix σ σ` a `C''`-Siegel reduced matrix. -/
theorem exists_perm_submatrix_isSiegelReduced {n : ℕ} (A : GL (Fin n) ℝ) (C C' : ℝ) :
    ∃ C'' : ℝ, 1 < C'' ∧ ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef → B.IsSiegelReduced C' →
      (∏ i, ((A : Matrix (Fin n) (Fin n) ℝ)ᵀ * B * (A : Matrix (Fin n) (Fin n) ℝ)) i i) ≤
        C * ((A : Matrix (Fin n) (Fin n) ℝ)ᵀ * B * (A : Matrix (Fin n) (Fin n) ℝ)).det →
      ∃ σ : Equiv.Perm (Fin n),
        Monotone (fun i ↦
          ((A : Matrix (Fin n) (Fin n) ℝ)ᵀ * B * (A : Matrix (Fin n) (Fin n) ℝ)) (σ i) (σ i)) ∧
        (((A : Matrix (Fin n) (Fin n) ℝ)ᵀ * B * (A : Matrix (Fin n) (Fin n) ℝ)).submatrix
          σ σ).IsSiegelReduced C'' := by
  obtain ⟨k, hk_ne, hk_max⟩ := exists_col_max_nonzero A
  let C₀ : ℝ := max C 1
  let C'₀ : ℝ := max C' 1
  let L : Fin n → ℝ := fun i ↦ ∑ a, |(A : Matrix (Fin n) (Fin n) ℝ) a i|
  let w : Fin n → Fin n → ℝ := fun p q ↦
    C'₀ ^ 3 * L p * L q / ((A : Matrix (Fin n) (Fin n) ℝ) (k p) p) ^ 2
  have hw_nonneg (p q : Fin n) : 0 ≤ w p q := by
    have hLp : 0 ≤ L p := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hLq : 0 ≤ L q := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hC'₀ : 0 ≤ C'₀ := zero_le_one.trans (le_max_right C' 1)
    exact div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC'₀ 3) hLp) hLq) (sq_nonneg _)
  let Moff : ℝ := ∑ p, ∑ q, w p q
  let C'' : ℝ := max C₀ Moff + 2
  refine ⟨C'', by linarith [le_max_left C₀ Moff, le_max_right C 1], fun B hB hred₀ hdet₀ ↦ ?_⟩
  have hred : B.IsSiegelReduced C'₀ := hred₀.mono (fun _ ↦ hB.diag_pos.le) (le_max_left C' 1)
  set B' := (A : Matrix (Fin n) (Fin n) ℝ)ᵀ * B * (A : Matrix (Fin n) (Fin n) ℝ)
  have hB' : B'.PosDef := by
    simpa [B'] using hB.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit A.isUnit)
  have hdet : (∏ i, B' i i) ≤ C₀ * B'.det :=
    hdet₀.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) hB'.det_pos.le)
  let σ : Equiv.Perm (Fin n) := Tuple.sort fun i ↦ B' i i
  have hmono : Monotone fun i ↦ B' (σ i) (σ i) := Tuple.monotone_sort fun i ↦ B' i i
  refine ⟨σ, hmono, ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩⟩
  · have hentry (p q : Fin n) : B' p q =
        (fun a ↦ (A : Matrix (Fin n) (Fin n) ℝ) a p) ⬝ᵥ B *ᵥ
          (fun b ↦ (A : Matrix (Fin n) (Fin n) ℝ) b q) := by
      simp [B', Matrix.mul_assoc, Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum]
    have htr := hB.abs_dotProduct_mulVec_mul_sq_le
      (fun a b ↦ (hred.abs_apply_lt a b).le) (fun a b hab ↦ (hred.diag_lt_of_lt hab).le)
      hred.prod_diag_lt.le (fun a ↦ (A : Matrix (Fin n) (Fin n) ℝ) a (σ i))
      (fun b ↦ (A : Matrix (Fin n) (Fin n) ℝ) b (σ j)) (k (σ i)) (hk_max (σ i))
    rw [← hentry (σ i) (σ j), ← hentry (σ i) (σ i)] at htr
    have hdiv : |B' (σ i) (σ j)| ≤ w (σ i) (σ j) * B' (σ i) (σ i) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_ne_zero (hk_ne (σ i)))]
      simpa [L, mul_assoc] using htr
    have hterm_le : w (σ i) (σ j) ≤ Moff :=
      (Finset.single_le_sum (fun q _ ↦ hw_nonneg (σ i) q) (Finset.mem_univ (σ j))).trans
        (Finset.single_le_sum (fun p _ ↦ Finset.sum_nonneg fun q _ ↦ hw_nonneg p q)
          (Finset.mem_univ (σ i)))
    exact hdiv.trans_lt ((mul_le_mul_of_nonneg_right hterm_le hB'.diag_pos.le).trans_lt
      (mul_lt_mul_of_pos_right (by linarith [le_max_right C₀ Moff]) hB'.diag_pos))
  · exact (show B' (σ i) (σ i) ≤ 1 * B' (σ j) (σ j) by simpa using hmono hij.le).trans_lt
      (mul_lt_mul_of_pos_right (by linarith [le_max_left C₀ Moff, le_max_right C 1]) hB'.diag_pos)
  · rw [show (∏ i, (B'.submatrix σ σ) i i) = ∏ i, B' i i from Equiv.prod_comp σ fun i ↦ B' i i,
      det_submatrix_equiv_self σ B']
    exact hdet.trans_lt
      (mul_lt_mul_of_pos_right (by linarith [le_max_left C₀ Moff]) hB'.det_pos)

end Real

end Matrix
