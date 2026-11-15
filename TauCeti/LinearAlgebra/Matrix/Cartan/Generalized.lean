/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Generalized Cartan matrices

A *generalized Cartan matrix* on an index type `I` is an integral matrix `A = (Aᵢⱼ)` with diagonal
entries `2`, nonpositive off-diagonal entries, and symmetric zero pattern (`Aᵢⱼ = 0 ↔ Aⱼᵢ = 0`).
Unlike `Matrix.IsFiniteCartan`, no positive-definiteness or finiteness condition is imposed on `I`,
and unlike `TauCeti.SymmetrizableDatum`, no symmetrizer is required.

These three axioms are the exact hypotheses on `A` needed for Serre's relations in a Kac–Moody
presentation to preserve the triangular decomposition and keep the Cartan realization faithful.

## Main definitions

* `Matrix.IsGeneralizedCartan`: the predicate that an integral square matrix is a generalized
  Cartan matrix.

## Main results

* `Matrix.IsGeneralizedCartan.transpose`, `Matrix.IsGeneralizedCartan.submatrix`,
  `Matrix.IsGeneralizedCartan.reindex` and `Matrix.IsGeneralizedCartan.fromBlocks`: closure of
  generalized Cartan matrices under transposition, principal submatrices, reindexing and block
  direct sums.
* `Matrix.IsFiniteCartan.isGeneralizedCartan`: every finite-type Cartan matrix is a generalized
  Cartan matrix.
* `CartanMatrix.isGeneralizedCartan_A`, `CartanMatrix.isGeneralizedCartan_B`,
  `CartanMatrix.isGeneralizedCartan_C`, `CartanMatrix.isGeneralizedCartan_D`,
  `CartanMatrix.isGeneralizedCartan_E`, `CartanMatrix.isGeneralizedCartan_F₄` and
  `CartanMatrix.isGeneralizedCartan_G₂`: the classical and exceptional families (including `E n` in
  every rank) are generalized Cartan matrices.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press,
  1990, §1.1.
-/

public section

namespace Matrix

/-- The proposition that an integral square matrix `A` on an index type `I` is a *generalized
Cartan matrix*: diagonal entries equal to `2`, nonpositive off-diagonal entries, and symmetric
vanishing of entries. -/
structure IsGeneralizedCartan {I : Type*} (A : Matrix I I ℤ) : Prop where
  /-- Every diagonal entry is `2`. -/
  diag : ∀ i, A i i = 2
  /-- Every off-diagonal entry is nonpositive. -/
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  /-- An entry vanishes if and only if the transposed entry vanishes. -/
  zero_comm : ∀ i j, A i j = 0 ↔ A j i = 0

/-- Every matrix on an empty index type is a generalized Cartan matrix. -/
@[simp]
theorem isGeneralizedCartan_of_isEmpty {I : Type*} [IsEmpty I] (A : Matrix I I ℤ) :
    A.IsGeneralizedCartan where
  diag := isEmptyElim
  offDiag_nonpos := isEmptyElim
  zero_comm := isEmptyElim

namespace IsGeneralizedCartan

variable {I J : Type*} {A : Matrix I I ℤ}

/-- A symmetric integral matrix with diagonal `2` and nonpositive off-diagonal entries is a
generalized Cartan matrix. -/
theorem of_isSymm (hsymm : A.IsSymm) (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) : A.IsGeneralizedCartan where
  diag := hdiag
  offDiag_nonpos := hoff
  zero_comm i j := by rw [hsymm.apply i j]

/-- The truncated negated diagonal entry `(-A i i).toNat` vanishes. -/
theorem toNat_neg_self (hA : A.IsGeneralizedCartan) (i : I) : (-A i i).toNat = 0 := by
  rw [hA.diag]
  rfl

/-- For `i ≠ j`, the nonpositivity of `A i j` makes `((-A i j).toNat : ℤ) = -A i j`. -/
theorem natCast_toNat_neg_of_ne (hA : A.IsGeneralizedCartan) {i j : I} (hij : i ≠ j) :
    ((-A i j).toNat : ℤ) = -A i j :=
  Int.toNat_of_nonneg (neg_nonneg.mpr (hA.offDiag_nonpos i j hij))

/-- Nonvanishing of entries is symmetric. -/
theorem ne_zero_comm (hA : A.IsGeneralizedCartan) (i j : I) : A i j ≠ 0 ↔ A j i ≠ 0 :=
  (hA.zero_comm i j).not

/-- A nonzero off-diagonal entry is strictly negative. -/
theorem neg_of_ne_of_ne_zero (hA : A.IsGeneralizedCartan) {i j : I} (hij : i ≠ j)
    (h0 : A i j ≠ 0) : A i j < 0 :=
  lt_of_le_of_ne (hA.offDiag_nonpos i j hij) h0

/-- The transpose of a generalized Cartan matrix is a generalized Cartan matrix. -/
protected theorem transpose (hA : A.IsGeneralizedCartan) : Aᵀ.IsGeneralizedCartan where
  diag i := hA.diag i
  offDiag_nonpos i j hij := hA.offDiag_nonpos j i hij.symm
  zero_comm i j := hA.zero_comm j i

/-- Transposition preserves and reflects the generalized Cartan matrix property. -/
@[simp]
protected theorem transpose_iff : Aᵀ.IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h => h.transpose, IsGeneralizedCartan.transpose⟩

/-- Restricting a generalized Cartan matrix along an embedding produces a generalized Cartan
matrix. -/
theorem submatrix (hA : A.IsGeneralizedCartan) (f : J ↪ I) :
    (A.submatrix f f).IsGeneralizedCartan where
  diag i := hA.diag (f i)
  offDiag_nonpos i j hij := hA.offDiag_nonpos (f i) (f j) (f.injective.ne hij)
  zero_comm i j := hA.zero_comm (f i) (f j)

/-- Reindexing a generalized Cartan matrix along an equivalence produces a generalized Cartan
matrix. -/
theorem reindex (hA : A.IsGeneralizedCartan) (e : I ≃ J) :
    (A.reindex e e).IsGeneralizedCartan :=
  hA.submatrix e.symm.toEmbedding

/-- Reindexing along an equivalence via `Matrix.submatrix` preserves and reflects the generalized
Cartan matrix property. -/
@[simp]
theorem submatrix_equiv_iff (e : J ≃ I) :
    (A.submatrix e e).IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h => by simpa using h.submatrix e.symm.toEmbedding, fun h => h.submatrix e.toEmbedding⟩

/-- Reindexing along an equivalence preserves and reflects the generalized Cartan matrix
property. -/
theorem reindex_iff (e : I ≃ J) :
    (A.reindex e e).IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  submatrix_equiv_iff e.symm

/-- The block-diagonal direct sum of two generalized Cartan matrices is a generalized Cartan
matrix. -/
theorem fromBlocks {B : Matrix J J ℤ} (hA : A.IsGeneralizedCartan)
    (hB : B.IsGeneralizedCartan) : (Matrix.fromBlocks A 0 0 B).IsGeneralizedCartan where
  diag := by rintro (i | j) <;> simp [hA.diag, hB.diag]
  offDiag_nonpos := by
    rintro (i | i) (j | j) hij
    · exact hA.offDiag_nonpos i j fun h => hij (congrArg Sum.inl h)
    · simp
    · simp
    · exact hB.offDiag_nonpos i j fun h => hij (congrArg Sum.inr h)
  zero_comm := by rintro (i | i) (j | j) <;> simp [hA.zero_comm, hB.zero_comm]

end IsGeneralizedCartan

/-- Every finite-type Cartan matrix is a generalized Cartan matrix. -/
theorem IsFiniteCartan.isGeneralizedCartan {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℤ} (hM : M.IsFiniteCartan) : M.IsGeneralizedCartan where
  diag := hM.diag
  offDiag_nonpos := hM.offDiag_nonpos
  zero_comm := hM.zero_comm

end Matrix

namespace CartanMatrix

/-- The Cartan matrix of type `A` is a generalized Cartan matrix in every rank. -/
@[simp]
theorem isGeneralizedCartan_A (n : ℕ) : (A n).IsGeneralizedCartan :=
  .of_isSymm (A_isSymm n) (fun i => congr_fun (A_diag n) i) (A_apply_le_zero_of_ne n)

/-- The Cartan matrix of type `B` is a generalized Cartan matrix in every rank. -/
@[simp]
theorem isGeneralizedCartan_B (n : ℕ) : (B n).IsGeneralizedCartan where
  diag := B_diag n
  offDiag_nonpos := B_off_diag_nonpos n
  zero_comm i j := by
    simp only [B, Matrix.of_apply]
    split_ifs <;> lia

/-- The Cartan matrix of type `C` is a generalized Cartan matrix in every rank. -/
@[simp]
theorem isGeneralizedCartan_C (n : ℕ) : (C n).IsGeneralizedCartan := by
  rw [← B_transpose]
  exact (isGeneralizedCartan_B n).transpose

/-- The Cartan matrix of type `D` is a generalized Cartan matrix in every rank. -/
@[simp]
theorem isGeneralizedCartan_D (n : ℕ) : (D n).IsGeneralizedCartan :=
  .of_isSymm (D_isSymm n) (D_diag n) (D_off_diag_nonpos n)

/-- The generalized Cartan matrix `E n` is a generalized Cartan matrix in every rank `n`
(finite for `n ≤ 8`, affine for `n = 9`, and indefinite for `n ≥ 10`). -/
@[simp]
theorem isGeneralizedCartan_E (n : ℕ) : (E n).IsGeneralizedCartan :=
  .of_isSymm (E_isSymm n) (E_diag n) (E_off_diag_nonpos n)

/-- The Cartan matrix of type `F₄` is a generalized Cartan matrix. -/
@[simp]
theorem isGeneralizedCartan_F₄ : F₄.IsGeneralizedCartan where
  diag := F₄_diag
  offDiag_nonpos := F₄_off_diag_nonpos
  zero_comm i j := by fin_cases i <;> fin_cases j <;> decide

/-- The Cartan matrix of type `G₂` is a generalized Cartan matrix. -/
@[simp]
theorem isGeneralizedCartan_G₂ : G₂.IsGeneralizedCartan where
  diag := G₂_diag
  offDiag_nonpos := G₂_off_diag_nonpos
  zero_comm i j := by fin_cases i <;> fin_cases j <;> decide

end CartanMatrix

/-! ### Examples -/

/-- The affine Cartan matrix `A₁⁽¹⁾` is a singular generalized Cartan matrix. -/
example : (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsGeneralizedCartan :=
  { diag := by decide
    offDiag_nonpos := by simp [Fin.forall_fin_two]
    zero_comm := by simp [Fin.forall_fin_two] }

/-- The matrix `[[2, -1, -2], [-1, 2, -1], [-1, -1, 2]]` is a non-symmetrizable generalized
Cartan matrix: any positive symmetrizer `(d₀, d₁, d₂)` would satisfy `d₀ = d₁ = d₂` and
`2 d₀ = d₂`, which is impossible. -/
example :
    let M : Matrix (Fin 3) (Fin 3) ℤ := !![2, -1, -2; -1, 2, -1; -1, -1, 2]
    M.IsGeneralizedCartan ∧
      ¬ ∃ d : Fin 3 → ℕ, (∀ i, 0 < d i) ∧ ∀ i j, (d i : ℤ) * M i j = d j * M j i := by
  refine ⟨{ diag := by decide
            offDiag_nonpos := fun i j => by fin_cases i <;> fin_cases j <;> decide
            zero_comm := fun i j => by fin_cases i <;> fin_cases j <;> decide }, ?_⟩
  rintro ⟨d, hd, hsymm⟩
  have h01 : (d 0 : ℤ) * (-1) = d 1 * (-1) := hsymm 0 1
  have h12 : (d 1 : ℤ) * (-1) = d 2 * (-1) := hsymm 1 2
  have h02 : (d 0 : ℤ) * (-2) = d 2 * (-1) := hsymm 0 2
  have hd0 : (0 : ℤ) < d 0 := Nat.cast_pos.mpr (hd 0)
  lia

/-- The matrix `[[2, -1], [0, 2]]` violates `zero_comm`, so it is not a generalized Cartan
matrix. -/
example : ¬ (!![2, -1; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsGeneralizedCartan := fun h =>
  absurd ((h.zero_comm 1 0).mp rfl) (by decide)
