/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SiegelReduction.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Round
import TauCeti.Algebra.Module.Primitive
import TauCeti.LinearAlgebra.Matrix.CornerBlockSucc
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
import TauCeti.LinearAlgebra.Matrix.PosDef.Northcott

/-!
# Hermite–Siegel reduction for positive-definite forms and `GL_n(ℝ)`

Every positive-definite real `n × n` matrix `B` is congruent under `GL_n(ℤ)` to a `C`-Siegel reduced
matrix, with a constant `C > 1` depending only on the rank `n`
(`Matrix.PosDef.exists_glZ_isSiegelReduced`). The proof inducts on `n` by combining three steps on
`Fin (m + 1)`:

1. By Northcott's property on the integer lattice, the quadratic form of `B` attains its nonzero
   integer minimum at a primitive vector `v`, which extends to an integral basis giving `γ₁ ∈ GL(ℤ)`
   carrying the first coordinate vector to `v`.
2. Eliminating the first row and column expresses `B₁ = γ₁ᵀ B γ₁` via an upper-unitriangular real
   congruence as `diag(B₁ 0 0, S)` where the Schur complement `S` on `Fin m` is positive definite of
   determinant `B₁.det / B₁ 0 0`, and the induction hypothesis reduces `S` by `γ₂ = diag(1, γ')`.
3. Rounding the superdiagonal entries of the top row modulo `B₂ 0 0` via an integer
   upper-unitriangular transvection `γ₃` achieves `|B₃ 0 j| ≤ B₃ 0 0 / 2` while preserving the
   minimal corner `B₃ 0 0` and the reduced Schur complement `S'`, from which all three
   `Matrix.IsSiegelReduced` bounds follow.

Combining quadratic-form reduction with the Iwasawa–Cholesky equivalence from
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SiegelReduction.Basic` yields Siegel's reduction
theorem `GL_n(ℝ) = GL_n(ℤ) · 𝔖_{u, t}` (`TauCeti.exists_glZ_mul_mem_siegelDomain`) and its
`SL_n`-refinement `SL_n(ℝ) = SL_n(ℤ) · (𝔖_{u, t} ∩ SL_n(ℝ))`
(`TauCeti.exists_slZ_mul_mem_siegelDomain`).

## Main statements

* `Matrix.PosDef.exists_glZ_isSiegelReduced`: existence of `C > 1` depending only on `n` such that
  every positive-definite `n × n` real matrix is `GL_n(ℤ)`-congruent to a `C`-Siegel reduced matrix.
* `TauCeti.exists_glZ_mul_mem_siegelDomain`: existence of `u > 0` and `t > 0` depending only on `n`
  such that `GL_n(ℝ) = GL_n(ℤ) · siegelDomain n u t`.
* `TauCeti.exists_slZ_mul_mem_siegelDomain`: existence of `u > 0` and `t > 0` depending only on `n`
  such that `SL_n(ℝ) = SL_n(ℤ) · (siegelDomain n u t ∩ SL_n(ℝ))`.

## References

* A. Borel, *Introduction aux groupes arithmétiques*, Hermann, 1969, Theorem 1.4 and Theorem 1.6.
* V. Platonov, A. Rapinchuk, I. Rapinchuk, *Algebraic Groups and Number Theory*, 2nd ed., Vol. 1,
  Cambridge University Press, 2023, Theorem 4.12, pp. 206–208.
-/

open Matrix
open scoped MatrixGroups

namespace TauCeti.SiegelReductionAux

/-- Extend a primitive integer vector `v` on `Fin (m + 1)` to an element of `GL (Fin (m + 1)) ℤ`
whose zeroth column is `v`. -/
theorem exists_glZ_mulVec_single_zero_eq {m : ℕ} {v : Fin (m + 1) → ℤ}
    (hv : TauCeti.IsPrimitive v) :
    ∃ γ : GL (Fin (m + 1)) ℤ,
      (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) *ᵥ Pi.single 0 1 = v := by
  let b₀ := Pi.basisFun ℤ (Fin (m + 1))
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hv
  obtain ⟨e, -, he0⟩ := (b₀.exists_basis_eq_iff 0 v).mpr
    ⟨f, fun j hj ↦ absurd hj (Fin.not_lt_zero j), hf⟩
  let φ := b₀.equiv e (Equiv.refl (Fin (m + 1)))
  refine ⟨b₀.toGL φ, ?_⟩
  rw [Module.Basis.coe_toGL, Matrix.mulVec_single_one]
  ext i
  rw [Matrix.col_apply, LinearMap.toMatrix_apply]
  have hφ0 : (φ : (Fin (m + 1) → ℤ) →ₗ[ℤ] Fin (m + 1) → ℤ) (b₀ 0) = v := by
    simp [φ, he0]
  rw [hφ0]
  simp [b₀]

/-- Cast an integer matrix action `(γ *ᵥ z)` to `ℝ`. -/
theorem cast_mulVec_glZ {n : ℕ} (γ : GL (Fin n) ℤ) (z : Fin n → ℤ) :
    ((γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *ᵥ
        (fun i ↦ (z i : ℝ)) =
      fun i ↦ (((γ : Matrix (Fin n) (Fin n) ℤ) *ᵥ z) i : ℝ) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- Congruence of `B` by `γ ∈ GL(ℤ)` preserves `PosDef` and evaluates at `z` as `B` at `γ *ᵥ z`. -/
theorem posDef_and_dotProduct_congr_glZ {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef)
    (γ : GL (Fin n) ℤ) :
    let G : Matrix (Fin n) (Fin n) ℝ := (γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ)
    (Gᵀ * B * G).PosDef ∧ ∀ z : Fin n → ℤ,
      (fun i ↦ (z i : ℝ)) ⬝ᵥ (Gᵀ * B * G) *ᵥ (fun i ↦ (z i : ℝ)) =
        (fun i ↦ (((γ : Matrix (Fin n) (Fin n) ℤ) *ᵥ z) i : ℝ)) ⬝ᵥ B *ᵥ
          (fun i ↦ (((γ : Matrix (Fin n) (Fin n) ℤ) *ᵥ z) i : ℝ)) := by
  intro G
  have hinj : Function.Injective G.mulVec :=
    Matrix.mulVec_injective_of_isUnit (γ.map (Int.castRingHom ℝ)).isUnit
  refine ⟨by simpa using hB.conjTranspose_mul_mul_same hinj, fun z ↦ ?_⟩
  have hcast := cast_mulVec_glZ γ z
  calc (fun i ↦ (z i : ℝ)) ⬝ᵥ (Gᵀ * B * G) *ᵥ (fun i ↦ (z i : ℝ))
      = (G *ᵥ fun i ↦ (z i : ℝ)) ⬝ᵥ B *ᵥ (G *ᵥ fun i ↦ (z i : ℝ)) := by
        rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.vecMul_transpose, ← Matrix.mulVec_mulVec]
    _ = _ := by rw [hcast]

/-- Step 1 of the inductive step: replace `B` by a `GL(ℤ)`-congruent matrix whose `(0, 0)` entry
is minimal among all nonzero integer vectors. -/
theorem exists_glZ_corner_minimal {m : ℕ} {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hB : B.PosDef) :
    ∃ γ₁ : GL (Fin (m + 1)) ℤ,
      let G₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
        (γ₁.map (Int.castRingHom ℝ) : GL (Fin (m + 1)) ℝ)
      let B₁ := G₁ᵀ * B * G₁
      B₁.PosDef ∧ ∀ z : Fin (m + 1) → ℤ, z ≠ 0 →
        B₁ 0 0 ≤ (fun i ↦ (z i : ℝ)) ⬝ᵥ B₁ *ᵥ (fun i ↦ (z i : ℝ)) := by
  obtain ⟨v, hv, hmin⟩ := hB.exists_isPrimitive_forall_dotProduct_mulVec_le
  obtain ⟨γ₁, hγ₁v⟩ := exists_glZ_mulVec_single_zero_eq hv
  obtain ⟨hB₁, hquad⟩ := posDef_and_dotProduct_congr_glZ hB γ₁
  refine ⟨γ₁, hB₁, fun z hz ↦ ?_⟩
  set G₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    ((γ₁.map (Int.castRingHom ℝ) : GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  set B₁ := G₁ᵀ * B * G₁
  have hsingle_cast :
      (fun k : Fin (m + 1) ↦ (((Pi.single 0 1 : Fin (m + 1) → ℤ) k) : ℝ)) = Pi.single 0 1 := by
    ext k; by_cases hk : k = 0 <;> simp [hk]
  have hB₁_zero : B₁ 0 0 = (fun i ↦ (v i : ℝ)) ⬝ᵥ B *ᵥ (fun i ↦ (v i : ℝ)) := by
    have hsingle := hquad (Pi.single 0 1)
    rw [hsingle_cast, hγ₁v] at hsingle
    simpa [B₁, G₁, Matrix.mulVec_single_one] using hsingle
  have hγz : (γ₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) *ᵥ z ≠ 0 := fun h0 ↦
    hz (Matrix.mulVec_injective_of_isUnit γ₁.isUnit (h0.trans (Matrix.mulVec_zero _).symm))
  rw [hB₁_zero, hquad z]
  exact hmin _ hγz

/-- Block-diagonal lift `diag(1, γ)` from `GL (Fin m) R` to `GL (Fin (m + 1)) R`. -/
def cornerBlockSuccGL {m : ℕ} {R : Type*} [CommRing R] (γ : GL (Fin m) R) :
    GL (Fin (m + 1)) R where
  val := Matrix.cornerBlockSucc 1 (γ : Matrix (Fin m) (Fin m) R)
  inv := Matrix.cornerBlockSucc 1 ((γ⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)
  val_inv := by simp [Matrix.cornerBlockSucc_mul_cornerBlockSucc]
  inv_val := by simp [Matrix.cornerBlockSucc_mul_cornerBlockSucc]

/-- Schur complement of the `(0, 0)` entry of an `(m + 1) × (m + 1)` real matrix. -/
noncomputable def schurComplement {m : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j ↦ B i.succ j.succ - B 0 i.succ * B 0 j.succ / B 0 0

/-- Real upper-unitriangular matrix eliminating the top row and left column of `B`. -/
noncomputable def schurElim {m : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of (Fin.cons (Fin.cons 1 fun j ↦ -(B 0 j.succ / B 0 0))
    fun i ↦ Fin.cons 0 ((1 : Matrix (Fin m) (Fin m) ℝ) i))

theorem isUpperUnitriangular_schurElim {m : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    (schurElim B).IsUpperUnitriangular := by
  refine (Matrix.isUpperUnitriangular_def _).mpr ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · refine Fin.cases (fun h0 ↦ absurd h0 (Fin.not_lt_zero j)) (fun i' hi' ↦ ?_) i hij
    refine Fin.cases (fun _ ↦ rfl) (fun j' hj' ↦ ?_) j hi'
    exact Matrix.one_apply_ne (Fin.succ_lt_succ_iff.mp hj').ne'
  · exact Fin.cases rfl (fun i' ↦ Matrix.one_apply_eq i') i

/-- Block-diagonalization `Uᵀ B U = diag(B 0 0, schurComplement B)` for symmetric `B` with
`B 0 0 ≠ 0`. -/
theorem transpose_schurElim_mul_mul {m : ℕ} {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hB : B.IsSymm) (ha : B 0 0 ≠ 0) :
    (schurElim B)ᵀ * B * schurElim B =
      Matrix.cornerBlockSucc (B 0 0) (schurComplement B) := by
  have hBU : B * schurElim B = Matrix.of (Fin.cons (Fin.cons (B 0 0) 0)
      fun i ↦ Fin.cons (B i.succ 0) (schurComplement B i)) := by
    refine Matrix.ext_fin_succ ?_ (fun j ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_)
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, schurElim]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, schurElim, Matrix.one_apply, mul_div_cancel₀ _ ha]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, schurElim]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, schurElim, schurComplement, Matrix.one_apply,
        hB.apply i.succ 0]
      ring
  rw [Matrix.mul_assoc, hBU]
  refine Matrix.ext_fin_succ ?_ (fun j ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_)
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]; simp [Matrix.transpose_apply, schurElim]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]; simp [Matrix.transpose_apply, schurElim]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [Matrix.transpose_apply, schurElim, Matrix.one_apply, hB.apply 0 i.succ,
      div_mul_cancel₀ _ ha]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [Matrix.transpose_apply, schurElim, Matrix.one_apply]

/-- For positive-definite `B`, its Schur complement is positive definite and
`B.det = B 0 0 * (schurComplement B).det`. -/
theorem posDef_and_det_schurComplement {m : ℕ} {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hB : B.PosDef) :
    (schurComplement B).PosDef ∧ B.det = B 0 0 * (schurComplement B).det := by
  have ha : B 0 0 ≠ 0 := hB.diag_pos.ne'
  have hsymm : B.IsSymm := Matrix.isHermitian_iff_isSymm.mp hB.isHermitian
  have hU := isUpperUnitriangular_schurElim B
  have hdiag := transpose_schurElim_mul_mul hsymm ha
  have hblk_posDef : (Matrix.cornerBlockSucc (B 0 0) (schurComplement B)).PosDef := by
    rw [← hdiag]
    have hinj : Function.Injective (schurElim B).mulVec := by
      rw [← hU.coe_toGL]
      exact Matrix.mulVec_injective_of_isUnit hU.toGL.isUnit
    simpa using hB.conjTranspose_mul_mul_same hinj
  have hsub : (Matrix.cornerBlockSucc (B 0 0) (schurComplement B)).submatrix Fin.succ Fin.succ =
      schurComplement B := by ext; simp
  have hS_posDef : (schurComplement B).PosDef := by
    rw [← hsub]
    exact hblk_posDef.submatrix (Fin.succ_injective m)
  have hdetU : (schurElim B).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hU.isUpperTriangular]
    exact Finset.prod_eq_one fun i _ ↦ hU.apply_diag i
  have hdet_blk : (Matrix.cornerBlockSucc (B 0 0) (schurComplement B)).det =
      B 0 0 * (schurComplement B).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [hsub]
  refine ⟨hS_posDef, ?_⟩
  calc B.det = ((schurElim B)ᵀ * B * schurElim B).det := by
        simp [Matrix.det_mul, Matrix.det_transpose, hdetU]
    _ = B 0 0 * (schurComplement B).det := by rw [hdiag, hdet_blk]

/-- Covariance of `schurComplement` under a block-diagonal congruence `diag(1, M)`. -/
theorem schurComplement_cornerBlockSucc_congr {m : ℕ} (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (M : Matrix (Fin m) (Fin m) ℝ) :
    let G := Matrix.cornerBlockSucc 1 M
    schurComplement (Gᵀ * B * G) = Mᵀ * schurComplement B * M := by
  intro G
  have h00 : (Gᵀ * B * G) 0 0 = B 0 0 := by
    simp [G, Matrix.mul_apply, Fin.sum_univ_succ]
  have h0s (j : Fin m) : (Gᵀ * B * G) 0 j.succ = ∑ k : Fin m, B 0 k.succ * M k j := by
    simp [G, Matrix.mul_apply, Fin.sum_univ_succ]
  have hss (i j : Fin m) :
      (Gᵀ * B * G) i.succ j.succ = ∑ l : Fin m, ∑ k : Fin m, M k i * B k.succ l.succ * M l j := by
    simp [G, Matrix.mul_apply, Fin.sum_univ_succ, Finset.sum_mul]
  have hrhs (i j : Fin m) :
      (Mᵀ * schurComplement B * M) i j =
        ∑ l : Fin m, ∑ k : Fin m, M k i * schurComplement B k l * M l j := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  ext i j
  rw [hrhs]
  simp only [schurComplement, Matrix.of_apply, h00, h0s, hss]
  have hprod : (∑ k : Fin m, B 0 k.succ * M k i) * (∑ l : Fin m, B 0 l.succ * M l j) / B 0 0 =
      ∑ l : Fin m, ∑ k : Fin m, (B 0 k.succ * M k i) * (B 0 l.succ * M l j) / B 0 0 := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Finset.sum_mul, Finset.sum_div]
  rw [hprod, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

/-- Integer upper-unitriangular matrix subtracting `q j` times column `0` from column `j.succ`. -/
def roundElimZ {m : ℕ} (q : Fin m → ℤ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  Matrix.of (Fin.cons (Fin.cons 1 fun j ↦ -q j)
    fun i ↦ Fin.cons 0 ((1 : Matrix (Fin m) (Fin m) ℤ) i))

theorem isUpperUnitriangular_roundElimZ {m : ℕ} (q : Fin m → ℤ) :
    (roundElimZ q).IsUpperUnitriangular := by
  refine (Matrix.isUpperUnitriangular_def _).mpr ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · refine Fin.cases (fun h0 ↦ absurd h0 (Fin.not_lt_zero j)) (fun i' hi' ↦ ?_) i hij
    refine Fin.cases (fun _ ↦ rfl) (fun j' hj' ↦ ?_) j hi'
    exact Matrix.one_apply_ne (Fin.succ_lt_succ_iff.mp hj').ne'
  · exact Fin.cases rfl (fun i' ↦ Matrix.one_apply_eq i') i

/-- Rounding transvection preserves `B 0 0` and `schurComplement B`, fixes `e₀`, and reduces the
top-row off-diagonal entries to `|B' 0 j.succ| ≤ B' 0 0 / 2`. -/
theorem roundElimZ_properties {m : ℕ} {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hB : B.IsSymm) (ha : 0 < B 0 0) :
    let q : Fin m → ℤ := fun j ↦ round (B 0 j.succ / B 0 0)
    let γ₃ : GL (Fin (m + 1)) ℤ := (isUpperUnitriangular_roundElimZ q).toGL
    let G₃ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
      (γ₃.map (Int.castRingHom ℝ) : GL (Fin (m + 1)) ℝ)
    let B' := G₃ᵀ * B * G₃
    (γ₃ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      B' 0 0 = B 0 0 ∧
      schurComplement B' = schurComplement B ∧
      ∀ j : Fin m, |B' 0 j.succ| ≤ B' 0 0 / 2 := by
  intro q γ₃ G₃ B'
  have hG₃ : G₃ = (roundElimZ q).map (Int.castRingHom ℝ) := by
    ext i j
    simp [G₃, γ₃]
  have hfix : (γ₃ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [Matrix.IsUpperUnitriangular.coe_toGL]
    refine Fin.cases ?_ (fun i ↦ ?_) |> fun h ↦ funext h
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, roundElimZ]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, roundElimZ]
  have h00 : B' 0 0 = B 0 0 := by
    simp [B', hG₃, Matrix.mul_apply, Fin.sum_univ_succ, roundElimZ]
  have h0s (j : Fin m) : B' 0 j.succ = B 0 j.succ - (q j : ℝ) * B 0 0 := by
    simp [B', hG₃, Matrix.mul_apply, Fin.sum_univ_succ, roundElimZ, Matrix.one_apply]
    ring
  have hss (i j : Fin m) : B' i.succ j.succ =
      B i.succ j.succ - (q i : ℝ) * B 0 j.succ - (q j : ℝ) * B 0 i.succ +
        (q i : ℝ) * (q j : ℝ) * B 0 0 := by
    simp [B', hG₃, Matrix.mul_apply, Fin.sum_univ_succ, roundElimZ, Matrix.one_apply,
      hB.apply _ 0]
    ring
  refine ⟨hfix, h00, ?_, fun j ↦ ?_⟩
  · ext i j
    have ha0 : B 0 0 ≠ 0 := ha.ne'
    simp only [schurComplement, Matrix.of_apply, h00, h0s, hss]
    field_simp
    ring
  · have hrew : B' 0 j.succ = B 0 0 * (B 0 j.succ / B 0 0 - (q j : ℝ)) := by
      rw [h0s j]
      field_simp [ha.ne']
    rw [hrew, h00, abs_mul, abs_of_pos ha]
    have hrnd : |B 0 j.succ / B 0 0 - (q j : ℝ)| ≤ 1 / 2 := abs_sub_round _
    linarith [mul_le_mul_of_nonneg_left hrnd ha.le]

/-- Diagonal bounds comparing `B i.succ i.succ` and `(schurComplement B) i i` when `B 0 0` is
minimal among diagonal entries and `|B 0 i.succ| ≤ B 0 0 / 2`. -/
theorem schur_diag_bounds {m : ℕ} {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (ha : 0 < B 0 0) (hmin : ∀ i : Fin m, B 0 0 ≤ B i.succ i.succ)
    (htop : ∀ i : Fin m, |B 0 i.succ| ≤ B 0 0 / 2) (i : Fin m) :
    schurComplement B i i ≤ B i.succ i.succ ∧
      B i.succ i.succ ≤ (4 / 3 : ℝ) * schurComplement B i i := by
  have hsq : (B 0 i.succ) ^ 2 ≤ (B 0 0 / 2) ^ 2 := by
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (htop i) 2
  have hdiv_nonneg : 0 ≤ B 0 i.succ * B 0 i.succ / B 0 0 :=
    div_nonneg (mul_self_nonneg _) ha.le
  have hdiv_le : B 0 i.succ * B 0 i.succ / B 0 0 ≤ B 0 0 / 4 := by
    rw [div_le_iff₀ ha]
    nlinarith [hsq]
  have hS : schurComplement B i i = B i.succ i.succ - B 0 i.succ * B 0 i.succ / B 0 0 := rfl
  constructor
  · linarith
  · linarith [hmin i]

/-- Off-diagonal entry bound `|B p r| < max (2 * C) ... * B p p` from Schur-complement reduction. -/
theorem abs_apply_lt_of_schurComplement {m : ℕ} {C C' : ℝ} (h1C : 1 < C) (h2C : 2 * C ≤ C')
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hB : B.PosDef)
    (hmin : ∀ i : Fin m, B 0 0 ≤ B i.succ i.succ)
    (htop : ∀ j : Fin m, |B 0 j.succ| ≤ B 0 0 / 2)
    (hS : (schurComplement B).IsSiegelReduced C) (p r : Fin (m + 1)) :
    |B p r| < C' * B p p := by
  have hsymm : B.IsSymm := Matrix.isHermitian_iff_isSymm.mp hB.isHermitian
  have ha : 0 < B 0 0 := hB.diag_pos
  refine Fin.cases ?_ (fun i ↦ ?_) p
  · refine Fin.cases ?_ (fun j ↦ ?_) r
    · rw [abs_of_pos ha]; nlinarith
    · exact (htop j).trans_lt (by nlinarith)
  · refine Fin.cases ?_ (fun j ↦ ?_) r
    · rw [hsymm.apply 0 i.succ]
      exact (htop i).trans_lt (by nlinarith [hmin i])
    · obtain ⟨hS_le, _⟩ := schur_diag_bounds ha hmin htop i
      have hcross : |B 0 i.succ * B 0 j.succ / B 0 0| ≤ B i.succ i.succ / 4 := by
        rw [abs_div, abs_mul, abs_of_pos ha, div_le_iff₀ ha]
        have hmul := mul_le_mul (htop i) (htop j) (abs_nonneg _) (by linarith)
        nlinarith [hmin i]
      have hdecomp : B i.succ j.succ =
          schurComplement B i j + B 0 i.succ * B 0 j.succ / B 0 0 := by
        simp [schurComplement]
      calc |B i.succ j.succ|
          ≤ |schurComplement B i j| + |B 0 i.succ * B 0 j.succ / B 0 0| := by
            rw [hdecomp]; exact abs_add_le _ _
        _ < C * schurComplement B i i + B i.succ i.succ / 4 :=
            add_lt_add_of_lt_of_le (hS.abs_apply_lt i j) hcross
        _ ≤ C' * B i.succ i.succ := by nlinarith [hB.diag_pos (i := i.succ)]

/-- Deductive assembly of `IsSiegelReduced` on `Fin (m + 1)` from corner minimality, top-row
rounding, and `C`-Siegel reduction of the Schur complement. -/
theorem isSiegelReduced_of_schurComplement {m : ℕ} {C : ℝ} (h1C : 1 < C)
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hB : B.PosDef)
    (hmin : ∀ i : Fin m, B 0 0 ≤ B i.succ i.succ)
    (htop : ∀ j : Fin m, |B 0 j.succ| ≤ B 0 0 / 2)
    (hS : (schurComplement B).IsSiegelReduced C) :
    B.IsSiegelReduced (max (2 * C) ((4 / 3 : ℝ) ^ m * C + 1)) := by
  set C' : ℝ := max (2 * C) ((4 / 3 : ℝ) ^ m * C + 1)
  have h2C : 2 * C ≤ C' := le_max_left _ _
  have ha : 0 < B 0 0 := hB.diag_pos
  obtain ⟨hS_posDef, hdet⟩ := posDef_and_det_schurComplement hB
  rw [Matrix.isSiegelReduced_def]
  refine ⟨abs_apply_lt_of_schurComplement h1C h2C hB hmin htop hS, fun p r hpr ↦ ?_, ?_⟩
  · refine Fin.cases (fun h0 ↦ ?_) (fun i hi ↦ ?_) p hpr
    · refine Fin.cases (fun h00 ↦ absurd h00 (Fin.not_lt_zero 0)) (fun j _ ↦ ?_) r h0
      nlinarith [hmin j, hB.diag_pos (i := j.succ)]
    · refine Fin.cases (fun h0 ↦ absurd h0 (Fin.not_lt_zero i.succ)) (fun j hj ↦ ?_) r hi
      obtain ⟨-, hB_le⟩ := schur_diag_bounds ha hmin htop i
      obtain ⟨hS_le, -⟩ := schur_diag_bounds ha hmin htop j
      have hij := hS.diag_lt_of_lt (Fin.succ_lt_succ_iff.mp hj)
      nlinarith [hS_posDef.diag_pos (i := j), hB.diag_pos (i := j.succ)]
  · have hprod_le : (∏ i : Fin m, B i.succ i.succ) ≤
        (4 / 3 : ℝ) ^ m * ∏ i : Fin m, schurComplement B i i := by
      calc (∏ i : Fin m, B i.succ i.succ)
          ≤ ∏ i : Fin m, ((4 / 3 : ℝ) * schurComplement B i i) :=
            Finset.prod_le_prod₀ (fun i _ ↦ (hB.diag_pos (i := Fin.succ i)).le)
              fun i _ ↦ (schur_diag_bounds ha hmin htop i).2
        _ = (4 / 3 : ℝ) ^ m * ∏ i : Fin m, schurComplement B i i := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
    have hpow_pos : 0 < (4 / 3 : ℝ) ^ m := by positivity
    have hC'_gt : (4 / 3 : ℝ) ^ m * C < C' := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
    rw [Fin.prod_univ_succ, hdet]
    calc B 0 0 * ∏ i : Fin m, B i.succ i.succ
        ≤ B 0 0 * ((4 / 3 : ℝ) ^ m * ∏ i : Fin m, schurComplement B i i) :=
          mul_le_mul_of_nonneg_left hprod_le ha.le
      _ < B 0 0 * ((4 / 3 : ℝ) ^ m * (C * (schurComplement B).det)) :=
          mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hS.prod_diag_lt hpow_pos) ha
      _ = ((4 / 3 : ℝ) ^ m * C) * (B 0 0 * (schurComplement B).det) := by ring
      _ < C' * (B 0 0 * (schurComplement B).det) :=
          mul_lt_mul_of_pos_right hC'_gt (mul_pos ha hS_posDef.det_pos)

/-- If `B₁` is positive definite on `Fin (m + 1)` with `(0, 0)` entry minimal on all nonzero
integer vectors, then any `GL(ℤ)`-congruent matrix `B₃ = (γ.map _)ᵀ * B₁ * (γ.map _)` has every
diagonal entry at least `B₁ 0 0`. -/
theorem corner_le_diag_congr_glZ {m : ℕ} {B₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hB₁ : B₁.PosDef)
    (hmin₁ : ∀ z : Fin (m + 1) → ℤ, z ≠ 0 →
      B₁ 0 0 ≤ (fun k ↦ (z k : ℝ)) ⬝ᵥ B₁ *ᵥ (fun k ↦ (z k : ℝ)))
    (γ : GL (Fin (m + 1)) ℤ) (r : Fin (m + 1)) :
    let G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
      (γ.map (Int.castRingHom ℝ) : GL (Fin (m + 1)) ℝ)
    B₁ 0 0 ≤ (Gᵀ * B₁ * G) r r := by
  intro G
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := γ
  have h1 : (Pi.single r 1 : Fin (m + 1) → ℤ) ≠ 0 := fun h ↦ by
    simpa using congrFun h r
  have hne : M *ᵥ Pi.single r 1 ≠ 0 := fun h0 ↦
    h1 (Matrix.mulVec_injective_of_isUnit γ.isUnit (h0.trans (Matrix.mulVec_zero _).symm))
  have hsingle_cast :
      (fun k : Fin (m + 1) ↦ (((Pi.single r 1 : Fin (m + 1) → ℤ) k) : ℝ)) = Pi.single r 1 := by
    ext k; by_cases hk : k = r <;> simp [hk]
  have hdiag := (posDef_and_dotProduct_congr_glZ hB₁ γ).2 (Pi.single r 1)
  rw [hsingle_cast] at hdiag
  have hentry : (Gᵀ * B₁ * G) r r =
      (fun k ↦ ((M *ᵥ Pi.single r 1) k : ℝ)) ⬝ᵥ B₁ *ᵥ
        (fun k ↦ ((M *ᵥ Pi.single r 1) k : ℝ)) := by
    simpa [G, M, Matrix.mulVec_single_one] using hdiag
  rw [hentry]
  exact hmin₁ _ hne

/-- Inductive step for `Matrix.PosDef.exists_glZ_isSiegelReduced`: given a reduction constant `C`
on `Fin m`, construct one on `Fin (m + 1)`. -/
theorem exists_glZ_isSiegelReduced_succ {m : ℕ} {C : ℝ} (h1C : 1 < C)
    (ih : ∀ S : Matrix (Fin m) (Fin m) ℝ, S.PosDef → ∃ γ : GL (Fin m) ℤ,
      (((γ.map (Int.castRingHom ℝ) : GL (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ)ᵀ * S *
        ((γ.map (Int.castRingHom ℝ) : GL (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ)).IsSiegelReduced
        C)
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hB : B.PosDef) :
    ∃ γ : GL (Fin (m + 1)) ℤ,
      (((γ.map (Int.castRingHom ℝ) : GL (Fin (m + 1)) ℝ) : Matrix _ _ ℝ)ᵀ * B *
        ((γ.map (Int.castRingHom ℝ) : GL (Fin (m + 1)) ℝ) : Matrix _ _ ℝ)).IsSiegelReduced
        (max (2 * C) ((4 / 3 : ℝ) ^ m * C + 1)) := by
  obtain ⟨γ₁, hB₁, hmin₁⟩ := exists_glZ_corner_minimal hB
  set G₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    ((γ₁.map (Int.castRingHom ℝ) : GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  set B₁ := G₁ᵀ * B * G₁
  obtain ⟨γ', hS'⟩ := ih (schurComplement B₁) (posDef_and_det_schurComplement hB₁).1
  let γ₂ := cornerBlockSuccGL γ'
  set G₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    ((γ₂.map (Int.castRingHom ℝ) : GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  set B₂ := G₂ᵀ * B₁ * G₂
  have hG₂_eq : G₂ = Matrix.cornerBlockSucc 1
      ((γ'.map (Int.castRingHom ℝ) : GL (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ) := by
    refine Matrix.ext_fin_succ ?_ (fun j ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_) <;>
      simp [G₂, γ₂, cornerBlockSuccGL]
  have hB₂_posDef : B₂.PosDef := (posDef_and_dotProduct_congr_glZ hB₁ γ₂).1
  have hB₂_symm : B₂.IsSymm := Matrix.isHermitian_iff_isSymm.mp hB₂_posDef.isHermitian
  obtain ⟨-, h00₃, hS₃, htop₃⟩ := roundElimZ_properties hB₂_symm hB₂_posDef.diag_pos
  let q : Fin m → ℤ := fun j ↦ round (B₂ 0 j.succ / B₂ 0 0)
  let γ₃ : GL (Fin (m + 1)) ℤ := (isUpperUnitriangular_roundElimZ q).toGL
  set G₃ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    ((γ₃.map (Int.castRingHom ℝ) : GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  set B₃ := G₃ᵀ * B₂ * G₃
  have hB₃_posDef : B₃.PosDef := (posDef_and_dotProduct_congr_glZ hB₂_posDef γ₃).1
  have hB₃_eq : (((γ₁ * γ₂ * γ₃).map (Int.castRingHom ℝ) : GL _ ℝ) : Matrix _ _ ℝ)ᵀ * B *
      (((γ₁ * γ₂ * γ₃).map (Int.castRingHom ℝ) : GL _ ℝ) : Matrix _ _ ℝ) = B₃ := by
    simp [B₃, B₂, B₁, G₃, G₂, G₁, Matrix.mul_assoc]
  refine ⟨γ₁ * γ₂ * γ₃, hB₃_eq.symm ▸
    isSiegelReduced_of_schurComplement h1C hB₃_posDef (fun i ↦ ?_) htop₃ ?_⟩
  · have h00_B₂ : B₂ 0 0 = B₁ 0 0 := by simp [B₂, hG₂_eq, Matrix.mul_apply, Fin.sum_univ_succ]
    have hmat : (((γ₂ * γ₃).map (Int.castRingHom ℝ) : GL _ ℝ) : Matrix _ _ ℝ)ᵀ * B₁ *
        (((γ₂ * γ₃).map (Int.castRingHom ℝ) : GL _ ℝ) : Matrix _ _ ℝ) = B₃ := by
      simp [B₃, B₂, G₃, G₂, Matrix.mul_assoc]
    rw [h00₃, h00_B₂, ← hmat]
    exact corner_le_diag_congr_glZ hB₁ hmin₁ (γ₂ * γ₃) i.succ
  · have hSB₂ : schurComplement B₂ =
        ((γ'.map (Int.castRingHom ℝ) : GL (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ)ᵀ *
          schurComplement B₁ *
          ((γ'.map (Int.castRingHom ℝ) : GL (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ) := by
      change schurComplement (G₂ᵀ * B₁ * G₂) = _
      rw [hG₂_eq, schurComplement_cornerBlockSucc_congr]
    rwa [hS₃, hSB₂]

/-- Diagonal sign-flip congruence preserves `IsSiegelReduced`. -/
theorem isSiegelReduced_diagonal_sign_congr {n : ℕ} {C : ℝ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsSiegelReduced C) {d : Fin n → ℝ} (hd : ∀ i, d i = 1 ∨ d i = -1) :
    ((Matrix.diagonal d)ᵀ * B * Matrix.diagonal d).IsSiegelReduced C := by
  have hd_sq (i : Fin n) : d i * d i = 1 := by rcases hd i with h | h <;> simp [h]
  have hd_abs (i : Fin n) : |d i| = 1 := by rcases hd i with h | h <;> simp [h]
  have hentry (i j : Fin n) :
      ((Matrix.diagonal d)ᵀ * B * Matrix.diagonal d) i j = d i * B i j * d j := by
    simp [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]
  have hdiag (i : Fin n) : ((Matrix.diagonal d)ᵀ * B * Matrix.diagonal d) i i = B i i := by
    rw [hentry, mul_right_comm, hd_sq, one_mul]
  have hdet : ((Matrix.diagonal d)ᵀ * B * Matrix.diagonal d).det = B.det := by
    have hdet_sq : (Matrix.diagonal d).det * (Matrix.diagonal d).det = 1 := by
      rw [← Matrix.det_mul, Matrix.diagonal_mul_diagonal]
      simp [hd_sq]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_right_comm, hdet_sq, one_mul]
  rw [Matrix.isSiegelReduced_def]
  refine ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · rw [hentry, hdiag, abs_mul, abs_mul, hd_abs, hd_abs, one_mul, mul_one]
    exact hB.abs_apply_lt i j
  · rw [hdiag, hdiag]
    exact hB.diag_lt_of_lt hij
  · simp_rw [hdiag, hdet]
    exact hB.prod_diag_lt

end TauCeti.SiegelReductionAux

public section

namespace Matrix.PosDef

/-- **Hermite–Siegel reduction for positive-definite matrices.** For every rank `n`, there exists a
constant `C > 1` depending only on `n` such that every positive-definite `n × n` real matrix `B` is
congruent under `GL (Fin n) ℤ` to a `C`-Siegel reduced matrix. -/
theorem exists_glZ_isSiegelReduced (n : ℕ) :
    ∃ C : ℝ, 1 < C ∧ ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef →
      ∃ γ : GL (Fin n) ℤ,
        (((γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * B *
          ((γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)).IsSiegelReduced
          C := by
  induction n with
  | zero =>
    refine ⟨2, one_lt_two, fun B _ ↦ ⟨1, ?_⟩⟩
    exact Matrix.isSiegelReduced_of_isEmpty.mpr one_lt_two
  | succ m ih =>
    obtain ⟨C, h1C, hC⟩ := ih
    have hmax : 1 < max (2 * C) ((4 / 3 : ℝ) ^ m * C + 1) := by
      have hle := le_max_left (2 * C) ((4 / 3 : ℝ) ^ m * C + 1)
      linarith
    exact ⟨_, hmax, TauCeti.SiegelReductionAux.exists_glZ_isSiegelReduced_succ h1C hC⟩

end Matrix.PosDef

namespace TauCeti

/-- **Siegel reduction for `GL_n(ℝ)`.** For every rank `n`, there exist parameters `u > 0` and
`t > 0` depending only on `n` such that every `g ∈ GL (Fin n) ℝ` factors as `γ * s` with
`γ ∈ GL (Fin n) ℤ` and `s ∈ siegelDomain n u t`. -/
theorem exists_glZ_mul_mem_siegelDomain (n : ℕ) :
    ∃ u : ℝ, 0 < u ∧ ∃ t : ℝ, 0 < t ∧
      ∀ g : GL (Fin n) ℝ, ∃ γ : GL (Fin n) ℤ, ∃ s ∈ siegelDomain n u t,
        g = γ.map (Int.castRingHom ℝ) * s := by
  obtain ⟨C, -, hC⟩ := Matrix.PosDef.exists_glZ_isSiegelReduced n
  obtain ⟨u, hu, t, ht, hdom⟩ := exists_mem_siegelDomain_of_isSiegelReduced_siegelGram n C
  refine ⟨u, hu, t, ht, fun g ↦ ?_⟩
  obtain ⟨γ, hred⟩ := hC g.siegelGram g.siegelGram_posDef
  refine ⟨γ, (γ.map (Int.castRingHom ℝ))⁻¹ * g, hdom _ ?_, by group⟩
  rwa [Matrix.GeneralLinearGroup.siegelGram_inv_mul]

/-- Helper adjusting `γ ∈ GL (Fin (m + 1)) ℤ` on the right by a sign flip so its determinant is `1`
while preserving `C`-Siegel reduction of `((γ.map _)⁻¹ * g).siegelGram`. -/
private theorem exists_glZ_det_one_siegelReduced {m : ℕ} {C : ℝ} {g : GL (Fin (m + 1)) ℝ}
    {γ : GL (Fin (m + 1)) ℤ}
    (hred : ((γ.map (Int.castRingHom ℝ))⁻¹ * g).siegelGram.IsSiegelReduced C) :
    ∃ γ₁ : GL (Fin (m + 1)) ℤ, γ₁.det = 1 ∧
      ((γ₁.map (Int.castRingHom ℝ))⁻¹ * g).siegelGram.IsSiegelReduced C := by
  rcases Int.units_eq_one_or γ.det with hdet | hdet
  · exact ⟨γ, hdet, hred⟩
  · let dZ : Fin (m + 1) → ℤ := Function.update 1 0 (-1)
    have hdZ_sq (i : Fin (m + 1)) : dZ i * dZ i = 1 := by
      by_cases hi : i = 0 <;> simp [dZ, hi]
    let J : GL (Fin (m + 1)) ℤ :=
      { val := Matrix.diagonal dZ
        inv := Matrix.diagonal dZ
        val_inv := by rw [Matrix.diagonal_mul_diagonal]; ext i j; simp [Matrix.one_apply, hdZ_sq]
        inv_val := by rw [Matrix.diagonal_mul_diagonal]; ext i j; simp [Matrix.one_apply, hdZ_sq] }
    have hJdet : J.det = -1 := by
      ext
      simp [J, dZ, Matrix.GeneralLinearGroup.val_det_apply, Fin.prod_univ_succ]
    refine ⟨γ * J, by rw [map_mul, hdet, hJdet]; decide, ?_⟩
    have hJmap : ((J.map (Int.castRingHom ℝ) : GL _ ℝ) : Matrix _ _ ℝ) =
        Matrix.diagonal (fun i ↦ (dZ i : ℝ)) := by
      ext i j; simp [J, Matrix.diagonal_apply]
    have hmul : ((γ * J).map (Int.castRingHom ℝ))⁻¹ * g =
        (J.map (Int.castRingHom ℝ))⁻¹ * ((γ.map (Int.castRingHom ℝ))⁻¹ * g) := by
      rw [map_mul, _root_.mul_inv_rev, mul_assoc]
    rw [hmul, Matrix.GeneralLinearGroup.siegelGram_inv_mul, hJmap]
    exact SiegelReductionAux.isSiegelReduced_diagonal_sign_congr hred fun i ↦ by
      by_cases hi : i = 0 <;> simp [dZ, hi]

/-- **Siegel reduction for `SL_n(ℝ)`.** For every rank `n`, there exist parameters `u > 0` and
`t > 0` depending only on `n` such that every `g ∈ Matrix.SpecialLinearGroup (Fin n) ℝ` factors as
`γ * s` with `γ ∈ Matrix.SpecialLinearGroup (Fin n) ℤ`, `s ∈ Matrix.SpecialLinearGroup (Fin n) ℝ`,
and `(s : GL (Fin n) ℝ) ∈ siegelDomain n u t`. -/
theorem exists_slZ_mul_mem_siegelDomain (n : ℕ) :
    ∃ u : ℝ, 0 < u ∧ ∃ t : ℝ, 0 < t ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin n) ℝ,
        ∃ γ : Matrix.SpecialLinearGroup (Fin n) ℤ,
          ∃ s : Matrix.SpecialLinearGroup (Fin n) ℝ,
            (s : GL (Fin n) ℝ) ∈ siegelDomain n u t ∧
              g = Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ * s := by
  rcases n with _ | m
  · refine ⟨1, zero_lt_one, 1, zero_lt_one, fun g ↦ ⟨1, 1, ?_, Subsingleton.elim _ _⟩⟩
    rw [siegelDomain_zero_eq_univ]
    exact Set.mem_univ _
  · obtain ⟨C, -, hC⟩ := Matrix.PosDef.exists_glZ_isSiegelReduced (m + 1)
    obtain ⟨u, hu, t, ht, hdom⟩ := exists_mem_siegelDomain_of_isSiegelReduced_siegelGram (m + 1) C
    refine ⟨u, hu, t, ht, fun g ↦ ?_⟩
    obtain ⟨γ₀, hred₀⟩ := hC (g : GL (Fin (m + 1)) ℝ).siegelGram
      (g : GL (Fin (m + 1)) ℝ).siegelGram_posDef
    rw [← Matrix.GeneralLinearGroup.siegelGram_inv_mul] at hred₀
    obtain ⟨γ₁, hdet₁, hred₁⟩ := exists_glZ_det_one_siegelReduced hred₀
    let γ : Matrix.SpecialLinearGroup (Fin (m + 1)) ℤ :=
      ⟨γ₁, by simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val hdet₁⟩
    let sGL : GL (Fin (m + 1)) ℝ := (γ₁.map (Int.castRingHom ℝ))⁻¹ * (g : GL (Fin (m + 1)) ℝ)
    have hγ_map : (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ : GL (Fin (m + 1)) ℝ) =
        γ₁.map (Int.castRingHom ℝ) := by
      ext i j
      exact rfl
    have hs_det : (sGL : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det = 1 := by
      have h1 : sGL.det = 1 := by
        simp [sGL, ← hγ_map, Matrix.SpecialLinearGroup.coeToGL_det]
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val h1
    let s : Matrix.SpecialLinearGroup (Fin (m + 1)) ℝ := ⟨sGL, hs_det⟩
    have hs_coe : (s : GL (Fin (m + 1)) ℝ) = sGL := by ext i j; rfl
    refine ⟨γ, s, hs_coe ▸ hdom sGL hred₁, Matrix.SpecialLinearGroup.toGL_injective ?_⟩
    rw [map_mul, hγ_map, hs_coe]
    simp [sGL]

end TauCeti
