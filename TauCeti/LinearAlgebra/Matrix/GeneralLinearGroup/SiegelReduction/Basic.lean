/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.InverseBound
public import TauCeti.LinearAlgebra.Matrix.PosDef.SiegelReduced.Cholesky
import Mathlib.Algebra.Order.Star.Real

/-!
# Siegel domains and inverse-transpose Gram matrices on `GL_n(ℝ)`

To pass between reduction of positive-definite symmetric matrices under `GL_n(ℤ)` and Siegel sets in
`GL_n(ℝ)` under left translation by `GL_n(ℤ)`, one associates to each `g ∈ GL_n(R)` the symmetric
matrix
`g.siegelGram = ((g⁻¹ : GL_n(R)) : Matrix n n R)ᵀ * ((g⁻¹ : GL_n(R)) : Matrix n n R)`
(`Matrix.GeneralLinearGroup.siegelGram`). Left multiplication by `γ⁻¹` transforms `siegelGram` by
congruence `(γ⁻¹ * g).siegelGram = γᵀ * g.siegelGram * γ`, while the fibers of `siegelGram` are
precisely the right cosets of `TauCeti.GLOrthogonal` (`siegelGram_eq_iff_exists_mem_GLOrthogonal`).

Over `ℝ`, inverting `TauCeti.iwasawaHomeomorph ℝ n` yields the unique `U A K` factorization
`g = v * a * k` with `v ∈ TauCeti.upperUnitriangularGroup (Fin n) ℝ`,
`a ∈ TauCeti.posDiagonalSubgroup (Fin n) ℝ`, and `k ∈ TauCeti.GLOrthogonal (Fin n) ℝ`
(`Matrix.GeneralLinearGroup.existsUnique_uak`). The **Siegel domain** `TauCeti.siegelDomain n u t`
consists of those `g = v * a * k` with `|v i j| ≤ u` (`i < j`) and `t * a_{i+1} ≤ a_i`
(`i + 1 < n`). Combining the nilpotent inverse bound for upper-unitriangular matrices with the
Cholesky characterization of `Matrix.IsSiegelReduced` establishes the two-sided cofinality between
`siegelDomain n u t` (`0 ≤ u`, `0 < t`) and `{g | g.siegelGram.IsSiegelReduced C}`.

## Main definitions

* `Matrix.GeneralLinearGroup.siegelGram`: the inverse-transpose Gram matrix `(g⁻¹)ᵀ * g⁻¹`.
* `TauCeti.siegelDomain n u t`: the Siegel set `Σ_n(u, t) ⊆ GL (Fin n) ℝ`.

## Main results

* `Matrix.GeneralLinearGroup.siegelGram_eq_iff_exists_mem_GLOrthogonal`: `g` and `h` have the same
  `siegelGram` if and only if `h = g * k` for some `k ∈ GLOrthogonal`.
* `Matrix.GeneralLinearGroup.existsUnique_uak`: unique `U A K` Iwasawa decomposition of `GL_n(ℝ)`.
* `TauCeti.siegelDomain_zero_eq_univ`, `TauCeti.siegelDomain_one_eq_univ`, and
  `TauCeti.mem_siegelDomain_two_of_coe_eq`: rank `0`, rank `1`, and the `SL_2(ℝ)` upper
  half-plane criterion `!![√y, x / √y; 0, (√y)⁻¹] ∈ siegelDomain 2 u t ↔ |x| ≤ u ∧ t ≤ y`.
* `TauCeti.exists_isSiegelReduced_siegelGram_of_mem_siegelDomain` and
  `TauCeti.exists_mem_siegelDomain_of_isSiegelReduced_siegelGram`: two-sided cofinality between
  Siegel domains and `IsSiegelReduced` preimages.

## References

* A. Borel, *Introduction aux groupes arithmétiques*, Hermann, 1969, §1.2–§1.8.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, 2nd ed.,
  Cambridge University Press, 2023, §4.2.1, pp. 205–208.
-/

public section

open Matrix
open scoped MatrixGroups

namespace Matrix.GeneralLinearGroup

section Semiring

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]

/-- The inverse-transpose Gram matrix `(g⁻¹)ᵀ * g⁻¹` of `g ∈ GL ι R`, covariant under left
translation `(γ⁻¹ * g).siegelGram = γᵀ * g.siegelGram * γ` and right-invariant under
`TauCeti.GLOrthogonal`. -/
def siegelGram (g : GL ι R) : Matrix ι ι R :=
  ((g⁻¹ : GL ι R) : Matrix ι ι R)ᵀ * ((g⁻¹ : GL ι R) : Matrix ι ι R)

/-- Unfolding `Matrix.GeneralLinearGroup.siegelGram`. -/
theorem siegelGram_def (g : GL ι R) :
    g.siegelGram = ((g⁻¹ : GL ι R) : Matrix ι ι R)ᵀ * ((g⁻¹ : GL ι R) : Matrix ι ι R) := by
  rfl

/-- The `siegelGram` of `1` is the identity matrix. -/
@[simp]
theorem siegelGram_one : (1 : GL ι R).siegelGram = 1 := by
  simp [siegelGram]

end Semiring

section CommSemiring

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- Every `siegelGram` over a commutative semiring is a symmetric matrix. -/
theorem isSymm_siegelGram (g : GL ι R) : g.siegelGram.IsSymm := by
  simp [IsSymm, siegelGram]

/-- Left multiplication transforms `siegelGram` by inverse congruence. -/
theorem siegelGram_mul_left (h g : GL ι R) :
    (h * g).siegelGram =
      ((h⁻¹ : GL ι R) : Matrix ι ι R)ᵀ * g.siegelGram * ((h⁻¹ : GL ι R) : Matrix ι ι R) := by
  simp [siegelGram, Matrix.mul_assoc]

/-- Left multiplication by `γ⁻¹` transforms `siegelGram` by congruence `γᵀ * g.siegelGram * γ`. -/
theorem siegelGram_inv_mul (γ g : GL ι R) :
    (γ⁻¹ * g).siegelGram = (γ : Matrix ι ι R)ᵀ * g.siegelGram * (γ : Matrix ι ι R) := by
  simpa using siegelGram_mul_left γ⁻¹ g

/-- Right multiplication by an orthogonal element leaves `siegelGram` unchanged. -/
@[simp]
theorem siegelGram_mul_of_mem_GLOrthogonal (g : GL ι R) {k : GL ι R}
    (hk : k ∈ TauCeti.GLOrthogonal ι R) :
    (g * k).siegelGram = g.siegelGram := by
  have hk' : k⁻¹ ∈ TauCeti.GLOrthogonal ι R := (TauCeti.GLOrthogonal ι R).inv_mem hk
  have hkk : ((k⁻¹ : GL ι R) : Matrix ι ι R)ᵀ * ((k⁻¹ : GL ι R) : Matrix ι ι R) = 1 :=
    TauCeti.GLOrthogonal.mem_iff.mp hk'
  calc (g * k).siegelGram
      = ((g⁻¹ : GL ι R) : Matrix ι ι R)ᵀ *
          (((k⁻¹ : GL ι R) : Matrix ι ι R)ᵀ * ((k⁻¹ : GL ι R) : Matrix ι ι R)) *
          ((g⁻¹ : GL ι R) : Matrix ι ι R) := by
            simp [siegelGram, Matrix.mul_assoc]
    _ = g.siegelGram := by rw [hkk, Matrix.mul_one]; rfl

/-- **Fibers of `siegelGram`.** Two elements `g, h ∈ GL ι R` have the same `siegelGram` if and only
if they lie in the same right coset of `TauCeti.GLOrthogonal ι R`. -/
theorem siegelGram_eq_iff_exists_mem_GLOrthogonal (g h : GL ι R) :
    g.siegelGram = h.siegelGram ↔ ∃ k ∈ TauCeti.GLOrthogonal ι R, h = g * k := by
  refine ⟨fun heq ↦ ?_, ?_⟩
  · refine ⟨g⁻¹ * h, ?_, by group⟩
    have hinv : h⁻¹ * g ∈ TauCeti.GLOrthogonal ι R := by
      rw [TauCeti.GLOrthogonal.mem_iff]
      calc ((h⁻¹ * g : GL ι R) : Matrix ι ι R)ᵀ * ((h⁻¹ * g : GL ι R) : Matrix ι ι R)
          = (g : Matrix ι ι R)ᵀ * h.siegelGram * (g : Matrix ι ι R) := by
              simp [siegelGram, Matrix.mul_assoc]
        _ = (g : Matrix ι ι R)ᵀ * g.siegelGram * (g : Matrix ι ι R) := by rw [← heq]
        _ = (g⁻¹ * g).siegelGram := (siegelGram_inv_mul g g).symm
        _ = 1 := by rw [inv_mul_cancel, siegelGram_one]
    have heq_inv : (h⁻¹ * g)⁻¹ = g⁻¹ * h := by group
    exact heq_inv ▸ (TauCeti.GLOrthogonal ι R).inv_mem hinv
  · rintro ⟨k, hk, rfl⟩
    exact (siegelGram_mul_of_mem_GLOrthogonal g hk).symm

end CommSemiring

section CommRing

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The determinant of `g.siegelGram` is `det(g⁻¹) ^ 2`. -/
theorem det_siegelGram (g : GL ι R) :
    g.siegelGram.det = ((g⁻¹ : GL ι R) : Matrix ι ι R).det ^ 2 := by
  rw [siegelGram, det_mul, det_transpose, sq]

end CommRing

section Real

/-- Over `ℝ`, `g.siegelGram` is positive definite for every `g ∈ GL ι ℝ`. -/
theorem siegelGram_posDef {ι : Type*} [Fintype ι] [DecidableEq ι] (g : GL ι ℝ) :
    g.siegelGram.PosDef := by
  simpa [siegelGram] using
    (PosDef.one (n := ι) (R := ℝ)).conjTranspose_mul_mul_same
      (mulVec_injective_of_isUnit (g⁻¹ : GL ι ℝ).isUnit)

/-- Every positive-definite real matrix on `Fin n` is `g.siegelGram` for some `g ∈ GL (Fin n) ℝ`. -/
theorem _root_.Matrix.PosDef.exists_siegelGram_eq {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosDef) : ∃ g : GL (Fin n) ℝ, g.siegelGram = B := by
  obtain ⟨U, hUtri, hUpos, hUB⟩ := hB.exists_isUpperTriangular_conjTranspose_mul_self_eq
  have hdet : IsUnit U.det := by
    rw [det_of_isUpperTriangular hUtri]
    exact (Finset.prod_pos fun i _ ↦ hUpos i).ne'.isUnit
  let u : GL (Fin n) ℝ := nonsingInvUnit U hdet
  have hu : (u : Matrix (Fin n) (Fin n) ℝ) = U := rfl
  exact ⟨u⁻¹, by simpa [siegelGram, hu] using hUB⟩

/-- **Unique `U A K` Iwasawa decomposition of `GL_n(ℝ)`.** Every `g ∈ GL (Fin n) ℝ` factors uniquely
as `v * a * k` with `v` upper unitriangular, `a` positive diagonal, and `k` orthogonal. -/
theorem existsUnique_uak {n : ℕ} (g : GL (Fin n) ℝ) :
    ∃! x : TauCeti.upperUnitriangularGroup (Fin n) ℝ × TauCeti.posDiagonalSubgroup (Fin n) ℝ ×
        TauCeti.GLOrthogonal (Fin n) ℝ,
      (x.1 : GL (Fin n) ℝ) * (x.2.1 : GL (Fin n) ℝ) * (x.2.2 : GL (Fin n) ℝ) = g := by
  have hmap (a : GL (Fin n) ℝ) : map (algebraMap ℝ ℝ) a = a := by ext i j; simp
  have hunit : TauCeti.GLOrthogonal (Fin n) ℝ = unitarySubgroup (GL (Fin n) ℝ) :=
    TauCeti.GLOrthogonal.eq_unitarySubgroup
  obtain ⟨⟨k₀, a₀, u₀⟩, hkau, huniq⟩ := existsUnique_iwasawa g⁻¹
  dsimp at hkau
  have hk₀ : (k₀ : GL (Fin n) ℝ)⁻¹ ∈ TauCeti.GLOrthogonal (Fin n) ℝ := by
    rw [hunit]
    exact (unitarySubgroup (GL (Fin n) ℝ)).inv_mem k₀.2
  refine ⟨⟨u₀⁻¹, a₀⁻¹, ⟨(k₀ : GL (Fin n) ℝ)⁻¹, hk₀⟩⟩, ?_, ?_⟩
  · calc ((u₀⁻¹ : TauCeti.upperUnitriangularGroup (Fin n) ℝ) : GL (Fin n) ℝ) *
          ((a₀⁻¹ : TauCeti.posDiagonalSubgroup (Fin n) ℝ) : GL (Fin n) ℝ) * (k₀ : GL (Fin n) ℝ)⁻¹
        = ((k₀ : GL (Fin n) ℝ) * (a₀ : GL (Fin n) ℝ) * (u₀ : GL (Fin n) ℝ))⁻¹ := by
            simp [mul_assoc]
      _ = g := by rw [hkau, inv_inv]
  · rintro ⟨v, a, k⟩ hvak
    dsimp at hvak
    have hk_unit : (k : GL (Fin n) ℝ)⁻¹ ∈ unitarySubgroup (GL (Fin n) ℝ) := by
      rw [← hunit]
      exact (TauCeti.GLOrthogonal (Fin n) ℝ).inv_mem k.2
    have hinv : (k : GL (Fin n) ℝ)⁻¹ *
        map (algebraMap ℝ ℝ) ((a⁻¹ : TauCeti.posDiagonalSubgroup (Fin n) ℝ) : GL (Fin n) ℝ) *
        ((v⁻¹ : TauCeti.upperUnitriangularGroup (Fin n) ℝ) : GL (Fin n) ℝ) = g⁻¹ := by
      rw [hmap, ← hvak]
      simp [mul_assoc]
    have heq := huniq ⟨⟨(k : GL (Fin n) ℝ)⁻¹, hk_unit⟩, a⁻¹, v⁻¹⟩ hinv
    injection heq with hk_eq hrest
    injection hrest with ha_eq hv_eq
    have hk' : k = ⟨(k₀ : GL (Fin n) ℝ)⁻¹, hk₀⟩ :=
      Subtype.ext (inv_eq_iff_eq_inv.mp (congrArg Subtype.val hk_eq))
    simp [inv_eq_iff_eq_inv.mp hv_eq, inv_eq_iff_eq_inv.mp ha_eq, hk']

/-- Uniqueness of the `U A K` factorization on `GL (Fin n) ℝ`. -/
theorem uak_unique {n : ℕ}
    {v₁ v₂ : TauCeti.upperUnitriangularGroup (Fin n) ℝ}
    {a₁ a₂ : TauCeti.posDiagonalSubgroup (Fin n) ℝ}
    {k₁ k₂ : TauCeti.GLOrthogonal (Fin n) ℝ}
    (h : (v₁ : GL (Fin n) ℝ) * (a₁ : GL (Fin n) ℝ) * (k₁ : GL (Fin n) ℝ) =
      (v₂ : GL (Fin n) ℝ) * (a₂ : GL (Fin n) ℝ) * (k₂ : GL (Fin n) ℝ)) :
    v₁ = v₂ ∧ a₁ = a₂ ∧ k₁ = k₂ := by
  obtain ⟨_, -, huniq⟩ :=
    existsUnique_uak ((v₂ : GL (Fin n) ℝ) * (a₂ : GL (Fin n) ℝ) * (k₂ : GL (Fin n) ℝ))
  have heq : (v₁, a₁, k₁) = (v₂, a₂, k₂) :=
    (huniq (v₁, a₁, k₁) h).trans (huniq (v₂, a₂, k₂) rfl).symm
  injection heq with hv hrest
  injection hrest with ha hk
  exact ⟨hv, ha, hk⟩

/-- Cholesky decomposition of `(v * a * k).siegelGram` for a `U A K` triple. -/
theorem siegelGram_uak {n : ℕ} (v : TauCeti.upperUnitriangularGroup (Fin n) ℝ)
    (a : TauCeti.posDiagonalSubgroup (Fin n) ℝ) (k : TauCeti.GLOrthogonal (Fin n) ℝ) :
    ((v : GL (Fin n) ℝ) * (a : GL (Fin n) ℝ) * (k : GL (Fin n) ℝ)).siegelGram =
      (((v⁻¹ : TauCeti.upperUnitriangularGroup (Fin n) ℝ) : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ)ᵀ *
        diagonal (fun i ↦ (((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i i)⁻¹ ^ 2) *
        (((v⁻¹ : TauCeti.upperUnitriangularGroup (Fin n) ℝ) : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) := by
  rw [siegelGram_mul_of_mem_GLOrthogonal _ k.2, siegelGram_mul_left, siegelGram_def]
  have ha : (((a : GL (Fin n) ℝ)⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      diagonal fun i ↦ (((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i i)⁻¹ :=
    TauCeti.coe_inv_of_mem_posDiagonalSubgroup a.2
  rw [ha, diagonal_transpose, diagonal_mul_diagonal]
  have hsq : (fun i ↦ (((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i i)⁻¹ *
      (((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i i)⁻¹) =
      fun i ↦ (((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i i)⁻¹ ^ 2 := by
    ext i; ring
  rw [hsq]
  simp [Matrix.mul_assoc]

end Real

end Matrix.GeneralLinearGroup

namespace TauCeti

open Matrix Matrix.GeneralLinearGroup

/-- **The Siegel domain `Σ_n(u, t)` in `GL_n(ℝ)`.** It consists of products `v * a * k` with `v`
upper unitriangular satisfying `|v i j| ≤ u` (`i < j`), `a` positive diagonal satisfying
`t * a_{i+1} ≤ a_i` (`i + 1 < n`), and `k` orthogonal. -/
def siegelDomain (n : ℕ) (u t : ℝ) : Set (GL (Fin n) ℝ) :=
  {g | ∃ (v : upperUnitriangularGroup (Fin n) ℝ) (a : posDiagonalSubgroup (Fin n) ℝ)
      (k : GLOrthogonal (Fin n) ℝ),
    (∀ i j, i < j → |((v : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j| ≤ u) ∧
    (∀ (i : ℕ) (hi : i + 1 < n),
      t * ((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) ⟨i + 1, hi⟩ ⟨i + 1, hi⟩ ≤
        ((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
          ⟨i, Nat.lt_of_succ_lt hi⟩ ⟨i, Nat.lt_of_succ_lt hi⟩) ∧
    (v : GL (Fin n) ℝ) * (a : GL (Fin n) ℝ) * (k : GL (Fin n) ℝ) = g}

/-- Unfolding membership in `TauCeti.siegelDomain`. -/
theorem mem_siegelDomain_iff {n : ℕ} {u t : ℝ} {g : GL (Fin n) ℝ} :
    g ∈ siegelDomain n u t ↔
      ∃ (v : upperUnitriangularGroup (Fin n) ℝ) (a : posDiagonalSubgroup (Fin n) ℝ)
        (k : GLOrthogonal (Fin n) ℝ),
        (∀ i j, i < j → |((v : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j| ≤ u) ∧
        (∀ (i : ℕ) (hi : i + 1 < n),
          t * ((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) ⟨i + 1, hi⟩ ⟨i + 1, hi⟩ ≤
            ((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
              ⟨i, Nat.lt_of_succ_lt hi⟩ ⟨i, Nat.lt_of_succ_lt hi⟩) ∧
        (v : GL (Fin n) ℝ) * (a : GL (Fin n) ℝ) * (k : GL (Fin n) ℝ) = g :=
  Iff.rfl

/-- The identity element belongs to `siegelDomain n u t` whenever `0 ≤ u` and `t ≤ 1`. -/
theorem one_mem_siegelDomain {n : ℕ} {u t : ℝ} (hu : 0 ≤ u) (ht : t ≤ 1) :
    (1 : GL (Fin n) ℝ) ∈ siegelDomain n u t :=
  ⟨1, 1, 1, fun i j hij ↦ by simp [Matrix.one_apply_ne hij.ne, hu],
    fun _ _ ↦ by simpa using ht, by simp⟩

/-- Monotonicity of `siegelDomain n u t`: enlarging `u` and shrinking `t` enlarges the domain. -/
theorem siegelDomain_mono {n : ℕ} {u₁ u₂ t₁ t₂ : ℝ} (hu : u₁ ≤ u₂) (ht : t₂ ≤ t₁) :
    siegelDomain n u₁ t₁ ⊆ siegelDomain n u₂ t₂ := by
  rintro g ⟨v, a, k, hv, ha, rfl⟩
  refine ⟨v, a, k, fun i j hij ↦ (hv i j hij).trans hu, fun i hi ↦ ?_, rfl⟩
  have hpos := apply_diag_pos_of_mem_posDiagonalSubgroup a.2 ⟨i + 1, hi⟩
  exact (mul_le_mul_of_nonneg_right ht hpos.le).trans (ha i hi)

/-- Right `O_n(ℝ)`-invariance of `siegelDomain n u t`. -/
theorem mul_mem_siegelDomain_of_mem_GLOrthogonal {n : ℕ} {u t : ℝ} {g k' : GL (Fin n) ℝ}
    (hg : g ∈ siegelDomain n u t) (hk' : k' ∈ GLOrthogonal (Fin n) ℝ) :
    g * k' ∈ siegelDomain n u t := by
  obtain ⟨v, a, k, hv, ha, rfl⟩ := hg
  exact ⟨v, a, k * ⟨k', hk'⟩, hv, ha, by simp [mul_assoc]⟩

/-- In rank `0`, every Siegel domain is all of `GL (Fin 0) ℝ`. -/
@[simp]
theorem siegelDomain_zero_eq_univ (u t : ℝ) :
    siegelDomain 0 u t = Set.univ := by
  ext g
  simp only [Set.mem_univ, iff_true]
  obtain ⟨⟨v, a, k⟩, hvak, _⟩ := existsUnique_uak g
  exact ⟨v, a, k, fun i ↦ Fin.elim0 i, fun _ hi ↦ by omega, hvak⟩

/-- In rank `1`, every Siegel domain is all of `GL (Fin 1) ℝ`. -/
@[simp]
theorem siegelDomain_one_eq_univ (u t : ℝ) :
    siegelDomain 1 u t = Set.univ := by
  ext g
  simp only [Set.mem_univ, iff_true]
  obtain ⟨⟨v, a, k⟩, hvak, _⟩ := existsUnique_uak g
  exact ⟨v, a, k, fun i j hij ↦ by omega, fun _ hi ↦ by omega, hvak⟩

/-- Explicit `U A K` factorization of the `2 × 2` upper half-plane matrix
`!![√y, x / √y; 0, (√y)⁻¹]`. -/
private theorem exists_uak_two_of_coe_eq {x y : ℝ} (hy : 0 < y) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![√y, x / √y; 0, (√y)⁻¹]) :
    ∃ (v₀ : upperUnitriangularGroup (Fin 2) ℝ) (a₀ : posDiagonalSubgroup (Fin 2) ℝ),
      ((v₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, x; 0, 1] ∧
      ((a₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = diagonal ![√y, (√y)⁻¹] ∧
      (v₀ : GL (Fin 2) ℝ) * (a₀ : GL (Fin 2) ℝ) *
        ((1 : GLOrthogonal (Fin 2) ℝ) : GL (Fin 2) ℝ) = g := by
  have hsy : 0 < √y := Real.sqrt_pos.mpr hy
  have hV : (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsUpperUnitriangular := by
    refine (Matrix.isUpperUnitriangular_def _).mpr ⟨fun i j hji ↦ ?_, fun i ↦ ?_⟩
    · fin_cases i <;> fin_cases j <;> simp at hji ⊢
    · fin_cases i <;> simp
  let v₀ : upperUnitriangularGroup (Fin 2) ℝ :=
    ⟨hV.toGL, UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup hV⟩
  let d₀ : Fin 2 → ℝˣ := ![Units.mk0 √y hsy.ne', Units.mk0 (√y)⁻¹ (inv_ne_zero hsy.ne')]
  have hd₀_mem : diagGL d₀ ∈ posDiagonalSubgroup (Fin 2) ℝ :=
    mem_posDiagonalSubgroup_iff.mpr
      ⟨![√y, (√y)⁻¹], fun i ↦ by fin_cases i <;> simp [hsy],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [d₀]⟩
  refine ⟨v₀, ⟨diagGL d₀, hd₀_mem⟩, hV.coe_toGL, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [d₀]
  · ext i j
    have hv_coe : ((v₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, x; 0, 1] := hV.coe_toGL
    simp only [OneMemClass.coe_one, mul_one, Units.val_mul, hv_coe, diagGL_coe, hg]
    fin_cases i <;> fin_cases j <;> simp [d₀, div_eq_mul_inv]

/-- **Upper half-plane criterion in rank `2`.** An invertible `2 × 2` real matrix with underlying
matrix `!![√y, x / √y; 0, (√y)⁻¹]` belongs to `siegelDomain 2 u t` if and only if `|x| ≤ u` and
`t ≤ y` (note invertibility forces `y > 0`). -/
theorem mem_siegelDomain_two_of_coe_eq {x y u t : ℝ} {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![√y, x / √y; 0, (√y)⁻¹]) :
    g ∈ siegelDomain 2 u t ↔ |x| ≤ u ∧ t ≤ y := by
  have hy : 0 < y := by
    by_contra! hle
    have hs : √y = 0 := Real.sqrt_eq_zero_of_nonpos hle
    refine Units.ne_zero g ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hg, hs]
  have hsy : 0 < √y := Real.sqrt_pos.mpr hy
  obtain ⟨v₀, a₀, hv₀, ha₀, hprod⟩ := exists_uak_two_of_coe_eq hy hg
  refine ⟨?_, fun ⟨hx, hty⟩ ↦ ?_⟩
  · rintro ⟨v, a, k, hv, ha, hvak⟩
    obtain ⟨rfl, rfl, -⟩ := uak_unique (hvak.trans hprod.symm)
    have hx' : |x| ≤ u := by simpa [hv₀] using hv 0 1 (by decide)
    have h0 : t * (√y)⁻¹ ≤ √y := by simpa [ha₀] using ha 0 (by decide)
    have hmul := mul_le_mul_of_nonneg_right h0 hsy.le
    rw [mul_assoc, inv_mul_cancel₀ hsy.ne', mul_one, Real.mul_self_sqrt hy.le] at hmul
    exact ⟨hx', hmul⟩
  · refine ⟨v₀, a₀, 1, fun i j hij ↦ ?_, fun i hi ↦ ?_, hprod⟩
    · rw [hv₀]
      fin_cases i <;> fin_cases j <;> simp [hx] at hij ⊢
    · obtain rfl : i = 0 := by omega
      suffices t * (√y)⁻¹ ≤ √y by simpa [ha₀] using this
      calc t * (√y)⁻¹ ≤ y * (√y)⁻¹ := mul_le_mul_of_nonneg_right hty (inv_nonneg.mpr hsy.le)
        _ = (√y * √y) * (√y)⁻¹ := by rw [Real.mul_self_sqrt hy.le]
        _ = √y := by rw [mul_assoc, mul_inv_cancel₀ hsy.ne', mul_one]

/-- **From Siegel domain to `IsSiegelReduced`.** For `0 < t`, there is a constant `C > 1` depending
only on `(n, u, t)` such that `g.siegelGram` is `C`-Siegel reduced for every
`g ∈ siegelDomain n u t`. -/
theorem exists_isSiegelReduced_siegelGram_of_mem_siegelDomain (n : ℕ) (u : ℝ) {t : ℝ}
    (ht : 0 < t) :
    ∃ C : ℝ, 1 < C ∧ ∀ g ∈ siegelDomain n u t, g.siegelGram.IsSiegelReduced C := by
  let u₀ : ℝ := max u 0
  let U' : ℝ := ∑ m ∈ Finset.Ico 1 n, (n : ℝ) ^ (m - 1) * u₀ ^ m
  let Bnd : ℝ := max U' (t⁻¹ ^ 2)
  obtain ⟨C, h1C, hC⟩ :=
    Matrix.IsUpperUnitriangular.exists_isSiegelReduced_transpose_mul_diagonal_mul n Bnd
  refine ⟨C, h1C, ?_⟩
  rintro g ⟨v, a, k, hv, ha, rfl⟩
  rw [siegelGram_uak v a k]
  let N : Matrix (Fin n) (Fin n) ℝ :=
    (((v⁻¹ : upperUnitriangularGroup (Fin n) ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
  let d : Fin n → ℝ := fun i ↦ (((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i i)⁻¹ ^ 2
  have hN : N.IsUpperUnitriangular := UpperUnitriangularGroup.isUpperUnitriangular v⁻¹
  have hd (i : Fin n) : 0 < d i :=
    pow_pos (inv_pos.mpr (apply_diag_pos_of_mem_posDiagonalSubgroup a.2 i)) 2
  refine hC N d hN hd (fun i j hij ↦ ?_) (fun i hi ↦ ?_)
  · have hv₀ (a b : Fin n) (hab : a < b) :
        |((v : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) a b| ≤ u₀ :=
      (hv a b hab).trans (le_max_left u 0)
    have hinv := UpperUnitriangularGroup.abs_inv_apply_le v hv₀ hij
    rw [Fintype.card_fin] at hinv
    exact hinv.trans (le_max_left U' (t⁻¹ ^ 2))
  · set a₀ := ((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) ⟨i, Nat.lt_of_succ_lt hi⟩
      ⟨i, Nat.lt_of_succ_lt hi⟩
    set a₁ := ((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) ⟨i + 1, hi⟩ ⟨i + 1, hi⟩
    have ha₀ : 0 < a₀ := apply_diag_pos_of_mem_posDiagonalSubgroup a.2 _
    have ha₁ : 0 < a₁ := apply_diag_pos_of_mem_posDiagonalSubgroup a.2 _
    have hinv_le : a₀⁻¹ ≤ t⁻¹ * a₁⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, inv_eq_one_div, one_div_mul_one_div,
        div_le_div_iff₀ ha₀ (mul_pos ht ha₁), one_mul, one_mul]
      exact ha i hi
    have hsq_le : d ⟨i, Nat.lt_of_succ_lt hi⟩ ≤ t⁻¹ ^ 2 * d ⟨i + 1, hi⟩ := by
      calc a₀⁻¹ ^ 2 ≤ (t⁻¹ * a₁⁻¹) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr ha₀.le) hinv_le 2
        _ = t⁻¹ ^ 2 * a₁⁻¹ ^ 2 := by ring
    exact hsq_le.trans (mul_le_mul_of_nonneg_right (le_max_right U' (t⁻¹ ^ 2)) (hd _).le)

/-- Helper converting a Cholesky pivot bound `(a₀⁻¹) ^ 2 ≤ Bnd₁ * (a₁⁻¹) ^ 2` into the Siegel
domain root inequality `(√Bnd₁)⁻¹ * a₁ ≤ a₀`. -/
private theorem inv_sqrt_mul_le_of_inv_sq_le {a₀ a₁ Bnd₁ : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁)
    (hBnd₁ : 0 < Bnd₁) (hsq : a₀⁻¹ ^ 2 ≤ Bnd₁ * a₁⁻¹ ^ 2) :
    (√Bnd₁)⁻¹ * a₁ ≤ a₀ := by
  have hs : 0 < √Bnd₁ := Real.sqrt_pos.mpr hBnd₁
  have hsq' : a₀⁻¹ ^ 2 ≤ (√Bnd₁ * a₁⁻¹) ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt hBnd₁.le]
  have hle : a₀⁻¹ ≤ √Bnd₁ * a₁⁻¹ :=
    le_of_sq_le_sq hsq' (mul_nonneg hs.le (inv_nonneg.mpr ha₁.le))
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hle (mul_pos ha₀ ha₁).le) (inv_nonneg.mpr hs.le)
  have hlhs : (√Bnd₁)⁻¹ * (a₀⁻¹ * (a₀ * a₁)) = (√Bnd₁)⁻¹ * a₁ := by
    rw [← mul_assoc a₀⁻¹, inv_mul_cancel₀ ha₀.ne', one_mul]
  have hrhs : (√Bnd₁)⁻¹ * ((√Bnd₁ * a₁⁻¹) * (a₀ * a₁)) = a₀ := by
    calc (√Bnd₁)⁻¹ * ((√Bnd₁ * a₁⁻¹) * (a₀ * a₁))
        = ((√Bnd₁)⁻¹ * √Bnd₁) * (a₁⁻¹ * a₁) * a₀ := by ring
      _ = a₀ := by rw [inv_mul_cancel₀ hs.ne', inv_mul_cancel₀ ha₁.ne', one_mul, one_mul]
  rwa [hlhs, hrhs] at hmul

/-- **From `IsSiegelReduced` to Siegel domain.** For every `(n, C)`, there exist `u > 0` and `t > 0`
depending only on `(n, C)` such that every `g ∈ GL (Fin n) ℝ` with `C`-Siegel reduced `siegelGram`
belongs to `siegelDomain n u t`. -/
theorem exists_mem_siegelDomain_of_isSiegelReduced_siegelGram (n : ℕ) (C : ℝ) :
    ∃ u : ℝ, 0 < u ∧ ∃ t : ℝ, 0 < t ∧
      ∀ g : GL (Fin n) ℝ, g.siegelGram.IsSiegelReduced C → g ∈ siegelDomain n u t := by
  obtain ⟨Bnd, hBnd0, hBnd⟩ := Matrix.IsSiegelReduced.exists_upperUnitriangular_bound n C
  let u : ℝ := (∑ m ∈ Finset.Ico 1 n, (n : ℝ) ^ (m - 1) * Bnd ^ m) + 1
  have hu_pos : 0 < u := by
    have : 0 ≤ ∑ m ∈ Finset.Ico 1 n, (n : ℝ) ^ (m - 1) * Bnd ^ m :=
      Finset.sum_nonneg fun m _ ↦ by positivity
    linarith
  let Bnd₁ : ℝ := max Bnd 1
  have hBnd₁_pos : 0 < Bnd₁ := zero_lt_one.trans_le (le_max_right Bnd 1)
  let t : ℝ := (√Bnd₁)⁻¹
  refine ⟨u, hu_pos, t, inv_pos.mpr (Real.sqrt_pos.mpr hBnd₁_pos), fun g hred ↦ ?_⟩
  obtain ⟨⟨v, a, k⟩, rfl, _⟩ := existsUnique_uak g
  dsimp at hred ⊢
  rw [siegelGram_uak v a k] at hred
  let N : Matrix (Fin n) (Fin n) ℝ :=
    (((v⁻¹ : upperUnitriangularGroup (Fin n) ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
  let d : Fin n → ℝ := fun i ↦ (((a : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i i)⁻¹ ^ 2
  have hN : N.IsUpperUnitriangular := UpperUnitriangularGroup.isUpperUnitriangular v⁻¹
  have hd (i : Fin n) : 0 < d i :=
    pow_pos (inv_pos.mpr (apply_diag_pos_of_mem_posDiagonalSubgroup a.2 i)) 2
  obtain ⟨hNbnd, hdbnd, _⟩ := hBnd N d hN hd hred
  refine ⟨v, a, k, fun i j hij ↦ ?_, fun i hi ↦ ?_, rfl⟩
  · have hv_inv := UpperUnitriangularGroup.abs_inv_apply_le v⁻¹ hNbnd hij
    rw [inv_inv, Fintype.card_fin] at hv_inv
    exact hv_inv.trans (le_add_of_nonneg_right zero_le_one)
  · have hij : (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin n) < ⟨i + 1, hi⟩ :=
      Fin.lt_def.mpr (Nat.lt_succ_self i)
    exact inv_sqrt_mul_le_of_inv_sq_le
      (apply_diag_pos_of_mem_posDiagonalSubgroup a.2 _)
      (apply_diag_pos_of_mem_posDiagonalSubgroup a.2 _) hBnd₁_pos
      ((hdbnd _ _ hij).trans (mul_le_mul_of_nonneg_right (le_max_left Bnd 1) (sq_nonneg _)))

end TauCeti
