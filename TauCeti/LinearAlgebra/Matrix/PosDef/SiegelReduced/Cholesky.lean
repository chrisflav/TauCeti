/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.LDL
public import TauCeti.LinearAlgebra.Matrix.PosDef.SiegelReduced.Basic
public import TauCeti.LinearAlgebra.Matrix.Triangular
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real

/-!
# Cholesky and unitriangular `LDL` characterization of Siegel-reduced matrices

Write a symmetric matrix on `Fin n` in unitriangular Cholesky / `LDL` coordinates as
`B = Nᵀ * diagonal d * N`, where `N` is upper unitriangular (`Matrix.IsUpperUnitriangular`) and `d`
has positive entries (`0 < d i`). Over `ℝ`, every positive-definite matrix `B` admits this
representation via `N = (LDL.lower hB)ᵀ` and `d = LDL.diagEntries hB`.

This file proves the uniform equivalence between `Matrix.IsSiegelReduced` on `B` and boundedness of
its Cholesky coordinates `(N, d)`, over any strictly ordered commutative ring:
* `Matrix.IsSiegelReduced.exists_upperUnitriangular_bound`: for each `(n, C)`, there is an explicit
  bound `R ≥ 0` depending only on `(n, C)` such that whenever
  `(Nᵀ * diagonal d * N).IsSiegelReduced C`, one has `|N i j| ≤ R` and `d i ≤ R * d j` for all
  `i < j`, as well as `(Nᵀ * diagonal d * N) i i < C * d i` for all `i`.
* `Matrix.IsUpperUnitriangular.exists_isSiegelReduced_transpose_mul_diagonal_mul`: conversely, for
  each `(n, R)`, there is an explicit `C > 1` depending only on `(n, R)` such that if `|N i j| ≤ R`
  for `i < j` and `d ⟨i, _⟩ ≤ R * d ⟨i + 1, _⟩` for `i + 1 < n`, then `Nᵀ * diagonal d * N` is
  `C`-Siegel reduced.
* `Matrix.PosDef.exists_ldl_bound_of_isSiegelReduced`: specialization of the forward bound to
  `LDL.lower hB` and `LDL.diagEntries hB` for positive-definite real matrices.

## References

* A. Borel, *Introduction aux groupes arithmétiques*, Hermann, 1969, Proposition 1.5 and Lemme 1.7.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, 2nd ed.,
  Cambridge University Press, 2023, §4.2, Proposition 4.4.
-/

public section

open scoped Matrix

namespace Matrix

section GeneralIndex

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- Formula for the `(i, j)` entry of `Nᵀ * diagonal d * N`. -/
private theorem transpose_mul_diagonal_mul_apply [DecidableEq ι] (N : Matrix ι ι R) (d : ι → R)
    (i j : ι) :
    (Nᵀ * diagonal d * N) i j = ∑ k, d k * N k i * N k j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [transpose_apply, diagonal_mul]
  ring

variable [LinearOrder ι]

/-- If `N` is upper unitriangular, then `Nᵀ * diagonal d * N` has determinant `∏ i, d i`. -/
theorem IsUpperUnitriangular.det_transpose_mul_diagonal_mul {N : Matrix ι ι R}
    (hN : N.IsUpperUnitriangular) (d : ι → R) :
    (Nᵀ * diagonal d * N).det = ∏ i, d i := by
  rw [det_mul, det_mul, det_transpose, hN.det_eq_one, one_mul, mul_one, det_diagonal]

/-- Isolating the `k = i` term of `(Nᵀ * diagonal d * N) i j` when `N` is upper unitriangular. -/
private theorem mul_apply_eq_sub_sum_filter_lt {N : Matrix ι ι R} (hN : N.IsUpperUnitriangular)
    (d : ι → R) (i j : ι) :
    d i * N i j =
      (Nᵀ * diagonal d * N) i j - ∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j := by
  rw [transpose_mul_diagonal_mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    hN.apply_diag i, mul_one]
  have hsub : (∑ k ∈ Finset.univ.erase i, d k * N k i * N k j) =
      ∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j := by
    refine (Finset.sum_subset (fun k hk ↦ Finset.mem_erase.mpr
      ⟨(Finset.mem_filter.mp hk).2.ne, Finset.mem_univ k⟩) fun k hk hnot ↦ ?_).symm
    have hik : i < k := lt_of_le_of_ne (not_lt.mp fun hlt ↦ hnot
      (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hlt⟩)) (Finset.mem_erase.mp hk).1.symm
    simp [hN.isUpperTriangular hik]
  rw [hsub]
  ring

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- Each diagonal entry of `Nᵀ * diagonal d * N` dominates the corresponding pivot `d i` when `N`
is upper unitriangular and `d ≥ 0`. -/
theorem IsUpperUnitriangular.diag_le_transpose_mul_diagonal_mul {N : Matrix ι ι R}
    (hN : N.IsUpperUnitriangular) {d : ι → R} (hd : ∀ i, 0 ≤ d i) (i : ι) :
    d i ≤ (Nᵀ * diagonal d * N) i i := by
  rw [transpose_mul_diagonal_mul_apply]
  calc d i = d i * N i i * N i i := by rw [hN.apply_diag i, mul_one, mul_one]
    _ ≤ ∑ k, d k * N k i * N k i := by
        refine Finset.single_le_sum (f := fun k ↦ d k * N k i * N k i) (fun k _ ↦ ?_)
          (Finset.mem_univ i)
        simpa [mul_assoc] using mul_nonneg (hd k) (mul_self_nonneg (N k i))

/-- If `Nᵀ * diagonal d * N` is `C`-Siegel reduced with `N` upper unitriangular and `d > 0`, then
`(Nᵀ * diagonal d * N) i i < C * d i` for every `i`, and `d i < C ^ 2 * d j` for `i < j`. -/
theorem IsSiegelReduced.transpose_mul_diagonal_mul_diag_lt {N : Matrix ι ι R}
    (hN : N.IsUpperUnitriangular) {d : ι → R} (hd : ∀ i, 0 < d i) {C : R}
    (hB : (Nᵀ * diagonal d * N).IsSiegelReduced C) :
    (∀ i, (Nᵀ * diagonal d * N) i i < C * d i) ∧ (∀ i j, i < j → d i < C ^ 2 * d j) := by
  set B := Nᵀ * diagonal d * N
  have hd_le (i : ι) : d i ≤ B i i := hN.diag_le_transpose_mul_diagonal_mul (fun k ↦ (hd k).le) i
  have hBdiag_pos (i : ι) : 0 < B i i := (hd i).trans_le (hd_le i)
  have hCpos : 0 < C := zero_lt_one.trans (hB.one_lt fun i ↦ (hBdiag_pos i).le)
  have hdiag_lt (i : ι) : B i i < C * d i := by
    have herase_pos : 0 < ∏ k ∈ Finset.univ.erase i, d k := Finset.prod_pos fun k _ ↦ hd k
    have herase_le : (∏ k ∈ Finset.univ.erase i, d k) ≤ ∏ k ∈ Finset.univ.erase i, B k k :=
      Finset.prod_le_prod₀ (fun k _ ↦ (hd k).le) (fun k _ ↦ hd_le k)
    refine lt_of_mul_lt_mul_right ?_ herase_pos.le
    calc B i i * (∏ k ∈ Finset.univ.erase i, d k)
        ≤ B i i * (∏ k ∈ Finset.univ.erase i, B k k) :=
          mul_le_mul_of_nonneg_left herase_le (hBdiag_pos i).le
      _ = ∏ k, B k k := Finset.mul_prod_erase Finset.univ (fun k ↦ B k k) (Finset.mem_univ i)
      _ < C * B.det := hB.prod_diag_lt
      _ = C * d i * (∏ k ∈ Finset.univ.erase i, d k) := by
          rw [hN.det_transpose_mul_diagonal_mul d,
            ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i), mul_assoc]
  refine ⟨hdiag_lt, fun i j hij ↦ ?_⟩
  calc d i ≤ B i i := hd_le i
    _ < C * B j j := hB.diag_lt_of_lt hij
    _ < C * (C * d j) := mul_lt_mul_of_pos_left (hdiag_lt j) hCpos
    _ = C ^ 2 * d j := by ring

end GeneralIndex

section OrderedCommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Explicit monotone row-by-row bound on `|N i j|` for a `C`-Siegel reduced
`Nᵀ * diagonal d * N`. -/
private def choleskyRowBound (n : ℕ) (C : R) : ℕ → R
  | 0 => C ^ 2
  | r + 1 => choleskyRowBound n C r + (n : R) * C ^ 2 * (choleskyRowBound n C r) ^ 2

private theorem choleskyRowBound_mono (n : ℕ) (C : R) : Monotone (choleskyRowBound n C) :=
  monotone_nat_of_le_succ fun r ↦ le_add_of_nonneg_right (by positivity)

private theorem sq_le_choleskyRowBound (n : ℕ) (C : R) (r : ℕ) :
    C ^ 2 ≤ choleskyRowBound n C r :=
  choleskyRowBound_mono n C (Nat.zero_le r)

private theorem abs_sum_filter_lt_le_choleskyRowBound {n : ℕ} {C : R}
    {N : Matrix (Fin n) (Fin n) R} {d : Fin n → R} (hd : ∀ i, 0 < d i)
    (hd_ratio : ∀ i j, i < j → d i < C ^ 2 * d j) {r : ℕ}
    (ih : ∀ i j : Fin n, i.val ≤ r → i < j → |N i j| ≤ choleskyRowBound n C r)
    {i j : Fin n} (heq : i.val = r + 1) (hij : i < j) :
    |∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j| ≤
      ((n : R) * C ^ 2 * (choleskyRowBound n C r) ^ 2) * d i := by
  have hdi : 0 ≤ d i := (hd i).le
  have hcr : 0 ≤ choleskyRowBound n C r := (sq_nonneg C).trans (sq_le_choleskyRowBound n C r)
  calc |∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j|
      ≤ ∑ k ∈ Finset.univ.filter (· < i), |d k * N k i * N k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.univ.filter (· < i),
          (C ^ 2 * d i) * choleskyRowBound n C r * choleskyRowBound n C r := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        have hki : k < i := (Finset.mem_filter.mp hk).2
        have hkr : k.val ≤ r := by
          have := Fin.lt_def.mp hki
          omega
        rw [abs_mul, abs_mul, abs_of_pos (hd k)]
        exact mul_le_mul
          (mul_le_mul (hd_ratio k i hki).le (ih k i hkr hki) (abs_nonneg _) (by positivity))
          (ih k j hkr (hki.trans hij)) (abs_nonneg _) (by positivity)
    _ ≤ (n : R) * ((C ^ 2 * d i) * choleskyRowBound n C r * choleskyRowBound n C r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast (Finset.card_filter_le _ _).trans_eq (by simp)
    _ = ((n : R) * C ^ 2 * (choleskyRowBound n C r) ^ 2) * d i := by ring

private theorem abs_apply_le_choleskyRowBound {n : ℕ} {C : R} {N : Matrix (Fin n) (Fin n) R}
    (hN : N.IsUpperUnitriangular) {d : Fin n → R} (hd : ∀ i, 0 < d i)
    (hB : (Nᵀ * diagonal d * N).IsSiegelReduced C) :
    ∀ (r : ℕ) (i j : Fin n), i.val ≤ r → i < j → |N i j| ≤ choleskyRowBound n C r := by
  obtain ⟨hdiag_lt, hd_ratio⟩ := hB.transpose_mul_diagonal_mul_diag_lt hN hd
  have hCpos : 0 < C :=
    zero_lt_one.trans (hB.one_lt fun k ↦ (hd k).le.trans
      (hN.diag_le_transpose_mul_diagonal_mul (fun l ↦ (hd l).le) k))
  have hBij_lt (i j : Fin n) : |(Nᵀ * diagonal d * N) i j| ≤ C ^ 2 * d i := by
    calc |(Nᵀ * diagonal d * N) i j|
        ≤ C * (Nᵀ * diagonal d * N) i i := (hB.abs_apply_lt i j).le
      _ ≤ C * (C * d i) := mul_le_mul_of_nonneg_left (hdiag_lt i).le hCpos.le
      _ = C ^ 2 * d i := by ring
  intro r
  induction r with
  | zero =>
    intro i j hi _
    have hemp : Finset.univ.filter (· < i) = ∅ := by
      ext k
      simp [Fin.lt_def, Nat.eq_zero_of_le_zero hi]
    have hmul := congrArg abs (mul_apply_eq_sub_sum_filter_lt hN d i j)
    rw [hemp, Finset.sum_empty, sub_zero, abs_mul, abs_of_pos (hd i)] at hmul
    exact le_of_mul_le_mul_left
      (hmul.le.trans (by simpa [choleskyRowBound, mul_comm] using hBij_lt i j)) (hd i)
  | succ r ih =>
    intro i j hi hij
    rcases Nat.of_le_succ hi with hle | heq
    · exact (ih i j hle hij).trans (choleskyRowBound_mono n C (Nat.le_succ r))
    · have hmul := congrArg abs (mul_apply_eq_sub_sum_filter_lt hN d i j)
      rw [abs_mul, abs_of_pos (hd i)] at hmul
      have htot : d i * |N i j| ≤ d i * choleskyRowBound n C (r + 1) := by
        calc d i * |N i j|
            ≤ |(Nᵀ * diagonal d * N) i j| +
                |∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j| :=
              hmul.le.trans (abs_sub _ _)
          _ ≤ C ^ 2 * d i + ((n : R) * C ^ 2 * (choleskyRowBound n C r) ^ 2) * d i :=
              add_le_add (hBij_lt i j)
                (abs_sum_filter_lt_le_choleskyRowBound hd hd_ratio ih heq hij)
          _ ≤ choleskyRowBound n C r * d i +
                ((n : R) * C ^ 2 * (choleskyRowBound n C r) ^ 2) * d i :=
              add_le_add
                (mul_le_mul_of_nonneg_right (sq_le_choleskyRowBound n C r) (hd i).le) le_rfl
          _ = d i * choleskyRowBound n C (r + 1) := by
              dsimp [choleskyRowBound]
              ring
      exact le_of_mul_le_mul_left htot (hd i)

/-- **Uniform Cholesky coordinate bounds from `IsSiegelReduced`.** For each `(n, C)` there is a
nonnegative constant `Bnd` depending only on `n` and `C` such that whenever `N` is upper
unitriangular, `d > 0`, and `Nᵀ * diagonal d * N` is `C`-Siegel reduced, one has `|N i j| ≤ Bnd`
and `d i ≤ Bnd * d j` for all `i < j`, together with `(Nᵀ * diagonal d * N) i i < C * d i`. -/
theorem IsSiegelReduced.exists_upperUnitriangular_bound (n : ℕ) (C : R) :
    ∃ Bnd : R, 0 ≤ Bnd ∧
      ∀ (N : Matrix (Fin n) (Fin n) R) (d : Fin n → R),
        N.IsUpperUnitriangular → (∀ i, 0 < d i) → (Nᵀ * diagonal d * N).IsSiegelReduced C →
          (∀ i j, i < j → |N i j| ≤ Bnd) ∧
          (∀ i j, i < j → d i ≤ Bnd * d j) ∧
          (∀ i, (Nᵀ * diagonal d * N) i i < C * d i) := by
  refine ⟨choleskyRowBound n C n, (sq_nonneg C).trans (sq_le_choleskyRowBound n C n),
    fun N d hN hd hB ↦ ?_⟩
  obtain ⟨hdiag_lt, hd_ratio⟩ := hB.transpose_mul_diagonal_mul_diag_lt hN hd
  refine ⟨fun i j hij ↦ abs_apply_le_choleskyRowBound hN hd hB n i j i.isLt.le hij,
    fun i j hij ↦ (hd_ratio i j hij).le.trans
      (mul_le_mul_of_nonneg_right (sq_le_choleskyRowBound n C n) (hd j).le),
    hdiag_lt⟩

/-- Adjacent ratio bounds `d ⟨k, _⟩ ≤ M * d ⟨k + 1, _⟩` propagate to `d i ≤ M ^ n * d j` for all
`i ≤ j` in `Fin n` when `1 ≤ M` and `d ≥ 0`. -/
private theorem diag_le_pow_mul_of_succ_le {n : ℕ} {d : Fin n → R} (hd : ∀ i, 0 ≤ d i)
    {M : R} (hM : 1 ≤ M)
    (hstep : ∀ (k : ℕ) (hk : k + 1 < n), d ⟨k, Nat.lt_of_succ_lt hk⟩ ≤ M * d ⟨k + 1, hk⟩)
    {i j : Fin n} (hij : i ≤ j) :
    d i ≤ M ^ n * d j := by
  have hrec : ∀ (m : ℕ) (q : Fin n), q.val - i.val = m → i ≤ q → d i ≤ M ^ m * d q := by
    intro m
    induction m with
    | zero =>
      intro q h0 hiq
      have hqi : i = q := Fin.ext (Nat.le_antisymm hiq (Nat.sub_eq_zero_iff_le.mp h0))
      simp [hqi]
    | succ m ih =>
      rintro ⟨_ | k, hqlt⟩ hq _
      · simp at hq
      · let q' : Fin n := ⟨k, Nat.lt_of_succ_lt hqlt⟩
        have hiq' : i ≤ q' := Fin.le_def.mpr (by simp at hq; dsimp [q']; omega)
        have hq'm : q'.val - i.val = m := by simp at hq; dsimp [q']; omega
        calc d i ≤ M ^ m * d q' := ih q' hq'm hiq'
          _ ≤ M ^ m * (M * d ⟨k + 1, hqlt⟩) :=
              mul_le_mul_of_nonneg_left (hstep k hqlt) (pow_nonneg (zero_le_one.trans hM) m)
          _ = M ^ (m + 1) * d ⟨k + 1, hqlt⟩ := by rw [pow_succ']; ring
  calc d i ≤ M ^ (j.val - i.val) * d j := hrec (j.val - i.val) j rfl hij
    _ ≤ M ^ n * d j :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM (by omega)) (hd j)

/-- Entrywise row bound `|(Nᵀ * diagonal d * N) p q| ≤ ((n * M ^ (n + 2) + 1) * d p)` from
Cholesky coordinate bounds. -/
private theorem abs_transpose_mul_diagonal_mul_apply_le {n : ℕ} {N : Matrix (Fin n) (Fin n) R}
    (hN : N.IsUpperUnitriangular) {d : Fin n → R} (hd : ∀ i, 0 < d i) {M : R} (hM : 1 ≤ M)
    (hN_le : ∀ i j, i < j → |N i j| ≤ M)
    (hd_le : ∀ i j, i ≤ j → d i ≤ M ^ n * d j) (p q : Fin n) :
    |(Nᵀ * diagonal d * N) p q| ≤ ((n : R) * M ^ (n + 2) + 1) * d p := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hdp : 0 ≤ d p := (hd p).le
  have hN_all (a b : Fin n) : |N a b| ≤ M := by
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact hN_le a b hab
    · simp [hN.apply_diag a, hM]
    · simp [hN.isUpperTriangular hba, hM0]
  rw [transpose_mul_diagonal_mul_apply]
  calc |∑ k, d k * N k p * N k q|
      ≤ ∑ k, |d k * N k p * N k q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, M ^ (n + 2) * d p := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        rcases le_or_gt k p with hkp | hpk
        · rw [abs_mul, abs_mul, abs_of_pos (hd k)]
          calc d k * |N k p| * |N k q|
              ≤ (M ^ n * d p) * M * M :=
                mul_le_mul (mul_le_mul (hd_le k p hkp) (hN_all k p) (abs_nonneg _) (by positivity))
                  (hN_all k q) (abs_nonneg _) (by positivity)
            _ = M ^ (n + 2) * d p := by ring
        · simp only [hN.isUpperTriangular hpk, mul_zero, zero_mul, abs_zero]
          positivity
    _ = ((n : R) * M ^ (n + 2)) * d p := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
    _ ≤ ((n : R) * M ^ (n + 2) + 1) * d p :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdp

/-- **Converse Cholesky criterion for `IsSiegelReduced`.** For each `(n, Bnd)` there is a constant
`C > 1` depending only on `n` and `Bnd` such that whenever `N` is upper unitriangular with
`|N i j| ≤ Bnd` (`i < j`) and `d > 0` satisfies `d ⟨k, _⟩ ≤ Bnd * d ⟨k + 1, _⟩` (`k + 1 < n`), the
matrix `Nᵀ * diagonal d * N` is `C`-Siegel reduced. -/
theorem IsUpperUnitriangular.exists_isSiegelReduced_transpose_mul_diagonal_mul (n : ℕ) (Bnd : R) :
    ∃ C : R, 1 < C ∧
      ∀ (N : Matrix (Fin n) (Fin n) R) (d : Fin n → R),
        N.IsUpperUnitriangular → (∀ i, 0 < d i) →
        (∀ i j, i < j → |N i j| ≤ Bnd) →
        (∀ (k : ℕ) (hk : k + 1 < n), d ⟨k, Nat.lt_of_succ_lt hk⟩ ≤ Bnd * d ⟨k + 1, hk⟩) →
          (Nᵀ * diagonal d * N).IsSiegelReduced C := by
  let M : R := max Bnd 1
  have hM1 : 1 ≤ M := le_max_right Bnd 1
  have hBndM : Bnd ≤ M := le_max_left Bnd 1
  let K₁ : R := (n : R) * M ^ (n + 2) + 1
  have hK₁0 : 0 ≤ K₁ := by positivity
  let C : R := K₁ ^ n + K₁ * M ^ n + 2
  have h1C : 1 < C := by
    have : 0 ≤ K₁ ^ n + K₁ * M ^ n := by positivity
    linarith
  refine ⟨C, h1C, fun N d hN hd hNbnd hdbnd ↦ ?_⟩
  set B := Nᵀ * diagonal d * N
  have hd_le_B (i : Fin n) : d i ≤ B i i :=
    hN.diag_le_transpose_mul_diagonal_mul (fun k ↦ (hd k).le) i
  have hB_pos (i : Fin n) : 0 < B i i := (hd i).trans_le (hd_le_B i)
  have hd_ratio (i j : Fin n) (hij : i ≤ j) : d i ≤ M ^ n * d j :=
    diag_le_pow_mul_of_succ_le (fun k ↦ (hd k).le) hM1
      (fun k hk ↦ (hdbnd k hk).trans (mul_le_mul_of_nonneg_right hBndM (hd _).le)) hij
  have hB_entry (p q : Fin n) : |B p q| ≤ K₁ * d p :=
    abs_transpose_mul_diagonal_mul_apply_le hN hd hM1
      (fun i j hij ↦ (hNbnd i j hij).trans hBndM) hd_ratio p q
  have hB_diag_upper (i : Fin n) : B i i ≤ K₁ * d i := (le_abs_self _).trans (hB_entry i i)
  refine isSiegelReduced_def.mpr ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · have hKC : K₁ < C := by
      have h1 : K₁ ≤ K₁ * M ^ n := le_mul_of_one_le_right hK₁0 (one_le_pow₀ hM1)
      have h2 : 0 ≤ K₁ ^ n := pow_nonneg hK₁0 n
      linarith
    exact ((hB_entry i j).trans (mul_le_mul_of_nonneg_left (hd_le_B i) hK₁0)).trans_lt
      (mul_lt_mul_of_pos_right hKC (hB_pos i))
  · have hKMC : K₁ * M ^ n < C := by
      have : 0 ≤ K₁ ^ n := pow_nonneg hK₁0 n
      linarith
    calc B i i ≤ K₁ * d i := hB_diag_upper i
      _ ≤ K₁ * (M ^ n * d j) := mul_le_mul_of_nonneg_left (hd_ratio i j hij.le) hK₁0
      _ = (K₁ * M ^ n) * d j := by ring
      _ ≤ (K₁ * M ^ n) * B j j := mul_le_mul_of_nonneg_left (hd_le_B j) (by positivity)
      _ < C * B j j := mul_lt_mul_of_pos_right hKMC (hB_pos j)
  · have hKnC : K₁ ^ n < C := by
      have : 0 ≤ K₁ * M ^ n := by positivity
      linarith
    have hdet_pos : 0 < ∏ i, d i := Finset.prod_pos fun i _ ↦ hd i
    rw [hN.det_transpose_mul_diagonal_mul d]
    calc (∏ i, B i i)
        ≤ ∏ i, (K₁ * d i) :=
          Finset.prod_le_prod₀ (fun i _ ↦ (hB_pos i).le) fun i _ ↦ hB_diag_upper i
      _ = K₁ ^ n * ∏ i, d i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ < C * ∏ i, d i := mul_lt_mul_of_pos_right hKnC hdet_pos

end OrderedCommRing

section Real

/-- **Uniform `LDL` coordinate bounds for `C`-Siegel reduced positive-definite real matrices.** -/
theorem PosDef.exists_ldl_bound_of_isSiegelReduced (n : ℕ) (C : ℝ) :
    ∃ Bnd : ℝ, 0 ≤ Bnd ∧
      ∀ (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef), B.IsSiegelReduced C →
        (∀ i j, i < j → |LDL.lower hB j i| ≤ Bnd) ∧
        (∀ i j, i < j → LDL.diagEntries hB i ≤ Bnd * LDL.diagEntries hB j) ∧
        (∀ i, B i i < C * LDL.diagEntries hB i) := by
  obtain ⟨Bnd, hBnd0, hBnd⟩ := IsSiegelReduced.exists_upperUnitriangular_bound n C
  refine ⟨Bnd, hBnd0, fun B hB hred ↦ ?_⟩
  let N : Matrix (Fin n) (Fin n) ℝ := (LDL.lower hB)ᵀ
  have hN : N.IsUpperUnitriangular :=
    (isUpperUnitriangular_def N).mpr
      ⟨(LDL.isLowerTriangular_lower hB).transpose, fun i ↦ by simp [N, LDL.lower_apply_diag]⟩
  have hB_eq : Nᵀ * diagonal (LDL.diagEntries hB) * N = B := by
    simpa [N, LDL.diag] using LDL.lower_conj_diag hB
  have hred' : (Nᵀ * diagonal (LDL.diagEntries hB) * N).IsSiegelReduced C := by
    rwa [hB_eq]
  obtain ⟨h1, h2, h3⟩ := hBnd N (LDL.diagEntries hB) hN (LDL.diagEntries_pos hB) hred'
  exact ⟨fun i j hij ↦ by simpa [N] using h1 i j hij, h2, fun i ↦ by simpa [hB_eq] using h3 i⟩

end Real

end Matrix
