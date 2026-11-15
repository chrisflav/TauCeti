/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import TauCeti.RingTheory.Ideal.AssociatedGraded

/-!
# The increasing `ℤ`-indexed `I`-adic filtration of a commutative ring

For an ideal `I` of a commutative semiring `R`, the powers `I ^ n` form a decreasing `ℕ`-indexed
filtration. Reindexing by negation and extending constantly by `R` in nonnegative degrees turns it
into an increasing, exhaustive, multiplicative `ℤ`-indexed filtration `Ideal.zFiltration I`:

* `I.zFiltration j = ⊤` for `0 ≤ j`, and
* `I.zFiltration (-n) = I ^ n` for `n : ℕ` (so `I.zFiltration j = I ^ (-j).toNat` for all `j : ℤ`).

This is the increasing `ℤ`-filtration attached to `I` in Mathlib's `IsRingFiltration` sense, with
strict filtration `j ↦ I.zFiltration (j - 1)`. Its Rees construction with respect to an inverse
parameter `t⁻¹` is the extended Rees algebra `R[It, t⁻¹]`.

Over a commutative ring `R`, the successive quotients `I.ZGradedPiece j = F_j ⧸ F_{j - 1}` vanish
for `0 < j`, while at nonpositive indices `-n` (`n : ℕ`) they canonically match the degree-`n`
pieces `I ^ n ⧸ I ^ (n + 1)` of `Ideal.AssociatedGraded I`. Summing over `ℤ` therefore gives an
`R`-linear equivalence `(⨁ j : ℤ, I.ZGradedPiece j) ≃ₗ[R] I.AssociatedGraded`.

## Main definitions

* `Ideal.zFiltration I`: the increasing `ℤ`-indexed `I`-adic filtration `j ↦ I ^ (-j).toNat`.
* `Ideal.ZGradedPiece I j`: the successive quotient `F_j ⧸ F_{j - 1}` at integer index `j`.
* `Ideal.zGradedPieceNegNatEquiv I n`: the `R`-linear isomorphism
  `I.ZGradedPiece (-n) ≃ₗ[R] I.GradedPiece n` identifying nonpositive filtration indices with
  nonnegative associated-graded degrees.
* `Ideal.zGradedDirectSumEquiv I`: the induced `R`-linear isomorphism
  `(⨁ j : ℤ, I.ZGradedPiece j) ≃ₗ[R] I.AssociatedGraded`.

## Main results

* `Ideal.zFiltration_mono`: `I.zFiltration` is `Monotone`.
* `Ideal.instGradedMonoidZFiltration` and `Ideal.instIsRingFiltrationZFiltration`: `I.zFiltration`
  is a `ℤ`-graded multiplicative ring filtration with strict piece `j ↦ I.zFiltration (j - 1)`.
* `Ideal.iSup_zFiltration` and `Ideal.iInf_zFiltration`: exhaustiveness (`⨆ j, F_j = ⊤`) and
  agreement of `⨅ j, F_j` with `⨅ n : ℕ, I ^ n`.
* `Ideal.map_zFiltration`: extension along a ring homomorphism commutes with `zFiltration`.
* `Ideal.subsingleton_zGradedPiece_of_pos`: the positive-index pieces `F_j ⧸ F_{j - 1}` (`0 < j`)
  are trivial.

## References

* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, GTM 150, §5.1 and §6.5.
* H. Matsumura, *Commutative Ring Theory*, Cambridge Studies in Advanced Mathematics 8, §15.
-/

public section

open scoped DirectSum

namespace Ideal

section Semiring

variable {R : Type*} [CommSemiring R] (I : Ideal R)

/-- The increasing `ℤ`-indexed `I`-adic filtration of `R`: `F_j = ⊤` for `0 ≤ j` and
`F_j = I ^ (-j).toNat` for `j < 0`. Both cases are given uniformly by `I ^ (-j).toNat`. -/
def zFiltration (j : ℤ) : Ideal R :=
  I ^ (-j).toNat

theorem zFiltration_def (j : ℤ) : I.zFiltration j = I ^ (-j).toNat :=
  (rfl)

/-- In nonnegative integer degrees, the increasing `I`-adic filtration equals the whole ring. -/
@[simp]
theorem zFiltration_of_nonneg {j : ℤ} (hj : 0 ≤ j) : I.zFiltration j = ⊤ := by
  rw [zFiltration_def, Int.toNat_of_nonpos (neg_nonpos.mpr hj), pow_zero, Ideal.one_eq_top]

theorem zFiltration_natCast (n : ℕ) : I.zFiltration (n : ℤ) = ⊤ :=
  I.zFiltration_of_nonneg (Nat.cast_nonneg n)

theorem zFiltration_zero : I.zFiltration 0 = ⊤ :=
  I.zFiltration_of_nonneg le_rfl

/-- At nonpositive integer index `-n` (`n : ℕ`), the filtration step is `I ^ n`. -/
@[simp]
theorem zFiltration_neg_natCast (n : ℕ) : I.zFiltration (-(n : ℤ)) = I ^ n := by
  rw [zFiltration_def, neg_neg, Int.toNat_natCast]

@[simp]
theorem zFiltration_neg_one : I.zFiltration (-1) = I := by
  simpa using I.zFiltration_neg_natCast 1

/-- At `-n - 1` (`n : ℕ`), the filtration step is `I ^ (n + 1)`. -/
theorem zFiltration_neg_natCast_sub_one (n : ℕ) :
    I.zFiltration (-(n : ℤ) - 1) = I ^ (n + 1) := by
  rw [sub_eq_add_neg, ← neg_add, ← Nat.cast_add_one, zFiltration_neg_natCast]

/-- The `ℤ`-indexed `I`-adic filtration is increasing. -/
theorem zFiltration_mono : Monotone I.zFiltration :=
  fun _ _ hij ↦ Ideal.pow_le_pow_right (Int.toNat_le_toNat (neg_le_neg hij))

/-- Reversing the sign of the index turns `I.zFiltration` into a decreasing `ℤ`-indexed family. -/
theorem zFiltration_antitone_neg : Antitone (fun d : ℤ ↦ I.zFiltration (-d)) :=
  fun _ _ h ↦ I.zFiltration_mono (neg_le_neg h)

/-- Pointwise multiplication respects the `ℤ`-indexed `I`-adic filtration: `1 ∈ F_0` and
`F_i * F_j ≤ F_{i + j}` for all `i, j : ℤ`. -/
instance instGradedMonoidZFiltration : SetLike.GradedMonoid I.zFiltration where
  one_mem := by simp
  mul_mem i j x y hx hy := by
    have hle : (-(i + j)).toNat ≤ (-i).toNat + (-j).toNat := by omega
    refine Ideal.pow_le_pow_right hle ?_
    rw [pow_add]
    exact Ideal.mul_mem_mul hx hy

/-- The `ℤ`-indexed `I`-adic filtration is a ring filtration in Mathlib's sense, with strict piece
`j ↦ I.zFiltration (j - 1)`. -/
instance instIsRingFiltrationZFiltration :
    IsRingFiltration I.zFiltration (fun j ↦ I.zFiltration (j - 1)) :=
  IsRingFiltration.mk_int I.zFiltration I.zFiltration_mono

/-- The `ℤ`-indexed `I`-adic filtration is exhaustive. -/
@[simp]
theorem iSup_zFiltration : ⨆ j : ℤ, I.zFiltration j = ⊤ :=
  eq_top_iff.mpr <| le_iSup_of_le 0 I.zFiltration_zero.ge

/-- The intersection of all steps of `I.zFiltration` agrees with `⨅ n : ℕ, I ^ n`. -/
theorem iInf_zFiltration : ⨅ j : ℤ, I.zFiltration j = ⨅ n : ℕ, I ^ n := by
  refine le_antisymm (le_iInf fun n ↦ iInf_le_of_le (-(n : ℤ)) (I.zFiltration_neg_natCast n).le)
    (le_iInf fun j ↦ ?_)
  rcases le_or_gt 0 j with hj | _
  · simp [I.zFiltration_of_nonneg hj]
  · exact iInf_le_of_le (-j).toNat le_rfl

/-- Extension of ideals along a ring homomorphism commutes with `zFiltration`. -/
theorem map_zFiltration {S : Type*} [CommSemiring S] (f : R →+* S) (j : ℤ) :
    (I.zFiltration j).map f = (I.map f).zFiltration j :=
  Ideal.map_pow f I (-j).toNat

variable {I} in
/-- A ring homomorphism carrying `I` into `J` carries each step `I.zFiltration j` into
`J.zFiltration j`. -/
theorem map_mem_zFiltration_of_le_comap {S : Type*} [CommSemiring S] {J : Ideal S}
    (f : R →+* S) (h : I ≤ J.comap f) {j : ℤ} {r : R} (hr : r ∈ I.zFiltration j) :
    f r ∈ J.zFiltration j := by
  have hmap : (I.zFiltration j).map f ≤ J.zFiltration j := by
    rw [I.map_zFiltration f j]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr h) (-j).toNat
  exact hmap (Ideal.mem_map_of_mem f hr)

end Semiring

section Ring

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The `j`-th successive quotient `F_j ⧸ F_{j - 1}` of the increasing `ℤ`-indexed `I`-adic
filtration. -/
abbrev ZGradedPiece (j : ℤ) :=
  ↥(I.zFiltration j) ⧸ Submodule.comap (I.zFiltration j).subtype (I.zFiltration (j - 1))

variable {I} in
/-- A representative `x ∈ F_j` vanishes in `I.ZGradedPiece j` precisely when `x ∈ F_{j - 1}`. -/
theorem zGradedPiece_mk_eq_zero_iff {j : ℤ} (x : ↥(I.zFiltration j)) :
    (Submodule.Quotient.mk x : I.ZGradedPiece j) = 0 ↔ (x : R) ∈ I.zFiltration (j - 1) := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]

/-- For strictly positive indices `0 < j`, both `F_j` and `F_{j - 1}` equal `R`, so the quotient
piece `I.ZGradedPiece j` is trivial. -/
theorem subsingleton_zGradedPiece_of_pos {j : ℤ} (hj : 0 < j) :
    Subsingleton (I.ZGradedPiece j) := by
  refine Subsingleton.intro fun a b ↦ ?_
  induction a using Submodule.Quotient.induction_on with | _ x =>
  induction b using Submodule.Quotient.induction_on with | _ y =>
  have hx0 : (Submodule.Quotient.mk x : I.ZGradedPiece j) = 0 := by
    rw [zGradedPiece_mk_eq_zero_iff, I.zFiltration_of_nonneg (Int.le_sub_one_of_lt hj)]
    exact Submodule.mem_top
  have hy0 : (Submodule.Quotient.mk y : I.ZGradedPiece j) = 0 := by
    rw [zGradedPiece_mk_eq_zero_iff, I.zFiltration_of_nonneg (Int.le_sub_one_of_lt hj)]
    exact Submodule.mem_top
  exact hx0.trans hy0.symm

private theorem map_comap_zFiltration_neg_natCast (n : ℕ) :
    (Submodule.comap (I.zFiltration (-(n : ℤ))).subtype (I.zFiltration (-(n : ℤ) - 1))).map
        (LinearEquiv.ofEq _ _ (I.zFiltration_neg_natCast n) :
          ↥(I.zFiltration (-(n : ℤ))) →ₗ[R] ↥(I ^ n)) =
      Submodule.comap (I ^ n).subtype (I ^ (n + 1)) := by
  ext x
  simp [I.zFiltration_neg_natCast_sub_one n]

/-- **Comparison at nonpositive indices.** At index `-n` (`n : ℕ`), the quotient piece
`F_{-n} ⧸ F_{-n - 1}` of the increasing `ℤ`-filtration is canonically `R`-linearly isomorphic to
the degree-`n` piece `I ^ n ⧸ I ^ (n + 1)` of `Ideal.AssociatedGraded I`. -/
noncomputable def zGradedPieceNegNatEquiv (n : ℕ) :
    I.ZGradedPiece (-(n : ℤ)) ≃ₗ[R] I.GradedPiece n :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (I.zFiltration_neg_natCast n))
    (I.map_comap_zFiltration_neg_natCast n)

@[simp]
theorem zGradedPieceNegNatEquiv_mk (n : ℕ) (x : ↥(I.zFiltration (-(n : ℤ)))) :
    I.zGradedPieceNegNatEquiv n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨x.1, I.zFiltration_neg_natCast n ▸ x.2⟩ :=
  (rfl)

@[simp]
theorem zGradedPieceNegNatEquiv_symm_mk (n : ℕ) (x : ↥(I ^ n)) :
    (I.zGradedPieceNegNatEquiv n).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨x.1, (I.zFiltration_neg_natCast n).symm ▸ x.2⟩ :=
  (rfl)

/-- Reindexing along `j ≤ 0` sends the quotient piece `F_j ⧸ F_{j - 1}` into degree `(-j).toNat`
of `Ideal.AssociatedGraded I`, and vanishes for `0 < j`. -/
private noncomputable def zGradedPieceToAssociatedGraded (j : ℤ) :
    I.ZGradedPiece j →ₗ[R] I.AssociatedGraded :=
  if hj : j ≤ 0 then
    (DirectSum.lof R ℕ I.GradedPiece (-j).toNat).comp <|
      Submodule.liftQ (Submodule.comap (I.zFiltration j).subtype (I.zFiltration (j - 1)))
        ((Submodule.mkQ (Submodule.comap (I ^ (-j).toNat).subtype (I ^ ((-j).toNat + 1)))).comp
          (LinearEquiv.ofEq _ _ (I.zFiltration_def j)).toLinearMap)
        fun x hx ↦ by
          rw [Submodule.mem_comap, Submodule.subtype_apply, zFiltration_def] at hx
          rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
            gradedPiece_mk_eq_zero_iff]
          have hnat : (-(j - 1)).toNat = (-j).toNat + 1 := by omega
          rwa [hnat] at hx
  else
    0

private theorem zGradedPieceToAssociatedGraded_of_pos {j : ℤ} (hj : 0 < j) :
    zGradedPieceToAssociatedGraded I j = 0 := by
  rw [zGradedPieceToAssociatedGraded]
  split_ifs with h
  · omega
  · rfl

private theorem zGradedPieceToAssociatedGraded_neg_natCast (n : ℕ) (q : I.ZGradedPiece (-(n : ℤ))) :
    zGradedPieceToAssociatedGraded I (-(n : ℤ)) q =
      DirectSum.of I.GradedPiece n (I.zGradedPieceNegNatEquiv n q) := by
  rw [zGradedPieceToAssociatedGraded]
  split_ifs with h
  · induction q using Submodule.Quotient.induction_on with | _ x =>
    rw [LinearMap.comp_apply, DirectSum.lof_eq_of, Submodule.liftQ_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, zGradedPieceNegNatEquiv_mk, ← AssociatedGraded.mk_apply,
      ← AssociatedGraded.mk_apply]
    exact AssociatedGraded.mk_congr (by simp) _
  · exact absurd (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) h

/-- **Direct-sum comparison.** Summing `Ideal.zGradedPieceNegNatEquiv` over nonpositive indices and
killing the subsingleton positive indices gives an `R`-linear isomorphism between the `ℤ`-indexed
associated graded module `⨁ j : ℤ, F_j ⧸ F_{j - 1}` and `Ideal.AssociatedGraded I`. -/
noncomputable def zGradedDirectSumEquiv :
    (⨁ j : ℤ, I.ZGradedPiece j) ≃ₗ[R] I.AssociatedGraded :=
  LinearEquiv.ofLinearMap
    (DirectSum.toModule R ℤ I.AssociatedGraded (zGradedPieceToAssociatedGraded I))
    (DirectSum.toModule R ℕ (⨁ j : ℤ, I.ZGradedPiece j) fun n ↦
      (DirectSum.lof R ℤ I.ZGradedPiece (-(n : ℤ))).comp
        (I.zGradedPieceNegNatEquiv n).symm.toLinearMap)
    (DirectSum.linearMap_ext R fun n ↦ LinearMap.ext fun q ↦ by
      simp [DirectSum.toModule_lof, zGradedPieceToAssociatedGraded_neg_natCast,
        ← DirectSum.lof_eq_of R])
    (DirectSum.linearMap_ext R fun j ↦ LinearMap.ext fun q ↦ by
      rcases le_or_gt j 0 with hj | hj
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
        subst hn
        simp [DirectSum.toModule_lof, zGradedPieceToAssociatedGraded_neg_natCast,
          ← DirectSum.lof_eq_of R]
      · have := I.subsingleton_zGradedPiece_of_pos hj
        rw [Subsingleton.elim q 0]
        simp)

@[simp]
theorem zGradedDirectSumEquiv_of_neg_natCast (n : ℕ) (q : I.ZGradedPiece (-(n : ℤ))) :
    I.zGradedDirectSumEquiv (DirectSum.of I.ZGradedPiece (-(n : ℤ)) q) =
      DirectSum.of I.GradedPiece n (I.zGradedPieceNegNatEquiv n q) := by
  simpa [zGradedDirectSumEquiv, ← DirectSum.lof_eq_of R] using
    zGradedPieceToAssociatedGraded_neg_natCast I n q

@[simp]
theorem zGradedDirectSumEquiv_of_pos {j : ℤ} (hj : 0 < j) (q : I.ZGradedPiece j) :
    I.zGradedDirectSumEquiv (DirectSum.of I.ZGradedPiece j q) = 0 := by
  simp [zGradedDirectSumEquiv, ← DirectSum.lof_eq_of R, zGradedPieceToAssociatedGraded_of_pos I hj]

@[simp]
theorem zGradedDirectSumEquiv_symm_of (n : ℕ) (q : I.GradedPiece n) :
    I.zGradedDirectSumEquiv.symm (DirectSum.of I.GradedPiece n q) =
      DirectSum.of I.ZGradedPiece (-(n : ℤ)) ((I.zGradedPieceNegNatEquiv n).symm q) := by
  simp [zGradedDirectSumEquiv, ← DirectSum.lof_eq_of R]

@[simp]
theorem zGradedDirectSumEquiv_symm_mk (n : ℕ) (x : ↥(I ^ n)) :
    I.zGradedDirectSumEquiv.symm (AssociatedGraded.mk I n x) =
      DirectSum.of I.ZGradedPiece (-(n : ℤ))
        (Submodule.Quotient.mk ⟨x.1, (I.zFiltration_neg_natCast n).symm ▸ x.2⟩) := by
  rw [AssociatedGraded.mk_apply, zGradedDirectSumEquiv_symm_of, zGradedPieceNegNatEquiv_symm_mk]

end Ring

end Ideal
