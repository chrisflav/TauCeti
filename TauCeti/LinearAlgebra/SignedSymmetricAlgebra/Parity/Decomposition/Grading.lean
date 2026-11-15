/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegerGrading
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Decomposition.Basic
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.WordLength
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import TauCeti.Algebra.Algebra.Operations
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.TensorProduct.Submodule
import TauCeti.RingTheory.GradedAlgebra.Trivial

/-!
# Word-length and parity-grading compatibility of the parity decomposition

For `G : InternalGrading R V ℤ`, this file describes how the parity decomposition maps in
`TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Decomposition.Basic` interact with word length
(`TauCeti.SignedSym.lengthPiece G`) and parity (`TauCeti.parityGrading (signedSymPiece G)`). Over
any commutative ring `R`, we determine the exact images of `lengthPiece G n` and
`parityGrading (signedSymPiece G) k` under `toSymmetricEven`, `toExteriorOdd`, and
`toSymTensorExterior`; when `Invertible (2 : R)` holds, these yield `↔` membership characterizations
for `fromSymmetricEven`, `fromExteriorOdd`, `toSymTensorExterior`, and `fromSymTensorExterior`.

## Main results

* `TauCeti.SignedSym.toSymmetricEven_eq_zero_of_mem_parityGrading_one`,
  `map_lengthPiece_toSymmetricEven`, `fromSymmetricEven_mem_lengthPiece_iff`.
* `TauCeti.SignedSym.map_lengthPiece_toExteriorOdd`, `map_parityGrading_toExteriorOdd`,
  `fromExteriorOdd_mem_lengthPiece_iff`, `fromExteriorOdd_mem_parityGrading_iff`.
* `TauCeti.SignedSym.map_lengthPiece_toSymTensorExterior`,
  `toSymTensorExterior_mem_iSup_map₂_homogeneousSubmodule_exteriorPower_iff`,
  `map_parityGrading_toSymTensorExterior`, `toSymTensorExterior_mem_map₂_top_parityGrading_iff`.
-/

public section

open DirectSum
open scoped TensorProduct

namespace TauCeti

universe u v

namespace SignedSym

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable (G : InternalGrading R V ℤ)

/-! ### Compatibility of the factor inclusions and projections -/

/-- Every element in the image of `fromSymmetricEven` has even parity. -/
theorem fromSymmetricEven_mem_parityGrading_zero
    (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    fromSymmetricEven G s ∈ parityGrading (signedSymPiece G) 0 := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap r =>
    simpa only [AlgHom.commutes] using SetLike.algebraMap_mem_graded _ r
  | ι x => simpa only [fromSymmetricEven_ι] using generator_mem_parityGrading G x.2
  | mul _ _ ha hb => simpa only [map_mul, zero_add] using SetLike.mul_mem_graded ha hb
  | add _ _ ha hb => rw [map_add]; exact add_mem ha hb

/-- `fromSymmetricEven` carries homogeneous polynomials of degree `n` into word length `n`. -/
theorem fromSymmetricEven_mem_lengthPiece {n : ℕ}
    {s : SymmetricAlgebra R (parityGrading G.piece 0)}
    (hs : s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) n) :
    fromSymmetricEven G s ∈ lengthPiece G n :=
  lengthPiece_def G n ▸ (fromSymmetricEven G).apply_mem_pow_of_mem_pow
    (by rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x.1, by simp⟩) hs

/-- Over any commutative ring, `toSymmetricEven` annihilates elements of odd parity. -/
theorem toSymmetricEven_eq_zero_of_mem_parityGrading_one {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) 1) : toSymmetricEven G a = 0 := by
  let ℬ := parityGrading (trivialGrading R (SymmetricAlgebra R (parityGrading G.piece 0)))
  have hhom : LinearMap.IsHomogeneous (toSymmetricEven G).toLinearMap
      (parityGrading (signedSymPiece G)) ℬ 0 :=
    isHomogeneous_coarsenGrading_of_generator_mem G (Int.castAddHom (ZMod 2)) ℬ _ fun q x hx => by
      have hx' : x ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hx
      rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) (q : ZMod 2) with hq | hq <;>
        (simp only [Int.coe_castAddHom, hq]; rw [hq] at hx')
      · exact mem_parityGrading_of_mem (n := 0) (by simp)
      · rw [toSymmetricEven_generator_of_mem_parityGrading_one G hx']; exact zero_mem _
  have hbot : ℬ 1 = ⊥ := by
    rw [show ℬ 1 = parityGrading (trivialGrading R _) 1 from rfl, parityGrading_one]
    exact iSup_eq_bot.2 fun k => trivialGrading_eq_bot R _ (by omega)
  simpa [hbot] using hhom.map_mem ha

/-- `toSymmetricEven` maps `lengthPiece G n` onto the degree-`n` symmetric submodule. -/
theorem map_lengthPiece_toSymmetricEven (n : ℕ) :
    (lengthPiece G n).map (toSymmetricEven G).toLinearMap =
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) n := by
  rw [lengthPiece_def, TauCeti.SymmetricAlgebra.homogeneousSubmodule, Submodule.map_pow,
    ← LinearMap.range_comp]
  refine congrArg (· ^ n) (le_antisymm ?_ ?_)
  · rintro _ ⟨x, rfl⟩; exact ⟨DirectSum.decompose (parityGrading G.piece) x 0, by simp⟩
  · rintro _ ⟨x, rfl⟩; exact ⟨x.1, toSymmetricEven_generator_of_mem_parityGrading_zero G x.2⟩

/-- Over any commutative ring, `toSymmetricEven` preserves word length. -/
theorem toSymmetricEven_mem_homogeneousSubmodule {n : ℕ} {a : SignedSym G}
    (ha : a ∈ lengthPiece G n) : toSymmetricEven G a ∈
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) n :=
  map_lengthPiece_toSymmetricEven G n ▸ Submodule.mem_map_of_mem ha

/-- `fromSymmetricEven G s` has word length `n` iff `s` is homogeneous of degree `n`. -/
@[simp]
theorem fromSymmetricEven_mem_lengthPiece_iff {n : ℕ}
    {s : SymmetricAlgebra R (parityGrading G.piece 0)} :
    fromSymmetricEven G s ∈ lengthPiece G n ↔
      s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) n :=
  ⟨fun h => by simpa using toSymmetricEven_mem_homogeneousSubmodule G h,
    fromSymmetricEven_mem_lengthPiece G⟩

/-- `toExteriorOdd` maps `lengthPiece G n` onto the `n`-th exterior power of `V_odd`. -/
theorem map_lengthPiece_toExteriorOdd (n : ℕ) :
    (lengthPiece G n).map (toExteriorOdd G).toLinearMap = ⋀[R]^n (parityGrading G.piece 1) := by
  rw [lengthPiece_def, _root_.ExteriorAlgebra.exteriorPower, Submodule.map_pow,
    ← LinearMap.range_comp]
  refine congrArg (· ^ n) (le_antisymm ?_ ?_)
  · rintro _ ⟨x, rfl⟩; exact ⟨DirectSum.decompose (parityGrading G.piece) x 1, by simp⟩
  · rintro _ ⟨x, rfl⟩; exact ⟨x.1, toExteriorOdd_generator_of_mem_parityGrading_one G x.2⟩

/-- Over any commutative ring, `toExteriorOdd` maps word length `n` into `⋀[R]^n`. -/
theorem toExteriorOdd_mem_exteriorPower {n : ℕ} {a : SignedSym G} (ha : a ∈ lengthPiece G n) :
    toExteriorOdd G a ∈ ⋀[R]^n (parityGrading G.piece 1) :=
  map_lengthPiece_toExteriorOdd G n ▸ Submodule.mem_map_of_mem ha

/-- `toExteriorOdd` preserves parity with respect to `TauCeti.ExteriorAlgebra.integerGrading`. -/
theorem toExteriorOdd_mem_parityGrading {k : ZMod 2} {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) k) :
    toExteriorOdd G a ∈ parityGrading
      (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k := by
  have hhom := isHomogeneous_coarsenGrading_of_generator_mem G (Int.castAddHom (ZMod 2))
    (parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)))
    (toExteriorOdd G) fun q x hx => by
      have hx' : x ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hx
      rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) (q : ZMod 2) with hq | hq <;>
        (simp only [Int.coe_castAddHom, hq]; rw [hq] at hx')
      · rw [toExteriorOdd_generator_of_mem_parityGrading_zero G hx']; exact zero_mem _
      · rw [toExteriorOdd_generator_of_mem_parityGrading_one G hx']
        exact mem_parityGrading_of_mem (TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one
          (R := R) (⟨x, hx'⟩ : parityGrading G.piece 1))
  simpa only [add_zero, AlgHom.toLinearMap_apply] using hhom.map_mem ha

/-- `fromExteriorOdd` carries `n`-th exterior powers into word length `n`. -/
theorem fromExteriorOdd_mem_lengthPiece [Invertible (2 : R)] {n : ℕ}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)}
    (he : e ∈ ⋀[R]^n (parityGrading G.piece 1)) : fromExteriorOdd G e ∈ lengthPiece G n :=
  lengthPiece_def G n ▸ (fromExteriorOdd G).apply_mem_pow_of_mem_pow
    (by rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x.1, by simp⟩) he

/-- When `2` is invertible, `fromExteriorOdd G e` has word length `n` iff `e ∈ ⋀[R]^n`. -/
@[simp]
theorem fromExteriorOdd_mem_lengthPiece_iff [Invertible (2 : R)] {n : ℕ}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)} :
    fromExteriorOdd G e ∈ lengthPiece G n ↔ e ∈ ⋀[R]^n (parityGrading G.piece 1) :=
  ⟨fun h => by simpa using toExteriorOdd_mem_exteriorPower G h, fromExteriorOdd_mem_lengthPiece G⟩

/-! ### Exact image characterizations for word length and parity -/

private theorem exists_preimage_of_mem_exteriorPower {j : ℕ}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)}
    (he : e ∈ ⋀[R]^j (parityGrading G.piece 1)) :
    ∃ b, b ∈ lengthPiece G j ∧ b ∈ parityGrading (signedSymPiece G) (j : ZMod 2) ∧
      toExteriorOdd G b = e ∧ toSymTensorExterior G b = 1 ⊗ₜ[R] e := by
  rw [_root_.ExteriorAlgebra.exteriorPower] at he
  induction he using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    exact ⟨algebraMap R (SignedSym G) r, SetLike.algebraMap_mem_graded _ r,
      Nat.cast_zero (R := ZMod 2) ▸ SetLike.algebraMap_mem_graded _ r, AlgHom.commutes _ r,
      (AlgHom.commutes _ r).trans (Algebra.TensorProduct.includeRight.commutes r).symm⟩
  | add _ _ _ _ _ hx hy =>
    obtain ⟨bx, hbx_len, hbx_par, hbx_odd, hbx_eq⟩ := hx
    obtain ⟨by_, hby_len, hby_par, hby_odd, hby_eq⟩ := hy
    exact ⟨bx + by_, add_mem hbx_len hby_len, add_mem hbx_par hby_par,
      by simp [hbx_odd, hby_odd], by simp [hbx_eq, hby_eq, TensorProduct.tmul_add]⟩
  | mem_mul _ hy k _ _ hz =>
    rcases hy with ⟨x, rfl⟩; obtain ⟨b, hb_len, hb_par, hb_odd, hb_eq⟩ := hz
    exact ⟨generator G x.1 * b,
      by simpa [Nat.add_comm] using
        SetLike.mul_mem_graded (generator_mem_lengthPiece G x.1) hb_len,
      by simpa [add_comm] using SetLike.mul_mem_graded (generator_mem_parityGrading G x.2) hb_par,
      by simp [toExteriorOdd_generator_of_mem_parityGrading_one G x.2, hb_odd],
      by simp [toSymTensorExterior_generator_of_mem_parityGrading_one G x.2, hb_eq]⟩

private theorem exists_preimage_of_mem_parityGrading {k : ZMod 2}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)}
    (he : e ∈ parityGrading
      (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) :
    ∃ b, b ∈ parityGrading (signedSymPiece G) k ∧
      toExteriorOdd G b = e ∧ toSymTensorExterior G b = 1 ⊗ₜ[R] e := by
  refine coarsenGrading_induction he (fun q hq y hy => ?_) ⟨0, zero_mem _, map_zero _, by simp⟩
    (fun _ _ ⟨by_, hby_par, hby_odd, hby_eq⟩ ⟨bz, hbz_par, hbz_odd, hbz_eq⟩ =>
      ⟨by_ + bz, add_mem hby_par hbz_par, by simp [hby_odd, hbz_odd],
        by simp [hby_eq, hbz_eq, TensorProduct.tmul_add]⟩)
  rcases lt_or_ge q 0 with hqneg | hqnonneg
  · rw [TauCeti.ExteriorAlgebra.integerGrading_of_neg hqneg, Submodule.mem_bot] at hy
    subst hy; exact ⟨0, zero_mem _, map_zero _, by simp⟩
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hqnonneg
    rw [TauCeti.ExteriorAlgebra.integerGrading_natCast] at hy
    obtain ⟨b, -, hb_par, hb_odd, hb_eq⟩ := exists_preimage_of_mem_exteriorPower G hy
    exact ⟨b, (by simpa using hq : (j : ZMod 2) = k) ▸ hb_par, hb_odd, hb_eq⟩

/-- `toExteriorOdd` maps `parityGrading (signedSymPiece G) k` onto the parity-`k` exterior piece. -/
theorem map_parityGrading_toExteriorOdd (k : ZMod 2) :
    (parityGrading (signedSymPiece G) k).map (toExteriorOdd G).toLinearMap =
      parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k := by
  refine le_antisymm ?_ fun e he => ?_
  · rintro _ ⟨a, ha, rfl⟩; exact toExteriorOdd_mem_parityGrading G ha
  · obtain ⟨b, hb_par, hb_odd, -⟩ := exists_preimage_of_mem_parityGrading G he
    exact ⟨b, hb_par, hb_odd⟩

/-- `toSymTensorExterior` sends words of length `n` into the total-degree-`n` tensor pieces. -/
theorem toSymTensorExterior_mem_iSup_map₂_homogeneousSubmodule_exteriorPower {n : ℕ}
    {a : SignedSym G} (ha : a ∈ lengthPiece G n) :
    toSymTensorExterior G a ∈ ⨆ (i : ℕ) (j : ℕ) (_ : i + j = n),
      Submodule.map₂ (TensorProduct.mk R _ _)
        (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
        (⋀[R]^j (parityGrading G.piece 1)) := by
  let A := TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0)
  let E (j : ℕ) := ⋀[R]^j (parityGrading G.piece 1)
  let S (m : ℕ) := ⨆ (i : ℕ) (j : ℕ) (_ : i + j = m),
    Submodule.map₂ (TensorProduct.mk R _ _) (A i) (E j)
  have mem_S {i j m : ℕ} (hij : i + j = m) {z}
      (hz : z ∈ Submodule.map₂ (TensorProduct.mk R _ _) (A i) (E j)) : z ∈ S m :=
    Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hij hz))
  -- Total degree on the tensor product is submultiplicative: `S m₁ * S m₂ ≤ S (m₁ + m₂)`.
  have hS_mul {m₁ m₂ : ℕ} : S m₁ * S m₂ ≤ S (m₁ + m₂) := by
    simp only [S, Submodule.iSup_mul, Submodule.mul_iSup]
    refine iSup₂_le fun i₁ j₁ => iSup_le fun h₁ => iSup₂_le fun i₂ j₂ => iSup_le fun h₂ =>
      (Submodule.map₂_tmul_mul_le _ _ _ _).trans <| (Submodule.map₂_le_map₂
        (Submodule.mul_le.mpr fun _ ha _ hb => SetLike.mul_mem_graded ha hb)
        (Submodule.mul_le.mpr fun _ ha _ hb => SetLike.mul_mem_graded ha hb)).trans <|
        le_iSup₂_of_le (i₂ + i₁) (j₂ + j₁) (le_iSup_of_le (by omega) le_rfl)
  refine length_induction G (P := fun m a => toSymTensorExterior G a ∈ S m)
    (fun r => ?_) (fun _ _ _ ha hb => by rw [map_add]; exact add_mem ha hb) (fun m x a ih => ?_) ha
  · rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    exact mem_S (i := 0) (j := 0) rfl <| Submodule.apply_mem_map₂ _
      (SetLike.algebraMap_mem_graded A r) (SetLike.one_mem_graded E)
  · have hgen : toSymTensorExterior G (generator G x) ∈ S 1 := by
      rw [toSymTensorExterior_generator]
      exact add_mem
        (mem_S (i := 1) (j := 0) rfl <| Submodule.apply_mem_map₂ _
          (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule R _ _) (SetLike.one_mem_graded E))
        (mem_S (i := 0) (j := 1) rfl <| Submodule.apply_mem_map₂ _
          (SetLike.one_mem_graded A) (TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _))
    rw [map_mul, Nat.add_comm m 1]
    exact hS_mul (Submodule.mul_mem_mul hgen ih)

/-- `toSymTensorExterior` maps `lengthPiece G n` onto the total-degree-`n` tensor pieces. -/
theorem map_lengthPiece_toSymTensorExterior (n : ℕ) :
    (lengthPiece G n).map (toSymTensorExterior G).toLinearMap =
      ⨆ (i : ℕ) (j : ℕ) (_ : i + j = n),
        Submodule.map₂ (TensorProduct.mk R _ _)
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
          (⋀[R]^j (parityGrading G.piece 1)) := by
  refine le_antisymm ?_
    (iSup₂_le fun i j => iSup_le fun hij => Submodule.map₂_le.mpr fun s hs e he => ?_)
  · rintro _ ⟨a, ha, rfl⟩
    exact toSymTensorExterior_mem_iSup_map₂_homogeneousSubmodule_exteriorPower G ha
  · obtain ⟨b, hb_len, -, -, hb_eq⟩ := exists_preimage_of_mem_exteriorPower G he
    exact ⟨fromSymmetricEven G s * b,
      hij ▸ SetLike.mul_mem_graded (fromSymmetricEven_mem_lengthPiece G hs) hb_len, by simp [hb_eq]⟩

/-- When `2` is invertible, total degree `n` under `toSymTensorExterior` matches `lengthPiece`. -/
@[simp]
theorem toSymTensorExterior_mem_iSup_map₂_homogeneousSubmodule_exteriorPower_iff
    [Invertible (2 : R)] {n : ℕ} {a : SignedSym G} :
    toSymTensorExterior G a ∈ (⨆ (i : ℕ) (j : ℕ) (_ : i + j = n),
        Submodule.map₂ (TensorProduct.mk R _ _)
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
          (⋀[R]^j (parityGrading G.piece 1))) ↔
      a ∈ lengthPiece G n := by
  rw [← map_lengthPiece_toSymTensorExterior G n, ← symTensorExteriorEquiv_toLinearMap G,
    Submodule.mem_map_equiv]
  simp

/-- When `2` is invertible, `fromSymTensorExterior G z ∈ lengthPiece G n` iff total degree `n`. -/
@[simp]
theorem fromSymTensorExterior_mem_lengthPiece_iff [Invertible (2 : R)] {n : ℕ}
    {z : SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1)} :
    fromSymTensorExterior G z ∈ lengthPiece G n ↔
      z ∈ ⨆ (i : ℕ) (j : ℕ) (_ : i + j = n),
        Submodule.map₂ (TensorProduct.mk R _ _)
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
          (⋀[R]^j (parityGrading G.piece 1)) := by
  rw [← toSymTensorExterior_mem_iSup_map₂_homogeneousSubmodule_exteriorPower_iff G,
    toSymTensorExterior_fromSymTensorExterior]

/-- `toSymTensorExterior` sends parity-`k` elements to tensors of exterior parity `k`. -/
theorem toSymTensorExterior_mem_map₂_top_parityGrading {k : ZMod 2} {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) k) :
    toSymTensorExterior G a ∈ Submodule.map₂ (TensorProduct.mk R _ _)
      (⊤ : Submodule R (SymmetricAlgebra R (parityGrading G.piece 0)))
      (parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) := by
  let E := parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1))
  let ℬ (j : ZMod 2) := Submodule.map₂ (TensorProduct.mk R _ _)
    (⊤ : Submodule R (SymmetricAlgebra R (parityGrading G.piece 0))) (E j)
  have : SetLike.GradedOne ℬ :=
    ⟨Submodule.apply_mem_map₂ _ Submodule.mem_top (SetLike.one_mem_graded E)⟩
  have : SetLike.GradedMul ℬ := ⟨fun _ _ _ _ hu hv => ((Submodule.map₂_tmul_mul_le _ _ _ _).trans
    (Submodule.map₂_le_map₂ le_top (coarsenGrading_mul_le _ _ _ _))) (Submodule.mul_mem_mul hu hv)⟩
  have : SetLike.GradedMonoid ℬ := {}
  have hhom := isHomogeneous_coarsenGrading_of_generator_mem G (Int.castAddHom (ZMod 2)) ℬ
    (toSymTensorExterior G) fun q x hx => by
      have hx' : x ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hx
      rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) (q : ZMod 2) with hq | hq <;>
        (simp only [Int.coe_castAddHom, hq]; rw [hq] at hx')
      · rw [toSymTensorExterior_generator_of_mem_parityGrading_zero G hx']
        exact Submodule.apply_mem_map₂ _ Submodule.mem_top (SetLike.one_mem_graded _)
      · rw [toSymTensorExterior_generator_of_mem_parityGrading_one G hx']
        exact Submodule.apply_mem_map₂ _ Submodule.mem_top <| mem_parityGrading_of_mem
          (TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one (R := R)
            (⟨x, hx'⟩ : parityGrading G.piece 1))
  simpa only [add_zero, AlgHom.toLinearMap_apply] using hhom.map_mem ha

/-- `toSymTensorExterior` maps parity `k` onto tensors whose exterior factor has parity `k`. -/
theorem map_parityGrading_toSymTensorExterior (k : ZMod 2) :
    (parityGrading (signedSymPiece G) k).map (toSymTensorExterior G).toLinearMap =
      Submodule.map₂ (TensorProduct.mk R _ _)
        (⊤ : Submodule R (SymmetricAlgebra R (parityGrading G.piece 0)))
        (parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) := by
  refine le_antisymm ?_ (Submodule.map₂_le.mpr fun s _ e he => ?_)
  · rintro _ ⟨a, ha, rfl⟩; exact toSymTensorExterior_mem_map₂_top_parityGrading G ha
  · obtain ⟨b, hb_par, -, hb_eq⟩ := exists_preimage_of_mem_parityGrading G he
    exact ⟨fromSymmetricEven G s * b,
      zero_add k ▸ SetLike.mul_mem_graded (fromSymmetricEven_mem_parityGrading_zero G s) hb_par,
      by simp [hb_eq]⟩

/-- When `2` is invertible, exterior parity `k` under `toSymTensorExterior` matches parity `k`. -/
@[simp]
theorem toSymTensorExterior_mem_map₂_top_parityGrading_iff [Invertible (2 : R)]
    {k : ZMod 2} {a : SignedSym G} :
    toSymTensorExterior G a ∈ Submodule.map₂ (TensorProduct.mk R _ _)
        (⊤ : Submodule R (SymmetricAlgebra R (parityGrading G.piece 0)))
        (parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) ↔
      a ∈ parityGrading (signedSymPiece G) k := by
  rw [← map_parityGrading_toSymTensorExterior G k, ← symTensorExteriorEquiv_toLinearMap G,
    Submodule.mem_map_equiv]
  simp

/-- When `2` is invertible, `fromSymTensorExterior G z` has parity `k` iff exterior parity `k`. -/
@[simp]
theorem fromSymTensorExterior_mem_parityGrading_iff [Invertible (2 : R)] {k : ZMod 2}
    {z : SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1)} :
    fromSymTensorExterior G z ∈ parityGrading (signedSymPiece G) k ↔
      z ∈ Submodule.map₂ (TensorProduct.mk R _ _)
        (⊤ : Submodule R (SymmetricAlgebra R (parityGrading G.piece 0)))
        (parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) := by
  rw [← toSymTensorExterior_mem_map₂_top_parityGrading_iff G,
    toSymTensorExterior_fromSymTensorExterior]

/-- `fromExteriorOdd` preserves parity with respect to `TauCeti.ExteriorAlgebra.integerGrading`. -/
theorem fromExteriorOdd_mem_parityGrading [Invertible (2 : R)] {k : ZMod 2}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)}
    (he : e ∈ parityGrading
      (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) :
    fromExteriorOdd G e ∈ parityGrading (signedSymPiece G) k := by
  rw [← toSymTensorExterior_mem_map₂_top_parityGrading_iff G, toSymTensorExterior_fromExteriorOdd]
  exact Submodule.apply_mem_map₂ _ Submodule.mem_top he

/-- When `2` is invertible, `fromExteriorOdd G e` has parity `k` iff `e` has exterior parity `k`. -/
@[simp]
theorem fromExteriorOdd_mem_parityGrading_iff [Invertible (2 : R)] {k : ZMod 2}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)} :
    fromExteriorOdd G e ∈ parityGrading (signedSymPiece G) k ↔
      e ∈ parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k :=
  ⟨fun h => by simpa using toExteriorOdd_mem_parityGrading G h, fromExteriorOdd_mem_parityGrading G⟩

end SignedSym

end TauCeti
