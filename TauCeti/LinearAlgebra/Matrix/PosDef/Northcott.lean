/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Order.Northcott
public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.Module.Primitive
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic

/-!
# Positive definiteness and Northcott finiteness on the integer lattice

A symmetric real matrix is positive definite if and only if its quadratic form has finite sublevel
sets on the integer lattice (`Matrix.IsSymm.posDef_iff_northcott`).

For `Northcott → PosDef`, a negative direction contradicts finiteness by scaling integer vectors
and density of rational vectors, while a real null direction gives infinitely many integer vectors
of bounded quadratic value by rounding its multiples. This criterion applies to Gram matrices of
height pairings, where finiteness is supplied by Northcott's theorem.

Conversely, over any archimedean linearly ordered field, a positive-definite matrix has the
Northcott property on the integer lattice (`Matrix.PosDef.northcott`): Cauchy–Schwarz against the
preimages of the standard basis vectors bounds each integer coordinate in terms of the quadratic
value. On a nonempty finite index type, a positive-definite form therefore attains its minimum on
the nonzero integer lattice at a primitive vector
(`Matrix.PosDef.exists_isPrimitive_forall_dotProduct_mulVec_le`).

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.9.
* [C. Hermite, *Extraits de lettres de M. Ch. Hermite à M. Jacobi sur différents objets de la
  théorie des nombres*], J. Reine Angew. Math. 40 (1850), 261–315.
-/

public section

namespace Matrix

open scoped Matrix

variable {ι : Type*} [Fintype ι]

/-- A symmetric real matrix is positive semidefinite if its quadratic form has the Northcott
property on the integer lattice. -/
theorem IsSymm.posSemidef_of_northcott {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    (hN : Northcott (fun z : ι → ℤ ↦
      (fun i ↦ (z i : ℝ)) ⬝ᵥ A *ᵥ (fun i ↦ (z i : ℝ)))) : A.PosSemidef := by
  classical
  let := hN
  let q : (ι → ℝ) → ℝ := fun x ↦ x ⬝ᵥ A *ᵥ x
  have hcont : Continuous q := by
    unfold q Matrix.mulVec dotProduct
    fun_prop
  have hsmul (t : ℝ) (x : ι → ℝ) : q (t • x) = t ^ 2 * q x := by
    simp [q, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two,
      mul_assoc]
  have hint (z : ι → ℤ) : 0 ≤ q (fun i ↦ (z i : ℝ)) := by
    by_contra hz
    have hzneg := lt_of_not_ge hz
    have hzne : z ≠ 0 := by
      intro h
      simp [h, q] at hzneg
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hzne
    have hfinite : (Set.univ : Set ℤ).Finite := by
      refine (Northcott.finite_le (h := fun z : ι → ℤ ↦ q (fun i ↦ (z i : ℝ))) 0).of_injOn
        (f := fun n : ℤ ↦ n • z) ?_ ?_
      · intro n _
        have heq : (fun i ↦ ((n • z) i : ℝ)) = (n : ℝ) • (fun i ↦ (z i : ℝ)) := by
          ext i
          simp
        simp only [Set.mem_ofPred_eq]
        rw [heq, hsmul]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hzneg.le
      · intro n _ m _ h
        exact mul_right_cancel₀ hi (by simpa using congrFun h i)
    exact Set.infinite_univ hfinite
  have hnonneg (x : ι → ℝ) : 0 ≤ q x := by
    refine (DenseRange.piMap (fun _ : ι ↦ Rat.denseRange_cast)).induction_on x
      (isClosed_le continuous_const hcont) ?_
    intro y
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors ℤ) y
    choose z hz using hd
    have heq : (fun i ↦ (z i : ℝ)) = (d : ℤ) • (fun i ↦ (y i : ℝ)) := by
      ext i
      simpa [Algebra.smul_def] using congrArg (fun r : ℚ ↦ (r : ℝ)) (hz i)
    have h := hint z
    rw [heq, ← Int.cast_smul_eq_zsmul ℝ, hsmul] at h
    exact nonneg_of_mul_nonneg_right h
      (sq_pos_of_ne_zero (by exact_mod_cast (nonZeroDivisors.ne_zero d.property)))
  refine PosSemidef.of_dotProduct_mulVec_nonneg (by simpa using hA) ?_
  simpa [q] using hnonneg

/-- A real matrix, not necessarily symmetric, whose quadratic form has the Northcott property on
the integer lattice has no nonzero real null vector. -/
theorem eq_zero_of_mulVec_eq_zero_of_northcott {A : Matrix ι ι ℝ}
    (hN : Northcott (fun z : ι → ℤ ↦
      (fun i ↦ (z i : ℝ)) ⬝ᵥ A *ᵥ (fun i ↦ (z i : ℝ))))
    {x : ι → ℝ} (hx : A *ᵥ x = 0) : x = 0 := by
  classical
  -- The symmetric part `S` of `A` has the same quadratic form, so it is positive semidefinite,
  -- and `x`, being isotropic for that form, is a null vector of `S`.
  obtain ⟨S, hS, hSN, hSx⟩ : ∃ S : Matrix ι ι ℝ, S.IsSymm ∧
      Northcott (fun z : ι → ℤ ↦ (fun i ↦ (z i : ℝ)) ⬝ᵥ S *ᵥ (fun i ↦ (z i : ℝ))) ∧
      S *ᵥ x = 0 := by
    let S : Matrix ι ι ℝ := (2⁻¹ : ℝ) • (A + Aᵀ)
    have hS : S.IsSymm := (isSymm_add_transpose_self A).smul _
    have hq (y : ι → ℝ) : y ⬝ᵥ S *ᵥ y = y ⬝ᵥ A *ᵥ y := by
      simp only [S, smul_mulVec, add_mulVec, mulVec_transpose, dotProduct_smul, dotProduct_add,
        dotProduct_comm y (y ᵥ* A), ← dotProduct_mulVec, smul_eq_mul]
      ring
    have hSN : Northcott (fun z : ι → ℤ ↦
        (fun i ↦ (z i : ℝ)) ⬝ᵥ S *ᵥ (fun i ↦ (z i : ℝ))) := by
      simpa only [hq] using hN
    refine ⟨S, hS, hSN, (hS.posSemidef_of_northcott hSN).dotProduct_mulVec_zero_iff.mp ?_⟩
    rw [star_trivial, hq, hx, dotProduct_zero]
  let := hSN
  let q : (ι → ℝ) → ℝ := fun x ↦ x ⬝ᵥ S *ᵥ x
  have hcont : Continuous q := by
    unfold q Matrix.mulVec dotProduct
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact
    (Set.Icc (fun _ : ι ↦ (-1 : ℝ)) 0)).bddAbove_image hcont.continuousOn
  have hs : Set.Finite {z : ι → ℤ | q (fun i ↦ (z i : ℝ)) ≤ C} :=
    Northcott.finite_le C
  let r : ℝ → ι → ℤ := fun t i ↦ ⌊t * x i⌋
  -- Rounding leaves an error in the compact cube [-1, 0]^ι. The null direction
  -- contributes neither a square term nor a cross term, by symmetry.
  have hr : ∀ t, r t ∈ {z : ι → ℤ | q (fun i ↦ (z i : ℝ)) ≤ C} := by
    intro t
    let e : ι → ℝ := (fun i ↦ (r t i : ℝ)) - t • x
    have he : e ∈ Set.Icc (fun _ : ι ↦ (-1 : ℝ)) 0 := by
      constructor <;> intro i
      · have := Int.lt_floor_add_one (t * x i)
        dsimp [e, r]
        linarith
      · exact sub_nonpos.mpr (Int.floor_le (t * x i))
    have hcross : x ⬝ᵥ S *ᵥ (fun i ↦ (r t i : ℝ)) = 0 := by
      rw [hS.dotProduct_mulVec_comm, hSx, dotProduct_zero]
    have hq : q e = q (fun i ↦ (r t i : ℝ)) := by
      simp [q, e, mulVec_sub, mulVec_smul, hSx, sub_dotProduct, smul_dotProduct, hcross]
    simpa only [Set.mem_ofPred_eq, hq] using hC (Set.mem_image_of_mem q he)
  ext i
  by_contra hi
  -- If a null vector has a nonzero coordinate, its rounded multiples attain every
  -- integer in that coordinate, contradicting the finite quadratic sublevel set.
  apply Set.infinite_univ (α := ℤ)
  refine (hs.image (fun z ↦ z i)).subset ?_
  intro z _
  refine ⟨r ((z : ℝ) / x i), hr _, ?_⟩
  simp [r, div_mul_cancel₀ _ hi]

/-- A symmetric real matrix is positive definite if its quadratic form has the Northcott
property on the integer lattice. No rationality assumption on its entries is needed. -/
theorem IsSymm.posDef_of_northcott {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    (hN : Northcott (fun z : ι → ℤ ↦
      (fun i ↦ (z i : ℝ)) ⬝ᵥ A *ᵥ (fun i ↦ (z i : ℝ)))) : A.PosDef := by
  classical
  apply (hA.posSemidef_of_northcott hN).posDef_iff_det_ne_zero.mpr
  intro hdet
  obtain ⟨v, hv, hAv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  exact hv (eq_zero_of_mulVec_eq_zero_of_northcott hN hAv)

/-- Over an archimedean strictly ordered commutative ring, the quadratic form of a
positive-definite matrix has the Northcott property on the integer lattice. -/
theorem PosDef.northcott {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] [StarRing R] {A : Matrix ι ι R} (hA : A.PosDef) :
    Northcott (fun z : ι → ℤ ↦ (fun i ↦ (z i : R)) ⬝ᵥ A *ᵥ (fun i ↦ (z i : R))) := by
  classical
  refine ⟨fun b ↦ ?_⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Set.toFinite _
  have := hA.trivialStar
  set F : LinearMap.BilinForm R (ι → R) := Matrix.toBilin' A
  have hF (x y : ι → R) : F x y = x ⬝ᵥ A *ᵥ y := Matrix.toBilin'_apply' A x y
  have hnonneg (x : ι → R) : 0 ≤ F x x := by
    simpa [hF] using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hsymm : LinearMap.IsSymm F :=
    LinearMap.BilinForm.isSymm_iff.mp (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA.isHermitian.isSymm)
  let u : ι → ι → R := fun k ↦ A.adjugate *ᵥ Pi.single k 1
  have hu (k : ι) : A *ᵥ u k = A.det • Pi.single k 1 := by
    rw [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
  obtain ⟨m, hm⟩ := Archimedean.arch 1 (pow_pos hA.det_pos 2)
  rw [nsmul_eq_mul] at hm
  obtain ⟨N, hN⟩ := exists_nat_ge ((m : R) * (max 0 b * ∑ k, F (u k) (u k)))
  refine (Finset.finite_toSet (Fintype.piFinset fun _ : ι ↦ Finset.Icc (-(N : ℤ)) N)).subset
    fun z hz ↦ Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun k ↦ Finset.mem_Icc.mpr ?_)
  have hzb : F (fun i ↦ (z i : R)) (fun i ↦ (z i : R)) ≤ max 0 b := by
    simpa [hF] using le_trans hz (le_max_right 0 b)
  have hdet_sq : (A.det * (z k : R)) ^ 2 ≤ max 0 b * ∑ j, F (u j) (u j) :=
    calc (A.det * (z k : R)) ^ 2 = F (fun i ↦ (z i : R)) (u k) ^ 2 := by
          rw [hF, hu, dotProduct_smul, dotProduct_single_one, smul_eq_mul, mul_comm]
      _ ≤ F (fun i ↦ (z i : R)) (fun i ↦ (z i : R)) * F (u k) (u k) :=
          F.apply_sq_le_of_symm hnonneg hsymm _ _
      _ ≤ max 0 b * ∑ j, F (u j) (u j) :=
          mul_le_mul hzb (Finset.single_le_sum (fun j _ ↦ hnonneg (u j)) (Finset.mem_univ k))
            (hnonneg _) (le_max_left 0 b)
  have hsq : ((z k) ^ 2 : R) ≤ (N : R) :=
    calc ((z k) ^ 2 : R) = 1 * (z k : R) ^ 2 := by simp
      _ ≤ ((m : R) * A.det ^ 2) * (z k : R) ^ 2 :=
          mul_le_mul_of_nonneg_right hm (sq_nonneg _)
      _ = (m : R) * (A.det * (z k : R)) ^ 2 := by ring
      _ ≤ (m : R) * (max 0 b * ∑ j, F (u j) (u j)) :=
          mul_le_mul_of_nonneg_left hdet_sq (Nat.cast_nonneg m)
      _ ≤ (N : R) := hN
  have habs : |z k| ≤ (N : ℤ) := by
    have hle : |z k| ≤ (z k) ^ 2 := by
      rcases eq_or_ne (z k) 0 with h0 | h0
      · simp [h0]
      · have : 1 ≤ |z k| := Int.one_le_abs h0
        nlinarith [sq_abs (z k)]
    have hcast : ((|z k| : ℤ) : R) ≤ (N : R) :=
      le_trans (by simpa using (Int.cast_le (R := R)).mpr hle) hsq
    exact_mod_cast hcast
  exact abs_le.mp habs

/-- A symmetric real matrix is positive definite if and only if its quadratic form has the
Northcott property on the integer lattice. -/
theorem IsSymm.posDef_iff_northcott {A : Matrix ι ι ℝ} (hA : A.IsSymm) :
    A.PosDef ↔ Northcott (fun z : ι → ℤ ↦
      (fun i ↦ (z i : ℝ)) ⬝ᵥ A *ᵥ (fun i ↦ (z i : ℝ))) :=
  ⟨PosDef.northcott, hA.posDef_of_northcott⟩

/-- On a nonempty finite index type, the quadratic form of a positive-definite matrix over an
archimedean strictly ordered commutative ring attains its minimum over nonzero integer vectors at a
primitive vector. -/
theorem PosDef.exists_isPrimitive_forall_dotProduct_mulVec_le [Nonempty ι] {R : Type*} [CommRing R]
    [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R] [StarRing R] {A : Matrix ι ι R}
    (hA : A.PosDef) :
    ∃ v : ι → ℤ, TauCeti.IsPrimitive v ∧ ∀ z : ι → ℤ, z ≠ 0 →
      (fun i ↦ (v i : R)) ⬝ᵥ A *ᵥ (fun i ↦ (v i : R)) ≤
        (fun i ↦ (z i : R)) ⬝ᵥ A *ᵥ (fun i ↦ (z i : R)) := by
  let := hA.northcott
  have := hA.trivialStar
  let q : (ι → ℤ) → R := fun z ↦ (fun i ↦ (z i : R)) ⬝ᵥ A *ᵥ (fun i ↦ (z i : R))
  have h1 : (1 : ι → ℤ) ≠ 0 := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    intro h
    simpa using congrFun h i₀
  obtain ⟨v, hv0, hmin⟩ := Northcott.exists_min_image q {z : ι → ℤ | z ≠ 0} ⟨1, h1⟩
  obtain ⟨d, w, hd, hw, rfl⟩ := TauCeti.exists_eq_zsmul_isPrimitive hv0
  have hwc : (fun i ↦ (w i : R)) ≠ 0 := fun h ↦
    hw.ne_zero (funext fun i ↦ Int.cast_eq_zero.mp (congrFun h i))
  have hwpos : 0 < q w := by simpa [q] using hA.dotProduct_mulVec_pos hwc
  have hscale : q (d • w) = (d : R) ^ 2 * q w := by
    have heq : (fun i ↦ ((d • w) i : R)) = (d : R) • (fun i ↦ (w i : R)) := by ext; simp
    dsimp only [q]
    rw [heq]
    simp [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, sq, mul_assoc]
  have hd1 : d = 1 := by
    have hle := hmin w hw.ne_zero
    rw [hscale] at hle
    have hsq : (d : R) ^ 2 ≤ 1 := le_of_mul_le_mul_right (by rwa [one_mul]) hwpos
    have hsqZ : d ^ 2 ≤ 1 := by exact_mod_cast hsq
    nlinarith
  exact ⟨(1 : ℤ) • w, by simpa using hw, fun z hz ↦ by simpa [hd1] using hmin z hz⟩

end Matrix
