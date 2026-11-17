/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import TauCeti.AlgebraicTopology.RationalHomotopy.FreeGradedCommutative.SignedSym
public import TauCeti.AlgebraicTopology.RationalHomotopy.Sullivan.Basic

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Basic
import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Derivation

/-!
# Concrete examples of Sullivan, minimal, non-minimal, and non-Sullivan DG algebras

This file constructs standard benchmark DG algebras on `TauCeti.SignedSym` and verifies their
Sullivan and minimality properties:

* `TauCeti.isMinimalSullivanAlgebra_oddSphere`: the odd sphere model `Λ(x₃)` with zero
  differential is minimal Sullivan.
* `TauCeti.exists_isMinimalSullivanAlgebra_evenSphere`: the even sphere model `Λ(x₂, y₃)` with
  `dx = 0` and `dy = x²` is minimal Sullivan, admits a DG map `x ↦ s, y ↦ 0` to any
  graded-commutative algebra with zero differential and `s² = 0`, and admits no DG map to `R[X]`
  sending `x ↦ X`.
* `TauCeti.exists_isSullivanAlgebra_not_isMinimal`: the contractible algebra `Λ(v₂, u₁)` with
  `dv = 0` and `du = v` (`v < u`) is Sullivan but not minimal (its induced differential on
  indecomposables is nonzero).
* `TauCeti.exists_isDGAlgebra_decomposable_not_isSullivanAlgebra`: the cyclic algebra
  `Λ(x₁, y₁, z₁)` with `dx = yz, dy = zx, dz = xy` has a free underlying graded-commutative
  algebra and a decomposable differential, yet admits no Sullivan presentation at all.

## References

* K. Hess, *Rational homotopy theory: a brief introduction*, Contemporary Mathematics 436 (2007),
  Example 1.12.
* J. W. Morgan, *The algebraic topology of smooth algebraic varieties*, Publications Mathématiques
  de l'IHÉS 48 (1978), Section 5.
-/

public section

namespace TauCeti

universe u

variable (R : Type u) [CommRing R]

/-- The odd sphere model `Λ(x₃)` with zero differential is a minimal Sullivan algebra. -/
theorem isMinimalSullivanAlgebra_oddSphere [Invertible (2 : R)] :
    IsMinimalSullivanAlgebra
      (signedSymPiece (InternalGrading.finsupp R fun _ : Unit => (3 : ℤ)))
      (0 : SignedSym (InternalGrading.finsupp R fun _ : Unit => (3 : ℤ)) →ₗ[R]
        SignedSym (InternalGrading.finsupp R fun _ : Unit => (3 : ℤ)))
      (freeGradedCommutativeGen R fun _ : Unit => 3) (fun _ : Unit => 3) where
  toIsFreeGradedCommutative := isFreeGradedCommutative_signedSym R (fun _ : Unit => 3)
  deg_pos _ := by omega
  d_mem_adjoin _ := zero_mem _
  d_mem_mul _ := zero_mem _

/-- The degree assignment `|x| = 2, |y| = 3` for the `S²` minimal model `Λ(x₂, y₃)`. -/
private abbrev evenSphereDeg : Fin 2 → ℕ :=
  fun i => if i = 0 then 2 else 3

/-- The generator map sending `x ↦ 0` and `y ↦ x²` on `Λ(x₂, y₃)`. -/
private noncomputable def evenSphereDelta :
    (Fin 2 →₀ R) →ₗ[R] SignedSym (InternalGrading.finsupp R fun i => (evenSphereDeg i : ℤ)) :=
  Finsupp.lsum R fun i =>
    LinearMap.toSpanSingleton R _ <|
      if i = 0 then 0
      else freeGradedCommutativeGen R evenSphereDeg 0 *
        freeGradedCommutativeGen R evenSphereDeg 0

private theorem evenSphereDelta_isHomogeneous :
    LinearMap.IsHomogeneous (evenSphereDelta R)
      (InternalGrading.finsupp R fun i => (evenSphereDeg i : ℤ)).piece
      (signedSymPiece (InternalGrading.finsupp R fun i => (evenSphereDeg i : ℤ))) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun p v hv => ?_
  rw [InternalGrading.finsupp_piece] at hv
  rw [← Finsupp.sum_single v, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hpi : (evenSphereDeg i : ℤ) = p := hv hi
  have hv_i : evenSphereDelta R (Finsupp.single i (v i)) =
      v i • (if i = 0 then 0 else
        freeGradedCommutativeGen R evenSphereDeg 0 *
          freeGradedCommutativeGen R evenSphereDeg 0) := by
    simp [evenSphereDelta]
  rw [hv_i]
  refine Submodule.smul_mem _ _ ?_
  have hi2 : i = 0 ∨ i = 1 := by omega
  rcases hi2 with rfl | rfl
  · simp
  · have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [h10, ↓reduceIte]
    have hx := freeGradedCommutativeGen_mem R evenSphereDeg 0
    have hmul := SetLike.mul_mem_graded hx hx
    have hdeg : ((evenSphereDeg 0 : ℤ) + evenSphereDeg 0) = p + 1 := by
      have hp3 : p = 3 := by simpa [evenSphereDeg, h10] using hpi.symm
      have h0 : evenSphereDeg 0 = 2 := by simp [evenSphereDeg]
      omega
    rwa [hdeg] at hmul

private noncomputable def evenSphereDiff :
    SignedSym (InternalGrading.finsupp R fun i => (evenSphereDeg i : ℤ)) →ₗ[R]
      SignedSym (InternalGrading.finsupp R fun i => (evenSphereDeg i : ℤ)) :=
  SignedSym.liftDerivation (evenSphereDelta R) (evenSphereDelta_isHomogeneous R)

private theorem evenSphereDiff_gen0 :
    evenSphereDiff R (freeGradedCommutativeGen R evenSphereDeg 0) = 0 := by
  rw [evenSphereDiff, freeGradedCommutativeGen_def, SignedSym.liftDerivation_generator]
  simp [evenSphereDelta]

private theorem evenSphereDiff_gen1 :
    evenSphereDiff R (freeGradedCommutativeGen R evenSphereDeg 1) =
      freeGradedCommutativeGen R evenSphereDeg 0 *
        freeGradedCommutativeGen R evenSphereDeg 0 := by
  rw [evenSphereDiff, freeGradedCommutativeGen_def, SignedSym.liftDerivation_generator]
  simp [evenSphereDelta]

private theorem isDGAlgebra_evenSphere :
    IsDGAlgebra (signedSymPiece (InternalGrading.finsupp R fun i => (evenSphereDeg i : ℤ)))
      (evenSphereDiff R) := by
  rw [evenSphereDiff, SignedSym.isDGAlgebra_liftDerivation_iff]
  intro v
  rw [← Finsupp.sum_single v, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hdelta : evenSphereDelta R (Finsupp.single i (v i)) =
      v i • (if i = 0 then 0 else
        freeGradedCommutativeGen R evenSphereDeg 0 *
          freeGradedCommutativeGen R evenSphereDeg 0) := by
    simp [evenSphereDelta]
  rw [hdelta, map_smul]
  have hi2 : i = 0 ∨ i = 1 := by omega
  rcases hi2 with rfl | rfl
  · simp
  · have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [h10, ↓reduceIte]
    have hx := freeGradedCommutativeGen_mem R evenSphereDeg 0
    rw [SignedSym.liftDerivation_mul (evenSphereDelta_isHomogeneous R) hx, ← evenSphereDiff,
      evenSphereDiff_gen0 R]
    simp [Units.smul_def]

/-- The even sphere model `Λ(x₂, y₃)` carries a DG differential with `dx = 0` and `dy = x²`
making it a minimal Sullivan algebra. Moreover, over a nontrivial ring, no algebra homomorphism
`Λ(x₂, y₃) → R[X]` sending `x ↦ X` commutes with the differentials (`d = 0` on `R[X]`), whereas
`x ↦ s, y ↦ 0` extends to a DG morphism into any graded-commutative algebra with zero differential
and `s ∈ ℬ 2` satisfying `s * s = 0`. -/
theorem exists_isMinimalSullivanAlgebra_evenSphere [Invertible (2 : R)] :
    ∃ (d : SignedSym (InternalGrading.finsupp R fun i : Fin 2 =>
          ((if i = 0 then (2 : ℕ) else 3 : ℕ) : ℤ)) →ₗ[R]
        SignedSym (InternalGrading.finsupp R fun i : Fin 2 =>
          ((if i = 0 then (2 : ℕ) else 3 : ℕ) : ℤ))),
      ∃ hA : IsDGAlgebra
        (signedSymPiece (InternalGrading.finsupp R fun i : Fin 2 =>
          ((if i = 0 then (2 : ℕ) else 3 : ℕ) : ℤ))) d,
        d (freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 3) 0) = 0 ∧
        d (freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 3) 1) =
          freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 3) 0 *
          freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 3) 0 ∧
        IsMinimalSullivanAlgebra
          (signedSymPiece (InternalGrading.finsupp R fun i : Fin 2 =>
            ((if i = 0 then (2 : ℕ) else 3 : ℕ) : ℤ)))
          d (freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 3))
          (fun i : Fin 2 => if i = 0 then 2 else 3) ∧
        (∀ {B : Type*} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ],
          (∀ {p q : ℤ} {a b : B}, a ∈ ℬ p → b ∈ ℬ q → a * b = (p * q).negOnePow • (b * a)) →
          ∀ {s : B}, s ∈ ℬ 2 → s * s = 0 →
            ∃ f : DGAlgHom hA (isDGAlgebra_zero ℬ),
              f (freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 3) 0) = s ∧
              f (freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 3) 1) = 0) ∧
        (∀ [Nontrivial R]
          (φ : SignedSym (InternalGrading.finsupp R fun i : Fin 2 =>
            ((if i = 0 then (2 : ℕ) else 3 : ℕ) : ℤ)) →ₐ[R] Polynomial R),
          φ (freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 3) 0) =
            Polynomial.X →
          ¬ (∀ a, (0 : Polynomial R →ₗ[R] Polynomial R) (φ a) = φ (d a))) := by
  refine ⟨evenSphereDiff R, isDGAlgebra_evenSphere R, evenSphereDiff_gen0 R,
    evenSphereDiff_gen1 R, ?_, ?_, ?_⟩
  · exact
      { toIsFreeGradedCommutative := isFreeGradedCommutative_signedSym R evenSphereDeg
        deg_pos := fun i => by
          have hi2 : i = 0 ∨ i = 1 := by omega
          rcases hi2 with rfl | rfl <;> decide
        d_mem_adjoin := fun i => by
          have hi2 : i = 0 ∨ i = 1 := by omega
          rcases hi2 with rfl | rfl
          · rw [evenSphereDiff_gen0]; exact zero_mem _
          · rw [evenSphereDiff_gen1]
            exact mul_mem (Algebra.subset_adjoin ⟨0, by decide, rfl⟩)
              (Algebra.subset_adjoin ⟨0, by decide, rfl⟩)
        d_mem_mul := fun i => by
          have hi2 : i = 0 ∨ i = 1 := by omega
          rcases hi2 with rfl | rfl
          · rw [evenSphereDiff_gen0]; exact zero_mem _
          · rw [evenSphereDiff_gen1]
            have hx : freeGradedCommutativeGen R evenSphereDeg 0 ∈
                positivePart (signedSymPiece
                  (InternalGrading.finsupp R fun i => (evenSphereDeg i : ℤ))) :=
              mem_positivePart_of_mem (by decide) (freeGradedCommutativeGen_mem R evenSphereDeg 0)
            exact Submodule.mul_mem_mul hx hx }
  · intro B _ _ ℬ _ hBc s hs hsq
    let b : Fin 2 → B := fun i => if i = 0 then s else 0
    have hb : ∀ i, b i ∈ ℬ (evenSphereDeg i) := fun i => by
      have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · simpa [b, evenSphereDeg] using hs
      · simp [b]
    have hfree := isFreeGradedCommutative_signedSym R evenSphereDeg
    have hd : ∀ i, (0 : B →ₗ[R] B) (b i) =
        hfree.lift b (fun j k => hBc (hb j) (hb k))
          (evenSphereDiff R (freeGradedCommutativeGen R evenSphereDeg i)) := fun i => by
      have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · simp [evenSphereDiff_gen0]
      · simp [evenSphereDiff_gen1, b, hsq]
    refine ⟨hfree.dgLift (isDGAlgebra_evenSphere R) (isDGAlgebra_zero ℬ) hBc b hb hd, ?_, ?_⟩
    · exact hfree.dgLift_apply (isDGAlgebra_evenSphere R) (isDGAlgebra_zero ℬ) hBc b hb hd 0
    · exact hfree.dgLift_apply (isDGAlgebra_evenSphere R) (isDGAlgebra_zero ℬ) hBc b hb hd 1
  · intro _ φ hφx h
    have hy := h (freeGradedCommutativeGen R evenSphereDeg 1)
    rw [LinearMap.zero_apply, evenSphereDiff_gen1, map_mul, hφx, ← sq] at hy
    have hcoeff := congrArg (fun p : Polynomial R => p.coeff 2) hy.symm
    simp only [Polynomial.coeff_X_pow, ↓reduceIte, Polynomial.coeff_zero] at hcoeff
    exact one_ne_zero hcoeff

/-- The degree assignment `|v| = 2, |u| = 1` (ordered `v < u`) for the non-minimal Sullivan
algebra `Λ(v₂, u₁)` with `dv = 0, du = v`. -/
private abbrev contractibleDeg : Fin 2 → ℕ :=
  fun i => if i = 0 then 2 else 1

private noncomputable def contractibleDelta :
    (Fin 2 →₀ R) →ₗ[R] SignedSym (InternalGrading.finsupp R fun i => (contractibleDeg i : ℤ)) :=
  Finsupp.lsum R fun i =>
    LinearMap.toSpanSingleton R _ <|
      if i = 0 then 0 else freeGradedCommutativeGen R contractibleDeg 0

private theorem contractibleDelta_isHomogeneous :
    LinearMap.IsHomogeneous (contractibleDelta R)
      (InternalGrading.finsupp R fun i => (contractibleDeg i : ℤ)).piece
      (signedSymPiece (InternalGrading.finsupp R fun i => (contractibleDeg i : ℤ))) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun p v hv => ?_
  rw [InternalGrading.finsupp_piece] at hv
  rw [← Finsupp.sum_single v, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hpi : (contractibleDeg i : ℤ) = p := hv hi
  have hv_i : contractibleDelta R (Finsupp.single i (v i)) =
      v i • (if i = 0 then 0 else freeGradedCommutativeGen R contractibleDeg 0) := by
    simp [contractibleDelta]
  rw [hv_i]
  refine Submodule.smul_mem _ _ ?_
  have hi2 : i = 0 ∨ i = 1 := by omega
  rcases hi2 with rfl | rfl
  · simp
  · have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [h10, ↓reduceIte]
    have hv0 := freeGradedCommutativeGen_mem R contractibleDeg 0
    have hdeg : (contractibleDeg 0 : ℤ) = p + 1 := by
      have hp1 : p = 1 := by simpa [contractibleDeg, h10] using hpi.symm
      have h0 : contractibleDeg 0 = 2 := by simp [contractibleDeg]
      omega
    rwa [hdeg] at hv0

private noncomputable def contractibleDiff :
    SignedSym (InternalGrading.finsupp R fun i => (contractibleDeg i : ℤ)) →ₗ[R]
      SignedSym (InternalGrading.finsupp R fun i => (contractibleDeg i : ℤ)) :=
  SignedSym.liftDerivation (contractibleDelta R) (contractibleDelta_isHomogeneous R)

private theorem contractibleDiff_gen0 :
    contractibleDiff R (freeGradedCommutativeGen R contractibleDeg 0) = 0 := by
  rw [contractibleDiff, freeGradedCommutativeGen_def, SignedSym.liftDerivation_generator]
  simp [contractibleDelta]

private theorem contractibleDiff_gen1 :
    contractibleDiff R (freeGradedCommutativeGen R contractibleDeg 1) =
      freeGradedCommutativeGen R contractibleDeg 0 := by
  rw [contractibleDiff, freeGradedCommutativeGen_def, SignedSym.liftDerivation_generator]
  simp [contractibleDelta]

private theorem isDGAlgebra_contractible :
    IsDGAlgebra (signedSymPiece (InternalGrading.finsupp R fun i => (contractibleDeg i : ℤ)))
      (contractibleDiff R) := by
  rw [contractibleDiff, SignedSym.isDGAlgebra_liftDerivation_iff]
  intro v
  rw [← Finsupp.sum_single v, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hdelta : contractibleDelta R (Finsupp.single i (v i)) =
      v i • (if i = 0 then 0 else freeGradedCommutativeGen R contractibleDeg 0) := by
    simp [contractibleDelta]
  rw [hdelta, map_smul]
  have hi2 : i = 0 ∨ i = 1 := by omega
  rcases hi2 with rfl | rfl
  · simp
  · have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [h10, ↓reduceIte]
    rw [← contractibleDiff, contractibleDiff_gen0 R, smul_zero]

/-- Over a nontrivial ring in which `2` is invertible, `Λ(v₂, u₁)` with `dv = 0` and `du = v`
(ordered `v < u`) is a Sullivan algebra that is not minimal, with nonzero induced differential on
indecomposables. -/
theorem exists_isSullivanAlgebra_not_isMinimal [Invertible (2 : R)] [Nontrivial R] :
    ∃ (d : SignedSym (InternalGrading.finsupp R fun i : Fin 2 =>
          ((if i = 0 then (2 : ℕ) else 1 : ℕ) : ℤ)) →ₗ[R]
        SignedSym (InternalGrading.finsupp R fun i : Fin 2 =>
          ((if i = 0 then (2 : ℕ) else 1 : ℕ) : ℤ))),
      ∃ hA : IsDGAlgebra
        (signedSymPiece (InternalGrading.finsupp R fun i : Fin 2 =>
          ((if i = 0 then (2 : ℕ) else 1 : ℕ) : ℤ))) d,
        d (freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 1) 0) = 0 ∧
        d (freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 1) 1) =
          freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 1) 0 ∧
        IsSullivanAlgebra
          (signedSymPiece (InternalGrading.finsupp R fun i : Fin 2 =>
            ((if i = 0 then (2 : ℕ) else 1 : ℕ) : ℤ)))
          d (freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 1))
          (fun i : Fin 2 => if i = 0 then 2 else 1) ∧
        ¬ IsMinimalSullivanAlgebra
          (signedSymPiece (InternalGrading.finsupp R fun i : Fin 2 =>
            ((if i = 0 then (2 : ℕ) else 1 : ℕ) : ℤ)))
          d (freeGradedCommutativeGen R (fun i : Fin 2 => if i = 0 then 2 else 1))
          (fun i : Fin 2 => if i = 0 then 2 else 1) ∧
        hA.indecomposablesDiff ≠ 0 := by
  have hsull : IsSullivanAlgebra
      (signedSymPiece (InternalGrading.finsupp R fun i => (contractibleDeg i : ℤ)))
      (contractibleDiff R) (freeGradedCommutativeGen R contractibleDeg) contractibleDeg :=
    { toIsFreeGradedCommutative := isFreeGradedCommutative_signedSym R contractibleDeg
      deg_pos := fun i => by
        have hi2 : i = 0 ∨ i = 1 := by omega
        rcases hi2 with rfl | rfl <;> decide
      d_mem_adjoin := fun i => by
        have hi2 : i = 0 ∨ i = 1 := by omega
        rcases hi2 with rfl | rfl
        · rw [contractibleDiff_gen0]; exact zero_mem _
        · rw [contractibleDiff_gen1]; exact Algebra.subset_adjoin ⟨0, by decide, rfl⟩ }
  have hnotmin : ¬ IsMinimalSullivanAlgebra
      (signedSymPiece (InternalGrading.finsupp R fun i => (contractibleDeg i : ℤ)))
      (contractibleDiff R) (freeGradedCommutativeGen R contractibleDeg) contractibleDeg := by
    intro hm
    have hmem : freeGradedCommutativeGen R contractibleDeg 0 ∈
        positivePart (signedSymPiece
          (InternalGrading.finsupp R fun i => (contractibleDeg i : ℤ))) *
        positivePart (signedSymPiece
          (InternalGrading.finsupp R fun i => (contractibleDeg i : ℤ))) :=
      contractibleDiff_gen1 R ▸ hm.d_mem_mul 1
    have hfree := isFreeGradedCommutative_signedSym R contractibleDeg
    have hpos : ∀ i, 0 < contractibleDeg i := fun i => by
      have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl <;> decide
    have h0 : hfree.indecomposablesBasis hpos 0 = 0 := by
      rw [hfree.indecomposablesBasis_apply hpos 0, Indecomposables.mk_eq_zero_iff]
      exact hmem
    exact (hfree.indecomposablesBasis hpos).ne_zero 0 h0
  refine ⟨contractibleDiff R, isDGAlgebra_contractible R, contractibleDiff_gen0 R,
    contractibleDiff_gen1 R, hsull, hnotmin, ?_⟩
  intro hdiff0
  exact hnotmin ((hsull.isMinimal_iff_indecomposablesDiff_eq_zero
    (isDGAlgebra_contractible R)).2 hdiff0)

/-- The cyclic generator map on `Λ(x₁, y₁, z₁)` sending `x ↦ yz`, `y ↦ zx`, `z ↦ xy`. -/
private noncomputable def cyclicDelta :
    (Fin 3 →₀ R) →ₗ[R] SignedSym (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ)) :=
  Finsupp.lsum R fun i =>
    LinearMap.toSpanSingleton R _ <|
      match i with
      | ⟨0, _⟩ => freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 1 *
          freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 2
      | ⟨1, _⟩ => freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 2 *
          freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 0
      | ⟨2, _⟩ => freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 0 *
          freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 1

private theorem cyclicDelta_isHomogeneous :
    LinearMap.IsHomogeneous (cyclicDelta R)
      (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ)).piece
      (signedSymPiece (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ))) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun p v hv => ?_
  rw [InternalGrading.finsupp_piece] at hv
  rw [← Finsupp.sum_single v, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hpi : ((1 : ℕ) : ℤ) = p := hv hi
  subst hpi
  have hg := freeGradedCommutativeGen_mem R (fun _ : Fin 3 => 1)
  have hmul : ∀ j k : Fin 3,
      freeGradedCommutativeGen R (fun _ : Fin 3 => 1) j *
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) k ∈
      signedSymPiece (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ))
        (((1 : ℕ) : ℤ) + 1) :=
    fun j k => SetLike.mul_mem_graded (hg j) (hg k)
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi3 with rfl | rfl | rfl <;>
    simpa [cyclicDelta] using Submodule.smul_mem _ (v _) (hmul _ _)

private noncomputable def cyclicDiff :
    SignedSym (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ)) →ₗ[R]
      SignedSym (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ)) :=
  SignedSym.liftDerivation (cyclicDelta R) (cyclicDelta_isHomogeneous R)

private theorem cyclicDiff_gen0 :
    cyclicDiff R (freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 0) =
      freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 1 *
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 2 := by
  rw [cyclicDiff, freeGradedCommutativeGen_def, SignedSym.liftDerivation_generator]
  simp [cyclicDelta]

private theorem cyclicDiff_gen1 :
    cyclicDiff R (freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 1) =
      freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 2 *
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 0 := by
  rw [cyclicDiff, freeGradedCommutativeGen_def, SignedSym.liftDerivation_generator]
  simp [cyclicDelta]

private theorem cyclicDiff_gen2 :
    cyclicDiff R (freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 2) =
      freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 0 *
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 1 := by
  rw [cyclicDiff, freeGradedCommutativeGen_def, SignedSym.liftDerivation_generator]
  simp [cyclicDelta]

private theorem isDGAlgebra_cyclic [Invertible (2 : R)] :
    IsDGAlgebra (signedSymPiece (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ)))
      (cyclicDiff R) := by
  have hfree := isFreeGradedCommutative_signedSym R (fun _ : Fin 3 => 1)
  have hsq : ∀ i : Fin 3,
      freeGradedCommutativeGen R (fun _ : Fin 3 => 1) i *
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) i = 0 :=
    fun i => hfree.sq_eq_zero_of_odd ⟨0, rfl⟩
  have hvan : ∀ i j : Fin 3,
      freeGradedCommutativeGen R (fun _ : Fin 3 => 1) i *
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) j *
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) i = 0 := fun i j => by
    rw [hfree.mul_comm i j, Units.smul_def, zsmul_eq_mul, mul_assoc, mul_assoc, hsq i, mul_zero,
      mul_zero]
  have hvan' : ∀ i j : Fin 3,
      freeGradedCommutativeGen R (fun _ : Fin 3 => 1) i *
        (freeGradedCommutativeGen R (fun _ : Fin 3 => 1) j *
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) i) = 0 := fun i j => by
    rw [← mul_assoc, hvan i j]
  rw [cyclicDiff, SignedSym.isDGAlgebra_liftDerivation_iff]
  intro v
  rw [← Finsupp.sum_single v, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hg := freeGradedCommutativeGen_mem R (fun _ : Fin 3 => 1)
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi3 with rfl | rfl | rfl
  · have hdelta : cyclicDelta R (Finsupp.single 0 (v 0)) =
        v 0 • (freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 1 *
          freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 2) := by
      simp [cyclicDelta]
    rw [hdelta, map_smul, SignedSym.liftDerivation_mul (cyclicDelta_isHomogeneous R) (hg 1),
      ← cyclicDiff, cyclicDiff_gen1 R, cyclicDiff_gen2 R, hvan 2 0, hvan' 1 0]
    simp [Units.smul_def]
  · have hdelta : cyclicDelta R (Finsupp.single 1 (v 1)) =
        v 1 • (freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 2 *
          freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 0) := by
      simp [cyclicDelta]
    rw [hdelta, map_smul, SignedSym.liftDerivation_mul (cyclicDelta_isHomogeneous R) (hg 2),
      ← cyclicDiff, cyclicDiff_gen2 R, cyclicDiff_gen0 R, hvan 0 1, hvan' 2 1]
    simp [Units.smul_def]
  · have hdelta : cyclicDelta R (Finsupp.single 2 (v 2)) =
        v 2 • (freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 0 *
          freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 1) := by
      simp [cyclicDelta]
    rw [hdelta, map_smul, SignedSym.liftDerivation_mul (cyclicDelta_isHomogeneous R) (hg 0),
      ← cyclicDiff, cyclicDiff_gen0 R, cyclicDiff_gen1 R, hvan 1 2, hvan' 0 2]
    simp [Units.smul_def]

/-- Over a nontrivial ring in which `2` is invertible, the cyclic DG algebra `Λ(x₁, y₁, z₁)` with
`dx = yz, dy = zx, dz = xy` has a free underlying graded-commutative algebra and a decomposable
differential `d (A⁺) ⊆ A⁺ · A⁺`, yet admits no Sullivan presentation at all. -/
theorem exists_isDGAlgebra_decomposable_not_isSullivanAlgebra [Invertible (2 : R)] [Nontrivial R] :
    ∃ (d : SignedSym (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ)) →ₗ[R]
        SignedSym (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ))),
      IsDGAlgebra (signedSymPiece (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ))) d ∧
      d (freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 0) =
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 1 *
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 2 ∧
      d (freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 1) =
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 2 *
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 0 ∧
      d (freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 2) =
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 0 *
        freeGradedCommutativeGen R (fun _ : Fin 3 => 1) 1 ∧
      (positivePart
          (signedSymPiece (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ)))).map d ≤
        positivePart (signedSymPiece (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ))) *
        positivePart (signedSymPiece (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ))) ∧
      ∀ {κ : Type*} [LinearOrder κ] [WellFoundedLT κ]
        (w : κ → SignedSym (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ)))
        (deg' : κ → ℕ),
        ¬ IsSullivanAlgebra
            (signedSymPiece (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ)))
            d w deg' := by
  refine ⟨cyclicDiff R, isDGAlgebra_cyclic R, cyclicDiff_gen0 R, cyclicDiff_gen1 R,
    cyclicDiff_gen2 R, ?_, ?_⟩
  · have hfree := isFreeGradedCommutative_signedSym R (fun _ : Fin 3 => 1)
    rw [hfree.map_positivePart_le_mul_iff (isDGAlgebra_cyclic R) (fun _ => by decide)]
    intro i
    have hm : ∀ j : Fin 3, freeGradedCommutativeGen R (fun _ : Fin 3 => 1) j ∈
        positivePart
          (signedSymPiece (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ))) :=
      fun j => hfree.mem_positivePart (fun _ => by decide) j
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi3 with rfl | rfl | rfl
    · rw [cyclicDiff_gen0]; exact Submodule.mul_mem_mul (hm 1) (hm 2)
    · rw [cyclicDiff_gen1]; exact Submodule.mul_mem_mul (hm 2) (hm 0)
    · rw [cyclicDiff_gen2]; exact Submodule.mul_mem_mul (hm 0) (hm 1)
  · intro κ _ _ w deg' hw
    let 𝒜 := signedSymPiece (InternalGrading.finsupp R fun _ : Fin 3 => ((1 : ℕ) : ℤ))
    let g := freeGradedCommutativeGen R (fun _ : Fin 3 => 1)
    have hfree := isFreeGradedCommutative_signedSym R (fun _ : Fin 3 => 1)
    -- `κ` must be nonempty because degree `1` is nontrivial.
    have hne : Nonempty κ := by
      by_contra hemp
      rw [not_nonempty_iff] at hemp
      have hbot : 𝒜 1 = ⊥ := by
        dsimp only [𝒜]
        rw [hw.grade_eq_span_standardMonomial 1, Submodule.span_eq_bot]
        rintro _ ⟨f, hfdeg, rfl⟩
        have hf0 : f.1 = 0 := by ext k; exact IsEmpty.elim hemp k
        rw [hf0, monomialDegree_zero] at hfdeg
        omega
      have hg0 : g 0 = 0 := by
        have hm : g 0 ∈ 𝒜 1 := freeGradedCommutativeGen_mem R (fun _ : Fin 3 => 1) 0
        exact (Submodule.mem_bot R).1 (hbot ▸ hm)
      have hne0 := hfree.basis.ne_zero (ExponentVector.single (deg := fun _ : Fin 3 => 1) 0)
      simp [ExponentVector.coe_single, g, hg0] at hne0
    -- Choose the minimal generator `k₀` of the supposed Sullivan presentation.
    let k₀ : κ := WellFounded.min wellFounded_lt Set.univ Set.univ_nonempty
    have hmin : ∀ j : κ, ¬ j < k₀ := fun j =>
      WellFounded.not_lt_min wellFounded_lt Set.univ (Set.mem_univ j)
    have hd0 : cyclicDiff R (w k₀) = 0 := hw.d_eq_zero_of_isMin (isDGAlgebra_cyclic R) hmin
    -- Every homogeneous element of degree `≥ 2` in `Λ(x₁, y₁, z₁)` is decomposable, so
    -- `deg' k₀ = 1`.
    have hdeg_le : deg' k₀ < 2 := by
      by_contra hge
      push Not at hge
      have hmem_mul : w k₀ ∈ positivePart 𝒜 * positivePart 𝒜 := by
        have hwk : w k₀ ∈ 𝒜 (deg' k₀ : ℤ) := hw.mem k₀
        dsimp only [𝒜] at hwk
        rw [hfree.grade_eq_span_standardMonomial (deg' k₀ : ℤ)] at hwk
        refine Submodule.span_induction (p := fun u _ => u ∈ positivePart 𝒜 * positivePart 𝒜)
          (fun u hu => ?_) (zero_mem _) (fun _ _ _ _ => add_mem)
          (fun r _ _ hu => Submodule.smul_mem _ r hu) hwk
        obtain ⟨f, hfdeg, rfl⟩ := hu
        have hwt : (f.1.sum fun _ n => n) = deg' k₀ := by
          have h2 : monomialDegree (fun _ : Fin 3 => 1) f.1 = deg' k₀ := Int.ofNat.inj hfdeg
          simpa [monomialDegree_def] using h2
        exact hfree.standardMonomial_mem_positivePart_mul_of_two_le_sum (fun _ => by decide)
          (by omega)
      have hzero : hw.toIsFreeGradedCommutative.indecomposablesBasis hw.deg_pos k₀ = 0 := by
        rw [hw.toIsFreeGradedCommutative.indecomposablesBasis_apply hw.deg_pos k₀,
          Indecomposables.mk_eq_zero_iff]
        exact hmem_mul
      exact (hw.toIsFreeGradedCommutative.indecomposablesBasis hw.deg_pos).ne_zero k₀ hzero
    have hdeg1 : deg' k₀ = 1 := by have := hw.deg_pos k₀; omega
    have hwk_ne : w k₀ ≠ 0 := by
      intro h0
      have hbasis0 := (hw.toIsFreeGradedCommutative.indecomposablesBasis hw.deg_pos).ne_zero k₀
      rw [hw.toIsFreeGradedCommutative.indecomposablesBasis_apply hw.deg_pos k₀] at hbasis0
      apply hbasis0
      rw [Indecomposables.mk_eq_zero_iff]
      simp [h0]
    -- Express `w k₀ ∈ 𝒜 1` as a linear combination of `g 0, g 1, g 2`.
    have hspan1 : 𝒜 1 ≤ Submodule.span R {g 0, g 1, g 2} := by
      dsimp only [𝒜]
      rw [hfree.grade_eq_span_standardMonomial 1, Submodule.span_le]
      rintro _ ⟨f, hfdeg, rfl⟩
      have hwt : (f.1.sum fun _ n => n) = 1 := by
        have h1 : monomialDegree (fun _ : Fin 3 => 1) f.1 = 1 := Int.ofNat.inj hfdeg
        simpa [monomialDegree_def] using h1
      obtain ⟨i, hfi⟩ := (Finsupp.sum_eq_one_iff f.1).1 hwt
      rw [hfi, standardMonomial_single, pow_one]
      have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi3 with rfl | rfl | rfl <;> exact Submodule.subset_span (by simp [g])
    have hwk1 : w k₀ ∈ Submodule.span R {g 0, g 1, g 2} := by
      have hmem1 : w k₀ ∈ 𝒜 1 := by
        have hwk : w k₀ ∈ 𝒜 (deg' k₀ : ℤ) := hw.mem k₀
        rwa [hdeg1] at hwk
      exact hspan1 hmem1
    rw [Submodule.mem_span_insert] at hwk1
    obtain ⟨c₀, u₁, hu₁, hwk_eq⟩ := hwk1
    rw [Submodule.mem_span_insert] at hu₁
    obtain ⟨c₁, u₂, hu₂, hu₁_eq⟩ := hu₁
    rw [Submodule.mem_span_singleton] at hu₂
    obtain ⟨c₂, rfl⟩ := hu₂
    subst hu₁_eq
    -- Compute `cyclicDiff R (w k₀)` in terms of the three distinct standard monomials
    -- `g 1 * g 2`, `g 0 * g 2`, `g 0 * g 1`.
    have hcomm20 : g 2 * g 0 = -(g 0 * g 2) := by
      simpa [Int.negOnePow_one, Units.smul_def] using hfree.mul_comm 2 0
    have hd_eq : c₀ • (g 1 * g 2) + (-c₁) • (g 0 * g 2) + c₂ • (g 0 * g 1) = 0 := by
      have h := hd0
      rw [hwk_eq, map_add, map_add, map_smul, map_smul, map_smul,
        cyclicDiff_gen0, cyclicDiff_gen1, cyclicDiff_gen2, hcomm20, smul_neg, ← neg_smul] at h
      simpa only [add_assoc] using h
    let e12 : ExponentVector (fun _ : Fin 3 => 1) :=
      ⟨Finsupp.single 1 1 + Finsupp.single 2 1, fun i _ => by
        have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi3 with rfl | rfl | rfl <;> simp⟩
    let e02 : ExponentVector (fun _ : Fin 3 => 1) :=
      ⟨Finsupp.single 0 1 + Finsupp.single 2 1, fun i _ => by
        have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi3 with rfl | rfl | rfl <;> simp⟩
    let e01 : ExponentVector (fun _ : Fin 3 => 1) :=
      ⟨Finsupp.single 0 1 + Finsupp.single 1 1, fun i _ => by
        have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi3 with rfl | rfl | rfl <;> simp⟩
    have hb12 : hfree.basis e12 = g 1 * g 2 := by
      rw [hfree.basis_apply, standardMonomial_add_of_lt g (fun a ha b hb => by
        have ha' : a = 1 := Finset.mem_singleton.1 (Finsupp.support_single_subset ha)
        have hb' : b = 2 := Finset.mem_singleton.1 (Finsupp.support_single_subset hb)
        subst ha'; subst hb'; decide)]
      simp
    have hb02 : hfree.basis e02 = g 0 * g 2 := by
      rw [hfree.basis_apply, standardMonomial_add_of_lt g (fun a ha b hb => by
        have ha' : a = 0 := Finset.mem_singleton.1 (Finsupp.support_single_subset ha)
        have hb' : b = 2 := Finset.mem_singleton.1 (Finsupp.support_single_subset hb)
        subst ha'; subst hb'; decide)]
      simp
    have hb01 : hfree.basis e01 = g 0 * g 1 := by
      rw [hfree.basis_apply, standardMonomial_add_of_lt g (fun a ha b hb => by
        have ha' : a = 0 := Finset.mem_singleton.1 (Finsupp.support_single_subset ha)
        have hb' : b = 1 := Finset.mem_singleton.1 (Finsupp.support_single_subset hb)
        subst ha'; subst hb'; decide)]
      simp
    have h12_02 : e12 ≠ e02 := fun h => by
      have := congrArg (fun e : ExponentVector (fun _ : Fin 3 => 1) => e.1 0) h
      simp [e12, e02] at this
    have h12_01 : e12 ≠ e01 := fun h => by
      have := congrArg (fun e : ExponentVector (fun _ : Fin 3 => 1) => e.1 0) h
      simp [e12, e01] at this
    have h02_01 : e02 ≠ e01 := fun h => by
      have := congrArg (fun e : ExponentVector (fun _ : Fin 3 => 1) => e.1 1) h
      simp [e02, e01] at this
    rw [← hb12, ← hb02, ← hb01] at hd_eq
    have hc0 : c₀ = 0 := by
      have h := congrArg (fun a => hfree.basis.repr a e12) hd_eq
      simp only [map_add, map_smul, map_zero, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_zero,
        Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, Module.Basis.repr_self,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne h12_02,
        Finsupp.single_eq_of_ne h12_01, mul_one, mul_zero, add_zero] at h
      exact h
    have hc1 : c₁ = 0 := by
      have h := congrArg (fun a => hfree.basis.repr a e02) hd_eq
      simp only [map_add, map_smul, map_zero, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_zero,
        Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, Module.Basis.repr_self,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne h12_02.symm,
        Finsupp.single_eq_of_ne h02_01, mul_one, mul_zero, add_zero, zero_add] at h
      exact neg_eq_zero.1 h
    have hc2 : c₂ = 0 := by
      have h := congrArg (fun a => hfree.basis.repr a e01) hd_eq
      simp only [map_add, map_smul, map_zero, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_zero,
        Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, Module.Basis.repr_self,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne h12_01.symm,
        Finsupp.single_eq_of_ne h02_01.symm, mul_one, mul_zero, zero_add] at h
      exact h
    exact hwk_ne (by simp [hwk_eq, hc0, hc1, hc2])

end TauCeti
