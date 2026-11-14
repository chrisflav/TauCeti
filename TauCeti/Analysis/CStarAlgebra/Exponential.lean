/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# Exponential unitaries and projections

Let `A` be a complete normed complex algebra with a continuous star structure.

* For a self-adjoint element `h` of `A`, the adjoint of the unitary `selfAdjoint.expUnitary h` is
  `expUnitary (-h)` (`selfAdjoint.star_expUnitary`).
* For a star projection `p` and `t : ℝ`, `selfAdjoint.expUnitary (t • ⟨p, hp.isSelfAdjoint⟩)`
  evaluates in closed form to `1 + (Complex.exp (Complex.I * t) - 1) • p`
  (`IsStarProjection.coe_expUnitary_smul`), and at `t = π` to the reflection `1 - 2 * p`
  (`IsStarProjection.coe_expUnitary_pi_smul`).
* Conversely, if `u : unitary A` is self-adjoint, then `r = 2⁻¹ • (1 - u)` is a star projection
  (`Unitary.isStarProjection_inv_two_smul_one_sub`) satisfying `expUnitary (π • r) = u`
  (`Unitary.expUnitary_pi_smul_inv_two_smul_one_sub`), giving an explicit exponential path from `1`
  to `u` without continuous functional calculus.

## Main declarations

* `selfAdjoint.star_expUnitary`: the adjoint of `expUnitary`.
* `IsStarProjection.coe_expUnitary_smul`, `IsStarProjection.coe_expUnitary_pi_smul`: closed-form
  values of `expUnitary` on real multiples of a star projection.
* `Unitary.isStarProjection_inv_two_smul_one_sub`,
  `Unitary.expUnitary_pi_smul_inv_two_smul_one_sub`: every self-adjoint unitary is `expUnitary` at
  `π` of its spectral-minus projection `2⁻¹ • (1 - u)`.

## References

* O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second
  edition, Section 2.5.3, for the one-parameter group `t ↦ exp (ith)` of a self-adjoint element.
* B. Blackadar, *K-Theory for Operator Algebras*, second edition, Proposition 4.6.2, for the
  projection `2⁻¹ • (1 - w)` and rotation path `t ↦ exp (i π t r)` of a self-adjoint unitary.
-/

public section

noncomputable section

namespace selfAdjoint

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- The adjoint of `expUnitary` is `expUnitary` of the negative. -/
@[simp]
theorem star_expUnitary (b : selfAdjoint A) : star (expUnitary b) = expUnitary (-b) := by
  rw [Unitary.star_eq_inv, inv_eq_of_mul_eq_one_right]
  rw [← Commute.expUnitary_add (Commute.refl (b : A)).neg_right, add_neg_cancel, expUnitary_zero]

end selfAdjoint

namespace IsStarProjection

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- For a star projection `p` and `t : ℝ`, `expUnitary (t • p)` equals
`1 + (exp (I * t) - 1) • p`. -/
theorem coe_expUnitary_smul {p : A} (hp : IsStarProjection p) (t : ℝ) :
    (selfAdjoint.expUnitary (t • ⟨p, hp.isSelfAdjoint⟩) : A) =
      1 + (Complex.exp (Complex.I * t) - 1) • p := by
  rw [selfAdjoint.expUnitary_coe, selfAdjoint.val_smul, ← Complex.coe_smul, smul_smul,
    hp.isIdempotentElem.exp_smul, Complex.exp_eq_exp_ℂ]

/-- For a star projection `p`, `expUnitary p` equals `1 + (exp I - 1) • p`. -/
theorem coe_expUnitary {p : A} (hp : IsStarProjection p) :
    (selfAdjoint.expUnitary ⟨p, hp.isSelfAdjoint⟩ : A) = 1 + (Complex.exp Complex.I - 1) • p := by
  simpa using hp.coe_expUnitary_smul 1

/-- Exponentiating `π` times a star projection `p` yields the reflection `1 - 2 * p`. -/
theorem coe_expUnitary_pi_smul {p : A} (hp : IsStarProjection p) :
    (selfAdjoint.expUnitary (Real.pi • ⟨p, hp.isSelfAdjoint⟩) : A) = 1 - 2 * p := by
  rw [hp.coe_expUnitary_smul, mul_comm Complex.I, Complex.exp_pi_mul_I]
  norm_num [two_mul, two_smul, sub_eq_add_neg, add_assoc]

end IsStarProjection

namespace Unitary

/-- For a self-adjoint unitary `u`, `2⁻¹ • (1 - u)` is a star projection. -/
theorem isStarProjection_inv_two_smul_one_sub {R : Type*} [Ring R] [StarRing R] [Module ℝ R]
    [IsScalarTower ℝ R R] [SMulCommClass ℝ R R] [StarModule ℝ R] {u : unitary R}
    (hu : IsSelfAdjoint (u : R)) :
    IsStarProjection ((2⁻¹ : ℝ) • (1 - (u : R))) := by
  have hu2 : (u : R) * (u : R) = 1 := by
    simpa only [hu.star_eq] using Unitary.mul_star_self_of_mem u.prop
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, smul_mul_smul_comm]
    simp only [sub_mul, mul_sub, mul_one, one_mul, hu2]
    have hsub : 1 - (u : R) - ((u : R) - 1) = (2 : ℝ) • (1 - (u : R)) := by
      rw [two_smul]
      abel
    rw [hsub, smul_smul]
    norm_num
  · rw [IsSelfAdjoint, star_smul, star_sub, star_one, hu.star_eq, RCLike.star_def,
      RCLike.conj_to_real]

/-- Every self-adjoint unitary `u` in a complete normed complex star-algebra is `expUnitary` at
`π` of its spectral-minus projection `2⁻¹ • (1 - u)`. -/
theorem expUnitary_pi_smul_inv_two_smul_one_sub {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A] {u : unitary A}
    (hu : IsSelfAdjoint (u : A)) :
    selfAdjoint.expUnitary
        (Real.pi • ⟨(2⁻¹ : ℝ) • (1 - (u : A)),
          (isStarProjection_inv_two_smul_one_sub hu).isSelfAdjoint⟩) = u := by
  ext
  rw [(isStarProjection_inv_two_smul_one_sub hu).coe_expUnitary_pi_smul, two_mul, ← two_smul ℝ,
    smul_smul]
  norm_num

end Unitary

end
