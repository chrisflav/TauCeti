/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Topology.Algebra.Star.Unitary
public import TauCeti.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Tactic.NormNum

/-!
# Unitary paths from spectral cuts

A unitary with nonnegative real part, and any self-adjoint unitary, is joined to the identity.
These continuous-functional-calculus paths supply the two factors of the reflection argument
for Hilbert-space unitaries. In addition, `Unitary.selfAdjointRotationPath` gives the explicit
exponential rotation path `t ↦ expUnitary ((t * π) • (2⁻¹ • (1 - u)))` from `1` to a self-adjoint
unitary `u`. They do not assert connectedness of the unitary group of a general C⋆-algebra.

The proofs of `Unitary.joined_one_of_nonneg_realPart` and `Unitary.joined_one_of_isSelfAdjoint` are
adapted from [AtiyahSinger/Analysis/FredholmPaths.lean][fredholm-paths] in Lean-Atiyah-Singer.
They supply the source formalization's supplementary reflection argument for the invertible
path connectedness used in *Spin Geometry*, III §7, Lemma 7.7, p. 203.

## References

* H. B. Lawson, Jr., and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38,
  Princeton University Press, 1989, Chapter III, §7, Lemma 7.7, p. 203,
  [DOI](https://doi.org/10.1515/9781400883912).
* B. Blackadar, *K-Theory for Operator Algebras*, second edition, Proposition 4.6.2.

[fredholm-paths]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/FredholmPaths.lean
-/

public section

open Complex
open scoped ComplexOrder ComplexStarModule unitInterval

/-- A unitary with nonnegative real part lies in the path component of the identity. -/
theorem Unitary.joined_one_of_nonneg_realPart
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (u : unitary A) (hu : 0 ≤ (ℜ (u : A) : A)) :
    Joined (1 : unitary A) u := by
  -- Positivity of the real part excludes the branch cut at -1.
  have hgap : -(1 : ℂ) ∉ spectrum ℂ (u : A) := by
    intro h
    have hmem : (-1 : ℝ) ∈ spectrum ℝ (ℜ (u : A) : A) := by
      rw [spectrum_realPart' (u : A) (by infer_instance)]
      exact ⟨-1, h, by simp⟩
    have hnonneg := spectrum_nonneg_of_nonneg hu hmem
    norm_num at hnonneg
  exact Unitary.joined 1 u ((Unitary.norm_sub_one_lt_two_iff u.property).mpr hgap)

/-- A self-adjoint unitary lies in the path component of the identity over the complex field. -/
theorem Unitary.joined_one_of_isSelfAdjoint
    {A : Type*} [CStarAlgebra A]
    (u : unitary A) (hu : IsSelfAdjoint (u : A)) : Joined (1 : unitary A) u := by
  let : PartialOrder A := CStarAlgebra.spectralOrder _
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
  -- Multiplication by i moves the spectrum {1,-1} away from the logarithm's cut.
  let w : unitary A := ⟨Complex.I • (1 : A), by
    constructor <;> simp [star_smul, smul_smul]⟩
  have hw : Joined (1 : unitary A) w := by
    apply Unitary.joined_one_of_nonneg_realPart
    dsimp only [w, Subtype.coe_mk]
    rw [realPart_apply_coe]
    simp [star_smul]
  have hwu : Joined (1 : unitary A) (w * u) := by
    apply Unitary.joined_one_of_nonneg_realPart
    simp only [Submonoid.coe_mul]
    dsimp only [w, Subtype.coe_mk]
    rw [realPart_apply_coe]
    simp [star_smul, hu.star_eq]
  simpa using hw.inv.mul hwu

/-- Explicit exponential rotation path `t ↦ expUnitary ((t * π) • (2⁻¹ • (1 - u)))` from `1` to a
self-adjoint unitary `u` in a unital C⋆-algebra. -/
noncomputable def Unitary.selfAdjointRotationPath {A : Type*} [CStarAlgebra A]
    {u : unitary A} (hu : IsSelfAdjoint (u : A)) : Path (1 : unitary A) u :=
  (selfAdjoint.expUnitaryPathToOne
    (Real.pi • ⟨(2⁻¹ : ℝ) • (1 - (u : A)),
      (Unitary.isStarProjection_inv_two_smul_one_sub hu).isSelfAdjoint⟩)).cast
    rfl (Unitary.expUnitary_pi_smul_inv_two_smul_one_sub hu).symm

@[simp]
theorem Unitary.selfAdjointRotationPath_apply {A : Type*} [CStarAlgebra A]
    {u : unitary A} (hu : IsSelfAdjoint (u : A)) (t : I) :
    Unitary.selfAdjointRotationPath hu t =
      selfAdjoint.expUnitary
        ((t : ℝ) • (Real.pi • ⟨(2⁻¹ : ℝ) • (1 - (u : A)),
          (Unitary.isStarProjection_inv_two_smul_one_sub hu).isSelfAdjoint⟩)) :=
  (rfl)

/-- Closed-form value of `Unitary.selfAdjointRotationPath` along `[0, 1]`. -/
theorem Unitary.coe_selfAdjointRotationPath_apply {A : Type*} [CStarAlgebra A]
    {u : unitary A} (hu : IsSelfAdjoint (u : A)) (t : I) :
    (Unitary.selfAdjointRotationPath hu t : A) =
      1 + (Complex.exp (Complex.I * ↑((t : ℝ) * Real.pi)) - 1) • ((2⁻¹ : ℝ) • (1 - (u : A))) := by
  rw [Unitary.selfAdjointRotationPath_apply, smul_smul]
  exact (Unitary.isStarProjection_inv_two_smul_one_sub hu).coe_expUnitary_smul ((t : ℝ) * Real.pi)
