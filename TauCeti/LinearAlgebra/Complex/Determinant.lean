/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Real determinants of complex and real-linear maps

The real determinant of a real-linear endomorphism of the complex plane is the two-by-two
determinant of its values at `1` and `I` in the basis `(1,I)`.

The real determinant of a complex-linear endomorphism of a complex module is the squared modulus
of its complex determinant (`LinearMap.det_restrictScalars_eq_normSq`). In particular it is
nonnegative, and positive for complex-linear automorphisms; this is why complex-linear maps
preserve real orientations. As a consequence, every real-linear endomorphism squaring to `-id`
has determinant `1` (`LinearMap.det_eq_one_of_comp_self_eq_neg_id`).
-/

public section

namespace LinearMap

/-- The real determinant of a map on the complex plane, expressed in the basis `(1,I)`. -/
theorem det_complex (L : ℂ →ₗ[ℝ] ℂ) :
    L.det = (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]

/-- The real determinant of a complex-linear endomorphism is the squared modulus of its complex
determinant. -/
theorem det_restrictScalars_eq_normSq (f : E →ₗ[ℂ] E) :
    (f.restrictScalars ℝ).det = Complex.normSq f.det := by
  rw [det_restrictScalars, Algebra.norm_complex_apply]

/-- The real determinant of a complex-linear endomorphism is nonnegative. -/
theorem det_restrictScalars_nonneg (f : E →ₗ[ℂ] E) : 0 ≤ (f.restrictScalars ℝ).det := by
  rw [det_restrictScalars_eq_normSq]
  exact Complex.normSq_nonneg _

/-- A complex-linear endomorphism with nonzero complex determinant has positive real
determinant. -/
theorem det_restrictScalars_pos {f : E →ₗ[ℂ] E} (hf : f.det ≠ 0) :
    0 < (f.restrictScalars ℝ).det := by
  rw [det_restrictScalars_eq_normSq]
  exact Complex.normSq_pos.mpr hf

/-- A real-linear endomorphism squaring to `-id` has determinant `1`. Extending scalars via
`Complex.liftAux` realizes it as multiplication by `I` on a complex vector space, whose real
determinant is `|I ^ n|² = 1`. -/
theorem det_eq_one_of_comp_self_eq_neg_id {V : Type*} [AddCommGroup V] [Module ℝ V]
    {L : V →ₗ[ℝ] V} (hL : L ∘ₗ L = -LinearMap.id) : L.det = 1 := by
  let _ : Module ℂ V :=
    Module.compHom V (Complex.liftAux L (by
      simpa only [Module.End.mul_eq_comp, Module.End.one_eq_id] using hL)).toRingHom
  have : IsScalarTower ℝ ℂ V := .of_algebraMap_smul fun r v ↦ by
    rw [MulAction.compHom_smul_def, Module.End.smul_def]
    simp
  have hLI : ((Complex.I • (LinearMap.id : V →ₗ[ℂ] V)).restrictScalars ℝ) = L := by
    ext v
    simp [MulAction.compHom_smul_def, Module.End.smul_def]
  rw [← hLI, det_restrictScalars_eq_normSq]
  by_cases h : Module.Finite ℂ V
  · rw [LinearMap.det_smul, LinearMap.det_id, mul_one, map_pow, Complex.normSq_I, one_pow]
  · rw [LinearMap.det_eq_one_of_not_module_finite h, map_one]

end LinearMap

namespace LinearEquiv

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]

/-- A complex-linear automorphism has positive real determinant. -/
theorem det_restrictScalars_pos (f : E ≃ₗ[ℂ] E) :
    0 < LinearMap.det (f.restrictScalars ℝ : E →ₗ[ℝ] E) :=
  LinearMap.det_restrictScalars_pos (f := (f : E →ₗ[ℂ] E)) f.isUnit_det'.ne_zero

end LinearEquiv
