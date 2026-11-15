/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic

/-!
# The geometric convention on real Clifford actions on Hermitian modules

Let `V` be a real inner product space, `Q` a quadratic form on `V`, and `S` a complex inner product
space carrying a real algebra homomorphism `ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S`; write
`c(v) = ρ (ι Q v)`. In spin geometry, `ρ` satisfies the **geometric convention**
(`AlgHom.IsGeometricClifford`) when

1. `Q v = -⟪v, v⟫_ℝ` (equivalently `Q v = -‖v‖ ^ 2`), and
2. each generator acts skew-Hermitianly: `⟪c(v) x, y⟫_ℂ = -⟪x, c(v) y⟫_ℂ`.

Polarizing `c(v)² = Q v` under `Q v = -⟪v, v⟫_ℝ` yields the anticommutator identity

  `c(v) c(w) + c(w) c(v) = (-2 * ⟪v, w⟫_ℝ) • 1`,

and combining this with skew-Hermitianness gives the polarized inner-product identity

  `⟪c(v) x, c(w) y⟫_ℂ + ⟪c(w) x, c(v) y⟫_ℂ = (2 * ⟪v, w⟫_ℝ : ℂ) * ⟪x, y⟫_ℂ`

together with norm scaling `‖c(v) x‖ = ‖v‖ * ‖x‖` without requiring `S` to be finite-dimensional.
In particular, every unit vector `u` defines a complex-linear isometric equivalence
`AlgHom.IsGeometricClifford.unitVectorIsometryEquiv` of `S` with inverse `-c(u)`.

For orthogonal vectors `u, v`, the bivector `c(u) c(v)` is skew-Hermitian and `i • (c(u) c(v))` is
symmetric and anticommutes with both `c(u)` and `c(v)`. When `‖u‖ = ‖v‖`, rotating `(u, v)` by
`(c • u + s • v, -s • u + c • v)` scales `c(u) c(v)` by `c ^ 2 + s ^ 2`, so oriented orthonormal
frame rotations leave `c(u) c(v)` invariant; when `‖u‖ = ‖v‖ = 1`, `i • (c(u) c(v))` is a
self-adjoint involution.

Extending `ρ` complex-linearly to `ρ.cliffordBaseChange ℂ` on `CliffordAlgebra (Q.baseChange ℂ)`
turns skew-Hermitianness on real vectors into `*-`compatibility with the conjugate-linear Clifford
involution `CliffordAlgebra.conjStar`. Finally, `AlgHom.IsGeometricClifford` is preserved by
isometric pullbacks, unitary conjugations, ungraded tensor twists `S ⊗[ℂ] W` and `W ⊗[ℂ] S`, and
graded tensor products `E ⊗[ℂ] F` over `L²` orthogonal sums `WithLp 2 (V₁ × V₂)`.

## Main definitions

* `AlgHom.IsGeometricClifford`: the geometric sign and skew-Hermitian convention on a real algebra
  map `CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S`.
* `AlgHom.IsGeometricClifford.unitVectorIsometryEquiv`: Clifford multiplication by a unit vector as
  a complex-linear isometric equivalence `S ≃ₗᵢ[ℂ] S`.
* `AlgHom.cliffordComplexProdTensor`: the graded tensor product of real Clifford actions on complex
  modules `E ⊗[ℂ] F`.

## Main results

* `CliffordAlgebra.ι_mul_ι_add_swap_eq_neg_two_inner`, `CliffordAlgebra.map_ι_mul_map_ι_add_swap`:
  the polarized anticommutator `c(v) c(w) + c(w) c(v) = (-2 * ⟪v, w⟫_ℝ) • 1`.
* `CliffordAlgebra.map_ι_rot_mul_map_ι_rot_of_eq_one`: `SO(2)` rotation invariance of the
  bivector `c(u) c(v)` of an orthogonal equal-norm pair.
* `AlgHom.inner_cliffordBaseChange_eq_conjStar_iff`,
  `AlgHom.adjoint_cliffordBaseChange_eq_conjStar_iff`: `ρ.cliffordBaseChange ℂ` is compatible with
  `CliffordAlgebra.conjStar` iff real vectors act skew-Hermitianly.
* `AlgHom.IsGeometricClifford.inner_map_ι_add_swap`,
  `AlgHom.IsGeometricClifford.norm_map_ι_apply`: polarized inner-product identity and norm scaling.
* `AlgHom.IsGeometricClifford.rTensor`, `AlgHom.IsGeometricClifford.lTensor`,
  `AlgHom.IsGeometricClifford.complexProdTensor`: preservation under ungraded and graded tensor
  products.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., §12.1.2, Definition 12.1.10.
-/

public section

open scoped InnerProductSpace TensorProduct ComplexConjugate

namespace CliffordAlgebra

section Polarization

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}

/-- For `Q v = -⟪v, v⟫_ℝ`, the polar form of `Q` is `-2 * ⟪v, w⟫_ℝ`. -/
theorem polar_eq_neg_two_inner (hQ : ∀ v, Q v = -⟪v, v⟫_ℝ) (v w : V) :
    QuadraticMap.polar Q v w = -2 * ⟪v, w⟫_ℝ := by
  simp only [QuadraticMap.polar, hQ, inner_add_left, inner_add_right, real_inner_comm w v]
  ring

/-- **Polarized Clifford relation**: when `Q v = -⟪v, v⟫_ℝ`,
`ι v * ι w + ι w * ι v = -2 ⟪v, w⟫_ℝ`. -/
theorem ι_mul_ι_add_swap_eq_neg_two_inner (hQ : ∀ v, Q v = -⟪v, v⟫_ℝ) (v w : V) :
    ι Q v * ι Q w + ι Q w * ι Q v = algebraMap ℝ (CliffordAlgebra Q) (-2 * ⟪v, w⟫_ℝ) := by
  rw [ι_mul_ι_add_swap, polar_eq_neg_two_inner hQ]

section Module

variable {K W : Type*} [CommRing K] [Algebra ℝ K] [AddCommGroup W] [Module K W] [Module ℝ W]
  [IsScalarTower ℝ K W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End K W)

/-- **Polarized anticommutator in a Clifford module**: when `Q v = -⟪v, v⟫_ℝ`,
`c(v) c(w) + c(w) c(v) = (-2 * ⟪v, w⟫_ℝ) • 1`. -/
theorem map_ι_mul_map_ι_add_swap (hQ : ∀ v, Q v = -⟪v, v⟫_ℝ) (v w : V) :
    ρ (ι Q v) * ρ (ι Q w) + ρ (ι Q w) * ρ (ι Q v) = (-2 * ⟪v, w⟫_ℝ) • 1 := by
  rw [← map_mul ρ, ← map_mul ρ, ← map_add ρ, ι_mul_ι_add_swap_eq_neg_two_inner hQ,
    AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

/-- Pointwise form of `CliffordAlgebra.map_ι_mul_map_ι_add_swap`. -/
theorem map_ι_apply_map_ι_apply_add_swap (hQ : ∀ v, Q v = -⟪v, v⟫_ℝ) (v w : V) (ψ : W) :
    ρ (ι Q v) (ρ (ι Q w) ψ) + ρ (ι Q w) (ρ (ι Q v) ψ) = (-2 * ⟪v, w⟫_ℝ) • ψ := by
  have h := congr($(map_ι_mul_map_ι_add_swap ρ hQ v w) ψ)
  simpa only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.smul_apply,
    one_apply_eq_self] using h

/-- Orthogonal vectors anticommute in any Clifford module when `Q v = -⟪v, v⟫_ℝ`. -/
theorem map_ι_mul_map_ι_of_inner_eq_zero (hQ : ∀ v, Q v = -⟪v, v⟫_ℝ) {v w : V}
    (hvw : ⟪v, w⟫_ℝ = 0) :
    ρ (ι Q v) * ρ (ι Q w) = -(ρ (ι Q w) * ρ (ι Q v)) := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [map_ι_mul_map_ι_add_swap ρ hQ, hvw, mul_zero, zero_smul]

/-- A unit vector squares to `-1` in any Clifford module when `Q v = -⟪v, v⟫_ℝ`. -/
theorem map_ι_mul_map_ι_of_norm_eq_one (hQ : ∀ v, Q v = -⟪v, v⟫_ℝ) {u : V} (hu : ‖u‖ = 1) :
    ρ (ι Q u) * ρ (ι Q u) = -1 := by
  rw [← map_mul ρ, ι_sq_scalar, hQ, real_inner_self_eq_norm_sq, hu, one_pow, map_neg, map_one,
    map_neg, map_one]

/-- For orthonormal `u, v` and `Q x = -⟪x, x⟫_ℝ`, the bivector `c(u) c(v)` squares to `-1`. -/
theorem map_ι_mul_map_ι_sq_of_orthonormal (hQ : ∀ x, Q x = -⟪x, x⟫_ℝ) {u v : V}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) :
    (ρ (ι Q u) * ρ (ι Q v)) * (ρ (ι Q u) * ρ (ι Q v)) = -1 := by
  calc
    (ρ (ι Q u) * ρ (ι Q v)) * (ρ (ι Q u) * ρ (ι Q v))
      = ρ (ι Q u) * ((ρ (ι Q v) * ρ (ι Q u)) * ρ (ι Q v)) := by simp [mul_assoc]
    _ = -(ρ (ι Q u) * (ρ (ι Q u) * (ρ (ι Q v) * ρ (ι Q v)))) := by
        rw [map_ι_mul_map_ι_of_inner_eq_zero ρ hQ (by rwa [real_inner_comm]), neg_mul, mul_neg,
          mul_assoc]
    _ = -1 := by
        rw [← mul_assoc (ρ (ι Q u)), map_ι_mul_map_ι_of_norm_eq_one ρ hQ hu,
          map_ι_mul_map_ι_of_norm_eq_one ρ hQ hv, neg_one_mul, neg_neg]

/-- **Planar similarity transformation of a Clifford bivector**: for orthogonal equal-norm vectors
`u, v`, replacing `(u, v)` by `(c • u + s • v, -s • u + c • v)` scales `c(u) c(v)` by
`c ^ 2 + s ^ 2`. -/
theorem map_ι_rot_mul_map_ι_rot_of_inner_eq_zero (hQ : ∀ x, Q x = -⟪x, x⟫_ℝ) {u v : V}
    (hnorm : ‖u‖ = ‖v‖) (huv : ⟪u, v⟫_ℝ = 0) (c s : ℝ) :
    ρ (ι Q (c • u + s • v)) * ρ (ι Q (-s • u + c • v)) =
      (c ^ 2 + s ^ 2) • (ρ (ι Q u) * ρ (ι Q v)) := by
  have hQu : ρ (ι Q u) * ρ (ι Q u) = (-‖v‖ ^ 2) • 1 := by
    rw [← map_mul ρ, ι_sq_scalar, hQ, real_inner_self_eq_norm_sq, hnorm, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one]
  have hQv : ρ (ι Q v) * ρ (ι Q v) = (-‖v‖ ^ 2) • 1 := by
    rw [← map_mul ρ, ι_sq_scalar, hQ, real_inner_self_eq_norm_sq, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one]
  have hvu : ρ (ι Q v) * ρ (ι Q u) = -(ρ (ι Q u) * ρ (ι Q v)) :=
    map_ι_mul_map_ι_of_inner_eq_zero ρ hQ (by rwa [real_inner_comm])
  simp only [map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    mul_neg, smul_neg, smul_smul, hQu, hQv, hvu]
  module

/-- **Oriented `SO(2)` rotation invariance of a Clifford bivector**: when `c ^ 2 + s ^ 2 = 1`,
rotating an orthogonal equal-norm pair `(u, v)` leaves `c(u) c(v)` unchanged. -/
theorem map_ι_rot_mul_map_ι_rot_of_eq_one (hQ : ∀ x, Q x = -⟪x, x⟫_ℝ) {u v : V}
    (hnorm : ‖u‖ = ‖v‖) (huv : ⟪u, v⟫_ℝ = 0) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    ρ (ι Q (c • u + s • v)) * ρ (ι Q (-s • u + c • v)) = ρ (ι Q u) * ρ (ι Q v) := by
  rw [map_ι_rot_mul_map_ι_rot_of_inner_eq_zero ρ hQ hnorm huv, hcs, one_smul]

end Module

section ComplexPlane

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℝ S] [IsScalarTower ℝ ℂ S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- For orthonormal `u, v` and `Q x = -⟪x, x⟫_ℝ`, the two-plane operator `i • (c(u) c(v))` is an
involution. -/
theorem smul_I_map_ι_mul_map_ι_sq_of_orthonormal (hQ : ∀ x, Q x = -⟪x, x⟫_ℝ) {u v : V}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) :
    (Complex.I • (ρ (ι Q u) * ρ (ι Q v))) * (Complex.I • (ρ (ι Q u) * ρ (ι Q v))) = 1 := by
  rw [smul_mul_smul_comm, Complex.I_mul_I, map_ι_mul_map_ι_sq_of_orthonormal ρ hQ hu hv huv,
    neg_one_smul, neg_neg]

/-- For orthogonal `u, v` and `Q x = -⟪x, x⟫_ℝ`, `i • (c(u) c(v))` anticommutes with `c(u)`. -/
theorem smul_I_map_ι_mul_map_ι_anticomm_left (hQ : ∀ x, Q x = -⟪x, x⟫_ℝ) {u v : V}
    (huv : ⟪u, v⟫_ℝ = 0) :
    (Complex.I • (ρ (ι Q u) * ρ (ι Q v))) * ρ (ι Q u) =
      -(ρ (ι Q u) * (Complex.I • (ρ (ι Q u) * ρ (ι Q v)))) := by
  have hvu : ρ (ι Q v) * ρ (ι Q u) = -(ρ (ι Q u) * ρ (ι Q v)) :=
    map_ι_mul_map_ι_of_inner_eq_zero ρ hQ (by rwa [real_inner_comm])
  rw [smul_mul_assoc, mul_assoc, hvu, mul_neg, smul_neg, mul_smul_comm]

/-- For orthogonal `u, v` and `Q x = -⟪x, x⟫_ℝ`, `i • (c(u) c(v))` anticommutes with `c(v)`. -/
theorem smul_I_map_ι_mul_map_ι_anticomm_right (hQ : ∀ x, Q x = -⟪x, x⟫_ℝ) {u v : V}
    (huv : ⟪u, v⟫_ℝ = 0) :
    (Complex.I • (ρ (ι Q u) * ρ (ι Q v))) * ρ (ι Q v) =
      -(ρ (ι Q v) * (Complex.I • (ρ (ι Q u) * ρ (ι Q v)))) := by
  have hvu : ρ (ι Q v) * ρ (ι Q u) = -(ρ (ι Q u) * ρ (ι Q v)) :=
    map_ι_mul_map_ι_of_inner_eq_zero ρ hQ (by rwa [real_inner_comm])
  rw [mul_smul_comm, ← mul_assoc, hvu, neg_mul, smul_neg, neg_neg, smul_mul_assoc]

end ComplexPlane

end Polarization

end CliffordAlgebra

namespace AlgHom

open CliffordAlgebra

/-! ### Compatibility of `cliffordBaseChange ℂ` with `conjStar` -/

section ConjStar

variable {V S : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}

section Inner

variable [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- If real vectors act skew-Hermitianly under `ρ`, then its complex-linear extension
`ρ.cliffordBaseChange ℂ` is compatible with `CliffordAlgebra.conjStar` on the whole complexified
Clifford algebra. -/
theorem inner_cliffordBaseChange_eq_conjStar
    (hρ : ∀ (v : V) (x y : S), ⟪ρ (ι Q v) x, y⟫_ℂ = -⟪x, ρ (ι Q v) y⟫_ℂ)
    (a : CliffordAlgebra (Q.baseChange ℂ)) (x y : S) :
    ⟪ρ.cliffordBaseChange ℂ a x, y⟫_ℂ = ⟪x, ρ.cliffordBaseChange ℂ (conjStar Q a) y⟫_ℂ := by
  refine sesqForm_map_eq_map_conjStar (ρ.cliffordBaseChange ℂ) (innerₛₗ ℂ) (fun v x y ↦ ?_) a x y
  simpa only [innerₛₗ_apply_apply, cliffordBaseChange_ι_one_tmul] using hρ v x y

/-- `ρ.cliffordBaseChange ℂ` is compatible with `CliffordAlgebra.conjStar` if and only if real
vectors act skew-Hermitianly under `ρ`. -/
theorem inner_cliffordBaseChange_eq_conjStar_iff :
    (∀ (a : CliffordAlgebra (Q.baseChange ℂ)) (x y : S),
        ⟪ρ.cliffordBaseChange ℂ a x, y⟫_ℂ = ⟪x, ρ.cliffordBaseChange ℂ (conjStar Q a) y⟫_ℂ) ↔
      ∀ (v : V) (x y : S), ⟪ρ (ι Q v) x, y⟫_ℂ = -⟪x, ρ (ι Q v) y⟫_ℂ := by
  refine ⟨fun h v x y ↦ ?_, ρ.inner_cliffordBaseChange_eq_conjStar⟩
  simpa [cliffordBaseChange_ι_one_tmul] using h (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) x y

end Inner

section Adjoint

variable [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- On a finite-dimensional complex inner product space, `ρ.cliffordBaseChange ℂ` is a
`*-`representation for `CliffordAlgebra.conjStar` if and only if each real vector acts
skew-adjointly under `ρ`. -/
theorem adjoint_cliffordBaseChange_eq_conjStar_iff :
    (∀ a : CliffordAlgebra (Q.baseChange ℂ),
        (ρ.cliffordBaseChange ℂ a).adjoint = ρ.cliffordBaseChange ℂ (conjStar Q a)) ↔
      ∀ v : V, (ρ (ι Q v)).adjoint = -ρ (ι Q v) := by
  simpa only [cliffordBaseChange_ι_one_tmul] using
    adjoint_map_eq_map_conjStar_iff (ρ.cliffordBaseChange ℂ)

/-- Inner-product form of `AlgHom.adjoint_cliffordBaseChange_eq_conjStar_iff`. -/
theorem adjoint_cliffordBaseChange_eq_conjStar_iff_inner :
    (∀ a : CliffordAlgebra (Q.baseChange ℂ),
        (ρ.cliffordBaseChange ℂ a).adjoint = ρ.cliffordBaseChange ℂ (conjStar Q a)) ↔
      ∀ (v : V) (x y : S), ⟪ρ (ι Q v) x, y⟫_ℂ = -⟪x, ρ (ι Q v) y⟫_ℂ := by
  rw [ρ.adjoint_cliffordBaseChange_eq_conjStar_iff]
  refine forall_congr' fun v ↦ ?_
  rw [eq_comm, LinearMap.eq_adjoint_iff]
  refine forall₂_congr fun x y ↦ ?_
  rw [LinearMap.neg_apply, inner_neg_left, neg_eq_iff_eq_neg]

end Adjoint

end ConjStar

/-! ### The geometric convention `AlgHom.IsGeometricClifford` -/

section Geometric

variable {V S : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}

section Seminormed

variable [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]

/-- **The geometric convention on a real Clifford action**: `Q v = -⟪v, v⟫_ℝ` and each generator
`ρ (ι Q v)` acts skew-Hermitianly on `S`. Neither finite-dimensionality nor completeness of `S` is
assumed. -/
structure IsGeometricClifford (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) : Prop where
  /-- The quadratic form is minus the real inner product: `Q v = -⟪v, v⟫_ℝ`. -/
  quadratic_eq (v : V) : Q v = -⟪v, v⟫_ℝ
  /-- Real vectors act skew-Hermitianly: `⟪c(v) x, y⟫_ℂ = -⟪x, c(v) y⟫_ℂ`. -/
  inner_map_ι_left (v : V) (x y : S) : ⟪ρ (ι Q v) x, y⟫_ℂ = -⟪x, ρ (ι Q v) y⟫_ℂ

/-- Norm-square characterization of `AlgHom.IsGeometricClifford`. -/
theorem isGeometricClifford_iff_norm_sq (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) :
    ρ.IsGeometricClifford ↔
      (∀ v : V, Q v = -‖v‖ ^ 2) ∧
        ∀ (v : V) (x y : S), ⟪ρ (ι Q v) x, y⟫_ℂ = -⟪x, ρ (ι Q v) y⟫_ℂ := by
  refine ⟨fun h ↦ ⟨fun v ↦ by rw [h.quadratic_eq, real_inner_self_eq_norm_sq],
    h.inner_map_ι_left⟩, fun ⟨hQ, hρ⟩ ↦ ⟨fun v ↦ ?_, hρ⟩⟩
  rw [hQ, real_inner_self_eq_norm_sq]

/-- Vector-lift characterization of `AlgHom.IsGeometricClifford` on `CliffordAlgebra.lift`. -/
theorem _root_.CliffordAlgebra.isGeometricClifford_lift_iff
    (f : V →ₗ[ℝ] Module.End ℂ S)
    (hf : ∀ v, f v * f v = algebraMap ℝ (Module.End ℂ S) (Q v)) :
    (CliffordAlgebra.lift Q ⟨f, hf⟩).IsGeometricClifford ↔
      (∀ v : V, Q v = -⟪v, v⟫_ℝ) ∧
        ∀ (v : V) (x y : S), ⟪f v x, y⟫_ℂ = -⟪x, f v y⟫_ℂ := by
  refine ⟨fun h ↦ ⟨h.quadratic_eq, fun v x y ↦ ?_⟩, fun ⟨hQ, h⟩ ↦ ⟨hQ, fun v x y ↦ ?_⟩⟩
  · simpa only [lift_ι_apply] using h.inner_map_ι_left v x y
  · simpa only [lift_ι_apply] using h v x y

namespace IsGeometricClifford

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- Under the geometric convention, `Q v = -‖v‖ ^ 2`. -/
theorem quadratic_eq_neg_norm_sq (v : V) : Q v = -‖v‖ ^ 2 := by
  rw [hρ.quadratic_eq, real_inner_self_eq_norm_sq]

/-- Right-hand skew-Hermitian identity `⟪x, c(v) y⟫_ℂ = -⟪c(v) x, y⟫_ℂ`. -/
theorem inner_map_ι_right (v : V) (x y : S) :
    ⟪x, ρ (ι Q v) y⟫_ℂ = -⟪ρ (ι Q v) x, y⟫_ℂ := by
  rw [hρ.inner_map_ι_left, neg_neg]

/-- Polarized anticommutator `c(v) c(w) + c(w) c(v) = (-2 * ⟪v, w⟫_ℝ) • 1` for a geometric
Clifford action. -/
theorem map_ι_mul_map_ι_add_swap (v w : V) :
    ρ (ι Q v) * ρ (ι Q w) + ρ (ι Q w) * ρ (ι Q v) = (-2 * ⟪v, w⟫_ℝ) • 1 :=
  CliffordAlgebra.map_ι_mul_map_ι_add_swap ρ hρ.quadratic_eq v w

/-- Pointwise polarized anticommutator for a geometric Clifford action. -/
theorem map_ι_apply_map_ι_apply_add_swap (v w : V) (x : S) :
    ρ (ι Q v) (ρ (ι Q w) x) + ρ (ι Q w) (ρ (ι Q v) x) = (-2 * ⟪v, w⟫_ℝ) • x :=
  CliffordAlgebra.map_ι_apply_map_ι_apply_add_swap ρ hρ.quadratic_eq v w x

/-- Under `AlgHom.IsGeometricClifford`, `ρ.cliffordBaseChange ℂ` is compatible with
`CliffordAlgebra.conjStar`. -/
theorem inner_cliffordBaseChange_eq_conjStar (a : CliffordAlgebra (Q.baseChange ℂ)) (x y : S) :
    ⟪ρ.cliffordBaseChange ℂ a x, y⟫_ℂ = ⟪x, ρ.cliffordBaseChange ℂ (conjStar Q a) y⟫_ℂ :=
  ρ.inner_cliffordBaseChange_eq_conjStar hρ.inner_map_ι_left a x y

/-- Under `AlgHom.IsGeometricClifford`, the real action is compatible with Clifford conjugation
`star` on `CliffordAlgebra Q` without requiring finite-dimensionality of `S`. -/
theorem inner_map_eq_map_star (a : CliffordAlgebra Q) (x y : S) :
    ⟪ρ a x, y⟫_ℂ = ⟪x, ρ (star a) y⟫_ℂ := by
  have h := hρ.inner_cliffordBaseChange_eq_conjStar (ofBaseChangeAux ℂ Q a) x y
  simpa only [cliffordBaseChange_ofBaseChangeAux, conjStar_ofBaseChangeAux] using h

/-- **Polarized inner-product identity**: for a geometric Clifford action,
`⟪c(v) x, c(w) y⟫_ℂ + ⟪c(w) x, c(v) y⟫_ℂ = (2 * ⟪v, w⟫_ℝ : ℂ) * ⟪x, y⟫_ℂ`. -/
theorem inner_map_ι_add_swap (v w : V) (x y : S) :
    ⟪ρ (ι Q v) x, ρ (ι Q w) y⟫_ℂ + ⟪ρ (ι Q w) x, ρ (ι Q v) y⟫_ℂ =
      ((2 * ⟪v, w⟫_ℝ : ℝ) : ℂ) * ⟪x, y⟫_ℂ := by
  rw [hρ.inner_map_ι_left, hρ.inner_map_ι_left, ← neg_add, ← inner_add_right,
    hρ.map_ι_apply_map_ι_apply_add_swap, ← Complex.coe_smul, inner_smul_right]
  push_cast
  ring

/-- **Inner-product scaling**: Clifford multiplication by `v` scales inner products by `‖v‖ ^ 2`. -/
theorem inner_map_ι_self (v : V) (x y : S) :
    ⟪ρ (ι Q v) x, ρ (ι Q v) y⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) * ⟪x, y⟫_ℂ := by
  rw [hρ.inner_map_ι_left, map_ι_apply_map_ι_apply, hρ.quadratic_eq_neg_norm_sq, inner_smul_right]
  push_cast
  ring

/-- **Norm scaling**: Clifford multiplication by `v` scales norms by `‖v‖`, without requiring `S`
to be finite-dimensional. -/
theorem norm_map_ι_apply (v : V) (x : S) : ‖ρ (ι Q v) x‖ = ‖v‖ * ‖x‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  exact Complex.ofReal_injective
    (by simpa [inner_self_eq_norm_sq_to_K, mul_pow] using hρ.inner_map_ι_self v x x)

/-- For orthogonal `u, v`, the bivector `c(u) c(v)` is skew-Hermitian. -/
theorem inner_map_ι_mul_map_ι_of_inner_eq_zero {u v : V} (huv : ⟪u, v⟫_ℝ = 0) (x y : S) :
    ⟪(ρ (ι Q u) * ρ (ι Q v)) x, y⟫_ℂ = -⟪x, (ρ (ι Q u) * ρ (ι Q v)) y⟫_ℂ := by
  have hvu : ρ (ι Q v) * ρ (ι Q u) = -(ρ (ι Q u) * ρ (ι Q v)) :=
    map_ι_mul_map_ι_of_inner_eq_zero ρ hρ.quadratic_eq (by rwa [real_inner_comm])
  rw [mul_apply_eq_comp, hρ.inner_map_ι_left, hρ.inner_map_ι_left, neg_neg,
    ← mul_apply_eq_comp, hvu, LinearMap.neg_apply, inner_neg_right]

/-- For orthogonal `u, v`, the two-plane operator `i • (c(u) c(v))` is symmetric with respect to
the complex inner product. -/
theorem isSymmetric_smul_I_map_ι_mul_map_ι_of_inner_eq_zero {u v : V} (huv : ⟪u, v⟫_ℝ = 0) :
    (Complex.I • (ρ (ι Q u) * ρ (ι Q v))).IsSymmetric := by
  intro x y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
    hρ.inner_map_ι_mul_map_ι_of_inner_eq_zero huv, Complex.conj_I, neg_mul, mul_neg, neg_neg]

/-- **Clifford multiplication by a unit vector as a complex-linear isometric equivalence**, with
inverse `-c(u)`. -/
def unitVectorIsometryEquiv {u : V} (hu : ‖u‖ = 1) : S ≃ₗᵢ[ℂ] S where
  toFun := ρ (ι Q u)
  invFun := -ρ (ι Q u)
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    simp [map_ι_apply_map_ι_apply, hρ.quadratic_eq_neg_norm_sq, hu]
  right_inv x := by
    simp [map_ι_apply_map_ι_apply, hρ.quadratic_eq_neg_norm_sq, hu]
  norm_map' x := by simp [hρ.norm_map_ι_apply, hu]

/-- Pointwise evaluation of `AlgHom.IsGeometricClifford.unitVectorIsometryEquiv`. -/
@[simp]
theorem unitVectorIsometryEquiv_apply {u : V} (hu : ‖u‖ = 1) (x : S) :
    hρ.unitVectorIsometryEquiv hu x = ρ (ι Q u) x :=
  (rfl)

/-- Pointwise evaluation of `(AlgHom.IsGeometricClifford.unitVectorIsometryEquiv).symm`. -/
@[simp]
theorem unitVectorIsometryEquiv_symm_apply {u : V} (hu : ‖u‖ = 1) (x : S) :
    (hρ.unitVectorIsometryEquiv hu).symm x = -ρ (ι Q u) x :=
  (rfl)

end IsGeometricClifford

end Seminormed

section Normed

variable [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S}

namespace IsGeometricClifford

/-- On a finite-dimensional module, generators act skew-adjointly under `IsGeometricClifford`. -/
theorem adjoint_map_ι (hρ : ρ.IsGeometricClifford) (v : V) :
    (ρ (ι Q v)).adjoint = -ρ (ι Q v) :=
  ((ρ.adjoint_cliffordBaseChange_eq_conjStar_iff.mp fun a ↦
    (ρ.adjoint_cliffordBaseChange_eq_conjStar_iff_inner.mpr hρ.inner_map_ι_left) a) v)

/-- On a finite-dimensional module, `(ρ a).adjoint = ρ (star a)` under `IsGeometricClifford`. -/
theorem adjoint_map (hρ : ρ.IsGeometricClifford) (a : CliffordAlgebra Q) :
    (ρ a).adjoint = ρ (star a) :=
  adjoint_map_eq_map_star hρ.adjoint_map_ι a

/-- On a finite-dimensional module, `(ρ.cliffordBaseChange ℂ a).adjoint =
ρ.cliffordBaseChange ℂ (conjStar Q a)` under `IsGeometricClifford`. -/
theorem adjoint_cliffordBaseChange (hρ : ρ.IsGeometricClifford)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (ρ.cliffordBaseChange ℂ a).adjoint = ρ.cliffordBaseChange ℂ (conjStar Q a) :=
  (ρ.adjoint_cliffordBaseChange_eq_conjStar_iff_inner.mpr hρ.inner_map_ι_left) a

end IsGeometricClifford

/-- Adjoint characterization of `AlgHom.IsGeometricClifford` in finite dimensions. -/
theorem isGeometricClifford_iff_adjoint
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) :
    ρ.IsGeometricClifford ↔
      (∀ v : V, Q v = -⟪v, v⟫_ℝ) ∧ ∀ v : V, (ρ (ι Q v)).adjoint = -ρ (ι Q v) := by
  rw [← ρ.adjoint_cliffordBaseChange_eq_conjStar_iff,
    ρ.adjoint_cliffordBaseChange_eq_conjStar_iff_inner]
  exact ⟨fun h ↦ ⟨h.quadratic_eq, h.inner_map_ι_left⟩, fun ⟨hQ, h⟩ ↦ ⟨hQ, h⟩⟩

/-- Complexified `conjStar`-adjoint characterization of `AlgHom.IsGeometricClifford` in finite
dimensions. -/
theorem isGeometricClifford_iff_adjoint_cliffordBaseChange
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) :
    ρ.IsGeometricClifford ↔
      (∀ v : V, Q v = -⟪v, v⟫_ℝ) ∧
        ∀ a : CliffordAlgebra (Q.baseChange ℂ),
          (ρ.cliffordBaseChange ℂ a).adjoint = ρ.cliffordBaseChange ℂ (conjStar Q a) := by
  rw [ρ.isGeometricClifford_iff_adjoint, ρ.adjoint_cliffordBaseChange_eq_conjStar_iff]

end Normed

/-! ### Functoriality and tensor-product constructions -/

section Constructions

/-- Pulling back a geometric Clifford action along a quadratic isometry `f : Q' →qᵢ Q` whose
underlying map preserves inner products preserves `AlgHom.IsGeometricClifford`. -/
theorem IsGeometricClifford.comp_map {V' : Type*} [SeminormedAddCommGroup V']
    [InnerProductSpace ℝ V'] {Q' : QuadraticForm ℝ V'} [SeminormedAddCommGroup S]
    [InnerProductSpace ℂ S] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S}
    (hρ : ρ.IsGeometricClifford) (f : Q' →qᵢ Q) (hf : ∀ u : V', ⟪f u, f u⟫_ℝ = ⟪u, u⟫_ℝ) :
    (ρ.comp (CliffordAlgebra.map f)).IsGeometricClifford where
  quadratic_eq u := by rw [← f.map_app, hρ.quadratic_eq, hf]
  inner_map_ι_left u x y := by
    simpa only [AlgHom.comp_apply, CliffordAlgebra.map_apply_ι] using hρ.inner_map_ι_left (f u) x y

/-- Conjugating a geometric Clifford action by a complex-linear isometric equivalence
`U : S ≃ₗᵢ[ℂ] S'` preserves `AlgHom.IsGeometricClifford`. -/
theorem IsGeometricClifford.conj {S' : Type*} [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]
    [SeminormedAddCommGroup S'] [InnerProductSpace ℂ S']
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
    (U : S ≃ₗᵢ[ℂ] S') :
    (((U.toLinearEquiv.conjAlgEquiv ℂ).toAlgHom.restrictScalars ℝ).comp ρ).IsGeometricClifford where
  quadratic_eq := hρ.quadratic_eq
  inner_map_ι_left v x y := by
    let ρ' := ((U.toLinearEquiv.conjAlgEquiv ℂ).toAlgHom.restrictScalars ℝ).comp ρ
    have hU (z : S') : ρ' (ι Q v) z = U (ρ (ι Q v) (U.symm z)) := rfl
    calc
      ⟪ρ' (ι Q v) x, y⟫_ℂ
        = ⟪U (ρ (ι Q v) (U.symm x)), U (U.symm y)⟫_ℂ := by rw [hU, U.apply_symm_apply]
      _ = -⟪U (U.symm x), U (ρ (ι Q v) (U.symm y))⟫_ℂ := by
          rw [U.inner_map_map, U.inner_map_map, hρ.inner_map_ι_left]
      _ = -⟪x, ρ' (ι Q v) y⟫_ℂ := by rw [U.apply_symm_apply, hU]

private theorem inner_rTensor_skew {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {A : E →ₗ[ℂ] E}
    (hA : ∀ x y : E, ⟪A x, y⟫_ℂ = -⟪x, A y⟫_ℂ) (x y : E ⊗[ℂ] F) :
    ⟪A.rTensor F x, y⟫_ℂ = -⟪x, A.rTensor F y⟫_ℂ := by
  induction x using TensorProduct.inductionOn with
  | tmul e₁ f₁ =>
    induction y using TensorProduct.inductionOn with
    | tmul e₂ f₂ => simp [hA]
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, inner_add_right, hy₁, hy₂, neg_add]
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, inner_add_left, hx₁, hx₂, neg_add]

private theorem inner_lTensor_skew {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {B : F →ₗ[ℂ] F}
    (hB : ∀ x y : F, ⟪B x, y⟫_ℂ = -⟪x, B y⟫_ℂ) (x y : E ⊗[ℂ] F) :
    ⟪B.lTensor E x, y⟫_ℂ = -⟪x, B.lTensor E y⟫_ℂ := by
  induction x using TensorProduct.inductionOn with
  | tmul e₁ f₁ =>
    induction y using TensorProduct.inductionOn with
    | tmul e₂ f₂ => simp [hB]
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, inner_add_right, hy₁, hy₂, neg_add]
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, inner_add_left, hx₁, hx₂, neg_add]

/-- **Ungraded right tensor twist**: twisting a geometric Clifford action on `S` by the identity on
a complex inner product space `W` produces a geometric Clifford action on `S ⊗[ℂ] W`. -/
theorem IsGeometricClifford.rTensor {W : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford) :
    (((Module.End.rTensorAlgHom ℂ S W).restrictScalars ℝ).comp ρ).IsGeometricClifford where
  quadratic_eq := hρ.quadratic_eq
  inner_map_ι_left v x y := inner_rTensor_skew (hρ.inner_map_ι_left v) x y

/-- **Ungraded left tensor twist**: twisting a geometric Clifford action on `S` by the identity on
`W` on the left produces a geometric Clifford action on `W ⊗[ℂ] S`. -/
theorem IsGeometricClifford.lTensor {W : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford) :
    (((Module.End.lTensorAlgHom ℂ S W).restrictScalars ℝ).comp ρ).IsGeometricClifford where
  quadratic_eq := hρ.quadratic_eq
  inner_map_ι_left v x y := inner_lTensor_skew (hρ.inner_map_ι_left v) x y

end Constructions

end Geometric

/-! ### Graded tensor product of real Clifford actions on complex modules -/

section ComplexProdTensor

variable {M₁ M₂ E F : Type*} [AddCommGroup M₁] [Module ℝ M₁] [AddCommGroup M₂] [Module ℝ M₂]
  {Q₁ : QuadraticForm ℝ M₁} {Q₂ : QuadraticForm ℝ M₂}
  [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]

private theorem cliffordBaseChange_anticomm (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E)
    (γ : Module.End ℂ E) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ)) (z : ℂ ⊗[ℝ] M₁) :
    γ * ρ₁.cliffordBaseChange ℂ (ι (Q₁.baseChange ℂ) z) =
      -(ρ₁.cliffordBaseChange ℂ (ι (Q₁.baseChange ℂ) z) * γ) := by
  induction z using TensorProduct.inductionOn with
  | tmul c v =>
    simp only [cliffordBaseChange_ι_tmul, mul_smul_comm, smul_mul_assoc, hγρ, smul_neg]
  | add x y hx hy => rw [map_add, map_add, mul_add, add_mul, hx, hy, neg_add]

/-- **The graded tensor product of real Clifford actions on complex modules.** Given real Clifford
actions `ρ₁` on `E` and `ρ₂` on `F` together with a complex-linear grading involution `γ` on `E`
anticommuting with `ρ₁ (ι Q₁ v)`, `(v, w)` acts on `E ⊗[ℂ] F` by `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`. Built
from `AlgHom.cliffordProdTensor` via `AlgHom.cliffordBaseChange ℂ`. -/
noncomputable def cliffordComplexProdTensor (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E)
    (γ : Module.End ℂ E) (hγ : γ * γ = 1)
    (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) :
    CliffordAlgebra (Q₁.prod Q₂) →ₐ[ℝ] Module.End ℂ (E ⊗[ℂ] F) :=
  let σ := (ρ₁.cliffordBaseChange ℂ).cliffordProdTensor γ hγ
    (cliffordBaseChange_anticomm ρ₁ γ hγρ) (ρ₂.cliffordBaseChange ℂ)
  let j : M₁ × M₂ →ₗ[ℝ] (ℂ ⊗[ℝ] M₁) × (ℂ ⊗[ℝ] M₂) :=
    LinearMap.prodMap (TensorProduct.mk ℝ ℂ M₁ 1) (TensorProduct.mk ℝ ℂ M₂ 1)
  CliffordAlgebra.lift (Q₁.prod Q₂)
    ⟨(σ.restrictScalars ℝ).toLinearMap.comp
        ((ι ((Q₁.baseChange ℂ).prod (Q₂.baseChange ℂ))).restrictScalars ℝ |>.comp j),
      fun x ↦ by
        simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply,
          AlgHom.restrictScalars_apply, ← map_mul, ι_sq_scalar, σ.commutes,
          QuadraticMap.prod_apply, j, LinearMap.prodMap_apply, TensorProduct.mk_apply,
          QuadraticForm.baseChange_tmul, one_mul]
        simp only [Algebra.algebraMap_eq_smul_one, add_smul, smul_assoc, one_smul]⟩

/-- A vector `(v, w)` acts under `AlgHom.cliffordComplexProdTensor` by `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`. -/
theorem cliffordComplexProdTensor_ι (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E)
    (γ : Module.End ℂ E) (hγ : γ * γ = 1)
    (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) (x : M₁ × M₂) :
    cliffordComplexProdTensor ρ₁ γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) x) =
      (ρ₁ (ι Q₁ x.1)).rTensor F + TensorProduct.map γ (ρ₂ (ι Q₂ x.2)) := by
  simp [cliffordComplexProdTensor, cliffordProdTensor_ι]

/-- Pulling back `AlgHom.cliffordComplexProdTensor` along `CliffordAlgebra.map f` sends `ι Q₁₂ v` to
`c₁((f v).1) ⊗ 1 + γ ⊗ c₂((f v).2)`. -/
theorem cliffordComplexProdTensor_comp_map_ι {M₁₂ : Type*} [AddCommGroup M₁₂] [Module ℝ M₁₂]
    {Q₁₂ : QuadraticForm ℝ M₁₂} (f : Q₁₂ →qᵢ Q₁.prod Q₂)
    (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E) (γ : Module.End ℂ E) (hγ : γ * γ = 1)
    (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) (v : M₁₂) :
    ((cliffordComplexProdTensor ρ₁ γ hγ hγρ ρ₂).comp (CliffordAlgebra.map f)) (ι Q₁₂ v) =
      (ρ₁ (ι Q₁ (f v).1)).rTensor F + TensorProduct.map γ (ρ₂ (ι Q₂ (f v).2)) := by
  rw [AlgHom.comp_apply, CliffordAlgebra.map_apply_ι, cliffordComplexProdTensor_ι]

/-- On a pure tensor, `c(v, w) (e ⊗ f) = c₁(v) e ⊗ f + γ e ⊗ c₂(w) f`. -/
@[simp]
theorem cliffordComplexProdTensor_ι_tmul (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E)
    (γ : Module.End ℂ E) (hγ : γ * γ = 1)
    (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) (x : M₁ × M₂) (e : E) (f : F) :
    cliffordComplexProdTensor ρ₁ γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) x) (e ⊗ₜ f) =
      ρ₁ (ι Q₁ x.1) e ⊗ₜ f + γ e ⊗ₜ ρ₂ (ι Q₂ x.2) f := by
  simp [cliffordComplexProdTensor_ι]

/-- A vector `(v, 0)` of the first summand acts through the first factor by `c₁(v) ⊗ 1`. -/
@[simp]
theorem cliffordComplexProdTensor_ι_inl (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E)
    (γ : Module.End ℂ E) (hγ : γ * γ = 1)
    (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) (v : M₁) :
    cliffordComplexProdTensor ρ₁ γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) (v, 0)) =
      (ρ₁ (ι Q₁ v)).rTensor F := by
  simp [cliffordComplexProdTensor_ι]

/-- A vector `(0, w)` of the second summand acts through the grading by `γ ⊗ c₂(w)`. -/
@[simp]
theorem cliffordComplexProdTensor_ι_inr (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E)
    (γ : Module.End ℂ E) (hγ : γ * γ = 1)
    (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) (w : M₂) :
    cliffordComplexProdTensor ρ₁ γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) (0, w)) =
      TensorProduct.map γ (ρ₂ (ι Q₂ w)) := by
  simp [cliffordComplexProdTensor_ι]

end ComplexProdTensor

section GeometricComplexProdTensor

variable {V₁ V₂ E F : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  {Q₁ : QuadraticForm ℝ V₁} {Q₂ : QuadraticForm ℝ V₂}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

private theorem inner_rTensor_add_map_skew {A γ : E →ₗ[ℂ] E} {B : F →ₗ[ℂ] F}
    (hA : ∀ x y : E, ⟪A x, y⟫_ℂ = -⟪x, A y⟫_ℂ) (hγ : γ.IsSymmetric)
    (hB : ∀ x y : F, ⟪B x, y⟫_ℂ = -⟪x, B y⟫_ℂ) (x y : E ⊗[ℂ] F) :
    ⟪(A.rTensor F + TensorProduct.map γ B) x, y⟫_ℂ =
      -⟪x, (A.rTensor F + TensorProduct.map γ B) y⟫_ℂ := by
  induction x using TensorProduct.inductionOn with
  | tmul e₁ f₁ =>
    induction y using TensorProduct.inductionOn with
    | tmul e₂ f₂ =>
      simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
        inner_add_left, inner_add_right, TensorProduct.inner_tmul, hA, hB, hγ e₁ e₂]
      ring
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, inner_add_right, hy₁, hy₂, neg_add]
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, inner_add_left, hx₁, hx₂, neg_add]

/-- **The graded tensor product of geometric Clifford actions is geometric** on the `L²` orthogonal
sum `WithLp 2 (V₁ × V₂)` whenever the grading involution `γ` on `E` is symmetric with respect to the
inner product. -/
theorem IsGeometricClifford.complexProdTensor
    {ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E} (hρ₁ : ρ₁.IsGeometricClifford)
    {γ : Module.End ℂ E} (hγ : γ * γ = 1)
    (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ)) (hγs : γ.IsSymmetric)
    {ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F} (hρ₂ : ρ₂.IsGeometricClifford)
    {Q₁₂ : QuadraticForm ℝ (WithLp 2 (V₁ × V₂))} (f : Q₁₂ →qᵢ Q₁.prod Q₂)
    (hf : ∀ x : WithLp 2 (V₁ × V₂), f x = WithLp.ofLp x) :
    ((cliffordComplexProdTensor ρ₁ γ hγ hγρ ρ₂).comp
      (CliffordAlgebra.map f)).IsGeometricClifford where
  quadratic_eq x := by
    rw [← f.map_app, hf, QuadraticMap.prod_apply, hρ₁.quadratic_eq, hρ₂.quadratic_eq,
      WithLp.prod_inner_apply, neg_add]
  inner_map_ι_left v x y := by
    have h_eq := cliffordComplexProdTensor_comp_map_ι f ρ₁ γ hγ hγρ ρ₂ v
    exact h_eq.symm ▸ inner_rTensor_add_map_skew
      (hρ₁.inner_map_ι_left (f v).1) hγs (hρ₂.inner_map_ι_left (f v).2) x y

end GeometricComplexProdTensor

end AlgHom
