/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Chirality
public import TauCeti.LinearAlgebra.Matrix.Pauli

/-!
# Concrete geometric Clifford actions: the real line and the negative Pauli plane

This file constructs the two basic concrete witnesses of `AlgHom.IsGeometricClifford` and computes
the intrinsic chirality operator and half-spinor eigenspaces on the two-dimensional example:

1. **The one-dimensional real line (`TauCeti.realLineCliffordAction`)**: on `V = ℝ` with
   `Q = -QuadraticMap.sq` (`Q r = -(r * r)`) and `S = ℂ`, the generator `1 : ℝ` acts by
   multiplication by `i`.
2. **The two-dimensional negative Pauli plane (`TauCeti.negativePlanePauliAction`)**: on
   `V = EuclideanSpace ℝ (Fin 2)` with `Q = -LinearMap.BilinMap.toQuadraticMap (innerₗ V)`
   (`Q v = -⟪v, v⟫_ℝ`) and `S = EuclideanSpace ℂ (Fin 2)`, the standard basis vectors `e₀ = (1, 0)`
   and `e₁ = (0, 1)` act by `i • σ₃ = i Z` and `i • σ₂ = i Y` via `TauCeti.pauli` and
   `Matrix.toEuclideanLin`.

On the negative Pauli plane, `c(e₀) c(e₁) = (i Z)(i Y) = i X`, so for the standard orientation
`(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation` the intrinsic chirality operator is

  `negativePlanePauliAction.cliffordBaseChange ℂ (complexVolume _ o) = i (i X) = -X`,

with `+1`-eigenvector `(1, -1)` and `-1`-eigenvector `(1, 1)` in `EuclideanSpace ℂ (Fin 2)`.

## Main definitions

* `TauCeti.realLineCliffordAction`: the geometric Clifford action of `Cℓ(ℝ, -x²)` on `ℂ` sending
  `1 ↦ i • 1`.
* `TauCeti.negativePlanePauliAction`: the geometric Clifford action of
  `Cℓ(EuclideanSpace ℝ (Fin 2), -‖v‖²)` on `EuclideanSpace ℂ (Fin 2)` sending `e₀ ↦ i Z` and
  `e₁ ↦ i Y`.

## Main results

* `TauCeti.isGeometricClifford_realLineCliffordAction`: `realLineCliffordAction` satisfies
  `AlgHom.IsGeometricClifford`.
* `TauCeti.isGeometricClifford_negativePlanePauliAction`: `negativePlanePauliAction` satisfies
  `AlgHom.IsGeometricClifford`.
* `TauCeti.cliffordBaseChange_complexVolume_negativePlanePauliAction`: the chirality operator on the
  negative Pauli plane is `(-pauli ![1, 0, 0]).toEuclideanLin` (`-X`).
* `TauCeti.mem_eigenspace_negativePlanePauliAction_one`,
  `TauCeti.mem_eigenspace_negativePlanePauliAction_neg_one`: `(1, -1)` and `(1, 1)` belong to the
  `+1`- and `-1`-eigenspaces of chirality on `EuclideanSpace ℂ (Fin 2)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., §12.1.2.
-/

public section

noncomputable section

open CliffordAlgebra Matrix Module
open scoped EuclideanSpace InnerProductSpace ComplexConjugate

namespace TauCeti

/-! ### One-dimensional geometric Clifford action `1 ↦ i` on `ℂ` -/

section RealLine

/-- The one-dimensional real Clifford action on `ℂ` over `-QuadraticMap.sq`, sending `r : ℝ` to
`r • (i • 1)`. -/
def realLineCliffordAction :
    CliffordAlgebra (-QuadraticMap.sq (R := ℝ)) →ₐ[ℝ] Module.End ℂ ℂ :=
  CliffordAlgebra.lift (-QuadraticMap.sq (R := ℝ))
    ⟨LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (Complex.I • (1 : Module.End ℂ ℂ)), fun r ↦ by
      simp only [LinearMap.smulRight_apply, LinearMap.id_coe, id_eq, neg_apply,
        QuadraticMap.sq_apply, Algebra.algebraMap_eq_smul_one]
      rw [smul_mul_smul_comm, smul_mul_smul_comm, one_mul, Complex.I_mul_I, neg_one_smul,
        smul_neg, neg_smul, mul_comm]⟩

/-- `realLineCliffordAction` sends `ι r` to `r • (i • 1)`. -/
@[simp]
theorem realLineCliffordAction_ι (r : ℝ) :
    realLineCliffordAction (ι (-QuadraticMap.sq (R := ℝ)) r) =
      r • (Complex.I • (1 : Module.End ℂ ℂ)) :=
  lift_ι_apply _ _ r

/-- The unit generator `1 : ℝ` acts on `ℂ` by `i • 1`. -/
theorem realLineCliffordAction_ι_one :
    realLineCliffordAction (ι (-QuadraticMap.sq (R := ℝ)) 1) =
      Complex.I • (1 : Module.End ℂ ℂ) := by
  simp

/-- Pointwise action of `realLineCliffordAction` on `z : ℂ`. -/
theorem realLineCliffordAction_ι_apply (r : ℝ) (z : ℂ) :
    realLineCliffordAction (ι (-QuadraticMap.sq (R := ℝ)) r) z = (r : ℂ) * (Complex.I * z) := by
  rw [realLineCliffordAction_ι, LinearMap.smul_apply, LinearMap.smul_apply,
    one_apply_eq_self, Complex.real_smul, smul_eq_mul]

/-- **The 1D real-line Clifford action `1 ↦ i` satisfies `AlgHom.IsGeometricClifford`.** -/
theorem isGeometricClifford_realLineCliffordAction :
    realLineCliffordAction.IsGeometricClifford where
  quadratic_eq r := by
    rw [neg_apply, QuadraticMap.sq_apply, RCLike.inner_apply, conj_trivial, mul_comm]
  inner_map_ι_left r x y := by
    rw [realLineCliffordAction_ι_apply, realLineCliffordAction_ι_apply, RCLike.inner_apply,
      RCLike.inner_apply, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring

end RealLine

/-! ### Two-dimensional negative Pauli plane `e₀ ↦ i Z`, `e₁ ↦ i Y` on `ℂ²` -/

section NegativePlane

/-- Real-linear embedding `(v₀, v₁) ↦ (0, v₁, v₀)` sending the standard basis `e₀, e₁` of
`EuclideanSpace ℝ (Fin 2)` to the `σ₃` and `σ₂` axes in `ℝ³`. -/
private def negativePlanePauliVec : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![0, v.ofLp 1, v.ofLp 0]
  map_add' u v := by
    ext i
    fin_cases i <;> simp
  map_smul' c v := by
    ext i
    fin_cases i <;> simp

/-- Real-linear generator map `v ↦ (i • pauli ![0, v₁, v₀]).toEuclideanLin` on
`EuclideanSpace ℂ (Fin 2)`. -/
private def negativePlanePauliGen :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (Matrix.toEuclideanLin.restrictScalars ℝ).toLinearMap.comp
    ((LinearMap.lsmul ℂ (Matrix (Fin 2) (Fin 2) ℂ) Complex.I).restrictScalars ℝ |>.comp
      (pauli.comp negativePlanePauliVec))

private theorem negativePlanePauliGen_apply (v : EuclideanSpace ℝ (Fin 2)) :
    negativePlanePauliGen v = (Complex.I • pauli ![0, v.ofLp 1, v.ofLp 0]).toEuclideanLin :=
  (rfl)

/-- **The 2D negative Pauli plane Clifford action** on `EuclideanSpace ℂ (Fin 2)` over
`-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2)))`, sending
`e₀ = (1, 0) ↦ i Z` and `e₁ = (0, 1) ↦ i Y`. -/
def negativePlanePauliAction :
    CliffordAlgebra (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2)))) →ₐ[ℝ]
      Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  CliffordAlgebra.lift (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
    ⟨negativePlanePauliGen, fun v ↦ by
      have hmul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
          A.toEuclideanLin * B.toEuclideanLin = (A * B).toEuclideanLin :=
        (map_mul (Matrix.toLpLinAlgEquiv 2) A B).symm
      have hone : (1 : Matrix (Fin 2) (Fin 2) ℂ).toEuclideanLin = 1 :=
        map_one (Matrix.toLpLinAlgEquiv 2)
      rw [negativePlanePauliGen_apply, hmul, smul_mul_smul_comm, Complex.I_mul_I, pauli_mul_self]
      have hv : ⟪v, v⟫_ℝ = v.ofLp 0 * v.ofLp 0 + v.ofLp 1 * v.ofLp 1 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, Fin.sum_univ_two]
      have hdot : (![0, v.ofLp 1, v.ofLp 0] ⬝ᵥ ![0, v.ofLp 1, v.ofLp 0] : ℝ) =
          ⟪v, v⟫_ℝ := by
        rw [hv]
        simp [dotProduct, Fin.sum_univ_three, add_comm]
      rw [hdot, neg_one_smul, map_neg, map_smul, hone, Complex.coe_smul, neg_apply,
        LinearMap.BilinMap.toQuadraticMap_apply, innerₗ_apply_apply,
        Algebra.algebraMap_eq_smul_one, neg_smul]⟩

/-- Action of `negativePlanePauliAction` on a real vector `v : EuclideanSpace ℝ (Fin 2)`. -/
@[simp]
theorem negativePlanePauliAction_ι (v : EuclideanSpace ℝ (Fin 2)) :
    negativePlanePauliAction
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2)))) v) =
      (Complex.I • pauli ![0, v.ofLp 1, v.ofLp 0]).toEuclideanLin :=
  lift_ι_apply _ _ v

/-- The first standard basis vector `e₀ = (1, 0)` acts by `(i • pauli ![0, 0, 1]).toEuclideanLin`
(`i Z`). -/
theorem negativePlanePauliAction_basisFun_zero :
    negativePlanePauliAction
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =
      (Complex.I • pauli ![0, 0, 1]).toEuclideanLin := by
  rw [negativePlanePauliAction_ι]
  congr 3
  ext i
  fin_cases i <;> simp [EuclideanSpace.basisFun_apply]

/-- The second standard basis vector `e₁ = (0, 1)` acts by `(i • pauli ![0, 1, 0]).toEuclideanLin`
(`i Y`). -/
theorem negativePlanePauliAction_basisFun_one :
    negativePlanePauliAction
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)) =
      (Complex.I • pauli ![0, 1, 0]).toEuclideanLin := by
  rw [negativePlanePauliAction_ι]
  congr 3
  ext i
  fin_cases i <;> simp [EuclideanSpace.basisFun_apply]

/-- **The negative Pauli plane action satisfies `AlgHom.IsGeometricClifford`.** -/
theorem isGeometricClifford_negativePlanePauliAction :
    negativePlanePauliAction.IsGeometricClifford := by
  rw [AlgHom.isGeometricClifford_iff_adjoint]
  refine ⟨fun v ↦ by rw [neg_apply, LinearMap.BilinMap.toQuadraticMap_apply, innerₗ_apply_apply],
    fun v ↦ ?_⟩
  rw [negativePlanePauliAction_ι, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_smul, RCLike.star_def, Complex.conj_I,
    (isHermitian_pauli ![0, v.ofLp 1, v.ofLp 0]).eq, neg_smul, map_neg]

/-- On the negative Pauli plane, the oriented bivector `c(e₀) c(e₁)` is `(i • X).toEuclideanLin`. -/
theorem negativePlanePauliAction_bivector :
    negativePlanePauliAction
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)) *
      negativePlanePauliAction
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)) =
      (Complex.I • pauli ![1, 0, 0]).toEuclideanLin := by
  have hmul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
      A.toEuclideanLin * B.toEuclideanLin = (A * B).toEuclideanLin :=
    (map_mul (Matrix.toLpLinAlgEquiv 2) A B).symm
  have hcross : (![0, 0, 1] : Fin 3 → ℝ) ⨯₃ ![0, 1, 0] = -![1, 0, 0] := by
    ext i
    fin_cases i <;> simp [cross_apply]
  have hdot : (![0, 0, 1] ⬝ᵥ ![0, 1, 0] : ℝ) = 0 := by
    simp [dotProduct, Fin.sum_univ_three]
  rw [negativePlanePauliAction_basisFun_zero, negativePlanePauliAction_basisFun_one, hmul,
    smul_mul_smul_comm, Complex.I_mul_I, pauli_mul_pauli, hdot, hcross, map_neg]
  simp

/-- **Chirality on the negative Pauli plane**: for the standard orientation of
`EuclideanSpace ℝ (Fin 2)`, the intrinsic chirality operator
`negativePlanePauliAction.cliffordBaseChange ℂ (complexVolume _ o)` is
`(-pauli ![1, 0, 0]).toEuclideanLin` (`-X`). -/
theorem cliffordBaseChange_complexVolume_negativePlanePauliAction :
    negativePlanePauliAction.cliffordBaseChange ℂ
        (complexVolume (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation) =
      (-pauli ![1, 0, 0]).toEuclideanLin := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 * 1) := ⟨by simp⟩
  refine (negativePlanePauliAction.cliffordBaseChange_complexVolume_eq_of_even (ℓ := 1) _
    isGeometricClifford_negativePlanePauliAction.quadratic_eq_neg_norm_sq
    (EuclideanSpace.basisFun (Fin 2) ℝ) rfl).trans ?_
  have hlist :
      (((List.finRange (2 * 1)).map (EuclideanSpace.basisFun (Fin 2) ℝ)).map fun v ↦
          negativePlanePauliAction
            (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2)))) v)).prod =
        negativePlanePauliAction
            (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
              (EuclideanSpace.basisFun (Fin 2) ℝ 0)) *
          negativePlanePauliAction
            (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
              (EuclideanSpace.basisFun (Fin 2) ℝ 1)) := by
    simp [List.finRange_succ]
  rw [pow_one, hlist, negativePlanePauliAction_bivector, ← map_smul, smul_smul, Complex.I_mul_I,
    neg_one_smul]

/-- **Positive half-spinor witness on the negative Pauli plane**: `(1, -1)` belongs to the
`+1`-eigenspace of the chirality operator `-X` on `EuclideanSpace ℂ (Fin 2)`. -/
theorem mem_eigenspace_negativePlanePauliAction_one :
    WithLp.toLp 2 ![1, -1] ∈
      (negativePlanePauliAction.cliffordBaseChange ℂ
        (complexVolume (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation)).eigenspace 1 := by
  rw [cliffordBaseChange_complexVolume_negativePlanePauliAction, Module.End.mem_eigenspace_iff,
    one_smul, Matrix.toLpLin_apply]
  ext i
  fin_cases i <;> simp [pauli_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Negative half-spinor witness on the negative Pauli plane**: `(1, 1)` belongs to the
`-1`-eigenspace of the chirality operator `-X` on `EuclideanSpace ℂ (Fin 2)`. -/
theorem mem_eigenspace_negativePlanePauliAction_neg_one :
    WithLp.toLp 2 ![1, 1] ∈
      (negativePlanePauliAction.cliffordBaseChange ℂ
        (complexVolume (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation)).eigenspace (-1) := by
  rw [cliffordBaseChange_complexVolume_negativePlanePauliAction, Module.End.mem_eigenspace_iff,
    neg_one_smul, Matrix.toLpLin_apply]
  ext i
  fin_cases i <;> simp [pauli_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end NegativePlane

end TauCeti

end
