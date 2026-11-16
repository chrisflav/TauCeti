/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix
public import TauCeti.Algebra.Coalgebra.Star
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Submodule

/-!
# Conjugate comodules over star bialgebras

Let `A` be a star bialgebra over a commutative star ring `R`, meaning a bialgebra with a
conjugate-linear involution `star` satisfying `Δ(a*) = Δ(a)*` (`TauCeti.StarCoalgebra R A`).
For any comodule `M` with a finite basis `b` and coefficient matrix `u`, the entrywise-starred
matrix `u.map star` again satisfies the matrix comultiplication and counit identities, and
therefore defines the *conjugate comodule* on `ι → R` via `TauCeti.Comodule.matrixComodule`.

Over a field with an involution `star`, the coordinatewise conjugate-linear equivalence
`m ↦ (i ↦ star (b.repr m i))` pairs matrix coefficients of the conjugate comodule with the
stars of matrix coefficients of `M`. Using the matrix-coefficient characterization of
subcomodules (`Submodule.coact_mem_range_iff_forall_matrixCoefficient_eq_zero`), this induces an
order isomorphism between the subcomodule lattices of `M` and its conjugate comodule; in
particular, the conjugate of a simple comodule is simple.

## Main declarations

* `TauCeti.Comodule.conjugateComodule`: the comodule on `ι → R` with coefficient matrix
  `(coefficientMatrix b).map star`.
* `TauCeti.Comodule.coefficientMatrix_conjugateComodule`: the coefficient matrix of
  `conjugateComodule b` in the standard coordinate basis is `(coefficientMatrix b).map star`.
* `TauCeti.Comodule.conjugateSubcomoduleOrderIso`: over a field with star, the order isomorphism
  between subcomodules of `M` and subcomodules of `conjugateComodule b`.
* `TauCeti.Comodule.isSimpleOrder_conjugateComodule_iff`: `conjugateComodule b` is simple
  exactly when `M` is simple.

## References

* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Section 1.3.
* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.Comodule

section Bialgebra

variable {R A M ι : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [Bialgebra R A] [StarRing A] [StarModule R A] [StarCoalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M] [Fintype ι]

/-- Entrywise star preserves the matrix comultiplication identity of a coefficient matrix. -/
private theorem map_comul_coefficientMatrix_map_star (b : Basis ι R M) :
    ((coefficientMatrix (C := A) b).map star).map (Bialgebra.comulAlgHom R A) =
      ((coefficientMatrix (C := A) b).map star).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        ((coefficientMatrix (C := A) b).map star).map
          (Algebra.TensorProduct.includeRight (R := R)) := by
  rw [map_comul_iff]
  intro i j
  rw [Matrix.map_apply, StarCoalgebra.comul_star, comul_coefficientMatrix_eq_sum, star_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp

omit [Fintype ι] in
/-- Entrywise star preserves the matrix counit identity of a coefficient matrix. -/
private theorem counit_basisFun_coefficientMatrix_map_star [Finite ι] (b : Basis ι R M) (i j : ι) :
    Coalgebra.counit (R := R) (((coefficientMatrix (C := A) b).map star) i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i := by
  classical
  rw [Matrix.map_apply, StarCoalgebra.counit_star, counit_coefficientMatrix,
    Basis.repr_self_apply]
  by_cases h : i = j <;> simp [h, eq_comm]

/-- The **conjugate comodule** of a finite free comodule in a basis `b`: the comodule on
`ι → R` whose coefficient matrix is `(coefficientMatrix b).map star`. -/
@[instance_reducible]
noncomputable def conjugateComodule (b : Basis ι R M) : Comodule R A (ι → R) :=
  matrixComodule R ((coefficientMatrix (C := A) b).map star)
    (map_comul_coefficientMatrix_map_star (A := A) b)
    (counit_basisFun_coefficientMatrix_map_star (A := A) b)

/-- The coefficient matrix of the conjugate comodule in the standard coordinate basis is the
entrywise star of the original coefficient matrix. -/
theorem coefficientMatrix_conjugateComodule (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := conjugateComodule (A := A) b
    coefficientMatrix (C := A) (Pi.basisFun R ι) = (coefficientMatrix (C := A) b).map star :=
  coefficientMatrix_matrixComodule R ((coefficientMatrix (C := A) b).map star)
    (map_comul_coefficientMatrix_map_star (A := A) b)
    (counit_basisFun_coefficientMatrix_map_star (A := A) b)

end Bialgebra

section Field

variable {k A M ι : Type*} [Field k] [StarRing k]
  [Semiring A] [Bialgebra k A] [StarRing A] [StarModule k A] [StarCoalgebra k A]
  [AddCommMonoid M] [Module k M] [Comodule k A M] [Fintype ι]

/-- The coordinatewise conjugate-linear equivalence `m ↦ (i ↦ star (b.repr m i))` attached to a
finite basis `b`. -/
private noncomputable def coordStarEquiv (b : Basis ι k M) :
    M ≃ₛₗ[starRingEnd k] (ι → k) where
  toFun m i := star (b.repr m i)
  map_add' m₁ m₂ := by ext i; simp
  map_smul' c m := by ext i; simp [starRingEnd_apply]
  invFun v := ∑ i, star (v i) • b i
  left_inv m := by
    conv_rhs => rw [← b.sum_repr m]
    simp
  right_inv v := by
    classical
    ext i
    simp [map_sum, Finsupp.single_apply]

/-- Pull a functional on `ι → k` back along `coordStarEquiv b` and conjugate its values to obtain
a `k`-linear functional on `M`. -/
private noncomputable def dualPullback (b : Basis ι k M) (ψ : Module.Dual k (ι → k)) :
    Module.Dual k M where
  toFun m := star (ψ (coordStarEquiv b m))
  map_add' m₁ m₂ := by simp
  map_smul' c m := by
    simp [map_smulₛₗ, starRingEnd_apply, smul_eq_mul]

/-- The matrix coefficient of `conjugateComodule b` against `ψ` at `coordStarEquiv b m` is the
star of the matrix coefficient of `M` against `dualPullback b ψ` at `m`. -/
private theorem matrixCoefficient_conjugateComodule (b : Basis ι k M)
    (ψ : Module.Dual k (ι → k)) (m : M) :
    letI : Comodule k A (ι → k) := conjugateComodule (A := A) b
    matrixCoefficient (R := k) (C := A) ψ (coordStarEquiv b m) =
      star (matrixCoefficient (R := k) (C := A) (dualPullback b ψ) m) := by
  classical
  let : Comodule k A (ι → k) := conjugateComodule (A := A) b
  have hbasis (j : ι) : coordStarEquiv b (b j) = Pi.basisFun k ι j := by
    ext i
    simp [coordStarEquiv, Pi.basisFun_apply, Pi.single_apply, Finsupp.single_apply,
      apply_ite star, eq_comm]
  have hm : m = ∑ j, b.repr m j • b j := (b.sum_repr m).symm
  have hem : coordStarEquiv b m = ∑ j, star (b.repr m j) • Pi.basisFun k ι j := by
    conv_lhs => rw [hm]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smulₛₗ, starRingEnd_apply, hbasis]
  conv_lhs => rw [hem]
  conv_rhs => rw [hm]
  simp only [matrixCoefficient_def, map_sum, map_smul,
    coact_basis_eq_sum_coefficientMatrix (Pi.basisFun k ι),
    coact_basis_eq_sum_coefficientMatrix b, coefficientMatrix_conjugateComodule,
    TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul, Matrix.map_apply,
    star_sum, star_smul, dualPullback, LinearMap.coe_mk, AddHom.coe_mk, hbasis, star_star]

/-- Forward direction of subcomodule correspondence under `coordStarEquiv b`. -/
private theorem map_coordStarEquiv_coact_mem (b : Basis ι k M) (W : Subcomodule k A M) :
    letI : Comodule k A (ι → k) := conjugateComodule (A := A) b
    ∀ ⦃v⦄, v ∈ W.toSubmodule.map (coordStarEquiv b).toLinearMap →
      coact (R := k) (C := A) (M := ι → k) v ∈
        LinearMap.range (TensorProduct.map
          (W.toSubmodule.map (coordStarEquiv b).toLinearMap).subtype
          (LinearMap.id : A →ₗ[k] A)) := by
  let : AddCommGroup A := Module.addCommMonoidToAddCommGroup k
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let : Comodule k A (ι → k) := conjugateComodule (A := A) b
  intro v hv
  obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hv
  rw [Submodule.coact_mem_range_iff_forall_matrixCoefficient_eq_zero]
  intro ψ
  rw [LinearEquiv.coe_toLinearMap, matrixCoefficient_conjugateComodule]
  set φ : Module.Dual k M := dualPullback b (ψ ∘ₗ _)
  have hφ : ∀ w ∈ W.toSubmodule, φ w = 0 := by
    intro w hw
    have hw' : coordStarEquiv b w ∈ W.toSubmodule.map (coordStarEquiv b).toLinearMap :=
      Submodule.mem_map_of_mem hw
    simp [φ, dualPullback, (Submodule.Quotient.mk_eq_zero _).mpr hw']
  have hfac : φ = W.toSubmodule.liftQ φ (fun w hw ↦ hφ w hw) ∘ₗ W.toSubmodule.mkQ := by
    ext x; rfl
  have hm0 := (W.toSubmodule.coact_mem_range_iff_forall_matrixCoefficient_eq_zero m).mp
    (W.coact_mem' hm) (W.toSubmodule.liftQ φ (fun w hw ↦ hφ w hw))
  rw [hfac, hm0, star_zero]

/-- Backward direction of subcomodule correspondence under `coordStarEquiv b`. -/
private theorem comap_coordStarEquiv_coact_mem (b : Basis ι k M) :
    letI : Comodule k A (ι → k) := conjugateComodule (A := A) b
    ∀ (V : Subcomodule k A (ι → k)) ⦃m : M⦄,
      m ∈ V.toSubmodule.comap (coordStarEquiv b).toLinearMap →
      coact (R := k) (C := A) (M := M) m ∈
        LinearMap.range (TensorProduct.map
          (V.toSubmodule.comap (coordStarEquiv b).toLinearMap).subtype
          (LinearMap.id : A →ₗ[k] A)) := by
  let : AddCommGroup A := Module.addCommMonoidToAddCommGroup k
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let : Comodule k A (ι → k) := conjugateComodule (A := A) b
  intro V m hm
  rw [Submodule.coact_mem_range_iff_forall_matrixCoefficient_eq_zero]
  intro φ
  set ψ : Module.Dual k (ι → k) :=
    { toFun v := star (φ ((V.toSubmodule.comap (coordStarEquiv b).toLinearMap).mkQ
        ((coordStarEquiv b).symm v)))
      map_add' v₁ v₂ := by simp
      map_smul' c v := by
        simp [map_smulₛₗ, starRingEnd_apply, smul_eq_mul] }
  have hψ : ∀ v ∈ V.toSubmodule, ψ v = 0 := by
    intro v hv
    have hv' : (coordStarEquiv b).symm v ∈ V.toSubmodule.comap (coordStarEquiv b).toLinearMap := by
      simpa using hv
    simp [ψ, (Submodule.Quotient.mk_eq_zero _).mpr hv']
  have hfac : ψ = V.toSubmodule.liftQ ψ (fun v hv ↦ hψ v hv) ∘ₗ V.toSubmodule.mkQ := by
    ext v; rfl
  have hdual :
      dualPullback b ψ = φ ∘ₗ (V.toSubmodule.comap (coordStarEquiv b).toLinearMap).mkQ := by
    ext x; simp [dualPullback, ψ]
  have hv0 := (V.toSubmodule.coact_mem_range_iff_forall_matrixCoefficient_eq_zero
    (coordStarEquiv b m)).mp (V.coact_mem' hm)
    (V.toSubmodule.liftQ ψ (fun v hv ↦ hψ v hv))
  rw [← hfac, matrixCoefficient_conjugateComodule, hdual, star_eq_zero] at hv0
  exact hv0

/-- Over a field with star, `coordStarEquiv b` induces an order isomorphism between the
subcomodule lattices of `M` and its conjugate comodule `conjugateComodule b`. -/
noncomputable def conjugateSubcomoduleOrderIso (b : Basis ι k M) :
    letI : Comodule k A (ι → k) := conjugateComodule (A := A) b
    Subcomodule k A M ≃o Subcomodule k A (ι → k) := by
  let : Comodule k A (ι → k) := conjugateComodule (A := A) b
  refine
    { toFun W := ⟨W.toSubmodule.map (coordStarEquiv b).toLinearMap,
        map_coordStarEquiv_coact_mem b W⟩
      invFun V := ⟨V.toSubmodule.comap (coordStarEquiv b).toLinearMap,
        comap_coordStarEquiv_coact_mem b V⟩
      left_inv W := by
        ext m
        simp only [← Subcomodule.mem_carrier, Subcomodule.toSubmodule, Submodule.mem_comap,
          Submodule.mem_map, LinearEquiv.coe_toLinearMap, EmbeddingLike.apply_eq_iff_eq,
          exists_eq_right]
      right_inv V := by
        ext v
        simp only [← Subcomodule.mem_carrier, Subcomodule.toSubmodule, Submodule.mem_map,
          Submodule.mem_comap, LinearEquiv.coe_toLinearMap]
        exact ⟨fun ⟨_, hm, hmv⟩ ↦ hmv ▸ hm,
          fun hv ↦ ⟨(coordStarEquiv b).symm v, by simpa using hv,
            (coordStarEquiv b).apply_symm_apply v⟩⟩
      map_rel_iff' := by
        intro W₁ W₂
        simp only [← Subcomodule.toSubmodule_le_toSubmodule]
        refine ⟨fun h m hm ↦ ?_, fun h ↦ Submodule.map_mono h⟩
        obtain ⟨m', hm', heq⟩ := h (Submodule.mem_map_of_mem hm)
        rwa [← (coordStarEquiv b).injective heq] }

/-- The conjugate comodule of a finite free comodule over a field with star is simple precisely
when the original comodule is simple. -/
theorem isSimpleOrder_conjugateComodule_iff (b : Basis ι k M) :
    (letI : Comodule k A (ι → k) := conjugateComodule (A := A) b;
      IsSimpleOrder (Subcomodule k A (ι → k))) ↔ IsSimpleOrder (Subcomodule k A M) :=
  (conjugateSubcomoduleOrderIso (A := A) b).symm.isSimpleOrder_iff

end Field

end TauCeti.Comodule
