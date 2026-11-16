/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep
public import TauCeti.RepresentationTheory.Continuous.StableLattice
public import TauCeti.Topology.Algebra.IntermediateField

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Topology.Baire.LocallyCompactRegular
import TauCeti.Algebra.Module.Lattice
import TauCeti.LinearAlgebra.LinearMap.BaseChange
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Range
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.NumberTheory.Padics.Subfield
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
import TauCeti.Topology.Algebra.Group.Baire

/-!
# Coefficient-field and integral descent for continuous representations

A continuous matrix homomorphism `ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` from a compact Hausdorff
topological group `Γ` has image contained in `GL ι E` for a single finite intermediate field
`ℚ_[ℓ] ⊆ E ⊆ PadicAlgCl ℓ`, which may be chosen to contain any prescribed finite extension
`K / ℚ_[ℓ]`. The proof is a Baire category argument: for each finite intermediate field `E`, the
preimage `H E = ρ⁻¹(GL ι E)` is a closed subgroup of `Γ` (since `E` is closed in `PadicAlgCl ℓ`);
these countably many closed subgroups cover the compact Hausdorff Baire space `Γ`, so some `H E₀`
is open and hence of finite index; adjoining the matrix entries of `ρ` on finitely many coset
representatives yields a finite coefficient field `E` containing `K` and the whole image of `ρ`.

This yields categorical descent of finite-dimensional continuous representations over `PadicAlgCl ℓ`
to finite coefficient fields: every finite-dimensional continuous representation over `PadicAlgCl ℓ`
descends to a finite intermediate field `E` containing any prescribed finite `K`
(`TauCeti.ContinuousRep.exists_finiteDimensional_baseChange_iso`), and any finite diagram of
finite-dimensional continuous representations and intertwining maps descends simultaneously to a
single finite intermediate field (`TauCeti.ContinuousRep.exists_finiteDimensional_diagram_descent`).
Together with the algebraic faithfulness and enlargement-agreement theorems in
`TauCeti.RepresentationTheory.Intertwining.Descent`, this identifies the category of
finite-dimensional continuous representations over `PadicAlgCl ℓ` as the filtered 2-colimit of those
over finite coefficient fields.

Combining coefficient-field descent with the stable-lattice theorem over valuatively topologized
fields (`TauCeti.ContinuousRep.exists_stable_lattice`), every continuous matrix homomorphism
`ρ : Γ →ₜ* GL ι E` over a valuatively topologized field whose valuation ring `𝒪[E]` is a principal
ideal domain is conjugate in `GL ι E` into matrices with entries in `𝒪[E]`
(`ContinuousMonoidHom.exists_conj_mem_integerRing`), and consequently every continuous
`ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` is conjugate into the closed unit ball of a finite intermediate
field `E` (`ContinuousMonoidHom.exists_integral_conj_GL`).

## Main results

* `ContinuousMonoidHom.exists_finiteDimensional_mem_of_countable`,
  `ContinuousMonoidHom.exists_finiteDimensional_mem`,
  `ContinuousMonoidHom.exists_finiteDimensional_factor_GL`: Baire coefficient-field descent for
  continuous matrix homomorphisms.
* `TauCeti.ContinuousRep.exists_finiteDimensional_baseChange_iso_of_countable`,
  `TauCeti.ContinuousRep.exists_finiteDimensional_baseChange_iso`,
  `TauCeti.ContinuousRep.exists_finiteDimensional_diagram_descent_of_countable`,
  `TauCeti.ContinuousRep.exists_finiteDimensional_diagram_descent`: descent of continuous
  representations and finite diagrams to a single finite coefficient field.
* `ContinuousMonoidHom.exists_conj_mem_integerRing`,
  `ContinuousMonoidHom.exists_integral_conj_GL_of_le`,
  `ContinuousMonoidHom.exists_integral_conj_GL`: integral descent into the integers of a
  discretely valued field and of a finite intermediate field of `PadicAlgCl ℓ`.

## References

* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *$\widehat{G}$-local systems on smooth projective
  curves are potentially automorphic*, Acta Math. 223 (2019), 1–111, Theorem 4.8.
* F. Calegari and D. Geraghty, *Modularity lifting beyond the Taylor–Wiles method*, Invent. Math.
  211 (2018), 297–433, §6.2, Proposition 6.8.
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
* K. A. Ribet, *Galois representations attached to eigenforms with Nebentypus*, §2.
-/

public section

open Matrix IntermediateField ValuativeRel
open scoped TensorProduct

section MatrixHelpers

/-- A matrix in `GL ι Ω` lies in the image of `GL ι E → GL ι Ω` if and only if all its entries
belong to the intermediate field `E`. -/
private theorem mem_range_generalLinearGroup_map_intermediateField_iff {F Ω : Type*}
    [Field F] [Field Ω] [Algebra F Ω] (E : IntermediateField F Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : GL ι Ω) :
    M ∈ (Matrix.GeneralLinearGroup.map E.val.toRingHom).range ↔
      ∀ i j, (M : Matrix ι ι Ω) i j ∈ E := by
  rw [Matrix.GeneralLinearGroup.mem_range_map_iff]
  exact forall₂_congr fun _ _ ↦ ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun hx ↦ ⟨⟨_, hx⟩, rfl⟩⟩

/-- The topological embedding `GL ι E →ₜ* GL ι Ω` induced by an intermediate field `E ⊆ Ω`. -/
private def intermediateFieldGLHom {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    [TopologicalSpace Ω] (E : IntermediateField F Ω) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    GL ι E →ₜ* GL ι Ω where
  toMonoidHom := Matrix.GeneralLinearGroup.map E.val.toRingHom
  continuous_toFun := Topology.IsInducing.subtypeVal.generalLinearGroup_map.continuous

private theorem isEmbedding_intermediateFieldGLHom {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    [TopologicalSpace Ω] (E : IntermediateField F Ω) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Topology.IsEmbedding (intermediateFieldGLHom E ι) :=
  ⟨Topology.IsInducing.subtypeVal.generalLinearGroup_map,
    Matrix.GeneralLinearGroup.map_injective Subtype.val_injective⟩

/-- Factor a continuous homomorphism `Γ →ₜ* GL ι Ω` whose matrix entries all lie in an intermediate
field `E` through `GL ι E`, preserving continuity for the subspace topology on `E`. -/
private noncomputable def factorGL {Γ F Ω : Type*} [Monoid Γ] [TopologicalSpace Γ]
    [Field F] [Field Ω] [Algebra F Ω] [TopologicalSpace Ω]
    (E : IntermediateField F Ω) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι Ω) (hρ : ∀ g i j, (ρ g : Matrix ι ι Ω) i j ∈ E) :
    Γ →ₜ* GL ι E :=
  let j := intermediateFieldGLHom E ι
  let ρ' : Γ →ₜ* (j : GL ι E →* GL ι Ω).range :=
    { toFun g := ⟨ρ g, (mem_range_generalLinearGroup_map_intermediateField_iff E (ρ g)).mpr (hρ g)⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' g₁ g₂ := Subtype.ext (map_mul ρ g₁ g₂)
      continuous_toFun := ρ.continuous.subtype_mk _ }
  let e := j.equivRangeOfIsEmbedding (isEmbedding_intermediateFieldGLHom E ι)
  (ContinuousMonoidHom.toContinuousMonoidHom e.symm).comp ρ'

private theorem generalLinearGroup_map_factorGL {Γ F Ω : Type*} [Monoid Γ] [TopologicalSpace Γ]
    [Field F] [Field Ω] [Algebra F Ω] [TopologicalSpace Ω]
    (E : IntermediateField F Ω) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι Ω) (hρ : ∀ g i j, (ρ g : Matrix ι ι Ω) i j ∈ E) (g : Γ) :
    Matrix.GeneralLinearGroup.map E.val.toRingHom (factorGL E ρ hρ g) = ρ g := by
  let j := intermediateFieldGLHom E ι
  let hj := isEmbedding_intermediateFieldGLHom E ι
  let y : (j : GL ι E →* GL ι Ω).range :=
    ⟨ρ g, (mem_range_generalLinearGroup_map_intermediateField_iff E (ρ g)).mpr (hρ g)⟩
  have hfactor : factorGL E ρ hρ g = (j.equivRangeOfIsEmbedding hj).symm y := by
    simp only [factorGL, ContinuousMonoidHom.coe_comp, Function.comp_apply,
      ContinuousMonoidHom.coe_coe]
    rfl
  have h : j ((j.equivRangeOfIsEmbedding hj).symm y) = ρ g := by
    have h' := congrArg Subtype.val ((j.equivRangeOfIsEmbedding hj).apply_symm_apply y)
    rwa [ContinuousMonoidHom.equivRangeOfIsEmbedding_apply] at h'
  rw [← hfactor] at h
  exact h

end MatrixHelpers

namespace ContinuousMonoidHom

section MatrixDescent

/-- **General Baire coefficient-field descent.** Let `Ω / F` be an algebraic extension of fields
with a topology on `Ω` such that the finite intermediate fields are countably many and each is
closed in `Ω`. Then any continuous homomorphism `ρ : Γ →ₜ* GL ι Ω` from a compact Hausdorff group
with separately continuous multiplication has all matrix entries in a single finite intermediate
field `E` containing any prescribed finite `K`. -/
theorem exists_finiteDimensional_mem_of_countable {Γ F Ω : Type*}
    [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ] [CompactSpace Γ] [T2Space Γ]
    [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω] [TopologicalSpace Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι Ω)
    (hclosed : ∀ E : IntermediateField F Ω, FiniteDimensional F E → IsClosed (E : Set Ω))
    (hcount : Set.Countable {E : IntermediateField F Ω | FiniteDimensional F E})
    (K : IntermediateField F Ω) [FiniteDimensional F K] :
    ∃ E : IntermediateField F Ω, K ≤ E ∧ FiniteDimensional F E ∧
      ∀ (g : Γ) (i j : ι), (ρ g : Matrix ι ι Ω) i j ∈ E := by
  have : BaireSpace Γ := BaireSpace.of_t2Space_locallyCompactSpace
  let H : IntermediateField F Ω → Subgroup Γ := fun E ↦
    (Matrix.GeneralLinearGroup.map E.val.toRingHom).range.comap ρ.toMonoidHom
  -- Step 1: for each finite `E`, `H E = ρ⁻¹(GL ι E)` is closed since `E` is closed in `Ω`.
  have hH_closed : ∀ E ∈ {E : IntermediateField F Ω | FiniteDimensional F E},
      IsClosed (H E : Set Γ) := by
    intro E hE
    have hset : (H E : Set Γ) =
        ⋂ i : ι, ⋂ j : ι, (fun g : Γ ↦ (ρ g : Matrix ι ι Ω) i j) ⁻¹' (E : Set Ω) := by
      ext g
      simp only [SetLike.mem_coe, H, Subgroup.mem_comap, MonoidHom.coe_ofClass,
        ContinuousMonoidHom.coe_toMonoidHom,
        mem_range_generalLinearGroup_map_intermediateField_iff, Set.mem_iInter, Set.mem_preimage]
    rw [hset]
    refine isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ (hclosed E hE).preimage ?_
    exact (_root_.continuous_apply j).comp
      (Matrix.GeneralLinearGroup.continuous_apply ρ ρ.continuous i)
  -- Step 2: the subgroups `H E` cover `Γ`, since each matrix has finitely many algebraic entries.
  have hH_cover :
      ⋃ E ∈ {E : IntermediateField F Ω | FiniteDimensional F E}, (H E : Set Γ) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun g ↦ ?_
    let Eg : IntermediateField F Ω :=
      IntermediateField.adjoin F (Set.range fun p : ι × ι ↦ (ρ g : Matrix ι ι Ω) p.1 p.2)
    have hEg_fin : FiniteDimensional F Eg :=
      IntermediateField.finiteDimensional_adjoin fun _ _ ↦ Algebra.IsIntegral.isIntegral _
    refine Set.mem_biUnion hEg_fin ?_
    rw [SetLike.mem_coe, Subgroup.mem_comap, ContinuousMonoidHom.coe_toMonoidHom,
      mem_range_generalLinearGroup_map_intermediateField_iff]
    intro i j
    exact IntermediateField.subset_adjoin F _ ⟨(i, j), rfl⟩
  -- Step 3: Baire category yields an open `H E₀`; compactness gives finite index, so adjoining
  -- coset-representative matrix entries produces a finite field `E ≥ K` containing all of `ρ(Γ)`.
  obtain ⟨E₀, hE₀_fin, hE₀_open⟩ :=
    Subgroup.exists_isOpen_of_biUnion_eq_univ hcount hH_closed hH_cover
  have : FiniteDimensional F E₀ := hE₀_fin
  have : Finite (Γ ⧸ H E₀) := Subgroup.quotient_finite_of_isOpen (H E₀) hE₀_open
  let S : Set Ω := Set.range fun p : (Γ ⧸ H E₀) × ι × ι ↦
    (ρ (Quotient.out p.1) : Matrix ι ι Ω) p.2.1 p.2.2
  have : Finite S := Set.finite_range _
  let E : IntermediateField F Ω := K ⊔ E₀ ⊔ IntermediateField.adjoin F S
  have hS_fin : FiniteDimensional F (IntermediateField.adjoin F S) :=
    IntermediateField.finiteDimensional_adjoin fun _ _ ↦ Algebra.IsIntegral.isIntegral _
  have hE_fin : FiniteDimensional F E := inferInstance
  refine ⟨E, le_sup_left.trans le_sup_left, hE_fin, fun g i j ↦ ?_⟩
  let q : Γ ⧸ H E₀ := QuotientGroup.mk g
  have hmem₀ : (Quotient.out q)⁻¹ * g ∈ H E₀ := by
    rw [← QuotientGroup.eq]
    exact Quotient.out_eq q
  have hρ_out : ρ (Quotient.out q) ∈ (Matrix.GeneralLinearGroup.map E.val.toRingHom).range :=
    (mem_range_generalLinearGroup_map_intermediateField_iff E _).mpr fun r s ↦
      (le_sup_right : IntermediateField.adjoin F S ≤ E)
        (IntermediateField.subset_adjoin F S ⟨(q, r, s), rfl⟩)
  have hρ_in :
      ρ ((Quotient.out q)⁻¹ * g) ∈ (Matrix.GeneralLinearGroup.map E.val.toRingHom).range :=
    (mem_range_generalLinearGroup_map_intermediateField_iff E _).mpr fun r s ↦
      (le_sup_right.trans le_sup_left : E₀ ≤ E)
        ((mem_range_generalLinearGroup_map_intermediateField_iff E₀ _).mp hmem₀ r s)
  have hρg : ρ g ∈ (Matrix.GeneralLinearGroup.map E.val.toRingHom).range := by
    have hmul : ρ g = ρ (Quotient.out q) * ρ ((Quotient.out q)⁻¹ * g) := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [hmul]
    exact mul_mem hρ_out hρ_in
  exact (mem_range_generalLinearGroup_map_intermediateField_iff E _).mp hρg i j

/-- **Coefficient-field descent from `PadicAlgCl ℓ`.** Every continuous matrix homomorphism
`ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` of a compact Hausdorff group with separately continuous
multiplication has all matrix entries in a single finite intermediate field `E / ℚ_[ℓ]` containing
any prescribed finite `K / ℚ_[ℓ]`. -/
theorem exists_finiteDimensional_mem {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [SeparatelyContinuousMul Γ] [CompactSpace Γ] [T2Space Γ]
    {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ))
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ), K ≤ E ∧ FiniteDimensional ℚ_[ℓ] E ∧
      ∀ (g : Γ) (i j : ι), (ρ g : Matrix ι ι (PadicAlgCl ℓ)) i j ∈ E :=
  ρ.exists_finiteDimensional_mem_of_countable
    (fun E _ ↦ E.isClosed_of_finiteDimensional)
    (PadicAlgCl.countable_finiteDimensional ℓ) K

/-- **Continuous factorization through a finite coefficient field.** A continuous matrix
homomorphism `ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` of a compact Hausdorff group with separately
continuous multiplication factors continuously through `GL ι E` for a finite intermediate field
`E / ℚ_[ℓ]` containing any prescribed finite `K`. -/
theorem exists_finiteDimensional_factor_GL {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [SeparatelyContinuousMul Γ] [CompactSpace Γ] [T2Space Γ] {ℓ : ℕ} [Fact ℓ.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ))
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρE : Γ →ₜ* GL ι E),
      K ≤ E ∧ ∀ g : Γ, Matrix.GeneralLinearGroup.map E.val.toRingHom (ρE g) = ρ g := by
  obtain ⟨E, hKE, hEfin, hmem⟩ := ρ.exists_finiteDimensional_mem K
  exact ⟨E, hEfin, factorGL E ρ hmem, hKE, generalLinearGroup_map_factorGL E ρ hmem⟩

end MatrixDescent

end ContinuousMonoidHom

namespace TauCeti.ContinuousRep

section CategoricalDescent

/-- Continuous representation on `ι → R` attached to a continuous matrix homomorphism
`Γ →ₜ* GL ι R`. -/
private def ofMatrixHom {Γ R ι : Type*} [Monoid Γ] [TopologicalSpace Γ]
    [CommRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι R) : ContinuousRep Γ R (ι → R) where
  toRepresentation :=
    { toFun g := Matrix.toLin' (ρ g : Matrix ι ι R)
      map_one' := by
        ext v i
        simp
      map_mul' g₁ g₂ := by
        ext v i
        simp [Matrix.toLin'_apply] }
  continuous_action := by
    refine continuous_pi fun i ↦ ?_
    simp_rw [MonoidHom.coe_mk, OneHom.coe_mk, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine continuous_finsetSum _ fun j _ ↦ ?_
    exact (((_root_.continuous_apply j).comp
      (Matrix.GeneralLinearGroup.continuous_apply ρ ρ.continuous i)).comp continuous_fst).mul
      ((_root_.continuous_apply j).comp continuous_snd)

@[simp]
private theorem ofMatrixHom_apply {Γ R ι : Type*} [Monoid Γ] [TopologicalSpace Γ]
    [CommRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι R) (g : Γ) (v : ι → R) :
    ofMatrixHom ρ g v = (ρ g : Matrix ι ι R) *ᵥ v :=
  rfl

/-- Matrix homomorphism `Γ →ₜ* GL ι Ω` attached to a continuous representation on a finite-
dimensional vector space with its module topology, relative to a basis `b`. Continuity of the
inverse matrix uses Cramer's rule over the topological division ring `Ω`. -/
private noncomputable def toMatrixHom {Γ Ω V ι : Type*}
    [Group Γ] [TopologicalSpace Γ]
    [Field Ω] [TopologicalSpace Ω] [IsTopologicalDivisionRing Ω]
    [AddCommGroup V] [Module Ω V] [TopologicalSpace V] [IsModuleTopology Ω V]
    [Fintype ι] [DecidableEq ι]
    (ρ : ContinuousRep Γ Ω V) (b : Module.Basis ι Ω V) : Γ →ₜ* GL ι Ω :=
  let toMat : Γ → Matrix ι ι Ω := fun g ↦ LinearMap.toMatrix b b (ρ g)
  have hmul (g₁ g₂ : Γ) : toMat (g₁ * g₂) = toMat g₁ * toMat g₂ := by
    simp only [toMat, map_mul, LinearMap.toMatrix_mul]
  have hone : toMat 1 = 1 := by
    simp only [toMat, map_one, LinearMap.toMatrix_one]
  let toGL : Γ → GL ι Ω := fun g ↦
    ⟨toMat g, toMat g⁻¹, by rw [← hmul, mul_inv_cancel, hone],
      by rw [← hmul, inv_mul_cancel, hone]⟩
  have hcont_mat : Continuous toMat := by
    have : ContinuousAdd V := IsModuleTopology.toContinuousAdd Ω V
    have hequiv : Continuous b.equivFun :=
      IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
    refine continuous_matrix fun i j ↦ ?_
    simp_rw [toMat, LinearMap.toMatrix_apply]
    exact ((_root_.continuous_apply i).comp hequiv).comp (ρ.continuous_orbit (b j))
  have hcont_inv : Continuous fun g : Γ ↦ toMat g⁻¹ := by
    have hinv_eq (g : Γ) : toMat g⁻¹ = (toMat g)⁻¹ :=
      (Matrix.inv_eq_right_inv (by rw [← hmul, mul_inv_cancel, hone])).symm
    simp_rw [hinv_eq]
    refine continuous_iff_continuousAt.mpr fun g ↦ ?_
    have hdet : (toMat g).det ≠ 0 := (toGL g).det_ne_zero
    have hRingInv : ContinuousAt Ring.inverse (toMat g).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet
    exact (continuousAt_matrix_inv (toMat g) hRingInv).comp hcont_mat.continuousAt
  { toFun := toGL
    map_one' := Units.ext hone
    map_mul' g₁ g₂ := Units.ext (hmul g₁ g₂)
    continuous_toFun := Units.continuous_iff.mpr ⟨hcont_mat, hcont_inv⟩ }

private theorem toMatrixHom_coe_apply {Γ Ω V ι : Type*}
    [Group Γ] [TopologicalSpace Γ]
    [Field Ω] [TopologicalSpace Ω] [IsTopologicalDivisionRing Ω]
    [AddCommGroup V] [Module Ω V] [TopologicalSpace V] [IsModuleTopology Ω V]
    [Fintype ι] [DecidableEq ι]
    (ρ : ContinuousRep Γ Ω V) (b : Module.Basis ι Ω V) (g : Γ) (i j : ι) :
    (toMatrixHom ρ b g : Matrix ι ι Ω) i j = b.repr (ρ g (b j)) i :=
  LinearMap.toMatrix_apply b b (ρ g) i j

/-- Canonical equivariant linear equivalence between the scalar extension of the descended matrix
representation `ofMatrixHom (factorGL E (toMatrixHom ρ b) hmem)` and `ρ`. -/
private noncomputable def baseChangeFactorEquiv {Γ F Ω V ι : Type*}
    [Group Γ] [TopologicalSpace Γ]
    [Field F] [Field Ω] [Algebra F Ω] [TopologicalSpace Ω] [IsTopologicalDivisionRing Ω]
    [AddCommGroup V] [Module Ω V] [TopologicalSpace V] [IsModuleTopology Ω V]
    [Fintype ι] [DecidableEq ι]
    (ρ : ContinuousRep Γ Ω V) (b : Module.Basis ι Ω V)
    (E : IntermediateField F Ω)
    (hmem : ∀ g i j, (toMatrixHom ρ b g : Matrix ι ι Ω) i j ∈ E) :
    ((ofMatrixHom (factorGL E (toMatrixHom ρ b) hmem)).toRepresentation.baseChange Ω).Equiv
      ρ.toRepresentation :=
  let e : Ω ⊗[E] (ι → E) ≃ₗ[Ω] V :=
    (TensorProduct.piScalarRight E Ω Ω ι).trans b.equivFun.symm
  Representation.Equiv.mk e fun g ↦ by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Representation.baseChange_apply,
      LinearMap.baseChange_tmul, coe_toRepresentation, ofMatrixHom_apply]
    have hmul : ∀ i : ι,
        (((factorGL E (toMatrixHom ρ b) hmem g : Matrix ι ι E) *ᵥ v) i : Ω) =
          ∑ j : ι, (toMatrixHom ρ b g : Matrix ι ι Ω) i j * (v j : Ω) := by
      intro i
      rw [← IntermediateField.coe_val]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, IntermediateField.coe_val]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hij : ((factorGL E (toMatrixHom ρ b) hmem g : Matrix ι ι E) i j : Ω) =
          (toMatrixHom ρ b g : Matrix ι ι Ω) i j :=
        congrFun (congrFun (congrArg (fun X : GL ι Ω ↦ (X : Matrix ι ι Ω))
          (generalLinearGroup_map_factorGL E (toMatrixHom ρ b) hmem g)) i) j
      exact congrArg (· * (v j : Ω)) hij
    have he_apply (u : ι → E) : e (c ⊗ₜ[E] u) = ∑ j : ι, (c * (u j : Ω)) • b j := by
      simp only [e, LinearEquiv.trans_apply, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, Module.Basis.equivFun_symm_apply, Algebra.smul_def,
        IntermediateField.algebraMap_apply, mul_comm]
    rw [he_apply, he_apply, map_sum]
    simp_rw [map_smul, hmul, Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hρbj : ρ g (b j) = ∑ i : ι, (toMatrixHom ρ b g : Matrix ι ι Ω) i j • b i := by
      conv_lhs => rw [← b.sum_repr (ρ g (b j))]
      simp_rw [toMatrixHom_coe_apply]
    rw [hρbj, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_smul, mul_left_comm, mul_comm (c * (v j : Ω))]

@[simp]
private theorem baseChangeFactorEquiv_tmul_single {Γ F Ω V ι : Type*}
    [Group Γ] [TopologicalSpace Γ]
    [Field F] [Field Ω] [Algebra F Ω] [TopologicalSpace Ω] [IsTopologicalDivisionRing Ω]
    [AddCommGroup V] [Module Ω V] [TopologicalSpace V] [IsModuleTopology Ω V]
    [Fintype ι] [DecidableEq ι]
    (ρ : ContinuousRep Γ Ω V) (b : Module.Basis ι Ω V)
    (E : IntermediateField F Ω)
    (hmem : ∀ g i j, (toMatrixHom ρ b g : Matrix ι ι Ω) i j ∈ E) (c : Ω) (j : ι) :
    baseChangeFactorEquiv ρ b E hmem (c ⊗ₜ[E] Pi.single j 1) = c • b j := by
  simp only [baseChangeFactorEquiv, Representation.Equiv.mk_apply, LinearEquiv.trans_apply,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Module.Basis.equivFun_symm_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Lift an equivalence between the algebraic scalar extension of `ρ` and `σ` to an isomorphism of
continuous representations. -/
private def baseChangeIsoOfEquiv {Γ A B M N : Type*}
    [Monoid Γ] [TopologicalSpace Γ]
    [CommSemiring A] [TopologicalSpace A]
    [Ring B] [TopologicalSpace B] [IsTopologicalSemiring B]
    [Algebra A B] [ContinuousSMul A B]
    [AddCommMonoid M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]
    [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]
    [AddCommMonoid N] [Module B N] [TopologicalSpace N] [IsModuleTopology B N]
    {ρ : ContinuousRep Γ A M} {σ : ContinuousRep Γ B N}
    (e : (ρ.toRepresentation.baseChange B).Equiv σ.toRepresentation) :
    ContinuousRep.Iso (ρ.baseChange B) σ :=
  ContinuousRep.Iso.ofEquiv
    (Representation.Equiv.mk e.toLinearEquiv fun g ↦ by
      rw [toRepresentation_baseChange]
      exact e.toIntertwiningMap.isIntertwining' g)

/-- Descend a single intertwining map whose matrix entries lie in `E` to an intertwining map between
the descended coordinate representations over `E`. -/
private theorem exists_descend_intertwining_matrix {Γ F Ω V₁ V₂ ι₁ ι₂ : Type*}
    [Group Γ] [TopologicalSpace Γ]
    [Field F] [Field Ω] [Algebra F Ω] [TopologicalSpace Ω] [IsTopologicalDivisionRing Ω]
    [AddCommGroup V₁] [Module Ω V₁] [TopologicalSpace V₁] [IsModuleTopology Ω V₁]
    [AddCommGroup V₂] [Module Ω V₂] [TopologicalSpace V₂] [IsModuleTopology Ω V₂]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ρ₁ : ContinuousRep Γ Ω V₁) (ρ₂ : ContinuousRep Γ Ω V₂)
    (b₁ : Module.Basis ι₁ Ω V₁) (b₂ : Module.Basis ι₂ Ω V₂)
    (E : IntermediateField F Ω)
    (hmem₁ : ∀ g i j, (toMatrixHom ρ₁ b₁ g : Matrix ι₁ ι₁ Ω) i j ∈ E)
    (hmem₂ : ∀ g i j, (toMatrixHom ρ₂ b₂ g : Matrix ι₂ ι₂ Ω) i j ∈ E)
    (f : ρ₁.toRepresentation.IntertwiningMap ρ₂.toRepresentation)
    (hf : ∀ i j, LinearMap.toMatrix b₁ b₂ f.toLinearMap i j ∈ E) :
    ∃ fE : (ofMatrixHom (factorGL E (toMatrixHom ρ₁ b₁) hmem₁)).toRepresentation.IntertwiningMap
        (ofMatrixHom (factorGL E (toMatrixHom ρ₂ b₂) hmem₂)).toRepresentation,
      ∀ x, baseChangeFactorEquiv ρ₂ b₂ E hmem₂ (fE.baseChange Ω x) =
        f (baseChangeFactorEquiv ρ₁ b₁ E hmem₁ x) := by
  let ρE₁ := ofMatrixHom (factorGL E (toMatrixHom ρ₁ b₁) hmem₁)
  let ρE₂ := ofMatrixHom (factorGL E (toMatrixHom ρ₂ b₂) hmem₂)
  let e₁ := baseChangeFactorEquiv ρ₁ b₁ E hmem₁
  let e₂ := baseChangeFactorEquiv ρ₂ b₂ E hmem₂
  let M := LinearMap.toMatrix b₁ b₂ f.toLinearMap
  let ME : Matrix ι₂ ι₁ E := fun i j ↦ ⟨M i j, hf i j⟩
  let gE : (ι₁ → E) →ₗ[E] (ι₂ → E) := Matrix.toLin' ME
  have hcompat : ∀ x, e₂ (gE.baseChange Ω x) = f (e₁ x) := by
    suffices e₂.toLinearEquiv.toLinearMap ∘ₗ gE.baseChange Ω =
        f.toLinearMap ∘ₗ e₁.toLinearEquiv.toLinearMap from
      fun x ↦ LinearMap.congr_fun this x
    refine ((Pi.basisFun E ι₁).baseChange Ω).ext fun j ↦ ?_
    simp only [LinearMap.comp_apply, Representation.Equiv.coe_toIntertwiningMap,
      Representation.IntertwiningMap.coe_toLinearMap, Module.Basis.baseChange_apply,
      Pi.basisFun_apply, LinearMap.baseChange_tmul, gE, Matrix.toLin'_apply]
    rw [baseChangeFactorEquiv_tmul_single, one_smul]
    have hvec : ME *ᵥ Pi.single j 1 = ∑ i, ME i j • Pi.single i 1 := by
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hvec, TensorProduct.tmul_sum, map_sum]
    have hfb : f (b₁ j) = ∑ i, M i j • b₂ i := by
      have h := Matrix.toLin_self b₁ b₂ M j
      rwa [Matrix.toLin_toMatrix] at h
    rw [hfb]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← TensorProduct.smul_tmul, baseChangeFactorEquiv_tmul_single]
    simp only [Algebra.smul_def, IntermediateField.algebraMap_apply, mul_one, ME]
  have hinter (g : Γ) : gE ∘ₗ ρE₁.toRepresentation g = ρE₂.toRepresentation g ∘ₗ gE := by
    apply LinearMap.baseChange_injective (R := E) (A := Ω)
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    apply LinearMap.ext
    intro x
    apply e₂.toLinearEquiv.injective
    simp only [Representation.Equiv.toLinearEquiv_apply,
      Representation.Equiv.coe_toIntertwiningMap]
    have he₁ := LinearMap.congr_fun (e₁.toIntertwiningMap.isIntertwining' g) x
    have he₂ := LinearMap.congr_fun (e₂.toIntertwiningMap.isIntertwining' g) (gE.baseChange Ω x)
    have hfb := LinearMap.congr_fun (f.isIntertwining' g) (e₁ x)
    simp only [LinearMap.comp_apply, Representation.IntertwiningMap.coe_toLinearMap,
      Representation.Equiv.coe_toIntertwiningMap, Representation.baseChange_apply]
      at he₁ he₂ hfb
    calc e₂ ((gE.baseChange Ω ∘ₗ (ρE₁.toRepresentation g).baseChange Ω) x)
        = f (e₁ ((ρE₁.toRepresentation g).baseChange Ω x)) := by
          rw [LinearMap.comp_apply, hcompat]
      _ = ρ₂.toRepresentation g (f (e₁ x)) := by rw [he₁, hfb]
      _ = e₂ (((ρE₂.toRepresentation g).baseChange Ω ∘ₗ gE.baseChange Ω) x) := by
          rw [LinearMap.comp_apply, ← hcompat, ← he₂]
  refine ⟨⟨gE, hinter⟩, fun x ↦ ?_⟩
  simpa only [← Representation.IntertwiningMap.coe_toLinearMap,
    Representation.IntertwiningMap.toLinearMap_baseChange] using hcompat x

/-- **Simultaneous descent of a finite diagram of continuous representations and intertwining maps
(general Baire form).** Under the hypotheses of
`ContinuousMonoidHom.exists_finiteDimensional_mem_of_countable` with `Ω` a topological division
ring, any finite family of finite-dimensional continuous representations and finite family of
intertwining maps between them descend simultaneously to a single finite intermediate field `E`
containing any prescribed finite `K`. -/
theorem exists_finiteDimensional_diagram_descent_of_countable {Γ F Ω : Type*}
    [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ] [CompactSpace Γ] [T2Space Γ]
    [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    [TopologicalSpace Ω] [IsTopologicalDivisionRing Ω]
    (hclosed : ∀ E : IntermediateField F Ω, FiniteDimensional F E → IsClosed (E : Set Ω))
    (hcount : Set.Countable {E : IntermediateField F Ω | FiniteDimensional F E})
    {α β : Type*} [Finite α] [Finite β]
    {V : α → Type*} [∀ a, AddCommGroup (V a)] [∀ a, Module Ω (V a)]
    [∀ a, FiniteDimensional Ω (V a)] [∀ a, TopologicalSpace (V a)]
    [∀ a, IsModuleTopology Ω (V a)]
    (ρ : ∀ a : α, ContinuousRep Γ Ω (V a))
    (src tgt : β → α)
    (f : ∀ b : β, (ρ (src b)).toRepresentation.IntertwiningMap (ρ (tgt b)).toRepresentation)
    (K : IntermediateField F Ω) [FiniteDimensional F K] :
    ∃ (E : IntermediateField F Ω) (_ : FiniteDimensional F E)
      (ρE : ∀ a : α, ContinuousRep Γ E (Fin (Module.finrank Ω (V a)) → E))
      (fE : ∀ b : β,
        (ρE (src b)).toRepresentation.IntertwiningMap (ρE (tgt b)).toRepresentation),
      K ≤ E ∧
        ∀ [∀ a, TopologicalSpace (Ω ⊗[E] (Fin (Module.finrank Ω (V a)) → E))]
          [∀ a, IsModuleTopology Ω (Ω ⊗[E] (Fin (Module.finrank Ω (V a)) → E))],
          ∃ e : ∀ a : α, ContinuousRep.Iso ((ρE a).baseChange Ω) (ρ a),
            ∀ b x, e (tgt b) ((fE b).baseChange Ω x) = f b (e (src b) x) := by
  let bas : ∀ a : α, Module.Basis (Fin (Module.finrank Ω (V a))) Ω (V a) :=
    fun a ↦ Module.finBasis Ω (V a)
  have hobj : ∀ a : α, ∃ Ea : IntermediateField F Ω,
      K ≤ Ea ∧ FiniteDimensional F Ea ∧
        ∀ g i j,
          (toMatrixHom (ρ a) (bas a) g :
            Matrix (Fin (Module.finrank Ω (V a))) (Fin (Module.finrank Ω (V a))) Ω) i j ∈ Ea :=
    fun a ↦ (toMatrixHom (ρ a) (bas a)).exists_finiteDimensional_mem_of_countable hclosed hcount K
  choose Ea _ hEa_fin hEa_mem using hobj
  let Ef : β → IntermediateField F Ω := fun b ↦
    IntermediateField.adjoin F (Set.range fun p :
      Fin (Module.finrank Ω (V (tgt b))) × Fin (Module.finrank Ω (V (src b))) ↦
        LinearMap.toMatrix (bas (src b)) (bas (tgt b)) (f b).toLinearMap p.1 p.2)
  have hEf_fin (b : β) : FiniteDimensional F (Ef b) :=
    IntermediateField.finiteDimensional_adjoin fun _ _ ↦ Algebra.IsIntegral.isIntegral _
  let E : IntermediateField F Ω := K ⊔ (⨆ a : α, Ea a) ⊔ (⨆ b : β, Ef b)
  have hE_fin : FiniteDimensional F E := inferInstance
  have hmem (a : α) (g : Γ) (i j : Fin (Module.finrank Ω (V a))) :
      (toMatrixHom (ρ a) (bas a) g :
        Matrix (Fin (Module.finrank Ω (V a))) (Fin (Module.finrank Ω (V a))) Ω) i j ∈ E :=
    ((le_iSup Ea a).trans (le_sup_right.trans le_sup_left)) (hEa_mem a g i j)
  let ρE : ∀ a : α, ContinuousRep Γ E (Fin (Module.finrank Ω (V a)) → E) :=
    fun a ↦ ofMatrixHom (factorGL E (toMatrixHom (ρ a) (bas a)) (hmem a))
  have hmor (b : β) :=
    exists_descend_intertwining_matrix (ρ (src b)) (ρ (tgt b)) (bas (src b)) (bas (tgt b)) E
      (hmem (src b)) (hmem (tgt b)) (f b) fun i j ↦
        ((le_iSup Ef b).trans le_sup_right) (IntermediateField.subset_adjoin F _ ⟨(i, j), rfl⟩)
  choose fE hfE using hmor
  exact ⟨E, hE_fin, ρE, fE, le_sup_left.trans le_sup_left,
    ⟨fun a ↦ baseChangeIsoOfEquiv (baseChangeFactorEquiv (ρ a) (bas a) E (hmem a)),
      fun b x ↦ by
        simpa only [baseChangeIsoOfEquiv, ContinuousRep.Iso.ofEquiv_apply,
          Representation.Equiv.mk_apply, Representation.Equiv.toLinearEquiv_apply,
          Representation.Equiv.coe_toIntertwiningMap] using hfE b x⟩⟩

/-- **Simultaneous descent of a finite diagram of continuous representations over `PadicAlgCl ℓ`.**
Any finite family of finite-dimensional continuous representations of a compact Hausdorff group
over `PadicAlgCl ℓ` and any finite family of intertwining maps between them descend simultaneously
to a single finite intermediate field `E / ℚ_[ℓ]` containing any prescribed finite `K`. -/
theorem exists_finiteDimensional_diagram_descent {Γ : Type*}
    [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ] [CompactSpace Γ] [T2Space Γ]
    {ℓ : ℕ} [Fact ℓ.Prime] {α β : Type*} [Finite α] [Finite β]
    {V : α → Type*} [∀ a, AddCommGroup (V a)] [∀ a, Module (PadicAlgCl ℓ) (V a)]
    [∀ a, FiniteDimensional (PadicAlgCl ℓ) (V a)] [∀ a, TopologicalSpace (V a)]
    [∀ a, IsModuleTopology (PadicAlgCl ℓ) (V a)]
    (ρ : ∀ a : α, ContinuousRep Γ (PadicAlgCl ℓ) (V a))
    (src tgt : β → α)
    (f : ∀ b : β, (ρ (src b)).toRepresentation.IntertwiningMap (ρ (tgt b)).toRepresentation)
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρE : ∀ a : α, ContinuousRep Γ E (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E))
      (fE : ∀ b : β,
        (ρE (src b)).toRepresentation.IntertwiningMap (ρE (tgt b)).toRepresentation),
      K ≤ E ∧
        ∀ [∀ a, TopologicalSpace (PadicAlgCl ℓ ⊗[E]
              (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E))]
          [∀ a, IsModuleTopology (PadicAlgCl ℓ) (PadicAlgCl ℓ ⊗[E]
              (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E))],
          ∃ e : ∀ a : α, ContinuousRep.Iso ((ρE a).baseChange (PadicAlgCl ℓ)) (ρ a),
            ∀ b x, e (tgt b) ((fE b).baseChange (PadicAlgCl ℓ) x) = f b (e (src b) x) :=
  exists_finiteDimensional_diagram_descent_of_countable
    (fun E _ ↦ E.isClosed_of_finiteDimensional)
    (PadicAlgCl.countable_finiteDimensional ℓ) ρ src tgt f K

/-- **Descent of a continuous representation (general Baire form).** Under the hypotheses of
`ContinuousMonoidHom.exists_finiteDimensional_mem_of_countable` with `Ω` a topological division
ring, every finite-dimensional continuous representation over `Ω` with its module topology is
isomorphic to the scalar extension of a continuous representation over a finite intermediate field
`E` containing any prescribed finite `K`. -/
theorem exists_finiteDimensional_baseChange_iso_of_countable {Γ F Ω V : Type*}
    [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ] [CompactSpace Γ] [T2Space Γ]
    [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    [TopologicalSpace Ω] [IsTopologicalDivisionRing Ω]
    [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
    [TopologicalSpace V] [IsModuleTopology Ω V]
    (ρ : ContinuousRep Γ Ω V)
    (hclosed : ∀ E : IntermediateField F Ω, FiniteDimensional F E → IsClosed (E : Set Ω))
    (hcount : Set.Countable {E : IntermediateField F Ω | FiniteDimensional F E})
    (K : IntermediateField F Ω) [FiniteDimensional F K] :
    ∃ (E : IntermediateField F Ω) (_ : FiniteDimensional F E)
      (ρE : ContinuousRep Γ E (Fin (Module.finrank Ω V) → E)),
      K ≤ E ∧
        ∀ [TopologicalSpace (Ω ⊗[E] (Fin (Module.finrank Ω V) → E))]
          [IsModuleTopology Ω (Ω ⊗[E] (Fin (Module.finrank Ω V) → E))],
          Nonempty (ContinuousRep.Iso (ρE.baseChange Ω) ρ) := by
  let b := Module.finBasis Ω V
  obtain ⟨E, hKE, hEfin, hmem⟩ :=
    (toMatrixHom ρ b).exists_finiteDimensional_mem_of_countable hclosed hcount K
  exact ⟨E, hEfin, ofMatrixHom (factorGL E (toMatrixHom ρ b) hmem), hKE,
    ⟨baseChangeIsoOfEquiv (baseChangeFactorEquiv ρ b E hmem)⟩⟩

/-- **Descent of a continuous representation from `PadicAlgCl ℓ`.** Every finite-dimensional
continuous representation of a compact Hausdorff group over `PadicAlgCl ℓ` with its module topology
descends to a finite intermediate field `E / ℚ_[ℓ]` containing any prescribed finite `K`. -/
theorem exists_finiteDimensional_baseChange_iso {Γ V : Type*}
    [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ] [CompactSpace Γ] [T2Space Γ]
    {ℓ : ℕ} [Fact ℓ.Prime] [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    [FiniteDimensional (PadicAlgCl ℓ) V] [TopologicalSpace V] [IsModuleTopology (PadicAlgCl ℓ) V]
    (ρ : ContinuousRep Γ (PadicAlgCl ℓ) V)
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρE : ContinuousRep Γ E (Fin (Module.finrank (PadicAlgCl ℓ) V) → E)),
      K ≤ E ∧
        ∀ [TopologicalSpace (PadicAlgCl ℓ ⊗[E] (Fin (Module.finrank (PadicAlgCl ℓ) V) → E))]
          [IsModuleTopology (PadicAlgCl ℓ)
            (PadicAlgCl ℓ ⊗[E] (Fin (Module.finrank (PadicAlgCl ℓ) V) → E))],
          Nonempty (ContinuousRep.Iso (ρE.baseChange (PadicAlgCl ℓ)) ρ) :=
  ρ.exists_finiteDimensional_baseChange_iso_of_countable
    (fun E _ ↦ E.isClosed_of_finiteDimensional)
    (PadicAlgCl.countable_finiteDimensional ℓ) K

end CategoricalDescent

end TauCeti.ContinuousRep

namespace ContinuousMonoidHom

section IntegralDescent

/-- **Integral conjugation over a discretely valued field.** Every continuous matrix homomorphism
`ρ : Γ →ₜ* GL ι E` of a compact group into `GL ι E` over a valuatively topologized field whose
valuation ring `𝒪[E]` is a principal ideal domain (in particular, any nonarchimedean local field)
is conjugate in `GL ι E` into matrices with entries in `𝒪[E]`. -/
theorem exists_conj_mem_integerRing {Γ E ι : Type*}
    [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
    [IsPrincipalIdealRing 𝒪[E]]
    [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι E) :
    ∃ P : GL ι E, ∀ (g : Γ) (i j : ι),
      ((P * ρ g * P⁻¹ : GL ι E) : Matrix ι ι E) i j ∈ 𝒪[E] := by
  let ρV : TauCeti.ContinuousRep Γ E (ι → E) := TauCeti.ContinuousRep.ofMatrixHom ρ
  obtain ⟨L, hL, hρL⟩ := ρV.exists_stable_lattice
  have : L.IsLattice E := hL
  have : Module.Finite 𝒪[E] L := Module.Finite.iff_fg.mpr Submodule.IsLattice.fg
  have : Module.IsTorsionFree 𝒪[E] L := Module.isTorsionFree_iff_smul_eq_zero.mpr fun a x hax ↦ by
    rcases eq_or_ne a 0 with rfl | ha
    · exact Or.inl rfl
    · right
      apply Subtype.ext
      have h : (a : E) • (x : ι → E) = 0 := congrArg Subtype.val hax
      exact (smul_eq_zero.mp h).resolve_left (fun h0 ↦ ha (Subtype.ext h0))
  have : Module.Free 𝒪[E] L := Module.free_of_finite_type_torsion_free'
  let b₀ := Module.Free.chooseBasis 𝒪[E] L
  let e := Pi.basisFun E ι
  let bL : Module.Basis ι 𝒪[E] L := b₀.reindex ((b₀.extendOfIsLattice E).indexEquiv e)
  let bV : Module.Basis ι E (ι → E) := bL.extendOfIsLattice E
  -- Change of basis from `e` to `bV` conjugates `ρ g` to the matrix of `ρV g` in the lattice basis.
  let P : GL ι E :=
    ⟨bV.toMatrix e, e.toMatrix bV,
      Module.Basis.toMatrix_mul_toMatrix_flip bV e,
      Module.Basis.toMatrix_mul_toMatrix_flip e bV⟩
  refine ⟨P, fun g i j ↦ ?_⟩
  have hρ_mat : LinearMap.toMatrix e e (ρV g) = (ρ g : Matrix ι ι E) := by
    ext r s
    simp [e, ρV, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hconj : ((P * ρ g * P⁻¹ : GL ι E) : Matrix ι ι E) = LinearMap.toMatrix bV bV (ρV g) := by
    have hP : (P : Matrix ι ι E) = bV.toMatrix e := rfl
    have hPinv : ((P⁻¹ : GL ι E) : Matrix ι ι E) = e.toMatrix bV := rfl
    simp only [Units.val_mul, hP, hPinv]
    rw [← hρ_mat, ← LinearMap.toMatrix_id_eq_basis_toMatrix e bV,
      ← LinearMap.toMatrix_id_eq_basis_toMatrix bV e,
      ← LinearMap.toMatrix_comp e e bV, ← LinearMap.toMatrix_comp bV e bV,
      LinearMap.id_comp, LinearMap.comp_id]
  rw [hconj, LinearMap.toMatrix_apply]
  -- `bV j ∈ L`, so `ρV g (bV j) ∈ L`, and its coordinates in the lattice basis `bV` lie in `𝒪[E]`.
  have hmem : ρV g (bV j) ∈ L := by
    rw [Module.Basis.extendOfIsLattice_apply]
    exact hρL g (bL j : ι → E) (bL j).2
  let w : L := ⟨ρV g (bV j), hmem⟩
  have hsum : ρV g (bV j) = ∑ k : ι, ((bL.repr w k : 𝒪[E]) : E) • bV k := by
    have hw : (w : ι → E) = ((∑ k : ι, bL.repr w k • bL k : L) : ι → E) :=
      congrArg Subtype.val (bL.sum_repr w).symm
    rw [Submodule.coe_sum] at hw
    simpa only [w, Submodule.coe_smul_of_tower, ← Module.Basis.extendOfIsLattice_apply E bL,
      Subring.smul_def] using hw
  have hcoord : bV.repr (ρV g (bV j)) i = ((bL.repr w i : 𝒪[E]) : E) := by
    rw [hsum, map_sum, Finset.sum_apply']
    simp [bV.repr_self, Finsupp.single_apply]
  rw [hcoord]
  exact (bL.repr w i).2

/-- **Integral descent from `PadicAlgCl ℓ` above a prescribed coefficient field.** Every continuous
matrix homomorphism `ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` of a compact Hausdorff group with separately
continuous multiplication is conjugate, by a matrix `P` with entries in a finite intermediate field
`E` containing `K`, into matrices with entries in `E` of norm at most `1`. -/
theorem exists_integral_conj_GL_of_le {Γ : Type*}
    [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ] [CompactSpace Γ] [T2Space Γ]
    {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ))
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (P : GL ι (PadicAlgCl ℓ)),
      K ≤ E ∧ FiniteDimensional ℚ_[ℓ] E ∧
        (∀ i j, (P : Matrix ι ι (PadicAlgCl ℓ)) i j ∈ E) ∧
        ∀ (g : Γ) (i j : ι),
          (P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j ∈ E ∧
          ‖(P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j‖ ≤ 1 := by
  obtain ⟨E, hEfin, ρE, hKE, hfactor⟩ := ρ.exists_finiteDimensional_factor_GL K
  let _ := TauCeti.algebraicExtensionValuativeRel ℚ_[ℓ] E
  have : IsNonarchimedeanLocalField E :=
    PadicAlgCl.isNonarchimedeanLocalField_of_finiteDimensional E
  obtain ⟨PE, hPE⟩ := ρE.exists_conj_mem_integerRing
  let P : GL ι (PadicAlgCl ℓ) := Matrix.GeneralLinearGroup.map E.val.toRingHom PE
  refine ⟨E, P, hKE, hEfin, fun i j ↦ (PE i j).2, fun g i j ↦ ?_⟩
  have hconj : P * ρ g * P⁻¹ =
      Matrix.GeneralLinearGroup.map E.val.toRingHom (PE * ρE g * PE⁻¹) := by
    rw [← hfactor g, map_mul, map_mul, map_inv]
  have hentry : (P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j =
      (((PE * ρE g * PE⁻¹ : GL ι E) : Matrix ι ι E) i j : PadicAlgCl ℓ) :=
    congrFun (congrFun
      (congrArg (fun X : GL ι (PadicAlgCl ℓ) ↦ (X : Matrix ι ι (PadicAlgCl ℓ))) hconj) i) j
  rw [hentry]
  exact ⟨Subtype.coe_prop _, (PadicAlgCl.mem_integerRing_iff_norm_le_one E _).mp (hPE g i j)⟩

/-- **Integral descent from `PadicAlgCl ℓ`.** Every continuous matrix homomorphism
`ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` of a compact Hausdorff group with separately continuous
multiplication is conjugate into the closed unit ball of a single finite intermediate field
`E / ℚ_[ℓ]`. -/
theorem exists_integral_conj_GL {Γ : Type*}
    [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ] [CompactSpace Γ] [T2Space Γ]
    {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)) :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (P : GL ι (PadicAlgCl ℓ)),
      FiniteDimensional ℚ_[ℓ] E ∧ ∀ (g : Γ) (i j : ι),
        (P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j ∈ E ∧
        ‖(P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j‖ ≤ 1 := by
  obtain ⟨E, P, -, hEfin, -, hconj⟩ := ρ.exists_integral_conj_GL_of_le ⊥
  exact ⟨E, P, hEfin, hconj⟩

end IntegralDescent

end ContinuousMonoidHom
