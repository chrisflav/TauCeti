/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import TauCeti.NumberTheory.Padics.AlgebraicClosure.FiniteSubfield
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep
public import TauCeti.RepresentationTheory.Continuous.StableLattice
public import TauCeti.RepresentationTheory.Descent
public import TauCeti.Topology.Algebra.IntermediateField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Baire.Lemmas
import TauCeti.Algebra.Module.Lattice
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subalgebra

/-!
# Coefficient-field descent and integral conjugation of continuous representations

This file proves that continuous finite-dimensional representations of compact Baire groups
(in particular, compact Hausdorff topological groups such as profinite Galois groups) over
`PadicAlgCl ℓ` (more generally, over an algebraic extension `Ω / F` of a complete nontrivially
normed field `F` with countably many finite intermediate fields) are defined over a finite
extension `E / F`, and can moreover be conjugated into `GL_n(𝒪_E)`.

## Overview of the proofs

1. **Baire coefficient-field descent** (`TauCeti.ContinuousRep.exists_finiteDimensional_mem_matrix`,
   `TauCeti.ContinuousRep.baire_descent`): For each finite intermediate field `E ⊆ Ω`, the
   elements `g ∈ Γ` whose matrix `ρ g` has all entries in `E` form a subgroup `H_E ≤ Γ` (closed
   under inversion by `Matrix.GeneralLinearGroup.inv_apply_mem_subfield`). Since `E` is
   finite-dimensional over the complete field `F`, it is closed in `Ω`, so `H_E` is closed in `Γ`.
   Every `g ∈ Γ` has finitely many matrix entries, all algebraic over `F`, so `Γ` is the countable
   union of the closed subgroups `H_E`. By the Baire category theorem, some `H_{E₀}` has nonempty
   interior and is therefore open. Compactness of `Γ` yields finitely many left coset
   representatives whose matrix entries generate a finite enlargement `E ⊇ K ⊔ E₀` containing all
   matrix entries of `ρ`.
2. **Descent of `ContinuousRep` objects and isomorphisms** (`TauCeti.ContinuousRep.exists_descent`,
   `TauCeti.ContinuousRep.exists_descent_family`, `TauCeti.ContinuousRep.Iso.baseChange_injective`,
   `TauCeti.ContinuousRep.Iso.exists_descent`): Choosing a basis of a finite-dimensional continuous
   `Ω`-representation `ρ` produces a matrix representation whose entries descend by Baire descent
   to a finite intermediate field `E ⊇ K`, yielding a continuous representation `ρE` on `Eⁿ` with
   `ρE.baseChange Ω ≅ ρ` (and similarly for any finite family of representations simultaneously).
   Combined with `Representation.Equiv.baseChange_injective` and
   `Representation.Equiv.exists_descent`, faithfully flat base change is injective on isomorphisms
   and isomorphisms over an algebraic extension descend to a finite enlargement.
3. **Integral conjugation** (`TauCeti.ContinuousRep.exists_conj_mem_integerRing`,
   `TauCeti.ContinuousRep.exists_conj_eq_map_integerRing`,
   `TauCeti.ContinuousRep.exists_integral_conj_GL`): Over a field `E` with a valuative topology
   whose valuation ring `𝒪[E]` is a principal ideal domain (such as any nonarchimedean local
   field), a compact group acting continuously on `Eⁿ` stabilizes a full `𝒪[E]`-lattice `L` by
   `Representation.exists_stable_lattice`. Since `𝒪[E]` is a PID, `L` is free of rank `n`; taking
   an `𝒪[E]`-basis of `L` yields a change-of-basis matrix `P ∈ GL_n(E)` conjugating `ρ` into
   `GL_n(𝒪[E])`. Combining Baire descent to a finite extension `E ⊆ PadicAlgCl ℓ` with the local
   field structure on `E` (`PadicAlgCl.isNonarchimedeanLocalField`) gives
   `TauCeti.ContinuousRep.exists_integral_conj_GL`.

## Main results

* `TauCeti.ContinuousRep.exists_finiteDimensional_mem_matrix`: general Baire descent of matrix
  representations over an algebraic extension with countably many finite intermediate fields.
* `TauCeti.ContinuousRep.exists_finiteDimensional_mem_matrix_family`: simultaneous Baire descent
  for a finite family of matrix representations.
* `TauCeti.ContinuousRep.baire_descent` and `TauCeti.ContinuousRep.baire_descent_family`: Baire
  descent over `PadicAlgCl ℓ` for one or finitely many continuous homomorphisms `Γ →ₜ* GL_ι`.
* `TauCeti.ContinuousRep.exists_descent`, `TauCeti.ContinuousRep.exists_descent_family`,
  `TauCeti.ContinuousRep.exists_descent_padicAlgCl`,
  `TauCeti.ContinuousRep.exists_descent_family_padicAlgCl`: descent of continuous representations
  (and finite families thereof) to a finite intermediate field.
* `TauCeti.ContinuousRep.Iso.baseChange_injective` and
  `TauCeti.ContinuousRep.Iso.exists_descent`: faithfulness and descent of isomorphisms of
  continuous representations.
* `TauCeti.ContinuousRep.exists_conj_mem_integerRing` and
  `TauCeti.ContinuousRep.exists_conj_eq_map_integerRing`: conjugation of a compact-group matrix
  representation over a valuative field with PID valuation ring into `GL_ι(𝒪[E])`.
* `TauCeti.ContinuousRep.exists_integral_conj_GL`: every continuous `Γ →ₜ* GL_ι(PadicAlgCl ℓ)`
  is conjugate in `GL_ι(PadicAlgCl ℓ)` to a representation with entries in `𝒪_E` for a finite
  extension `E / ℚ_ℓ`.

## References

* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *G-local systems on smooth projective curves
  are potentially automorphic*, Acta Math. 223 (2019), Theorem 4.8.
* F. Calegari and D. Geraghty, *Modularity lifting beyond the Taylor–Wiles method*, Invent. Math.
  211 (2018), Proposition 6.8.
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
* K. A. Ribet, *Galois representations attached to eigenforms with Nebentypus*, §2.
-/

public section

open Filter Matrix Module Submodule Topology ValuativeRel
open scoped Pointwise TensorProduct

namespace TauCeti.ContinuousRep

section MatrixBaireDescent

variable {F Ω ι : Type*} [Field F] [Field Ω] [Algebra F Ω] [Fintype ι] [DecidableEq ι]

/-- The subgroup of `Γ` consisting of elements whose matrix under `ρ` has all entries in the
intermediate field `E`. -/
private def entrySubgroup {Γ : Type*} [Group Γ] (ρ : Γ →* GL ι Ω) (E : IntermediateField F Ω) :
    Subgroup Γ where
  carrier := {g : Γ | ∀ i j, (ρ g : Matrix ι ι Ω) i j ∈ E}
  one_mem' i j := by
    simp only [map_one, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact E.one_mem
    · exact E.zero_mem
  mul_mem' {g h} hg hh i j := by
    simp only [map_mul, Units.val_mul, Matrix.mul_apply]
    exact E.sum_mem fun k _ ↦ E.mul_mem (hg i k) (hh k j)
  inv_mem' {g} hg i j := by
    rw [map_inv]
    exact Matrix.GeneralLinearGroup.inv_apply_mem_subfield E.toSubfield (ρ g) hg i j

/-- **General Baire coefficient-field descent for matrix representations.** Let `Ω / F` be an
algebraic extension of a complete nontrivially normed field `F` having only countably many finite
intermediate fields, and let `Γ` be a compact Baire group with separately continuous
multiplication. Then every matrix representation `ρ : Γ →* GL_ι(Ω)` with continuous matrix
entries has all entries in a finite intermediate field `E ⊇ K` of `Ω / F`. -/
theorem exists_finiteDimensional_mem_matrix
    {Γ F Ω ι : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ]
    [NontriviallyNormedField F] [CompleteSpace F]
    [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    [TopologicalSpace Ω] [IsTopologicalAddGroup Ω] [ContinuousSMul F Ω] [T2Space Ω]
    [Fintype ι] [DecidableEq ι]
    (hcount : {E : IntermediateField F Ω | FiniteDimensional F E}.Countable)
    (ρ : Γ →* GL ι Ω) (hρ : Continuous fun g ↦ (ρ g : Matrix ι ι Ω))
    (K : IntermediateField F Ω) [FiniteDimensional F K] :
    ∃ E : IntermediateField F Ω, K ≤ E ∧ FiniteDimensional F E ∧
      ∀ g i j, (ρ g : Matrix ι ι Ω) i j ∈ E := by
  let S : Set (IntermediateField F Ω) := {E | FiniteDimensional F E}
  have hclosed : ∀ E ∈ S, IsClosed ((entrySubgroup ρ E : Subgroup Γ) : Set Γ) := fun E hE ↦ by
    have : FiniteDimensional F E := hE
    have hE_closed : IsClosed (E : Set Ω) := E.toSubmodule.isClosed_of_finiteDimensional
    have hcar : ((entrySubgroup ρ E : Subgroup Γ) : Set Γ) =
        ⋂ i : ι, ⋂ j : ι, (fun g ↦ (ρ g : Matrix ι ι Ω) i j) ⁻¹' (E : Set Ω) := by
      ext g
      simp [entrySubgroup]
    rw [hcar]
    refine isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ hE_closed.preimage ?_
    exact (_root_.continuous_apply j).comp ((_root_.continuous_apply i).comp hρ)
  have hcover : (⋃ E ∈ S, ((entrySubgroup ρ E : Subgroup Γ) : Set Γ)) = Set.univ := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    let T : Set Ω := Set.range fun p : ι × ι ↦ (ρ g : Matrix ι ι Ω) p.1 p.2
    let Eg : IntermediateField F Ω := IntermediateField.adjoin F T
    have hEg : FiniteDimensional F Eg := IntermediateField.finiteDimensional_adjoin fun x _ ↦
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    exact ⟨Eg, hEg, fun i j ↦ IntermediateField.subset_adjoin F T ⟨(i, j), rfl⟩⟩
  have hdense : Dense (⋃ E ∈ S, interior ((entrySubgroup ρ E : Subgroup Γ) : Set Γ)) := by
    have h := dense_biUnion_interior_of_closed hclosed hcount
    simpa [hcover] using h
  obtain ⟨g₀, hg₀⟩ := hdense.nonempty
  obtain ⟨E₀, hE₀_fin, hg₀_int⟩ := Set.mem_iUnion₂.mp hg₀
  have hE₀_open : IsOpen ((entrySubgroup ρ E₀ : Subgroup Γ) : Set Γ) :=
    (entrySubgroup ρ E₀).isOpen_of_mem_nhds (mem_interior_iff_mem_nhds.mp hg₀_int)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun g : Γ ↦ g • ((entrySubgroup ρ E₀ : Subgroup Γ) : Set Γ))
    (fun g ↦ hE₀_open.leftCoset g)
    (fun g _ ↦ Set.mem_iUnion.mpr ⟨g, ⟨1, (entrySubgroup ρ E₀).one_mem, by simp⟩⟩)
  let U : Set Ω := ⋃ t ∈ s, Set.range fun p : ι × ι ↦ (ρ t : Matrix ι ι Ω) p.1 p.2
  have hU_fin : U.Finite := s.finite_toSet.biUnion fun _ _ ↦ Set.finite_range _
  have : Finite U := hU_fin.to_subtype
  let EU : IntermediateField F Ω := IntermediateField.adjoin F U
  have hEU_fin : FiniteDimensional F EU := IntermediateField.finiteDimensional_adjoin fun x _ ↦
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have : FiniteDimensional F E₀ := hE₀_fin
  let E : IntermediateField F Ω := K ⊔ E₀ ⊔ EU
  have hE_fin : FiniteDimensional F E :=
    have : FiniteDimensional F ↥(K ⊔ E₀) := IntermediateField.finiteDimensional_sup K E₀
    IntermediateField.finiteDimensional_sup (K ⊔ E₀) EU
  refine ⟨E, le_sup_left.trans le_sup_left, hE_fin, fun g ↦ ?_⟩
  obtain ⟨t, ht, hgt⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ g))
  obtain ⟨h, hh, rfl⟩ := Set.mem_smul_set.mp hgt
  have htE : t ∈ entrySubgroup ρ E := fun i j ↦
    (le_sup_right : EU ≤ E)
      (IntermediateField.subset_adjoin F U (Set.mem_biUnion ht ⟨(i, j), rfl⟩))
  have hhE : h ∈ entrySubgroup ρ E := fun i j ↦
    (le_sup_right.trans le_sup_left : E₀ ≤ E) (hh i j)
  exact (entrySubgroup ρ E).mul_mem htE hhE

/-- **Simultaneous Baire descent for a finite family of matrix representations.** Under the
hypotheses of `TauCeti.ContinuousRep.exists_finiteDimensional_mem_matrix`, any finite family of
continuous matrix representations `ρ a : Γ →* GL_{ι a}(Ω)` has all matrix entries in a single
finite intermediate field `E ⊇ K`. -/
theorem exists_finiteDimensional_mem_matrix_family
    {Γ F Ω α : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ]
    [NontriviallyNormedField F] [CompleteSpace F]
    [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    [TopologicalSpace Ω] [IsTopologicalAddGroup Ω] [ContinuousSMul F Ω] [T2Space Ω]
    [Finite α] {ι : α → Type*} [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)]
    (hcount : {E : IntermediateField F Ω | FiniteDimensional F E}.Countable)
    (ρ : ∀ a, Γ →* GL (ι a) Ω)
    (hρ : ∀ a, Continuous fun g ↦ (ρ a g : Matrix (ι a) (ι a) Ω))
    (K : IntermediateField F Ω) [FiniteDimensional F K] :
    ∃ E : IntermediateField F Ω, K ≤ E ∧ FiniteDimensional F E ∧
      ∀ a g i j, (ρ a g : Matrix (ι a) (ι a) Ω) i j ∈ E := by
  classical
  cases nonempty_fintype α
  suffices h : ∀ s : Finset α, ∃ E : IntermediateField F Ω, K ≤ E ∧ FiniteDimensional F E ∧
      ∀ a ∈ s, ∀ g i j, (ρ a g : Matrix (ι a) (ι a) Ω) i j ∈ E by
    obtain ⟨E, hKE, hE, hmem⟩ := h Finset.univ
    exact ⟨E, hKE, hE, fun a ↦ hmem a (Finset.mem_univ a)⟩
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨K, le_rfl, inferInstance, fun _ ha ↦ (Finset.notMem_empty _ ha).elim⟩
  | @insert a s _ ih =>
    obtain ⟨E₁, hKE₁, hE₁, hmem₁⟩ := ih
    have : FiniteDimensional F E₁ := hE₁
    obtain ⟨E₂, hE₁E₂, hE₂, hmem₂⟩ :=
      exists_finiteDimensional_mem_matrix hcount (ρ a) (hρ a) E₁
    refine ⟨E₂, hKE₁.trans hE₁E₂, hE₂, fun b hb g i j ↦ ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hbs
    · exact hmem₂ g i j
    · exact hE₁E₂ (hmem₁ b hbs g i j)

/-- **Baire descent over `PadicAlgCl ℓ`.** Every continuous homomorphism
`ρ : Γ →ₜ* GL_ι(PadicAlgCl ℓ)` from a compact Baire group with separately continuous
multiplication (in particular, any compact Hausdorff topological group) takes values in
`GL_ι(E)` for some finite intermediate field `E / ℚ_[ℓ]` containing a given finite subfield `K`. -/
theorem baire_descent
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ]
    (ℓ : ℕ) [Fact ℓ.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ))
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      K ≤ E ∧ FiniteDimensional ℚ_[ℓ] E ∧
      ∀ (g : Γ) (i j : ι), (ρ g : Matrix ι ι (PadicAlgCl ℓ)) i j ∈ E :=
  exists_finiteDimensional_mem_matrix (PadicAlgCl.countable_setOf_finiteDimensional ℓ)
    ρ.toMonoidHom (Units.continuous_val.comp ρ.continuous) K

/-- **Simultaneous Baire descent over `PadicAlgCl ℓ`** for a finite family of continuous
homomorphisms `ρ a : Γ →ₜ* GL_{ι a}(PadicAlgCl ℓ)`. -/
theorem baire_descent_family
    {Γ α : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ] [Finite α]
    (ℓ : ℕ) [Fact ℓ.Prime] {ι : α → Type*} [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)]
    (ρ : ∀ a, Γ →ₜ* GL (ι a) (PadicAlgCl ℓ))
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      K ≤ E ∧ FiniteDimensional ℚ_[ℓ] E ∧
      ∀ a (g : Γ) (i j : ι a), (ρ a g : Matrix (ι a) (ι a) (PadicAlgCl ℓ)) i j ∈ E :=
  exists_finiteDimensional_mem_matrix_family (PadicAlgCl.countable_setOf_finiteDimensional ℓ)
    (fun a ↦ (ρ a).toMonoidHom) (fun a ↦ Units.continuous_val.comp (ρ a).continuous) K

end MatrixBaireDescent

section ContinuousRepDescent

/-- The matrix representation attached to a continuous representation on a finite-dimensional
vector space, using `Module.finBasis`. -/
private noncomputable def toMatrixHom {Γ Ω V : Type*} [Group Γ] [TopologicalSpace Γ]
    [Field Ω] [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] [TopologicalSpace V]
    (ρ : ContinuousRep Γ Ω V) : Γ →* GL (Fin (Module.finrank Ω V)) Ω :=
  let b := Module.finBasis Ω V
  { toFun g :=
      { val := LinearMap.toMatrix b b (ρ g)
        inv := LinearMap.toMatrix b b (ρ g⁻¹)
        val_inv := by
          rw [← LinearMap.toMatrix_comp b b b, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel,
            map_one, Module.End.one_eq_id, LinearMap.toMatrix_id]
        inv_val := by
          rw [← LinearMap.toMatrix_comp b b b, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel,
            map_one, Module.End.one_eq_id, LinearMap.toMatrix_id] }
    map_one' := by
      ext i j
      simp [Module.End.one_eq_id]
    map_mul' g h := by
      apply Units.ext
      rw [Units.val_mul]
      dsimp only
      rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b] }

/-- The matrix entries of a continuous representation on a finite-dimensional space with its
module topology vary continuously on `Γ`. -/
private theorem continuous_toMatrixHom {Γ Ω V : Type*} [Group Γ] [TopologicalSpace Γ]
    [Field Ω] [TopologicalSpace Ω] [IsTopologicalRing Ω]
    [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
    [TopologicalSpace V] [IsModuleTopology Ω V] (ρ : ContinuousRep Γ Ω V) :
    Continuous fun g ↦ (toMatrixHom ρ g : Matrix (Fin (Module.finrank Ω V))
      (Fin (Module.finrank Ω V)) Ω) := by
  have := IsModuleTopology.toContinuousAdd Ω V
  let b := Module.finBasis Ω V
  refine continuous_matrix fun i j ↦ ?_
  have hcoord : Continuous (b.coord i : V → Ω) :=
    IsModuleTopology.continuous_of_linearMap (b.coord i)
  exact (hcoord.comp (ρ.continuous_orbit (b j))).congr fun g ↦ by
    simp [toMatrixHom, LinearMap.toMatrix_apply, b]

/-- Package a matrix descent of `ρ : ContinuousRep Γ Ω V` to an intermediate field `E` as a
continuous representation on `Fin (finrank Ω V) → E` whose base change to `Ω` is isomorphic
to `ρ`. -/
private noncomputable def ofMatrixDescent {Γ F Ω V : Type*} [Group Γ] [TopologicalSpace Γ]
    [Field F] [Field Ω] [Algebra F Ω] [TopologicalSpace Ω] [IsTopologicalRing Ω]
    [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
    [TopologicalSpace V] [IsModuleTopology Ω V]
    (ρ : ContinuousRep Γ Ω V) (E : IntermediateField F Ω)
    (hmem : ∀ g i j, (toMatrixHom ρ g : Matrix (Fin (Module.finrank Ω V))
      (Fin (Module.finrank Ω V)) Ω) i j ∈ E) :
    ContinuousRep Γ E (Fin (Module.finrank Ω V) → E) :=
  let ρE := Matrix.GeneralLinearGroup.liftSubring E.toSubring (toMatrixHom ρ) hmem
  { toRepresentation :=
      { toFun g := Matrix.mulVecLin (ρE g : Matrix (Fin (Module.finrank Ω V))
          (Fin (Module.finrank Ω V)) E)
        map_one' := by
          rw [map_one, Units.val_one, Matrix.mulVecLin_one]
          rfl
        map_mul' g h := by
          rw [map_mul, Units.val_mul, Matrix.mulVecLin_mul]
          rfl }
    continuous_action := by
      refine continuous_pi fun i ↦ ?_
      have hentry (j : Fin (Module.finrank Ω V)) :
          Continuous fun g : Γ ↦ (ρE g : Matrix (Fin (Module.finrank Ω V))
            (Fin (Module.finrank Ω V)) E) i j :=
        IsInducing.subtypeVal.continuous_iff.mpr <|
          ((_root_.continuous_apply j).comp ((_root_.continuous_apply i).comp
            (continuous_toMatrixHom ρ))).congr fun g ↦
              (Matrix.GeneralLinearGroup.liftSubring_apply E.toSubring
                (toMatrixHom ρ) hmem g i j).symm
      have hsum : Continuous fun p : Γ × (Fin (Module.finrank Ω V) → E) ↦
          ∑ j, (ρE p.1 : Matrix (Fin (Module.finrank Ω V))
            (Fin (Module.finrank Ω V)) E) i j * p.2 j := by
        fun_prop
      exact hsum.congr fun p ↦ by
        simp [Matrix.mulVec, dotProduct] }

/-- The base change of `ofMatrixDescent` to `Ω` is isomorphic as a continuous representation to
the original representation `ρ`. -/
private noncomputable def baseChangeOfMatrixDescentIso {Γ F Ω V : Type*} [Group Γ]
    [TopologicalSpace Γ] [Field F] [Field Ω] [Algebra F Ω]
    [TopologicalSpace Ω] [IsTopologicalRing Ω]
    [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
    [TopologicalSpace V] [IsModuleTopology Ω V]
    (ρ : ContinuousRep Γ Ω V) (E : IntermediateField F Ω)
    (hmem : ∀ g i j, (toMatrixHom ρ g : Matrix (Fin (Module.finrank Ω V))
      (Fin (Module.finrank Ω V)) Ω) i j ∈ E)
    [TopologicalSpace (Ω ⊗[E] (Fin (Module.finrank Ω V) → E))]
    [IsModuleTopology Ω (Ω ⊗[E] (Fin (Module.finrank Ω V) → E))] :
    Iso ((ofMatrixDescent ρ E hmem).baseChange Ω) ρ := by
  let b := Module.finBasis Ω V
  let eE := Pi.basisFun E (Fin (Module.finrank Ω V))
  let φ : Ω ⊗[E] (Fin (Module.finrank Ω V) → E) ≃ₗ[Ω] V :=
    (eE.baseChange Ω).equiv b (Equiv.refl _)
  refine Iso.ofEquiv (Representation.Equiv.mk φ fun g ↦ ?_)
  apply (eE.baseChange Ω).ext
  intro j
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Module.Basis.baseChange_apply]
  have hbc : ((ofMatrixDescent ρ E hmem).baseChange Ω).toRepresentation g (1 ⊗ₜ[E] eE j) =
      1 ⊗ₜ[E] (ofMatrixDescent ρ E hmem g) (eE j) := by
    rw [toRepresentation_baseChange, Representation.baseChange_apply, LinearMap.baseChange_tmul,
      coe_toRepresentation]
  rw [hbc]
  have hφ (k : Fin (Module.finrank Ω V)) : φ (1 ⊗ₜ[E] eE k) = b k := by
    simpa [φ, Module.Basis.baseChange_apply] using
      (eE.baseChange Ω).equiv_apply k b (Equiv.refl _)
  rw [hφ j]
  let ρE := Matrix.GeneralLinearGroup.liftSubring E.toSubring (toMatrixHom ρ) hmem
  have hact : (ofMatrixDescent ρ E hmem g) (eE j) =
      ∑ i, (ρE g : Matrix _ _ E) i j • eE i := by
    ext i
    simp [ofMatrixDescent, ρE, eE, Matrix.mulVec, dotProduct, Pi.basisFun_apply, Pi.single_apply]
  rw [hact, TensorProduct.tmul_sum, map_sum]
  have hρb : ρ g (b j) = ∑ i, ((ρE g : Matrix _ _ E) i j : Ω) • b i := by
    rw [← b.sum_repr (ρ g (b j))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    rw [Matrix.GeneralLinearGroup.liftSubring_apply]
    exact (LinearMap.toMatrix_apply b b (ρ g) i j).symm
  rw [coe_toRepresentation, hρb]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have htmul (a : Ω) : φ (a ⊗ₜ[E] eE i) = a • b i := by
    calc φ (a ⊗ₜ[E] eE i) = φ (a • (1 ⊗ₜ[E] eE i)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = a • b i := by rw [map_smul, hφ i]
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, htmul]
  rfl

/-- **Descent of a continuous representation to a finite intermediate field.** Under the hypotheses
of Baire descent, every finite-dimensional continuous representation `ρ : ContinuousRep Γ Ω V`
(with `V` carrying its `Ω`-module topology) descends to a continuous representation over a finite
intermediate field `E ⊇ K` of `Ω / F`. -/
theorem exists_descent
    {Γ F Ω V : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ]
    [NontriviallyNormedField F] [CompleteSpace F]
    [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    [TopologicalSpace Ω] [IsTopologicalRing Ω] [ContinuousSMul F Ω] [T2Space Ω]
    [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
    [TopologicalSpace V] [IsModuleTopology Ω V]
    (hcount : {E : IntermediateField F Ω | FiniteDimensional F E}.Countable)
    (ρ : ContinuousRep Γ Ω V)
    (K : IntermediateField F Ω) [FiniteDimensional F K] :
    ∃ (E : IntermediateField F Ω) (_ : K ≤ E) (_ : FiniteDimensional F E)
      (ρE : ContinuousRep Γ E (Fin (Module.finrank Ω V) → E)),
      ∀ [TopologicalSpace (Ω ⊗[E] (Fin (Module.finrank Ω V) → E))]
        [IsModuleTopology Ω (Ω ⊗[E] (Fin (Module.finrank Ω V) → E))],
        Nonempty (Iso (ρE.baseChange Ω) ρ) := by
  obtain ⟨E, hKE, hE, hmem⟩ := exists_finiteDimensional_mem_matrix hcount (toMatrixHom ρ)
    (continuous_toMatrixHom ρ) K
  exact ⟨E, hKE, hE, ofMatrixDescent ρ E hmem,
    fun [_] [_] ↦ ⟨baseChangeOfMatrixDescentIso ρ E hmem⟩⟩

/-- **Simultaneous descent of a finite family of continuous representations.** Any finite family
`ρ a : ContinuousRep Γ Ω (V a)` descends simultaneously to a single finite intermediate field
`E ⊇ K` of `Ω / F`. -/
theorem exists_descent_family
    {Γ F Ω α : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ] [Finite α]
    [NontriviallyNormedField F] [CompleteSpace F]
    [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    [TopologicalSpace Ω] [IsTopologicalRing Ω] [ContinuousSMul F Ω] [T2Space Ω]
    {V : α → Type*} [∀ a, AddCommGroup (V a)] [∀ a, Module Ω (V a)]
    [∀ a, FiniteDimensional Ω (V a)] [∀ a, TopologicalSpace (V a)]
    [∀ a, IsModuleTopology Ω (V a)]
    (hcount : {E : IntermediateField F Ω | FiniteDimensional F E}.Countable)
    (ρ : ∀ a, ContinuousRep Γ Ω (V a))
    (K : IntermediateField F Ω) [FiniteDimensional F K] :
    ∃ (E : IntermediateField F Ω) (_ : K ≤ E) (_ : FiniteDimensional F E)
      (ρE : ∀ a, ContinuousRep Γ E (Fin (Module.finrank Ω (V a)) → E)),
      ∀ a [TopologicalSpace (Ω ⊗[E] (Fin (Module.finrank Ω (V a)) → E))]
        [IsModuleTopology Ω (Ω ⊗[E] (Fin (Module.finrank Ω (V a)) → E))],
        Nonempty (Iso ((ρE a).baseChange Ω) (ρ a)) := by
  obtain ⟨E, hKE, hE, hmem⟩ := exists_finiteDimensional_mem_matrix_family hcount
    (fun a ↦ toMatrixHom (ρ a)) (fun a ↦ continuous_toMatrixHom (ρ a)) K
  exact ⟨E, hKE, hE, fun a ↦ ofMatrixDescent (ρ a) E (hmem a),
    fun a [_] [_] ↦ ⟨baseChangeOfMatrixDescentIso (ρ a) E (hmem a)⟩⟩

/-- **Descent of a continuous `PadicAlgCl ℓ`-representation to a finite extension of `ℚ_[ℓ]`.** -/
theorem exists_descent_padicAlgCl
    {Γ V : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] [FiniteDimensional (PadicAlgCl ℓ) V]
    [TopologicalSpace V] [IsModuleTopology (PadicAlgCl ℓ) V]
    (ρ : ContinuousRep Γ (PadicAlgCl ℓ) V)
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : K ≤ E) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρE : ContinuousRep Γ E (Fin (Module.finrank (PadicAlgCl ℓ) V) → E)),
      ∀ [TopologicalSpace (PadicAlgCl ℓ ⊗[E] (Fin (Module.finrank (PadicAlgCl ℓ) V) → E))]
        [IsModuleTopology (PadicAlgCl ℓ)
          (PadicAlgCl ℓ ⊗[E] (Fin (Module.finrank (PadicAlgCl ℓ) V) → E))],
        Nonempty (Iso (ρE.baseChange (PadicAlgCl ℓ)) ρ) :=
  exists_descent (PadicAlgCl.countable_setOf_finiteDimensional ℓ) ρ K

/-- **Simultaneous descent of a finite family of continuous `PadicAlgCl ℓ`-representations to a
single finite extension of `ℚ_[ℓ]`.** -/
theorem exists_descent_family_padicAlgCl
    {Γ α : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ] [Finite α]
    (ℓ : ℕ) [Fact ℓ.Prime]
    {V : α → Type*} [∀ a, AddCommGroup (V a)] [∀ a, Module (PadicAlgCl ℓ) (V a)]
    [∀ a, FiniteDimensional (PadicAlgCl ℓ) (V a)] [∀ a, TopologicalSpace (V a)]
    [∀ a, IsModuleTopology (PadicAlgCl ℓ) (V a)]
    (ρ : ∀ a, ContinuousRep Γ (PadicAlgCl ℓ) (V a))
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : K ≤ E) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρE : ∀ a, ContinuousRep Γ E (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E)),
      ∀ a [TopologicalSpace (PadicAlgCl ℓ ⊗[E] (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E))]
        [IsModuleTopology (PadicAlgCl ℓ)
          (PadicAlgCl ℓ ⊗[E] (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E))],
        Nonempty (Iso ((ρE a).baseChange (PadicAlgCl ℓ)) (ρ a)) :=
  exists_descent_family (PadicAlgCl.countable_setOf_finiteDimensional ℓ) ρ K

/-- **Faithfully flat base change is injective on isomorphisms of continuous representations.** -/
theorem Iso.baseChange_injective
    {Γ A B M N : Type*} [Monoid Γ] [TopologicalSpace Γ]
    [CommRing A] [TopologicalSpace A]
    [Ring B] [TopologicalSpace B] [IsTopologicalSemiring B] [Algebra A B] [ContinuousSMul A B]
    [Module.FaithfullyFlat A B]
    [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [TopologicalSpace N] [IsModuleTopology A N] [Module.Finite A N]
    [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]
    [TopologicalSpace (B ⊗[A] N)] [IsModuleTopology B (B ⊗[A] N)]
    {ρ : ContinuousRep Γ A M} {σ : ContinuousRep Γ A N} :
    Function.Injective (fun e : Iso ρ σ ↦ e.baseChange B) := fun e₁ e₂ h ↦ by
  have heq : e₁.toRepresentationEquiv.baseChange B = e₂.toRepresentationEquiv.baseChange B := by
    apply Representation.Equiv.ext
    funext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul b m =>
      have hx := DFunLike.congr_fun h (b ⊗ₜ m)
      simpa only [Iso.baseChange_tmul, Representation.Equiv.baseChange_tmul,
        Iso.coe_toRepresentationEquiv] using hx
  have hrep := Representation.Equiv.baseChange_injective heq
  exact Iso.ext fun m ↦ DFunLike.congr_fun hrep m

/-- **Descent of an isomorphism of continuous representations to a finite intermediate field.**
Over an algebraic field extension `Ω / E` of topological fields, an isomorphism between
base-changed finite-dimensional continuous `E`-representations descends to an isomorphism over a
finite intermediate field `E' : IntermediateField E Ω`. -/
theorem Iso.exists_descent
    {Γ E Ω V W : Type*} [Monoid Γ] [TopologicalSpace Γ]
    [Field E] [TopologicalSpace E]
    [Field Ω] [Algebra E Ω] [Algebra.IsAlgebraic E Ω]
    [TopologicalSpace Ω] [IsTopologicalRing Ω] [ContinuousSMul E Ω]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [TopologicalSpace V] [IsModuleTopology E V]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    [TopologicalSpace W] [IsModuleTopology E W]
    [TopologicalSpace (Ω ⊗[E] V)] [IsModuleTopology Ω (Ω ⊗[E] V)]
    [TopologicalSpace (Ω ⊗[E] W)] [IsModuleTopology Ω (Ω ⊗[E] W)]
    {ρ : ContinuousRep Γ E V} {σ : ContinuousRep Γ E W}
    (e : Iso (ρ.baseChange Ω) (σ.baseChange Ω)) :
    ∃ (E' : IntermediateField E Ω) (_ : FiniteDimensional E E'),
      ∀ [TopologicalSpace (E' ⊗[E] V)] [IsModuleTopology E' (E' ⊗[E] V)]
        [TopologicalSpace (E' ⊗[E] W)] [IsModuleTopology E' (E' ⊗[E] W)]
        [TopologicalSpace (Ω ⊗[E'] (E' ⊗[E] V))] [IsModuleTopology Ω (Ω ⊗[E'] (E' ⊗[E] V))]
        [TopologicalSpace (Ω ⊗[E'] (E' ⊗[E] W))] [IsModuleTopology Ω (Ω ⊗[E'] (E' ⊗[E] W))],
        ∃ e' : Iso (ρ.baseChange E') (σ.baseChange E'),
          (e'.baseChange Ω).trans (σ.baseChangeTransIso E' Ω) =
            (ρ.baseChangeTransIso E' Ω).trans e := by
  let e₀ : (Representation.baseChange Ω ρ.toRepresentation).Equiv
      (Representation.baseChange Ω σ.toRepresentation) :=
    Representation.Equiv.mk e.toRepresentationEquiv.toLinearEquiv fun g ↦ by
      rw [← toRepresentation_baseChange, ← toRepresentation_baseChange]
      exact e.toRepresentationEquiv.isIntertwining' g
  obtain ⟨E', hE', e', he'⟩ := Representation.Equiv.exists_descent e₀
  refine ⟨E', hE', fun [_] [_] [_] [_] [_] [_] [_] [_] ↦ ?_⟩
  let e'C : Iso (ρ.baseChange E') (σ.baseChange E') :=
    Iso.ofEquiv (Representation.Equiv.mk e'.toLinearEquiv fun g ↦ by
      rw [toRepresentation_baseChange, toRepresentation_baseChange]
      exact e'.isIntertwining' g)
  refine ⟨e'C, Iso.ext fun x ↦ ?_⟩
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [Iso.trans_apply, map_add, hx, hy]
  | tmul ω y =>
    have hx := DFunLike.congr_fun he' (ω ⊗ₜ y)
    have h1 : e'C y = e' y := Iso.ofEquiv_apply _ y
    have h2 : ∀ z, e₀ z = e z := fun _ ↦ rfl
    have hσ (a : Ω) (b : E' ⊗[E] W) :
        σ.baseChangeTransIso E' Ω (a ⊗ₜ b) =
          σ.toRepresentation.baseChangeTransEquiv E' Ω (a ⊗ₜ b) := by
      induction b using TensorProduct.inductionOn with
      | add b₁ b₂ hb₁ hb₂ => simp [TensorProduct.tmul_add, map_add, hb₁, hb₂]
      | tmul c w => simp
    have hρ (a : Ω) (b : E' ⊗[E] V) :
        ρ.baseChangeTransIso E' Ω (a ⊗ₜ b) =
          ρ.toRepresentation.baseChangeTransEquiv E' Ω (a ⊗ₜ b) := by
      induction b using TensorProduct.inductionOn with
      | add b₁ b₂ hb₁ hb₂ => simp [TensorProduct.tmul_add, map_add, hb₁, hb₂]
      | tmul c v => simp
    simpa only [Iso.trans_apply, Iso.baseChange_tmul, h1, hσ, hρ,
      Representation.Equiv.trans_apply, Representation.Equiv.baseChange_tmul, h2] using hx

end ContinuousRepDescent

section IntegralConjugation

/-- **Integral conjugation over a valuative field with PID valuation ring.** A continuous matrix
representation of a compact group over a field `E` with a valuative topology whose valuation ring
`𝒪[E]` is a principal ideal domain (in particular, any nonarchimedean local field) is conjugate in
`GL_ι(E)` to a representation with all matrix entries in `𝒪[E]`. -/
theorem exists_conj_mem_integerRing
    {Γ E ι : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
    [IsPrincipalIdealRing 𝒪[E]]
    [Fintype ι] [DecidableEq ι]
    (ρ : Γ →* GL ι E) (hρ : Continuous fun g ↦ (ρ g : Matrix ι ι E)) :
    ∃ P : GL ι E, ∀ g i j, (P * ρ g * P⁻¹ : Matrix ι ι E) i j ∈ 𝒪[E] := by
  let r : Representation E Γ (ι → E) :=
    { toFun g := Matrix.mulVecLin (ρ g : Matrix ι ι E)
      map_one' := by
        rw [map_one, Units.val_one, Matrix.mulVecLin_one]
        rfl
      map_mul' g h := by
        rw [map_mul, Units.val_mul, Matrix.mulVecLin_mul]
        rfl }
  have hr (x : ι → E) : Continuous fun g ↦ r g x := by
    refine continuous_pi fun i ↦ ?_
    have hentry (j : ι) : Continuous fun g : Γ ↦ (ρ g : Matrix ι ι E) i j :=
      (_root_.continuous_apply j).comp ((_root_.continuous_apply i).comp hρ)
    have hsum : Continuous fun g : Γ ↦ ∑ j, (ρ g : Matrix ι ι E) i j * x j := by
      fun_prop
    exact hsum.congr fun g ↦ by simp [r, Matrix.mulVec, dotProduct]
  obtain ⟨L, hL, hstab⟩ := r.exists_stable_lattice hr
  have : IsLattice E L := hL
  have : Module.IsTorsionFree 𝒪[E] E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective 𝒪[E] E)
  let bL₀ := Module.Free.chooseBasis 𝒪[E] L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex 𝒪[E] L) = Fintype.card ι := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Submodule.IsLattice.finrank_of_pi E L]
  let bL : Basis ι 𝒪[E] L := bL₀.reindex (Fintype.equivOfCardEq hcard)
  let b : Basis ι E (ι → E) := bL.extendOfIsLattice E
  let std : Basis ι E (ι → E) := Pi.basisFun E ι
  let P : GL ι E :=
    { val := b.toMatrix std
      inv := std.toMatrix b
      val_inv := b.toMatrix_mul_toMatrix_flip std
      inv_val := std.toMatrix_mul_toMatrix_flip b }
  refine ⟨P, fun g i j ↦ ?_⟩
  have hconj : (P * ρ g * P⁻¹ : Matrix ι ι E) = LinearMap.toMatrix b b (r g) := by
    have hstd : LinearMap.toMatrix std std (r g) = (ρ g : Matrix ι ι E) := by
      ext a c
      simp [r, std, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hPval : (P : Matrix ι ι E) = b.toMatrix std := rfl
    have hPinv : ((P⁻¹ : GL ι E) : Matrix ι ι E) = std.toMatrix b := rfl
    rw [hPval, hPinv, ← hstd, ← LinearMap.toMatrix_id_eq_basis_toMatrix,
      ← LinearMap.toMatrix_id_eq_basis_toMatrix, ← LinearMap.toMatrix_comp,
      ← LinearMap.toMatrix_comp, LinearMap.id_comp, LinearMap.comp_id]
  rw [hconj, LinearMap.toMatrix_apply]
  have hbj : b j ∈ L := by
    rw [Module.Basis.extendOfIsLattice_apply]
    exact (bL j).2
  let v : L := ⟨r g (b j), hstab g (b j) hbj⟩
  have hv : r g (b j) = ∑ k, ((bL.repr v k : 𝒪[E]) : E) • b k := by
    calc r g (b j) = (v : ι → E) := rfl
      _ = ((∑ k, bL.repr v k • bL k : L) : ι → E) := congrArg Subtype.val (bL.sum_repr v).symm
      _ = ∑ k, ((bL.repr v k : 𝒪[E]) : E) • b k := by
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Submodule.coe_smul_of_tower, Module.Basis.extendOfIsLattice_apply]
        rfl
  rw [← Module.Basis.coord_apply, hv, map_sum]
  simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact (bL.repr v i).2

/-- **Integral conjugation lifted to `Γ →ₜ* GL_ι(𝒪[E])`.** Under the hypotheses of
`TauCeti.ContinuousRep.exists_conj_mem_integerRing`, a continuous homomorphism `ρ : Γ →ₜ* GL_ι(E)`
is conjugate in `GL_ι(E)` to the image of a continuous homomorphism `ρ₀ : Γ →ₜ* GL_ι(𝒪[E])`. -/
theorem exists_conj_eq_map_integerRing
    {Γ E ι : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
    [IsPrincipalIdealRing 𝒪[E]]
    [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι E) :
    ∃ (P : GL ι E) (ρ₀ : Γ →ₜ* GL ι 𝒪[E]),
      ∀ g, Matrix.GeneralLinearGroup.map 𝒪[E].subtype (ρ₀ g) = P * ρ g * P⁻¹ := by
  obtain ⟨P, hP⟩ :=
    exists_conj_mem_integerRing ρ.toMonoidHom (Units.continuous_val.comp ρ.continuous)
  let ρ' : Γ →* GL ι E :=
    { toFun g := P * ρ g * P⁻¹
      map_one' := by simp
      map_mul' g h := by simp [mul_assoc] }
  let ρ₀_monoid : Γ →* GL ι 𝒪[E] := Matrix.GeneralLinearGroup.liftSubring 𝒪[E] ρ' hP
  have hmap (g : Γ) : Matrix.GeneralLinearGroup.map 𝒪[E].subtype (ρ₀_monoid g) = P * ρ g * P⁻¹ :=
    Matrix.GeneralLinearGroup.map_liftSubring 𝒪[E] ρ' hP g
  have hcont : Continuous ρ₀_monoid := by
    refine (IsInducing.generalLinearGroup_map (f := 𝒪[E].subtype)
      IsInducing.subtypeVal).continuous_iff.mpr ?_
    have hconj : Continuous fun g : Γ ↦ P * ρ g * P⁻¹ :=
      (continuous_const.mul ρ.continuous).mul continuous_const
    exact hconj.congr fun g ↦ (hmap g).symm
  exact ⟨P, ⟨ρ₀_monoid, hcont⟩, hmap⟩

/-- **Integral conjugation over `PadicAlgCl ℓ`.** Every continuous homomorphism
`ρ : Γ →ₜ* GL_ι(PadicAlgCl ℓ)` from a compact Baire group with separately continuous
multiplication (in particular, any compact Hausdorff topological group) is conjugate in
`GL_ι(PadicAlgCl ℓ)` to a representation with entries in `𝒪_E` (norm at most `1`) for some finite
intermediate field `E / ℚ_[ℓ]`. -/
theorem exists_integral_conj_GL
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ]
    (ℓ : ℕ) [Fact ℓ.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)) :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (P : GL ι (PadicAlgCl ℓ)),
      FiniteDimensional ℚ_[ℓ] E ∧
      ∀ (g : Γ) (i j : ι),
        (P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j ∈ E ∧
          ‖(P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j‖ ≤ 1 := by
  obtain ⟨E, -, hE, hmem⟩ := baire_descent ℓ ρ ⊥
  have : FiniteDimensional ℚ_[ℓ] E := hE
  let ρE : Γ →* GL ι E := Matrix.GeneralLinearGroup.liftSubring E.toSubring ρ.toMonoidHom hmem
  have hρm : Continuous fun g ↦ (ρ g : Matrix ι ι (PadicAlgCl ℓ)) :=
    Units.continuous_val.comp ρ.continuous
  have hρE_cont : Continuous fun g ↦ (ρE g : Matrix ι ι E) :=
    continuous_matrix fun i j ↦
      IsInducing.subtypeVal.continuous_iff.mpr <|
        ((_root_.continuous_apply j).comp ((_root_.continuous_apply i).comp hρm)).congr fun g ↦
          (Matrix.GeneralLinearGroup.liftSubring_apply E.toSubring ρ.toMonoidHom hmem g i j).symm
  let := TauCeti.algebraicExtensionValuativeRel ℚ_[ℓ] E
  have := PadicAlgCl.isNonarchimedeanLocalField E
  obtain ⟨PE, hPE⟩ := exists_conj_mem_integerRing ρE hρE_cont
  let P : GL ι (PadicAlgCl ℓ) := Matrix.GeneralLinearGroup.map E.subtype PE
  refine ⟨E, P, hE, fun g i j ↦ ?_⟩
  have hentry : (P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j =
      ((PE * ρE g * PE⁻¹ : Matrix ι ι E) i j : PadicAlgCl ℓ) := by
    have hGL : P * ρ g * P⁻¹ = Matrix.GeneralLinearGroup.map E.subtype (PE * ρE g * PE⁻¹) := by
      have hsub : Matrix.GeneralLinearGroup.map E.subtype (ρE g) = ρ g :=
        Matrix.GeneralLinearGroup.map_liftSubring E.toSubring ρ.toMonoidHom hmem g
      simp only [P, map_mul, map_inv, hsub]
    rw [← Units.val_mul, ← Units.val_mul, hGL, Matrix.GeneralLinearGroup.map_apply,
      Units.val_mul, Units.val_mul]
    rfl
  rw [hentry]
  exact ⟨SetLike.coe_mem _, (PadicAlgCl.mem_integerRing_iff E _).mp (hPE g i j)⟩

end IntegralConjugation

end TauCeti.ContinuousRep
