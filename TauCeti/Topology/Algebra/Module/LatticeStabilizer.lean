/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Lattice
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup

/-!
# Topological matrix form of a lattice stabilizer

Let `R` be a commutative topological ring embedded topologically (`Topology.IsInducing`) in its
fraction field `K`, where `K` is a topological semiring, and let `L ⊆ V` be a full `R`-lattice
with a finite `R`-basis `b : Module.Basis ι R L`.

Algebraically, `Module.Basis.stabilizerMulEquivGL` identifies the stabilizer of `L` in `V ≃ₗ[K] V`
with `GL ι R`, compatibly with `Module.Basis.toGL` in the extended `K`-basis `b.extendOfIsLattice K`
and the entrywise map `GL ι R → GL ι K`. Because `(b.extendOfIsLattice K).toGLContinuousMulEquiv`
is a topological group isomorphism and `GL ι R → GL ι K` is topologically inducing, this algebraic
isomorphism is automatically a topological group isomorphism
(`Module.Basis.stabilizerContinuousMulEquiv`).

## Main definitions

* `Module.Basis.stabilizerContinuousMulEquiv`: topological group isomorphism between the stabilizer
  of a full lattice `L` in `V ≃ₗ[K] V` (with the subspace topology) and `GL ι R`, whenever
  `algebraMap R K` is topologically inducing.
-/

public section

open scoped MatrixGroups Pointwise

namespace Module.Basis

variable {R K V ι : Type*} [CommRing R] [TopologicalSpace R]
  [Field K] [Algebra R K] [IsFractionRing R K] [TopologicalSpace K] [IsTopologicalSemiring K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [Fintype ι] [DecidableEq ι]

variable (K) in
/-- **Topological matrix form of a lattice stabilizer.** For a full `R`-lattice `L ⊆ V` with a
finite `R`-basis `b`, if `algebraMap R K : R → K` is topologically inducing, then the stabilizer
of `L` in `V ≃ₗ[K] V` is isomorphic as a topological group to `GL ι R`. -/
noncomputable def stabilizerContinuousMulEquiv {L : Submodule R V} [L.IsLattice K]
    (b : Module.Basis ι R L) (hR : Topology.IsInducing (algebraMap R K)) :
    MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ≃ₜ* GL ι R where
  __ := b.stabilizerMulEquivGL K
  continuous_toFun := by
    rw [hR.generalLinearGroup_map.continuous_iff]
    exact (((b.extendOfIsLattice K).toGLContinuousMulEquiv.continuous.comp
      continuous_subtype_val).congr fun g ↦ by simp)
  continuous_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuous_iff,
      (b.extendOfIsLattice K).toGLContinuousMulEquiv.isEmbedding.isInducing.continuous_iff]
    exact hR.generalLinearGroup_map.continuous.congr fun A ↦ by simp

@[simp]
theorem coe_stabilizerContinuousMulEquiv {L : Submodule R V} [L.IsLattice K]
    (b : Module.Basis ι R L) (hR : Topology.IsInducing (algebraMap R K)) :
    (b.stabilizerContinuousMulEquiv K hR :
      MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ≃* GL ι R) = b.stabilizerMulEquivGL K :=
  (rfl)

@[simp]
theorem stabilizerContinuousMulEquiv_apply {L : Submodule R V} [L.IsLattice K]
    (b : Module.Basis ι R L) (hR : Topology.IsInducing (algebraMap R K))
    (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) :
    b.stabilizerContinuousMulEquiv K hR g = b.stabilizerMulEquivGL K g :=
  (rfl)

@[simp]
theorem stabilizerContinuousMulEquiv_symm_apply {L : Submodule R V} [L.IsLattice K]
    (b : Module.Basis ι R L) (hR : Topology.IsInducing (algebraMap R K)) (A : GL ι R) :
    (b.stabilizerContinuousMulEquiv K hR).symm A = (b.stabilizerMulEquivGL K).symm A :=
  (rfl)

end Module.Basis
