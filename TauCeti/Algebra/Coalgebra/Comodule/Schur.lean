/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Intertwiner
public import TauCeti.Algebra.Coalgebra.Comodule.Preadditive
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import TauCeti.RingTheory.Semisimple.Schur

/-!
# Schur's lemma for simple comodules

Over an algebraically closed field, every comodule endomorphism of a simple right comodule is a
scalar multiple of the identity. No separate finite-dimensionality assumption is needed: over a
field, a simple comodule is automatically finite-dimensional by
`TauCeti.Subcomodule.finite_of_isAtom`. Passing through `TauCeti.Comodule.convolutionModule`
applies module-level Schur's lemma (`TauCeti.endAlgEquivSelfOfIsSimpleModule`) directly.

Translated into coefficient matrices via `Module.Basis.map_coact_iff_coefficientMatrix`, any
scalar matrix intertwining the coefficient matrix of a simple comodule over an algebraically
closed field is a scalar multiple of the identity matrix, while any scalar matrix intertwining
the coefficient matrices of two comodules with no nonzero morphism between them vanishes.

## Main results

* `TauCeti.Comodule.nontrivial_of_isSimpleOrder`: every simple comodule is nontrivial.
* `TauCeti.Comodule.finite_of_isSimpleOrder`: every simple comodule over a projective coalgebra is
  finite.
* `TauCeti.Comodule.forall_hom_eq_zero_comm`: between simple comodules over a projective
  coalgebra, the vanishing of all morphisms in one direction is symmetric.
* `TauCeti.Comodule.Hom.exists_eq_smul_id`: every endomorphism of a simple comodule over an
  algebraically closed field is a scalar multiple of the identity.
* `TauCeti.Comodule.exists_eq_smul_one_of_coefficientMatrix_mul_eq`: a scalar matrix commuting
  with the coefficient matrix of a simple comodule over an algebraically closed field is a
  scalar multiple of the identity matrix.
* `TauCeti.Comodule.eq_zero_of_coefficientMatrix_mul_eq`: a scalar matrix intertwining two
  coefficient matrices vanishes when there is no nonzero comodule morphism between the comodules.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Section 1.3.
-/

public section

open Module

namespace TauCeti.Comodule

attribute [local instance] convolutionModule

section CommSemiring

variable {R C M : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Every simple comodule is nontrivial. -/
theorem nontrivial_of_isSimpleOrder [IsSimpleOrder (Subcomodule R C M)] : Nontrivial M := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hbt : (⊥ : Subcomodule R C M) = ⊤ :=
    Subcomodule.ext fun m ↦ by simp [Subsingleton.elim m 0]
  exact bot_ne_top hbt

end CommSemiring

section CommRing

variable {R C M N : Type*} [CommRing R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Projective R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M]
  [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- Every simple comodule over a projective coalgebra is finitely generated. -/
theorem finite_of_isSimpleOrder [IsSimpleOrder (Subcomodule R C M)] : Module.Finite R M := by
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  have hfin : Module.Finite R (⊤ : Subcomodule R C M).toSubmodule :=
    Subcomodule.finite_of_isAtom (isAtom_top (α := Subcomodule R C M))
  rw [Subcomodule.top_toSubmodule] at hfin
  exact Module.Finite.equiv (Submodule.topEquiv (R := R) (M := M))

private theorem hom_eq_zero_of_forall_eq_zero [IsSimpleOrder (Subcomodule R C M)]
    [IsSimpleOrder (Subcomodule R C N)] (h : ∀ f : Hom R C M N, f = 0)
    (g : Hom R C N M) : g = 0 := by
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  have : IsSimpleModule (WithConv (C →ₗ[R] R)) M := isSimpleModule_convolution_iff.mpr inferInstance
  have : IsSimpleModule (WithConv (C →ₗ[R] R)) N := isSimpleModule_convolution_iff.mpr inferInstance
  by_contra hg
  have hg' : g.toConvolutionLinearMap ≠ 0 := fun h0 ↦ hg <| by
    ext n
    simpa using LinearMap.congr_fun h0 n
  let e := LinearEquiv.ofBijective g.toConvolutionLinearMap (LinearMap.bijective_of_ne_zero hg')
  have hzero : e.symm.toLinearMap.toComoduleHom = 0 := h _
  have := IsSimpleModule.nontrivial (WithConv (C →ₗ[R] R)) M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  apply hm
  have := congrArg (fun f : Hom R C M N ↦ f m) hzero
  simpa [e] using this

/-- Between simple comodules over a projective coalgebra, having no nonzero comodule morphism is
a symmetric condition: any nonzero morphism is an isomorphism for the convolution-dual action. -/
theorem forall_hom_eq_zero_comm [IsSimpleOrder (Subcomodule R C M)]
    [IsSimpleOrder (Subcomodule R C N)] :
    (∀ f : Hom R C M N, f = 0) ↔ (∀ g : Hom R C N M, g = 0) :=
  ⟨hom_eq_zero_of_forall_eq_zero, hom_eq_zero_of_forall_eq_zero⟩

end CommRing

section IsAlgClosed

variable {k C M : Type*} [Field k] [IsAlgClosed k]
  [AddCommMonoid C] [Module k C] [Coalgebra k C]
  [AddCommMonoid M] [Module k M] [Comodule k C M]

/-- **Schur's lemma for simple comodules.** Over an algebraically closed field, every comodule
endomorphism of a simple comodule is a scalar multiple of the identity. -/
theorem Hom.exists_eq_smul_id [IsSimpleOrder (Subcomodule k C M)] (f : Hom k C M M) :
    ∃ c : k, f = c • Hom.id k C M := by
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup k
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  have : IsSimpleModule (WithConv (C →ₗ[k] k)) M := isSimpleModule_convolution_iff.mpr inferInstance
  have : Module.Finite k M := finite_of_isSimpleOrder (R := k) (C := C)
  refine ⟨TauCeti.endAlgEquivSelfOfIsSimpleModule (k := k) (A := WithConv (C →ₗ[k] k))
    f.toConvolutionLinearMap, ?_⟩
  ext m
  rw [Hom.smul_apply, Hom.id_apply, ← Hom.toConvolutionLinearMap_apply]
  exact (TauCeti.endAlgEquivSelfOfIsSimpleModule_smul (k := k) f.toConvolutionLinearMap m).symm

end IsAlgClosed

section MatrixIntertwiner

/-- A scalar matrix intertwining the coefficient matrices of two finite free comodules vanishes
when there is no nonzero comodule morphism between them. -/
theorem eq_zero_of_coefficientMatrix_mul_eq
    {R A M N ι κ : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Coalgebra R A]
    [AddCommMonoid M] [Module R M] [Comodule R A M]
    [AddCommMonoid N] [Module R N] [Comodule R A N]
    [Fintype ι] [Fintype κ] (b : Basis ι R M) (c : Basis κ R N)
    (hzero : ∀ f : Hom R A M N, f = 0) {T : Matrix κ ι R}
    (hT : coefficientMatrix (C := A) c * T.map (algebraMap R A) =
      T.map (algebraMap R A) * coefficientMatrix (C := A) b) :
    T = 0 := by
  classical
  let f₀ : M →ₗ[R] N := Matrix.toLin b c T
  have hf₀ : LinearMap.toMatrix b c f₀ = T := LinearMap.toMatrix_toLin b c T
  let f : Hom R A M N :=
    ⟨f₀, (b.map_coact_iff_coefficientMatrix c f₀).mpr (by rwa [hf₀])⟩
  have hfz : f₀ = 0 := congrArg Hom.toLinearMap (hzero f)
  rw [← hf₀, hfz, map_zero]

/-- **Matrix form of Schur's lemma for simple comodules.** Over an algebraically closed field, any
scalar matrix commuting with the coefficient matrix of a simple comodule is a scalar multiple of
the identity matrix. -/
theorem exists_eq_smul_one_of_coefficientMatrix_mul_eq
    {k A M ι : Type*} [Field k] [IsAlgClosed k] [Semiring A] [Algebra k A] [Coalgebra k A]
    [AddCommMonoid M] [Module k M] [Comodule k A M] [IsSimpleOrder (Subcomodule k A M)]
    [Fintype ι] [DecidableEq ι] (b : Basis ι k M) {T : Matrix ι ι k}
    (hT : coefficientMatrix (C := A) b * T.map (algebraMap k A) =
      T.map (algebraMap k A) * coefficientMatrix (C := A) b) :
    ∃ c : k, T = c • (1 : Matrix ι ι k) := by
  let f₀ : M →ₗ[k] M := Matrix.toLin b b T
  have hf₀ : LinearMap.toMatrix b b f₀ = T := LinearMap.toMatrix_toLin b b T
  let f : Hom k A M M :=
    ⟨f₀, (b.map_coact_iff_coefficientMatrix b f₀).mpr (by rwa [hf₀])⟩
  obtain ⟨c, hc⟩ := f.exists_eq_smul_id
  refine ⟨c, ?_⟩
  have hlin : f₀ = c • LinearMap.id := congrArg Hom.toLinearMap hc
  rw [← hf₀, hlin, map_smul, LinearMap.toMatrix_id]

end MatrixIntertwiner

end TauCeti.Comodule
