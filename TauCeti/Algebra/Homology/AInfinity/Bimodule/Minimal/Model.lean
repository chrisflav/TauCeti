/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Iso
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Minimal.Basic
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Transfer
public import TauCeti.Algebra.Homology.Contraction.Linear.Homology

/-!
# Minimal models of A-infinity bimodules

Let `M` be an `(A, B)` `A∞` bimodule over `A∞` algebras `A` and `B`.  Whenever `(M, m_{0,0})`
admits a homogeneous special contraction onto a graded module `N` equipped with zero differential
over a commutative ring `R`, homological transfer (`TauCeti.AInfinityBimodule.transfer`) puts a
minimal `(A, B)` `A∞` bimodule structure on `N`, quasi-isomorphic to `M` via the extending and
projecting morphisms and unique up to isomorphism of `A∞` bimodules
(`TauCeti.AInfinityBimodule.isMinimal_transfer`,
`TauCeti.AInfinityBimodule.isIso_transferProjection_comp`, and
`TauCeti.AInfinityBimodule.isIso_comp_transferInclusion`).

Over a field `K`, every graded vector space `(M, m_{0,0})` with a square-zero degree-one
differential contracts onto its cohomology `H = ker m_{0,0} ⧸ im m_{0,0}` with zero differential
(`TauCeti.InternalGrading.homologyContraction`).  Transferring along this contraction yields the
bimodule version of Kadeishvili's theorem:

* `TauCeti.AInfinityBimodule.minimalModel` is a minimal `(A, B)` `A∞` bimodule structure on the
  unary cohomology `MM.Cohomology`, over the same algebras `A` and `B`;
* `TauCeti.AInfinityBimodule.minimalModelInclusion` and
  `TauCeti.AInfinityBimodule.minimalModelProjection` are quasi-isomorphisms between `MM` and
  `MM.minimalModel` with `minimalModelProjection.comp minimalModelInclusion = id`, inducing the
  canonical identifications on cohomology;
* any quasi-isomorphism between `MM` and a minimal `(A, B)` `A∞` bimodule becomes an isomorphism of
  `A∞` bimodules upon composing with `minimalModelProjection` or `minimalModelInclusion`
  (`TauCeti.AInfinityBimodule.isIso_minimalModelProjection_comp` and
  `TauCeti.AInfinityBimodule.isIso_comp_minimalModelInclusion`).

The right-module counterpart is `TauCeti.AInfinityRightModule.minimalModel` in
`TauCeti.Algebra.Homology.AInfinity.Module.Right.Minimal.Model`.

## Main definitions

* `TauCeti.AInfinityBimodule.minimalModel`: the minimal `(A, B)` `A∞` bimodule structure on
  `MM.Cohomology` over a field.
* `TauCeti.AInfinityBimodule.minimalModelInclusion`: the quasi-isomorphism from `MM.minimalModel`
  to `MM`.
* `TauCeti.AInfinityBimodule.minimalModelProjection`: the quasi-isomorphism from `MM` to
  `MM.minimalModel`.

## Main results

* `TauCeti.AInfinityBimodule.isMinimal_transfer`,
  `TauCeti.AInfinityBimodule.isIso_transferProjection_comp`, and
  `TauCeti.AInfinityBimodule.isIso_comp_transferInclusion`: minimality and uniqueness up to
  isomorphism for transfer along any homogeneous special contraction onto a zero-differential
  retract over a commutative ring.
* `TauCeti.AInfinityBimodule.isMinimal_minimalModel`: the minimal model over a field has zero unary
  differential.
* `TauCeti.AInfinityBimodule.isQuasiIso_minimalModelInclusion`,
  `TauCeti.AInfinityBimodule.isQuasiIso_minimalModelProjection`, and
  `TauCeti.AInfinityBimodule.minimalModelProjection_comp_minimalModelInclusion`: both morphisms are
  quasi-isomorphisms and the projection retracts the inclusion.
* `TauCeti.AInfinityBimodule.cohomologyMap_minimalModelInclusion` and
  `TauCeti.AInfinityBimodule.cohomologyMap_minimalModelProjection`: both morphisms induce the
  canonical identification on cohomology.
* `TauCeti.AInfinityBimodule.isIso_minimalModelProjection_comp` and
  `TauCeti.AInfinityBimodule.isIso_comp_minimalModelInclusion`: uniqueness of the minimal model up
  to isomorphism of `A∞` bimodules.

## References

* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 4--5.
* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
-/

public section

namespace TauCeti

universe uR uK uA uB uM uN uP

namespace AInfinityBimodule

/-! ### Minimal transfer under explicit splitting hypotheses over a commutative ring -/

section CommRing

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM} {N : Type uN} {P : Type uP}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} (MM : AInfinityBimodule AA BB M)
  {GN : InternalGrading R N ℤ} (c : LinearSpecialContraction MM.differential (0 : Module.End R N))
  (hh : LinearMap.IsHomogeneous c.homotopy MM.grading.piece MM.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GN.piece MM.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj MM.grading.piece GN.piece 0)

/-- Transferring an `A∞` bimodule along a homogeneous special contraction onto `(N, 0)` produces a
minimal `A∞` bimodule on `N`. -/
theorem isMinimal_transfer : (MM.transfer c hh hincl hproj).IsMinimal :=
  (isMinimal_def _).2 (MM.differential_transfer c hh hincl hproj)

/-- If `f` is a quasi-isomorphism from a minimal bimodule `PP` to `MM`, then `f` followed by the
projection onto any zero-differential transfer retract of `MM` is an isomorphism of `A∞`
bimodules. -/
theorem isIso_transferProjection_comp {PP : AInfinityBimodule AA BB P} (hP : PP.IsMinimal)
    {f : AInfinityBimoduleHom PP MM} (hf : f.IsQuasiIso) :
    ((MM.transferProjection c hh hincl hproj).comp f).IsIso :=
  ((MM.isQuasiIso_transferProjection c hh hincl hproj).comp hf).isIso ((isMinimal_def _).1 hP)
    (MM.differential_transfer c hh hincl hproj)

/-- If `g` is a quasi-isomorphism from `MM` to a minimal bimodule `PP`, then the inclusion of any
zero-differential transfer retract of `MM` followed by `g` is an isomorphism of `A∞` bimodules. -/
theorem isIso_comp_transferInclusion {PP : AInfinityBimodule AA BB P} (hP : PP.IsMinimal)
    {g : AInfinityBimoduleHom MM PP} (hg : g.IsQuasiIso) :
    (g.comp (MM.transferInclusion c hh hincl hproj)).IsIso :=
  (hg.comp (MM.isQuasiIso_transferInclusion c hh hincl hproj)).isIso
    (MM.differential_transfer c hh hincl hproj) ((isMinimal_def _).1 hP)

end CommRing

/-! ### Kadeishvili's minimal model over a field -/

section Field

variable {K : Type uK} {A : Type uA} {B : Type uB} {M : Type uM}
  [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup M] [Module K M] {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B}
  (MM : AInfinityBimodule AA BB M)

/-- The **minimal model** of an `(A, B)` `A∞` bimodule over a field: the `(A, B)` `A∞` bimodule on
the unary cohomology `MM.Cohomology = ker m_{0,0} ⧸ im m_{0,0}` transferred along
`InternalGrading.homologyContraction`.  Its unary differential vanishes
(`differential_minimalModel`). -/
noncomputable def minimalModel : AInfinityBimodule AA BB MM.Cohomology :=
  MM.transfer
    (MM.grading.homologyContraction MM.isHomogeneous_differential MM.differential_comp_self_eq_zero)
    (MM.grading.isHomogeneous_homologyContraction_homotopy _ _)
    (MM.grading.isHomogeneous_homologyContraction_incl _ _)
    (MM.grading.isHomogeneous_homologyContraction_proj _ _)

/-- Defining presentation of `minimalModel` as homological transfer along
`InternalGrading.homologyContraction`. -/
theorem minimalModel_def :
    MM.minimalModel =
      MM.transfer
        (MM.grading.homologyContraction MM.isHomogeneous_differential
          MM.differential_comp_self_eq_zero)
        (MM.grading.isHomogeneous_homologyContraction_homotopy _ _)
        (MM.grading.isHomogeneous_homologyContraction_incl _ _)
        (MM.grading.isHomogeneous_homologyContraction_proj _ _) :=
  (rfl)

/-- The minimal model carries the cohomology grading induced by homogeneous cycles. -/
@[simp]
theorem minimalModel_grading :
    MM.minimalModel.grading =
      MM.grading.homology MM.isHomogeneous_differential MM.differential_comp_self_eq_zero :=
  transfer_grading ..

/-- The minimal model has zero unary differential. -/
@[simp]
theorem differential_minimalModel : MM.minimalModel.differential = 0 :=
  differential_transfer ..

/-- The minimal model is a minimal `A∞` bimodule. -/
theorem isMinimal_minimalModel : MM.minimalModel.IsMinimal :=
  MM.isMinimal_transfer ..

/-- The quasi-isomorphism of `A∞` bimodules from the minimal model to `MM`, extending the choice of
homogeneous cycle representatives of cohomology classes. -/
noncomputable def minimalModelInclusion : AInfinityBimoduleHom MM.minimalModel MM :=
  MM.transferInclusion _
    (MM.grading.isHomogeneous_homologyContraction_homotopy _ _)
    (MM.grading.isHomogeneous_homologyContraction_incl _ _)
    (MM.grading.isHomogeneous_homologyContraction_proj _ _)

/-- The bar map of `minimalModelInclusion` is the perturbed inclusion of the contraction onto
cohomology. -/
@[simp]
theorem barMap_minimalModelInclusion :
    MM.minimalModelInclusion.barMap =
      (MM.transferContraction
        (MM.grading.homologyContraction MM.isHomogeneous_differential
          MM.differential_comp_self_eq_zero)
        (MM.grading.isHomogeneous_homologyContraction_homotopy _ _)
        (MM.grading.isHomogeneous_homologyContraction_incl _ _)
        (MM.grading.isHomogeneous_homologyContraction_proj _ _)).incl :=
  barMap_transferInclusion ..

/-- The linear part of the inclusion of the minimal model is the inclusion of the contraction onto
cohomology. -/
@[simp]
theorem linearPart_minimalModelInclusion :
    MM.minimalModelInclusion.linearPart =
      (MM.grading.homologyContraction MM.isHomogeneous_differential
        MM.differential_comp_self_eq_zero).incl :=
  linearPart_transferInclusion ..

/-- The linear part of the inclusion of the minimal model takes values in the unary cycles. -/
theorem linearPart_minimalModelInclusion_mem_ker (y : MM.Cohomology) :
    MM.minimalModelInclusion.linearPart y ∈ LinearMap.ker MM.differential := by
  rw [linearPart_minimalModelInclusion]
  exact InternalGrading.homologyContraction_incl_mem_ker ..

/-- The linear part of the inclusion of the minimal model sends each cohomology class to a cycle
representing it. -/
theorem homologyπ_linearPart_minimalModelInclusion (y : MM.Cohomology) :
    MM.differential.homologyπ MM.differential_comp_self_eq_zero
        ⟨_, MM.linearPart_minimalModelInclusion_mem_ker y⟩ = y := by
  simp only [linearPart_minimalModelInclusion]
  exact InternalGrading.homologyπ_homologyContraction_incl ..

/-- Under the canonical identification `MM.Cohomology ≃ₗ[K] MM.minimalModel.Cohomology`, the
inclusion of the minimal model induces the identity on cohomology. -/
theorem cohomologyMap_minimalModelInclusion_cohomologyEquiv (y : MM.Cohomology) :
    MM.minimalModelInclusion.cohomologyMap (MM.isMinimal_minimalModel.cohomologyEquiv y) = y := by
  rw [IsMinimal.cohomologyEquiv_apply, LinearMap.homologyπ_apply,
    AInfinityBimoduleHom.cohomologyMap_mk, ← LinearMap.homologyπ_apply]
  exact MM.homologyπ_linearPart_minimalModelInclusion y

/-- The cohomology map of the inclusion of the minimal model is the inverse of the canonical
identification `MM.isMinimal_minimalModel.cohomologyEquiv`. -/
theorem cohomologyMap_minimalModelInclusion :
    MM.minimalModelInclusion.cohomologyMap =
      MM.isMinimal_minimalModel.cohomologyEquiv.symm.toLinearMap := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨y, rfl⟩ := MM.isMinimal_minimalModel.cohomologyEquiv.surjective z
  rw [cohomologyMap_minimalModelInclusion_cohomologyEquiv, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- The inclusion of the minimal model is a quasi-isomorphism of `A∞` bimodules. -/
theorem isQuasiIso_minimalModelInclusion : MM.minimalModelInclusion.IsQuasiIso :=
  isQuasiIso_transferInclusion ..

/-- The quasi-isomorphism of `A∞` bimodules from `MM` to its minimal model, extending the
projection that sends each cycle to its cohomology class. -/
noncomputable def minimalModelProjection : AInfinityBimoduleHom MM MM.minimalModel :=
  MM.transferProjection _
    (MM.grading.isHomogeneous_homologyContraction_homotopy _ _)
    (MM.grading.isHomogeneous_homologyContraction_incl _ _)
    (MM.grading.isHomogeneous_homologyContraction_proj _ _)

/-- The bar map of `minimalModelProjection` is the perturbed projection of the contraction onto
cohomology. -/
@[simp]
theorem barMap_minimalModelProjection :
    MM.minimalModelProjection.barMap =
      (MM.transferContraction
        (MM.grading.homologyContraction MM.isHomogeneous_differential
          MM.differential_comp_self_eq_zero)
        (MM.grading.isHomogeneous_homologyContraction_homotopy _ _)
        (MM.grading.isHomogeneous_homologyContraction_incl _ _)
        (MM.grading.isHomogeneous_homologyContraction_proj _ _)).proj :=
  barMap_transferProjection ..

/-- The linear part of the projection onto the minimal model is the projection of the contraction
onto cohomology. -/
@[simp]
theorem linearPart_minimalModelProjection :
    MM.minimalModelProjection.linearPart =
      (MM.grading.homologyContraction MM.isHomogeneous_differential
        MM.differential_comp_self_eq_zero).proj :=
  linearPart_transferProjection ..

/-- The linear part of the projection onto the minimal model sends each unary cycle to its
cohomology class. -/
theorem linearPart_minimalModelProjection_of_mem_ker {x : M}
    (hx : x ∈ LinearMap.ker MM.differential) :
    MM.minimalModelProjection.linearPart x =
      MM.differential.homologyπ MM.differential_comp_self_eq_zero ⟨x, hx⟩ := by
  rw [linearPart_minimalModelProjection, InternalGrading.homologyContraction_proj_of_mem_ker]

/-- The projection onto the minimal model is a left inverse of its inclusion. -/
@[simp]
theorem minimalModelProjection_comp_minimalModelInclusion :
    MM.minimalModelProjection.comp MM.minimalModelInclusion =
      AInfinityBimoduleHom.id MM.minimalModel :=
  transferProjection_comp_transferInclusion ..

/-- The projection onto the minimal model induces the canonical identification
`MM.isMinimal_minimalModel.cohomologyEquiv` on cohomology. -/
@[simp]
theorem cohomologyMap_minimalModelProjection_apply (y : MM.Cohomology) :
    MM.minimalModelProjection.cohomologyMap y = MM.isMinimal_minimalModel.cohomologyEquiv y := by
  have h := LinearMap.congr_fun (AInfinityBimoduleHom.cohomologyMap_comp
    MM.minimalModelProjection MM.minimalModelInclusion)
    (MM.isMinimal_minimalModel.cohomologyEquiv y)
  simpa only [minimalModelProjection_comp_minimalModelInclusion,
    AInfinityBimoduleHom.cohomologyMap_id, LinearMap.id_apply, LinearMap.comp_apply,
    cohomologyMap_minimalModelInclusion_cohomologyEquiv] using h.symm

/-- As a linear map, the cohomology map of `minimalModelProjection` is
`MM.isMinimal_minimalModel.cohomologyEquiv`. -/
theorem cohomologyMap_minimalModelProjection :
    MM.minimalModelProjection.cohomologyMap =
      MM.isMinimal_minimalModel.cohomologyEquiv.toLinearMap :=
  LinearMap.ext MM.cohomologyMap_minimalModelProjection_apply

/-- The projection onto the minimal model is a quasi-isomorphism of `A∞` bimodules. -/
theorem isQuasiIso_minimalModelProjection : MM.minimalModelProjection.IsQuasiIso :=
  isQuasiIso_transferProjection ..

/-! ### Uniqueness of the minimal model -/

section Uniqueness

variable {N : Type uN} [AddCommGroup N] [Module K N] {NN : AInfinityBimodule AA BB N}

/-- **Uniqueness of the minimal model**, for a quasi-isomorphism into `MM`: if `f` is a
quasi-isomorphism from a minimal bimodule `NN` to `MM`, then `f` followed by the projection onto
`MM.minimalModel` is an isomorphism of `A∞` bimodules. -/
theorem isIso_minimalModelProjection_comp (hN : NN.IsMinimal)
    {f : AInfinityBimoduleHom NN MM} (hf : f.IsQuasiIso) :
    (MM.minimalModelProjection.comp f).IsIso :=
  MM.isIso_transferProjection_comp _ _ _ _ hN hf

/-- **Uniqueness of the minimal model**, for a quasi-isomorphism out of `MM`: if `g` is a
quasi-isomorphism from `MM` to a minimal bimodule `NN`, then the inclusion of `MM.minimalModel`
followed by `g` is an isomorphism of `A∞` bimodules. -/
theorem isIso_comp_minimalModelInclusion (hN : NN.IsMinimal)
    {g : AInfinityBimoduleHom MM NN} (hg : g.IsQuasiIso) :
    (g.comp MM.minimalModelInclusion).IsIso :=
  MM.isIso_comp_transferInclusion _ _ _ _ hN hg

end Uniqueness

end Field

end AInfinityBimodule

end TauCeti
