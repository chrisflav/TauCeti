/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.LineBundle.Degree
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.Modules.Annihilator
public import TauCeti.AlgebraicGeometry.Modules.FiniteType
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension

import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Degree
import TauCeti.AlgebraicGeometry.Cohomology.Affine
import TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Curves.Cohomology
import TauCeti.AlgebraicGeometry.Curves.Degree.Pullback
import TauCeti.AlgebraicGeometry.LineBundle.LocalRing
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic
import TauCeti.AlgebraicGeometry.Modules.SchemeTheoreticSupport
import TauCeti.AlgebraicGeometry.Modules.StructureSheafSequence
import TauCeti.AlgebraicGeometry.Morphisms.Integral.Dimension
import TauCeti.AlgebraicGeometry.Normalization.Dominant
import TauCeti.AlgebraicGeometry.Normalization.Finite
import TauCeti.AlgebraicGeometry.Normalization.Modification
import TauCeti.AlgebraicGeometry.Normalization.Regular
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import TauCeti.AlgebraicGeometry.Scheme.Normal
import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Normalization invariance and pullback of degree on singular integral curves

Let `X` be an integral scheme, proper over a field `k` with fibres of dimension at most one. The
curve `X` may be singular. Its normalization `ν : X^ν ⟶ X` in its function field is a finite
modification onto `X` (`isFinite_fromNormalization_of_isUniversallyJapanese` and
`isModification_fromNormalization_fromSpecStalk_genericPoint`), and in dimension one `X^ν` is a
regular proper curve over `k`.

For any finite modification `f : X' ⟶ X` over `k`, the structure-sheaf sequence
`0 ⟶ 𝒪_X ⟶ f_* 𝒪_{X'} ⟶ Q ⟶ 0` is short exact with a quasi-coherent cokernel `Q` of finite type
whose stalk at the generic point of `X` vanishes. Its scheme-theoretic support `V(Ann Q)` is
locally Artinian and finite over `k`, so `Hⁱ(X, Q) = 0` for `i ≥ 1`, `H⁰(X, Q)` is
finite-dimensional over `k`, and `L ⊗ Q ≅ Q` for every invertible sheaf `L` on `X` because the
Picard group of a discrete scheme is trivial. Tensoring the sequence with `L` and taking the
long exact cohomology sequence yields
`χ₂(f^* L) - χ₂(L) = χ₂(L ⊗ Q) = χ₂(Q) = χ₂(𝒪_{X'}) - χ₂(𝒪_X)`, so `deg_k (f^* L) = deg_k L`.

Applying this to the normalization `ν : X^ν ⟶ X` removes all cohomology-finiteness and regularity
hypotheses from the degree theory of integral proper curves over a field:

* `H⁰(X, L)` and `H¹(X, L)` are finite-dimensional over `k` for every invertible sheaf `L` on `X`;
* `deg_k (ν^* L) = deg_k L`, and more generally `deg_k (f^* L) = deg_k L` for every finite
  modification `f : X' ⟶ X` over `k`;
* `LineBundleClass.eulerDegree k` is additive on `Pic X` without assuming cohomology finiteness;
* for every finite dominant `k`-morphism `g : C' ⟶ C` between integral proper schemes over `k` with
  `RelativeDimensionLE 1 (C ↘ Spec (.of k))`, lifting `g` to the normalizations `g^ν : C'^ν ⟶ C^ν`
  reduces to the regular case and yields `deg_k (g^* a) = [K(C') : K(C)] · deg_k a`.

## Main results

* `TauCeti.AlgebraicGeometry.isLocallyArtinian_subscheme_annihilator`: a torsion quasi-coherent
  module of finite type on an irreducible locally Noetherian scheme of dimension at most one has
  locally Artinian scheme-theoretic support.
* `TauCeti.AlgebraicGeometry.nonempty_tensor_iso_of_subsingleton_stalk_genericPoint`: twisting
  such a torsion module by an invertible sheaf does not change its isomorphism class.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.finiteDimensional_cohomology_of_isProper`:
  `H⁰(X, L)` and `H¹(X, L)` are finite-dimensional for every invertible sheaf `L` on an integral
  proper scheme of relative dimension at most one over a field.
* `TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_pullback_fromNormalization` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_pullback_of_isModification`: the
  Euler-characteristic degree is invariant under pullback along normalization and along any finite
  modification.
* `TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_mul_of_isProper`,
  `TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_inv_of_isProper`,
  `TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegreeHomOfIsProper`,
  `TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_pow_of_isProper` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_zpow_of_isProper`: unconditional
  additivity of `eulerDegree` on integral proper schemes of relative dimension at most one over a
  field.
* `TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_pullback_of_isFinite_isDominant`:
  `deg_k (g^* a) = [K(C') : K(C)] · deg_k a` for any finite dominant morphism `g : C' ⟶ C` of
  integral proper schemes of relative dimension at most one over a field, without regularity or
  cohomology-finiteness hypotheses.

## References

* [The Stacks Project, Section 33.44](https://stacks.math.columbia.edu/tag/0AYQ): degrees on
  proper curves, especially Lemma 33.44.4 (0AYU, pullback along finite morphisms).
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 7.3 and Proposition 7.5.4 (behaviour
  of the Euler characteristic and degree under normalization).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-! ### Torsion finite-type quasi-coherent sheaves -/

section Torsion

variable {X : Scheme.{u}} [IrreducibleSpace X] [IsLocallyNoetherian X]

/-- **Scheme-theoretic support of a torsion module on a curve.** On an irreducible locally
Noetherian scheme `X` of dimension at most one, the closed subscheme cut out by the annihilator
ideal sheaf of a quasi-coherent module of finite type whose stalk at the generic point vanishes is
locally Artinian, hence discrete. -/
theorem isLocallyArtinian_subscheme_annihilator (hX : topologicalKrullDim X ≤ 1)
    (M : X.Modules) [M.IsQuasicoherent]
    (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U))
    [Subsingleton (M.presheaf.stalk (genericPoint X))] :
    IsLocallyArtinian (M.annihilator hM).subscheme := by
  set I := M.annihilator hM
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have hη : genericPoint X ∉ I.support := by
    rw [M.mem_support_annihilator_iff_nontrivial_stalk hM]
    exact not_nontrivial_iff_subsingleton.mpr inferInstance
  have hdim (y : X) : Order.coheight y ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans hX
  -- Every point of `V(Ann M)` maps to a closed point of `X`, so `V(Ann M)` has dimension ≤ 0.
  have hZ : topologicalKrullDim I.subscheme ≤ 0 := by
    rw [TauCeti.topologicalKrullDim_eq_iSup_coheight]
    refine iSup_le fun z ↦ ?_
    have hmax : IsMax z := fun w hw ↦ by
      have hw_ne : I.subschemeι w ≠ genericPoint X := fun h ↦
        hη (h ▸ (Scheme.IdealSheafData.range_subschemeι I).subset ⟨w, rfl⟩)
      have hclosed : IsClosed ({I.subschemeι w} : Set X) :=
        TauCeti.isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hdim
          ((Scheme.coheight_eq_one_iff_ne_genericPoint hX).mpr hw_ne)
      have heq : I.subschemeι z = I.subschemeι w :=
        (hw.map I.subschemeι.continuous).mem_closed hclosed rfl
      exact (I.subschemeι.isClosedEmbedding.injective heq).ge
    rw [Order.coheight_eq_zero.mpr hmax]
    rfl
  exact IsLocallyArtinian.of_topologicalKrullDim_le_zero hZ

/-- **Twisting a torsion module on a curve by a line bundle.** On an irreducible locally Noetherian
scheme `X` of dimension at most one, tensoring a torsion quasi-coherent module `M` of finite type
with any invertible sheaf `L` yields a module isomorphic to `M`. -/
theorem nonempty_tensor_iso_of_subsingleton_stalk_genericPoint
    (hX : topologicalKrullDim X ≤ 1) (L : InvertibleSheaf X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] [Subsingleton (M.presheaf.stalk (genericPoint X))] :
    Nonempty (L.obj ⊗ M ≅ M) := by
  have hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U) := fun U ↦
    (Scheme.Modules.isFiniteType_iff_finite_sections M).mp inferInstance U.1 U.2
  set I := M.annihilator hM
  set ι := I.subschemeι
  have := isLocallyArtinian_subscheme_annihilator hX M hM
  have : IsIso ((pullbackPushforwardAdjunction ι).unit.app M) :=
    isIso_unit_app_of_ker_ideal_le_annihilator ι M fun U ↦
      (Scheme.IdealSheafData.le_def.mp (Scheme.IdealSheafData.ker_subschemeι I).le U).trans_eq
        (M.annihilator_ideal hM U)
  let eM : M ≅ (pushforward ι).obj ((Scheme.Modules.pullback ι).obj M) :=
    asIso ((pullbackPushforwardAdjunction ι).unit.app M)
  -- The support `I.subscheme` is discrete, so `ι^* L` is trivial.
  obtain ⟨eL⟩ := LineBundleClass.mk_eq_one_iff.mp (LineBundleClass.eq_one_of_discreteTopology
    (LineBundleClass.mk ((InvertibleSheaf.pullback ι).obj L)))
  let E := (InvertibleSheaf.toFiniteLocallyFree X).obj L
  have hEL : ((FiniteLocallyFreeSheaf.pullback ι).obj E).obj =
      ((InvertibleSheaf.pullback ι).obj L).obj :=
    (FiniteLocallyFreeSheaf.pullback_obj_obj ι E).trans (InvertibleSheaf.pullback_obj_obj ι L).symm
  refine ⟨tensorIso (Iso.refl L.obj) eM ≪≫
    (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso ι E).app ((Scheme.Modules.pullback ι).obj M) ≪≫
    (pushforward ι).mapIso
      (tensorIso (eqToIso hEL ≪≫ eL) (Iso.refl _) ≪≫ λ_ _) ≪≫ eM.symm⟩

/-- A locally Artinian quasi-compact scheme locally of finite type over a field is finite over the
field. -/
private lemma isFinite_of_isLocallyArtinian {k : Type u} [Field k] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsLocallyArtinian Z] :
    IsFinite f := by
  have : LocallyQuasiFinite f :=
    locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr fun _ ↦
      IsDiscrete.univ.mono (Set.subset_univ _)
  have : IsLocallyArtinian (Spec (.of k)) := Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  exact IsFinite.of_locallyQuasiFinite f

/-- A quasi-coherent module of finite type on a scheme finite over a field has finite-dimensional
`H⁰`. -/
private lemma finiteDimensional_cohomology_zero_of_isFinite {k : Type u} [Field k]
    {Z : Scheme.{u}} [Z.Over (Spec (.of k))] [IsFinite (Z ↘ Spec (.of k))]
    (G : Z.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    FiniteDimensional k (Cohomology G 0) := by
  have : IsAffine Z := isAffine_of_isAffineHom (Z ↘ Spec (.of k))
  have hG : Module.Finite Γ(Z, ⊤) Γ(G, ⊤) :=
    (Scheme.Modules.isFiniteType_iff_finite_sections G).mp inferInstance ⊤ (isAffineOpen_top Z)
  let _ : Algebra k Γ(Z, ⊤) := (baseRingToGlobalSections k Z).toAlgebra
  have : IsScalarTower k Γ(Z, ⊤) Γ(G, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ by
      rw [RingHom.algebraMap_toAlgebra]
      exact (base_smul_globalSections k Z G r s).symm
  have hbase : Module.Finite k Γ(Z, ⊤) :=
    (Z ↘ Spec (.of k)).moduleFinite_appTop
      (RingHom.ext fun r ↦ baseRingToGlobalSections_apply k Z r)
  have : FiniteDimensional k Γ(G, ⊤) := Module.Finite.trans Γ(Z, ⊤) Γ(G, ⊤)
  exact Module.Finite.equiv (cohomologyZeroBaseLinearEquiv k Z G).symm

section TorsionCohomology

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [RelativeDimensionLE 1 (X ↘ Spec (.of k))]

/-- On an integral proper scheme of relative dimension at most one over a field, a torsion
quasi-coherent module of finite type has no positive cohomology and finite-dimensional `H⁰`. -/
private lemma subsingleton_and_finiteDimensional_cohomology_of_subsingleton_stalk_genericPoint
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    [Subsingleton (M.presheaf.stalk (genericPoint X))] :
    (∀ n, Subsingleton (Cohomology M (n + 1))) ∧ FiniteDimensional k (Cohomology M 0) := by
  have hX : topologicalKrullDim X ≤ 1 :=
    (relativeDimensionLE_iff_of_field (X ↘ Spec (.of k))).mp inferInstance
  have hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U) := fun U ↦
    (Scheme.Modules.isFiniteType_iff_finite_sections M).mp inferInstance U.1 U.2
  set I := M.annihilator hM
  set ι := I.subschemeι
  have := isLocallyArtinian_subscheme_annihilator hX M hM
  let _ : I.subscheme.Over (Spec (.of k)) := ⟨ι ≫ X ↘ Spec (.of k)⟩
  have : ι.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsProper (I.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper (ι ≫ X ↘ Spec (.of k)))
  have : IsFinite (I.subscheme ↘ Spec (.of k)) :=
    isFinite_of_isLocallyArtinian (I.subscheme ↘ Spec (.of k))
  have : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subscheme ↘ Spec (.of k))
  have : IsIso ((pullbackPushforwardAdjunction ι).unit.app M) :=
    isIso_unit_app_of_ker_ideal_le_annihilator ι M fun U ↦
      (Scheme.IdealSheafData.le_def.mp (Scheme.IdealSheafData.ker_subschemeι I).le U).trans_eq
        (M.annihilator_ideal hM U)
  let G := (Scheme.Modules.pullback ι).obj M
  let eM : M ≅ (pushforward ι).obj G := asIso ((pullbackPushforwardAdjunction ι).unit.app M)
  refine ⟨fun n ↦ ?_, ?_⟩
  · have := subsingleton_cohomology_succ_of_isAffine G n
    exact ((cohomologyBaseLinearEquivOfIso k eM (n + 1)).trans
      (ι.cohomologyPushforwardBaseLinearEquiv k G (n + 1))).toEquiv.subsingleton
  · have : FiniteDimensional k (Cohomology G 0) :=
      finiteDimensional_cohomology_zero_of_isFinite G
    exact Module.Finite.equiv ((cohomologyBaseLinearEquivOfIso k eM 0).trans
      (ι.cohomologyPushforwardBaseLinearEquiv k G 0)).symm

end TorsionCohomology

end Torsion

/-! ### Finite modifications -/

section Modification

variable {X X' : Scheme.{u}} (f : X' ⟶ X)

/-- A modification is dominant: its image contains a dense open of the target. -/
private lemma isDominant_of_isModification [IsModification f] : IsDominant f := by
  obtain ⟨U, hU, -, hfU⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
  refine ⟨hU.mono fun y hy ↦ ?_⟩
  obtain ⟨x, hx⟩ := (f ∣_ U).surjective ⟨y, hy⟩
  refine ⟨x.1, ?_⟩
  have h := congrArg (U.ι ·) hx
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply] at h
  exact h

/-- A morphism `f : X' ⟶ X` is an isomorphism on sections over every open inside an open `U`
over which `f ∣_ U` is an isomorphism. -/
private lemma isIso_app_of_isIso_morphismRestrict {U : X.Opens} [IsIso (f ∣_ U)]
    {V : X.Opens} (hVU : V ≤ U) : IsIso (f.app V) := by
  let W : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have hUW : U.ι ''ᵁ W = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  have hpre : (f ⁻¹ᵁ U).ι ''ᵁ (f ∣_ U) ⁻¹ᵁ W = f ⁻¹ᵁ (U.ι ''ᵁ W) :=
    image_morphismRestrict_preimage f U W
  have happ : (f ∣_ U).app W = f.app (U.ι ''ᵁ W) ≫ X'.presheaf.map (eqToHom hpre).op := by
    rw [morphismRestrict_app' f U W, Scheme.Hom.appLE]
    congr 2
  have hIsoW : IsIso (f.app (U.ι ''ᵁ W)) := by
    have : IsIso (f.app (U.ι ''ᵁ W) ≫ X'.presheaf.map (eqToHom hpre).op) :=
      happ ▸ (inferInstance : IsIso ((f ∣_ U).app W))
    exact IsIso.of_isIso_comp_right (f.app (U.ι ''ᵁ W)) (X'.presheaf.map (eqToHom hpre).op)
  rw [← hUW]
  exact hIsoW

/-- The structure-sheaf map `𝒪_X ⟶ f_* 𝒪_{X'}` as a morphism in `X.Modules`. -/
private abbrev unitToPushforwardUnit :
    (𝟙_ X.Modules) ⟶ (pushforward f).obj (𝟙_ X'.Modules) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- For a finite morphism `f : X' ⟶ X` to a locally Noetherian target, the cokernel of
`𝒪_X ⟶ f_* 𝒪_{X'}` is of finite type. -/
private lemma isFiniteType_cokernel_unitToPushforwardUnit [IsLocallyNoetherian X] [IsFinite f] :
    (cokernel (unitToPushforwardUnit f)).IsFiniteType := by
  have : (𝟙_ X'.Modules).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_structureSheaf X'
  have : (𝟙_ X'.Modules).IsFiniteType :=
    let E := (InvertibleSheaf.toFiniteLocallyFree X').obj
      ⟨𝟙_ X'.Modules, SheafOfModules.isInvertible_tensorUnit X'⟩
    inferInstanceAs E.obj.IsFiniteType
  have : ((pushforward f).obj (𝟙_ X'.Modules)).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite f (𝟙_ X'.Modules)
  have : ((pushforward f).obj (𝟙_ X'.Modules)).IsFiniteType :=
    isFiniteType_of_isFinitePresentation _
  exact isFiniteType_of_epi (cokernel.π (unitToPushforwardUnit f))

/-- The cokernel of `𝒪_X ⟶ f_* 𝒪_{X'}` for a modification `f : X' ⟶ X` of an integral scheme has
trivial stalk at the generic point of `X`. -/
private lemma subsingleton_stalk_cokernel_unitToPushforwardUnit [IsIntegral X]
    [IsModification f] :
    Subsingleton ((cokernel (unitToPushforwardUnit f)).presheaf.stalk (genericPoint X)) := by
  set α := unitToPushforwardUnit f
  set Q := cokernel α
  obtain ⟨U, hU, -, hfU⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
  obtain ⟨u, hu⟩ := hU.nonempty
  have hηU : genericPoint X ∈ U := (genericPoint_specializes u).mem_open U.isOpen hu
  -- Over `U`, `α` is an isomorphism, so `Q|_U` is zero.
  have : IsIso ((restrictFunctor U.ι).map α) := by
    refine isIso_restrictFunctor_map_of_isIso_app α U fun V hVU ↦ ?_
    have : IsIso (f.app V) := isIso_app_of_isIso_morphismRestrict f hVU
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso (f.app V)
  have : Limits.PreservesColimitsOfSize.{u, u} (restrictFunctor U.ι) :=
    (restrictAdjunction U.ι).leftAdjoint_preservesColimits
  have hzeroCok : IsZero (cokernel ((restrictFunctor U.ι).map α)) := by
    rw [IsZero.iff_id_eq_zero]
    have hπ : cokernel.π ((restrictFunctor U.ι).map α) = 0 := by
      rw [← Category.id_comp (cokernel.π _), ← IsIso.inv_hom_id ((restrictFunctor U.ι).map α),
        Category.assoc, cokernel.condition, comp_zero]
    rw [← cancel_epi (cokernel.π ((restrictFunctor U.ι).map α)), hπ, zero_comp, zero_comp]
  have hzero : IsZero (Q.restrict U.ι) :=
    hzeroCok.of_iso (PreservesCokernel.iso (restrictFunctor U.ι) α)
  -- Every germ of `Q` at `genericPoint X` restricts to zero on a smaller open inside `U`.
  refine ⟨fun a b ↦ ?_⟩
  suffices ∀ s : Q.presheaf.stalk (genericPoint X), s = 0 by rw [this a, this b]
  intro s
  obtain ⟨V, hηV, t, rfl⟩ := Q.presheaf.exists_germ_eq s
  let W : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have hUW : U.ι ''ᵁ W = U ⊓ V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hηW : genericPoint X ∈ U.ι ''ᵁ W := hUW.symm ▸ ⟨hηU, hηV⟩
  have hle : U.ι ''ᵁ W ≤ V := hUW.le.trans inf_le_right
  have ht0 : Q.presheaf.map (homOfLE hle).op t = 0 := by
    have h₀ : (Q.restrictAppIso U.ι W).inv (Q.presheaf.map (homOfLE hle).op t) = 0 := by
      simpa using ConcreteCategory.congr_hom
        congr(Hom.app $(hzero.eq_of_src (𝟙 _) 0) W)
        ((Q.restrictAppIso U.ι W).inv (Q.presheaf.map (homOfLE hle).op t))
    rw [← Iso.inv_hom_id_apply (Q.restrictAppIso U.ι W) (Q.presheaf.map (homOfLE hle).op t),
      h₀, map_zero]
  rw [← Q.presheaf.germ_res_apply (homOfLE hle) (genericPoint X) hηW t, ht0, map_zero]

/-- On a separated compact scheme over a field, pushforward along an affine morphism preserves
cohomology as `k`-vector spaces in every degree. -/
private def cohomologyPushforwardBaseLinearEquivOfIsProper {k : Type u} [Field k]
    [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))] [f.IsOver (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsAffineHom f] (M : X'.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Cohomology ((pushforward f).obj M) n ≃ₗ[k] Cohomology M n :=
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from (X ↘ Spec (.of k))]
    infer_instance
  let 𝒰 := X.affineCover.finiteSubcover
  f.cohomologyPushforwardBaseLinearEquivOfIsAffineHom (fun i ↦ (𝒰.f i).opensRange)
    (fun i ↦ isAffineOpen_opensRange (𝒰.f i)) 𝒰.iSup_opensRange k M n

/-- Pushforward along an affine morphism to a proper scheme over `k` preserves truncated Euler
characteristics of quasi-coherent sheaves. -/
private lemma eulerCharBelow_pushforward_of_isProper {k : Type u} [Field k]
    [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))] [f.IsOver (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsAffineHom f] (M : X'.Modules) [M.IsQuasicoherent] (n : ℕ) :
    eulerCharBelow k X ((pushforward f).obj M) n = eulerCharBelow k X' M n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eulerCharBelow_succ, eulerCharBelow_succ, ih,
      (cohomologyPushforwardBaseLinearEquivOfIsProper f M n).finrank_eq]

/-- Projection-formula identification of `L ⊗ f_* 𝒪_{X'}` with `f_* (f^* L)`. -/
private def tensorPushforwardUnitIsoOfInvertible (L : InvertibleSheaf X) :
    L.obj ⊗ (pushforward f).obj (𝟙_ X'.Modules) ≅
      (pushforward f).obj ((InvertibleSheaf.pullback f).obj L).obj :=
  let E := (InvertibleSheaf.toFiniteLocallyFree X).obj L
  FiniteLocallyFreeSheaf.tensorPushforwardUnitIso f E ≪≫
    (pushforward f).mapIso (eqToIso ((FiniteLocallyFreeSheaf.pullback_obj_obj f E).trans
      (InvertibleSheaf.pullback_obj_obj f L).symm))

/-- For a finite modification `f : X' ⟶ X` of an integral proper scheme of relative dimension at
most one over `k`, the structure-sheaf map `𝒪_X ⟶ f_* 𝒪_{X'}` is mono and its cokernel `Q` is
invariant under twisting by any invertible sheaf, has vanishing higher cohomology, and has
finite-dimensional `H⁰`. -/
private lemma modification_cokernel_properties {k : Type u} [Field k]
    [X.Over (Spec (.of k))]
    [IsIntegral X] [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]
    [IsFinite f] [IsModification f] :
    Mono (unitToPushforwardUnit f) ∧
      (∀ L : InvertibleSheaf X,
        Nonempty (L.obj ⊗ cokernel (unitToPushforwardUnit f) ≅
          cokernel (unitToPushforwardUnit f))) ∧
      (∀ n, Subsingleton (Cohomology (cokernel (unitToPushforwardUnit f)) (n + 1))) ∧
      FiniteDimensional k (Cohomology (cokernel (unitToPushforwardUnit f)) 0) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have hX : topologicalKrullDim X ≤ 1 :=
    (relativeDimensionLE_iff_of_field (X ↘ Spec (.of k))).mp inferInstance
  have : IsDominant f := isDominant_of_isModification f
  have : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have hmono : Mono (unitToPushforwardUnit f) := f.mono_unitToPushforwardObjUnit
  have : (cokernel (unitToPushforwardUnit f)).IsQuasicoherent :=
    f.isQuasicoherent_cokernel_unitToPushforwardObjUnit
  have : (cokernel (unitToPushforwardUnit f)).IsFiniteType :=
    isFiniteType_cokernel_unitToPushforwardUnit f
  have : Subsingleton ((cokernel (unitToPushforwardUnit f)).presheaf.stalk (genericPoint X)) :=
    subsingleton_stalk_cokernel_unitToPushforwardUnit f
  have ⟨hQsub, hQfd⟩ :=
    subsingleton_and_finiteDimensional_cohomology_of_subsingleton_stalk_genericPoint k
      (cokernel (unitToPushforwardUnit f))
  exact ⟨hmono, fun L ↦ nonempty_tensor_iso_of_subsingleton_stalk_genericPoint hX L _, hQsub, hQfd⟩

/-- For a finite modification `f : X' ⟶ X` over `k` of an integral proper scheme of relative
dimension at most one, twisting the structure-sheaf sequence by `L` relates `χ₂(f^* L)` and
`χ₂(L)` by the same constant `χ₂(Q)`. -/
private lemma finiteDimensional_and_eulerCharBelow_diff_of_isModification {k : Type u} [Field k]
    [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))] [f.IsOver (Spec (.of k))]
    [IsIntegral X] [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]
    [IsFinite f] [IsModification f] (L : InvertibleSheaf X)
    (hfin' : ∀ i < 2, FiniteDimensional k (Cohomology ((InvertibleSheaf.pullback f).obj L).obj i)) :
    (∀ i < 2, FiniteDimensional k (Cohomology L.obj i)) ∧
      eulerCharBelow k X' ((InvertibleSheaf.pullback f).obj L).obj 2 -
        eulerCharBelow k X L.obj 2 =
          eulerCharBelow k X (cokernel (unitToPushforwardUnit f)) 2 := by
  have ⟨_, htensor, hQsub, hQfd⟩ := modification_cokernel_properties (k := k) f
  set α := unitToPushforwardUnit f
  set Q := cokernel α
  let E := (InvertibleSheaf.toFiniteLocallyFree X).obj L
  have : L.obj.IsLocallyFree := inferInstanceAs E.obj.IsLocallyFree
  have : L.obj.IsFiniteType := inferInstanceAs E.obj.IsFiniteType
  have hSL := shortExact_map_tensorLeft L.obj (TauCeti.cokernelSequence_shortExact α)
  set SL := (ShortComplex.cokernelSequence α).map (tensorLeft L.obj)
  let e₁ : SL.X₁ ≅ L.obj := ρ_ L.obj
  let e₂ : SL.X₂ ≅ (pushforward f).obj ((InvertibleSheaf.pullback f).obj L).obj :=
    tensorPushforwardUnitIsoOfInvertible f L
  obtain ⟨e₃⟩ := htensor L
  have hSL₃_sub : Subsingleton (Cohomology SL.X₃ 1) :=
    (cohomologyBaseLinearEquivOfIso k e₃ 1).toEquiv.subsingleton
  have hSL₃_fd : FiniteDimensional k (Cohomology SL.X₃ 0) :=
    Module.Finite.equiv (cohomologyBaseLinearEquivOfIso k e₃ 0).symm
  have hSL₂_fd (i : ℕ) (hi : i < 2) : FiniteDimensional k (Cohomology SL.X₂ i) := by
    have := hfin' i hi
    exact Module.Finite.equiv ((cohomologyBaseLinearEquivOfIso k e₂ i).trans
      (cohomologyPushforwardBaseLinearEquivOfIsProper f _ i)).symm
  have hSL₁_fd0 : FiniteDimensional k (Cohomology SL.X₁ 0) := by
    have := hSL₂_fd 0 (by omega)
    have : Mono SL.f := hSL.mono_f
    exact finiteDimensional_cohomology_zero_of_mono k X SL.f
  have hSL₁_fd1 : FiniteDimensional k (Cohomology SL.X₁ 1) := by
    have := hSL₂_fd 1 (by omega)
    exact finiteDimensional_cohomology_X₁ k X hSL 0 1 rfl
  have hL_fd (i : ℕ) (hi : i < 2) : FiniteDimensional k (Cohomology L.obj i) := by
    refine (finiteDimensional_cohomology_congr k e₁ i).mp ?_
    interval_cases i <;> assumption
  have hδ : cohomologyδBaseLinear k X hSL 1 2 rfl = 0 :=
    LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  have hadd := eulerCharBelow_eq_add_of_cohomologyδ_eq_zero k hSL 1
    (fun i hi h0 ↦ (by omega : i = 1) ▸ hSL₁_fd1) hSL₂_fd hδ
  refine ⟨hL_fd, ?_⟩
  have h1 : eulerCharBelow k X SL.X₁ 2 = eulerCharBelow k X L.obj 2 :=
    eulerCharBelow_congr k e₁ 2
  have h2 : eulerCharBelow k X SL.X₂ 2 =
      eulerCharBelow k X' ((InvertibleSheaf.pullback f).obj L).obj 2 :=
    (eulerCharBelow_congr k e₂ 2).trans (eulerCharBelow_pushforward_of_isProper f _ 2)
  have h3 : eulerCharBelow k X SL.X₃ 2 = eulerCharBelow k X Q 2 :=
    eulerCharBelow_congr k e₃ 2
  linarith

end Modification

/-! ### Unconditional cohomology finiteness and normalization invariance -/

section ProperIntegralCurve

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]

omit [IsIntegral X] [RelativeDimensionLE 1 (X ↘ Spec (.of k))] in
/-- On a proper scheme of dimension zero over a field, `H⁰` and `H¹` of every invertible sheaf are
finite-dimensional. -/
private lemma finiteDimensional_cohomology_of_topologicalKrullDim_eq_zero
    (h0 : topologicalKrullDim X = 0) (L : InvertibleSheaf X) {i : ℕ} (hi : i < 2) :
    FiniteDimensional k (Cohomology L.obj i) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero h0.le
  have : IsFinite (X ↘ Spec (.of k)) :=
    isFinite_of_isLocallyArtinian (X ↘ Spec (.of k))
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of k))
  interval_cases i
  · let E := (InvertibleSheaf.toFiniteLocallyFree X).obj L
    have : L.obj.IsFiniteType := inferInstanceAs E.obj.IsFiniteType
    exact finiteDimensional_cohomology_zero_of_isFinite L.obj
  · have := subsingleton_cohomology_succ_of_isAffine L.obj 0
    infer_instance

omit [IsProper (X ↘ Spec (.of k))] in
include k in
/-- On an integral scheme over `k` of relative dimension at most one, the Krull dimension is either
`0` or `1`. -/
private lemma topologicalKrullDim_eq_zero_or_one :
    topologicalKrullDim X = 0 ∨ topologicalKrullDim X = 1 := by
  have hle : topologicalKrullDim X ≤ 1 :=
    (relativeDimensionLE_iff_of_field (X ↘ Spec (.of k))).mp inferInstance
  have hge : (0 : WithBot ℕ∞) ≤ topologicalKrullDim X :=
    le_trans (by exact_mod_cast zero_le)
      (TauCeti.coheight_le_topologicalKrullDim (genericPoint X))
  cases hd : topologicalKrullDim X with
  | bot =>
    rw [hd] at hge
    exact absurd hge (by decide)
  | coe n =>
    rw [hd] at hle
    rcases le_iff_eq_or_lt.mp (WithBot.coe_le_coe.mp hle) with rfl | hlt
    · exact Or.inr rfl
    · exact Or.inl (congrArg WithBot.some (Order.lt_one_iff.mp hlt))

omit [RelativeDimensionLE 1 (X ↘ Spec (.of k))] in
/-- The normalization of a one-dimensional integral proper scheme over a field is a regular proper
curve over that field. -/
private lemma isCurveOver_normalization (h1 : topologicalKrullDim X = 1) :
    letI : (X.fromSpecStalk (genericPoint X)).normalization.Over (Spec (.of k)) :=
      ⟨(X.fromSpecStalk (genericPoint X)).fromNormalization ≫ X ↘ Spec (.of k)⟩
    (X.fromSpecStalk (genericPoint X)).normalization.IsCurveOver k ∧
      ∀ y : CodimensionOnePoint (X.fromSpecStalk (genericPoint X)).normalization,
        IsDiscreteValuationRing
          ((X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk (y : _)) := by
  set ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let _ : (X.fromSpecStalk (genericPoint X)).normalization.Over (Spec (.of k)) :=
    ⟨ν ≫ X ↘ Spec (.of k)⟩
  have : IsFinite ν := isFinite_fromNormalization_of_isUniversallyJapanese k
  have : IsProper ((X.fromSpecStalk (genericPoint X)).normalization ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper (ν ≫ X ↘ Spec (.of k)))
  have hdim : topologicalKrullDim (X.fromSpecStalk (genericPoint X)).normalization = 1 :=
    (Scheme.Hom.topologicalKrullDim_normalization (X.fromSpecStalk (genericPoint X))).trans h1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsRegular (X.fromSpecStalk (genericPoint X)).normalization :=
    isRegular_normalization_fromSpecStalk_genericPoint h1.le
  exact ⟨(Scheme.isCurveOver_iff (k := k)).mpr ⟨inferInstance, inferInstance, hdim⟩,
    fun y ↦ IsNormalScheme.isDiscreteValuationRing_stalk y.1 y.2⟩

/-- **Cohomology finiteness on singular integral proper curves.** Let `X` be an integral scheme,
proper over a field `k` with fibres of dimension at most one. Then `H⁰(X, L)` and `H¹(X, L)` are
finite-dimensional over `k` for every invertible sheaf `L` on `X`. -/
theorem InvertibleSheaf.finiteDimensional_cohomology_of_isProper (L : InvertibleSheaf X)
    {i : ℕ} (hi : i < 2) : FiniteDimensional k (Cohomology L.obj i) := by
  rcases topologicalKrullDim_eq_zero_or_one k (X := X) with h0 | h1
  · exact finiteDimensional_cohomology_of_topologicalKrullDim_eq_zero k h0 L hi
  · set ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let _ : (X.fromSpecStalk (genericPoint X)).normalization.Over (Spec (.of k)) :=
      ⟨ν ≫ X ↘ Spec (.of k)⟩
    have : ν.IsOver (Spec (.of k)) := ⟨rfl⟩
    have : IsFinite ν := isFinite_fromNormalization_of_isUniversallyJapanese k
    have ⟨hcurve, hdvr⟩ := isCurveOver_normalization k h1
    have hfin' (j : ℕ) (_ : j < 2) :
        FiniteDimensional k (Cohomology ((InvertibleSheaf.pullback ν).obj L).obj j) :=
      let E := (InvertibleSheaf.toFiniteLocallyFree _).obj ((InvertibleSheaf.pullback ν).obj L)
      have : ((InvertibleSheaf.pullback ν).obj L).obj.IsFiniteType :=
        inferInstanceAs E.obj.IsFiniteType
      finiteDimensional_cohomology_of_isCurveOver k _ j
    exact (finiteDimensional_and_eulerCharBelow_diff_of_isModification ν L hfin').1 i hi

/-- **Degree invariance under a finite modification.** Let `X` be an integral scheme, proper over a
field `k` with fibres of dimension at most one, and let `f : X' ⟶ X` be a finite modification over
`k`. Then `deg_k (f^* L) = deg_k L` for every invertible sheaf `L` on `X`. -/
theorem InvertibleSheaf.eulerDegree_pullback_of_isModification {X' : Scheme.{u}}
    [X'.Over (Spec (.of k))] (f : X' ⟶ X) [f.IsOver (Spec (.of k))]
    [IsFinite f] [IsModification f] (L : InvertibleSheaf X) :
    ((InvertibleSheaf.pullback f).obj L).eulerDegree k = L.eulerDegree k := by
  have ⟨_, htensor, hQsub, hQfd⟩ := modification_cokernel_properties (k := k) f
  -- The exact sequence `0 ⟶ M ⟶ f_* f^* M ⟶ M ⊗ Q ⟶ 0` gives finite-dim `H⁰, H¹` on `X'`.
  have hfin' (M : InvertibleSheaf X) (i : ℕ) (hi : i < 2) :
      FiniteDimensional k (Cohomology ((InvertibleSheaf.pullback f).obj M).obj i) := by
    let E := (InvertibleSheaf.toFiniteLocallyFree X).obj M
    have : M.obj.IsLocallyFree := inferInstanceAs E.obj.IsLocallyFree
    have : M.obj.IsFiniteType := inferInstanceAs E.obj.IsFiniteType
    have hSM := shortExact_map_tensorLeft M.obj
      (TauCeti.cokernelSequence_shortExact (unitToPushforwardUnit f))
    set SM := (ShortComplex.cokernelSequence (unitToPushforwardUnit f)).map (tensorLeft M.obj)
    obtain ⟨e₃⟩ := htensor M
    have : FiniteDimensional k (Cohomology SM.X₁ i) :=
      (finiteDimensional_cohomology_congr k (ρ_ M.obj) i).mpr
        (M.finiteDimensional_cohomology_of_isProper k hi)
    have : FiniteDimensional k (Cohomology SM.X₃ i) :=
      (finiteDimensional_cohomology_congr k e₃ i).mpr (by
        interval_cases i
        · exact hQfd
        · have := hQsub 0; infer_instance)
    have : FiniteDimensional k (Cohomology (M.obj ⊗ (pushforward f).obj (𝟙_ X'.Modules)) i) :=
      finiteDimensional_cohomology_X₂ k X hSM i
    exact Module.Finite.equiv ((cohomologyBaseLinearEquivOfIso k
      (tensorPushforwardUnitIsoOfInvertible f M) i).trans
      (cohomologyPushforwardBaseLinearEquivOfIsProper f _ i))
  -- Apply the Euler-characteristic comparison to both `L` and `𝒪_X` and subtract.
  have hL := (finiteDimensional_and_eulerCharBelow_diff_of_isModification f L (hfin' L)).2
  have hO := (finiteDimensional_and_eulerCharBelow_diff_of_isModification f
    (InvertibleSheaf.trivial X) (hfin' (InvertibleSheaf.trivial X))).2
  have heO : ((InvertibleSheaf.pullback f).obj (InvertibleSheaf.trivial X)).obj ≅
      (InvertibleSheaf.trivial X').obj :=
    (Scheme.Modules.pullback f).mapIso
      (eqToIso (InvertibleSheaf.trivial_obj X) ≪≫ TauCeti.SheafOfModules.freePUnitIsoUnit _) ≪≫
      Scheme.Modules.pullbackObjUnitIso f ≪≫
      (TauCeti.SheafOfModules.freePUnitIsoUnit _).symm ≪≫
      eqToIso (InvertibleSheaf.trivial_obj X').symm
  have hO' : eulerCharBelow k X'
        ((InvertibleSheaf.pullback f).obj (InvertibleSheaf.trivial X)).obj 2 =
      eulerCharBelow k X' (InvertibleSheaf.trivial X').obj 2 :=
    eulerCharBelow_congr k heO 2
  rw [InvertibleSheaf.eulerDegree_def, InvertibleSheaf.eulerDegree_def]
  linarith

/-- **Degree invariance under a finite modification on `Pic X`.** Let `X` be an integral scheme,
proper over a field `k` with fibres of dimension at most one, and let `f : X' ⟶ X` be a finite
modification over `k`. Then `deg_k (f^* a) = deg_k a` for every line-bundle class `a` on `X`. -/
theorem LineBundleClass.eulerDegree_pullback_of_isModification {X' : Scheme.{u}}
    [X'.Over (Spec (.of k))] (f : X' ⟶ X) [f.IsOver (Spec (.of k))]
    [IsFinite f] [IsModification f] (a : LineBundleClass X) :
    eulerDegree k (pullback f a) = eulerDegree k a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk, eulerDegree_mk, eulerDegree_mk]
  exact L.eulerDegree_pullback_of_isModification k f

/-- **Degree invariance under normalization.** Pulling back an invertible sheaf along the
normalization `ν : X^ν ⟶ X` of an integral proper scheme of relative dimension at most one over a
field `k` preserves its Euler-characteristic degree. -/
theorem InvertibleSheaf.eulerDegree_pullback_fromNormalization (L : InvertibleSheaf X) :
    letI : (X.fromSpecStalk (genericPoint X)).normalization.Over (Spec (.of k)) :=
      ⟨(X.fromSpecStalk (genericPoint X)).fromNormalization ≫ X ↘ Spec (.of k)⟩
    ((InvertibleSheaf.pullback
      (X.fromSpecStalk (genericPoint X)).fromNormalization).obj L).eulerDegree k =
        L.eulerDegree k := by
  set ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let _ : (X.fromSpecStalk (genericPoint X)).normalization.Over (Spec (.of k)) :=
    ⟨ν ≫ X ↘ Spec (.of k)⟩
  have : ν.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsFinite ν := isFinite_fromNormalization_of_isUniversallyJapanese k
  exact L.eulerDegree_pullback_of_isModification k ν

/-- **Degree invariance under normalization on `Pic X`.** Pulling back a line-bundle class along
the normalization `ν : X^ν ⟶ X` of an integral proper scheme of relative dimension at most one over
a field `k` preserves its Euler-characteristic degree. -/
theorem LineBundleClass.eulerDegree_pullback_fromNormalization (a : LineBundleClass X) :
    letI : (X.fromSpecStalk (genericPoint X)).normalization.Over (Spec (.of k)) :=
      ⟨(X.fromSpecStalk (genericPoint X)).fromNormalization ≫ X ↘ Spec (.of k)⟩
    eulerDegree k (pullback (X.fromSpecStalk (genericPoint X)).fromNormalization a) =
      eulerDegree k a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  let _ : (X.fromSpecStalk (genericPoint X)).normalization.Over (Spec (.of k)) :=
    ⟨(X.fromSpecStalk (genericPoint X)).fromNormalization ≫ X ↘ Spec (.of k)⟩
  rw [pullback_mk, eulerDegree_mk, eulerDegree_mk]
  exact L.eulerDegree_pullback_fromNormalization k

/-! ### Unconditional additivity and pullback formula -/

namespace LineBundleClass

/-- **Additivity of degree on integral proper curves.** On an integral scheme proper over a field
`k` with fibres of dimension at most one (possibly singular), the Euler-characteristic degree is
additive on line-bundle classes. -/
@[simp]
theorem eulerDegree_mul_of_isProper (a b : LineBundleClass X) :
    eulerDegree k (a * b) = eulerDegree k a + eulerDegree k b := by
  have := (InvertibleSheaf.trivial X).finiteDimensional_cohomology_of_isProper k (i := 0) (by omega)
  have := (InvertibleSheaf.trivial X).finiteDimensional_cohomology_of_isProper k (i := 1) (by omega)
  exact eulerDegree_mul_of_isIntegral k a b

/-- The inverse class has the opposite Euler-characteristic degree on an integral scheme proper
over `k` with fibres of dimension at most one. -/
@[simp]
theorem eulerDegree_inv_of_isProper (a : LineBundleClass X) :
    eulerDegree k a⁻¹ = -eulerDegree k a := by
  have := (InvertibleSheaf.trivial X).finiteDimensional_cohomology_of_isProper k (i := 0) (by omega)
  have := (InvertibleSheaf.trivial X).finiteDimensional_cohomology_of_isProper k (i := 1) (by omega)
  exact eulerDegree_inv_of_isIntegral k a

variable (X) in
/-- The Euler-characteristic degree as a group homomorphism `Additive (LineBundleClass X) →+ ℤ` on
an arbitrary integral proper scheme of relative dimension at most one over a field `k`. -/
def eulerDegreeHomOfIsProper : Additive (LineBundleClass X) →+ ℤ :=
  AddMonoidHom.mk' (fun a ↦ eulerDegree k a.toMul) fun a b ↦
    eulerDegree_mul_of_isProper k a.toMul b.toMul

/-- `eulerDegreeHomOfIsProper` evaluates to `LineBundleClass.eulerDegree`. -/
@[simp]
lemma eulerDegreeHomOfIsProper_apply (a : Additive (LineBundleClass X)) :
    eulerDegreeHomOfIsProper k X a = eulerDegree k a.toMul :=
  (rfl)

/-- The Euler-characteristic degree of a natural tensor power on an integral proper scheme of
relative dimension at most one over `k`. -/
@[simp]
theorem eulerDegree_pow_of_isProper (a : LineBundleClass X) (n : ℕ) :
    eulerDegree k (a ^ n) = n * eulerDegree k a := by
  simpa using (eulerDegreeHomOfIsProper k X).map_nsmul n (Additive.ofMul a)

/-- The Euler-characteristic degree of an integer tensor power on an integral proper scheme of
relative dimension at most one over `k`. -/
@[simp]
theorem eulerDegree_zpow_of_isProper (a : LineBundleClass X) (n : ℤ) :
    eulerDegree k (a ^ n) = n * eulerDegree k a := by
  simpa using (eulerDegreeHomOfIsProper k X).map_zsmul n (Additive.ofMul a)

end LineBundleClass

end ProperIntegralCurve

namespace LineBundleClass

variable (k : Type u) [Field k]

/-- The one-dimensional case of `eulerDegree_pullback_of_isFinite_isDominant`, proved by lifting
`g` to the normalizations and applying `eulerDegree_pullback_of_isDominant` to the regular target
`C^ν`. -/
private theorem eulerDegree_pullback_of_isFinite_isDominant_dim_one {C C' : Scheme.{u}}
    [C.Over (Spec (.of k))] [C'.Over (Spec (.of k))]
    (g : C' ⟶ C) [g.IsOver (Spec (.of k))] [IsFinite g]
    [IsIntegral C] [IsIntegral C'] [IsDominant g]
    [IsProper (C ↘ Spec (.of k))] [IsProper (C' ↘ Spec (.of k))]
    [RelativeDimensionLE 1 (C ↘ Spec (.of k))] [RelativeDimensionLE 1 (C' ↘ Spec (.of k))]
    (h1 : topologicalKrullDim C = 1) (h1' : topologicalKrullDim C' = 1) (a : LineBundleClass C) :
    eulerDegree k (pullback g a) =
      Module.finrank g.functionFieldMap.hom.fieldRange C'.functionField * eulerDegree k a := by
  set νC := (C.fromSpecStalk (genericPoint C)).fromNormalization
  set νC' := (C'.fromSpecStalk (genericPoint C')).fromNormalization
  set gν := normalizationLift g
  let _ : (C.fromSpecStalk (genericPoint C)).normalization.Over (Spec (.of k)) :=
    ⟨νC ≫ C ↘ Spec (.of k)⟩
  let _ : (C'.fromSpecStalk (genericPoint C')).normalization.Over (Spec (.of k)) :=
    ⟨νC' ≫ C' ↘ Spec (.of k)⟩
  have : νC.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : νC'.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : gν.IsOver (Spec (.of k)) := ⟨by
    change gν ≫ νC ≫ C ↘ Spec (.of k) = νC' ≫ C' ↘ Spec (.of k)
    rw [normalizationLift_fromNormalization_assoc, HomIsOver.comp_over]⟩
  have : IsFinite νC := isFinite_fromNormalization_of_isUniversallyJapanese k
  have : IsFinite νC' := isFinite_fromNormalization_of_isUniversallyJapanese k
  have : IsFinite gν := isFinite_normalizationLift g
  have ⟨hcurveC, hdvrC⟩ := isCurveOver_normalization k h1
  have ⟨hcurveC', _⟩ := isCurveOver_normalization k h1'
  have : RelativeDimensionLE 1 ((C.fromSpecStalk (genericPoint C)).normalization ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr hcurveC.topologicalKrullDim_eq_one.le
  have : RelativeDimensionLE 1
      ((C'.fromSpecStalk (genericPoint C')).normalization ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr hcurveC'.topologicalKrullDim_eq_one.le
  have : ∀ y : (C.fromSpecStalk (genericPoint C)).normalization,
      ValuationRing ((C.fromSpecStalk (genericPoint C)).normalization.presheaf.stalk y) :=
    Scheme.IsCurveOver.valuationRing_stalk k _
  have hfin (Z : Scheme.{u}) [IsIntegral Z] [Z.Over (Spec (.of k))]
      [IsProper (Z ↘ Spec (.of k))] [RelativeDimensionLE 1 (Z ↘ Spec (.of k))] :
      FiniteDimensional k (Cohomology (InvertibleSheaf.trivial Z).obj 0) ∧
        FiniteDimensional k (Cohomology (InvertibleSheaf.trivial Z).obj 1) :=
    ⟨(InvertibleSheaf.trivial Z).finiteDimensional_cohomology_of_isProper k (by omega),
      (InvertibleSheaf.trivial Z).finiteDimensional_cohomology_of_isProper k (by omega)⟩
  have ⟨_, _⟩ := hfin (C.fromSpecStalk (genericPoint C)).normalization
  have ⟨_, _⟩ := hfin (C'.fromSpecStalk (genericPoint C')).normalization
  calc
    eulerDegree k (pullback g a)
        = eulerDegree k (pullback νC' (pullback g a)) :=
      (eulerDegree_pullback_fromNormalization k (pullback g a)).symm
    _ = eulerDegree k (pullback (νC' ≫ g) a) := by rw [pullback_comp]
    _ = eulerDegree k (pullback (gν ≫ νC) a) := by rw [normalizationLift_fromNormalization]
    _ = eulerDegree k (pullback gν (pullback νC a)) := by rw [pullback_comp]
    _ = Module.finrank gν.functionFieldMap.hom.fieldRange
          (C'.fromSpecStalk (genericPoint C')).normalization.functionField *
          eulerDegree k (pullback νC a) :=
      eulerDegree_pullback_of_isDominant k gν (pullback νC a)
    _ = Module.finrank g.functionFieldMap.hom.fieldRange C'.functionField * eulerDegree k a := by
      rw [finrank_functionFieldMap_normalizationLift g, eulerDegree_pullback_fromNormalization k a]

/-- **The pullback formula for degree on arbitrary integral proper curves.** Let `g : C' ⟶ C` be a
finite dominant morphism over a field `k` between integral schemes, where `C` is proper over `k`
with fibres of dimension at most one. Then `deg_k (g^* a) = [K(C') : K(C)] · deg_k a` for every
line-bundle class `a` on `C`. Neither `C` nor `C'` need be regular. -/
@[stacks 0AYU]
theorem eulerDegree_pullback_of_isFinite_isDominant {C C' : Scheme.{u}}
    [C.Over (Spec (.of k))] [C'.Over (Spec (.of k))]
    (g : C' ⟶ C) [g.IsOver (Spec (.of k))] [IsFinite g]
    [IsIntegral C] [IsIntegral C'] [IsDominant g]
    [IsProper (C ↘ Spec (.of k))] [RelativeDimensionLE 1 (C ↘ Spec (.of k))]
    (a : LineBundleClass C) :
    eulerDegree k (pullback g a) =
      Module.finrank g.functionFieldMap.hom.fieldRange C'.functionField * eulerDegree k a := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of k))
  have : IsProper (C' ↘ Spec (.of k)) := by
    rw [← HomIsOver.comp_over (f := g) (S := Spec (.of k))]
    infer_instance
  have : IsLocallyNoetherian C' := LocallyOfFiniteType.isLocallyNoetherian (C' ↘ Spec (.of k))
  have hdim_eq : topologicalKrullDim C' = topologicalKrullDim C :=
    g.topologicalKrullDim_eq_of_isIntegralHom_of_isDominant
  have : RelativeDimensionLE 1 (C' ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field (C' ↘ Spec (.of k))).mpr
      (hdim_eq.le.trans ((relativeDimensionLE_iff_of_field (C ↘ Spec (.of k))).mp inferInstance))
  rcases topologicalKrullDim_eq_zero_or_one k (X := C) with h0 | h1
  · have : IsLocallyArtinian C := IsLocallyArtinian.of_topologicalKrullDim_le_zero h0.le
    have : IsLocallyArtinian C' :=
      IsLocallyArtinian.of_topologicalKrullDim_le_zero (hdim_eq.trans h0).le
    rw [eq_one_of_discreteTopology a, eq_one_of_discreteTopology (pullback g 1),
      eulerDegree_one, eulerDegree_one, mul_zero]
  · exact eulerDegree_pullback_of_isFinite_isDominant_dim_one k g h1 (hdim_eq.trans h1) a

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
