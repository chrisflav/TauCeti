/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Normalization.Basic
public import TauCeti.AlgebraicGeometry.Scheme.Normal
import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.AlgebraicGeometry.Morphisms.Integral.Dimension
import TauCeti.AlgebraicGeometry.Normalization.IsIso
import TauCeti.AlgebraicGeometry.Normalization.Regular

/-!
# Normalization, function fields, and universal property for dominant morphisms

Let `Y` be an integral scheme and `ν_Y : Y^ν ⟶ Y` its normalization in its function field, along
`Spec k(Y) ⟶ Y`. Since `Spec k(Y) ⟶ Y^ν ⟶ Y` factors `Spec k(Y) ⟶ Y`, the normalization morphism
`ν_Y` is dominant and induces an isomorphism on function fields `k(Y) ≃ k(Y^ν)`
(`TauCeti.AlgebraicGeometry.isIso_functionFieldMap_fromNormalization_fromSpecStalk_genericPoint`),
with no finiteness or Noetherianity hypothesis. Being integral and dominant, every relative
normalization of a dominant morphism preserves Krull dimension
(`AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_normalization`).

Normalization enjoys its standard universal property (Stacks, Lemma 29.54.5 (035Q)): every dominant
morphism `f : Z ⟶ Y` from a normal integral scheme `Z` to an integral scheme `Y` factors uniquely
through `ν_Y : Y^ν ⟶ Y` (`TauCeti.AlgebraicGeometry.liftToNormalization`). In particular,
normalization is functorial for arbitrary dominant morphisms `g : X ⟶ Y` of integral schemes, with
a unique lift `g^ν : X^ν ⟶ Y^ν` satisfying `g^ν ≫ ν_Y = ν_X ≫ g`
(`TauCeti.AlgebraicGeometry.normalizationLift`). This lift is dominant, respects identities and
composition, induces the same function-field extension degree `[k(X^ν) : k(Y^ν)] = [k(X) : k(Y)]`,
is integral whenever `g` is integral, and is finite whenever `g` and `ν_X` are finite.

## Main definitions

* `TauCeti.AlgebraicGeometry.liftToNormalization`: the unique lift `Z ⟶ Y^ν` of a dominant
  morphism `f : Z ⟶ Y` from a normal integral scheme `Z` to an integral scheme `Y`.
* `TauCeti.AlgebraicGeometry.normalizationLift`: the unique lift `X^ν ⟶ Y^ν` of a dominant
  morphism `g : X ⟶ Y` of integral schemes to their normalizations.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isDominant_fromNormalization`: the relative normalization of a
  dominant morphism is dominant.
* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_normalization`: the relative normalization of a
  dominant morphism has the same Krull dimension as the target.
* `TauCeti.AlgebraicGeometry.isIso_functionFieldMap_fromNormalization_fromSpecStalk_genericPoint`:
  normalization of an integral scheme induces an isomorphism on function fields.
* `TauCeti.AlgebraicGeometry.liftToNormalization_fromNormalization` and
  `TauCeti.AlgebraicGeometry.eq_liftToNormalization`: characterizing commutation and uniqueness for
  the universal property of normalization.
* `TauCeti.AlgebraicGeometry.normalizationLift_fromNormalization` and
  `TauCeti.AlgebraicGeometry.eq_normalizationLift`: characterizing commutation and uniqueness of
  `normalizationLift`.
* `TauCeti.AlgebraicGeometry.isDominant_normalizationLift`,
  `TauCeti.AlgebraicGeometry.isIntegralHom_normalizationLift` and
  `TauCeti.AlgebraicGeometry.isFinite_normalizationLift`: properties of `normalizationLift`.
* `TauCeti.AlgebraicGeometry.normalizationLift_id` and
  `TauCeti.AlgebraicGeometry.normalizationLift_comp`: functoriality of `normalizationLift`.
* `TauCeti.AlgebraicGeometry.finrank_functionFieldMap_normalizationLift`: the lift has the same
  function-field extension degree as `g`.

## References

* [Stacks Project, Lemma 29.54.5](https://stacks.math.columbia.edu/tag/035Q) (universal property
  and functoriality of normalization).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}}

/-- The relative normalization of a dominant quasi-compact quasi-separated morphism is dominant over
the target. -/
instance isDominant_fromNormalization (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : IsDominant f.fromNormalization := by
  have h : DenseRange (f.toNormalization ≫ f.fromNormalization) := by
    rw [f.toNormalization_fromNormalization]
    exact f.denseRange
  exact ⟨h.mono <| by rintro _ ⟨x, rfl⟩; exact ⟨f.toNormalization x, rfl⟩⟩

/-- The relative normalization of a dominant quasi-compact quasi-separated morphism has the same
Krull dimension as the target. -/
theorem topologicalKrullDim_normalization (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] :
    topologicalKrullDim f.normalization = topologicalKrullDim Y :=
  f.fromNormalization.topologicalKrullDim_eq_of_isIntegralHom_of_isDominant

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- In an integral dominant morphism of integral schemes, the only point mapping to the generic
point is the generic point. -/
private lemma eq_genericPoint_of_isIntegralHom_apply [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsIntegralHom f] [IsDominant f] {x : X} (hx : f x = genericPoint Y) :
    x = genericPoint X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint Y)) isOpen_univ
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hxV : x ∈ f ⁻¹ᵁ U := by simpa [hx] using hηU
  have hηV : genericPoint X ∈ f ⁻¹ᵁ U := by
    simpa [f.genericPoint_eq_of_isDominant] using hηU
  let _ : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : Algebra.IsIntegral Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := ⟨f.isIntegral_app U hU⟩
  -- Both `x` and `genericPoint X` correspond to primes of `Γ(X, f ⁻¹ᵁ U)` lying over the same
  -- prime of `Γ(Y, U)`; incomparability for integral extensions forces them to coincide.
  have hsp : hV.primeIdealOf ⟨genericPoint X, hηV⟩ ⤳ hV.primeIdealOf ⟨x, hxV⟩ :=
    (hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff
      (x := hV.primeIdealOf ⟨genericPoint X, hηV⟩) (y := hV.primeIdealOf ⟨x, hxV⟩)).mp <| by
      rw [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf]
      exact genericPoint_specializes x
  have hle : (hV.primeIdealOf ⟨genericPoint X, hηV⟩).asIdeal ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr hsp
  have heq_under : (hV.primeIdealOf ⟨genericPoint X, hηV⟩).asIdeal.under Γ(Y, U) =
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.under Γ(Y, U) := by
    have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := f) U hU (f ⁻¹ᵁ U) hV le_rfl hηV
    have h2 := IsAffineOpen.comap_primeIdealOf_appLE (f := f) U hU (f ⁻¹ᵁ U) hV le_rfl hxV
    have hf : (⟨f (genericPoint X), hηV⟩ : U) = ⟨f x, hxV⟩ :=
      Subtype.ext (f.genericPoint_eq_of_isDominant.trans hx.symm)
    have hcomap : (hV.primeIdealOf ⟨genericPoint X, hηV⟩).comap (f.app U).hom =
        (hV.primeIdealOf ⟨x, hxV⟩).comap (f.app U).hom := by
      simpa only [Scheme.Hom.appLE_eq_app] using
        h1.trans ((congrArg hU.primeIdealOf hf).trans h2.symm)
    exact congrArg PrimeSpectrum.asIdeal hcomap
  have hprime : hV.primeIdealOf ⟨genericPoint X, hηV⟩ = hV.primeIdealOf ⟨x, hxV⟩ :=
    PrimeSpectrum.ext <| hle.eq_or_lt.resolve_right fun hlt ↦
      (Ideal.IsIntegral.under_lt_under hlt).ne heq_under
  exact (hV.fromSpec_primeIdealOf ⟨x, hxV⟩).symm.trans <|
    (congrArg hV.fromSpec hprime.symm).trans (hV.fromSpec_primeIdealOf ⟨genericPoint X, hηV⟩)

/-- The canonical morphism `Spec k(Y) ⟶ Y` induces an isomorphism on function fields. -/
private instance isIso_functionFieldMap_fromSpecStalk_genericPoint [IsIntegral Y] :
    IsIso (Y.fromSpecStalk (genericPoint Y)).functionFieldMap := by
  set f := Y.fromSpecStalk (genericPoint Y)
  have hspec : Spec.map f.functionFieldMap =
      (Spec Y.functionField).fromSpecStalk (genericPoint (Spec Y.functionField)) :=
    (cancel_mono f).mp (Scheme.Hom.SpecMap_functionFieldMap_fromSpecStalk f)
  have : IsIso ((Spec Y.functionField).fromSpecStalk (genericPoint (Spec Y.functionField))) := by
    have : Subsingleton (Spec Y.functionField) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum Y.functionField))
    rw [Subsingleton.elim (genericPoint (Spec Y.functionField)) (IsLocalRing.closedPoint _),
      ← AlgebraicGeometry.Spec_stalkClosedPointIso]
    infer_instance
  have : IsIso (Scheme.Spec.map f.functionFieldMap.op) := by
    change IsIso (Spec.map f.functionFieldMap)
    rw [hspec]
    infer_instance
  have : IsIso f.functionFieldMap.op := isIso_of_reflects_iso f.functionFieldMap.op Scheme.Spec
  exact isIso_of_op f.functionFieldMap

/-- **Normalization preserves the function field.** For an integral scheme `Y`, the normalization
morphism `ν_Y : Y^ν ⟶ Y` induces an isomorphism `k(Y) ≃ k(Y^ν)` on function fields. -/
instance isIso_functionFieldMap_fromNormalization_fromSpecStalk_genericPoint [IsIntegral Y] :
    IsIso (Y.fromSpecStalk (genericPoint Y)).fromNormalization.functionFieldMap := by
  set f := Y.fromSpecStalk (genericPoint Y)
  have hcomp : f.fromNormalization.functionFieldMap ≫ f.toNormalization.functionFieldMap =
      f.functionFieldMap := by
    rw [← Scheme.Hom.functionFieldMap_comp, eq_comm, Scheme.Hom.eq_functionFieldMap_iff,
      Scheme.Hom.SpecMap_functionFieldMap_fromSpecStalk, f.toNormalization_fromNormalization]
  have hsurj : Function.Surjective f.toNormalization.functionFieldMap := by
    have hcomp_surj : Function.Surjective
        (f.toNormalization.functionFieldMap.hom ∘ f.fromNormalization.functionFieldMap.hom) := by
      rw [← RingHom.coe_comp, ← CommRingCat.hom_comp, hcomp]
      exact (ConcreteCategory.bijective_of_isIso f.functionFieldMap).2
    exact hcomp_surj.of_comp
  have : IsIso f.toNormalization.functionFieldMap :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨f.toNormalization.functionFieldMap.hom.injective,
      hsurj⟩
  have : IsIso (f.fromNormalization.functionFieldMap ≫ f.toNormalization.functionFieldMap) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_right f.fromNormalization.functionFieldMap
    f.toNormalization.functionFieldMap

section UniversalProperty

/-- Two morphisms from an integral scheme `W` to the normalization `Y^ν` of an integral scheme `Y`
that compose to the same dominant morphism `W ⟶ Y` must coincide. -/
private lemma eq_of_comp_fromNormalization [IsIntegral X] [IsIntegral Y]
    {g₁ g₂ : X ⟶ (Y.fromSpecStalk (genericPoint Y)).normalization}
    (h : g₁ ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization =
      g₂ ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization)
    [IsDominant (g₁ ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization)] :
    g₁ = g₂ := by
  set νY := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  have hdom₁ : IsDominant g₁ := by
    rw [isDominant_iff_genericPoint_eq]
    refine eq_genericPoint_of_isIntegralHom_apply νY ?_
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.genericPoint_eq_of_isDominant]
  have hdom₂ : IsDominant g₂ := by
    rw [isDominant_iff_genericPoint_eq]
    refine eq_genericPoint_of_isIntegralHom_apply νY ?_
    rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.genericPoint_eq_of_isDominant]
  let _ : X.Over Y := ⟨g₁ ≫ νY⟩
  let _ : (Y.fromSpecStalk (genericPoint Y)).normalization.Over Y := ⟨νY⟩
  have : IsSeparated ((Y.fromSpecStalk (genericPoint Y)).normalization ↘ Y) :=
    inferInstanceAs (IsSeparated νY)
  have : g₁.IsOver Y := ⟨rfl⟩
  have : g₂.IsOver Y := ⟨h.symm⟩
  refine Scheme.Hom.ext_of_functionFieldMap_eq Y ?_
  rw [← cancel_epi νY.functionFieldMap, ← Scheme.Hom.functionFieldMap_comp,
    ← Scheme.Hom.functionFieldMap_comp, eq_comm, Scheme.Hom.eq_functionFieldMap_iff,
    Scheme.Hom.SpecMap_functionFieldMap_fromSpecStalk, h]

/-- Local ring-homomorphism step for the universal property of normalization: for a dominant
morphism `f : Z ⟶ Y` from a normal integral scheme `Z` to an integral scheme `Y`, and affine opens
`V ⊆ Z` (nonempty) and `U ⊆ Y` with `V ⊆ f ⁻¹ U`, every section of `Y^ν` over `ν_Y ⁻¹ U` pulls back
into the integrally closed domain `Γ(Z, V)`. -/
private lemma exists_liftToNormalizationApp [IsIntegral Z] [IsNormalScheme Z] [IsIntegral Y]
    (f : Z ⟶ Y) [IsDominant f] (U : Y.affineOpens) (V : Z.affineOpens) [Nonempty V.1]
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    ∃ φ : Γ((Y.fromSpecStalk (genericPoint Y)).normalization,
        (Y.fromSpecStalk (genericPoint Y)).fromNormalization ⁻¹ᵁ U.1) ⟶ Γ(Z, V.1),
      (Y.fromSpecStalk (genericPoint Y)).fromNormalization.app U.1 ≫ φ = f.appLE U.1 V.1 hVU := by
  let νY := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  let Yν := (Y.fromSpecStalk (genericPoint Y)).normalization
  have : Nonempty U.1 := ⟨⟨f (Classical.arbitrary V.1).1, hVU (Classical.arbitrary V.1).2⟩⟩
  let ψ : Γ(Yν, νY ⁻¹ᵁ U.1) ⟶ Z.functionField :=
    Yν.germToFunctionField (νY ⁻¹ᵁ U.1) ≫ inv νY.functionFieldMap ≫ f.functionFieldMap
  have hcomp : νY.app U.1 ≫ ψ = f.appLE U.1 V.1 hVU ≫ Z.germToFunctionField V.1 := by
    have h₁ : νY.app U.1 ≫ Yν.germToFunctionField (νY ⁻¹ᵁ U.1) =
        Y.germToFunctionField U.1 ≫ νY.functionFieldMap :=
      (νY.germToFunctionField_functionFieldMap U.1).symm
    have h₂ : f.appLE U.1 V.1 hVU ≫ Z.germToFunctionField V.1 =
        Y.germToFunctionField U.1 ≫ f.functionFieldMap := by
      simp [Scheme.Hom.appLE, Scheme.germToFunctionField]
    rw [show νY.app U.1 ≫ ψ = (νY.app U.1 ≫ Yν.germToFunctionField (νY ⁻¹ᵁ U.1)) ≫
      inv νY.functionFieldMap ≫ f.functionFieldMap by simp [ψ, Category.assoc], h₁,
      Category.assoc, IsIso.hom_inv_id_assoc, h₂]
  have := functionField_isFractionRing_of_isAffineOpen Z V.1 V.2
  have := IsNormalScheme.isIntegrallyClosed_of_isAffineOpen V.2
  have hex (x : Γ(Yν, νY ⁻¹ᵁ U.1)) : ∃ y : Γ(Z, V.1), Z.germToFunctionField V.1 y = ψ x := by
    obtain ⟨p, hp, hpx⟩ := νY.isIntegral_app U.1 U.2 x
    have hint : _root_.IsIntegral Γ(Z, V.1) (ψ x) := by
      refine ⟨p.map (f.appLE U.1 V.1 hVU).hom, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have heq : (algebraMap Γ(Z, V.1) Z.functionField).comp (f.appLE U.1 V.1 hVU).hom =
          ψ.hom.comp (νY.app U.1).hom :=
        RingHom.ext fun r ↦ (congr($hcomp r)).symm
      rw [heq, ← Polynomial.hom_eval₂, hpx, map_zero]
    exact IsIntegrallyClosed.isIntegral_iff.mp hint
  choose φ hφ using hex
  have hinj := Z.germToFunctionField_injective V.1
  refine ⟨CommRingCat.ofHom
    { toFun := φ
      map_one' := hinj (by rw [hφ, map_one, map_one])
      map_mul' := fun a b ↦ hinj (by rw [hφ, map_mul, map_mul, hφ, hφ])
      map_zero' := hinj (by rw [hφ, map_zero, map_zero])
      map_add' := fun a b ↦ hinj (by rw [hφ, map_add, map_add, hφ, hφ]) }, ?_⟩
  ext r
  exact hinj (by simpa [hφ] using congr($hcomp r))

/-- Local scheme-level lift of a dominant morphism `f : Z ⟶ Y` from a normal integral scheme `Z`
over a nonempty affine open `V ⊆ f ⁻¹ U`. -/
private lemma exists_liftToNormalization_local [IsIntegral Z] [IsNormalScheme Z] [IsIntegral Y]
    (f : Z ⟶ Y) [IsDominant f] (U : Y.affineOpens) (V : Z.affineOpens) [Nonempty V.1]
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    ∃ g : (V.1 : Scheme) ⟶ (Y.fromSpecStalk (genericPoint Y)).normalization,
      g ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization = V.1.ι ≫ f := by
  let νY := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen V.1 := V.2
  obtain ⟨φ, hφ⟩ := exists_liftToNormalizationApp f U V hVU
  refine ⟨hV.isoSpec.hom ≫ Spec.map φ ≫ (hU.preimage νY).fromSpec, ?_⟩
  have hν := IsAffineOpen.SpecMap_appLE_fromSpec νY hU (hU.preimage νY) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hν
  calc hV.isoSpec.hom ≫ Spec.map φ ≫ (hU.preimage νY).fromSpec ≫ νY
      = hV.isoSpec.hom ≫ (Spec.map φ ≫ Spec.map (νY.app U.1)) ≫ hU.fromSpec := by
        rw [← hν, Category.assoc]
    _ = hV.isoSpec.hom ≫ Spec.map (f.appLE U.1 V.1 hVU) ≫ hU.fromSpec := by
        rw [← Spec.map_comp, hφ]
    _ = V.1.ι ≫ f := by
        rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, hV.isoSpec_hom_fromSpec_assoc]

/-- Gluing helper for `liftToNormalization`: constructs the lifted morphism together with its
commutation with `fromNormalization`. -/
private lemma exists_liftToNormalization [IsIntegral Z] [IsNormalScheme Z] [IsIntegral Y]
    (f : Z ⟶ Y) [IsDominant f] :
    ∃ g : Z ⟶ (Y.fromSpecStalk (genericPoint Y)).normalization,
      g ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization = f := by
  let νY := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  have hcov (z : Z) : ∃ (U : Y.affineOpens) (V : Z.affineOpens), z ∈ V.1 ∧ V.1 ≤ f ⁻¹ᵁ U.1 := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hfz, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f z)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVU⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (show z ∈ (f ⁻¹ᵁ U).1 from hfz) (f ⁻¹ᵁ U).isOpen
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hzV, hVU⟩
  choose U V hzV hVU using hcov
  choose g hg using fun z : Z ↦
    have : Nonempty (V z).1 := ⟨⟨z, hzV z⟩⟩
    exists_liftToNormalization_local f (U z) (V z) (hVU z)
  let 𝒰 : Z.OpenCover := Z.openCoverOfIsOpenCover (fun z ↦ (V z).1)
    (eq_top_iff.mpr fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hzV z⟩)
  let g' : ∀ z : 𝒰.I₀, 𝒰.X z ⟶ (Y.fromSpecStalk (genericPoint Y)).normalization := g
  have hη (i : Z) : genericPoint Z ∈ (V i).1 :=
    (genericPoint_specializes i).mem_open (V i).1.isOpen (hzV i)
  have hglue (z w : 𝒰.I₀) : pullback.fst (𝒰.f z) (𝒰.f w) ≫ g' z =
      pullback.snd (𝒰.f z) (𝒰.f w) ≫ g' w := by
    obtain ⟨q, hqz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒰.f z) (g := 𝒰.f w)
      (⟨genericPoint Z, hη z⟩ : (V z).1) (⟨genericPoint Z, hη w⟩ : (V w).1) rfl
    have : Nonempty (pullback (𝒰.f z) (𝒰.f w) : Scheme) := ⟨q⟩
    have : IsIntegral (pullback (𝒰.f z) (𝒰.f w)) :=
      isIntegral_of_isOpenImmersion (pullback.fst (𝒰.f z) (𝒰.f w) ≫ 𝒰.f z)
    have hgf (i : 𝒰.I₀) : g' i ≫ νY = 𝒰.f i ≫ f := hg i
    have hcomp : (pullback.fst (𝒰.f z) (𝒰.f w) ≫ g' z) ≫ νY =
        (pullback.snd (𝒰.f z) (𝒰.f w) ≫ g' w) ≫ νY := by
      rw [Category.assoc, Category.assoc, hgf z, hgf w, ← Category.assoc, ← Category.assoc,
        pullback.condition]
    have : IsDominant ((pullback.fst (𝒰.f z) (𝒰.f w) ≫ g' z) ≫ νY) := by
      rw [Category.assoc, hgf z]
      refine ⟨(dense_iff_closure_eq.mpr (genericPoint_closure Y)).mono
        (Set.singleton_subset_iff.mpr ⟨q, ?_⟩)⟩
      change f (𝒰.f z (pullback.fst (𝒰.f z) (𝒰.f w) q)) = genericPoint Y
      rw [show 𝒰.f z (pullback.fst (𝒰.f z) (𝒰.f w) q) = genericPoint Z from congrArg (𝒰.f z) hqz]
      exact f.genericPoint_eq_of_isDominant
    exact eq_of_comp_fromNormalization hcomp
  refine ⟨𝒰.glueMorphisms g' hglue, 𝒰.hom_ext _ _ fun z ↦ ?_⟩
  rw [Scheme.Cover.ι_glueMorphisms_assoc]
  exact hg z

/-- **Universal property of normalization (Stacks, Lemma 29.54.5 / 035Q).** Every dominant morphism
`f : Z ⟶ Y` from a normal integral scheme `Z` to an integral scheme `Y` factors uniquely through
the normalization `ν_Y : Y^ν ⟶ Y`. -/
@[stacks 035Q]
noncomputable def liftToNormalization [IsIntegral Z] [IsNormalScheme Z] [IsIntegral Y]
    (f : Z ⟶ Y) [IsDominant f] :
    Z ⟶ (Y.fromSpecStalk (genericPoint Y)).normalization :=
  (exists_liftToNormalization f).choose

/-- The universal lift to normalization satisfies `liftToNormalization f ≫ ν_Y = f`. -/
@[reassoc (attr := simp)]
theorem liftToNormalization_fromNormalization [IsIntegral Z] [IsNormalScheme Z] [IsIntegral Y]
    (f : Z ⟶ Y) [IsDominant f] :
    liftToNormalization f ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization = f :=
  (exists_liftToNormalization f).choose_spec

/-- **Uniqueness of the universal lift to normalization.** Any morphism `k : Z ⟶ Y^ν` satisfying
`k ≫ ν_Y = f` equals `liftToNormalization f`. -/
theorem eq_liftToNormalization [IsIntegral Z] [IsNormalScheme Z] [IsIntegral Y]
    (f : Z ⟶ Y) [IsDominant f]
    {k : Z ⟶ (Y.fromSpecStalk (genericPoint Y)).normalization}
    (hk : k ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization = f) :
    k = liftToNormalization f :=
  have : IsDominant (k ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization) := by
    rw [hk]; infer_instance
  eq_of_comp_fromNormalization (hk.trans (liftToNormalization_fromNormalization f).symm)

end UniversalProperty

section Lift

variable [IsIntegral X] [IsIntegral Y]

/-- **Functoriality of normalization for dominant morphisms.** Given a dominant morphism `g : X ⟶ Y`
of integral schemes, there is a unique morphism `g^ν : X^ν ⟶ Y^ν` between their normalizations
satisfying `g^ν ≫ ν_Y = ν_X ≫ g` (`normalizationLift_fromNormalization`). -/
@[stacks 035Q]
noncomputable def normalizationLift (g : X ⟶ Y) [IsDominant g] :
    (X.fromSpecStalk (genericPoint X)).normalization ⟶
      (Y.fromSpecStalk (genericPoint Y)).normalization :=
  liftToNormalization ((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ g)

/-- The normalization lift commutes with the normalization morphisms: `g^ν ≫ ν_Y = ν_X ≫ g`. -/
@[reassoc (attr := simp)]
theorem normalizationLift_fromNormalization (g : X ⟶ Y) [IsDominant g] :
    normalizationLift g ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization =
      (X.fromSpecStalk (genericPoint X)).fromNormalization ≫ g :=
  liftToNormalization_fromNormalization _

/-- The normalization lift of a dominant morphism is dominant. -/
instance isDominant_normalizationLift (g : X ⟶ Y) [IsDominant g] :
    IsDominant (normalizationLift g) := by
  rw [isDominant_iff_genericPoint_eq]
  refine eq_genericPoint_of_isIntegralHom_apply
    (Y.fromSpecStalk (genericPoint Y)).fromNormalization ?_
  rw [← Scheme.Hom.comp_apply, normalizationLift_fromNormalization,
    Scheme.Hom.genericPoint_eq_of_isDominant]

/-- **Uniqueness of the normalization lift.** Any morphism `k : X^ν ⟶ Y^ν` satisfying
`k ≫ ν_Y = ν_X ≫ g` equals `normalizationLift g`. -/
theorem eq_normalizationLift (g : X ⟶ Y) [IsDominant g]
    {k : (X.fromSpecStalk (genericPoint X)).normalization ⟶
      (Y.fromSpecStalk (genericPoint Y)).normalization}
    (hk : k ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization =
      (X.fromSpecStalk (genericPoint X)).fromNormalization ≫ g) :
    k = normalizationLift g :=
  eq_liftToNormalization _ hk

/-- The normalization lift of an integral dominant morphism is integral. -/
instance isIntegralHom_normalizationLift (g : X ⟶ Y) [IsIntegralHom g] [IsDominant g] :
    IsIntegralHom (normalizationLift g) := by
  set νX := (X.fromSpecStalk (genericPoint X)).fromNormalization
  set h := (X.fromSpecStalk (genericPoint X)).normalization.fromSpecStalk
    (genericPoint (X.fromSpecStalk (genericPoint X)).normalization) ≫ (νX ≫ g)
  have : IsIso (h.normalizationDesc _ (νX ≫ g) rfl) :=
    isIso_normalizationDesc_fromSpecStalk_genericPoint
      (fun _ ↦ IsNormalScheme.isIntegrallyClosed_stalk _) (νX ≫ g)
  let k := inv (h.normalizationDesc _ (νX ≫ g) rfl) ≫
    h.normalizationMap (Y.fromSpecStalk (genericPoint Y))
      (Spec.map (νX ≫ g).functionFieldMap)
      (Scheme.Hom.SpecMap_functionFieldMap_fromSpecStalk (νX ≫ g))
  have hk : k = normalizationLift g := eq_normalizationLift g <| by
    dsimp only [k]
    rw [Category.assoc, Scheme.Hom.normalizationMap_fromNormalization, IsIso.inv_comp_eq,
      Scheme.Hom.normalizationDesc_comp]
  rw [← hk]
  infer_instance

/-- The normalization lift of the identity is the identity. -/
@[simp]
theorem normalizationLift_id :
    normalizationLift (𝟙 X) = 𝟙 (X.fromSpecStalk (genericPoint X)).normalization :=
  (eq_normalizationLift (𝟙 X) (by simp)).symm

/-- The normalization lift respects composition. -/
@[reassoc, simp]
theorem normalizationLift_comp [IsIntegral Z] (g : X ⟶ Y) (h : Y ⟶ Z)
    [IsDominant g] [IsDominant h] :
    normalizationLift (g ≫ h) = normalizationLift g ≫ normalizationLift h :=
  (eq_normalizationLift (g ≫ h) (by simp)).symm

/-- If `g : X ⟶ Y` and `ν_X : X^ν ⟶ X` are finite, then `normalizationLift g : X^ν ⟶ Y^ν` is
finite. -/
theorem isFinite_normalizationLift (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization] :
    IsFinite (normalizationLift g) := by
  have : IsFinite (normalizationLift g ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization) := by
    rw [normalizationLift_fromNormalization]
    infer_instance
  exact IsFinite.of_comp (normalizationLift g) (Y.fromSpecStalk (genericPoint Y)).fromNormalization

/-- **Invariance of the function-field extension degree under normalization.** For a dominant
morphism `g : X ⟶ Y` of integral schemes, the lift `g^ν : X^ν ⟶ Y^ν` induces a function-field
extension of the same degree `[k(X^ν) : k(Y^ν)] = [k(X) : k(Y)]`. -/
theorem finrank_functionFieldMap_normalizationLift (g : X ⟶ Y) [IsDominant g] :
    Module.finrank (normalizationLift g).functionFieldMap.hom.fieldRange
        (X.fromSpecStalk (genericPoint X)).normalization.functionField =
      Module.finrank g.functionFieldMap.hom.fieldRange X.functionField := by
  set νX := (X.fromSpecStalk (genericPoint X)).fromNormalization
  set νY := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  have hsq : νY.functionFieldMap ≫ (normalizationLift g).functionFieldMap =
      g.functionFieldMap ≫ νX.functionFieldMap := by
    rw [← Scheme.Hom.functionFieldMap_comp, ← Scheme.Hom.functionFieldMap_comp,
      eq_comm, Scheme.Hom.eq_functionFieldMap_iff,
      Scheme.Hom.SpecMap_functionFieldMap_fromSpecStalk, normalizationLift_fromNormalization]
  let eX := (asIso νX.functionFieldMap).commRingCatIsoToRingEquiv
  let eY := (asIso νY.functionFieldMap).commRingCatIsoToRingEquiv
  have hcomm (y : Y.functionField) :
      (normalizationLift g).functionFieldMap.hom (eY y) = eX (g.functionFieldMap.hom y) :=
    congr($hsq y)
  -- `eX` restricts to a ring equivalence between the images of `k(Y)` and `k(Y^ν)`.
  let φ : g.functionFieldMap.hom.fieldRange →+*
      (normalizationLift g).functionFieldMap.hom.fieldRange :=
    { toFun := fun a ↦ ⟨eX a.1, by
        obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp a.2
        exact RingHom.mem_fieldRange.mpr ⟨eY y, (hcomm y).trans (congrArg eX hy)⟩⟩
      map_one' := Subtype.ext (map_one eX)
      map_mul' := fun _ _ ↦ Subtype.ext (map_mul eX _ _)
      map_zero' := Subtype.ext (map_zero eX)
      map_add' := fun _ _ ↦ Subtype.ext (map_add eX _ _) }
  let eF : g.functionFieldMap.hom.fieldRange ≃+*
      (normalizationLift g).functionFieldMap.hom.fieldRange :=
    RingEquiv.ofBijective φ
      ⟨fun a b hab ↦ Subtype.ext (eX.injective (congrArg Subtype.val hab)), fun b ↦ by
        obtain ⟨y', hy'⟩ := RingHom.mem_fieldRange.mp b.2
        refine ⟨⟨g.functionFieldMap.hom (eY.symm y'),
          RingHom.mem_fieldRange.mpr ⟨eY.symm y', rfl⟩⟩, Subtype.ext ?_⟩
        exact (hcomm (eY.symm y')).symm.trans <| (congrArg _ (eY.apply_symm_apply y')).trans hy'⟩
  exact (Algebra.finrank_eq_of_equiv_equiv eF eX (RingHom.ext fun _ ↦ rfl)).symm

end Lift

end TauCeti.AlgebraicGeometry
