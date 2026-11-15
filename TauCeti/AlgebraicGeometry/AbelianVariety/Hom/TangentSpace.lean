/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.End.Basic
public import TauCeti.AlgebraicGeometry.AbelianVariety.TangentSpace
public import TauCeti.AlgebraicGeometry.GroupScheme.Etale
public import TauCeti.AlgebraicGeometry.TangentSpace.DualNumber
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.RingTheory.RegularLocalRing.Normal

/-!
# Induced tangent maps of homomorphisms of abelian varieties

Every homomorphism `f : A ⟶ B` of abelian varieties over a field `K` preserves the zero section, so
it induces a `K`-linear differential `AbelianVariety.Hom.tangentMap f : T₀A →ₗ[K] T₀B` on tangent
spaces at the identity.

Through the pointed dual-number equivalence `trivSqZeroPointEquiv`, `T₀A` is identified with the
`K[ε]/(ε²)`-points of `A` lying over the identity section. Composing such an infinitesimal point
with `f` transports the group law on `A ⟶ B` into addition of `K`-linear maps (`Stacks Tag 0BFG`),
and dualizing back to cotangent spaces expresses `Hom.tangentMap f` via the Zariski cotangent
pullback `(Hom.toSchemeHom f).zariskiCotangentMap A.zeroPoint`.

Consequently:
* `AbelianVariety.Hom.tangentMap` is functorial (`tangentMap_id`, `tangentMap_comp`) and sends the
  pointwise group operations on `A ⟶ B` to the additive group operations on `T₀A →ₗ[K] T₀B`
  (`tangentMap_one`, `tangentMap_mul`, `tangentMap_inv`, `tangentMap_div`, `tangentMap_zpow`);
* `AbelianVariety.End.tangentRingHom` is the covariant ring homomorphism
  `End A →+* Module.End K A.TangentSpace`, and `AbelianVariety.tangentMap_mulBy` computes the
  differential of `[n]` as scalar multiplication by `(n : K)`;
* `AbelianVariety.Hom.formallyUnramified_toSchemeHom_iff` and
  `AbelianVariety.Hom.unramified_toSchemeHom_iff` show that `f` is (formally) unramified if and only
  if `Hom.tangentMap f` is injective;
* `AbelianVariety.Hom.etale_toSchemeHom_iff_bijective_tangentMap` (`Stacks Tag 0BFH`) shows that `f`
  is étale if and only if `Hom.tangentMap f` is bijective, and for endomorphisms `f : A ⟶ A`
  injectivity suffices (`AbelianVariety.Hom.etale_toSchemeHom_end_iff_injective_tangentMap`).

## References

* [The Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [The Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* J. S. Milne, *Abelian Varieties*, I §7.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti.AlgebraicGeometry.AbelianVariety

open scoped Hom

universe u

variable {K : Type u} [Field K]

noncomputable section

/-! ### Preservation of the identity point and residue field -/

/-- The underlying scheme morphism of an abelian-variety homomorphism preserves the zero section. -/
@[simp, reassoc]
theorem Hom.zeroSection_comp_toSchemeHom {A B : AbelianVariety K} (f : A ⟶ B) :
    A.zeroSection ≫ Hom.toSchemeHom f = B.zeroSection :=
  congrArg Over.Hom.left (Hom.one_hom f)

/-- Every homomorphism of abelian varieties sends `0` to `0`. -/
@[simp]
theorem Hom.toSchemeHom_zeroPoint {A B : AbelianVariety K} (f : A ⟶ B) :
    Hom.toSchemeHom f A.zeroPoint = B.zeroPoint :=
  (congrArg (Hom.toSchemeHom f) A.zeroPoint_def).trans <|
    (Scheme.Hom.comp_apply A.zeroSection (Hom.toSchemeHom f)
      (IsLocalRing.closedPoint K)).symm.trans <|
      congr($(Hom.zeroSection_comp_toSchemeHom f) (IsLocalRing.closedPoint K)).trans
        B.zeroPoint_def.symm

/-- The underlying scheme morphism of an abelian-variety homomorphism is locally of finite type. -/
instance Hom.locallyOfFiniteType_toSchemeHom {A B : AbelianVariety K} (f : A ⟶ B) :
    LocallyOfFiniteType (Hom.toSchemeHom f) := by
  have : LocallyOfFiniteType (Hom.toSchemeHom f ≫ B.toOver.hom) := by
    rw [Hom.toSchemeHom_comp_hom]
    infer_instance
  exact locallyOfFiniteType_of_comp (Hom.toSchemeHom f) B.toOver.hom

/-- At the identity point, every homomorphism of abelian varieties induces a bijection on residue
fields. -/
theorem Hom.residueFieldMap_zeroPoint_bijective {A B : AbelianVariety K} (f : A ⟶ B) :
    Function.Bijective ((Hom.toSchemeHom f).residueFieldMap A.zeroPoint) := by
  have hA : A.toOver.hom.residueDegree A.zeroPoint = 1 :=
    (congrArg A.toOver.hom.residueDegree A.zeroPoint_def).trans
      (residueDegree_eq_one_of_section A.zeroSection_comp_toOver_hom _)
  have hB : B.toOver.hom.residueDegree (Hom.toSchemeHom f A.zeroPoint) = 1 :=
    (congrArg B.toOver.hom.residueDegree
      ((Hom.toSchemeHom_zeroPoint f).trans B.zeroPoint_def)).trans
      (residueDegree_eq_one_of_section B.zeroSection_comp_toOver_hom _)
  have hdeg : (Hom.toSchemeHom f).residueDegree A.zeroPoint = 1 := by
    have hmul := (Hom.toSchemeHom f).residueDegree_comp B.toOver.hom A.zeroPoint
    rwa [Hom.toSchemeHom_comp_hom, hA, hB, Nat.one_mul, eq_comm] at hmul
  exact ((Hom.toSchemeHom f).residueDegree_eq_one_iff A.zeroPoint).mp hdeg

/-! ### Infinitesimal points and `T₀A` -/

/-- Forward map of `tangentSpaceSemilinearEquiv`: evaluate `v : T₀A` and identify `κ(0)` with `K`
via `zeroResidueFieldRingEquiv`. -/
private noncomputable def tangentSpaceToSemilinearFun (A : AbelianVariety K) (v : A.TangentSpace) :
    ZariskiCotangentSpace A.toScheme A.zeroPoint
      →ₛₗ[A.zeroResidueFieldRingEquiv.toRingHom] K where
  toFun w := A.zeroResidueFieldRingEquiv (A.tangentSpaceEval v w)
  map_add' w₁ w₂ := by
    rw [tangentSpaceEval_apply, map_add, map_add, ← tangentSpaceEval_apply,
      ← tangentSpaceEval_apply]
  map_smul' r w := by
    rw [tangentSpaceEval_apply, map_smul, smul_eq_mul, map_mul, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, smul_eq_mul, ← tangentSpaceEval_apply]

private lemma tangentSpaceToSemilinearFun_apply (A : AbelianVariety K) (v : A.TangentSpace)
    (w : ZariskiCotangentSpace A.toScheme A.zeroPoint) :
    tangentSpaceToSemilinearFun A v w = A.zeroResidueFieldRingEquiv (A.tangentSpaceEval v w) :=
  rfl

/-- Inverse map of `tangentSpaceSemilinearEquiv` at the level of cotangent functionals. -/
private noncomputable def semilinearFunToDual (A : AbelianVariety K)
    (ℓ : ZariskiCotangentSpace A.toScheme A.zeroPoint
      →ₛₗ[A.zeroResidueFieldRingEquiv.toRingHom] K) :
    Module.Dual (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint))
      (ZariskiCotangentSpace A.toScheme A.zeroPoint) where
  toFun w := A.zeroResidueFieldRingEquiv.symm (ℓ w)
  map_add' w₁ w₂ := by rw [map_add, map_add]
  map_smul' r w := by
    rw [ℓ.map_smulₛₗ, smul_eq_mul, map_mul, smul_eq_mul, RingHom.id_apply]
    exact congrArg (· * _) (A.zeroResidueFieldRingEquiv.symm_apply_apply r)

private lemma semilinearFunToDual_apply (A : AbelianVariety K)
    (ℓ : ZariskiCotangentSpace A.toScheme A.zeroPoint
      →ₛₗ[A.zeroResidueFieldRingEquiv.toRingHom] K)
    (w : ZariskiCotangentSpace A.toScheme A.zeroPoint) :
    semilinearFunToDual A ℓ w = A.zeroResidueFieldRingEquiv.symm (ℓ w) :=
  rfl

/-- Evaluating a tangent vector in `T₀A` and applying `zeroResidueFieldRingEquiv` identifies `T₀A`
`K`-linearly with the `zeroResidueFieldRingEquiv`-semilinear functionals on the Zariski cotangent
space at `0`. -/
private noncomputable def tangentSpaceSemilinearEquiv (A : AbelianVariety K) :
    A.TangentSpace ≃ₗ[K]
      (ZariskiCotangentSpace A.toScheme A.zeroPoint
        →ₛₗ[A.zeroResidueFieldRingEquiv.toRingHom] K) where
  toFun := tangentSpaceToSemilinearFun A
  invFun ℓ := A.tangentSpaceLinearEquiv.symm (semilinearFunToDual A ℓ)
  left_inv v := by
    apply A.tangentSpaceLinearEquiv.injective
    ext w
    rw [LinearEquiv.apply_symm_apply, semilinearFunToDual_apply, tangentSpaceToSemilinearFun_apply,
      RingEquiv.symm_apply_apply, ← tangentSpaceEval_apply]
  right_inv ℓ := by
    ext w
    rw [tangentSpaceToSemilinearFun_apply, tangentSpaceEval_apply, LinearEquiv.apply_symm_apply,
      semilinearFunToDual_apply, RingEquiv.apply_symm_apply]
  map_add' v₁ v₂ := by
    ext w
    rw [tangentSpaceToSemilinearFun_apply, LinearMap.add_apply, tangentSpaceToSemilinearFun_apply,
      tangentSpaceToSemilinearFun_apply, tangentSpaceEval_apply, map_add, LinearMap.add_apply,
      map_add, ← tangentSpaceEval_apply, ← tangentSpaceEval_apply]
  map_smul' c v := by
    ext w
    rw [tangentSpaceToSemilinearFun_apply, RingHom.id_apply, LinearMap.smul_apply,
      tangentSpaceToSemilinearFun_apply, tangentSpace_smul_def, tangentSpaceEval_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, smul_eq_mul,
      ← tangentSpaceEval_apply]

private lemma mapEquiv_stalkCongr_refl {X : Scheme.{u}} (x : X) (w : ZariskiCotangentSpace X x) :
    IsLocalRing.CotangentSpace.mapEquiv
        (X.presheaf.stalkCongr (Inseparable.of_eq (rfl : x = x))).commRingCatIsoToRingEquiv w =
      w := by
  obtain ⟨m, rfl⟩ := (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).toCotangent_surjective w
  rw [IsLocalRing.CotangentSpace.mapEquiv_apply, IsLocalRing.CotangentSpace.map_toCotangent]
  exact congrArg _ (Subtype.ext (by simp [TopCat.Presheaf.stalkCongr]))

/-- Transport of semilinear cotangent functionals along an equality of points `h : x = y`. -/
private noncomputable def cotangentSemilinearCongr {X : Scheme.{u}} {x y : X} (h : x = y)
    (ex : IsLocalRing.ResidueField (X.presheaf.stalk x) ≃+* K)
    (ey : IsLocalRing.ResidueField (X.presheaf.stalk y) ≃+* K)
    (hex : ∀ z, ex z = ey (h ▸ z)) :
    (ZariskiCotangentSpace X x →ₛₗ[ex.toRingHom] K) ≃ₗ[K]
      (ZariskiCotangentSpace X y →ₛₗ[ey.toRingHom] K) := by
  cases h
  have he : ex = ey := RingEquiv.ext hex
  cases he
  exact LinearEquiv.refl K _

private lemma cotangentSemilinearCongr_apply {X : Scheme.{u}} {x y : X} (h : x = y)
    (ex : IsLocalRing.ResidueField (X.presheaf.stalk x) ≃+* K)
    (ey : IsLocalRing.ResidueField (X.presheaf.stalk y) ≃+* K)
    (hex : ∀ z, ex z = ey (h ▸ z))
    (ℓ : ZariskiCotangentSpace X x →ₛₗ[ex.toRingHom] K) (w : ZariskiCotangentSpace X y) :
    cotangentSemilinearCongr h ex ey hex ℓ w =
      ℓ (IsLocalRing.CotangentSpace.mapEquiv
        (X.presheaf.stalkCongr (Inseparable.of_eq h.symm)).commRingCatIsoToRingEquiv w) := by
  cases h
  have he : ex = ey := RingEquiv.ext hex
  cases he
  rw [mapEquiv_stalkCongr_refl]
  rfl

private lemma cotangentSemilinearCongr_symm_apply {X : Scheme.{u}} {x y : X} (h : x = y)
    (ex : IsLocalRing.ResidueField (X.presheaf.stalk x) ≃+* K)
    (ey : IsLocalRing.ResidueField (X.presheaf.stalk y) ≃+* K)
    (hex : ∀ z, ex z = ey (h ▸ z))
    (ℓ : ZariskiCotangentSpace X y →ₛₗ[ey.toRingHom] K) (w : ZariskiCotangentSpace X x) :
    (cotangentSemilinearCongr h ex ey hex).symm ℓ w =
      ℓ (IsLocalRing.CotangentSpace.mapEquiv
        (X.presheaf.stalkCongr (Inseparable.of_eq h)).commRingCatIsoToRingEquiv w) := by
  cases h
  have he : ex = ey := RingEquiv.ext hex
  cases he
  rw [mapEquiv_stalkCongr_refl]
  rfl

private lemma zeroResidueField_eq_section (A : AbelianVariety K)
    (z : IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) :
    A.zeroResidueFieldRingEquiv z =
      residueFieldRingEquivOfSection (overSection_comp_hom η[A.toOver])
        (A.zeroPoint_def ▸ z) :=
  (A.zeroResidueFieldRingEquiv_apply z).trans
    (residueFieldRingEquivOfSection_apply (overSection_comp_hom η[A.toOver]) _).symm

/-- `K`-linear identification of `T₀A` with the semilinear cotangent functionals at
`overSectionHom η[A.toOver] (closedPoint K)`. -/
private noncomputable def tangentSpaceToSectionDual (A : AbelianVariety K) :
    A.TangentSpace ≃ₗ[K]
      (ZariskiCotangentSpace A.toScheme
          (overSectionHom η[A.toOver] (IsLocalRing.closedPoint K))
        →ₛₗ[(residueFieldRingEquivOfSection (overSection_comp_hom η[A.toOver])).toRingHom] K) :=
  (tangentSpaceSemilinearEquiv A).trans <|
    cotangentSemilinearCongr A.zeroPoint_def A.zeroResidueFieldRingEquiv
      (residueFieldRingEquivOfSection (overSection_comp_hom η[A.toOver]))
      (zeroResidueField_eq_section A)

/-- Canonical bijection between `T₀A` and `Spec (TrivSqZeroExt K K)`-points of `A` extending the
identity section. -/
private noncomputable def tangentSpaceEquivPointedOver (A : AbelianVariety K) :
    A.TangentSpace ≃
      {t : trivSqZeroOver K K ⟶ A.toOver // trivSqZeroSection K K ≫ t = η[A.toOver]} :=
  (tangentSpaceToSectionDual A).toEquiv.trans (trivSqZeroPointEquiv A.toOver η[A.toOver] K).symm

private lemma trivSqZeroPointEquiv_tangentSpaceEquivPointedOver (A : AbelianVariety K)
    (v : A.TangentSpace) :
    trivSqZeroPointEquiv A.toOver η[A.toOver] K (tangentSpaceEquivPointedOver A v) =
      tangentSpaceToSectionDual A v :=
  (trivSqZeroPointEquiv A.toOver η[A.toOver] K).apply_symm_apply _

private lemma tangentSpaceToSectionDual_symm_trivSqZeroPointEquiv (A : AbelianVariety K)
    (t : {t : trivSqZeroOver K K ⟶ A.toOver // trivSqZeroSection K K ≫ t = η[A.toOver]}) :
    (tangentSpaceEquivPointedOver A).symm t =
      (tangentSpaceToSectionDual A).symm (trivSqZeroPointEquiv A.toOver η[A.toOver] K t) :=
  rfl

private lemma unit_eq_one_toOver (A : AbelianVariety K) :
    η[A.toOver] = (1 : 𝟙_ (Over (Spec (.of K))) ⟶ A.toOver) := by
  rw [CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

private lemma tangentSpaceEquivPointedOver_add (A : AbelianVariety K) (v₁ v₂ : A.TangentSpace) :
    (tangentSpaceEquivPointedOver A (v₁ + v₂)).1 =
      (tangentSpaceEquivPointedOver A v₁).1 * (tangentSpaceEquivPointedOver A v₂).1 := by
  let t₁ := tangentSpaceEquivPointedOver A v₁
  let t₂ := tangentSpaceEquivPointedOver A v₂
  let prodPt : {t : trivSqZeroOver K K ⟶ A.toOver // trivSqZeroSection K K ≫ t = η[A.toOver]} :=
    ⟨t₁.1 * t₂.1, by
      rw [MonObj.comp_mul, t₁.2, t₂.2, unit_eq_one_toOver A, _root_.mul_one]⟩
  suffices tangentSpaceEquivPointedOver A (v₁ + v₂) = prodPt from congrArg Subtype.val this
  apply (trivSqZeroPointEquiv A.toOver η[A.toOver] K).injective
  rw [trivSqZeroPointEquiv_tangentSpaceEquivPointedOver, map_add,
    trivSqZeroPointEquiv_mul A.toOver t₁ t₂,
    trivSqZeroPointEquiv_tangentSpaceEquivPointedOver,
    trivSqZeroPointEquiv_tangentSpaceEquivPointedOver]

private lemma tangentSpaceEquivPointedOver_smul (A : AbelianVariety K) (c : K)
    (v : A.TangentSpace) :
    (tangentSpaceEquivPointedOver A (c • v)).1 =
      trivSqZeroOverMap (LinearMap.lsmul K K c) ≫ (tangentSpaceEquivPointedOver A v).1 := by
  let t := tangentSpaceEquivPointedOver A v
  let smulPt : {t : trivSqZeroOver K K ⟶ A.toOver // trivSqZeroSection K K ≫ t = η[A.toOver]} :=
    ⟨trivSqZeroOverMap (LinearMap.lsmul K K c) ≫ t.1, by
      rw [trivSqZeroSection_overMap_assoc, t.2]⟩
  suffices tangentSpaceEquivPointedOver A (c • v) = smulPt from congrArg Subtype.val this
  apply (trivSqZeroPointEquiv A.toOver η[A.toOver] K).injective
  ext w
  rw [trivSqZeroPointEquiv_tangentSpaceEquivPointedOver, map_smul, LinearMap.smul_apply,
    trivSqZeroPointEquiv_overMap η[A.toOver] (LinearMap.lsmul K K c) t w, LinearMap.lsmul_apply,
    trivSqZeroPointEquiv_tangentSpaceEquivPointedOver]

/-! ### The induced `K`-linear differential `Hom.tangentMap` -/

/-- Postcompose an infinitesimal point at the identity of `A` with `f : A ⟶ B`. -/
private noncomputable def pointedOverComp {A B : AbelianVariety K} (f : A ⟶ B)
    (t : {t : trivSqZeroOver K K ⟶ A.toOver // trivSqZeroSection K K ≫ t = η[A.toOver]}) :
    {t : trivSqZeroOver K K ⟶ B.toOver // trivSqZeroSection K K ≫ t = η[B.toOver]} :=
  ⟨t.1 ≫ Hom.toOverHom f, by rw [← Category.assoc, t.2, Hom.one_hom]⟩

/-- The `K`-linear differential `df₀ : T₀A →ₗ[K] T₀B` induced at the identity by a homomorphism
`f : A ⟶ B` of abelian varieties. -/
noncomputable def Hom.tangentMap {A B : AbelianVariety K} (f : A ⟶ B) :
    A.TangentSpace →ₗ[K] B.TangentSpace where
  toFun v := (tangentSpaceEquivPointedOver B).symm
    (pointedOverComp f (tangentSpaceEquivPointedOver A v))
  map_add' v₁ v₂ := by
    let t₁ := tangentSpaceEquivPointedOver A v₁
    let t₂ := tangentSpaceEquivPointedOver A v₂
    have hcomp : pointedOverComp f (tangentSpaceEquivPointedOver A (v₁ + v₂)) =
        ⟨(pointedOverComp f t₁).1 * (pointedOverComp f t₂).1, by
          rw [MonObj.comp_mul, (pointedOverComp f t₁).2, (pointedOverComp f t₂).2,
            unit_eq_one_toOver B, _root_.mul_one]⟩ :=
      Subtype.ext <| by
        dsimp [pointedOverComp]
        rw [tangentSpaceEquivPointedOver_add, MonObj.mul_comp]
    rw [hcomp, tangentSpaceToSectionDual_symm_trivSqZeroPointEquiv,
      trivSqZeroPointEquiv_mul B.toOver (pointedOverComp f t₁) (pointedOverComp f t₂), map_add]
    rfl
  map_smul' c v := by
    let t := tangentSpaceEquivPointedOver A v
    have hcomp : pointedOverComp f (tangentSpaceEquivPointedOver A (c • v)) =
        ⟨trivSqZeroOverMap (LinearMap.lsmul K K c) ≫ (pointedOverComp f t).1, by
          rw [trivSqZeroSection_overMap_assoc, (pointedOverComp f t).2]⟩ :=
      Subtype.ext <| by
        dsimp [pointedOverComp]
        rw [tangentSpaceEquivPointedOver_smul, Category.assoc]
    rw [RingHom.id_apply, hcomp, tangentSpaceToSectionDual_symm_trivSqZeroPointEquiv]
    have hsmul : trivSqZeroPointEquiv B.toOver η[B.toOver] K
        ⟨trivSqZeroOverMap (LinearMap.lsmul K K c) ≫ (pointedOverComp f t).1, by
          rw [trivSqZeroSection_overMap_assoc, (pointedOverComp f t).2]⟩ =
        c • trivSqZeroPointEquiv B.toOver η[B.toOver] K (pointedOverComp f t) := by
      ext w
      exact trivSqZeroPointEquiv_overMap η[B.toOver] (LinearMap.lsmul K K c) (pointedOverComp f t) w
    rw [hsmul, map_smul]
    rfl

/-- Point-transport coherence for `Scheme.Hom.zariskiCotangentMap`. -/
private lemma zariskiCotangentMap_congr_points {X Y : Scheme.{u}} (g : X ⟶ Y)
    {x x' : X} {y y' : Y} (hx : x = x') (hy : y = y') (hyx : y = g x) (hyx' : y' = g x')
    (w : ZariskiCotangentSpace Y y) :
    IsLocalRing.CotangentSpace.mapEquiv
        (X.presheaf.stalkCongr (Inseparable.of_eq hx.symm)).commRingCatIsoToRingEquiv
        (g.zariskiCotangentMap x'
          (IsLocalRing.CotangentSpace.mapEquiv
            (Y.presheaf.stalkCongr (Inseparable.of_eq hyx')).commRingCatIsoToRingEquiv
            (IsLocalRing.CotangentSpace.mapEquiv
              (Y.presheaf.stalkCongr (Inseparable.of_eq hy)).commRingCatIsoToRingEquiv w))) =
      g.zariskiCotangentMap x
        (IsLocalRing.CotangentSpace.mapEquiv
          (Y.presheaf.stalkCongr (Inseparable.of_eq hyx)).commRingCatIsoToRingEquiv w) := by
  cases hx
  cases hy
  rw [mapEquiv_stalkCongr_refl, mapEquiv_stalkCongr_refl]

/-- `Hom.tangentMap f` is dual to `(Hom.toSchemeHom f).zariskiCotangentMap A.zeroPoint` under the
residue-field identifications `zeroResidueFieldRingEquiv`. -/
theorem Hom.zeroResidueFieldRingEquiv_tangentSpaceEval_tangentMap {A B : AbelianVariety K}
    (f : A ⟶ B) (v : A.TangentSpace) (w : ZariskiCotangentSpace B.toScheme B.zeroPoint) :
    B.zeroResidueFieldRingEquiv (B.tangentSpaceEval (Hom.tangentMap f v) w) =
      A.zeroResidueFieldRingEquiv
        (A.tangentSpaceEval v
          ((Hom.toSchemeHom f).zariskiCotangentMap A.zeroPoint
            (IsLocalRing.CotangentSpace.mapEquiv
              (B.toScheme.presheaf.stalkCongr
                (Inseparable.of_eq (Hom.toSchemeHom_zeroPoint f).symm)).commRingCatIsoToRingEquiv
              w))) := by
  have hB : tangentSpaceSemilinearEquiv B (Hom.tangentMap f v) w =
      (cotangentSemilinearCongr B.zeroPoint_def B.zeroResidueFieldRingEquiv
        (residueFieldRingEquivOfSection (overSection_comp_hom η[B.toOver]))
        (zeroResidueField_eq_section B)).symm
        (trivSqZeroPointEquiv B.toOver η[B.toOver] K
          (pointedOverComp f (tangentSpaceEquivPointedOver A v))) w := by
    -- Unfold `Hom.tangentMap` and cancel `tangentSpaceSemilinearEquiv B` against its inverse.
    change tangentSpaceSemilinearEquiv B
      ((tangentSpaceSemilinearEquiv B).symm _) w = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  refine hB.trans ?_
  rw [cotangentSemilinearCongr_symm_apply]
  refine (trivSqZeroPointEquiv_comp_of_eq η[A.toOver] η[B.toOver] (Hom.toOverHom f)
    (Hom.one_hom f) (tangentSpaceEquivPointedOver A v) _).trans ?_
  rw [trivSqZeroPointEquiv_tangentSpaceEquivPointedOver]
  dsimp only [tangentSpaceToSectionDual, LinearEquiv.trans_apply]
  exact (cotangentSemilinearCongr_apply A.zeroPoint_def A.zeroResidueFieldRingEquiv
    (residueFieldRingEquivOfSection (overSection_comp_hom η[A.toOver]))
    (zeroResidueField_eq_section A) (tangentSpaceSemilinearEquiv A v) _).trans
    (congrArg (tangentSpaceSemilinearEquiv A v)
      (zariskiCotangentMap_congr_points (Hom.toSchemeHom f) A.zeroPoint_def B.zeroPoint_def
        (Hom.toSchemeHom_zeroPoint f).symm
        ((congr($(Hom.zeroSection_comp_toSchemeHom f)
          (IsLocalRing.closedPoint K))).symm.trans
          (Scheme.Hom.comp_apply A.zeroSection (Hom.toSchemeHom f)
            (IsLocalRing.closedPoint K))) w))

/-! ### Functoriality and additivity of `Hom.tangentMap` -/

/-- The identity homomorphism induces the identity map on `T₀A`. -/
@[simp]
theorem Hom.tangentMap_id (A : AbelianVariety K) :
    Hom.tangentMap (𝟙 A) = LinearMap.id := by
  ext v
  have hcomp : pointedOverComp (𝟙 A) (tangentSpaceEquivPointedOver A v) =
      tangentSpaceEquivPointedOver A v :=
    Subtype.ext <| by
      dsimp [pointedOverComp]
      rw [Hom.toOverHom_id, Category.comp_id]
  exact (congrArg (tangentSpaceEquivPointedOver A).symm hcomp).trans
    ((tangentSpaceEquivPointedOver A).symm_apply_apply v)

private lemma tangentMap_def {A B : AbelianVariety K} (f : A ⟶ B) (v : A.TangentSpace) :
    Hom.tangentMap f v =
      (tangentSpaceEquivPointedOver B).symm
        (pointedOverComp f (tangentSpaceEquivPointedOver A v)) :=
  rfl

/-- `Hom.tangentMap` is covariantly functorial under composition of homomorphisms. -/
@[simp]
theorem Hom.tangentMap_comp {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.tangentMap (f ≫ g) = (Hom.tangentMap g).comp (Hom.tangentMap f) := by
  ext v
  rw [LinearMap.comp_apply, tangentMap_def, tangentMap_def, tangentMap_def,
    Equiv.apply_symm_apply]
  refine congrArg (tangentSpaceEquivPointedOver C).symm (Subtype.ext ?_)
  dsimp only [pointedOverComp]
  rw [Hom.toOverHom_comp, Category.assoc]

/-- The trivial homomorphism `1 : A ⟶ B` induces the zero linear map on tangent spaces. -/
@[simp]
theorem Hom.tangentMap_one (A B : AbelianVariety K) :
    Hom.tangentMap (1 : A ⟶ B) = 0 := by
  ext v
  have hcomp : pointedOverComp (1 : A ⟶ B) (tangentSpaceEquivPointedOver A v) =
      ⟨1, by
        rw [CategoryTheory.Hom.one_def, ← Category.assoc,
          toUnit_unique (trivSqZeroSection K K ≫ toUnit _) (𝟙 _), Category.id_comp]⟩ :=
    Subtype.ext <| by simp [pointedOverComp, Hom.toOverHom_one]
  rw [LinearMap.zero_apply, tangentMap_def, hcomp,
    tangentSpaceToSectionDual_symm_trivSqZeroPointEquiv, trivSqZeroPointEquiv_one, map_zero]

/-- **Stacks Project, Tag 0BFG.** Multiplying two homomorphisms `f, g : A ⟶ B` for the pointwise
group law adds their differentials `Hom.tangentMap f + Hom.tangentMap g` on `T₀A`. -/
@[stacks 0BFG, simp]
theorem Hom.tangentMap_mul {A B : AbelianVariety K} (f g : A ⟶ B) :
    Hom.tangentMap (f * g) = Hom.tangentMap f + Hom.tangentMap g := by
  ext v
  let tf := pointedOverComp f (tangentSpaceEquivPointedOver A v)
  let tg := pointedOverComp g (tangentSpaceEquivPointedOver A v)
  have hcomp : pointedOverComp (f * g) (tangentSpaceEquivPointedOver A v) =
      ⟨tf.1 * tg.1, by
        rw [MonObj.comp_mul, tf.2, tg.2, unit_eq_one_toOver B, _root_.mul_one]⟩ :=
    Subtype.ext <| by simp [pointedOverComp, tf, tg, Hom.toOverHom_mul, MonObj.comp_mul]
  rw [LinearMap.add_apply, tangentMap_def, hcomp,
    tangentSpaceToSectionDual_symm_trivSqZeroPointEquiv,
    trivSqZeroPointEquiv_mul B.toOver tf tg, map_add]
  rfl

/-- `Hom.tangentMap` bundled as an additive group homomorphism out of `Additive (A ⟶ B)`. -/
noncomputable def Hom.tangentMapAddMonoidHom (A B : AbelianVariety K) :
    Additive (A ⟶ B) →+ (A.TangentSpace →ₗ[K] B.TangentSpace) where
  toFun x := Hom.tangentMap (Additive.toMul x)
  map_zero' := by rw [_root_.toMul_zero, Hom.tangentMap_one]
  map_add' x y := by rw [_root_.toMul_add, Hom.tangentMap_mul]

/-- The pointwise inverse of a homomorphism negates its differential on `T₀A`. -/
@[simp]
theorem Hom.tangentMap_inv {A B : AbelianVariety K} (f : A ⟶ B) :
    Hom.tangentMap f⁻¹ = -Hom.tangentMap f :=
  _root_.map_neg (Hom.tangentMapAddMonoidHom A B) (Additive.ofMul f)

/-- The pointwise quotient of two homomorphisms subtracts their differentials on `T₀A`. -/
@[simp]
theorem Hom.tangentMap_div {A B : AbelianVariety K} (f g : A ⟶ B) :
    Hom.tangentMap (f / g) = Hom.tangentMap f - Hom.tangentMap g :=
  _root_.map_sub (Hom.tangentMapAddMonoidHom A B) (Additive.ofMul f) (Additive.ofMul g)

/-- Taking the `n`-th pointwise power of a homomorphism multiplies its differential by `n`. -/
@[simp]
theorem Hom.tangentMap_zpow {A B : AbelianVariety K} (f : A ⟶ B) (n : ℤ) :
    Hom.tangentMap (f ^ n) = n • Hom.tangentMap f :=
  _root_.map_zsmul (Hom.tangentMapAddMonoidHom A B) n (Additive.ofMul f)

/-! ### Action of the endomorphism ring and multiplication by `n` -/

/-- Sending an endomorphism of `A` to its differential at `0` is a covariant ring homomorphism
`End A →+* Module.End K A.TangentSpace`. -/
noncomputable def End.tangentRingHom (A : AbelianVariety K) :
    End A →+* Module.End K A.TangentSpace where
  toFun x := Hom.tangentMap (End.toHom x)
  map_one' := by rw [End.toHom_one, Hom.tangentMap_id]; rfl
  map_mul' x y := by rw [End.toHom_mul, Hom.tangentMap_comp]; rfl
  map_zero' := by rw [End.toHom_zero, Hom.tangentMap_one]
  map_add' x y := by rw [End.toHom_add, Hom.tangentMap_mul]

/-- `End.tangentRingHom A` acts on `x : End A` as `Hom.tangentMap (End.toHom x)`. -/
@[simp]
theorem End.tangentRingHom_apply (A : AbelianVariety K) (x : End A) :
    End.tangentRingHom A x = Hom.tangentMap (End.toHom x) :=
  (rfl)

/-- Multiplication by `n : ℤ` on an abelian variety `A` over `K` acts on `T₀A` as scalar
multiplication by `(n : K)`. -/
@[simp]
theorem tangentMap_mulBy (A : AbelianVariety K) (n : ℤ) :
    Hom.tangentMap (mulBy A n) = (n : K) • LinearMap.id := by
  rw [← End.toHom_ofHom (mulBy A n), End.ofHom_mulBy, ← End.tangentRingHom_apply, map_intCast]
  ext v
  simp [← Int.cast_smul_eq_zsmul K]

/-! ### Differential criteria for unramified and étale homomorphisms -/

private lemma tangentSpace_eq_zero_of_forall_eval (A : AbelianVariety K) (v : A.TangentSpace)
    (h : ∀ w, A.zeroResidueFieldRingEquiv (A.tangentSpaceEval v w) = 0) :
    v = 0 := by
  apply A.tangentSpaceLinearEquiv.injective
  ext w
  rw [map_zero, LinearMap.zero_apply, ← tangentSpaceEval_apply]
  exact A.zeroResidueFieldRingEquiv.injective ((h w).trans (map_zero _).symm)

/-- `Hom.tangentMap f` is injective if and only if `(Hom.toSchemeHom f).zariskiCotangentMap` at `0`
is surjective. -/
theorem Hom.injective_tangentMap_iff_surjective_zariskiCotangentMap {A B : AbelianVariety K}
    (f : A ⟶ B) :
    Function.Injective (Hom.tangentMap f) ↔
      Function.Surjective ((Hom.toSchemeHom f).zariskiCotangentMap A.zeroPoint) := by
  let eB := (B.toScheme.presheaf.stalkCongr
    (Inseparable.of_eq (Hom.toSchemeHom_zeroPoint f).symm)).commRingCatIsoToRingEquiv
  have : RingHomSurjective
      ((IsLocalRing.ResidueField.map ((Hom.toSchemeHom f).stalkMap A.zeroPoint).hom).comp
        (IsLocalRing.ResidueField.map (RingHomClass.toRingHom eB))) :=
    ⟨(Hom.residueFieldMap_zeroPoint_bijective f).2.comp
      (IsLocalRing.ResidueField.mapEquiv eB).surjective⟩
  have : RingHomCompTriple
      (IsLocalRing.ResidueField.map (RingHomClass.toRingHom eB))
      (IsLocalRing.ResidueField.map ((Hom.toSchemeHom f).stalkMap A.zeroPoint).hom)
      ((IsLocalRing.ResidueField.map ((Hom.toSchemeHom f).stalkMap A.zeroPoint).hom).comp
        (IsLocalRing.ResidueField.map (RingHomClass.toRingHom eB))) :=
    ⟨rfl⟩
  let C := ((Hom.toSchemeHom f).zariskiCotangentMap A.zeroPoint).comp
    (IsLocalRing.CotangentSpace.mapEquiv eB).toLinearMap
  rw [← (IsLocalRing.CotangentSpace.mapEquiv eB).surjective.of_comp_iff
    ((Hom.toSchemeHom f).zariskiCotangentMap A.zeroPoint)]
  refine ⟨fun hinj ↦ by_contra fun hnsurj ↦ ?_, fun hsurj ↦ ?_⟩
  · have hlt : LinearMap.range C < ⊤ := lt_top_iff_ne_top.mpr (mt LinearMap.range_eq_top.mp hnsurj)
    obtain ⟨φ, hφ0, hφbot⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    let v : A.TangentSpace := A.tangentSpaceLinearEquiv.symm φ
    have hv0 : v ≠ 0 := fun hv ↦ hφ0 (A.tangentSpaceLinearEquiv.symm.injective (hv.trans
      (map_zero _).symm))
    refine hv0 (hinj ((tangentSpace_eq_zero_of_forall_eval B (Hom.tangentMap f v) fun w ↦ ?_).trans
      (map_zero _).symm))
    rw [Hom.zeroResidueFieldRingEquiv_tangentSpaceEval_tangentMap]
    have hCw : φ (C w) = 0 := by
      have hmem : φ (C w) ∈ Submodule.map φ (LinearMap.range C) :=
        Submodule.mem_map_of_mem (LinearMap.mem_range_self C w)
      rwa [hφbot, Submodule.mem_bot] at hmem
    have heval : A.tangentSpaceEval v (C w) = φ (C w) := by
      rw [tangentSpaceEval_apply]
      exact congrFun (congrArg DFunLike.coe (A.tangentSpaceLinearEquiv.apply_symm_apply φ)) (C w)
    exact (congrArg A.zeroResidueFieldRingEquiv (heval.trans hCw)).trans (map_zero _)
  · rw [injective_iff_map_eq_zero]
    intro v hv
    refine tangentSpace_eq_zero_of_forall_eval A v fun u ↦ ?_
    obtain ⟨w, rfl⟩ := hsurj u
    have h0 : B.tangentSpaceEval (Hom.tangentMap f v) w = 0 := by
      rw [hv, tangentSpaceEval_apply, map_zero, LinearMap.zero_apply]
    exact (Hom.zeroResidueFieldRingEquiv_tangentSpaceEval_tangentMap f v w).symm.trans
      ((congrArg B.zeroResidueFieldRingEquiv h0).trans (map_zero _))

private lemma stalkMap_formallyUnramified_congr {X Y : Scheme.{u}} (g : X ⟶ Y) {x x' : X}
    (h : x = x') :
    (g.stalkMap x).hom.FormallyUnramified ↔ (g.stalkMap x').hom.FormallyUnramified := by
  cases h
  rfl

/-- A homomorphism `f : A ⟶ B` of abelian varieties is formally unramified if and only if its
differential `Hom.tangentMap f : T₀A →ₗ[K] T₀B` is injective. -/
theorem Hom.formallyUnramified_toSchemeHom_iff {A B : AbelianVariety K} (f : A ⟶ B) :
    FormallyUnramified (Hom.toSchemeHom f) ↔ Function.Injective (Hom.tangentMap f) :=
  (formallyUnramified_iff_stalkMap_unit (Hom.toOverHom f)).trans <|
    (stalkMap_formallyUnramified_congr (Hom.toSchemeHom f) A.zeroPoint_def.symm).trans <|
      ((Hom.toSchemeHom f).formallyUnramified_stalkMap_iff_zariskiCotangentMap_surjective
        A.zeroPoint (Hom.residueFieldMap_zeroPoint_bijective f).2).trans
        (Hom.injective_tangentMap_iff_surjective_zariskiCotangentMap f).symm

/-- A homomorphism `f : A ⟶ B` of abelian varieties is unramified if and only if its differential
`Hom.tangentMap f : T₀A →ₗ[K] T₀B` is injective. -/
theorem Hom.unramified_toSchemeHom_iff {A B : AbelianVariety K} (f : A ⟶ B) :
    Unramified (Hom.toSchemeHom f) ↔ Function.Injective (Hom.tangentMap f) := by
  rw [unramified_iff, and_iff_right (Hom.locallyOfFiniteType_toSchemeHom f),
    Hom.formallyUnramified_toSchemeHom_iff]

/-- If `B.dim ≤ A.dim` and `Hom.tangentMap f` is injective, then `f : A ⟶ B` is étale. -/
theorem Hom.etale_toSchemeHom_of_injective_tangentMap {A B : AbelianVariety K} (f : A ⟶ B)
    (hdim : B.dim ≤ A.dim) (hinj : Function.Injective (Hom.tangentMap f)) :
    Etale (Hom.toSchemeHom f) := by
  have hfu_hom : FormallyUnramified (Hom.toSchemeHom f) :=
    (Hom.formallyUnramified_toSchemeHom_iff f).mpr hinj
  have hfu : ((Hom.toSchemeHom f).stalkMap A.zeroPoint).hom.FormallyUnramified :=
    (stalkMap_formallyUnramified_congr (Hom.toSchemeHom f) A.zeroPoint_def.symm).mp
      ((formallyUnramified_iff_stalkMap_unit (Hom.toOverHom f)).mp hfu_hom)
  have : IsRegularLocalRing (B.toScheme.presheaf.stalk (Hom.toSchemeHom f A.zeroPoint)) :=
    isRegularLocalRing_stalk_of_smooth B.toOver.hom _
  have hdimA : ringKrullDim (A.toScheme.presheaf.stalk A.zeroPoint) = A.dim :=
    ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed A.toOver.hom
      A.isClosed_singleton_zeroPoint
  have hdimB :
      ringKrullDim (B.toScheme.presheaf.stalk (Hom.toSchemeHom f A.zeroPoint)) = B.dim := by
    rw [Hom.toSchemeHom_zeroPoint]
    exact ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed B.toOver.hom
      B.isClosed_singleton_zeroPoint
  have hstalk_le : ringKrullDim (B.toScheme.presheaf.stalk (Hom.toSchemeHom f A.zeroPoint)) ≤
      ringKrullDim (A.toScheme.presheaf.stalk A.zeroPoint) := by
    rwa [hdimA, hdimB]
  obtain ⟨U, hU₀, hEtU⟩ :=
    (Hom.toSchemeHom f).exists_etale_of_formallyUnramified_stalkMap_of_ringKrullDim_le hfu hstalk_le
  exact (etale_iff_exists_etale_unit (Hom.toOverHom f)).mpr ⟨U, A.zeroPoint_def ▸ hU₀, hEtU⟩

/-- An étale homomorphism of abelian varieties preserves Krull dimension. -/
theorem Hom.dim_eq_of_etale {A B : AbelianVariety K} (f : A ⟶ B) [Etale (Hom.toSchemeHom f)] :
    A.dim = B.dim := by
  have hstalk := (Hom.toSchemeHom f).ringKrullDim_stalk_eq_of_etale A.zeroPoint
  rw [Hom.toSchemeHom_zeroPoint,
    ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed B.toOver.hom
      B.isClosed_singleton_zeroPoint,
    ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed A.toOver.hom
      A.isClosed_singleton_zeroPoint] at hstalk
  exact hstalk.symm

/-- **Stacks Project, Tag 0BFH.** A homomorphism `f : A ⟶ B` of abelian varieties over a field `K`
is étale if and only if its differential `Hom.tangentMap f : T₀A →ₗ[K] T₀B` is bijective. -/
@[stacks 0BFH]
theorem Hom.etale_toSchemeHom_iff_bijective_tangentMap {A B : AbelianVariety K} (f : A ⟶ B) :
    Etale (Hom.toSchemeHom f) ↔ Function.Bijective (Hom.tangentMap f) := by
  refine ⟨fun hEt ↦ ?_, fun hbij ↦ ?_⟩
  · have hinj : Function.Injective (Hom.tangentMap f) :=
      (Hom.formallyUnramified_toSchemeHom_iff f).mp inferInstance
    have hdim_cast : (Module.finrank K A.TangentSpace : WithBot ℕ∞) =
        (Module.finrank K B.TangentSpace : WithBot ℕ∞) := by
      rw [finrank_tangentSpace_eq_dim, finrank_tangentSpace_eq_dim]
      exact Hom.dim_eq_of_etale f
    have hfinrank : Module.finrank K A.TangentSpace = Module.finrank K B.TangentSpace := by
      exact_mod_cast hdim_cast
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mp hinj⟩
  · have hfinrank : Module.finrank K A.TangentSpace = Module.finrank K B.TangentSpace :=
      (LinearEquiv.ofBijective (Hom.tangentMap f) hbij).finrank_eq
    have hdim : B.dim ≤ A.dim := by
      rw [← finrank_tangentSpace_eq_dim, ← finrank_tangentSpace_eq_dim, hfinrank]
    exact Hom.etale_toSchemeHom_of_injective_tangentMap f hdim hbij.1

/-- Between abelian varieties of the same dimension, a homomorphism is étale if and only if its
differential at `0` is injective. -/
theorem Hom.etale_toSchemeHom_iff_injective_tangentMap_of_dim_eq {A B : AbelianVariety K}
    (f : A ⟶ B) (hdim : A.dim = B.dim) :
    Etale (Hom.toSchemeHom f) ↔ Function.Injective (Hom.tangentMap f) :=
  ⟨fun _ ↦ (Hom.formallyUnramified_toSchemeHom_iff f).mp inferInstance,
    Hom.etale_toSchemeHom_of_injective_tangentMap f hdim.symm.le⟩

/-- An endomorphism `f : A ⟶ A` of an abelian variety is étale if and only if its differential on
`T₀A` is injective. -/
theorem Hom.etale_toSchemeHom_end_iff_injective_tangentMap {A : AbelianVariety K} (f : A ⟶ A) :
    Etale (Hom.toSchemeHom f) ↔ Function.Injective (Hom.tangentMap f) :=
  Hom.etale_toSchemeHom_iff_injective_tangentMap_of_dim_eq f rfl

end

end TauCeti.AlgebraicGeometry.AbelianVariety
