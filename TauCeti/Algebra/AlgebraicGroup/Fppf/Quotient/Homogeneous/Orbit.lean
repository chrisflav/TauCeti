/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.SchemeAction
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Classification
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Homogeneous
public import TauCeti.AlgebraicGeometry.IdealSheaf.Section
import TauCeti.AlgebraicGeometry.Geometrically.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Homogeneous orbit schemes and fppf homogeneous quotients

Let `G = Spec H` be an affine group scheme over a commutative ring `R`, acting on a scheme `X`
over `Spec R`. Building on `TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.SchemeAction`,
this file connects the scheme-theoretic orbit-and-stabilizer API (`TauCeti.SchemeAction`) with
the fppf homogeneous-quotient API (`CommHopfAlgCat`):

* For a closed section `x : 𝟙_ (Over (Spec R)) ⟶ X`, the scheme-theoretic stabilizer
  `stabilizer G.X x` is a closed subgroup scheme `stabilizerClosedSubgroup H x`, corresponding
  via `hopfIdealOrderIsoClosedSubgroup` to the Hopf ideal `stabilizerHopfIdeal H x`. Its
  `A`-valued points are precisely the `A`-points of `G` fixing `x`, and the stabilizer ideal of
  a translate `g • x` is the `g`-conjugate of `stabilizerHopfIdeal H x`.
* Over a field `k`, when `G` is finite type and geometrically reduced and `X` is finite type, the
  locally closed orbit scheme `orbitOver G.X x` represents
  `fppfHomogeneousQuotient H (stabilizerHopfIdeal H x)`. Consequently, when `X` is reduced and
  `orbit G.X x = Set.univ`, `X` itself represents `fppfHomogeneousQuotient H`
  `(stabilizerHopfIdeal H x)` with `orbitMap G.X x` as quotient projection, and is equivariantly
  isomorphic to every other scheme representing that quotient (including a projective orbit over
  an algebraically closed field when `H` is reduced).

## Main declarations

* `CommHopfAlgCat.stabilizerClosedSubgroup`, `CommHopfAlgCat.stabilizerHopfIdeal`,
  `CommHopfAlgCat.quotientSpecStabilizerIso`: the Hopf ideal and closed subgroup scheme of a
  scheme-theoretic stabilizer.
* `CommHopfAlgCat.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff`: `A`-points of
  `stabilizerHopfIdeal H x` match `stabilizerPoints`.
* `CommHopfAlgCat.stabilizerHopfIdeal_smul`: conjugation formula for stabilizers of translates.
* `CommHopfAlgCat.orbitOverQuotientIsoPointsSheaf`,
  `CommHopfAlgCat.orbitQuotientIsoPointsSheaf`, `CommHopfAlgCat.orbitQuotientIso`: orbit schemes
  and homogeneous `G`-schemes represent fppf homogeneous quotients by stabilizer Hopf ideals.
* `CommHopfAlgCat.exists_projectiveOrbit_orbitQuotientIso`: over an algebraically closed field,
  every reduced homogeneous `G`-scheme of finite type is equivariantly isomorphic to a projective
  orbit scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§5.c, 7.c–7.f.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§14–16.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ModObj
  AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat TauCeti.SchemeAction

universe u

section StabilizerHopfIdeal

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)
  {X : Over (Spec (CommRingCat.of R))}
  [ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) X]
  (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ X) [IsClosedImmersion x.left]

/-- The scheme-theoretic stabilizer of a closed section `x`, packaged as a closed subgroup scheme
of `Spec H`. -/
def stabilizerClosedSubgroup :
    ClosedSubgroupScheme ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H)) :=
  let f : Grp.mk (stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x) ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H) :=
    Grp.homMk (A := Grp.mk _)
      (B := Grp.mk ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))))
      (stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x)
  letI : IsClosedImmersion f.hom.hom.left := by
    change IsClosedImmersion
      (stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x).left
    infer_instance
  ClosedSubgroupScheme.mk f

/-- The Hopf ideal of `H` cutting out the scheme-theoretic stabilizer of a closed section `x`. -/
def stabilizerHopfIdeal : HopfIdeal R H :=
  OrderDual.ofDual ((hopfIdealOrderIsoClosedSubgroup H).symm (stabilizerClosedSubgroup H x))

/-- The quotient closed subgroup cut out by `stabilizerHopfIdeal H x` is `stabilizerClosedSubgroup H
x`. -/
@[simp]
theorem quotientClosedSubgroup_stabilizerHopfIdeal :
    quotientClosedSubgroup H (stabilizerHopfIdeal H x) = stabilizerClosedSubgroup H x :=
  hopfIdealOrderIsoClosedSubgroup_apply_symm_apply H (stabilizerClosedSubgroup H x)

/-- Canonical isomorphism of group schemes over `Spec R` identifying
`Spec (H ⧸ stabilizerHopfIdeal H x)` with the scheme-theoretic stabilizer of `x`. -/
def quotientSpecStabilizerIso :
    quotientSpec H (stabilizerHopfIdeal H x) ≅
      Grp.mk (stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x) :=
  let f : Grp.mk (stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x) ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H) :=
    Grp.homMk (A := Grp.mk _)
      (B := Grp.mk ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))))
      (stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x)
  letI : IsClosedImmersion f.hom.hom.left := by
    change IsClosedImmersion
      (stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x).left
    infer_instance
  let hq : ClosedSubgroupScheme.mk (quotientSpecι H (stabilizerHopfIdeal H x)) =
      stabilizerClosedSubgroup H x :=
    (quotientClosedSubgroup_def H (stabilizerHopfIdeal H x)).symm.trans
      (quotientClosedSubgroup_stabilizerHopfIdeal H x)
  (ClosedSubgroupScheme.mkIso (quotientSpecι H (stabilizerHopfIdeal H x))).symm ≪≫
    eqToIso (congrArg
      (fun P : ClosedSubgroupScheme
          ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H)) ↦
        (P.val : Grp (Over (Spec (CommRingCat.of R)))))
      hq) ≪≫
    ClosedSubgroupScheme.mkIso f

/-- The inverse of `quotientSpecStabilizerIso` commutes with the subgroup inclusions into `Spec H`.
-/
@[reassoc (attr := simp)]
theorem quotientSpecStabilizerIso_inv_comp_quotientSpecι :
    (quotientSpecStabilizerIso H x).inv.hom.hom ≫
        (quotientSpecι H (stabilizerHopfIdeal H x)).hom.hom =
      stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x := by
  let f : Grp.mk (stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x) ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H) :=
    Grp.homMk (A := Grp.mk _)
      (B := Grp.mk ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))))
      (stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x)
  have : IsClosedImmersion f.hom.hom.left := by
    change IsClosedImmersion
      (stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x).left
    infer_instance
  have hq : ClosedSubgroupScheme.mk (quotientSpecι H (stabilizerHopfIdeal H x)) =
      stabilizerClosedSubgroup H x :=
    (quotientClosedSubgroup_def H (stabilizerHopfIdeal H x)).symm.trans
      (quotientClosedSubgroup_stabilizerHopfIdeal H x)
  have heq : (eqToIso (congrArg
      (fun P : ClosedSubgroupScheme
          ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H)) ↦
        (P.val : Grp (Over (Spec (CommRingCat.of R)))))
      hq)).inv ≫
      (ClosedSubgroupScheme.mkIso (quotientSpecι H (stabilizerHopfIdeal H x))).hom ≫
      quotientSpecι H (stabilizerHopfIdeal H x) = (stabilizerClosedSubgroup H x).val.arrow := by
    have hinv : (ClosedSubgroupScheme.mkIso (quotientSpecι H (stabilizerHopfIdeal H x))).hom ≫
        quotientSpecι H (stabilizerHopfIdeal H x) =
        (ClosedSubgroupScheme.mk (quotientSpecι H (stabilizerHopfIdeal H x))).val.arrow := by
      calc (ClosedSubgroupScheme.mkIso (quotientSpecι H (stabilizerHopfIdeal H x))).hom ≫
            quotientSpecι H (stabilizerHopfIdeal H x)
          = (ClosedSubgroupScheme.mkIso (quotientSpecι H (stabilizerHopfIdeal H x))).hom ≫
              (ClosedSubgroupScheme.mkIso (quotientSpecι H (stabilizerHopfIdeal H x))).inv ≫
                (ClosedSubgroupScheme.mk
                  (quotientSpecι H (stabilizerHopfIdeal H x))).val.arrow := by
            rw [ClosedSubgroupScheme.mkIso_inv_comp_arrow]
        _ = _ := by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [hinv]
    exact Subobject.arrow_congr _ _ (congrArg Subtype.val hq.symm)
  have hgrp : (quotientSpecStabilizerIso H x).inv ≫ quotientSpecι H (stabilizerHopfIdeal H x) =
      f := by
    dsimp only [quotientSpecStabilizerIso]
    erw [Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, Category.assoc, Category.assoc, heq]
    exact ClosedSubgroupScheme.mkIso_inv_comp_arrow f
  exact congrArg (fun φ ↦ φ.hom.hom) hgrp

/-- `quotientSpecStabilizerIso` commutes with the subgroup inclusions into `Spec H`. -/
@[reassoc (attr := simp)]
theorem quotientSpecStabilizerIso_hom_incl :
    (quotientSpecStabilizerIso H x).hom.hom.hom ≫
        stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x =
      (quotientSpecι H (stabilizerHopfIdeal H x)).hom.hom := by
  rw [← quotientSpecStabilizerIso_inv_comp_quotientSpecι H x]
  have hid : (quotientSpecStabilizerIso H x).hom.hom.hom ≫
      (quotientSpecStabilizerIso H x).inv.hom.hom = 𝟙 _ :=
    congrArg (fun φ ↦ φ.hom.hom) (quotientSpecStabilizerIso H x).hom_inv_id
  erw [← Category.assoc, hid, Category.id_comp]

private theorem mapMulEquiv_quotientPointsHom
    (I : HopfIdeal R H) (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    Spec.mapMulEquiv (quotientPointsHom H I A q) =
      Spec.mapMulEquiv q ≫ (quotientSpecι H I).hom.hom := by
  have hdom : quotientPointsHom H I A q = BialgHom.mapDomain (mkQuotient H I).hom q := by
    apply WithConv.ofConv_injective
    rw [quotientPointsHom_apply, BialgHom.mapDomain_apply]
  rw [hdom, TauCeti.CommHopfAlgCat.mapMulEquiv_mapDomain, quotientSpecι_def]
  rfl

private theorem exists_quotientPointsHom_of_comp_quotientSpecι
    (I : HopfIdeal R H) (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R) (H := H) A)
    (s' : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (quotientSpec H I).X)
    (hs' : s' ≫ (quotientSpecι H I).hom.hom = Spec.mapMulEquiv g) :
    ∃ q, quotientPointsHom H I A q = g := by
  let s'' : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of (quotient H I))).asOver (Spec (CommRingCat.of R)) :=
    s'
  refine ⟨Spec.mapMulEquiv.symm s'', ?_⟩
  apply Spec.mapMulEquiv.injective
  rw [mapMulEquiv_quotientPointsHom]
  have hinv : Spec.mapMulEquiv (Spec.mapMulEquiv.symm s'') = s'' :=
    Spec.mapMulEquiv.apply_symm_apply s''
  erw [hinv]
  exact hs'

/-- **`A`-valued points of `stabilizerHopfIdeal`.** An `A`-valued point of `G = Spec H` lies in the
point subgroup cut out by `stabilizerHopfIdeal H x` if and only if its corresponding scheme point
lies in `stabilizerPoints`. -/
theorem mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff
    (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ quotientPointsSubgroup H (stabilizerHopfIdeal H x) A ↔
      Spec.mapMulEquiv g ∈ stabilizerPoints
        ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x
        ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))) := by
  rw [← stabilizer.exists_lift_iff]
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨Spec.mapMulEquiv q ≫ (quotientSpecStabilizerIso H x).hom.hom.hom, ?_⟩
    erw [Category.assoc, quotientSpecStabilizerIso_hom_incl, mapMulEquiv_quotientPointsHom]
    rfl
  · rintro ⟨s, hs⟩
    refine exists_quotientPointsHom_of_comp_quotientSpecι H (stabilizerHopfIdeal H x) A g
      (s ≫ (quotientSpecStabilizerIso H x).inv.hom.hom) ?_
    rw [Category.assoc, quotientSpecStabilizerIso_inv_comp_quotientSpecι]
    exact hs

/-- An `A`-valued point of `G = Spec H` lies in `quotientPointsSubgroup H (stabilizerHopfIdeal H x)`
if and only if its orbit image equals the constant point at `x`. -/
theorem mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_comp_orbitMap
    (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ quotientPointsSubgroup H (stabilizerHopfIdeal H x) A ↔
      Spec.mapMulEquiv g ≫
          orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x =
        toUnit ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))) ≫ x :=
  (mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff H x A g).trans
    (mem_stabilizerPoints_iff _ x _)

/-- Two `A`-valued points of `Spec H` have the same image under `orbitMap` if and only if they lie
in the same left coset of the stabilizer Hopf ideal. -/
theorem mapMulEquiv_comp_orbitMap_eq_iff
    {A : CommAlgCat.{u} R} (g g' : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv g ≫
          orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x =
        Spec.mapMulEquiv g' ≫
          orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x ↔
      g⁻¹ * g' ∈ quotientPointsSubgroup H (stabilizerHopfIdeal H x) A := by
  rw [mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff, map_mul, map_inv,
    inv_mul_mem_stabilizerPoints_iff]

/-- The orbit morphism is invariant under right multiplication by points of the stabilizer Hopf
ideal. -/
theorem mapMulEquiv_mul_comp_orbitMap
    {A : CommAlgCat.{u} R} (g : HopfAlgebra.points (R := R) (H := H) A)
    (n : quotientPointsSubgroup H (stabilizerHopfIdeal H x) A) :
    Spec.mapMulEquiv (g * n.val) ≫
        orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x =
      Spec.mapMulEquiv g ≫
        orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x := by
  rw [eq_comm, mapMulEquiv_comp_orbitMap_eq_iff, inv_mul_cancel_left]
  exact n.property

/-- Translating a closed section by a rational group point preserves closedness of the section. -/
instance isClosedImmersion_smul_left
    (g : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) :
    IsClosedImmersion (g • x).left := by
  have hg : g • x = x ≫
      (TauCeti.translation X g).hom := by
    rw [TauCeti.comp_translation_hom, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [hg, Over.comp_left]
  infer_instance

/-- **Conjugation formula for stabilizers.** The stabilizer Hopf ideal of a translate `g • x` is
the `g`-conjugate of the stabilizer Hopf ideal of `x`. -/
theorem stabilizerHopfIdeal_smul
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    stabilizerHopfIdeal H
        (((Over.homMk (𝟙 (Spec (CommRingCat.of R)))
          (by simp [Scheme.asOver, OverClass.asOver, Over.mk_hom,
            AlgebraicGeometry.specOverSpec_over]) :
          𝟙_ (Over (Spec (CommRingCat.of R))) ⟶
            (Spec (CommRingCat.of R)).asOver (Spec (CommRingCat.of R))) ≫
          Spec.mapMulEquiv g) • x) =
      (stabilizerHopfIdeal H x).conjugate g := by
  let g' := (Over.homMk (𝟙 (Spec (CommRingCat.of R)))
    (by simp [Scheme.asOver, OverClass.asOver, Over.mk_hom,
            AlgebraicGeometry.specOverSpec_over]) :
    𝟙_ (Over (Spec (CommRingCat.of R))) ⟶
      (Spec (CommRingCat.of R)).asOver (Spec (CommRingCat.of R))) ≫ Spec.mapMulEquiv g
  change stabilizerHopfIdeal H (g' • x) = (stabilizerHopfIdeal H x).conjugate g
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
  intro A
  ext y
  rw [← extendPoint_inv_mul_mul_mem_quotientPointsSubgroup_iff_mem_conjugate,
    mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff,
    mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff,
    map_mul, map_mul, map_inv, ← toUnit_comp_unitPoint_mapMulEquiv H g A]
  exact ⟨fun hy ↦ inv_conj_mem_stabilizerPoints_of_mem_smul _ x g' hy, fun hy ↦ by
    let k := toUnit ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))) ≫ g'
    have hconj : k * (k⁻¹ * Spec.mapMulEquiv y * k) * k⁻¹ ∈
        stabilizerPoints ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) (g' • x)
          ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))) :=
      conj_mem_stabilizerPoints_smul _ x g' hy
    simp only [_root_.mul_assoc, mul_inv_cancel, _root_.mul_one, mul_inv_cancel_left] at hconj
    exact hconj⟩

/-- `H ⧸ stabilizerHopfIdeal H x` is smooth over `R` if and only if the scheme-theoretic
stabilizer of `x` is smooth over `Spec R`. -/
theorem algebraSmooth_quotient_stabilizerHopfIdeal_iff :
    Algebra.Smooth R (quotient H (stabilizerHopfIdeal H x)) ↔
      Smooth (stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x).hom := by
  have : MorphismProperty.RespectsIso (@Smooth) := by
    rw [HasRingHomProperty.eq_affineLocally @Smooth]
    exact affineLocally_respectsIso (@RingHom.Smooth) RingHom.Smooth.respectsIso
  rw [← smoothCommHopfAlgProperty_iff (R := R) (H := quotient H (stabilizerHopfIdeal H x)),
    TauCeti.algebraSmooth_iff_smooth_hopfSpec R (quotient H (stabilizerHopfIdeal H x)),
    smoothAffineGroupSchemeProperty_iff]
  change Smooth ((Grp.forget _).obj (quotientSpec H (stabilizerHopfIdeal H x))).hom ↔ _
  exact MorphismProperty.over_iso_iff (@Smooth)
    ((Grp.forget _).mapIso (quotientSpecStabilizerIso H x))

end StabilizerHopfIdeal

section OrbitSchemeQuotient

local instance locallyOfFiniteType_specHopf
    {k : Type u} [Field k] {H : Type u} [CommRing H] [Algebra k H] [Algebra.FiniteType k H] :
    LocallyOfFiniteType ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom := by
  change LocallyOfFiniteType (Spec (CommRingCat.of H) ↘ Spec (CommRingCat.of k))
  infer_instance

local instance compactSpace_specHopf
    {k : Type u} [Field k] {H : Type u} [CommRing H] [Algebra k H] [Algebra.FiniteType k H] :
    CompactSpace ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).left := by
  change CompactSpace (Spec (CommRingCat.of H))
  infer_instance

local instance isClosedImmersion_fieldSection
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    {x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X} : IsClosedImmersion x.left :=
  TauCeti.isClosedImmersion_section x

variable {k : Type u} [Field k] (H : _root_.CommHopfAlgCat.{u} k) [Algebra.FiniteType k H]
  {X : Over (Spec (CommRingCat.of k))}
  [ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) X]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)

/-- Two `A`-valued points of `Spec H` have the same image in the orbit scheme `orbitOver _ x` if
and only if they lie in the same left coset of `stabilizerHopfIdeal H x`. -/
theorem mapMulEquiv_comp_orbitProjection_eq_iff
    {A : CommAlgCat.{u} k} (g g' : HopfAlgebra.points (R := k) (H := H) A) :
    Spec.mapMulEquiv g ≫
          orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x =
        Spec.mapMulEquiv g' ≫
          orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x ↔
      g⁻¹ * g' ∈ quotientPointsSubgroup H (stabilizerHopfIdeal H x) A := by
  rw [← mapMulEquiv_comp_orbitMap_eq_iff H x]
  refine ⟨fun h ↦ ?_, fun h ↦ (cancel_mono (orbitInclusion _ x)).mp ?_⟩
  · rw [← orbitProjection_inclusion, ← Category.assoc, h, Category.assoc]
  · simpa only [Category.assoc, orbitProjection_inclusion] using h

/-- The orbit projection onto `orbitOver _ x` is invariant under right multiplication by points of
`stabilizerHopfIdeal H x`. -/
theorem mapMulEquiv_mul_comp_orbitProjection
    {A : CommAlgCat.{u} k} (g : HopfAlgebra.points (R := k) (H := H) A)
    (n : quotientPointsSubgroup H (stabilizerHopfIdeal H x) A) :
    Spec.mapMulEquiv (g * n.val) ≫
        orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x =
      Spec.mapMulEquiv g ≫
        orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x := by
  apply (cancel_mono (orbitInclusion _ x)).mp
  simpa only [Category.assoc, orbitProjection_inclusion] using
    mapMulEquiv_mul_comp_orbitMap H x g n

variable [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]

/-- **Orbit schemes represent fppf homogeneous quotients.** When `G = Spec H` is finite type and
geometrically reduced over `k` and `X` is finite type over `k`, the locally closed orbit scheme
`orbitOver G x` represents `fppfHomogeneousQuotient H (stabilizerHopfIdeal H x)`. -/
def orbitOverQuotientIsoPointsSheaf :
    fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      CommAlgCat.pointsSheaf
        (orbitOver ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x) :=
  have : Flat
      (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    by rw [orbitProjection_left]; exact TauCeti.SchemeAction.flat_toOrbit _ x
  have : LocallyOfFinitePresentation
      (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    by rw [orbitProjection_left]; exact TauCeti.SchemeAction.locallyOfFinitePresentation_toOrbit _ x
  have : Surjective
      (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    by rw [orbitProjection_left]; infer_instance
  fppfHomogeneousQuotientIsoPointsSheaf H (stabilizerHopfIdeal H x)
    (orbitProjection _ x)
    (fun _ g n ↦ mapMulEquiv_mul_comp_orbitProjection H x g n)
    (fun _ g g' h ↦ (mapMulEquiv_comp_orbitProjection_eq_iff H x g g').mp h)

/-- Under `orbitOverQuotientIsoPointsSheaf`, the canonical quotient projection is
`orbitProjection`. -/
@[simp]
theorem representedQuotientProjection_orbitOverQuotientIsoPointsSheaf :
    representedQuotientProjection H (stabilizerHopfIdeal H x)
        (orbitOverQuotientIsoPointsSheaf H x) =
      orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x := by
  have : Flat
      (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    by rw [orbitProjection_left]; exact TauCeti.SchemeAction.flat_toOrbit _ x
  have : LocallyOfFinitePresentation
      (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    by rw [orbitProjection_left]; exact TauCeti.SchemeAction.locallyOfFinitePresentation_toOrbit _ x
  have : Surjective
      (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    by rw [orbitProjection_left]; infer_instance
  exact representedQuotientProjection_fppfHomogeneousQuotientIsoPointsSheaf H
    (stabilizerHopfIdeal H x) (orbitProjection _ x) _ _

/-- The restricted action `orbitModObj` on `orbitOver _ x` agrees with `representedQuotientModObj`
induced by `orbitOverQuotientIsoPointsSheaf`. -/
theorem representedQuotientModObj_orbitOverQuotientIsoPointsSheaf :
    orbitModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x =
      representedQuotientModObj H (stabilizerHopfIdeal H x)
        (orbitOverQuotientIsoPointsSheaf H x) :=
  representedQuotientModObj_eq_of_comp H (stabilizerHopfIdeal H x)
    (orbitOverQuotientIsoPointsSheaf H x) (by
      simpa only [representedQuotientProjection_orbitOverQuotientIsoPointsSheaf] using
        mul_orbitProjection _ x)

/-- The orbit projection onto `orbitOver _ x` is smooth if and only if the quotient Hopf algebra
by `stabilizerHopfIdeal H x` is smooth over `k`. -/
theorem smooth_orbitProjection_iff :
    Smooth (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left ↔
      Algebra.Smooth k (quotient H (stabilizerHopfIdeal H x)) := by
  rw [orbitProjection_left, smooth_toOrbit_iff, algebraSmooth_quotient_stabilizerHopfIdeal_iff]

end OrbitSchemeQuotient

section HomogeneousOrbit

local instance locallyOfFiniteType_specHopf'
    {k : Type u} [Field k] {H : Type u} [CommRing H] [Algebra k H] [Algebra.FiniteType k H] :
    LocallyOfFiniteType ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom := by
  change LocallyOfFiniteType (Spec (CommRingCat.of H) ↘ Spec (CommRingCat.of k))
  infer_instance

local instance compactSpace_specHopf'
    {k : Type u} [Field k] {H : Type u} [CommRing H] [Algebra k H] [Algebra.FiniteType k H] :
    CompactSpace ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).left := by
  change CompactSpace (Spec (CommRingCat.of H))
  infer_instance

local instance isClosedImmersion_fieldSection'
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    {x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X} : IsClosedImmersion x.left :=
  TauCeti.isClosedImmersion_section x

variable {k : Type u} [Field k] (H : _root_.CommHopfAlgCat.{u} k) [Algebra.FiniteType k H]
  {X : Over (Spec (CommRingCat.of k))}
  [mX : ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) X]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left] [IsReduced X.left]
  (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
  [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]

/-- **Homogeneous orbit comparison.** When `G = Spec H` is geometrically reduced of finite type,
`X` is reduced of finite type, and `orbit G x = Set.univ`, `X` itself represents the fppf
homogeneous quotient `G / Stab(x)`. -/
def orbitQuotientIsoPointsSheaf
    (hx : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅ CommAlgCat.pointsSheaf X :=
  have : Flat (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    flat_orbitMap_of_orbit_eq_univ _ x hx
  have : LocallyOfFinitePresentation
      (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    locallyOfFinitePresentation_orbitMap_of_orbit_eq_univ _ x hx
  have : Surjective
      (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    surjective_orbitMap_of_orbit_eq_univ _ x hx
  fppfHomogeneousQuotientIsoPointsSheaf H (stabilizerHopfIdeal H x)
    (orbitMap _ x)
    (fun _ g n ↦ mapMulEquiv_mul_comp_orbitMap H x g n)
    (fun _ g g' h ↦ (mapMulEquiv_comp_orbitMap_eq_iff H x g g').mp h)

/-- Under `orbitQuotientIsoPointsSheaf`, the canonical quotient projection is `orbitMap`. -/
@[simp]
theorem representedQuotientProjection_orbitQuotientIsoPointsSheaf
    (hx : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    representedQuotientProjection H (stabilizerHopfIdeal H x)
        (orbitQuotientIsoPointsSheaf H x hx) =
      orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x := by
  have : Flat (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    flat_orbitMap_of_orbit_eq_univ _ x hx
  have : LocallyOfFinitePresentation
      (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    locallyOfFinitePresentation_orbitMap_of_orbit_eq_univ _ x hx
  have : Surjective
      (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left :=
    surjective_orbitMap_of_orbit_eq_univ _ x hx
  exact representedQuotientProjection_fppfHomogeneousQuotientIsoPointsSheaf H
    (stabilizerHopfIdeal H x) (orbitMap _ x) _ _

/-- The given `ModObj` instance on `X` agrees with `representedQuotientModObj` induced by
`orbitQuotientIsoPointsSheaf`. -/
theorem representedQuotientModObj_orbitQuotientIsoPointsSheaf
    (hx : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    mX = representedQuotientModObj H (stabilizerHopfIdeal H x)
        (orbitQuotientIsoPointsSheaf H x hx) :=
  representedQuotientModObj_eq_of_comp H (stabilizerHopfIdeal H x)
    (orbitQuotientIsoPointsSheaf H x hx) (by
      simpa only [representedQuotientProjection_orbitQuotientIsoPointsSheaf] using
        mul_orbitMap _ x)

/-- Any other scheme `Y` representing `G / Stab(x)` is canonically isomorphic to `X` over `Spec k`.
-/
def orbitQuotientIso
    (hx : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ)
    {Y : Over (Spec (CommRingCat.of k))}
    (e : fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅ CommAlgCat.pointsSheaf Y) :
    Y ≅ X :=
  representedQuotientIso H (stabilizerHopfIdeal H x) e (orbitQuotientIsoPointsSheaf H x hx)

/-- The canonical comparison isomorphism `orbitQuotientIso` is equivariant with respect to
`representedQuotientModObj` on `Y` and the given action on `X`. -/
instance isModHom_orbitQuotientIso_hom
    (hx : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ)
    {Y : Over (Spec (CommRingCat.of k))}
    (e : fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅ CommAlgCat.pointsSheaf Y) :
    letI := representedQuotientModObj H (stabilizerHopfIdeal H x) e
    IsModHom ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k)))
      (orbitQuotientIso H x hx e).hom := by
  let := representedQuotientModObj H (stabilizerHopfIdeal H x) e
  have hm := representedQuotientModObj_orbitQuotientIsoPointsSheaf H x hx
  have hmod := isModHom_representedQuotientIso H (stabilizerHopfIdeal H x) e
    (orbitQuotientIsoPointsSheaf H x hx)
  rw [← hm] at hmod
  exact hmod

/-- The canonical comparison isomorphism `orbitQuotientIso` intertwines
`representedQuotientProjection` with `orbitMap`. -/
@[reassoc (attr := simp)]
theorem representedQuotientProjection_comp_orbitQuotientIso_hom
    (hx : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ)
    {Y : Over (Spec (CommRingCat.of k))}
    (e : fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅ CommAlgCat.pointsSheaf Y) :
    representedQuotientProjection H (stabilizerHopfIdeal H x) e ≫
        (orbitQuotientIso H x hx e).hom =
      orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x := by
  rw [orbitQuotientIso, representedQuotientIso_hom,
    representedQuotientProjection_comp_fppfHomogeneousQuotientSchemeMap,
    representedQuotientProjection_orbitQuotientIsoPointsSheaf]

/-- Over an algebraically closed field, if `orbit G x = Set.univ`, rational points of `G` act
transitively on rational points of `X`. -/
theorem exists_smul_eq_of_orbit_eq_univ [IsAlgClosed k]
    (hx : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ)
    (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) :
    ∃ g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k),
      ((Over.homMk (𝟙 (Spec (CommRingCat.of k)))
        (by simp [Scheme.asOver, OverClass.asOver, Over.mk_hom,
            AlgebraicGeometry.specOverSpec_over]) :
        𝟙_ (Over (Spec (CommRingCat.of k))) ⟶
          (Spec (CommRingCat.of k)).asOver (Spec (CommRingCat.of k))) ≫
        Spec.mapMulEquiv g) • x = y := by
  let eps : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶
      (Spec (CommRingCat.of k)).asOver (Spec (CommRingCat.of k)) :=
    Over.homMk (𝟙 (Spec (CommRingCat.of k)))
      (by simp [Scheme.asOver, OverClass.asOver, Over.mk_hom,
            AlgebraicGeometry.specOverSpec_over])
  let epsInv : (Spec (CommRingCat.of k)).asOver (Spec (CommRingCat.of k)) ⟶
      𝟙_ (Over (Spec (CommRingCat.of k))) :=
    toUnit ((Spec (CommRingCat.of k)).asOver (Spec (CommRingCat.of k)))
  have heps : eps ≫ epsInv = 𝟙 _ := toUnit_unique _ _
  obtain ⟨g, hg⟩ := exists_mapMulEquiv_comp_representedQuotientProjection_eq H
    (stabilizerHopfIdeal H x) (orbitQuotientIsoPointsSheaf H x hx) (epsInv ≫ y)
  rw [representedQuotientProjection_orbitQuotientIsoPointsSheaf] at hg
  refine ⟨g, ?_⟩
  calc (eps ≫ Spec.mapMulEquiv g) • x
      = (eps ≫ Spec.mapMulEquiv g) ≫ orbitMap _ x := by
        rw [comp_orbitMap, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    _ = (eps ≫ epsInv) ≫ y := by rw [Category.assoc, hg, ← Category.assoc]
    _ = y := by rw [heps, Category.id_comp]

/-- Over an algebraically closed field, any two rational points of a homogeneous `G`-scheme have
conjugate stabilizer Hopf ideals. -/
theorem exists_stabilizerHopfIdeal_eq_conjugate_of_orbit_eq_univ [IsAlgClosed k]
    (hx : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ)
    (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) :
    ∃ g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k),
      stabilizerHopfIdeal H y = (stabilizerHopfIdeal H x).conjugate g := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_orbit_eq_univ H x hx y
  exact ⟨g, stabilizerHopfIdeal_smul H x g⟩

omit [GeometricallyReduced
  ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom] in
/-- **Every reduced homogeneous `G`-scheme over an algebraically closed field is equivariantly
isomorphic to a projective orbit scheme.** -/
theorem exists_projectiveOrbit_orbitQuotientIso [IsAlgClosed k] [_root_.IsReduced H]
    (hx : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (m : M) (hm : Module.IsUnimodular k m)
      (e : fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
        Comodule.projectiveOrbitPointsSheaf (H := H) m hm),
      letI := representedQuotientModObj H (stabilizerHopfIdeal H x) e
      ∃ φ : Over.mk (Comodule.projectiveOrbitToSpec (H := H) m hm) ≅ X,
        IsModHom ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) φ.hom ∧
          representedQuotientProjection H (stabilizerHopfIdeal H x) e ≫ φ.hom =
            orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x := by
  have : IsReduced
      ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).left := by
    change IsReduced (Spec (CommRingCat.of H))
    infer_instance
  have : GeometricallyReduced
      ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom :=
    AlgebraicGeometry.geometricallyReduced_of_perfectField _
  obtain ⟨M, _, _, _, _, m, hm, ⟨e⟩⟩ :=
    TauCeti.HopfIdeal.exists_fppfHomogeneousQuotient_iso_projectiveOrbitPoints
      (stabilizerHopfIdeal H x)
  exact ⟨M, _, _, _, _, m, hm, e, orbitQuotientIso H x hx e,
    isModHom_orbitQuotientIso_hom H x hx e,
    representedQuotientProjection_comp_orbitQuotientIso_hom H x hx e⟩

end HomogeneousOrbit

section Checks

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)

/-- Sanity check: the stabilizer Hopf ideal of the unique global point under the trivial action on
the base scheme `Spec R` is `⊥`. -/
theorem stabilizerHopfIdeal_trivialAction_unit :
    letI := ModObj.trivialAction ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)))
      (𝟙_ (Over (Spec (CommRingCat.of R))))
    stabilizerHopfIdeal H (𝟙 (𝟙_ (Over (Spec (CommRingCat.of R))))) = ⊥ := by
  let := ModObj.trivialAction ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)))
    (𝟙_ (Over (Spec (CommRingCat.of R))))
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
  intro A
  ext g
  simp only [quotientPointsSubgroup_bot, Subgroup.mem_top, iff_true]
  rw [mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_comp_orbitMap]
  exact toUnit_unique _ _

/-- Sanity check: the stabilizer Hopf ideal of the identity section under the left regular action
of `Spec H` on itself is the augmentation ideal. -/
theorem stabilizerHopfIdeal_regular_one :
    letI := ModObj.regular ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)))
    letI : IsClosedImmersion
        η[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))].left :=
      have : IsSeparated
          ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))).hom := by
        change IsSeparated (Spec (CommRingCat.of H) ↘ Spec (CommRingCat.of R))
        infer_instance
      AlgebraicGeometry.Scheme.Hom.isClosedImmersion_of_comp_eq_id _ (Over.w _)
    stabilizerHopfIdeal H η[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))] =
      HopfIdeal.augmentation R H := by
  let G := (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))
  let := ModObj.regular G
  have : IsSeparated G.hom := by
    change IsSeparated (Spec (CommRingCat.of H) ↘ Spec (CommRingCat.of R))
    infer_instance
  have : IsClosedImmersion η[G].left :=
    AlgebraicGeometry.Scheme.Hom.isClosedImmersion_of_comp_eq_id _ (Over.w η[G])
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
  intro A
  ext g
  rw [mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_comp_orbitMap,
    mem_quotientPointsSubgroup_augmentation_iff]
  have horb : orbitMap G η[G] = 𝟙 G := by
    calc orbitMap G η[G]
        = 𝟙 G ≫ orbitMap G η[G] := (Category.id_comp _).symm
      _ = (𝟙 G : G ⟶ G) • (toUnit G ≫ η[G]) := comp_orbitMap G (𝟙 G) η[G]
      _ = (𝟙 G : G ⟶ G) * 1 := by
          rw [← Hom.one_def, Hom.smul_def]
          change lift (𝟙 G) (1 : G ⟶ G) ≫ μ[G] = _
          rw [← Hom.mul_def]
      _ = 𝟙 G := _root_.mul_one (𝟙 G)
  have h1 : toUnit ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))) ≫ η[G] =
      (1 : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ G) :=
    (Hom.one_def (X := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)))
      (M := G)).symm
  rw [horb, Category.comp_id, h1, ← map_one Spec.mapMulEquiv]
  exact Spec.mapMulEquiv.injective.eq_iff

end Checks

end CommHopfAlgCat
