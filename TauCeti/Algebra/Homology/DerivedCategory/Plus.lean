/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# Localization, truncations, and triangles in the bounded-below derived category

Mathlib constructs the bounded-below derived category `DerivedCategory.Plus C` of an abelian
category `C` as a localizing full subcategory of `DerivedCategory C`, with localization functor
`DerivedCategory.Plus.Q : CochainComplex.Plus C ⥤ DerivedCategory.Plus C`. This file provides the
basic complex-level interface for `CochainComplex.Plus C` and `DerivedCategory.Plus C`:

* single complexes (`CochainComplex.Plus.singleFunctor`) and compatibility with
  `DerivedCategory.Plus.singleFunctor` (`DerivedCategory.Plus.singleFunctorIsoCompQ`);
* canonical truncations `CochainComplex.Plus.truncLE` and `CochainComplex.Plus.truncGE`, together
  with the distinguished truncation triangle `DerivedCategory.Plus.truncLEGETriangle` in
  `DerivedCategory.Plus C`;
* mapping cones (`CochainComplex.Plus.mappingCone`, `CochainComplex.Plus.mappingConeTriangle`) and
  their distinguished triangles (`DerivedCategory.Plus.mappingConeTriangle_distinguished`);
* comparison of homology on `DerivedCategory.Plus C` with homology of bounded-below complexes
  (`DerivedCategory.Plus.homologyFunctorFactors`), homotopy invariance and quasi-isomorphism
  characterization of `DerivedCategory.Plus.Q`, and `t`-structure degree bounds on `Q.obj K`.

## References

* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque 239 (1996).
* The Stacks Project, Derived Categories, §13.12 (tag 05RU) and §13.16 (tag 05T6).
-/

public section

noncomputable section

open CategoryTheory Category Limits Pretriangulated Triangulated

universe w v u

namespace CochainComplex.Plus

section SingleAndTrunc

variable (C : Type u) [Category.{v} C]

section HasZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroObject C]

variable {C} in
/-- The canonical truncation `τ≤n K` of a bounded-below cochain complex `K`, viewed in
`CochainComplex.Plus C`. -/
@[expose, implicit_reducible]
def truncLE (K : Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) : Plus C :=
  ⟨K.obj.truncLE n, by
    obtain ⟨b, _⟩ := K.property
    exact ⟨b, inferInstance⟩⟩

variable {C} in
@[simp]
lemma truncLE_obj (K : Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.truncLE n).obj = K.obj.truncLE n :=
  rfl

variable {C} in
/-- The canonical inclusion `K.truncLE n ⟶ K` in `CochainComplex.Plus C`. -/
@[expose, implicit_reducible]
def ιTruncLE (K : Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) : K.truncLE n ⟶ K :=
  ObjectProperty.homMk (K.obj.ιTruncLE n)

variable {C} in
@[simp]
lemma ιTruncLE_hom (K : Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.ιTruncLE n).hom = K.obj.ιTruncLE n :=
  rfl

variable {C} in
/-- The canonical truncation `τ≥n K` of a bounded-below cochain complex `K`, viewed in
`CochainComplex.Plus C`. -/
@[expose, implicit_reducible]
def truncGE (K : Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) : Plus C :=
  ⟨K.obj.truncGE n, ⟨n, inferInstance⟩⟩

variable {C} in
@[simp]
lemma truncGE_obj (K : Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.truncGE n).obj = K.obj.truncGE n :=
  rfl

variable {C} in
/-- The canonical quotient map `K ⟶ K.truncGE n` in `CochainComplex.Plus C`. -/
@[expose, implicit_reducible]
def πTruncGE (K : Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) : K ⟶ K.truncGE n :=
  ObjectProperty.homMk (K.obj.πTruncGE n)

variable {C} in
@[simp]
lemma πTruncGE_hom (K : Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.πTruncGE n).hom = K.obj.πTruncGE n :=
  rfl

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] [HasZeroObject C]

/-- The functor `C ⥤ CochainComplex.Plus C` placing an object in degree `n : ℤ`. -/
@[expose]
def singleFunctor (n : ℤ) : C ⥤ Plus C :=
  ObjectProperty.lift _ (CochainComplex.singleFunctor C n) (fun _ ↦ ⟨n, inferInstance⟩)

@[simp]
lemma singleFunctor_obj_obj (n : ℤ) (X : C) :
    ((singleFunctor C n).obj X).obj = (CochainComplex.singleFunctor C n).obj X :=
  rfl

@[simp]
lemma singleFunctor_map_hom (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    ((singleFunctor C n).map f).hom = (CochainComplex.singleFunctor C n).map f :=
  rfl

/-- `CochainComplex.Plus.singleFunctor` lifts `CochainComplex.singleFunctor` along `Plus.ι`. -/
@[expose]
def singleFunctorCompιIso (n : ℤ) :
    singleFunctor C n ⋙ Plus.ι C ≅ CochainComplex.singleFunctor C n :=
  ObjectProperty.liftCompιIso ..

@[simp]
lemma singleFunctorCompιIso_hom_app (n : ℤ) (X : C) :
    (singleFunctorCompιIso C n).hom.app X = 𝟙 _ :=
  rfl

@[simp]
lemma singleFunctorCompιIso_inv_app (n : ℤ) (X : C) :
    (singleFunctorCompιIso C n).inv.app X = 𝟙 _ :=
  rfl

end Preadditive

section MappingCone

variable {C} [Preadditive C] [HasBinaryBiproducts C]

/-- The mapping cone of a morphism in `CochainComplex.Plus C`, again as a bounded-below cochain
complex. -/
@[expose, implicit_reducible]
def mappingCone {K L : Plus C} (f : K ⟶ L) : Plus C :=
  ⟨CochainComplex.mappingCone f.hom, by
    obtain ⟨n₁, _⟩ := K.property
    obtain ⟨n₂, _⟩ := L.property
    exact ⟨min (n₁ - 1) n₂, CochainComplex.isStrictlyGE_mappingCone f.hom n₁ n₂ _⟩⟩

@[simp]
lemma mappingCone_obj {K L : Plus C} (f : K ⟶ L) :
    (mappingCone f).obj = CochainComplex.mappingCone f.hom :=
  rfl

/-- The standard mapping-cone triangle `K ⟶ L ⟶ mappingCone f ⟶ K⟦1⟧` in
`CochainComplex.Plus C`. -/
@[expose, implicit_reducible]
def mappingConeTriangle {K L : Plus C} (f : K ⟶ L) : Triangle (Plus C) :=
  let mor₃₀ : (Plus.ι C).obj (mappingCone f) ⟶ ((Plus.ι C).obj K)⟦(1 : ℤ)⟧ :=
    (CochainComplex.HomComplex.Cocycle.homOf
      ((-CochainComplex.mappingCone.fst f.hom).rightShift 1 0 (zero_add 1)) :
      CochainComplex.mappingCone f.hom ⟶ K.obj⟦(1 : ℤ)⟧)
  let invShift : ((Plus.ι C).obj K)⟦(1 : ℤ)⟧ ⟶ (Plus.ι C).obj (K⟦(1 : ℤ)⟧) :=
    ((Plus.ι C).commShiftIso (1 : ℤ)).inv.app K
  Triangle.mk f (ObjectProperty.homMk (CochainComplex.mappingCone.inr f.hom) : L ⟶ mappingCone f)
    ((Plus.fullyFaithfulι C).preimage (mor₃₀ ≫ invShift))

/-- Including `CochainComplex.Plus C` into `CochainComplex C ℤ` sends `mappingConeTriangle f` to
`CochainComplex.mappingCone.triangle f.hom`. -/
def mappingConeTriangleMapιIso {K L : Plus C} (f : K ⟶ L) :
    (Plus.ι C).mapTriangle.obj (mappingConeTriangle f) ≅
      CochainComplex.mappingCone.triangle f.hom :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [mappingConeTriangle])
    (by
      dsimp only [Functor.mapTriangle_obj, mappingConeTriangle, Triangle.mk_mor₂,
        CochainComplex.mappingCone.triangle, Iso.refl_hom]
      rw [id_comp, comp_id]
      rfl)
    (by
      dsimp only [Functor.mapTriangle_obj, mappingConeTriangle, Triangle.mk_mor₃, Triangle.mk_obj₁,
        CochainComplex.mappingCone.triangle, Iso.refl_hom]
      rw [(Plus.fullyFaithfulι C).map_preimage, CategoryTheory.Functor.map_id, comp_id, id_comp,
        assoc, Iso.inv_hom_id_app]
      exact comp_id _)

end MappingCone

end SingleAndTrunc

end CochainComplex.Plus

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A triangle in `DerivedCategory.Plus C` is distinguished if and only if its image under
`DerivedCategory.Plus.ι` is distinguished in `DerivedCategory C`. -/
lemma mem_distTriang_iff (T : Triangle (DerivedCategory.Plus C)) :
    T ∈ distTriang (DerivedCategory.Plus C) ↔
      Plus.ι.mapTriangle.obj T ∈ distTriang (DerivedCategory C) :=
  Iff.rfl

variable (C) in
/-- Homology on `DerivedCategory.Plus C` restricted along `DerivedCategory.Plus.Q` is canonically
isomorphic to homology of the underlying bounded-below cochain complexes. -/
def homologyFunctorFactors (n : ℤ) :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (QCompιIso C) (DerivedCategory.homologyFunctor C n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (CochainComplex.Plus.ι C) (DerivedCategory.homologyFunctorFactors C n)

@[reassoc (attr := simp)]
lemma homologyFunctorFactors_hom_naturality {K L : CochainComplex.Plus C} (f : K ⟶ L) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map f) ≫
        (homologyFunctorFactors C n).hom.app L =
      (homologyFunctorFactors C n).hom.app K ≫ HomologicalComplex.homologyMap f.hom n :=
  (homologyFunctorFactors C n).hom.naturality f

/-- A morphism in `CochainComplex.Plus C` becomes an isomorphism in `DerivedCategory.Plus C` if and
only if its underlying chain map is a quasi-isomorphism. -/
lemma isIso_Q_map_iff_quasiIso {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    IsIso (DerivedCategory.Plus.Q.map f) ↔ QuasiIso f.hom := by
  rw [← isIso_iff_of_reflects_iso (DerivedCategory.Plus.Q.map f) Plus.ι, ← Functor.comp_map,
    NatIso.isIso_map_iff (QCompιIso C) f]
  exact DerivedCategory.isIso_Q_map_iff_quasiIso C f.hom

instance {K L : CochainComplex.Plus C} (f : K ⟶ L) [QuasiIso f.hom] :
    IsIso (DerivedCategory.Plus.Q.map f) := by
  rwa [isIso_Q_map_iff_quasiIso]

/-- Homotopic morphisms of bounded-below cochain complexes induce equal morphisms in
`DerivedCategory.Plus C`. -/
lemma Q_map_eq_of_homotopy {K L : CochainComplex.Plus C} {f g : K ⟶ L} (h : Homotopy f.hom g.hom) :
    DerivedCategory.Plus.Q.map f = DerivedCategory.Plus.Q.map g := by
  apply Plus.ι.map_injective
  rw [← cancel_mono ((QCompιIso C).hom.app L)]
  exact ((QCompιIso C).hom.naturality f).trans
    ((DerivedCategory.Q_map_eq_of_homotopy C h) ▸ ((QCompιIso C).hom.naturality g).symm)

/-- The image of `K : CochainComplex.Plus C` in `DerivedCategory.Plus C` is `≥ n` for the canonical
`t`-structure if and only if `K.obj` has vanishing homology below degree `n`. -/
lemma isGE_Q_obj_iff (K : CochainComplex.Plus C) (n : ℤ) :
    (DerivedCategory.Plus.Q.obj K).IsGE n ↔ K.obj.IsGE n := by
  let e : Plus.ι.obj (DerivedCategory.Plus.Q.obj K) ≅ DerivedCategory.Q.obj K.obj :=
    (QCompιIso C).app K
  rw [← isGE_ι_obj_iff, ← DerivedCategory.isGE_Q_obj_iff]
  exact ⟨fun _ ↦ DerivedCategory.TStructure.t.isGE_of_iso e n,
    fun _ ↦ DerivedCategory.TStructure.t.isGE_of_iso e.symm n⟩

/-- The image of `K : CochainComplex.Plus C` in `DerivedCategory.Plus C` is `≤ n` for the canonical
`t`-structure if and only if `K.obj` has vanishing homology above degree `n`. -/
lemma isLE_Q_obj_iff (K : CochainComplex.Plus C) (n : ℤ) :
    (DerivedCategory.Plus.Q.obj K).IsLE n ↔ K.obj.IsLE n := by
  let e : Plus.ι.obj (DerivedCategory.Plus.Q.obj K) ≅ DerivedCategory.Q.obj K.obj :=
    (QCompιIso C).app K
  rw [← isLE_ι_obj_iff, ← DerivedCategory.isLE_Q_obj_iff]
  exact ⟨fun _ ↦ DerivedCategory.TStructure.t.isLE_of_iso e n,
    fun _ ↦ DerivedCategory.TStructure.t.isLE_of_iso e.symm n⟩

instance (K : CochainComplex.Plus C) (n : ℤ) [K.obj.IsGE n] :
    (DerivedCategory.Plus.Q.obj K).IsGE n := by
  rwa [isGE_Q_obj_iff]

instance (K : CochainComplex.Plus C) (n : ℤ) [K.obj.IsLE n] :
    (DerivedCategory.Plus.Q.obj K).IsLE n := by
  rwa [isLE_Q_obj_iff]

/-- If `X : DerivedCategory.Plus C` is `≥ n`, its homology vanishes in every degree `i < n`. -/
lemma isZero_of_isGE (X : DerivedCategory.Plus C) (n i : ℤ) (hi : i < n) [X.IsGE n] :
    IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj X) :=
  DerivedCategory.isZero_of_isGE (Plus.ι.obj X) n i hi

/-- If `X : DerivedCategory.Plus C` is `≤ n`, its homology vanishes in every degree `i > n`. -/
lemma isZero_of_isLE (X : DerivedCategory.Plus C) (n i : ℤ) (hi : n < i) [X.IsLE n] :
    IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj X) :=
  DerivedCategory.isZero_of_isLE (Plus.ι.obj X) n i hi

variable (C) in
/-- `DerivedCategory.Plus.singleFunctor C n` is canonically isomorphic to
`CochainComplex.Plus.singleFunctor C n ⋙ DerivedCategory.Plus.Q`. -/
def singleFunctorIsoCompQ (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ≅
      CochainComplex.Plus.singleFunctor C n ⋙ DerivedCategory.Plus.Q :=
  (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight C).preimageIso
    (singleFunctorιIso C n ≪≫ DerivedCategory.singleFunctorIsoCompQ C n ≪≫
      Functor.isoWhiskerRight (CochainComplex.Plus.singleFunctorCompιIso C n).symm
        DerivedCategory.Q ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (CochainComplex.Plus.singleFunctor C n) (QCompιIso C).symm ≪≫
      (Functor.associator _ _ _).symm)

lemma whiskerRight_singleFunctorIsoCompQ_hom (n : ℤ) :
    Functor.whiskerRight (singleFunctorIsoCompQ C n).hom Plus.ι =
      (singleFunctorιIso C n ≪≫ DerivedCategory.singleFunctorIsoCompQ C n ≪≫
        Functor.isoWhiskerRight (CochainComplex.Plus.singleFunctorCompιIso C n).symm
          DerivedCategory.Q ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (CochainComplex.Plus.singleFunctor C n) (QCompιIso C).symm ≪≫
        (Functor.associator _ _ _).symm).hom :=
  (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight C).map_preimage _

/-- The image of a mapping-cone triangle in `CochainComplex.Plus C` under `DerivedCategory.Plus.Q`
is distinguished in `DerivedCategory.Plus C`. -/
lemma mappingConeTriangle_distinguished {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.Q.mapTriangle.obj (CochainComplex.Plus.mappingConeTriangle f) ∈
      distTriang (DerivedCategory.Plus C) := by
  rw [mem_distTriang_iff]
  refine isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished f.hom) _ ?_
  exact (Functor.mapTriangleCompIso DerivedCategory.Plus.Q Plus.ι).symm.app _ ≪≫
    (Functor.mapTriangleIso (QCompιIso C)).app _ ≪≫
    (Functor.mapTriangleCompIso (CochainComplex.Plus.ι C) DerivedCategory.Q).app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso (CochainComplex.Plus.mappingConeTriangleMapιIso f)

/-- For `K : CochainComplex.Plus C`, the underlying object of `DerivedCategory.Plus.Q.obj K` in
`DerivedCategory C` is canonically isomorphic to `DerivedCategory.Q.obj K.obj`. -/
@[expose]
def ιQObjIso (K : CochainComplex.Plus C) :
    Plus.ι.obj (DerivedCategory.Plus.Q.obj K) ≅ DerivedCategory.Q.obj K.obj :=
  (QCompιIso C).app K

/-- The canonical connecting morphism `Q.obj (K.truncGE n₁) ⟶ (Q.obj (K.truncLE n₀))⟦1⟧` in
`DerivedCategory.Plus C` when `n₀ + 1 = n₁`. -/
def truncLEGEδ (K : CochainComplex.Plus C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    DerivedCategory.Plus.Q.obj (K.truncGE n₁) ⟶
      (DerivedCategory.Plus.Q.obj (K.truncLE n₀))⟦(1 : ℤ)⟧ :=
  let eGE : Plus.ι.obj (DerivedCategory.Plus.Q.obj (K.truncGE n₁)) ≅
      DerivedCategory.Q.obj (K.obj.truncGE n₁) :=
    ιQObjIso (K.truncGE n₁)
  let eLE : Plus.ι.obj (DerivedCategory.Plus.Q.obj (K.truncLE n₀)) ≅
      DerivedCategory.Q.obj (K.obj.shortComplexTruncLE n₀).X₁ :=
    ιQObjIso (K.truncLE n₀)
  let eφ : DerivedCategory.Q.obj (K.obj.shortComplexTruncLE n₀).X₃ ≅
      DerivedCategory.Q.obj (K.obj.truncGE n₁) :=
    @asIso _ _ _ _ (DerivedCategory.Q.map (K.obj.shortComplexTruncLEX₃ToTruncGE n₀ n₁ h))
      ((DerivedCategory.isIso_Q_map_iff_quasiIso C _).2
        (by dsimp [CochainComplex.shortComplexTruncLEX₃ToTruncGE]; infer_instance))
  DerivedCategory.TStructure.t.plus.fullyFaithfulι.preimage
    (eGE.hom ≫ eφ.inv ≫ DerivedCategory.triangleOfSESδ (K.obj.shortComplexTruncLE_shortExact n₀) ≫
      eLE.inv⟦(1 : ℤ)⟧' ≫
      (Plus.ι.commShiftIso (1 : ℤ)).inv.app (DerivedCategory.Plus.Q.obj (K.truncLE n₀)))

/-- The canonical truncation triangle
`Q.obj (K.truncLE n₀) ⟶ Q.obj K ⟶ Q.obj (K.truncGE n₁) ⟶ (Q.obj (K.truncLE n₀))⟦1⟧`
in `DerivedCategory.Plus C` when `n₀ + 1 = n₁`. -/
@[expose, implicit_reducible]
def truncLEGETriangle (K : CochainComplex.Plus C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    Triangle (DerivedCategory.Plus C) :=
  Triangle.mk (DerivedCategory.Plus.Q.map (K.ιTruncLE n₀))
    (DerivedCategory.Plus.Q.map (K.πTruncGE n₁)) (truncLEGEδ K n₀ n₁ h)

/-- The canonical truncation triangle `truncLEGETriangle K n₀ n₁ h` is distinguished in
`DerivedCategory.Plus C`. -/
lemma truncLEGETriangle_distinguished (K : CochainComplex.Plus C) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁ := by lia) :
    truncLEGETriangle K n₀ n₁ h ∈ distTriang (DerivedCategory.Plus C) := by
  rw [mem_distTriang_iff]
  have hS := K.obj.shortComplexTruncLE_shortExact n₀
  let eLE : Plus.ι.obj (DerivedCategory.Plus.Q.obj (K.truncLE n₀)) ≅
      DerivedCategory.Q.obj (K.obj.shortComplexTruncLE n₀).X₁ :=
    ιQObjIso (K.truncLE n₀)
  let e₂ : Plus.ι.obj (DerivedCategory.Plus.Q.obj K) ≅
      DerivedCategory.Q.obj (K.obj.shortComplexTruncLE n₀).X₂ :=
    ιQObjIso K
  let eGE : Plus.ι.obj (DerivedCategory.Plus.Q.obj (K.truncGE n₁)) ≅
      DerivedCategory.Q.obj (K.obj.truncGE n₁) :=
    ιQObjIso (K.truncGE n₁)
  let eφ : DerivedCategory.Q.obj (K.obj.shortComplexTruncLE n₀).X₃ ≅
      DerivedCategory.Q.obj (K.obj.truncGE n₁) :=
    @asIso _ _ _ _ (DerivedCategory.Q.map (K.obj.shortComplexTruncLEX₃ToTruncGE n₀ n₁ h))
      ((DerivedCategory.isIso_Q_map_iff_quasiIso C _).2
        (by dsimp [CochainComplex.shortComplexTruncLEX₃ToTruncGE]; infer_instance))
  let e₃ := eGE ≪≫ eφ.symm
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _ ?_
  refine Triangle.isoMk _ _ eLE e₂ e₃ ?_ ?_ ?_
  · exact (QCompιIso C).hom.naturality (K.ιTruncLE n₀)
  · dsimp only [Functor.mapTriangle_obj, truncLEGETriangle, DerivedCategory.triangleOfSES,
      Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₂, e₃, Iso.trans_hom, Iso.symm_hom]
    rw [← cancel_mono eφ.hom, assoc, assoc, eφ.inv_hom_id, comp_id]
    have hnat : Plus.ι.map (DerivedCategory.Plus.Q.map (K.πTruncGE n₁)) ≫ eGE.hom =
        e₂.hom ≫ DerivedCategory.Q.map (K.obj.πTruncGE n₁) :=
      (QCompιIso C).hom.naturality (K.πTruncGE n₁)
    rw [hnat, assoc]
    dsimp only [eφ, asIso_hom]
    rw [← DerivedCategory.Q.map_comp,
      ← CochainComplex.g_shortComplexTruncLEX₃ToTruncGE K.obj n₀ n₁ h]
  · dsimp only [Functor.mapTriangle_obj, truncLEGETriangle, DerivedCategory.triangleOfSES,
      Triangle.mk_obj₁, Triangle.mk_obj₃, Triangle.mk_mor₃, e₃, Iso.trans_hom, Iso.symm_hom]
    rw [assoc]
    unfold truncLEGEδ
    rw [DerivedCategory.TStructure.t.plus.fullyFaithfulι.map_preimage]
    have hq : eLE.inv⟦(1 : ℤ)⟧' ≫ eLE.hom⟦(1 : ℤ)⟧' =
        𝟙 ((DerivedCategory.Q.obj (K.obj.shortComplexTruncLE n₀).X₁)⟦(1 : ℤ)⟧) := by
      rw [← (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_comp, eLE.inv_hom_id,
        (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id]
    dsimp only [eGE, eLE, eφ] at hq ⊢
    rw [assoc, assoc, assoc, assoc, Iso.inv_hom_id_app_assoc, hq, comp_id, assoc]

end DerivedCategory.Plus
