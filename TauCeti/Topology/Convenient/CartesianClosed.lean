/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Convenient.Category
public import Mathlib.Topology.Convenient.HomSpace

/-!
# Cartesian closed structure on `X`-generated topological spaces

Let `X : ι → Type u` be a family of topological spaces. This file establishes the Cartesian
monoidal closed structure on both Mathlib's category `ContinuousGeneratedByCat X` of topological
spaces with `X`-continuous maps and the full subcategory `GeneratedByTopCat X` of `X`-generated
spaces inside `TopCat`.

* Every family `X` yields explicit finite products on `ContinuousGeneratedByCat X` (with the
  ordinary product topology on `Y × Z`) and on `GeneratedByTopCat X` (with the `X`-generated
  topology `WithGeneratedByTopology X (Y × Z)`), giving `CartesianMonoidalCategory` and
  `BraidedCategory` instances on both categories.
* Under the two convenience hypotheses `[∀ i, LocallyCompactSpace (X i)]` and
  `[∀ i j, IsGeneratedBy X (X i × X j)]`, Mathlib's `ContinuousMapGeneratedBy.curryEquiv` supplies
  explicit `MonoidalClosed` instances on both `ContinuousGeneratedByCat X` (internal hom
  `ContinuousMapGeneratedBy X Y Z`) and `GeneratedByTopCat X` (internal hom
  `WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z)`).
* Under the same two hypotheses, the ordinary product `Y × Z` of two `X`-generated spaces is
  already `X`-generated whenever either factor is locally compact
  (`Topology.IsGeneratedBy.prod_of_locallyCompact_left`, `prod_of_locallyCompact_right`), so the
  categorical product in `GeneratedByTopCat X` agrees with the ordinary product in `TopCat`
  (`GeneratedByTopCat.prodIsoTopCat`).
* For any space `Y : TopCat`, the coreflection counit `(GeneratedByTopCat.adjCounit).app Y` is an
  isomorphism in `TopCat` if and only if `Y` is `X`-generated
  (`GeneratedByTopCat.isIso_adjCounit_app_iff`).

## References

* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*,
  Arch. Math. (Basel) 22 (1971), 545–555.
* M. Escardó, J. Lawson and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
-/

public section

universe t u v v' w

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology

namespace Topology

section Product

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

/-- If `Y` is locally compact and `X`-generated, `Z` is `X`-generated, and every product `Y × X i`
is `X`-generated, then the ordinary product `Y × Z` is `X`-generated. -/
theorem IsGeneratedBy.prod_of_locallyCompact_left_of_forall
    [LocallyCompactSpace Y] [IsGeneratedBy X Y] [IsGeneratedBy X Z]
    (hYX : ∀ i, IsGeneratedBy X (Y × X i)) :
    IsGeneratedBy X (Y × Z) := by
  refine ⟨?_⟩
  let e : Y × Z → WithGeneratedByTopology X (Y × Z) := WithGeneratedByTopology.equiv.symm
  have he : ContinuousGeneratedBy X e :=
    (WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy X (Y × Z)).prop
  have hslice (z : Z) : Continuous (fun y : Y ↦ e (y, z)) :=
    (IsGeneratedBy.continuous_iff X _).2 fun i f ↦
      he ⟨fun x ↦ (f x, z), f.continuous.prodMk continuous_const⟩
  let φ : Z → C(Y, WithGeneratedByTopology X (Y × Z)) := fun z ↦ ⟨fun y ↦ e (y, z), hslice z⟩
  have hφ : Continuous φ := by
    refine (IsGeneratedBy.continuous_iff X φ).2 fun i g ↦ ?_
    have : IsGeneratedBy X (Y × X i) := hYX i
    have hcont : Continuous (fun p : Y × X i ↦ e (p.1, g p.2)) :=
      (IsGeneratedBy.continuous_iff X _).2 fun j p ↦
        he ⟨fun a ↦ ((p a).1, g (p a).2),
          (continuous_fst.comp p.continuous).prodMk
            (g.continuous.comp (continuous_snd.comp p.continuous))⟩
    exact (ContinuousMap.curry ⟨fun p : X i × Y ↦ e (p.2, g p.1),
      hcont.comp continuous_swap⟩).continuous
  exact (ContinuousMap.continuous_uncurry_of_continuous ⟨φ, hφ⟩).comp continuous_swap

/-- If `X` is a convenient family of locally compact test spaces closed under binary products,
then the ordinary product `Y × Z` of two `X`-generated spaces is `X`-generated whenever `Y` is
locally compact. -/
theorem IsGeneratedBy.prod_of_locallyCompact_left
    [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]
    [LocallyCompactSpace Y] [IsGeneratedBy X Y] [IsGeneratedBy X Z] :
    IsGeneratedBy X (Y × Z) := by
  refine IsGeneratedBy.prod_of_locallyCompact_left_of_forall fun i ↦ ?_
  have : IsGeneratedBy X (X i × Y) :=
    IsGeneratedBy.prod_of_locallyCompact_left_of_forall fun j ↦ inferInstance
  exact (Homeomorph.prodComm (X i) Y).isQuotientMap.isGeneratedBy

/-- If `X` is a convenient family of locally compact test spaces closed under binary products,
then the ordinary product `Y × Z` of two `X`-generated spaces is `X`-generated whenever `Z` is
locally compact. -/
theorem IsGeneratedBy.prod_of_locallyCompact_right
    [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]
    [IsGeneratedBy X Y] [LocallyCompactSpace Z] [IsGeneratedBy X Z] :
    IsGeneratedBy X (Y × Z) := by
  have : IsGeneratedBy X (Z × Y) := IsGeneratedBy.prod_of_locallyCompact_left
  exact (Homeomorph.prodComm Z Y).isQuotientMap.isGeneratedBy

end Product

namespace ContinuousMapGeneratedBy

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

/-- View an ordinary continuous map as an `X`-continuous map. -/
def ofContinuousMap (f : C(Y, Z)) : ContinuousMapGeneratedBy X Y Z where
  toFun := f
  prop := f.continuous.continuousGeneratedBy

@[simp]
theorem ofContinuousMap_apply (f : C(Y, Z)) (y : Y) :
    ofContinuousMap (X := X) f y = f y := by
  rfl

/-- The canonical map `C(Y, Z) → ContinuousMapGeneratedBy X Y Z` is continuous from the
compact-open topology to the test-open topology. -/
@[continuity, fun_prop]
theorem continuous_ofContinuousMap :
    Continuous (ofContinuousMap (X := X) (Y := Y) (Z := Z)) := by
  rw [ContinuousMapGeneratedBy.continuous_iff]
  intro i f
  exact ContinuousMap.continuous_precomp f

/-- When the domain `Y` is `X`-generated, every `X`-continuous map `Y → Z` is continuous. -/
def toContinuousMap [IsGeneratedBy X Y] (f : ContinuousMapGeneratedBy X Y Z) : C(Y, Z) where
  toFun := f
  continuous_toFun := (IsGeneratedBy.continuous_iff X f).2 f.prop

@[simp]
theorem toContinuousMap_apply [IsGeneratedBy X Y] (f : ContinuousMapGeneratedBy X Y Z) (y : Y) :
    toContinuousMap f y = f y := by
  rfl

/-- When the domain `Y` is `X`-generated, `X`-continuous maps `Y → Z` correspond bijectively to
continuous maps `C(Y, Z)`. -/
def equivContinuousMap [IsGeneratedBy X Y] : ContinuousMapGeneratedBy X Y Z ≃ C(Y, Z) where
  toFun := toContinuousMap
  invFun := ofContinuousMap
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equivContinuousMap_apply [IsGeneratedBy X Y] (f : ContinuousMapGeneratedBy X Y Z) :
    equivContinuousMap f = toContinuousMap f := by
  rfl

@[simp]
theorem equivContinuousMap_symm_apply [IsGeneratedBy X Y] (f : C(Y, Z)) :
    equivContinuousMap (X := X).symm f = ofContinuousMap f := by
  rfl

end ContinuousMapGeneratedBy

end Topology

namespace ContinuousGeneratedByCat

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

/-- `PUnit` is a terminal object in `ContinuousGeneratedByCat X`. -/
def isTerminalPUnit : IsTerminal (of (X := X) PUnit.{v + 1}) :=
  IsTerminal.ofUniqueHom (fun _ ↦ homMk (fun _ ↦ PUnit.unit) continuous_const.continuousGeneratedBy)
    fun _ _ ↦ by ext

/-- The explicit binary product fan of `Y` and `Z` in `ContinuousGeneratedByCat X`, carried by the
ordinary product space `Y × Z`. -/
@[expose]
def prodBinaryFan (Y Z : ContinuousGeneratedByCat.{v} X) : BinaryFan Y Z :=
  BinaryFan.mk
    (P := of (X := X) (Y × Z))
    (homMk Prod.fst continuous_fst.continuousGeneratedBy)
    (homMk Prod.snd continuous_snd.continuousGeneratedBy)

/-- The ordinary product space `Y × Z` is a binary product in `ContinuousGeneratedByCat X`. -/
def prodBinaryFanIsLimit (Y Z : ContinuousGeneratedByCat.{v} X) :
    IsLimit (prodBinaryFan Y Z) :=
  BinaryFan.IsLimit.mk _
    (fun {W} f g ↦ homMk (fun w ↦ (f w, g w)) fun _ p ↦ (f.hom.prop p).prodMk (g.hom.prop p))
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ _ hm₁ hm₂ ↦ by
      ext w
      exact Prod.ext (congrArg (fun k ↦ k.hom w) hm₁) (congrArg (fun k ↦ k.hom w) hm₂))

instance instCartesianMonoidalCategory :
    CartesianMonoidalCategory (ContinuousGeneratedByCat.{v} X) :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun Y Z ↦ ⟨prodBinaryFan Y Z, prodBinaryFanIsLimit Y Z⟩)

instance instBraidedCategory : BraidedCategory (ContinuousGeneratedByCat.{v} X) :=
  .ofCartesianMonoidalCategory

@[simp]
theorem fst_apply {Y Z : ContinuousGeneratedByCat.{v} X} (p : ↑(Y ⊗ Z)) :
    fst Y Z p = p.1 := by
  rfl

@[simp]
theorem snd_apply {Y Z : ContinuousGeneratedByCat.{v} X} (p : ↑(Y ⊗ Z)) :
    snd Y Z p = p.2 := by
  rfl

@[simp]
theorem lift_apply {W Y Z : ContinuousGeneratedByCat.{v} X} (f : W ⟶ Y) (g : W ⟶ Z) (w : W) :
    CartesianMonoidalCategory.lift f g w = (f w, g w) := by
  rfl

@[simp]
theorem tensorHom_apply {W Y Z T : ContinuousGeneratedByCat.{v} X} (f : W ⟶ Y) (g : Z ⟶ T)
    (p : ↑(W ⊗ Z)) : (f ⊗ₘ g) p = (f p.1, g p.2) := by
  rfl

@[simp]
theorem whiskerLeft_apply (Y : ContinuousGeneratedByCat.{v} X)
    {Z T : ContinuousGeneratedByCat.{v} X} (g : Z ⟶ T) (p : ↑(Y ⊗ Z)) :
    (Y ◁ g) p = (p.1, g p.2) := by
  rfl

@[simp]
theorem whiskerRight_apply {Y Z : ContinuousGeneratedByCat.{v} X} (f : Y ⟶ Z)
    (T : ContinuousGeneratedByCat.{v} X) (p : ↑(Y ⊗ T)) :
    (f ▷ T) p = (f p.1, p.2) := by
  rfl

@[simp]
theorem braiding_hom_apply {Y Z : ContinuousGeneratedByCat.{v} X} (p : ↑(Y ⊗ Z)) :
    (β_ Y Z).hom p = (p.2, p.1) := by
  rfl

@[simp]
theorem braiding_inv_apply {Y Z : ContinuousGeneratedByCat.{v} X} (p : ↑(Z ⊗ Y)) :
    (β_ Y Z).inv p = (p.2, p.1) := by
  rfl

section Closed

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

/-- The internal hom functor `Z ↦ ContinuousMapGeneratedBy X Y Z` on
`ContinuousGeneratedByCat X`. -/
@[expose, simps! obj]
def homFunctor (Y : ContinuousGeneratedByCat.{v} X) :
    ContinuousGeneratedByCat.{v} X ⥤ ContinuousGeneratedByCat.{v} X where
  obj Z := of (X := X) (ContinuousMapGeneratedBy X Y Z)
  map p := homMk p.hom.postcomp p.hom.postcomp.prop

theorem homFunctor_map_apply (Y : ContinuousGeneratedByCat.{v} X)
    {Z T : ContinuousGeneratedByCat.{v} X} (p : Z ⟶ T) (g : ContinuousMapGeneratedBy X Y Z) :
    (homFunctor Y).map p g = p.hom.postcomp g := by
  rfl

/-- Currying in `ContinuousGeneratedByCat X`, given directly by
`ContinuousMapGeneratedBy.curryEquiv`. -/
def curryEquiv (Y Z T : ContinuousGeneratedByCat.{v} X) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ of (X := X) (ContinuousMapGeneratedBy X Y T)) where
  toFun f := ⟨ContinuousMapGeneratedBy.curryEquiv f.hom⟩
  invFun g := ⟨ContinuousMapGeneratedBy.curryEquiv.symm g.hom⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem curryEquiv_apply_apply {Y Z T : ContinuousGeneratedByCat.{v} X} (f : Y ⊗ Z ⟶ T)
    (z : Z) (y : Y) : curryEquiv Y Z T f z y = f (y, z) := by
  rfl

theorem curryEquiv_symm_apply {Y Z T : ContinuousGeneratedByCat.{v} X}
    (g : Z ⟶ of (X := X) (ContinuousMapGeneratedBy X Y T)) (p : ↑(Y ⊗ Z)) :
    (curryEquiv Y Z T).symm g p = g p.2 p.1 := by
  rfl

/-- The adjunction `Y ⊗ - ⊣ ContinuousMapGeneratedBy X Y -` on `ContinuousGeneratedByCat X`. -/
def tensorLeftAdjunction (Y : ContinuousGeneratedByCat.{v} X) :
    tensorLeft Y ⊣ homFunctor Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

instance closed (Y : ContinuousGeneratedByCat.{v} X) : Closed Y where
  rightAdj := homFunctor Y
  adj := tensorLeftAdjunction Y

instance instMonoidalClosed : MonoidalClosed (ContinuousGeneratedByCat.{v} X) where
  closed := closed

theorem ihom_obj (Y Z : ContinuousGeneratedByCat.{v} X) :
    (ihom Y).obj Z = of (X := X) (ContinuousMapGeneratedBy X Y Z) := by
  rfl

theorem ev_app_apply (Y Z : ContinuousGeneratedByCat.{v} X) (y : Y)
    (g : ContinuousMapGeneratedBy X Y Z) :
    (ihom.ev Y).app Z (y, g) = g y := by
  rfl

end Closed

end ContinuousGeneratedByCat

namespace GeneratedByTopCat

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

/-- The coreflection counit `WithGeneratedByTopology X Y → Y` is an isomorphism in `TopCat` if and
only if `Y` is `X`-generated. -/
theorem isIso_adjCounit_app_iff (Y : TopCat.{v}) :
    IsIso ((adjCounit (X := X)).app Y) ↔ IsGeneratedBy X Y := by
  refine ⟨fun _ ↦ ⟨?_⟩, fun _ ↦ ?_⟩
  · let e : WithGeneratedByTopology X Y ≃ₜ Y :=
      TopCat.homeoOfIso (asIso ((adjCounit (X := X)).app Y))
    have hinv : ⇑e.symm = (WithGeneratedByTopology.equiv (X := X) (Y := Y)).symm := by
      ext y
      exact e.injective (e.apply_symm_apply y)
    exact hinv ▸ e.symm.continuous
  · have h : (adjCounit (X := X)).app Y =
        (TopCat.isoOfHomeo (IsGeneratedBy.homeomorph (X := X) (Y := Y))).hom := rfl
    rw [h]
    infer_instance

/-- When `Y` is `X`-generated, the coreflection counit at `Y` is an isomorphism in `TopCat`. -/
instance isIso_adjCounit_app (Y : TopCat.{v}) [IsGeneratedBy X Y] :
    IsIso ((adjCounit (X := X)).app Y) :=
  (isIso_adjCounit_app_iff Y).2 inferInstance

/-- `PUnit` is a terminal object in `GeneratedByTopCat X`. -/
def isTerminalPUnit : IsTerminal (of (X := X) PUnit.{v + 1}) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ ObjectProperty.homMk (TopCat.ofHom (ContinuousMap.const _ PUnit.unit)))
    fun _ _ ↦ by ext

/-- The explicit binary product fan of `Y` and `Z` in `GeneratedByTopCat X`, carried by
`WithGeneratedByTopology X (Y × Z)`. -/
@[expose]
def prodBinaryFan (Y Z : GeneratedByTopCat.{v} X) : BinaryFan Y Z :=
  BinaryFan.mk
    (P := of (X := X) (WithGeneratedByTopology X (Y × Z)))
    (ObjectProperty.homMk (TopCat.ofHom
      ⟨Prod.fst ∘ WithGeneratedByTopology.equiv (X := X),
        continuous_fst.comp (WithGeneratedByTopology.continuous_equiv (X := X))⟩))
    (ObjectProperty.homMk (TopCat.ofHom
      ⟨Prod.snd ∘ WithGeneratedByTopology.equiv (X := X),
        continuous_snd.comp (WithGeneratedByTopology.continuous_equiv (X := X))⟩))

/-- `WithGeneratedByTopology X (Y × Z)` is a binary product in `GeneratedByTopCat X`. -/
def prodBinaryFanIsLimit (Y Z : GeneratedByTopCat.{v} X) : IsLimit (prodBinaryFan Y Z) :=
  BinaryFan.IsLimit.mk _
    (fun {W} f g ↦ ObjectProperty.homMk (TopCat.ofHom
      ⟨(WithGeneratedByTopology.equiv (X := X)).symm ∘ fun w ↦ (f.hom w, g.hom w),
        (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := X) _).2
          (f.hom.hom.continuous.prodMk g.hom.hom.continuous)⟩))
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ _ hm₁ hm₂ ↦ by
      ext w
      apply (WithGeneratedByTopology.equiv (X := X)).injective
      exact Prod.ext
        (congrArg (fun k ↦ k.hom w) hm₁)
        (congrArg (fun k ↦ k.hom w) hm₂))

instance instCartesianMonoidalCategory : CartesianMonoidalCategory (GeneratedByTopCat.{v} X) :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun Y Z ↦ ⟨prodBinaryFan Y Z, prodBinaryFanIsLimit Y Z⟩)

instance instBraidedCategory : BraidedCategory (GeneratedByTopCat.{v} X) :=
  .ofCartesianMonoidalCategory

@[simp]
theorem fst_apply {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Y ⊗ Z)) :
    fst Y Z p = (WithGeneratedByTopology.equiv (X := X) p).1 := by
  rfl

@[simp]
theorem snd_apply {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Y ⊗ Z)) :
    snd Y Z p = (WithGeneratedByTopology.equiv (X := X) p).2 := by
  rfl

@[simp]
theorem lift_apply {W Y Z : GeneratedByTopCat.{v} X} (f : W ⟶ Y) (g : W ⟶ Z) (w : W) :
    CartesianMonoidalCategory.lift f g w =
      (WithGeneratedByTopology.equiv (X := X)).symm (f w, g w) := by
  rfl

@[simp]
theorem tensorHom_apply {W Y Z T : GeneratedByTopCat.{v} X} (f : W ⟶ Y) (g : Z ⟶ T)
    (p : ↑(W ⊗ Z)) :
    (f ⊗ₘ g) p = (WithGeneratedByTopology.equiv (X := X)).symm
      (f (WithGeneratedByTopology.equiv (X := X) p).1,
        g (WithGeneratedByTopology.equiv (X := X) p).2) := by
  rfl

@[simp]
theorem whiskerLeft_apply (Y : GeneratedByTopCat.{v} X)
    {Z T : GeneratedByTopCat.{v} X} (g : Z ⟶ T) (p : ↑(Y ⊗ Z)) :
    (Y ◁ g) p = (WithGeneratedByTopology.equiv (X := X)).symm
      ((WithGeneratedByTopology.equiv (X := X) p).1,
        g (WithGeneratedByTopology.equiv (X := X) p).2) := by
  rfl

@[simp]
theorem whiskerRight_apply {Y Z : GeneratedByTopCat.{v} X} (f : Y ⟶ Z)
    (T : GeneratedByTopCat.{v} X) (p : ↑(Y ⊗ T)) :
    (f ▷ T) p = (WithGeneratedByTopology.equiv (X := X)).symm
      (f (WithGeneratedByTopology.equiv (X := X) p).1,
        (WithGeneratedByTopology.equiv (X := X) p).2) := by
  rfl

@[simp]
theorem braiding_hom_apply {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Y ⊗ Z)) :
    (β_ Y Z).hom p = (WithGeneratedByTopology.equiv (X := X)).symm
      ((WithGeneratedByTopology.equiv (X := X) p).2,
        (WithGeneratedByTopology.equiv (X := X) p).1) := by
  rfl

/-- When the ordinary product `Y × Z` is already `X`-generated, the categorical product `Y ⊗ Z` in
`GeneratedByTopCat X` is isomorphic in `TopCat` to the ordinary product `Y × Z`. -/
def prodIsoTopCat (Y Z : GeneratedByTopCat.{v} X) [IsGeneratedBy X (Y × Z)] :
    (Y ⊗ Z).obj ≅ Y.obj ⊗ Z.obj :=
  TopCat.isoOfHomeo (IsGeneratedBy.homeomorph (X := X) (Y := Y × Z))

@[simp]
theorem prodIsoTopCat_hom_apply (Y Z : GeneratedByTopCat.{v} X) [IsGeneratedBy X (Y × Z)]
    (p : ↑(Y ⊗ Z)) :
    (prodIsoTopCat Y Z).hom p = WithGeneratedByTopology.equiv (X := X) p := by
  rfl

@[simp]
theorem prodIsoTopCat_inv_apply (Y Z : GeneratedByTopCat.{v} X) [IsGeneratedBy X (Y × Z)]
    (p : ↑(Y.obj ⊗ Z.obj)) :
    (prodIsoTopCat Y Z).inv p = (WithGeneratedByTopology.equiv (X := X)).symm p := by
  rfl

@[reassoc (attr := simp)]
theorem prodIsoTopCat_hom_fst (Y Z : GeneratedByTopCat.{v} X) [IsGeneratedBy X (Y × Z)] :
    (prodIsoTopCat Y Z).hom ≫ CartesianMonoidalCategory.fst Y.obj Z.obj =
      (CartesianMonoidalCategory.fst Y Z).hom := by
  rfl

@[reassoc (attr := simp)]
theorem prodIsoTopCat_hom_snd (Y Z : GeneratedByTopCat.{v} X) [IsGeneratedBy X (Y × Z)] :
    (prodIsoTopCat Y Z).hom ≫ CartesianMonoidalCategory.snd Y.obj Z.obj =
      (CartesianMonoidalCategory.snd Y Z).hom := by
  rfl

section Closed

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

/-- The internal hom functor `Z ↦ WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z)` on
`GeneratedByTopCat X`. -/
@[expose, simps! obj]
def homFunctor (Y : GeneratedByTopCat.{v} X) :
    GeneratedByTopCat.{v} X ⥤ GeneratedByTopCat.{v} X where
  obj Z := of (X := X) (WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z))
  map p := ObjectProperty.homMk (TopCat.ofHom
    (ContinuousMapGeneratedBy.ofContinuousMap (X := X) p.hom.hom).postcomp.prop.continuousMap)

theorem homFunctor_map_apply (Y : GeneratedByTopCat.{v} X) {Z T : GeneratedByTopCat.{v} X}
    (p : Z ⟶ T) (g : WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z)) (y : Y) :
    WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y T)
        ((homFunctor Y).map p g) y =
      p (WithGeneratedByTopology.equiv (X := X) g y) := by
  rfl

/-- Currying in `GeneratedByTopCat X`: continuous maps `k(Y × Z) → T` correspond bijectively to
continuous maps `Z → k(ContinuousMapGeneratedBy X Y T)`. -/
def curryEquiv (Y Z T : GeneratedByTopCat.{v} X) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ (homFunctor Y).obj T) where
  toFun f :=
    let f' : ContinuousMapGeneratedBy X (Y × Z) T :=
      ⟨f.hom ∘ (WithGeneratedByTopology.equiv (X := X)).symm, by
        rw [continuousGeneratedBy_iff]
        have h : (WithGeneratedByTopology.equiv (X := X) (Y := T)).symm ∘
            (f.hom ∘ (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)).symm) ∘
            WithGeneratedByTopology.equiv (X := X) (Y := Y × Z) =
            (WithGeneratedByTopology.equiv (X := X) (Y := T)).symm ∘ f.hom := by
          ext p
          rfl
        rw [h]
        exact (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := X) _).2 f.hom.hom.continuous⟩
    let g := ContinuousMapGeneratedBy.curryEquiv f'
    ObjectProperty.homMk (TopCat.ofHom
      ⟨(WithGeneratedByTopology.equiv (X := X)).symm ∘ g,
        (IsGeneratedBy.continuous_iff X _).2 fun _ k ↦
          (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := X) _).2 (g.prop k)⟩)
  invFun g :=
    let g' : ContinuousMapGeneratedBy X Z (ContinuousMapGeneratedBy X Y T) :=
      ⟨WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y T) ∘ g.hom,
        ((WithGeneratedByTopology.continuous_equiv (X := X)
          (Y := ContinuousMapGeneratedBy X Y T)).comp
          g.hom.hom.continuous).continuousGeneratedBy⟩
    let f := ContinuousMapGeneratedBy.curryEquiv.symm g'
    ObjectProperty.homMk (TopCat.ofHom
      ⟨f ∘ WithGeneratedByTopology.equiv (X := X),
        (WithGeneratedByTopology.continuous_equiv (X := X)).comp f.prop.continuousMap.continuous⟩)
  left_inv _ := rfl
  right_inv _ := rfl

theorem curryEquiv_apply_apply {Y Z T : GeneratedByTopCat.{v} X} (f : Y ⊗ Z ⟶ T)
    (z : Z) (y : Y) :
    WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y T)
        (curryEquiv Y Z T f z) y =
      f ((WithGeneratedByTopology.equiv (X := X)).symm (y, z)) := by
  rfl

theorem curryEquiv_symm_apply {Y Z T : GeneratedByTopCat.{v} X}
    (g : Z ⟶ (homFunctor Y).obj T) (p : ↑(Y ⊗ Z)) :
    (curryEquiv Y Z T).symm g p =
      WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y T)
        (g (WithGeneratedByTopology.equiv (X := X) p).2)
        (WithGeneratedByTopology.equiv (X := X) p).1 := by
  rfl

/-- The adjunction `Y ⊗ - ⊣ homFunctor Y` on `GeneratedByTopCat X`. -/
def tensorLeftAdjunction (Y : GeneratedByTopCat.{v} X) :
    tensorLeft Y ⊣ homFunctor Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := by
        ext z
        rfl }

instance closed (Y : GeneratedByTopCat.{v} X) : Closed Y where
  rightAdj := homFunctor Y
  adj := tensorLeftAdjunction Y

instance instMonoidalClosed : MonoidalClosed (GeneratedByTopCat.{v} X) where
  closed := closed

theorem ihom_obj (Y Z : GeneratedByTopCat.{v} X) :
    (ihom Y).obj Z = of (X := X) (WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z)) := by
  rfl

theorem ev_app_apply (Y Z : GeneratedByTopCat.{v} X) (y : Y)
    (g : WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z)) :
    (ihom.ev Y).app Z ((WithGeneratedByTopology.equiv (X := X)).symm (y, g)) =
      WithGeneratedByTopology.equiv (X := X) g y := by
  rfl

end Closed

end GeneratedByTopCat
