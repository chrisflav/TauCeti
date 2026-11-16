/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Dagger.Monoidal
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Balanced
public import TauCeti.CategoryTheory.Monoidal.Pivotal.LeftDual
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Trace
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive

/-!
# Unitary dual functors and induced pivotal structures

A *unitary dual functor* on a right rigid dagger monoidal category `C` is a choice of right duals
whose right adjoint mates commute with the dagger (`dagger (fᘁ) = (dagger f)ᘁ`) and whose tensor
comparisons `rightDualTensorIso X Y : (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` are unitary. Unitarity of the unit
comparison `rightDualUnitIso C : (𝟙_ C)ᘁ ≅ 𝟙_ C` follows automatically from left unitality.

Combining the dagger with right adjoint mates defines the covariant *conjugate* operation
`TauCeti.dualConj f := dagger (fᘁ) = (dagger f)ᘁ : Xᘁ ⟶ Yᘁ`, which assembles into a dagger
monoidal functor `TauCeti.dualConjFunctor C : C ⥤ Cᴹᵒᵖ` (a bi-involution in the sense of
Henriques–Penneys–Tener and Penneys).

Comparing `TauCeti.daggerExactPairing X Xᘁ : ExactPairing Xᘁ X` with the chosen right dual
pairing of `Xᘁ` gives a canonical monoidal natural isomorphism
`TauCeti.unitaryDualPivotalNatIso C : 𝟭 C ≅ doubleRightDualFunctor C` whose components
`TauCeti.unitaryDualPivotalIsoApp X : X ≅ Xᘁᘁ` are unitary and satisfy the bi-involution
coherence `dualConj (unitaryDualPivotalIsoApp X).hom = (unitaryDualPivotalIsoApp Xᘁ).hom`. Via
`TauCeti.pivotalCategoryOfRightRigid`, this induces a rigid structure
`TauCeti.unitaryDualRigidCategory` whose left duals are the right duals with dagger-adjoint
evaluations and coevaluations, together with a `TauCeti.PivotalCategory` structure
`TauCeti.unitaryDualPivotalCategory`.

For any pivotal structure matching `TauCeti.unitaryDualPivotalIsoApp`, the categorical traces
`TauCeti.leftTrace` and `TauCeti.rightTrace` satisfy the dagger-positive formulas
`leftTrace f = dagger (ε_ X Xᘁ) ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ` and
`rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ dagger (η_ X Xᘁ)`. In particular they commute with the
dagger, send `dagger g ≫ g` and `g ≫ dagger g` to elements of the same form in `𝟙_ C ⟶ 𝟙_ C`,
and yield self-adjoint dimensions that are nonzero on nonzero objects whenever the dagger is
faithful.

In a braided (or dagger braided) monoidal category, the twist of `TauCeti.balancedOfBraidedPivotal`
for the induced pivotal structure is the identity at `X` precisely when
`unitaryDualPivotalIsoApp X` agrees with `TauCeti.drinfeldIso X`, equivalently when
`dagger (η_ X Xᘁ) = (β_ X Xᘁ).hom ≫ ε_ X Xᘁ`.

## Main declarations

* `TauCeti.UnitaryDualFunctor`: unitary dual functor structure on a right rigid dagger monoidal
  category, with `TauCeti.isUnitary_rightDualUnitIso`;
* `TauCeti.dualConj` and `TauCeti.dualConjFunctor`: the covariant dagger-monoidal conjugate functor
  `C ⥤ Cᴹᵒᵖ` and its additive and conjugate-linear laws;
* `TauCeti.unitaryDualPivotalIsoApp` and `TauCeti.unitaryDualPivotalNatIso`: the canonical unitary
  monoidal natural isomorphism `𝟭 C ≅ doubleRightDualFunctor C`, with
  `TauCeti.isUnitary_unitaryDualPivotalIsoApp` and `TauCeti.dualConj_unitaryDualPivotalIsoApp_hom`;
* `TauCeti.unitaryDualRigidCategory` and `TauCeti.unitaryDualPivotalCategory`: the induced rigid
  and pivotal structures;
* `TauCeti.leftTrace_eq_dagger_evaluation`, `TauCeti.rightTrace_eq_dagger_coevaluation`,
  `TauCeti.leftTrace_dagger_comp`, `TauCeti.rightTrace_comp_dagger`,
  `TauCeti.leftDim_ne_zero_of_dagger_faithful`, and `TauCeti.rightDim_ne_zero_of_dagger_faithful`:
  dagger-compatibility, algebraic positivity, and nonvanishing of traces and dimensions;
* `TauCeti.unitaryDualPivotalIsoApp_eq_drinfeldIso_iff_dagger_coevaluation` and
  `TauCeti.balancedOfBraidedPivotal_twist_eq_id_iff`: compatibility with a braiding and triviality
  of the induced twist.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1
* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  [arXiv:1808.00323](https://arxiv.org/abs/1808.00323), §§2.1–2.2
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory MonoidalOpposite ExactPairing
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe w v u

namespace TauCeti

/-- A *unitary dual functor* on a right rigid dagger category: right adjoint mates commute with the
dagger, and the tensor comparisons `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` are unitary. In a dagger monoidal
category, unitarity of the unit comparison `(𝟙_ C)ᘁ ≅ 𝟙_ C` follows automatically
(`TauCeti.isUnitary_rightDualUnitIso`). -/
class UnitaryDualFunctor (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [DaggerCategory C] [RightRigidCategory C] : Prop where
  /-- Taking right adjoint mates commutes with the dagger. -/
  dagger_rightAdjointMate : ∀ {X Y : C} (f : X ⟶ Y), dagger (fᘁ) = (dagger f)ᘁ
  /-- The tensor comparisons `rightDualTensorIso X Y : (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` are unitary. -/
  isUnitary_rightDualTensorIso : ∀ (X Y : C), IsUnitary (rightDualTensorIso X Y).hom

export UnitaryDualFunctor (dagger_rightAdjointMate isUnitary_rightDualTensorIso)

attribute [simp] isUnitary_rightDualTensorIso

section UnitaryDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [RightRigidCategory C] [UnitaryDualFunctor C]

/-- The dagger of `(rightDualTensorIso X Y).hom` is `(rightDualTensorIso X Y).inv`. -/
@[simp]
theorem dagger_rightDualTensorIso_hom (X Y : C) :
    dagger (rightDualTensorIso X Y).hom = (rightDualTensorIso X Y).inv :=
  (rightDualTensorIso X Y).dagger_hom_eq_inv_of_isUnitary (isUnitary_rightDualTensorIso X Y)

/-- The dagger of `(rightDualTensorIso X Y).inv` is `(rightDualTensorIso X Y).hom`. -/
@[simp]
theorem dagger_rightDualTensorIso_inv (X Y : C) :
    dagger (rightDualTensorIso X Y).inv = (rightDualTensorIso X Y).hom := by
  rw [← dagger_rightDualTensorIso_hom, dagger_dagger]

/-- The inverse tensor comparisons `Yᘁ ⊗ Xᘁ ⟶ (X ⊗ Y)ᘁ` are unitary. -/
@[simp]
theorem isUnitary_rightDualTensorIso_inv (X Y : C) : IsUnitary (rightDualTensorIso X Y).inv := by
  rw [← dagger_rightDualTensorIso_hom]
  exact (isUnitary_rightDualTensorIso X Y).dagger

/-- Taking the right adjoint mate preserves unitary arrows. -/
theorem IsUnitary.rightAdjointMate {X Y : C} {f : X ⟶ Y} (hf : IsUnitary f) :
    IsUnitary (fᘁ) := by
  rw [isUnitary_iff, dagger_rightAdjointMate, ← comp_rightAdjointMate, ← comp_rightAdjointMate,
    hf.dagger_hom_id, hf.hom_dagger_id, rightAdjointMate_id, rightAdjointMate_id]
  exact ⟨rfl, rfl⟩

/-- Taking the right adjoint mate preserves and reflects unitary arrows. -/
@[simp]
theorem isUnitary_rightAdjointMate_iff {X Y : C} (f : X ⟶ Y) :
    IsUnitary (fᘁ) ↔ IsUnitary f := by
  refine ⟨fun h => ?_, IsUnitary.rightAdjointMate⟩
  rw [isUnitary_iff]
  have h1 : (dagger f ≫ f)ᘁ = (𝟙 Y)ᘁ := by
    rw [comp_rightAdjointMate, ← dagger_rightAdjointMate, h.hom_dagger_id, rightAdjointMate_id]
  have h2 : (f ≫ dagger f)ᘁ = (𝟙 X)ᘁ := by
    rw [comp_rightAdjointMate, ← dagger_rightAdjointMate, h.dagger_hom_id, rightAdjointMate_id]
  exact ⟨rightAdjointMate_injective h2, rightAdjointMate_injective h1⟩

variable [DaggerMonoidalCategory C]

/-- The unit comparison `rightDualUnitIso C : (𝟙_ C)ᘁ ≅ 𝟙_ C` is automatically unitary, as a
consequence of left unitality and unitarity of `rightDualTensorIso`. -/
@[simp]
theorem isUnitary_rightDualUnitIso : IsUnitary (rightDualUnitIso C).hom := by
  -- Use the rigid structure's right dual of `𝟙_ C` rather than `hasRightDualUnit`.
  let d1 : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  let I' : C := d1.rightDual
  let u : I' ≅ 𝟙_ C := rightDualUnitIso C
  -- Left unitality for `X = 𝟙_ C` writes `I' ◁ u.hom` as a composite of unitary morphisms.
  have hlu : (ρ_ I').inv =
      (@rightAdjointMate C _ _ (𝟙_ C ⊗ 𝟙_ C) (𝟙_ C) _ d1 (λ_ (𝟙_ C)).hom) ≫
        (@rightDualTensorIso C _ _ (𝟙_ C) (𝟙_ C) d1 d1 _).hom ≫ I' ◁ u.hom := by
    simpa only [u, ← rightDualUnitIso_hom] using
      @rightDualTensorIso_leftUnitality C _ _ (𝟙_ C) d1 d1 _
  have h1 : IsUnitary
      (@rightAdjointMate C _ _ (𝟙_ C ⊗ 𝟙_ C) (𝟙_ C) _ d1 (λ_ (𝟙_ C)).hom) :=
    (isUnitary_leftUnitor (𝟙_ C)).rightAdjointMate
  have h2 : IsUnitary (@rightDualTensorIso C _ _ (𝟙_ C) (𝟙_ C) d1 d1 _).hom :=
    isUnitary_rightDualTensorIso (𝟙_ C) (𝟙_ C)
  have hIu : IsUnitary (I' ◁ u.hom) := by
    have heq : I' ◁ u.hom =
        dagger (@rightDualTensorIso C _ _ (𝟙_ C) (𝟙_ C) d1 d1 _).hom ≫
          dagger (@rightAdjointMate C _ _ (𝟙_ C ⊗ 𝟙_ C) (𝟙_ C) _ d1 (λ_ (𝟙_ C)).hom) ≫
            (ρ_ I').inv := by
      rw [hlu, h1.dagger_hom_id_assoc, h2.dagger_hom_id_assoc]
    rw [heq]
    exact h2.dagger.comp (h1.dagger.comp (isUnitary_rightUnitor_inv I'))
  -- From `I' ◁ (u.hom ≫ dagger u.hom) = 𝟙`, conjugate by `u.hom ▷ I'` and `λ_`.
  have hId : I' ◁ (u.hom ≫ dagger u.hom) = 𝟙 (I' ⊗ I') := by
    simpa [MonoidalCategory.whiskerLeft_comp] using hIu.hom_dagger_id
  have h1d : 𝟙_ C ◁ (u.hom ≫ dagger u.hom) = 𝟙 (𝟙_ C ⊗ I') := by
    rw [← cancel_epi (u.hom ▷ I'), ← whisker_exchange, hId, Category.id_comp,
      Category.comp_id]
  have hud : u.hom ≫ dagger u.hom = 𝟙 I' := by
    have hnat := leftUnitor_naturality (u.hom ≫ dagger u.hom)
    rw [h1d, Category.id_comp] at hnat
    exact (cancel_epi (λ_ I').hom).mp (hnat.symm.trans (Category.comp_id _).symm)
  exact u.isUnitary_hom_iff.mpr ((cancel_epi u.hom).mp (hud.trans u.hom_inv_id.symm))

/-- The dagger of `(rightDualUnitIso C).hom` is `(rightDualUnitIso C).inv`. -/
@[simp]
theorem dagger_rightDualUnitIso_hom :
    dagger (rightDualUnitIso C).hom = (rightDualUnitIso C).inv :=
  (rightDualUnitIso C).dagger_hom_eq_inv_of_isUnitary isUnitary_rightDualUnitIso

/-- The dagger of `(rightDualUnitIso C).inv` is `(rightDualUnitIso C).hom`. -/
@[simp]
theorem dagger_rightDualUnitIso_inv :
    dagger (rightDualUnitIso C).inv = (rightDualUnitIso C).hom := by
  rw [← dagger_rightDualUnitIso_hom, dagger_dagger]

/-- The inverse unit comparison `(rightDualUnitIso C).inv : 𝟙_ C ⟶ (𝟙_ C)ᘁ` is unitary. -/
@[simp]
theorem isUnitary_rightDualUnitIso_inv : IsUnitary (rightDualUnitIso C).inv := by
  rw [← dagger_rightDualUnitIso_hom]
  exact isUnitary_rightDualUnitIso.dagger

end UnitaryDual

section DualConjBasic

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [RightRigidCategory C]

/-- The covariant conjugate `dualConj f := (fᘁ)† : Xᘁ ⟶ Yᘁ` of a morphism `f : X ⟶ Y` in a right
rigid dagger category. Under `UnitaryDualFunctor C`, this equals `(f†)ᘁ`. -/
noncomputable def dualConj {X Y : C} (f : X ⟶ Y) : Xᘁ ⟶ Yᘁ :=
  dagger (fᘁ)

/-- The conjugate of `f` is the dagger of its right adjoint mate. -/
theorem dualConj_eq_dagger_rightAdjointMate {X Y : C} (f : X ⟶ Y) :
    dualConj f = dagger (fᘁ) :=
  (rfl)

/-- The conjugate of an identity arrow is the identity arrow on the dual. -/
@[simp]
theorem dualConj_id (X : C) : dualConj (𝟙 X) = 𝟙 Xᘁ := by
  rw [dualConj_eq_dagger_rightAdjointMate, rightAdjointMate_id, dagger_id]

/-- Conjugation is covariant: it preserves composition. -/
@[simp]
theorem dualConj_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dualConj (f ≫ g) = dualConj f ≫ dualConj g := by
  rw [dualConj_eq_dagger_rightAdjointMate, comp_rightAdjointMate, dagger_comp]
  rfl

/-- Taking the dagger of a conjugate recovers the right adjoint mate. -/
@[simp]
theorem dagger_dualConj {X Y : C} (f : X ⟶ Y) : dagger (dualConj f) = fᘁ := by
  rw [dualConj_eq_dagger_rightAdjointMate, dagger_dagger]

/-- Conjugation is injective on hom-sets. -/
theorem dualConj_injective {X Y : C} :
    Function.Injective (dualConj (C := C) (X := X) (Y := Y)) := by
  intro f g h
  exact rightAdjointMate_injective (dagger_inj.mp h)

/-- Conjugation detects equality of morphisms. -/
@[simp]
theorem dualConj_inj {X Y : C} {f g : X ⟶ Y} : dualConj f = dualConj g ↔ f = g :=
  dualConj_injective.eq_iff

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

/-- Conjugation preserves zero morphisms. -/
@[simp]
theorem dualConj_zero [DaggerPreadditive C] {X Y : C} : dualConj (0 : X ⟶ Y) = 0 := by
  rw [dualConj_eq_dagger_rightAdjointMate, rightAdjointMate_zero, dagger_zero]

/-- Conjugation is additive. -/
@[simp]
theorem dualConj_add [DaggerPreadditive C] {X Y : C} (f g : X ⟶ Y) :
    dualConj (f + g) = dualConj f + dualConj g := by
  rw [dualConj_eq_dagger_rightAdjointMate, rightAdjointMate_add, dagger_add]
  rfl

/-- Conjugation commutes with negation. -/
@[simp]
theorem dualConj_neg [DaggerPreadditive C] {X Y : C} (f : X ⟶ Y) :
    dualConj (-f) = -dualConj f :=
  eq_neg_of_add_eq_zero_left (by rw [← dualConj_add, neg_add_cancel, dualConj_zero])

/-- Conjugation commutes with subtraction. -/
@[simp]
theorem dualConj_sub [DaggerPreadditive C] {X Y : C} (f g : X ⟶ Y) :
    dualConj (f - g) = dualConj f - dualConj g := by
  rw [sub_eq_add_neg, dualConj_add, dualConj_neg, sub_eq_add_neg]

/-- Conjugation commutes with natural scalar multiplication. -/
@[simp]
theorem dualConj_nsmul [DaggerPreadditive C] {X Y : C} (n : ℕ) (f : X ⟶ Y) :
    dualConj (n • f) = n • dualConj f := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, ih]

/-- Conjugation commutes with integer scalar multiplication. -/
@[simp]
theorem dualConj_zsmul [DaggerPreadditive C] {X Y : C} (n : ℤ) (f : X ⟶ Y) :
    dualConj (n • f) = n • dualConj f := by
  cases n with
  | ofNat n => simp
  | negSucc n => simp [negSucc_zsmul]

/-- In a conjugate-linear dagger monoidal category, conjugation is conjugate-linear. -/
@[simp]
theorem dualConj_smul {R : Type w} [Semiring R] [Star R] [Linear R C] [MonoidalLinear R C]
    [DaggerLinear R C] {X Y : C} (r : R) (f : X ⟶ Y) :
    dualConj (r • f) = star r • dualConj f := by
  rw [dualConj_eq_dagger_rightAdjointMate]
  have h : (r • f)ᘁ = r • fᘁ := by simp [CategoryTheory.rightAdjointMate]
  rw [h, dagger_smul]
  rfl

end Preadditive

variable (C)

/-- The covariant conjugate functor `C ⥤ Cᴹᵒᵖ` sending `X` to `mop Xᘁ` and `f` to
`(dualConj f).mop`. -/
@[expose]
noncomputable def dualConjFunctor : C ⥤ Cᴹᵒᵖ where
  obj X := mop Xᘁ
  map f := (dualConj f).mop
  map_id X := Quiver.Hom.unmop_inj (dualConj_id X)
  map_comp f g := Quiver.Hom.unmop_inj (dualConj_comp f g)

/-- On objects, `dualConjFunctor C` sends `X` to `mop Xᘁ`. -/
@[simp]
theorem dualConjFunctor_obj (X : C) : (dualConjFunctor C).obj X = mop Xᘁ :=
  (rfl)

/-- On morphisms, `dualConjFunctor C` sends `f` to `(dualConj f).mop`. -/
@[simp]
theorem dualConjFunctor_map {X Y : C} (f : X ⟶ Y) :
    (dualConjFunctor C).map f = (dualConj f).mop :=
  (rfl)

end DualConjBasic

section DualConjUnitary

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [RightRigidCategory C] [UnitaryDualFunctor C]

/-- The conjugate of `f` is the right adjoint mate of its dagger. -/
theorem dualConj_eq_rightAdjointMate_dagger {X Y : C} (f : X ⟶ Y) :
    dualConj f = (dagger f)ᘁ :=
  dagger_rightAdjointMate f

/-- Conjugation commutes with the dagger. -/
@[simp]
theorem dualConj_dagger {X Y : C} (f : X ⟶ Y) : dualConj (dagger f) = dagger (dualConj f) := by
  rw [dualConj_eq_rightAdjointMate_dagger, dualConj_eq_dagger_rightAdjointMate, dagger_dagger,
    dagger_dagger]

/-- Applying conjugation twice recovers the double right adjoint mate `fᘁᘁ`. -/
@[simp]
theorem dualConj_dualConj {X Y : C} (f : X ⟶ Y) : dualConj (dualConj f) = fᘁᘁ := by
  rw [dualConj_eq_rightAdjointMate_dagger, dagger_dualConj]

/-- Conjugation preserves unitary arrows. -/
theorem IsUnitary.dualConj {X Y : C} {f : X ⟶ Y} (hf : IsUnitary f) :
    IsUnitary (TauCeti.dualConj f) :=
  hf.rightAdjointMate.dagger

/-- Conjugation preserves and reflects unitary arrows. -/
@[simp]
theorem isUnitary_dualConj_iff {X Y : C} (f : X ⟶ Y) : IsUnitary (dualConj f) ↔ IsUnitary f := by
  rw [dualConj_eq_dagger_rightAdjointMate, isUnitary_dagger_iff, isUnitary_rightAdjointMate_iff]

/-- The conjugate functor preserves daggers. -/
instance dualConjFunctorPreservesDagger (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [DaggerCategory C] [RightRigidCategory C] [UnitaryDualFunctor C] :
    (dualConjFunctor C).PreservesDagger where
  map_dagger f := Quiver.Hom.unmop_inj (dualConj_dagger f)

variable [DaggerMonoidalCategory C]

/-- Conjugation reverses tensor products up to `rightDualTensorIso`. -/
@[reassoc]
theorem dualConj_tensorHom_comp_rightDualTensorIso_hom {X₁ Y₁ X₂ Y₂ : C}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    dualConj (f ⊗ₘ g) ≫ (rightDualTensorIso Y₁ Y₂).hom =
      (rightDualTensorIso X₁ X₂).hom ≫ (dualConj g ⊗ₘ dualConj f) := by
  rw [dualConj_eq_rightAdjointMate_dagger, dagger_tensorHom,
    rightDualTensorIso_hom_naturality (dagger f) (dagger g),
    ← dualConj_eq_rightAdjointMate_dagger, ← dualConj_eq_rightAdjointMate_dagger]

/-- Conjugation reverses tensor products up to `(rightDualTensorIso _ _).inv`. -/
@[reassoc]
theorem rightDualTensorIso_inv_comp_dualConj_tensorHom {X₁ Y₁ X₂ Y₂ : C}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (rightDualTensorIso X₁ X₂).inv ≫ dualConj (f ⊗ₘ g) =
      (dualConj g ⊗ₘ dualConj f) ≫ (rightDualTensorIso Y₁ Y₂).inv := by
  rw [Iso.inv_comp_eq, ← dualConj_tensorHom_comp_rightDualTensorIso_hom_assoc,
    Iso.hom_inv_id, Category.comp_id]

variable (C)

/-- Strong monoidal structure on `dualConjFunctor C : C ⥤ Cᴹᵒᵖ`, with unit comparison
`(rightDualUnitIso C).symm` and tensor comparisons `(rightDualTensorIso X Y).symm`. -/
noncomputable def dualConjFunctorCoreMonoidal : (dualConjFunctor C).CoreMonoidal where
  εIso := (mopFunctor C).mapIso (rightDualUnitIso C).symm
  μIso X Y := (mopFunctor C).mapIso (rightDualTensorIso X Y).symm
  μIso_hom_natural_left f Y := by
    apply Quiver.Hom.unmop_inj
    have h : Yᘁ ◁ dualConj f ≫ (rightDualTensorIso _ Y).inv =
        (rightDualTensorIso _ Y).inv ≫ dualConj (f ▷ Y) := by
      simpa using (rightDualTensorIso_inv_comp_dualConj_tensorHom f (𝟙 Y)).symm
    exact h
  μIso_hom_natural_right X g := by
    apply Quiver.Hom.unmop_inj
    have h : dualConj g ▷ Xᘁ ≫ (rightDualTensorIso X _).inv =
        (rightDualTensorIso X _).inv ≫ dualConj (X ◁ g) := by
      simpa using (rightDualTensorIso_inv_comp_dualConj_tensorHom (𝟙 X) g).symm
    exact h
  associativity X Y Z := by
    apply Quiver.Hom.unmop_inj
    have h := congrArg dagger (rightDualTensorIso_associativity X Y Z)
    have h' : Zᘁ ◁ (rightDualTensorIso X Y).inv ≫ (rightDualTensorIso (X ⊗ Y) Z).inv ≫
        dualConj (α_ X Y Z).hom =
        (α_ Zᘁ Yᘁ Xᘁ).inv ≫ (rightDualTensorIso Y Z).inv ▷ Xᘁ ≫
          (rightDualTensorIso X (Y ⊗ Z)).inv := by
      simpa only [dagger_comp, dagger_whiskerLeft, dagger_whiskerRight, dagger_associator_hom,
        dagger_rightDualTensorIso_hom, ← dualConj_eq_dagger_rightAdjointMate,
        Category.assoc] using h
    exact h'
  left_unitality X := by
    apply Quiver.Hom.unmop_inj
    have h := congrArg dagger
      (@rightDualTensorIso_leftUnitality C _ _ X _ (RightRigidCategory.rightDual _) _)
    rw [← rightDualUnitIso_hom] at h
    have h' : (ρ_ Xᘁ).hom =
        Xᘁ ◁ (rightDualUnitIso C).inv ≫
          (@rightDualTensorIso C _ _ (𝟙_ C) X (RightRigidCategory.rightDual _) _ _).inv ≫
            dualConj (λ_ X).hom := by
      simpa only [dagger_comp, dagger_whiskerLeft, dagger_rightUnitor_inv,
        dagger_rightDualTensorIso_hom, dagger_rightDualUnitIso_hom,
        ← dualConj_eq_dagger_rightAdjointMate, Category.assoc] using h
    exact h'
  right_unitality X := by
    apply Quiver.Hom.unmop_inj
    have h := congrArg dagger
      (@rightDualTensorIso_rightUnitality C _ _ X _ (RightRigidCategory.rightDual _) _)
    rw [← rightDualUnitIso_hom] at h
    have h' : (λ_ Xᘁ).hom =
        (rightDualUnitIso C).inv ▷ Xᘁ ≫
          (@rightDualTensorIso C _ _ X (𝟙_ C) _ (RightRigidCategory.rightDual _) _).inv ≫
            dualConj (ρ_ X).hom := by
      simpa only [dagger_comp, dagger_whiskerRight, dagger_leftUnitor_inv,
        dagger_rightDualTensorIso_hom, dagger_rightDualUnitIso_hom,
        ← dualConj_eq_dagger_rightAdjointMate, Category.assoc] using h
    exact h'

/-- The conjugate functor `dualConjFunctor C : C ⥤ Cᴹᵒᵖ` is strong monoidal. -/
noncomputable instance dualConjFunctorMonoidal : (dualConjFunctor C).Monoidal :=
  (dualConjFunctorCoreMonoidal C).toMonoidal

/-- The conjugate functor `dualConjFunctor C : C ⥤ Cᴹᵒᵖ` is dagger monoidal. -/
instance dualConjFunctorIsDaggerMonoidal : (dualConjFunctor C).IsDaggerMonoidal where
  isUnitary_ε := (isUnitary_mop_iff _).mpr isUnitary_rightDualUnitIso_inv
  isUnitary_μ X Y := (isUnitary_mop_iff _).mpr (isUnitary_rightDualTensorIso_inv X Y)

end DualConjUnitary

section InducedPivotalBasic

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C] [RightRigidCategory C]

/-- The canonical isomorphism `φ_X : X ≅ Xᘁᘁ` induced by a dagger monoidal structure on a right
rigid category, comparing `daggerExactPairing X Xᘁ : ExactPairing Xᘁ X` with the chosen right dual
pairing of `Xᘁ`. -/
noncomputable def unitaryDualPivotalIsoApp (X : C) : X ≅ ((Xᘁ : C)ᘁ : C) :=
  rightDualIso (daggerExactPairing X Xᘁ) HasRightDual.exact

/-- Evaluating `unitaryDualPivotalIsoApp X` against `Xᘁ` gives the dagger of `η_ X Xᘁ`. -/
@[reassoc (attr := simp)]
theorem unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation (X : C) :
    (unitaryDualPivotalIsoApp X).hom ▷ Xᘁ ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) = dagger (η_ X Xᘁ) := by
  rw [unitaryDualPivotalIsoApp, rightDualIso_hom, rightMate_comp_evaluation,
    daggerExactPairing_evaluation, MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- Applying `(unitaryDualPivotalIsoApp X).inv` after `η_ Xᘁ Xᘁᘁ` gives the dagger of `ε_ X Xᘁ`. -/
@[reassoc (attr := simp)]
theorem coevaluation_comp_whiskerLeft_unitaryDualPivotalIsoApp_inv (X : C) :
    η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ (unitaryDualPivotalIsoApp X).inv = dagger (ε_ X Xᘁ) := by
  have h := coevaluation_comp_rightMate (daggerExactPairing X Xᘁ) HasRightDual.exact (𝟙 Xᘁ)
  rw [daggerExactPairing_coevaluation, id_whiskerRight, Category.comp_id] at h
  rw [unitaryDualPivotalIsoApp, rightDualIso_inv]
  exact h

/-- Applying `(unitaryDualPivotalIsoApp X).hom` after `dagger (ε_ X Xᘁ)` recovers `η_ Xᘁ Xᘁᘁ`. -/
@[reassoc (attr := simp)]
theorem dagger_evaluation_comp_whiskerLeft_unitaryDualPivotalIsoApp_hom (X : C) :
    dagger (ε_ X Xᘁ) ≫ Xᘁ ◁ (unitaryDualPivotalIsoApp X).hom = η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) := by
  rw [← coevaluation_comp_whiskerLeft_unitaryDualPivotalIsoApp_inv, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
    Category.comp_id]

end InducedPivotalBasic

section InducedPivotal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C] [RightRigidCategory C] [UnitaryDualFunctor C]

/-- Naturality of `unitaryDualPivotalIsoApp` with respect to double right adjoint mates. -/
@[reassoc]
theorem unitaryDualPivotalIsoApp_hom_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (unitaryDualPivotalIsoApp Y).hom = (unitaryDualPivotalIsoApp X).hom ≫ fᘁᘁ := by
  apply rightHom_ext (X := Yᘁ)
  rw [comp_whiskerRight, Category.assoc, unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation,
    comp_whiskerRight, Category.assoc, rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
    unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation]
  apply dagger_inj.mp
  simpa only [dagger_comp, dagger_whiskerRight, dagger_whiskerLeft, dagger_dagger,
    dagger_rightAdjointMate] using (coevaluation_comp_rightAdjointMate (dagger f)).symm

/-- Naturality of the inverse of `unitaryDualPivotalIsoApp`. -/
@[reassoc]
theorem unitaryDualPivotalIsoApp_inv_naturality {X Y : C} (f : X ⟶ Y) :
    fᘁᘁ ≫ (unitaryDualPivotalIsoApp Y).inv = (unitaryDualPivotalIsoApp X).inv ≫ f := by
  rw [← cancel_epi (unitaryDualPivotalIsoApp X).hom,
    ← unitaryDualPivotalIsoApp_hom_naturality_assoc]
  simp

variable (C)

/-- The canonical natural isomorphism `𝟭 C ≅ doubleRightDualFunctor C` induced by a unitary dual
functor. -/
noncomputable def unitaryDualPivotalNatIso : 𝟭 C ≅ doubleRightDualFunctor C :=
  NatIso.ofComponents unitaryDualPivotalIsoApp fun f => unitaryDualPivotalIsoApp_hom_naturality f

variable {C}

/-- The components of `unitaryDualPivotalNatIso C` are `unitaryDualPivotalIsoApp X`. -/
@[simp]
theorem unitaryDualPivotalNatIso_hom_app (X : C) :
    (unitaryDualPivotalNatIso C).hom.app X = (unitaryDualPivotalIsoApp X).hom :=
  (rfl)

/-- The components of the inverse of `unitaryDualPivotalNatIso C` are
`(unitaryDualPivotalIsoApp X).inv`. -/
@[simp]
theorem unitaryDualPivotalNatIso_inv_app (X : C) :
    (unitaryDualPivotalNatIso C).inv.app X = (unitaryDualPivotalIsoApp X).inv :=
  (rfl)

/-- The natural isomorphism `unitaryDualPivotalNatIso C` is monoidal. -/
instance unitaryDualPivotalNatIso_isMonoidal :
    NatTrans.IsMonoidal (unitaryDualPivotalNatIso C).hom := by
  refine NatTrans.IsMonoidal.of_tensor (unitaryDualPivotalNatIso C).hom fun X Y => ?_
  have hmain : (unitaryDualPivotalIsoApp (X ⊗ Y)).hom =
      ((unitaryDualPivotalIsoApp X).hom ⊗ₘ (unitaryDualPivotalIsoApp Y).hom) ≫
        (rightDualTensorIso Yᘁ Xᘁ).inv ≫ (rightDualTensorIso X Y).homᘁ := by
    refine rightHom_ext (X := (X ⊗ Y)ᘁ) ?_
    rw [unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation, comp_whiskerRight, comp_whiskerRight,
      Category.assoc, Category.assoc, rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
      ← whisker_exchange_assoc, rightDualTensorIso_inv_whiskerRight_evaluation, tensor_evaluation]
    -- Evaluate `φ_X ▷ Xᘁ` and `φ_Y ▷ Yᘁ` inside the tensor product pairing of `Yᘁ` and `Xᘁ`.
    have key : ((unitaryDualPivotalIsoApp X).hom ⊗ₘ (unitaryDualPivotalIsoApp Y).hom) ▷
          (Yᘁ ⊗ Xᘁ) ≫
        𝟙 _ ⊗≫ ((Xᘁ : C)ᘁ : C) ◁ ε_ (Yᘁ : C) ((Yᘁ : C)ᘁ : C) ▷ (Xᘁ : C) ⊗≫
          ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) =
        dagger (η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)) := by
      have hη : dagger (η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)) =
          𝟙 _ ⊗≫ X ◁ dagger (η_ Y Yᘁ) ▷ Xᘁ ⊗≫ dagger (η_ X Xᘁ) := by
        have hη0 : η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) =
            η_ X Xᘁ ≫ (ρ_ X).inv ▷ Xᘁ ≫ (X ◁ η_ Y Yᘁ) ▷ Xᘁ ≫
              (α_ X Y Yᘁ).inv ▷ Xᘁ ≫ (α_ (X ⊗ Y) Yᘁ Xᘁ).hom := by
          rw [ExactPairing.tensor_coevaluation]; monoidal
        have hd := congrArg dagger hη0
        simp only [dagger_comp, dagger_whiskerLeft, dagger_whiskerRight, dagger_associator_hom,
          dagger_associator_inv, dagger_rightUnitor_inv, Category.assoc] at hd
        rw [hd]; monoidal
      rw [hη]
      calc
        _ = 𝟙 _ ⊗≫ ((unitaryDualPivotalIsoApp X).hom ▷ ((Y ⊗ Yᘁ) ⊗ Xᘁ) ≫
              ((Xᘁ : C)ᘁ : C) ◁ (((unitaryDualPivotalIsoApp Y).hom ▷ Yᘁ ≫
                ε_ (Yᘁ : C) ((Yᘁ : C)ᘁ : C)) ▷ Xᘁ)) ⊗≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) := by
          rw [tensorHom_def]; monoidal
        _ = 𝟙 _ ⊗≫ (X ◁ (((unitaryDualPivotalIsoApp Y).hom ▷ Yᘁ ≫
                ε_ (Yᘁ : C) ((Yᘁ : C)ᘁ : C)) ▷ Xᘁ) ≫
              (unitaryDualPivotalIsoApp X).hom ▷ (𝟙_ C ⊗ Xᘁ)) ⊗≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) := by
          rw [whisker_exchange]
        _ = _ := by
          rw [unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation,
            ← unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation X]
          monoidal
    rw [key]
    apply dagger_inj.mp
    simpa only [dagger_comp, dagger_whiskerLeft, dagger_dagger, dagger_rightDualTensorIso_hom] using
      (by
        rw [← coevaluation_comp_whiskerLeft_rightDualTensorIso_hom, Category.assoc,
          ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id,
          Category.comp_id] :
        η_ (X ⊗ Y) (X ⊗ Y)ᘁ = η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) ≫ (X ⊗ Y) ◁ (rightDualTensorIso X Y).inv)
  rw [Functor.LaxMonoidal.id_μ, Category.id_comp, unitaryDualPivotalNatIso_hom_app,
    unitaryDualPivotalNatIso_hom_app, unitaryDualPivotalNatIso_hom_app, doubleRightDualFunctor_μ]
  exact hmain

variable (C)

/-- The rigid structure induced by a unitary dual functor: left duals are the chosen right duals,
paired with `X` via the dagger-adjoint evaluations and coevaluations. Not a global instance, to
avoid diamonds with preexisting rigid structures. -/
@[expose, instance_reducible]
noncomputable def unitaryDualRigidCategory : RigidCategory C :=
  rigidCategoryOfIsoDoubleRightDual (unitaryDualPivotalNatIso C).app

/-- The pivotal structure induced by a unitary dual functor on `unitaryDualRigidCategory C`. Not a
global instance, to avoid diamonds with preexisting pivotal structures such as
`TauCeti.symmetricPivotalCategory`. -/
@[expose, instance_reducible]
noncomputable def unitaryDualPivotalCategory :
    @PivotalCategory C _ _ (unitaryDualRigidCategory C) :=
  pivotalCategoryOfRightRigid (unitaryDualPivotalNatIso C)

variable {C}

/-- In `unitaryDualRigidCategory C`, the left-dual evaluation of `X` is `dagger (η_ X Xᘁ)`. -/
@[reassoc]
theorem unitaryDualRigidCategory_evaluation (X : C) :
    let _ := unitaryDualRigidCategory C
    ε_ (ᘁX) X = dagger (η_ X Xᘁ) :=
  (rigidCategoryOfIsoDoubleRightDual_evaluation (unitaryDualPivotalNatIso C).app X).trans
    (unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation X)

/-- In `unitaryDualRigidCategory C`, the left-dual coevaluation of `X` is `dagger (ε_ X Xᘁ)`. -/
@[reassoc]
theorem unitaryDualRigidCategory_coevaluation (X : C) :
    let _ := unitaryDualRigidCategory C
    η_ (ᘁX) X = dagger (ε_ X Xᘁ) :=
  (rigidCategoryOfIsoDoubleRightDual_coevaluation (unitaryDualPivotalNatIso C).app X).trans
    (coevaluation_comp_whiskerLeft_unitaryDualPivotalIsoApp_inv X)

/-- The components of `unitaryDualPivotalCategory C` are `unitaryDualPivotalIsoApp X`. -/
theorem pivotalIsoApp_unitaryDualPivotalCategory (X : C) :
    @pivotalIsoApp C _ _ (unitaryDualRigidCategory C) (unitaryDualPivotalCategory C) X =
      unitaryDualPivotalIsoApp X :=
  pivotalIsoApp_pivotalCategoryOfRightRigid (unitaryDualPivotalNatIso C) X

/-- For `unitaryDualPivotalCategory C`, the comparison `leftDualIsoRightDual X` is the identity. -/
theorem leftDualIsoRightDual_unitaryDualPivotalCategory (X : C) :
    @leftDualIsoRightDual C _ _ (unitaryDualRigidCategory C) (unitaryDualPivotalCategory C) X =
      Iso.refl _ :=
  leftDualIsoRightDual_pivotalCategoryOfRightRigid (unitaryDualPivotalNatIso C) X

/-- **Unitarity of the induced pivotal isomorphism**: every component
`unitaryDualPivotalIsoApp X : X ≅ Xᘁᘁ` is unitary. -/
@[simp]
theorem isUnitary_unitaryDualPivotalIsoApp (X : C) :
    IsUnitary (unitaryDualPivotalIsoApp X).hom := by
  let := unitaryDualRigidCategory C
  let := unitaryDualPivotalCategory C
  -- Freyd–Yetter gives `φ_{Xᘁ}⁻¹ = (φ_X)ᘁ`.
  have hfy : (unitaryDualPivotalIsoApp Xᘁ).inv = ((unitaryDualPivotalIsoApp X).hom)ᘁ := by
    have h := pivotalIsoApp_rightDual_inv X
    rw [pivotalIsoApp_unitaryDualPivotalCategory, pivotalIsoApp_unitaryDualPivotalCategory] at h
    exact h
  -- Compute `dagger (ε_ Xᘁ Xᘁᘁ)` via `coevaluation_comp_rightAdjointMate`.
  have hε : dagger (ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C)) =
      η_ X Xᘁ ≫ (unitaryDualPivotalIsoApp X).hom ▷ Xᘁ := by
    rw [← coevaluation_comp_whiskerLeft_unitaryDualPivotalIsoApp_inv Xᘁ, hfy,
      coevaluation_comp_rightAdjointMate]
  -- Taking the dagger of `(φ_X ▷ Xᘁ) ≫ ε_{Xᘁ} = η_X†` and substituting `hε` yields
  -- `η_ X Xᘁ ≫ (φ_X ≫ φ_X†) ▷ Xᘁ = η_ X Xᘁ`.
  have hd := congrArg dagger (unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation X)
  simp only [dagger_comp, dagger_whiskerRight, dagger_dagger, hε, Category.assoc,
    ← comp_whiskerRight] at hd
  have hhd : (unitaryDualPivotalIsoApp X).hom ≫ dagger (unitaryDualPivotalIsoApp X).hom = 𝟙 X :=
    ExactPairing.leftHom_ext (by simpa using hd)
  exact (unitaryDualPivotalIsoApp X).isUnitary_hom_iff.mpr
    ((cancel_epi (unitaryDualPivotalIsoApp X).hom).mp
      (hhd.trans (unitaryDualPivotalIsoApp X).hom_inv_id.symm))

/-- The dagger of `(unitaryDualPivotalIsoApp X).hom` is `(unitaryDualPivotalIsoApp X).inv`. -/
@[simp]
theorem dagger_unitaryDualPivotalIsoApp_hom (X : C) :
    dagger (unitaryDualPivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).inv :=
  (unitaryDualPivotalIsoApp X).dagger_hom_eq_inv_of_isUnitary (isUnitary_unitaryDualPivotalIsoApp X)

/-- The dagger of `(unitaryDualPivotalIsoApp X).inv` is `(unitaryDualPivotalIsoApp X).hom`. -/
@[simp]
theorem dagger_unitaryDualPivotalIsoApp_inv (X : C) :
    dagger (unitaryDualPivotalIsoApp X).inv = (unitaryDualPivotalIsoApp X).hom := by
  rw [← dagger_unitaryDualPivotalIsoApp_hom, dagger_dagger]

/-- The inverse of `unitaryDualPivotalIsoApp X` is unitary. -/
@[simp]
theorem isUnitary_unitaryDualPivotalIsoApp_inv (X : C) :
    IsUnitary (unitaryDualPivotalIsoApp X).inv := by
  rw [← dagger_unitaryDualPivotalIsoApp_hom]
  exact (isUnitary_unitaryDualPivotalIsoApp X).dagger

/-- **Bi-involution coherence**: conjugating `φ_X` gives `φ_{Xᘁ}`. -/
@[simp]
theorem dualConj_unitaryDualPivotalIsoApp_hom (X : C) :
    dualConj (unitaryDualPivotalIsoApp X).hom = (unitaryDualPivotalIsoApp Xᘁ).hom := by
  let := unitaryDualRigidCategory C
  let := unitaryDualPivotalCategory C
  have hfy : ((unitaryDualPivotalIsoApp X).hom)ᘁ = (unitaryDualPivotalIsoApp Xᘁ).inv := by
    have h := (pivotalIsoApp_rightDual_inv X).symm
    rw [pivotalIsoApp_unitaryDualPivotalCategory, pivotalIsoApp_unitaryDualPivotalCategory] at h
    exact h
  rw [dualConj_eq_dagger_rightAdjointMate, hfy, dagger_unitaryDualPivotalIsoApp_inv]

/-- Applying `unitaryDualPivotalIsoApp` conjugates `dualConj (dualConj f)` back to `f`. -/
@[reassoc]
theorem dualConj_dualConj_eq (X Y : C) (f : X ⟶ Y) :
    dualConj (dualConj f) =
      (unitaryDualPivotalIsoApp X).inv ≫ f ≫ (unitaryDualPivotalIsoApp Y).hom := by
  rw [dualConj_dualConj, unitaryDualPivotalIsoApp_hom_naturality, Iso.inv_hom_id_assoc]

end InducedPivotal

section Trace

/-! The trace and dimension formulas below are stated for any ambient pivotal structure whose
component at `X` agrees with `unitaryDualPivotalIsoApp X`. In particular they apply directly to
`unitaryDualPivotalCategory C`, as well as to `symmetricPivotalCategory` whenever the induced twist
is trivial. -/

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C] [RigidCategory C] [PivotalCategory C]

/-- For a pivotal structure matching `unitaryDualPivotalIsoApp X`, the left trace is given by
`dagger (ε_ X Xᘁ) ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ`. -/
theorem leftTrace_eq_dagger_evaluation {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) (f : X ⟶ X) :
    leftTrace f = dagger (ε_ X Xᘁ) ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ := by
  have hinv : (pivotalIsoApp X).inv = (unitaryDualPivotalIsoApp X).inv :=
    congrArg Iso.inv (Iso.ext hφ)
  rw [leftTrace_eq_pivotalIsoApp, hinv, ← Category.assoc,
    coevaluation_comp_whiskerLeft_unitaryDualPivotalIsoApp_inv]

/-- For a pivotal structure matching `unitaryDualPivotalIsoApp X`, the right trace is given by
`η_ X Xᘁ ≫ f ▷ Xᘁ ≫ dagger (η_ X Xᘁ)`. -/
theorem rightTrace_eq_dagger_coevaluation {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) (f : X ⟶ X) :
    rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ dagger (η_ X Xᘁ) := by
  rw [rightTrace_eq_pivotalIsoApp, hφ, unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation]

/-- The left trace commutes with the dagger. -/
theorem dagger_leftTrace {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) (f : X ⟶ X) :
    dagger (leftTrace f) = leftTrace (dagger f) := by
  rw [leftTrace_eq_dagger_evaluation hφ, leftTrace_eq_dagger_evaluation hφ]
  simp [Category.assoc]

/-- The right trace commutes with the dagger. -/
theorem dagger_rightTrace {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) (f : X ⟶ X) :
    dagger (rightTrace f) = rightTrace (dagger f) := by
  rw [rightTrace_eq_dagger_coevaluation hφ, rightTrace_eq_dagger_coevaluation hφ]
  simp [Category.assoc]

/-- Algebraic positivity of the left trace: `leftTrace (g ≫ dagger g)` has the form `dagger h ≫ h`
for `h = Xᘁ ◁ dagger g ≫ ε_ X Xᘁ : Xᘁ ⊗ Y ⟶ 𝟙_ C`. -/
theorem leftTrace_comp_dagger {X Y : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) (g : X ⟶ Y) :
    leftTrace (g ≫ dagger g) =
      dagger (Xᘁ ◁ dagger g ≫ ε_ X Xᘁ) ≫ (Xᘁ ◁ dagger g ≫ ε_ X Xᘁ) := by
  rw [leftTrace_eq_dagger_evaluation hφ]
  simp [MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- Algebraic positivity of the left trace: `leftTrace (dagger g ≫ g)` has the form `dagger h ≫ h`
for `h = Yᘁ ◁ g ≫ ε_ Y Yᘁ : Yᘁ ⊗ X ⟶ 𝟙_ C`. -/
theorem leftTrace_dagger_comp {X Y : C}
    (hφ : (pivotalIsoApp Y).hom = (unitaryDualPivotalIsoApp Y).hom) (g : X ⟶ Y) :
    leftTrace (dagger g ≫ g) =
      dagger (Yᘁ ◁ g ≫ ε_ Y Yᘁ) ≫ (Yᘁ ◁ g ≫ ε_ Y Yᘁ) := by
  simpa using leftTrace_comp_dagger hφ (dagger g)

/-- Algebraic positivity of the right trace: `rightTrace (g ≫ dagger g)` has the form
`h ≫ dagger h` for `h = η_ X Xᘁ ≫ g ▷ Xᘁ : 𝟙_ C ⟶ Y ⊗ Xᘁ`. -/
theorem rightTrace_comp_dagger {X Y : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) (g : X ⟶ Y) :
    rightTrace (g ≫ dagger g) =
      (η_ X Xᘁ ≫ g ▷ Xᘁ) ≫ dagger (η_ X Xᘁ ≫ g ▷ Xᘁ) := by
  rw [rightTrace_eq_dagger_coevaluation hφ]
  simp [comp_whiskerRight, Category.assoc]

/-- Algebraic positivity of the right trace in `dagger g ≫ g` form. -/
theorem rightTrace_dagger_comp {X Y : C}
    (hφ : (pivotalIsoApp Y).hom = (unitaryDualPivotalIsoApp Y).hom) (g : X ⟶ Y) :
    rightTrace (dagger g ≫ g) =
      (η_ Y Yᘁ ≫ dagger g ▷ Yᘁ) ≫ dagger (η_ Y Yᘁ ≫ dagger g ▷ Yᘁ) := by
  simpa using rightTrace_comp_dagger hφ (dagger g)

/-- The left dimension of `X` is `dagger (ε_ X Xᘁ) ≫ ε_ X Xᘁ`. -/
theorem leftDim_eq_dagger_evaluation {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) :
    leftDim X = dagger (ε_ X Xᘁ) ≫ ε_ X Xᘁ := by
  simpa using leftTrace_eq_dagger_evaluation hφ (𝟙 X)

/-- The right dimension of `X` is `η_ X Xᘁ ≫ dagger (η_ X Xᘁ)`. -/
theorem rightDim_eq_dagger_coevaluation {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) :
    rightDim X = η_ X Xᘁ ≫ dagger (η_ X Xᘁ) := by
  simpa using rightTrace_eq_dagger_coevaluation hφ (𝟙 X)

/-- The left dimension is self-adjoint. -/
theorem dagger_leftDim {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) :
    dagger (leftDim X) = leftDim X := by
  rw [leftDim_eq_dagger_evaluation hφ, dagger_comp, dagger_dagger]

/-- The right dimension is self-adjoint. -/
theorem dagger_rightDim {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) :
    dagger (rightDim X) = rightDim X := by
  rw [rightDim_eq_dagger_coevaluation hφ, dagger_comp, dagger_dagger]

/-- Conjugation exchanges the left and right traces up to taking the dagger. -/
theorem leftTrace_dualConj [UnitaryDualFunctor C] {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) (f : X ⟶ X) :
    leftTrace (dualConj f) = dagger (rightTrace f) := by
  rw [dualConj_eq_rightAdjointMate_dagger, leftTrace_rightAdjointMate, dagger_rightTrace hφ]

/-- Conjugation exchanges the right and left traces up to taking the dagger. -/
theorem rightTrace_dualConj [UnitaryDualFunctor C] {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) (f : X ⟶ X) :
    rightTrace (dualConj f) = dagger (leftTrace f) := by
  rw [dualConj_eq_rightAdjointMate_dagger, rightTrace_rightAdjointMate, dagger_leftTrace hφ]

/-- If the dagger is faithful (`dagger u ≫ u = 0 → u = 0`), then every nonzero object has nonzero
left dimension. -/
theorem leftDim_ne_zero_of_dagger_faithful [Limits.HasZeroMorphisms C]
    (hfaith : ∀ {A B : C} (u : A ⟶ B), dagger u ≫ u = 0 → u = 0)
    {X : C} (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom)
    (hX : ¬ Limits.IsZero X) : leftDim X ≠ 0 := by
  intro h0
  rw [leftDim_eq_dagger_evaluation hφ] at h0
  have hε : ε_ X Xᘁ = 0 := hfaith (ε_ X Xᘁ) h0
  apply hX
  rw [Limits.IsZero.iff_id_eq_zero]
  have hz := ExactPairing.evaluation_coevaluation X Xᘁ
  rw [hε, whiskerLeft_zero_of_hasLeftDual, Limits.comp_zero, Limits.comp_zero] at hz
  have h1 : (λ_ X).hom ≫ (ρ_ X).inv = 0 := hz.symm
  have h2 : (λ_ X).hom = 0 := by
    rw [← cancel_mono (ρ_ X).inv, h1, Limits.zero_comp]
  rw [← (λ_ X).inv_hom_id, h2, Limits.comp_zero]

/-- If the dagger is faithful (`u ≫ dagger u = 0 → u = 0`), then every nonzero object has nonzero
right dimension. -/
theorem rightDim_ne_zero_of_dagger_faithful [Limits.HasZeroMorphisms C]
    (hfaith : ∀ {A B : C} (u : A ⟶ B), u ≫ dagger u = 0 → u = 0)
    {X : C} (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom)
    (hX : ¬ Limits.IsZero X) : rightDim X ≠ 0 := by
  intro h0
  rw [rightDim_eq_dagger_coevaluation hφ] at h0
  exact coevaluation_ne_zero hX (hfaith (η_ X Xᘁ) h0)

end Trace

section InducedTrace

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C] [RightRigidCategory C] [UnitaryDualFunctor C]

/-- For `unitaryDualPivotalCategory C`, the left trace is `dagger (ε_ X Xᘁ) ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ`. -/
theorem unitaryDual_leftTrace_eq {X : C} (f : X ⟶ X) :
    let _ := unitaryDualRigidCategory C
    let _ := unitaryDualPivotalCategory C
    leftTrace f = dagger (ε_ X Xᘁ) ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ := by
  let := unitaryDualRigidCategory C
  let := unitaryDualPivotalCategory C
  exact leftTrace_eq_dagger_evaluation
    (congrArg Iso.hom (pivotalIsoApp_unitaryDualPivotalCategory X)) f

/-- For `unitaryDualPivotalCategory C`, the right trace is `η_ X Xᘁ ≫ f ▷ Xᘁ ≫ dagger (η_ X Xᘁ)`. -/
theorem unitaryDual_rightTrace_eq {X : C} (f : X ⟶ X) :
    let _ := unitaryDualRigidCategory C
    let _ := unitaryDualPivotalCategory C
    rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ dagger (η_ X Xᘁ) := by
  let := unitaryDualRigidCategory C
  let := unitaryDualPivotalCategory C
  exact rightTrace_eq_dagger_coevaluation
    (congrArg Iso.hom (pivotalIsoApp_unitaryDualPivotalCategory X)) f

end InducedTrace

section BraidedCompatibility

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C] [BraidedCategory C]

/-- In a braided dagger monoidal category with right duals, `unitaryDualPivotalIsoApp X` agrees
with `drinfeldIso X` if and only if `dagger (η_ X Xᘁ) = (β_ X Xᘁ).hom ≫ ε_ X Xᘁ`. -/
theorem unitaryDualPivotalIsoApp_eq_drinfeldIso_iff_dagger_coevaluation [RightRigidCategory C]
    (X : C) :
    (unitaryDualPivotalIsoApp X).hom = (drinfeldIso X).hom ↔
      dagger (η_ X Xᘁ) = (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  constructor
  · intro h
    rw [← unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation, h, drinfeldIso_hom_comp_evaluation]
  · intro h
    refine rightHom_ext (X := Xᘁ) ?_
    rw [unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation, drinfeldIso_hom_comp_evaluation, h]

/-- In a dagger braided category with right duals, `unitaryDualPivotalIsoApp X` agrees with
`drinfeldIso X` if and only if `dagger (ε_ X Xᘁ) = η_ X Xᘁ ≫ (β_ X Xᘁ).hom`. -/
theorem unitaryDualPivotalIsoApp_eq_drinfeldIso_iff_dagger_evaluation [RightRigidCategory C]
    [DaggerBraidedCategory C] (X : C) :
    (unitaryDualPivotalIsoApp X).hom = (drinfeldIso X).hom ↔
      dagger (ε_ X Xᘁ) = η_ X Xᘁ ≫ (β_ X Xᘁ).hom := by
  rw [unitaryDualPivotalIsoApp_eq_drinfeldIso_iff_dagger_coevaluation]
  constructor
  · intro h
    have hd := congrArg dagger h
    simp only [dagger_comp, dagger_dagger, dagger_braiding_hom] at hd
    rw [← cancel_mono (β_ X Xᘁ).inv, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact hd.symm
  · intro h
    have hd := congrArg dagger h
    simp only [dagger_comp, dagger_dagger, dagger_braiding_hom] at hd
    rw [← cancel_epi (β_ X Xᘁ).inv, Iso.inv_hom_id_assoc]
    exact hd.symm

/-- For any pivotal structure matching `unitaryDualPivotalIsoApp X`, the twist of
`balancedOfBraidedPivotal C` at `X` is the identity if and only if `unitaryDualPivotalIsoApp X`
agrees with `drinfeldIso X`. -/
theorem balancedOfBraidedPivotal_twist_eq_id_iff [RigidCategory C] [PivotalCategory C] {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom) :
    (balancedOfBraidedPivotal C).twist.hom.app X = 𝟙 X ↔
      (unitaryDualPivotalIsoApp X).hom = (drinfeldIso X).hom := by
  rw [balancedOfBraidedPivotal_twist_hom_app, hφ, Iso.comp_inv_eq, Category.id_comp]

/-- In a dagger braided category, when `unitaryDualPivotalIsoApp X` agrees with `drinfeldIso X`,
the left and right traces of every endomorphism of `X` agree. -/
theorem leftTrace_eq_rightTrace_of_eq_drinfeldIso [DaggerBraidedCategory C] [RigidCategory C]
    [PivotalCategory C] {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom)
    (hd : (unitaryDualPivotalIsoApp X).hom = (drinfeldIso X).hom) (f : X ⟶ X) :
    leftTrace f = rightTrace f := by
  rw [leftTrace_eq_dagger_evaluation hφ, rightTrace_eq_dagger_coevaluation hφ,
    (unitaryDualPivotalIsoApp_eq_drinfeldIso_iff_dagger_evaluation X).mp hd,
    (unitaryDualPivotalIsoApp_eq_drinfeldIso_iff_dagger_coevaluation X).mp hd,
    Category.assoc, braiding_naturality_left_assoc]

end BraidedCompatibility

end TauCeti
