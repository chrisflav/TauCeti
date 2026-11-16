/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.CategoryTheory.Dagger.Functor
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate

/-!
# Dagger monoidal categories and dagger monoidal functors

A *dagger monoidal category* is a monoidal category equipped with a dagger compatible with the
tensor product (`dagger (X ◁ f) = X ◁ dagger f` and `dagger (f ▷ Z) = dagger f ▷ Z`) such that the
associators and left and right unitors are unitary. A *dagger braided category* further requires the
braiding isomorphisms to be unitary.

In any dagger monoidal category, taking the dagger of the evaluation and coevaluation of an
`ExactPairing X Y` yields an `ExactPairing Y X` (`TauCeti.daggerExactPairing`). Thus right duals
automatically carry dagger-adjoint left-dual pairings.

A strong monoidal dagger-preserving functor `F : C ⥤ D` is *dagger monoidal*
(`CategoryTheory.Functor.IsDaggerMonoidal`) when its unit and tensor comparisons `ε F` and
`μ F X Y` are unitary. The pointwise dagger of a monoidal natural transformation between dagger
monoidal functors is again monoidal, so the full subcategory `TauCeti.DaggerMonoidalFunctor C D` of
`LaxMonoidalFunctor C D` inherits a `TauCeti.DaggerCategory` structure whose unitary isomorphisms
are the pointwise unitary monoidal natural isomorphisms.

## Main declarations

* `TauCeti.DaggerMonoidalCategory`: dagger compatibility with the monoidal structure and unitarity
  of associators and unitors, with `TauCeti.dagger_tensorHom` and unitarity closure lemmas;
* `TauCeti.daggerExactPairing`: the opposite-handed exact pairing obtained by taking daggers of
  evaluation and coevaluation, with `CategoryTheory.ExactPairing.rightMate_daggerExactPairing`;
* `TauCeti.DaggerBraidedCategory`: unitarity of the braiding isomorphisms;
* `CategoryTheory.Functor.IsDaggerMonoidal`: unitary unit and tensor comparisons on a strong
  monoidal dagger-preserving functor, closed under identity and composition;
* `CategoryTheory.NatTrans.isMonoidal_dagger`: the pointwise dagger of a monoidal natural
  transformation between dagger monoidal functors is monoidal;
* `TauCeti.DaggerMonoidalFunctor`: the bundled dagger category of dagger monoidal functors, with
  its fully faithful forgetful functor to `LaxMonoidalFunctor` and unitary isomorphism constructors.

## References

* P. Selinger, *Dagger compact closed categories and completely positive maps*,
  Electron. Notes Theor. Comput. Sci. **170** (2007), 139–163
* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1
* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  [arXiv:1808.00323](https://arxiv.org/abs/1808.00323), §2.1
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory MonoidalOpposite ExactPairing
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

universe v₁ v₂ v₃ v u₁ u₂ u₃ u

namespace TauCeti

section MonoidalOpposite

variable {C : Type u} [Category.{v} C] [DaggerCategory C]

/-- The monoidal opposite of a dagger category inherits the same dagger on morphisms. -/
instance instDaggerCategoryMonoidalOpposite : DaggerCategory Cᴹᵒᵖ where
  dagger f := (dagger f.unmop).mop
  dagger_id X := Quiver.Hom.unmop_inj (dagger_id (unmop X))
  dagger_comp f g := Quiver.Hom.unmop_inj (dagger_comp f.unmop g.unmop)
  dagger_dagger f := Quiver.Hom.unmop_inj (dagger_dagger f.unmop)

/-- Taking the dagger in `Cᴹᵒᵖ` acts on the underlying morphism in `C`. -/
@[simp]
theorem dagger_mop {X Y : C} (f : X ⟶ Y) : dagger f.mop = (dagger f).mop :=
  (rfl)

/-- Removing the monoidal opposite wrapper commutes with the dagger. -/
@[simp]
theorem unmop_dagger {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) : (dagger f).unmop = dagger f.unmop :=
  (rfl)

/-- A morphism in `Cᴹᵒᵖ` is unitary if and only if its underlying morphism in `C` is unitary. -/
@[simp]
theorem isUnitary_mop_iff {X Y : C} (f : X ⟶ Y) : IsUnitary f.mop ↔ IsUnitary f := by
  simp only [isUnitary_iff, dagger_mop, ← mop_comp, ← mop_id, Quiver.Hom.mop_inj.eq_iff]

/-- A morphism in `Cᴹᵒᵖ` is unitary if and only if its unwrapped morphism is unitary. -/
@[simp]
theorem isUnitary_unmop_iff {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) :
    IsUnitary f.unmop ↔ IsUnitary f := by
  simpa using (isUnitary_mop_iff f.unmop).symm

end MonoidalOpposite

/-- Compatibility of a dagger structure with a monoidal structure: the dagger commutes with
whiskering and all monoidal coherence isomorphisms (associators and unitors) are unitary. -/
class DaggerMonoidalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [DaggerCategory C] : Prop where
  /-- Left whiskering commutes with the dagger. -/
  dagger_whiskerLeft : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), dagger (X ◁ f) = X ◁ dagger f
  /-- Right whiskering commutes with the dagger. -/
  dagger_whiskerRight : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), dagger (f ▷ Z) = dagger f ▷ Z
  /-- The associators are unitary. -/
  isUnitary_associator : ∀ (X Y Z : C), IsUnitary (α_ X Y Z).hom
  /-- The left unitors are unitary. -/
  isUnitary_leftUnitor : ∀ (X : C), IsUnitary (λ_ X).hom
  /-- The right unitors are unitary. -/
  isUnitary_rightUnitor : ∀ (X : C), IsUnitary (ρ_ X).hom

export DaggerMonoidalCategory (dagger_whiskerLeft dagger_whiskerRight isUnitary_associator
  isUnitary_leftUnitor isUnitary_rightUnitor)

attribute [simp] dagger_whiskerLeft dagger_whiskerRight isUnitary_associator
  isUnitary_leftUnitor isUnitary_rightUnitor

section DaggerMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C]

/-- Taking the dagger commutes with the tensor product of morphisms. -/
@[simp]
theorem dagger_tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    dagger (f ⊗ₘ g) = dagger f ⊗ₘ dagger g := by
  rw [tensorHom_def, dagger_comp, dagger_whiskerLeft, dagger_whiskerRight, ← tensorHom_def']

/-- The dagger of the forward associator is the inverse associator. -/
@[simp]
theorem dagger_associator_hom (X Y Z : C) : dagger (α_ X Y Z).hom = (α_ X Y Z).inv :=
  (α_ X Y Z).dagger_hom_eq_inv_of_isUnitary (isUnitary_associator X Y Z)

/-- The dagger of the inverse associator is the forward associator. -/
@[simp]
theorem dagger_associator_inv (X Y Z : C) : dagger (α_ X Y Z).inv = (α_ X Y Z).hom := by
  rw [← dagger_associator_hom, dagger_dagger]

/-- The inverse associators are unitary. -/
@[simp]
theorem isUnitary_associator_inv (X Y Z : C) : IsUnitary (α_ X Y Z).inv := by
  rw [← dagger_associator_hom]
  exact (isUnitary_associator X Y Z).dagger

/-- The dagger of the forward left unitor is the inverse left unitor. -/
@[simp]
theorem dagger_leftUnitor_hom (X : C) : dagger (λ_ X).hom = (λ_ X).inv :=
  (λ_ X).dagger_hom_eq_inv_of_isUnitary (isUnitary_leftUnitor X)

/-- The dagger of the inverse left unitor is the forward left unitor. -/
@[simp]
theorem dagger_leftUnitor_inv (X : C) : dagger (λ_ X).inv = (λ_ X).hom := by
  rw [← dagger_leftUnitor_hom, dagger_dagger]

/-- The inverse left unitors are unitary. -/
@[simp]
theorem isUnitary_leftUnitor_inv (X : C) : IsUnitary (λ_ X).inv := by
  rw [← dagger_leftUnitor_hom]
  exact (isUnitary_leftUnitor X).dagger

/-- The dagger of the forward right unitor is the inverse right unitor. -/
@[simp]
theorem dagger_rightUnitor_hom (X : C) : dagger (ρ_ X).hom = (ρ_ X).inv :=
  (ρ_ X).dagger_hom_eq_inv_of_isUnitary (isUnitary_rightUnitor X)

/-- The dagger of the inverse right unitor is the forward right unitor. -/
@[simp]
theorem dagger_rightUnitor_inv (X : C) : dagger (ρ_ X).inv = (ρ_ X).hom := by
  rw [← dagger_rightUnitor_hom, dagger_dagger]

/-- The inverse right unitors are unitary. -/
@[simp]
theorem isUnitary_rightUnitor_inv (X : C) : IsUnitary (ρ_ X).inv := by
  rw [← dagger_rightUnitor_hom]
  exact (isUnitary_rightUnitor X).dagger

namespace IsUnitary

/-- Left whiskering preserves unitary arrows. -/
theorem whiskerLeft (X : C) {Y Z : C} {f : Y ⟶ Z} (hf : IsUnitary f) : IsUnitary (X ◁ f) := by
  rw [isUnitary_iff]
  simp [← MonoidalCategory.whiskerLeft_comp, hf.hom_dagger_id, hf.dagger_hom_id]

/-- Right whiskering preserves unitary arrows. -/
theorem whiskerRight {X Y : C} {f : X ⟶ Y} (hf : IsUnitary f) (Z : C) : IsUnitary (f ▷ Z) := by
  rw [isUnitary_iff]
  simp [← comp_whiskerRight, hf.hom_dagger_id, hf.dagger_hom_id]

/-- Tensor products of unitary arrows are unitary. -/
theorem tensorHom {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (hf : IsUnitary f) (hg : IsUnitary g) :
    IsUnitary (f ⊗ₘ g) := by
  rw [tensorHom_def]
  exact (hf.whiskerRight Y).comp (hg.whiskerLeft X)

end IsUnitary

/-- The monoidal opposite of a dagger monoidal category is a dagger monoidal category. -/
instance instDaggerMonoidalCategoryMonoidalOpposite : DaggerMonoidalCategory Cᴹᵒᵖ where
  dagger_whiskerLeft X _ _ f := Quiver.Hom.unmop_inj (dagger_whiskerRight f.unmop (unmop X))
  dagger_whiskerRight f Z := Quiver.Hom.unmop_inj (dagger_whiskerLeft (unmop Z) f.unmop)
  isUnitary_associator X Y Z :=
    (isUnitary_unmop_iff _).mp (isUnitary_associator_inv (unmop Z) (unmop Y) (unmop X))
  isUnitary_leftUnitor X := (isUnitary_unmop_iff _).mp (isUnitary_rightUnitor (unmop X))
  isUnitary_rightUnitor X := (isUnitary_unmop_iff _).mp (isUnitary_leftUnitor (unmop X))

section DaggerExactPairing

/-- In a dagger monoidal category, taking the daggers of the evaluation and coevaluation of an
exact pairing `ExactPairing X Y` produces an exact pairing `ExactPairing Y X`. Not an instance,
to avoid loops in typeclass search. -/
@[instance_reducible]
def daggerExactPairing (X Y : C) [ExactPairing X Y] : ExactPairing Y X where
  coevaluation' := dagger (ε_ X Y)
  evaluation' := dagger (η_ X Y)
  coevaluation_evaluation' := by
    simpa only [dagger_comp, dagger_whiskerLeft, dagger_whiskerRight, dagger_associator_hom,
      dagger_leftUnitor_hom, dagger_rightUnitor_inv, Category.assoc] using
        congrArg dagger (ExactPairing.evaluation_coevaluation X Y)
  evaluation_coevaluation' := by
    simpa only [dagger_comp, dagger_whiskerLeft, dagger_whiskerRight, dagger_associator_inv,
      dagger_rightUnitor_hom, dagger_leftUnitor_inv, Category.assoc] using
        congrArg dagger (ExactPairing.coevaluation_evaluation X Y)

/-- The evaluation of `daggerExactPairing X Y` is the dagger of `η_ X Y`. -/
@[simp, reassoc]
theorem daggerExactPairing_evaluation (X Y : C) [ExactPairing X Y] :
    @ExactPairing.evaluation C _ _ Y X (daggerExactPairing X Y) = dagger (η_ X Y) :=
  (rfl)

/-- The coevaluation of `daggerExactPairing X Y` is the dagger of `ε_ X Y`. -/
@[simp, reassoc]
theorem daggerExactPairing_coevaluation (X Y : C) [ExactPairing X Y] :
    @ExactPairing.coevaluation C _ _ Y X (daggerExactPairing X Y) = dagger (ε_ X Y) :=
  (rfl)

end DaggerExactPairing

end DaggerMonoidal

/-- Compatibility of a dagger structure with a braiding: every braiding isomorphism is unitary. -/
class DaggerBraidedCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [DaggerCategory C] : Prop where
  /-- The braiding isomorphisms are unitary. -/
  isUnitary_braiding : ∀ (X Y : C), IsUnitary (β_ X Y).hom

export DaggerBraidedCategory (isUnitary_braiding)

attribute [simp] isUnitary_braiding

section DaggerBraided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [DaggerCategory C] [DaggerBraidedCategory C]

/-- The dagger of the forward braiding is the inverse braiding. -/
@[simp]
theorem dagger_braiding_hom (X Y : C) : dagger (β_ X Y).hom = (β_ X Y).inv :=
  (β_ X Y).dagger_hom_eq_inv_of_isUnitary (isUnitary_braiding X Y)

/-- The dagger of the inverse braiding is the forward braiding. -/
@[simp]
theorem dagger_braiding_inv (X Y : C) : dagger (β_ X Y).inv = (β_ X Y).hom := by
  rw [← dagger_braiding_hom, dagger_dagger]

/-- The inverse braiding isomorphisms are unitary. -/
@[simp]
theorem isUnitary_braiding_inv (X Y : C) : IsUnitary (β_ X Y).inv := by
  rw [← dagger_braiding_hom]
  exact (isUnitary_braiding X Y).dagger

end DaggerBraided

/-- In a symmetric dagger braided category, the dagger of `β_{X,Y}` is `β_{Y,X}`. -/
theorem dagger_braiding_hom_eq_swap {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] [DaggerCategory C] [DaggerBraidedCategory C] (X Y : C) :
    dagger (β_ X Y).hom = (β_ Y X).hom := by
  rw [dagger_braiding_hom, SymmetricCategory.braiding_swap_eq_inv_braiding]

end TauCeti

namespace CategoryTheory.ExactPairing

open TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C]

/-- Taking a right mate with respect to `pX, pY`, applying the dagger, and then taking a right mate
with respect to the dagger exact pairings recovers the dagger of the original morphism. -/
theorem rightMate_daggerExactPairing {X X' Y Y' : C} (pX : ExactPairing X X')
    (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    rightMate (daggerExactPairing X X') (daggerExactPairing Y Y')
      (dagger (rightMate pX pY f)) = dagger f := by
  let := daggerExactPairing X X'
  apply rightHom_ext (X := X')
  rw [rightMate_comp_evaluation, daggerExactPairing_evaluation, daggerExactPairing_evaluation]
  apply dagger_inj.mp
  simpa only [dagger_comp, dagger_whiskerRight, dagger_whiskerLeft, dagger_dagger] using
    coevaluation_comp_rightMate pX pY f

end CategoryTheory.ExactPairing

namespace CategoryTheory.Functor

open TauCeti

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [DaggerCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [DaggerCategory E]

/-- A strong monoidal dagger-preserving functor is *dagger monoidal* when its unit and tensor
comparisons are unitary. -/
class IsDaggerMonoidal (F : C ⥤ D) [F.Monoidal] [F.PreservesDagger] : Prop where
  /-- The unit comparison `ε F : 𝟙_ D ⟶ F.obj (𝟙_ C)` is unitary. -/
  isUnitary_ε : IsUnitary (ε F)
  /-- The tensor comparisons `μ F X Y : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)` are unitary. -/
  isUnitary_μ : ∀ (X Y : C), IsUnitary (μ F X Y)

section IsDaggerMonoidal

variable (F : C ⥤ D) [F.Monoidal] [F.PreservesDagger] [F.IsDaggerMonoidal]

/-- The unit comparison of a dagger monoidal functor is unitary. -/
@[simp]
theorem isUnitary_ε : IsUnitary (ε F) := IsDaggerMonoidal.isUnitary_ε

/-- The tensor comparisons of a dagger monoidal functor are unitary. -/
@[simp]
theorem isUnitary_μ (X Y : C) : IsUnitary (μ F X Y) := IsDaggerMonoidal.isUnitary_μ X Y

/-- The dagger of the unit comparison `ε F` is the inverse unit comparison `η F`. -/
@[simp]
theorem dagger_ε : dagger (ε F) = η F :=
  (εIso F).dagger_hom_eq_inv_of_isUnitary (isUnitary_ε F)

/-- The dagger of the inverse unit comparison `η F` is `ε F`. -/
@[simp]
theorem dagger_η : dagger (η F) = ε F := by
  rw [← dagger_ε, dagger_dagger]

/-- The inverse unit comparison of a dagger monoidal functor is unitary. -/
@[simp]
theorem isUnitary_η : IsUnitary (η F) := by
  rw [← dagger_ε]
  exact (isUnitary_ε F).dagger

/-- The dagger of the tensor comparison `μ F X Y` is the inverse tensor comparison `δ F X Y`. -/
@[simp]
theorem dagger_μ (X Y : C) : dagger (μ F X Y) = δ F X Y :=
  (μIso F X Y).dagger_hom_eq_inv_of_isUnitary (isUnitary_μ F X Y)

/-- The dagger of the inverse tensor comparison `δ F X Y` is `μ F X Y`. -/
@[simp]
theorem dagger_δ (X Y : C) : dagger (δ F X Y) = μ F X Y := by
  rw [← dagger_μ, dagger_dagger]

/-- The inverse tensor comparisons of a dagger monoidal functor are unitary. -/
@[simp]
theorem isUnitary_δ (X Y : C) : IsUnitary (δ F X Y) := by
  rw [← dagger_μ]
  exact (isUnitary_μ F X Y).dagger

end IsDaggerMonoidal

/-- The identity functor is dagger monoidal. -/
instance instIsDaggerMonoidalId : (𝟭 C).IsDaggerMonoidal where
  isUnitary_ε := by simp
  isUnitary_μ _ _ := by simp

/-- The composite of dagger monoidal functors is dagger monoidal. -/
instance instIsDaggerMonoidalComp (F : C ⥤ D) (G : D ⥤ E)
    [F.Monoidal] [F.PreservesDagger] [F.IsDaggerMonoidal]
    [G.Monoidal] [G.PreservesDagger] [G.IsDaggerMonoidal] :
    (F ⋙ G).IsDaggerMonoidal where
  isUnitary_ε := by
    rw [Functor.LaxMonoidal.comp_ε]
    exact (isUnitary_ε G).comp (G.map_isUnitary (isUnitary_ε F))
  isUnitary_μ X Y := by
    rw [Functor.LaxMonoidal.comp_μ]
    exact (isUnitary_μ G (F.obj X) (F.obj Y)).comp (G.map_isUnitary (isUnitary_μ F X Y))

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

open TauCeti

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [DaggerCategory D]
  [DaggerMonoidalCategory D]

/-- The pointwise dagger of a monoidal natural transformation between dagger monoidal functors is
again a monoidal natural transformation. -/
instance isMonoidal_dagger {F G : C ⥤ D}
    [F.Monoidal] [F.PreservesDagger] [F.IsDaggerMonoidal]
    [G.Monoidal] [G.PreservesDagger] [G.IsDaggerMonoidal]
    (α : F ⟶ G) [NatTrans.IsMonoidal α] : NatTrans.IsMonoidal α.dagger where
  unit := by
    have h := congrArg TauCeti.dagger (NatTrans.IsMonoidal.unit (τ := α))
    simp only [TauCeti.dagger_comp, Functor.dagger_ε] at h
    calc ε G ≫ α.dagger.app (𝟙_ C)
        = ε G ≫ (TauCeti.dagger (α.app (𝟙_ C)) ≫ η F) ≫ ε F := by
          simp only [NatTrans.dagger_app, Category.assoc, Functor.Monoidal.η_ε, Category.comp_id]
      _ = ε G ≫ η G ≫ ε F := by rw [h]
      _ = ε F := by rw [Functor.Monoidal.ε_η_assoc]
  tensor X Y := by
    have h := congrArg TauCeti.dagger (NatTrans.IsMonoidal.tensor (τ := α) X Y)
    simp only [TauCeti.dagger_comp, dagger_tensorHom, Functor.dagger_μ] at h
    calc μ G X Y ≫ α.dagger.app (X ⊗ Y)
        = μ G X Y ≫ (TauCeti.dagger (α.app (X ⊗ Y)) ≫ δ F X Y) ≫ μ F X Y := by
          simp only [NatTrans.dagger_app, Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
      _ = μ G X Y ≫
            (δ G X Y ≫ (TauCeti.dagger (α.app X) ⊗ₘ TauCeti.dagger (α.app Y))) ≫ μ F X Y := by
          rw [h]
      _ = (α.dagger.app X ⊗ₘ α.dagger.app Y) ≫ μ F X Y := by
          simp only [NatTrans.dagger_app, ← Category.assoc, Functor.Monoidal.μ_δ,
            Category.id_comp]

end CategoryTheory.NatTrans

namespace TauCeti

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [DaggerCategory C]
variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D] [DaggerCategory D]

/-- Bundled dagger monoidal functors between dagger monoidal categories, forming a full subcategory
of `LaxMonoidalFunctor C D` equipped with a native dagger structure. -/
structure DaggerMonoidalFunctor extends C ⥤ D where
  /-- The underlying strong monoidal structure. -/
  monoidal : toFunctor.Monoidal := by infer_instance
  /-- Preservation of the dagger. -/
  preservesDagger : toFunctor.PreservesDagger := by infer_instance
  /-- Unitarity of the unit and tensor comparisons. -/
  isDaggerMonoidal : toFunctor.IsDaggerMonoidal := by infer_instance

namespace DaggerMonoidalFunctor

attribute [instance] monoidal preservesDagger isDaggerMonoidal

variable {C D}

/-- Bundle a dagger monoidal functor into `DaggerMonoidalFunctor C D`. -/
def of (F : C ⥤ D) [F.Monoidal] [F.PreservesDagger] [F.IsDaggerMonoidal] :
    DaggerMonoidalFunctor C D where
  toFunctor := F

/-- The underlying functor of `DaggerMonoidalFunctor.of F` is `F`. -/
@[simp]
theorem of_toFunctor (F : C ⥤ D) [F.Monoidal] [F.PreservesDagger] [F.IsDaggerMonoidal] :
    (of F).toFunctor = F :=
  (rfl)

/-- Forget the dagger structure to obtain a bundled `LaxMonoidalFunctor`. -/
@[expose]
def toLaxMonoidalFunctor (F : DaggerMonoidalFunctor C D) : LaxMonoidalFunctor C D where
  toFunctor := F.toFunctor

/-- The underlying functor of `F.toLaxMonoidalFunctor` is `F.toFunctor`. -/
@[simp]
theorem toLaxMonoidalFunctor_toFunctor (F : DaggerMonoidalFunctor C D) :
    F.toLaxMonoidalFunctor.toFunctor = F.toFunctor :=
  (rfl)

/-- A morphism of dagger monoidal functors is a monoidal natural transformation between the
underlying functors. -/
structure Hom (F G : DaggerMonoidalFunctor C D) where
  /-- The underlying natural transformation. -/
  hom : F.toFunctor ⟶ G.toFunctor
  /-- Compatibility with the unit and tensor comparisons. -/
  isMonoidal : NatTrans.IsMonoidal hom := by infer_instance

attribute [instance] Hom.isMonoidal

/-- Morphisms of dagger monoidal functors are monoidal natural transformations, matching the full
subcategory of `LaxMonoidalFunctor C D`. -/
instance instCategory : Category (DaggerMonoidalFunctor C D) where
  Hom F G := Hom F G
  id F := ⟨𝟙 F.toFunctor, inferInstance⟩
  comp α β := ⟨α.hom ≫ β.hom, inferInstance⟩

/-- The identity morphism in `DaggerMonoidalFunctor C D` has identity underlying transformation. -/
@[simp]
theorem id_hom (F : DaggerMonoidalFunctor C D) : (𝟙 F : F ⟶ F).hom = 𝟙 F.toFunctor :=
  (rfl)

/-- Composition in `DaggerMonoidalFunctor C D` composes the underlying natural transformations. -/
@[simp, reassoc]
theorem comp_hom {F G H : DaggerMonoidalFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom :=
  (rfl)

/-- Two morphisms of dagger monoidal functors agree if their underlying natural transformations
agree. -/
@[ext]
theorem hom_ext {F G : DaggerMonoidalFunctor C D} {α β : F ⟶ G}
    (h : α.hom = β.hom) : α = β := by
  cases α
  cases β
  subst h
  rfl

/-- Construct a morphism in `DaggerMonoidalFunctor C D` from a monoidal natural transformation. -/
def homMk {F G : DaggerMonoidalFunctor C D} (α : F.toFunctor ⟶ G.toFunctor)
    [NatTrans.IsMonoidal α] : F ⟶ G :=
  ⟨α, inferInstance⟩

/-- The underlying natural transformation of `homMk α` is `α`. -/
@[simp]
theorem homMk_hom {F G : DaggerMonoidalFunctor C D} (α : F.toFunctor ⟶ G.toFunctor)
    [NatTrans.IsMonoidal α] : (homMk α).hom = α :=
  (rfl)

/-- Construct an isomorphism in `DaggerMonoidalFunctor C D` from a monoidal natural isomorphism. -/
def isoMk {F G : DaggerMonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : F ≅ G where
  hom := homMk e.hom
  inv := homMk e.inv
  hom_inv_id := by ext : 1; exact e.hom_inv_id
  inv_hom_id := by ext : 1; exact e.inv_hom_id

/-- The forward morphism of `isoMk e` has underlying natural transformation `e.hom`. -/
@[simp]
theorem isoMk_hom_hom {F G : DaggerMonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : (isoMk e).hom.hom = e.hom :=
  (rfl)

/-- The inverse morphism of `isoMk e` has underlying natural transformation `e.inv`. -/
@[simp]
theorem isoMk_inv_hom {F G : DaggerMonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : (isoMk e).inv.hom = e.inv :=
  (rfl)

section Dagger

variable [DaggerMonoidalCategory D]

/-- The category of dagger monoidal functors is a dagger category under pointwise daggers. -/
instance instDaggerCategory : DaggerCategory (DaggerMonoidalFunctor C D) where
  dagger α := homMk α.hom.dagger
  dagger_id F := by ext; simp
  dagger_comp α β := by ext; simp
  dagger_dagger α := by ext; simp

/-- The dagger of a morphism in `DaggerMonoidalFunctor C D` acts by `NatTrans.dagger`. -/
@[simp]
theorem dagger_hom {F G : DaggerMonoidalFunctor C D} (α : F ⟶ G) :
    (dagger α).hom = α.hom.dagger :=
  (rfl)

/-- A morphism in `DaggerMonoidalFunctor C D` is unitary if and only if every component is
unitary in `D`. -/
theorem isUnitary_iff {F G : DaggerMonoidalFunctor C D} (α : F ⟶ G) :
    IsUnitary α ↔ ∀ X : C, IsUnitary (α.hom.app X) := by
  constructor
  · intro h X
    rw [TauCeti.isUnitary_iff]
    exact ⟨by simpa using congrArg (fun β : F ⟶ F => β.hom.app X) h.hom_dagger_id,
      by simpa using congrArg (fun β : G ⟶ G => β.hom.app X) h.dagger_hom_id⟩
  · intro h
    rw [TauCeti.isUnitary_iff]
    constructor <;> (ext X; simp [(h X).hom_dagger_id, (h X).dagger_hom_id])

/-- A monoidal natural transformation with unitary components yields a unitary isomorphism in
`DaggerMonoidalFunctor C D`. -/
def unitaryIso {F G : DaggerMonoidalFunctor C D} (α : F ⟶ G)
    (hα : ∀ X : C, IsUnitary (α.hom.app X)) : F ≅ G :=
  ((isUnitary_iff α).mpr hα).toIso

/-- The forward morphism of `unitaryIso α hα` is `α`. -/
@[simp]
theorem unitaryIso_hom {F G : DaggerMonoidalFunctor C D} (α : F ⟶ G)
    (hα : ∀ X : C, IsUnitary (α.hom.app X)) : (unitaryIso α hα).hom = α :=
  IsUnitary.toIso_hom _

/-- The inverse morphism of `unitaryIso α hα` is `dagger α`. -/
@[simp]
theorem unitaryIso_inv {F G : DaggerMonoidalFunctor C D} (α : F ⟶ G)
    (hα : ∀ X : C, IsUnitary (α.hom.app X)) : (unitaryIso α hα).inv = dagger α :=
  IsUnitary.toIso_inv _

end Dagger

variable (C D)

/-- The forgetful functor from `DaggerMonoidalFunctor C D` to `LaxMonoidalFunctor C D`. -/
@[expose]
def forget : DaggerMonoidalFunctor C D ⥤ LaxMonoidalFunctor C D where
  obj F := F.toLaxMonoidalFunctor
  map α := ⟨α.hom, α.isMonoidal⟩

/-- `forget` sends a dagger monoidal functor to `F.toLaxMonoidalFunctor`. -/
@[simp]
theorem forget_obj (F : DaggerMonoidalFunctor C D) :
    (forget C D).obj F = F.toLaxMonoidalFunctor :=
  (rfl)

/-- `forget` preserves the underlying natural transformation of a morphism. -/
@[simp]
theorem forget_map_hom {F G : DaggerMonoidalFunctor C D} (α : F ⟶ G) :
    ((forget C D).map α).hom = α.hom :=
  (rfl)

/-- The forgetful functor `DaggerMonoidalFunctor C D ⥤ LaxMonoidalFunctor C D` is fully
faithful. -/
def fullyFaithfulForget : (forget C D).FullyFaithful where
  preimage α := ⟨α.hom, α.isMonoidal⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- The forgetful functor from `DaggerMonoidalFunctor C D` to `LaxMonoidalFunctor C D` is full. -/
instance instFullForget : (forget C D).Full := (fullyFaithfulForget C D).full

/-- The forgetful functor from `DaggerMonoidalFunctor C D` to `LaxMonoidalFunctor C D` is
faithful. -/
instance instFaithfulForget : (forget C D).Faithful := (fullyFaithfulForget C D).faithful

end DaggerMonoidalFunctor

end TauCeti
