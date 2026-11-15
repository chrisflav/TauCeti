/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Braided.Free.Substitution
public import TauCeti.CategoryTheory.Quotient.Braided

/-!
# Braided monoidal categories presented by generators and relations

A *braided presentation* consists of a tensor signature `S` (generating objects and arbitrary-arity
coupons between formal tensor words) together with a family `R : HomRel S.FreeBraided` of typed
equations between morphisms of the free braided monoidal category on `S`. The braided monoidal
category `S.PresentedBraided R` is the quotient of `TauCeti.TensorSignature.FreeBraided S` by the
least monoidal congruence `HomRel.MonoidalClosure R` containing `R`, equipped with the descended
monoidal and braided structures from `TauCeti.CategoryTheory.Quotient.Braided`. Only the equations
`R` are imposed beyond the axioms of a braided monoidal category.

Its universal property restricts that of `S.FreeBraided` to interpretations satisfying `R`: given
images `fo` of the generating objects and `fc` of the coupons in an arbitrary (not necessarily
strict) braided monoidal category `D`, the interpretation `FreeBraided.lift fo fc` descends through
`S.PresentedBraided R` if and only if it identifies the two sides of every equation of `R`
(`PresentedBraided.exists_comp_quotientFunctor_eq_lift_iff`), yielding the strong braided functor
`PresentedBraided.lift fo fc h`, unique up to a unique monoidal natural isomorphism extending given
isomorphisms on the generating objects (`PresentedBraided.monoidalNatIso`,
`PresentedBraided.natTrans_ext`). Furthermore, a braided substitution between signatures descends
to a strong braided functor between presented braided categories whenever it sends defining
equations to valid equations (`BraidedSubstitution.descend`).

## Main definitions and results

* `TauCeti.TensorSignature.PresentedBraided S R`: the braided monoidal category presented by `S`
  and `R`, with strict braided quotient functor `PresentedBraided.quotientFunctor R` and soundness
  `PresentedBraided.sound`.
* `TauCeti.TensorSignature.PresentedBraided.lift fo fc h`: the strong braided functor into an
  arbitrary braided monoidal category `D`, with `PresentedBraided.quotientFunctor_comp_lift` and
  `PresentedBraided.exists_comp_quotientFunctor_eq_lift_iff`.
* `TauCeti.TensorSignature.PresentedBraided.monoidalNatIso` and `PresentedBraided.natTrans_ext`:
  coherence of monoidal natural isomorphisms and transformations out of `S.PresentedBraided R`.
* `TauCeti.TensorSignature.BraidedSubstitution.descend`: descent of a `BraidedSubstitution` to a
  strong braided functor between presented braided monoidal categories.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §§1, 3.
* P. Selinger, *A survey of graphical languages for monoidal categories*, New Structures for
  Physics, Lecture Notes in Phys. 813 (2011), §3.3.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory BraidedCategory

namespace TauCeti.TensorSignature

variable (S : TensorSignature.{u, v}) (R : HomRel S.FreeBraided)

/-- The braided monoidal category presented by the tensor signature `S` and the equations `R`
between morphisms of `S.FreeBraided`: the quotient of `S.FreeBraided` by the least monoidal
congruence containing `R`, with the descended monoidal and braided structures. -/
abbrev PresentedBraided : Type u :=
  CategoryTheory.Quotient (HomRel.MonoidalClosure R)

namespace PresentedBraided

variable {S}

/-- The quotient functor from the free braided monoidal category on `S` onto the braided monoidal
category presented by `S` and `R`. It is strict braided monoidal for the descended structures. -/
abbrev quotientFunctor : S.FreeBraided ⥤ S.PresentedBraided R :=
  CategoryTheory.Quotient.functor _

variable {R}

/-- Every defining equation in `R` holds in `S.PresentedBraided R`. -/
theorem sound {X Y : S.FreeBraided} {f g : X ⟶ Y} (h : R f g) :
    (quotientFunctor R).map f = (quotientFunctor R).map g :=
  CategoryTheory.Quotient.sound _ (.of h)

section Lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (fo : S.Obj → D)
  (fc : ∀ g : S.Coupon,
    FreeMonoidalCategory.projectObj fo (S.src g) ⟶ FreeMonoidalCategory.projectObj fo (S.tgt g))
  (h : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
    (FreeBraided.lift fo fc).map f = (FreeBraided.lift fo fc).map g)

/-- The functor out of `S.PresentedBraided R` determined by the images `fo` of the generating
objects and `fc` of the coupons, provided the induced braided interpretation
`FreeBraided.lift fo fc` satisfies the equations `R`. It is strong braided monoidal, with identity
tensorator and unit comparison. -/
@[expose] def lift : S.PresentedBraided R ⥤ D :=
  CategoryTheory.Quotient.lift _ (FreeBraided.lift fo fc) fun _ _ _ _ hfg ↦
    HomRel.MonoidalClosure.map_eq h hfg

instance : (lift fo fc h).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

noncomputable instance : (lift fo fc h).Braided :=
  CategoryTheory.Quotient.liftBraided _ _ _

/-- Restricting `PresentedBraided.lift fo fc h` along `quotientFunctor R` recovers
`FreeBraided.lift fo fc`. -/
theorem quotientFunctor_comp_lift :
    quotientFunctor R ⋙ lift fo fc h = FreeBraided.lift fo fc :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- The braided interpretation `FreeBraided.lift fo fc` factors through `quotientFunctor R` if and
only if it identifies the two sides of every defining equation in `R`. -/
theorem exists_comp_quotientFunctor_eq_lift_iff :
    (∃ F : S.PresentedBraided R ⥤ D, quotientFunctor R ⋙ F = FreeBraided.lift fo fc) ↔
      ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
        (FreeBraided.lift fo fc).map f = (FreeBraided.lift fo fc).map g :=
  ⟨fun ⟨F, hF⟩ _ _ _ _ hfg ↦ by
    rw [← hF]
    exact congrArg F.map (sound hfg),
    fun hR ↦ ⟨lift fo fc hR, quotientFunctor_comp_lift fo fc hR⟩⟩

@[simp]
theorem lift_obj (X : S.FreeBraided) :
    (lift fo fc h).obj ((quotientFunctor R).obj X) = (FreeBraided.lift fo fc).obj X :=
  (rfl)

@[simp]
theorem lift_map {X Y : S.FreeBraided} (f : X ⟶ Y) :
    (lift fo fc h).map ((quotientFunctor R).map f) = (FreeBraided.lift fo fc).map f :=
  (rfl)

@[simp]
theorem lift_ε : Functor.LaxMonoidal.ε (lift fo fc h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_ε _ _).trans (FreeBraided.lift_ε fo fc)

@[simp]
theorem lift_η : Functor.OplaxMonoidal.η (lift fo fc h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_η _ _).trans (FreeBraided.lift_η fo fc)

@[simp]
theorem lift_μ (X Y : S.PresentedBraided R) :
    Functor.LaxMonoidal.μ (lift fo fc h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_μ _ _ X.as Y.as).trans (FreeBraided.lift_μ fo fc X.as Y.as)

@[simp]
theorem lift_δ (X Y : S.PresentedBraided R) :
    Functor.OplaxMonoidal.δ (lift fo fc h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_δ _ _ X.as Y.as).trans (FreeBraided.lift_δ fo fc X.as Y.as)

end Lift

section MonoidalUniqueness

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation from a strong monoidal functor out of `S.PresentedBraided R`
to a lax monoidal one is determined by its components at the generating objects. -/
theorem natTrans_ext {F G : S.PresentedBraided R ⥤ D} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β]
    (h : ∀ a, α.app ((quotientFunctor R).obj (.of a)) = β.app ((quotientFunctor R).obj (.of a))) :
    α = β :=
  CategoryTheory.Quotient.natTrans_ext _ _ (FreeBraided.natTrans_ext h)

end MonoidalUniqueness

section BraidedUniqueness

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (F G : S.PresentedBraided R ⥤ D) [F.Braided] [G.Braided]
  (e : ∀ a, F.obj ((quotientFunctor R).obj (.of a)) ≅ G.obj ((quotientFunctor R).obj (.of a)))

/-- Two strong braided functors out of `S.PresentedBraided R` that agree up to isomorphisms `e` on
the generating objects, compatibly with every coupon, are isomorphic by a monoidal natural
isomorphism extending `e`. -/
noncomputable def monoidalNatIso
    (he : ∀ g, F.map ((quotientFunctor R).map (FreeBraided.coupon g)) ≫
        (FreeBraided.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.tgt g)).hom =
      (FreeBraided.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.src g)).hom ≫
        G.map ((quotientFunctor R).map (FreeBraided.coupon g))) :
    F ≅ G :=
  CategoryTheory.Quotient.natIsoLift _ (FreeBraided.monoidalNatIso he)

variable {F G e}
  (he : ∀ g, F.map ((quotientFunctor R).map (FreeBraided.coupon g)) ≫
      (FreeBraided.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.tgt g)).hom =
    (FreeBraided.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.src g)).hom ≫
      G.map ((quotientFunctor R).map (FreeBraided.coupon g)))

@[simp]
theorem monoidalNatIso_hom_app (X : S.FreeBraided) :
    (monoidalNatIso F G e he).hom.app ((quotientFunctor R).obj X) =
      (FreeBraided.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e X.as).hom :=
  FreeBraided.monoidalNatIso_hom_app he X

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso F G e he).hom.app ((quotientFunctor R).obj (.of a)) = (e a).hom :=
  FreeBraided.monoidalNatIso_hom_app_of he a

noncomputable instance : NatTrans.IsMonoidal (monoidalNatIso F G e he).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    (CategoryTheory.Quotient.natTransLift _ (FreeBraided.monoidalNatIso he).hom))

end BraidedUniqueness

end PresentedBraided

namespace BraidedSubstitution

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}
  (σ : BraidedSubstitution S T)
  {R₁ : HomRel S.FreeBraided} {R₂ : HomRel T.FreeBraided}
  (hσ : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R₁ f g →
    (PresentedBraided.quotientFunctor R₂).map (σ.toFunctor.map f) =
      (PresentedBraided.quotientFunctor R₂).map (σ.toFunctor.map g))

/-- Descend a braided substitution `σ` to a functor between presented braided monoidal categories
when `σ` sends every defining equation in `R₁` to an equation holding in `T.PresentedBraided R₂`.
It is strong braided monoidal, with identity tensorator and unit comparison. -/
@[expose] def descend : S.PresentedBraided R₁ ⥤ T.PresentedBraided R₂ :=
  CategoryTheory.Quotient.lift _ (σ.toFunctor ⋙ PresentedBraided.quotientFunctor R₂)
    fun _ _ _ _ hfg ↦
      HomRel.MonoidalClosure.map_eq
        (F := σ.toFunctor ⋙ PresentedBraided.quotientFunctor R₂) hσ hfg

instance : (σ.descend hσ).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

noncomputable instance : (σ.descend hσ).Braided :=
  CategoryTheory.Quotient.liftBraided _ _ _

/-- Precomposing `σ.descend hσ` with `PresentedBraided.quotientFunctor R₁` equals postcomposing
`σ.toFunctor` with `PresentedBraided.quotientFunctor R₂`. -/
theorem quotientFunctor_comp_descend :
    PresentedBraided.quotientFunctor R₁ ⋙ σ.descend hσ =
      σ.toFunctor ⋙ PresentedBraided.quotientFunctor R₂ :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem descend_obj (X : S.FreeBraided) :
    (σ.descend hσ).obj ((PresentedBraided.quotientFunctor R₁).obj X) =
      (PresentedBraided.quotientFunctor R₂).obj (σ.toFunctor.obj X) :=
  (rfl)

@[simp]
theorem descend_map {X Y : S.FreeBraided} (f : X ⟶ Y) :
    (σ.descend hσ).map ((PresentedBraided.quotientFunctor R₁).map f) =
      (PresentedBraided.quotientFunctor R₂).map (σ.toFunctor.map f) :=
  (rfl)

@[simp]
theorem descend_ε : Functor.LaxMonoidal.ε (σ.descend hσ) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_ε _ _).trans <|
    (Functor.LaxMonoidal.comp_ε σ.toFunctor (PresentedBraided.quotientFunctor R₂)).trans <|
      (congrArg₂ (· ≫ ·) (CategoryTheory.Quotient.functor_ε)
        ((congrArg (PresentedBraided.quotientFunctor R₂).map σ.toFunctor_ε).trans
          (Functor.map_id _ _))).trans (Category.id_comp _)

@[simp]
theorem descend_η : Functor.OplaxMonoidal.η (σ.descend hσ) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_η _ _).trans <|
    (Functor.OplaxMonoidal.comp_η σ.toFunctor (PresentedBraided.quotientFunctor R₂)).trans <|
      (congrArg₂ (· ≫ ·)
        ((congrArg (PresentedBraided.quotientFunctor R₂).map σ.toFunctor_η).trans
          (Functor.map_id _ _))
        (CategoryTheory.Quotient.functor_η)).trans (Category.id_comp _)

@[simp]
theorem descend_μ (X Y : S.PresentedBraided R₁) :
    Functor.LaxMonoidal.μ (σ.descend hσ) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_μ _ _ X.as Y.as).trans <|
    (Functor.LaxMonoidal.comp_μ σ.toFunctor (PresentedBraided.quotientFunctor R₂)
      X.as Y.as).trans <|
      (congrArg₂ (· ≫ ·) (CategoryTheory.Quotient.functor_μ _ _)
        ((congrArg (PresentedBraided.quotientFunctor R₂).map
          (σ.toFunctor_μ X.as Y.as)).trans (Functor.map_id _ _))).trans
        (Category.id_comp _)

@[simp]
theorem descend_δ (X Y : S.PresentedBraided R₁) :
    Functor.OplaxMonoidal.δ (σ.descend hσ) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_δ _ _ X.as Y.as).trans <|
    (Functor.OplaxMonoidal.comp_δ σ.toFunctor (PresentedBraided.quotientFunctor R₂)
      X.as Y.as).trans <|
      (congrArg₂ (· ≫ ·)
        ((congrArg (PresentedBraided.quotientFunctor R₂).map
          (σ.toFunctor_δ X.as Y.as)).trans (Functor.map_id _ _))
        (CategoryTheory.Quotient.functor_δ _ _)).trans (Category.id_comp _)

end BraidedSubstitution

end TauCeti.TensorSignature
