/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Detecting monomorphisms, epimorphisms and isomorphisms with injective objects

In a category with enough injectives, morphisms into injective objects separate parallel pairs
and detect monomorphisms: a morphism `f : X ⟶ Y` is a monomorphism if precomposition with `f` is
surjective on `Hom(-, I)` for every injective object `I` (take `I` to be an injective object
containing `X`), and is an epimorphism if precomposition with `f` is injective on `Hom(-, I)` for
every injective `I` (compose a parallel pair after `f` with a monomorphism into an injective). In
a balanced category with enough injectives—in particular any abelian category with enough
injectives, such as `ModuleCat K`—a morphism `f` is therefore an isomorphism exactly when
precomposition with `f` is bijective on `Hom(-, I)` for every injective object `I`.

## Main results

* `TauCeti.mono_of_surjective_precomp_injective`: if `g ↦ f ≫ g` is surjective into every
  injective object, then `f` is a monomorphism.
* `TauCeti.epi_of_injective_precomp_injective`: if `g ↦ f ≫ g` is injective into every injective
  object, then `f` is an epimorphism.
* `TauCeti.isIso_of_bijective_precomp_injective` and
  `TauCeti.isIso_iff_bijective_precomp_injective`: in a balanced category with enough injectives,
  `f` is an isomorphism iff `g ↦ f ≫ g` is bijective into every injective object.
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [EnoughInjectives C]

/-- In a category with enough injectives, a morphism `f : X ⟶ Y` is a monomorphism if
precomposition `g ↦ f ≫ g` is surjective on `Hom(-, I)` for every injective object `I`. -/
theorem mono_of_surjective_precomp_injective {X Y : C} (f : X ⟶ Y)
    (h : ∀ (I : C) [Injective I], Function.Surjective fun g : Y ⟶ I ↦ f ≫ g) : Mono f := by
  obtain ⟨g, hg⟩ := h (Injective.under X) (Injective.ι X)
  exact mono_of_mono_fac hg

/-- In a category with enough injectives, a morphism `f : X ⟶ Y` is an epimorphism if
precomposition `g ↦ f ≫ g` is injective on `Hom(-, I)` for every injective object `I`. -/
theorem epi_of_injective_precomp_injective {X Y : C} (f : X ⟶ Y)
    (h : ∀ (I : C) [Injective I], Function.Injective fun g : Y ⟶ I ↦ f ≫ g) : Epi f :=
  ⟨fun {Z} g₁ g₂ heq ↦ (cancel_mono (Injective.ι Z)).1
    (h (Injective.under Z) (by simp [reassoc_of% heq]))⟩

/-- In a balanced category with enough injectives, a morphism `f : X ⟶ Y` is an isomorphism if
precomposition `g ↦ f ≫ g` is bijective on `Hom(-, I)` for every injective object `I`. -/
theorem isIso_of_bijective_precomp_injective [Balanced C] {X Y : C} (f : X ⟶ Y)
    (h : ∀ (I : C) [Injective I], Function.Bijective fun g : Y ⟶ I ↦ f ≫ g) : IsIso f :=
  have := mono_of_surjective_precomp_injective f fun I _ ↦ (h I).2
  have := epi_of_injective_precomp_injective f fun I _ ↦ (h I).1
  isIso_of_mono_of_epi f

/-- In a balanced category with enough injectives, a morphism `f : X ⟶ Y` is an isomorphism
exactly when precomposition `g ↦ f ≫ g` is bijective on `Hom(-, I)` for every injective object
`I`. -/
theorem isIso_iff_bijective_precomp_injective [Balanced C] {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ (I : C) [Injective I], Function.Bijective fun g : Y ⟶ I ↦ f ≫ g :=
  ⟨fun _ I _ ↦ ⟨fun _ _ h ↦ (cancel_epi f).1 h, fun g ↦ ⟨inv f ≫ g, by simp⟩⟩,
    isIso_of_bijective_precomp_injective f⟩

end TauCeti
