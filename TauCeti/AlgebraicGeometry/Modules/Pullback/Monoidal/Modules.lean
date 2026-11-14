/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Monoidal
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Identity
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Strong symmetric monoidal pullback of sheaves of modules on schemes

For every morphism of schemes `f : X ⟶ Y` and all sheaves of `𝒪_Y`-modules `M` and `N`, the
canonical oplax tensor comparison `δ : f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` is an isomorphism
(`Scheme.Modules.isIso_pullback_δ`, `Scheme.Modules.pullbackTensorIso`), without any flatness,
finiteness, or quasi-coherence assumptions.

Together with the structure-sheaf identification `f^* 𝒪_Y ≅ 𝒪_X`
(`Scheme.Modules.pullbackObjUnitIso`), this upgrades
`Scheme.Modules.pullback f : Y.Modules ⥤ X.Modules` to a strong symmetric monoidal functor
(`Scheme.Modules.pullbackMonoidal`, `Scheme.Modules.pullbackBraided`). Moreover, the
canonical identity, composition, and morphism-equality identifications `pullbackId`, `pullbackComp`,
and `pullbackCongr` are monoidal natural isomorphisms
(`Scheme.Modules.isMonoidal_pullbackId_hom`, `Scheme.Modules.isMonoidal_pullbackComp_hom`,
`Scheme.Modules.isMonoidal_pullbackCongr_hom`), and arbitrary pullback preserves left and right
dualizable `𝒪_Y`-modules (`Scheme.Modules.nonempty_hasLeftDual_pullback`,
`Scheme.Modules.nonempty_hasRightDual_pullback`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isIso_pullback_δ` and
  `AlgebraicGeometry.Scheme.Modules.pullbackTensorIso`: unconditional invertibility of
  `δ (pullback f) M N` and the resulting isomorphism `f^* (M ⊗ N) ≅ f^* M ⊗ f^* N`.
* `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal` and
  `AlgebraicGeometry.Scheme.Modules.pullbackBraided`: strong braided (hence symmetric) monoidal
  structure on `Scheme.Modules.pullback f`.
* `AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackId_hom`,
  `AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackComp_hom`, and
  `AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackCongr_hom`: monoidal coherences for identity,
  composition, and equal morphisms.

## References

* [The Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD).
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 5.2(d).
-/

public section

open CategoryTheory MonoidalCategory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

section Morphism

variable {X Y : Scheme.{u}}

/-- **Unconditional pullback of tensor products on schemes.** For any morphism of schemes
`f : X ⟶ Y` and any `𝒪_Y`-modules `M` and `N`, the canonical oplax tensor comparison
`δ : f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` is an isomorphism, with no flatness, finiteness, or
quasi-coherence assumptions. -/
instance isIso_pullback_δ (f : X ⟶ Y) (M N : Y.Modules) :
    IsIso (Functor.OplaxMonoidal.δ (pullback f) M N) :=
  TauCeti.SheafOfModules.isIso_pullback_δ f.toRingCatSheafHom M N

/-- The canonical isomorphism `f^* (M ⊗ N) ≅ f^* M ⊗ f^* N` for arbitrary `𝒪_Y`-modules along a
morphism of schemes `f : X ⟶ Y`. -/
def pullbackTensorIso (f : X ⟶ Y) (M N : Y.Modules) :
    (pullback f).obj (M ⊗ N) ≅ (pullback f).obj M ⊗ (pullback f).obj N :=
  asIso (Functor.OplaxMonoidal.δ (pullback f) M N)

/-- The forward morphism of `pullbackTensorIso` is the oplax tensor comparison `δ`. -/
@[simp]
theorem pullbackTensorIso_hom (f : X ⟶ Y) (M N : Y.Modules) :
    (pullbackTensorIso f M N).hom = Functor.OplaxMonoidal.δ (pullback f) M N := by
  unfold pullbackTensorIso
  rfl

/-- Module pullback along any morphism of schemes is a strong monoidal functor on all sheaves of
modules. -/
instance pullbackMonoidal (f : X ⟶ Y) : (pullback f).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (pullback f)

/-- The inverse morphism of `pullbackTensorIso` is the lax tensor comparison `μ`. -/
@[simp]
theorem pullbackTensorIso_inv (f : X ⟶ Y) (M N : Y.Modules) :
    (pullbackTensorIso f M N).inv = Functor.LaxMonoidal.μ (pullback f) M N := by
  unfold pullbackTensorIso
  exact Functor.Monoidal.inv_δ (pullback f) M N

/-- The lax tensor comparison `μ` of strong monoidal module pullback is the inverse of `δ`. -/
theorem pullback_μ (f : X ⟶ Y) (M N : Y.Modules) :
    Functor.LaxMonoidal.μ (pullback f) M N = inv (Functor.OplaxMonoidal.δ (pullback f) M N) :=
  IsIso.eq_inv_of_hom_inv_id (Functor.Monoidal.δ_μ (pullback f) M N)

/-- The lax unit comparison `ε` of strong monoidal module pullback is `(pullbackObjUnitIso f).inv`.
-/
@[simp]
theorem pullback_ε (f : X ⟶ Y) :
    Functor.LaxMonoidal.ε (pullback f) = (pullbackObjUnitIso f).inv := by
  have h : Functor.LaxMonoidal.ε (pullback f) ≫ (pullbackObjUnitIso f).hom = 𝟙 _ :=
    (congrArg (Functor.LaxMonoidal.ε (pullback f) ≫ ·) (pullback_η f).symm).trans
      (Functor.Monoidal.ε_η (pullback f))
  exact (Iso.comp_hom_eq_id (pullbackObjUnitIso f)).mp h

/-- Module pullback along any morphism of schemes is a braided (hence symmetric) strong monoidal
functor on all sheaves of modules. -/
instance pullbackBraided (f : X ⟶ Y) : (pullback f).Braided where
  braided M N := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback f) M N), Functor.Monoidal.δ_μ_assoc,
      ← Category.assoc, ← pullback_map_braiding_hom_comp_δ f M N, Category.assoc,
      Functor.Monoidal.δ_μ, Category.comp_id]

/-- The canonical congruence `pullbackCongr h` for module pullbacks along equal morphisms of schemes
is a monoidal natural isomorphism. -/
instance isMonoidal_pullbackCongr_hom {f f' : X ⟶ Y} (h : f = f') :
    NatTrans.IsMonoidal (pullbackCongr h).hom := by
  subst h
  have hrfl : pullbackCongr (rfl : f = f) = Iso.refl (pullback f) := by
    simp [pullbackCongr]
  rw [hrfl]
  exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 (pullback f)))

/-- Arbitrary scheme-module pullback preserves left dualizability without quasi-coherence
assumptions. -/
theorem nonempty_hasLeftDual_pullback (f : X ⟶ Y) (M : Y.Modules)
    (hM : Nonempty (HasLeftDual M)) : Nonempty (HasLeftDual ((pullback f).obj M)) := by
  obtain ⟨hM⟩ := hM
  exact ⟨(pullback f).mapHasLeftDual M⟩

/-- Arbitrary scheme-module pullback preserves right dualizability without quasi-coherence
assumptions. -/
theorem nonempty_hasRightDual_pullback (f : X ⟶ Y) (M : Y.Modules)
    (hM : Nonempty (HasRightDual M)) : Nonempty (HasRightDual ((pullback f).obj M)) := by
  obtain ⟨hM⟩ := hM
  exact ⟨(pullback f).mapHasRightDual M⟩

end Morphism

/-- The canonical identity comparison `pullbackId X` for module pullback on a scheme is a monoidal
natural isomorphism. -/
instance isMonoidal_pullbackId_hom (X : Scheme.{u}) :
    NatTrans.IsMonoidal (pullbackId X).hom where
  unit := by
    rw [pullback_ε, ← pullbackObjUnitIso_id X, Iso.inv_hom_id, Functor.LaxMonoidal.id_ε]
  tensor M N := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback (𝟙 X)) M N),
      Functor.Monoidal.δ_μ_assoc, ← pullback_id_δ X M N, Functor.LaxMonoidal.id_μ,
      Category.comp_id]

/-- The canonical composition comparison `pullbackComp f g` for module pullbacks along composable
morphisms of schemes is a monoidal natural isomorphism. -/
instance isMonoidal_pullbackComp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (pullbackComp f g).hom where
  unit := by
    rw [Functor.LaxMonoidal.comp_ε, Category.assoc, pullback_ε, pullback_ε, pullback_ε,
      pullbackObjUnitIso_inv_comp]
  tensor M N := by
    rw [Functor.LaxMonoidal.comp_μ, Category.assoc, pullback_μ, pullback_μ, pullback_μ]
    exact inv_δ_comp_pullbackComp_hom_app f g M N

end AlgebraicGeometry.Scheme.Modules

end
