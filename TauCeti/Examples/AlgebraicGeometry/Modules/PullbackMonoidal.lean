/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Composition
import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Identity
import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Modules
import TauCeti.AlgebraicGeometry.Modules.Pullback.Stalk

/-!
# Examples for pullback stalks and strong symmetric monoidal module pullback

These examples exercise the stalk formula `(f^* M)_x ≅ 𝒪_{X, x} ⊗_{𝒪_{Y, f(x)}} M_{f(x)}` and the
unconditional strong symmetric monoidal structure on `Scheme.Modules.pullback f` in concrete,
non-flat, non-quasicoherent settings, while simultaneously importing the `QuasicoherentSheaf`
monoidal pullback modules to verify that both monoidal structures coexist without instance diamonds.
-/

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Placing the local ring `𝒪_{Spec ℤ, (2)}` as a skyscraper module sheaf at `(2)` gives a sheaf of
`𝒪_{Spec ℤ}`-modules whose global sections recover `𝒪_{Spec ℤ, (2)}`, and whose tensor square pulls
back isomorphically along the non-flat morphism `Spec (ℤ/4ℤ) ⟶ Spec ℤ` without any quasi-coherence
hypothesis. -/
example :
    let Y := Spec (CommRingCat.of ℤ)
    let f : Spec (CommRingCat.of (ZMod 4)) ⟶ Y :=
      Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 4)))
    let p : Y := (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 2)))).base default
    let M₀ := ModuleCat.of ↑(Y.presheaf.stalk p) ↑(Y.presheaf.stalk p)
    let S : Y.Modules := (SheafOfModules.skyscraper Y.sheaf p).obj M₀
    Nonempty (Γ(S, ⊤) ≃+ M₀) ∧
      Nonempty ((pullback f).obj (S ⊗ S) ≅ (pullback f).obj S ⊗ (pullback f).obj S) := by
  intro Y f p M₀ S
  exact ⟨⟨SheafOfModules.skyscraperSectionsEquiv Y.sheaf p M₀ (U := ⊤) trivial⟩,
    ⟨pullbackTensorIso f S S⟩⟩

/-- Over the non-flat morphism `Spec (ℤ/4ℤ) ⟶ Spec ℤ`, the stalk of any pulled-back `𝒪_{Spec ℤ}`-
module `M` at any point `x` is naturally isomorphic to the scalar extension of `M_{f(x)}` along
`f.stalkMap x`, and sends `s ⊗ m_{f(x)}` to `s` times the pulled-back germ of `m`. -/
example (M : (Spec (CommRingCat.of ℤ)).Modules) (x : Spec (CommRingCat.of (ZMod 4)))
    (s : ↑((Spec (CommRingCat.of (ZMod 4))).presheaf.stalk x)) (m : Γ(M, ⊤)) :
    let f : Spec (CommRingCat.of (ZMod 4)) ⟶ Spec (CommRingCat.of ℤ) :=
      Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 4)))
    (pullbackStalkIso f x).hom.app M
        (s ⊗ₜ[_, (f.stalkMap x).hom] M.presheaf.germ ⊤ (f x) trivial m) =
      s • ((pullback f).obj M).presheaf.germ (f ⁻¹ᵁ ⊤) x trivial
        (((pullbackPushforwardAdjunction f).unit.app M).app ⊤ m) := by
  intro f
  exact pullbackStalkIso_hom_app_tmul_germ f M x s ⊤ trivial m

/-- Equipping `𝒪_{X, x}` with the `𝒪_{Y, f(x)}`-algebra structure of `f.stalkMap x`, the canonical
germ map `pullbackStalkBaseMap` satisfies `IsBaseChange` for every `𝒪_Y`-module `M`. -/
example {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) (x : X) :
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Module ↑(Y.presheaf.stalk (f x)) ↑(((pullback f).obj M).presheaf.stalk x) :=
      Module.compHom _ (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))
    letI : IsScalarTower ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x)
        ↑(((pullback f).obj M).presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange ↑(X.presheaf.stalk x) (pullbackStalkBaseMap f M x rfl) := by
  let : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Module ↑(Y.presheaf.stalk (f x)) ↑(((pullback f).obj M).presheaf.stalk x) :=
    Module.compHom _ (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))
  let : IsScalarTower ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x)
      ↑(((pullback f).obj M).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact isBaseChange_pullbackStalkBaseMap f M x rfl

/-- Because `pullback f` is strong monoidal on all `Y.Modules`, Mathlib's `Functor.Monoidal`
supplies the natural isomorphism `tensorLeft M ⋙ pullback f ≅ pullback f ⋙ tensorLeft (f^* M)` for
an arbitrary (not necessarily quasi-coherent) module `M`. -/
example {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) :
    Nonempty (tensorLeft M ⋙ pullback f ≅ pullback f ⋙ tensorLeft ((pullback f).obj M)) :=
  ⟨(Functor.Monoidal.commTensorLeft (pullback f) M).symm⟩

/-- Along the two-step non-flat tower `Spec (ℤ/2ℤ) ⟶ Spec (ℤ/4ℤ) ⟶ Spec ℤ`, the composition
comparison `pullbackComp` commutes with the strong monoidal tensorators on arbitrary modules. -/
example (M N : (Spec (CommRingCat.of ℤ)).Modules) :
    let g : Spec (CommRingCat.of (ZMod 4)) ⟶ Spec (CommRingCat.of ℤ) :=
      Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 4)))
    let f : Spec (CommRingCat.of (ZMod 2)) ⟶ Spec (CommRingCat.of (ZMod 4)) :=
      Spec.map (CommRingCat.ofHom (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)))
    Functor.LaxMonoidal.μ (pullback g ⋙ pullback f) M N ≫
        (pullbackComp f g).hom.app (M ⊗ N) =
      ((pullbackComp f g).hom.app M ⊗ₘ (pullbackComp f g).hom.app N) ≫
        Functor.LaxMonoidal.μ (pullback (f ≫ g)) M N := by
  intro g f
  exact NatTrans.IsMonoidal.tensor (τ := (pullbackComp f g).hom) M N

/-- Both `(Scheme.Modules.pullback f).Braided` and `(QuasicoherentSheaf.pullback f).Braided`
coexist without instance diamonds, and `Scheme.Modules.pullback f` transports right duals of
arbitrary dualizable modules via `Functor.mapRightDualIso`. -/
example {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) [HasRightDual M]
    (E F : TauCeti.AlgebraicGeometry.QuasicoherentSheaf Y) :
    letI : HasRightDual ((pullback f).obj M) := (pullback f).mapHasRightDual M
    Nonempty ((pullback f).obj (Mᘁ) ≅ ((pullback f).obj M)ᘁ) ∧
      (Functor.LaxMonoidal.μ (TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pullback f) E F ≫
        (TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pullback f).map (β_ E F).hom =
        (β_ _ _).hom ≫
          Functor.LaxMonoidal.μ (TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pullback f) F E) := by
  let : HasRightDual ((pullback f).obj M) := (pullback f).mapHasRightDual M
  exact ⟨⟨(pullback f).mapRightDualIso M⟩,
    Functor.LaxBraided.braided (F := TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pullback f) E F⟩

end

end AlgebraicGeometry.Scheme.Modules
