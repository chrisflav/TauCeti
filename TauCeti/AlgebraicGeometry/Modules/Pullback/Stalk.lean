/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Stalk
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Stalk

/-!
# Stalks of a pulled-back module over a scheme

For a morphism of schemes `f : X ⟶ Y` and a point `x : X`, the general ringed-space ring stalk
homomorphism `SheafOfModules.ringStalkHom f.toRingCatSheafHom x` coincides with `f.stalkMap x`
(`Scheme.Modules.ringStalkHom_toRingCatSheafHom`). Specializing `SheafOfModules.pullbackStalkIso`
yields a natural isomorphism `(f^* M)_x ≅ 𝒪_{X, x} ⊗_{𝒪_{Y, f(x)}} M_{f(x)}` of `𝒪_{X, x}`-modules
for every `𝒪_Y`-module `M`, with no finiteness or quasi-coherence assumptions
(`Scheme.Modules.pullbackStalkIso`, `Scheme.Modules.pullbackStalkEquiv`,
`Scheme.Modules.isBaseChange_pullbackStalkBaseMap`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.stalkFunctor`: the stalk at `x : X` as a functor
  `X.Modules ⥤ ModuleCat ↑(X.presheaf.stalk x)`.
* `AlgebraicGeometry.Scheme.Modules.ringStalkHom_toRingCatSheafHom`: identifies
  `SheafOfModules.ringStalkHom f.toRingCatSheafHom x` with `f.stalkMap x`.
* `AlgebraicGeometry.Scheme.Modules.pullbackStalkIso`: natural isomorphism
  `stalkFunctor Y (f x) ⋙ extendScalars (f.stalkMap x).hom ≅ pullback f ⋙ stalkFunctor X x`.
* `AlgebraicGeometry.Scheme.Modules.pullbackStalkEquiv` and
  `AlgebraicGeometry.Scheme.Modules.isBaseChange_pullbackStalkBaseMap`: the `𝒪_{X, x}`-linear
  equivalence `𝒪_{X, x} ⊗[𝒪_{Y, f(x)}] M_{f(x)} ≃ₗ[𝒪_{X, x}] (f^* M)_x` and its `IsBaseChange`
  characterization.

## References

* [The Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098).
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 5.2(b).
-/

public section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The stalk at `x : X` of `𝒪_X`-modules, bundled as a functor to `𝒪_{X, x}`-modules. -/
-- Its object part presents the stalk carrier over `X.presheaf.stalk x` in germ formulas.
@[expose] def stalkFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat.{u} ↑(X.presheaf.stalk x) where
  obj M := ModuleCat.of ↑(X.presheaf.stalk x) ↑(M.presheaf.stalk x)
  map φ := ModuleCat.ofHom (PresheafOfModules.stalkMapCommRing (S := X.presheaf) x φ.val)
  map_id M := (SheafOfModules.stalkFunctor X.sheaf x).map_id M
  map_comp φ ψ := (SheafOfModules.stalkFunctor X.sheaf x).map_comp φ ψ

/-- On germs, `Scheme.Modules.stalkFunctor` applies the section map of a module morphism. -/
@[simp]
theorem stalkFunctor_map_germ {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) :
    (stalkFunctor X x).map φ (M.presheaf.germ U x hx m) =
      N.presheaf.germ U x hx (φ.app U m) :=
  PresheafOfModules.stalkMapCommRing_germ (S := X.presheaf) x φ.val U hx m

private def extendScalarsCongrIso {R₀ S₀ : Type u} [CommRing R₀] [CommRing S₀]
    {ρ₁ ρ₂ : R₀ →+* S₀} (h : ρ₁ = ρ₂) :
    ModuleCat.extendScalars.{u} ρ₁ ≅ ModuleCat.extendScalars.{u} ρ₂ :=
  eqToIso (congrArg ModuleCat.extendScalars h)

private theorem extendScalarsCongrIso_hom_app_tmul {R₀ S₀ : Type u} [CommRing R₀] [CommRing S₀]
    {ρ₁ ρ₂ : R₀ →+* S₀} (h : ρ₁ = ρ₂) (M₀ : ModuleCat.{u} R₀) (s : S₀) (m : M₀) :
    ((extendScalarsCongrIso h).hom.app M₀) (s ⊗ₜ[R₀, ρ₁] m) = s ⊗ₜ[R₀, ρ₂] m := by
  subst h
  rfl

variable {X Y : Scheme.{u}}

/-- For a morphism of schemes `f : X ⟶ Y`, the ring stalk homomorphism induced by
`f.toRingCatSheafHom` at `x : X` is `f.stalkMap x`. -/
@[simp]
theorem ringStalkHom_toRingCatSheafHom (f : X ⟶ Y) (x : X) :
    SheafOfModules.ringStalkHom f.toRingCatSheafHom x = f.stalkMap x := by
  refine Y.presheaf.stalk_hom_ext fun U hx ↦ ?_
  refine (SheafOfModules.germ_comp_ringStalkHom f.toRingCatSheafHom x U hx).trans ?_
  exact (congrArg (· ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hx) (by ext r; rfl)).trans
    (f.germ_stalkMap U x hx).symm

/-- **Stalk of a pulled-back `𝒪_Y`-module.** For any morphism of schemes `f : X ⟶ Y` and point
`x : X`, taking the stalk at `x` after pulling back along `f` is naturally isomorphic to taking the
stalk at `f(x)` and extending scalars along `(f.stalkMap x).hom : 𝒪_{Y, f(x)} →+* 𝒪_{X, x}`. -/
def pullbackStalkIso (f : X ⟶ Y) (x : X) :
    stalkFunctor Y (f x) ⋙ ModuleCat.extendScalars (f.stalkMap x).hom ≅
      pullback f ⋙ stalkFunctor X x :=
  Functor.isoWhiskerLeft (stalkFunctor Y (f x))
      (extendScalarsCongrIso
        (congrArg CommRingCat.Hom.hom (ringStalkHom_toRingCatSheafHom f x).symm)) ≪≫
    SheafOfModules.pullbackStalkIso f.toRingCatSheafHom x

/-- On `s ⊗ m_{f(x)}`, the forward component of `pullbackStalkIso` multiplies the pulled-back germ
of `m` at `x` by `s`. -/
@[simp]
theorem pullbackStalkIso_hom_app_tmul_germ (f : X ⟶ Y) (M : Y.Modules) (x : X)
    (s : ↑(X.presheaf.stalk x)) (U : Y.Opens) (hx : f x ∈ U) (m : Γ(M, U)) :
    dsimp% only [Functor.comp_obj]
    ((pullbackStalkIso f x).hom.app M
        (s ⊗ₜ[↑(Y.presheaf.stalk (f x)), (f.stalkMap x).hom] M.presheaf.germ U (f x) hx m) =
      s • ((pullback f).obj M).presheaf.germ (f ⁻¹ᵁ U) x hx
        (((pullbackPushforwardAdjunction f).unit.app M).app U m)) := by
  have h₁ : (pullbackStalkIso f x).hom.app M
      (s ⊗ₜ[↑(Y.presheaf.stalk (f x)), (f.stalkMap x).hom] M.presheaf.germ U (f x) hx m) =
      (SheafOfModules.pullbackStalkIso f.toRingCatSheafHom x).hom.app M
        (((extendScalarsCongrIso (congrArg CommRingCat.Hom.hom
          (ringStalkHom_toRingCatSheafHom f x).symm)).hom.app
            ((stalkFunctor Y (f x)).obj M))
          (s ⊗ₜ[↑(Y.presheaf.stalk (f x)), (f.stalkMap x).hom]
            M.presheaf.germ U (f x) hx m)) := by
    unfold pullbackStalkIso
    rfl
  exact h₁.trans ((congrArg ((SheafOfModules.pullbackStalkIso f.toRingCatSheafHom x).hom.app M)
    (extendScalarsCongrIso_hom_app_tmul _ _ s _)).trans
    (SheafOfModules.pullbackStalkIso_hom_app_tmul_germ f.toRingCatSheafHom M x s U hx m))

/-- On `1 ⊗ m_{f(x)}`, the forward component of `pullbackStalkIso` produces the germ at `x` of the
image of `m` under the pullback--pushforward unit. -/
theorem pullbackStalkIso_hom_app_one_tmul_germ (f : X ⟶ Y) (M : Y.Modules) (x : X)
    (U : Y.Opens) (hx : f x ∈ U) (m : Γ(M, U)) :
    (pullbackStalkIso f x).hom.app M
        ((1 : ↑(X.presheaf.stalk x)) ⊗ₜ[↑(Y.presheaf.stalk (f x)), (f.stalkMap x).hom]
          M.presheaf.germ U (f x) hx m) =
      ((pullback f).obj M).presheaf.germ (f ⁻¹ᵁ U) x hx
        (((pullbackPushforwardAdjunction f).unit.app M).app U m) :=
  (pullbackStalkIso_hom_app_tmul_germ f M x 1 U hx m).trans (one_smul _ _)

section Algebra

/-- When `𝒪_{X, x}` carries an `𝒪_{Y, f(x)}`-algebra structure induced by `f.stalkMap x`, the stalk
`(f^* M)_x` is `𝒪_{X, x}`-linearly equivalent to `𝒪_{X, x} ⊗[𝒪_{Y, f(x)}] M_{f(x)}`. -/
def pullbackStalkEquiv (f : X ⟶ Y) (M : Y.Modules) (x : X)
    [Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x)]
    (halg : algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) =
      (f.stalkMap x).hom := by rfl) :
    ↑(X.presheaf.stalk x) ⊗[↑(Y.presheaf.stalk (f x))] ↑(M.presheaf.stalk (f x)) ≃ₗ[
      ↑(X.presheaf.stalk x)] ↑(((pullback f).obj M).presheaf.stalk x) :=
  ((ModuleCat.extendScalarsAlgebraMapIso ((stalkFunctor Y (f x)).obj M)).symm ≪≫
    (extendScalarsCongrIso halg).app ((stalkFunctor Y (f x)).obj M) ≪≫
    (pullbackStalkIso f x).app M).toLinearEquiv

/-- `pullbackStalkEquiv` sends `s ⊗ m_{f(x)}` to `s` times the pulled-back germ of `m` at `x`. -/
@[simp]
theorem pullbackStalkEquiv_tmul_germ (f : X ⟶ Y) (M : Y.Modules) (x : X)
    [Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x)]
    (halg : algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) =
      (f.stalkMap x).hom := by rfl)
    (s : ↑(X.presheaf.stalk x)) (U : Y.Opens) (hx : f x ∈ U) (m : Γ(M, U)) :
    pullbackStalkEquiv f M x halg
        (s ⊗ₜ[↑(Y.presheaf.stalk (f x))] M.presheaf.germ U (f x) hx m) =
      s • ((pullback f).obj M).presheaf.germ (f ⁻¹ᵁ U) x hx
        (((pullbackPushforwardAdjunction f).unit.app M).app U m) := by
  let M₀ := (stalkFunctor Y (f x)).obj M
  let g : M₀ := M.presheaf.germ U (f x) hx m
  have h₁ : pullbackStalkEquiv f M x halg (s ⊗ₜ[↑(Y.presheaf.stalk (f x))] g) =
      (pullbackStalkIso f x).hom.app M
        (((extendScalarsCongrIso halg).hom.app M₀)
          ((ModuleCat.extendScalarsAlgebraMapIso M₀).inv (s ⊗ₜ g))) := by
    unfold pullbackStalkEquiv
    rfl
  exact h₁.trans ((congrArg (fun z ↦ (pullbackStalkIso f x).hom.app M
      (((extendScalarsCongrIso halg).hom.app M₀) z))
    (ModuleCat.extendScalarsAlgebraMapIso_inv_tmul M₀ s g)).trans
    ((congrArg ((pullbackStalkIso f x).hom.app M)
      (extendScalarsCongrIso_hom_app_tmul halg M₀ s g)).trans
      (pullbackStalkIso_hom_app_tmul_germ f M x s U hx m)))

/-- The canonical `𝒪_{Y, f(x)}`-linear map `M_{f(x)} →ₗ[𝒪_{Y, f(x)}] (f^* M)_x` sending the germ of
a section `m` at `f(x)` to the germ of its unit image at `x`. -/
def pullbackStalkBaseMap (f : X ⟶ Y) (M : Y.Modules) (x : X)
    [Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x)]
    [Module ↑(Y.presheaf.stalk (f x)) ↑(((pullback f).obj M).presheaf.stalk x)]
    [IsScalarTower ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x)
      ↑(((pullback f).obj M).presheaf.stalk x)]
    (halg : algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) =
      (f.stalkMap x).hom := by rfl) :
    ↑(M.presheaf.stalk (f x)) →ₗ[↑(Y.presheaf.stalk (f x))]
      ↑(((pullback f).obj M).presheaf.stalk x) :=
  ((pullbackStalkEquiv f M x halg).toLinearMap.restrictScalars
    ↑(Y.presheaf.stalk (f x))).comp
      (TensorProduct.mk ↑(Y.presheaf.stalk (f x))
        ↑(X.presheaf.stalk x) ↑(M.presheaf.stalk (f x)) 1)

/-- `pullbackStalkBaseMap` sends the germ of `m ∈ Γ(M, U)` at `f(x)` to the germ at `x` of its image
under the pullback--pushforward unit. -/
@[simp]
theorem pullbackStalkBaseMap_germ (f : X ⟶ Y) (M : Y.Modules) (x : X)
    [Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x)]
    [Module ↑(Y.presheaf.stalk (f x)) ↑(((pullback f).obj M).presheaf.stalk x)]
    [IsScalarTower ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x)
      ↑(((pullback f).obj M).presheaf.stalk x)]
    (halg : algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) =
      (f.stalkMap x).hom := by rfl)
    (U : Y.Opens) (hx : f x ∈ U) (m : Γ(M, U)) :
    pullbackStalkBaseMap f M x halg (M.presheaf.germ U (f x) hx m) =
      ((pullback f).obj M).presheaf.germ (f ⁻¹ᵁ U) x hx
        (((pullbackPushforwardAdjunction f).unit.app M).app U m) := by
  unfold pullbackStalkBaseMap
  exact (pullbackStalkEquiv_tmul_germ f M x halg 1 U hx m).trans (one_smul _ _)

/-- The canonical map `pullbackStalkBaseMap` exhibits `(f^* M)_x` as the base change of `M_{f(x)}`
along `𝒪_{Y, f(x)} → 𝒪_{X, x}`. -/
theorem isBaseChange_pullbackStalkBaseMap (f : X ⟶ Y) (M : Y.Modules) (x : X)
    [Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x)]
    [Module ↑(Y.presheaf.stalk (f x)) ↑(((pullback f).obj M).presheaf.stalk x)]
    [IsScalarTower ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x)
      ↑(((pullback f).obj M).presheaf.stalk x)]
    (halg : algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) =
      (f.stalkMap x).hom := by rfl) :
    IsBaseChange ↑(X.presheaf.stalk x) (pullbackStalkBaseMap f M x halg) := by
  refine IsBaseChange.of_equiv (pullbackStalkEquiv f M x halg) fun _ ↦ ?_
  unfold pullbackStalkBaseMap
  rfl

end Algebra

end AlgebraicGeometry.Scheme.Modules

end
