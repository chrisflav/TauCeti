/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Identity
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Stalk
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Pullback of sheaves of modules is strong symmetric monoidal

Let `f : Y ⟶ X` be a continuous map of topological spaces, `𝒪X` and `𝒪Y` sheaves of commutative
rings on `X` and `Y`, and `φ : 𝒪X ⟶ f_* 𝒪Y` a morphism of the underlying sheaves of rings for which
module pushforward has a left adjoint `SheafOfModules.pullback φ`.

This file proves that the canonical oplax tensor comparison
`δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` of `SheafOfModules.pullback φ` is an isomorphism for arbitrary
sheaves of `𝒪X`-modules `E` and `F`, with no flatness, finiteness, or quasi-coherence assumptions.
Combined with invertibility of the unit comparison `η : f^* 𝒪X ⟶ 𝒪Y` (since `Opens.map f` is final)
and compatibility with the braiding (`SheafOfModules.pullback_map_braiding_hom_comp_δ`), module
pullback is a strong braided (hence symmetric) monoidal functor.

At each point `y : Y`, both `(f^* (E ⊗ F))_y` and `(f^* E ⊗ f^* F)_y` are base changes of
`E_{f(y)} ⊗_{𝒪_{X, f(y)}} F_{f(y)}` along `ringStalkHom φ y : 𝒪_{X, f(y)} ⟶ 𝒪_{Y, y}`: the first
by `SheafOfModules.isBaseChange_pullbackStalkBaseMap` and `tensorObjStalkEquiv`, and the second by
`IsBaseChange.tensorProduct` and `tensorObjStalkEquiv`. On pure tensors of germs over a common open
neighborhood of `f(y)`, the stalk map of `δ` intertwines the two base-change maps, so it is
bijective by `IsBaseChange.bijective_of_comp_eq`; `isIso_of_bijective_stalkFunctor_map` concludes.

## Main declarations

* `TauCeti.SheafOfModules.tensorObjStalkEquiv`: the `R_x`-linear equivalence
  `(M ⊗ N)_x ≃ₗ[R_x] M_x ⊗[R_x] N_x` for the monoidal tensor product `M ⊗ N`.
* `TauCeti.SheafOfModules.isIso_pullback_η` and `TauCeti.SheafOfModules.isIso_pullback_δ`:
  invertibility of the unit and tensor comparisons of `SheafOfModules.pullback φ`.
* `SheafOfModules.pullbackTensorIso`: the canonical isomorphism `f^* (E ⊗ F) ≅ f^* E ⊗ f^* F`.
* `TauCeti.SheafOfModules.pullbackMonoidal` and `TauCeti.SheafOfModules.pullbackBraided`: the
  strong symmetric monoidal structure on `SheafOfModules.pullback φ`, with comparison formulas
  `pullback_μ` and `pullback_ε`.
* `TauCeti.SheafOfModules.isMonoidal_pullbackId_hom` and
  `TauCeti.SheafOfModules.isMonoidal_pullbackComp_hom`: monoidal coherence for identity and
  composite pullbacks.

## References

* [The Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) (pullback of tensor
  products of sheaves of modules).
-/

public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace TopCat.Presheaf
open scoped TensorProduct

namespace TauCeti.SheafOfModules

open _root_.SheafOfModules

universe u

noncomputable section

section TensorStalk

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (M N : _root_.SheafOfModules.{u} (ringCatSheaf R))

private theorem tensorUnderlyingIso_hom_app_forget_μ
    (U : Opens X) (x₀ : M.val.obj (op U) ⊗[R.obj.obj (op U)] N.val.obj (op U)) :
    ((M.tensorUnderlyingIso N).hom.val.app (op U))
      (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app (op U))
        x₀) =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        (M.val ⊗ N.val)).app (op U)) x₀ := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)
  let := adj.rightAdjointLaxMonoidal
  have hδ : Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj))
        M.val N.val ≫ (adj.counit.app M ⊗ₘ adj.counit.app N) =
      (M.tensorUnderlyingIso N).inv := by
    rw [← sheafificationIso_hom, ← sheafificationIso_hom]
    exact (_root_.SheafOfModules.tensorUnderlyingIso_inv (R := R) M N).symm
  have hμ := congrArg
    (fun k ↦ ((M.tensorUnderlyingIso N).hom.val.app (op U)) ((k.app (op U)).hom x₀))
    ((_root_.SheafOfModules.sheafificationAdjunction_μ_eq_forget_μ (R := R) M N).symm.trans
      (Adjunction.rightAdjointLaxMonoidal_μ adj M N))
  let y₀ := ((adj.unit.app (M.val ⊗ N.val)).app (op U)).hom x₀
  have hcancel : ((M.tensorUnderlyingIso N).hom.val.app (op U))
      (((Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj))
          M.val N.val ≫ (adj.counit.app M ⊗ₘ adj.counit.app N)).val.app (op U)) y₀) = y₀ :=
    congrArg (fun f ↦ (f.val.app (op U)).hom y₀)
      ((congrArg (· ≫ (M.tensorUnderlyingIso N).hom) hδ).trans
        (Iso.inv_hom_id (M.tensorUnderlyingIso N)))
  exact hμ.trans hcancel

variable (x : X)

/-- For the monoidal tensor product `M ⊗ N` of sheaves of `R`-modules, the stalk `(M ⊗ N)_x` is
`R_x`-linearly equivalent to `M_x ⊗[R_x] N_x`. -/
def tensorObjStalkEquiv :
    ↑(TopCat.Presheaf.stalk (M ⊗ N).val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk M.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk R.obj x)]
        ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
  (((_root_.SheafOfModules.stalkFunctor R x).mapIso
    (M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm)).toLinearEquiv).trans
    (tensorStalkEquiv R M N x)

/-- `tensorObjStalkEquiv` sends the germ of the image of `m ⊗ₜ n` under the lax tensor comparison of
`forget` to `m_x ⊗ₜ n_x`. -/
@[simp]
theorem tensorObjStalkEquiv_germ_μ_tmul (U : Opens X) (hx : x ∈ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, Functor.id_obj, Functor.comp_obj]
    (tensorObjStalkEquiv R M N x
        (TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
          ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app (op U)
            (m ⊗ₜ[R.obj.obj (op U)] n))) =
      TopCat.Presheaf.germ M.val.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R.obj x)]
        TopCat.Presheaf.germ N.val.presheaf U x hx n) := by
  let α : M ⊗ N ⟶ tensorProduct R M N :=
    (M.tensorUnderlyingIso N).hom ≫ (tensorProductIso R M N).inv
  have hα : α.val.app (op U)
      ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app (op U)
        (m ⊗ₜ[R.obj.obj (op U)] n)) =
      (tensorProductIso R M N).inv.val.app (op U)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
          (M.val ⊗ N.val)).app (op U) (m ⊗ₜ[R.obj.obj (op U)] n)) :=
    congrArg ((tensorProductIso R M N).inv.val.app (op U))
      (tensorUnderlyingIso_hom_app_forget_μ R M N U (m ⊗ₜ[R.obj.obj (op U)] n))
  have hdef : tensorObjStalkEquiv R M N x
      (TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
        ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app (op U)
          (m ⊗ₜ[R.obj.obj (op U)] n))) =
      tensorStalkComparison R M N x
        ((_root_.SheafOfModules.stalkFunctor R x).map α
          (TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
            ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app (op U)
              (m ⊗ₜ[R.obj.obj (op U)] n)))) := by
    unfold tensorObjStalkEquiv
    exact tensorStalkEquiv_apply R M N x _
  exact hdef.trans
    ((congrArg (tensorStalkComparison R M N x)
      ((_root_.SheafOfModules.stalkFunctor_map_germ R x α U hx _).trans
        (congrArg (TopCat.Presheaf.germ (tensorProduct R M N).val.presheaf U x hx) hα))).trans
      (tensorStalkComparison_germ_unit_tmul R M N x U hx m n))

/-- The inverse of `tensorObjStalkEquiv` sends `m_x ⊗ₜ n_x` to the germ of the image of `m ⊗ₜ n`
under the lax tensor comparison of `forget`. -/
@[simp]
theorem tensorObjStalkEquiv_symm_tmul_germ (U : Opens X) (hx : x ∈ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, Functor.id_obj, Functor.comp_obj]
    ((tensorObjStalkEquiv R M N x).symm
        (TopCat.Presheaf.germ M.val.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R.obj x)]
          TopCat.Presheaf.germ N.val.presheaf U x hx n) =
      TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
        ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app (op U)
          (m ⊗ₜ[R.obj.obj (op U)] n))) :=
  (tensorObjStalkEquiv R M N x).symm_apply_eq.mpr
    (tensorObjStalkEquiv_germ_μ_tmul R M N x U hx m n).symm

end TensorStalk

/-- Pure commutative-algebra comparison: if `bEF`, `bE`, `bF` are base changes along `R₀ → S₀` and
`d : M_EF →ₗ[S₀] T_EF` intertwines `bEF ∘ e₀.symm` with `bE ⊗ bF` through `e₁`, then `d` is
bijective. Abstracting over opaque module types avoids unfolding sheafification colimits during
kernel typechecking. -/
private theorem bijective_of_baseChange_comm
    {R₀ S₀ E₀ F₀ EF₀ M_EF M_E M_F T_EF : Type u}
    [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
    [AddCommGroup E₀] [Module R₀ E₀]
    [AddCommGroup F₀] [Module R₀ F₀]
    [AddCommGroup EF₀] [Module R₀ EF₀]
    [AddCommGroup M_EF] [Module R₀ M_EF] [Module S₀ M_EF] [IsScalarTower R₀ S₀ M_EF]
    [AddCommGroup M_E] [Module R₀ M_E] [Module S₀ M_E] [IsScalarTower R₀ S₀ M_E]
    [AddCommGroup M_F] [Module R₀ M_F] [Module S₀ M_F] [IsScalarTower R₀ S₀ M_F]
    [AddCommGroup T_EF] [Module S₀ T_EF]
    (e₀ : EF₀ ≃ₗ[R₀] E₀ ⊗[R₀] F₀)
    (e₁ : T_EF ≃ₗ[S₀] M_E ⊗[S₀] M_F)
    (bEF : EF₀ →ₗ[R₀] M_EF) (hbEF : IsBaseChange S₀ bEF)
    (bE : E₀ →ₗ[R₀] M_E) (hbE : IsBaseChange S₀ bE)
    (bF : F₀ →ₗ[R₀] M_F) (hbF : IsBaseChange S₀ bF)
    (d : M_EF →ₗ[S₀] T_EF)
    (hd : ∀ sE sF, e₁ (d (bEF (e₀.symm (sE ⊗ₜ[R₀] sF)))) = bE sE ⊗ₜ[S₀] bF sF) :
    Function.Bijective d := by
  let g₁ := bEF.comp e₀.symm.toLinearMap
  let g₂ := TensorProduct.mapOfCompatibleSMul S₀ R₀ R₀ M_E M_F ∘ₗ TensorProduct.map bE bF
  have hg₁ : IsBaseChange S₀ g₁ := IsBaseChange.comp_equiv e₀.symm bEF hbEF
  have hg₂ : IsBaseChange S₀ g₂ := IsBaseChange.tensorProduct hbE hbF
  let d' : M_EF →ₗ[S₀] M_E ⊗[S₀] M_F := e₁.toLinearMap.comp d
  have hcomm : (d'.restrictScalars R₀).comp g₁ = g₂ := by
    refine TensorProduct.ext' fun sE sF ↦ ?_
    exact (hd sE sF).trans
      ((congrArg (TensorProduct.mapOfCompatibleSMul S₀ R₀ R₀ M_E M_F)
        (TensorProduct.map_tmul bE bF sE sF)).trans
        (TensorProduct.mapOfCompatibleSMul_tmul S₀ R₀ R₀ M_E M_F (bE sE) (bF sF))).symm
  have hbij : Function.Bijective d' :=
    IsBaseChange.bijective_of_comp_eq hg₁ hg₂ d' fun z ↦ LinearMap.congr_fun hcomm z
  exact ⟨fun a b hab ↦ hbij.1 (congrArg e₁ hab), fun b ↦
    let ⟨a, ha⟩ := hbij.2 (e₁ b)
    ⟨a, e₁.injective ha⟩⟩

section Pullback

variable {X Y : TopCat.{u}} {f : Y ⟶ X}
  {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- For a continuous map `f : Y ⟶ X`, `Opens.map f` is final, so the oplax unit comparison
`η : f^* 𝒪X ⟶ 𝒪Y` of module pullback is an isomorphism. -/
instance isIso_pullback_η :
    IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} φ)) := by
  rw [pullback_η φ]
  exact _root_.SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal φ

/-- On sections over `U : Opens X`, the pullback--pushforward unit at `E ⊗ F` followed by the
pushforward of `δ (pullback φ) E F` sends the image of `m ⊗ₜ n` to the image of the pure tensor of
the unit images of `m` and `n` over `f ⁻¹' U`. -/
private theorem pullback_δ_val_app_unit_μ_tmul
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) (U : Opens X)
    (m : E.val.obj (op U)) (n : F.val.obj (op U)) :
    (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F).val.app
        (op ((Opens.map f).obj U))
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app (E ⊗ F)).val.app
          (op U)
          ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) E F).app (op U)
            (m ⊗ₜ[𝒪X.obj.obj (op U)] n))) =
      (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪Y))
          ((_root_.SheafOfModules.pullback.{u} φ).obj E)
          ((_root_.SheafOfModules.pullback.{u} φ).obj F)).app
        (op ((Opens.map f).obj U))
        ((((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app E).val.app
            (op U) m) ⊗ₜ[𝒪Y.obj.obj (op ((Opens.map f).obj U))]
          (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app F).val.app
            (op U) n)) := by
  let PE := (_root_.SheafOfModules.pullback.{u} φ).obj E
  let PF := (_root_.SheafOfModules.pullback.{u} φ).obj F
  let uE : E ⟶ (_root_.SheafOfModules.pushforward.{u} φ).obj PE :=
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app E
  let uF : F ⟶ (_root_.SheafOfModules.pushforward.{u} φ).obj PF :=
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app F
  let uEF : E ⊗ F ⟶
      (_root_.SheafOfModules.pushforward.{u} φ).obj
        ((_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F)) :=
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app (E ⊗ F)
  have hmate : uEF ≫ (_root_.SheafOfModules.pushforward.{u} φ).map
        (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) =
      (uE ⊗ₘ uF) ≫ Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward.{u} φ) PE PF :=
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).homEquiv_unit _ _ _).symm.trans
      ((congrArg ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).homEquiv _ _)
        (pullback_δ φ E F)).trans (Equiv.apply_symm_apply _ _))
  have hpre : Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) E F ≫
      (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)).map
        (uEF ≫ (_root_.SheafOfModules.pushforward.{u} φ).map
          (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F)) =
      (uE.val ⊗ₘ uF.val) ≫
        (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X))
          ((_root_.SheafOfModules.pushforward.{u} φ).obj PE)
          ((_root_.SheafOfModules.pushforward.{u} φ).obj PF) ≫
        (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)).map
          (Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward.{u} φ) PE PF)) :=
    (congrArg (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) E F ≫ ·)
      ((congrArg (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)).map hmate).trans
        ((_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)).map_comp _ _))).trans
      (Functor.LaxMonoidal.μ_natural_assoc
        (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) uE uF
        ((_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)).map
          (Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward.{u} φ) PE PF))).symm
  have heval := congrArg (fun p ↦ (p.app (op U)).hom (m ⊗ₜ[𝒪X.obj.obj (op U)] n)) hpre
  have hA : ((uE.val ⊗ₘ uF.val).app (op U)).hom (m ⊗ₜ[𝒪X.obj.obj (op U)] n) =
      (uE.val.app (op U) m) ⊗ₜ[𝒪X.obj.obj (op U)] (uF.val.app (op U) n) :=
    @ModuleCat.MonoidalCategory.tensorHom_tmul (𝒪X.obj.obj (op U)) _ _ _ _ _
      (uE.val.app (op U)) (uF.val.app (op U)) m n
  let g := ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X))
        ((_root_.SheafOfModules.pushforward.{u} φ).obj PE)
        ((_root_.SheafOfModules.pushforward.{u} φ).obj PF) ≫
      (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)).map
        (Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward.{u} φ) PE PF)).app (op U)).hom
  exact heval.trans ((congrArg g hA).trans
    (pushforward_μ_app_tmul φ PE PF (op U) (uE.val.app (op U) m) (uF.val.app (op U) n)))

/-- On pure tensors of stalk elements at `f y`, the stalk map of `δ (pullback φ) E F` followed by
`tensorObjStalkEquiv` intertwines the pullback stalk base-change maps. -/
private theorem stalkFunctor_map_pullback_δ_baseMap
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) (y : Y)
    [Algebra ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
    (hφ : algebraMap ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) =
      (_root_.SheafOfModules.ringStalkHom φ y).hom)
    [Module ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F)).val.presheaf y)]
    [IsScalarTower ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F)).val.presheaf y)]
    [Module ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj E).val.presheaf y)]
    [IsScalarTower ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj E).val.presheaf y)]
    [Module ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj F).val.presheaf y)]
    [IsScalarTower ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj F).val.presheaf y)]
    (sE : ↑(TopCat.Presheaf.stalk E.val.presheaf (f y)))
    (sF : ↑(TopCat.Presheaf.stalk F.val.presheaf (f y))) :
    tensorObjStalkEquiv 𝒪Y ((_root_.SheafOfModules.pullback.{u} φ).obj E)
        ((_root_.SheafOfModules.pullback.{u} φ).obj F) y
        ((_root_.SheafOfModules.stalkFunctor 𝒪Y y).map
          (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F)
          (_root_.SheafOfModules.pullbackStalkBaseMap φ (E ⊗ F) y hφ
            ((tensorObjStalkEquiv 𝒪X E F (f y)).symm
              (sE ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))] sF)))) =
      _root_.SheafOfModules.pullbackStalkBaseMap φ E y hφ sE ⊗ₜ[
        ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
        _root_.SheafOfModules.pullbackStalkBaseMap φ F y hφ sF := by
  obtain ⟨U₁, hy₁, m₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq E.val.presheaf sE
  obtain ⟨U₂, hy₂, n₂, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf sF
  let U : Opens X := U₁ ⊓ U₂
  have hy : f y ∈ U := ⟨hy₁, hy₂⟩
  let i₁ : U ⟶ U₁ := homOfLE inf_le_left
  let i₂ : U ⟶ U₂ := homOfLE inf_le_right
  let m : E.val.obj (op U) := E.val.map i₁.op m₁
  let n : F.val.obj (op U) := F.val.map i₂.op n₂
  let PE := (_root_.SheafOfModules.pullback.{u} φ).obj E
  let PF := (_root_.SheafOfModules.pullback.{u} φ).obj F
  let PEF := (_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F)
  let δEF := Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F
  let sEF : (E ⊗ F).val.obj (op U) :=
    (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) E F).app (op U)
      (m ⊗ₜ[𝒪X.obj.obj (op U)] n)
  let uEF_s : PEF.val.obj (op ((Opens.map f).obj U)) :=
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app (E ⊗ F)).val.app
      (op U) sEF
  let uE_m : PE.val.obj (op ((Opens.map f).obj U)) :=
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app E).val.app (op U) m
  let uF_n : PF.val.obj (op ((Opens.map f).obj U)) :=
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app F).val.app (op U) n
  have hresE := (TopCat.Presheaf.germ_res_apply E.val.presheaf i₁ (f y) hy m₁).symm
  have hresF := (TopCat.Presheaf.germ_res_apply F.val.presheaf i₂ (f y) hy n₂).symm
  have hL₀ := congrArg (fun z ↦ tensorObjStalkEquiv 𝒪Y PE PF y
    ((_root_.SheafOfModules.stalkFunctor 𝒪Y y).map δEF
      (_root_.SheafOfModules.pullbackStalkBaseMap φ (E ⊗ F) y hφ
        ((tensorObjStalkEquiv 𝒪X E F (f y)).symm z))))
    (congrArg₂ (· ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))] ·) hresE hresF)
  have hL₁ := congrArg (fun z ↦ tensorObjStalkEquiv 𝒪Y PE PF y
    ((_root_.SheafOfModules.stalkFunctor 𝒪Y y).map δEF
      (_root_.SheafOfModules.pullbackStalkBaseMap φ (E ⊗ F) y hφ z)))
    (tensorObjStalkEquiv_symm_tmul_germ 𝒪X E F (f y) U hy m n)
  have hL₂ := congrArg (fun z ↦ tensorObjStalkEquiv 𝒪Y PE PF y
    ((_root_.SheafOfModules.stalkFunctor 𝒪Y y).map δEF z))
    (_root_.SheafOfModules.pullbackStalkBaseMap_germ φ (E ⊗ F) y hφ U hy sEF)
  have hL₃ := congrArg (tensorObjStalkEquiv 𝒪Y PE PF y)
    ((_root_.SheafOfModules.stalkFunctor_map_germ 𝒪Y y δEF ((Opens.map f).obj U) hy uEF_s).trans
      (congrArg (TopCat.Presheaf.germ (PE ⊗ PF).val.presheaf ((Opens.map f).obj U) y hy)
        (pullback_δ_val_app_unit_μ_tmul φ E F U m n)))
  have hL₄ := tensorObjStalkEquiv_germ_μ_tmul 𝒪Y PE PF y ((Opens.map f).obj U) hy uE_m uF_n
  have hR := congrArg₂ (· ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)] ·)
    ((congrArg (_root_.SheafOfModules.pullbackStalkBaseMap φ E y hφ) hresE).trans
      (_root_.SheafOfModules.pullbackStalkBaseMap_germ φ E y hφ U hy m))
    ((congrArg (_root_.SheafOfModules.pullbackStalkBaseMap φ F y hφ) hresF).trans
      (_root_.SheafOfModules.pullbackStalkBaseMap_germ φ F y hφ U hy n))
  exact hL₀.trans (hL₁.trans (hL₂.trans (hL₃.trans (hL₄.trans hR.symm))))

private theorem bijective_stalkFunctor_map_pullback_δ
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) (y : Y) :
    Function.Bijective
      ((_root_.SheafOfModules.stalkFunctor 𝒪Y y).map
        (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F)) := by
  let R₀ := ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))
  let S₀ := ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
  let : Algebra R₀ S₀ := (_root_.SheafOfModules.ringStalkHom φ y).hom.toAlgebra
  let M_EF :=
    ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F)).val.presheaf y)
  let M_E := ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj E).val.presheaf y)
  let M_F := ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj F).val.presheaf y)
  let : Module R₀ M_EF := Module.compHom M_EF (algebraMap R₀ S₀)
  let : IsScalarTower R₀ S₀ M_EF := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module R₀ M_E := Module.compHom M_E (algebraMap R₀ S₀)
  let : IsScalarTower R₀ S₀ M_E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module R₀ M_F := Module.compHom M_F (algebraMap R₀ S₀)
  let : IsScalarTower R₀ S₀ M_F := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact bijective_of_baseChange_comm
    (tensorObjStalkEquiv 𝒪X E F (f y))
    (tensorObjStalkEquiv 𝒪Y ((_root_.SheafOfModules.pullback.{u} φ).obj E)
      ((_root_.SheafOfModules.pullback.{u} φ).obj F) y)
    (_root_.SheafOfModules.pullbackStalkBaseMap φ (E ⊗ F) y rfl)
    (_root_.SheafOfModules.isBaseChange_pullbackStalkBaseMap φ (E ⊗ F) y rfl)
    (_root_.SheafOfModules.pullbackStalkBaseMap φ E y rfl)
    (_root_.SheafOfModules.isBaseChange_pullbackStalkBaseMap φ E y rfl)
    (_root_.SheafOfModules.pullbackStalkBaseMap φ F y rfl)
    (_root_.SheafOfModules.isBaseChange_pullbackStalkBaseMap φ F y rfl)
    ((_root_.SheafOfModules.stalkFunctor 𝒪Y y).map
      (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F)).hom
    (stalkFunctor_map_pullback_δ_baseMap φ E F y rfl)

/-- **Pullback of tensor products of sheaves of modules.** For any morphism of ringed spaces
`(f, φ)` whose module pushforward has a left adjoint, and any two sheaves of `𝒪X`-modules `E` and
`F`, the oplax tensor comparison `δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` is an isomorphism, with no
flatness, finiteness, or quasi-coherence assumptions. -/
instance isIso_pullback_δ (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) :=
  _root_.SheafOfModules.isIso_of_bijective_stalkFunctor_map _
    (bijective_stalkFunctor_map_pullback_δ φ E F)

/-- The canonical isomorphism `f^* (E ⊗ F) ≅ f^* E ⊗ f^* F` for arbitrary sheaves of modules along
a morphism of ringed spaces. -/
def _root_.SheafOfModules.pullbackTensorIso
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    (_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F) ≅
      (_root_.SheafOfModules.pullback.{u} φ).obj E ⊗
        (_root_.SheafOfModules.pullback.{u} φ).obj F :=
  asIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F)

/-- The forward morphism of `pullbackTensorIso` is the oplax tensor comparison `δ`. -/
@[simp]
theorem _root_.SheafOfModules.pullbackTensorIso_hom
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    (_root_.SheafOfModules.pullbackTensorIso φ E F).hom =
      Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F := by
  unfold _root_.SheafOfModules.pullbackTensorIso
  rfl

/-- Module pullback along any morphism of ringed spaces is a strong monoidal functor. -/
instance pullbackMonoidal : (_root_.SheafOfModules.pullback.{u} φ).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} φ)

/-- The inverse morphism of `pullbackTensorIso` is the lax tensor comparison `μ`. -/
@[simp]
theorem _root_.SheafOfModules.pullbackTensorIso_inv
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    (_root_.SheafOfModules.pullbackTensorIso φ E F).inv =
      Functor.LaxMonoidal.μ (_root_.SheafOfModules.pullback.{u} φ) E F := by
  unfold _root_.SheafOfModules.pullbackTensorIso
  exact Functor.Monoidal.inv_δ (_root_.SheafOfModules.pullback.{u} φ) E F

/-- The lax tensor comparison `μ` of strong monoidal module pullback is the inverse of `δ`. -/
theorem pullback_μ (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.pullback.{u} φ) E F =
      inv (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) :=
  IsIso.eq_inv_of_hom_inv_id (Functor.Monoidal.δ_μ (_root_.SheafOfModules.pullback.{u} φ) E F)

/-- The lax unit comparison `ε` of strong monoidal module pullback is the inverse of
`pullbackObjUnitToUnit φ`. -/
@[simp]
theorem pullback_ε :
    Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} φ) =
      inv (_root_.SheafOfModules.pullbackObjUnitToUnit φ) := by
  have h : Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} φ) ≫
      _root_.SheafOfModules.pullbackObjUnitToUnit φ = 𝟙 _ :=
    (congrArg (Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} φ) ≫ ·)
      (pullback_η φ).symm).trans (Functor.Monoidal.ε_η (_root_.SheafOfModules.pullback.{u} φ))
  exact IsIso.eq_inv_of_inv_hom_id h

/-- Module pullback along any morphism of ringed spaces is a braided (hence symmetric) strong
monoidal functor. -/
instance pullbackBraided : (_root_.SheafOfModules.pullback.{u} φ).Braided where
  braided E F := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F),
      Functor.Monoidal.δ_μ_assoc, ← Category.assoc, ← pullback_map_braiding_hom_comp_δ φ E F,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]

end Pullback

section Coherence

/-- On any small ringed site, the oplax unit comparison for identity pullback is invertible. -/
instance isIso_pullback_id_η {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    letI := pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
    IsIso (Functor.OplaxMonoidal.η
      (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
        (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))) := by
  let := pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  rw [pullback_id_η R]
  infer_instance

/-- On any small ringed site, the oplax tensor comparison for identity pullback is invertible. -/
instance isIso_pullback_id_δ {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    letI := pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
    IsIso (Functor.OplaxMonoidal.δ
      (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
        (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) M N) := by
  let := pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  have h := pullback_id_δ R M N
  have : IsIso (Functor.OplaxMonoidal.δ
      (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
        (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) M N ≫
      ((_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app M ⊗ₘ
        (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app N)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (Functor.OplaxMonoidal.δ
      (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
        (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) M N)
    ((_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app M ⊗ₘ
      (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app N)

/-- On any small ringed site, the canonical identity comparison `pullbackId` for module pullback
is a monoidal natural transformation with respect to the strong monoidal structure induced from
`pullbackOplaxMonoidal`. -/
theorem isMonoidal_pullbackId_hom {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    letI := pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
    letI := Functor.Monoidal.ofOplaxMonoidal
      (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
        (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (_root_.SheafOfModules.pullbackId.{u} (ringCatSheaf R)).hom
      inferInstance
      Functor.LaxMonoidal.id := by
  let := pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  let := Functor.Monoidal.ofOplaxMonoidal
    (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
      (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
  refine { unit := ?_, tensor := fun M N ↦ ?_ }
  · rw [← pullback_id_η R]
    exact Functor.Monoidal.ε_η _
  · refine (cancel_epi (Functor.OplaxMonoidal.δ
      (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
        (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) M N)).mp ?_
    exact (Functor.Monoidal.δ_μ_assoc _ M N _).trans
      ((pullback_id_δ R M N).symm.trans (by rw [Functor.LaxMonoidal.id_μ, Category.comp_id]))

section Comp

variable {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [L.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} {G : D ⥤ E} [F.IsContinuous J K] [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L]
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}} {T : Sheaf L CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj (ringCatSheaf T))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{u} ψ).IsRightAdjoint]

/-- When two composable module pullbacks on ringed sites have invertible oplax unit comparisons, so
does the pullback along their composite. -/
instance isIso_pullback_comp_η
    [IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} φ))]
    [IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} ψ))] :
    IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} (F := F ⋙ G)
      (R := ringCatSheaf T) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))) := by
  rw [pullback_comp_η φ ψ]
  infer_instance

/-- When two composable module pullbacks on ringed sites have invertible oplax tensor comparisons,
so does the pullback along their composite. -/
instance isIso_pullback_comp_δ
    [∀ M N, IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) M N)]
    [∀ M N, IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} ψ) M N)]
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} (F := F ⋙ G)
      (R := ringCatSheaf T) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) M N) := by
  rw [pullback_comp_δ φ ψ M N]
  infer_instance

/-- Whenever two composable module pullbacks on ringed sites have invertible oplax unit and tensor
comparisons, the canonical composition comparison `pullbackComp φ ψ` is a monoidal natural
transformation. -/
theorem isMonoidal_pullbackComp_hom
    [IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} φ))]
    [IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} ψ))]
    [∀ M N, IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) M N)]
    [∀ M N, IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} ψ) M N)] :
    letI := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} φ)
    letI := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} ψ)
    letI := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} (F := F ⋙ G)
      (R := ringCatSheaf T) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
    NatTrans.IsMonoidal (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom := by
  let := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} φ)
  let := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} ψ)
  let := Functor.Monoidal.ofOplaxMonoidal
    (_root_.SheafOfModules.pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
  refine { unit := ?_, tensor := fun M N ↦ ?_ }
  · refine (cancel_mono (Functor.OplaxMonoidal.η
      (_root_.SheafOfModules.pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)))).mp ?_
    rw [Category.assoc, Functor.Monoidal.ε_η, Functor.LaxMonoidal.comp_ε,
      pullback_comp_η φ ψ]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp_assoc, Functor.Monoidal.ε_η, CategoryTheory.Functor.map_id,
      Category.id_comp, Functor.Monoidal.ε_η]
  · refine (cancel_mono (Functor.OplaxMonoidal.δ
      (_root_.SheafOfModules.pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) M N)).mp ?_
    have hL : (Functor.LaxMonoidal.μ
          (_root_.SheafOfModules.pullback.{u} φ ⋙ _root_.SheafOfModules.pullback.{u} ψ) M N ≫
        (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app (M ⊗ N)) ≫
        Functor.OplaxMonoidal.δ
          (_root_.SheafOfModules.pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
            (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) M N =
        ((_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app M ⊗ₘ
          (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app N) := by
      refine (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·)
          (congrArg ((_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app (M ⊗ N) ≫ ·)
            (pullback_comp_δ φ ψ M N))).trans ?_)
      rw [Functor.LaxMonoidal.comp_μ]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
      rw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ, CategoryTheory.Functor.map_id,
        Category.id_comp, Functor.Monoidal.μ_δ_assoc]
    have hR : (((_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app M ⊗ₘ
          (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app N) ≫
        Functor.LaxMonoidal.μ
          (_root_.SheafOfModules.pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
            (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) M N) ≫
        Functor.OplaxMonoidal.δ
          (_root_.SheafOfModules.pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
            (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) M N =
        ((_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app M ⊗ₘ
          (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app N) :=
      (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_δ _ M N)).trans (Category.comp_id _))
    exact hL.trans hR.symm

end Comp

end Coherence

end

end TauCeti.SheafOfModules
