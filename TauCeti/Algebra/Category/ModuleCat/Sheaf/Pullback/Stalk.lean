/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Skyscraper

/-!
# Stalks of a pulled-back sheaf of modules

Let `f : Y ⟶ X` be a continuous map of topological spaces, `𝒪X` and `𝒪Y` sheaves of commutative
rings on `X` and `Y`, and `φ : 𝒪X ⟶ f_* 𝒪Y` a morphism of the underlying sheaves of rings. At each
point `y : Y`, `φ` induces a local ring homomorphism `𝒪_{X, f(y)} ⟶ 𝒪_{Y, y}`
(`SheafOfModules.ringStalkHom`).

Pushing a skyscraper `𝒪_{Y, y}`-module sheaf at `y` forward along `φ` yields the skyscraper
`𝒪_{X, f(y)}`-module sheaf at `f(y)` of the scalar-restricted module
(`SheafOfModules.skyscraperPushforwardIso`), without assuming that pullback exists. When
`SheafOfModules.pushforward φ` has a left adjoint `SheafOfModules.pullback φ`, uniqueness of left
adjoints identifies the stalk of a pulled-back module sheaf `(f^* G)_y` naturally with the scalar
extension `𝒪_{Y, y} ⊗_{𝒪_{X, f(y)}} G_{f(y)}` (`SheafOfModules.pullbackStalkIso`), without any
finiteness or quasi-coherence assumption on `G`.

When `𝒪_{Y, y}` is equipped with an `𝒪_{X, f(y)}`-algebra structure whose `algebraMap` is
`(ringStalkHom φ y).hom`, `SheafOfModules.pullbackStalkEquiv` packages this stalk identification as
an `𝒪_{Y, y}`-linear equivalence `𝒪_{Y, y} ⊗[𝒪_{X, f(y)}] G_{f(y)} ≃ₗ[𝒪_{Y, y}] (f^* G)_y`, and
`SheafOfModules.isBaseChange_pullbackStalkBaseMap` records that the canonical `𝒪_{X, f(y)}`-linear
germ map `G_{f(y)} →ₗ[𝒪_{X, f(y)}] (f^* G)_y` exhibits `(f^* G)_y` as the base change of
`G_{f(y)}` along `𝒪_{X, f(y)} → 𝒪_{Y, y}`.

## Main declarations

* `SheafOfModules.ringStalkHom`: the induced ring stalk morphism `𝒪_{X, f(y)} ⟶ 𝒪_{Y, y}`.
* `SheafOfModules.skyscraperPushforwardIso`: natural isomorphism
  `skyscraper 𝒪Y y ⋙ pushforward φ ≅ restrictScalars (ringStalkHom φ y).hom ⋙ skyscraper 𝒪X (f y)`.
* `SheafOfModules.pullbackStalkIso`: natural isomorphism
  `stalkFunctor 𝒪X (f y) ⋙ extendScalars (ringStalkHom φ y).hom ≅ pullback φ ⋙ stalkFunctor 𝒪Y y`,
  computed on pure tensors of germs by `SheafOfModules.pullbackStalkIso_hom_app_tmul_germ`.
* `SheafOfModules.pullbackStalkEquiv` and `SheafOfModules.isBaseChange_pullbackStalkBaseMap`: the
  `𝒪_{Y, y}`-linear tensor equivalence and `IsBaseChange` witness for `(f^* G)_y`.

## References

* [The Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098) (stalks of the pullback
  of a sheaf of modules).
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 5.2(b) (in the generality of ringed
  spaces).
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf
open scoped TensorProduct ChangeOfRings
open TauCeti.SheafOfModules (ringCatSheaf commRingCatHom)

universe u v

noncomputable section

namespace SheafOfModules

section RingStalkHom

variable {X Y : TopCat.{u}} {f : Y ⟶ X}
  {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}

/-- The ring homomorphism `𝒪_{X, f(y)} ⟶ 𝒪_{Y, y}` on commutative ring stalks induced by a
morphism `φ : 𝒪X ⟶ f_* 𝒪Y` of sheaves of rings over `f : Y ⟶ X`. -/
def ringStalkHom
    (φ : ringCatSheaf 𝒪X ⟶
      ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
    (y : Y) :
    TopCat.Presheaf.stalk 𝒪X.obj (f y) ⟶ TopCat.Presheaf.stalk 𝒪Y.obj y :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f y)).map
      (commRingCatHom (F := Opens.map f) (S := 𝒪X) (R := 𝒪Y) φ) ≫
    TopCat.Presheaf.stalkPushforward CommRingCat.{u} f 𝒪Y.obj y

variable (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))

/-- `ringStalkHom` sends the germ of a section `r ∈ 𝒪X(U)` at `f(y)` to the germ of `φ(U)(r)` at
`y`. -/
@[reassoc (attr := simp)]
theorem germ_comp_ringStalkHom (y : Y) (U : Opens X) (hy : f y ∈ U) :
    TopCat.Presheaf.germ 𝒪X.obj U (f y) hy ≫ ringStalkHom φ y =
      (commRingCatHom φ).app (op U) ≫ TopCat.Presheaf.germ 𝒪Y.obj ((Opens.map f).obj U) y hy := by
  unfold ringStalkHom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ TopCat.Presheaf.stalkPushforward CommRingCat.{u} f 𝒪Y.obj y)
      (TopCat.Presheaf.stalkFunctor_map_germ U (f y) hy
        (commRingCatHom (F := Opens.map f) (S := 𝒪X) (R := 𝒪Y) φ))).trans
      ((Category.assoc _ _ _).trans
        (congrArg ((commRingCatHom (F := Opens.map f) (S := 𝒪X) (R := 𝒪Y) φ).app (op U) ≫ ·)
          (TopCat.Presheaf.stalkPushforward_germ CommRingCat.{u} f 𝒪Y.obj U y hy))))

/-- Elementwise form of `germ_comp_ringStalkHom`. -/
@[simp]
theorem ringStalkHom_germ (y : Y) (U : Opens X) (hy : f y ∈ U) (r : 𝒪X.obj.obj (op U)) :
    (ringStalkHom φ y).hom (TopCat.Presheaf.germ 𝒪X.obj U (f y) hy r) =
      TopCat.Presheaf.germ 𝒪Y.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r) :=
  congr($((germ_comp_ringStalkHom φ y U hy)).hom r)

end RingStalkHom

section SkyscraperPushforward

variable {X Y : TopCat.{u}} {f : Y ⟶ X}
  {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  (y : Y)

private def skyscraperPushforwardAppEquiv
    (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) (U : Opens X) :
    (((pushforward.{v} φ).obj ((skyscraper.{u, v} 𝒪Y y).obj M)).val.obj (op U)) ≃ₗ[
      (ringCatSheaf 𝒪X).obj.obj (op U)]
      (((skyscraper.{u, v} 𝒪X (f y)).obj
        ((ModuleCat.restrictScalars.{v} (ringStalkHom φ y).hom).obj M)).val.obj (op U)) :=
  let M' := (ModuleCat.restrictScalars.{v} (ringStalkHom φ y).hom).obj M
  let N_U := ((skyscraper.{u, v} 𝒪Y y).obj M).val.obj (op ((Opens.map f).obj U))
  { toFun s := skyscraperSectionMk 𝒪X (f y) M' fun hy ↦
      skyscraperSectionsEquiv 𝒪Y y M (show y ∈ (Opens.map f).obj U from hy) (s : N_U)
    invFun t := (skyscraperSectionMk 𝒪Y y M (U := (Opens.map f).obj U) fun hy ↦
      skyscraperSectionsEquiv 𝒪X (f y) M' (show f y ∈ U from hy) t : N_U)
    left_inv s :=
      show (skyscraperSectionMk 𝒪Y y M (U := (Opens.map f).obj U) _ : N_U) = (s : N_U) from
        skyscraper_section_ext fun hy ↦
          (skyscraperSectionsEquiv_skyscraperSectionMk 𝒪Y y M _ hy).trans
            (skyscraperSectionsEquiv_skyscraperSectionMk 𝒪X (f y) M' _ (show f y ∈ U from hy))
    right_inv t := skyscraper_section_ext fun hy ↦
      (skyscraperSectionsEquiv_skyscraperSectionMk 𝒪X (f y) M' _ hy).trans
        (skyscraperSectionsEquiv_skyscraperSectionMk 𝒪Y y M _
          (show y ∈ (Opens.map f).obj U from hy))
    map_add' s₁ s₂ := skyscraper_section_ext fun hy ↦ by
      let hy' : y ∈ (Opens.map f).obj U := hy
      have h₁ : skyscraperSectionsEquiv 𝒪X (f y) M' hy
          (skyscraperSectionMk 𝒪X (f y) M' fun h ↦
            skyscraperSectionsEquiv 𝒪Y y M (show y ∈ (Opens.map f).obj U from h)
              (((s₁ + s₂ : ((pushforward.{v} φ).obj ((skyscraper.{u, v} 𝒪Y y).obj M)).val.obj
                (op U)) : N_U))) =
          (skyscraperSectionsEquiv 𝒪Y y M hy' ((s₁ : N_U) + (s₂ : N_U)) : M') :=
        skyscraperSectionsEquiv_skyscraperSectionMk 𝒪X (f y) M' _ hy
      have h₂ : (skyscraperSectionsEquiv 𝒪Y y M hy' ((s₁ : N_U) + (s₂ : N_U)) : M') =
          @HAdd.hAdd M' M' M' instHAdd
            (skyscraperSectionsEquiv 𝒪Y y M hy' (s₁ : N_U))
            (skyscraperSectionsEquiv 𝒪Y y M hy' (s₂ : N_U)) :=
        (skyscraperSectionsEquiv 𝒪Y y M hy').map_add (s₁ : N_U) (s₂ : N_U)
      have h₃ := ((skyscraperSectionsEquiv 𝒪X (f y) M' hy).map_add
        (skyscraperSectionMk 𝒪X (f y) M' fun h ↦
          skyscraperSectionsEquiv 𝒪Y y M (show y ∈ (Opens.map f).obj U from h) (s₁ : N_U))
        (skyscraperSectionMk 𝒪X (f y) M' fun h ↦
          skyscraperSectionsEquiv 𝒪Y y M (show y ∈ (Opens.map f).obj U from h) (s₂ : N_U))).trans
        (congrArg₂ (@HAdd.hAdd M' M' M' instHAdd)
          (skyscraperSectionsEquiv_skyscraperSectionMk 𝒪X (f y) M' _ hy)
          (skyscraperSectionsEquiv_skyscraperSectionMk 𝒪X (f y) M' _ hy))
      exact h₁.trans (h₂.trans h₃.symm)
    map_smul' r s := skyscraper_section_ext fun hy ↦ by
      let hy' : y ∈ (Opens.map f).obj U := hy
      let rX : 𝒪X.obj.obj (op U) := r
      let rY : 𝒪Y.obj.obj (op ((Opens.map f).obj U)) := φ.hom.app (op U) rX
      -- On the pushforward, `r` acts through `φ.hom.app (op U) r`; on `M'`, the germ of `r` at
      -- `f(y)` acts through `ringStalkHom φ y`.
      have hL : skyscraperSectionsEquiv 𝒪X (f y) M' hy
          (skyscraperSectionMk 𝒪X (f y) M' fun h ↦
            skyscraperSectionsEquiv 𝒪Y y M (show y ∈ (Opens.map f).obj U from h)
              ((r • s : ((pushforward.{v} φ).obj ((skyscraper.{u, v} 𝒪Y y).obj M)).val.obj (op U)) :
                N_U)) =
          TopCat.Presheaf.germ 𝒪Y.obj ((Opens.map f).obj U) y hy' rY •
            skyscraperSectionsEquiv 𝒪Y y M hy' (s : N_U) :=
        (skyscraperSectionsEquiv_skyscraperSectionMk 𝒪X (f y) M' _ hy).trans
          (skyscraperSectionsEquiv_smul 𝒪Y y M hy' rY (s : N_U))
      have hR : skyscraperSectionsEquiv 𝒪X (f y) M' hy
          (r • skyscraperSectionMk 𝒪X (f y) M' fun h ↦
            skyscraperSectionsEquiv 𝒪Y y M (show y ∈ (Opens.map f).obj U from h) (s : N_U)) =
          (ringStalkHom φ y).hom (TopCat.Presheaf.germ 𝒪X.obj U (f y) hy rX) •
            skyscraperSectionsEquiv 𝒪Y y M hy' (s : N_U) :=
        (skyscraperSectionsEquiv_smul 𝒪X (f y) M' hy rX _).trans
          ((congrArg (TopCat.Presheaf.germ 𝒪X.obj U (f y) hy rX • ·)
            (skyscraperSectionsEquiv_skyscraperSectionMk 𝒪X (f y) M' _ hy)).trans
            (ModuleCat.restrictScalars.smul_def (ringStalkHom φ y).hom
              (TopCat.Presheaf.germ 𝒪X.obj U (f y) hy rX) _))
      exact hL.trans ((congrArg (· • skyscraperSectionsEquiv 𝒪Y y M hy' (s : N_U))
        (ringStalkHom_germ φ y U hy rX).symm).trans hR.symm) }

private theorem skyscraperSectionsEquiv_skyscraperPushforwardAppEquiv
    (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) {U : Opens X} (hy : f y ∈ U)
    (s : ((pushforward.{v} φ).obj ((skyscraper.{u, v} 𝒪Y y).obj M)).val.obj (op U)) :
    skyscraperSectionsEquiv 𝒪X (f y)
        ((ModuleCat.restrictScalars.{v} (ringStalkHom φ y).hom).obj M) hy
        (skyscraperPushforwardAppEquiv φ y M U s) =
      skyscraperSectionsEquiv 𝒪Y y M (show y ∈ (Opens.map f).obj U from hy) s := by
  unfold skyscraperPushforwardAppEquiv
  exact skyscraperSectionsEquiv_skyscraperSectionMk 𝒪X (f y) _ _ hy

/-- Pushing forward a skyscraper module sheaf at `y` along `φ : 𝒪X ⟶ f_* 𝒪Y` yields the skyscraper
module sheaf at `f(y)` of its scalar restriction along `ringStalkHom φ y`, naturally in the
`𝒪_{Y, y}`-module. -/
def skyscraperPushforwardIso :
    skyscraper.{u, v} 𝒪Y y ⋙ pushforward.{v} φ ≅
      ModuleCat.restrictScalars.{v} (ringStalkHom φ y).hom ⋙ skyscraper.{u, v} 𝒪X (f y) :=
  NatIso.ofComponents
    (fun M ↦ (fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun U ↦ (skyscraperPushforwardAppEquiv φ y M U.unop).toModuleIso)
        fun U V i ↦ by
          apply ModuleCat.hom_ext
          refine LinearMap.ext fun s ↦
            show (skyscraperPushforwardAppEquiv φ y M V.unop
                (((pushforward.{v} φ).obj ((skyscraper.{u, v} 𝒪Y y).obj M)).val.map i s) :
                  ((skyscraper.{u, v} 𝒪X (f y)).obj _).val.obj (op V.unop)) =
              ((skyscraper.{u, v} 𝒪X (f y)).obj _).val.map i.unop.op
                (skyscraperPushforwardAppEquiv φ y M U.unop s) from
            skyscraper_section_ext fun hy ↦
              (skyscraperSectionsEquiv_skyscraperPushforwardAppEquiv φ y M hy
                (((pushforward.{v} φ).obj ((skyscraper.{u, v} 𝒪Y y).obj M)).val.map i s)).trans
                ((skyscraperSectionsEquiv_map 𝒪Y y M ((Opens.map f).map i.unop)
                  (show y ∈ (Opens.map f).obj V.unop from hy) s).trans
                  ((skyscraperSectionsEquiv_skyscraperPushforwardAppEquiv φ y M (i.unop.le hy)
                    s).symm.trans
                    (skyscraperSectionsEquiv_map 𝒪X (f y) _ i.unop hy
                      (skyscraperPushforwardAppEquiv φ y M U.unop s)).symm))))
    fun {M N} l ↦ by
      ext U : 2
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun s ↦ skyscraper_section_ext fun hy ↦ ?_
      exact (skyscraperSectionsEquiv_skyscraperPushforwardAppEquiv φ y N hy
        (((pushforward.{v} φ).map ((skyscraper.{u, v} 𝒪Y y).map l)).val.app U s)).trans
        ((skyscraperSectionsEquiv_skyscraper_map_app 𝒪Y y l
          (show y ∈ (Opens.map f).obj U.unop from hy) s).trans
          ((congrArg l
            (skyscraperSectionsEquiv_skyscraperPushforwardAppEquiv φ y M hy s).symm).trans
            (skyscraperSectionsEquiv_skyscraper_map_app 𝒪X (f y)
              ((ModuleCat.restrictScalars (ringStalkHom φ y).hom).map l) hy
              (skyscraperPushforwardAppEquiv φ y M U.unop s)).symm))

/-- Evaluating `(skyscraperPushforwardIso φ y).hom.app M` at `f(y) ∈ U` preserves the value of a
section at `y`. -/
@[simp]
theorem skyscraperSectionsEquiv_skyscraperPushforwardIso_hom_app
    (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) {U : Opens X} (hy : f y ∈ U)
    (s : ((pushforward.{v} φ).obj ((skyscraper.{u, v} 𝒪Y y).obj M)).val.obj (op U)) :
    dsimp% only [Functor.comp_obj]
    (skyscraperSectionsEquiv 𝒪X (f y)
        ((ModuleCat.restrictScalars.{v} (ringStalkHom φ y).hom).obj M) hy
        (((skyscraperPushforwardIso φ y).hom.app M).val.app (op U) s) =
      skyscraperSectionsEquiv 𝒪Y y M (U := (Opens.map f).obj U) hy s) := by
  unfold skyscraperPushforwardIso
  exact skyscraperSectionsEquiv_skyscraperPushforwardAppEquiv φ y M hy s

/-- Evaluating `(skyscraperPushforwardIso φ y).inv.app M` at `y ∈ f ⁻¹' U` preserves the value of a
section at `f(y)`. -/
@[simp]
theorem skyscraperSectionsEquiv_skyscraperPushforwardIso_inv_app
    (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) {U : Opens X} (hy : f y ∈ U)
    (t : ((skyscraper.{u, v} 𝒪X (f y)).obj
      ((ModuleCat.restrictScalars.{v} (ringStalkHom φ y).hom).obj M)).val.obj (op U)) :
    dsimp% only [Functor.comp_obj]
    (skyscraperSectionsEquiv 𝒪Y y M (U := (Opens.map f).obj U) hy
        (((skyscraperPushforwardIso φ y).inv.app M).val.app (op U) t) =
      skyscraperSectionsEquiv 𝒪X (f y)
        ((ModuleCat.restrictScalars.{v} (ringStalkHom φ y).hom).obj M) hy t) := by
  have h := skyscraperSectionsEquiv_skyscraperPushforwardIso_hom_app φ y M hy
    (((skyscraperPushforwardIso φ y).inv.app M).val.app (op U) t)
  have hinv : ((skyscraperPushforwardIso φ y).hom.app M).val.app (op U)
      (((skyscraperPushforwardIso φ y).inv.app M).val.app (op U) t) = t :=
    congr($(((evaluation _ (op U)).mapIso ((skyscraperPushforwardIso φ y).app M)).inv_hom_id) t)
  rw [hinv] at h
  exact h.symm

end SkyscraperPushforward

section PullbackStalk

variable {X Y : TopCat.{u}} {f : Y ⟶ X}
  {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(pushforward.{u} φ).IsRightAdjoint]

/-- **Stalk of a pulled-back sheaf of modules.** For any morphism of ringed spaces `(f, φ)` whose
module pushforward has a left adjoint `pullback φ`, and any point `y : Y`, taking the stalk at `y`
after pulling back along `φ` is naturally isomorphic to taking the stalk at `f(y)` and extending
scalars along `ringStalkHom φ y : 𝒪_{X, f(y)} ⟶ 𝒪_{Y, y}`. -/
def pullbackStalkIso (y : Y) :
    stalkFunctor 𝒪X (f y) ⋙ ModuleCat.extendScalars (ringStalkHom φ y).hom ≅
      pullback.{u} φ ⋙ stalkFunctor 𝒪Y y :=
  Adjunction.leftAdjointUniq
    ((stalkSkyscraperAdjunction 𝒪X (f y)).comp
      (ModuleCat.extendRestrictScalarsAdj (ringStalkHom φ y).hom))
    (((pullbackPushforwardAdjunction.{u} φ).comp
      (stalkSkyscraperAdjunction 𝒪Y y)).ofNatIsoRight (skyscraperPushforwardIso φ y))

/-- On `1 ⊗ m_{f(y)}`, the forward component of `pullbackStalkIso` produces the germ at `y` of the
image of `m` under the pullback--pushforward unit. -/
theorem pullbackStalkIso_hom_app_one_tmul_germ (G : SheafOfModules.{u} (ringCatSheaf 𝒪X))
    (y : Y) (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    (pullbackStalkIso φ y).hom.app G
        ((1 : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)),
          (ringStalkHom φ y).hom] germ G.val.presheaf U (f y) hy m) =
      germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y hy
        (((pullbackPushforwardAdjunction.{u} φ).unit.app G).val.app (op U) m) := by
  let adj₁ := (stalkSkyscraperAdjunction 𝒪X (f y)).comp
    (ModuleCat.extendRestrictScalarsAdj (ringStalkHom φ y).hom)
  let adj₂ := ((pullbackPushforwardAdjunction.{u} φ).comp
    (stalkSkyscraperAdjunction 𝒪Y y)).ofNatIsoRight (skyscraperPushforwardIso φ y)
  have h : adj₁.homEquiv G ((pullback φ ⋙ stalkFunctor 𝒪Y y).obj G)
      ((pullbackStalkIso φ y).hom.app G) = adj₂.unit.app G := by
    unfold pullbackStalkIso
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app adj₁ adj₂ G
  have heval := congrArg (fun α : G ⟶ (skyscraper 𝒪X (f y)).obj _ ↦
    skyscraperSectionsEquiv 𝒪X (f y) _ hy (α.val.app (op U) m)) h
  -- Evaluate the left-hand side via the composite hom-equivalence and the right-hand side via the
  -- composite unit transported along `skyscraperPushforwardIso`.
  have hhom : adj₁.homEquiv G ((pullback φ ⋙ stalkFunctor 𝒪Y y).obj G)
      ((pullbackStalkIso φ y).hom.app G) =
      stalkSkyscraperHomEquiv 𝒪X (f y) G _
        ((ModuleCat.extendRestrictScalarsAdj (ringStalkHom φ y).hom).homEquiv _ _
          ((pullbackStalkIso φ y).hom.app G)) := by
    dsimp [adj₁]
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, stalkSkyscraperAdjunction_homEquiv]
  have hL : skyscraperSectionsEquiv 𝒪X (f y) _ hy
      ((adj₁.homEquiv G ((pullback φ ⋙ stalkFunctor 𝒪Y y).obj G)
        ((pullbackStalkIso φ y).hom.app G)).val.app (op U) m) =
      (pullbackStalkIso φ y).hom.app G
        ((1 : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) ⊗ₜ[_, (ringStalkHom φ y).hom]
          germ G.val.presheaf U (f y) hy m) :=
    (congrArg (fun α : G ⟶ (skyscraper 𝒪X (f y)).obj _ ↦
      skyscraperSectionsEquiv 𝒪X (f y) _ hy (α.val.app (op U) m)) hhom).trans
      ((skyscraperSectionsEquiv_stalkSkyscraperHomEquiv 𝒪X (f y) G _
        ((ModuleCat.extendRestrictScalarsAdj (ringStalkHom φ y).hom).homEquiv _ _
          ((pullbackStalkIso φ y).hom.app G)) hy m).trans
        (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
          ((pullbackStalkIso φ y).hom.app G) (germ G.val.presheaf U (f y) hy m)))
  have hR : skyscraperSectionsEquiv 𝒪X (f y) _ hy ((adj₂.unit.app G).val.app (op U) m) =
      germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y hy
        (((pullbackPushforwardAdjunction.{u} φ).unit.app G).val.app (op U) m) := by
    let m' : ((pullback.{u} φ).obj G).val.obj (op ((Opens.map f).obj U)) :=
      ((pullbackPushforwardAdjunction.{u} φ).unit.app G).val.app (op U) m
    exact (skyscraperSectionsEquiv_skyscraperPushforwardIso_hom_app φ y _ hy
      (((stalkSkyscraperAdjunction 𝒪Y y).unit.app ((pullback φ).obj G)).val.app
        (op ((Opens.map f).obj U)) m')).trans
      (skyscraperSectionsEquiv_stalkSkyscraperAdjunction_unit 𝒪Y y
        ((pullback φ).obj G) hy m')
  exact hL.symm.trans (heval.trans hR)

/-- On a pure tensor `s ⊗ m_{f(y)}`, the forward component of `pullbackStalkIso` multiplies the
pulled-back germ of `m` at `y` by `s`. -/
@[simp]
theorem pullbackStalkIso_hom_app_tmul_germ (G : SheafOfModules.{u} (ringCatSheaf 𝒪X))
    (y : Y) (s : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) (U : Opens X) (hy : f y ∈ U)
    (m : G.val.obj (op U)) :
    dsimp% only [Functor.comp_obj, PresheafOfModules.presheaf_obj_coe]
    ((pullbackStalkIso φ y).hom.app G
        (s ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)), (ringStalkHom φ y).hom]
          germ G.val.presheaf U (f y) hy m) =
      s • germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y hy
        (((pullbackPushforwardAdjunction.{u} φ).unit.app G).val.app (op U) m)) := by
  have hsmul := (ModuleCat.ExtendScalars.smul_tmul (ringStalkHom φ y).hom
    (M := (stalkFunctor 𝒪X (f y)).obj G) s 1 (germ G.val.presheaf U (f y) hy m)).trans
    (congrArg (· ⊗ₜ[_, (ringStalkHom φ y).hom] germ G.val.presheaf U (f y) hy m) (mul_one s))
  exact (congrArg ((pullbackStalkIso φ y).hom.app G) hsmul.symm).trans
    ((((pullbackStalkIso φ y).hom.app G).hom.map_smul s _).trans
      (congrArg (s • ·) (pullbackStalkIso_hom_app_one_tmul_germ φ G y U hy m)))

section Algebra

variable (G : SheafOfModules.{u} (ringCatSheaf 𝒪X)) (y : Y)
  [Algebra ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]

/-- When `𝒪_{Y, y}` carries an `𝒪_{X, f(y)}`-algebra structure induced by `ringStalkHom φ y`, the
stalk `(f^* G)_y` is `𝒪_{Y, y}`-linearly equivalent to `𝒪_{Y, y} ⊗[𝒪_{X, f(y)}] G_{f(y)}`. -/
def pullbackStalkEquiv
    (halg : algebraMap ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) =
      (ringStalkHom φ y).hom := by rfl) :
    ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
      ↑(TopCat.Presheaf.stalk G.val.presheaf (f y)) ≃ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
      ↑(TopCat.Presheaf.stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
  ((ModuleCat.extendScalarsAlgebraMapIso ((stalkFunctor 𝒪X (f y)).obj G)).symm ≪≫
    eqToIso (congrArg (fun ρ ↦ (ModuleCat.extendScalars ρ).obj ((stalkFunctor 𝒪X (f y)).obj G))
      halg) ≪≫
    (pullbackStalkIso φ y).app G).toLinearEquiv

/-- `pullbackStalkEquiv` sends `s ⊗ m_{f(y)}` to `s` times the pulled-back germ of `m` at `y`. -/
@[simp]
theorem pullbackStalkEquiv_tmul_germ
    (halg : algebraMap ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) =
      (ringStalkHom φ y).hom := by rfl)
    (s : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) (U : Opens X) (hy : f y ∈ U)
    (m : G.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (pullbackStalkEquiv φ G y halg (s ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
        germ G.val.presheaf U (f y) hy m) =
      s • germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y hy
        (((pullbackPushforwardAdjunction.{u} φ).unit.app G).val.app (op U) m)) := by
  let M₀ := (stalkFunctor 𝒪X (f y)).obj G
  let g : M₀ := germ G.val.presheaf U (f y) hy m
  have heq : ∀ {ρ₁ ρ₂ : ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) →+* ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)}
      (h : ρ₁ = ρ₂),
      (eqToIso (congrArg (fun ρ ↦ (ModuleCat.extendScalars ρ).obj M₀) h)).hom (s ⊗ₜ[_, ρ₁] g) =
        s ⊗ₜ[_, ρ₂] g := by
    intro _ _ h
    subst h
    rfl
  have h₁ : pullbackStalkEquiv φ G y halg (s ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))] g) =
      (pullbackStalkIso φ y).hom.app G
        ((eqToIso (congrArg (fun ρ ↦ (ModuleCat.extendScalars ρ).obj M₀) halg)).hom
          ((ModuleCat.extendScalarsAlgebraMapIso M₀).inv (s ⊗ₜ g))) := by
    unfold pullbackStalkEquiv
    rfl
  exact h₁.trans ((congrArg (fun z ↦ (pullbackStalkIso φ y).hom.app G
    ((eqToIso (congrArg (fun ρ ↦ (ModuleCat.extendScalars ρ).obj M₀) halg)).hom z))
    (ModuleCat.extendScalarsAlgebraMapIso_inv_tmul M₀ s g)).trans
    ((congrArg ((pullbackStalkIso φ y).hom.app G) (heq halg)).trans
      (pullbackStalkIso_hom_app_tmul_germ φ G y s U hy m)))

/-- The canonical `𝒪_{X, f(y)}`-linear map `G_{f(y)} →ₗ[𝒪_{X, f(y)}] (f^* G)_y` sending the germ
of a section `m` at `f(y)` to the germ of its unit image at `y`. -/
def pullbackStalkBaseMap
    [Module ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))
      ↑(TopCat.Presheaf.stalk ((pullback.{u} φ).obj G).val.presheaf y)]
    [IsScalarTower ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
      ↑(TopCat.Presheaf.stalk ((pullback.{u} φ).obj G).val.presheaf y)]
    (halg : algebraMap ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) =
      (ringStalkHom φ y).hom := by rfl) :
    ↑(TopCat.Presheaf.stalk G.val.presheaf (f y)) →ₗ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
      ↑(TopCat.Presheaf.stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
  ((pullbackStalkEquiv φ G y halg).toLinearMap.restrictScalars
    ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))).comp
      (TensorProduct.mk ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))
        ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) ↑(TopCat.Presheaf.stalk G.val.presheaf (f y)) 1)

variable [Module ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))
    ↑(TopCat.Presheaf.stalk ((pullback.{u} φ).obj G).val.presheaf y)]
  [IsScalarTower ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
    ↑(TopCat.Presheaf.stalk ((pullback.{u} φ).obj G).val.presheaf y)]

/-- `pullbackStalkBaseMap` sends the germ of `m ∈ G(U)` at `f(y)` to the germ at `y` of its image
under the pullback--pushforward unit. -/
@[simp]
theorem pullbackStalkBaseMap_germ
    (halg : algebraMap ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) =
      (ringStalkHom φ y).hom := by rfl)
    (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (pullbackStalkBaseMap φ G y halg (germ G.val.presheaf U (f y) hy m) =
      germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y hy
        (((pullbackPushforwardAdjunction.{u} φ).unit.app G).val.app (op U) m)) := by
  unfold pullbackStalkBaseMap
  exact (pullbackStalkEquiv_tmul_germ φ G y halg 1 U hy m).trans (one_smul _ _)

/-- The canonical map `pullbackStalkBaseMap` exhibits `(f^* G)_y` as the base change of `G_{f(y)}`
along `𝒪_{X, f(y)} → 𝒪_{Y, y}`. -/
theorem isBaseChange_pullbackStalkBaseMap
    (halg : algebraMap ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) =
      (ringStalkHom φ y).hom := by rfl) :
    IsBaseChange ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) (pullbackStalkBaseMap φ G y halg) := by
  refine IsBaseChange.of_equiv (pullbackStalkEquiv φ G y halg) fun _ ↦ ?_
  unfold pullbackStalkBaseMap
  rfl

end Algebra

end PullbackStalk

end SheafOfModules

end
