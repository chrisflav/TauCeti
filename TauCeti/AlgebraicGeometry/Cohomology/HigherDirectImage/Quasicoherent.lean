/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Scalars
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.LocallyBijective
import TauCeti.Algebra.Module.LocalizedModule.Map
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Restrict
import TauCeti.AlgebraicGeometry.Cohomology.Localization

/-!
# Higher direct images of quasi-coherent modules are quasi-coherent

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes and `M` a
quasi-coherent `𝒪_X`-module. Then every higher direct image `Rⁿ f_* M` is quasi-coherent
(`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_higherDirectImage`). Over an affine base `Y` with
`X` quasi-compact and quasi-separated, its sections over a basic open `D(g)` of `Y` are the
cohomology `Hⁿ(f⁻¹ D(g), M)`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageBasicOpenSectionsAddEquiv`).

The higher direct image is the sheafification of the presheaf of `𝒪_Y`-modules
`V ↦ Hⁿ(f⁻¹ V, M)` (`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheaf`). If `X` is
quasi-compact and quasi-separated, the restriction of this presheaf from `Y` to the basic open
`D(g)` of a global function `g` is the localization at the powers of `g`
(`AlgebraicGeometry.Scheme.Hom.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen`): its
underlying map is the restriction `Hⁿ(X, M) ⟶ Hⁿ(X_{f^* g}, M)`, which is a localization because
cohomology of quasi-coherent modules commutes with localization
(`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_cohomologyOnResLinear_inf_basicOpen`), and
its scalar action is the action through pullback of functions
(`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafToPresheafIso_hom_app_smul`). A presheaf
of modules with this property on an affine scheme has quasi-coherent sheafification, with the
same sections over basic opens
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyBijective`). Over a general base,
higher direct images are local on the target
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageRestrictIso`), and `f` restricts over each affine
open of `Y` to a morphism from a quasi-compact quasi-separated scheme.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen`: for
  quasi-compact quasi-separated `X` and quasi-coherent `M`, the restriction of `V ↦ Hⁿ(f⁻¹ V, M)`
  from `Y` to `D(g)` is the localization at the powers of `g`;
* `AlgebraicGeometry.Scheme.Hom.isQuasicoherent_higherDirectImage`: the higher direct images of a
  quasi-coherent module along a quasi-compact quasi-separated morphism are quasi-coherent;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageBasicOpenSectionsAddEquiv`: over an affine base,
  the sections of `Rⁿ f_* M` over `D(g)` are `Hⁿ(f⁻¹ D(g), M)`;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageTopAddEquiv`: over an affine base, the global
  sections of `Rⁿ f_* M` are additively equivalent to `Hⁿ(X, M)`;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageTopAddEquiv_smul`: compatibility of
  `higherDirectImageTopAddEquiv` with the action of global functions via `f^*`;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageTopBaseLinearEquiv`: over `Spec R`, the `R`-linear
  equivalence `Hⁿ(X, M) ≃ₗ[R] Γ(Rⁿ f_* M, ⊤)` when the target is affine.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.5.
* The Stacks Project, Lemma 30.4.5 (tag 01XJ).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Higher direct images commute with localization.** For a quasi-compact quasi-separated
scheme `X`, a quasi-coherent `M` and a global function `g` on `Y`, the restriction of the presheaf
of modules `V ↦ Hⁿ(f⁻¹ V, M)` from `Y` to the basic open `D(g)` is the localization at the
powers of `g`. -/
theorem isLocalizedModule_higherDirectImagePresheaf_map_basicOpen [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (g : Γ(Y, ⊤)) :
    IsLocalizedModule (.powers g) (PresheafOfModulesOfCommRing.map (R := Y.presheaf)
      ((f.higherDirectImagePresheaf n).obj M) (homOfLE (Y.basicOpen_le g)).op).hom := by
  let e := f.higherDirectImagePresheafToPresheafIso M n
  have hW : f ⁻¹ᵁ Y.basicOpen g = f ⁻¹ᵁ ⊤ ⊓ X.basicOpen (f.appTop g) := by
    rw [Scheme.preimage_basicOpen]
    exact (inf_eq_right.2 (X.basicOpen_le _)).symm
  have : IsLocalizedModule ((Submonoid.powers g).map f.appTop.hom)
      (cohomologyOnResLinear M n (f.preimage_mono (Y.basicOpen_le g))) := by
    rw [Submonoid.map_powers]
    exact isLocalizedModule_cohomologyOnResLinear_inf_basicOpen M _
      (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ) _ hW n
  -- Identify the restriction map with restriction in cohomology, semilinearly along `f^*`.
  refine IsLocalizedModule.of_bijective_semilinearMap (.powers g) _
    (cohomologyOnResLinear M n (f.preimage_mono (Y.basicOpen_le g)))
    { toFun := e.hom.app (.op ⊤)
      map_add' := map_add _
      map_smul' := fun r x ↦ ?_ }
    { toFun := e.hom.app (.op (Y.basicOpen g))
      map_add' := map_add _
      map_smul' := fun r x ↦
        f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r (Y.basicOpen g) x }
    (ConcreteCategory.bijective_of_isIso (e.hom.app (.op ⊤)))
    (ConcreteCategory.bijective_of_isIso (e.hom.app (.op (Y.basicOpen g)))) fun x ↦ ?_
  · refine (congrArg _ ?_).trans (f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r ⊤ x)
    -- the inclusion of `⊤` into itself is the identity, as morphisms of a preorder are unique
    rw [show (⊤ : Y.Opens).leTop = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  · rw [cohomologyOnResLinear_apply]
    exact ConcreteCategory.congr_hom (e.hom.naturality (homOfLE (Y.basicOpen_le g)).op) x

section Affine

variable [IsAffine Y] [QuasiCompact f] [QuasiSeparated f] (M : X.Modules)
  [M.IsQuasicoherent] (n : ℕ)

/-- **Higher direct images over an affine base.** For a quasi-compact quasi-separated scheme `X`
over an affine scheme `Y` and a quasi-coherent `M`, the sections of the higher direct image
`Rⁿ f_* M` over an open `V` equal to the basic open of a global function are the cohomology
`Hⁿ(f⁻¹ V, M)`. The equivalence sends a class to the section of the sheafification of
`V ↦ Hⁿ(f⁻¹ V, M)` that it defines
(`higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app`). -/
def higherDirectImageBasicOpenSectionsAddEquiv {V : Y.Opens}
    (hV : ∃ g : Γ(Y, ⊤), Y.basicOpen g = V) :
    cohomologyOn M n (f ⁻¹ᵁ V) ≃+ Γ((f.higherDirectImage n).obj M, V) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
    ((f.higherDirectImagePresheaf n).obj M)).app (.op V)
  let e := ((f.higherDirectImagePresheafToPresheafIso M n).app (.op V)).symm
  let i := ((Scheme.Modules.toPresheaf Y).mapIso
    ((f.higherDirectImagePresheafSheafificationIso n).app M)).app (.op V)
  exact e.addCommGroupIsoToAddEquiv.trans ((AddEquiv.ofBijective η.hom.toAddMonoidHom
    (by
      obtain ⟨g, rfl⟩ := hV
      have hY := isAffineOpen_top Y
      exact hY.bijective_sheafificationAdjunction_unit_app_basicOpen_of_isLocalizedModule _
        (f.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen M n) g)).trans
      i.addCommGroupIsoToAddEquiv)

/-- The equivalence `higherDirectImageBasicOpenSectionsAddEquiv` sends the class in
`Hⁿ(f⁻¹ V, M)` of a section `x` of the presheaf `V ↦ Hⁿ(f⁻¹ V, M)` to the section of its
sheafification `Rⁿ f_* M` defined by `x`. -/
-- Apply before simp normalizes the cohomology presheaf section type.
@[simp↓]
lemma higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app
    {V : Y.Opens} (hV : ∃ g : Γ(Y, ⊤), Y.basicOpen g = V)
    (x : ((f.higherDirectImagePresheaf n).obj M).obj (.op V)) :
    f.higherDirectImageBasicOpenSectionsAddEquiv M n hV
        ((f.higherDirectImagePresheafToPresheafIso M n).hom.app _ x) =
      ((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app _
        (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
          ((f.higherDirectImagePresheaf n).obj M)).app _ x) := by
  -- the equivalence first inverts the identification of the presheaf with cohomology
  exact congrArg (fun y ↦ ((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app _
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
      ((f.higherDirectImagePresheaf n).obj M)).app _ y))
    (Iso.hom_inv_id_apply ((f.higherDirectImagePresheafToPresheafIso M n).app _) x)

/-- Over an affine base, the higher direct images of a quasi-coherent module on a quasi-compact
quasi-separated scheme are quasi-coherent. -/
private lemma isQuasicoherent_higherDirectImage_of_isAffine :
    ((f.higherDirectImage n).obj M).IsQuasicoherent := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  apply (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((f.higherDirectImagePresheafSheafificationIso n).app M)
  exact Scheme.Modules.isQuasicoherent_sheafification_of_isLocalizedModule _
    (fun _ : Unit ↦ ⊤) (fun _ ↦ isAffineOpen_top Y) iSup_const
    fun _ ↦ f.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen M n

/-- Transporting cohomology along an equality of opens respects the action of global functions. -/
private lemma eqToIso_cohomologyOn_inv_smul {X : Scheme.{u}} (M : X.Modules) (n : ℕ)
    {U V : X.Opens} (h : U = V) (r : Γ(X, ⊤)) (x : cohomologyOn M n V) :
    (eqToIso (congrArg (cohomologyOn M n) h)).inv (r • x) =
      r • (eqToIso (congrArg (cohomologyOn M n) h)).inv x := by
  subst h
  rfl

/-- **Global sections of a higher direct image over an affine base.** For a quasi-compact,
quasi-separated morphism `f : X ⟶ Y` into an affine scheme `Y` and a quasi-coherent `𝒪_X`-module
`M`, the global sections of `Rⁿ f_* M` are additively equivalent to `Hⁿ(X, M)`. -/
def higherDirectImageTopAddEquiv :
    Cohomology M n ≃+ Γ((f.higherDirectImage n).obj M, ⊤) :=
  ((cohomologyOnTopIso M n).symm ≪≫
    (eqToIso (congrArg (cohomologyOn M n) f.preimage_top)).symm).addCommGroupIsoToAddEquiv.trans
    (f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩)

/-- The identification of `Hⁿ(X, M)` with the global sections of `Rⁿ f_* M` over an affine base
is compatible with the action of global functions on `Y` via `f^*`. -/
theorem higherDirectImageTopAddEquiv_smul (r : Γ(Y, ⊤)) (x : Cohomology M n) :
    f.higherDirectImageTopAddEquiv M n (f.appTop r • x) =
      r • f.higherDirectImageTopAddEquiv M n x := by
  let i := (cohomologyOnTopIso M n).symm ≪≫
    (eqToIso (congrArg (cohomologyOn M n) f.preimage_top)).symm
  let e := (f.higherDirectImagePresheafToPresheafIso M n).app (.op ⊤)
  obtain ⟨y₀, hy⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 (i.hom x)
  let y : ((f.higherDirectImagePresheaf n).obj M).obj (.op ⊤) := y₀
  let r' : Y.ringCatSheaf.obj.obj (.op ⊤) := r
  have hy' : (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤) y = i.hom x := hy
  -- Ascribe `cohomologyOn M n (f ⁻¹ᵁ ⊤)` explicitly so `HSMul` resolves to the cohomology action.
  have hy_coh : (show cohomologyOn M n (f ⁻¹ᵁ ⊤) from
      (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤) y) = i.hom x := hy
  have he_smul : (show cohomologyOn M n (f ⁻¹ᵁ ⊤) from
      (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤) (r' • y)) =
      f.appTop r • (show cohomologyOn M n (f ⁻¹ᵁ ⊤) from
        (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤) y) := by
    -- Ascribe the ring-sheaf section type to match `higherDirectImagePresheafToPresheafIso`.
    have hmap : (show Y.ringCatSheaf.obj.obj (.op ⊤) from
        Y.presheaf.map (⊤ : Y.Opens).leTop.op r) = r' := by
      -- The inclusion of `⊤` into itself is the identity, so restriction acts trivially on `r`.
      rw [show (⊤ : Y.Opens).leTop = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
      rfl
    rw [← hmap]
    exact f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r ⊤ y
  have hinv_smul : (cohomologyOnTopIso M n).inv (f.appTop r • x) =
      f.appTop r • (cohomologyOnTopIso M n).inv x := by
    apply (ConcreteCategory.bijective_of_isIso (cohomologyOnTopIso M n).hom).1
    rw [Iso.inv_hom_id_apply, ← cohomologyOnTopLinearEquiv_apply,
      (cohomologyOnTopLinearEquiv M n).map_smul, cohomologyOnTopLinearEquiv_apply,
      Iso.inv_hom_id_apply]
  have hi_smul : i.hom (f.appTop r • x) = f.appTop r • i.hom x := by
    dsimp only [i, Iso.trans_hom, Iso.symm_hom]
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hinv_smul,
      eqToIso_cohomologyOn_inv_smul M n f.preimage_top]
  have h1 : i.hom (f.appTop r • x) =
      (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤) (r' • y) :=
    hi_smul.trans ((congrArg (f.appTop r • ·) hy_coh.symm).trans he_smul.symm)
  have hstep (x' : Cohomology M n)
      (z : ((f.higherDirectImagePresheaf n).obj M).obj (.op ⊤))
      (hz : (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤) z = i.hom x') :
      f.higherDirectImageTopAddEquiv M n x' =
        ((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app (.op ⊤)
          (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
            ((f.higherDirectImagePresheaf n).obj M)).app (.op ⊤) z) := by
    dsimp only [higherDirectImageTopAddEquiv, AddEquiv.trans_apply]
    rw [Iso.addCommGroupIsoToAddEquiv_apply]
    -- The isomorphism prefix matches `i.hom`, allowing rewriting via `hz`.
    change f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩ (i.hom x') = _
    rw [← hz]
    exact
      f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app
        M n ⟨1, Y.basicOpen_one⟩ z
  rw [hstep (f.appTop r • x) (r' • y) h1.symm, hstep x y hy']
  exact (congrArg (((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app (.op ⊤))
    ((((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
      ((f.higherDirectImagePresheaf n).obj M)).app (.op ⊤)).hom.map_smul r' y)).trans
    ((((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app (.op ⊤)).hom.map_smul
      r' _)

/-- **Base-linear global sections of a higher direct image over an affine base.** When `f : X ⟶ Y`
is a quasi-compact, quasi-separated morphism over `Spec R` into an affine scheme `Y` and `M` is
quasi-coherent, `Hⁿ(X, M)` is `R`-linearly equivalent to `Γ(Rⁿ f_* M, ⊤)`. -/
def higherDirectImageTopBaseLinearEquiv (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))] :
    Cohomology M n ≃ₗ[R] Γ((f.higherDirectImage n).obj M, ⊤) where
  __ := f.higherDirectImageTopAddEquiv M n
  map_smul' r x := by
    have hr : f.appTop (baseRingToGlobalSections R Y r) = baseRingToGlobalSections R X r := by
      rw [baseRingToGlobalSections_apply, baseRingToGlobalSections_apply,
        ← CommRingCat.comp_apply, ← comp_appTop, HomIsOver.comp_over]
    -- The inherited additive-equivalence field computes through `higherDirectImageTopAddEquiv`.
    change f.higherDirectImageTopAddEquiv M n (r • x) =
      r • f.higherDirectImageTopAddEquiv M n x
    rw [base_smul_cohomology, base_smul_globalSections, ← hr,
      f.higherDirectImageTopAddEquiv_smul M n]

/-- The forward map of `higherDirectImageTopBaseLinearEquiv` is `higherDirectImageTopAddEquiv`. -/
@[simp]
lemma higherDirectImageTopBaseLinearEquiv_apply (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))]
    (x : Cohomology M n) :
    f.higherDirectImageTopBaseLinearEquiv M n R x = f.higherDirectImageTopAddEquiv M n x := by
  rfl

/-- The inverse map of `higherDirectImageTopBaseLinearEquiv` is the inverse of
`higherDirectImageTopAddEquiv`. -/
@[simp]
lemma higherDirectImageTopBaseLinearEquiv_symm_apply (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))]
    (x : Γ((f.higherDirectImage n).obj M, ⊤)) :
    (f.higherDirectImageTopBaseLinearEquiv M n R).symm x =
      (f.higherDirectImageTopAddEquiv M n).symm x := by
  rfl

end Affine

/-- **Higher direct images of quasi-coherent modules are quasi-coherent.** For a quasi-compact
quasi-separated morphism `f : X ⟶ Y` and a quasi-coherent `𝒪_X`-module `M`, every higher direct
image `Rⁿ f_* M` is quasi-coherent. -/
instance isQuasicoherent_higherDirectImage [QuasiCompact f] [QuasiSeparated f] (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) : ((f.higherDirectImage n).obj M).IsQuasicoherent := by
  refine (Scheme.Modules.isQuasicoherent_iff_of_iSup_eq_top _ (fun U : Y.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top Y)).2 fun U ↦ ?_
  -- over the affine open `U`, the higher direct image is that of `f ∣_ U`, whose source
  -- `f⁻¹ U` is quasi-compact and quasi-separated
  have : IsAffine U.1 := U.2
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    ((f.higherDirectImageRestrictIso U.1 n).app M).symm
    (isQuasicoherent_higherDirectImage_of_isAffine (f ∣_ U.1) (M.restrict (f ⁻¹ᵁ U.1).ι) n)

end AlgebraicGeometry.Scheme.Hom
