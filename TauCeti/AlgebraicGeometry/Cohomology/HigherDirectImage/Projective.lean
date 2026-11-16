/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Restrict
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Serre
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import TauCeti.AlgebraicGeometry.Modules.Restriction.FinitePresentation

/-!
# Coherence of higher direct images along projective morphisms

Let `f : X ⟶ Y` be a morphism of schemes. This file establishes two basic facts about higher
direct images `R^q f_* M` of quasi-coherent modules and combines them with Serre's finiteness
theorem (`AlgebraicGeometry.Scheme.IsProjectiveOver.finite_cohomology`) to prove that higher direct
images along locally projective morphisms over locally Noetherian bases preserve coherence (finite
presentation):

* **Scalar linearity over affine bases**
  (`AlgebraicGeometry.Scheme.Hom.higherDirectImageBasicOpenSectionsAddEquiv_smul`,
  `AlgebraicGeometry.Scheme.Modules.cohomologyHigherDirectImageSpecΓLinearEquiv`): for a
  quasi-compact, quasi-separated morphism `f : X ⟶ Spec R` and a quasi-coherent `𝒪_X`-module `M`,
  the global sections `Γ(Spec R, R^q f_* M)` are `R`-linearly isomorphic to the cohomology module
  `H^q(X, M)`.
* **Compatibility with target isomorphisms**
  (`AlgebraicGeometry.Scheme.Hom.higherDirectImageCompIso`): for any morphism `f : X ⟶ Y` and
  isomorphism `e : Y ≅ Z`, restricting `R^q f_*` along `e⁻¹` is naturally isomorphic to
  `R^q (f ≫ e)_*`.
* **Coherence for projective morphisms**:
  `Scheme.IsProjectiveOver.isFinitePresentation_higherDirectImage` and
  `Scheme.Hom.isFinitePresentation_higherDirectImage_of_locally_isProjectiveOver` show that
  if `Y` is locally Noetherian and `f : X ⟶ Y` is projective over an affine open cover of `Y`,
  then for every quasi-coherent `𝒪_X`-module `M` of finite type and every `q : ℕ`, the higher
  direct image `R^q f_* M` is finitely presented (and in particular quasi-coherent and of finite
  type).

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.8.8(b).
* [The Stacks Project, Tag 01Y0 and Section 30.19](https://stacks.math.columbia.edu/tag/02O5).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry.Scheme.Modules

/-! ### Scalar linearity of higher direct images over an affine base -/

/-- The additive equivalence `H^q(f⁻¹ V, M) ≃+ Γ(R^q f_* M, V)` over a basic open `V` of an affine
base `Y` is semilinear with respect to the action of global functions `Γ(Y, ⊤)` via `f^*` on the
left and restriction to `V` on the right. -/
theorem higherDirectImageBasicOpenSectionsAddEquiv_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent]
    (q : ℕ) {V : Y.Opens} (hV : ∃ g : Γ(Y, ⊤), Y.basicOpen g = V) (r : Γ(Y, ⊤))
    (c : cohomologyOn M q (f ⁻¹ᵁ V)) :
    f.higherDirectImageBasicOpenSectionsAddEquiv M q hV (f.appTop r • c) =
      Y.presheaf.map V.leTop.op r • f.higherDirectImageBasicOpenSectionsAddEquiv M q hV c := by
  let e := (f.higherDirectImagePresheafToPresheafIso M q).app (.op V)
  let x : ((f.higherDirectImagePresheaf q).obj M).obj (.op V) := e.inv c
  have hcx : (f.higherDirectImagePresheafToPresheafIso M q).hom.app (.op V) x = c :=
    Iso.inv_hom_id_apply e c
  let rV : Y.ringCatSheaf.obj.obj (.op V) := Y.presheaf.map V.leTop.op r
  have hsmul : (f.higherDirectImagePresheafToPresheafIso M q).hom.app (.op V) (rV • x) =
      f.appTop r • c := by
    rw [← hcx]
    exact f.higherDirectImagePresheafToPresheafIso_hom_app_smul M q r V x
  rw [← hsmul, ← hcx,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app]
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
    ((f.higherDirectImagePresheaf q).obj M)).app (.op V)
  let i := ((f.higherDirectImagePresheafSheafificationIso q).app M).hom.val.app (.op V)
  exact (congrArg i (η.hom.map_smul rV x)).trans (i.hom.map_smul rV (η x))

/-! ### Compatibility of higher direct images with target isomorphisms -/

/-- Restricting the higher direct image `R^q f_*` along the inverse of a target isomorphism
`e : Y ≅ Z` agrees naturally with `R^q (f ≫ e)_*`. -/
def higherDirectImageCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z) (q : ℕ) :
    f.higherDirectImage q ⋙ Scheme.Modules.restrictFunctor e.inv ≅
      (f ≫ e.hom).higherDirectImage q := by
  letI := (Scheme.Modules.pushforward f).additive_of_preserves_binary_products
  letI := (Scheme.Modules.pushforward (f ≫ e.hom)).additive_of_preserves_binary_products
  haveI : (𝟭 X.Modules).PreservesInjectiveObjects := ⟨fun h ↦ h⟩
  let iso : Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor e.inv ≅
      𝟭 X.Modules ⋙ Scheme.Modules.pushforward (f ≫ e.hom) :=
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward f)
        (TauCeti.AlgebraicGeometry.pushforwardIsoRestrictFunctor e).symm ≪≫
      Scheme.Modules.pushforwardComp f e.hom ≪≫
      (Functor.leftUnitor (Scheme.Modules.pushforward (f ≫ e.hom))).symm
  exact Functor.rightDerivedCompIso (Scheme.Modules.pushforward f)
      (Scheme.Modules.restrictFunctor e.inv) (𝟭 X.Modules)
      (Scheme.Modules.pushforward (f ≫ e.hom)) iso q ≪≫
    Functor.leftUnitor _

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry.Scheme.Modules

/-! ### `R`-linear identification of cohomology with global sections of `R^q f_*` over `Spec R` -/

/-- **Cohomology as global sections of the higher direct image over `Spec R`.** For a
quasi-compact, quasi-separated scheme `X` over `Spec R` and a quasi-coherent `𝒪_X`-module `M`,
the cohomology module `H^q(X, M)` is `R`-linearly isomorphic to the global sections of
`R^q (X ↘ Spec R)_* M`. -/
def cohomologyHigherDirectImageSpecΓLinearEquiv {X : Scheme.{u}} (M : X.Modules) (R : Type u)
    [CommRing R] [X.Over (Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [QuasiSeparated (X ↘ Spec (.of R))] [M.IsQuasicoherent] (q : ℕ) :
    Cohomology M q ≃ₗ[R]
      moduleSpecΓFunctor.obj (((X ↘ Spec (.of R)).higherDirectImage q).obj M) := by
  let f := X ↘ Spec (.of R)
  let eRes : cohomologyOn M q ⊤ ≃ₗ[R] cohomologyOn M q (f ⁻¹ᵁ ⊤) := by
    rw [Scheme.Hom.preimage_top f]
  let eTop : Cohomology M q ≃ₗ[R] cohomologyOn M q (f ⁻¹ᵁ ⊤) :=
    (cohomologyOnTopBaseLinearEquiv M R q).symm.trans eRes
  let eRaw := f.higherDirectImageBasicOpenSectionsAddEquiv M q ⟨1, (Spec (.of R)).basicOpen_one⟩
  let eSec : cohomologyOn M q (f ⁻¹ᵁ ⊤) ≃+
      moduleSpecΓFunctor.obj ((f.higherDirectImage q).obj M) := eRaw
  refine eTop.trans { eSec with map_smul' := fun r c ↦ ?_ }
  let r' : Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv r
  let rTop : Γ(Spec (.of R), ⊤) :=
    ((Spec (.of R)).ringCatSheaf.obj.map ((initialOpOfTerminal isTerminalTop).to (.op ⊤))).hom r'
  have h1 : (r : R) • c = f.appTop r' • c := by
    rw [base_smul_cohomologyOn, baseRingToGlobalSections_apply]
  have h2 : (Spec (.of R)).presheaf.map (⊤ : (Spec (.of R)).Opens).leTop.op r' = r' := by
    rw [show (⊤ : (Spec (.of R)).Opens).leTop = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  have h3 : rTop = r' := by
    change ((Spec (.of R)).ringCatSheaf.obj.map
      ((initialOpOfTerminal isTerminalTop).to (.op ⊤))).hom r' = r'
    rw [IsInitial.to_self, CategoryTheory.Functor.map_id]
    rfl
  change eRaw (r • c) = rTop • eRaw c
  rw [h1, h3]
  simpa only [eRaw, h2] using f.higherDirectImageBasicOpenSectionsAddEquiv_smul M q
    ⟨1, (Spec (.of R)).basicOpen_one⟩ r' c

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

open TauCeti.AlgebraicGeometry.Scheme.Modules

/-! ### Coherence of higher direct images along projective morphisms -/

/-- **Coherence of higher direct images over a Noetherian affine base.** Let `R` be a Noetherian
ring and `X` a projective scheme over `Spec R`. For every quasi-coherent `𝒪_X`-module `M` of
finite type and every `q : ℕ`, the higher direct image `R^q (X ↘ Spec R)_* M` is finitely
presented (hence coherent). -/
theorem IsProjectiveOver.isFinitePresentation_higherDirectImage (R : Type u) [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    (((X ↘ Spec (.of R)).higherDirectImage q).obj M).IsFinitePresentation := by
  let f := X ↘ Spec (.of R)
  let G := (f.higherDirectImage q).obj M
  have : G.IsQuasicoherent := f.isQuasicoherent_higherDirectImage M q
  have : Module.Finite R (Cohomology M q) := IsProjectiveOver.finite_cohomology R M q
  have : Module.Finite R (moduleSpecΓFunctor.obj G) :=
    Module.Finite.equiv (M.cohomologyHigherDirectImageSpecΓLinearEquiv R q)
  have : Module.FinitePresentation R (moduleSpecΓFunctor.obj G) :=
    Module.finitePresentation_of_finite R _
  exact (SheafOfModules.isFinitePresentation (Spec (.of R)).ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ G.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G))
    (TauCeti.AlgebraicGeometry.isFinitePresentation_tilde (moduleSpecΓFunctor.obj G))

/-- **Coherence of higher direct images for locally projective morphisms over locally Noetherian
schemes.** Let `f : X ⟶ Y` be a morphism to a locally Noetherian scheme `Y` that is projective over
an affine open cover `{U i}` of `Y`. Then for every quasi-coherent `𝒪_X`-module `M` of finite type
and every `q : ℕ`, the higher direct image `R^q f_* M` is finitely presented (hence coherent). -/
theorem Hom.isFinitePresentation_higherDirectImage_of_locally_isProjectiveOver {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) {ι : Type*} (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : ⨆ i, U i = ⊤)
    (hproj : ∀ i,
      letI : (f ⁻¹ᵁ U i).toScheme.Over (Spec Γ(Y, U i)) := ⟨(f ∣_ U i) ≫ (hU i).isoSpec.hom⟩
      (f ⁻¹ᵁ U i).toScheme.IsProjectiveOver Γ(Y, U i))
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    ((f.higherDirectImage q).obj M).IsFinitePresentation := by
  refine Scheme.Modules.isFinitePresentation_of_isFinitePresentation_restrict _ U hcover fun i ↦ ?_
  let Mi := M.restrict (f ⁻¹ᵁ U i).ι
  have : Mi.IsQuasicoherent := inferInstance
  have : Mi.IsFiniteType := inferInstance
  have : IsNoetherianRing Γ(Y, U i) := IsLocallyNoetherian.component_noetherian ⟨U i, hU i⟩
  let _ : (f ⁻¹ᵁ U i).toScheme.Over (Spec Γ(Y, U i)) := ⟨(f ∣_ U i) ≫ (hU i).isoSpec.hom⟩
  have : (f ⁻¹ᵁ U i).toScheme.IsProjectiveOver Γ(Y, U i) := hproj i
  have hspec : ((((f ∣_ U i) ≫ (hU i).isoSpec.hom).higherDirectImage q).obj
      Mi).IsFinitePresentation :=
    IsProjectiveOver.isFinitePresentation_higherDirectImage Γ(Y, U i) Mi q
  have hres : ((((f ∣_ U i).higherDirectImage q).obj Mi).restrict
      (hU i).isoSpec.inv).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec Γ(Y, U i)).ringCatSheaf).prop_of_iso
      (((f ∣_ U i).higherDirectImageCompIso (hU i).isoSpec q).app Mi).symm hspec
  have hUi : (((f ∣_ U i).higherDirectImage q).obj Mi).IsFinitePresentation :=
    (Scheme.Modules.isFinitePresentation_restrict_iff_of_isIso _ (hU i).isoSpec.inv).mp hres
  exact (SheafOfModules.isFinitePresentation (U i).toScheme.ringCatSheaf).prop_of_iso
    ((f.higherDirectImageRestrictIso (U i) q).app M).symm hUi

end AlgebraicGeometry.Scheme
