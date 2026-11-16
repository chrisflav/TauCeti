/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Serre
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Restrict
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.Modules.Restriction.FinitePresentation

/-!
# Serre's finiteness and coherent higher direct images for projective schemes

Let `R` be a Noetherian commutative ring, `X` a projective scheme over `R`
(`AlgebraicGeometry.Scheme.IsProjectiveOver R X`), and `F` a coherent (quasi-coherent, finite-type)
`𝒪_X`-module. Embedding `X` over `Spec R` as a closed subscheme of a standard projective space
`ℙ^{n+1}_R` (`Scheme.IsProjectiveOver.exists_isClosedImmersion_proj_pi`) and applying Serre's
finiteness theorem on projective space (`Module.Basis.finite_cohomology_of_isFiniteType`) to the
closed-immersion pushforward yields:

* **Serre's finiteness theorem for projective schemes**
  (`AlgebraicGeometry.Scheme.Modules.finite_cohomology_of_isProjectiveOver`,
  `AlgebraicGeometry.Scheme.Modules.finite_globalSections_of_isProjectiveOver`): for every `q : ℕ`,
  `Hᵠ(X, F)` is a finitely generated `R`-module, and in particular `Γ(X, F)` is finite over `R`.
* **Coherence of higher direct images over a Noetherian affine base**
  (`AlgebraicGeometry.Scheme.Hom.isFinitePresentation_higherDirectImage_of_isProjectiveOver`,
  `AlgebraicGeometry.Scheme.Hom.isFiniteType_higherDirectImage_of_isProjectiveOver`,
  `AlgebraicGeometry.Scheme.Hom.isFinitePresentation_pushforward_of_isProjectiveOver`): for every
  `q : ℕ`, the higher direct image `Rᵠ(X ↘ Spec R)_* F` is finitely presented (coherent) on
  `Spec R`, as is the ordinary pushforward `(X ↘ Spec R)_* F`.
* **Coherence of higher direct images for locally projective morphisms**
  (`Scheme.Hom.isFinitePresentation_higherDirectImage_of_locally_isProjectiveOver`): for a
  quasi-compact, quasi-separated morphism `f : X ⟶ Y` into a locally Noetherian scheme `Y`
  whose restriction over every affine open `U ⊆ Y` is projective over `Γ(Y, U)`, every higher
  direct image `Rᵠ f_* F` of a finite-type quasi-coherent sheaf `F` is finitely presented on `Y`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2 and Theorem III.8.8.
* [The Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Serre's finiteness theorem for projective schemes.** For a scheme `X` projective over a
Noetherian ring `R` and a quasi-coherent `𝒪_X`-module `F` of finite type, every cohomology group
`Hᵠ(X, F)` is a finitely generated `R`-module. -/
theorem finite_cohomology_of_isProjectiveOver (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨n, f, hf, hfR⟩ := Scheme.IsProjectiveOver.exists_isClosedImmersion_proj_pi R (X := X)
  have : IsNoetherian
      (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin (n + 2) → R))) :=
    TauCeti.SymmetricAlgebra.instIsNoetherianProj R (Fin (n + 2) → R)
  let fF := (pushforward f).obj F
  have hpf_fp : fF.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pushforward_of_isFinite f F
  have : fF.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation fF
  have : fF.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation fF
  have hfin := (Pi.basisFun R (Fin (n + 2))).finite_cohomology_of_isFiniteType fF q
  exact (f.moduleFinite_cohomology_pushforward_iff R F q).mp hfin

/-- **Finiteness of global sections on projective schemes.** For a scheme `X` projective over a
Noetherian ring `R` and a quasi-coherent `𝒪_X`-module `F` of finite type, the `R`-module of
global sections `Γ(X, F)` is finitely generated. -/
theorem finite_globalSections_of_isProjectiveOver (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    Module.Finite R Γ(F, ⊤) := by
  have := finite_cohomology_of_isProjectiveOver R F 0
  exact Module.Finite.equiv (cohomologyZeroBaseLinearEquiv R X F)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

/-- **Coherence of higher direct images for projective schemes over a Noetherian ring.** For a
scheme `X` projective over a Noetherian ring `R` and a quasi-coherent `𝒪_X`-module `F` of finite
type, every higher direct image `Rᵠ(X ↘ Spec R)_* F` is finitely presented on `Spec R`. -/
theorem isFinitePresentation_higherDirectImage_of_isProjectiveOver
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    (((X ↘ Spec (.of R)).higherDirectImage q).obj F).IsFinitePresentation := by
  have hfin : Module.Finite R (Cohomology F q) :=
    Scheme.Modules.finite_cohomology_of_isProjectiveOver R F q
  let e : Cohomology F q ≃ₗ[R]
      moduleSpecΓFunctor.obj (((X ↘ Spec (.of R)).higherDirectImage q).obj F) :=
    { __ := (X ↘ Spec (.of R)).higherDirectImageTopAddEquiv F q
      map_smul' := fun r x ↦ by
        have htop : (Spec (.of R)).presheaf.map (⊤ : (Spec (.of R)).Opens).leTop.op
            ((Scheme.ΓSpecIso (.of R)).inv r) = (Scheme.ΓSpecIso (.of R)).inv r := by
          -- The inclusion of `⊤` into itself is the identity, so restriction acts trivially.
          rw [show (⊤ : (Spec (.of R)).Opens).leTop = 𝟙 _ from rfl, op_id,
            CategoryTheory.Functor.map_id]
          rfl
        have hr : (X ↘ Spec (.of R)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) =
            baseRingToGlobalSections R X r := (baseRingToGlobalSections_apply R X r).symm
        -- Unfold the `R`-action on `moduleSpecΓFunctor.obj _` to the `Γ(Spec R, ⊤)`-action.
        change (X ↘ Spec (.of R)).higherDirectImageTopAddEquiv F q (r • x) =
          ((Spec (.of R)).presheaf.map (⊤ : (Spec (.of R)).Opens).leTop.op
            ((Scheme.ΓSpecIso (.of R)).inv r)) •
              (X ↘ Spec (.of R)).higherDirectImageTopAddEquiv F q x
        rw [base_smul_cohomology, htop, ← hr,
          (X ↘ Spec (.of R)).higherDirectImageTopAddEquiv_smul F q] }
  have : Module.Finite R
      (moduleSpecΓFunctor.obj (((X ↘ Spec (.of R)).higherDirectImage q).obj F)) :=
    Module.Finite.equiv e
  exact (Scheme.Modules.isFinitePresentation_iff_finitePresentation_moduleSpecΓ
    (((X ↘ Spec (.of R)).higherDirectImage q).obj F)).mpr
      (Module.finitePresentation_of_finite R _)

/-- For a scheme `X` projective over a Noetherian ring `R` and a quasi-coherent `𝒪_X`-module `F` of
finite type, every higher direct image `Rᵠ(X ↘ Spec R)_* F` is of finite type on `Spec R`. -/
theorem isFiniteType_higherDirectImage_of_isProjectiveOver
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    (((X ↘ Spec (.of R)).higherDirectImage q).obj F).IsFiniteType := by
  have := isFinitePresentation_higherDirectImage_of_isProjectiveOver R F q
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
    (((X ↘ Spec (.of R)).higherDirectImage q).obj F)

/-- For a scheme `X` projective over a Noetherian ring `R` and a quasi-coherent `𝒪_X`-module `F` of
finite type, the pushforward `(X ↘ Spec R)_* F` is finitely presented on `Spec R`. -/
theorem isFinitePresentation_pushforward_of_isProjectiveOver
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ((Scheme.Modules.pushforward (X ↘ Spec (.of R))).obj F).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation (Spec (.of R)).ringCatSheaf).prop_of_iso
    (((X ↘ Spec (.of R)).higherDirectImageZeroIso).app F)
    (isFinitePresentation_higherDirectImage_of_isProjectiveOver R F 0)

/-- **Coherence of higher direct images for locally projective morphisms.** Let `f : X ⟶ Y` be a
quasi-compact, quasi-separated morphism into a locally Noetherian scheme `Y` whose preimage over
every affine open `U ⊆ Y` is projective over `Γ(Y, U)`. Then for every quasi-coherent `𝒪_X`-module
`F` of finite type and every `q : ℕ`, the higher direct image `Rᵠ f_* F` is finitely presented on
`Y`. -/
theorem isFinitePresentation_higherDirectImage_of_locally_isProjectiveOver
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hproj : ∀ U : Y.affineOpens,
      letI : (f ⁻¹ᵁ U.1).toScheme.Over (Spec Γ(Y, U.1)) := ⟨(f ∣_ U.1) ≫ U.2.isoSpec.hom⟩
      (f ⁻¹ᵁ U.1).toScheme.IsProjectiveOver Γ(Y, U.1))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    ((f.higherDirectImage q).obj F).IsFinitePresentation := by
  refine Scheme.Modules.isFinitePresentation_of_isFinitePresentation_restrict
    ((f.higherDirectImage q).obj F) (fun U : Y.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top Y) fun U ↦ ?_
  have : IsAffine U.1.toScheme := U.2
  have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(U.1.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩
  let g := f ∣_ U.1
  let FU := F.restrict (f ⁻¹ᵁ U.1).ι
  let _ : U.1.toScheme.Over (Spec Γ(Y, U.1)) := ⟨U.2.isoSpec.hom⟩
  let _ : (f ⁻¹ᵁ U.1).toScheme.Over (Spec Γ(Y, U.1)) := ⟨g ≫ U.2.isoSpec.hom⟩
  have : g.IsOver (Spec Γ(Y, U.1)) := ⟨rfl⟩
  have : (f ⁻¹ᵁ U.1).toScheme.IsProjectiveOver Γ(Y, U.1) := hproj U
  have hfin : Module.Finite Γ(Y, U.1) (Cohomology FU q) :=
    Scheme.Modules.finite_cohomology_of_isProjectiveOver Γ(Y, U.1) FU q
  let N := (g.higherDirectImage q).obj FU
  have hΓN_R : Module.Finite Γ(Y, U.1) Γ(N, ⊤) :=
    Module.Finite.equiv (g.higherDirectImageTopBaseLinearEquiv FU q Γ(Y, U.1))
  let _ : Algebra Γ(Y, U.1) Γ(U.1.toScheme, ⊤) :=
    (baseRingToGlobalSections Γ(Y, U.1) U.1.toScheme).toAlgebra
  have : IsScalarTower Γ(Y, U.1) Γ(U.1.toScheme, ⊤) Γ(N, ⊤) :=
    ⟨fun r s x ↦ by
      rw [Algebra.smul_def, base_smul_globalSections, mul_smul]
      rfl⟩
  have : Module.Finite Γ(U.1.toScheme, ⊤) Γ(N, ⊤) :=
    Module.Finite.of_restrictScalars_finite Γ(Y, U.1) Γ(U.1.toScheme, ⊤) Γ(N, ⊤)
  have hN_fp : N.IsFinitePresentation :=
    (Scheme.Modules.isFinitePresentation_iff_finitePresentation_globalSections_of_isAffine N).mpr
      (Module.finitePresentation_of_finite _ _)
  exact (SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf).prop_of_iso
    ((f.higherDirectImageRestrictIso U.1 q).app F).symm hN_fp

end AlgebraicGeometry.Scheme.Hom
