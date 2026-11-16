/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

/-!
# Projective schemes over a ring

A scheme `X` over `Spec R` is *projective over `R`* if it is a closed subscheme, over `R`, of the
projective spectrum `Proj (Sym_R M)` of the symmetric algebra of a finite `R`-module `M`. Mathlib
has no class of projective morphisms, so this file records projectivity over an affine base as a
predicate on schemes over `Spec R`.

Over an affine base this is the usual notion: a finite `R`-module `M` is a quotient of some `Rⁿ`,
so `Proj (Sym_R M)` is itself a closed subscheme of `Proj (Sym_R Rⁿ) = ℙⁿ⁻¹_R`, and the definition
agrees with Hartshorne's (a closed subscheme of some `ℙⁿ_R`). Over a field `k` every finite module
is a finite-dimensional vector space, so `Proj (Sym_k M)` is a projective space over `k`.

A projective scheme over `R` is proper over `R`, because closed immersions are proper and
`Proj (Sym_R M)` is proper over `R` for finite `M`
(`TauCeti.SymmetricAlgebra.instIsProperProjToSpec`).

## Main definitions

* `AlgebraicGeometry.Scheme.IsProjectiveOver R X`: the scheme `X` over `Spec R` is a closed
  subscheme, over `R`, of `Proj (Sym_R M)` for some finite `R`-module `M`.

## Main results

* `AlgebraicGeometry.Scheme.IsProjectiveOver.of_isClosedImmersion`: a closed subscheme over `R` of
  a projective scheme over `R` is projective over `R`.
* `AlgebraicGeometry.Scheme.exists_isClosedImmersion_proj_of_surjective`: a surjective `R`-linear
  map `N →ₗ[R] M` induces a closed immersion `Proj (Sym_R M) ⟶ Proj (Sym_R N)` over `Spec R`.
* `AlgebraicGeometry.Scheme.IsProjectiveOver.exists_isClosedImmersion_proj_pi`: every projective
  scheme over `R` embeds over `R` as a closed subscheme of `Proj (Sym_R (Fin (n + 2) → R))`.
* the instance `(Proj (Sym_R M)).IsProjectiveOver R` for a finite `R`-module `M`.
* the instance `IsProper (X ↘ Spec R)` for `X` projective over `R`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.4 (definition of a
  projective morphism before Theorem II.4.9).
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]

/-- A scheme `X` over `Spec R` is *projective over `R`* if it is a closed subscheme, over `R`, of
the projective spectrum `Proj (Sym_R M)` of the symmetric algebra of a finite `R`-module `M`. -/
class IsProjectiveOver : Prop where
  /-- There is a closed immersion over `R` into `Proj (Sym_R M)` for a finite `R`-module `M`. -/
  exists_isClosedImmersion : ∃ (M : Type u) (_ : AddCommMonoid M) (_ : Module R M)
    (_ : Module.Finite R M) (f : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M)),
    IsClosedImmersion f ∧ f.IsOver (Spec (.of R))

/-- The projective spectrum of the symmetric algebra of a finite `R`-module is projective
over `R`. -/
instance isProjectiveOver_proj (M : Type u) [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M)).IsProjectiveOver R :=
  ⟨⟨M, inferInstance, inferInstance, inferInstance, 𝟙 _, inferInstance, inferInstance⟩⟩

/-- A closed subscheme over `R` of a projective scheme over `R` is projective over `R`. -/
theorem IsProjectiveOver.of_isClosedImmersion {Y : Scheme.{u}} [Y.Over (Spec (.of R))]
    [Y.IsProjectiveOver R] (f : X ⟶ Y) [IsClosedImmersion f] [f.IsOver (Spec (.of R))] :
    X.IsProjectiveOver R := by
  obtain ⟨M, _, _, _, g, hg, hgR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := Y)
  exact ⟨⟨M, inferInstance, inferInstance, inferInstance, f ≫ g, inferInstance, inferInstance⟩⟩

/-- **A projective scheme is proper**: a scheme projective over `R` is proper over `R`. -/
instance IsProjectiveOver.isProper [X.IsProjectiveOver R] : IsProper (X ↘ Spec (.of R)) := by
  obtain ⟨M, _, _, _, f, hf, hfR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  rw [← comp_over f (Spec (.of R))]
  infer_instance

/-- A surjective `R`-linear map `g : M →ₗ[R] N` induces a closed immersion
`Proj (Sym_R N) ⟶ Proj (Sym_R M)` over `Spec R`. -/
theorem exists_isClosedImmersion_proj_of_surjective {M N : Type u}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (g : M →ₗ[R] N) (hg : Function.Surjective g) :
    ∃ f : Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R N) ⟶
        Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M),
      IsClosedImmersion f ∧ f.IsOver (Spec (.of R)) := by
  let φ := _root_.SymmetricAlgebra.gradedMap R g
  have hφ_surj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := _root_.SymmetricAlgebra.map_surjective R g hg y
    exact ⟨x, (_root_.SymmetricAlgebra.gradedMap_apply R g x).trans hx⟩
  have hirrel : HomogeneousIdeal.irrelevant (TauCeti.SymmetricAlgebra.homogeneousSubmodule R N) ≤
      (HomogeneousIdeal.irrelevant (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M)).map φ :=
    HomogeneousIdeal.irrelevant_le_map_of_surjective φ hφ_surj
  refine ⟨Proj.map φ hirrel, Proj.isClosedImmersion_map φ hirrel hφ_surj, ⟨?_⟩⟩
  rw [TauCeti.SymmetricAlgebra.over_eq_projToSpec, TauCeti.SymmetricAlgebra.over_eq_projToSpec,
    TauCeti.SymmetricAlgebra.projToSpec_def, TauCeti.SymmetricAlgebra.projToSpec_def,
    Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, GradedRingHom.gradedZeroRingHom_apply_coe,
    SetLike.GradeZero.coe_algebraMap, φ, _root_.SymmetricAlgebra.gradedMap_apply,
    AlgHom.commutes]

/-- Every projective scheme over `R` embeds over `Spec R` as a closed subscheme of a standard
projective space `Proj (Sym_R (Fin (n + 2) → R))` of positive dimension. -/
theorem IsProjectiveOver.exists_isClosedImmersion_proj_pi [X.IsProjectiveOver R] :
    ∃ (n : ℕ)
      (f : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin (n + 2) → R))),
      IsClosedImmersion f ∧ f.IsOver (Spec (.of R)) := by
  obtain ⟨M, _, _, hMfin, f, hf, hfR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let w : Fin (n + 2) → M := fun i ↦ if h : i.1 < n then v ⟨i.1, h⟩ else 0
  have hw_span : Submodule.span R (Set.range w) = ⊤ := by
    refine top_unique ?_
    rw [← hv]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨i.1, by omega⟩, ?_⟩
    simp [w, i.2]
  have hsurj : Function.Surjective (Fintype.linearCombination R w) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hw_span]
  obtain ⟨j, hj, hjR⟩ := exists_isClosedImmersion_proj_of_surjective R
    (Fintype.linearCombination R w) hsurj
  exact ⟨n, f ≫ j, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
