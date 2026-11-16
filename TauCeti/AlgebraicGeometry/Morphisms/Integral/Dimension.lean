/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.Topology.KrullDimension.Basic

/-!
# Dimension under integral morphisms

An integral morphism `f : X ⟶ Y` of schemes is affine, and over every affine open `U ⊆ Y` the
pullback on sections `Γ(Y, U) ⟶ Γ(X, f ⁻¹ U)` is an integral ring homomorphism. By incomparability
and going-up for integral ring extensions (`TauCeti.ringKrullDim_le_of_isIntegral` and
`TauCeti.ringKrullDim_le_of_hasGoingUp_of_surjective`), an integral morphism never increases Krull
dimension, and if it is surjective — in particular, if it is dominant, since integral morphisms are
closed — it preserves Krull dimension. No reducedness, finiteness, Noetherianity or base-field
hypothesis is needed.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_le_of_isIntegralHom`: an integral morphism
  satisfies `dim X ≤ dim Y`.
* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_of_isIntegralHom_of_surjective`: a
  surjective integral morphism preserves Krull dimension.
* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_of_isIntegralHom_of_isDominant`: a
  dominant integral morphism preserves Krull dimension (without reducedness on the target).

## References

* [Stacks Project, Lemma 29.44.9](https://stacks.math.columbia.edu/tag/02JW) and
  [Lemma 10.112.1](https://stacks.math.columbia.edu/tag/00OK) (going-up and incomparability for
  integral extensions).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}}

/-- The Krull dimension of an affine open `U` equals the Krull dimension of its ring of sections. -/
private lemma topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen {Z : Scheme.{u}} {U : Z.Opens}
    (hU : IsAffineOpen U) :
    topologicalKrullDim (U : Set Z) = ringKrullDim Γ(Z, U) :=
  (hU.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq).trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)

/-- The Krull dimension of the source of a morphism is the supremum of the Krull dimensions of the
preimages of the affine opens of the target. -/
private lemma topologicalKrullDim_eq_iSup_preimage_affineOpens (f : X ⟶ Y) :
    topologicalKrullDim X = ⨆ U : Y.affineOpens, topologicalKrullDim (f ⁻¹ᵁ U.1 : Set X) :=
  TauCeti.topologicalKrullDim_eq_iSup_of_isOpenEmbedding
    (fun U : Y.affineOpens ↦ (Subtype.val : (f ⁻¹ᵁ U.1 : Set X) → X))
    (fun U ↦ (f ⁻¹ᵁ U.1).isOpen.isOpenEmbedding_subtypeVal) fun x ↦ by
      obtain ⟨U, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (by rw [iSup_affineOpens_eq_top]; trivial : f x ∈ ⨆ U : Y.affineOpens, U.1)
      exact ⟨U, ⟨x, hy⟩, rfl⟩

/-- For a surjective affine morphism `f : X ⟶ Y` and an affine open `U` of `Y`, the induced map
`Spec Γ(X, f ⁻¹ U) ⟶ Spec Γ(Y, U)` on prime spectra is surjective. -/
private lemma comap_app_surjective (f : X ⟶ Y) [IsAffineHom f] [Surjective f]
    (U : Y.affineOpens) :
    Function.Surjective (PrimeSpectrum.comap (f.app U).hom) := by
  intro p
  obtain ⟨x, hx⟩ := f.surjective (U.2.fromSpec p)
  have hxU : x ∈ f ⁻¹ᵁ U.1 := by
    change f x ∈ U.1
    rw [hx]
    exact U.2.range_fromSpec.subset ⟨p, rfl⟩
  obtain ⟨q, hq⟩ := (U.2.preimage f).range_fromSpec.symm.subset hxU
  have hcomm := IsAffineOpen.SpecMap_appLE_fromSpec f U.2 (U.2.preimage f) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hcomm
  refine ⟨q, ?_⟩
  have hfeq : U.2.fromSpec (Spec.map (f.app U) q) = U.2.fromSpec p := by
    simpa [Scheme.Hom.comp_apply, hq, hx] using congr($hcomm q)
  have hinj : Function.Injective U.2.fromSpec := by
    rw [← U.2.isoSpec_inv_ι]
    exact U.1.ι.isOpenEmbedding.injective.comp (Scheme.Hom.homeomorph U.2.isoSpec.inv).injective
  exact hinj hfeq

/-- **Dimension does not increase along an integral morphism.** For an integral morphism
`f : X ⟶ Y`, `dim X ≤ dim Y`. -/
theorem topologicalKrullDim_le_of_isIntegralHom (f : X ⟶ Y) [IsIntegralHom f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_iSup_preimage_affineOpens f,
    topologicalKrullDim_eq_iSup_preimage_affineOpens (𝟙 Y)]
  refine iSup_mono fun U ↦ ?_
  rw [show (𝟙 Y ⁻¹ᵁ U.1 : Y.Opens) = U.1 from rfl,
    topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen (U.2.preimage f),
    topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen U.2]
  let _ : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : Algebra.IsIntegral Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := ⟨f.isIntegral_app U U.2⟩
  exact TauCeti.ringKrullDim_le_of_isIntegral

/-- **Surjective integral morphisms preserve Krull dimension.** For a surjective integral morphism
`f : X ⟶ Y`, `dim X = dim Y`. -/
theorem topologicalKrullDim_eq_of_isIntegralHom_of_surjective (f : X ⟶ Y)
    [IsIntegralHom f] [Surjective f] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_iSup_preimage_affineOpens f,
    topologicalKrullDim_eq_iSup_preimage_affineOpens (𝟙 Y)]
  refine iSup_congr fun U ↦ ?_
  rw [show (𝟙 Y ⁻¹ᵁ U.1 : Y.Opens) = U.1 from rfl,
    topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen (U.2.preimage f),
    topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen U.2]
  let _ : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : Algebra.IsIntegral Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := ⟨f.isIntegral_app U U.2⟩
  exact TauCeti.ringKrullDim_le_of_isIntegral.antisymm
    (TauCeti.ringKrullDim_le_of_hasGoingUp_of_surjective (comap_app_surjective f U))

/-- **Dominant integral morphisms preserve Krull dimension.** For an integral dominant morphism
`f : X ⟶ Y`, `dim X = dim Y`. Because integral morphisms are closed, dominance implies surjectivity,
so no reducedness hypothesis on `Y` is needed. -/
theorem topologicalKrullDim_eq_of_isIntegralHom_of_isDominant (f : X ⟶ Y)
    [IsIntegralHom f] [IsDominant f] :
    topologicalKrullDim X = topologicalKrullDim Y :=
  have : Surjective f := Surjective.of_universallyClosed_of_isDominant f
  f.topologicalKrullDim_eq_of_isIntegralHom_of_surjective

end AlgebraicGeometry.Scheme.Hom
