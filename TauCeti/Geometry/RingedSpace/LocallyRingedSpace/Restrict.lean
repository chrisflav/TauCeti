/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.Restrict

/-!
# Inclusions between restrictions of a locally ringed space to nested opens

For opens `V ≤ W` of a locally ringed space `X`, the restriction of `X` to `V` includes into its
restriction to `W` as an open immersion, compatibly with the open immersions into `X`. This lifts
`AlgebraicGeometry.PresheafedSpace.restrictHomOfLE` to `LocallyRingedSpace` and provides the
locally-ringed-space counterpart of Mathlib's `AlgebraicGeometry.Scheme.homOfLE`.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE`: the open immersion `X|_V ⟶ X|_W` for
  `V ≤ W`.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_restrictHomOfLE`: `restrictHomOfLE` is an
  open immersion.
* `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE_ofRestrict`: composing with `X|_W ⟶ X`
  gives `X|_V ⟶ X`.
* `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE_refl`,
  `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE_comp`: functoriality of the inclusions.
-/

public section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

variable (X : LocallyRingedSpace.{u})

/-- For opens `V ≤ W` of `X`, the open-immersion inclusion of the restriction of `X` to `V` into
its restriction to `W`. The body is exposed so that the base map and sheaf components reduce to
those of `PresheafedSpace.restrictHomOfLE`. -/
@[expose]
def restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding where
  toHom := X.toPresheafedSpace.restrictHomOfLE h
  prop x := by
    have := PresheafedSpace.IsOpenImmersion.stalk_iso (X.toPresheafedSpace.restrictHomOfLE h) x
    exact isLocalHom_of_isIso ((X.toPresheafedSpace.restrictHomOfLE h).stalkMap x)

/-- The underlying morphism of presheafed spaces of `LocallyRingedSpace.restrictHomOfLE` is
`PresheafedSpace.restrictHomOfLE`. -/
@[simp]
theorem restrictHomOfLE_toHom {V W : Opens X} (h : V ≤ W) :
    (X.restrictHomOfLE h).toHom = X.toPresheafedSpace.restrictHomOfLE h :=
  (rfl)

/-- On underlying topological spaces, `restrictHomOfLE` is the inclusion of `V` into `W`. -/
theorem restrictHomOfLE_base {V W : Opens X} (h : V ≤ W) :
    (X.restrictHomOfLE h).base = (Opens.toTopCat X.toTopCat).map (homOfLE h) :=
  (rfl)

/-- The inclusion `X|_V ⟶ X|_W` is an open immersion of locally ringed spaces. -/
instance isOpenImmersion_restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    IsOpenImmersion (X.restrictHomOfLE h) :=
  inferInstanceAs (PresheafedSpace.IsOpenImmersion (X.toPresheafedSpace.restrictHomOfLE h))

/-- The inclusion `X|_V ⟶ X|_W` followed by `X|_W ⟶ X` is `X|_V ⟶ X`. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_ofRestrict {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding :=
  Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_ofRestrict h)

/-- The inclusion of a restriction into itself is the identity. -/
@[simp]
theorem restrictHomOfLE_refl (V : Opens X) :
    X.restrictHomOfLE (le_refl V) = 𝟙 (X.restrict V.isOpenEmbedding) :=
  Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_refl V)

/-- Inclusions between restrictions to nested opens compose. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_comp {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    X.restrictHomOfLE h ≫ X.restrictHomOfLE k = X.restrictHomOfLE (h.trans k) :=
  Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_comp h k)

end AlgebraicGeometry.LocallyRingedSpace
