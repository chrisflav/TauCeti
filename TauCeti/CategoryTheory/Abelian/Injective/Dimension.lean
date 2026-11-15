/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Global symmetry of projective and injective dimension, and injective copresentations

In any abelian category `C`, a uniform bound `HasProjectiveDimensionLT X n` on every object `X`
is equivalent to the same uniform bound `HasInjectiveDimensionLT Y n` on every object `Y`: both
conditions assert that `Ext^i(X, Y)` is a subsingleton for all `X`, `Y` and all `i ≥ n`, with the
two universal object quantifiers exchanged. No existence of projectives, injectives, or small `Ext`
universe is required, since both predicates are defined in `HasExt.standard C`. Consequently the
supremum of projective dimensions over `C` agrees with the supremum of injective dimensions.

When `C` has enough injectives, the chosen monomorphism `Injective.ι X : X ⟶ Injective.under X`
into an injective object fits into the short exact sequence
`0 ⟶ X ⟶ Injective.under X ⟶ cokernel (Injective.ι X) ⟶ 0`
(`CategoryTheory.Injective.cokernelShortComplex_shortExact`), the dual of
`CategoryTheory.Projective.kernelShortComplex_shortExact`.

## Main definitions

* `CategoryTheory.Injective.cokernelShortComplex`: the short complex `X ⟶ I ⟶ coker ι` of the
  chosen injective presentation `ι : X ⟶ I`.

## Main results

* `CategoryTheory.injectiveDimension_le_of_hasInjectiveDimensionLT`: degreewise transfer of
  injective-dimension bounds implies `injectiveDimension Y ≤ injectiveDimension X`.
* `CategoryTheory.forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT` and
  `CategoryTheory.forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE`: uniform
  projective-dimension bounds across an abelian category coincide with uniform injective-dimension
  bounds.
* `CategoryTheory.iSup_projectiveDimension_eq_iSup_injectiveDimension`: the global projective and
  global injective dimensions of an abelian category coincide.
* `CategoryTheory.Injective.cokernelShortComplex_shortExact`: the chosen injective copresentation
  short complex is short exact.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 4.1 (global dimension via Ext).
* M. Auslander, *On the dimension of modules and algebras III. Global dimension*, Nagoya Math. J.
  **9** (1955), 67–77.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- If every bound on the injective dimension of `X` is also a bound for `Y`, then the injective
dimension of `Y` is at most that of `X`. The objects may lie in different abelian categories. -/
theorem injectiveDimension_le_of_hasInjectiveDimensionLT {D : Type*} [Category* D] [Abelian D]
    {X : C} {Y : D}
    (h : ∀ n : ℕ, HasInjectiveDimensionLT X n → HasInjectiveDimensionLT Y n) :
    injectiveDimension Y ≤ injectiveDimension X :=
  sInf_le_sInf fun _ hd i hi ↦ h i (hd i hi)

variable (C) in
/-- **Global symmetry of homological dimension (`< n`).** Every object of an abelian category has
projective dimension `< n` if and only if every object has injective dimension `< n`: both say
that all `Ext` groups in degrees `≥ n` vanish. -/
theorem forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT (n : ℕ) :
    (∀ X : C, HasProjectiveDimensionLT X n) ↔ (∀ Y : C, HasInjectiveDimensionLT Y n) := by
  let := HasExt.standard C
  simp only [hasProjectiveDimensionLT_iff.{max u v}, hasInjectiveDimensionLT_iff.{max u v}]
  exact ⟨fun h Y i hi X e ↦ h X i hi e, fun h X i hi Y e ↦ h Y i hi e⟩

variable (C) in
/-- **Global symmetry of homological dimension (`≤ n`).** Every object of an abelian category has
projective dimension `≤ n` if and only if every object has injective dimension `≤ n`. -/
theorem forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE (n : ℕ) :
    (∀ X : C, HasProjectiveDimensionLE X n) ↔ (∀ Y : C, HasInjectiveDimensionLE Y n) :=
  forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT C (n + 1)

variable (C) in
/-- **Global projective and injective dimensions coincide.** In any abelian category, the supremum
of projective dimensions over all objects equals the supremum of injective dimensions. -/
theorem iSup_projectiveDimension_eq_iSup_injectiveDimension :
    (⨆ X : C, projectiveDimension X) = ⨆ Y : C, injectiveDimension Y := by
  refine eq_of_forall_ge_iff fun d ↦ ?_
  induction d with
  | bot =>
    simp only [le_bot_iff, iSup_eq_bot, projectiveDimension_eq_bot_iff,
      injectiveDimension_eq_bot_iff]
  | coe d =>
    induction d with
    | top => simp
    | coe n =>
      simpa [iSup_le_iff, projectiveDimension_le_iff, injectiveDimension_le_iff] using
        forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE C n

section EnoughInjectives

variable [EnoughInjectives C]

/-- The short complex `X ⟶ I ⟶ coker ι` of the chosen injective presentation `ι : X ⟶ I`. -/
noncomputable abbrev Injective.cokernelShortComplex (X : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι X) (cokernel.π (Injective.ι X)) (cokernel.condition _)

/-- The chosen injective presentation `0 ⟶ X ⟶ I ⟶ coker ι ⟶ 0` is short exact. -/
theorem Injective.cokernelShortComplex_shortExact (X : C) :
    (Injective.cokernelShortComplex X).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }

instance (X : C) : Injective (Injective.cokernelShortComplex X).X₂ :=
  inferInstanceAs (Injective (Injective.under X))

end EnoughInjectives

end CategoryTheory
