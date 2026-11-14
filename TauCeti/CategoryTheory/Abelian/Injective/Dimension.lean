/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-!
# Comparing injective dimensions, and global projective-injective symmetry

If every bound `HasInjectiveDimensionLT X n` on one object implies the same bound on another
object `Y`, possibly in a different abelian category, then the injective dimension of `Y` is at
most that of `X`. Along an adjunction `F ⊣ G` between abelian categories in which `F` preserves
finite limits and `G` preserves finite colimits (so both functors are exact and additive), `F`
preserves projective dimension bounds and `G` preserves injective dimension bounds via
`CategoryTheory.Adjunction.extEquiv`; in particular, any equivalence of abelian categories
preserves injective dimension.

Because `HasProjectiveDimensionLT` and `HasInjectiveDimensionLT` are both defined by the vanishing
of `Ext X Y i` in degrees `i ≥ n`, a uniform bound on all projective dimensions in an abelian
category is equivalent to the same uniform bound on all injective dimensions, without assuming
enough projectives or enough injectives. Consequently the global projective dimension
`⨆ X : C, projectiveDimension X` coincides with `⨆ Y : C, injectiveDimension Y`.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 4.1 (global dimension).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- If every bound on the injective dimension of `X` is also a bound for `Y`, then the injective
dimension of `Y` is at most that of `X`. The objects may lie in different abelian categories. -/
theorem injectiveDimension_le_of_hasInjectiveDimensionLT {D : Type u'} [Category.{v'} D] [Abelian D]
    {X : C} {Y : D}
    (h : ∀ n : ℕ, HasInjectiveDimensionLT X n → HasInjectiveDimensionLT Y n) :
    injectiveDimension Y ≤ injectiveDimension X :=
  sInf_le_sInf fun _ hd i hi ↦ h i (hd i hi)

section Adjunction

variable {D : Type u'} [Category.{v'} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- Along an adjunction `F ⊣ G` between abelian categories with `F` left exact and `G` right exact,
the left adjoint `F` preserves projective dimension bounds. -/
theorem Adjunction.hasProjectiveDimensionLT
    [PreservesFiniteLimits F] [PreservesFiniteColimits G]
    (adj : F ⊣ G) {X : C} {n : ℕ} (hX : HasProjectiveDimensionLT X n) :
    HasProjectiveDimensionLT (F.obj X) n := by
  have : F.IsLeftAdjoint := adj.isLeftAdjoint
  have : G.IsRightAdjoint := adj.isRightAdjoint
  have := F.additive_of_preserves_binary_products
  have := G.additive_of_preserves_binary_products
  let := HasExt.standard C
  let := HasExt.standard D
  rw [hasProjectiveDimensionLT_iff] at hX ⊢
  intro i hi Y e
  exact adj.extEquiv.injective (by rw [map_zero]; exact hX i hi _)

/-- Along an adjunction `F ⊣ G` between abelian categories with `F` left exact and `G` right exact,
the right adjoint `G` preserves injective dimension bounds. -/
theorem Adjunction.hasInjectiveDimensionLT
    [PreservesFiniteLimits F] [PreservesFiniteColimits G]
    (adj : F ⊣ G) {Y : D} {n : ℕ} (hY : HasInjectiveDimensionLT Y n) :
    HasInjectiveDimensionLT (G.obj Y) n := by
  have : F.IsLeftAdjoint := adj.isLeftAdjoint
  have : G.IsRightAdjoint := adj.isRightAdjoint
  have := F.additive_of_preserves_binary_products
  have := G.additive_of_preserves_binary_products
  let := HasExt.standard C
  let := HasExt.standard D
  rw [hasInjectiveDimensionLT_iff] at hY ⊢
  intro i hi X e
  exact adj.extEquiv.symm.injective (by rw [map_zero]; exact hY i hi _)

/-- **Injective dimension bounds are invariant under an equivalence.** The object `e.functor.obj X`
has injective dimension `< n` if and only if `X` does. -/
@[simp]
theorem Equivalence.hasInjectiveDimensionLT_functor_obj_iff (e : C ≌ D) (X : C) (n : ℕ) :
    HasInjectiveDimensionLT (e.functor.obj X) n ↔ HasInjectiveDimensionLT X n := by
  refine ⟨fun h ↦ ?_, e.symm.toAdjunction.hasInjectiveDimensionLT⟩
  have : HasInjectiveDimensionLT ((e.functor ⋙ e.inverse).obj X) n :=
    e.toAdjunction.hasInjectiveDimensionLT h
  exact hasInjectiveDimensionLT_of_iso (e.unitIso.app X).symm n

/-- **An equivalence of abelian categories preserves injective dimension.** -/
@[simp]
theorem Equivalence.injectiveDimension_functor_obj (e : C ≌ D) (X : C) :
    injectiveDimension (e.functor.obj X) = injectiveDimension X :=
  le_antisymm
    (injectiveDimension_le_of_hasInjectiveDimensionLT fun n ↦
      (e.hasInjectiveDimensionLT_functor_obj_iff X n).mpr)
    (injectiveDimension_le_of_hasInjectiveDimensionLT fun n ↦
      (e.hasInjectiveDimensionLT_functor_obj_iff X n).mp)

end Adjunction

section GlobalSymmetry

variable (C)

/-- **Uniform projective- and injective-dimension bounds agree.** Every object of an abelian
category has projective dimension `< n` if and only if every object has injective dimension `< n`,
since both conditions state that `Ext X Y i = 0` for all `X`, `Y` and all `i ≥ n`. -/
theorem forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT (n : ℕ) :
    (∀ X : C, HasProjectiveDimensionLT X n) ↔ ∀ Y : C, HasInjectiveDimensionLT Y n := by
  let := HasExt.standard C
  simp only [hasProjectiveDimensionLT_iff, hasInjectiveDimensionLT_iff]
  exact ⟨fun h Y i hi X e ↦ h X i hi e, fun h X i hi Y e ↦ h Y i hi e⟩

/-- Every object of an abelian category has projective dimension `≤ n` if and only if every object
has injective dimension `≤ n`. -/
theorem forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE (n : ℕ) :
    (∀ X : C, HasProjectiveDimensionLE X n) ↔ ∀ Y : C, HasInjectiveDimensionLE Y n :=
  forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT C (n + 1)

private theorem iSup_projectiveDimension_le_iff (d : WithBot ℕ∞) :
    (⨆ X : C, projectiveDimension X) ≤ d ↔ (⨆ Y : C, injectiveDimension Y) ≤ d := by
  rw [iSup_le_iff, iSup_le_iff]
  induction d using WithBot.recBotCoe with
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff, injectiveDimension_eq_bot_iff]
  | coe d =>
    induction d with
    | top =>
      exact ⟨fun _ _ ↦ le_top, fun _ _ ↦ le_top⟩
    | coe n =>
      exact (forall_congr' fun X ↦ projectiveDimension_le_iff X n).trans
        ((forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE C n).trans
          (forall_congr' fun Y ↦ (injectiveDimension_le_iff Y n).symm))

/-- **Global dimension symmetry.** In any abelian category, the supremum of all projective
dimensions equals the supremum of all injective dimensions. -/
theorem iSup_projectiveDimension_eq_iSup_injectiveDimension :
    (⨆ X : C, projectiveDimension X) = ⨆ Y : C, injectiveDimension Y :=
  le_antisymm ((iSup_projectiveDimension_le_iff C _).mpr le_rfl)
    ((iSup_projectiveDimension_le_iff C _).mp le_rfl)

end GlobalSymmetry

end CategoryTheory
