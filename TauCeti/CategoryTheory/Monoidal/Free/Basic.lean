/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic

/-!
# Port length of formal tensor words

`CategoryTheory.FreeMonoidalCategory.length` counts the generating-object ports in a formal
parenthesized tensor word, ignoring inserted monoidal units and parenthesization. A single
generator has length `1`, the monoidal unit has length `0`, and tensoring adds lengths.

Morphisms in `FreeMonoidalCategory` (associators and unitors) preserve `length`
(`FreeMonoidalCategory.length_eq_of_hom`). In particular, tensoring with the formal unit does not
introduce a strand, and formal words of different port counts are not isomorphic in the structural
category.
-/

public section

universe u v

open CategoryTheory MonoidalCategory

namespace CategoryTheory.FreeMonoidalCategory

variable {α : Type u} {β : Type v}

/-- The number of generating-object ports in a formal tensor word. Units contribute `0` and
tensor products add port counts. -/
def length : FreeMonoidalCategory α → ℕ
  | .of _ => 1
  | .unit => 0
  | .tensor X Y => length X + length Y

@[simp]
theorem length_of (a : α) : (of a).length = 1 := (rfl)

@[simp]
theorem length_tensorUnit : (𝟙_ (FreeMonoidalCategory α)).length = 0 := (rfl)

@[simp]
theorem length_tensorObj (X Y : FreeMonoidalCategory α) :
    (X ⊗ Y).length = X.length + Y.length := (rfl)

/-- Every morphism of the object-generated free monoidal category preserves port length. -/
theorem length_eq_of_hom {X Y : FreeMonoidalCategory α} (f : X ⟶ Y) :
    X.length = Y.length := by
  induction f using Hom.inductionOn with
  | id => rfl
  | α_hom X Y Z => exact Nat.add_assoc X.length Y.length Z.length
  | α_inv X Y Z => exact (Nat.add_assoc X.length Y.length Z.length).symm
  | l_hom X => exact Nat.zero_add X.length
  | l_inv X => exact (Nat.zero_add X.length).symm
  | ρ_hom X => exact Nat.add_zero X.length
  | ρ_inv X => exact (Nat.add_zero X.length).symm
  | comp _ _ hf hg => exact hf.trans hg
  | whiskerLeft Z _ hf => exact congrArg (Z.length + ·) hf
  | whiskerRight _ Z hf => exact congrArg (· + Z.length) hf

/-- Interpreting each generator as a word of constant port length `k` scales the port length of
every word by `k`. -/
theorem length_projectObj_const {f : α → FreeMonoidalCategory β} {k : ℕ}
    (hf : ∀ a, (f a).length = k) (X : FreeMonoidalCategory α) :
    (projectObj f X).length = X.length * k := by
  induction X with
  | of a => simp [projectObj, hf a]
  | unit => simp [projectObj]
  | tensor X Y ihX ihY => simp [projectObj, ihX, ihY, Nat.add_mul]

end CategoryTheory.FreeMonoidalCategory
