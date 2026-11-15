/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Invertible

/-!
# Invertibility and ring inverses

If `2` is a unit in a semiring, zero is the only element that doubles to zero. Over a ring,
`Ring.inverse` commutes with negation (`Ring.inverse_neg`).
-/

public section

open scoped Ring

/-- If `2` is a unit, only zero doubles to zero. -/
theorem IsUnit.eq_zero_of_add_self_eq_zero {R : Type*} [Semiring R] (h2 : IsUnit (2 : R)) :
    ∀ x : R, x + x = 0 → x = 0 := by
  intro x hx
  exact h2.mul_right_eq_zero.mp (by rwa [two_mul])

/-- `Ring.inverse` commutes with negation: `(-a)⁻¹ʳ = -a⁻¹ʳ`, whether or not `a` is a unit. -/
@[simp]
theorem Ring.inverse_neg {R : Type*} [Ring R] (a : R) : (-a)⁻¹ʳ = -a⁻¹ʳ := by
  by_cases ha : IsUnit a
  · obtain ⟨_⟩ := ha.nonempty_invertible
    let _ := invertibleNeg a
    simp [Ring.inverse_invertible]
  · have hna : ¬IsUnit (-a) := fun h ↦ by
      obtain ⟨_⟩ := h.nonempty_invertible
      let _ := invertibleNeg (-a)
      rw [neg_neg] at *
      exact ha (isUnit_of_invertible a)
    simp [Ring.inverse_non_unit, ha, hna]
