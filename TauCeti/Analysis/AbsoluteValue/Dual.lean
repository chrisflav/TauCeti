/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.Linarith
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Sup-norm bounds for dual bases under an absolute value

Given a real-valued absolute value `w` on a field `F` and a linearly independent family
`l : ι → Module.Dual F (ι → F)` on a finite-dimensional coordinate space, the forms `l i` span
`Module.Dual F (ι → F)` and therefore express every coordinate projection as a linear combination
of the `l i`. Applying the triangle inequality bounds the `w`-sup norm `⨆ j, w (x j)` of every
vector `x : ι → F` by a positive constant times `⨆ i, w (l i x)`
(`AbsoluteValue.exists_pos_forall_iSup_le_mul_iSup_apply`).
-/

public section

open Module

namespace AbsoluteValue

/-- A linearly independent family `l : ι → Module.Dual F (ι → F)` spans the dual space, so for any
real-valued absolute value `w` on `F` the sup norm `⨆ j, w (x j)` is bounded by a positive constant
times `⨆ i, w (l i x)`. -/
theorem exists_pos_forall_iSup_le_mul_iSup_apply {F ι : Type*} [Field F] [Finite ι]
    (w : AbsoluteValue F ℝ) {l : ι → Dual F (ι → F)} (hl : LinearIndependent F l) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ι → F, ⨆ j, w (x j) ≤ C * ⨆ i, w (l i x) := by
  have : Fintype ι := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with _ | _
  · exact ⟨1, one_pos, fun x ↦ by simp⟩
  · obtain ⟨a, ha⟩ := hl.exists_sum_smul_eq_proj
    set C : ℝ := 1 + ∑ j, ∑ i, w (a j i)
    have hC : 0 < C := by
      have h0 : 0 ≤ ∑ j, ∑ i, w (a j i) :=
        Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ w.nonneg _
      linarith
    refine ⟨C, hC, fun x ↦ ciSup_le fun j ↦ ?_⟩
    have hxj : x j = ∑ i, a j i * l i x := by
      simpa using (LinearMap.congr_fun (ha j) x).symm
    have hsum : ∑ i, w (a j i) ≤ C := by
      have h1 : ∑ i, w (a j i) ≤ ∑ j', ∑ i, w (a j' i) :=
        Finset.single_le_sum (f := fun j' ↦ ∑ i, w (a j' i))
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ w.nonneg _) (Finset.mem_univ j)
      linarith
    calc w (x j)
        = w (∑ i, a j i * l i x) := congrArg w hxj
      _ ≤ ∑ i, w (a j i * l i x) := w.sum_le _ _
      _ = ∑ i, w (a j i) * w (l i x) := by simp [map_mul]
      _ ≤ ∑ i, w (a j i) * ⨆ k, w (l k x) :=
          Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
            (le_ciSup (f := fun k ↦ w (l k x)) (Finite.bddAbove_range _) i) (w.nonneg _)
      _ = (∑ i, w (a j i)) * ⨆ k, w (l k x) := (Finset.sum_mul ..).symm
      _ ≤ C * ⨆ k, w (l k x) :=
          mul_le_mul_of_nonneg_right hsum (Real.iSup_nonneg fun _ ↦ w.nonneg _)

end AbsoluteValue
