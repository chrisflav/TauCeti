/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Field.Basic

/-!
# Positive and negative parts of a balanced sum

When a finite sum in a linearly ordered additive commutative group is zero, its total negative
part equals its total positive part, and twice its total positive part equals the sum of absolute
values. This expresses the balance of supply and demand and the total-variation identity for two
families of equal sum without requiring an Archimedean property or order completeness.
-/

public section

namespace Finset

section OrderedAddCommGroup

variable {ι K : Type*} [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]

/-- A balanced finite family has equal total negative and positive parts. -/
theorem sum_max_neg_eq_sum_max (s : Finset ι) (b : ι → K) (hb : ∑ v ∈ s, b v = 0) :
    ∑ v ∈ s, max (-b v) 0 = ∑ v ∈ s, max (b v) 0 := by
  have h : (∑ v ∈ s, max (b v) 0) - ∑ v ∈ s, max (-b v) 0 = 0 := by
    rw [← sum_sub_distrib]
    simpa only [max_zero_sub_max_neg_zero_eq_self] using hb
  exact (sub_eq_zero.1 h).symm

/-- Twice the total positive part of a balanced finite family equals the sum of absolute values. -/
theorem two_nsmul_sum_max_eq_sum_abs (s : Finset ι) (b : ι → K) (hb : ∑ v ∈ s, b v = 0) :
    2 • ∑ v ∈ s, max (b v) 0 = ∑ v ∈ s, |b v| := by
  calc 2 • ∑ v ∈ s, max (b v) 0
      = (∑ v ∈ s, max (b v) 0) + ∑ v ∈ s, max (-b v) 0 := by
          rw [two_nsmul, s.sum_max_neg_eq_sum_max b hb]
    _ = ∑ v ∈ s, |b v| := by
          rw [← sum_add_distrib]
          exact sum_congr rfl fun v _ ↦ max_zero_add_max_neg_zero_eq_abs_self (b v)

/-- Two finite families with the same sum have equal total positive parts of `g - f` and `f - g`. -/
theorem sum_max_sub_eq_sum_max_sub (s : Finset ι) {f g : ι → K}
    (hfg : ∑ v ∈ s, f v = ∑ v ∈ s, g v) :
    ∑ v ∈ s, max (g v - f v) 0 = ∑ v ∈ s, max (f v - g v) 0 := by
  simpa only [neg_sub] using
    s.sum_max_neg_eq_sum_max (fun v ↦ f v - g v) (by rw [sum_sub_distrib, hfg, sub_self])

end OrderedAddCommGroup

/-- Total-variation identity: when two finite families in a linearly ordered field have the same
sum, the total positive part of `f - g` equals half their `L¹`-distance. -/
theorem sum_max_sub_eq_sum_abs_sub_div_two {ι K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (s : Finset ι) {f g : ι → K} (hfg : ∑ v ∈ s, f v = ∑ v ∈ s, g v) :
    ∑ v ∈ s, max (f v - g v) 0 = (∑ v ∈ s, |f v - g v|) / 2 := by
  have h2 := s.two_nsmul_sum_max_eq_sum_abs (fun v ↦ f v - g v)
    (by rw [sum_sub_distrib, hfg, sub_self])
  rw [two_nsmul, ← two_mul] at h2
  exact (eq_div_iff two_ne_zero).2 (by rw [mul_comm, h2])

end Finset
