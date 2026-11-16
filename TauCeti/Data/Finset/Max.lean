/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max

/-!
# Extremal selections on finite sets

This file provides two order-selection principles on finite sets:

* `Finset.exists_last_min_image`: a function on a nonempty finite linearly ordered set has a last
  minimizer, whose value is minimal on the set and strictly smaller than its value at every later
  point. This is used for the last vertex of minimal height in Littelmann root operators
  (`TauCeti.exists_strictly_rising_of_isAChain`).
* `Finset.exists_subset_card_eq_forall_le` and `Finset.exists_subset_card_eq_forall_ge`: any
  finite set `s` of cardinality at least `n` has an `n`-element subset on which a function `f` to a
  linear order takes its `n` smallest (or `n` largest) values.
-/

public section

namespace Finset

/-- A function on a nonempty finite linearly ordered set attains its minimum at a last point.
Every later point of the set has strictly larger value. -/
theorem exists_last_min_image {α β : Type*} [LinearOrder α] [LinearOrder β]
    (s : Finset α) (f : α → β) (hs : s.Nonempty) :
    ∃ a ∈ s, (∀ b ∈ s, f a ≤ f b) ∧ ∀ b ∈ s, a < b → f a < f b := by
  classical
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image f hs
  let t := s.filter fun b ↦ f b = f a
  have ht : t.Nonempty := ⟨a, mem_filter.mpr ⟨ha, rfl⟩⟩
  have hlast := mem_filter.mp (t.max'_mem ht)
  refine ⟨t.max' ht, hlast.1, ?_, ?_⟩
  · intro b hb
    rw [hlast.2]
    exact hmin b hb
  · intro b hb hab
    rw [hlast.2]
    refine lt_of_le_of_ne (hmin b hb) fun h ↦ ?_
    exact hab.not_ge (t.le_max' b (mem_filter.mpr ⟨hb, h.symm⟩))

/-- Any finite set `s` of cardinality at least `n` contains an `n`-element subset `t` on which a
function `f` to a linear order takes its `n` smallest values: `f a ≤ f b` whenever `a ∈ t` and
`b ∈ s \ t`. -/
theorem exists_subset_card_eq_forall_le {α β : Type*} [LinearOrder β] (s : Finset α)
    (f : α → β) {n : ℕ} (hn : n ≤ s.card) :
    ∃ t ⊆ s, t.card = n ∧ ∀ a ∈ t, ∀ b ∈ s, b ∉ t → f a ≤ f b := by
  classical
  induction n with
  | zero => exact ⟨∅, empty_subset s, card_empty, fun _ ha ↦ (notMem_empty _ ha).elim⟩
  | succ k ih =>
    obtain ⟨t, hts, hcard, hle⟩ := ih (Nat.le_of_succ_le hn)
    have hne : (s \ t).Nonempty := by
      rw [← card_pos, card_sdiff_of_subset hts, hcard]
      omega
    obtain ⟨m, hm, hmin⟩ := (s \ t).exists_min_image f hne
    rw [mem_sdiff] at hm
    refine ⟨insert m t, insert_subset hm.1 hts, by rw [card_insert_of_notMem hm.2, hcard], ?_⟩
    intro a ha b hb hbt
    have hb' : b ∈ s \ t := mem_sdiff.mpr ⟨hb, fun h ↦ hbt (mem_insert_of_mem h)⟩
    rcases mem_insert.mp ha with rfl | hat
    · exact hmin b hb'
    · exact hle a hat b hb (mem_sdiff.mp hb').2

/-- Any finite set `s` of cardinality at least `n` contains an `n`-element subset `t` on which a
function `f` to a linear order takes its `n` largest values: `f b ≤ f a` whenever `a ∈ t` and
`b ∈ s \ t`. -/
theorem exists_subset_card_eq_forall_ge {α β : Type*} [LinearOrder β] (s : Finset α)
    (f : α → β) {n : ℕ} (hn : n ≤ s.card) :
    ∃ t ⊆ s, t.card = n ∧ ∀ a ∈ t, ∀ b ∈ s, b ∉ t → f b ≤ f a :=
  exists_subset_card_eq_forall_le (β := βᵒᵈ) s f hn

end Finset
