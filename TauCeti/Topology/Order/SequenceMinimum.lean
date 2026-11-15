/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field

/-!
# Attainment of sequence minima and minimizing sequences for infima

A sequence bounded below by a sequence converging to `c` attains its minimum if it has values at
most `c` arbitrarily far out (`Filter.Tendsto.exists_minimum_of_lower_bound`). This allows a
converging lower barrier to certify attainment without requiring convergence of the sequence itself.

When a function `f` into an ordered topological space with continuous addition is bounded below on
`s : Set X` (`BddBelow (f '' s)`), any family eventually in `s` whose values eventually exceed
`sInf (f '' s)` by at most `ε i → 0` converges in value to `sInf (f '' s)`
(`TauCeti.tendsto_csInf_of_le_csInf_add`). For `f : X → ℝ` bounded below on a nonempty set `s`,
there exists a minimizing sequence `u` in `s` with `f (u n) < sInf (f '' s) + 1 / (n + 1)`
(`TauCeti.exists_seq_lt_csInf_add_one_div`).

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
-/

public section

open Filter Set
open scoped Topology

namespace Filter.Tendsto

/-- A sequence above a convergent lower barrier attains its minimum, with value at
most the barrier's limit, provided it has values at most that limit frequently. -/
theorem exists_minimum_of_lower_bound {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] {a b : ℕ → α} {c : α}
    (hb : Tendsto b atTop (𝓝 c)) (hba : ∀ n, b n ≤ a n)
    (ha : ∃ᶠ n in atTop, a n ≤ c) :
    ∃ n, a n ≤ c ∧ ∀ m, a n ≤ a m := by
  classical
  by_cases h : ∀ n, c ≤ a n
  · obtain ⟨n, hn⟩ := ha.exists
    exact ⟨n, hn, fun m => hn.trans (h m)⟩
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have htail : ∀ᶠ n in atTop, a i < a n :=
      (hb.eventually (eventually_gt_nhds hi)).mono fun n hn => hn.trans_le (hba n)
    obtain ⟨N, hN⟩ := eventually_atTop.1 htail
    obtain ⟨k, _, hmin⟩ := Set.exists_min_image (Set.Iic (max N i)) a (Set.finite_Iic _)
      ⟨i, le_max_right N i⟩
    refine ⟨k, (hmin i (le_max_right N i)).trans hi.le, fun m => ?_⟩
    by_cases hm : m ≤ max N i
    · exact hmin m hm
    · exact (hmin i (le_max_right N i)).trans (hN m (by omega)).le

end Filter.Tendsto

namespace TauCeti

/-- If `f` is bounded below on `s` (`BddBelow (f '' s)`), any family eventually in `s` whose values
eventually exceed `sInf (f '' s)` by at most `ε i → 0` satisfies `f (u i) → sInf (f '' s)`. -/
theorem tendsto_csInf_of_le_csInf_add {ι X β : Type*} [ConditionallyCompleteLattice β]
    [TopologicalSpace β] [OrderTopology β] [AddZeroClass β] [ContinuousAdd β] {l : Filter ι}
    {f : X → β} {s : Set X} (hbdd : BddBelow (f '' s)) {u : ι → X} (hu : ∀ᶠ i in l, u i ∈ s)
    {ε : ι → β} (hε : Tendsto ε l (𝓝 0)) (hle : ∀ᶠ i in l, f (u i) ≤ sInf (f '' s) + ε i) :
    Tendsto (fun i ↦ f (u i)) l (𝓝 (sInf (f '' s))) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (hu.mono fun _ hi ↦ csInf_le hbdd (mem_image_of_mem f hi)) hle
  simpa only [add_zero] using tendsto_const_nhds.add hε

/-- Every nonempty set on which a real-valued function is bounded below admits a minimizing
sequence `u n ∈ s` with `f (u n) < sInf (f '' s) + 1 / (n + 1)` and `f (u n) → sInf (f '' s)`. -/
theorem exists_seq_lt_csInf_add_one_div {X : Type*} {f : X → ℝ} {s : Set X}
    (hne : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧
      (∀ n, f (u n) < sInf (f '' s) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s))) := by
  have hex (n : ℕ) : ∃ x ∈ s, f x < sInf (f '' s) + 1 / ((n : ℝ) + 1) := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt (hne.image f) (lt_add_of_pos_right _ (one_div_pos.2 n.cast_add_one_pos))
    exact ⟨x, hx, hlt⟩
  choose u hu hlt using hex
  have hε : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div, Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat 1).2
        ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tendsto_natCast_atTop_atTop)
  exact ⟨u, hu, hlt, tendsto_csInf_of_le_csInf_add hbdd (.of_forall hu) hε
    (.of_forall fun n ↦ (hlt n).le)⟩

end TauCeti
