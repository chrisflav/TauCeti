/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation distance and eventwise excess on countable spaces

For two finite measures on a countable space with measurable singletons, total variation
distance is the sum of the absolute differences of their singleton masses. We give the extended
and real formulas, together with summability of the real series. No probability normalization
is required, and the formulas also cover the empty space.

We also compute the largest one-sided eventwise excess `⨆ (A) (_ : MeasurableSet A), μ A - ν A`
on any countable space with measurable singletons: for arbitrary measures `μ` and `ν` (not
necessarily finite), it equals `∑' x, (μ {x} - ν {x})`, where subtraction is truncated in `ℝ≥0∞`.
The set `{x | ν {x} < μ {x}}` attains this excess whenever `ν` is finite, and for arbitrary
measures on a finite type.

These identities identify total variation distance between distributions on a countable state
space with the ℓ¹ distance of their point masses. We use Mathlib's normalization: the distance
between probability measures is at most two, not one.

The total variation proofs use Mathlib's `VectorMeasure.variation_apply_singleton` and the
decomposition of a measure into its singleton masses, rather than constructing a separate discrete
distance.

## References

* D. A. Levin and Y. Peres, with contributions by E. L. Wilmer, *Markov Chains and Mixing Times*,
  second edition, American Mathematical Society, 2017, Proposition 4.2 and Remark 4.3, p. 48.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

section Countable

variable [Countable α]

/-- On a countable space with measurable singletons, the largest eventwise excess of `μ` over `ν`
is the sum of the truncated singleton differences `μ {x} - ν {x}`. No finiteness assumption on `μ`
or `ν` is required. -/
theorem iSup_measure_sub_eq_tsum_singleton (μ ν : Measure α) :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑' x, (μ {x} - ν {x}) := by
  classical
  apply le_antisymm
  · refine iSup₂_le fun A hA => tsub_le_iff_left.2 ?_
    rw [← μ.tsum_indicator_apply_singleton A hA, ← ν.tsum_indicator_apply_singleton A hA,
      ← tsum_add]
    refine tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ A
    · simp [hx, le_add_tsub]
    · simp [hx]
  · rw [tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    let t : Finset α := s.filter fun x => ν {x} < μ {x}
    have hsum_eq : ∑ x ∈ s, (μ {x} - ν {x}) = ∑ x ∈ t, (μ {x} - ν {x}) := by
      refine (Finset.sum_filter_of_ne fun x _ hx => ?_).symm
      exact tsub_pos_iff_lt.1 (pos_iff_ne_zero.2 hx)
    have hνt_ne_top : ν (t : Set α) ≠ ⊤ := by
      rw [← sum_measure_singleton, ENNReal.sum_ne_top]
      exact fun x hx => ne_top_of_lt (Finset.mem_filter.1 hx).2
    have hsplit : μ (t : Set α) = ν (t : Set α) + ∑ x ∈ t, (μ {x} - ν {x}) := by
      rw [← sum_measure_singleton, ← sum_measure_singleton, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x hx =>
        (add_tsub_cancel_of_le (Finset.mem_filter.1 hx).2.le).symm
    have hsub : μ (t : Set α) - ν (t : Set α) = ∑ x ∈ t, (μ {x} - ν {x}) := by
      rw [hsplit, ENNReal.add_sub_cancel_left hνt_ne_top]
    rw [hsum_eq, ← hsub]
    exact le_iSup₂ (f := fun (A : Set α) (_ : MeasurableSet A) => μ A - ν A)
      (t : Set α) t.measurableSet

private theorem measure_lt_eq_add_tsum_sub (μ ν : Measure α) :
    μ {x | ν {x} < μ {x}} = ν {x | ν {x} < μ {x}} + ∑' x, (μ {x} - ν {x}) := by
  let P : Set α := {x | ν {x} < μ {x}}
  have hP : MeasurableSet P := (Set.to_countable P).measurableSet
  rw [← μ.tsum_indicator_apply_singleton P hP, ← ν.tsum_indicator_apply_singleton P hP, ← tsum_add]
  congr 1
  ext x
  by_cases hx : ν {x} < μ {x}
  · simp [P, hx, add_tsub_cancel_of_le hx.le]
  · simp [P, hx, tsub_eq_zero_of_le (not_lt.1 hx)]

/-- On a countable space with measurable singletons, if `ν` is finite then the set
`{x | ν {x} < μ {x}}` attains the largest eventwise excess of `μ` over `ν`. -/
theorem measure_sub_lt_eq_tsum_singleton (μ ν : Measure α) [IsFiniteMeasure ν] :
    μ {x | ν {x} < μ {x}} - ν {x | ν {x} < μ {x}} = ∑' x, (μ {x} - ν {x}) := by
  rw [measure_lt_eq_add_tsum_sub, ENNReal.add_sub_cancel_left (measure_ne_top ν _)]

variable {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- On a countable space, extended total variation distance is the sum of the extended norms
of the differences of singleton masses. -/
theorem etvDist_eq_tsum_enorm_singleton :
    etvDist μ ν = ∑' x, ‖μ.real {x} - ν.real {x}‖ₑ := by
  rw [etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist]
  rw [← (μ.toSignedMeasure - ν.toSignedMeasure).variation.tsum_indicator_apply_singleton
    Set.univ MeasurableSet.univ]
  simp [VectorMeasure.variation_apply_singleton, Measure.toSignedMeasure_apply]

/-- The absolute differences of singleton masses of two finite measures form a summable family
on a countable space. -/
theorem summable_abs_measureReal_singleton_sub :
    Summable (fun x => |μ.real {x} - ν.real {x}|) := by
  have h := ENNReal.summable_toReal (etvDist_eq_tsum_enorm_singleton (μ := μ) (ν := ν) ▸
    etvDist_ne_top μ ν)
  simpa using h

/-- On a countable space, total variation distance is the ℓ¹ distance of the singleton masses.
In particular, no factor of one half occurs with Mathlib's normalization. -/
theorem tvDist_eq_tsum_abs_singleton :
    tvDist μ ν = ∑' x, |μ.real {x} - ν.real {x}| := by
  rw [tvDist, etvDist_eq_tsum_enorm_singleton, ENNReal.tsum_toReal_eq (by simp)]
  simp

end Countable

section Fintype

variable [Fintype α]

/-- On a finite type with measurable singletons, the largest eventwise excess of `μ` over `ν`
is the finite sum `∑ x, (μ {x} - ν {x})`. -/
theorem iSup_measure_sub_eq_sum_singleton (μ ν : Measure α) :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑ x, (μ {x} - ν {x}) := by
  rw [iSup_measure_sub_eq_tsum_singleton, tsum_fintype]

/-- On a finite type with measurable singletons, the set `{x | ν {x} < μ {x}}` attains the largest
eventwise excess of `μ` over `ν`, for arbitrary (not necessarily finite) measures `μ` and `ν`. -/
theorem measure_sub_lt_eq_sum_singleton (μ ν : Measure α) :
    μ {x | ν {x} < μ {x}} - ν {x | ν {x} < μ {x}} = ∑ x, (μ {x} - ν {x}) := by
  let P : Set α := {x | ν {x} < μ {x}}
  have hP : MeasurableSet P := (Set.to_countable P).measurableSet
  have hνP : ν P ≠ ⊤ := by
    rw [← ν.tsum_indicator_apply_singleton P hP, tsum_fintype, ENNReal.sum_ne_top]
    intro x _
    by_cases hx : ν {x} < μ {x}
    · simpa [P, hx] using ne_top_of_lt hx
    · simp [P, hx]
  rw [measure_lt_eq_add_tsum_sub, tsum_fintype, ENNReal.add_sub_cancel_left hνP]

end Fintype

end MeasureTheory
