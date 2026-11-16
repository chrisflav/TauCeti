/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.Probability.PopulationSampling.Finite
import TauCeti.Probability.PopulationSampling.Map
import TauCeti.Probability.PopulationSampling.OnePair

/-!
# Sampling discrepancy for populations with repeated values

For a finite population `x : κ → α` of size `n = Fintype.card κ` sampled `m = Fintype.card ι`
times, the collision probability `1 - p` with `p = n.descFactorial m / n ^ m` bounds the eventwise
discrepancy between sampling without and with replacement (`sampleWithoutReplacement` and
`sampleWithReplacement`), and is attained when `x` takes distinct values.

This file proves that repeated values strictly lower the discrepancy for `2 ≤ m ≤ n`, and
characterizes equality. Whenever `x` is not injective, two distinct indices `a ≠ b` share a value,
so `x` factors through the one-pair population `Function.update id b a`. Combining the pushforward
contraction of `TauCeti.Probability.PopulationSampling.Map` with the exact one-pair formula of
`TauCeti.Probability.PopulationSampling.OnePair` bounds both one-sided excesses by
`ENNReal.ofReal (1 - p - t * min p (1 - p))` and Mathlib's total variation distance `etvDist` by
twice that quantity, where `t = m.descFactorial 2 / n.descFactorial 2`. These bounds require no
separation or singleton hypotheses on the value space `α` and hold for all `m` and `n` (when
`n < m`, the without-replacement law is zero, `p = 0`, and the bound evaluates to `1`).

For `2 ≤ m ≤ n`, the reduction `t * min p (1 - p)` is strictly positive, so every non-injective
population has discrepancy strictly below the collision probability `1 - p` (and `etvDist` strictly
below `2 * (1 - p)`). Together with the attainment theorems for distinct-valued populations in
`TauCeti.Probability.PopulationSampling.Distinct` and `TauCeti.Probability.PopulationSampling.Map`,
this characterizes injectivity of `x` as equality in the collision bound, either under explicit
measurability of the all-distinct event `{f : ι → α | Function.Injective f}` or under
`[MeasurableSingletonClass α]`. For `m ≤ 1`, the two sampling laws already coincide for every
population law (`sampleWithoutReplacement_eq_sampleWithReplacement_of_card_le_one`).

## Main declarations

* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective`,
  `iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective`: both
  one-sided excesses of a non-injective deterministic population are bounded by
  `ENNReal.ofReal (1 - p - t * min p (1 - p))`;
* `sampleWithoutReplacement_dirac_le_sampleWithReplacement_add_of_not_injective`,
  `sampleWithReplacement_dirac_le_sampleWithoutReplacement_add_of_not_injective`: the corresponding
  eventwise bounds for arbitrary (not necessarily measurable) sets;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective`: the extended
  total variation distance is at most twice that bound;
* `descFactorial_div_mul_min_pos`, `ofReal_one_sub_descFactorial_div_pow_sub_lt`: for
  `2 ≤ m ≤ n`, the reduction `t * min p (1 - p)` is strictly positive, so the repeated-value bound
  is strictly below the collision probability `1 - p`;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective`: strict
  inequalities below the collision bound for every non-injective population when `2 ≤ m ≤ n`;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff`,
  `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff_of_measurableSet`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff_of_measurableSet`:
  for `2 ≤ m ≤ n`, attaining the collision discrepancy characterizes injective populations.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

section RepeatedBounds

variable {ι κ α : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSpace α]

/-- **Repeated-value sampling discrepancy, without-over-with excess.** If `x : κ → α` is not
injective, the largest eventwise excess of sampling `x` without replacement over sampling `x` with
replacement is at most `ENNReal.ofReal (1 - p - t * min p (1 - p))`, where
`p = |κ|.descFactorial |ι| / |κ| ^ |ι|` and `t = |ι|.descFactorial 2 / |κ|.descFactorial 2`.
No separation or singleton hypothesis on `α` and no ordering between `|ι|` and `|κ|` is needed. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A) ≤
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  obtain ⟨a, b, hxab, hab⟩ := Function.not_injective_iff.1 hx
  rcases le_or_gt (Fintype.card ι) (Fintype.card κ) with hmn | hnm
  · classical
    exact (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_update_id hxab).trans_eq
      (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn)
  · have : IsEmpty (ι ↪ κ) := ⟨fun e => hnm.not_ge (Fintype.card_le_of_injective e e.injective)⟩
    rw [sampleWithoutReplacement_eq_zero_of_isEmpty]
    simp

/-- **Repeated-value sampling discrepancy, with-over-without excess.** If `x : κ → α` is not
injective, the largest eventwise excess of sampling `x` with replacement over sampling `x` without
replacement is at most `ENNReal.ofReal (1 - p - t * min p (1 - p))`, where
`p = |κ|.descFactorial |ι| / |κ| ^ |ι|` and `t = |ι|.descFactorial 2 / |κ|.descFactorial 2`.
No separation or singleton hypothesis on `α` and no ordering between `|ι|` and `|κ|` is needed. -/
theorem iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithReplacement (Measure.dirac x) A -
          sampleWithoutReplacement (Measure.dirac x) A) ≤
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  obtain ⟨a, b, hxab, hab⟩ := Function.not_injective_iff.1 hx
  rcases le_or_gt (Fintype.card ι) (Fintype.card κ) with hmn | hnm
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
    classical
    exact (iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_update_id e
      hxab).trans_eq
      (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn)
  · have : IsEmpty (ι ↪ κ) := ⟨fun e => hnm.not_ge (Fintype.card_le_of_injective e e.injective)⟩
    let : Nonempty (ι → κ) := ⟨fun _ => a⟩
    let := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac x)
    rw [sampleWithoutReplacement_eq_zero_of_isEmpty]
    simp only [Nat.descFactorial_eq_zero_iff_lt.2 hnm, Nat.cast_zero, zero_div, sub_zero,
      min_eq_left zero_le_one, mul_zero, ENNReal.ofReal_one, FunLike.coe_zero, Pi.zero_apply,
      tsub_zero]
    exact iSup₂_le fun _ _ => prob_le_one

/-- **Repeated-value eventwise bound, without replacement to with replacement.** For any set `A`
(not necessarily measurable) and any non-injective population `x : κ → α`, sampling `x` without
replacement exceeds sampling `x` with replacement on `A` by at most
`ENNReal.ofReal (1 - p - t * min p (1 - p))`. -/
theorem sampleWithoutReplacement_dirac_le_sampleWithReplacement_add_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) (A : Set (ι → α)) :
    sampleWithoutReplacement (Measure.dirac x) A ≤
      sampleWithReplacement (Measure.dirac x) A +
        ENNReal.ofReal
          (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
              (Fintype.card κ : ℝ) ^ Fintype.card ι
           let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
           1 - p - t * min p (1 - p)) :=
  measure_le_add_of_iSup_sub_le
    (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective hx) A

/-- **Repeated-value eventwise bound, with replacement to without replacement.** For any set `A`
(not necessarily measurable) and any non-injective population `x : κ → α`, sampling `x` with
replacement exceeds sampling `x` without replacement on `A` by at most
`ENNReal.ofReal (1 - p - t * min p (1 - p))`. -/
theorem sampleWithReplacement_dirac_le_sampleWithoutReplacement_add_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) (A : Set (ι → α)) :
    sampleWithReplacement (Measure.dirac x) A ≤
      sampleWithoutReplacement (Measure.dirac x) A +
        ENNReal.ofReal
          (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
              (Fintype.card κ : ℝ) ^ Fintype.card ι
           let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
           1 - p - t * min p (1 - p)) :=
  measure_le_add_of_iSup_sub_le
    (iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective hx) A

/-- **Repeated-value sampling discrepancy, total-variation form.** If `x : κ → α` is not injective,
Mathlib's extended total variation distance between sampling `x` without and with replacement is at
most `2 * ENNReal.ofReal (1 - p - t * min p (1 - p))`. No separation or singleton hypothesis on `α`
and no ordering between `|ι|` and `|κ|` is needed. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) ≤
      2 * ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  rw [two_mul]
  exact etvDist_le_of_forall_le_add
    (fun A _ => sampleWithoutReplacement_dirac_le_sampleWithReplacement_add_of_not_injective hx A)
    (fun A _ => sampleWithReplacement_dirac_le_sampleWithoutReplacement_add_of_not_injective hx A)

end RepeatedBounds

section Strictness

/-- For `2 ≤ m ≤ n`, the one-pair tie reduction `t * min p (1 - p)` is strictly positive, where
`p = n.descFactorial m / n ^ m` and `t = m.descFactorial 2 / n.descFactorial 2`. -/
theorem descFactorial_div_mul_min_pos {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    0 < (let p : ℝ := n.descFactorial m / (n : ℝ) ^ m
         let t : ℝ := m.descFactorial 2 / n.descFactorial 2
         t * min p (1 - p)) := by
  have hn2 : 2 ≤ n := hm.trans hmn
  have hn0 : n ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hpow_pos : (0 : ℝ) < (n : ℝ) ^ m := pow_pos hn_pos m
  have hp_pos : (0 : ℝ) < n.descFactorial m / (n : ℝ) ^ m :=
    div_pos (by exact_mod_cast Nat.descFactorial_pos.2 hmn) hpow_pos
  have hp_lt : (n.descFactorial m : ℝ) / (n : ℝ) ^ m < 1 :=
    (div_lt_one hpow_pos).2 (by exact_mod_cast Nat.descFactorial_lt_pow hn0 hm)
  have ht_pos : (0 : ℝ) < m.descFactorial 2 / n.descFactorial 2 :=
    div_pos (by exact_mod_cast Nat.descFactorial_pos.2 hm)
      (by exact_mod_cast Nat.descFactorial_pos.2 hn2)
  exact mul_pos ht_pos (lt_min hp_pos (sub_pos.2 hp_lt))

/-- For `2 ≤ m ≤ n`, the repeated-value excess bound `ENNReal.ofReal (1 - p - t * min p (1 - p))`
is strictly smaller than the collision probability `1 - n.descFactorial m / n ^ m`. -/
theorem ofReal_one_sub_descFactorial_div_pow_sub_lt {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    ENNReal.ofReal
        (let p : ℝ := n.descFactorial m / (n : ℝ) ^ m
         let t : ℝ := m.descFactorial 2 / n.descFactorial 2
         1 - p - t * min p (1 - p)) <
      1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m := by
  have hn0 : n ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hpow_pos : (0 : ℝ) < (n : ℝ) ^ m := pow_pos hn_pos m
  set p : ℝ := n.descFactorial m / (n : ℝ) ^ m
  have hp_nonneg : 0 ≤ p := by positivity
  have hp_lt : p < 1 :=
    (div_lt_one hpow_pos).2 (by exact_mod_cast Nat.descFactorial_lt_pow hn0 hm)
  have h1p : 1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m = ENNReal.ofReal (1 - p) := by
    rw [ENNReal.ofReal_sub 1 hp_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos hpow_pos]
    simp
  rw [h1p, ENNReal.ofReal_lt_ofReal_iff (sub_pos.2 hp_lt)]
  exact sub_lt_self _ (descFactorial_div_mul_min_pos hm hmn)

end Strictness

section Characterization

variable {ι κ α : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSpace α]

/-- For `2 ≤ |ι| ≤ |κ|`, every non-injective population has largest sampling excess strictly below
the collision probability `1 - |κ|.descFactorial |ι| / |κ| ^ |ι|`, with no hypothesis on `α`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x)
    (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A) <
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι :=
  (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective hx).trans_lt
    (ofReal_one_sub_descFactorial_div_pow_sub_lt hm hmn)

/-- For `2 ≤ |ι| ≤ |κ|`, every non-injective population has extended total variation distance
strictly below twice the collision probability, with no hypothesis on `α`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x)
    (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) <
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) :=
  (etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective hx).trans_lt
    (ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top
      (ofReal_one_sub_descFactorial_div_pow_sub_lt hm hmn))

/-- **Characterization of distinct populations, excess form.** For `2 ≤ |ι| ≤ |κ|` and a value
space with measurable singletons, the largest excess of sampling `x` without replacement over
sampling `x` with replacement equals the collision probability
`1 - |κ|.descFactorial |ι| / |κ| ^ |ι|` if and only if `x` is injective, without requiring
measurability of `{f : ι → α | Function.Injective f}` in `ι → α`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff
    [MeasurableSingletonClass α]
    (x : κ → α) (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A) =
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι ↔ Function.Injective x := by
  refine ⟨fun heq => by_contra fun hx =>
    (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective
      hx hm hmn).ne heq, fun hx => ?_⟩
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  exact iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_of_injective hx e

/-- **Characterization of distinct populations, total-variation form.** For `2 ≤ |ι| ≤ |κ|` and a
value space with measurable singletons, Mathlib's total variation distance between sampling `x`
without and with replacement equals twice the collision probability if and only if `x` is
injective, without requiring measurability of `{f : ι → α | Function.Injective f}` in `ι → α`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff
    [MeasurableSingletonClass α]
    (x : κ → α) (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) =
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) ↔ Function.Injective x := by
  refine ⟨fun heq => by_contra fun hx =>
    (etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
      hx hm hmn).ne heq, fun hx => ?_⟩
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  exact etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_of_injective hx e

/-- **Characterization of distinct populations for an arbitrary value space, excess form.** For
`2 ≤ |ι| ≤ |κ|`, when the all-distinct event `{f : ι → α | Function.Injective f}` is measurable,
the largest excess of sampling `x` without replacement over sampling `x` with replacement equals
the collision probability `1 - |κ|.descFactorial |ι| / |κ| ^ |ι|` if and only if `x` is
injective. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff_of_measurableSet
    (x : κ → α) (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ)
    (hI : MeasurableSet {f : ι → α | Function.Injective f}) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A) =
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι ↔ Function.Injective x := by
  refine ⟨fun heq => by_contra fun hx =>
    (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective
      hx hm hmn).ne heq, fun hx => ?_⟩
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  exact iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq hx e hI

/-- **Characterization of distinct populations for an arbitrary value space, total-variation
form.** For `2 ≤ |ι| ≤ |κ|`, when the all-distinct event `{f : ι → α | Function.Injective f}` is
measurable, Mathlib's total variation distance between sampling `x` without and with replacement
equals twice the collision probability if and only if `x` is injective. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff_of_measurableSet
    (x : κ → α) (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ)
    (hI : MeasurableSet {f : ι → α | Function.Injective f}) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) =
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) ↔ Function.Injective x := by
  refine ⟨fun heq => by_contra fun hx =>
    (etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
      hx hm hmn).ne heq, fun hx => ?_⟩
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  exact etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq hx e hI

end Characterization

end TauCeti.Probability
