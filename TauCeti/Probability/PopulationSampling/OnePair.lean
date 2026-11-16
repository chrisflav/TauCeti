/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.Probability.PopulationSampling.Finite
import Mathlib.Data.Finset.Preimage
import TauCeti.Logic.Function.Update
import TauCeti.MeasureTheory.Measure.TotalVariation.Countable

/-!
# The one-pair population: fibres and exact sampling discrepancy

For distinct indices `a b : κ`, the *one-pair population* `Function.update id b a : κ → κ` sends
`b` to `a` and fixes every other index; it is the population with exactly one repeated value.
Sampling it along an index map `f : ι → κ` gives the word `Function.update id b a ∘ f`. This file
counts the index maps and the embeddings producing a given word, and uses those fibre counts
together with the two-hit mass (`uniformOn_injective_mem_range_and_mem_range` in
`TauCeti.Probability.UniformSampling`) to compute the exact discrepancy between sampling the
one-pair population without and with replacement.

Write `r` for the number of `i` with `Function.update id b a (f i) = a`, that is with
`f i ∈ {a, b}`. For an injective `f`, `r ≤ 2`, and `r = 2` exactly when `a` and `b` both lie in the
range of `f`. The word of `f` is produced by `2 ^ r` index maps, and, when `f` is an embedding, by
one embedding if `r = 0` and by two (namely `f` and `Equiv.swap a b ∘ f`) otherwise.

Consequently, when `|ι| ≤ |κ|`, writing `p = |κ|.descFactorial |ι| / |κ| ^ |ι|` and
`t = |ι|.descFactorial 2 / |κ|.descFactorial 2`, on the support of the without-replacement law
the likelihood ratio of with-replacement to without-replacement is `p` when `r ≤ 1` (mass `1 - t`)
and `2 * p` when `r = 2` (mass `t`). Summing the positive singleton differences gives the exact
eventwise excess `ENNReal.ofReal (1 - p - t * min p (1 - p))`, and twice that value for Mathlib's
total variation distance `etvDist`.

## Main declarations

* `card_filter_update_id_apply_eq_le_two`, `card_filter_update_id_apply_eq_eq_two_iff`: an
  injective index map meets `{a, b}` at most twice, and twice exactly when it hits both;
* `natCard_update_id_comp_eq_update_id_comp`: the number of index maps with the same word is
  `2 ^ r`;
* `natCard_embedding_update_id_comp_eq_update_id_comp`: the number of embeddings with the same
  word is `1` if `r = 0` and `2` otherwise;
* `sampleWithoutReplacement_dirac_update_id_card_filter_eq_two`: the without-replacement law of
  the one-pair population assigns mass `|ι|.descFactorial 2 / |κ|.descFactorial 2` to words
  containing `a` twice;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq`: the exact largest
  eventwise excess `ENNReal.ofReal (1 - p - t * min p (1 - p))`;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq`: the exact extended
  total variation distance, twice that excess.

The embeddings with the same word as an embedding `f`, namely `f` and `Equiv.swap a b ∘ f`, are
described by `Function.Embedding.update_id_comp_eq_update_id_comp_iff` in
`TauCeti.Logic.Function.Update`.
-/

public section

noncomputable section

open Finset Function MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {ι κ : Type*} {a b : κ}

section Fibres

variable [DecidableEq κ]

/-- The values of an injective index map at the indices it sends to `a` or `b` are distinct
elements of `{a, b}`, so they number the elements of `{a, b}` in its range. -/
private theorem card_filter_update_id_apply_eq_eq_card_filter_mem_range [Fintype ι] {f : ι → κ}
    (hf : Injective f) :
    #{i | update id b a (f i) = a} = #(({a, b} : Finset κ).filter (· ∈ Set.range f)) := by
  rw [← card_preimage _ f hf.injOn]
  congr 1
  ext i
  simp

/-- An injective index map sends at most two indices into `{a, b}`. -/
theorem card_filter_update_id_apply_eq_le_two [Fintype ι] {f : ι → κ} (hf : Injective f) :
    #{i | update id b a (f i) = a} ≤ 2 := by
  classical
  rw [card_filter_update_id_apply_eq_eq_card_filter_mem_range hf]
  exact (card_filter_le _ _).trans card_le_two

/-- An injective index map sends exactly two indices into `{a, b}` if and only if both `a` and
`b` lie in its range. -/
theorem card_filter_update_id_apply_eq_eq_two_iff [Fintype ι] {f : ι → κ} (hf : Injective f)
    (hab : a ≠ b) :
    #{i | update id b a (f i) = a} = 2 ↔ a ∈ Set.range f ∧ b ∈ Set.range f := by
  classical
  rw [card_filter_update_id_apply_eq_eq_card_filter_mem_range hf, ← card_pair hab,
    card_filter_eq_iff]
  simp

/-- The index maps with the same one-pair word as `f` choose freely between `a` and `b` at each
index that `f` sends into `{a, b}`, and agree with `f` elsewhere: there are `2 ^ r` of them, where
`r` is the number of such indices. The index type `κ` need not be finite. -/
theorem natCard_update_id_comp_eq_update_id_comp [Fintype ι] (hab : a ≠ b) (f : ι → κ) :
    Nat.card {g : ι → κ // update id b a ∘ g = update id b a ∘ f} =
      2 ^ #{i | update id b a (f i) = a} := by
  classical
  -- The fibre is a product, over `ι`, of the fibres of the one-pair population.
  have hfib (i : ι) : Nat.card {y : κ // update id b a y = update id b a (f i)} =
      if update id b a (f i) = a then 2 else 1 := by
    have hset : {y : κ | update id b a y = update id b a (f i)} =
        ({f i, Equiv.swap a b (f i)} : Set κ) := by
      ext y
      simp [update_id_apply_eq_update_id_apply_iff]
    rw [← Set.coe_ofPred, Nat.card_coe_set_eq, hset]
    split_ifs with h
    · exact Set.ncard_pair (Equiv.swap_apply_ne_self_iff.2 ⟨hab, update_id_apply_eq_iff.1 h⟩).symm
    · have he : Equiv.swap a b (f i) = f i := not_not.1 fun hne =>
        h (update_id_apply_eq_iff.2 (Equiv.swap_apply_ne_self_iff.1 hne).2)
      rw [he, Set.pair_eq_singleton, Set.ncard_singleton]
  have e : {g : ι → κ // update id b a ∘ g = update id b a ∘ f} ≃
      ∀ i, {y : κ // update id b a y = update id b a (f i)} :=
    (Equiv.subtypeEquivRight fun g => funext_iff).trans
      (Equiv.subtypePiEquivPi (p := fun i y => update id b a y = update id b a (f i)))
  rw [Nat.card_congr e, Nat.card_pi]
  simp_rw [hfib]
  rw [prod_ite, prod_const_one, mul_one, prod_const]

/-- The embeddings with the same one-pair word as an embedding `f` number one when `f` avoids
`{a, b}` and two otherwise: `f` itself and `Equiv.swap a b ∘ f`. The index type `κ` need not be
finite. -/
theorem natCard_embedding_update_id_comp_eq_update_id_comp [Fintype ι] (hab : a ≠ b)
    (f : ι ↪ κ) :
    Nat.card {g : ι ↪ κ // update id b a ∘ g = update id b a ∘ f} =
      if #{i | update id b a (f i) = a} = 0 then 1 else 2 := by
  classical
  have hset : {g : ι ↪ κ | update id b a ∘ g = update id b a ∘ f} =
      ({f, f.trans (Equiv.swap a b).toEmbedding} : Set (ι ↪ κ)) := by
    ext g
    simp [Embedding.update_id_comp_eq_update_id_comp_iff]
  have hfix : f.trans (Equiv.swap a b).toEmbedding = f ↔ #{i | update id b a (f i) = a} = 0 := by
    simp only [DFunLike.ext_iff, Embedding.trans_apply, Equiv.coe_toEmbedding, card_eq_zero,
      filter_eq_empty_iff, mem_univ, true_implies, update_id_apply_eq_iff, not_or]
    refine forall_congr' fun i => ?_
    rw [← not_iff_not, ← ne_eq, Equiv.swap_apply_ne_self_iff]
    simp [hab, or_iff_not_imp_left]
  rw [← Set.coe_ofPred, Nat.card_coe_set_eq, hset]
  split_ifs with h
  · rw [hfix.2 h, Set.pair_eq_singleton, Set.ncard_singleton]
  · exact Set.ncard_pair fun he => h (hfix.1 he.symm)

end Fibres

section Discrepancy

variable [Fintype ι] [Fintype κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Under sampling without replacement from the one-pair population `update id b a`, the event that
the sampled word takes the merged value `a` twice has probability
`|ι|.descFactorial 2 / |κ|.descFactorial 2`, provided `a ≠ b` and `|ι| ≤ |κ|`. -/
theorem sampleWithoutReplacement_dirac_update_id_card_filter_eq_two
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
        {y : ι → κ | #{i | y i = a} = 2} =
      (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2 := by
  have hpre : {k : ι → κ | Injective k} ∩
        ((fun k i => update id b a (k i)) ⁻¹' {y : ι → κ | #{i | y i = a} = 2}) =
      {k : ι → κ | Injective k} ∩ {k : ι → κ | a ∈ Set.range k ∧ b ∈ Set.range k} := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    exact and_congr_right fun hk => card_filter_update_id_apply_eq_eq_two_iff hk hab
  rw [sampleWithoutReplacement_dirac,
    Measure.map_apply (measurable_readPopulation _) (Set.toFinite _).measurableSet,
    ← uniformOn_inter_self (Set.toFinite _), hpre, uniformOn_inter_self (Set.toFinite _),
    uniformOn_injective_mem_range_and_mem_range hab hmn]

/-- Pointwise excess of `P (update id b a)` over `Q (update id b a)` on each word `y`: on the
support of `P`, the likelihood ratio `Q {y} / P {y}` is `p` when `a` appears at most once in `y`
and `2 * p` when `a` appears twice; off the support both sides vanish. -/
private theorem sampleWithoutReplacement_dirac_update_id_singleton_sub
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) (y : ι → κ) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} -
        sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {y} =
      (let p : ℝ≥0∞ := (Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
       if #{i | y i = a} = 2 then 1 - 2 * p else 1 - p) *
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} := by
  set P := sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
  set Q := sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  set d : ℝ≥0∞ := ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞)
  set N : ℝ≥0∞ := (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
  set p : ℝ≥0∞ := d / N
  by_cases hy : ∃ f : ι ↪ κ, update id b a ∘ f = y
  · obtain ⟨f, rfl⟩ := hy
    set r := #{i | update id b a (f i) = a}
    have hr : r ≤ 2 := card_filter_update_id_apply_eq_le_two f.injective
    have hd0 : d ≠ 0 := Nat.cast_ne_zero.2 (Nat.descFactorial_pos.2 hmn).ne'
    have hd_top : d ≠ ⊤ := ENNReal.natCast_ne_top _
    have hp_mul (c : ℝ≥0∞) : p * (c / d) = c / N := by
      simp only [p, div_eq_mul_inv]
      calc d * N⁻¹ * (c * d⁻¹)
          = (d * d⁻¹) * (c * N⁻¹) := by ring
        _ = c * N⁻¹ := by rw [ENNReal.mul_inv_cancel hd0 hd_top, one_mul]
    have hP : P {update id b a ∘ f} = ((if r = 0 then 1 else 2 : ℕ) : ℝ≥0∞) / d := by
      rw [sampleWithoutReplacement_dirac_apply_singleton,
        natCard_embedding_update_id_comp_eq_update_id_comp hab f]
    have hQ : Q {update id b a ∘ f} = ((2 ^ r : ℕ) : ℝ≥0∞) / N := by
      rw [sampleWithReplacement_dirac_apply_singleton,
        natCard_update_id_comp_eq_update_id_comp hab f]
    have hratio : Q {update id b a ∘ f} =
        (if r = 2 then 2 * p else p) * P {update id b a ∘ f} := by
      rw [hP, hQ]
      interval_cases r
      · simpa using (hp_mul 1).symm
      · simpa using (hp_mul 2).symm
      · rw [ite_eq_left rfl, ite_eq_right (by decide), mul_assoc, hp_mul]
        simp only [div_eq_mul_inv]
        rw [← mul_assoc]
        norm_num
    have hsub : P {update id b a ∘ f} - Q {update id b a ∘ f} =
        (1 - if r = 2 then 2 * p else p) * P {update id b a ∘ f} := by
      rw [hratio, ENNReal.sub_mul (fun _ _ => measure_ne_top P _), one_mul]
    rw [hsub]
    congr 1
    simp only [r, Function.comp_apply]
    split_ifs <;> rfl
  · have hP0 : P {y} = 0 := by
      have : IsEmpty {f : ι ↪ κ // update id b a ∘ f = y} :=
        ⟨fun ⟨f, hf⟩ => hy ⟨f, hf⟩⟩
      rw [sampleWithoutReplacement_dirac_apply_singleton, Nat.card_eq_zero.2 (.inl this)]
      simp
    simp [hP0]

/-- Algebraic combination of the two likelihood-ratio regimes for the one-pair population:
`(1 - 2 p)_+ * t + (1 - p) * (1 - t) = 1 - p - t * min p (1 - p)` for `p, t ∈ [0, 1]`. -/
private theorem one_sub_two_mul_ofReal_add_one_sub_ofReal {p t : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - 2 * ENNReal.ofReal p) * ENNReal.ofReal t +
        (1 - ENNReal.ofReal p) * (1 - ENNReal.ofReal t) =
      ENNReal.ofReal (1 - p - t * min p (1 - p)) := by
  have h1 : 1 - 2 * ENNReal.ofReal p = ENNReal.ofReal (max (1 - 2 * p) 0) := by
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le,
      ENNReal.ofReal_sub 1 (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  have h2 : 1 - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
    rw [ENNReal.ofReal_sub 1 hp0, ENNReal.ofReal_one]
  have h3 : 1 - ENNReal.ofReal t = ENNReal.ofReal (1 - t) := by
    rw [ENNReal.ofReal_sub 1 ht0, ENNReal.ofReal_one]
  rw [h1, h2, h3, ← ENNReal.ofReal_mul (le_max_right _ _),
    ← ENNReal.ofReal_mul (sub_nonneg.2 hp1),
    ← ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) ht0)
      (mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 ht1))]
  congr 1
  rcases le_total p (1 - p) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_right (by linarith)]
    ring

/-- **Exact one-pair discrepancy, excess form.** For distinct `a b : κ` and `|ι| ≤ |κ|`, the
largest eventwise excess of sampling `Function.update id b a` without replacement over sampling it
with replacement is `ENNReal.ofReal (1 - p - t * min p (1 - p))`, where
`p = |κ|.descFactorial |ι| / |κ| ^ |ι|` and `t = |ι|.descFactorial 2 / |κ|.descFactorial 2`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    (⨆ (A : Set (ι → κ)) (_ : MeasurableSet A),
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) A -
          sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) A) =
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  classical
  set P := sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
  set Q := sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  set p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
    (Fintype.card κ : ℝ) ^ Fintype.card ι
  set t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
  set p_e : ℝ≥0∞ := (Fintype.card κ).descFactorial (Fintype.card ι) /
    (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
  set t_e : ℝ≥0∞ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
  set s : Finset (ι → κ) := Finset.univ.filter fun y => #{i | y i = a} = 2
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  let _ : IsProbabilityMeasure P := isProbabilityMeasure_sampleWithoutReplacement _ e
  -- Express `p_e` and `t_e` as `ENNReal.ofReal` of values in `[0, 1]`.
  have hκ2 : 2 ≤ Fintype.card κ := Fintype.one_lt_card_iff.2 ⟨a, b, hab⟩
  have hpow_pos : (0 : ℝ) < (Fintype.card κ : ℝ) ^ Fintype.card ι :=
    pow_pos (by exact_mod_cast (lt_of_lt_of_le (by decide) hκ2)) _
  have hd2_pos : (0 : ℝ) < ((Fintype.card κ).descFactorial 2 : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 hκ2
  have hp_eq : p_e = ENNReal.ofReal p := by rw [ENNReal.ofReal_div_of_pos hpow_pos]; simp [p_e]
  have ht_eq : t_e = ENNReal.ofReal t := by rw [ENNReal.ofReal_div_of_pos hd2_pos]; simp [t_e]
  have hp1 : p ≤ 1 := (div_le_one hpow_pos).2 (by exact_mod_cast Nat.descFactorial_le_pow _ _)
  have ht1 : t ≤ 1 := (div_le_one hd2_pos).2 (by exact_mod_cast Nat.descFactorial_le 2 hmn)
  -- Evaluate the `P`-masses of the two-hit event `s` and its complement `sᶜ`.
  have hPs : P (s : Set (ι → κ)) = t_e := by
    have hs : (s : Set (ι → κ)) = {y : ι → κ | #{i | y i = a} = 2} := by simp [s]
    rw [hs]
    exact sampleWithoutReplacement_dirac_update_id_card_filter_eq_two hab hmn
  have hPsc : P ((sᶜ : Finset (ι → κ)) : Set (ι → κ)) = 1 - t_e := by
    rw [Finset.coe_compl, prob_compl_eq_one_sub s.measurableSet, hPs]
  -- Sum the pointwise excesses split over `s` and `sᶜ`.
  calc
    (⨆ (A : Set (ι → κ)) (_ : MeasurableSet A), P A - Q A)
      = ∑ y : ι → κ, (P {y} - Q {y}) := iSup_measure_sub_eq_sum_singleton P Q
    _ = ∑ y : ι → κ,
          (if #{i | y i = a} = 2 then (1 - 2 * p_e) * P {y} else (1 - p_e) * P {y}) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [sampleWithoutReplacement_dirac_update_id_singleton_sub hab hmn y]
        split_ifs <;> rfl
    _ = (∑ y ∈ s, (1 - 2 * p_e) * P {y}) + ∑ y ∈ sᶜ, (1 - p_e) * P {y} := by
        rw [Finset.sum_ite]
        refine congrArg₂ (· + ·) rfl (Finset.sum_congr ?_ fun _ _ => rfl)
        ext y
        simp [s]
    _ = (1 - 2 * p_e) * P (s : Set (ι → κ)) +
          (1 - p_e) * P ((sᶜ : Finset (ι → κ)) : Set (ι → κ)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, sum_measure_singleton, sum_measure_singleton]
    _ = (1 - 2 * ENNReal.ofReal p) * ENNReal.ofReal t +
          (1 - ENNReal.ofReal p) * (1 - ENNReal.ofReal t) := by
        rw [hPs, hPsc, hp_eq, ht_eq]
    _ = ENNReal.ofReal (1 - p - t * min p (1 - p)) :=
        one_sub_two_mul_ofReal_add_one_sub_ofReal (by positivity) hp1 (by positivity) ht1

/-- **Exact one-pair discrepancy, total-variation form.** For distinct `a b : κ` and `|ι| ≤ |κ|`,
Mathlib's total variation distance between sampling `Function.update id b a` without and with
replacement is twice the exact excess `ENNReal.ofReal (1 - p - t * min p (1 - p))`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)))
        (sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))) =
      2 * ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  let : Nonempty (ι → κ) := ⟨e⟩
  let := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  let := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  rw [etvDist_eq_two_mul_iSup_sub (by rw [measure_univ, measure_univ]),
    iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn]

end Discrepancy

end Probability

end TauCeti
