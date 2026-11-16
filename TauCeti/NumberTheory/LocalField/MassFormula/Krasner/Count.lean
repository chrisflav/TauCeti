/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Divisors
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount
public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Box
public import TauCeti.NumberTheory.LocalField.MassFormula.Representative
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.NumberTheory.LocalField.InertiaDegree
import TauCeti.NumberTheory.LocalField.MassFormula.Main

/-!
# Krasner's discriminant-refined count and total extension counts

Let `K` be a nonarchimedean local field with residue cardinality `q = Nat.card 𝓀[K]`. For a degree
`n` and wild exponent `j`, let `σ_K(n, j) = {E ∈ σ_K(n) | E.wildExponent = j}` be the set of
totally ramified degree-`n` subextensions of `SeparableClosure K` with discriminant exponent
`n - 1 + j`.

Integrating the root-count identity `∑_{L ∈ σ_K(n)} L.rootCount a = n` over the discriminant box
`TauCeti.eisensteinBox K n j` against the Haar measure normalized on `integerBox K (Fin n)`, and
using the exact box volume (`TauCeti.measure_eisensteinBox`) together with the local root-count
integral (`IntermediateField.lintegral_rootCount_eisensteinBox_of_wildExponent_eq`), yields
**Krasner's count**:

* `σ_K(n, j)` is finite for every `n, j : ℕ` (in both mixed and equal characteristic);
* when `IsOreAdmissible K n j`, its cardinality equals
  `n · q ^ (n + j - 1 - ∑_{h=1}^{n-1} ν_h)` if `n ∣ j` and
  `n · (q - 1) · q ^ (n + j - 2 - ∑_{h=1}^{n-1} ν_h)` if `n ∤ j`, where
  `ν_h = oreCoefficientDepth K n j h`;
* when `¬ IsOreAdmissible K n j`, `σ_K(n, j)` is empty.

From Krasner's count we derive:

* **Bounded-discriminant finiteness**: for every local field `K` (including equal characteristic)
  and every `n, D : ℕ`, only finitely many `E ∈ σ_K(n)` have wild exponent or discriminant exponent
  at most `D`.
* **Consistency with Serre's mass formula**: `∑' j, #σ_K(n, j) / q ^ j = n`, both in `ℝ≥0∞` and as
  a convergent real series.
* **Isomorphism-class form**: for any representative set `R` of `σ_K(n)` (`0 < n`),
  `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = #σ_K(n, j) / n`.
* **Total counts**: `#σ_K(n) = ∑' j, #σ_K(n, j)` in general, reducing to a finite sum over
  `0 ≤ j ≤ n · v_K(n)` whenever `(n : K) ≠ 0`; and the count of all degree-`n` subextensions of
  `SeparableClosure K` equals `∑_{f ∣ n} #σ_{K_f}(n / f)`, where `K_f` is the degree-`f` unramified
  subextension.

## Main definitions

* `TauCeti.krasnerCount K n j`: Krasner's discriminant-refined count as a rational number.

## Main results

* `TauCeti.encard_totallyRamifiedOfDegree_wildExponent_eq`,
  `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq`, and `TauCeti.krasner_refined_count`:
  Krasner's theorem in `ℕ∞`, `ℕ`, and `ℚ` forms.
* `TauCeti.finite_totallyRamifiedOfDegree_wildExponent_le` and
  `TauCeti.finite_totallyRamifiedOfDegree_discriminantExponent_le`: bounded-discriminant finiteness.
* `TauCeti.tsum_ncard_wildExponent_eq_div_pow` and `TauCeti.hasSum_krasnerCount_div_pow`:
  consistency with Serre's first mass formula.
* `TauCeti.IsRepresentativeSet.sum_one_div_natCard_algEquiv_of_wildExponent_eq`: isomorphism-class
  form of Krasner's count.
* `TauCeti.encard_totallyRamifiedOfDegree_eq_tsum`,
  `TauCeti.ncard_totallyRamifiedOfDegree_eq_sum_krasnerCount`, and
  `TauCeti.encard_finrank_eq_sum_encard_totallyRamifiedOfDegree`: total extension counts.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `𝔭`-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, Colloq. Internat. CNRS **143** (1966), 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Theorem 6.1.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
-/

public section
noncomputable section

open ValuativeRel MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### The rational box count formula -/

open scoped Classical in
variable (K) in
/-- Krasner's discriminant-refined count of totally ramified degree-`n` subextensions with wild
exponent `j`, written as a rational number:
`n · q ^ (n + j - 1 - ∑_{h=1}^{n-1} ν_h) · (if n ∣ j then 1 else 1 - q⁻¹)` when
`IsOreAdmissible K n j`, and `0` otherwise. By `TauCeti.krasnerCount_eq_natCast`, this value is
always a nonnegative integer. -/
def krasnerCount (n j : ℕ) : ℚ :=
  if IsOreAdmissible K n j then
    (n : ℚ) *
      (Nat.card 𝓀[K] : ℚ) ^
        (((n + j - 1 : ℕ) : ℤ) - ∑ h ∈ Finset.Ico 1 n, (oreCoefficientDepth K n j h : ℤ)) *
      if j % n = 0 then 1 else 1 - (Nat.card 𝓀[K] : ℚ)⁻¹
  else 0

open scoped Classical in
/-- Unfolding `TauCeti.krasnerCount`. -/
theorem krasnerCount_def (n j : ℕ) :
    krasnerCount K n j =
      if IsOreAdmissible K n j then
        (n : ℚ) *
          (Nat.card 𝓀[K] : ℚ) ^
            (((n + j - 1 : ℕ) : ℤ) - ∑ h ∈ Finset.Ico 1 n, (oreCoefficientDepth K n j h : ℤ)) *
          if j % n = 0 then 1 else 1 - (Nat.card 𝓀[K] : ℚ)⁻¹
      else 0 := by
  rw [krasnerCount]

/-- `krasnerCount` vanishes outside Ore-admissible pairs `(n, j)`. -/
theorem krasnerCount_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    krasnerCount K n j = 0 := by
  rw [krasnerCount_def, ite_eq_right h]

/-- At degree `0`, `krasnerCount` is `0`. -/
@[simp]
theorem krasnerCount_zero_left (j : ℕ) : krasnerCount K 0 j = 0 :=
  krasnerCount_of_not_isOreAdmissible (isOreAdmissible_zero_left j)

/-- When `IsOreAdmissible K n j` and `j % n = 0`, `krasnerCount` evaluates to the natural number
`n * q ^ (n + j - 1 - ∑_{h=1}^{n-1} ν_h)`. -/
theorem krasnerCount_eq_natCast_of_mod_eq_zero {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hb : j % n = 0) :
    krasnerCount K n j =
      ((n * Nat.card 𝓀[K] ^
        (n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) : ℕ) : ℚ) := by
  have hS := sum_oreCoefficientDepth_le (K := K) hadm.pos j
  rw [krasnerCount_def, ite_eq_left hadm, ite_eq_left hb, mul_one]
  have hexp : (((n + j - 1 : ℕ) : ℤ) -
      ∑ h ∈ Finset.Ico 1 n, (oreCoefficientDepth K n j h : ℤ)) =
      ((n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h : ℕ) : ℤ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sub hS]
  rw [hexp, zpow_natCast]
  push_cast
  rfl

/-- When `IsOreAdmissible K n j` and `0 < j % n`, `krasnerCount` evaluates to the natural number
`n * (q - 1) * q ^ (n + j - 2 - ∑_{h=1}^{n-1} ν_h)`. -/
theorem krasnerCount_eq_natCast_of_mod_pos {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hb : 0 < j % n) :
    krasnerCount K n j =
      ((n * (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^
        (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) : ℕ) : ℚ) := by
  have hS := sum_oreCoefficientDepth_add_one_le (K := K) hadm.pos hb
  have hq : (1 : ℕ) ≤ Nat.card 𝓀[K] := Nat.card_pos
  have hq0 : (Nat.card 𝓀[K] : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [krasnerCount_def, ite_eq_left hadm, ite_eq_right hb.ne']
  set S := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  have hsub : n + j - 1 - S = (n + j - 2 - S) + 1 := by omega
  have hexp : (((n + j - 1 : ℕ) : ℤ) -
      ∑ h ∈ Finset.Ico 1 n, (oreCoefficientDepth K n j h : ℤ)) =
      ((n + j - 2 - S + 1 : ℕ) : ℤ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sub (by omega : S ≤ n + j - 1), hsub]
  rw [hexp, zpow_natCast, pow_succ]
  push_cast [hq]
  field_simp [hq0]

open scoped Classical in
/-- `krasnerCount K n j` is always the rational cast of an explicit natural number. -/
theorem krasnerCount_eq_natCast (n j : ℕ) :
    krasnerCount K n j =
      ((if IsOreAdmissible K n j then
        if j % n = 0 then
          n * Nat.card 𝓀[K] ^
            (n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)
        else
          n * (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^
            (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)
      else 0 : ℕ) : ℚ) := by
  by_cases hadm : IsOreAdmissible K n j
  · rcases (j % n).eq_zero_or_pos with hb0 | hbpos
    · rw [ite_eq_left hadm, ite_eq_left hb0, krasnerCount_eq_natCast_of_mod_eq_zero hadm hb0]
    · rw [ite_eq_left hadm, ite_eq_right hbpos.ne', krasnerCount_eq_natCast_of_mod_pos hadm hbpos]
  · rw [ite_eq_right hadm, Nat.cast_zero, krasnerCount_of_not_isOreAdmissible hadm]

/-! ### Krasner's discriminant-refined count -/

private theorem pow_mul_one_div_pow_add {a : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ∞) (m k : ℕ) :
    a ^ k * (1 / a ^ (m + k)) = 1 / a ^ m := by
  rw [pow_add, one_div, ENNReal.mul_inv (.inl (pow_ne_zero _ ha0)) (.inl (ENNReal.pow_ne_top hat)),
    mul_comm (a ^ m)⁻¹, ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero _ ha0) (ENNReal.pow_ne_top hat), one_mul, one_div]

private theorem sub_one_mul_one_div_eq {a : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ∞) :
    (a - 1) * (1 / a) = 1 - 1 / a := by
  rw [one_div, ENNReal.sub_mul (fun _ _ ↦ ENNReal.inv_ne_top.mpr ha0), one_mul,
    ENNReal.mul_inv_cancel ha0 hat]

private theorem box_volume_eq_count_mul_local_integral {n j : ℕ} (hadm : IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    (n : ℝ≥0∞) * μ (eisensteinBox K n j) =
      ((if j % n = 0 then
          n * Nat.card 𝓀[K] ^
            (n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)
        else
          n * (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^
            (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) : ℕ) : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) := by
  set S := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  set Q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  have hq0 : Q ≠ 0 := by simp [Q, Nat.card_pos.ne']
  have hqt : Q ≠ ∞ := ENNReal.natCast_ne_top _
  rw [measure_eisensteinBox hadm μ hμ]
  rcases (j % n).eq_zero_or_pos with hb0 | hbpos
  · have hS := sum_oreCoefficientDepth_le (K := K) hadm.pos j
    have hexp : (1 + S) + (n + j - 1 - S) = n + j := by have := hadm.pos; omega
    rw [ite_eq_left hb0, ite_eq_left hb0, mul_one]
    push_cast
    calc (n : ℝ≥0∞) * (1 / Q ^ (1 + S) * (1 - 1 / Q))
        = (n : ℝ≥0∞) * ((Q ^ (n + j - 1 - S) * (1 / Q ^ ((1 + S) + (n + j - 1 - S)))) *
            (1 - 1 / Q)) := by rw [pow_mul_one_div_pow_add hq0 hqt]
      _ = (n : ℝ≥0∞) * Q ^ (n + j - 1 - S) * (1 / Q ^ (n + j) * (1 - 1 / Q)) := by
          rw [hexp]; ring
  · have hS := sum_oreCoefficientDepth_add_one_le (K := K) hadm.pos hbpos
    have hexp : (1 + S + 1) + (n + j - 2 - S) = n + j := by have := hadm.pos; omega
    rw [ite_eq_right hbpos.ne', ite_eq_right hbpos.ne']
    push_cast
    have hsplit : 1 / Q ^ (1 + S + 1) = 1 / Q ^ (1 + S) * (1 / Q) := by
      simp only [one_div, pow_succ]
      exact ENNReal.mul_inv (.inl (pow_ne_zero _ hq0)) (.inl (ENNReal.pow_ne_top hqt))
    have hq1 : (Q - 1) * (1 / Q) = 1 - 1 / Q := sub_one_mul_one_div_eq hq0 hqt
    calc (n : ℝ≥0∞) * (1 / Q ^ (1 + S) * (1 - 1 / Q) * (1 - 1 / Q))
        = (n : ℝ≥0∞) * (1 / Q ^ (1 + S) * (1 / Q) * (Q - 1) * (1 - 1 / Q)) := by
            rw [← hq1]; ring
      _ = (n : ℝ≥0∞) * (1 / Q ^ (1 + S + 1) * (Q - 1) * (1 - 1 / Q)) := by rw [hsplit]
      _ = (n : ℝ≥0∞) * ((Q ^ (n + j - 2 - S) * (1 / Q ^ ((1 + S + 1) + (n + j - 2 - S)))) *
            (Q - 1) * (1 - 1 / Q)) := by rw [pow_mul_one_div_pow_add hq0 hqt]
      _ = (n : ℝ≥0∞) * (Q - 1) * Q ^ (n + j - 2 - S) *
            (1 / Q ^ (n + j) * (1 - 1 / Q)) := by rw [hexp]; ring

private theorem tsum_ite_wildExponent_eq (n j : ℕ) (C : ℝ≥0∞) :
    (∑' L : totallyRamifiedOfDegree K n, if L.1.wildExponent = j then C else 0) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard : ℝ≥0∞) * C := by
  classical
  let T : Set (IntermediateField K (SeparableClosure K)) :=
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}
  let f : IntermediateField K (SeparableClosure K) → ℝ≥0∞ := fun L ↦ if L ∈ T then C else 0
  have hcongr : (∑' L : totallyRamifiedOfDegree K n, if L.1.wildExponent = j then C else 0) =
      ∑' L : totallyRamifiedOfDegree K n, f L.1 :=
    tsum_congr fun L ↦ by simp only [f, T, Set.mem_ofPred_eq, L.2, true_and]
  have hsupp : Function.support f ⊆ T := fun L hL ↦ by by_contra h; exact hL (by simp [f, h])
  have hT : ∑' L : T, f L.1 = ∑' _ : T, C := tsum_congr fun L ↦ ite_eq_left L.2
  rw [hcongr, tsum_subtype_eq_of_support_subset (hsupp.trans fun _ h ↦ h.1),
    ← tsum_subtype_eq_of_support_subset hsupp, hT, ENNReal.tsum_set_const]

private theorem tsum_lintegral_rootCount_eisensteinBox_eq_encard_mul (n j : ℕ)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ∑' L : totallyRamifiedOfDegree K n,
        ∫⁻ a in eisensteinBox K n j, (L.1.rootCount a : ℝ≥0∞) ∂μ =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) := by
  rw [← tsum_ite_wildExponent_eq n j]
  refine tsum_congr fun L ↦ ?_
  by_cases hj : L.1.wildExponent = j
  · rw [L.1.lintegral_rootCount_eisensteinBox_of_wildExponent_eq L.2 hj μ hμ, ite_eq_left hj]
  · rw [L.1.lintegral_rootCount_eisensteinBox_of_wildExponent_ne L.2 hj μ, ite_eq_right hj]

open scoped Classical in
/-- **Krasner's discriminant-refined count in `ℕ∞`**: for every nonarchimedean local field `K` and
every `n, j : ℕ`, the extended cardinality of `{E ∈ σ_K(n) | E.wildExponent = j}` equals the exact
natural-number box count when `IsOreAdmissible K n j`, and `0` otherwise. -/
theorem encard_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard =
      ((if IsOreAdmissible K n j then
        if j % n = 0 then
          n * Nat.card 𝓀[K] ^
            (n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)
        else
          n * (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^
            (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)
      else 0 : ℕ) : ℕ∞) := by
  by_cases hadm : IsOreAdmissible K n j
  · let : MeasurableSpace (Fin n → K) := borel _
    have : BorelSpace (Fin n → K) := ⟨rfl⟩
    let B : TopologicalSpace.PositiveCompacts (Fin n → K) :=
      ⟨⟨integerBox K (Fin n), isCompact_integerBox⟩, by
        rw [isOpen_integerBox.interior_eq]
        exact ⟨0, by simp⟩⟩
    let μ : Measure (Fin n → K) := Measure.addHaarMeasure B
    have hμ : μ (integerBox K (Fin n)) = 1 := Measure.addHaarMeasure_self
    set C : ℝ≥0∞ := 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
    have hq_gt : (1 : ℝ≥0∞) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
    have hC0 : C ≠ 0 := by
      refine mul_ne_zero (ENNReal.div_pos one_ne_zero
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))).ne' (tsub_pos_of_lt ?_).ne'
      rwa [one_div, ENNReal.inv_lt_one]
    have hCt : C ≠ ∞ := by
      refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top ?_)
        (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
      rw [one_div]
      exact ENNReal.inv_le_one.mpr (one_le_pow₀ hq_gt.le)
    have htot := tsum_lintegral_rootCount_eisensteinBox_eq (K := K) (n := n) (j := j) μ
    rw [tsum_lintegral_rootCount_eisensteinBox_eq_encard_mul n j μ hμ,
      box_volume_eq_count_mul_local_integral hadm μ hμ] at htot
    have hmul := (ENNReal.mul_left_inj hC0 hCt).mp htot
    rw [ite_eq_left hadm, ← ENat.toENNReal_inj, ENat.toENNReal_coe]
    exact hmul
  · have hemp : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun E ⟨hE, hj⟩ ↦
        hadm ((ore_realizability n j).mp ⟨E, hE, hj⟩)
    rw [hemp, Set.encard_empty, ite_eq_right hadm, Nat.cast_zero]

/-- Every wild-exponent stratum `{E ∈ σ_K(n) | E.wildExponent = j}` is finite, in both mixed and
equal characteristic. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite := by
  rw [← Set.encard_lt_top_iff, encard_totallyRamifiedOfDegree_wildExponent_eq]
  exact ENat.natCast_lt_top _

open scoped Classical in
/-- **Krasner's discriminant-refined count in `ℕ`**: the exact cardinality of
`{E ∈ σ_K(n) | E.wildExponent = j}`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard =
      if IsOreAdmissible K n j then
        if j % n = 0 then
          n * Nat.card 𝓀[K] ^
            (n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)
        else
          n * (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^
            (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)
      else 0 := by
  have h := encard_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  rw [← (finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq] at h
  exact_mod_cast h

/-- **Krasner's theorem** ([Krasner 1966], [Pauli–Roblot 2001, Theorem 6.1]): for every degree `n`
and wild exponent `j`, the cardinality of `{E ∈ σ_K(n) | E.wildExponent = j}` equals
`krasnerCount K n j`. -/
theorem krasner_refined_count (n j : ℕ) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) =
      krasnerCount K n j := by
  rw [ncard_totallyRamifiedOfDegree_wildExponent_eq, krasnerCount_eq_natCast]

/-! ### Bounded-discriminant finiteness -/

/-- For every nonarchimedean local field `K` (including equal characteristic) and all `n, D : ℕ`,
only finitely many totally ramified degree-`n` subextensions have wild exponent at most `D`. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent ≤ D}.Finite := by
  have hsub : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent ≤ D} ⊆
      ⋃ j ∈ Finset.range (D + 1), {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} := by
    intro E ⟨hE, hle⟩
    exact Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)) ⟨hE, rfl⟩
  exact ((Finset.finite_toSet (Finset.range (D + 1))).biUnion fun j _ ↦
    finite_totallyRamifiedOfDegree_wildExponent_eq n j).subset hsub

/-- For every nonarchimedean local field `K` (including equal characteristic) and all `n, D : ℕ`,
only finitely many totally ramified degree-`n` subextensions have discriminant exponent at most
`D`. -/
theorem finite_totallyRamifiedOfDegree_discriminantExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.discriminantExponent ≤ D}.Finite := by
  refine (finite_totallyRamifiedOfDegree_wildExponent_le n D).subset fun E ⟨hE, hle⟩ ↦ ⟨hE, ?_⟩
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hE
  have hwd := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hE
  omega

/-! ### Consistency with Serre's mass formula -/

private theorem totallyRamifiedOfDegree_eq_iUnion_wildExponent (n : ℕ) :
    totallyRamifiedOfDegree K n =
      ⋃ j : ℕ, {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} := by
  ext E
  simp

private theorem pairwiseDisjoint_wildExponent (n : ℕ) :
    (Set.univ : Set ℕ).PairwiseDisjoint
      (fun j ↦ {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}) := by
  intro j₁ _ j₂ _ hne
  exact Set.disjoint_left.mpr fun _ h₁ h₂ ↦ hne (h₁.2.symm.trans h₂.2)

/-- **Consistency with Serre's first mass formula (in `ℝ≥0∞`)**: summing `#σ_K(n, j) / q ^ j` over
all `j : ℕ` recovers `n`. -/
theorem tsum_ncard_wildExponent_eq_div_pow (n : ℕ) :
    ∑' j : ℕ,
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ j = n := by
  have hmass := tsum_one_div_natCard_residueField_pow_wildExponent (K := K) (n := n)
  rw [← hmass]
  conv_rhs => rw [totallyRamifiedOfDegree_eq_iUnion_wildExponent n]
  rw [tsum_iUnion (f := fun L : IntermediateField K (SeparableClosure K) ↦
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.wildExponent) (pairwiseDisjoint_wildExponent (K := K) n)]
  refine tsum_congr fun j ↦ ?_
  have hcongr : ∑' L : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j},
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent =
      ∑' _ : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ j :=
    tsum_congr fun L ↦ by rw [L.2.2]
  rw [hcongr, ENNReal.tsum_set_const,
    ← (finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
    ENat.toENNReal_coe, mul_one_div]

/-- **Consistency with Serre's first mass formula (real series)**: the series
`∑_j krasnerCount K n j / q ^ j` converges to `n`. -/
theorem hasSum_krasnerCount_div_pow (n : ℕ) :
    HasSum (fun j : ℕ ↦ (krasnerCount K n j : ℝ) / (Nat.card 𝓀[K] : ℝ) ^ j) n := by
  let f : ℕ → ℝ≥0 := fun j ↦
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0) /
      (Nat.card 𝓀[K] : ℝ≥0) ^ j
  have hcoe (j : ℕ) : (f j : ℝ≥0∞) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ j := by
    rw [ENNReal.coe_div (pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))]
    push_cast
    rfl
  have hsum_enn : ∑' j : ℕ, (f j : ℝ≥0∞) = ((n : ℝ≥0) : ℝ≥0∞) := by
    simpa only [hcoe, ENNReal.coe_natCast] using tsum_ncard_wildExponent_eq_div_pow (K := K) n
  have hsum_nn : HasSum f (n : ℝ≥0) := by
    rwa [← ENNReal.hasSum_coe, CompleteLattice.summable.hasSum_iff]
  have hsum_real : HasSum (fun j ↦ (f j : ℝ)) (n : ℝ) := by
    simpa only [NNReal.coe_natCast] using NNReal.hasSum_coe.mpr hsum_nn
  refine hsum_real.congr_fun fun j ↦ ?_
  have hkr := krasner_refined_count (K := K) n j
  have hkrR : (krasnerCount K n j : ℝ) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ) := by
    exact_mod_cast hkr.symm
  simp [f, hkrR]

/-! ### Isomorphism-class form of Krasner's count -/

namespace IsRepresentativeSet

variable {n j : ℕ} {R : Set (IntermediateField K (SeparableClosure K))}

/-- Within any set of isomorphism-class representatives `R` of `σ_K(n)`, only finitely many
representatives have a given wild exponent `j`. -/
theorem finite_wildExponent_eq (hR : IsRepresentativeSet n R) :
    {M ∈ R | M.wildExponent = j}.Finite :=
  (finite_totallyRamifiedOfDegree_wildExponent_eq n j).subset fun _ ⟨hM, hj⟩ ↦ ⟨hR.subset hM, hj⟩

/-- **Isomorphism-class form of Krasner's count (in `ℝ≥0∞`)**: for `0 < n` and any representative
set `R` of `σ_K(n)`, `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = #σ_K(n, j) / n`. -/
theorem tsum_one_div_natCard_algEquiv_of_wildExponent_eq (hR : IsRepresentativeSet n R)
    (hn : 0 < n) :
    ∑' M : {M ∈ R | M.wildExponent = j}, (1 / (Nat.card (M.1 ≃ₐ[K] M.1) : ℝ≥0∞)) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) / n := by
  classical
  let ind : IntermediateField K (SeparableClosure K) → ℝ≥0∞ :=
    fun L ↦ if L.wildExponent = j then 1 else 0
  have hinv : ∀ {L M : IntermediateField K (SeparableClosure K)}, (L ≃ₐ[K] M) → ind L = ind M :=
    fun e ↦ by simp [ind, IntermediateField.wildExponent_eq_of_algEquiv e]
  have hreg := hR.tsum_eq_tsum_div_natCard_algEquiv_mul ind hinv
  have hlhs : ∑' L : totallyRamifiedOfDegree K n, ind L.1 =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) := by
    rw [tsum_ite_wildExponent_eq n j 1, mul_one,
      ← (finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
      ENat.toENNReal_coe]
  have hrhs : ∑' M : R, (n : ℝ≥0∞) / Nat.card (M.1 ≃ₐ[K] M.1) * ind M.1 =
      (n : ℝ≥0∞) * ∑' M : {M ∈ R | M.wildExponent = j},
        (1 / (Nat.card (M.1 ≃ₐ[K] M.1) : ℝ≥0∞)) := by
    let S := {M ∈ R | M.wildExponent = j}
    let g : IntermediateField K (SeparableClosure K) → ℝ≥0∞ :=
      fun M ↦ if M ∈ S then (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) else 0
    have hcongr : ∑' M : R, (n : ℝ≥0∞) / Nat.card (M.1 ≃ₐ[K] M.1) * ind M.1 =
        ∑' M : R, g M.1 := tsum_congr fun M ↦ by simp [ind, g, S, M.2]
    have hsupp : Function.support g ⊆ S := fun M hM ↦ by by_contra h; exact hM (by simp [g, h])
    rw [hcongr, tsum_subtype_eq_of_support_subset (hsupp.trans fun _ h ↦ h.1),
      ← tsum_subtype_eq_of_support_subset hsupp, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun M ↦ ?_
    simp only [g, M.2, ↓reduceIte, div_eq_mul_inv, one_mul]
  rw [hlhs, hrhs] at hreg
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  exact (ENNReal.eq_div_iff hn0 (ENNReal.natCast_ne_top _)).mpr hreg.symm

/-- **Isomorphism-class form of Krasner's count (finite sum in `ℚ`)**: for `0 < n` and any
representative set `R` of `σ_K(n)`, `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = krasnerCount K n j / n`. -/
theorem sum_one_div_natCard_algEquiv_of_wildExponent_eq (hR : IsRepresentativeSet n R)
    (hn : 0 < n) :
    ∑ M ∈ (hR.finite_wildExponent_eq (j := j)).toFinset,
        (1 / (Nat.card (M ≃ₐ[K] M) : ℚ)) =
      krasnerCount K n j / n := by
  have h := hR.tsum_one_div_natCard_algEquiv_of_wildExponent_eq (j := j) hn
  have hfin := hR.finite_wildExponent_eq (j := j)
  set s := hfin.toFinset
  have htsum : ∑' M : {M ∈ R | M.wildExponent = j}, (1 / (Nat.card (M.1 ≃ₐ[K] M.1) : ℝ≥0∞)) =
      ∑ M ∈ s, (1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞)) := by
    let e : {M ∈ R | M.wildExponent = j} ≃ s :=
      Equiv.subtypeEquivRight fun M ↦ (Set.Finite.mem_toFinset hfin).symm
    rw [← Finset.tsum_subtype s (fun M ↦ 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞))]
    exact e.tsum_eq (fun M : s ↦ 1 / (Nat.card (M.1 ≃ₐ[K] M.1) : ℝ≥0∞))
  rw [htsum] at h
  have hrat_eq : ((∑ M ∈ s, (1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0)) : ℝ≥0) : ℝ≥0∞) =
      (((({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0) /
        (n : ℝ≥0)) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofNNReal_finsetSum, ENNReal.coe_div (by exact_mod_cast hn.ne')]
    have hterm (M : IntermediateField K (SeparableClosure K)) (hM : M ∈ s) :
        ((1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0) : ℝ≥0) : ℝ≥0∞) =
          1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) := by
      have hMR : M ∈ totallyRamifiedOfDegree K n :=
        hR.subset ((Set.Finite.mem_toFinset hfin).mp hM).1
      have := (mem_totallyRamifiedOfDegree_iff.mp hMR).2.finite
      have hAut : Nat.card (M ≃ₐ[K] M) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨.refl⟩, inferInstance⟩
      rw [ENNReal.coe_div (by exact_mod_cast hAut)]
      push_cast; rfl
    rw [Finset.sum_congr rfl hterm, h]
    push_cast; rfl
  have hnn : ∑ M ∈ s, (1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0)) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0) / (n : ℝ≥0) :=
    ENNReal.coe_injective hrat_eq
  have hreal : ∑ M ∈ s, (1 / (Nat.card (M ≃ₐ[K] M) : ℝ)) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ) / (n : ℝ) := by
    have := congrArg ((↑) : ℝ≥0 → ℝ) hnn
    simpa using this
  rw [← krasner_refined_count (K := K) n j]
  apply Rat.cast_injective (α := ℝ)
  push_cast
  exact hreal

end IsRepresentativeSet

/-! ### Total counts of extensions of a given degree -/

/-- **Krasner's total count of `σ_K(n)` (general form)**: for every local field `K` and degree `n`,
the cardinality of `σ_K(n)` in `ℝ≥0∞` is the infinite sum of the finite stratum counts
`#σ_K(n, j)`. -/
theorem encard_totallyRamifiedOfDegree_eq_tsum (n : ℕ) :
    ((totallyRamifiedOfDegree K n).encard : ℝ≥0∞) =
      ∑' j : ℕ, ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) := by
  have h1 : ((totallyRamifiedOfDegree K n).encard : ℝ≥0∞) =
      ∑' _ : totallyRamifiedOfDegree K n, (1 : ℝ≥0∞) := by simp
  rw [h1]
  conv_lhs => rw [totallyRamifiedOfDegree_eq_iUnion_wildExponent n]
  rw [tsum_iUnion (f := fun _ ↦ (1 : ℝ≥0∞)) (pairwiseDisjoint_wildExponent n)]
  refine tsum_congr fun j ↦ ?_
  rw [ENNReal.tsum_set_const, mul_one,
    ← (finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
    ENat.toENNReal_coe]

/-- Whenever `(n : K) ≠ 0`, `σ_K(n)` is finite. -/
theorem finite_totallyRamifiedOfDegree_of_natCast_ne_zero {n : ℕ} (hnK : (n : K) ≠ 0) :
    (totallyRamifiedOfDegree K n).Finite :=
  (finite_totallyRamifiedOfDegree_wildExponent_le n (n * natCastValuation K n hnK)).subset
    fun _ hE ↦ ⟨hE, IntermediateField.wildExponent_le_mul_natCastValuation hE hnK⟩

/-- Whenever `(n : K) ≠ 0`, `#σ_K(n)` is the finite sum of the stratum counts over
`0 ≤ j ≤ n * v_K(n)`. -/
theorem ncard_totallyRamifiedOfDegree_eq_sum {n : ℕ} (hnK : (n : K) ≠ 0) :
    (totallyRamifiedOfDegree K n).ncard =
      ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1),
        {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard := by
  set M := n * natCastValuation K n hnK + 1
  have hunion : totallyRamifiedOfDegree K n =
      ⋃ j ∈ (Finset.range M : Set ℕ), {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} := by
    ext E
    simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range, Set.mem_ofPred_eq, exists_prop]
    exact ⟨fun hE ↦ ⟨E.wildExponent,
        Nat.lt_succ_of_le (IntermediateField.wildExponent_le_mul_natCastValuation hE hnK), hE, rfl⟩,
      fun ⟨_, _, hE, _⟩ ↦ hE⟩
  have hdisj : (Finset.range M : Set ℕ).PairwiseDisjoint
      (fun j ↦ {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}) :=
    (pairwiseDisjoint_wildExponent n).subset (Set.subset_univ _)
  conv_lhs => rw [hunion]
  rw [(Finset.finite_toSet _).ncard_biUnion
    (fun j _ ↦ finite_totallyRamifiedOfDegree_wildExponent_eq n j) hdisj]
  simp only [Finset.mem_coe, finsum_mem_finset_eq_sum]

/-- Whenever `(n : K) ≠ 0`, `#σ_K(n)` equals the finite sum of `krasnerCount K n j` over
`0 ≤ j ≤ n * v_K(n)`. -/
theorem ncard_totallyRamifiedOfDegree_eq_sum_krasnerCount {n : ℕ} (hnK : (n : K) ≠ 0) :
    ((totallyRamifiedOfDegree K n).ncard : ℚ) =
      ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1), krasnerCount K n j := by
  rw [ncard_totallyRamifiedOfDegree_eq_sum hnK, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ ↦ krasner_refined_count n j

/-- **Total count of all extensions of degree `n`**: for `0 < n`, the extended cardinality of the
set of all degree-`n` subextensions of `SeparableClosure K` equals `∑_{f ∣ n} #σ_{K_f}(n / f)`,
where `K_f = unramifiedExtension K (SeparableClosure K) f` carries its canonical local-field
structure. -/
theorem encard_finrank_eq_sum_encard_totallyRamifiedOfDegree {n : ℕ} (hn : 0 < n) :
    {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = n}.encard =
      ∑ f ∈ n.divisors,
        let U := unramifiedExtension K (SeparableClosure K) f
        letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
        letI := finiteIntermediateFieldTopology K (SeparableClosure K) U
        haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
        (totallyRamifiedOfDegree U (n / f)).encard := by
  let S (f : ℕ) : Set (IntermediateField K (SeparableClosure K)) :=
    {L | Module.finrank K L = n ∧ L.inertiaDegree = f}
  have hunion : {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = n} =
      ⋃ f ∈ (n.divisors : Set ℕ), S f := by
    ext L
    simp only [S, Set.mem_iUnion, Finset.mem_coe, Nat.mem_divisors, Set.mem_ofPred_eq, exists_prop]
    refine ⟨fun hL ↦ ⟨L.inertiaDegree, ⟨?_, hn.ne'⟩, hL, rfl⟩, fun ⟨_, _, hL, _⟩ ↦ hL⟩
    have : Module.Finite K L := Module.finite_of_finrank_pos (hL ▸ hn)
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    rw [IntermediateField.inertiaDegree_eq]
    exact ⟨ramificationIndex K L, by rw [mul_comm, ramificationIndex_mul_inertiaDegree K L, hL]⟩
  have hdisj : (n.divisors : Set ℕ).PairwiseDisjoint S := by
    intro f₁ _ f₂ _ hne
    exact Set.disjoint_left.mpr fun _ h₁ h₂ ↦ hne (h₁.2.symm.trans h₂.2)
  rw [hunion, (Finset.finite_toSet n.divisors).encard_biUnion hdisj]
  simp only [Finset.mem_coe, finsum_mem_finset_eq_sum]
  refine Finset.sum_congr rfl fun f hf ↦ ?_
  have hdvd : f ∣ n := Nat.dvd_of_mem_divisors hf
  have hf0 : f ≠ 0 := ne_zero_of_dvd_ne_zero hn.ne' hdvd
  have hmul : f * (n / f) = n := Nat.mul_div_cancel' hdvd
  simpa only [S, hmul] using encard_finrank_and_inertiaDegree_eq (K := K) hf0 (n / f)

end TauCeti
