/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Box
public import TauCeti.NumberTheory.LocalField.MassFormula.Main
public import TauCeti.NumberTheory.LocalField.Unramified.IntermediateField
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.NumberTheory.LocalField.MassFormula.Integral

/-!
# Krasner's discriminant-refined count of local field extensions

Let `K` be a nonarchimedean local field with residue cardinality `q = #𝓀[K]`, and let
`σ_K(n) = TauCeti.totallyRamifiedOfDegree K n`. For `L ∈ σ_K(n)` with discriminant exponent `d(L)`,
Serre's wild exponent is `c(L) = d(L) - n + 1` (`IntermediateField.wildExponent`). Building on Ore's
realizability theorem and Krasner's discriminant box `TauCeti.eisensteinBox K n j`, this file counts
the members of `σ_K(n)` of each wild exponent `j` in arbitrary characteristic, specializes the
formula to `ℚ_[p]`, checks consistency with Serre's mass formulas, and derives total degree-`n`
counts.

## Main definitions and results

* `TauCeti.krasnerCount`, `TauCeti.krasner_refined_count`, and
  `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_of_measure_eisensteinBox`: Krasner's
  discriminant-refined count of `{E ∈ σ_K(n) | c(E) = j}`.
* `TauCeti.finite_totallyRamifiedOfDegree_wildExponent_le` and
  `TauCeti.finite_totallyRamifiedOfDegree_discriminantExponent_le`: bounded-height finiteness in
  every characteristic.
* `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_padic`: Pauli–Roblot closed form over
  `ℚ_[p]`, yielding `#σ_{ℚ_2}(2) = 6`, `#σ_{ℚ_3}(3) = 21`, and `#σ_{ℚ_2}(4) = 92`.
* `TauCeti.tsum_ncard_wildExponent_div_natCard_residueField_pow`,
  `TauCeti.hasSum_krasnerCount_div_natCard_residueField_pow`, and
  `TauCeti.IsRepresentativeSet.tsum_one_div_natCard_algEquiv_wildExponent_eq`: mass consistency.
* `TauCeti.encard_totallyRamifiedOfDegree_eq_tsum`,
  `TauCeti.ncard_totallyRamifiedOfDegree_eq_sum_of_cast_ne_zero`, and
  `TauCeti.encard_finrank_eq_sum_totallyRamifiedOfDegree`: total counts by degree.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `p`-adique*, Éditions du CNRS,
  Paris (1966), 143–169.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Theorem 6.1.
-/

public section
noncomputable section

open MeasureTheory Polynomial ValuativeRel
open TauCeti.Polynomial (monicOfCoeff natDegree_monicOfCoeff)
open scoped ENNReal IntermediateField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Krasner's discriminant-refined count -/

variable (K) in
/-- **Krasner's refined count**: rational expression for the number of totally ramified degree-`n`
extensions of `K` inside `SeparableClosure K` with wild exponent `j`, equal to `0` outside Ore's
admissible wild exponents. -/
def krasnerCount (n j : ℕ) : ℚ := by
  classical
  let q : ℚ := Nat.card 𝓀[K]
  exact if IsOreAdmissible K n j then
    n * q ^ (((n + j - 1 : ℕ) : ℤ) -
      ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h : ℕ) : ℤ)) *
        (if j % n = 0 then 1 else 1 - q⁻¹)
  else 0

/-- In degree `0`, `krasnerCount` vanishes. -/
@[simp]
theorem krasnerCount_zero_left (j : ℕ) : krasnerCount K 0 j = 0 := by
  classical simp [krasnerCount]

/-- Outside Ore's admissible wild exponents, `krasnerCount` vanishes. -/
theorem krasnerCount_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    krasnerCount K n j = 0 := by
  classical rw [krasnerCount, ite_eq_right h]

/-- On an Ore-admissible wild exponent, `krasnerCount` unfolds to Krasner's box formula. -/
theorem krasnerCount_of_isOreAdmissible {n j : ℕ} (h : IsOreAdmissible K n j) :
    krasnerCount K n j =
      (n : ℚ) * (Nat.card 𝓀[K] : ℚ) ^ (((n + j - 1 : ℕ) : ℤ) -
        ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h : ℕ) : ℤ)) *
          (if j % n = 0 then 1 else 1 - (Nat.card 𝓀[K] : ℚ)⁻¹) := by
  classical rw [krasnerCount, ite_eq_left h]

/-- **Bounded-height finiteness**: for every local field `K` (including in equal characteristic)
and every `n, D : ℕ`, only finitely many members of `totallyRamifiedOfDegree K n` have wild
exponent at most `D`. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent ≤ D}.Finite := by
  have htsum : ∑' L : totallyRamifiedOfDegree K n,
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent ≠ ∞ := by
    rw [tsum_one_div_natCard_residueField_pow_wildExponent]; exact ENNReal.natCast_ne_top n
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ^ D ≠ ∞ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  refine ((ENNReal.finite_const_le_of_tsum_ne_top htsum
    (ENNReal.div_pos one_ne_zero hq).ne').image Subtype.val).subset fun E ⟨hE, hle⟩ ↦
      ⟨⟨E, hE⟩, ENNReal.div_le_div_left
        (pow_le_pow_right₀ (Nat.one_le_cast.mpr Nat.card_pos) hle) 1, rfl⟩

/-- **Bounded-discriminant finiteness**: for every local field `K` and `n, D : ℕ`, only finitely
many members of `totallyRamifiedOfDegree K n` have discriminant exponent at most `D`. -/
theorem finite_totallyRamifiedOfDegree_discriminantExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.discriminantExponent ≤ D}.Finite :=
  (finite_totallyRamifiedOfDegree_wildExponent_le (K := K) n (D + 1)).subset fun E ⟨hE, hd⟩ ↦
    ⟨hE, by rw [IntermediateField.wildExponent_def]; omega⟩

/-- For every `n, j : ℕ`, the stratum `{E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}` is
finite. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite :=
  (finite_totallyRamifiedOfDegree_wildExponent_le n j).subset fun _ ⟨hE, hj⟩ ↦ ⟨hE, hj.le⟩

/-- If `L ∈ σ_K(n)` contains a root of an Eisenstein polynomial `monicOfCoeff a`, then
`a ∈ eisensteinBox K n L.wildExponent`. -/
private theorem mem_eisensteinBox_of_rootCount_ne_zero {n : ℕ} (hn : 0 < n)
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinSet K n) (hrc : L.rootCount a ≠ 0) :
    a ∈ eisensteinBox K n L.wildExponent := by
  have hL' := mem_totallyRamifiedOfDegree_iff.mp hL
  have := hL'.2.finite
  obtain ⟨y, hy⟩ :=
    Multiset.card_pos_iff_exists_mem.mp (pos_iff_ne_zero.mpr (L.rootCount_def a ▸ hrc))
  have hx : aeval (L.val y) (monicOfCoeff a) = 0 := by
    rw [aeval_algHom_apply, (mem_aroots.mp hy).2, map_zero]
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  have hzdeg := (mem_totallyRamifiedOfDegree_iff.mp
    (adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg (hf.symm ▸ hx))).1
  have hgen : K⟮L.val y⟯ = L := IntermediateField.eq_of_le_of_finrank_eq
    (IntermediateField.adjoin_simple_le_iff.mpr y.2) (hzdeg.trans hL'.1.symm)
  exact (mem_eisensteinBox_iff_wildExponent_adjoin_eq hn ha hx).mpr (congrArg _ hgen)

/-- For `L ∈ σ_K(n)` of wild exponent `j`, the integral of `L.rootCount` over `eisensteinBox K n j`
equals its integral over `eisensteinSet K n`. -/
private theorem setLIntegral_eisensteinBox_rootCount {n j : ℕ} (hn : 0 < n)
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    (hj : L.wildExponent = j) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hsplit := lintegral_inter_add_sdiff (μ := μ) (fun a ↦ (L.rootCount a : ℝ≥0∞))
    (eisensteinSet K n) (measurableSet_eisensteinBox (K := K) n j)
  rw [Set.inter_eq_self_of_subset_right (eisensteinBox_subset_eisensteinSet n j)] at hsplit
  have hdiff : ∫⁻ a in eisensteinSet K n \ eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ = 0 := by
    refine (setLIntegral_congr_fun
      (measurableSet_eisensteinSet.diff (measurableSet_eisensteinBox n j)) fun a ⟨heis, hnot⟩ ↦ ?_
      ).trans lintegral_zero
    exact Nat.cast_eq_zero.mpr (Classical.byContradiction fun hrc ↦
      hnot (hj ▸ mem_eisensteinBox_of_rootCount_ne_zero hn hL heis hrc))
  have hrel := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hL
  have hdj : L.discriminantExponent + 1 = n + j := by omega
  rw [hdiff, add_zero, L.lintegral_rootCount hL μ hμ, hdj] at hsplit
  exact hsplit

/-- Pointwise on `eisensteinBox K n j`, root counts over the `j`-stratum of `σ_K(n)` sum to `n`. -/
private theorem sum_rootCount_eq_of_mem_eisensteinBox {n j : ℕ} (hn : 0 < n)
    {a : Fin n → K} (ha : a ∈ eisensteinBox K n j) :
    (∑ L ∈ (finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).toFinset,
      (L.rootCount a : ℝ≥0∞)) = n := by
  classical
  set hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  have heis := eisensteinBox_subset_eisensteinSet n j ha
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp heis
  rw [← tsum_rootCount_eq_of_separable he hf (separable_monicOfCoeff_of_mem_eisensteinBox ha),
    tsum_subtype (totallyRamifiedOfDegree K n) (fun L ↦ (L.rootCount a : ℝ≥0∞)),
    tsum_eq_sum (s := hfin.toFinset)]
  · exact Finset.sum_congr rfl fun L hL ↦ by simp [(hfin.mem_toFinset.mp hL).1]
  · intro L hnot
    rw [hfin.mem_toFinset] at hnot
    by_cases hmem : L ∈ totallyRamifiedOfDegree K n
    · simp only [Set.indicator_of_mem hmem, Nat.cast_eq_zero]
      by_contra hrc
      exact Set.disjoint_left.mp (pairwiseDisjoint_eisensteinBox (K := K) n trivial trivial
        fun hj ↦ hnot ⟨hmem, hj⟩) (mem_eisensteinBox_of_rootCount_ne_zero hn hmem heis hrc) ha
    · simp [hmem]

/-- **Measure form of Krasner's count**: for `0 < n` and normalized left-invariant measure `μ`,
`# {E ∈ σ_K(n) | c(E) = j} * q ^ (-(n + j)) * (1 - q⁻¹) = n * μ (eisensteinBox K n j)`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_mul_measure_eisensteinBox {n : ℕ}
    (hn : 0 < n) (j : ℕ) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
      (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) =
      (n : ℝ≥0∞) * μ (eisensteinBox K n j) := by
  set hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  set B := eisensteinBox K n j
  have haemeas (L : IntermediateField K (SeparableClosure K)) (hL : L ∈ hfin.toFinset) :
      AEMeasurable (fun a ↦ (L.rootCount a : ℝ≥0∞)) (μ.restrict B) :=
    (aemeasurable_rootCount_restrict_eisensteinSet μ (hfin.mem_toFinset.mp hL).1).mono_set
      (eisensteinBox_subset_eisensteinSet n j)
  calc ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)))
      = ∑ L ∈ hfin.toFinset, ∫⁻ a in B, (L.rootCount a : ℝ≥0∞) ∂μ := by
        rw [Set.ncard_eq_toFinset_card _ hfin, ← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_congr rfl fun L hL ↦
          (setLIntegral_eisensteinBox_rootCount hn (hfin.mem_toFinset.mp hL).1
            (hfin.mem_toFinset.mp hL).2 μ hμ).symm
    _ = ∫⁻ a in B, ∑ L ∈ hfin.toFinset, (L.rootCount a : ℝ≥0∞) ∂μ :=
        (lintegral_finsetSum' hfin.toFinset haemeas).symm
    _ = ∫⁻ _ in B, (n : ℝ≥0∞) ∂μ := setLIntegral_congr_fun (measurableSet_eisensteinBox n j)
        fun _ ha ↦ sum_rootCount_eq_of_mem_eisensteinBox hn ha
    _ = (n : ℝ≥0∞) * μ B := setLIntegral_const _ _

/-- **Krasner's theorem in measure form**: for `0 < n` and normalized left-invariant measure `μ`,
`# {E ∈ σ_K(n) | c(E) = j} = n * q ^ (n + j) * μ (eisensteinBox K n j) / (1 - q⁻¹)` in `ℝ≥0∞`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_of_measure_eisensteinBox {n : ℕ}
    (hn : 0 < n) (j : ℕ) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) =
      (n : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * μ (eisensteinBox K n j) /
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hid := ncard_totallyRamifiedOfDegree_wildExponent_eq_mul_measure_eisensteinBox hn j μ hμ
  set q := (Nat.card 𝓀[K] : ℝ≥0∞)
  set N := ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞)
  have hq1 : (1 : ℝ≥0∞) < q := Nat.one_lt_cast.mpr (Finite.one_lt_card (α := 𝓀[K]))
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq1).ne'
  have hqt : q ≠ ⊤ := ENNReal.natCast_ne_top _
  have hu0 : 1 - 1 / q ≠ 0 :=
    (tsub_pos_iff_lt.mpr (by rw [one_div]; exact ENNReal.inv_lt_one.mpr hq1)).ne'
  have hu_top : 1 - 1 / q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hinv : 1 / q ^ (n + j) * q ^ (n + j) = 1 := by
    rw [one_div]; exact ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt)
  rw [ENNReal.eq_div_iff hu0 hu_top]
  calc (1 - 1 / q) * N = (1 - 1 / q) * N * (1 / q ^ (n + j) * q ^ (n + j)) := by rw [hinv, mul_one]
    _ = N * (1 / q ^ (n + j) * (1 - 1 / q)) * q ^ (n + j) := by ring
    _ = (n : ℝ≥0∞) * q ^ (n + j) * μ (eisensteinBox K n j) := by rw [hid]; ring

/-- Converting the `ℝ≥0∞` volume identity on an Ore-admissible box into `krasnerCount K n j`. -/
private theorem cast_ncard_eq_krasnerCount_of_isOreAdmissible {n j : ℕ} (hn : 0 < n)
    (hadm : IsOreAdmissible K n j) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) = krasnerCount K n j := by
  let _ : MeasurableSpace (Fin n → K) := borel _
  have _ : BorelSpace (Fin n → K) := ⟨rfl⟩
  let B : TopologicalSpace.PositiveCompacts (Fin n → K) :=
    ⟨⟨integerBox K (Fin n), isCompact_integerBox⟩, by
      rw [isOpen_integerBox.interior_eq]; exact ⟨0, by simp⟩⟩
  let μ := Measure.addHaarMeasure B
  -- Substitute the Haar volume of `eisensteinBox K n j` and cancel `1 - q⁻¹`.
  have hid0 := ncard_totallyRamifiedOfDegree_wildExponent_eq_of_measure_eisensteinBox hn j μ
    Measure.addHaarMeasure_self
  rw [measure_eisensteinBox hn hadm μ Measure.addHaarMeasure_self] at hid0
  rw [krasnerCount_of_isOreAdmissible hadm]
  set q := Nat.card 𝓀[K]
  set N := {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard
  have hq1 : 1 < q := Finite.one_lt_card (α := 𝓀[K])
  have hq0_enn : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq1).ne'
  have hqt_enn : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hu0 : 1 - 1 / (q : ℝ≥0∞) ≠ 0 :=
    (tsub_pos_iff_lt.mpr
      (by rw [one_div]; exact ENNReal.inv_lt_one.mpr (by exact_mod_cast hq1))).ne'
  have hu_top : 1 - 1 / (q : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  set sd := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  have hid : (N : ℝ≥0∞) = (n : ℝ≥0∞) * (q : ℝ≥0∞) ^ (n + j) *
      (1 / (q : ℝ≥0∞) ^ (1 + sd) * if j % n = 0 then 1 else 1 - 1 / (q : ℝ≥0∞)) := by
    rw [hid0]; symm; rw [ENNReal.eq_div_iff hu0 hu_top]; ring
  -- Clear powers of `q` uniformly in `ℕ` and cast to `ℚ`.
  let c : ℕ := if j % n = 0 then q else q - 1
  have hc_enn : (if j % n = 0 then (1 : ℝ≥0∞) else 1 - 1 / (q : ℝ≥0∞)) * q = c := by
    dsimp only [c]; split_ifs
    · simp
    · rw [ENNReal.sub_mul fun _ _ ↦ hqt_enn, one_mul, one_div,
        ENNReal.inv_mul_cancel hq0_enn hqt_enn, ENNReal.natCast_sub, Nat.cast_one]
  have hmul : (N : ℝ≥0∞) * (q : ℝ≥0∞) ^ (1 + sd + 1) = (n : ℝ≥0∞) * (q : ℝ≥0∞) ^ (n + j) * c := by
    rw [hid, pow_succ, ← hc_enn]
    calc _ = (n : ℝ≥0∞) * (q : ℝ≥0∞) ^ (n + j) *
          (((q : ℝ≥0∞) ^ (1 + sd))⁻¹ * (q : ℝ≥0∞) ^ (1 + sd)) *
          ((if j % n = 0 then 1 else 1 - (q : ℝ≥0∞)⁻¹) * q) := by simp only [one_div]; ring
      _ = _ := by
        rw [ENNReal.inv_mul_cancel (pow_ne_zero _ hq0_enn) (ENNReal.pow_ne_top hqt_enn), mul_one,
          one_div]
  have hnat : N * q ^ (1 + sd + 1) = n * q ^ (n + j) * c := by exact_mod_cast hmul
  have hq0_rat : (q : ℚ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq1).ne'
  have hc_rat : (c : ℚ) = (if j % n = 0 then 1 else 1 - (q : ℚ)⁻¹) * q := by
    dsimp only [c]; split_ifs
    · simp
    · simp [Nat.cast_sub hq1.le, sub_mul, inv_mul_cancel₀ hq0_rat]
  have hrat : (N : ℚ) * (q : ℚ) ^ (1 + sd + 1) =
      (n : ℚ) * (q : ℚ) ^ (n + j) * (if j % n = 0 then 1 else 1 - (q : ℚ)⁻¹) * q := by
    simpa [hc_rat, mul_assoc] using congrArg (Nat.cast (R := ℚ)) hnat
  have hexp : ((n + j - 1 : ℕ) : ℤ) - (sd : ℤ) = ((n + j : ℕ) : ℤ) - ((1 + sd : ℕ) : ℤ) := by
    omega
  rw [hexp, zpow_sub₀ hq0_rat, zpow_natCast, zpow_natCast]
  refine mul_right_cancel₀ (pow_ne_zero (1 + sd + 1) hq0_rat) ?_
  rw [hrat, pow_succ]
  conv_lhs =>
    enter [1, 1, 2]
    rw [← div_mul_cancel₀ ((q : ℚ) ^ (n + j)) (pow_ne_zero (1 + sd) hq0_rat)]
  ring

/-- **Krasner's discriminant-refined count**: for `0 < n` and any local field `K` (including in
equal characteristic), the members of `totallyRamifiedOfDegree K n` with wild exponent `j` form a
finite set of cardinality `krasnerCount K n j`. -/
theorem krasner_refined_count (n j : ℕ) (hn : 0 < n) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite ∧
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) =
        krasnerCount K n j := by
  refine ⟨finite_totallyRamifiedOfDegree_wildExponent_eq n j, ?_⟩
  by_cases hadm : IsOreAdmissible K n j
  · exact cast_ncard_eq_krasnerCount_of_isOreAdmissible hn hadm
  · have hempty : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun E ⟨hE, hj⟩ ↦
        hadm ((ore_realizability n j hn).mp ⟨E, hE, hj⟩)
    rw [krasnerCount_of_not_isOreAdmissible hadm, hempty, Set.ncard_empty, Nat.cast_zero]

/-! ### Closed form over `ℚ_[p]` -/

/-- Evaluating `∑_{h ∈ Ico 1 n} min (j / n + [h < j % n]) (v_p(h))` for Ore-admissible `(n, j)`. -/
private theorem sum_min_padicValNat_ore (p : ℕ) [Fact p.Prime] {n j : ℕ} (hn : 0 < n)
    (hadm : IsOreAdmissible ℚ_[p] n j) :
    (∑ h ∈ Finset.Ico 1 n, min (j / n + if h < j % n then 1 else 0) (padicValNat p h)) + j / n =
      (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) +
        if j % n = 0 then 0 else (j % n) / p ^ (j / n + 1) := by
  set a := j / n; set b := j % n
  have hb_lt : b < n := Nat.mod_lt j hn
  have ha_le : a ≤ padicValNat p n :=
    Nat.div_le_of_le_mul (mul_comm n _ ▸ ((isOreAdmissible_padic_iff p hn).mp hadm).2)
  -- Express `min m (v_p(h))` as a divisor indicator sum and count multiples in `Ico 1 m`.
  have hmin (m : ℕ) {h : ℕ} (hh : h ≠ 0) :
      min m (padicValNat p h) = ∑ i ∈ Finset.Icc 1 m, if p ^ i ∣ h then 1 else 0 := by
    have hdvd (i : ℕ) : p ^ i ∣ h ↔ i ≤ padicValNat p h :=
      Nat.padicValNat_def ▸ multiplicity_dvd_iff_le hh
    have hflt : (Finset.Icc 1 m).filter (· ≤ padicValNat p h) =
        Finset.Icc 1 (min m (padicValNat p h)) := by ext; simp [le_min_iff, and_assoc]
    simp only [hdvd, ← Finset.card_filter, hflt, Nat.card_Icc]; omega
  have hdiv {m : ℕ} (hm : 0 < m) (d : ℕ) :
      (∑ h ∈ Finset.Ico 1 m, if d ∣ h then 1 else 0) + (if d ∣ m then 1 else 0) = m / d := by
    have hIoc : Finset.Ioc 0 m = insert m (Finset.Ico 1 m) := by ext; simp; omega
    have hcard := Nat.Ioc_filter_dvd_card_eq_div m d
    rw [Finset.card_filter, hIoc, Finset.sum_insert (by simp)] at hcard; omega
  -- Swap sums on `1 ≤ i ≤ a`, using `p ^ i ∣ n` from `a ≤ v_p(n)`.
  have hsum_base : (∑ i ∈ Finset.Icc 1 a, ∑ h ∈ Finset.Ico 1 n, if p ^ i ∣ h then 1 else 0) + a =
      ∑ i ∈ Finset.Icc 1 a, n / p ^ i := by
    have ha_sum : a = ∑ _i ∈ Finset.Icc 1 a, 1 := by simp
    conv_lhs => enter [2]; rw [ha_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hdvd_n : p ^ i ∣ n := (multiplicity_dvd_iff_le hn.ne').mpr
      (Nat.padicValNat_def ▸ (Finset.mem_Icc.mp hi).2.trans ha_le)
    simpa [hdvd_n] using hdiv hn (p ^ i)
  -- Split off the `p ^ (a + 1)` term for `h < b`.
  have hsplit (h : ℕ) (hh : h ∈ Finset.Ico 1 n) :
      min (a + if h < b then 1 else 0) (padicValNat p h) =
        (∑ i ∈ Finset.Icc 1 a, if p ^ i ∣ h then 1 else 0) +
          if h < b ∧ p ^ (a + 1) ∣ h then 1 else 0 := by
    have hh0 : h ≠ 0 := by have := (Finset.mem_Ico.mp hh).1; omega
    by_cases hlt : h < b
    · simp only [hlt, ↓reduceIte, true_and]
      rw [hmin (a + 1) hh0, Finset.sum_Icc_succ_top (Nat.le_add_left 1 a)]
    · simp [hlt, hmin a hh0]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_comm,
    add_right_comm _ _ a, hsum_base]
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · simp [hb0]
  · have hvb : padicValNat p b ≤ a := by
      rcases isOreAdmissible_iff.mp hadm with ⟨h0, -⟩ | ⟨-, hv, -⟩
      · omega
      · rwa [_root_.Padic.natValuation_of_ne_zero p hbpos.ne', Nat.cast_le] at hv
    have hnot_dvd_b : ¬ p ^ (a + 1) ∣ b := by
      rw [multiplicity_dvd_iff_le hbpos.ne', ← Nat.padicValNat_def]; omega
    simp only [hbpos.ne', ↓reduceIte]
    have hb_div : (∑ h ∈ Finset.Ico 1 b, if p ^ (a + 1) ∣ h then 1 else 0) = b / p ^ (a + 1) := by
      simpa [hnot_dvd_b] using hdiv hbpos (p ^ (a + 1))
    rw [← hb_div, ← Finset.sum_subset (Finset.Ico_subset_Ico_right hb_lt.le)]
    · exact congrArg _ (Finset.sum_congr rfl fun h hh ↦ by simp [(Finset.mem_Ico.mp hh).2])
    · intro h hh hnot
      have hge : ¬ h < b := fun hlt ↦ hnot (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hh).1, hlt⟩)
      simp [hge]

/-- Over `ℚ_[p]`, evaluating `∑_{h ∈ Ico 1 n} oreCoefficientDepth ℚ_[p] n j h` yields the exponent
of Pauli–Roblot Theorem 6.1. -/
private theorem sum_oreCoefficientDepth_padic (p : ℕ) [Fact p.Prime] {n j : ℕ} (hn : 0 < n)
    (hadm : IsOreAdmissible ℚ_[p] n j) :
    ((n + j - 1 : ℕ) : ℤ) -
      ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth ℚ_[p] n j h : ℕ) : ℤ) =
      ((∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i : ℕ) : ℤ) +
        if j % n = 0 then 0 else (((j % n) / p ^ (j / n + 1) : ℕ) : ℤ) + 1 := by
  have hb_lt : j % n < n := Nat.mod_lt j hn
  have hterm (h : ℕ) (hh : h ∈ Finset.Ico 1 n) :
      oreCoefficientDepth ℚ_[p] n j h +
        min (j / n + if h < j % n then 1 else 0) (padicValNat p h) =
        j / n + 1 + if h < j % n then 1 else 0 := by
    have hhK : (h : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Ico.mp hh).1; omega)
    rw [oreCoefficientDepth_of_cast_ne_zero ℚ_[p] n j hhK,
      _root_.Padic.natCastValuation_eq_padicValNat]; omega
  have hflt : (Finset.Ico 1 n).filter (· < j % n) = Finset.Ico 1 (j % n) := by ext; simp; omega
  have hsum_add : (∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth ℚ_[p] n j h) +
      (∑ h ∈ Finset.Ico 1 n, min (j / n + if h < j % n then 1 else 0) (padicValNat p h)) =
      (n - 1) * (j / n + 1) + (j % n - 1) := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Ico, smul_eq_mul, ← Finset.card_filter, hflt, Nat.card_Ico]
  have hmin := sum_min_padicValNat_ore p hn hadm
  have hmul : (n - 1) * (j / n + 1) + (j / n + 1) + j % n = j + n := by
    rw [← add_one_mul, Nat.sub_add_cancel (m := 1) hn, mul_add_one, add_right_comm, Nat.div_add_mod]
  rcases eq_or_ne (j % n) 0 with hb0 | hb0
  · rw [ite_eq_left hb0] at hmin; rw [ite_eq_left hb0]; omega
  · rw [ite_eq_right hb0] at hmin; rw [ite_eq_right hb0]; omega

open scoped Classical in
/-- **Pauli–Roblot closed form for Krasner's count over `ℚ_[p]`** ([Pauli–Roblot 2001, Theorem
6.1]): for `0 < n`, the number of totally ramified degree-`n` extensions of `ℚ_[p]` with wild
exponent `j` is `n * p ^ (∑_{i=1}^{j/n} n / p^i)` when `n ∣ j` (and `j` is Ore-admissible),
`n * (p - 1) * p ^ (∑_{i=1}^{j/n} n / p^i + (j % n) / p^{j/n + 1})` when `¬ n ∣ j` (and `j` is
Ore-admissible), and `0` otherwise. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_padic (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : 0 < n) (j : ℕ) :
    {E ∈ totallyRamifiedOfDegree ℚ_[p] n | E.wildExponent = j}.ncard =
      if IsOreAdmissible ℚ_[p] n j then
        if j % n = 0 then
          n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)
        else
          n * (p - 1) * p ^ ((∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) +
            (j % n) / p ^ (j / n + 1))
      else 0 := by
  have hp_pos : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply Nat.cast_injective (R := ℚ)
  rw [(krasner_refined_count (K := ℚ_[p]) n j hn).2]
  by_cases hadm : IsOreAdmissible ℚ_[p] n j
  · rw [krasnerCount_of_isOreAdmissible hadm, ite_eq_left hadm, _root_.Padic.natCard_residueField p,
      sum_oreCoefficientDepth_padic p hn hadm]
    rcases eq_or_ne (j % n) 0 with hb0 | hb
    · simp only [hb0, ↓reduceIte, add_zero, zpow_natCast, mul_one]; push_cast; rfl
    · simp only [hb, ↓reduceIte]
      rw [← add_assoc, ← Nat.cast_add, zpow_add_one₀ hp_pos.ne', zpow_natCast]
      push_cast [Nat.cast_sub (Fact.out : p.Prime).pos]; field_simp
  · rw [krasnerCount_of_not_isOreAdmissible hadm, ite_eq_right hadm, Nat.cast_zero]

/-! ### Mass consistency and isomorphism-class mass at height `j` -/

/-- **Regrouped Serre mass consistency**: summing `# {E ∈ σ_K(n) | c(E) = j} * q ^ (-j)` over all
wild exponents `j` recovers `n`, Serre's first mass formula grouped by wild exponent. -/
theorem tsum_ncard_wildExponent_div_natCard_residueField_pow (n : ℕ) :
    ∑' j : ℕ, ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ j = n := by
  rw [← tsum_one_div_natCard_residueField_pow_wildExponent (K := K) (n := n)]
  set S := totallyRamifiedOfDegree K n
  set q := (Nat.card 𝓀[K] : ℝ≥0∞)
  rw [← tsum_fiberwise (fun L : S ↦ 1 / q ^ L.1.wildExponent) (fun L ↦ L.1.wildExponent)]
  refine tsum_congr fun j ↦ ?_
  have hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  calc ({E ∈ S | E.wildExponent = j}.ncard : ℝ≥0∞) / q ^ j
      = ∑' E : {E ∈ S | E.wildExponent = j}, 1 / q ^ E.1.wildExponent := by
        rw [tsum_congr fun E ↦ by rw [E.2.2], ENNReal.tsum_set_const, ← hfin.cast_ncard_eq,
          ENat.toENNReal_coe, div_eq_mul_inv, one_div]
    _ = ∑' L : ((fun L : S ↦ L.1.wildExponent) ⁻¹' {j}), 1 / q ^ L.1.1.wildExponent :=
        ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ S) (fun E ↦ E.wildExponent = j)).tsum_eq
          fun E ↦ 1 / q ^ E.1.wildExponent).symm

/-- **Real-series consistency of `krasnerCount` with Serre's first mass formula**: for `0 < n`,
the real series `∑_j krasnerCount K n j / q ^ j` converges to `n`. -/
theorem hasSum_krasnerCount_div_natCard_residueField_pow {n : ℕ} (hn : 0 < n) :
    HasSum (fun j : ℕ ↦ (krasnerCount K n j : ℝ) / (Nat.card 𝓀[K] : ℝ) ^ j) n := by
  have hterm (j : ℕ) : (krasnerCount K n j : ℝ) / (Nat.card 𝓀[K] : ℝ) ^ j =
      (({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ j).toReal := by
    have hkc : (krasnerCount K n j : ℝ) =
        ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ) := by
      exact_mod_cast (krasner_refined_count (K := K) n j hn).2.symm
    rw [hkc, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  simp_rw [hterm]
  have htsum := tsum_ncard_wildExponent_div_natCard_residueField_pow (K := K) n
  have hne := htsum ▸ ENNReal.natCast_ne_top n
  rw [← ENNReal.toReal_natCast n, ← htsum, ENNReal.tsum_toReal_eq (ne_top_of_tsum_ne_top hne)]
  exact ENNReal.hasSum_toReal hne

namespace IsRepresentativeSet

/-- **Isomorphism-class mass at wild exponent `j`**: for `0 < n` and any representative set `R` of
`σ_K(n)`, the `K`-isomorphism classes in `R` with wild exponent `j` have total automorphism-weighted
mass `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = # {E ∈ σ_K(n) | c(E) = j} / n`. -/
theorem tsum_one_div_natCard_algEquiv_wildExponent_eq {n : ℕ}
    {R : Set (IntermediateField K (SeparableClosure K))} (hR : IsRepresentativeSet n R)
    (hn : 0 < n) (j : ℕ) :
    ∑' M : {M ∈ R | M.wildExponent = j}, 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) / n := by
  classical
  set S := totallyRamifiedOfDegree K n
  let w (M : IntermediateField K (SeparableClosure K)) : ℝ≥0∞ := 1 / Nat.card (M ≃ₐ[K] M)
  have h := hR.tsum_eq_tsum_div_natCard_algEquiv_mul
    (fun L ↦ if L.wildExponent = j then (1 : ℝ≥0∞) else 0)
    fun e ↦ by rw [IntermediateField.wildExponent_eq_of_algEquiv e]
  have hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  have hlhs : (∑' L : S, if L.1.wildExponent = j then (1 : ℝ≥0∞) else 0) =
      ({E ∈ S | E.wildExponent = j}.ncard : ℝ≥0∞) := by
    have hsub := tsum_subtype ({L : S | L.1.wildExponent = j}) (fun _ : S ↦ (1 : ℝ≥0∞))
    simp only [Set.indicator_apply, Set.mem_ofPred_eq] at hsub
    rw [← hsub, ← ENat.toENNReal_coe, hfin.cast_ncard_eq, ← ENNReal.tsum_set_one]
    exact (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ S)
      (fun E ↦ E.wildExponent = j)).tsum_eq fun _ ↦ (1 : ℝ≥0∞)
  have hrhs : (∑' M : R, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) *
      if M.1.wildExponent = j then 1 else 0) =
      (n : ℝ≥0∞) * ∑' M : {M ∈ R | M.wildExponent = j}, w M.1 := by
    have heq (M : R) : (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) *
        (if M.1.wildExponent = j then 1 else 0) =
        (n : ℝ≥0∞) * if M.1.wildExponent = j then w M.1 else 0 := by
      split_ifs <;> simp [w, div_eq_mul_inv]
    simp only [heq, ENNReal.tsum_mul_left]
    congr 1
    have hsub := tsum_subtype ({M : R | M.1.wildExponent = j}) (fun M : R ↦ w M.1)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq] at hsub
    exact hsub.symm.trans ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ R)
      (fun E ↦ E.wildExponent = j)).tsum_eq fun M ↦ w M.1)
  rw [hlhs, hrhs] at h
  exact (ENNReal.eq_div_iff (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top _)).mpr h.symm

end IsRepresentativeSet

/-! ### Total count of extensions of given degree -/

/-- **Krasner's total count**: the extended cardinality of `totallyRamifiedOfDegree K n` (in
`ℝ≥0∞`) equals the sum over all wild exponents `j` of `# {E ∈ σ_K(n) | c(E) = j}`, in every
characteristic. -/
theorem encard_totallyRamifiedOfDegree_eq_tsum (n : ℕ) :
    ((totallyRamifiedOfDegree K n).encard : ℝ≥0∞) =
      ∑' j : ℕ, ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) := by
  set S := totallyRamifiedOfDegree K n
  rw [← ENNReal.tsum_set_one,
    ← tsum_fiberwise (fun _ : S ↦ (1 : ℝ≥0∞)) (fun L ↦ L.1.wildExponent)]
  refine tsum_congr fun j ↦ ?_
  have hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  rw [← ENat.toENNReal_coe, hfin.cast_ncard_eq, ← ENNReal.tsum_set_one]
  exact (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ S)
    (fun E ↦ E.wildExponent = j)).tsum_eq fun _ ↦ (1 : ℝ≥0∞)

/-- For `0 < n`, the extended cardinality of `totallyRamifiedOfDegree K n` (in `ℝ≥0∞`) is the sum
over Ore-admissible wild exponents `j` of `# {E ∈ σ_K(n) | c(E) = j}`. -/
theorem encard_totallyRamifiedOfDegree_eq_tsum_isOreAdmissible {n : ℕ} (hn : 0 < n) :
    ((totallyRamifiedOfDegree K n).encard : ℝ≥0∞) =
      ∑' j : {j : ℕ | IsOreAdmissible K n j},
        ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j.1}.ncard : ℝ≥0∞) := by
  rw [encard_totallyRamifiedOfDegree_eq_tsum, tsum_subtype {j : ℕ | IsOreAdmissible K n j}
    (fun j ↦ ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞))]
  refine tsum_congr fun j ↦ ?_
  by_cases hadm : IsOreAdmissible K n j
  · simp [hadm]
  · rw [Set.indicator_of_notMem (hadm : j ∉ {j : ℕ | IsOreAdmissible K n j})]
    simp only [Nat.cast_eq_zero, Set.ncard_eq_zero
      (finite_totallyRamifiedOfDegree_wildExponent_eq n j), Set.eq_empty_iff_forall_notMem]
    exact fun E ⟨hE, rfl⟩ ↦ hadm ((ore_realizability n E.wildExponent hn).mp ⟨E, hE, rfl⟩)

/-- Away from equal characteristic `p ∣ n` (that is, whenever `(n : K) ≠ 0`), `σ_K(n)` is finite
and its cardinality is the finite sum of `# {E ∈ σ_K(n) | c(E) = j}` over
`0 ≤ j ≤ n * v_K(n)`. -/
theorem ncard_totallyRamifiedOfDegree_eq_sum_of_cast_ne_zero {n : ℕ} (hnK : (n : K) ≠ 0) :
    (totallyRamifiedOfDegree K n).ncard =
      ∑ j ∈ Finset.Iic (n * natCastValuation K n hnK),
        {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard := by
  set S := totallyRamifiedOfDegree K n
  set B := n * natCastValuation K n hnK
  have hunion : S = ⋃ j ∈ (Finset.Iic B : Set ℕ), {E ∈ S | E.wildExponent = j} := by
    ext E
    simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_Iic, Set.mem_ofPred_eq, exists_prop]
    exact ⟨fun hE ↦ ⟨E.wildExponent, IntermediateField.wildExponent_le_mul_natCastValuation hE hnK,
      hE, rfl⟩, fun ⟨_, _, hE, _⟩ ↦ hE⟩
  conv_lhs => rw [hunion]
  rw [(Finset.finite_toSet _).ncard_biUnion
      (fun j _ ↦ finite_totallyRamifiedOfDegree_wildExponent_eq n j)
      (fun _ _ _ _ hne ↦ Set.disjoint_left.mpr fun _ h1 h2 ↦ hne (h1.2.symm.trans h2.2)),
    finsum_mem_coe_finset]

/-- When `0 < n` and `(n : K) ≠ 0`, `(#σ_K(n) : ℚ)` is the finite sum of `krasnerCount K n j` over
`0 ≤ j ≤ n * v_K(n)`. -/
theorem cast_ncard_totallyRamifiedOfDegree_eq_sum_krasnerCount {n : ℕ} (hn : 0 < n)
    (hnK : (n : K) ≠ 0) :
    ((totallyRamifiedOfDegree K n).ncard : ℚ) =
      ∑ j ∈ Finset.Iic (n * natCastValuation K n hnK), krasnerCount K n j := by
  rw [ncard_totallyRamifiedOfDegree_eq_sum_of_cast_ne_zero hnK, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (krasner_refined_count n j hn).2

/-- Over `ℚ_[p]`, `#σ_{ℚ_[p]}(n)` for `0 < n` is the sum of the stratum counts for
`0 ≤ j ≤ n * v_p(n)`. -/
theorem ncard_totallyRamifiedOfDegree_eq_sum_padic (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    (totallyRamifiedOfDegree ℚ_[p] n).ncard =
      ∑ j ∈ Finset.Iic (n * padicValNat p n),
        {E ∈ totallyRamifiedOfDegree ℚ_[p] n | E.wildExponent = j}.ncard := by
  rw [ncard_totallyRamifiedOfDegree_eq_sum_of_cast_ne_zero (Nat.cast_ne_zero.mpr hn.ne'),
    _root_.Padic.natCastValuation_eq_padicValNat]

/-- **`#σ_{ℚ_2}(2) = 6`** via Krasner's formula (`2` extensions at wild exponent `1` and `4` at
wild exponent `2`; compare `TauCeti.encard_totallyRamifiedOfDegree_two_padicTwo` via Kummer
theory). -/
theorem ncard_totallyRamifiedOfDegree_two_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 2).ncard = 6 := by
  have hIic : Finset.Iic 2 = {0, 1, 2} := by decide
  rw [ncard_totallyRamifiedOfDegree_eq_sum_padic 2 (by decide : 0 < 2)]
  simp_rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic 2 (by decide : 0 < 2),
    isOreAdmissible_padic_iff 2 (by decide : 0 < 2)]
  simp [Nat.padicValNat_def, hIic]

/-- **`#σ_{ℚ_3}(3) = 21`**: `ℚ_3` has `21` totally ramified cubic extensions inside
`SeparableClosure ℚ_3` (`6` at wild exponent `1`, `6` at wild exponent `2`, and `9` at wild
exponent `3`). -/
theorem ncard_totallyRamifiedOfDegree_three_padicThree :
    (totallyRamifiedOfDegree ℚ_[3] 3).ncard = 21 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hIic : Finset.Iic 3 = {0, 1, 2, 3} := by decide
  rw [ncard_totallyRamifiedOfDegree_eq_sum_padic 3 (by decide : 0 < 3)]
  simp_rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic 3 (by decide : 0 < 3),
    isOreAdmissible_padic_iff 3 (by decide : 0 < 3)]
  simp [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2), hIic]

/-- **`#σ_{ℚ_2}(4) = 92`**: `ℚ_2` has `92` totally ramified quartic extensions inside
`SeparableClosure ℚ_2` (stratum counts `4, 8, 16, 16, 16, 32` at wild exponents
`1, 3, 5, 6, 7, 8`). -/
theorem ncard_totallyRamifiedOfDegree_four_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 4).ncard = 92 := by
  have hv4 : multiplicity 2 4 = 2 := Nat.multiplicity_prime_pow (p := 2) 2
  have hIic : Finset.Iic 8 = {0, 1, 2, 3, 4, 5, 6, 7, 8} := by decide
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  rw [ncard_totallyRamifiedOfDegree_eq_sum_padic 2 (by decide : 0 < 4)]
  simp_rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic 2 (by decide : 0 < 4),
    isOreAdmissible_padic_iff 2 (by decide : 0 < 4)]
  simp [Nat.padicValNat_def, hv4, multiplicity_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3),
    hIic, hIcc]

/-- **Canonical tower decomposition of the total degree-`n` count**: for `0 < n`, the extended
cardinality of all subextensions of `SeparableClosure K / K` of degree `n` equals
`∑_{f ∣ n} #σ_{K_f}(n / f)`, where `K_f = unramifiedExtension K (SeparableClosure K) f` is the
canonical unramified extension of degree `f`. (`0 < n` is required because infinite subextensions
have `Module.finrank = 0`.) -/
theorem encard_finrank_eq_sum_totallyRamifiedOfDegree {n : ℕ} (hn : 0 < n) :
    {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = n}.encard =
      ∑ f ∈ n.divisors,
        (letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K)
          (unramifiedExtension K (SeparableClosure K) f)
        letI := finiteIntermediateFieldTopology K (SeparableClosure K)
          (unramifiedExtension K (SeparableClosure K) f)
        haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
          (unramifiedExtension K (SeparableClosure K) f)
        (totallyRamifiedOfDegree (unramifiedExtension K (SeparableClosure K) f)
          (n / f)).encard) := by
  let P (f : ℕ) : Set (IntermediateField K (SeparableClosure K)) :=
    {L | Module.finrank K L = f * (n / f) ∧ L.inertiaDegree = f}
  have hunion : {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = n} =
      ⋃ f ∈ (n.divisors : Set ℕ), P f := by
    ext L
    simp only [P, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe, Nat.mem_divisors, ne_eq,
      hn.ne', not_false_eq_true, and_true, exists_prop]
    refine ⟨fun hdeg ↦ ?_, fun ⟨f, hdvd, hdeg, _⟩ ↦ Nat.mul_div_cancel' hdvd ▸ hdeg⟩
    have : Module.Finite K L := Module.finite_of_finrank_pos (hdeg ▸ hn)
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    have hmul := ramificationIndex_mul_inertiaDegree K L
    rw [← L.inertiaDegree_eq, hdeg] at hmul
    have hdvd : L.inertiaDegree ∣ n := ⟨ramificationIndex K L, by rw [← hmul, mul_comm]⟩
    exact ⟨L.inertiaDegree, hdvd, (Nat.mul_div_cancel' hdvd).symm ▸ hdeg, rfl⟩
  have hdisj : Set.PairwiseDisjoint (n.divisors : Set ℕ) P :=
    fun _ _ _ _ hne ↦ Set.disjoint_left.mpr fun _ h1 h2 ↦ hne (h1.2.symm.trans h2.2)
  rw [hunion, (Finset.finite_toSet _).encard_biUnion hdisj, finsum_mem_coe_finset]
  refine Finset.sum_congr rfl fun f hf ↦ ?_
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K)
    (unramifiedExtension K (SeparableClosure K) f)
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K)
    (unramifiedExtension K (SeparableClosure K) f)
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
    (unramifiedExtension K (SeparableClosure K) f)
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K)
    (unramifiedExtension K (SeparableClosure K) f)
  exact encard_finrank_and_inertiaDegree_eq (Nat.pos_of_mem_divisors hf).ne' (n / f)

end TauCeti
