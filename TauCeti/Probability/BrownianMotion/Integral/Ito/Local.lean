/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.L2
public import Mathlib.Probability.Process.LocalProperty
import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.Predictable.Basic

/-!
# Local Brownian Itô integral processes

Extend the `L²` Brownian Itô integral from `BrownianIntegrable` integrands to arbitrary
`LocallyBrownianIntegrable` integrands by closed-level energy localization, pathwise patching,
and predictable modification on the raw filtration.

## Main results

* `TauCeti.isItoIntegral_of_stopped_eqOn`: gluing principle for `IsItoIntegral` along stopping
  times tending almost surely to infinity.
* `TauCeti.LocallyBrownianIntegrable.exists_isItoIntegral`: every locally Brownian-integrable
  integrand admits a strongly predictable Itô integral that is a continuous local martingale.
* `TauCeti.IsItoIntegral.locally_martingale`: every strongly progressive Itô integral of a locally
  Brownian-integrable integrand is a native local martingale.
* `TauCeti.IsItoIntegral.stoppedProcess`: stopping any Itô integral of a locally
  Brownian-integrable integrand at a stopping time `σ` yields an Itô integral of `1_{[0, σ]} H`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H I : ℝ≥0 → Ω → ℝ}

private theorem continuous_stoppedProcess_local {f : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hf : Continuous fun t ↦ f t ω) :
    Continuous fun t ↦ stoppedProcess f τ t ω := by
  cases h : τ ω with
  | top =>
    have heq : (fun t : ℝ≥0 ↦ stoppedProcess f τ t ω) = fun t ↦ f t ω := by
      ext t
      rw [stoppedProcess_eq_of_le (by rw [h]; exact le_top)]
    rw [heq]
    exact hf
  | coe a =>
    have heq : (fun t : ℝ≥0 ↦ stoppedProcess f τ t ω) = fun t ↦ f (min t a) ω := by
      ext t
      rw [stoppedProcess, h, ← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe]
    rw [heq]
    exact hf.comp (continuous_id.min continuous_const)

/-- **Local gluing principle for Itô integrals.** A strongly predictable integrand `H` and an
almost-surely continuous process `I` form an Itô integral whenever they agree up to a sequence of
stopping times tending almost surely to infinity with a sequence of Itô integrals. -/
theorem isItoIntegral_of_stopped_eqOn [IsFiniteMeasure P]
    (hH : IsStronglyPredictable ℱ H)
    (hI_cont : ∀ᵐ ω ∂P, Continuous fun t ↦ I t ω)
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : ∀ n, IsStoppingTime ℱ (τ n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    {Hseq Iseq : ℕ → ℝ≥0 → Ω → ℝ}
    (hIn : ∀ n, IsItoIntegral ℱ P W (Hseq n) (Iseq n))
    (hagree : ∀ n, ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ n ω →
      Hseq n s ω = H s ω ∧ Iseq n s ω = I s ω) :
    IsItoIntegral ℱ P W H I := by
  refine ⟨hH, hI_cont, fun t ↦ ?_⟩
  have hinv_pos (n : ℕ) : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
    ENNReal.inv_pos.mpr (by simp)
  have hinv_lim : Tendsto (fun n : ℕ ↦ ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hex (n : ℕ) : ∃ L : ElementaryIntegrand ℱ,
      P {ω | ((n : ℝ≥0∞) + 1)⁻¹ ≤
          ∫⁻ s, ‖L.toProcess s ω - Hseq n s ω‖ₑ ^ 2 ∂Probability.timeMeasure t} <
        ((n : ℝ≥0∞) + 1)⁻¹ ∧
      P {ω | ((n : ℝ≥0∞) + 1)⁻¹ ≤ edist (L.integral W t ω) (Iseq n t ω)} <
        ((n : ℝ≥0∞) + 1)⁻¹ := by
    obtain ⟨K, hK_en, hK_int⟩ := (hIn n).approx t
    have h1 := (hK_en _ (hinv_pos n)).eventually (eventually_lt_nhds (hinv_pos n))
    have h2 := (hK_int _ (hinv_pos n)).eventually (eventually_lt_nhds (hinv_pos n))
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    exact ⟨K k, hk1, hk2⟩
  choose L hL_en hL_int using hex
  have hτ_le (n : ℕ) : MeasurableSet {ω | τ n ω ≤ (t : WithTop ℝ≥0)} :=
    ℱ.le t _ (hτ n t)
  have hPτ : Tendsto (fun n ↦ P {ω | τ n ω ≤ (t : WithTop ℝ≥0)}) atTop (𝓝 0) := by
    have h1 (n : ℕ) : P {ω | τ n ω ≤ (t : WithTop ℝ≥0)} =
        ∫⁻ ω, ({ω | τ n ω ≤ (t : WithTop ℝ≥0)} : Set Ω).indicator 1 ω ∂P := by
      rw [lintegral_indicator_one (hτ_le n)]
    simp_rw [h1]
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P := by simp
    rw [h0]
    refine tendsto_lintegral_of_dominated_convergence (fun _ ↦ 1)
      (fun n ↦ measurable_const.indicator (hτ_le n))
      (fun n ↦ Eventually.of_forall fun ω ↦ Set.indicator_le_self _ _ ω)
      (by simp [measure_ne_top]) ?_
    filter_upwards [hlim] with ω hω
    have hev : ∀ᶠ n in atTop, (t : WithTop ℝ≥0) < τ n ω :=
      (WithTop.tendsto_nhds_top_iff _).mp hω t
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    exact (Set.indicator_of_notMem (not_le.mpr hn) _).symm
  have hsum_lim :
      Tendsto (fun n ↦ P {ω | τ n ω ≤ (t : WithTop ℝ≥0)} + ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [add_zero] using hPτ.add hinv_lim
  refine ⟨L, fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum_lim
      (Eventually.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [hinv_lim.eventually (eventually_le_nhds hε)] with n hn
    have hnull : P {ω | ¬ ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ n ω →
        Hseq n s ω = H s ω ∧ Iseq n s ω = I s ω} = 0 :=
      ae_iff.mp (hagree n)
    have hsub : {ω | ε ≤ ∫⁻ s, ‖(L n).toProcess s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t} ⊆
        {ω | ¬ ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ n ω →
          Hseq n s ω = H s ω ∧ Iseq n s ω = I s ω} ∪
        ({ω | τ n ω ≤ (t : WithTop ℝ≥0)} ∪
          {ω | ((n : ℝ≥0∞) + 1)⁻¹ ≤
            ∫⁻ s, ‖(L n).toProcess s ω - Hseq n s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) := by
      intro ω hω
      by_cases hgood : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ n ω →
          Hseq n s ω = H s ω ∧ Iseq n s ω = I s ω
      · right
        by_cases hle : τ n ω ≤ (t : WithTop ℝ≥0)
        · exact Or.inl hle
        · right
          have htlt : (t : WithTop ℝ≥0) < τ n ω := not_le.mp hle
          have heq : ∫⁻ s, ‖(L n).toProcess s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t =
              ∫⁻ s, ‖(L n).toProcess s ω - Hseq n s ω‖ₑ ^ 2 ∂Probability.timeMeasure t := by
            refine lintegral_congr_ae ?_
            filter_upwards [Probability.ae_mem_Ioc_timeMeasure t] with s hs
            have hsτ : (s : WithTop ℝ≥0) ≤ τ n ω := (WithTop.coe_le_coe.mpr hs.2).trans htlt.le
            rw [(hgood s hsτ).1]
          change ε ≤ _ at hω
          exact hn.trans (heq ▸ hω)
      · exact Or.inl hgood
    calc
      P {ω | ε ≤ ∫⁻ s, ‖(L n).toProcess s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}
          ≤ P {ω | ¬ ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ n ω →
              Hseq n s ω = H s ω ∧ Iseq n s ω = I s ω} +
            (P {ω | τ n ω ≤ (t : WithTop ℝ≥0)} +
              P {ω | ((n : ℝ≥0∞) + 1)⁻¹ ≤
                ∫⁻ s, ‖(L n).toProcess s ω - Hseq n s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add le_rfl (measure_union_le _ _)))
      _ ≤ P {ω | τ n ω ≤ (t : WithTop ℝ≥0)} + ((n : ℝ≥0∞) + 1)⁻¹ := by
        rw [hnull, zero_add]
        exact add_le_add le_rfl (hL_en n).le
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum_lim
      (Eventually.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [hinv_lim.eventually (eventually_le_nhds hε)] with n hn
    have hnull : P {ω | ¬ ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ n ω →
        Hseq n s ω = H s ω ∧ Iseq n s ω = I s ω} = 0 :=
      ae_iff.mp (hagree n)
    have hsub : {ω | ε ≤ edist ((L n).integral W t ω) (I t ω)} ⊆
        {ω | ¬ ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ n ω →
          Hseq n s ω = H s ω ∧ Iseq n s ω = I s ω} ∪
        ({ω | τ n ω ≤ (t : WithTop ℝ≥0)} ∪
          {ω | ((n : ℝ≥0∞) + 1)⁻¹ ≤ edist ((L n).integral W t ω) (Iseq n t ω)}) := by
      intro ω hω
      by_cases hgood : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ n ω →
          Hseq n s ω = H s ω ∧ Iseq n s ω = I s ω
      · right
        by_cases hle : τ n ω ≤ (t : WithTop ℝ≥0)
        · exact Or.inl hle
        · right
          have htτ : (t : WithTop ℝ≥0) ≤ τ n ω := (not_le.mp hle).le
          change ε ≤ edist ((L n).integral W t ω) (I t ω) at hω
          rw [← (hgood t htτ).2] at hω
          exact hn.trans hω
      · exact Or.inl hgood
    calc
      P {ω | ε ≤ edist ((L n).integral W t ω) (I t ω)}
          ≤ P {ω | ¬ ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ n ω →
              Hseq n s ω = H s ω ∧ Iseq n s ω = I s ω} +
            (P {ω | τ n ω ≤ (t : WithTop ℝ≥0)} +
              P {ω | ((n : ℝ≥0∞) + 1)⁻¹ ≤ edist ((L n).integral W t ω) (Iseq n t ω)}) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add le_rfl (measure_union_le _ _)))
      _ ≤ P {ω | τ n ω ≤ (t : WithTop ℝ≥0)} + ((n : ℝ≥0∞) + 1)⁻¹ := by
        rw [hnull, zero_add]
        exact add_le_add le_rfl (hL_int n).le

/-- Construct a strongly predictable continuous local-martingale Itô integral for a
`LocallyBrownianIntegrable` integrand together with its energy-localized `L²` stages. -/
private theorem LocallyBrownianIntegrable.exists_energyLocalized_itoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    (hH : LocallyBrownianIntegrable ℱ P H) :
    let τ (n : ℕ) := nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
    let H_n (n : ℕ) (t : ℝ≥0) (ω : Ω) :=
      if (t : WithTop ℝ≥0) ≤ τ n ω then nnvolume.finiteEnergyCutoff H t ω else 0
    ∃ (I : ℝ≥0 → Ω → ℝ) (I_n : ℕ → ℝ≥0 → Ω → ℝ),
      IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P ∧
      (∀ n, IsItoIntegral ℱ P W (H_n n) (I_n n)) ∧
      (∀ n, IsStronglyPredictable ℱ (I_n n)) ∧
      (∀ n, stoppedProcess I (τ n) ≡ᵐ[P] I_n n) := by
  have : IsProbabilityMeasure P := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let τ (n : ℕ) : Ω → WithTop ℝ≥0 := nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
  let H_n (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    if (t : WithTop ℝ≥0) ≤ τ n ω then nnvolume.finiteEnergyCutoff H t ω else 0
  have hτ_loc : IsLocalizingSequence ℱ τ P := hH.isLocalizingSequence_energyLocalizer
  have hHn (n : ℕ) : BrownianIntegrable ℱ P (H_n n) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer _
  choose I_n hIn hIn_pred hIn_mart using fun n ↦ (hHn n).exists_isItoIntegral hW hcont
  have hcompat (n m : ℕ) (hnm : n ≤ m) : stoppedProcess (I_n m) (τ n) ≡ᵐ[P] I_n n := by
    have hstop := (hIn m).stoppedProcess_of_brownianIntegrable hW (hHn m)
      (hIn_pred m).stronglyAdapted (hτ_loc.isStoppingTime n)
    have hHeq : (fun (t : ℝ≥0) ω ↦ if (t : WithTop ℝ≥0) ≤ τ n ω then H_n m t ω else 0) =
        H_n n := by
      ext t ω
      have hτle : τ n ω ≤ τ m ω := nnvolume.monotone_energyLocalizer H ω
        (add_le_add (Nat.cast_le.mpr hnm) le_rfl)
      dsimp only [H_n]
      by_cases ht : (t : WithTop ℝ≥0) ≤ τ n ω
      · simp only [ht, ht.trans hτle, ite_true]
      · simp only [ht, ite_false]
    rw [hHeq] at hstop
    exact hstop.indist hW (hIn n)
  obtain ⟨X, hX_prog, hX_cont, hX_stop⟩ :=
    exists_isStronglyProgressive_patch_stoppedProcess hτ_loc.tendsto_top
      (fun n ↦ (hIn_pred n).isStronglyProgressive) (fun n ↦ (hIn n).ae_continuous) hcompat
  obtain ⟨I, hI_pred, hI_cont, hIX⟩ :=
    hX_prog.stronglyAdapted.exists_isStronglyPredictable_indist_of_ae_continuous hX_cont
  have hI_stop (n : ℕ) : stoppedProcess I (τ n) ≡ᵐ[P] I_n n := by
    filter_upwards [hIX, hX_stop n] with ω hωIX hωX t
    rw [← hωX t]
    exact hωIX _
  have hI_ito : IsItoIntegral ℱ P W H I := by
    refine isItoIntegral_of_stopped_eqOn hH.isStronglyPredictable hI_cont
      hτ_loc.isStoppingTime hτ_loc.tendsto_top hIn fun n ↦ ?_
    filter_upwards [hH.ae_accumulatedEnergy_lt_top, hI_stop n] with ω hfin hstop s hs
    refine ⟨?_, ?_⟩
    · simp only [H_n, hs, ite_true]
      exact nnvolume.finiteEnergyCutoff_eqOn (hfin s) le_rfl
    · rw [← hstop s, stoppedProcess_eq_of_le hs]
  have hI_loc : Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
    refine hI_pred.isStronglyProgressive.locally_martingale_of_ae_stopped_eq hτ_loc hIn_mart
      fun n t ↦ ?_
    filter_upwards [hI_stop n] with ω hω
    have hpos : (⊥ : WithTop ℝ≥0) < τ n ω := by
      change (0 : WithTop ℝ≥0) < nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω
      exact nnvolume.energyLocalizer_pos (H := H) (by positivity : (0 : ℝ≥0) < (n : ℝ≥0) + 1) ω
    rw [← hω t, stoppedProcess_indicator_comm']
    exact (Set.indicator_of_mem hpos _).symm
  exact ⟨I, I_n, hI_ito, hI_pred, hI_loc, hIn, hIn_pred, hI_stop⟩

/-- **Existence of the local Brownian Itô integral.** Every locally Brownian-integrable integrand
admits a strongly predictable Itô integral that is a continuous local martingale on the raw
filtration. -/
theorem LocallyBrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
  obtain ⟨I, -, hI, hpred, hloc, -, -, -⟩ := hH.exists_energyLocalized_itoIntegral hW hcont
  exact ⟨I, hI, hpred, hloc⟩

/-- Every strongly progressive Itô integral of a locally Brownian-integrable integrand is a
native local martingale. -/
theorem IsItoIntegral.locally_martingale
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    (hH : LocallyBrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hprog : IsStronglyProgressive ℱ I) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
  obtain ⟨J, hJ, -, hJ_loc⟩ := hH.exists_isItoIntegral hW hcont
  exact hprog.locally_martingale_of_indist hJ_loc (hJ.indist hW hI)

/-- **Local stopping identity for Brownian Itô integrals.** Stopping any Itô integral of a
locally Brownian-integrable integrand `H` at a stopping time `σ` yields an Itô integral of
`1_{[0, σ]} H`. -/
theorem IsItoIntegral.stoppedProcess
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    (hH : LocallyBrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I σ) := by
  have : IsProbabilityMeasure P := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let τ (n : ℕ) : Ω → WithTop ℝ≥0 := nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
  let H_n (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    if (t : WithTop ℝ≥0) ≤ τ n ω then nnvolume.finiteEnergyCutoff H t ω else 0
  have hτ_loc : IsLocalizingSequence ℱ τ P := hH.isLocalizingSequence_energyLocalizer
  have hHn (n : ℕ) : BrownianIntegrable ℱ P (H_n n) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer _
  obtain ⟨J, I_n, hJ, -, -, hIn, hIn_pred, hJ_stop⟩ :=
    hH.exists_energyLocalized_itoIntegral hW hcont
  have hIJ : I ≡ᵐ[P] J := hI.indist hW hJ
  have hIn_σ (n : ℕ) : IsItoIntegral ℱ P W
      (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H_n n t ω else 0)
      (MeasureTheory.stoppedProcess (I_n n) σ) :=
    (hIn n).stoppedProcess_of_brownianIntegrable hW (hHn n) (hIn_pred n).stronglyAdapted hσ
  refine isItoIntegral_of_stopped_eqOn (hH.isStronglyPredictable.ite_le hσ)
    (hI.ae_continuous.mono fun _ h ↦ continuous_stoppedProcess_local h)
    hτ_loc.isStoppingTime hτ_loc.tendsto_top hIn_σ fun n ↦ ?_
  filter_upwards [hH.ae_accumulatedEnergy_lt_top, hJ_stop n, hIJ] with ω hfin hstop hωIJ s hs
  refine ⟨?_, ?_⟩
  · by_cases hsσ : (s : WithTop ℝ≥0) ≤ σ ω
    · simp only [hsσ, ite_true, H_n, hs]
      exact nnvolume.finiteEnergyCutoff_eqOn (hfin s) le_rfl
    · simp only [hsσ, ite_false]
  · have hmin_lt : min (s : WithTop ℝ≥0) (σ ω) < ⊤ :=
      lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top s)
    let t' : ℝ≥0 := (min (s : WithTop ℝ≥0) (σ ω)).untop hmin_lt.ne
    have ht'_eq : (t' : WithTop ℝ≥0) = min (s : WithTop ℝ≥0) (σ ω) :=
      WithTop.coe_untop _ hmin_lt.ne
    have ht'_le : (t' : WithTop ℝ≥0) ≤ τ n ω :=
      ht'_eq ▸ (min_le_left _ _).trans hs
    have hu : (min (s : WithTop ℝ≥0) (σ ω)).untopA = t' :=
      WithTop.untopA_eq_untop hmin_lt.ne
    simp only [MeasureTheory.stoppedProcess, hu]
    rw [← hstop t', stoppedProcess_eq_of_le ht'_le, ← hωIJ t']

end TauCeti
