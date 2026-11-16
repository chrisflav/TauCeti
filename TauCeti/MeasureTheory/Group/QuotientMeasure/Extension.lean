/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.QuotientMeasure.Basic
public import TauCeti.MeasureTheory.Measure.Count.Topology
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.UrysohnsLemma
import TauCeti.Topology.Compactness.LocallyCompact

/-!
# Extensions, stages, and boundary cases for Weil's quotient measure

This module develops the measure-theoretic extensions and functorial properties of
`TauCeti.quotientMeasure` constructed in `TauCeti.MeasureTheory.Group.QuotientMeasure.Basic`.

Let `G` be a second countable locally compact Hausdorff group, `H ≤ G` a closed subgroup on which
the modular characters of `G` and `H` agree, and `μG`, `μH` right Haar measures on `G` and `H`,
with quotient measure `ν = TauCeti.quotientMeasure H hH μG μH hmod` on `H \ G`.

1. **Nonnegative Borel functions**: Using monotone compactly supported continuous approximations of
   open sets and Dynkin's π–λ theorem, Weil's formula extends to all measurable functions
   `f : G → ℝ≥0∞` (`TauCeti.measurable_lintegral_rightCoset`,
   `TauCeti.lintegral_eq_lintegral_quotientMeasure`, `TauCeti.measure_eq_lintegral_quotientMeasure`,
   `TauCeti.ae_ae_of_ae_quotientMeasure`).
2. **Bochner integrable functions**: For any real normed space `E` and `f : G → E` integrable
   against `μG`, the fiber `h ↦ f (h * q.out)` is `μH`-integrable for `ν`-almost every `q`, the
   fiber integral is `ν`-integrable, and its integral over `H \ G` equals `∫ g, f g ∂μG`
   (`TauCeti.ae_integrable_of_integrable_quotientMeasure`,
   `TauCeti.integrable_integral_quotientMeasure`,
   `TauCeti.integral_eq_integral_quotientMeasure_of_integrable`).
3. **Composition in stages**: For closed subgroups `H₁ ≤ H₂ ≤ G` with matching modular characters,
   the quotient measures on `H₁ \ G`, `H₁ \ H₂`, and `H₂ \ G` compose in stages on both compactly
   supported continuous functions (`TauCeti.integral_quotientMeasure_stages`) and nonnegative Borel
   functions (`TauCeti.lintegral_quotientMeasure_stages`).
4. **Boundary cases**: For `H = ⊥` with counting measure, `quotientMeasure` transports to `μG`
   (`TauCeti.map_quotientBotHomeomorph_quotientMeasure`); for `H = ⊤` with matching Haar measure,
   `quotientMeasure` gives `Set.univ` mass `1` (`TauCeti.quotientMeasure_top_univ`).

## References

* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §2.6 (Theorem 2.49).
* Vladimir Platonov, Andrei Rapinchuk, Igor Rapinchuk, *Algebraic Groups and Number Theory*,
  Theorem 3.64.
-/

public section

open Filter MeasureTheory Set Topology CompactlySupportedContinuousMap
open scoped CompactlySupported ENNReal NNReal Pointwise Topology

namespace TauCeti

/-! ### Monotone `C_c` approximation and Dynkin π–λ extension -/

section MonotoneExtension

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X]

/-- Every open set `U` in a second countable locally compact Hausdorff space is the pointwise
supremum of an increasing sequence of nonnegative compactly supported continuous functions valued
in `[0, 1]`. -/
private lemma exists_monotone_cc_iSup_eq_indicator {U : Set X} (hU : IsOpen U) :
    ∃ f : ℕ → C_c(X, ℝ), Monotone f ∧ (∀ n x, 0 ≤ f n x) ∧
      ∀ x, (⨆ n, ENNReal.ofReal (f n x)) = U.indicator 1 x := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have hKc : ∀ n : ℕ, IsCompact (((↑) : U → X) '' compactCovering U n) := fun n =>
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hKU : ∀ n : ℕ, (((↑) : U → X) '' compactCovering U n) ⊆ U := by
    intro n x hx
    rcases hx with ⟨y, -, rfl⟩
    exact y.2
  -- Choose `g n ∈ C_c(X, ℝ)` with `0 ≤ g n ≤ 1`, `g n = 1` on `K n`, and `tsupport (g n) ⊆ U`.
  have hg_ex : ∀ n : ℕ, ∃ g : C_c(X, ℝ),
      (∀ x ∈ (((↑) : U → X) '' compactCovering U n), g x = 1) ∧
      tsupport (g : X → ℝ) ⊆ U ∧ ∀ x, g x ∈ Icc (0 : ℝ) 1 := by
    intro n
    obtain ⟨g₀, hg1, hgsupp, hgU, hgIcc⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen (hKc n) hU (hKU n)
    exact ⟨⟨g₀, hgsupp⟩, hg1, hgU, hgIcc⟩
  choose g hg1 hgU hgIcc using hg_ex
  -- Take running pointwise suprema `f n x = sup_{k ≤ n} g k x`.
  let fFun : ℕ → X → ℝ := fun n x =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => g k x
  have hf_cont : ∀ n, Continuous (fFun n) := fun n =>
    Continuous.finset_sup'_apply Finset.nonempty_range_add_one fun k _ => (g k).continuous
  have hf_supp : ∀ n, HasCompactSupport (fFun n) := by
    intro n
    have hK : IsCompact (⋃ k ∈ Finset.range (n + 1), tsupport (g k : X → ℝ)) :=
      (Finset.range (n + 1)).isCompact_biUnion fun k _ => (g k).hasCompactSupport
    refine HasCompactSupport.of_support_subset_isCompact hK fun x hx => ?_
    have hex : ∃ k ∈ Finset.range (n + 1), g k x ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : fFun n x = 0 := by
        refine le_antisymm ?_ ?_
        · exact Finset.sup'_le Finset.nonempty_range_add_one _ fun k hk => le_of_eq (hall k hk)
        · exact (hgIcc 0 x).1.trans
            (Finset.le_sup' (fun k => g k x) (Finset.mem_range.mpr (Nat.zero_lt_succ n)))
      exact hx h0
    rcases hex with ⟨k, hk, hgk⟩
    exact mem_biUnion hk (subset_tsupport _ hgk)
  let f : ℕ → C_c(X, ℝ) := fun n => ⟨⟨fFun n, hf_cont n⟩, hf_supp n⟩
  have hf_mono : Monotone f := by
    intro m n hmn x
    exact Finset.sup'_mono (fun k => g k x) (Finset.range_mono (Nat.succ_le_succ hmn))
      Finset.nonempty_range_add_one
  have hf_nonneg : ∀ n x, 0 ≤ f n x := fun n x =>
    (hgIcc 0 x).1.trans
      (Finset.le_sup' (fun k => g k x) (Finset.mem_range.mpr (Nat.zero_lt_succ n)))
  have hf_le_one : ∀ n x, f n x ≤ 1 := fun n x =>
    Finset.sup'_le Finset.nonempty_range_add_one _ fun k _ => (hgIcc k x).2
  refine ⟨f, hf_mono, hf_nonneg, fun x => ?_⟩
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx, Pi.one_apply]
    refine le_antisymm ?_ ?_
    · exact iSup_le fun n => by simpa using ENNReal.ofReal_le_ofReal (hf_le_one n x)
    · obtain ⟨n, hn⟩ := exists_mem_compactCovering (⟨x, hx⟩ : U)
      have hxK : x ∈ ((↑) : U → X) '' compactCovering U n := ⟨⟨x, hx⟩, hn, rfl⟩
      have hfn : f n x = 1 := le_antisymm (hf_le_one n x) <| by
        rw [← hg1 n x hxK]
        exact Finset.le_sup' (fun k => g k x) (Finset.mem_range.mpr (Nat.lt_succ_self n))
      exact le_iSup_of_le n (by simp [hfn])
  · rw [Set.indicator_of_notMem hx]
    have hzero : ∀ n, f n x = 0 := by
      intro n
      refine le_antisymm ?_ (hf_nonneg n x)
      exact Finset.sup'_le Finset.nonempty_range_add_one _ fun k _ => le_of_eq <|
        image_eq_zero_of_notMem_tsupport fun hmem => hx (hgU k hmem)
    simp [hzero]

/-- Every second countable locally compact Hausdorff space is an increasing union of open sets
with compact closure. -/
private lemma exists_monotone_isOpen_isCompact_closure_iUnion_eq_univ :
    ∃ V : ℕ → Set X, Monotone V ∧ (∀ n, IsOpen (V n)) ∧
      (∀ n, IsCompact (closure (V n))) ∧ (⋃ n, V n) = Set.univ := by
  have hex : ∀ n : ℕ, ∃ C : Set X, IsCompact C ∧ compactCovering X n ⊆ interior C := fun n =>
    exists_compact_superset (isCompact_compactCovering X n)
  choose C hCc hCsub using hex
  let V : ℕ → Set X := fun n => ⋃ k ∈ Finset.range (n + 1), interior (C k)
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    exact biUnion_subset_biUnion_left (Finset.range_mono (Nat.succ_le_succ hmn))
  · intro n
    exact isOpen_biUnion fun _ _ => isOpen_interior
  · intro n
    have hK : IsCompact (⋃ k ∈ Finset.range (n + 1), C k) :=
      (Finset.range (n + 1)).isCompact_biUnion fun k _ => hCc k
    have hsub : V n ⊆ ⋃ k ∈ Finset.range (n + 1), C k :=
      iUnion₂_mono fun k _ => interior_subset
    exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)
  · ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_mem_compactCovering x
    exact ⟨n, mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_self n)) (hCsub n hn)⟩

/-- **Monotone-class `lintegral` extension**: if a locally finite Borel measure `μ` on a second
countable locally compact Hausdorff space `X` disintegrates against a measure `ν` on a measurable
space `Y` and a family of measures `κ : Y → Measure X` finite on compacts on all nonnegative
compactly supported continuous functions, then the disintegration extends to all measurable
functions `f : X → ℝ≥0∞` (with exact Borel measurability of the fiber integral). -/
private lemma measurable_and_lintegral_eq_of_compactlySupported
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (κ : Y → Measure X)
    (hfin : ∀ y : Y, ∀ K : Set X, IsCompact K → κ y K < ∞)
    (hcc_meas : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) →
      Measurable fun y : Y => ∫⁻ x, ENNReal.ofReal (f x) ∂(κ y))
    (hcc_eq : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) →
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ∫⁻ y, (∫⁻ x, ENNReal.ofReal (f x) ∂(κ y)) ∂ν) :
    ∀ {f : X → ℝ≥0∞}, Measurable f →
      Measurable (fun y : Y => ∫⁻ x, f x ∂(κ y)) ∧
      ∫⁻ x, f x ∂μ = ∫⁻ y, (∫⁻ x, f x ∂(κ y)) ∂ν := by
  -- Step 1: open sets via monotone `C_c` approximation and `lintegral_iSup`.
  have hopen : ∀ {U : Set X}, IsOpen U →
      Measurable (fun y : Y => κ y U) ∧ μ U = ∫⁻ y, κ y U ∂ν := by
    intro U hU
    obtain ⟨f, hf_mono, hf_nonneg, hfiSup⟩ := exists_monotone_cc_iSup_eq_indicator hU
    have hfm : ∀ n, Measurable fun x => ENNReal.ofReal (f n x) := fun n =>
      ENNReal.measurable_ofReal.comp (f n).continuous.measurable
    have hf_enn_mono : Monotone fun n x => ENNReal.ofReal (f n x) := fun m n hmn x =>
      ENNReal.ofReal_le_ofReal (hf_mono hmn x)
    have hκ_eq : ∀ y : Y, κ y U = ⨆ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂(κ y) := by
      intro y
      rw [← lintegral_indicator_one hU.measurableSet]
      simp_rw [← hfiSup]
      exact lintegral_iSup hfm hf_enn_mono
    have hμ_eq : μ U = ⨆ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂μ := by
      rw [← lintegral_indicator_one hU.measurableSet]
      simp_rw [← hfiSup]
      exact lintegral_iSup hfm hf_enn_mono
    refine ⟨?_, ?_⟩
    · simp_rw [hκ_eq]
      exact Measurable.iSup fun n => hcc_meas (f n) (hf_nonneg n)
    · rw [hμ_eq]
      simp_rw [hcc_eq _ (hf_nonneg _), hκ_eq]
      exact (lintegral_iSup (fun n => hcc_meas (f n) (hf_nonneg n))
        (fun m n hmn y => lintegral_mono fun x => hf_enn_mono hmn x)).symm
  -- Step 2: all Borel sets intersected with a relatively compact open set `V`, via π–λ.
  have hrel : ∀ {V : Set X}, IsOpen V → IsCompact (closure V) → ∀ {s : Set X}, MeasurableSet s →
      Measurable (fun y : Y => κ y (s ∩ V)) ∧ μ (s ∩ V) = ∫⁻ y, κ y (s ∩ V) ∂ν := by
    intro V hVo hVc s hs
    have hVfin : μ V ≠ ∞ :=
      ((measure_mono subset_closure).trans_lt hVc.measure_lt_top).ne
    have hκVfin : ∀ y : Y, κ y V ≠ ∞ := fun y =>
      ((measure_mono subset_closure).trans_lt (hfin y (closure V) hVc)).ne
    have hVprop := hopen hVo
    refine MeasurableSpace.induction_on_inter BorelSpace.measurable_eq isPiSystem_isOpen
      (C := fun t _ => Measurable (fun y : Y => κ y (t ∩ V)) ∧ μ (t ∩ V) = ∫⁻ y, κ y (t ∩ V) ∂ν)
      ?_ ?_ ?_ ?_ s hs
    · simp
    · intro U hUo
      exact hopen (hUo.inter hVo)
    · intro t ht ⟨hmt, heqt⟩
      have hdiff : tᶜ ∩ V = V \ (t ∩ V) := by
        ext x
        simp [and_comm]
      have hsub : t ∩ V ⊆ V := inter_subset_right
      have hκ_sub : ∀ y : Y, κ y (tᶜ ∩ V) = κ y V - κ y (t ∩ V) := fun y => by
        rw [hdiff, measure_sdiff hsub (ht.inter hVo.measurableSet).nullMeasurableSet
          ((measure_mono hsub).trans_lt (lt_top_iff_ne_top.mpr (hκVfin y))).ne]
      have hm_compl : Measurable fun y : Y => κ y (tᶜ ∩ V) := by
        simp_rw [hκ_sub]
        exact hVprop.1.sub hmt
      refine ⟨hm_compl, ?_⟩
      have hdisj_t : Disjoint (tᶜ ∩ V) (t ∩ V) :=
        disjoint_compl_left.mono inter_subset_left inter_subset_left
      have hadd_μ : μ (tᶜ ∩ V) + μ (t ∩ V) = μ V := by
        rw [← measure_union hdisj_t (ht.inter hVo.measurableSet),
          ← union_inter_distrib_right, compl_union_self, univ_inter]
      have hadd_κ : ∀ y : Y, κ y (tᶜ ∩ V) + κ y (t ∩ V) = κ y V := fun y => by
        rw [← measure_union hdisj_t (ht.inter hVo.measurableSet),
          ← union_inter_distrib_right, compl_union_self, univ_inter]
      have hsum : μ (tᶜ ∩ V) + μ (t ∩ V) =
          (∫⁻ y, κ y (tᶜ ∩ V) ∂ν) + ∫⁻ y, κ y (t ∩ V) ∂ν := by
        rw [hadd_μ, hVprop.2, ← lintegral_add_left hm_compl]
        exact lintegral_congr fun y => (hadd_κ y).symm
      rw [← heqt] at hsum
      have hfin_t : μ (t ∩ V) ≠ ∞ :=
        ((measure_mono hsub).trans_lt (lt_top_iff_ne_top.mpr hVfin)).ne
      exact (ENNReal.add_left_inj hfin_t).mp hsum
    · intro f hdisj hf hprop
      have hdisjV : Pairwise (Function.onFun Disjoint fun n => f n ∩ V) := fun i j hij =>
        (hdisj hij).mono inter_subset_left inter_subset_left
      have heqU : (⋃ n, f n) ∩ V = ⋃ n, (f n ∩ V) := iUnion_inter _ _
      have hκ_tsum : ∀ y : Y, κ y ((⋃ n, f n) ∩ V) = ∑' n, κ y (f n ∩ V) := fun y => by
        rw [heqU, measure_iUnion hdisjV fun n => (hf n).inter hVo.measurableSet]
      have hμ_tsum : μ ((⋃ n, f n) ∩ V) = ∑' n, μ (f n ∩ V) := by
        rw [heqU, measure_iUnion hdisjV fun n => (hf n).inter hVo.measurableSet]
      refine ⟨?_, ?_⟩
      · simp_rw [hκ_tsum]
        exact Measurable.tsum fun n => (hprop n).1
      · rw [hμ_tsum]
        simp_rw [hκ_tsum, (hprop _).2]
        exact (lintegral_tsum fun n => (hprop n).1.aemeasurable).symm
  -- Step 3: all Borel sets via monotone exhaustion by relatively compact open sets.
  have hset : ∀ {s : Set X}, MeasurableSet s →
      Measurable (fun y : Y => κ y s) ∧ μ s = ∫⁻ y, κ y s ∂ν := by
    intro s hs
    obtain ⟨V, hVmono, hVo, hVc, hVuniv⟩ :=
      exists_monotone_isOpen_isCompact_closure_iUnion_eq_univ (X := X)
    have hs_eq : s = ⋃ n, (s ∩ V n) := by
      rw [← inter_iUnion, hVuniv, inter_univ]
    have hmono : Monotone fun n => s ∩ V n := fun m n hmn =>
      inter_subset_inter_right s (hVmono hmn)
    have hκ_sup : ∀ y : Y, κ y s = ⨆ n, κ y (s ∩ V n) := fun y => by
      conv_lhs => rw [hs_eq]
      exact hmono.measure_iUnion
    have hμ_sup : μ s = ⨆ n, μ (s ∩ V n) := by
      conv_lhs => rw [hs_eq]
      exact hmono.measure_iUnion
    refine ⟨?_, ?_⟩
    · simp_rw [hκ_sup]
      exact Measurable.iSup fun n => (hrel (hVo n) (hVc n) hs).1
    · rw [hμ_sup]
      simp_rw [(hrel (hVo _) (hVc _) hs).2, hκ_sup]
      exact (lintegral_iSup (fun n => (hrel (hVo n) (hVc n) hs).1)
        (fun m n hmn y => measure_mono (hmono hmn))).symm
  -- Step 4: simple functions, then arbitrary measurable `f : X → ℝ≥0∞` via `SimpleFunc.eapprox`.
  have hsimple : ∀ g : SimpleFunc X ℝ≥0∞,
      Measurable (fun y : Y => ∫⁻ x, g x ∂(κ y)) ∧
      ∫⁻ x, g x ∂μ = ∫⁻ y, (∫⁻ x, g x ∂(κ y)) ∂ν := by
    intro g
    have hκ_g : ∀ y : Y, ∫⁻ x, g x ∂(κ y) = ∑ c ∈ g.range, c * κ y (g ⁻¹' {c}) := fun y =>
      g.lintegral_eq_lintegral _
    have hμ_g : ∫⁻ x, g x ∂μ = ∑ c ∈ g.range, c * μ (g ⁻¹' {c}) :=
      g.lintegral_eq_lintegral _
    refine ⟨?_, ?_⟩
    · simp_rw [hκ_g]
      exact Finset.measurable_sum _ fun c _ =>
        (hset (g.measurableSet_preimage {c})).1.const_mul c
    · rw [hμ_g]
      simp_rw [hκ_g]
      rw [lintegral_finsetSum _ fun c _ =>
        (hset (g.measurableSet_preimage {c})).1.const_mul c]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [lintegral_const_mul _ (hset (g.measurableSet_preimage {c})).1,
        (hset (g.measurableSet_preimage {c})).2]
  intro f hf
  have hκ_f : ∀ y : Y, ∫⁻ x, f x ∂(κ y) = ⨆ n, ∫⁻ x, SimpleFunc.eapprox f n x ∂(κ y) := by
    intro y
    rw [← lintegral_iSup (fun n => (SimpleFunc.eapprox f n).measurable)
      (SimpleFunc.monotone_eapprox f)]
    exact lintegral_congr fun x => (SimpleFunc.iSup_eapprox_apply hf x).symm
  have hμ_f : ∫⁻ x, f x ∂μ = ⨆ n, ∫⁻ x, SimpleFunc.eapprox f n x ∂μ := by
    rw [← lintegral_iSup (fun n => (SimpleFunc.eapprox f n).measurable)
      (SimpleFunc.monotone_eapprox f)]
    exact lintegral_congr fun x => (SimpleFunc.iSup_eapprox_apply hf x).symm
  refine ⟨?_, ?_⟩
  · simp_rw [hκ_f]
    exact Measurable.iSup fun n => (hsimple (SimpleFunc.eapprox f n)).1
  · rw [hμ_f]
    simp_rw [(hsimple (SimpleFunc.eapprox f _)).2, hκ_f]
    exact (lintegral_iSup (fun n => (hsimple (SimpleFunc.eapprox f n)).1)
      (fun m n hmn y => lintegral_mono fun x => SimpleFunc.monotone_eapprox f hmn x)).symm

end MonotoneExtension

/-! ### Nonnegative Borel extension of Weil's formula -/

section LIntegralExtension

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Internal helper proving both measurability and Weil's `lintegral` formula simultaneously. -/
private lemma measurable_and_lintegral_eq_quotientMeasure
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun q : MulAction.orbitRel.Quotient H G =>
      ∫⁻ h : H, f ((h : G) * q.out) ∂μH) ∧
    ∫⁻ g, f g ∂μG =
      ∫⁻ q, (∫⁻ h : H, f ((h : G) * q.out) ∂μH) ∂(quotientMeasure H hH μG μH hmod) := by
  let ν := quotientMeasure H hH μG μH hmod
  let φ : MulAction.orbitRel.Quotient H G → H → G := fun q h => (h : G) * q.out
  have hφ_cont : ∀ q, Continuous (φ q) := fun q => continuous_subtype_val.mul continuous_const
  let κ : MulAction.orbitRel.Quotient H G → Measure G := fun q => Measure.map (φ q) μH
  have hκ_int : ∀ q {F : G → ℝ≥0∞}, Measurable F →
      ∫⁻ x, F x ∂(κ q) = ∫⁻ h : H, F ((h : G) * q.out) ∂μH := fun q _ hF =>
    lintegral_map hF (hφ_cont q).measurable
  have hmain := measurable_and_lintegral_eq_of_compactlySupported μG ν κ
    (fun q K hK => by
      have hpre_comp : IsCompact (φ q ⁻¹' K) := by
        have hsub : φ q ⁻¹' K ⊆ ((↑) : H → G) ⁻¹' (K * {q.out⁻¹}) := fun h hh =>
          ⟨(h : G) * q.out, hh, q.out⁻¹, rfl, by group⟩
        have hcl : IsClosed (φ q ⁻¹' K) := hK.isClosed.preimage (hφ_cont q)
        have hKc : IsCompact (((↑) : H → G) ⁻¹' (K * {q.out⁻¹})) :=
          hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.mul isCompact_singleton)
        exact hKc.of_isClosed_subset hcl hsub
      rw [Measure.map_apply (hφ_cont q).measurable hK.measurableSet]
      exact hpre_comp.measure_lt_top)
    (fun F hFnn => by
      have havg : (fun q => ∫⁻ x, ENNReal.ofReal (F x) ∂(κ q)) =
          fun q => ENNReal.ofReal (quotientAverage H hH μH F q) := by
        ext q
        rw [hκ_int q (F := fun x => ENNReal.ofReal (F x))
            (ENNReal.measurable_ofReal.comp F.continuous.measurable),
          quotientAverage_apply]
        have hF_int : Integrable (fun h : H => F ((h : G) * q.out)) μH := by
          have hsupp : HasCompactSupport fun h : H => F ((h : G) * q.out) := by
            have hKc : IsCompact (((↑) : H → G) ⁻¹' (tsupport F * {q.out⁻¹})) :=
              hH.isClosedEmbedding_subtypeVal.isCompact_preimage
                (F.hasCompactSupport.mul isCompact_singleton)
            exact HasCompactSupport.of_support_subset_isCompact hKc fun h hh =>
              ⟨(h : G) * q.out, subset_tsupport F hh, q.out⁻¹, rfl, by group⟩
          exact (F.continuous.comp (hφ_cont q)).integrable_of_hasCompactSupport hsupp
        exact (ofReal_integral_eq_lintegral_ofReal hF_int
          (Eventually.of_forall fun h => hFnn _)).symm
      rw [havg]
      exact ENNReal.measurable_ofReal.comp (quotientAverage H hH μH F).continuous.measurable)
    (fun F hFnn => by
      have : IsFiniteMeasureOnCompacts ν :=
        isFiniteMeasureOnCompacts_quotientMeasure H hH μG μH hmod
      have havg : ∀ q, ∫⁻ x, ENNReal.ofReal (F x) ∂(κ q) =
          ENNReal.ofReal (quotientAverage H hH μH F q) := by
        intro q
        rw [hκ_int q (F := fun x => ENNReal.ofReal (F x))
            (ENNReal.measurable_ofReal.comp F.continuous.measurable),
          quotientAverage_apply]
        have hF_int : Integrable (fun h : H => F ((h : G) * q.out)) μH := by
          have hsupp : HasCompactSupport fun h : H => F ((h : G) * q.out) := by
            have hKc : IsCompact (((↑) : H → G) ⁻¹' (tsupport F * {q.out⁻¹})) :=
              hH.isClosedEmbedding_subtypeVal.isCompact_preimage
                (F.hasCompactSupport.mul isCompact_singleton)
            exact HasCompactSupport.of_support_subset_isCompact hKc fun h hh =>
              ⟨(h : G) * q.out, subset_tsupport F hh, q.out⁻¹, rfl, by group⟩
          exact (F.continuous.comp (hφ_cont q)).integrable_of_hasCompactSupport hsupp
        exact (ofReal_integral_eq_lintegral_ofReal hF_int
          (Eventually.of_forall fun h => hFnn _)).symm
      simp_rw [havg]
      rw [← ofReal_integral_eq_lintegral_ofReal F.integrable (Eventually.of_forall hFnn),
        ← ofReal_integral_eq_lintegral_ofReal (quotientAverage H hH μH F).integrable
          (Eventually.of_forall fun q => (quotientAverage H hH μH).map_nonneg hFnn q),
        integral_quotientMeasure, quotientFunctional_quotientAverage])
    hf
  simpa only [hκ_int _ hf] using hmain

/-- For any measurable `f : G → ℝ≥0∞`, the orbit `lintegral` `q ↦ ∫⁻ h : H, f (h * q.out) ∂μH`
is Borel measurable on `H \ G`. -/
theorem measurable_lintegral_rightCoset (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun q : MulAction.orbitRel.Quotient H G =>
      ∫⁻ h : H, f ((h : G) * q.out) ∂μH := by
  have : (Measure.haar : Measure G).inv.IsMulRightInvariant := inferInstance
  have : IsFiniteMeasureOnCompacts (Measure.haar : Measure G).inv :=
    { lt_top_of_isCompact K hK := by
        rw [Measure.inv_apply]
        exact hK.inv.measure_lt_top }
  have : (Measure.haar : Measure G).inv.IsOpenPosMeasure :=
    { open_pos U hUo hUne := by
        rw [Measure.inv_apply]
        exact hUo.inv.measure_ne_zero _ hUne.inv }
  exact (measurable_and_lintegral_eq_quotientMeasure H hH (Measure.haar : Measure G).inv
    μH hmod hf).1

/-- **Weil's integration formula for nonnegative Borel functions**: for every measurable
`f : G → ℝ≥0∞`, `∫⁻ g, f g ∂μG = ∫⁻ q, (∫⁻ h : H, f (h * q.out) ∂μH) ∂ν`. -/
theorem lintegral_eq_lintegral_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂μG =
      ∫⁻ q, (∫⁻ h : H, f ((h : G) * q.out) ∂μH) ∂(quotientMeasure H hH μG μH hmod) :=
  (measurable_and_lintegral_eq_quotientMeasure H hH μG μH hmod hf).2

/-- **Weil's measure formula**: for every measurable set `s ⊆ G`, `μG s` is the `quotientMeasure`
integral of the `μH`-measures of its `H`-coset slices. -/
theorem measure_eq_lintegral_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {s : Set G} (hs : MeasurableSet s) :
    μG s = ∫⁻ q, μH {h : H | (h : G) * q.out ∈ s} ∂(quotientMeasure H hH μG μH hmod) := by
  have h1m : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hs
  have h1 := lintegral_eq_lintegral_quotientMeasure H hH μG μH hmod h1m
  rw [lintegral_indicator_one hs] at h1
  refine h1.trans (lintegral_congr fun q => ?_)
  have hpre : MeasurableSet {h : H | (h : G) * q.out ∈ s} :=
    hs.preimage (continuous_subtype_val.mul continuous_const).measurable
  rw [← lintegral_indicator_one hpre]
  exact lintegral_congr fun h => by
    by_cases hh : (h : G) * q.out ∈ s <;> simp [hh]

/-- Almost-everywhere properties on `G` slice along `H`-orbits: if `p` holds `μG`-a.e., then for
`quotientMeasure`-a.e. coset `q`, `p (h * q.out)` holds for `μH`-a.e. `h : H`. -/
theorem ae_ae_of_ae_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {p : G → Prop} (hp : ∀ᵐ g ∂μG, p g) :
    ∀ᵐ q ∂(quotientMeasure H hH μG μH hmod), ∀ᵐ h : H ∂μH, p ((h : G) * q.out) := by
  let N := toMeasurable μG {g : G | ¬ p g}
  have hNm : MeasurableSet N := measurableSet_toMeasurable μG _
  have hN0 : μG N = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hp
  have hNsub : {g : G | ¬ p g} ⊆ N := subset_toMeasurable μG _
  have hmeas : Measurable fun q : MulAction.orbitRel.Quotient H G =>
      μH {h : H | (h : G) * q.out ∈ N} := by
    have h1m : Measurable (N.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hNm
    have hm := measurable_lintegral_rightCoset H hH μH hmod h1m
    have hfun : (fun q : MulAction.orbitRel.Quotient H G =>
        μH {h : H | (h : G) * q.out ∈ N}) =
        fun q => ∫⁻ h : H, N.indicator (1 : G → ℝ≥0∞) ((h : G) * q.out) ∂μH := by
      ext q
      have hpre : MeasurableSet {h : H | (h : G) * q.out ∈ N} :=
        hNm.preimage (continuous_subtype_val.mul continuous_const).measurable
      rw [← lintegral_indicator_one hpre]
      exact lintegral_congr fun h => by
        by_cases hh : (h : G) * q.out ∈ N <;> simp [hh]
    rw [hfun]
    exact hm
  have hint0 : ∫⁻ q, μH {h : H | (h : G) * q.out ∈ N} ∂(quotientMeasure H hH μG μH hmod) = 0 := by
    rw [← measure_eq_lintegral_quotientMeasure H hH μG μH hmod hNm, hN0]
  have hae0 : ∀ᵐ q ∂(quotientMeasure H hH μG μH hmod), μH {h : H | (h : G) * q.out ∈ N} = 0 :=
    (lintegral_eq_zero_iff hmeas).mp hint0
  filter_upwards [hae0] with q hq
  rw [ae_iff]
  exact measure_mono_null (fun h hh => hNsub hh) hq

end LIntegralExtension

/-! ### Bochner integrable extension of Weil's formula -/

section BochnerExtension

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {E : Type*} [NormedAddCommGroup E]

/-- For an integrable function `f : G → E`, almost every `H`-fiber `h ↦ f (h * q.out)` is
`μH`-integrable. -/
theorem ae_integrable_of_integrable_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {f : G → E} (hf : Integrable f μG) :
    ∀ᵐ q ∂(quotientMeasure H hH μG μH hmod), Integrable (fun h : H => f ((h : G) * q.out)) μH := by
  let ν := quotientMeasure H hH μG μH hmod
  let f₀ := hf.aestronglyMeasurable.mk f
  have hf₀_sm : StronglyMeasurable f₀ := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hf₀_ae : f =ᵐ[μG] f₀ := hf.aestronglyMeasurable.ae_eq_mk
  have hf₀_int : Integrable f₀ μG := hf.congr hf₀_ae
  have hnorm_meas : Measurable fun g : G => ‖f₀ g‖ₑ := hf₀_sm.eNorm
  have hlint_lt : ∫⁻ q, (∫⁻ h : H, ‖f₀ ((h : G) * q.out)‖ₑ ∂μH) ∂ν < ∞ := by
    rw [← lintegral_eq_lintegral_quotientMeasure H hH μG μH hmod hnorm_meas]
    exact hf₀_int.2
  have hae_fin : ∀ᵐ q ∂ν, ∫⁻ h : H, ‖f₀ ((h : G) * q.out)‖ₑ ∂μH < ∞ :=
    ae_lt_top (measurable_lintegral_rightCoset H hH μH hmod hnorm_meas) hlint_lt.ne
  have hae_eq : ∀ᵐ q ∂ν, ∀ᵐ h : H ∂μH, f ((h : G) * q.out) = f₀ ((h : G) * q.out) :=
    ae_ae_of_ae_quotientMeasure H hH μG μH hmod hf₀_ae
  filter_upwards [hae_fin, hae_eq] with q hqfin hqeq
  have hf₀_q : Integrable (fun h : H => f₀ ((h : G) * q.out)) μH :=
    ⟨(hf₀_sm.comp_measurable
        (continuous_subtype_val.mul continuous_const).measurable).aestronglyMeasurable,
      hqfin⟩
  exact hf₀_q.congr (hqeq.mono fun _ h => h.symm)

variable [NormedSpace ℝ E]

/-- Internal helper verifying integrability and Weil's formula for integrable simple functions. -/
private lemma simpleFunc_quotientMeasure [CompleteSpace E]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    (s : SimpleFunc G E) (hs : Integrable s μG) :
    Integrable (fun q : MulAction.orbitRel.Quotient H G =>
      ∫ h : H, s ((h : G) * q.out) ∂μH) (quotientMeasure H hH μG μH hmod) ∧
    ∫ g, s g ∂μG =
      ∫ q, (∫ h : H, s ((h : G) * q.out) ∂μH) ∂(quotientMeasure H hH μG μH hmod) := by
  classical
  let ν := quotientMeasure H hH μG μH hmod
  let S : Finset E := s.range.erase 0
  let A : E → Set G := fun c => s ⁻¹' {c}
  have hAm : ∀ c, MeasurableSet (A c) := fun c => s.measurableSet_preimage {c}
  have hAfin : ∀ c ∈ S, μG (A c) < ∞ := by
    intro c hc
    have hc0 : c ≠ 0 := Finset.ne_of_mem_erase hc
    have hmul : ‖c‖ₑ * μG (A c) ≤ ∫⁻ g, ‖s g‖ₑ ∂μG := by
      rw [← setLIntegral_const (A c) ‖c‖ₑ]
      calc ∫⁻ _ in A c, ‖c‖ₑ ∂μG = ∫⁻ g in A c, ‖s g‖ₑ ∂μG :=
            setLIntegral_congr_fun (hAm c) fun g hg => by simp [A] at hg; simp [hg]
        _ ≤ ∫⁻ g, ‖s g‖ₑ ∂μG := setLIntegral_le_lintegral _ _
    have hlt : ‖c‖ₑ * μG (A c) < ∞ := hmul.trans_lt hs.2
    exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne (by simp [hc0])
  -- Slice measure `m c q = μH {h | h * q.out ∈ A c}`.
  let m : E → MulAction.orbitRel.Quotient H G → ℝ≥0∞ :=
    fun c q => μH {h : H | (h : G) * q.out ∈ A c}
  have hm_meas : ∀ c, Measurable (m c) := by
    intro c
    have h1m : Measurable ((A c).indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator (hAm c)
    have hm := measurable_lintegral_rightCoset H hH μH hmod h1m
    have hfun : m c = fun q => ∫⁻ h : H, (A c).indicator (1 : G → ℝ≥0∞) ((h : G) * q.out) ∂μH := by
      ext q
      have hpre : MeasurableSet {h : H | (h : G) * q.out ∈ A c} :=
        (hAm c).preimage (continuous_subtype_val.mul continuous_const).measurable
      change μH {h : H | (h : G) * q.out ∈ A c} = _
      rw [← lintegral_indicator_one hpre]
      exact lintegral_congr fun h => by
        by_cases hh : (h : G) * q.out ∈ A c <;> simp [hh]
    rw [hfun]
    exact hm
  have hm_eq : ∀ c, ∫⁻ q, m c q ∂ν = μG (A c) := fun c =>
    (measure_eq_lintegral_quotientMeasure H hH μG μH hmod (hAm c)).symm
  have hm_ae_fin : ∀ c ∈ S, ∀ᵐ q ∂ν, m c q < ∞ := fun c hc =>
    ae_lt_top (hm_meas c) (by rw [hm_eq c]; exact (hAfin c hc).ne)
  have hm_all_fin : ∀ᵐ q ∂ν, ∀ c ∈ S, m c q < ∞ := (ae_ball_iff S.countable_toSet).mpr hm_ae_fin
  -- Pointwise decomposition of `s` as a finite sum over `S`.
  have hs_sum : ∀ g : G, s g = ∑ c ∈ S, (A c).indicator (fun _ => c) g := by
    intro g
    by_cases h0 : s g = 0
    · rw [h0]
      symm
      refine Finset.sum_eq_zero fun c hc => Set.indicator_of_notMem ?_ _
      intro hg
      exact Finset.ne_of_mem_erase hc (by simpa [A, h0] using hg.symm)
    · have hmem : s g ∈ S := Finset.mem_erase.mpr ⟨h0, s.mem_range_self g⟩
      rw [Finset.sum_eq_single (s g)]
      · simp [A]
      · intro c _ hne
        exact Set.indicator_of_notMem (fun hg => hne (by simpa [A] using hg.symm)) _
      · intro hnot
        exact absurd hmem hnot
  -- Express the fiber integral as `∑ c ∈ S, (m c q).toReal • c` for `ν`-a.e. `q`.
  let Gfun : MulAction.orbitRel.Quotient H G → E := fun q => ∑ c ∈ S, (m c q).toReal • c
  have hfib_ae : (fun q => ∫ h : H, s ((h : G) * q.out) ∂μH) =ᵐ[ν] Gfun := by
    filter_upwards [hm_all_fin] with q hq
    have hfun_eq : (fun h : H => s ((h : G) * q.out)) =
        fun h : H => ∑ c ∈ S, {h' : H | (h' : G) * q.out ∈ A c}.indicator (fun _ => c) h := by
      ext h
      rw [hs_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hh : (h : G) * q.out ∈ A c <;> simp [hh]
    rw [hfun_eq, integral_finsetSum]
    · refine Finset.sum_congr rfl fun c _ => ?_
      have hpre : MeasurableSet {h' : H | (h' : G) * q.out ∈ A c} :=
        (hAm c).preimage (continuous_subtype_val.mul continuous_const).measurable
      rw [integral_indicator_const c hpre, Measure.real_def]
    · intro c hc
      have hpre : MeasurableSet {h' : H | (h' : G) * q.out ∈ A c} :=
        (hAm c).preimage (continuous_subtype_val.mul continuous_const).measurable
      exact (integrableOn_const (hq c hc).ne).integrable_indicator hpre
  -- Each summand `(m c ·).toReal • c` is `ν`-integrable with integral `(μG (A c)).toReal • c`.
  have hterm_int : ∀ c ∈ S, Integrable (fun q => (m c q).toReal • c) ν := by
    intro c hc
    have hreal_int : Integrable (fun q => (m c q).toReal) ν :=
      integrable_toReal_of_lintegral_ne_top (hm_meas c).aemeasurable
        (by rw [hm_eq c]; exact (hAfin c hc).ne)
    exact hreal_int.smul_const c
  have hG_int : Integrable Gfun ν := integrable_finsetSum S hterm_int
  refine ⟨hG_int.congr hfib_ae.symm, ?_⟩
  rw [integral_congr_ae hfib_ae, integral_finsetSum S hterm_int]
  have hs_int : ∫ g, s g ∂μG = ∑ c ∈ S, (μG (A c)).toReal • c := by
    have hfun : (s : G → E) = fun g => ∑ c ∈ S, (A c).indicator (fun _ => c) g := funext hs_sum
    conv_lhs => rw [hfun]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [integral_indicator_const c (hAm c), Measure.real_def]
    · intro c hc
      exact (integrableOn_const (hAfin c hc).ne).integrable_indicator (hAm c)
  rw [hs_int]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [integral_smul_const, integral_toReal (hm_meas c).aemeasurable (hm_ae_fin c hc), hm_eq c]

/-- Internal helper proving both integrability of the fiber integral and Weil's Bochner formula. -/
private lemma integrable_and_integral_eq_quotientMeasure
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {f : G → E} (hf : Integrable f μG) :
    Integrable (fun q : MulAction.orbitRel.Quotient H G =>
      ∫ h : H, f ((h : G) * q.out) ∂μH) (quotientMeasure H hH μG μH hmod) ∧
    ∫ g, f g ∂μG =
      ∫ q, (∫ h : H, f ((h : G) * q.out) ∂μH) ∂(quotientMeasure H hH μG μH hmod) := by
  by_cases hE : CompleteSpace E
  · let ν := quotientMeasure H hH μG μH hmod
    -- Replace `f` with a strongly measurable representative `f₀`.
    let f₀ := hf.aestronglyMeasurable.mk f
    have hf₀_sm : StronglyMeasurable f₀ := hf.aestronglyMeasurable.stronglyMeasurable_mk
    have hf₀_ae : f =ᵐ[μG] f₀ := hf.aestronglyMeasurable.ae_eq_mk
    have hf₀_int : Integrable f₀ μG := hf.congr hf₀_ae
    have hfib_congr : (fun q => ∫ h : H, f ((h : G) * q.out) ∂μH) =ᵐ[ν]
        fun q => ∫ h : H, f₀ ((h : G) * q.out) ∂μH := by
      filter_upwards [ae_ae_of_ae_quotientMeasure H hH μG μH hmod hf₀_ae] with q hq
      exact integral_congr_ae hq
    suffices h0 : Integrable (fun q => ∫ h : H, f₀ ((h : G) * q.out) ∂μH) ν ∧
        ∫ g, f₀ g ∂μG = ∫ q, (∫ h : H, f₀ ((h : G) * q.out) ∂μH) ∂ν by
      exact ⟨h0.1.congr hfib_congr.symm, by
        rw [integral_congr_ae hf₀_ae, h0.2, integral_congr_ae hfib_congr.symm]⟩
    -- Approximate `f₀` in `L¹(μG)` by integrable simple functions with error `< (1 / 2) ^ n`.
    have hmem1 : MemLp f₀ 1 μG := memLp_one_iff_integrable.mpr hf₀_int
    have happrox : ∀ n : ℕ, ∃ s : SimpleFunc G E,
        ∫⁻ g, ‖f₀ g - s g‖ₑ ∂μG < (1 / 2 : ℝ≥0∞) ^ n ∧ Integrable s μG := by
      intro n
      have hpos : ((1 / 2 : ℝ≥0∞) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
      obtain ⟨s, hlt, hsmem⟩ := hmem1.exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top hpos
      have hsint : Integrable s μG := memLp_one_iff_integrable.mp hsmem
      rw [eLpNorm_one_eq_lintegral_eNorm (hf₀_int.1.sub hsint.1)] at hlt
      exact ⟨s, hlt, hsint⟩
    choose s hs_err hs_int using happrox
    let F : MulAction.orbitRel.Quotient H G → E := fun q => ∫ h : H, f₀ ((h : G) * q.out) ∂μH
    let Fn : ℕ → MulAction.orbitRel.Quotient H G → E :=
      fun n q => ∫ h : H, s n ((h : G) * q.out) ∂μH
    let d : ℕ → MulAction.orbitRel.Quotient H G → ℝ≥0∞ :=
      fun n q => ∫⁻ h : H, ‖f₀ ((h : G) * q.out) - s n ((h : G) * q.out)‖ₑ ∂μH
    have hd_meas : ∀ n, Measurable (d n) := fun n =>
      measurable_lintegral_rightCoset H hH μH hmod (hf₀_sm.sub (s n).stronglyMeasurable).eNorm
    have hd_int : ∀ n, ∫⁻ q, d n q ∂ν = ∫⁻ g, ‖f₀ g - s n g‖ₑ ∂μG := fun n =>
      (lintegral_eq_lintegral_quotientMeasure H hH μG μH hmod
        (hf₀_sm.sub (s n).stronglyMeasurable).eNorm).symm
    have htsum_lt : ∫⁻ q, (∑' n, d n q) ∂ν < ∞ := by
      rw [lintegral_tsum fun n => (hd_meas n).aemeasurable]
      calc ∑' n, ∫⁻ q, d n q ∂ν
          ≤ ∑' n : ℕ, (1 / 2 : ℝ≥0∞) ^ n := tsum_le_tsum fun n => by
            rw [hd_int n]
            exact (hs_err n).le
        _ < ∞ := by
            rw [ENNReal.tsum_geometric]
            exact ENNReal.inv_lt_top.mpr (by norm_num)
    have hae_tsum : ∀ᵐ q ∂ν, ∑' n, d n q ≠ ∞ :=
      (ae_lt_top (Measurable.tsum hd_meas) htsum_lt.ne).mono fun _ h => h.ne
    have hae_f₀ : ∀ᵐ q ∂ν, Integrable (fun h : H => f₀ ((h : G) * q.out)) μH :=
      ae_integrable_of_integrable_quotientMeasure H hH μG μH hmod hf₀_int
    have hae_sn : ∀ᵐ q ∂ν, ∀ n, Integrable (fun h : H => s n ((h : G) * q.out)) μH :=
      ae_all_iff.mpr fun n =>
        ae_integrable_of_integrable_quotientMeasure H hH μG μH hmod (hs_int n)
    -- Pointwise convergence `Fn n q → F q` for `ν`-a.e. `q`.
    have hae_tendsto : ∀ᵐ q ∂ν, Tendsto (fun n => Fn n q) atTop (𝓝 (F q)) := by
      filter_upwards [hae_tsum, hae_f₀, hae_sn] with q hqsum hqf hqs
      have hd0 : Tendsto (fun n => d n q) atTop (𝓝 0) :=
        ENNReal.tendsto_atTop_zero_of_tsum_ne_top hqsum
      rw [tendsto_iff_edist_tendsto_0]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd0
        (fun _ => bot_le) fun n => ?_
      rw [eDist_eq_eNorm_sub, ← integral_sub (hqs n) hqf]
      calc ‖∫ h : H, (s n ((h : G) * q.out) - f₀ ((h : G) * q.out)) ∂μH‖ₑ
          ≤ ∫⁻ h : H, ‖s n ((h : G) * q.out) - f₀ ((h : G) * q.out)‖ₑ ∂μH :=
            eNorm_integral_le_lintegral_eNorm _
        _ = d n q := lintegral_congr fun h => eNorm_sub_rev _ _
    have hF_asm : AEStronglyMeasurable F ν :=
      aestronglyMeasurable_of_tendsto_ae atTop
        (fun n => (simpleFunc_quotientMeasure H hH μG μH hmod (s n) (hs_int n)).1.1) hae_tendsto
    have hF_fin : HasFiniteIntegral F ν := by
      rw [hasFiniteIntegral_iff_eNorm]
      calc ∫⁻ q, ‖F q‖ₑ ∂ν
          ≤ ∫⁻ q, (∫⁻ h : H, ‖f₀ ((h : G) * q.out)‖ₑ ∂μH) ∂ν :=
            lintegral_mono fun q => eNorm_integral_le_lintegral_eNorm _
        _ = ∫⁻ g, ‖f₀ g‖ₑ ∂μG :=
            (lintegral_eq_lintegral_quotientMeasure H hH μG μH hmod hf₀_sm.eNorm).symm
        _ < ∞ := hf₀_int.2
    have hF_int : Integrable F ν := ⟨hF_asm, hF_fin⟩
    refine ⟨hF_int, ?_⟩
    -- Compare the limits of `∫ s n ∂μG` and `∫ Fn n ∂ν`.
    have hpow0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ≥0∞) ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    have hlim_G : Tendsto (fun n => ∫ g, s n g ∂μG) atTop (𝓝 (∫ g, f₀ g ∂μG)) := by
      rw [tendsto_iff_edist_tendsto_0]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow0
        (fun _ => bot_le) fun n => ?_
      rw [eDist_eq_eNorm_sub, ← integral_sub (hs_int n) hf₀_int]
      calc ‖∫ g, (s n g - f₀ g) ∂μG‖ₑ
          ≤ ∫⁻ g, ‖s n g - f₀ g‖ₑ ∂μG := eNorm_integral_le_lintegral_eNorm _
        _ = ∫⁻ g, ‖f₀ g - s n g‖ₑ ∂μG := lintegral_congr fun g => eNorm_sub_rev _ _
        _ ≤ (1 / 2 : ℝ≥0∞) ^ n := (hs_err n).le
    have hlim_ν : Tendsto (fun n => ∫ q, Fn n q ∂ν) atTop (𝓝 (∫ q, F q ∂ν)) := by
      rw [tendsto_iff_edist_tendsto_0]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow0
        (fun _ => bot_le) fun n => ?_
      have hFn_int := (simpleFunc_quotientMeasure H hH μG μH hmod (s n) (hs_int n)).1
      rw [eDist_eq_eNorm_sub, ← integral_sub hFn_int hF_int]
      calc ‖∫ q, (Fn n q - F q) ∂ν‖ₑ
          ≤ ∫⁻ q, ‖Fn n q - F q‖ₑ ∂ν := eNorm_integral_le_lintegral_eNorm _
        _ ≤ ∫⁻ q, d n q ∂ν := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae_f₀, hae_sn] with q hqf hqs
            rw [← integral_sub (hqs n) hqf]
            calc ‖∫ h : H, (s n ((h : G) * q.out) - f₀ ((h : G) * q.out)) ∂μH‖ₑ
                ≤ ∫⁻ h : H, ‖s n ((h : G) * q.out) - f₀ ((h : G) * q.out)‖ₑ ∂μH :=
                  eNorm_integral_le_lintegral_eNorm _
              _ = d n q := lintegral_congr fun h => eNorm_sub_rev _ _
        _ = ∫⁻ g, ‖f₀ g - s n g‖ₑ ∂μG := hd_int n
        _ ≤ (1 / 2 : ℝ≥0∞) ^ n := (hs_err n).le
    have hseq_eq : (fun n => ∫ g, s n g ∂μG) = fun n => ∫ q, Fn n q ∂ν :=
      funext fun n => (simpleFunc_quotientMeasure H hH μG μH hmod (s n) (hs_int n)).2
    rw [hseq_eq] at hlim_G
    exact tendsto_nhds_unique hlim_G hlim_ν
  · simp [integral_of_not_completeSpace hE]

/-- For an integrable function `f : G → E`, the fiber integral `q ↦ ∫ h : H, f (h * q.out) ∂μH`
is integrable against `quotientMeasure`. -/
theorem integrable_integral_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {f : G → E} (hf : Integrable f μG) :
    Integrable (fun q : MulAction.orbitRel.Quotient H G =>
      ∫ h : H, f ((h : G) * q.out) ∂μH) (quotientMeasure H hH μG μH hmod) :=
  (integrable_and_integral_eq_quotientMeasure H hH μG μH hmod hf).1

/-- **Weil's integration formula for Bochner integrable functions**: for every real normed space `E`
and every `f : G → E` integrable against `μG`,
`∫ g, f g ∂μG = ∫ q, (∫ h : H, f (h * q.out) ∂μH) ∂ν`. -/
theorem integral_eq_integral_quotientMeasure_of_integrable
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {f : G → E} (hf : Integrable f μG) :
    ∫ g, f g ∂μG =
      ∫ q, (∫ h : H, f ((h : G) * q.out) ∂μH) ∂(quotientMeasure H hH μG μH hmod) :=
  (integrable_and_integral_eq_quotientMeasure H hH μG μH hmod hf).2

end BochnerExtension

/-! ### Composition in stages for nested closed subgroups `H₁ ≤ H₂ ≤ G` -/

section Stages

variable {G : Type*} [Group G]

/-- Fiber map `(H₁.subgroupOf H₂) \ H₂ → H₁ \ G` sending `H₁ h₂ ↦ H₁ (h₂ * g)`. -/
def rightCosetStageMap (H₁ H₂ : Subgroup G) (g : G) :
    MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂ → MulAction.orbitRel.Quotient H₁ G :=
  Quotient.lift (fun h₂ : H₂ => (Quotient.mk'' ((h₂ : G) * g) : MulAction.orbitRel.Quotient H₁ G))
    fun x y ⟨k, hk⟩ => by
      have hxy : (k : H₂) * y = x := hk
      apply Quotient.sound'
      refine ⟨⟨(k : G), k.2⟩, ?_⟩
      change (k : G) * ((y : G) * g) = (x : G) * g
      rw [← mul_assoc]
      exact congrArg (· * g) (congrArg Subtype.val hxy)

@[simp]
theorem rightCosetStageMap_mk (H₁ H₂ : Subgroup G) (g : G) (h₂ : H₂) :
    rightCosetStageMap H₁ H₂ g (Quotient.mk'' h₂) = Quotient.mk'' ((h₂ : G) * g) := by
  rfl

/-- Evaluating `rightCosetStageMap` at a coset `q₁₂` uses its representative `q₁₂.out`. -/
theorem rightCosetStageMap_apply (H₁ H₂ : Subgroup G) (g : G)
    (q₁₂ : MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂) :
    rightCosetStageMap H₁ H₂ g q₁₂ = Quotient.mk'' ((q₁₂.out : G) * g) := by
  conv_lhs => rw [← Quotient.out_eq' q₁₂]
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

@[fun_prop]
theorem continuous_rightCosetStageMap (H₁ H₂ : Subgroup G) (g : G) :
    Continuous (rightCosetStageMap H₁ H₂ g) :=
  isQuotientMap_quotient_mk'.continuous_iff.mpr <|
    continuous_quot_mk.comp (continuous_subtype_val.mul continuous_const)

/-- **Composition in stages** for compactly supported continuous functions: for closed subgroups
`H₁ ≤ H₂ ≤ G` with matching modular characters and compatible right Haar measures `μH₁` on `H₁`
and `μH₁₂` on `H₁.subgroupOf H₂`, integration against the quotient measure on `H₁ \ G` factors
as integration over `H₁ \ H₂` followed by integration over `H₂ \ G`. -/
theorem integral_quotientMeasure_stages [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {H₁ H₂ : Subgroup G} (hle : H₁ ≤ H₂)
    (hH₁ : IsClosed (H₁ : Set G)) (hH₂ : IsClosed (H₂ : Set G))
    [LocallyCompactSpace H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [LocallyCompactSpace H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [LocallyCompactSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (H₁.subgroupOf H₂)] [BorelSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₁ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₁ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₂ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₂ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    [BorelSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH₂ : Measure H₂) [μH₂.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₂]
    [μH₂.IsOpenPosMeasure]
    (μH₁ : Measure H₁) [μH₁.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₁]
    [μH₁.IsOpenPosMeasure]
    (μH₁₂ : Measure (H₁.subgroupOf H₂)) [μH₁₂.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH₁₂] [μH₁₂.IsOpenPosMeasure]
    (hμ : Measure.map (Subgroup.subgroupOfEquivOfLe hle) μH₁₂ = μH₁)
    (hmod₁ : ∀ h : H₁, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₁) h)
    (hmod₂ : ∀ h : H₂, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₂) h)
    (hmod₁₂ : ∀ h : H₁.subgroupOf H₂, Measure.modularCharacter (G := H₂) h =
      Measure.modularCharacter (G := H₁.subgroupOf H₂) h)
    {φ : MulAction.orbitRel.Quotient H₁ G → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∫ q₁, φ q₁ ∂(quotientMeasure H₁ hH₁ μG μH₁ hmod₁) =
      ∫ q₂, (∫ q₁₂, φ (Quotient.mk'' ((q₁₂.out : G) * q₂.out))
        ∂(quotientMeasure (H₁.subgroupOf H₂) (hH₁.preimage continuous_subtype_val)
          μH₂ μH₁₂ hmod₁₂))
        ∂(quotientMeasure H₂ hH₂ μG μH₂ hmod₂) := by
  have hH₁₂ : IsClosed ((H₁.subgroupOf H₂ : Subgroup H₂) : Set H₂) :=
    hH₁.preimage continuous_subtype_val
  let Φ : C_c(MulAction.orbitRel.Quotient H₁ G, ℝ) := ⟨⟨φ, hφ⟩, hφc⟩
  obtain ⟨f, hf_avg⟩ := quotientAverage_surjective H₁ hH₁ μH₁ Φ
  have he_cont : Continuous (Subgroup.subgroupOfEquivOfLe hle) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  -- Rewrite the LHS using Weil's formula on `H₁ \ G`.
  have hlhs : ∫ q₁, φ q₁ ∂(quotientMeasure H₁ hH₁ μG μH₁ hmod₁) = ∫ g, f g ∂μG := by
    calc ∫ q₁, φ q₁ ∂(quotientMeasure H₁ hH₁ μG μH₁ hmod₁)
        = ∫ q₁, Φ q₁ ∂(quotientMeasure H₁ hH₁ μG μH₁ hmod₁) := rfl
      _ = quotientFunctional H₁ hH₁ μG μH₁ hmod₁ Φ :=
          integral_quotientMeasure H₁ hH₁ μG μH₁ hmod₁ Φ
      _ = quotientFunctional H₁ hH₁ μG μH₁ hmod₁ (quotientAverage H₁ hH₁ μH₁ f) := by
          rw [hf_avg]
      _ = ∫ g, f g ∂μG := quotientFunctional_quotientAverage H₁ hH₁ μG μH₁ hmod₁ f
  -- For each `q₂`, rewrite the inner integral over `H₁ \ H₂` as `∫ h₂ : H₂, f (h₂ * q₂.out) ∂μH₂`.
  have hinner : ∀ q₂ : MulAction.orbitRel.Quotient H₂ G,
      ∫ q₁₂, φ (Quotient.mk'' ((q₁₂.out : G) * q₂.out))
          ∂(quotientMeasure (H₁.subgroupOf H₂) hH₁₂ μH₂ μH₁₂ hmod₁₂) =
        ∫ h₂ : H₂, f ((h₂ : G) * q₂.out) ∂μH₂ := by
    intro q₂
    let fg : H₂ → ℝ := fun h₂ => f ((h₂ : G) * q₂.out)
    have hfg_cont : Continuous fg := f.continuous.comp (continuous_subtype_val.mul continuous_const)
    have hfg_supp : HasCompactSupport fg := by
      have hKc : IsCompact (((↑) : H₂ → G) ⁻¹' (tsupport f * {q₂.out⁻¹})) :=
        hH₂.isClosedEmbedding_subtypeVal.isCompact_preimage
          (f.hasCompactSupport.mul isCompact_singleton)
      exact HasCompactSupport.of_support_subset_isCompact hKc fun h₂ hh₂ =>
        ⟨(h₂ : G) * q₂.out, subset_tsupport f hh₂, q₂.out⁻¹, rfl, by group⟩
    rw [integral_eq_integral_quotientMeasure (H₁.subgroupOf H₂) hH₁₂ μH₂ μH₁₂ hmod₁₂
      hfg_cont hfg_supp]
    refine integral_congr_ae (Eventually.of_forall fun q₁₂ => ?_)
    dsimp only
    have hφ_eval : φ (Quotient.mk'' ((q₁₂.out : G) * q₂.out)) =
        ∫ h₁ : H₁, f ((h₁ : G) * ((q₁₂.out : G) * q₂.out)) ∂μH₁ := by
      change Φ (Quotient.mk'' ((q₁₂.out : G) * q₂.out)) = _
      rw [← hf_avg, quotientAverage_mk]
    rw [hφ_eval, ← hμ, integral_map (f := fun h₁ : H₁ => f ((h₁ : G) * ((q₁₂.out : G) * q₂.out)))
      he_cont.aemeasurable
      (f.continuous.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable]
    congr 1 with k
    simp [fg, mul_assoc]
  rw [hlhs]
  simp_rw [hinner]
  exact integral_eq_integral_quotientMeasure H₂ hH₂ μG μH₂ hmod₂ f.continuous f.hasCompactSupport

/-- **Composition in stages** for nonnegative Borel functions on second countable groups. -/
theorem lintegral_quotientMeasure_stages [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {H₁ H₂ : Subgroup G} (hle : H₁ ≤ H₂)
    (hH₁ : IsClosed (H₁ : Set G)) (hH₂ : IsClosed (H₂ : Set G))
    [LocallyCompactSpace H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [LocallyCompactSpace H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [LocallyCompactSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (H₁.subgroupOf H₂)] [BorelSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₁ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₁ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₂ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₂ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    [BorelSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH₂ : Measure H₂) [μH₂.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₂]
    [μH₂.IsOpenPosMeasure]
    (μH₁ : Measure H₁) [μH₁.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₁]
    [μH₁.IsOpenPosMeasure]
    (μH₁₂ : Measure (H₁.subgroupOf H₂)) [μH₁₂.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH₁₂] [μH₁₂.IsOpenPosMeasure]
    (hμ : Measure.map (Subgroup.subgroupOfEquivOfLe hle) μH₁₂ = μH₁)
    (hmod₁ : ∀ h : H₁, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₁) h)
    (hmod₂ : ∀ h : H₂, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₂) h)
    (hmod₁₂ : ∀ h : H₁.subgroupOf H₂, Measure.modularCharacter (G := H₂) h =
      Measure.modularCharacter (G := H₁.subgroupOf H₂) h)
    {φ : MulAction.orbitRel.Quotient H₁ G → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ q₁, φ q₁ ∂(quotientMeasure H₁ hH₁ μG μH₁ hmod₁) =
      ∫⁻ q₂, (∫⁻ q₁₂, φ (Quotient.mk'' ((q₁₂.out : G) * q₂.out))
        ∂(quotientMeasure (H₁.subgroupOf H₂) (hH₁.preimage continuous_subtype_val)
          μH₂ μH₁₂ hmod₁₂))
        ∂(quotientMeasure H₂ hH₂ μG μH₂ hmod₂) := by
  have hH₁₂ : IsClosed ((H₁.subgroupOf H₂ : Subgroup H₂) : Set H₂) :=
    hH₁.preimage continuous_subtype_val
  have : IsClosed (H₁ : Set G) := hH₁
  let : T2Space (MulAction.orbitRel.Quotient H₁ G) := t2Space_quotient_mulAction_of_properSMul
  let : LocallyCompactSpace (MulAction.orbitRel.Quotient H₁ G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H₁) (T := G)).locallyCompactSpace
  let : SecondCountableTopology (MulAction.orbitRel.Quotient H₁ G) :=
    ContinuousConstSMul.secondCountableTopology
  let ν₁ := quotientMeasure H₁ hH₁ μG μH₁ hmod₁
  let ν₂ := quotientMeasure H₂ hH₂ μG μH₂ hmod₂
  let ν₁₂ := quotientMeasure (H₁.subgroupOf H₂) hH₁₂ μH₂ μH₁₂ hmod₁₂
  have : IsFiniteMeasureOnCompacts ν₁ :=
    isFiniteMeasureOnCompacts_quotientMeasure H₁ hH₁ μG μH₁ hmod₁
  have : IsFiniteMeasureOnCompacts ν₂ :=
    isFiniteMeasureOnCompacts_quotientMeasure H₂ hH₂ μG μH₂ hmod₂
  have : IsFiniteMeasureOnCompacts ν₁₂ :=
    isFiniteMeasureOnCompacts_quotientMeasure (H₁.subgroupOf H₂) hH₁₂ μH₂ μH₁₂ hmod₁₂
  let κ : MulAction.orbitRel.Quotient H₂ G → Measure (MulAction.orbitRel.Quotient H₁ G) :=
    fun q₂ => Measure.map (rightCosetStageMap H₁ H₂ q₂.out) ν₁₂
  have hκ_int : ∀ q₂ {F : MulAction.orbitRel.Quotient H₁ G → ℝ≥0∞}, Measurable F →
      ∫⁻ q₁, F q₁ ∂(κ q₂) = ∫⁻ q₁₂, F (Quotient.mk'' ((q₁₂.out : G) * q₂.out)) ∂ν₁₂ := by
    intro q₂ F hF
    rw [lintegral_map hF (continuous_rightCosetStageMap H₁ H₂ q₂.out).measurable]
    exact lintegral_congr fun q₁₂ => by rw [rightCosetStageMap_apply]
  have hpre_comp : ∀ (q₂ : MulAction.orbitRel.Quotient H₂ G)
      (K : Set (MulAction.orbitRel.Quotient H₁ G)), IsCompact K →
      IsCompact (rightCosetStageMap H₁ H₂ q₂.out ⁻¹' K) := by
    intro q₂ K hK
    have hrange : K ⊆ Set.range (Quotient.mk'' : G → MulAction.orbitRel.Quotient H₁ G) :=
      fun q _ => ⟨q.out, Quotient.out_eq' q⟩
    obtain ⟨D, hDc, hDcover⟩ :=
      (isOpenMap_quotient_mk'_mul (Γ := H₁) (T := G)).exists_isCompact_subset_image hK hrange
    have hC : IsCompact ((Quotient.mk'' : H₂ → MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂) ''
        (((↑) : H₂ → G) ⁻¹' (D * {q₂.out⁻¹}))) :=
      (hH₂.isClosedEmbedding_subtypeVal.isCompact_preimage
        (hDc.mul isCompact_singleton)).image continuous_quot_mk
    have hcl : IsClosed (rightCosetStageMap H₁ H₂ q₂.out ⁻¹' K) :=
      hK.isClosed.preimage (continuous_rightCosetStageMap H₁ H₂ q₂.out)
    refine hC.of_isClosed_subset hcl fun q₁₂ hq₁₂ => ?_
    rw [mem_preimage, rightCosetStageMap_apply] at hq₁₂
    obtain ⟨d, hdD, hdq⟩ := hDcover hq₁₂
    have heq : Quotient.mk'' d =
        (Quotient.mk'' ((q₁₂.out : G) * q₂.out) : MulAction.orbitRel.Quotient H₁ G) := hdq
    obtain ⟨h₁, hh₁⟩ := Quotient.exact' heq
    have hh₁' : (h₁ : G) * ((q₁₂.out : G) * q₂.out) = d := hh₁
    let k : H₂ := ⟨(h₁ : G), hle h₁.2⟩ * q₁₂.out
    have hk_mem : (k : G) ∈ D * {q₂.out⁻¹} :=
      ⟨d, hdD, q₂.out⁻¹, rfl, by
        change d * q₂.out⁻¹ = (h₁ : G) * (q₁₂.out : G)
        rw [← hh₁']
        group⟩
    refine ⟨k, hk_mem, ?_⟩
    have hmk : (Quotient.mk'' k : MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂) =
        Quotient.mk'' q₁₂.out :=
      Quotient.sound' ⟨⟨⟨(h₁ : G), hle h₁.2⟩, h₁.2⟩, rfl⟩
    rw [hmk, Quotient.out_eq']
  have hinner_cc : ∀ (F : C_c(MulAction.orbitRel.Quotient H₁ G, ℝ)),
      (∀ q₁, 0 ≤ F q₁) →
      ∃ ψ : C_c(MulAction.orbitRel.Quotient H₂ G, ℝ),
        (∀ q₂, 0 ≤ ψ q₂) ∧
        ∀ q₂, ∫⁻ q₁, ENNReal.ofReal (F q₁) ∂(κ q₂) = ENNReal.ofReal (ψ q₂) := by
    intro F hFnn
    obtain ⟨f, hf_avg, hf_nn⟩ := exists_quotientAverage_eq H₁ hH₁ μH₁ F
    have hf0 : ∀ g, 0 ≤ f g := hf_nn hFnn
    refine ⟨quotientAverage H₂ hH₂ μH₂ f, fun q₂ => (quotientAverage H₂ hH₂ μH₂).map_nonneg hf0 q₂,
      fun q₂ => ?_⟩
    rw [hκ_int q₂ (F := fun q₁ => ENNReal.ofReal (F q₁))
      (ENNReal.measurable_ofReal.comp F.continuous.measurable)]
    have hF_q₂_int : Integrable (fun q₁₂ => F (Quotient.mk'' ((q₁₂.out : G) * q₂.out))) ν₁₂ := by
      have hfun : (fun q₁₂ => F (Quotient.mk'' ((q₁₂.out : G) * q₂.out))) =
          fun q₁₂ => F (rightCosetStageMap H₁ H₂ q₂.out q₁₂) :=
        funext fun q₁₂ => by rw [rightCosetStageMap_apply]
      rw [hfun]
      have hsupp : HasCompactSupport fun q₁₂ => F (rightCosetStageMap H₁ H₂ q₂.out q₁₂) :=
        HasCompactSupport.of_support_subset_isCompact (hpre_comp q₂ _ F.hasCompactSupport)
          fun q₁₂ hq => subset_tsupport F hq
      exact (F.continuous.comp
        (continuous_rightCosetStageMap H₁ H₂ q₂.out)).integrable_of_hasCompactSupport hsupp
    rw [← ofReal_integral_eq_lintegral_ofReal hF_q₂_int (Eventually.of_forall fun _ => hFnn _)]
    congr 1
    -- Match the inner integral with `quotientAverage H₂ hH₂ μH₂ f q₂`.
    have he_cont : Continuous (Subgroup.subgroupOfEquivOfLe hle) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    let fg : H₂ → ℝ := fun h₂ => f ((h₂ : G) * q₂.out)
    have hfg_cont : Continuous fg := f.continuous.comp (continuous_subtype_val.mul continuous_const)
    have hfg_supp : HasCompactSupport fg := by
      have hKc : IsCompact (((↑) : H₂ → G) ⁻¹' (tsupport f * {q₂.out⁻¹})) :=
        hH₂.isClosedEmbedding_subtypeVal.isCompact_preimage
          (f.hasCompactSupport.mul isCompact_singleton)
      exact HasCompactSupport.of_support_subset_isCompact hKc fun h₂ hh₂ =>
        ⟨(h₂ : G) * q₂.out, subset_tsupport f hh₂, q₂.out⁻¹, rfl, by group⟩
    rw [quotientAverage_apply,
      integral_eq_integral_quotientMeasure (H₁.subgroupOf H₂) hH₁₂ μH₂ μH₁₂ hmod₁₂
        hfg_cont hfg_supp]
    refine integral_congr_ae (Eventually.of_forall fun q₁₂ => ?_)
    dsimp only
    rw [← hf_avg, quotientAverage_mk, ← hμ,
      integral_map (f := fun h₁ : H₁ => f ((h₁ : G) * ((q₁₂.out : G) * q₂.out)))
        he_cont.aemeasurable
        (f.continuous.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable]
    congr 1 with k
    simp [fg, mul_assoc]
  have hmain := measurable_and_lintegral_eq_of_compactlySupported ν₁ ν₂ κ
    (fun q₂ K hK => by
      rw [Measure.map_apply (continuous_rightCosetStageMap H₁ H₂ q₂.out).measurable
        hK.measurableSet]
      exact (hpre_comp q₂ K hK).measure_lt_top)
    (fun F hFnn => by
      obtain ⟨ψ, -, hψ⟩ := hinner_cc F hFnn
      have hfun : (fun q₂ => ∫⁻ q₁, ENNReal.ofReal (F q₁) ∂(κ q₂)) =
          fun q₂ => ENNReal.ofReal (ψ q₂) := funext hψ
      rw [hfun]
      exact ENNReal.measurable_ofReal.comp ψ.continuous.measurable)
    (fun F hFnn => by
      obtain ⟨ψ, hψnn, hψ⟩ := hinner_cc F hFnn
      simp_rw [hψ]
      rw [← ofReal_integral_eq_lintegral_ofReal F.integrable (Eventually.of_forall hFnn),
        ← ofReal_integral_eq_lintegral_ofReal ψ.integrable (Eventually.of_forall hψnn)]
      congr 1
      have hstage := integral_quotientMeasure_stages hle hH₁ hH₂ μG μH₂ μH₁ μH₁₂ hμ
        hmod₁ hmod₂ hmod₁₂ F.continuous F.hasCompactSupport
      refine hstage.trans (integral_congr_ae (Eventually.of_forall fun q₂ => ?_))
      dsimp only
      have hF_q₂_int : Integrable (fun q₁₂ => F (Quotient.mk'' ((q₁₂.out : G) * q₂.out))) ν₁₂ := by
        have hfun : (fun q₁₂ => F (Quotient.mk'' ((q₁₂.out : G) * q₂.out))) =
            fun q₁₂ => F (rightCosetStageMap H₁ H₂ q₂.out q₁₂) :=
          funext fun q₁₂ => by rw [rightCosetStageMap_apply]
        rw [hfun]
        have hsupp : HasCompactSupport fun q₁₂ => F (rightCosetStageMap H₁ H₂ q₂.out q₁₂) :=
          HasCompactSupport.of_support_subset_isCompact (hpre_comp q₂ _ F.hasCompactSupport)
            fun q₁₂ hq => subset_tsupport F hq
        exact (F.continuous.comp
          (continuous_rightCosetStageMap H₁ H₂ q₂.out)).integrable_of_hasCompactSupport hsupp
      have hq := hψ q₂
      rw [hκ_int q₂ (F := fun q₁ => ENNReal.ofReal (F q₁))
          (ENNReal.measurable_ofReal.comp F.continuous.measurable),
        ← ofReal_integral_eq_lintegral_ofReal hF_q₂_int
          (Eventually.of_forall fun _ => hFnn _)] at hq
      exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => hFnn _) (hψnn q₂)).mp hq)
    hφ
  simpa only [hκ_int _ hφ] using hmain.2

end Stages

/-! ### Boundary cases: `H = ⊥` and `H = ⊤` -/

section BoundaryCases

/-- Canonical homeomorphism `(⊥ : Subgroup G) \ G ≃ₜ G` sending `⊥ g ↦ g`. -/
def quotientBotHomeomorph (G : Type*) [Group G] [TopologicalSpace G] :
    MulAction.orbitRel.Quotient (⊥ : Subgroup G) G ≃ₜ G where
  toFun := Quotient.lift id fun _ _ ⟨h, hh⟩ => by
    have h1 : (h : G) = 1 := Subgroup.mem_bot.mp h.2
    simpa [Subgroup.smul_def, h1] using hh.symm
  invFun := Quotient.mk''
  left_inv q := by
    induction q using Quotient.inductionOn' with | h g => rfl
  right_inv _ := rfl
  continuous_toFun := isQuotientMap_quotient_mk'.continuous_iff.mpr continuous_id
  continuous_invFun := continuous_quot_mk

@[simp]
theorem quotientBotHomeomorph_mk {G : Type*} [Group G] [TopologicalSpace G]
    (g : G) : quotientBotHomeomorph G (Quotient.mk'' g) = g := by
  rfl

@[simp]
theorem quotientBotHomeomorph_symm_apply {G : Type*} [Group G] [TopologicalSpace G]
    (g : G) : (quotientBotHomeomorph G).symm g = Quotient.mk'' g := by
  rfl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- For the trivial subgroup `H = ⊥` equipped with counting measure, transporting `quotientMeasure`
along `quotientBotHomeomorph G : ⊥ \ G ≃ₜ G` recovers the ambient regular right Haar measure
`μG`. -/
theorem map_quotientBotHomeomorph_quotientMeasure [T2Space G]
    [MeasurableSpace (⊥ : Subgroup G)] [BorelSpace (⊥ : Subgroup G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient (⊥ : Subgroup G) G)]
    [BorelSpace (MulAction.orbitRel.Quotient (⊥ : Subgroup G) G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [μG.IsOpenPosMeasure] [μG.Regular] :
    Measure.map (quotientBotHomeomorph G)
      (quotientMeasure (⊥ : Subgroup G) (by simp [Subgroup.coe_bot]) μG Measure.count
        fun h => by have h1 : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.2); simp [h1]) = μG := by
  have hbot : IsClosed ((⊥ : Subgroup G) : Set G) := by simp [Subgroup.coe_bot]
  have hmod : ∀ h : (⊥ : Subgroup G), Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := (⊥ : Subgroup G)) h := fun h => by
    have h1 : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.2)
    simp [h1]
  let e := quotientBotHomeomorph G
  have hreg : (Measure.map e.symm μG).Regular :=
    (inferInstance : μG.Regular).map e.symm
  have heq : Measure.map e.symm μG =
      quotientMeasure (⊥ : Subgroup G) hbot μG Measure.count hmod := by
    refine quotientMeasure_eq_of_regular (⊥ : Subgroup G) hbot μG Measure.count hmod
      fun f hf _ => ?_
    have huniq : ∀ h : (⊥ : Subgroup G), h = 1 := fun h =>
      Subtype.ext (Subgroup.mem_bot.mp h.2)
    have hfun : (fun q : MulAction.orbitRel.Quotient (⊥ : Subgroup G) G =>
        ∫ h : (⊥ : Subgroup G), f ((h : G) * q.out) ∂Measure.count) = fun q => f (e q) := by
      ext q
      rw [integral_fintype Integrable.of_finite]
      have heq_out : e q = q.out := by
        conv_lhs => rw [← Quotient.out_eq' q]
        exact quotientBotHomeomorph_mk q.out
      simp [huniq default, heq_out]
    rw [integral_map e.symm.continuous.aemeasurable
      (by rw [hfun]; exact (hf.comp e.continuous).aestronglyMeasurable)]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    dsimp only
    rw [congr_fun hfun (e.symm g), e.apply_symm_apply]
  rw [← heq, Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
  simp

/-- For `H = ⊤` with matching right Haar measure `Measure.map Subgroup.topEquiv μH = μG`,
`quotientMeasure` gives the single-point space `⊤ \ G` total mass `1`. -/
theorem quotientMeasure_top_univ
    [LocallyCompactSpace (⊤ : Subgroup G)]
    [MeasurableSpace (⊤ : Subgroup G)] [BorelSpace (⊤ : Subgroup G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient (⊤ : Subgroup G) G)]
    [BorelSpace (MulAction.orbitRel.Quotient (⊤ : Subgroup G) G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure (⊤ : Subgroup G)) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure]
    (hμ : Measure.map Subgroup.topEquiv μH = μG)
    (hmod : ∀ h : (⊤ : Subgroup G), Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := (⊤ : Subgroup G)) h) :
    quotientMeasure (⊤ : Subgroup G) (by simp) μG μH hmod Set.univ = 1 := by
  let ν := quotientMeasure (⊤ : Subgroup G) (by simp) μG μH hmod
  have : IsFiniteMeasureOnCompacts ν :=
    isFiniteMeasureOnCompacts_quotientMeasure (⊤ : Subgroup G) (by simp) μG μH hmod
  have hsub : Subsingleton (MulAction.orbitRel.Quotient (⊤ : Subgroup G) G) :=
    ⟨fun a b => by
      induction a using Quotient.inductionOn' with | h x =>
      induction b using Quotient.inductionOn' with | h y =>
      exact Quotient.sound' ⟨⟨x * y⁻¹, trivial⟩, by change x * y⁻¹ * y = x; group⟩⟩
  have hfin : ν Set.univ ≠ ∞ := isCompact_univ.measure_lt_top.ne
  obtain ⟨f, hfc, hfnn, hf1⟩ := exists_continuous_nonneg_pos (1 : G)
  have hpos : 0 < ∫ g, f g ∂μG :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero hfc hfnn hf1
  have hweil := integral_eq_integral_quotientMeasure (⊤ : Subgroup G) (by simp) μG μH hmod
    f.continuous hfc
  have hinner : ∀ q : MulAction.orbitRel.Quotient (⊤ : Subgroup G) G,
      ∫ h : (⊤ : Subgroup G), f ((h : G) * q.out) ∂μH = ∫ g, f g ∂μG := by
    intro q
    have htop_cont : Continuous (Subgroup.topEquiv (G := G)) := continuous_subtype_val
    rw [← hμ, integral_map htop_cont.aemeasurable f.continuous.aestronglyMeasurable]
    have hmul := integral_mul_right_eq_self (μ := μH)
      (fun h : (⊤ : Subgroup G) => f (h : G)) ⟨q.out, trivial⟩
    simpa using hmul
  simp_rw [hinner] at hweil
  rw [integral_const, smul_eq_mul, Measure.real_def] at hweil
  have htoReal : (ν Set.univ).toReal = 1 := by
    nlinarith
  rw [← ENNReal.ofReal_toReal hfin, htoReal, ENNReal.ofReal_one]

end BoundaryCases

end TauCeti
