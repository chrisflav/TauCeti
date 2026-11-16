/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import TauCeti.MeasureTheory.Group.QuotientMeasure.Extension
public import TauCeti.MeasureTheory.Measure.Count.Topology
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Metrizable.Urysohn
import TauCeti.MeasureTheory.Group.ModularCharacter

/-!
# Discrete subgroups, inversion transport, and unfolding for Weil's quotient measure

This module specializes Weil's quotient measure `TauCeti.quotientMeasure` to discrete subgroups
`Γ ≤ G` equipped with counting measure, and bridges the right-coset convention `Γ \ G` (with right
translation action) to Mathlib's left-coset convention `G ⧸ Γ` (with `IsFundamentalDomain Γ.op`
and `QuotientMeasureEqMeasurePreimage`).

## Main results

* `TauCeti.modularCharacter_eq_one_of_discreteTopology`: Every discrete topological group is
  unimodular.
* `TauCeti.automorphize_inv_rightCosetEquivLeftCoset` and
  `TauCeti.automorphize_inv_rightCosetHomeomorphLeftCoset`: Pointwise identification between
  Mathlib's right-orbit automorphization `QuotientGroup.automorphize (f ∘ Inv.inv)` on `G ⧸ Γ` and
  the left-coset sum `∑' γ : Γ, f (γ * q.out)` on `Γ \ G`.
* `TauCeti.map_rightCosetHomeomorphLeftCoset_quotientMeasure`: For a discrete subgroup `Γ` of a
  unimodular second countable locally compact Hausdorff group `G` and a fundamental domain `𝓕` for
  the right action `Γ.op` on `G`, pushing `quotientMeasure` forward along
  `rightCosetHomeomorphLeftCoset Γ : Γ \ G ≃ₜ G ⧸ Γ` recovers Mathlib's quotient measure
  `Measure.map QuotientGroup.mk (μG.restrict 𝓕)`.
* `TauCeti.quotientMeasureEqMeasurePreimage_map_rightCosetHomeomorphLeftCoset`: The pushed-forward
  quotient measure satisfies Mathlib's `QuotientMeasureEqMeasurePreimage`.
* `TauCeti.integral_eq_integral_tsum_quotientMeasure`: Left-coset unfolding
  `∫ g, f g ∂μG = ∫ q, (∑' γ : Γ, f (γ * q.out)) ∂ν` for Bochner integrable functions on `G`.

## References

* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §2.6 (Theorem 2.49).
* Vladimir Platonov, Andrei Rapinchuk, Igor Rapinchuk, *Algebraic Groups and Number Theory*,
  Theorem 3.64.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise Topology

namespace TauCeti

/-- Every discrete topological group is unimodular: its modular character is identically `1`. -/
@[simp]
theorem modularCharacter_eq_one_of_discreteTopology {Γ : Type*} [Group Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ] [IsTopologicalGroup Γ] (γ : Γ) :
    Measure.modularCharacter γ = 1 := by
  borelize Γ
  rw [modularCharacter_apply,
    Measure.modularCharacterFun_eq_haarScalarFactor (Measure.count : Measure Γ)]
  simp only [map_mul_right_eq_self, Measure.haarScalarFactor_self]

/-- Pointwise comparison between Mathlib's right-orbit automorphization on `G ⧸ Γ` and the
left-coset sum on `Γ \ G` along `rightCosetEquivLeftCoset`. -/
theorem automorphize_inv_rightCosetEquivLeftCoset {G : Type*} [Group G] (Γ : Subgroup G)
    {M : Type*} [TopologicalSpace M] [AddCommMonoid M]
    (f : G → M) (q : MulAction.orbitRel.Quotient Γ G) :
    QuotientGroup.automorphize (fun g => f g⁻¹) (rightCosetEquivLeftCoset Γ q) =
      ∑' γ : Γ, f ((γ : G) * q.out) := by
  conv_lhs => rw [← Quotient.out_eq' q, rightCosetEquivLeftCoset_mk]
  change ∑' γ : Γ.op, f ((γ • q.out⁻¹)⁻¹) = ∑' γ : Γ, f ((γ : G) * q.out)
  let e : Γ ≃ Γ.op :=
    { toFun := fun γ => ⟨MulOpposite.op (γ⁻¹ : G), γ⁻¹.2⟩
      invFun := fun γ => ⟨(MulOpposite.unop (γ : Gᵐᵒᵖ))⁻¹, by
        simpa using Subgroup.inv_mem Γ γ.2⟩
      left_inv := fun γ => by ext; simp
      right_inv := fun γ => by ext; simp }
  rw [← e.tsum_eq]
  congr 1 with γ
  change f ((q.out⁻¹ * (γ : G)⁻¹)⁻¹) = f ((γ : G) * q.out)
  simp [mul_inv_rev]

/-- Pointwise comparison between Mathlib's right-orbit automorphization on `G ⧸ Γ` and the
left-coset sum on `Γ \ G` along `rightCosetHomeomorphLeftCoset`. -/
theorem automorphize_inv_rightCosetHomeomorphLeftCoset {G : Type*} [Group G]
    [TopologicalSpace G] [ContinuousInv G] (Γ : Subgroup G)
    {M : Type*} [TopologicalSpace M] [AddCommMonoid M]
    (f : G → M) (q : MulAction.orbitRel.Quotient Γ G) :
    QuotientGroup.automorphize (fun g => f g⁻¹) (rightCosetHomeomorphLeftCoset Γ q) =
      ∑' γ : Γ, f ((γ : G) * q.out) := by
  rw [← Homeomorph.coe_toEquiv, rightCosetHomeomorphLeftCoset_toEquiv]
  exact automorphize_inv_rightCosetEquivLeftCoset Γ f q

section DiscreteInversion

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- A right Haar measure on a unimodular second countable locally compact Hausdorff group is
invariant under inversion (`μG.inv = μG`). -/
private lemma inv_eq_self_of_unimodular (μG : Measure G) [μG.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (huni : ∀ g : G, Measure.modularCharacter g = 1) :
    μG.inv = μG := by
  have : IsFiniteMeasureOnCompacts μG.inv :=
    { lt_top_of_isCompact K hK := by
        rw [Measure.inv_apply]
        exact hK.inv.measure_lt_top }
  have : μG.inv.IsOpenPosMeasure :=
    { open_pos U hUo hUne := by
        rw [Measure.inv_apply]
        exact hUo.inv.measure_ne_zero _ hUne.inv }
  have : μG.inv.IsHaarMeasure := ⟨⟩
  let : TopologicalSpace.MetrizableSpace G :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable G
  have : μG.inv.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μG.inv
  have hinv := Measure.inv_eq_withDensity_modularCharacter_of_regular μG.inv
  rw [Measure.inv_inv] at hinv
  have h1 : (fun x : G => (Measure.modularCharacter x : ℝ≥0∞)) = 1 := by
    ext x
    simp [huni x]
  rw [h1, withDensity_one] at hinv
  exact hinv.symm

/-- **Inversion between left and right quotient conventions**: for a discrete subgroup `Γ` of a
unimodular second countable locally compact Hausdorff group `G` and a fundamental domain `𝓕` for
the right action `Γ.op` on `G`, the inversion homeomorphism `Γ \ G ≃ₜ G ⧸ Γ` carries Weil's
quotient measure (for `μG` and counting measure on `Γ`) to Mathlib's quotient measure
`Measure.map QuotientGroup.mk (μG.restrict 𝓕)`. -/
theorem map_rightCosetHomeomorphLeftCoset_quotientMeasure
    (Γ : Subgroup G) [DiscreteTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
    [MeasurableSpace (MulAction.orbitRel.Quotient Γ G)]
    [BorelSpace (MulAction.orbitRel.Quotient Γ G)]
    [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (huni : ∀ g : G, Measure.modularCharacter g = 1)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ.op 𝓕 μG) :
    Measure.map (rightCosetHomeomorphLeftCoset Γ)
        (quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
          fun γ => by simp [huni]) =
      Measure.map (QuotientGroup.mk : G → G ⧸ Γ) (μG.restrict 𝓕) := by
  have hΓ : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
  have hmod : ∀ γ : Γ, Measure.modularCharacter (G := G) γ =
      Measure.modularCharacter (G := Γ) γ := fun γ => by simp [huni]
  let ν := quotientMeasure Γ hΓ μG Measure.count hmod
  let e := rightCosetHomeomorphLeftCoset Γ
  let π : G → G ⧸ Γ := QuotientGroup.mk
  have : Countable Γ := countable_of_Lindelof_of_discrete
  have hinv_eq : μG.inv = μG := inv_eq_self_of_unimodular μG huni
  -- Pick a Borel set `𝓕₀` equal `μG`-a.e. to `𝓕`.
  obtain ⟨𝓕₀, h𝓕₀m, h𝓕₀ae⟩ := h𝓕.nullMeasurableSet
  -- For `μG`-a.e. `y`, there is a unique `γ : Γ.op` with `γ • y ∈ 𝓕₀`.
  have hae_unique : ∀ᵐ y ∂μG, ∃! γ : Γ.op, γ • y ∈ 𝓕₀ := by
    have hdisj : ∀ᵐ y ∂μG, ∀ γ₁ γ₂ : Γ.op, γ₁ ≠ γ₂ → ¬ (y ∈ γ₁ • 𝓕 ∧ y ∈ γ₂ • 𝓕) := by
      rw [ae_all_iff]
      intro γ₁
      rw [ae_all_iff]
      intro γ₂
      by_cases hne : γ₁ = γ₂
      · exact Eventually.of_forall fun _ h => absurd hne h
      · have h0 : μG (γ₁ • 𝓕 ∩ γ₂ • 𝓕) = 0 := h𝓕.aedisjoint hne
        filter_upwards [compl_mem_ae_iff.mpr h0] with y hy _
        exact hy
    have hshift : ∀ᵐ y ∂μG, ∀ γ : Γ.op, (γ • y ∈ 𝓕 ↔ γ • y ∈ 𝓕₀) := by
      rw [ae_all_iff]
      intro γ
      have hqmp : QuasiMeasurePreserving (fun y : G => γ • y) μG μG :=
        (measurePreserving_smul γ μG).quasiMeasurePreserving
      exact hqmp.ae h𝓕₀ae
    filter_upwards [h𝓕.ae_covers, hdisj, hshift] with y ⟨γ₀, hγ₀⟩ hdisjy hshifty
    refine ⟨γ₀, (hshifty γ₀).mp hγ₀, fun γ hγ => ?_⟩
    by_contra hne
    have h1 : y ∈ γ⁻¹ • 𝓕 := by
      rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
      exact (hshifty γ).mpr hγ
    have h2 : y ∈ γ₀⁻¹ • 𝓕 := by
      rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
      exact hγ₀
    exact hdisjy γ⁻¹ γ₀⁻¹ (fun h => hne (inv_injective h)) ⟨h1, h2⟩
  -- Pull `hae_unique` back by `Inv.inv` (using `μG.inv = μG`) and slice to `ν`-a.e. `q`.
  have hae_inv : ∀ᵐ g ∂μG, ∃! γ : Γ.op, γ • g⁻¹ ∈ 𝓕₀ := by
    have hmp : MeasurePreserving (Inv.inv : G → G) μG μG :=
      ⟨measurable_inv, by rw [← Measure.inv_def, hinv_eq]⟩
    exact hmp.quasiMeasurePreserving.ae hae_unique
  have hae_q : ∀ᵐ q ∂ν, ∃! γ : Γ.op, γ • q.out⁻¹ ∈ 𝓕₀ := by
    filter_upwards [ae_ae_of_ae_quotientMeasure Γ hΓ μG Measure.count hmod hae_inv] with q hq
    have h1 : (1 : Γ) ∉ {γ : Γ | ¬ ∃! γ' : Γ.op, γ' • ((γ : G) * q.out)⁻¹ ∈ 𝓕₀} := by
      intro hmem
      have hpos : (0 : ℝ≥0∞) < Measure.count {γ : Γ |
          ¬ ∃! γ' : Γ.op, γ' • ((γ : G) * q.out)⁻¹ ∈ 𝓕₀} :=
        (by simp : (0 : ℝ≥0∞) < Measure.count ({1} : Set Γ)).trans_le
          (measure_mono (singleton_subset_iff.mpr hmem))
      exact hpos.ne' (ae_iff.mp hq)
    simpa using h1
  -- Test equality of the two measures on every measurable set `s ⊆ G ⧸ Γ`.
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply e.continuous.measurable hs,
    Measure.map_apply QuotientGroup.continuous_mk.measurable hs,
    Measure.restrict_apply (hs.preimage QuotientGroup.continuous_mk.measurable)]
  -- Rewrite `μG (π ⁻¹' s ∩ 𝓕)` via `𝓕₀` and `μG.inv = μG`.
  let A : Set G := Inv.inv ⁻¹' (π ⁻¹' s ∩ 𝓕₀)
  have hAm : MeasurableSet A :=
    ((hs.preimage QuotientGroup.continuous_mk.measurable).inter h𝓕₀m).preimage measurable_inv
  have hμA : μG A = μG (π ⁻¹' s ∩ 𝓕) := by
    have hinvA : μG A = μG.inv (π ⁻¹' s ∩ 𝓕₀) := (Measure.inv_apply μG _).symm
    rw [hinvA, hinv_eq]
    exact measure_congr <| h𝓕₀ae.symm.mono fun x hx => by
      simp [Set.mem_inter_iff, hx]
  rw [← hμA, measure_eq_lintegral_quotientMeasure Γ hΓ μG Measure.count hmod hAm,
    ← lintegral_indicator_one (hs.preimage e.continuous.measurable)]
  symm
  refine lintegral_congr_ae ?_
  filter_upwards [hae_q] with q hq
  -- For `q` with a unique `γ : Γ.op` landing `q.out⁻¹` in `𝓕₀`, the slice count is `1_{e⁻¹ s} q`.
  classical
  let γ₀ : Γ := ⟨(MulOpposite.unop (hq.choose : Gᵐᵒᵖ))⁻¹,
    by simpa using Subgroup.inv_mem Γ hq.choose.2⟩
  have hslice_eq : {γ : Γ | (γ : G) * q.out ∈ A} =
      if q ∈ e ⁻¹' s then ({γ₀} : Set Γ) else ∅ := by
    have hpi : ∀ γ : Γ, π (((γ : G) * q.out)⁻¹) = e q := fun γ => by
      have h1 : π (((γ : G) * q.out)⁻¹) = QuotientGroup.mk (q.out⁻¹ * (γ⁻¹ : Γ)) := by
        simp [π, mul_inv_rev]
      rw [h1, QuotientGroup.mk_mul_of_mem q.out⁻¹ (γ⁻¹ : Γ).2]
      conv_rhs => rw [← Quotient.out_eq' q, rightCosetHomeomorphLeftCoset_mk]
    by_cases hqs : q ∈ e ⁻¹' s
    · simp only [hqs, ↓reduceIte]
      ext γ
      simp only [mem_ofPred_eq, mem_singleton_iff, A, mem_preimage, mem_inter_iff, hpi γ,
        (show e q ∈ s from hqs), true_and]
      constructor
      · intro hγ
        let γ' : Γ.op := ⟨MulOpposite.op (γ⁻¹ : G), γ⁻¹.2⟩
        have hγ'_mem : γ' • q.out⁻¹ ∈ 𝓕₀ := by
          simpa [γ', mul_inv_rev] using hγ
        have huniq : γ' = hq.choose := hq.choose_spec.2 γ' hγ'_mem
        ext
        have hval := congrArg (fun x : Γ.op => MulOpposite.unop (x : Gᵐᵒᵖ)) huniq
        simpa [γ', γ₀] using congrArg Inv.inv hval
      · intro hγ
        subst hγ
        have hmem : q.out⁻¹ * MulOpposite.unop (hq.choose : Gᵐᵒᵖ) ∈ 𝓕₀ := hq.choose_spec.1
        simpa [γ₀, mul_inv_rev] using hmem
    · simp only [hqs, ↓reduceIte]
      ext γ
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, A, mem_preimage, mem_inter_iff,
        hpi γ]
      exact fun h => hqs h.1
  rw [hslice_eq]
  by_cases hqs : q ∈ e ⁻¹' s <;> simp [hqs]

omit [LocallyCompactSpace G] [T2Space G] in
/-- For a discrete subgroup `Γ` of a second countable topological group `G`, the quotient
measurable space `Quotient.instMeasurableSpace` on `G ⧸ Γ` coincides with `borel (G ⧸ Γ)`. -/
private lemma borelSpace_quotientGroup_of_discreteTopology
    (Γ : Subgroup G) [DiscreteTopology Γ] : BorelSpace (G ⧸ Γ) := by
  refine ⟨le_antisymm ?_ ?_⟩
  · -- `Quotient.instMeasurableSpace ≤ borel (G ⧸ Γ)` via local homeomorphism charts `g • V`.
    intro s hs
    have hpre : MeasurableSet (QuotientGroup.mk ⁻¹' s : Set G) := hs
    obtain ⟨U, hUo, hUeq⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Γ))
    have h1U : (1 : G) ∈ U := by
      have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' U := by simp [hUeq]
      exact this
    have hcont : Continuous (fun p : G × G => p.1⁻¹ * p.2) :=
      continuous_fst.inv.mul continuous_snd
    have hnhds : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' U ∈ 𝓝 ((1 : G), (1 : G)) :=
      (hUo.preimage hcont).mem_nhds (by simpa using h1U)
    rw [nhds_prod_eq, Filter.mem_prod_iff] at hnhds
    obtain ⟨V₁, hV₁, V₂, hV₂, hprod⟩ := hnhds
    let V : Set G := interior V₁ ∩ interior V₂
    have hVo : IsOpen V := isOpen_interior.inter isOpen_interior
    have h1V : (1 : G) ∈ V :=
      ⟨mem_interior_iff_mem_nhds.mpr hV₁, mem_interior_iff_mem_nhds.mpr hV₂⟩
    have hVV : ∀ x ∈ V, ∀ y ∈ V, x⁻¹ * y ∈ U := fun x hx y hy =>
      hprod (mk_mem_prod (interior_subset hx.1) (interior_subset hy.2))
    -- Cover `G` by open translates `g • V` and extract a countable subcover via Lindelöf.
    have hcover : (Set.univ : Set G) ⊆ ⋃ g : G, g • V := fun g _ =>
      mem_iUnion.mpr ⟨g, ⟨1, h1V, by simp⟩⟩
    obtain ⟨I, hIcnt, hIcov⟩ := isLindelof_univ.elim_countable_subcover
      (fun g : G => g • V) (fun g => hVo.smul g) hcover
    have hs_eq : s = ⋃ g ∈ I, (QuotientGroup.mk : G → G ⧸ Γ) ''
        (QuotientGroup.mk ⁻¹' s ∩ g • V) := by
      ext q
      induction q using Quotient.inductionOn' with | h x =>
      simp only [mem_iUnion, mem_image, mem_inter_iff, mem_preimage]
      constructor
      · intro hx
        obtain ⟨g, hgI, hxg⟩ := mem_iUnion₂.mp (hIcov (mem_univ x))
        exact ⟨g, hgI, x, ⟨hx, hxg⟩, rfl⟩
      · rintro ⟨_, _, y, ⟨hy, -⟩, hyx⟩
        exact hyx ▸ hy
    rw [hs_eq]
    refine MeasurableSet.biUnion (m := borel (G ⧸ Γ)) hIcnt fun g _ => ?_
    -- `QuotientGroup.mk` restricted to `g • V` is an open embedding.
    let f : ↥(g • V) → G ⧸ Γ := fun x => QuotientGroup.mk x.1
    have hf_inj : Function.Injective f := by
      rintro ⟨x, v₁, hv₁, rfl⟩ ⟨y, v₂, hv₂, rfl⟩ hxy
      have hmem : (g * v₁)⁻¹ * (g * v₂) ∈ (Γ : Set G) :=
        QuotientGroup.eq.mp hxy
      have hsimp : (g * v₁)⁻¹ * (g * v₂) = v₁⁻¹ * v₂ := by group
      have hγ : (⟨v₁⁻¹ * v₂, hsimp ▸ hmem⟩ : Γ) ∈ ((↑) : Γ → G) ⁻¹' U := hVV v₁ hv₁ v₂ hv₂
      rw [hUeq, mem_singleton_iff] at hγ
      have hv : v₁⁻¹ * v₂ = 1 := congrArg Subtype.val hγ
      have hv12 : v₁ = v₂ := by
        calc v₁ = v₁ * (v₁⁻¹ * v₂) := by rw [hv, mul_one]
          _ = v₂ := by group
      exact Subtype.ext (by simp [hv12])
    have hf_open_emb : IsOpenEmbedding f :=
      IsOpenEmbedding.of_continuous_injective_isOpenMap
        (QuotientGroup.continuous_mk.comp continuous_subtype_val) hf_inj
        (QuotientGroup.isOpenMap_coe.comp (hVo.smul g).isOpenEmbedding_subtypeVal.isOpenMap)
    have himg : (QuotientGroup.mk : G → G ⧸ Γ) '' (QuotientGroup.mk ⁻¹' s ∩ g • V) =
        f '' (((↑) : ↥(g • V) → G) ⁻¹' (QuotientGroup.mk ⁻¹' s)) := by
      ext q
      constructor
      · rintro ⟨x, ⟨hx, hxv⟩, rfl⟩
        exact ⟨⟨x, hxv⟩, hx, rfl⟩
      · rintro ⟨⟨x, hxv⟩, hx, rfl⟩
        exact ⟨x, ⟨hx, hxv⟩, rfl⟩
    rw [himg]
    let : MeasurableSpace (G ⧸ Γ) := borel (G ⧸ Γ)
    have : BorelSpace (G ⧸ Γ) := ⟨rfl⟩
    exact hf_open_emb.measurableEmbedding.measurableSet_image.mpr
      (hpre.preimage continuous_subtype_val.measurable)
  · -- `borel (G ⧸ Γ) ≤ Quotient.instMeasurableSpace` from continuity of `QuotientGroup.mk`.
    refine MeasurableSpace.generateFrom_le fun U hUo => ?_
    exact (hUo.preimage QuotientGroup.continuous_mk).measurableSet

/-- The transported quotient measure on `G ⧸ Γ` satisfies Mathlib's
`QuotientMeasureEqMeasurePreimage` (without assuming a priori existence of a fundamental
domain). -/
theorem quotientMeasureEqMeasurePreimage_map_rightCosetHomeomorphLeftCoset
    (Γ : Subgroup G) [DiscreteTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
    [MeasurableSpace (MulAction.orbitRel.Quotient Γ G)]
    [BorelSpace (MulAction.orbitRel.Quotient Γ G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (huni : ∀ g : G, Measure.modularCharacter g = 1) :
    QuotientMeasureEqMeasurePreimage μG
      (Measure.map (rightCosetHomeomorphLeftCoset Γ)
        (quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
          fun γ => by simp [huni])) := by
  refine ⟨fun t ht => ?_⟩
  have : BorelSpace (G ⧸ Γ) := borelSpace_quotientGroup_of_discreteTopology Γ
  exact map_rightCosetHomeomorphLeftCoset_quotientMeasure Γ μG huni ht

/-- **Left-coset unfolding for discrete subgroups**: for an integrable `f : G → E` into any real
normed space `E` on a unimodular second countable locally compact Hausdorff group `G` and a
discrete subgroup `Γ`, `∫ g, f g ∂μG = ∫ q, (∑' γ : Γ, f (γ * q.out)) ∂ν`. -/
theorem integral_eq_integral_tsum_quotientMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : Subgroup G) [DiscreteTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
    [MeasurableSpace (MulAction.orbitRel.Quotient Γ G)]
    [BorelSpace (MulAction.orbitRel.Quotient Γ G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (huni : ∀ g : G, Measure.modularCharacter g = 1)
    {f : G → E} (hf : Integrable f μG) :
    ∫ g, f g ∂μG =
      ∫ q, (∑' γ : Γ, f ((γ : G) * q.out))
        ∂(quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
          fun γ => by simp [huni]) := by
  by_cases hE : CompleteSpace E
  · have hΓ : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
    have hmod : ∀ γ : Γ, Measure.modularCharacter (G := G) γ =
        Measure.modularCharacter (G := Γ) γ := fun γ => by simp [huni]
    have : Countable Γ := countable_of_Lindelof_of_discrete
    rw [integral_eq_integral_quotientMeasure_of_integrable Γ hΓ μG Measure.count hmod hf]
    refine integral_congr_ae ?_
    filter_upwards
      [ae_integrable_of_integrable_quotientMeasure Γ hΓ μG Measure.count hmod hf] with q hq
    rw [integral_countable hq]
    simp [Measure.real_def]
  · simp [integral_of_not_completeSpace hE]

end DiscreteInversion

end TauCeti
