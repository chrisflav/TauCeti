/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.BoundedVariation.Hyperplane
import TauCeti.Analysis.BoundedVariation.Isometry
import TauCeti.Analysis.BoundedVariation.Real
import TauCeti.MeasureTheory.Covering.DensityTheorem
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.InnerHalfSpace
import TauCeti.MeasureTheory.Measure.Hausdorff

/-!
# One-dimensional sets of locally finite perimeter

In a one-dimensional real inner product space `E`, every set `s` of locally finite perimeter in an
open set `Ω` is locally almost everywhere trivial or a half-line: around every point `x ∈ Ω` there
is a ball `ball x δ ⊆ Ω` on which `s` agrees almost everywhere with `∅`, `univ`, or a half-line
`{y | ⟪y, w⟫ < ⟪x, w⟫}` for a unit vector `w`.

This local classification yields an explicit description of all boundary notions in dimension `1`:
* `TauCeti.exists_ball_ae_eq_empty_or_univ_or_halfLine`: local normal form around every `x ∈ Ω`,
  for any additive Haar measure.
* `TauCeti.countable_reducedBoundary_of_finrank_eq_one`: the reduced boundary `∂*s` is countable.
* `TauCeti.reducedBoundary_eq_inter_essentialBoundary_of_finrank_eq_one`: `∂*s = Ω ∩ ∂ᵉs` as an
  exact set equality (not merely up to a null set).
* `TauCeti.map_variationMeasure_eq_count_restrict_reducedBoundary_of_finrank_eq_one`: with respect
  to Lebesgue volume, the pushforward of `|Dχ_s|` is counting measure restricted to `∂*s`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1 and Chapter 15
  (one-dimensional sets of finite perimeter).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 and §3.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set TopologicalSpace TestFunction Filter
open scoped ENNReal NNReal Topology Distributions RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E}

/-! ### Auxiliary helpers -/

/-- Every additive Haar measure on `E` is a positive finite scalar multiple of Lebesgue volume. -/
private theorem exists_pos_ne_top_smul_volume_dim_one [μ.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • volume := by
  set c : ℝ≥0 := Measure.addHaarScalarFactor μ volume
  have hμ : μ = c • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  refine ⟨(c : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · intro h0
    rw [ENNReal.coe_eq_zero] at h0
    rw [h0, zero_smul] at hμ
    exact (measure_ball_pos μ 0 one_pos).ne' (by simp [hμ])
  · rw [hμ]; rfl

/-- Pushing forward a restricted Lebesgue volume along a linear isometry equivalence restricts
volume to the image. -/
private theorem map_restrict_linearIsometryEquiv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (e : F ≃ₗᵢ[ℝ] E) {A : Set F} (hA : MeasurableSet A) :
    Measure.map e (volume.restrict A) = volume.restrict (e '' A) := by
  have hemp : MeasurePreserving e volume volume := e.measurePreserving
  have hemb : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  ext B hB
  rw [Measure.map_apply e.continuous.measurable hB,
    Measure.restrict_apply (hB.preimage e.continuous.measurable), Measure.restrict_apply hB,
    ← hemp.measure_preimage (hB.inter (hemb.measurableSet_image.2 hA)).nullMeasurableSet,
    preimage_inter, e.injective.preimage_image]

/-- Pulling back a locally integrable function along a linear isometry equivalence preserves local
integrability on the preimage open set. -/
private theorem locallyIntegrableOn_comp_linearIsometryEquiv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (e : F ≃ₗᵢ[ℝ] E) {u : E → ℝ} (hu : LocallyIntegrableOn u Ω) :
    LocallyIntegrableOn (u ∘ e) (Opens.comap (e : C(F, E)) Ω) := by
  rw [locallyIntegrableOn_iff (Opens.comap (e : C(F, E)) Ω).isOpen.isLocallyClosed]
  intro K hKU hK
  have hint : IntegrableOn u (e '' K) volume :=
    hu.integrableOn_compact_subset (image_subset_iff.2 hKU) (hK.image e.continuous)
  have hemb : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  rw [IntegrableOn, ← map_restrict_linearIsometryEquiv e hK.isClosed.measurableSet] at hint
  exact hemb.integrable_map_iff.1 hint

/-! ### Local normal form on `ℝ` -/

/-- If an interval `(p, b)` contains points of both `L₀` and `L₁` arbitrarily close to `p` from
the right, there exist strictly decreasing sequences of arbitrary length `N + 1` alternating
between `L₀` and `L₁`. -/
private theorem exists_strictAnti_alternating_right {L₀ L₁ : Set ℝ} {p b : ℝ}
    (h₀ : ∀ δ > 0, ∃ t ∈ Ioo p (p + δ), t ∈ L₀) (h₁ : ∀ δ > 0, ∃ t ∈ Ioo p (p + δ), t ∈ L₁)
    (N : ℕ) (hb : p < b) :
    ∃ t : Fin (N + 1) → ℝ, StrictAnti t ∧ (∀ i, t i ∈ Ioo p b) ∧
      ∀ i : Fin (N + 1), if Even (i : ℕ) then t i ∈ L₀ else t i ∈ L₁ := by
  induction N with
  | zero =>
    obtain ⟨t₀, ht₀, hL₀⟩ := h₀ (b - p) (sub_pos.2 hb)
    refine ⟨fun _ => t₀, fun i j hij => absurd hij (by omega),
      fun _ => ⟨ht₀.1, by linarith [ht₀.2]⟩, fun i => by simp [Fin.eq_zero i, hL₀]⟩
  | succ N ih =>
    obtain ⟨t, hanti, hmem, halt⟩ := ih
    set last := t (Fin.last N)
    have hlp : 0 < last - p := sub_pos.2 (hmem (Fin.last N)).1
    obtain ⟨u, hu, huL⟩ : ∃ u ∈ Ioo p last, if Even (N + 1) then u ∈ L₀ else u ∈ L₁ := by
      split_ifs
      · obtain ⟨u, hu, hL⟩ := h₀ (last - p) hlp
        exact ⟨u, ⟨hu.1, by linarith [hu.2]⟩, hL⟩
      · obtain ⟨u, hu, hL⟩ := h₁ (last - p) hlp
        exact ⟨u, ⟨hu.1, by linarith [hu.2]⟩, hL⟩
    refine ⟨Fin.snoc t u, ?_, fun i => ?_, fun i => ?_⟩
    · refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [Fin.snoc_last, Fin.snoc_castSucc] using hu.2
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hanti j.castSucc_lt_succ
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact ⟨hu.1, hu.2.trans (hmem (Fin.last N)).2⟩
      · rw [Fin.snoc_castSucc]; exact hmem j
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [Fin.snoc_last] using huL
      · simpa [Fin.snoc_castSucc] using halt j

/-- Almost every point of `(a, b)` is a Lebesgue point of `s.indicator 1`. -/
private theorem ae_lebesgue_indicator_Ioo {U : Opens ℝ} {s : Set ℝ}
    (hu : LocallyIntegrableOn (s.indicator (1 : ℝ → ℝ)) U)
    {a b : ℝ} (hIcc : Icc a b ⊆ U) :
    ∀ᵐ x ∂volume.restrict (Ioo a b),
      Tendsto (fun r => ⨍ y in closedBall x r, ‖s.indicator 1 y - s.indicator (1 : ℝ → ℝ) x‖)
        (𝓝[>] 0) (𝓝 0) := by
  have hIoo : IntegrableOn (s.indicator (1 : ℝ → ℝ)) (Ioo a b) :=
    (hu.integrableOn_compact_subset hIcc isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_average_closedBall_norm_sub volume
    (f := (Ioo a b).indicator (s.indicator (1 : ℝ → ℝ)))
    (hIoo.integrable_indicator measurableSet_Ioo).locallyIntegrable
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioo] with x hx hxIoo
  refine hx.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (eventually_closedBall_subset (isOpen_Ioo.mem_nhds hxIoo))] with r hr
  refine setAverage_congr_fun measurableSet_closedBall (ae_of_all _ fun y hy => ?_)
  simp [indicator_of_mem (hr hy), indicator_of_mem hxIoo]

/-- On `ℝ`, a set `s` of finite perimeter on an open set `U` containing `[a, b]` is a.e. constant on
a sufficiently small open interval to the right of any `p ∈ (a, b)`. -/
private theorem exists_right_ae_const_real {U : Opens ℝ} {s : Set ℝ}
    (hu : LocallyIntegrableOn (s.indicator (1 : ℝ → ℝ)) U)
    (hfin : totalVariationOn volume U (s.indicator 1) ≠ ∞)
    {a b p : ℝ} (hIcc : Icc a b ⊆ U) (hp : p ∈ Ioo a b) :
    ∃ δ > 0, p + δ ≤ b ∧
      (s =ᵐ[volume.restrict (Ioo p (p + δ))] (∅ : Set ℝ) ∨
       s =ᵐ[volume.restrict (Ioo p (p + δ))] univ) := by
  have hae' := ae_lebesgue_indicator_Ioo hu hIcc
  set L₀ : Set ℝ := {x ∈ Ioo a b |
    Tendsto (fun r => ⨍ y in closedBall x r, ‖s.indicator (1 : ℝ → ℝ) y - 0‖) (𝓝[>] 0) (𝓝 0)}
  set L₁ : Set ℝ := {x ∈ Ioo a b |
    Tendsto (fun r => ⨍ y in closedBall x r, ‖s.indicator (1 : ℝ → ℝ) y - 1‖) (𝓝[>] 0) (𝓝 0)}
  by_contra hno
  push Not at hno
  have hmeet (v : ℕ) (hv : v = 0 ∨ v = 1) (δ : ℝ) (hδ : 0 < δ) :
      ∃ t ∈ Ioo p (p + δ), t ∈ if v = 0 then L₀ else L₁ := by
    set δ' := min δ (b - p)
    have hδ' : 0 < δ' := lt_min hδ (sub_pos.2 hp.2)
    have hsub : Ioo p (p + δ') ⊆ Ioo a b := fun y hy =>
      ⟨hp.1.trans hy.1, by linarith [hy.2, min_le_right δ (b - p)]⟩
    have haeJ := ae_restrict_of_ae_restrict_of_subset hsub hae'
    rcases hv with rfl | rfl
    · have hpos : volume.restrict (Ioo p (p + δ')) sᶜ ≠ 0 := fun h0 =>
        (hno δ' hδ' (by linarith [min_le_right δ (b - p)])).2 (ae_eq_univ.2 h0)
      obtain ⟨t, ht, hLeb, htI⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
        (ae_restrict_of_ae (haeJ.and (ae_restrict_mem measurableSet_Ioo)))
      refine ⟨t, ⟨htI.1, htI.2.trans_le (by linarith [min_le_left δ (b - p)])⟩, ?_⟩
      simp only [↓reduceIte]
      exact ⟨hsub htI, by simpa only [indicator_of_notMem ht] using hLeb⟩
    · have hpos : volume.restrict (Ioo p (p + δ')) s ≠ 0 := fun h0 =>
        (hno δ' hδ' (by linarith [min_le_right δ (b - p)])).1 (ae_eq_empty.2 h0)
      obtain ⟨t, ht, hLeb, htI⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
        (ae_restrict_of_ae (haeJ.and (ae_restrict_mem measurableSet_Ioo)))
      refine ⟨t, ⟨htI.1, htI.2.trans_le (by linarith [min_le_left δ (b - p)])⟩, ?_⟩
      simp only [one_ne_zero, ↓reduceIte]
      exact ⟨hsub htI, by simpa only [indicator_of_mem ht, Pi.one_apply] using hLeb⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (totalVariationOn volume U (s.indicator 1)).toReal
  obtain ⟨t, hanti, htI, halt⟩ := exists_strictAnti_alternating_right
    (fun δ hδ => by simpa using hmeet 0 (Or.inl rfl) δ hδ)
    (fun δ hδ => by simpa using hmeet 1 (Or.inr rfl) δ hδ) N hp.2
  let x : Fin (N + 1) → ℝ := fun i => t i.rev
  let v : Fin (N + 1) → ℝ := fun i => if Even (i.rev : ℕ) then 0 else 1
  have hx_mono : Monotone x := fun i j hij => hanti.antitone (Fin.rev_le_rev.2 hij)
  have hxIcc : Icc (x 0) (x (Fin.last N)) ⊆ U := fun y hy =>
    hIcc ⟨(hp.1.trans (htI _).1).le.trans hy.1, hy.2.trans (htI _).2.le⟩
  have hle := TauCeti.Real.ofReal_sum_abs_sub_le_totalVariationOn (v := v) hu hx_mono hxIcc
    fun i => by
    have hi := halt i.rev
    simp only [x, v]
    split_ifs at hi ⊢ <;> exact hi.2
  have hsum : ∑ i : Fin N, |v i.succ - v i.castSucc| = (N : ℝ) := by
    have hterm (i : Fin N) : |v i.succ - v i.castSucc| = 1 := by
      have hpar : (i.castSucc.rev : ℕ) = (i.succ.rev : ℕ) + 1 := by
        simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]; omega
      simp only [v, hpar, Nat.even_add_one]
      split_ifs <;> norm_num
    simp [hterm]
  rw [hsum] at hle
  have hlt : totalVariationOn volume U (s.indicator 1) < ENNReal.ofReal N := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_nonneg.trans_lt hN)).2 hN
  exact not_lt.2 hle hlt

/-- On `ℝ`, a set `s` of finite perimeter on `U` containing `[a, b]` is a.e. constant on a
sufficiently small open interval to the left of any `p ∈ (a, b)`. -/
private theorem exists_left_ae_const_real {U : Opens ℝ} {s : Set ℝ}
    (hu : LocallyIntegrableOn (s.indicator (1 : ℝ → ℝ)) U)
    (hfin : totalVariationOn volume U (s.indicator 1) ≠ ∞)
    {a b p : ℝ} (hIcc : Icc a b ⊆ U) (hp : p ∈ Ioo a b) :
    ∃ δ > 0, a ≤ p - δ ∧
      (s =ᵐ[volume.restrict (Ioo (p - δ) p)] (∅ : Set ℝ) ∨
       s =ᵐ[volume.restrict (Ioo (p - δ) p)] univ) := by
  let negE : ℝ ≃ₗᵢ[ℝ] ℝ := LinearIsometryEquiv.neg ℝ
  have hneg_mp : MeasurePreserving negE volume volume := negE.measurePreserving
  have hneg_emb : MeasurableEmbedding negE := negE.toMeasurableEquiv.measurableEmbedding
  set U' : Opens ℝ := Opens.comap (negE : C(ℝ, ℝ)) U
  have hIcc' : Icc (-b) (-a) ⊆ U' := fun y hy => by
    change -y ∈ U
    exact hIcc ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hu' : LocallyIntegrableOn ((negE ⁻¹' s).indicator (1 : ℝ → ℝ)) U' := by
    have heq : (negE ⁻¹' s).indicator (1 : ℝ → ℝ) = s.indicator 1 ∘ negE :=
      funext fun _ => Set.indicator_comp_right (g := fun _ => (1 : ℝ)) negE
    rw [heq]
    exact locallyIntegrableOn_comp_linearIsometryEquiv negE hu
  have hfin' : totalVariationOn volume U' ((negE ⁻¹' s).indicator 1) ≠ ∞ := by
    rwa [← perimeter_def, negE.perimeter_comap hneg_mp, perimeter_def]
  obtain ⟨δ, hδ, hδb, hR⟩ := exists_right_ae_const_real hu' hfin' hIcc'
    (show -p ∈ Ioo (-b) (-a) from ⟨by linarith [hp.2], by linarith [hp.1]⟩)
  have hmap : Measure.map negE (volume.restrict (Ioo (-p) (-p + δ))) =
      volume.restrict (Ioo (p - δ) p) := by
    rw [map_restrict_linearIsometryEquiv negE measurableSet_Ioo]
    congr 1; ext y
    simp only [mem_image, mem_Ioo, negE, LinearIsometryEquiv.coe_neg]
    exact ⟨fun ⟨z, hz, hy⟩ => ⟨by linarith [hz.2], by linarith [hz.1]⟩,
      fun hy => ⟨-y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, neg_neg y⟩⟩
  have pull {t : Set ℝ} (ht : negE ⁻¹' s =ᵐ[volume.restrict (Ioo (-p) (-p + δ))] negE ⁻¹' t) :
      s =ᵐ[volume.restrict (Ioo (p - δ) p)] t := by
    rw [ae_eq_set] at ht ⊢
    rw [← hmap, hneg_emb.map_apply, hneg_emb.map_apply]
    exact ht
  exact ⟨δ, hδ, by linarith, hR.imp (fun h => pull (t := ∅) (by simpa using h))
    (fun h => pull (t := univ) (by simpa using h))⟩

/-- On `ℝ`, a set `s` of locally finite perimeter agrees a.e. on a small ball around every `p ∈ U`
with `∅`, `univ`, `{y | y < p}`, or `{y | p < y}`. -/
private theorem exists_ball_ae_eq_model_real {U : Opens ℝ} {s : Set ℝ}
    (hu : LocallyIntegrableOn (s.indicator (1 : ℝ → ℝ)) U)
    (hfin : ∀ K, IsCompact K → K ⊆ U →
      ∃ V : Opens ℝ, K ⊆ (V : Set ℝ) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞)
    {p : ℝ} (hp : p ∈ U) :
    ∃ δ > 0, ball p δ ⊆ U ∧
      (s =ᵐ[volume.restrict (ball p δ)] (∅ : Set ℝ) ∨
       s =ᵐ[volume.restrict (ball p δ)] univ ∨
       s =ᵐ[volume.restrict (ball p δ)] {y : ℝ | y < p} ∨
       s =ᵐ[volume.restrict (ball p δ)] {y : ℝ | p < y}) := by
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (U.isOpen.mem_nhds hp)
  obtain ⟨V, hKV, hVfin⟩ := hfin (closedBall p r) (isCompact_closedBall p r) hrU
  set W : Opens ℝ := V ⊓ U
  have hIccW : Icc (p - r) (p + r) ⊆ W := fun y hy =>
    ⟨hKV (by rwa [Real.closedBall_eq_Icc]), hrU (by rwa [Real.closedBall_eq_Icc])⟩
  have huW : LocallyIntegrableOn (s.indicator (1 : ℝ → ℝ)) W := hu.mono_set inf_le_right
  have hWfin : totalVariationOn volume W (s.indicator 1) ≠ ∞ :=
    ne_top_of_le_ne_top hVfin (totalVariationOn_mono inf_le_left)
  have hpI : p ∈ Ioo (p - r) (p + r) := ⟨sub_lt_self p hr, lt_add_of_pos_right p hr⟩
  obtain ⟨δ₁, hδ₁, -, hR⟩ := exists_right_ae_const_real huW hWfin hIccW hpI
  obtain ⟨δ₂, hδ₂, -, hL⟩ := exists_left_ae_const_real huW hWfin hIccW hpI
  set δ := min (min δ₁ δ₂) r
  have hδ : 0 < δ := lt_min (lt_min hδ₁ hδ₂) hr
  have hδU : ball p δ ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_right _ _))).trans hrU
  have hδ1 : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hR' : s =ᵐ[volume.restrict (Ioo p (p + δ))] (∅ : Set ℝ) ∨
      s =ᵐ[volume.restrict (Ioo p (p + δ))] univ :=
    hR.imp (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right (by linarith)))
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right (by linarith)))
  have hL' : s =ᵐ[volume.restrict (Ioo (p - δ) p)] (∅ : Set ℝ) ∨
      s =ᵐ[volume.restrict (Ioo (p - δ) p)] univ :=
    hL.imp (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left (by linarith)))
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left (by linarith)))
  have hball_eq : volume.restrict (ball p δ) =
      volume.restrict (Ioo (p - δ) p ∪ Ioo p (p + δ)) := by
    refine Measure.restrict_congr_set ?_
    rw [Real.ball_eq_Ioo, ae_eq_set]
    refine ⟨measure_mono_null (fun y hy => ?_) (measure_singleton p),
      measure_mono_null (fun y hy => ?_) measure_empty⟩
    · simp only [Set.mem_sdiff, mem_Ioo, mem_union, not_or, not_and_or, not_lt] at hy
      rw [mem_singleton_iff]
      rcases hy.2.1 with h | h
      · linarith [hy.1.1]
      · rcases hy.2.2 with h' | h'
        · exact le_antisymm h' h
        · linarith [hy.1.2]
    · simp only [Set.mem_sdiff, mem_union, mem_Ioo] at hy
      rcases hy.1 with h | h
      · exact absurd ⟨h.1, h.2.trans (by linarith)⟩ hy.2
      · exact absurd ⟨(by linarith : p - δ < p).trans h.1, h.2⟩ hy.2
  have combine {t : Set ℝ} (hl : s =ᵐ[volume.restrict (Ioo (p - δ) p)] t)
      (hr' : s =ᵐ[volume.restrict (Ioo p (p + δ))] t) :
      s =ᵐ[volume.restrict (ball p δ)] t := by
    rw [hball_eq]; exact (ae_restrict_union_iff _ _ _).2 ⟨hl, hr'⟩
  refine ⟨δ, hδ, hδU, ?_⟩
  rcases hL' with hL0 | hL1 <;> rcases hR' with hR0 | hR1
  · exact Or.inl (combine hL0 hR0)
  · refine Or.inr (Or.inr (Or.inr (combine ?_ ?_)))
    · exact hL0.trans ((ae_restrict_mem measurableSet_Ioo).mono fun y hy => by
        simp [not_lt.2 hy.2.le])
    · exact hR1.trans ((ae_restrict_mem measurableSet_Ioo).mono fun y hy => by simp [hy.1])
  · refine Or.inr (Or.inr (Or.inl (combine ?_ ?_)))
    · exact hL1.trans ((ae_restrict_mem measurableSet_Ioo).mono fun y hy => by simp [hy.2])
    · exact hR0.trans ((ae_restrict_mem measurableSet_Ioo).mono fun y hy => by
        simp [not_lt.2 hy.1.le])
  · exact Or.inr (Or.inl (combine hL1 hR1))

/-! ### Transport to an arbitrary 1-dimensional inner product space -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- A one-dimensional inner product space `E` admits an explicit linear isometry equivalence
`y ↦ ⟪y, v⟫` onto `ℝ` for a unit vector `v`. -/
private theorem exists_linearIsometryEquiv_real (h1 : finrank ℝ E = 1) :
    ∃ (v : E) (e : E ≃ₗᵢ[ℝ] ℝ), ‖v‖ = 1 ∧ (∀ y, e y = ⟪y, v⟫) ∧ ∀ t, e.symm t = t • v := by
  let b : OrthonormalBasis (Fin 1) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr h1)
  set v : E := b 0
  have hv : ‖v‖ = 1 := b.orthonormal.1 0
  have hspan (y : E) : ⟪y, v⟫ • v = y := by
    have h := b.sum_repr' y
    simp only [Fin.sum_univ_one, real_inner_comm] at h
    exact h
  let e : E ≃ₗᵢ[ℝ] ℝ :=
    { toFun := fun y => ⟪y, v⟫
      invFun := fun t => t • v
      map_add' := fun x y => inner_add_left x y v
      map_smul' := fun r x => by simp [real_inner_smul_left]
      left_inv := hspan
      right_inv := fun t => by simp [real_inner_smul_left, hv]
      norm_map' := fun y => by
        have h := congrArg norm (hspan y)
        rw [norm_smul, hv, mul_one] at h
        exact h }
  exact ⟨v, e, hv, fun _ => rfl, fun _ => rfl⟩

/-- **Local normal form for 1D sets of locally finite perimeter.** In a one-dimensional real inner
product space, for any additive Haar measure `μ` and any set `s` of locally finite perimeter in an
open set `Ω`, around every point `x ∈ Ω` there is a ball `ball x δ ⊆ Ω` on which `s` agrees
`μ`-a.e. with `∅`, `univ`, or a half-line `{y | ⟪y, w⟫ < ⟪x, w⟫}` for a unit vector `w`. -/
theorem exists_ball_ae_eq_empty_or_univ_or_halfLine [μ.IsAddHaarMeasure] (h1 : finrank ℝ E = 1)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞)
    {x : E} (hx : x ∈ Ω) :
    ∃ δ > 0, ball x δ ⊆ Ω ∧
      (s =ᵐ[μ.restrict (ball x δ)] (∅ : Set E) ∨
       s =ᵐ[μ.restrict (ball x δ)] univ ∨
       ∃ w : E, ‖w‖ = 1 ∧ s =ᵐ[μ.restrict (ball x δ)] {y : E | ⟪y, w⟫ < ⟪x, w⟫}) := by
  obtain ⟨c, hc0, hc, rfl⟩ := exists_pos_ne_top_smul_volume_dim_one (μ := μ)
  have hu' : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω := by
    rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hu ⊢
    exact fun K hKΩ hK => by
      have := hu K hKΩ hK
      rwa [IntegrableOn, Measure.restrict_smul, integrable_smul_measure hc0 hc] at this
  have hfin' : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞ := by
    intro K hK hKΩ
    obtain ⟨V, hKV, hV⟩ := hfin K hK hKΩ
    rw [totalVariationOn_smul_measure hc] at hV
    exact ⟨V, hKV, fun ht => hV (by rw [ht, ENNReal.mul_top hc0])⟩
  obtain ⟨v, e, hv, he, -⟩ := exists_linearIsometryEquiv_real h1
  have hes_mp : MeasurePreserving e.symm volume volume := e.symm.measurePreserving
  have hes_emb : MeasurableEmbedding e.symm := e.symm.toMeasurableEquiv.measurableEmbedding
  set U : Opens ℝ := Opens.comap (e.symm : C(ℝ, E)) Ω
  have hxU : e x ∈ U := by change e.symm (e x) ∈ Ω; simpa using hx
  have huU : LocallyIntegrableOn ((e.symm ⁻¹' s).indicator (1 : ℝ → ℝ)) U := by
    have hcomp : (e.symm ⁻¹' s).indicator (1 : ℝ → ℝ) = s.indicator 1 ∘ e.symm :=
      funext fun _ => Set.indicator_comp_right (g := fun _ => (1 : ℝ)) e.symm
    rw [hcomp]
    exact locallyIntegrableOn_comp_linearIsometryEquiv e.symm hu'
  have hfinU : ∀ K, IsCompact K → K ⊆ U →
      ∃ V : Opens ℝ, K ⊆ (V : Set ℝ) ∧
        totalVariationOn volume V ((e.symm ⁻¹' s).indicator 1) ≠ ∞ := by
    intro K hK hKU
    obtain ⟨W, hKW, hWfin⟩ := hfin' (e.symm '' K) (hK.image e.symm.continuous)
      (image_subset_iff.2 hKU)
    refine ⟨Opens.comap (e.symm : C(ℝ, E)) W, fun t ht => hKW ⟨t, ht, rfl⟩, ?_⟩
    rwa [← perimeter_def, e.symm.perimeter_comap hes_mp, perimeter_def]
  obtain ⟨δ, hδ, hδU, hmod⟩ := exists_ball_ae_eq_model_real huU hfinU hxU
  have hδΩ : ball x δ ⊆ Ω := fun y hy => by
    have : e y ∈ ball (e x) δ := by rwa [mem_ball, e.isometry.dist_eq]
    have := hδU this
    change e.symm (e y) ∈ Ω at this
    simpa using this
  have hmap : Measure.map e.symm (volume.restrict (ball (e x) δ)) =
      volume.restrict (ball x δ) := by
    rw [map_restrict_linearIsometryEquiv e.symm measurableSet_ball]
    congr 1; ext y
    simp only [mem_image, mem_ball]
    refine ⟨fun ⟨t, ht, hy⟩ => ?_,
      fun hy => ⟨e y, by rwa [e.isometry.dist_eq], e.symm_apply_apply y⟩⟩
    rw [← hy, ← e.isometry.dist_eq, e.apply_symm_apply]; exact ht
  have pull {t : Set ℝ} (ht : e.symm ⁻¹' s =ᵐ[volume.restrict (ball (e x) δ)] t) :
      s =ᵐ[(c • volume).restrict (ball x δ)] e ⁻¹' t := by
    have ht' : e.symm ⁻¹' s =ᵐ[volume.restrict (ball (e x) δ)] e.symm ⁻¹' (e ⁻¹' t) := by
      simpa [preimage_preimage] using ht
    have hvol : s =ᵐ[volume.restrict (ball x δ)] e ⁻¹' t := by
      rw [ae_eq_set] at ht' ⊢
      rw [← hmap, hes_emb.map_apply, hes_emb.map_apply]
      exact ht'
    rw [Measure.restrict_smul]
    exact (Measure.ae_ennreal_smul_measure_iff hc0).2 hvol
  refine ⟨δ, hδ, hδΩ, ?_⟩
  rcases hmod with h0 | h1' | hlt | hgt
  · exact Or.inl (by simpa using pull h0)
  · exact Or.inr (Or.inl (by simpa using pull h1'))
  · refine Or.inr (Or.inr ⟨v, hv, ?_⟩)
    simpa [he] using pull hlt
  · refine Or.inr (Or.inr ⟨-v, by rwa [norm_neg], ?_⟩)
    convert pull hgt using 1
    ext y; simp [he, inner_neg_right]

/-! ### Explicit boundary computation on a half-line ball in dimension `1` -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- In dimension `1`, the hyperplane `{y | ⟪y, w⟫ = ⟪x, w⟫}` reduces to `{x}`. -/
private theorem setOf_inner_eq_singleton (h1 : finrank ℝ E = 1) {x w : E} (hw : ‖w‖ = 1) :
    {y : E | ⟪y, w⟫ = ⟪x, w⟫} = {x} := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.1 (hw ▸ one_ne_zero)
  have : Fact (finrank ℝ E = 0 + 1) := ⟨h1⟩
  have hsub_orth : Subsingleton (ℝ ∙ w)ᗮ :=
    finrank_zero_iff.1 (Submodule.finrank_orthogonal_span_singleton (n := 0) hw0)
  ext y
  simp only [mem_ofPred_eq, mem_singleton_iff]
  refine ⟨fun hy => ?_, fun hy => hy ▸ rfl⟩
  have hmem : y - x ∈ (ℝ ∙ w)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_left, hy, sub_self]
  exact sub_eq_zero.1 (congrArg Subtype.val (Subsingleton.elim (⟨y - x, hmem⟩ : (ℝ ∙ w)ᗮ) 0))

/-- Variation measure and polar density of a 1D half-line inside `ball x δ`. -/
private theorem dim_one_halfLine_variationMeasure_and_polarDensity (h1 : finrank ℝ E = 1)
    {x w : E} (hw : ‖w‖ = 1) {δ : ℝ} (hδ : 0 < δ) :
    let B : Opens E := ⟨ball x δ, isOpen_ball⟩
    let H : Set E := {y : E | ⟪y, w⟫ < ⟪x, w⟫}
    variationMeasure volume B (H.indicator 1) = Measure.dirac ⟨x, mem_ball_self hδ⟩ ∧
    polarDensity volume B (H.indicator 1) ⟨x, mem_ball_self hδ⟩ = -w := by
  intro B H
  have hhyp := setOf_inner_eq_singleton h1 (x := x) hw
  have hHm : MeasurableSet H := measurableSet_lt (by fun_prop) measurable_const
  have huH : LocallyIntegrableOn (H.indicator (1 : E → ℝ)) B :=
    ((locallyIntegrable_const 1).indicator hHm).locallyIntegrableOn _
  have hper (U : Opens E) : totalVariationOn volume U (H.indicator 1) =
      Measure.count ((U : Set E) ∩ {x}) := by
    rw [← perimeter_def, perimeter_setOf_inner_lt hw ⟪x, w⟫ U, h1, Nat.sub_self, hhyp,
      Measure.euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_eq_count]
  have hfinH : ∀ K, IsCompact K → K ⊆ (B : Set E) →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (H.indicator 1) ≠ ∞ :=
    fun _ _ hKB => ⟨B, hKB, by
      rw [hper B]
      exact ((measure_mono inter_subset_right).trans_eq (Measure.count_singleton x)).trans_lt
        ENNReal.one_lt_top |>.ne⟩
  set xB : B := ⟨x, mem_ball_self hδ⟩
  have hvar : variationMeasure volume B (H.indicator 1) = Measure.dirac xB := by
    refine (eq_variationMeasure huH hfinH fun U _ => ?_).symm
    rw [hper U, Measure.dirac_apply' _ (U.isOpen.preimage continuous_subtype_val).measurableSet]
    by_cases hxU : x ∈ (U : Set E)
    · rw [inter_eq_right.2 (singleton_subset_iff.2 hxU), Measure.count_singleton,
        indicator_of_mem (show xB ∈ ((↑) : B → E) ⁻¹' U from hxU), Pi.one_apply]
    · rw [inter_singleton_eq_empty.2 hxU, measure_empty,
        indicator_of_notMem (show xB ∉ ((↑) : B → E) ⁻¹' U from hxU)]
  refine ⟨hvar, ?_⟩
  have : IsLocallyFiniteMeasure (variationMeasure volume B (H.indicator 1)) :=
    hvar ▸ inferInstance
  have hae := ae_eq_polarDensity huH hfinH (σ := fun _ : B => -w) (locallyIntegrable_const (-w))
    fun φ => by
      rw [hvar, integral_dirac, inner_neg_right, neg_neg]
      have h1' : ∫ y, divergenceCLM φ y * H.indicator 1 y = ∫ y in H, divergenceCLM φ y := by
        rw [← integral_indicator hHm]
        congr 1; ext y; by_cases hy : y ∈ H <;> simp [hy]
      rw [h1', show (fun y => divergenceCLM φ y) =
        fun y => LinearMap.trace ℝ E (fderiv ℝ (φ : E → E) y : E →ₗ[ℝ] E) from
          funext fun y => divergenceCLM_apply φ y,
        setIntegral_setOf_inner_lt_trace_fderiv hw ⟪x, w⟫ (φ.contDiff.of_le (by simp))
          φ.hasCompactSupport, h1, Nat.sub_self, hhyp, Measure.euclideanHausdorffMeasure_zero,
        hausdorffMeasure_zero_eq_count, Measure.restrict_singleton, Measure.count_singleton,
        one_smul, integral_dirac]
  rw [Filter.EventuallyEq, hvar,
    ae_dirac_iff (measurableSet_eq_fun measurable_const measurable_polarDensity)] at hae
  exact hae.symm

/-- Reduced boundary of a 1D half-line inside `ball x δ` equals `{x}`. -/
private theorem dim_one_halfLine_reducedBoundary (h1 : finrank ℝ E = 1)
    {x w : E} (hw : ‖w‖ = 1) {δ : ℝ} (hδ : 0 < δ) :
    reducedBoundary volume ⟨ball x δ, isOpen_ball⟩ {y : E | ⟪y, w⟫ < ⟪x, w⟫} = {x} := by
  set B : Opens E := ⟨ball x δ, isOpen_ball⟩
  set H : Set E := {y : E | ⟪y, w⟫ < ⟪x, w⟫}
  set xB : B := ⟨x, mem_ball_self hδ⟩
  obtain ⟨hvar, hpol⟩ := dim_one_halfLine_variationMeasure_and_polarDensity h1 hw hδ
  ext y
  rw [mem_singleton_iff]
  constructor
  · intro hy
    by_contra hyx
    have hpos : 0 < dist x y := dist_pos.2 (Ne.symm hyx)
    have h0 : Tendsto (fun r => ⨍ z in ((↑) : B → E) ⁻¹' closedBall y r,
        polarDensity volume B (H.indicator 1) z ∂variationMeasure volume B (H.indicator 1))
        (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hpos] with r hr
      have hnot : xB ∉ ((↑) : B → E) ⁻¹' closedBall y r := by
        simp [xB, mem_closedBall, not_le.2 hr.2]
      rw [hvar, setAverage_eq, measureReal_def, Measure.dirac_apply' _
        (isClosed_closedBall.preimage continuous_subtype_val).measurableSet,
        indicator_of_notMem hnot]
      simp
    have heq := tendsto_nhds_unique (tendsto_setAverage_polarDensity hy) h0
    have h1' := norm_outerNormal hy
    rw [neg_eq_zero.1 heq, norm_zero] at h1'
    exact zero_ne_one h1'
  · intro hy
    rw [hy, mem_reducedBoundary]
    refine ⟨mem_ball_self hδ, -w, by rwa [norm_neg], ?_⟩
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
    dsimp only
    have hmem : xB ∈ ((↑) : B → E) ⁻¹' closedBall x r := by simp [xB, hr.le]
    have hres : (Measure.dirac xB).restrict (((↑) : B → E) ⁻¹' closedBall x r) = Measure.dirac xB :=
      Measure.restrict_eq_self_of_ae_mem (by rwa [ae_dirac_eq])
    rw [hvar, setAverage_eq, measureReal_def, Measure.dirac_apply' _
      (isClosed_closedBall.preimage continuous_subtype_val).measurableSet,
      indicator_of_mem hmem, Pi.one_apply, hres, integral_dirac, hpol]
    simp

/-- Essential boundary of a 1D half-line inside `ball x δ` equals `{x}`. -/
private theorem dim_one_halfLine_essentialBoundary (h1 : finrank ℝ E = 1)
    {x w : E} (hw : ‖w‖ = 1) {δ : ℝ} (hδ : 0 < δ) :
    ball x δ ∩ essentialBoundary volume {y : E | ⟪y, w⟫ < ⟪x, w⟫} = {x} := by
  set H : Set E := {y : E | ⟪y, w⟫ < ⟪x, w⟫}
  have hhyp := setOf_inner_eq_singleton h1 (x := x) hw
  ext y
  rw [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨_, hy⟩
    rw [mem_essentialBoundary] at hy
    by_contra hyx
    have hne : ⟪y, w⟫ ≠ ⟪x, w⟫ := fun h => hyx (by
      have : y ∈ {z : E | ⟪z, w⟫ = ⟪x, w⟫} := h
      rwa [hhyp, mem_singleton_iff] at this)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine hy.1 (interior_subset_essentialInterior ?_)
      rw [(isOpen_lt (by fun_prop) continuous_const : IsOpen H).interior_eq]
      exact hlt
    · refine hy.2 (compl_closure_subset_essentialExterior ?_)
      have hopen : IsOpen {z : E | ⟪x, w⟫ < ⟪z, w⟫} := isOpen_lt continuous_const (by fun_prop)
      intro hcl
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ hopen hgt
      exact not_lt.2 (show ⟪z, w⟫ < ⟪x, w⟫ from hz2).le hz1
  · intro hy
    rw [hy]
    refine ⟨mem_ball_self hδ, ?_⟩
    rw [mem_essentialBoundary]
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    have hhalf : HasDensityAt volume H x (1 / 2) := by
      rw [hasDensityAt_iff]
      refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
      dsimp only
      set S₁ := H ∩ closedBall x r
      set S₂ := {z : E | ⟪x, w⟫ < ⟪z, w⟫} ∩ closedBall x r
      have hmp : MeasurePreserving (fun z : E => (2 • x) - z) volume volume :=
        Measure.measurePreserving_sub_left volume (2 • x)
      have hpre : (fun z : E => (2 • x) - z) ⁻¹' S₂ = S₁ := by
        ext z
        simp only [S₁, S₂, H, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_closedBall,
          dist_eq_norm, inner_sub_left, two_smul, inner_add_left]
        refine and_congr ⟨fun h => by linarith, fun h => by linarith⟩ ?_
        have hsub : x + x - z - x = -(z - x) := by abel
        rw [hsub, norm_neg]
      have hS2m : MeasurableSet S₂ :=
        (isOpen_lt continuous_const (by fun_prop)).measurableSet.inter measurableSet_closedBall
      have hS12 : volume S₁ = volume S₂ := by
        rw [← hpre, hmp.measure_preimage hS2m.nullMeasurableSet]
      have hunion : S₁ ∪ S₂ ∪ {x} = closedBall x r := by
        ext z
        simp only [S₁, S₂, H, mem_union, mem_inter_iff, mem_ofPred_eq]
        constructor
        · rintro ((h | h) | rfl)
          · exact h.2
          · exact h.2
          · exact mem_closedBall_self hr.le
        · intro hz
          rcases lt_trichotomy ⟪z, w⟫ ⟪x, w⟫ with h | h | h
          · exact Or.inl (Or.inl ⟨h, hz⟩)
          · right
            have : z ∈ {y : E | ⟪y, w⟫ = ⟪x, w⟫} := h
            rwa [hhyp, mem_singleton_iff] at this
          · exact Or.inl (Or.inr ⟨h, hz⟩)
      have hdisj : Disjoint S₁ S₂ := disjoint_left.2 fun z h1 h2 =>
        not_lt.2 (show ⟪z, w⟫ < ⟪x, w⟫ from h1.1).le (show ⟪x, w⟫ < ⟪z, w⟫ from h2.1)
      have hunion_m : volume (S₁ ∪ S₂ ∪ {x}) = volume (S₁ ∪ S₂) :=
        le_antisymm ((measure_union_le _ _).trans (by simp)) (measure_mono subset_union_left)
      have hsum : volume (closedBall x r) = 2 * volume S₁ := by
        rw [← hunion, hunion_m, measure_union hdisj hS2m, ← hS12, two_mul]
      have hBpos : volume (closedBall x r) ≠ 0 := (measure_closedBall_pos volume x hr).ne'
      have hS1pos : volume S₁ ≠ 0 := fun h0 => hBpos (by simp [hsum, h0])
      have hS1fin : volume S₁ ≠ ∞ :=
        ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
      rw [hsum]
      conv_rhs => lhs; rw [← one_mul (volume S₁)]
      rw [ENNReal.mul_div_mul_right _ _ hS1pos hS1fin]
    exact ⟨fun h1' => by
        rw [mem_essentialInterior] at h1'
        have := hhalf.unique h1'; norm_num at this,
      fun h0' => by
        rw [mem_essentialExterior] at h0'
        have := hhalf.unique h0'; norm_num at this⟩

/-! ### Global 1-dimensional boundary structure -/

/-- Two sets agreeing almost everywhere on an open set `B` have the same essential boundary in
`B`. -/
private theorem essentialBoundary_inter_congr_ae {B : Opens E} {t : Set E}
    (hst : s =ᵐ[volume.restrict (B : Set E)] t) :
    (B : Set E) ∩ essentialBoundary volume s = (B : Set E) ∩ essentialBoundary volume t := by
  ext y
  refine and_congr_right fun hy => ?_
  have hd (d : ℝ≥0∞) : HasDensityAt volume s y d ↔ HasDensityAt volume t y d := by
    simp only [hasDensityAt_iff]
    obtain ⟨ε, hε, hεB⟩ := nhds_basis_closedBall.mem_iff.1 (B.isOpen.mem_nhds hy)
    refine tendsto_congr' (Filter.eventually_of_mem (Ioc_mem_nhdsGT hε) fun r hr => ?_)
    dsimp only
    congr 1
    have hsub : closedBall y r ⊆ (B : Set E) := (closedBall_subset_closedBall hr.2).trans hεB
    have hst' := ae_restrict_of_ae_restrict_of_subset hsub hst
    rw [← Measure.restrict_apply' isClosed_closedBall.measurableSet,
      ← Measure.restrict_apply' isClosed_closedBall.measurableSet]
    exact measure_congr hst'
  simp only [mem_essentialBoundary, mem_essentialInterior, mem_essentialExterior, hd]

/-- Local 1D summary on a model ball `B = ball x δ ⊆ Ω`. -/
private theorem dim_one_local_summary (h1 : finrank ℝ E = 1)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞)
    {x : E} {δ : ℝ} (hδ : 0 < δ) (hB : (⟨ball x δ, isOpen_ball⟩ : Opens E) ≤ Ω)
    (hmod : s =ᵐ[volume.restrict (ball x δ)] (∅ : Set E) ∨
      s =ᵐ[volume.restrict (ball x δ)] univ ∨
      ∃ w : E, ‖w‖ = 1 ∧ s =ᵐ[volume.restrict (ball x δ)] {y : E | ⟪y, w⟫ < ⟪x, w⟫}) :
    let B : Opens E := ⟨ball x δ, isOpen_ball⟩
    ((B : Set E) ∩ reducedBoundary volume Ω s).Countable ∧
    (B : Set E) ∩ reducedBoundary volume Ω s = (B : Set E) ∩ essentialBoundary volume s ∧
    ((variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)).restrict (B : Set E) =
      (Measure.count.restrict (reducedBoundary volume Ω s)).restrict (B : Set E) := by
  intro B
  have hred_eq : reducedBoundary volume B s = (B : Set E) ∩ reducedBoundary volume Ω s :=
    reducedBoundary_eq_inter_of_le hu hfin hB
  have hmap_eq : ((variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)).restrict
      (B : Set E) = (variationMeasure volume B (s.indicator 1)).map ((↑) : B → E) := by
    have hB' : B ≤ Ω := hB
    have h1' := map_inclusion_variationMeasure hu hfin hB'
    have hembΩ : MeasurableEmbedding ((↑) : Ω → E) :=
      Ω.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
    have h2 : (variationMeasure volume B (s.indicator 1)).map ((↑) : B → E) =
        ((variationMeasure volume B (s.indicator 1)).map
          (Set.inclusion (SetLike.coe_subset_coe.2 hB'))).map ((↑) : Ω → E) :=
      (Measure.map_map continuous_subtype_val.measurable
        (Opens.isOpenEmbedding_of_le hB').continuous.measurable).symm
    rw [h2, h1']
    ext A hA
    rw [Measure.restrict_apply hA, hembΩ.map_apply, hembΩ.map_apply,
      Measure.restrict_apply (hA.preimage continuous_subtype_val.measurable), preimage_inter]
  have hvar0 : variationMeasure volume B ((∅ : Set E).indicator 1) = 0 := by
    have : (∅ : Set E).indicator (1 : E → ℝ) = 0 := by ext; simp
    rw [this]
    exact (eq_variationMeasure (locallyIntegrable_zero.locallyIntegrableOn _)
      (fun _ _ h => ⟨B, h, by simp⟩) fun U _ => by simp).symm
  have hred0 : reducedBoundary volume B ∅ = ∅ := eq_empty_of_forall_notMem fun y hy =>
    variationMeasure_preimage_closedBall_ne_zero hy one_pos (by rw [hvar0]; simp)
  have hess0 : essentialBoundary volume (∅ : Set E) = ∅ :=
    subset_empty_iff.1 (essentialBoundary_subset_frontier.trans (by simp))
  have hess1 : essentialBoundary volume (univ : Set E) = ∅ :=
    subset_empty_iff.1 (essentialBoundary_subset_frontier.trans (by simp))
  have hzero_case {t : Set E} (hst : s =ᵐ[volume.restrict (B : Set E)] t)
      (hvt : variationMeasure volume B (t.indicator 1) = 0)
      (hrt : reducedBoundary volume B t = ∅) (het : essentialBoundary volume t = ∅) :
      ((B : Set E) ∩ reducedBoundary volume Ω s).Countable ∧
      (B : Set E) ∩ reducedBoundary volume Ω s = (B : Set E) ∩ essentialBoundary volume s ∧
      ((variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)).restrict (B : Set E) =
        (Measure.count.restrict (reducedBoundary volume Ω s)).restrict (B : Set E) := by
    have hr : (B : Set E) ∩ reducedBoundary volume Ω s = ∅ := by
      rw [← hred_eq, reducedBoundary_congr_ae hst, hrt]
    have hv : variationMeasure volume B (s.indicator 1) = 0 := by
      rw [variationMeasure_congr_ae (indicator_ae_eq_of_ae_eq_set hst), hvt]
    refine ⟨by rw [hr]; exact countable_empty, ?_, ?_⟩
    · rw [hr, essentialBoundary_inter_congr_ae hst, het, inter_empty]
    · rw [hmap_eq, hv, Measure.map_zero, Measure.restrict_restrict B.isOpen.measurableSet,
        hr, Measure.restrict_empty]
  rcases hmod with h0 | h1' | ⟨w, hw, hH⟩
  · exact hzero_case h0 hvar0 hred0 hess0
  · refine hzero_case h1' ?_ ?_ hess1
    · have hc : (univ : Set E).indicator (1 : E → ℝ) = fun y => 1 - (∅ : Set E).indicator 1 y := by
        ext; simp
      rw [hc, variationMeasure_const_sub, hvar0]
    · rw [show (univ : Set E) = (∅ : Set E)ᶜ from compl_empty.symm, reducedBoundary_compl, hred0]
  · have hvarH := (dim_one_halfLine_variationMeasure_and_polarDensity h1 (x := x) hw hδ).1
    have hredH := dim_one_halfLine_reducedBoundary h1 (x := x) hw hδ
    have hessH := dim_one_halfLine_essentialBoundary h1 (x := x) hw hδ
    have hr : (B : Set E) ∩ reducedBoundary volume Ω s = {x} := by
      rw [← hred_eq, reducedBoundary_congr_ae hH, hredH]
    have hv : variationMeasure volume B (s.indicator 1) =
        Measure.dirac ⟨x, mem_ball_self hδ⟩ := by
      rw [variationMeasure_congr_ae (indicator_ae_eq_of_ae_eq_set hH), hvarH]
    refine ⟨by rw [hr]; exact countable_singleton x, ?_, ?_⟩
    · rw [hr, essentialBoundary_inter_congr_ae hH]; exact hessH.symm
    · rw [hmap_eq, hv, Measure.map_dirac' continuous_subtype_val.measurable,
        Measure.restrict_restrict B.isOpen.measurableSet, hr, Measure.restrict_singleton,
        Measure.count_singleton, one_smul]

/-- Global 1D summary for Lebesgue volume. -/
private theorem dim_one_summary_volume (h1 : finrank ℝ E = 1)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞) :
    (reducedBoundary volume Ω s).Countable ∧
    reducedBoundary volume Ω s = (Ω : Set E) ∩ essentialBoundary volume s ∧
    (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E) =
      Measure.count.restrict (reducedBoundary volume Ω s) := by
  choose δ hδ hδΩ hmod using fun x : Ω =>
    exists_ball_ae_eq_empty_or_univ_or_halfLine (μ := volume) h1 hu hfin x.2
  let B : Ω → Opens E := fun x => ⟨ball (x : E) (δ x), isOpen_ball⟩
  have hcov_all : ⋃ x : Ω, (B x : Set E) = (Ω : Set E) := by
    refine Subset.antisymm (iUnion_subset fun x => hδΩ x) fun y hy => ?_
    exact mem_iUnion.2 ⟨⟨y, hy⟩, mem_ball_self (hδ ⟨y, hy⟩)⟩
  obtain ⟨T, hTc, hTcov⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : Ω => (B x : Set E))
    (fun x => (B x).isOpen)
  rw [hcov_all] at hTcov
  have : Countable T := hTc.to_subtype
  have hcovT : ⋃ x : T, (B x.1 : Set E) = (Ω : Set E) := by rw [← hTcov]; ext y; simp
  have hloc (x : Ω) := dim_one_local_summary h1 hu hfin (hδ x) (hδΩ x) (hmod x)
  refine ⟨?_, ?_, ?_⟩
  · have heq : reducedBoundary volume Ω s =
        ⋃ x : T, (B x.1 : Set E) ∩ reducedBoundary volume Ω s := by
      rw [← iUnion_inter, hcovT, inter_eq_right.2 reducedBoundary_subset]
    rw [heq]
    exact countable_iUnion fun x => (hloc x.1).1
  · ext y
    by_cases hy : y ∈ (Ω : Set E)
    · rw [← hcovT, mem_iUnion] at hy
      obtain ⟨x, hx⟩ := hy
      exact ⟨fun h => ⟨hδΩ x.1 hx, ((Set.ext_iff.1 (hloc x.1).2.1 y).1 ⟨hx, h⟩).2⟩,
        fun h => ((Set.ext_iff.1 (hloc x.1).2.1 y).2 ⟨hx, h.2⟩).2⟩
    · exact ⟨fun h => (hy (reducedBoundary_subset h)).elim, fun h => (hy h.1).elim⟩
  · have hres₁ : ((variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)).restrict
        (Ω : Set E) = (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E) := by
      ext A hA
      rw [Measure.restrict_apply hA,
        Measure.map_apply continuous_subtype_val.measurable (hA.inter Ω.isOpen.measurableSet),
        Measure.map_apply continuous_subtype_val.measurable hA, preimage_inter]
      congr 1; ext y; exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
    have hres₂ : (Measure.count.restrict (reducedBoundary volume Ω s)).restrict (Ω : Set E) =
        Measure.count.restrict (reducedBoundary volume Ω s) := by
      rw [Measure.restrict_restrict Ω.isOpen.measurableSet, inter_eq_right.2 reducedBoundary_subset]
    rw [← hres₁, ← hres₂, ← hcovT]
    exact Measure.restrict_iUnion_congr.2 fun x => (hloc x.1).2.2

/-- In dimension `1`, the reduced boundary of any set is countable for every additive Haar
measure `μ`. -/
theorem countable_reducedBoundary_of_finrank_eq_one [μ.IsAddHaarMeasure] (h1 : finrank ℝ E = 1) :
    (reducedBoundary μ Ω s).Countable := by
  obtain ⟨c, hc0, hc, rfl⟩ := exists_pos_ne_top_smul_volume_dim_one (μ := μ)
  rw [reducedBoundary_smul_measure hc0 hc]
  by_cases h : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω ∧
      ∀ K, IsCompact K → K ⊆ Ω →
        ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞
  · exact (dim_one_summary_volume h1 h.1 h.2).1
  · rw [reducedBoundary_eq_empty_of_not h]
    exact countable_empty

/-- In dimension `1`, for a set `s` of locally finite perimeter in `Ω` and any additive Haar
measure `μ`, the reduced boundary coincides exactly with `Ω ∩ ∂ᵉs`. -/
theorem reducedBoundary_eq_inter_essentialBoundary_of_finrank_eq_one [μ.IsAddHaarMeasure]
    (h1 : finrank ℝ E = 1) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞) :
    reducedBoundary μ Ω s = (Ω : Set E) ∩ essentialBoundary μ s := by
  obtain ⟨c, hc0, hc, rfl⟩ := exists_pos_ne_top_smul_volume_dim_one (μ := μ)
  have hu' : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω := by
    rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hu ⊢
    exact fun K hKΩ hK => by
      have := hu K hKΩ hK
      rwa [IntegrableOn, Measure.restrict_smul, integrable_smul_measure hc0 hc] at this
  have hfin' : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞ := by
    intro K hK hKΩ
    obtain ⟨V, hKV, hV⟩ := hfin K hK hKΩ
    rw [totalVariationOn_smul_measure hc] at hV
    exact ⟨V, hKV, fun ht => hV (by rw [ht, ENNReal.mul_top hc0])⟩
  rw [reducedBoundary_smul_measure hc0 hc, essentialBoundary_smul_measure hc0 hc]
  exact (dim_one_summary_volume h1 hu' hfin').2.1

/-- In dimension `1`, the pushforward of the perimeter measure `|Dχ_s|` equals counting measure
restricted to the reduced boundary `∂*s`. -/
theorem map_variationMeasure_eq_count_restrict_reducedBoundary_of_finrank_eq_one
    (h1 : finrank ℝ E = 1) :
    (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E) =
      Measure.count.restrict (reducedBoundary volume Ω s) := by
  by_cases h : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω ∧
      ∀ K, IsCompact K → K ⊆ Ω →
        ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞
  · exact (dim_one_summary_volume h1 h.1 h.2).2.2
  · rw [variationMeasure_eq_zero_of_not h, reducedBoundary_eq_empty_of_not h, Measure.map_zero,
      Measure.restrict_empty]

end TauCeti
