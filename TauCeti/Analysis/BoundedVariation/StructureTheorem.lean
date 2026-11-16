/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import TauCeti.Analysis.BoundedVariation.OneDimensional.Perimeter
import TauCeti.Analysis.BoundedVariation.RelativeIsoperimetric
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.Geometry.MeasureTheory.Rectifiable.Density
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Hausdorff

/-!
# De Giorgi's structure theorem for sets of locally finite perimeter

Let `E` be a finite-dimensional real inner product space of dimension `n = finrank ℝ E`, `Ω` an
open subset of `E`, and `s` a set of locally finite perimeter in `Ω`. This file establishes the
structure of the reduced boundary `∂*s` (`TauCeti.reducedBoundary`) and its relation to the
perimeter measure `|Dχ_s|` (`TauCeti.variationMeasure`), the normalized `(n - 1)`-dimensional
Euclidean Hausdorff measure `μHE[n - 1]`, and the essential boundary `∂ᵉs`
(`TauCeti.essentialBoundary`), in every dimension `n ≥ 0`:

1. **Countable rectifiability** (`TauCeti.countablyRectifiable_reducedBoundary`): the reduced
   boundary `∂*s` is countably `(n - 1)`-rectifiable, for any additive Haar measure.
2. **De Giorgi's measure identification**
   (`TauCeti.map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary`,
   `TauCeti.variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary`): with respect
   to Lebesgue volume, the perimeter measure `|Dχ_s|` is the restriction of `μHE[n - 1]` to `∂*s`.
   In particular `P(s; U) = μHE[n - 1] (U ∩ ∂*s)` for every open `U ⊆ Ω`
   (`TauCeti.perimeter_eq_euclideanHausdorffMeasure_inter_reducedBoundary`), and the Gauss–Green
   formula holds against `μHE[n - 1]` on `∂*s`
   (`TauCeti.setIntegral_trace_fderiv_eq_setIntegral_inner_outerNormal`).
3. **Equivalence of reduced and essential boundaries**
   (`TauCeti.reducedBoundary_ae_eq_inter_essentialBoundary`): for any additive Haar measure,
   `∂*s ⊆ Ω ∩ ∂ᵉs` and `μHE[n - 1] ((Ω ∩ ∂ᵉs) \ ∂*s) = 0`. In particular `Ω ∩ ∂ᵉs` is also
   countably `(n - 1)`-rectifiable and supports the perimeter measure.

## Proof outline

* **Dimension `n ≥ 2`.** At each `x ∈ ∂*s`, the blow-up theorem
  (`TauCeti.tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter`) forces nearby points
  with uniform two-sided volume density bounds to lie in a narrow cone around the tangent
  hyperplane `(ℝ ∙ ν_s x)ᗮ`. Covering the unit sphere and `E` by countable dense nets splits `∂*s`
  into countably many pieces on which orthogonal projection onto a fixed hyperplane has a
  `4`-Lipschitz inverse, proving countable `(n - 1)`-rectifiability.

  Combining the perimeter density limit
  (`TauCeti.tendsto_variationMeasure_closedBall_div_volume_closedBall`) with Euclidean Hausdorff
  density bounds gives mutual comparability of `|Dχ_s|` and `μHE[n - 1]|_{∂*s}`. On any open
  `W ⊆ Ω` of finite perimeter, both restricted measures are finite, and Besicovitch differentiation
  together with the rectifiable density theorem
  (`TauCeti.CountablyRectifiable.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`)
  identifies the Radon–Nikodym derivative as `1`. Exhausting `Ω` by compact sets yields
  `|Dχ_s| = μHE[n - 1]|_{∂*s}` globally.

  For the essential boundary, the ball density ratio
  `r ↦ μ.real (s ∩ closedBall x r) / μ.real (closedBall x r)` is continuous on `(0, ∞)`. At any
  `x ∈ (Ω ∩ ∂ᵉs) \ ∂*s`, the intermediate value theorem gives arbitrarily small radii where the
  ratio stays bounded away from `0` and `1`; the relative isoperimetric inequality
  (`TauCeti.min_measure_inter_measure_sdiff_rpow_le_perimeter`) then yields a positive lower
  `(n - 1)`-density for `|Dχ_s|`, so `μHE[n - 1] ((Ω ∩ ∂ᵉs) \ ∂*s) = 0` since `|Dχ_s|` is
  concentrated on `∂*s`.

* **Dimensions `n = 0` and `n = 1`.** For `n = 0` the reduced and essential boundaries are empty
  and the variation measure vanishes. For `n = 1`, the results follow from the one-dimensional
  local classification in `TauCeti.Analysis.BoundedVariation.OneDimensional.Perimeter`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapters 15–16
  (De Giorgi's structure theorem and Federer's theorem on the essential boundary).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §§5.7–5.8 (structure of sets of finite perimeter).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set TopologicalSpace TestFunction Filter
open scoped ENNReal NNReal Topology Distributions RealInnerProductSpace symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E}

/-! ### Shared measure-theoretic helpers -/

/-- Outer-regularity density comparison for the variation measure: if at every point `x ∈ A ⊆ Ω`
there are arbitrarily small radii `r > 0` with `c * ω_k r ^ k ≤ |Dχ_s| (closedBall x r)`, then
`c * μHE[k] A ≤ |Dχ_s| (coe ⁻¹' A)`. -/
private theorem mul_euclideanHausdorffMeasure_le_variationMeasure_preimage (k : ℕ) {c : ℝ≥0∞}
    {A : Set E} (hAΩ : A ⊆ Ω)
    (h : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0,
      c * volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≤
        variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r)) :
    c * μHE[k] A ≤ variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' A) := by
  set lam := variationMeasure μ Ω (s.indicator 1)
  refine le_of_forall_gt fun b hb => ?_
  obtain ⟨V, hAV, hVo, hVb⟩ := (((↑) : Ω → E) ⁻¹' A).exists_isOpen_lt_of_lt b hb
  let U : Opens E := ⟨((↑) : Ω → E) '' V, Ω.isOpen.isOpenMap_subtype_val V hVo⟩
  have hUV : ((↑) : Ω → E) ⁻¹' (U : Set E) = V := Subtype.val_injective.preimage_image V
  have hAU : A ⊆ (U : Set E) := fun x hx => ⟨⟨x, hAΩ hx⟩, hAV hx, rfl⟩
  have hmap : (lam.map ((↑) : Ω → E)) (U : Set E) = lam V := by
    rw [Measure.map_apply continuous_subtype_val.measurable U.isOpen.measurableSet, hUV]
  refine (Measure.mul_euclideanHausdorffMeasure_le_measure_of_isOpen
    (lam.map ((↑) : Ω → E)) k U.isOpen hAU fun x hx => ?_).trans_lt (hmap.trans_lt hVb)
  refine (h x hx).mono fun r hr => ?_
  rwa [Measure.map_apply continuous_subtype_val.measurable isClosed_closedBall.measurableSet]

/-- In dimension `0`, every set has empty reduced boundary, empty essential boundary, and zero
variation measure. -/
private theorem dim_zero_summary [μ.IsAddHaarMeasure] (h0 : finrank ℝ E = 0) :
    reducedBoundary μ Ω s = ∅ ∧ essentialBoundary μ s = ∅ ∧
      variationMeasure μ Ω (s.indicator 1) = 0 := by
  have : Subsingleton E := finrank_zero_iff.1 h0
  have hred : reducedBoundary μ Ω s = ∅ := eq_empty_of_forall_notMem fun x hx => by
    have h1 := norm_outerNormal hx
    rw [Subsingleton.elim (outerNormal μ Ω s x) 0, norm_zero] at h1
    exact zero_ne_one h1
  have hess : essentialBoundary μ s = ∅ := eq_empty_of_forall_notMem fun x hx => by
    rw [mem_essentialBoundary] at hx
    rcases Set.eq_empty_or_nonempty s with rfl | ⟨y, hy⟩
    · exact hx.2 (by simp [mem_essentialExterior, hasDensityAt_iff])
    · have hs : s = univ := eq_univ_of_forall fun z => Subsingleton.elim y z ▸ hy
      refine hx.1 ?_
      rw [mem_essentialInterior, hs, hasDensityAt_iff]
      refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
      dsimp only
      rw [univ_inter, ENNReal.div_self (measure_closedBall_pos μ x hr).ne'
        measure_closedBall_lt_top.ne]
  have hvar : variationMeasure μ Ω (s.indicator 1) = 0 := by
    by_cases h : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ ∧
        ∀ K, IsCompact K → K ⊆ Ω →
          ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞
    · refine (eq_variationMeasure h.1 h.2 fun U _ => ?_).symm
      simp only [FunLike.coe_zero, Pi.zero_apply]
      symm
      refine le_antisymm (totalVariationOn_le_iff.2 fun φ _ => ?_) bot_le
      have hdiv : ∀ x, divergenceCLM φ x = 0 := fun x => by
        rw [divergenceCLM_apply]
        have hf : fderiv ℝ (φ : E → E) x = 0 := Subsingleton.elim _ _
        simp [hf]
      simp [hdiv]
    · exact variationMeasure_eq_zero_of_not h
  exact ⟨hred, hess, hvar⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A countable set in a normed space is countably `0`-rectifiable. -/
private theorem countablyRectifiable_zero_of_countable {A : Set E} (hA : A.Countable) :
    CountablyRectifiable 0 A := by
  have : Countable A := hA.to_subtype
  have hcov : A = ⋃ x : A, {(x : E)} := by
    ext y; simp only [mem_iUnion, mem_singleton_iff]
    exact ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩
  rw [hcov]
  refine CountablyRectifiable.iUnion fun x => ?_
  have hlip : LipschitzWith 0 (fun _ : EuclideanSpace ℝ (Fin 0) => (x : E)) :=
    LipschitzWith.const (x : E)
  refine (CountablyRectifiable.of_lipschitzWith (A := univ)
    (hlip.restrict univ)).mono fun y hy => ?_
  rw [mem_singleton_iff.1 hy]
  exact ⟨⟨0, trivial⟩, rfl⟩

/-! ### Section 1: Countable rectifiability in dimension `n ≥ 2` -/

/-- For an additive Haar measure, the blow-up at `x ∈ ∂*s` prevents points with uniform two-sided
volume density bounds from lying outside a cone around `(ℝ ∙ ν_s x)ᗮ`. -/
private theorem measure_blowUp_symmDiff_ge_of_inner_gt [μ.IsAddHaarMeasure]
    {x y : E} (hx : x ∈ reducedBoundary μ Ω s) {δ : ℝ} (hxy0 : 0 < ‖y - x‖)
    (hxyδ : 2 * ‖y - x‖ < δ)
    (hy : ∀ r ∈ Ioo 0 δ,
      (1 / 4 : ℝ≥0∞) * μ (ball y r) ≤ μ (s ∩ ball y r) ∧
      (1 / 4 : ℝ≥0∞) * μ (ball y r) ≤ μ (ball y r \ s))
    (hcone : (1 / 2 : ℝ) * ‖y - x‖ < |⟪y - x, outerNormal μ Ω s x⟫|) :
    let r := 2 * ‖y - x‖
    (1 / 4 : ℝ≥0∞) * μ (ball (0 : E) (1 / 4)) ≤
      μ ((((fun w => x + r • w) ⁻¹' s) ∆ {w | ⟪w, outerNormal μ Ω s x⟫ < 0}) ∩
        closedBall (0 : E) 1) := by
  intro r
  have hr : 0 < r := by positivity
  set ν := outerNormal μ Ω s x
  have hν : ‖ν‖ = 1 := norm_outerNormal hx
  set z : E := r⁻¹ • (y - x)
  have hz_norm : ‖z‖ = 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_eq_div]
    dsimp only [r]
    field_simp [hxy0.ne']
  have hz_inner : 1 / 4 < |⟪z, ν⟫| := by
    rw [real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.2 hr), inv_mul_eq_div,
      div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) hr]
    linarith
  have hBsub : ball z (1 / 4) ⊆ closedBall (0 : E) 1 := fun w hw => by
    rw [mem_closedBall_zero_iff]
    have h1 : ‖w - z‖ < 1 / 4 := by rwa [mem_ball, dist_eq_norm] at hw
    linarith [norm_sub_norm_le w z, hz_norm]
  have hscale (t : Set E) : μ (((fun w => x + r • w) ⁻¹' t) ∩ ball z (1 / 4)) =
      (ENNReal.ofReal r ^ finrank ℝ E)⁻¹ * μ (t ∩ ball y (r / 4)) := by
    have himg : (fun w => x + r • w) ⁻¹' ball y (r / 4) = ball z (1 / 4) := by
      ext w
      have hyz : x + r • z = y := by simp [z, smul_smul, mul_inv_cancel₀ hr.ne']
      simp only [mem_preimage, mem_ball, dist_eq_norm, ← hyz]
      rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      constructor <;> intro h <;> nlinarith
    have hcomp : (fun w : E => x + r • w) = (fun w => x + w) ∘ (fun w => r • w) := rfl
    rw [← himg, ← preimage_inter, hcomp, preimage_comp,
      Measure.addHaar_preimage_smul μ hr.ne', measure_preimage_add,
      abs_of_pos (inv_pos.2 (pow_pos hr _)),
      ENNReal.ofReal_inv_of_pos (pow_pos hr _), ENNReal.ofReal_pow hr.le]
  have hBmeas : μ (ball z (1 / 4)) = (ENNReal.ofReal r ^ finrank ℝ E)⁻¹ * μ (ball y (r / 4)) := by
    simpa using hscale univ
  have hr4 : r / 4 ∈ Ioo 0 δ := ⟨by positivity, by linarith⟩
  have hB0 : μ (ball (0 : E) (1 / 4)) = μ (ball z (1 / 4)) := by
    rw [Measure.addHaar_ball_center μ z (1 / 4)]
  rcases lt_or_ge 0 ⟪z, ν⟫ with hzpos | hzneg
  · have hpos : 1 / 4 < ⟪z, ν⟫ := by rwa [abs_of_pos hzpos] at hz_inner
    have hsub : ((fun w => x + r • w) ⁻¹' s) ∩ ball z (1 / 4) ⊆
        (((fun w => x + r • w) ⁻¹' s) ∆ {w | ⟪w, ν⟫ < 0}) ∩ closedBall (0 : E) 1 := by
      intro w ⟨hws, hwB⟩
      refine ⟨Or.inl ⟨hws, ?_⟩, hBsub hwB⟩
      simp only [mem_ofPred_eq, not_lt]
      have h1 : ‖w - z‖ < 1 / 4 := by rwa [mem_ball, dist_eq_norm] at hwB
      have h2 : |⟪w - z, ν⟫| ≤ ‖w - z‖ := by
        simpa [hν] using abs_real_inner_le_norm (w - z) ν
      have h3 : ⟪w, ν⟫ = ⟪z, ν⟫ + ⟪w - z, ν⟫ := by rw [inner_sub_left]; ring
      linarith [(abs_le.1 h2).1]
    calc (1 / 4 : ℝ≥0∞) * μ (ball (0 : E) (1 / 4))
        = (ENNReal.ofReal r ^ finrank ℝ E)⁻¹ * ((1 / 4 : ℝ≥0∞) * μ (ball y (r / 4))) := by
            rw [hB0, hBmeas, mul_left_comm]
      _ ≤ (ENNReal.ofReal r ^ finrank ℝ E)⁻¹ * μ (s ∩ ball y (r / 4)) :=
            mul_le_mul_right (hy (r / 4) hr4).1 _
      _ = μ (((fun w => x + r • w) ⁻¹' s) ∩ ball z (1 / 4)) := (hscale s).symm
      _ ≤ _ := measure_mono hsub
  · have hneg : ⟪z, ν⟫ < -(1 / 4) := by
      rw [abs_of_nonpos hzneg] at hz_inner; linarith
    have hsub : ((fun w => x + r • w) ⁻¹' sᶜ) ∩ ball z (1 / 4) ⊆
        (((fun w => x + r • w) ⁻¹' s) ∆ {w | ⟪w, ν⟫ < 0}) ∩ closedBall (0 : E) 1 := by
      intro w ⟨hws, hwB⟩
      refine ⟨Or.inr ⟨?_, hws⟩, hBsub hwB⟩
      change ⟪w, ν⟫ < 0
      have h1 : ‖w - z‖ < 1 / 4 := by rwa [mem_ball, dist_eq_norm] at hwB
      have h2 : |⟪w - z, ν⟫| ≤ ‖w - z‖ := by
        simpa [hν] using abs_real_inner_le_norm (w - z) ν
      have h3 : ⟪w, ν⟫ = ⟪z, ν⟫ + ⟪w - z, ν⟫ := by rw [inner_sub_left]; ring
      linarith [(abs_le.1 h2).2]
    calc (1 / 4 : ℝ≥0∞) * μ (ball (0 : E) (1 / 4))
        = (ENNReal.ofReal r ^ finrank ℝ E)⁻¹ * ((1 / 4 : ℝ≥0∞) * μ (ball y (r / 4))) := by
            rw [hB0, hBmeas, mul_left_comm]
      _ ≤ (ENNReal.ofReal r ^ finrank ℝ E)⁻¹ * μ (sᶜ ∩ ball y (r / 4)) := by
            rw [inter_comm, ← Set.sdiff_eq]
            exact mul_le_mul_right (hy (r / 4) hr4).2 _
      _ = μ (((fun w => x + r • w) ⁻¹' sᶜ) ∩ ball z (1 / 4)) := (hscale sᶜ).symm
      _ ≤ _ := measure_mono hsub

/-- At every point `x` of the reduced boundary (in dimension `n ≥ 2`), both `s` and `sᶜ` eventually
occupy at least a quarter of every small ball `ball x r`. -/
private theorem exists_nat_two_sided_ball_density [μ.IsAddHaarMeasure] (hn : 2 ≤ finrank ℝ E)
    {x : E} (hx : x ∈ reducedBoundary μ Ω s) :
    ∃ m : ℕ, ∀ r ∈ Ioo 0 (1 / ((m : ℝ) + 1)),
      (1 / 4 : ℝ≥0∞) * μ (ball x r) ≤ μ (s ∩ ball x r) ∧
      (1 / 4 : ℝ≥0∞) * μ (ball x r) ≤ μ (ball x r \ s) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hdens (t : Set E) (ht : x ∈ reducedBoundary μ Ω t) :
      ∀ᶠ r in 𝓝[>] 0, (1 / 4 : ℝ≥0∞) * μ (ball x r) ≤ μ (t ∩ ball x r) := by
    have h1 := hasDensityAt_of_mem_reducedBoundary hn ht
    rw [hasDensityAt_iff] at h1
    have hlt : (1 / 4 : ℝ≥0∞) < 1 / 2 := by norm_num
    filter_upwards [h1.eventually (Ioi_mem_nhds hlt), self_mem_nhdsWithin] with r hr _
    have hcb : μ (closedBall x r) = μ (ball x r) := μ.addHaar_closedBall_eq_addHaar_ball x r
    have htcb : μ (t ∩ closedBall x r) = μ (t ∩ ball x r) :=
      measure_congr (EventuallyEqSet.inter .rfl (μ.addHaar_closedBall_ae_eq_ball x r))
    rw [hcb, htcb] at hr
    exact ENNReal.mul_le_of_le_div hr.le
  have hboth := (hdens s hx).and (hdens sᶜ (by rwa [reducedBoundary_compl]))
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hboth
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m, fun r hr => ?_⟩
  have ⟨h1, h2⟩ := hsub ⟨hr.1, hr.2.trans hm⟩
  rw [inter_comm, ← Set.sdiff_eq] at h2
  exact ⟨h1, h2⟩

/-- A subset of `E` whose chords make angle at least `arcsin (1/4)` away from a unit vector `v₀`
(meaning `|⟪y - x, v₀⟫| ≤ (3/4) ‖y - x‖`) is countably `(n - 1)`-rectifiable, via orthogonal
projection onto `(ℝ ∙ v₀)ᗮ`. -/
private theorem countablyRectifiable_of_abs_inner_le (hn : 2 ≤ finrank ℝ E) {v₀ : E}
    (hv₀ : ‖v₀‖ = 1) {P : Set E}
    (hP : ∀ x ∈ P, ∀ y ∈ P, |⟪y - x, v₀⟫| ≤ (3 / 4 : ℝ) * ‖y - x‖) :
    CountablyRectifiable (finrank ℝ E - 1) P := by
  have hv0 : v₀ ≠ 0 := norm_ne_zero_iff.1 (hv₀ ▸ one_ne_zero)
  have : Fact (finrank ℝ E = finrank ℝ E - 1 + 1) := ⟨(Nat.sub_add_cancel (by omega)).symm⟩
  let eP : (ℝ ∙ v₀)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E - 1)) :=
    ((stdOrthonormalBasis ℝ (ℝ ∙ v₀)ᗮ).reindex (finCongr
      (Submodule.finrank_orthogonal_span_singleton (n := finrank ℝ E - 1) hv0))).repr
  have hmem (z : E) : z - ⟪z, v₀⟫ • v₀ ∈ (ℝ ∙ v₀)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, hv₀]
    ring
  let π : E → EuclideanSpace ℝ (Fin (finrank ℝ E - 1)) := fun z => eP ⟨z - ⟪z, v₀⟫ • v₀, hmem z⟩
  have hπ_dist {x y : E} (hx : x ∈ P) (hy : y ∈ P) : dist y x ≤ 4 * dist (π y) (π x) := by
    have hdiff : dist (π y) (π x) = ‖(y - x) - ⟪y - x, v₀⟫ • v₀‖ := by
      rw [dist_eq_norm, ← map_sub, eP.norm_map]
      change ‖(y - ⟪y, v₀⟫ • v₀) - (x - ⟪x, v₀⟫ • v₀)‖ = _
      congr 1
      rw [inner_sub_left, sub_smul]
      abel
    have htri : ‖y - x‖ ≤ ‖(y - x) - ⟪y - x, v₀⟫ • v₀‖ + |⟪y - x, v₀⟫| := by
      calc ‖y - x‖ = ‖((y - x) - ⟪y - x, v₀⟫ • v₀) + ⟪y - x, v₀⟫ • v₀‖ := by abel_nf
        _ ≤ ‖(y - x) - ⟪y - x, v₀⟫ • v₀‖ + ‖⟪y - x, v₀⟫ • v₀‖ := norm_add_le _ _
        _ = ‖(y - x) - ⟪y - x, v₀⟫ • v₀‖ + |⟪y - x, v₀⟫| := by
            rw [norm_smul, Real.norm_eq_abs, hv₀, mul_one]
    rw [dist_eq_norm, hdiff]
    linarith [hP x hx y hy]
  classical
  let f : EuclideanSpace ℝ (Fin (finrank ℝ E - 1)) → E := fun u =>
    if h : ∃ x ∈ P, π x = u then h.choose else 0
  have hf_mem {u : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))} (hu : u ∈ π '' P) :
      f u ∈ P ∧ π (f u) = u := by
    have h : ∃ x ∈ P, π x = u := hu
    simpa [f, h] using h.choose_spec
  have hlip : LipschitzOnWith 4 f (π '' P) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro u₁ hu₁ u₂ hu₂
    have ⟨h1P, h1π⟩ := hf_mem hu₁
    have ⟨h2P, h2π⟩ := hf_mem hu₂
    simpa [h1π, h2π] using hπ_dist h2P h1P
  have hsub : P ⊆ f '' (π '' P) := fun x hx => by
    have hu : π x ∈ π '' P := ⟨x, hx, rfl⟩
    have ⟨hfP, hfπ⟩ := hf_mem hu
    have heq : f (π x) = x := by
      have hd := hπ_dist hx hfP
      rw [hfπ, dist_self, mul_zero] at hd
      exact dist_le_zero.1 hd
    exact ⟨π x, hu, heq⟩
  exact (CountablyRectifiable.of_lipschitzOnWith hlip).mono hsub

/-- Each cone-bounded piece of `D` with nearly constant outer normal is countably
`(n - 1)`-rectifiable. -/
private theorem countablyRectifiable_cone_piece (hn : 2 ≤ finrank ℝ E) (D : Set E) (k : ℕ)
    {v₀ c₀ : E} (hv₀ : ‖v₀‖ = 1) :
    CountablyRectifiable (finrank ℝ E - 1)
      {x ∈ D | dist x c₀ < 1 / (2 * ((k : ℝ) + 1)) ∧
        ‖outerNormal μ Ω s x - v₀‖ < 1 / 4 ∧
        ∀ y ∈ D, ‖y - x‖ < 1 / ((k : ℝ) + 1) →
          |⟪y - x, outerNormal μ Ω s x⟫| ≤ (1 / 2 : ℝ) * ‖y - x‖} := by
  refine countablyRectifiable_of_abs_inner_le hn hv₀ fun x hx y hy => ?_
  have hxy : ‖y - x‖ < 1 / ((k : ℝ) + 1) := by
    have h1 : ‖y - x‖ ≤ dist y c₀ + dist x c₀ := by
      rw [← dist_eq_norm, dist_comm x c₀]
      exact dist_triangle y c₀ x
    have hk0 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hhalf : 1 / (2 * ((k : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) = 1 / ((k : ℝ) + 1) := by
      field_simp; ring
    linarith [hx.2.1, hy.2.1]
  have h1 := hx.2.2.2 y hy.1 hxy
  have h2 : |⟪y - x, v₀ - outerNormal μ Ω s x⟫| ≤ (1 / 4 : ℝ) * ‖y - x‖ := by
    calc |⟪y - x, v₀ - outerNormal μ Ω s x⟫|
        ≤ ‖y - x‖ * ‖v₀ - outerNormal μ Ω s x‖ := abs_real_inner_le_norm _ _
      _ = ‖y - x‖ * ‖outerNormal μ Ω s x - v₀‖ := by rw [norm_sub_rev v₀]
      _ ≤ ‖y - x‖ * (1 / 4) := by gcongr; exact hx.2.2.1.le
      _ = (1 / 4 : ℝ) * ‖y - x‖ := mul_comm _ _
  have hsplit : ⟪y - x, v₀⟫ =
      ⟪y - x, outerNormal μ Ω s x⟫ + ⟪y - x, v₀ - outerNormal μ Ω s x⟫ := by
    rw [inner_sub_right]; ring
  linarith [hsplit ▸ abs_add_le ⟪y - x, outerNormal μ Ω s x⟫
    ⟪y - x, v₀ - outerNormal μ Ω s x⟫]

/-- At each `x ∈ ∂*s`, the half-space blow-up gives a scale `1 / (k + 1)` below which all points of
a uniform two-sided density set `D` stay inside the cone `|⟪y - x, ν_s x⟫| ≤ (1/2) ‖y - x‖`. -/
private theorem exists_nat_cone_bound_of_mem_reducedBoundary [μ.IsAddHaarMeasure]
    (hn : 2 ≤ finrank ℝ E) {m : ℕ} {x : E} (hx : x ∈ reducedBoundary μ Ω s) :
    ∃ k : ℕ, ∀ y : E,
      (∀ r ∈ Ioo 0 (1 / ((m : ℝ) + 1)),
        (1 / 4 : ℝ≥0∞) * μ (ball y r) ≤ μ (s ∩ ball y r) ∧
        (1 / 4 : ℝ≥0∞) * μ (ball y r) ≤ μ (ball y r \ s)) →
      ‖y - x‖ < 1 / ((k : ℝ) + 1) →
      |⟪y - x, outerNormal μ Ω s x⟫| ≤ (1 / 2 : ℝ) * ‖y - x‖ := by
  have hc₀ : (0 : ℝ≥0∞) < (1 / 4 : ℝ≥0∞) * μ (ball (0 : E) (1 / 4)) :=
    ENNReal.mul_pos (by norm_num) (measure_ball_pos μ 0 (by norm_num)).ne'
  have hblow := tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx
    (isCompact_closedBall 0 1)
  obtain ⟨ρ, hρ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hblow.eventually (Iio_mem_nhds hc₀))
  have hρ' : 0 < min (ρ / 2) (1 / (2 * ((m : ℝ) + 1))) := lt_min (half_pos hρ) (by positivity)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hρ'
  refine ⟨k, fun y hy hxy => ?_⟩
  by_contra hgt
  push Not at hgt
  have hxy0 : 0 < ‖y - x‖ := by
    by_contra h0
    have h0' : ‖y - x‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
    rw [h0', norm_eq_zero.1 h0', inner_zero_left, abs_zero, mul_zero] at hgt
    exact lt_irrefl 0 hgt
  have hm0 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have h2r : 2 * ‖y - x‖ < 1 / ((m : ℝ) + 1) := by
    have hle := hk.trans_le (min_le_right _ _)
    have h2 : 2 * (1 / (2 * ((m : ℝ) + 1))) = 1 / ((m : ℝ) + 1) := by field_simp
    linarith
  have h2ρ : 2 * ‖y - x‖ < ρ := by linarith [hk.trans_le (min_le_left _ _)]
  exact not_lt_of_ge (measure_blowUp_symmDiff_ge_of_inner_gt hx hxy0 h2r hy hgt)
    (hsub ⟨by positivity, h2ρ⟩)

/-- **Countable rectifiability in dimension `n ≥ 2`.** For any additive Haar measure, the reduced
boundary of any set is countably `(n - 1)`-rectifiable. -/
private theorem countablyRectifiable_reducedBoundary_of_two_le [μ.IsAddHaarMeasure]
    (hn : 2 ≤ finrank ℝ E) : CountablyRectifiable (finrank ℝ E - 1) (reducedBoundary μ Ω s) := by
  let D : ℕ → Set E := fun m => {x ∈ reducedBoundary μ Ω s | ∀ r ∈ Ioo 0 (1 / ((m : ℝ) + 1)),
    (1 / 4 : ℝ≥0∞) * μ (ball x r) ≤ μ (s ∩ ball x r) ∧
    (1 / 4 : ℝ≥0∞) * μ (ball x r) ≤ μ (ball x r \ s)}
  obtain ⟨S₀, hS₀c, hS₀d⟩ := TopologicalSpace.exists_countable_dense (Metric.sphere (0 : E) 1)
  obtain ⟨C₀, hC₀c, hC₀d⟩ := TopologicalSpace.exists_countable_dense E
  have : Countable S₀ := hS₀c.to_subtype
  have : Countable C₀ := hC₀c.to_subtype
  have hcov : reducedBoundary μ Ω s ⊆
      ⋃ m : ℕ, ⋃ k : ℕ, ⋃ v₀ : S₀, ⋃ c₀ : C₀,
        {x ∈ D m | dist x (c₀ : E) < 1 / (2 * ((k : ℝ) + 1)) ∧
          ‖outerNormal μ Ω s x - (v₀.1 : E)‖ < 1 / 4 ∧
          ∀ y ∈ D m, ‖y - x‖ < 1 / ((k : ℝ) + 1) →
            |⟪y - x, outerNormal μ Ω s x⟫| ≤ (1 / 2 : ℝ) * ‖y - x‖} := by
    intro x hx
    obtain ⟨m, hm⟩ := exists_nat_two_sided_ball_density hn hx
    obtain ⟨k, hk⟩ := exists_nat_cone_bound_of_mem_reducedBoundary hn (m := m) hx
    have hνS : outerNormal μ Ω s x ∈ Metric.sphere (0 : E) 1 :=
      mem_sphere_zero_iff_norm.2 (norm_outerNormal hx)
    obtain ⟨v₀, hv₀S, hv₀⟩ := Metric.mem_closure_iff.1 (hS₀d ⟨outerNormal μ Ω s x, hνS⟩)
      (1 / 4) (by norm_num)
    obtain ⟨c₀, hc₀C, hc₀d⟩ := Metric.mem_closure_iff.1 (hC₀d x)
      (1 / (2 * ((k : ℝ) + 1))) (by positivity)
    rw [Subtype.dist_eq, dist_eq_norm] at hv₀
    refine mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨⟨v₀, hv₀S⟩, mem_iUnion.2 ⟨⟨c₀, hc₀C⟩,
      ⟨hx, hm⟩, hc₀d, hv₀, fun y hy hxy => hk y hy.2 hxy⟩⟩⟩⟩
  refine (CountablyRectifiable.iUnion fun m => CountablyRectifiable.iUnion fun k =>
    CountablyRectifiable.iUnion fun v₀ : S₀ => CountablyRectifiable.iUnion fun c₀ : C₀ => ?_).mono
      hcov
  exact countablyRectifiable_cone_piece hn (D m) k (mem_sphere_zero_iff_norm.1 v₀.1.2)

/-- **Countable rectifiability of the reduced boundary.** In any finite-dimensional real inner
product space `E` of dimension `n = finrank ℝ E` and for any additive Haar measure `μ`, the
reduced boundary `∂*s` is countably `(n - 1)`-rectifiable.

No integrability, measurability, finite-perimeter, or dimension hypothesis is required. -/
theorem countablyRectifiable_reducedBoundary [μ.IsAddHaarMeasure] :
    CountablyRectifiable (finrank ℝ E - 1) (reducedBoundary μ Ω s) := by
  rcases lt_or_ge (finrank ℝ E) 2 with hlt | hn
  · interval_cases hdim : finrank ℝ E
    · rw [(dim_zero_summary hdim).1]
      exact CountablyRectifiable.empty
    · exact countablyRectifiable_zero_of_countable
        (countable_reducedBoundary_of_finrank_eq_one hdim)
  · exact countablyRectifiable_reducedBoundary_of_two_le hn

/-! ### Section 2: De Giorgi's structure theorem -/

/-- In dimension `n ≥ 2`, `μHE[n - 1] A ≤ |Dχ_s| (coe ⁻¹' A)` for every subset `A ⊆ ∂*s`. -/
private theorem euclideanHausdorffMeasure_le_variationMeasure_preimage (hn : 2 ≤ finrank ℝ E)
    {A : Set E} (hA : A ⊆ reducedBoundary volume Ω s) :
    μHE[finrank ℝ E - 1] A ≤ variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' A) := by
  set lam := variationMeasure volume Ω (s.indicator 1)
  have hmul (c : ℝ≥0∞) (hc : c < 1) :
      c * μHE[finrank ℝ E - 1] A ≤ lam (((↑) : Ω → E) ⁻¹' A) := by
    refine mul_euclideanHausdorffMeasure_le_variationMeasure_preimage (finrank ℝ E - 1)
      (hA.trans reducedBoundary_subset) fun x hx => ?_
    have hlim := tendsto_variationMeasure_closedBall_div_volume_closedBall hn (hA hx)
    refine (hlim.eventually (Ioi_mem_nhds hc)).frequently.mono fun r hr => ?_
    exact ENNReal.mul_le_of_le_div hr.le
  by_contra hlt
  push Not at hlt
  have hpos : 0 < μHE[finrank ℝ E - 1] A := bot_le.trans_lt hlt
  by_cases htop : μHE[finrank ℝ E - 1] A = ∞
  · have := hmul (1 / 2) (by norm_num)
    rw [htop, ENNReal.mul_top (by norm_num)] at this
    exact not_top_lt (this.trans_lt hlt)
  · have hdiv : lam (((↑) : Ω → E) ⁻¹' A) / μHE[finrank ℝ E - 1] A < 1 :=
      (ENNReal.div_lt_iff (Or.inl hpos.ne') (Or.inl htop)).2 (by simpa using hlt)
    obtain ⟨c, hbc, hc1⟩ := exists_between hdiv
    have hlt' := (ENNReal.div_lt_iff (Or.inl hpos.ne') (Or.inl htop)).1 hbc
    exact not_lt.2 (hmul c hc1) hlt'

/-- In dimension `n ≥ 2`, `|Dχ_s| (coe ⁻¹' A) ≤ 2 ^ n * μHE[n - 1] A` for every `A ⊆ ∂*s`. -/
private theorem variationMeasure_preimage_le_mul_euclideanHausdorffMeasure (hn : 2 ≤ finrank ℝ E)
    {A : Set E} (hA : A ⊆ reducedBoundary volume Ω s) :
    variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' A) ≤
      2 ^ (finrank ℝ E - 1) * 2 * μHE[finrank ℝ E - 1] A := by
  set lam := variationMeasure volume Ω (s.indicator 1)
  have hemb : MeasurableEmbedding ((↑) : Ω → E) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  rw [← hemb.map_apply]
  refine Measure.measure_le_mul_euclideanHausdorffMeasure (lam.map ((↑) : Ω → E))
    (finrank ℝ E - 1) two_ne_zero (by simp) fun x hx => ?_
  have hlim := tendsto_variationMeasure_closedBall_div_volume_closedBall hn (hA hx)
  filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ≥0∞) < 2)),
    self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [hemb.map_apply]
  exact (ENNReal.div_le_iff_le_mul
    (Or.inl (measure_closedBall_pos volume _ hr0).ne')
    (Or.inl measure_closedBall_lt_top.ne)).1 hr.le

/-- **Local measure identification in dimension `n ≥ 2`.** On any open `W : Opens E` with finite
perimeter measure `|Dχ_s|(coe ⁻¹' W) < ∞`, the pushforward of `|Dχ_s|` restricted to `W` equals
`μHE[n - 1]` restricted to `W ∩ ∂*s`. -/
private theorem map_variationMeasure_restrict_eq_of_two_le (hn : 2 ≤ finrank ℝ E) {W : Opens E}
    (hWfin : variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' (W : Set E)) < ∞) :
    ((variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)).restrict (W : Set E) =
      μHE[finrank ℝ E - 1].restrict ((W : Set E) ∩ reducedBoundary volume Ω s) := by
  set k := finrank ℝ E - 1
  set lam := variationMeasure volume Ω (s.indicator 1)
  set ν₁ : Measure E := (lam.map ((↑) : Ω → E)).restrict (W : Set E)
  set ν₂ : Measure E := μHE[k].restrict ((W : Set E) ∩ reducedBoundary volume Ω s)
  have hemb : MeasurableEmbedding ((↑) : Ω → E) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  have hWrbm : MeasurableSet ((W : Set E) ∩ reducedBoundary volume Ω s) :=
    W.isOpen.measurableSet.inter measurableSet_reducedBoundary
  have hfin₁ : IsFiniteMeasure ν₁ := ⟨by
    rwa [Measure.restrict_apply_univ, hemb.map_apply]⟩
  have hfin₂ : IsFiniteMeasure ν₂ := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (euclideanHausdorffMeasure_le_variationMeasure_preimage hn inter_subset_right).trans_lt
      ((measure_mono (preimage_mono inter_subset_left)).trans_lt hWfin)⟩
  have hac : ν₁ ≪ ν₂ := Measure.AbsolutelyContinuous.mk fun A hAm hA₂ => by
    rw [Measure.restrict_apply hAm] at hA₂ ⊢
    rw [hemb.map_apply]
    have hsplit : ((↑) : Ω → E) ⁻¹' (A ∩ (W : Set E)) ⊆
        ((↑) : Ω → E) ⁻¹' (A ∩ ((W : Set E) ∩ reducedBoundary volume Ω s)) ∪
          {y : Ω | (y : E) ∉ reducedBoundary volume Ω s} := by
      intro y ⟨hyA, hyW⟩
      by_cases hyrb : (y : E) ∈ reducedBoundary volume Ω s
      · exact Or.inl ⟨hyA, hyW, hyrb⟩
      · exact Or.inr hyrb
    have hnull : lam {y : Ω | (y : E) ∉ reducedBoundary volume Ω s} = 0 :=
      ae_iff.1 ae_mem_reducedBoundary
    have h1 := (measure_mono (μ := lam) hsplit).trans (measure_union_le _ _)
    rw [hnull, add_zero] at h1
    have h2 := variationMeasure_preimage_le_mul_euclideanHausdorffMeasure (Ω := Ω) (s := s)
      (A := A ∩ ((W : Set E) ∩ reducedBoundary volume Ω s)) hn
      (inter_subset_right.trans inter_subset_right)
    rw [hA₂, mul_zero] at h2
    exact le_antisymm (h1.trans h2) bot_le
  have hrn : ν₁.rnDeriv ν₂ =ᵐ[ν₂] 1 := by
    have hrect : CountablyRectifiable k ((W : Set E) ∩ reducedBoundary volume Ω s) :=
      (countablyRectifiable_reducedBoundary_of_two_le hn).mono inter_subset_right
    have hdens₂ := hrect.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div
      hWrbm.nullMeasurableSet
    filter_upwards [ae_restrict_mem hWrbm, Besicovitch.ae_tendsto_rnDeriv ν₁ ν₂,
      ae_restrict_of_ae hdens₂] with x hx hbes hd2
    have hd1 : Tendsto (fun r => ν₁ (closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
      refine (tendsto_variationMeasure_closedBall_div_volume_closedBall hn hx.2).congr' ?_
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (eventually_closedBall_subset (W.isOpen.mem_nhds hx.1))] with r hr
      rw [Measure.restrict_apply isClosed_closedBall.measurableSet, inter_eq_left.2 hr,
        hemb.map_apply]
    have hd2' : Tendsto (fun r => ν₂ (closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
      refine (hd2 hx).congr fun r => ?_
      rw [Measure.restrict_apply isClosed_closedBall.measurableSet, inter_comm]
    have hquot : Tendsto (fun r => ν₁ (closedBall x r) / ν₂ (closedBall x r)) (𝓝[>] 0) (𝓝 1) := by
      have hdiv := ENNReal.Tendsto.div hd1 (Or.inl one_ne_zero) hd2' (Or.inl ENNReal.one_ne_top)
      rw [ENNReal.div_self one_ne_zero ENNReal.one_ne_top] at hdiv
      refine hdiv.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
      set v := volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)
      have hv0 : v ≠ 0 := (measure_closedBall_pos volume _ hr).ne'
      have hvtop : v ≠ ∞ := measure_closedBall_lt_top.ne
      dsimp only
      simp only [ENNReal.div_eq_inv_mul]
      rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hvtop))
          (Or.inl (ENNReal.inv_ne_top.2 hv0)),
        inv_inv, mul_comm v, mul_assoc, ← mul_assoc v v⁻¹, ENNReal.mul_inv_cancel hv0 hvtop,
        one_mul]
    exact tendsto_nhds_unique hbes hquot
  rw [← Measure.withDensity_rnDeriv_eq ν₁ ν₂ hac, withDensity_congr_ae hrn, withDensity_one]

/-- **De Giorgi's structure theorem (pushforward form).** In any finite-dimensional real inner
product space `E` of dimension `n = finrank ℝ E`, the pushforward of the perimeter measure
`|Dχ_s|` from an open set `Ω` to `E` equals the `(n - 1)`-dimensional Euclidean Hausdorff measure
`μHE[n - 1]` restricted to the reduced boundary `∂*s`.

No integrability, measurability, finite-perimeter, or dimension hypothesis is required: when `s`
does not have locally finite perimeter in `Ω`, both sides vanish. -/
theorem map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary :
    (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E) =
      μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s) := by
  by_cases h : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω ∧
      ∀ K, IsCompact K → K ⊆ Ω →
        ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞
  swap
  · rw [variationMeasure_eq_zero_of_not h, reducedBoundary_eq_empty_of_not h, Measure.map_zero,
      Measure.restrict_empty]
  rcases lt_or_ge (finrank ℝ E) 2 with hlt | hn
  · interval_cases hdim : finrank ℝ E
    · obtain ⟨hred, -, hvar⟩ := dim_zero_summary (μ := volume) (Ω := Ω) (s := s) hdim
      rw [hvar, hred, Measure.map_zero, Measure.restrict_empty]
    · rw [map_variationMeasure_eq_count_restrict_reducedBoundary_of_finrank_eq_one hdim,
        Measure.euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_eq_count]
  · have := Ω.isOpen.locallyCompactSpace
    let K : CompactExhaustion Ω := CompactExhaustion.choice Ω
    let W : ℕ → Opens E := fun n =>
      ⟨((↑) : Ω → E) '' interior (K n),
        Ω.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior⟩
    have hWle (n : ℕ) : W n ≤ Ω := by rintro _ ⟨y, -, rfl⟩; exact y.2
    have hWcov : ⋃ n, (W n : Set E) = (Ω : Set E) := by
      refine Subset.antisymm (iUnion_subset fun n => hWle n) fun y hy => ?_
      obtain ⟨n, hn'⟩ := K.exists_mem ⟨y, hy⟩
      exact mem_iUnion.2 ⟨n + 1, ⟨y, hy⟩, K.subset_interior_succ n hn', rfl⟩
    have hres₁ : ((variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)).restrict
        (Ω : Set E) = (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E) := by
      ext A hA
      rw [Measure.restrict_apply hA,
        Measure.map_apply continuous_subtype_val.measurable (hA.inter Ω.isOpen.measurableSet),
        Measure.map_apply continuous_subtype_val.measurable hA, preimage_inter]
      congr 1; ext y; exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
    have hres₂ : (μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s)).restrict (Ω : Set E) =
        μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s) := by
      rw [Measure.restrict_restrict Ω.isOpen.measurableSet, inter_eq_right.2 reducedBoundary_subset]
    rw [← hres₁, ← hres₂, ← hWcov]
    refine Measure.restrict_iUnion_congr.2 fun n => ?_
    have hWfin : variationMeasure volume Ω (s.indicator 1)
        (((↑) : Ω → E) ⁻¹' (W n : Set E)) < ∞ := by
      have hpre : ((↑) : Ω → E) ⁻¹' (W n : Set E) = interior (K n) :=
        Subtype.val_injective.preimage_image _
      rw [hpre]
      exact (measure_mono interior_subset).trans_lt (K.isCompact n).measure_lt_top
    rw [map_variationMeasure_restrict_eq_of_two_le hn hWfin,
      Measure.restrict_restrict (W n).isOpen.measurableSet]

/-- **De Giorgi's structure theorem (ambient set form).** For every set `A : Set E` (not assumed
measurable), the perimeter measure of `coe ⁻¹' A` in `Ω` equals `μHE[n - 1] (A ∩ ∂*s)`. -/
theorem variationMeasure_preimage_eq_euclideanHausdorffMeasure_inter_reducedBoundary (A : Set E) :
    variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' A) =
      μHE[finrank ℝ E - 1] (A ∩ reducedBoundary volume Ω s) := by
  have hemb : MeasurableEmbedding ((↑) : Ω → E) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  rw [← hemb.map_apply,
    map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary,
    Measure.restrict_apply' measurableSet_reducedBoundary]

/-- **De Giorgi's structure theorem (subset form).** For every set `S : Set Ω` (not assumed
measurable), the perimeter measure of `S` equals `μHE[n - 1] (coe '' S ∩ ∂*s)`. -/
theorem variationMeasure_apply_eq_euclideanHausdorffMeasure_image_inter_reducedBoundary
    (S : Set Ω) :
    variationMeasure volume Ω (s.indicator 1) S =
      μHE[finrank ℝ E - 1] (((↑) : Ω → E) '' S ∩ reducedBoundary volume Ω s) := by
  conv_lhs => rw [← Subtype.val_injective.preimage_image S]
  exact variationMeasure_preimage_eq_euclideanHausdorffMeasure_inter_reducedBoundary _

/-- **De Giorgi's structure theorem (measure equality on `Ω`).** On the subspace `Ω`, the
perimeter measure `|Dχ_s|` equals the `(n - 1)`-dimensional Euclidean Hausdorff measure `μHE[n - 1]`
restricted to `coe ⁻¹' ∂*s`. -/
theorem variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary :
    variationMeasure volume Ω (s.indicator 1) =
      (μHE[finrank ℝ E - 1] : Measure Ω).restrict
        (((↑) : Ω → E) ⁻¹' reducedBoundary volume Ω s) := by
  ext S hS
  rw [variationMeasure_apply_eq_euclideanHausdorffMeasure_image_inter_reducedBoundary,
    Measure.restrict_apply hS]
  have himg : ((↑) : Ω → E) ⁻¹' (((↑) : Ω → E) '' S ∩ reducedBoundary volume Ω s) =
      S ∩ ((↑) : Ω → E) ⁻¹' reducedBoundary volume Ω s := by
    rw [preimage_inter, Subtype.val_injective.preimage_image]
  have hsub : ((↑) : Ω → E) '' S ∩ reducedBoundary volume Ω s ⊆ range ((↑) : Ω → E) :=
    inter_subset_right.trans (by rw [Subtype.range_coe]; exact reducedBoundary_subset)
  rw [← himg, isometry_subtype_coe.euclideanHausdorffMeasure_preimage, inter_eq_left.2 hsub]

/-- **Perimeter equals Hausdorff measure of the reduced boundary.** For a set `s` of locally finite
perimeter in `Ω` and every open subset `U ⊆ Ω`, `P(s; U) = μHE[n - 1] (U ∩ ∂*s)`. -/
theorem perimeter_eq_euclideanHausdorffMeasure_inter_reducedBoundary {U : Opens E}
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞)
    (hU : U ≤ Ω) :
    perimeter volume U s = μHE[finrank ℝ E - 1] ((U : Set E) ∩ reducedBoundary volume Ω s) := by
  rw [perimeter_def, ← variationMeasure_preimage_coe hu hfin hU,
    variationMeasure_preimage_eq_euclideanHausdorffMeasure_inter_reducedBoundary]

/-- For a set `s` of locally finite perimeter in `Ω`, `P(s; Ω) = μHE[n - 1] (∂*s)`. -/
theorem perimeter_eq_euclideanHausdorffMeasure_reducedBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞) :
    perimeter volume Ω s = μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s) := by
  rw [perimeter_eq_euclideanHausdorffMeasure_inter_reducedBoundary hu hfin le_rfl,
    inter_eq_right.2 reducedBoundary_subset]

/-- **De Giorgi's Gauss–Green formula (indicator form).** For a set `s` of locally finite perimeter
in `Ω` and any `C¹` vector field `φ` with compact support in `Ω`,
`∫ (div φ) χ_s = ∫_{∂*s} ⟪φ, ν_s⟫ dμHE[n - 1]`. -/
theorem integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x =
      ∫ x in reducedBoundary volume Ω s, ⟪φ x, outerNormal volume Ω s x⟫ ∂μHE[finrank ℝ E - 1] := by
  have hemb : MeasurableEmbedding ((↑) : Ω → E) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  rw [integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal hu hfin hφ hc hs,
    ← hemb.integral_map (fun x => ⟪φ x, outerNormal volume Ω s x⟫),
    map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary]

/-- **De Giorgi's Gauss–Green formula.** For a set `s` of locally finite perimeter in `Ω` and any
`C¹` vector field `φ` with compact support in `Ω`,
`∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dμHE[n - 1]`. -/
theorem setIntegral_trace_fderiv_eq_setIntegral_inner_outerNormal
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x in s, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) =
      ∫ x in reducedBoundary volume Ω s, ⟪φ x, outerNormal volume Ω s x⟫ ∂μHE[finrank ℝ E - 1] := by
  rw [← integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal hu hfin hφ hc hs]
  have hsΩ : NullMeasurableSet (s ∩ Ω) volume :=
    (nullMeasurableSet_restrict Ω.isOpen.measurableSet.nullMeasurableSet).1
      ((aemeasurable_indicator_const_iff (1 : ℝ)).1 hu.aestronglyMeasurable.aemeasurable)
  have hsupp (x : E) (hx : x ∉ (Ω : Set E)) :
      LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) = 0 := by
    have h0 : fderiv ℝ φ x = 0 := by
      have hev : φ =ᶠ[𝓝 x] 0 := Filter.eventually_of_mem
        ((isClosed_tsupport φ).isOpen_compl.mem_nhds fun h => hx (hs h))
        fun y hy => image_eq_zero_of_notMem_tsupport hy
      rw [hev.fderiv_eq, fderiv_zero, Pi.zero_apply]
    simp [h0]
  calc
    ∫ x in s, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E)
      = ∫ x in (Ω : Set E), LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) ∂(volume.restrict s) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
    _ = ∫ x in s ∩ Ω, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) := by
        rw [Measure.restrict_restrict Ω.isOpen.measurableSet, inter_comm]
    _ = ∫ x, (s ∩ Ω).indicator (fun y => LinearMap.trace ℝ E (fderiv ℝ φ y : E →ₗ[ℝ] E)) x :=
        (integral_indicator₀ hsΩ).symm
    _ = ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x := by
        congr 1; ext x
        by_cases hxΩ : x ∈ (Ω : Set E) <;> by_cases hxs : x ∈ s <;> simp [hxΩ, hxs, hsupp]

/-! ### Section 3: Equivalence of reduced and essential boundaries -/

/-- For any additive Haar measure on a nontrivial finite-dimensional space, the ball density ratio
`r ↦ μ.real (s ∩ closedBall x r) / μ.real (closedBall x r)` is continuous on `(0, ∞)`. -/
private theorem continuousOn_measureReal_inter_closedBall_div [μ.IsAddHaarMeasure]
    (hn : 1 ≤ finrank ℝ E) (s : Set E) (x : E) :
    ContinuousOn (fun r => μ.real (s ∩ closedBall x r) / μ.real (closedBall x r)) (Ioi 0) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hden : ContinuousOn (fun r : ℝ => μ.real (closedBall x r)) (Ioi 0) := by
    have hcont : Continuous (fun r : ℝ => r ^ finrank ℝ E * μ.real (ball (0 : E) 1)) := by fun_prop
    refine hcont.continuousOn.congr fun r hr => ?_
    rw [measureReal_def, Measure.addHaar_closedBall μ x (le_of_lt hr), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hr) _), measureReal_def]
  have hnum : ContinuousOn (fun r : ℝ => μ.real (s ∩ closedBall x r)) (Ioi 0) := by
    intro r₀ (hr₀ : 0 < r₀)
    refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
    have hcont : ContinuousAt (fun r : ℝ => |r ^ finrank ℝ E - r₀ ^ finrank ℝ E| *
        μ.real (ball (0 : E) 1)) r₀ := by fun_prop
    obtain ⟨δ, hδ, hsub⟩ := Metric.continuousAt_iff.1 hcont ε hε
    refine ⟨min δ (r₀ / 2), lt_min hδ (half_pos hr₀), fun r (hr : 0 < r) hdr => ?_⟩
    set a := min r r₀
    set b := max r r₀
    have ha : 0 < a := lt_min hr hr₀
    have hab : a ≤ b := min_le_max
    have hle : μ.real (s ∩ closedBall x a) ≤ μ.real (s ∩ closedBall x b) :=
      measureReal_mono (inter_subset_inter_right s (closedBall_subset_closedBall hab))
        (measure_ne_top_of_subset inter_subset_right measure_closedBall_lt_top.ne)
    have hdiff : μ.real (s ∩ closedBall x b) - μ.real (s ∩ closedBall x a) ≤
        (b ^ finrank ℝ E - a ^ finrank ℝ E) * μ.real (ball (0 : E) 1) := by
      have hcov : s ∩ closedBall x b ⊆ (s ∩ closedBall x a) ∪ (closedBall x b \ ball x a) := by
        intro y ⟨hys, hyb⟩
        by_cases hya : y ∈ ball x a
        · exact Or.inl ⟨hys, ball_subset_closedBall hya⟩
        · exact Or.inr ⟨hyb, hya⟩
      have hsubadd := (measureReal_mono (μ := μ) hcov (measure_union_ne_top
        (measure_ne_top_of_subset inter_subset_right measure_closedBall_lt_top.ne)
        (measure_ne_top_of_subset sdiff_subset measure_closedBall_lt_top.ne))).trans
        (measureReal_union_le _ _)
      rw [μ.addHaar_real_closedBall_sdiff_ball x ha hab] at hsubadd
      linarith
    have habs : |μ.real (s ∩ closedBall x r) - μ.real (s ∩ closedBall x r₀)| ≤
        |r ^ finrank ℝ E - r₀ ^ finrank ℝ E| * μ.real (ball (0 : E) 1) := by
      rcases le_total r r₀ with hrr | hrr
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by simpa [a, b, hrr] using hle)),
          abs_sub_comm (r ^ finrank ℝ E),
          abs_of_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hr.le hrr _))]
        simpa [a, b, hrr] using hdiff
      · rw [abs_of_nonneg (sub_nonneg.2 (by simpa [a, b, hrr] using hle)),
          abs_of_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hr₀.le hrr _))]
        simpa [a, b, hrr] using hdiff
    have hlt : |r ^ finrank ℝ E - r₀ ^ finrank ℝ E| * μ.real (ball (0 : E) 1) < ε := by
      have h1 := hsub (hdr.trans_le (min_le_left _ _))
      simpa [Real.dist_eq, abs_of_nonneg measureReal_nonneg] using h1
    rw [Real.dist_eq]
    exact habs.trans_lt hlt
  refine hnum.div hden fun r (hr : 0 < r) => ?_
  exact (ENNReal.toReal_pos (measure_closedBall_pos μ x hr).ne' measure_closedBall_lt_top.ne).ne'

/-- At any point `x ∈ essentialBoundary μ s` (in dimension `n ≥ 1`), the intermediate value theorem
gives a fixed margin `ε_m > 0` such that the closed-ball density stays in `[ε_m, 1 - ε_m]` along
arbitrarily small radii. -/
private theorem exists_nat_frequently_density_mem_Icc [μ.IsAddHaarMeasure] (hn : 1 ≤ finrank ℝ E)
    {x : E} (hx : x ∈ essentialBoundary μ s) :
    ∃ m : ℕ, ∃ᶠ r in 𝓝[>] 0,
      1 / (2 * ((m : ℝ) + 2)) ≤ μ.real (s ∩ closedBall x r) / μ.real (closedBall x r) ∧
      μ.real (s ∩ closedBall x r) / μ.real (closedBall x r) ≤ 1 - 1 / (2 * ((m : ℝ) + 2)) := by
  rw [mem_essentialBoundary] at hx
  set f : ℝ → ℝ := fun r => μ.real (s ∩ closedBall x r) / μ.real (closedBall x r)
  have hf_eq {r : ℝ} (_ : 0 < r) :
      f r = (μ (s ∩ closedBall x r) / μ (closedBall x r)).toReal := by
    rw [ENNReal.toReal_div]; rfl
  have hf0 (r : ℝ) : 0 ≤ f r := div_nonneg measureReal_nonneg measureReal_nonneg
  have hf1 {r : ℝ} (_ : 0 < r) : f r ≤ 1 :=
    div_le_one_of_le₀ (measureReal_mono inter_subset_right measure_closedBall_lt_top.ne)
      measureReal_nonneg
  have hnot0 : ¬Tendsto f (𝓝[>] 0) (𝓝 0) := fun h => hx.2 <| by
    rw [mem_essentialExterior, hasDensityAt_iff]
    have h' := ENNReal.tendsto_ofReal h
    rw [ENNReal.ofReal_zero] at h'
    refine h'.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
    rw [hf_eq hr, ENNReal.ofReal_toReal (ENNReal.div_ne_top
      (measure_ne_top_of_subset inter_subset_right measure_closedBall_lt_top.ne)
      (measure_closedBall_pos μ x hr).ne')]
  have hnot1 : ¬Tendsto f (𝓝[>] 0) (𝓝 1) := fun h => hx.1 <| by
    rw [mem_essentialInterior, hasDensityAt_iff]
    have h' := ENNReal.tendsto_ofReal h
    rw [ENNReal.ofReal_one] at h'
    refine h'.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
    rw [hf_eq hr, ENNReal.ofReal_toReal (ENNReal.div_ne_top
      (measure_ne_top_of_subset inter_subset_right measure_closedBall_lt_top.ne)
      (measure_closedBall_pos μ x hr).ne')]
  obtain ⟨α, hα, hαf⟩ : ∃ α > 0, ∃ᶠ r in 𝓝[>] 0, α ≤ f r := by
    rw [Metric.tendsto_nhds] at hnot0
    push Not at hnot0
    obtain ⟨α, hα, hfreq⟩ := hnot0
    exact ⟨α, hα, hfreq.mono fun r hr => by
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hf0 r)] at hr⟩
  obtain ⟨β, hβ, hβf⟩ : ∃ β > 0, ∃ᶠ r in 𝓝[>] 0, f r ≤ 1 - β := by
    rw [Metric.tendsto_nhds] at hnot1
    push Not at hnot1
    obtain ⟨β, hβ, hfreq⟩ := hnot1
    refine ⟨β, hβ, (hfreq.and_eventually self_mem_nhdsWithin).mono fun r ⟨hr, (hr0 : 0 < r)⟩ => ?_⟩
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hf1 hr0))] at hr
    linarith
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (lt_min hα hβ)
  set ε : ℝ := 1 / (2 * ((m : ℝ) + 2))
  have hεlt : ε < min α β := by
    calc ε < 1 / ((m : ℝ) + 1) := by apply one_div_lt_one_div_of_lt (by positivity); linarith
      _ < min α β := hm
  have hε4 : ε ≤ 1 / 4 := by
    rw [one_div_le_one_div (by positivity) (by norm_num)]; linarith
  refine ⟨m, Filter.frequently_iff.2 fun {U} hU => ?_⟩
  obtain ⟨δ, hδ, hδU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  obtain ⟨r₁, hfr₁, hr₁⟩ := (hαf.and_eventually (Ioo_mem_nhdsGT hδ)).exists
  obtain ⟨r₂, hfr₂, hr₂⟩ := (hβf.and_eventually (Ioo_mem_nhdsGT hδ)).exists
  by_cases h1 : f r₁ ≤ 1 - ε
  · exact ⟨r₁, hδU hr₁, (hεlt.trans_le (min_le_left _ _)).le.trans hfr₁, h1⟩
  · push Not at h1
    have h2 : f r₂ ≤ 1 - ε := hfr₂.trans (by linarith [hεlt.trans_le (min_le_right _ _)])
    have huIcc : uIcc r₁ r₂ ⊆ Ioo 0 δ := fun r hr =>
      ⟨(lt_min hr₁.1 hr₂.1).trans_le hr.1, hr.2.trans_lt (max_lt hr₁.2 hr₂.2)⟩
    have hmem : 1 - ε ∈ uIcc (f r₁) (f r₂) := by
      rw [uIcc_of_ge (h2.trans h1.le)]
      exact ⟨h2, h1.le⟩
    obtain ⟨r, hr, hfr⟩ := intermediate_value_uIcc
      ((continuousOn_measureReal_inter_closedBall_div (μ := μ) hn s x).mono
        (huIcc.trans fun _ h => h.1)) hmem
    exact ⟨r, hδU (huIcc hr), by linarith, by linarith⟩

/-- Single-scale relative isoperimetric lower bound: when the closed-ball density of `s` at scale
`r` lies in `[ε, 1 - ε]`, the perimeter measure of `closedBall x r` is bounded below by a positive
multiple of `ω_{n - 1} r ^ (n - 1)`. -/
private theorem isoperimetric_lower_density_of_density_mem_Icc [μ.IsAddHaarMeasure]
    (hn : 2 ≤ finrank ℝ E) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞)
    {x : E} {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hcbΩ : closedBall x r ⊆ Ω)
    (hlo : ε ≤ μ.real (s ∩ closedBall x r) / μ.real (closedBall x r))
    (hhi : μ.real (s ∩ closedBall x r) / μ.real (closedBall x r) ≤ 1 - ε) :
    let n := finrank ℝ E
    let Ciso : ℝ≥0∞ := ENNReal.ofReal (2 ^ (n + 1) / μ.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹)
    let ωk : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1)
    ((ENNReal.ofReal ε * μ (ball (0 : E) 1)) ^ (1 - (n : ℝ)⁻¹) / (Ciso * ωk)) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) r) ≤
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
  intro n Ciso ωk
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hballΩ : ball x r ⊆ Ω := ball_subset_closedBall.trans hcbΩ
  have hsΩ : NullMeasurableSet s (μ.restrict Ω) :=
    (aemeasurable_indicator_const_iff (1 : ℝ)).1 hu.aestronglyMeasurable.aemeasurable
  have hs_ball : NullMeasurableSet s (μ.restrict (ball x r)) :=
    hsΩ.mono_ac (Measure.restrict_mono hballΩ le_rfl).absolutelyContinuous
  have hcb_eq : μ (closedBall x r) = μ (ball x r) := μ.addHaar_closedBall_eq_addHaar_ball x r
  have hs_eq : μ (s ∩ closedBall x r) = μ (s ∩ ball x r) :=
    measure_congr (EventuallyEqSet.inter .rfl (μ.addHaar_closedBall_ae_eq_ball x r))
  have hmin_ge : ENNReal.ofReal ε * μ (ball x r) ≤
      min (μ (s ∩ ball x r)) (μ (ball x r \ s)) := by
    have hBpos : 0 < μ.real (closedBall x r) :=
      ENNReal.toReal_pos (measure_closedBall_pos μ x hr).ne' measure_closedBall_lt_top.ne
    have h1r : ε * μ.real (ball x r) ≤ μ.real (s ∩ ball x r) := by
      have := (le_div_iff₀ hBpos).1 hlo
      simpa [measureReal_def, hcb_eq, hs_eq] using this
    have h2r : ε * μ.real (ball x r) ≤ μ.real (ball x r \ s) := by
      have hadd : μ (s ∩ ball x r) + μ (ball x r \ s) = μ (ball x r) := by
        have := measure_add_measure_compl₀ (μ := μ.restrict (ball x r)) hs_ball
        rw [Measure.restrict_apply_univ, Measure.restrict_apply' measurableSet_ball,
          Measure.restrict_apply' measurableSet_ball, inter_comm sᶜ, ← Set.sdiff_eq] at this
        exact this
      have hadd_r : μ.real (s ∩ ball x r) + μ.real (ball x r \ s) = μ.real (ball x r) := by
        rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_add
          (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)
          (measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne), hadd]
      have hhi' : μ.real (s ∩ ball x r) ≤ (1 - ε) * μ.real (ball x r) := by
        have := (div_le_iff₀ hBpos).1 hhi
        simpa [measureReal_def, hcb_eq, hs_eq] using this
      linarith
    refine le_min ?_ ?_
    · rw [← ofReal_measureReal measure_ball_lt_top.ne,
        ← ofReal_measureReal (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne),
        ← ENNReal.ofReal_mul hε.le]
      exact ENNReal.ofReal_le_ofReal h1r
    · rw [← ofReal_measureReal measure_ball_lt_top.ne,
        ← ofReal_measureReal (measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne),
        ← ENNReal.ofReal_mul hε.le]
      exact ENNReal.ofReal_le_ofReal h2r
  have hiso := min_measure_inter_measure_sdiff_rpow_le_perimeter (μ := μ)
    (Ω := ⟨ball x r, isOpen_ball⟩) hn hs_ball subset_rfl
  have hper_le : perimeter μ ⟨ball x r, isOpen_ball⟩ s ≤
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
    rw [perimeter_def, ← variationMeasure_preimage_coe hu hfin hballΩ]
    exact measure_mono (preimage_mono ball_subset_closedBall)
  have hexp : 0 < 1 - (n : ℝ)⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ (by exact_mod_cast hn))
  have hrpow : (ENNReal.ofReal r ^ n) ^ (1 - (n : ℝ)⁻¹) = ENNReal.ofReal r ^ (n - 1) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast]
    congr 1
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [mul_sub, mul_one, mul_inv_cancel₀ hn0, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hvol_ball : μ (ball x r) = ENNReal.ofReal r ^ n * μ (ball (0 : E) 1) := by
    rw [Measure.addHaar_ball_of_pos μ x hr, ENNReal.ofReal_pow hr.le]
  have hvol_k : volume (closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) r) =
      ENNReal.ofReal r ^ (n - 1) * ωk := by
    rw [Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr.le]
  set c : ℝ≥0∞ := (ENNReal.ofReal ε * μ (ball (0 : E) 1)) ^ (1 - (n : ℝ)⁻¹) / (Ciso * ωk)
  have hlhs : c * (Ciso * ωk) * ENNReal.ofReal r ^ (n - 1) ≤
      (ENNReal.ofReal ε * μ (ball x r)) ^ (1 - (n : ℝ)⁻¹) := by
    have hfac : ENNReal.ofReal ε * μ (ball x r) =
        (ENNReal.ofReal ε * μ (ball (0 : E) 1)) * ENNReal.ofReal r ^ n := by
      rw [hvol_ball]; ring
    rw [hfac, ENNReal.mul_rpow_of_nonneg _ _ hexp.le, hrpow]
    exact mul_le_mul_left (ENNReal.mul_le_of_le_div le_rfl) _
  have hstep : c * volume (closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) r) * Ciso ≤
      Ciso * variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
    calc c * volume (closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) r) * Ciso
        = c * (Ciso * ωk) * ENNReal.ofReal r ^ (n - 1) := by rw [hvol_k]; ring
      _ ≤ (ENNReal.ofReal ε * μ (ball x r)) ^ (1 - (n : ℝ)⁻¹) := hlhs
      _ ≤ min (μ (s ∩ ball x r)) (μ (ball x r \ s)) ^ (1 - (n : ℝ)⁻¹) :=
            ENNReal.rpow_le_rpow hmin_ge hexp.le
      _ ≤ Ciso * perimeter μ ⟨ball x r, isOpen_ball⟩ s := hiso
      _ ≤ Ciso * variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) :=
            mul_le_mul_right hper_le _
  have hCiso_pos : Ciso ≠ 0 := (ENNReal.ofReal_pos.2 (div_pos (by positivity)
    (Real.rpow_pos_of_pos (ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne'
      measure_ball_lt_top.ne) _))).ne'
  rw [mul_comm _ Ciso] at hstep
  exact (ENNReal.mul_le_mul_iff_right hCiso_pos ENNReal.ofReal_ne_top).1 hstep

/-- In dimension `n ≥ 2`, `(Ω ∩ ∂ᵉs) \ ∂*s` has `μHE[n - 1]`-measure zero. -/
private theorem euclideanHausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_of_two_le
    [μ.IsAddHaarMeasure] (hn : 2 ≤ finrank ℝ E)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞) :
    μHE[finrank ℝ E - 1] (((Ω : Set E) ∩ essentialBoundary μ s) \ reducedBoundary μ Ω s) = 0 := by
  set n := finrank ℝ E
  set k := n - 1
  set A : Set E := ((Ω : Set E) ∩ essentialBoundary μ s) \ reducedBoundary μ Ω s
  set A_m : ℕ → Set E := fun m => {x ∈ A | ∃ᶠ r in 𝓝[>] 0,
    1 / (2 * ((m : ℝ) + 2)) ≤ μ.real (s ∩ closedBall x r) / μ.real (closedBall x r) ∧
    μ.real (s ∩ closedBall x r) / μ.real (closedBall x r) ≤ 1 - 1 / (2 * ((m : ℝ) + 2))}
  have hcov : A ⊆ ⋃ m : ℕ, A_m m := fun x hx => by
    obtain ⟨m, hm⟩ := exists_nat_frequently_density_mem_Icc (μ := μ) (by omega) hx.1.2
    exact mem_iUnion.2 ⟨m, hx, hm⟩
  have hnull_m (m : ℕ) : μHE[k] (A_m m) = 0 := by
    set ε : ℝ := 1 / (2 * ((m : ℝ) + 2))
    have hε : 0 < ε := by positivity
    set Ciso : ℝ≥0∞ := ENNReal.ofReal (2 ^ (n + 1) / μ.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹)
    set ωk : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1)
    set c : ℝ≥0∞ := (ENNReal.ofReal ε * μ (ball (0 : E) 1)) ^ (1 - (n : ℝ)⁻¹) / (Ciso * ωk)
    have hc0 : c ≠ 0 := ENNReal.div_ne_zero.2
      ⟨(ENNReal.rpow_pos (ENNReal.mul_pos (ENNReal.ofReal_pos.2 hε).ne'
        (measure_ball_pos μ 0 one_pos).ne')
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)).ne',
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne⟩
    have hle : c * μHE[k] (A_m m) ≤
        variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' A_m m) := by
      refine mul_euclideanHausdorffMeasure_le_variationMeasure_preimage k
        (fun x hx => hx.1.1.1) fun x hx => ?_
      refine (hx.2.and_eventually ((eventually_nhdsWithin_of_eventually_nhds
        (eventually_closedBall_subset (Ω.isOpen.mem_nhds hx.1.1.1))).and
        self_mem_nhdsWithin)).mono fun r ⟨⟨hlo, hhi⟩, hcbΩ, (hr : 0 < r)⟩ => ?_
      exact isoperimetric_lower_density_of_density_mem_Icc hn hu hfin hr hε hcbΩ hlo hhi
    have hzero : variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' A_m m) = 0 :=
      measure_mono_null (fun y hy => hy.1.2) (ae_iff.1 ae_mem_reducedBoundary)
    rw [hzero, nonpos_iff_eq_zero, mul_eq_zero] at hle
    exact hle.resolve_left hc0
  exact measure_mono_null hcov (measure_iUnion_null hnull_m)

/-- **The reduced boundary lies in `Ω ∩ ∂ᵉs`.** Holds in every dimension `n ≥ 0` and for every
additive Haar measure `μ`, without finiteness or measurability hypotheses. -/
theorem reducedBoundary_subset_inter_essentialBoundary [μ.IsAddHaarMeasure] :
    reducedBoundary μ Ω s ⊆ (Ω : Set E) ∩ essentialBoundary μ s := by
  rcases lt_or_ge (finrank ℝ E) 2 with hlt | hn
  · interval_cases hdim : finrank ℝ E
    · rw [(dim_zero_summary hdim).1]
      exact empty_subset _
    · by_cases h : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ ∧
          ∀ K, IsCompact K → K ⊆ Ω →
            ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞
      · exact (reducedBoundary_eq_inter_essentialBoundary_of_finrank_eq_one hdim h.1 h.2).subset
      · rw [reducedBoundary_eq_empty_of_not h]
        exact empty_subset _
  · exact subset_inter reducedBoundary_subset (reducedBoundary_subset_essentialBoundary hn)

/-- **Federer's essential-boundary equivalence (null difference).** For a set `s` of locally finite
perimeter in `Ω` and any additive Haar measure `μ`, the difference `(Ω ∩ ∂ᵉs) \ ∂*s` has
`(n - 1)`-dimensional Euclidean Hausdorff measure zero, in every dimension `n ≥ 0`. -/
theorem euclideanHausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary [μ.IsAddHaarMeasure]
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞) :
    μHE[finrank ℝ E - 1] (((Ω : Set E) ∩ essentialBoundary μ s) \ reducedBoundary μ Ω s) = 0 := by
  rcases lt_or_ge (finrank ℝ E) 2 with hlt | hn
  · interval_cases hdim : finrank ℝ E
    · rw [(dim_zero_summary (μ := μ) (Ω := Ω) (s := s) hdim).2.1, inter_empty, empty_sdiff,
        measure_empty]
    · rw [reducedBoundary_eq_inter_essentialBoundary_of_finrank_eq_one hdim hu hfin,
        Set.sdiff_self, measure_empty]
  · exact euclideanHausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_of_two_le
      hn hu hfin

/-- **Equivalence of reduced and essential boundaries.** For a set `s` of locally finite perimeter
in `Ω` and any additive Haar measure `μ`, `∂*s` and `Ω ∩ ∂ᵉs` agree up to a `μHE[n - 1]`-null
set, in every dimension `n ≥ 0`. -/
theorem reducedBoundary_ae_eq_inter_essentialBoundary [μ.IsAddHaarMeasure]
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞) :
    reducedBoundary μ Ω s =ᵐ[μHE[finrank ℝ E - 1]] ((Ω : Set E) ∩ essentialBoundary μ s) := by
  rw [ae_eq_set]
  refine ⟨by rw [sdiff_eq_empty.2 reducedBoundary_subset_inter_essentialBoundary, measure_empty],
    euclideanHausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary hu hfin⟩

/-- For a set `s` of locally finite perimeter in `Ω` and any additive Haar measure `μ`, the part
`Ω ∩ ∂ᵉs` of the essential boundary in `Ω` is countably `(n - 1)`-rectifiable. -/
theorem countablyRectifiable_inter_essentialBoundary [μ.IsAddHaarMeasure]
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞) :
    CountablyRectifiable (finrank ℝ E - 1) ((Ω : Set E) ∩ essentialBoundary μ s) :=
  countablyRectifiable_reducedBoundary.congr
    (reducedBoundary_ae_eq_inter_essentialBoundary hu hfin)

/-- For a set `s` of locally finite perimeter in `Ω`, the pushforward of the perimeter measure
`|Dχ_s|` equals `μHE[n - 1]` restricted to `Ω ∩ ∂ᵉs`. -/
theorem map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_essentialBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞) :
    (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E) =
      μHE[finrank ℝ E - 1].restrict ((Ω : Set E) ∩ essentialBoundary volume s) := by
  rw [map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary]
  exact Measure.restrict_congr_set (reducedBoundary_ae_eq_inter_essentialBoundary hu hfin)

/-- For a set `s` of locally finite perimeter in `Ω`,
`P(s; Ω) = μHE[n - 1] (Ω ∩ ∂ᵉs)`. -/
theorem perimeter_eq_euclideanHausdorffMeasure_inter_essentialBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞) :
    perimeter volume Ω s = μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ essentialBoundary volume s) := by
  rw [perimeter_eq_euclideanHausdorffMeasure_reducedBoundary hu hfin,
    measure_congr (reducedBoundary_ae_eq_inter_essentialBoundary hu hfin)]

end TauCeti
