/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.BoundedVariation.PolarDecomposition
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.InnerProductSpace.CompleteSquare
import TauCeti.MeasureTheory.Covering.Besicovitch

/-!
# The reduced boundary and the measure-theoretic outer normal

Let `Ω` be an open set of a finite-dimensional real inner product space `E` and `s` a set of
locally finite perimeter in `Ω`. The derivative of its indicator is the vector measure
`Dχ_s = σ |Dχ_s|`, where `|Dχ_s|` is the perimeter measure (`TauCeti.variationMeasure`) and `σ` is
the polar density (`TauCeti.polarDensity`). A point `x ∈ Ω` belongs to the **reduced boundary**
`∂*s` (`TauCeti.reducedBoundary`) when the averages

`⨍_{closedBall x r} σ d|Dχ_s| = Dχ_s (closedBall x r) / |Dχ_s| (closedBall x r)`

converge, as `r → 0⁺`, to a unit vector. The **measure-theoretic outer normal**
`ν_s x` (`TauCeti.outerNormal`) is minus that limit, so that `Dχ_s = -ν_s |Dχ_s|`.

These are the objects of De Giorgi's structure theorem for sets of finite perimeter. This file
proves their basic properties.

* The perimeter measure is concentrated on the reduced boundary, and the outer normal is `-σ`
  at `|Dχ_s|`-almost every point (`TauCeti.ae_mem_reducedBoundary`,
  `TauCeti.ae_outerNormal_eq`). This is Lebesgue's differentiation theorem for `σ` against the
  Radon measure `|Dχ_s|` on `Ω`, which is available because `Ω` inherits the Besicovitch
  covering property (`Besicovitch.ae_tendsto_average_closedBall`). Consequently the
  **Gauss–Green formula** `∫_s div φ = ∫ ⟪φ, ν_s⟫ d|Dχ_s|` holds for every `C¹` vector field `φ`
  with compact support in `Ω`, where `div φ = tr (Dφ)`
  (`TauCeti.integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal`). It is the case
  `u = χ_s` of integration by parts against `C¹` vector fields,
  `∫ u div φ dμ = -∫ ⟪φ, σ_u⟫ d|Du|`
  (`TauCeti.integral_trace_fderiv_mul_eq_neg_integral_inner_polarDensity`).
* A point of the reduced boundary forces `s` to have locally finite perimeter in `Ω`
  (`TauCeti.locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary`), and in
  particular to be null-measurable on `Ω`
  (`TauCeti.nullMeasurableSet_restrict_of_mem_reducedBoundary`), so otherwise `∂*s` is empty
  (`TauCeti.reducedBoundary_eq_empty_of_not`).
* Every point of the reduced boundary lies in the support of `|Dχ_s|`
  (`TauCeti.variationMeasure_preimage_closedBall_ne_zero`). Hence `s` has nonzero perimeter and
  positive measure in every small ball around it (`TauCeti.perimeter_ball_ne_zero`,
  `TauCeti.measure_inter_ball_pos`). Its perimeter in a small ball `ball x r` is at most the
  perimeter measure of `closedBall x r`, as for any point of `Ω` when `s` has locally finite
  perimeter (`TauCeti.eventually_perimeter_ball_le_variationMeasure_closedBall`,
  `TauCeti.eventually_perimeter_ball_le_variationMeasure_closedBall_of_mem_reducedBoundary`), and,
  when `μ` is an additive Haar measure, the point lies in the topological frontier of `s`
  (`TauCeti.reducedBoundary_subset_frontier`).
* The outer normal concentrates at `ν_s x` in mean at every point `x` of the reduced boundary:
  `⨍_{closedBall x r} ‖ν_s - ν_s x‖ d|Dχ_s| → 0`
  (`TauCeti.tendsto_setLIntegral_enorm_outerNormal_sub_div`). The averages of the unit vectors
  `ν_s` tend to the unit vector `ν_s x`, and for unit vectors `‖a - ν‖² = 2 (1 - ⟪a, ν⟫)`.
* The reduced boundary and the outer normal only depend on `s` almost everywhere on `Ω`
  (`TauCeti.reducedBoundary_congr_ae`, `TauCeti.outerNormal_congr_ae`); in particular
  `∂*(s ∩ Ω) = ∂*s` (`TauCeti.reducedBoundary_inter_opens`). When `μ` is an additive
  Haar measure, the complement has the same reduced boundary with the opposite normal
  (`TauCeti.reducedBoundary_compl`, `TauCeti.outerNormal_compl`).
* Both `∂*s` and `ν_s` are invariant under positive finite scaling of `μ`
  (`TauCeti.reducedBoundary_smul_measure`, `TauCeti.outerNormal_smul_measure`) and local with
  respect to open subsets `U ⊆ Ω` (`TauCeti.reducedBoundary_eq_inter_of_le`,
  `TauCeti.outerNormal_eq_of_le`). Moreover, `∂*s` is always a Borel set
  (`TauCeti.measurableSet_reducedBoundary`).

The definition uses closed balls, matching `TauCeti.HasDensityAt`; it does not require `x` to lie
in the support of `|Dχ_s|`, since a unit limit forces this. When `s` does not have locally finite
perimeter in `Ω`, the perimeter measure is zero by convention and the reduced boundary is empty.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §15.1 (Definition 15.1
  and Proposition 15.5) and Chapter 15 (blow-ups at points of the reduced boundary).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1 (the
  Gauss–Green measure of a set of locally finite perimeter).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s t : Set E} {x : E}

/-- The **reduced boundary** `∂*s` of `s` in the open set `Ω`: the points `x ∈ Ω` at which the
averages of the polar density `σ` of `Dχ_s` over `closedBall x r`, against the perimeter measure
`|Dχ_s|`, converge to a unit vector as `r → 0⁺`. When `|Dχ_s| (closedBall x r)` is positive and
finite, these averages are the ratios `Dχ_s (closedBall x r) / |Dχ_s| (closedBall x r)`. -/
def reducedBoundary (μ : Measure E) (Ω : Opens E) (s : Set E) : Set E :=
  {x | x ∈ Ω ∧ ∃ ν : E, ‖ν‖ = 1 ∧
    Tendsto (fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
      polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1)) (𝓝[>] 0) (𝓝 ν)}

/-- The **measure-theoretic outer normal** `ν_s x` of `s` in `Ω`: minus the limit, as `r → 0⁺`,
of the averages of the polar density of `Dχ_s` over `closedBall x r` against `|Dχ_s|`. At points
of the reduced boundary it is a unit vector (`TauCeti.norm_outerNormal`), and
`Dχ_s = -ν_s |Dχ_s|`
(`TauCeti.integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal`). Elsewhere its
value carries no meaning. -/
def outerNormal (μ : Measure E) (Ω : Opens E) (s : Set E) (x : E) : E :=
  -limUnder (𝓝[>] (0 : ℝ)) fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
    polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1)

/-- Membership in the reduced boundary, unfolded. -/
theorem mem_reducedBoundary : x ∈ reducedBoundary μ Ω s ↔ x ∈ Ω ∧ ∃ ν : E, ‖ν‖ = 1 ∧
    Tendsto (fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
      polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1)) (𝓝[>] 0) (𝓝 ν) :=
  Iff.rfl

/-- The reduced boundary of `s` in `Ω` lies in `Ω`. -/
theorem reducedBoundary_subset : reducedBoundary μ Ω s ⊆ Ω := fun _ hx => hx.1

/-- At a point of the reduced boundary, the averages of the polar density of `Dχ_s` over shrinking
closed balls tend to `-ν_s x`. -/
theorem tendsto_setAverage_polarDensity (hx : x ∈ reducedBoundary μ Ω s) :
    Tendsto (fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
      polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1)) (𝓝[>] 0)
      (𝓝 (-outerNormal μ Ω s x)) := by
  obtain ⟨-, ν, -, hν⟩ := hx
  rw [outerNormal, neg_neg]
  exact tendsto_nhds_limUnder ⟨ν, hν⟩

/-- If the averages of the polar density of `Dχ_s` over shrinking closed balls around `x` tend to
`ν`, then the outer normal at `x` is `-ν`. -/
theorem outerNormal_eq_of_tendsto {ν : E}
    (h : Tendsto (fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
      polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1)) (𝓝[>] 0) (𝓝 ν)) :
    outerNormal μ Ω s x = -ν := by
  rw [outerNormal, h.limUnder_eq]

/-- The outer normal is a unit vector at every point of the reduced boundary. -/
@[simp]
theorem norm_outerNormal (hx : x ∈ reducedBoundary μ Ω s) : ‖outerNormal μ Ω s x‖ = 1 := by
  obtain ⟨-, ν, hν1, hν⟩ := hx
  rw [outerNormal_eq_of_tendsto hν, norm_neg, hν1]

/-- **The reduced boundary lies in the support of the perimeter measure.** Every closed ball of
positive radius around a point of `∂*s` has positive `|Dχ_s|` measure. -/
theorem variationMeasure_preimage_closedBall_ne_zero (hx : x ∈ reducedBoundary μ Ω s) {r : ℝ}
    (hr : 0 < r) :
    variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) ≠ 0 := by
  intro h0
  obtain ⟨-, ν, hν1, hν⟩ := hx
  -- The averages over the smaller balls are averages against the zero measure.
  have h : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x ρ,
      polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1) = 0 := by
    filter_upwards [Ioc_mem_nhdsGT hr] with ρ hρ
    rw [Measure.restrict_eq_zero.2 (measure_mono_null
      (preimage_mono (closedBall_subset_closedBall hρ.2)) h0), average_zero_measure]
  have hν0 := tendsto_nhds_unique hν (tendsto_const_nhds.congr' (h.mono fun _ h => h.symm))
  simp [hν0] at hν1

/-- A point of the reduced boundary forces `s` to have locally finite perimeter in `Ω`: its
indicator is locally integrable on `Ω` and has finite total variation near every compact subset
of `Ω`. -/
theorem locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary
    (hx : x ∈ reducedBoundary μ Ω s) :
    LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ ∧ ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞ := by
  by_contra h
  exact variationMeasure_preimage_closedBall_ne_zero hx one_pos
    (by simp [variationMeasure_eq_zero_of_not h])

/-- The reduced boundary is empty unless `s` has locally finite perimeter in `Ω`. -/
theorem reducedBoundary_eq_empty_of_not (h : ¬(LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ ∧
    ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)) :
    reducedBoundary μ Ω s = ∅ :=
  eq_empty_of_forall_notMem fun _ hx =>
    h (locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx)

/-- A point of the reduced boundary forces `s` to be null-measurable on `Ω`. -/
theorem nullMeasurableSet_restrict_of_mem_reducedBoundary (hx : x ∈ reducedBoundary μ Ω s) :
    NullMeasurableSet s (μ.restrict Ω) :=
  (aemeasurable_indicator_const_iff (1 : ℝ)).1
    (locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary
      hx).1.aestronglyMeasurable.aemeasurable

/-- A point of the reduced boundary of `s` in `Ω` forces `s ∩ Ω` to be null-measurable. -/
theorem nullMeasurableSet_inter_of_mem_reducedBoundary (hx : x ∈ reducedBoundary μ Ω s) :
    NullMeasurableSet (s ∩ Ω) μ :=
  (nullMeasurableSet_restrict Ω.isOpen.measurableSet.nullMeasurableSet).1
    (nullMeasurableSet_restrict_of_mem_reducedBoundary hx)

/-- At a point of the reduced boundary, the perimeter of `s` in every ball around the point is
nonzero. -/
theorem perimeter_ball_ne_zero (hx : x ∈ reducedBoundary μ Ω s) {r : ℝ} (hr : 0 < r) :
    perimeter μ ⟨ball x r, isOpen_ball⟩ s ≠ 0 := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  -- The perimeter in the ball is at least that in the smaller ball `ball x (min r ε) ⊆ Ω`.
  have hρ : 0 < min r ε := lt_min hr hε
  have hρΩ : ball x (min r ε) ⊆ Ω := (ball_subset_ball (min_le_right r ε)).trans hεΩ
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  intro hP
  have hP' : perimeter μ ⟨ball x (min r ε), isOpen_ball⟩ s = 0 :=
    le_antisymm (hP ▸ perimeter_mono (Ω' := ⟨ball x (min r ε), isOpen_ball⟩)
      (Ω := ⟨ball x r, isOpen_ball⟩) (ball_subset_ball (min_le_left r ε))) bot_le
  have hU := variationMeasure_preimage_coe hu hfin
    (U := ⟨ball x (min r ε), isOpen_ball⟩) hρΩ
  rw [Opens.coe_mk, ← perimeter_def, hP'] at hU
  exact variationMeasure_preimage_closedBall_ne_zero hx (half_pos hρ)
    (measure_mono_null (preimage_mono (closedBall_subset_ball (half_lt_self hρ))) hU)

/-- For a set of locally finite perimeter in `Ω`, the perimeter of `s` in a ball `ball x r ⊆ Ω`
is at most the perimeter measure of `closedBall x r`. -/
theorem perimeter_ball_le_variationMeasure_closedBall
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) {r : ℝ}
    (hr : ball x r ⊆ Ω) :
    perimeter μ ⟨ball x r, isOpen_ball⟩ s ≤
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
  rw [perimeter_def, ← variationMeasure_preimage_coe hu hfin (U := ⟨ball x r, isOpen_ball⟩) hr]
  exact measure_mono (preimage_mono ball_subset_closedBall)

/-- For a set of locally finite perimeter in `Ω` and a point `x ∈ Ω`, for every small `r > 0`, the
perimeter of `s` in `ball x r` is at most the perimeter measure of `closedBall x r`. -/
theorem eventually_perimeter_ball_le_variationMeasure_closedBall
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hx : x ∈ Ω) :
    ∀ᶠ r in 𝓝[>] 0, perimeter μ ⟨ball x r, isOpen_ball⟩ s ≤
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds hx)
  filter_upwards [Ioc_mem_nhdsGT hε] with r hr
  exact perimeter_ball_le_variationMeasure_closedBall hu hfin ((ball_subset_ball hr.2).trans hεΩ)

/-- At a point of the reduced boundary, for every small `r > 0`, the perimeter of `s` in
`ball x r` is at most the perimeter measure of `closedBall x r`. -/
theorem eventually_perimeter_ball_le_variationMeasure_closedBall_of_mem_reducedBoundary
    (hx : x ∈ reducedBoundary μ Ω s) :
    ∀ᶠ r in 𝓝[>] 0, perimeter μ ⟨ball x r, isOpen_ball⟩ s ≤
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) :=
  have h := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  eventually_perimeter_ball_le_variationMeasure_closedBall h.1 h.2 (reducedBoundary_subset hx)

/-- At a point of the reduced boundary, `s` charges every ball around the point. -/
theorem measure_inter_ball_pos (hx : x ∈ reducedBoundary μ Ω s) {r : ℝ} (hr : 0 < r) :
    0 < μ (s ∩ ball x r) := by
  refine pos_iff_ne_zero.2 fun h0 => perimeter_ball_ne_zero hx hr ?_
  -- Otherwise `s` is null in `ball x r`, so its perimeter there vanishes.
  rw [perimeter_congr_ae (t := ∅), perimeter_empty]
  rw [Opens.coe_mk, ae_eq_empty, Measure.restrict_apply' measurableSet_ball, h0]

/-- **The reduced boundary lies in the topological frontier.** Near a point outside the frontier
of `s`, the indicator of `s` is constant, so the perimeter measure vanishes there. -/
theorem reducedBoundary_subset_frontier [μ.IsAddHaarMeasure] :
    reducedBoundary μ Ω s ⊆ frontier s := by
  intro x hx
  by_contra hxf
  -- A ball around `x` inside `Ω` lies in `s` or in its complement.
  obtain ⟨V, hV, hVs⟩ : ∃ V ∈ 𝓝 x, V ⊆ s ∨ V ⊆ sᶜ := by
    rw [frontier, Set.mem_sdiff, not_and_or, not_not] at hxf
    rcases hxf with h | h
    · exact ⟨_, isClosed_closure.isOpen_compl.mem_nhds h,
        Or.inr (compl_subset_compl.2 subset_closure)⟩
    · exact ⟨_, isOpen_interior.mem_nhds h, Or.inl interior_subset⟩
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 (inter_mem hV (Ω.isOpen.mem_nhds hx.1))
  refine perimeter_ball_ne_zero hx hr ?_
  rcases hVs with h | h
  · rw [perimeter_congr_ae (t := univ), perimeter_univ]
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    simp [h (hrV hy).1]
  · rw [perimeter_congr_ae (t := ∅), perimeter_empty]
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    simpa using h (hrV hy).1

/-- At `|Dχ_s|`-almost every point the polar density has norm one and is the limit of its averages
over shrinking closed balls. -/
private theorem ae_tendsto_setAverage_polarDensity :
    ∀ᵐ y : Ω ∂variationMeasure μ Ω (s.indicator 1), ‖polarDensity μ Ω (s.indicator 1) y‖ = 1 ∧
      Tendsto (fun r => ⨍ z in ((↑) : Ω → E) ⁻¹' closedBall (y : E) r,
        polarDensity μ Ω (s.indicator 1) z ∂variationMeasure μ Ω (s.indicator 1)) (𝓝[>] 0)
        (𝓝 (polarDensity μ Ω (s.indicator 1) y)) := by
  by_cases h : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ ∧ ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞
  · have := Ω.isOpen.locallyCompactSpace
    filter_upwards [ae_norm_polarDensity_eq_one h.1 h.2,
      Besicovitch.ae_tendsto_average_closedBall _ locallyIntegrable_polarDensity]
      with y h1 hy
    simpa only [Subtype.preimage_closedBall] using ⟨h1, hy⟩
  · simp [variationMeasure_eq_zero_of_not h]

/-- **The perimeter measure is concentrated on the reduced boundary**: `|Dχ_s|`-almost every point
of `Ω` lies in `∂*s`. -/
theorem ae_mem_reducedBoundary :
    ∀ᵐ y : Ω ∂variationMeasure μ Ω (s.indicator 1), ↑y ∈ reducedBoundary μ Ω s := by
  filter_upwards [ae_tendsto_setAverage_polarDensity] with y ⟨h1, hy⟩
  exact ⟨y.2, _, h1, hy⟩

/-- The outer normal is minus the polar density of `Dχ_s` at `|Dχ_s|`-almost every point. -/
theorem ae_outerNormal_eq :
    ∀ᵐ y : Ω ∂variationMeasure μ Ω (s.indicator 1),
      outerNormal μ Ω s y = -polarDensity μ Ω (s.indicator 1) y := by
  filter_upwards [ae_tendsto_setAverage_polarDensity] with y hy
  exact outerNormal_eq_of_tendsto hy.2

/-- **The Gauss–Green formula, `Dχ_s = -ν_s |Dχ_s|`.** For a set `s` of locally finite perimeter
in `Ω`, the outer normal `ν_s` represents the distributional derivative of the indicator against
the perimeter measure: `∫_s div φ dμ = ∫ ⟪φ, ν_s⟫ d|Dχ_s|` for every `C¹` vector field `φ` with
compact support in `Ω`, where `div φ = tr (Dφ)`. -/
theorem integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x ∂μ =
      ∫ y, ⟪φ y, outerNormal μ Ω s y⟫ ∂variationMeasure μ Ω (s.indicator 1) := by
  rw [integral_trace_fderiv_mul_eq_neg_integral_inner_polarDensity hu hfin hφ hc hs,
    ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [ae_outerNormal_eq] with y hy
  rw [hy, inner_neg_right]

/-! ### Concentration of the outer normal -/

/-- The outer normal is integrable against the perimeter measure on sets of finite measure. -/
theorem integrableOn_outerNormal {S : Set Ω} (hS : variationMeasure μ Ω (s.indicator 1) S ≠ ∞) :
    IntegrableOn (fun y : Ω => outerNormal μ Ω s y) S (variationMeasure μ Ω (s.indicator 1)) := by
  refine Measure.integrableOn_of_bounded hS ?_ (M := 1) ?_
  · exact (measurable_polarDensity (μ := μ) (Ω := Ω) (u := s.indicator 1)).neg
      |>.aestronglyMeasurable.congr (ae_outerNormal_eq.mono fun _ h => h.symm)
  · filter_upwards [ae_restrict_of_ae ae_mem_reducedBoundary] with y hy
    exact (norm_outerNormal hy).le

/-- At a point `x` of the reduced boundary, for every `η > 0` and every small `r`, the perimeter
measure of `closedBall x r` is finite and
`∫_{closedBall x r} ‖ν_s - ν_s x‖ d|Dχ_s| ≤ 2 η |Dχ_s| (closedBall x r)`. -/
theorem eventually_setIntegral_norm_outerNormal_sub_le
    (hx : x ∈ reducedBoundary μ Ω s) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] 0,
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) ≠ ∞ ∧
      ∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
          ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖ ∂variationMeasure μ Ω (s.indicator 1) ≤
        2 * η * (variationMeasure μ Ω (s.indicator 1)).real
          (((↑) : Ω → E) ⁻¹' closedBall x r) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  set lam := variationMeasure μ Ω (s.indicator 1)
  set ν := outerNormal μ Ω s x
  set n : Ω → E := fun y => outerNormal μ Ω s y
  have hν : ‖ν‖ = 1 := norm_outerNormal hx
  have hn1 : ∀ᵐ y ∂lam, ‖n y‖ = 1 := by
    filter_upwards [ae_outerNormal_eq, ae_norm_polarDensity_eq_one hu hfin] with y h1 h2
    simp only [n, h1, norm_neg, h2]
  -- The averages of `ν_s` over small balls tend to `ν`.
  have havg : Tendsto (fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r, n y ∂lam) (𝓝[>] 0)
      (𝓝 ν) := by
    have h := (tendsto_setAverage_polarDensity hx).neg
    rw [neg_neg] at h
    refine h.congr fun r => ?_
    rw [← average_neg]
    exact average_congr (ae_restrict_of_ae (ae_outerNormal_eq.mono fun _ h => h.symm))
  have hinner : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      1 - η ^ 2 / 2 < ⟪ν, ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r, n y ∂lam⟫ := by
    refine (tendsto_const_nhds.inner havg).eventually_const_lt ?_
    rw [real_inner_self_eq_norm_sq, hν]
    linarith [pow_pos hη 2]
  obtain ⟨ε, hε, hεΩ⟩ :=
    nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [hinner, Ioc_mem_nhdsGT hε] with r hr hrε
  set S := ((↑) : Ω → E) ⁻¹' closedBall x r
  have hS : IsCompact S := Topology.IsInducing.subtypeVal.isCompact_preimage'
    (isCompact_closedBall x r) (by
      rw [Subtype.range_coe]
      exact (closedBall_subset_closedBall hrε.2).trans hεΩ)
  have hSfin : lam S ≠ ∞ := hS.measure_lt_top.ne
  refine ⟨hSfin, ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hn : IntegrableOn n S lam := integrableOn_outerNormal hSfin
  have hc (c : ℝ) : IntegrableOn (fun _ => c) S lam := integrableOn_const hSfin
  have hν' : IntegrableOn (fun _ => ν) S lam := integrableOn_const hSfin
  have hin : IntegrableOn (fun y => ⟪ν, n y⟫) S lam := Integrable.const_inner ν hn
  calc ∫ y in S, ‖n y - ν‖ ∂lam
      ≤ ∫ y in S, ((η / 2 + 1 / η) - 1 / η * ⟪ν, n y⟫) ∂lam := by
        refine setIntegral_mono_on_ae (hn.sub hν').norm ((hc _).sub (hin.const_mul _)) hSm ?_
        filter_upwards [hn1] with y hy _
        exact norm_sub_le_add_div_sub_inner hy hν hη
    _ = lam.real S * ((η / 2 + 1 / η) - 1 / η * ⟪ν, ⨍ y in S, n y ∂lam⟫) := by
        rw [integral_sub (hc _) (hin.const_mul _), integral_const_mul, integral_inner hn,
          setIntegral_const, ← measure_smul_setAverage _ hSfin, inner_smul_right, smul_eq_mul]
        ring
    _ ≤ 2 * η * lam.real S := by
        have hle : (η / 2 + 1 / η) - 1 / η * ⟪ν, ⨍ y in S, n y ∂lam⟫ ≤ 2 * η := by
          have h2 : 1 / η * (1 - η ^ 2 / 2) = 1 / η - η / 2 := by field_simp
          nlinarith [mul_lt_mul_of_pos_left hr (one_div_pos.2 hη)]
        nlinarith [measureReal_nonneg (μ := lam) (s := S)]

/-- **Concentration of the outer normal at the reduced boundary.** At a point `x` of the reduced
boundary of `s` in `Ω`, the mean deviation of the outer normal from `ν_s x` over small closed
balls tends to zero:

`(∫_{closedBall x r} ‖ν_s - ν_s x‖ d|Dχ_s|) / |Dχ_s| (closedBall x r) → 0`  as `r → 0⁺`. -/
theorem tendsto_setLIntegral_enorm_outerNormal_sub_div (hx : x ∈ reducedBoundary μ Ω s) :
    Tendsto (fun r => (∫⁻ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖ₑ ∂variationMeasure μ Ω (s.indicator 1)) /
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
  set lam := variationMeasure μ Ω (s.indicator 1)
  refine ENNReal.tendsto_nhds_zero.2 fun δ hδ => ?_
  obtain rfl | hδt := eq_or_ne δ ∞
  · exact .of_forall fun _ => le_top
  have hδr : 0 < δ.toReal / 2 := half_pos (ENNReal.toReal_pos hδ.ne' hδt)
  filter_upwards [eventually_setIntegral_norm_outerNormal_sub_le hx hδr] with r ⟨hSfin, hr⟩
  set S := ((↑) : Ω → E) ⁻¹' closedBall x r
  refine ENNReal.div_le_of_le_mul ?_
  have hi : IntegrableOn (fun y : Ω => outerNormal μ Ω s y - outerNormal μ Ω s x) S lam :=
    (integrableOn_outerNormal hSfin).sub (integrableOn_const hSfin)
  rw [← ofReal_integral_norm_eq_lintegral_eNorm hi]
  calc ENNReal.ofReal (∫ y in S, ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖ ∂lam)
      ≤ ENNReal.ofReal (2 * (δ.toReal / 2) * lam.real S) := ENNReal.ofReal_le_ofReal hr
    _ = δ * lam S := by
        rw [mul_div_cancel₀ _ two_ne_zero, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hδt, ofReal_measureReal hSfin]


/-! ### Invariance under null modification and complements -/

/-- The averages defining the reduced boundary only depend on `s` almost everywhere on `Ω`. -/
private theorem setAverage_polarDensity_congr_ae (h : s =ᵐ[μ.restrict Ω] t) (x : E) (r : ℝ) :
    ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1) =
      ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity μ Ω (t.indicator 1) y ∂variationMeasure μ Ω (t.indicator 1) := by
  have hst : s.indicator (1 : E → ℝ) =ᵐ[μ.restrict Ω] t.indicator 1 :=
    indicator_ae_eq_of_ae_eq_set h
  rw [← variationMeasure_congr_ae hst]
  exact average_congr (ae_restrict_of_ae (polarDensity_congr_ae hst))

/-- **Locality of the reduced boundary.** If `s = t` almost everywhere on `Ω`, they have the same
reduced boundary in `Ω`. -/
theorem reducedBoundary_congr_ae (h : s =ᵐ[μ.restrict Ω] t) :
    reducedBoundary μ Ω s = reducedBoundary μ Ω t := by
  ext x
  simp only [mem_reducedBoundary, setAverage_polarDensity_congr_ae h]

/-- Intersecting `s` with `Ω` does not change its reduced boundary in `Ω`. -/
@[simp]
theorem reducedBoundary_inter_opens : reducedBoundary μ Ω (s ∩ Ω) = reducedBoundary μ Ω s := by
  refine reducedBoundary_congr_ae ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
  exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩

/-- **Locality of the outer normal.** If `s = t` almost everywhere on `Ω`, they have the same
outer normal. -/
theorem outerNormal_congr_ae (h : s =ᵐ[μ.restrict Ω] t) :
    outerNormal μ Ω s = outerNormal μ Ω t := by
  ext x
  simp only [outerNormal, setAverage_polarDensity_congr_ae h]

/-- Against an additive Haar measure, the averages defining the reduced boundary of `sᶜ` are
opposite to those of `s`. -/
private theorem setAverage_polarDensity_compl [μ.IsAddHaarMeasure] (x : E) (r : ℝ) :
    ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity μ Ω (sᶜ.indicator 1) y ∂variationMeasure μ Ω (sᶜ.indicator 1) =
      -⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1) := by
  have hc : sᶜ.indicator (1 : E → ℝ) = fun y => 1 - s.indicator 1 y := by
    ext y
    by_cases hy : y ∈ s <;> simp [hy]
  rw [hc, variationMeasure_const_sub, ← average_neg]
  exact average_congr (ae_restrict_of_ae (polarDensity_const_sub 1))

/-- **The complement has the same reduced boundary**, against an additive Haar measure. -/
@[simp]
theorem reducedBoundary_compl [μ.IsAddHaarMeasure] :
    reducedBoundary μ Ω sᶜ = reducedBoundary μ Ω s := by
  ext x
  simp only [mem_reducedBoundary, setAverage_polarDensity_compl]
  refine and_congr_right fun _ => ⟨fun ⟨ν, h1, hν⟩ => ⟨-ν, by rwa [norm_neg], ?_⟩,
    fun ⟨ν, h1, hν⟩ => ⟨-ν, by rwa [norm_neg], hν.neg⟩⟩
  simpa using hν.neg

/-- **The complement has the opposite outer normal** at every point of the reduced boundary,
against an additive Haar measure. -/
theorem outerNormal_compl [μ.IsAddHaarMeasure] (hx : x ∈ reducedBoundary μ Ω s) :
    outerNormal μ Ω sᶜ x = -outerNormal μ Ω s x := by
  rw [outerNormal]
  simp only [setAverage_polarDensity_compl]
  rw [(tendsto_setAverage_polarDensity hx).neg.limUnder_eq, neg_neg]

/-- Scaling the ambient measure by a positive finite factor does not change the averages defining
the reduced boundary. -/
private theorem setAverage_polarDensity_smul_measure {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (x : E) (r : ℝ) :
    ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity (c • μ) Ω (s.indicator 1) y ∂variationMeasure (c • μ) Ω (s.indicator 1) =
      ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1) := by
  rw [variationMeasure_smul_measure hc, Measure.restrict_smul, average_eq',
    smul_apply, smul_eq_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hc), smul_smul,
    mul_right_comm, ENNReal.inv_mul_cancel hc0 hc, one_mul, ← average_eq']
  exact average_congr (ae_restrict_of_ae (polarDensity_smul_measure hc0 hc))

/-- Scaling the ambient measure by a positive finite factor does not change the reduced
boundary. -/
theorem reducedBoundary_smul_measure {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    reducedBoundary (c • μ) Ω s = reducedBoundary μ Ω s := by
  ext x
  simp only [mem_reducedBoundary, setAverage_polarDensity_smul_measure hc0 hc]

/-- Scaling the ambient measure by a positive finite factor does not change the outer normal. -/
theorem outerNormal_smul_measure {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    outerNormal (c • μ) Ω s = outerNormal μ Ω s := by
  ext x
  simp only [outerNormal, setAverage_polarDensity_smul_measure hc0 hc]

/-! ### Restriction to an open subset -/

/-- Near a point `x ∈ U ⊆ Ω`, the polar-density averages on `U` and on `Ω` agree for all small
closed balls. -/
private theorem eventuallyEq_setAverage_polarDensity_of_le {U : Opens E}
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞)
    (hU : U ≤ Ω) (hx : x ∈ U) :
    (fun r => ⨍ y in ((↑) : U → E) ⁻¹' closedBall x r,
        polarDensity μ U (s.indicator 1) y ∂variationMeasure μ U (s.indicator 1)) =ᶠ[𝓝[>] 0]
      fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1) := by
  set ι : U → Ω := inclusion (SetLike.coe_subset_coe.2 hU)
  have hemb : Topology.IsOpenEmbedding ι := Opens.isOpenEmbedding_of_le hU
  have hmap : (variationMeasure μ U (s.indicator 1)).map ι =
      (variationMeasure μ Ω (s.indicator 1)).restrict (((↑) : Ω → E) ⁻¹' (U : Set E)) :=
    map_inclusion_variationMeasure hu hfin hU
  have hpol : polarDensity μ Ω (s.indicator 1) ∘ ι =ᵐ[variationMeasure μ U (s.indicator 1)]
      polarDensity μ U (s.indicator 1) := polarDensity_comp_inclusion hu hfin hU
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 (U.isOpen.mem_nhds hx)
  filter_upwards [Ioc_mem_nhdsGT hε] with r hr
  have hrU : closedBall x r ⊆ U := (closedBall_subset_closedBall hr.2).trans hεU
  set SU : Set U := ((↑) : U → E) ⁻¹' closedBall x r
  set SΩ : Set Ω := ((↑) : Ω → E) ⁻¹' closedBall x r
  have hSUm : MeasurableSet SU :=
    (isClosed_closedBall.preimage continuous_subtype_val).measurableSet
  have hSΩm : MeasurableSet SΩ :=
    (isClosed_closedBall.preimage continuous_subtype_val).measurableSet
  have hpre : ι ⁻¹' SΩ = SU := rfl
  have hsub : SΩ ⊆ ((↑) : Ω → E) ⁻¹' (U : Set E) := preimage_mono hrU
  have hmeas : variationMeasure μ U (s.indicator 1) SU =
      variationMeasure μ Ω (s.indicator 1) SΩ := by
    rw [← hpre, ← Measure.map_apply hemb.continuous.measurable hSΩm, hmap,
      Measure.restrict_apply hSΩm, inter_eq_left.2 hsub]
  have hint : ∫ y in SU, polarDensity μ U (s.indicator 1) y ∂variationMeasure μ U (s.indicator 1) =
      ∫ y in SΩ, polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1) := by
    rw [← setIntegral_congr_ae hSUm (hpol.mono fun y hy _ => hy), ← hpre]
    simp only [Function.comp_apply]
    rw [← hemb.measurableEmbedding.setIntegral_map (polarDensity μ Ω (s.indicator 1)) SΩ, hmap,
      Measure.restrict_restrict hSΩm, inter_eq_left.2 hsub]
  simp only [setAverage_eq, measureReal_def, hmeas, hint]

/-- **Locality in the open set.** For a set `s` of locally finite perimeter in `Ω` and an open
subset `U ⊆ Ω`, the reduced boundary of `s` in `U` is `U ∩ ∂*s`. -/
theorem reducedBoundary_eq_inter_of_le {U : Opens E}
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞)
    (hU : U ≤ Ω) :
    reducedBoundary μ U s = (U : Set E) ∩ reducedBoundary μ Ω s := by
  ext y
  by_cases hy : y ∈ U
  · simp only [mem_inter_iff, SetLike.mem_coe, hy, true_and, mem_reducedBoundary, hU hy]
    refine exists_congr fun ν => and_congr_right fun _ =>
      tendsto_congr' (eventuallyEq_setAverage_polarDensity_of_le hu hfin hU hy)
  · simp only [mem_inter_iff, SetLike.mem_coe, hy, false_and, iff_false]
    exact fun h => hy (reducedBoundary_subset h)

/-- For a set `s` of locally finite perimeter in `Ω` and an open subset `U ⊆ Ω`, the outer normal
in `U` agrees with the outer normal in `Ω` at every point of `U`. -/
theorem outerNormal_eq_of_le {U : Opens E}
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞)
    (hU : U ≤ Ω) (hx : x ∈ U) :
    outerNormal μ U s x = outerNormal μ Ω s x := by
  rw [outerNormal, outerNormal, Filter.limUnder, Filter.limUnder,
    Filter.map_congr (eventuallyEq_setAverage_polarDensity_of_le hu hfin hU hx)]

/-! ### Borel measurability of the reduced boundary -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For a bounded measurable function `f` and a finite measure `ν` on `Ω`, the integral of `f` over
`closedBall x r` is right-continuous in `r`. -/
private theorem continuousWithinAt_integral_ite_dist_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f : Ω → F} (hfm : Measurable f)
    {C : ℝ} (hfC : ∀ y, ‖f y‖ ≤ C) (x : E) (r₀ : ℝ) :
    ContinuousWithinAt (fun r => ∫ y : Ω, (if dist (y : E) x ≤ r then f y else 0) ∂ν)
      (Ici r₀) r₀ := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_
    (integrable_const C) ?_
  · refine .of_forall fun r => (Measurable.ite
      (measurableSet_le (continuous_subtype_val.dist continuous_const).measurable measurable_const)
      hfm measurable_const).aestronglyMeasurable
  · refine .of_forall fun r => .of_forall fun y => ?_
    split_ifs
    · exact hfC y
    · rw [norm_zero]
      exact (norm_nonneg (f y)).trans (hfC y)
  · refine .of_forall fun y => ?_
    by_cases hy : dist (y : E) x ≤ r₀
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r (hr : r₀ ≤ r)
      simp [hy, hy.trans hr]
    · push Not at hy
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hy)] with r (hr : r < dist (y : E) x)
      simp [not_le.2 hy, not_le.2 hr]

/-- For a measurable function `f` into a second-countable Banach space and a finite measure `ν` on
`Ω`, the integral of `f` over `closedBall x r` is Borel measurable in `x`. -/
private theorem measurable_integral_ite_dist_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f : Ω → F} (hfm : Measurable f) (r : ℝ) :
    Measurable fun x : E => ∫ y : Ω, (if dist (y : E) x ≤ r then f y else 0) ∂ν :=
  (Measurable.ite (measurableSet_le
    ((continuous_subtype_val.comp continuous_snd).dist continuous_fst).measurable measurable_const)
    (hfm.comp measurable_snd) measurable_const).stronglyMeasurable.integral_prod_right'.measurable

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Right-continuity on `(0, δ₁)` transfers the rational Cauchy property as `q → 0⁺` to the real
Cauchy property along `𝓝[>] 0`. -/
private theorem cauchy_map_nhdsGT_of_rat {δ δ₁ : ℝ} (hδ₁ : 0 < δ₁) (hδ₁δ : δ₁ ≤ δ) {g : ℝ → E}
    (hrc : ∀ r ∈ Ioo 0 δ₁, ContinuousWithinAt g (Ici r) r)
    (hcauchy : ∀ n : ℕ, ∃ k : ℕ, ∀ q₁ q₂ : ℚ,
      (0 : ℝ) < q₁ → (q₁ : ℝ) < min δ (1 / ((k : ℝ) + 1)) →
      (0 : ℝ) < q₂ → (q₂ : ℝ) < min δ (1 / ((k : ℝ) + 1)) →
        dist (g q₁) (g q₂) ≤ 1 / ((n : ℝ) + 1)) :
    Cauchy (Filter.map g (𝓝[>] 0)) := by
  rw [Metric.cauchy_iff]
  refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
  obtain ⟨k, hk⟩ := hcauchy n
  set η := min δ₁ (1 / ((k : ℝ) + 1))
  have hη : 0 < η := lt_min hδ₁ (by positivity)
  have hη_le : η ≤ min δ (1 / ((k : ℝ) + 1)) := min_le_min_right _ hδ₁δ
  refine ⟨g '' Ioo 0 η, Filter.image_mem_map (Ioo_mem_nhdsGT hη), ?_⟩
  rintro _ ⟨r₁, hr₁, rfl⟩ _ ⟨r₂, hr₂, rfl⟩
  have approx {r : ℝ} (hr : r ∈ Ioo 0 η) :
      ∃ q : ℚ, (0 : ℝ) < q ∧ (q : ℝ) < min δ (1 / ((k : ℝ) + 1)) ∧
        dist (g r) (g q) < 1 / ((n : ℝ) + 1) := by
    have hcont := hrc r ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhdsWithin_iff.1
      (hcont (Metric.ball_mem_nhds (g r) (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))))
    obtain ⟨q, hrq, hqlt⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right r hρ) hr.2)
    have hqη : (q : ℝ) < η := hqlt.trans_le (min_le_right _ _)
    refine ⟨q, hr.1.trans hrq, hqη.trans_le hη_le, ?_⟩
    rw [dist_comm]
    refine hsub ⟨?_, hrq.le⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.2 hrq)]
    linarith [hqlt.trans_le (min_le_left _ _)]
  obtain ⟨q₁, hq₁0, hq₁, hd₁⟩ := approx hr₁
  obtain ⟨q₂, hq₂0, hq₂, hd₂⟩ := approx hr₂
  calc dist (g r₁) (g r₂)
      ≤ dist (g r₁) (g q₁) + dist (g q₁) (g q₂) + dist (g q₂) (g r₂) := dist_triangle4 _ _ _ _
    _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
        rw [dist_comm (g q₂)]
        linarith [hk q₁ q₂ hq₁0 hq₁ hq₂0 hq₂]
    _ < ε := by linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- Convergence of a right-continuous family `g : ℝ → E` to a unit vector as `r → 0⁺` is
characterised by its Cauchy and unit-norm behaviour along positive rationals. -/
private theorem exists_norm_one_tendsto_iff_rat {δ : ℝ} (hδ : 0 < δ) {m : ℝ → ℝ} {g : ℝ → E}
    (hm_mono : Monotone m) (hm_pos : ∀ r, g r ≠ 0 → 0 < m r)
    (hg_rc : ∀ r, 0 < m r → ContinuousWithinAt g (Ici r) r) :
    (∃ ν : E, ‖ν‖ = 1 ∧ Tendsto g (𝓝[>] 0) (𝓝 ν)) ↔
      (∀ n : ℕ, ∃ k : ℕ, ∀ q₁ q₂ : ℚ,
        (0 : ℝ) < q₁ → (q₁ : ℝ) < min δ (1 / ((k : ℝ) + 1)) →
        (0 : ℝ) < q₂ → (q₂ : ℝ) < min δ (1 / ((k : ℝ) + 1)) →
          dist (g q₁) (g q₂) ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, ∃ k : ℕ, ∀ q : ℚ,
        (0 : ℝ) < q → (q : ℝ) < min δ (1 / ((k : ℝ) + 1)) →
          |‖g q‖ - 1| ≤ 1 / ((n : ℝ) + 1)) := by
  constructor
  · rintro ⟨ν, hν1, hg⟩
    refine ⟨fun n => ?_, fun n => ?_⟩
    · have hε : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
      obtain ⟨ρ, hρ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
        (hg.eventually (Metric.ball_mem_nhds ν hε))
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hρ
      refine ⟨k, fun q₁ q₂ hq₁0 hq₁ hq₂0 hq₂ => ?_⟩
      have h1 : dist (g q₁) ν < 1 / (2 * ((n : ℝ) + 1)) :=
        hsub ⟨hq₁0, (hq₁.trans_le (min_le_right _ _)).trans hk⟩
      have h2 : dist (g q₂) ν < 1 / (2 * ((n : ℝ) + 1)) :=
        hsub ⟨hq₂0, (hq₂.trans_le (min_le_right _ _)).trans hk⟩
      have hhalf : 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
        rw [← add_div, ← two_mul, mul_div_mul_left _ _ two_ne_zero]
      linarith [dist_triangle_right (g q₁) (g q₂) ν]
    · have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨ρ, hρ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
        (hg.norm.eventually (Metric.ball_mem_nhds ‖ν‖ hε))
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hρ
      refine ⟨k, fun q hq0 hq => ?_⟩
      have h1 : dist ‖g q‖ ‖ν‖ < 1 / ((n : ℝ) + 1) :=
        hsub ⟨hq0, (hq.trans_le (min_le_right _ _)).trans hk⟩
      rw [hν1, Real.dist_eq] at h1
      exact h1.le
  · rintro ⟨hcauchy, hnorm⟩
    obtain ⟨k₀, hk₀⟩ := hnorm 1
    set δ₁ := min δ (1 / ((k₀ : ℝ) + 1))
    have hδ₁ : 0 < δ₁ := lt_min hδ (by positivity)
    have hrc : ∀ r ∈ Ioo 0 δ₁, ContinuousWithinAt g (Ici r) r := fun r hr => by
      obtain ⟨q, hq0, hqr⟩ := exists_rat_btwn hr.1
      have hqnorm := hk₀ q hq0 (hqr.trans hr.2)
      have hgq : g q ≠ 0 := fun h0 => by
        rw [h0, norm_zero] at hqnorm
        norm_num at hqnorm
      exact hg_rc r ((hm_pos q hgq).trans_le (hm_mono hqr.le))
    obtain ⟨ν, hν'⟩ := cauchy_iff_exists_le_nhds.1
      (cauchy_map_nhdsGT_of_rat hδ₁ (min_le_left _ _) hrc hcauchy)
    have hν : Tendsto g (𝓝[>] 0) (𝓝 ν) := hν'
    refine ⟨ν, eq_of_forall_dist_le fun ε hε => ?_, hν⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨k, hk⟩ := hnorm n
    obtain ⟨ρ, hρ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (hν.norm.eventually (Metric.ball_mem_nhds ‖ν‖ (half_pos hε)))
    obtain ⟨q, hq0, hqlt⟩ :=
      exists_rat_btwn (lt_min (lt_min hδ (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))) hρ)
    have hq1 : dist ‖g q‖ ‖ν‖ < ε / 2 := hsub ⟨hq0, hqlt.trans_le (min_le_right _ _)⟩
    have hq2 : dist ‖g q‖ 1 ≤ 1 / ((n : ℝ) + 1) := by
      rw [Real.dist_eq]
      exact hk q hq0 (hqlt.trans_le (min_le_left _ _))
    linarith [dist_triangle_left ‖ν‖ 1 ‖g q‖]

omit [FiniteDimensional ℝ E] in
/-- For `x ∈ ball c δ` and `r ∈ (0, δ]`, integrating `1` and a bounded representative of `σ` over
`{y | dist y x ≤ r}` against `|Dχ_s|` restricted to `closedBall c (2 * δ)` recovers the
polar-density average on `closedBall x r`. -/
private theorem inv_integral_ite_smul_eq_setAverage {c : E} {δ : ℝ} {lam : Measure Ω}
    {σ σ' : Ω → E} (hσ'ae : σ' =ᵐ[lam] σ) {x : E} (hx : x ∈ ball c δ) {r : ℝ} (hr : r ∈ Ioc 0 δ) :
    let ν := lam.restrict (((↑) : Ω → E) ⁻¹' closedBall c (2 * δ))
    (∫ y : Ω, (if dist (y : E) x ≤ r then (1 : ℝ) else 0) ∂ν)⁻¹ •
        (∫ y : Ω, (if dist (y : E) x ≤ r then σ' y else 0) ∂ν) =
      ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r, σ y ∂lam := by
  intro ν
  set S : Set Ω := ((↑) : Ω → E) ⁻¹' closedBall x r
  have hSK : S ⊆ ((↑) : Ω → E) ⁻¹' closedBall c (2 * δ) := fun y hy => by
    rw [mem_preimage, mem_closedBall] at hy ⊢
    have hxc : dist x c < δ := hx
    linarith [dist_triangle (y : E) x c, hr.2]
  have hSm : MeasurableSet S := (isClosed_closedBall.preimage continuous_subtype_val).measurableSet
  have hm : ∫ y : Ω, (if dist (y : E) x ≤ r then (1 : ℝ) else 0) ∂ν = lam.real S := by
    have hite : (fun y : Ω => if dist (y : E) x ≤ r then (1 : ℝ) else 0) = S.indicator 1 := by
      ext y; by_cases h : dist (y : E) x ≤ r <;> simp [S, mem_closedBall, h]
    simp only [hite, integral_indicator_one hSm, measureReal_def, ν, Measure.restrict_apply hSm,
      inter_eq_left.2 hSK]
  have hI : ∫ y : Ω, (if dist (y : E) x ≤ r then σ' y else 0) ∂ν = ∫ y in S, σ y ∂lam := by
    have hite : (fun y : Ω => if dist (y : E) x ≤ r then σ' y else 0) = S.indicator σ' := by
      ext y; by_cases h : dist (y : E) x ≤ r <;> simp [S, mem_closedBall, h]
    rw [hite, integral_indicator hSm, Measure.restrict_restrict hSm, inter_eq_left.2 hSK]
    exact setIntegral_congr_ae hSm (hσ'ae.mono fun _ h _ => h)
  rw [setAverage_eq, hm, hI]

/-- Inside a ball `ball c δ` with `closedBall c (2 * δ) ⊆ Ω`, the reduced boundary is Borel
measurable. -/
private theorem measurableSet_ball_inter_reducedBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞)
    {c : E} {δ : ℝ} (hδ : 0 < δ) (hΩ : closedBall c (2 * δ) ⊆ Ω) :
    MeasurableSet (ball c δ ∩ reducedBoundary μ Ω s) := by
  set lam := variationMeasure μ Ω (s.indicator 1)
  set σ := polarDensity μ Ω (s.indicator 1)
  set σ' : Ω → E := fun y => if ‖σ y‖ ≤ 1 then σ y else 0
  have hσ'm : Measurable σ' := Measurable.ite
    (measurableSet_le measurable_polarDensity.norm measurable_const)
    measurable_polarDensity measurable_const
  have hσ'1 (y : Ω) : ‖σ' y‖ ≤ 1 := by simp only [σ']; split_ifs with h <;> simp [h]
  have hσ'ae : σ' =ᵐ[lam] σ := by
    filter_upwards [ae_norm_polarDensity_eq_one hu hfin] with y hy
    have hy' : ‖σ y‖ = 1 := hy
    simp [σ', hy']
  have hKc : IsCompact (((↑) : Ω → E) ⁻¹' closedBall c (2 * δ)) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall c (2 * δ))
      (by rwa [Subtype.range_coe])
  set ν : Measure Ω := lam.restrict (((↑) : Ω → E) ⁻¹' closedBall c (2 * δ))
  have : IsFiniteMeasure ν := ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  set m : ℝ → E → ℝ := fun r x => ∫ y : Ω, (if dist (y : E) x ≤ r then (1 : ℝ) else 0) ∂ν
  set I : ℝ → E → E := fun r x => ∫ y : Ω, (if dist (y : E) x ≤ r then σ' y else 0) ∂ν
  set g : ℝ → E → E := fun r x => (m r x)⁻¹ • I r x
  have hgm (r : ℝ) : Measurable (g r) :=
    ((measurable_integral_ite_dist_le measurable_const r).inv).smul
      (measurable_integral_ite_dist_le hσ'm r)
  have hm_int (r : ℝ) (x : E) :
      Integrable (fun y : Ω => if dist (y : E) x ≤ r then (1 : ℝ) else 0) ν := by
    refine ((integrable_const (1 : ℝ)).indicator
      ((isClosed_closedBall (x := x) (ε := r)).preimage continuous_subtype_val).measurableSet).congr
      (.of_forall fun y => ?_)
    by_cases h : dist (y : E) x ≤ r <;> simp [mem_closedBall, h]
  have heq : ball c δ ∩ reducedBoundary μ Ω s =
      ball c δ ∩
        ((⋂ n : ℕ, ⋃ k : ℕ, ⋂ q₁ : ℚ, ⋂ q₂ : ℚ,
            ⋂ (_ : (0 : ℝ) < q₁), ⋂ (_ : (q₁ : ℝ) < min δ (1 / ((k : ℝ) + 1))),
            ⋂ (_ : (0 : ℝ) < q₂), ⋂ (_ : (q₂ : ℝ) < min δ (1 / ((k : ℝ) + 1))),
              {x : E | dist (g q₁ x) (g q₂ x) ≤ 1 / ((n : ℝ) + 1)}) ∩
         (⋂ n : ℕ, ⋃ k : ℕ, ⋂ q : ℚ, ⋂ (_ : (0 : ℝ) < q),
            ⋂ (_ : (q : ℝ) < min δ (1 / ((k : ℝ) + 1))),
              {x : E | |‖g q x‖ - 1| ≤ 1 / ((n : ℝ) + 1)})) := by
    ext x
    by_cases hx : x ∈ ball c δ
    · have hxΩ : x ∈ Ω :=
        hΩ (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hx))
      have hm_mono : Monotone fun r => m r x := fun r₁ r₂ hr =>
        integral_mono (hm_int r₁ x) (hm_int r₂ x) fun y => by
          split_ifs with h₁ h₂
          · exact le_rfl
          · exact absurd (h₁.trans hr) h₂
          · exact zero_le_one
          · exact le_rfl
      have hm_pos (r : ℝ) (hgr : g r x ≠ 0) : 0 < m r x :=
        lt_of_le_of_ne (integral_nonneg fun y => by split_ifs <;> positivity)
          fun h0 => hgr (by simp [g, ← h0])
      have hg_rc (r : ℝ) (hmr : 0 < m r x) : ContinuousWithinAt (fun t => g t x) (Ici r) r :=
        ((continuousWithinAt_integral_ite_dist_le (ν := ν) (C := 1) measurable_const
          (fun _ => by simp) x r).inv₀ hmr.ne').smul
          (continuousWithinAt_integral_ite_dist_le (ν := ν) hσ'm hσ'1 x r)
      have htend : (∃ ν₀ : E, ‖ν₀‖ = 1 ∧ Tendsto (fun r => g r x) (𝓝[>] 0) (𝓝 ν₀)) ↔
          x ∈ reducedBoundary μ Ω s := by
        simp only [mem_reducedBoundary, hxΩ, true_and]
        exact exists_congr fun ν₀ => and_congr_right fun _ => tendsto_congr'
          (Filter.eventually_of_mem (Ioc_mem_nhdsGT hδ)
            fun r hr => inv_integral_ite_smul_eq_setAverage hσ'ae hx hr)
      simp only [mem_inter_iff, hx, true_and, ← htend,
        exists_norm_one_tendsto_iff_rat hδ hm_mono hm_pos hg_rc, mem_iInter, mem_iUnion,
        mem_ofPred_eq]
    · simp [hx]
  rw [heq]
  refine measurableSet_ball.inter ((MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
    MeasurableSet.iInter fun (q₁ : ℚ) => MeasurableSet.iInter fun (q₂ : ℚ) =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
          measurableSet_le ((hgm q₁).dist (hgm q₂)) measurable_const).inter
    (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
      MeasurableSet.iInter fun (q : ℚ) =>
        MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
          measurableSet_le (continuous_abs.measurable.comp ((hgm q).norm.sub measurable_const))
            measurable_const))

/-- **The reduced boundary is a Borel set.** -/
theorem measurableSet_reducedBoundary : MeasurableSet (reducedBoundary μ Ω s) := by
  by_cases h : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ ∧
      ∀ K, IsCompact K → K ⊆ Ω →
        ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V (s.indicator 1) ≠ ∞
  swap
  · rw [reducedBoundary_eq_empty_of_not h]
    exact MeasurableSet.empty
  obtain ⟨hu, hfin⟩ := h
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense E
  have : Countable D := hDc.to_subtype
  set ι := {p : D × ℚ // (0 : ℝ) < p.2 ∧ closedBall (p.1 : E) (2 * (p.2 : ℝ)) ⊆ Ω}
  have hcov : reducedBoundary μ Ω s = ⋃ p : ι, ball (p.1.1 : E) (p.1.2 : ℝ) ∩
      reducedBoundary μ Ω s := by
    refine Subset.antisymm (fun x hx => ?_) (iUnion_subset fun _ => inter_subset_right)
    obtain ⟨r, hr, hrΩ⟩ :=
      nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
    obtain ⟨q, hq0, hqr⟩ := exists_rat_btwn (div_pos hr (by norm_num : (0 : ℝ) < 3))
    obtain ⟨d, hdD, hdx⟩ := Metric.mem_closure_iff.1 (hDd x) q hq0
    have hΩ' : closedBall d (2 * (q : ℝ)) ⊆ Ω := fun y hy => hrΩ <| by
      rw [mem_closedBall] at hy ⊢
      have : dist d x < q := by rwa [dist_comm]
      linarith [dist_triangle y d x, (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).1 hqr]
    exact mem_iUnion.2 ⟨⟨(⟨d, hdD⟩, q), hq0, hΩ'⟩, hdx, hx⟩
  rw [hcov]
  exact MeasurableSet.iUnion fun p => measurableSet_ball_inter_reducedBoundary hu hfin p.2.1 p.2.2

end TauCeti
