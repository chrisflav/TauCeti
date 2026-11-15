/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import TauCeti.Analysis.Normed.Operator.Basic
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Topology.Compactness.Normed
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Calculus.FDeriv.Const

/-!
# Parametric integrals with a fixed compact support

Let `X` be a topological space with a Borel measure finite on compact sets, and let `D t x`
take values in a normed space over `𝕜 = ℝ` or `ℂ`. Suppose `D t` is continuous and vanishes
outside a fixed compact set for parameters in a normed space near `t₀`. A jointly continuous
parameter derivative can then be integrated to compute the derivative of the integral, both on
neighbourhoods of `t₀` and within a convex parameter set `s` containing `t₀` (covering one-sided
derivatives at endpoints of intervals and boundary half-balls).

On an open parameter domain, the integral is `C¹` when the first parameter derivative is
jointly continuous, and `C²` when both the first and second are jointly continuous. The
second derivative is also computed by integration. A general successor step reduces higher
regularity to the regularity of the integral of the first parameter derivative.

The lemmas `integrable_of_hasFDerivAt_of_compact_support`,
`integrable_of_hasFDerivWithinAt_of_compact_support`, and
`integrable_of_hasFDerivAt_of_hasFDerivAt_of_compact_support` give integrability of the first
and second parameter derivatives, including when the support hypothesis holds only on a
neighbourhood of the parameter. Parallel `HasDerivAt`/`HasDerivWithinAt`/`deriv` lemmas provide
integrability, differentiation, and `C¹`/`C²`/successor regularity for scalar parameters in `𝕜`;
in particular, `integrable_of_hasDerivAt_of_compact_support`,
`integrable_of_hasDerivWithinAt_of_compact_support`, and
`integrable_of_hasDerivAt_of_hasDerivAt_of_compact_support` give scalar derivative integrability,
and `Convex.hasDerivWithinAt_integral_of_compact_support` differentiates scalar families within
any real-convex subset of `𝕜`.
Directional evaluation of the first derivative integral uses `ContinuousLinearMap.integral_apply`;
the corresponding two-direction formula uses `ContinuousLinearMap.integral_apply_apply`.
-/

public section

open MeasureTheory Set Function Filter Metric
open scoped Topology ContDiff

noncomputable section

namespace TauCeti

private theorem fderiv_eq_zero_of_support {𝕜 H E X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {U : Set H} {K : Set X}
    {D : H → X → E} {t₀ : H} {x : X} {f' : H →L[𝕜] E} (hU : U ∈ 𝓝 t₀)
    (hderiv : HasFDerivAt (D · x) f' t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) (hx : x ∉ K) : f' = 0 :=
  hderiv.eq_zero_of_eventually_const (Filter.Eventually.mono hU fun t ht ↦ hsupp t ht x hx)

private theorem fderivWithin_eq_zero_of_support {𝕜 H E X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s U : Set H} {K : Set X}
    {D : H → X → E} {t₀ : H} {x : X} {f' : H →L[𝕜] E} (ht₀ : t₀ ∈ s)
    (hsu : UniqueDiffWithinAt 𝕜 s t₀) (hU : U ∈ 𝓝[s] t₀)
    (hderiv : HasFDerivWithinAt (D · x) f' s t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) (hx : x ∉ K) : f' = 0 :=
  hsu.eq hderiv <| (hasFDerivWithinAt_const (0 : E) t₀ s).congr_of_eventuallyEq
    (Filter.Eventually.mono hU fun t ht ↦ hsupp t ht x hx)
    (hsupp t₀ (mem_of_mem_nhdsWithin ht₀ hU) x hx)

section Integrability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {𝕜 E : Type*}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {U : Set H} {K : Set X} {D : H → X → E} {D₁ : X → H →L[𝕜] E}

/-- A continuous parameter derivative of a family supported in a fixed compact set near the
parameter is integrable, without a completeness assumption on the codomain. -/
theorem integrable_of_hasFDerivAt_of_compact_support {t₀ : H} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD₁ : Continuous D₁)
    (hderiv : ∀ x, HasFDerivAt (D · x) (D₁ x) t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) : Integrable D₁ μ := by
  apply hD₁.integrable_of_support_subset_isCompact hK
  exact support_subset_iff'.2 fun x hx ↦
    fderiv_eq_zero_of_support hU (hderiv x) hsupp hx

/-- A continuous second parameter derivative of a family supported in a fixed compact set
near the parameter is integrable, without a completeness assumption on the codomain. -/
theorem integrable_of_hasFDerivAt_of_hasFDerivAt_of_compact_support
    {D₁ : H → X → H →L[𝕜] E} {D₂ : X → H →L[𝕜] H →L[𝕜] E}
    {t₀ : H} (hU : U ∈ 𝓝 t₀) (hK : IsCompact K) (hD₂ : Continuous D₂)
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ x, HasFDerivAt (D₁ · x) (D₂ x) t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) : Integrable D₂ μ := by
  apply integrable_of_hasFDerivAt_of_compact_support
    (interior_mem_nhds.2 hU) hK hD₂ hderiv₂
  exact fun t ht x hx ↦ fderiv_eq_zero_of_support (mem_interior_iff_mem_nhds.1 ht)
    (hderiv₁ t (interior_subset ht) x) hsupp hx

/-- A continuous scalar parameter derivative of a family supported in a fixed compact set
near the parameter is integrable, without a completeness assumption on the codomain. -/
theorem integrable_of_hasDerivAt_of_compact_support
    {U : Set 𝕜} {D : 𝕜 → X → E} {D₁ : X → E} {t₀ : 𝕜} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD₁ : Continuous D₁)
    (hderiv : ∀ x, HasDerivAt (D · x) (D₁ x) t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) : Integrable D₁ μ := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  exact e.integrable_comp_iff.1 (integrable_of_hasFDerivAt_of_compact_support
    (D₁ := fun x ↦ e (D₁ x)) hU hK (e.continuous.comp hD₁)
    (fun x ↦ (hderiv x).hasFDerivAt) hsupp)

/-- A continuous second scalar parameter derivative of a family supported in a fixed compact
set near the parameter is integrable, without a completeness assumption on the codomain. -/
theorem integrable_of_hasDerivAt_of_hasDerivAt_of_compact_support
    {U : Set 𝕜} {D D₁ : 𝕜 → X → E} {D₂ : X → E} {t₀ : 𝕜} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD₂ : Continuous D₂)
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ x, HasDerivAt (D₁ · x) (D₂ x) t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) : Integrable D₂ μ := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  let e₁ := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := 𝕜 →L[𝕜] E)
  have h := integrable_of_hasFDerivAt_of_hasFDerivAt_of_compact_support (μ := μ)
    (D₁ := fun t x ↦ e (D₁ t x)) (D₂ := fun x ↦ e₁ (e (D₂ x))) hU hK
    (e₁.continuous.comp (e.continuous.comp hD₂))
    (fun t ht x ↦ (hderiv₁ t ht x).hasFDerivAt)
    (fun x ↦ (e.hasFDerivAt.comp_hasDerivAt t₀ (hderiv₂ x)).hasFDerivAt) hsupp
  apply e.integrable_comp_iff.1
  simpa [e₁] using h.apply_continuousLinearMap (1 : 𝕜)

/-- A continuous within-set parameter derivative of a family supported in a fixed compact set
near the parameter within `s` is integrable, provided `s` has unique derivatives at `t₀`,
without a completeness assumption on the codomain. -/
theorem integrable_of_hasFDerivWithinAt_of_compact_support {s : Set H} {t₀ : H}
    (ht₀ : t₀ ∈ s) (hsu : UniqueDiffWithinAt 𝕜 s t₀) (hU : U ∈ 𝓝[s] t₀)
    (hK : IsCompact K) (hD₁ : Continuous D₁)
    (hderiv : ∀ x, HasFDerivWithinAt (D · x) (D₁ x) s t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) : Integrable D₁ μ := by
  apply hD₁.integrable_of_support_subset_isCompact hK
  exact support_subset_iff'.2 fun x hx ↦
    fderivWithin_eq_zero_of_support ht₀ hsu hU (hderiv x) hsupp hx

/-- A continuous within-set scalar parameter derivative of a family supported in a fixed
compact set near the parameter within `s` is integrable, provided `s` has unique derivatives
at `t₀`, without a completeness assumption on the codomain. -/
theorem integrable_of_hasDerivWithinAt_of_compact_support {s U : Set 𝕜}
    {D : 𝕜 → X → E} {D₁ : X → E} {t₀ : 𝕜} (ht₀ : t₀ ∈ s)
    (hsu : UniqueDiffWithinAt 𝕜 s t₀) (hU : U ∈ 𝓝[s] t₀) (hK : IsCompact K)
    (hD₁ : Continuous D₁) (hderiv : ∀ x, HasDerivWithinAt (D · x) (D₁ x) s t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) : Integrable D₁ μ := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  exact e.integrable_comp_iff.1 (integrable_of_hasFDerivWithinAt_of_compact_support
    (D₁ := fun x ↦ e (D₁ x)) ht₀ hsu hU hK (e.continuous.comp hD₁)
    (fun x ↦ (hderiv x).hasFDerivWithinAt) hsupp)

end Integrability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {U : Set H} {K : Set X} {D : H → X → E} {D₁ : H → X → H →L[𝕜] E}
  {D₂ : H → X → H →L[𝕜] H →L[𝕜] E}

/-- **Differentiation under the integral sign with a fixed compact support.** Suppose `D t`
is continuous and vanishes outside a fixed compact set for parameters in a neighbourhood of
`t₀`. If its parameter derivative `D₁` is jointly continuous there, then the integral has
derivative equal to the integral of `D₁ t₀`. -/
theorem hasFDerivAt_integral_of_compact_support {t₀ : H} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    HasFDerivAt (fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₁ t₀ x ∂μ) t₀ := by
  classical
  have ht₀ := mem_of_mem_nhds hU
  have ht₀i : t₀ ∈ interior U := mem_interior_iff_mem_nhds.2 hU
  have hUi : IsOpen (interior U ×ˢ (univ : Set X)) := isOpen_interior.prod isOpen_univ
  have hD₁i := hD₁.mono (prod_mono interior_subset (Subset.refl univ))
  obtain ⟨C, hC⟩ := hK.exists_eventually_norm_le hUi
    (fun x _ ↦ hD₁i.continuousAt (hUi.mem_nhds ⟨ht₀i, mem_univ x⟩))
    (fun x _ ↦ ⟨ht₀i, mem_univ x⟩)
  have hS : {t | t ∈ interior U ∧ ∀ x ∈ K, ‖D₁ t x‖ ≤ C} ∈ 𝓝 t₀ := by
    filter_upwards [interior_mem_nhds.2 hU, hC] with t ht hCt
    exact ⟨ht, fun x hx ↦ (hCt x hx).2⟩
  have hzero (t : H) (ht : t ∈ interior U) (x : X) (hx : x ∉ K) : D₁ t x = 0 :=
    fderiv_eq_zero_of_support (mem_interior_iff_mem_nhds.1 ht)
      (hderiv t (interior_subset ht) x) hsupp hx
  have hmeas : ∀ t ∈ U, StronglyMeasurable (D t) := fun t ht ↦
    (hD t ht).stronglyMeasurable_of_support_subset_isCompact hK
      (support_subset_iff'.2 (hsupp t ht))
  have hD₁t : Continuous (D₁ t₀) := continuousOn_univ.1 (hD₁.uncurry_left t₀ ht₀)
  have hbound : Integrable ((toMeasurable μ K).indicator fun _ ↦ max C 0) μ := by
    refine (integrableOn_const ?_).integrable_indicator (measurableSet_toMeasurable μ K)
    simpa only [measure_toMeasurable] using hK.measure_ne_top
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le hS
    ?_ ?_ (integrable_of_hasFDerivAt_of_compact_support hU hK hD₁t
      (hderiv t₀ ht₀) hsupp).aestronglyMeasurable
    (ae_of_all _ fun x t ht ↦ ?_) hbound
    (ae_of_all _ fun x t ht ↦ hderiv t (interior_subset ht.1) x)
  · filter_upwards [hU] with t ht using (hmeas t ht).aestronglyMeasurable
  · exact (hD t₀ ht₀).integrable_of_support_subset_isCompact hK
      (support_subset_iff'.2 (hsupp t₀ ht₀))
  · by_cases hx : x ∈ K
    · rw [indicator_of_mem (subset_toMeasurable μ K hx)]
      exact (ht.2 x hx).trans (le_max_left _ _)
    · rw [hzero t ht.1 x hx, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ le_max_right _ _) _

/-- If the integral of the parameter derivative is `C^n`, then a family of continuous
functions with fixed compact support and jointly continuous parameter derivative has a
`C^(n+1)` integral. -/
theorem contDiffOn_succ_integral_of_compact_support {n : ℕ∞} (hU : IsOpen U)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0)
    (hI₁ : ContDiffOn 𝕜 n (fun t ↦ ∫ x, D₁ t x ∂μ) U) :
    ContDiffOn 𝕜 ((n : ℕ∞ω) + 1) (fun t ↦ ∫ x, D t x ∂μ) U := by
  have h₁ := fun (t : H) (ht : t ∈ U) ↦
    hasFDerivAt_integral_of_compact_support (μ := μ) (hU.mem_nhds ht) hK hD hD₁ hderiv hsupp
  exact (contDiffOn_succ_iff_fderiv_of_isOpen hU).2
    ⟨fun t ht ↦ (h₁ t ht).differentiableAt.differentiableWithinAt, by simp,
      hI₁.congr fun t ht ↦ (h₁ t ht).fderiv⟩

/-- A family of continuous functions with fixed compact support and jointly continuous
parameter derivative has a `C¹` integral on its open parameter domain. -/
theorem contDiffOn_one_integral_of_compact_support (hU : IsOpen U) (hK : IsCompact K)
    (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContDiffOn 𝕜 1 (fun t ↦ ∫ x, D t x ∂μ) U := by
  apply contDiffOn_succ_integral_of_compact_support (n := 0) hU hK hD hD₁ hderiv hsupp
  refine contDiffOn_zero.2 (continuousOn_integral_of_compact_support hK hD₁ ?_)
  exact fun t x ht hx ↦ fderiv_eq_zero_of_support (hU.mem_nhds ht) (hderiv t ht x) hsupp hx

/-- **Second differentiation under the integral sign with a fixed compact support.**
For continuous `D t` with fixed compact support near `t₀`, jointly continuous first and second
parameter derivatives can both be integrated to compute the derivative of the Fréchet
derivative of the integral. -/
theorem hasFDerivAt_fderiv_integral_of_compact_support {t₀ : H} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ)) (hD₂ : ContinuousOn (uncurry D₂) (U ×ˢ univ))
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ t ∈ U, ∀ x, HasFDerivAt (D₁ · x) (D₂ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    HasFDerivAt (fderiv 𝕜 fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₂ t₀ x ∂μ) t₀ := by
  have hUi : interior U ∈ 𝓝 t₀ := interior_mem_nhds.2 hU
  have hsupp₁ : ∀ t ∈ interior U, ∀ x ∉ K, D₁ t x = 0 := fun t ht x hx ↦
    fderiv_eq_zero_of_support (mem_interior_iff_mem_nhds.1 ht)
      (hderiv₁ t (interior_subset ht) x) hsupp hx
  have h₂ := hasFDerivAt_integral_of_compact_support (μ := μ) hUi hK
    (fun t ht ↦ continuousOn_univ.1 (hD₁.uncurry_left t (interior_subset ht)))
    (hD₂.mono (prod_mono interior_subset (Subset.refl univ)))
    (fun t ht ↦ hderiv₂ t (interior_subset ht)) hsupp₁
  refine h₂.congr_of_eventuallyEq ?_
  filter_upwards [hUi] with t ht
  exact (hasFDerivAt_integral_of_compact_support
    (mem_interior_iff_mem_nhds.1 ht) hK hD hD₁ hderiv₁ hsupp).fderiv

/-- **`C²` parametric integrals with a fixed compact support.** A family of continuous
functions with fixed compact support and jointly continuous first and second parameter
derivatives has a `C²` integral on its open parameter domain. -/
theorem contDiffOn_two_integral_of_compact_support (hU : IsOpen U) (hK : IsCompact K)
    (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ)) (hD₂ : ContinuousOn (uncurry D₂) (U ×ˢ univ))
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ t ∈ U, ∀ x, HasFDerivAt (D₁ · x) (D₂ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContDiffOn 𝕜 2 (fun t ↦ ∫ x, D t x ∂μ) U := by
  have hsupp₁ : ∀ t ∈ U, ∀ x ∉ K, D₁ t x = 0 := fun t ht x hx ↦
    fderiv_eq_zero_of_support (hU.mem_nhds ht) (hderiv₁ t ht x) hsupp hx
  exact contDiffOn_succ_integral_of_compact_support (n := 1) hU hK hD hD₁ hderiv₁ hsupp
    (contDiffOn_one_integral_of_compact_support hU hK
      (fun t ht ↦ continuousOn_univ.1 (hD₁.uncurry_left t ht)) hD₂ hderiv₂ hsupp₁)

section Scalar

variable {U : Set 𝕜} {D D₁ D₂ : 𝕜 → X → E}

/-- A scalar parameter derivative of a continuous family with fixed compact support and a
jointly continuous parameter derivative can be integrated to differentiate the integral. -/
theorem hasDerivAt_integral_of_compact_support {t₀ : 𝕜} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    HasDerivAt (fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₁ t₀ x ∂μ) t₀ := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  have h := hasFDerivAt_integral_of_compact_support (μ := μ)
    (D₁ := fun t x ↦ e (D₁ t x)) hU hK hD
    (e.continuous.comp_continuousOn hD₁) (fun t ht x ↦ (hderiv t ht x).hasFDerivAt) hsupp
  rw [e.integral_comp_comm (D₁ t₀)] at h
  exact hasDerivAt_iff_hasFDerivAt.2 h

/-- If the integral of the scalar parameter derivative is `C^n`, then a continuous family
with fixed compact support and jointly continuous derivative has a `C^(n+1)` integral. -/
theorem contDiffOn_succ_integral_of_hasDerivAt_of_compact_support {n : ℕ∞}
    (hU : IsOpen U) (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0)
    (hI₁ : ContDiffOn 𝕜 n (fun t ↦ ∫ x, D₁ t x ∂μ) U) :
    ContDiffOn 𝕜 ((n : ℕ∞ω) + 1) (fun t ↦ ∫ x, D t x ∂μ) U := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  apply contDiffOn_succ_integral_of_compact_support (D₁ := fun t x ↦ e (D₁ t x))
    hU hK hD (e.continuous.comp_continuousOn hD₁)
    (fun t ht x ↦ (hderiv t ht x).hasFDerivAt) hsupp
  simp_rw [e.integral_comp_comm]
  exact e.contDiff.comp_contDiffOn hI₁

/-- A continuous family with fixed compact support and jointly continuous scalar parameter
derivative has a `C¹` integral on its open parameter domain. -/
theorem contDiffOn_one_integral_of_hasDerivAt_of_compact_support
    (hU : IsOpen U) (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContDiffOn 𝕜 1 (fun t ↦ ∫ x, D t x ∂μ) U := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  exact contDiffOn_one_integral_of_compact_support (D₁ := fun t x ↦ e (D₁ t x))
    hU hK hD (e.continuous.comp_continuousOn hD₁)
    (fun t ht x ↦ (hderiv t ht x).hasFDerivAt) hsupp

/-- A continuous family with fixed compact support and jointly continuous first and second
scalar parameter derivatives has a `C²` integral on its open parameter domain. -/
theorem contDiffOn_two_integral_of_hasDerivAt_of_compact_support
    (hU : IsOpen U) (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ)) (hD₂ : ContinuousOn (uncurry D₂) (U ×ˢ univ))
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ t ∈ U, ∀ x, HasDerivAt (D₁ · x) (D₂ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContDiffOn 𝕜 2 (fun t ↦ ∫ x, D t x ∂μ) U := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  let e₁ := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := 𝕜 →L[𝕜] E)
  exact contDiffOn_two_integral_of_compact_support
    (D₁ := fun t x ↦ e (D₁ t x)) (D₂ := fun t x ↦ e₁ (e (D₂ t x))) hU hK hD
    (e.continuous.comp_continuousOn hD₁)
    (e₁.continuous.comp_continuousOn (e.continuous.comp_continuousOn hD₂))
    (fun t ht x ↦ (hderiv₁ t ht x).hasFDerivAt)
    (fun t ht x ↦ (e.hasFDerivAt.comp_hasDerivAt t (hderiv₂ t ht x)).hasFDerivAt) hsupp

/-- With a scalar parameter, jointly continuous first and second derivatives of a continuous
family with fixed compact support near `t₀` can both be integrated to compute the derivative
of the derivative of the integral. -/
theorem hasDerivAt_deriv_integral_of_compact_support {t₀ : 𝕜} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ)) (hD₂ : ContinuousOn (uncurry D₂) (U ×ˢ univ))
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ t ∈ U, ∀ x, HasDerivAt (D₁ · x) (D₂ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    HasDerivAt (deriv fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₂ t₀ x ∂μ) t₀ := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  let e₁ := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := 𝕜 →L[𝕜] E)
  have h := hasFDerivAt_fderiv_integral_of_compact_support (μ := μ)
    (D₁ := fun t x ↦ e (D₁ t x)) (D₂ := fun t x ↦ e₁ (e (D₂ t x))) hU hK hD
    (e.continuous.comp_continuousOn hD₁)
    (e₁.continuous.comp_continuousOn (e.continuous.comp_continuousOn hD₂))
    (fun t ht x ↦ (hderiv₁ t ht x).hasFDerivAt)
    (fun t ht x ↦ (e.hasFDerivAt.comp_hasDerivAt t (hderiv₂ t ht x)).hasFDerivAt) hsupp
  rw [ContinuousLinearEquiv.integral_comp_comm (𝕜 := 𝕜) (E := 𝕜 →L[𝕜] E)
    (F := 𝕜 →L[𝕜] 𝕜 →L[𝕜] E) e₁, e.integral_comp_comm] at h
  have h' := (e.symm.hasFDerivAt.comp t₀ h).hasDerivAt
  simpa [e, e₁, comp_def, fderiv_apply_one_eq_deriv] using h'

end Scalar

section Convex

/-- A real-convex subset `s` of a normed field `𝕜` that is not a singleton has unique `𝕜`-linear
derivatives at every point `t₀ ∈ s`: choosing `t₁ ∈ s` with `t₁ ≠ t₀` puts the nonzero scalar
`t₁ - t₀` into the `𝕜`-tangent cone at `t₀`, whose `𝕜`-span is therefore all of `𝕜`. -/
private theorem uniqueDiffWithinAt_of_convex_of_nontrivial {s : Set 𝕜} {t₀ : 𝕜}
    (hs : Convex ℝ s) (ht₀ : t₀ ∈ s) (hs' : s.Nontrivial) :
    UniqueDiffWithinAt 𝕜 s t₀ := by
  obtain ⟨t₁, ht₁, hne⟩ := hs'.exists_ne t₀
  have hmem : t₁ - t₀ ∈ tangentConeAt 𝕜 s t₀ :=
    tangentConeAt_mono_field
      (sub_mem_posTangentConeAt_of_openSegment_subset (hs.openSegment_subset ht₀ ht₁))
  have hspan : Submodule.span 𝕜 (tangentConeAt 𝕜 s t₀) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z = (z * (t₁ - t₀)⁻¹) • (t₁ - t₀) := by
      simp [smul_eq_mul, mul_assoc, inv_mul_cancel₀ (sub_ne_zero.2 hne)]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  exact (uniqueDiffWithinAt_iff 𝕜 s t₀).2 ⟨by simp [hspan], subset_closure ht₀⟩

/-- **Differentiation under the integral sign within a convex set, with compact support.**
Let `s` be convex in `H`, `t₀ ∈ s`, and `U ∈ 𝓝[s] t₀`. Suppose `D t` is continuous and vanishes
outside a compact set `K` for `t ∈ U`, `D₁` is jointly continuous on `U × univ` with `D₁ t₀ = 0`
outside `K`, and `D · x` has derivative `D₁ t x` within `s` at `t` for `t ∈ U` and `x ∈ K`.
Then `t ↦ ∫ x, D t x ∂μ` has derivative `∫ x, D₁ t₀ x ∂μ` within `s` at `t₀`, without any
unique-differentiability assumption on `s` or completeness assumption on `E`. -/
theorem _root_.Convex.hasFDerivWithinAt_integral_of_compact_support [NormedSpace ℝ H]
    {s : Set H} {t₀ : H} (hs : Convex ℝ s) (ht₀ : t₀ ∈ s) (hU : U ∈ 𝓝[s] t₀)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x ∈ K, HasFDerivWithinAt (D · x) (D₁ t x) s t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) (hsupp₁ : ∀ x ∉ K, D₁ t₀ x = 0) :
    HasFDerivWithinAt (fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₁ t₀ x ∂μ) s t₀ := by
  have ht₀U : t₀ ∈ U := mem_of_mem_nhdsWithin ht₀ hU
  have hint (t : H) (ht : t ∈ U) : Integrable (D t) μ :=
    (hD t ht).integrable_of_support_subset_isCompact hK (support_subset_iff'.2 (hsupp t ht))
  have hint₁ : Integrable (D₁ t₀) μ :=
    (continuousOn_univ.1 (hD₁.uncurry_left t₀ ht₀U)).integrable_of_support_subset_isCompact hK
      (support_subset_iff'.2 hsupp₁)
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set M := μ.real (toMeasurable μ K)
  have hM0 : 0 ≤ M := measureReal_nonneg
  set ε := c / (M + 1)
  have hε : 0 < ε := div_pos hc (by linarith)
  obtain ⟨v, hv, hvD⟩ := hK.mem_uniformity_of_prod
    (hD₁.mono (prod_mono Subset.rfl (subset_univ K))) ht₀U (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.mem_nhdsWithin_iff.1 (inter_mem hU (nhdsWithin_le_of_mem hU hv))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds t₀ hδ)]
    with t hts htδ
  have htU : t ∈ U := (hball ⟨htδ, hts⟩).1
  have hsδ : Convex ℝ (s ∩ Metric.ball t₀ δ) := hs.inter (convex_ball t₀ δ)
  have hbound_int : Integrable ((toMeasurable μ K).indicator fun _ ↦ ε * ‖t - t₀‖) μ := by
    refine (integrableOn_const ?_).integrable_indicator (measurableSet_toMeasurable μ K)
    simpa only [measure_toMeasurable] using hK.measure_ne_top
  have hdiff : (∫ x, D t x ∂μ) - (∫ x, D t₀ x ∂μ) - (∫ x, D₁ t₀ x ∂μ) (t - t₀) =
      ∫ x, (D t x - D t₀ x - D₁ t₀ x (t - t₀)) ∂μ := by
    have hsub : Integrable (fun x ↦ D t x - D t₀ x) μ := (hint t htU).sub (hint t₀ ht₀U)
    symm
    rw [integral_sub hsub (hint₁.apply_continuousLinearMap (t - t₀)),
      integral_sub (hint t htU) (hint t₀ ht₀U), ContinuousLinearMap.integral_apply hint₁ (t - t₀)]
  rw [hdiff]
  refine (norm_integral_le_of_norm_le hbound_int (ae_of_all _ fun x ↦ ?_)).trans ?_
  · by_cases hx : x ∈ K
    · rw [indicator_of_mem (subset_toMeasurable μ K hx)]
      exact hsδ.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fun z ↦ D z x)
        (f' := fun z ↦ D₁ z x)
        (fun z (hz : z ∈ s ∩ Metric.ball t₀ δ) ↦
          (hderiv z (hball ⟨hz.2, hz.1⟩).1 x hx).mono inter_subset_left)
        (fun z (hz : z ∈ s ∩ Metric.ball t₀ δ) ↦ by
          have hd : dist (D₁ z x) (D₁ t₀ x) < ε := hvD z (hball ⟨hz.2, hz.1⟩).2 x hx
          simpa only [dist_eq_norm] using hd.le)
        ⟨ht₀, Metric.mem_ball_self hδ⟩ ⟨hts, htδ⟩
    · simp only [hsupp t htU x hx, hsupp t₀ ht₀U x hx, hsupp₁ x hx, sub_self, zero_apply,
        norm_zero]
      exact indicator_nonneg (fun _ _ ↦ by positivity) x
  · rw [integral_indicator_const _ (measurableSet_toMeasurable μ K), smul_eq_mul, ← mul_assoc]
    gcongr
    calc M * ε ≤ (M + 1) * (c / (M + 1)) := by gcongr; linarith
      _ = c := mul_div_cancel₀ c (by linarith)

/-- **Differentiation under the integral sign within a convex set with unique derivatives.**
When `s` has unique derivatives at `t₀` and `D · x` is differentiable within `s` everywhere in
`X`, the vanishing of `D₁ t₀` outside `K` follows automatically from `hsupp`. -/
theorem _root_.Convex.hasFDerivWithinAt_integral_of_uniqueDiffWithinAt_of_compact_support
    [NormedSpace ℝ H] {s : Set H} {t₀ : H} (hs : Convex ℝ s) (ht₀ : t₀ ∈ s)
    (hsu : UniqueDiffWithinAt 𝕜 s t₀) (hU : U ∈ 𝓝[s] t₀) (hK : IsCompact K)
    (hD : ∀ t ∈ U, Continuous (D t)) (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasFDerivWithinAt (D · x) (D₁ t x) s t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    HasFDerivWithinAt (fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₁ t₀ x ∂μ) s t₀ :=
  hs.hasFDerivWithinAt_integral_of_compact_support ht₀ hU hK hD hD₁
    (fun t ht x _ ↦ hderiv t ht x) hsupp fun x hx ↦
      fderivWithin_eq_zero_of_support ht₀ hsu hU
        (hderiv t₀ (mem_of_mem_nhdsWithin ht₀ hU) x) hsupp hx

/-- **Scalar differentiation under the integral sign within a convex set, with differentiability
assumed only on the support.** -/
theorem _root_.Convex.hasDerivWithinAt_integral_of_compact_support_of_eq_zero
    {s U : Set 𝕜} {D D₁ : 𝕜 → X → E} {t₀ : 𝕜} (hs : Convex ℝ s) (ht₀ : t₀ ∈ s)
    (hU : U ∈ 𝓝[s] t₀) (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x ∈ K, HasDerivWithinAt (D · x) (D₁ t x) s t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) (hsupp₁ : ∀ x ∉ K, D₁ t₀ x = 0) :
    HasDerivWithinAt (fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₁ t₀ x ∂μ) s t₀ := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  have h := hs.hasFDerivWithinAt_integral_of_compact_support (μ := μ)
    (D₁ := fun t x ↦ e (D₁ t x)) ht₀ hU hK hD (e.continuous.comp_continuousOn hD₁)
    (fun t ht x hx ↦ (hderiv t ht x hx).hasFDerivWithinAt) hsupp
    (fun x hx ↦ by simp [hsupp₁ x hx])
  rw [e.integral_comp_comm (D₁ t₀)] at h
  exact hasDerivWithinAt_iff_hasFDerivWithinAt.2 h

/-- **Scalar differentiation under the integral sign within a convex set.** Let `s` be a
real-convex subset of `𝕜`, `t₀ ∈ s`, and `U ∈ 𝓝[s] t₀`. If `D t` is continuous and vanishes
outside `K` for `t ∈ U` and has jointly continuous scalar derivative `D₁` within `s`, then
`t ↦ ∫ x, D t x ∂μ` has scalar derivative `∫ x, D₁ t₀ x ∂μ` within `s` at `t₀`. Neither
unique differentiability of `s` nor completeness of `E` is needed: singleton `s` is handled
directly, and any nontrivial real-convex subset of `𝕜` has unique `𝕜`-linear derivatives. -/
theorem _root_.Convex.hasDerivWithinAt_integral_of_compact_support
    {s U : Set 𝕜} {D D₁ : 𝕜 → X → E} {t₀ : 𝕜} (hs : Convex ℝ s) (ht₀ : t₀ ∈ s)
    (hU : U ∈ 𝓝[s] t₀) (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivWithinAt (D · x) (D₁ t x) s t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    HasDerivWithinAt (fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₁ t₀ x ∂μ) s t₀ := by
  rcases s.eq_singleton_or_nontrivial ht₀ with rfl | hs'
  · simp [hasDerivWithinAt_iff_isLittleO]
  have hsu : UniqueDiffWithinAt 𝕜 s t₀ :=
    uniqueDiffWithinAt_of_convex_of_nontrivial hs ht₀ hs'
  exact hs.hasDerivWithinAt_integral_of_compact_support_of_eq_zero ht₀ hU hK hD hD₁
    (fun t ht x _ ↦ hderiv t ht x) hsupp fun x hx ↦ by
      have h0 := fderivWithin_eq_zero_of_support ht₀ hsu hU
        ((hderiv t₀ (mem_of_mem_nhdsWithin ht₀ hU) x).hasFDerivWithinAt) hsupp hx
      simpa using congr_arg (· (1 : 𝕜)) h0

end Convex

end TauCeti
