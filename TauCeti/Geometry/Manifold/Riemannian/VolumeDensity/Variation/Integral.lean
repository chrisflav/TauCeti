/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Variation.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric
import Mathlib.Topology.PartitionOfUnity
import TauCeti.Analysis.Calculus.ParametricIntegral.CompactSupport
import TauCeti.Topology.Instances.Matrix

/-!
# Differentiating Riemannian integrals along families of metrics

Let `g_τ` be a family of continuous Riemannian metrics on a `C¹` manifold `M` with parameter
derivative `h = ∂_τ g_τ` at `τ = t` within a convex set `s ⊆ ℝ`, and let `f_τ : M → F` be a
time-dependent family of vector-valued functions supported in a fixed compact set `K ⊆ M` (in
particular, any continuous family on a compact manifold). Because the chart volume density
`ρ_τ = √(det G_τ)` satisfies `∂_τ ρ = ½ tr_g(h) ρ` (`TauCeti.hasDerivWithinAt_chartVolumeDensity`),
integrals against the Riemannian volume measure `TauCeti.riemannianVolume` differentiate by

`∂_τ ∫ f_τ dV_{g_τ} = ∫ (∂_τ f + ½ tr_g(h) f) dV_g`.

No orientation and no boundaryless assumption are needed: a continuous partition of unity splits the
integral over finitely many chart domains covering `K`, and each piece is read directly on the
subspace `(extChartAt I α).target` against the pullback of coordinate Haar measure, avoiding any
discontinuous extension by zero across a manifold boundary or corner.

The metric-trace continuity hypothesis `htr_cont` is separated from the entrywise continuity lemma
`TauCeti.continuousOn_bilinFormTrace` so callers can discharge it either from local-frame entries
of a general bilinear variation `h`, directly from a conformal factor `μ` when `h = μ g`, or
directly from continuity of scalar curvature when `h = -2 Ric(g)` along a Ricci flow:

`∂_τ ∫ f_τ dV_{g_τ} = ∫ (∂_τ f - Scal(g) f) dV_g`.

Parallel theorems in the `TauCeti.WithMetric` namespace avoid installing varying `RiemannianBundle`
instances at the call site when the metrics are `ContMDiffRiemannianMetric`s.

## Main results

* `TauCeti.continuousOn_chartVolumeDensity`, `TauCeti.continuousOn_bilinFormTrace`: joint
  parameter-and-space continuity of the chart volume density and metric trace.
* `TauCeti.continuousOn_integral_riemannianVolume_of_compact_support`,
  `TauCeti.continuousOn_integral_riemannianVolume`: continuity of `p ↦ ∫ f_p dV_{g_p}` in a
  topological parameter `p`.
* `TauCeti.hasDerivWithinAt_integral_riemannianVolume_of_compact_support`,
  `TauCeti.hasDerivAt_integral_riemannianVolume_of_compact_support`,
  `TauCeti.hasDerivWithinAt_integral_riemannianVolume`,
  `TauCeti.hasDerivAt_integral_riemannianVolume`: differentiation of `τ ↦ ∫ f_τ dV_{g_τ}` along a
  metric variation `∂_τ g = h`.
* `TauCeti.hasDerivWithinAt_integral_riemannianVolume_of_conformal`,
  `TauCeti.hasDerivWithinAt_integral_riemannianVolume_of_ricciFlow`: specializations to conformal
  variations `∂_τ g = μ g` and to Ricci flow `∂_τ g = -2 Ric(g)`.
* `TauCeti.WithMetric.continuousOn_integral_riemannianVolume`,
  `TauCeti.WithMetric.hasDerivWithinAt_integral_riemannianVolume`,
  `TauCeti.WithMetric.hasDerivWithinAt_integral_riemannianVolume_of_ricciFlow`: metric-indexed copy
  forms without local `letI` instances.

## References

* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Section 2.3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 2.44.
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set Filter
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-! ### Joint continuity of chart Gram quantities and metric traces -/

section Continuity

variable [IsManifold I 1 M] {P : Type*} [TopologicalSpace P] {U : Set P}

/-- If a parameter-indexed family of continuous fiberwise bilinear forms on `T M` defines a
continuous bundle section on `U × (chartAt H α).source`, then its evaluations on every pair of
members of `chartLocalFrame α` are jointly continuous there. -/
theorem continuousOn_apply_chartLocalFrame_of_bundle
    {B : P → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} (α : M)
    (hB : ContinuousOn
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) q.2 (B q.1 q.2))
      (U ×ˢ (chartAt H α).source))
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : P × M ↦ B q.1 q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source) := by
  have : IsManifold I (0 + 1) M := by simpa using ‹IsManifold I 1 M›
  have hframe (k : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun q : P × M ↦ TotalSpace.mk' E q.2 (chartLocalFrame (I := I) α k q.2))
        (U ×ˢ (chartAt H α).source) :=
    ((contMDiffOn_chartLocalFrame (I := I) (n := 0) α k).continuousOn).comp
      continuous_snd.continuousOn fun _ hq ↦ by
        simpa only [TangentBundle.trivializationAt_baseSet] using hq.2
  have happ : ContinuousOn
      (fun q : P × M ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q.2
        (B q.1 q.2 (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2)))
      (U ×ˢ (chartAt H α).source) :=
    hB.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (hframe i) (hframe j)
  intro q hq
  have h := happ q hq
  simp only [FiberBundle.continuousWithinAt_totalSpace] at h
  exact h.2

/-- If the chart-frame inner products of a family of metrics `g_p` are jointly continuous on
`U × (chartAt H α).source`, so is the chart Gram matrix `chartGramMatrix α`. -/
theorem continuousOn_chartGramMatrix
    {g : P → RiemannianMetric (fun x : M ↦ TangentSpace I x)} (α : M)
    (hg : ∀ i j, ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source)) :
    ContinuousOn (fun q : P × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩
        chartGramMatrix (I := I) α q.2)
      (U ×ˢ (chartAt H α).source) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_matrix fun i j ↦ ?_
  refine (continuousOn_iff_continuous_domRestrict.1 (hg i j)).congr fun q ↦ ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1.1⟩
  exact (chartGramMatrix_apply (I := I) α q.1.2 i j).symm

/-- If the chart-frame inner products of a family of metrics `g_p` are jointly continuous on
`U × (chartAt H α).source`, so is the chart volume density `chartVolumeDensity α`. -/
theorem continuousOn_chartVolumeDensity
    {g : P → RiemannianMetric (fun x : M ↦ TangentSpace I x)} (α : M)
    (hg : ∀ i j, ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source)) :
    ContinuousOn (fun q : P × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩
        chartVolumeDensity (I := I) α q.2)
      (U ×ˢ (chartAt H α).source) := by
  refine (Real.continuous_sqrt.comp_continuousOn <|
    continuous_id.matrix_det.comp_continuousOn (continuousOn_chartGramMatrix α hg)).congr
    fun q _ ↦ ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩
  exact chartVolumeDensity_def (I := I) α q.2

/-- If the chart-frame inner products of a family of metrics `g_p` are jointly continuous on
`U × (chartAt H α).source`, so is every entry of `chartInvGramMatrix α`. -/
theorem continuousOn_chartInvGramMatrix_apply
    {g : P → RiemannianMetric (fun x : M ↦ TangentSpace I x)} (α : M)
    (hg : ∀ i j, ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : P × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩
        chartInvGramMatrix (I := I) α q.2 i j)
      (U ×ˢ (chartAt H α).source) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hG := continuousOn_iff_continuous_domRestrict.1 (continuousOn_chartGramMatrix α hg)
  refine continuous_iff_continuousAt.2 fun q ↦ ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1.1⟩
  have hq : q.1.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using q.2.2
  refine (hG.continuousAt.matrix_inv_apply (chartGramMatrix_det_pos α hq).ne' i j).congr ?_
  exact Filter.Eventually.of_forall fun r ↦ by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g r.1.1⟩
    exact congr_fun₂ (chartInvGramMatrix_def α r.1.2).symm i j

/-- If the chart-frame entries of both a metric family `g_p` and a bilinear-form family `h_p` are
jointly continuous on `U × (chartAt H α).source` for every chart `α`, then the metric trace
`tr_{g_p}(h_p)` is jointly continuous on `U × univ`. -/
theorem continuousOn_bilinFormTrace
    {g : P → RiemannianMetric (fun x : M ↦ TangentSpace I x)}
    {h : P → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)}
    (hg : ∀ α i j, ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hh : ∀ α i j, ContinuousOn (fun q : P × M ↦ h q.1 q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source)) :
    ContinuousOn (fun q : P × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩
        bilinFormTrace (h q.1 q.2))
      (U ×ˢ univ) := by
  intro q hq
  let α := q.2
  have hsum : ContinuousOn (fun r : P × M ↦ ∑ i, ∑ j,
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g r.1⟩;
        chartInvGramMatrix (I := I) α r.2 i j) *
        h r.1 r.2 (chartLocalFrame (I := I) α i r.2) (chartLocalFrame (I := I) α j r.2))
      (U ×ˢ (chartAt H α).source) :=
    continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
      (continuousOn_chartInvGramMatrix_apply α (hg α) i j).mul (hh α i j)
  have hcongr : EqOn (fun r : P × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g r.1⟩
        bilinFormTrace (h r.1 r.2))
      (fun r : P × M ↦ ∑ i, ∑ j,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g r.1⟩;
          chartInvGramMatrix (I := I) α r.2 i j) *
          h r.1 r.2 (chartLocalFrame (I := I) α i r.2) (chartLocalFrame (I := I) α j r.2))
      (U ×ˢ (chartAt H α).source) := fun r hr ↦ by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g r.1⟩
    exact bilinFormTrace_eq_sum_chartInvGramMatrix α hr.2 _
  have hnhds : U ×ˢ (chartAt H α).source ∈ 𝓝[U ×ˢ univ] q := by
    refine mem_nhdsWithin.2 ⟨univ ×ˢ (chartAt H α).source,
      isOpen_univ.prod (chartAt H α).open_source, ⟨trivial, mem_chart_source H α⟩, ?_⟩
    rintro r ⟨⟨_, hr₂⟩, hr₁, _⟩
    exact ⟨hr₁, hr₂⟩
  exact ((hsum.congr hcongr) q ⟨hq.1, mem_chart_source H α⟩).mono_of_mem_nhdsWithin hnhds

end Continuity

/-! ### Subspace coordinate measure on an extended chart target -/

section SubspaceMeasure

/-- Coordinate Haar measure pulled back to the subspace `(extChartAt I α).target`. Working on the
subspace avoids extending chart integrands by zero across a manifold boundary or corner. -/
private def targetHaarMeasure (α : M) : Measure (extChartAt I α).target :=
  (Module.finBasis ℝ E).addHaar.comap Subtype.val

private instance isFiniteMeasureOnCompacts_targetHaarMeasure (α : M) :
    IsFiniteMeasureOnCompacts (targetHaarMeasure (I := I) α) := by
  refine ⟨fun K hK ↦ ?_⟩
  have hsub : MeasurableEmbedding (Subtype.val : (extChartAt I α).target → E) :=
    MeasurableEmbedding.subtype_coe (measurableSet_extChartAt_target α)
  rw [targetHaarMeasure, hsub.comap_apply]
  exact (hK.image continuous_subtype_val).measure_lt_top

omit [FiniteDimensional ℝ E] in
/-- A compact subset of a chart source maps to a compact subset of the subspace
`(extChartAt I α).target`. -/
private theorem isCompact_preimage_image_extChartAt {α : M} {K : Set M} (hK : IsCompact K)
    (hK_src : K ⊆ (chartAt H α).source) :
    IsCompact (Subtype.val ⁻¹' (extChartAt I α '' K) : Set (extChartAt I α).target) := by
  have hsrc : K ⊆ (extChartAt I α).source := by rwa [extChartAt_source]
  have hKE : IsCompact (extChartAt I α '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt α).mono hsrc)
  have hsub : extChartAt I α '' K ⊆ (extChartAt I α).target :=
    (image_mono hsrc).trans (extChartAt I α).image_source_eq_target.subset
  rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hsub]
  exact hKE

omit [FiniteDimensional ℝ E] in
private theorem symm_mem_of_mem_preimage_image_extChartAt {α : M} {K : Set M}
    (hK_src : K ⊆ (chartAt H α).source) {z : (extChartAt I α).target}
    (hz : z ∈ (Subtype.val ⁻¹' (extChartAt I α '' K) : Set (extChartAt I α).target)) :
    (extChartAt I α).symm z ∈ K := by
  obtain ⟨x, hx, hxz⟩ := hz
  have hx' : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hK_src hx
  simpa only [← hxz, (extChartAt I α).left_inv hx'] using hx

omit [FiniteDimensional ℝ E] in
private theorem symm_notMem_of_notMem_preimage_image_extChartAt {α : M} {K : Set M}
    {z : (extChartAt I α).target}
    (hz : z ∉ (Subtype.val ⁻¹' (extChartAt I α '' K) : Set (extChartAt I α).target)) :
    (extChartAt I α).symm z ∉ K := fun hmem ↦
  hz (by simpa only [mem_preimage, (extChartAt I α).right_inv z.2] using
    mem_image_of_mem (extChartAt I α) hmem)

/-- For a function `φ` supported in `(chartAt H α).source`, its integral against
`riemannianVolume I M` equals the integral on `(extChartAt I α).target` against
`targetHaarMeasure α` weighted by `chartVolumeDensity α`. -/
private theorem integral_riemannianVolume_eq_targetHaarMeasure [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {α : M} {φ : M → F}
    (hφ : Function.support φ ⊆ (chartAt H α).source) :
    ∫ x, φ x ∂riemannianVolume I M =
      ∫ z : (extChartAt I α).target,
        chartVolumeDensity (I := I) α ((extChartAt I α).symm z) • φ ((extChartAt I α).symm z)
          ∂targetHaarMeasure (I := I) α := by
  have hsub : MeasurableEmbedding (Subtype.val : (extChartAt I α).target → E) :=
    MeasurableEmbedding.subtype_coe (measurableSet_extChartAt_target α)
  have himg : extChartAt I α '' (chartAt H α).source = (extChartAt I α).target := by
    rw [← extChartAt_source (I := I), PartialEquiv.image_source_eq_target]
  have hsupp : ∫ x, φ x ∂riemannianVolume I M =
      ∫ x in (chartAt H α).source, φ x ∂riemannianVolume I M := by
    rw [← setIntegral_univ, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
      (subset_univ (chartAt H α).source)]
    exact fun _ hx ↦ Function.notMem_support.mp fun hmem ↦ (notMem_of_mem_sdiff hx) (hφ hmem)
  rw [hsupp,
    setIntegral_riemannianVolume_of_subset Subset.rfl (chartAt H α).open_source.measurableSet φ,
    himg]
  have hmap : (targetHaarMeasure (I := I) α).map Subtype.val =
      (Module.finBasis ℝ E).addHaar.restrict (extChartAt I α).target := by
    simpa only [targetHaarMeasure, Subtype.range_coe] using
      hsub.map_comap (Module.finBasis ℝ E).addHaar
  rw [← hmap, hsub.integral_map]

private theorem integral_smul_eq_targetHaarMeasure [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    (g₀ : ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {α : M} {ψ : C(M, ℝ)}
    (hψ_src : tsupport ψ ⊆ (chartAt H α).source) (Φ : M → F) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle g₀;
      ∫ x, ψ x • Φ x ∂riemannianVolume I M) =
      ∫ z : (extChartAt I α).target,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
          chartVolumeDensity (I := I) α ((extChartAt I α).symm z) * ψ ((extChartAt I α).symm z)) •
          Φ ((extChartAt I α).symm z) ∂targetHaarMeasure (I := I) α := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g₀
  rw [integral_riemannianVolume_eq_targetHaarMeasure fun x hx ↦
    hψ_src (subset_tsupport ψ fun h0 ↦ hx (by simp [h0]))]
  exact integral_congr_ae (ae_of_all _ fun _ ↦ by simp [mul_smul])

/-- Joint continuity on `U × (extChartAt I α).target` of the chart volume density multiplied by a
cutoff `ψ` supported in `(chartAt H α).source`: outside `tsupport ψ`, `ψ` vanishes on a
neighbourhood, while near `tsupport ψ` the chart density is jointly continuous. -/
private theorem continuousOn_chartVolumeDensity_mul_cutoff [IsManifold I 1 M]
    {P : Type*} [TopologicalSpace P] {U : Set P}
    {g : P → RiemannianMetric (fun x : M ↦ TangentSpace I x)} {α : M} {ψ : C(M, ℝ)}
    (hψ_src : tsupport ψ ⊆ (chartAt H α).source)
    (hg_cont : ∀ i j, ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source)) :
    ContinuousOn
      (fun q : P × (extChartAt I α).target ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩
        chartVolumeDensity (I := I) α ((extChartAt I α).symm q.2) *
          ψ ((extChartAt I α).symm q.2))
      (U ×ˢ univ) := by
  let symmT : (extChartAt I α).target → M := fun z ↦ (extChartAt I α).symm z
  have hsymmT : Continuous symmT :=
    continuousOn_iff_continuous_domRestrict.1 (continuousOn_extChartAt_symm α)
  intro q hq
  by_cases hqz : symmT q.2 ∈ (chartAt H α).source
  · have hρ := (continuousOn_chartVolumeDensity (g := g) α hg_cont).comp
      (continuous_id.prodMap hsymmT).continuousOn
      (s := U ×ˢ (symmT ⁻¹' (chartAt H α).source)) fun r hr ↦ ⟨hr.1, hr.2⟩
    have hopen : IsOpen (symmT ⁻¹' (chartAt H α).source) :=
      (chartAt H α).open_source.preimage hsymmT
    have hnhds : U ×ˢ (symmT ⁻¹' (chartAt H α).source) ∈ 𝓝[U ×ˢ univ] q :=
      mem_nhdsWithin.2 ⟨univ ×ˢ (symmT ⁻¹' (chartAt H α).source), isOpen_univ.prod hopen,
        ⟨trivial, hqz⟩, fun _ hr ↦ ⟨hr.2.1, hr.1.2⟩⟩
    exact ((hρ.mul (ψ.continuous.comp (hsymmT.comp continuous_snd)).continuousOn) q
      ⟨hq.1, hqz⟩).mono_of_mem_nhdsWithin hnhds
  · have hcompl : IsOpen ((tsupport ψ)ᶜ) := (isClosed_tsupport ψ).isOpen_compl
    have hqz' : (extChartAt I α).symm q.2 ∈ (tsupport ψ)ᶜ := fun hmem ↦ hqz (hψ_src hmem)
    refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds ((isOpen_univ.prod (hcompl.preimage hsymmT)).mem_nhds
        ⟨trivial, hqz'⟩)] with r hr
      rw [image_eq_zero_of_notMem_tsupport hr.2, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hqz', mul_zero]

end SubspaceMeasure

/-! ### Partition-of-unity decomposition and parametric continuity of Riemannian integrals -/

section ParametricContinuity

variable [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Decompose a continuous function `Φ : M → F` vanishing outside `K` along a continuous partition
of unity summing to `1` on `K`. -/
private theorem integral_riemannianVolume_eq_sum_of_support_subset [LindelofSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {n : ℕ} {K : Set M} {ψ : Fin n → C(M, ℝ)} (hψ_sum : EqOn (∑ i, ψ i) 1 K)
    (hψ_comp : ∀ i, HasCompactSupport (ψ i)) {Φ : M → F} (hΦ_cont : Continuous Φ)
    (hΦ_supp : ∀ x ∉ K, Φ x = 0) :
    ∫ x, Φ x ∂riemannianVolume I M =
      ∑ i, ∫ x, ψ i x • Φ x ∂riemannianVolume I M := by
  have hpt (x : M) : Φ x = ∑ i, ψ i x • Φ x := by
    by_cases hx : x ∈ K
    · have h1 : ∑ i, ψ i x = 1 := by
        simpa only [ContinuousMap.coe_sum, Finset.sum_apply, Pi.one_apply] using hψ_sum hx
      rw [← Finset.sum_smul, h1, one_smul]
    · simp [hΦ_supp x hx]
  rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum]
  intro i _
  exact ((ψ i).continuous.smul hΦ_cont).integrable_of_hasCompactSupport ((hψ_comp i).smul_right)

/-- Single-chart parametric continuity for `p ↦ ∫ x, ψ x • f p x ∂V_{g p}` when `tsupport ψ` lies
inside `(chartAt H α).source`. -/
private theorem continuousOn_integral_riemannianVolume_of_tsupport_subset_source [LindelofSpace M]
    {P : Type*} [TopologicalSpace P] {U : Set P}
    (g : P → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {f : P → M → F} {α : M} {ψ : C(M, ℝ)} (hψ_comp : HasCompactSupport ψ)
    (hψ_src : tsupport ψ ⊆ (chartAt H α).source)
    (hg_cont : ∀ i j, ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ)) :
    ContinuousOn
      (fun p ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g p).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g p);
        ∫ x, ψ x • f p x ∂riemannianVolume I M)
      U := by
  let symmT : (extChartAt I α).target → M := fun z ↦ (extChartAt I α).symm z
  have hsymmT : Continuous symmT :=
    continuousOn_iff_continuous_domRestrict.1 (continuousOn_extChartAt_symm α)
  let K' : Set (extChartAt I α).target := Subtype.val ⁻¹' (extChartAt I α '' tsupport ψ)
  have hK' : IsCompact K' := isCompact_preimage_image_extChartAt hψ_comp hψ_src
  let D : P → (extChartAt I α).target → F := fun p z ↦
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g p).toRiemannianMetric⟩;
      chartVolumeDensity (I := I) α (symmT z) * ψ (symmT z)) • f p (symmT z)
  have hc := continuousOn_chartVolumeDensity_mul_cutoff (U := U)
    (g := fun p ↦ (g p).toRiemannianMetric) hψ_src hg_cont
  have hfc : ContinuousOn (fun q : P × (extChartAt I α).target ↦ f q.1 (symmT q.2)) (U ×ˢ univ) :=
    hf_cont.comp (continuous_id.prodMap hsymmT).continuousOn (s := U ×ˢ univ)
      fun q hq ↦ ⟨hq.1, trivial⟩
  have hD_supp (p : P) (z : (extChartAt I α).target) (_ : p ∈ U) (hz : z ∉ K') : D p z = 0 := by
    have h0 : ψ (symmT z) = 0 := image_eq_zero_of_notMem_tsupport
      (symm_notMem_of_notMem_preimage_image_extChartAt hz)
    simp [D, h0]
  exact (continuousOn_integral_of_compact_support (μ := targetHaarMeasure (I := I) α)
    hK' (hc.smul hfc) hD_supp).congr fun p _ ↦
    integral_smul_eq_targetHaarMeasure (g p) hψ_src (f p)

variable [T2Space M]

/-- **Parametric continuity of Riemannian integrals with compact support.** Let `g_p` be a family
of continuous Riemannian metrics on `M` whose chart-frame entries depend jointly continuously on
`(p, x)` on `U × (chartAt H α).source`, and let `f_p : M → F` be jointly continuous on `U × univ`
and vanish outside a fixed compact set `K` for `p ∈ U`. Then `p ↦ ∫ x, f_p x dV_{g_p}` is
continuous on `U`. -/
theorem continuousOn_integral_riemannianVolume_of_compact_support [LindelofSpace M]
    {P : Type*} [TopologicalSpace P] {U : Set P}
    (g : P → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {f : P → M → F} {K : Set M} (hK : IsCompact K)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf_supp : ∀ p ∈ U, ∀ x ∉ K, f p x = 0) :
    ContinuousOn
      (fun p ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g p).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g p);
        ∫ x, f p x ∂riemannianVolume I M)
      U := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨n, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hK
  obtain ⟨ψ, hψ_sub, hψ_sum, _, hψ_comp⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact (fun i ↦ (hu i).1) hK hcover
  have hsum_cont : ContinuousOn
      (fun p ↦ ∑ i,
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g p).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g p);
        ∫ x, ψ i x • f p x ∂riemannianVolume I M) U :=
    continuousOn_finsetSum _ fun i _ ↦
      continuousOn_integral_riemannianVolume_of_tsupport_subset_source g (hψ_comp i)
        ((hψ_sub i).trans (by rw [← extChartAt_source (I := I)]; exact (hu i).2.1))
        (hg_cont (α i)) hf_cont
  refine hsum_cont.congr fun p hp ↦ ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g p).toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle (g p)
  exact integral_riemannianVolume_eq_sum_of_support_subset (I := I) (Φ := f p) hψ_sum hψ_comp
    (hf_cont.comp_continuous (continuous_const.prodMk continuous_id) fun x ↦ ⟨hp, mem_univ x⟩)
    (hf_supp p hp)

/-- **Parametric continuity of Riemannian integrals on a compact manifold.** On a compact manifold
`M`, if the chart-frame entries of `g_p` are jointly continuous on `U × (chartAt H α).source` and
`f_p : M → F` is jointly continuous on `U × univ`, then `p ↦ ∫ x, f_p x dV_{g_p}` is continuous on
`U`. -/
theorem continuousOn_integral_riemannianVolume [CompactSpace M]
    {P : Type*} [TopologicalSpace P] {U : Set P}
    (g : P → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {f : P → M → F}
    (hg_cont : ∀ α i j, ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ)) :
    ContinuousOn
      (fun p ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g p).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g p);
        ∫ x, f p x ∂riemannianVolume I M)
      U :=
  continuousOn_integral_riemannianVolume_of_compact_support g isCompact_univ hg_cont hf_cont
    fun _ _ _ hx ↦ (hx (mem_univ _)).elim

end ParametricContinuity

/-! ### Differentiating Riemannian integrals along metric families -/

section IntegralVariation

variable [IsManifold I 1 M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s U : Set ℝ} {t : ℝ}

omit [T2Space M] in
/-- Single-chart differentiation under the integral sign for `τ ↦ ∫ x, ψ x • f τ x ∂V_{g τ}` when
`tsupport ψ ⊆ (chartAt H α).source` and `f τ` vanishes outside `K`. -/
private theorem hasDerivWithinAt_integral_riemannianVolume_of_tsupport_subset_source
    [LindelofSpace M]
    (g : ℝ → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)}
    {f f' : ℝ → M → F} {K : Set M} {α : M} {ψ : C(M, ℝ)}
    (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t) (hK : IsCompact K)
    (hψ_src : tsupport ψ ⊆ (chartAt H α).source)
    (hg_cont : ∀ i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x ∈ K, ∀ v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w) (h τ x v w) s τ)
    (htr_cont : ContinuousOn (fun q : ℝ × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
        bilinFormTrace (h q.1 q.2)) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x ∈ K, HasDerivWithinAt (fun τ' ↦ f τ' x) (f' τ x) s τ)
    (hf_supp : ∀ τ ∈ U, ∀ x ∉ K, f τ x = 0)
    (hf'_supp : ∀ x ∉ K, f' t x = 0) :
    HasDerivWithinAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        ∫ x, ψ x • f τ x ∂riemannianVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t);
        ∫ x, ψ x • (f' t x + (2⁻¹ * bilinFormTrace (h t x)) • f t x) ∂riemannianVolume I M)
      s t := by
  let symmT : (extChartAt I α).target → M := fun z ↦ (extChartAt I α).symm z
  have hsymmT : Continuous symmT :=
    continuousOn_iff_continuous_domRestrict.1 (continuousOn_extChartAt_symm α)
  let c : ℝ → (extChartAt I α).target → ℝ := fun τ z ↦
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
    chartVolumeDensity (I := I) α (symmT z) * ψ (symmT z)
  have hc_cont : ContinuousOn (Function.uncurry c) (U ×ˢ univ) :=
    continuousOn_chartVolumeDensity_mul_cutoff (U := U)
      (g := fun τ ↦ (g τ).toRiemannianMetric) hψ_src hg_cont
  let K₀ : Set M := K ∩ tsupport ψ
  let K' : Set (extChartAt I α).target := Subtype.val ⁻¹' (extChartAt I α '' K₀)
  have hK' : IsCompact K' := isCompact_preimage_image_extChartAt
    (hK.inter_right (isClosed_tsupport ψ)) (inter_subset_right.trans hψ_src)
  let D : ℝ → (extChartAt I α).target → F := fun τ z ↦ c τ z • f τ (symmT z)
  let D₁ : ℝ → (extChartAt I α).target → F := fun τ z ↦
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
    c τ z • (f' τ (symmT z) + (2⁻¹ * bilinFormTrace (h τ (symmT z))) • f τ (symmT z))
  have hmap : MapsTo (Prod.map id symmT) (U ×ˢ univ) (U ×ˢ univ) := fun _ hr ↦ ⟨hr.1, trivial⟩
  have hD₁_cont : ContinuousOn (Function.uncurry D₁) (U ×ˢ univ) :=
    hc_cont.smul <| (hf'_cont.comp (continuous_id.prodMap hsymmT).continuousOn hmap).add <|
      ((continuousOn_const (c := (2⁻¹ : ℝ))).mul
        (htr_cont.comp (continuous_id.prodMap hsymmT).continuousOn hmap)).smul
        (hf_cont.comp (continuous_id.prodMap hsymmT).continuousOn hmap)
  have hderiv (τ : ℝ) (hτ : τ ∈ U) (z : (extChartAt I α).target) (hz : z ∈ K') :
      HasDerivWithinAt (D · z) (D₁ τ z) s τ := by
    have hzK₀ : symmT z ∈ K₀ :=
      symm_mem_of_mem_preimage_image_extChartAt (inter_subset_right.trans hψ_src) hz
    have hc_d := (hasDerivWithinAt_chartVolumeDensity (g := fun τ' ↦ (g τ').toRiemannianMetric) α
      (hψ_src hzK₀.2) (hg_deriv τ hτ (symmT z) hzK₀.1)).mul_const (ψ (symmT z))
    refine (hc_d.smul (hf_deriv τ hτ (symmT z) hzK₀.1)).congr_deriv ?_
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
    dsimp only [D₁, c]
    rw [smul_add, smul_smul]
    congr 2
    ring
  have hzero (z : (extChartAt I α).target) (hz : z ∉ K') :
      symmT z ∉ K ∨ ψ (symmT z) = 0 :=
    (Classical.em (symmT z ∈ K)).elim (fun hzK ↦ Or.inr (image_eq_zero_of_notMem_tsupport
      fun hψ ↦ symm_notMem_of_notMem_preimage_image_extChartAt hz ⟨hzK, hψ⟩)) Or.inl
  have hsupp (τ : ℝ) (hτ : τ ∈ U) (z : (extChartAt I α).target) (hz : z ∉ K') : D τ z = 0 :=
    (hzero z hz).elim (fun h ↦ by simp [D, hf_supp τ hτ _ h]) fun h ↦ by simp [D, c, h]
  have hsupp₁ (z : (extChartAt I α).target) (hz : z ∉ K') : D₁ t z = 0 :=
    (hzero z hz).elim
      (fun h ↦ by simp [D₁, hf_supp t (mem_of_mem_nhdsWithin ht hU) _ h, hf'_supp _ h])
      fun h ↦ by simp [D₁, c, h]
  have hD_cont (τ : ℝ) (hτ : τ ∈ U) : Continuous (D τ) :=
    (hc_cont.smul (hf_cont.comp (continuous_id.prodMap hsymmT).continuousOn hmap)).comp_continuous
      (continuous_const.prodMk continuous_id) fun z ↦ ⟨hτ, mem_univ z⟩
  have hmain := hs.hasDerivWithinAt_integral_of_compact_support_of_eq_zero
    (μ := targetHaarMeasure (I := I) α) ht hU hK' hD_cont hD₁_cont hderiv hsupp hsupp₁
  simpa only [integral_smul_eq_targetHaarMeasure _ hψ_src] using hmain

/-- **Differentiating a Riemannian integral with compact support along a metric family.**
Let `s ⊆ ℝ` be convex with `t ∈ s` and `U ∈ 𝓝[s] t`. Suppose the continuous metrics `g_τ` have
jointly continuous chart-frame entries on `U × (chartAt H α).source` and within-`s` derivative
`h_τ` on `K`, with `tr_{g_τ}(h_τ)` jointly continuous on `U × univ`, and let `f_τ : M → F` vanish
outside the compact set `K` for `τ ∈ U` with jointly continuous `f` and within-`s` parameter
derivative `f'`. Then

`∂_τ ∫ x, f_τ x dV_{g_τ} = ∫ x, (f'_t x + (½ tr_{g_t}(h_t x)) • f_t x) dV_{g_t}`

within `s` at `t`. -/
theorem hasDerivWithinAt_integral_riemannianVolume_of_compact_support [LindelofSpace M]
    (g : ℝ → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)}
    {f f' : ℝ → M → F} {K : Set M}
    (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t) (hK : IsCompact K)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x ∈ K, ∀ v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w) (h τ x v w) s τ)
    (htr_cont : ContinuousOn (fun q : ℝ × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
        bilinFormTrace (h q.1 q.2)) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x, HasDerivWithinAt (fun τ' ↦ f τ' x) (f' τ x) s τ)
    (hf_supp : ∀ τ ∈ U, ∀ x ∉ K, f τ x = 0) :
    HasDerivWithinAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        ∫ x, f τ x ∂riemannianVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t);
        ∫ x, (f' t x + (2⁻¹ * bilinFormTrace (h t x)) • f t x) ∂riemannianVolume I M)
      s t := by
  rcases s.eq_singleton_or_nontrivial ht with rfl | hs'
  · simp [hasDerivWithinAt_iff_isLittleO]
  have htU : t ∈ U := mem_of_mem_nhdsWithin ht hU
  have hsu : UniqueDiffWithinAt ℝ s t :=
    uniqueDiffOn_convex hs (hs.nontrivial_iff_nonempty_interior.1 hs') t ht
  have hf'_supp (x : M) (hx : x ∉ K) : f' t x = 0 := by
    have h0 : HasDerivWithinAt (fun τ ↦ f τ x) 0 s t :=
      (hasDerivWithinAt_const t s (0 : F)).congr_of_eventuallyEq
        (Filter.Eventually.mono hU fun τ hτ ↦ hf_supp τ hτ x hx) (hf_supp t htU x hx)
    rw [← (hf_deriv t htU x).derivWithin hsu, h0.derivWithin hsu]
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨n, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hK
  obtain ⟨ψ, hψ_sub, hψ_sum, _, hψ_comp⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact (fun i ↦ (hu i).1) hK hcover
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ ↦
    hasDerivWithinAt_integral_riemannianVolume_of_tsupport_subset_source g hs ht hU hK
      ((hψ_sub i).trans (by rw [← extChartAt_source (I := I)]; exact (hu i).2.1))
      (hg_cont (α i)) hg_deriv htr_cont hf_cont hf'_cont (fun τ hτ x _ ↦ hf_deriv τ hτ x)
      hf_supp hf'_supp
  have hRHS : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle (g t);
      ∫ x, (f' t x + (2⁻¹ * bilinFormTrace (h t x)) • f t x) ∂riemannianVolume I M) =
      ∑ i, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t);
        ∫ x, ψ i x • (f' t x + (2⁻¹ * bilinFormTrace (h t x)) • f t x) ∂riemannianVolume I M) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      instIsContinuousRiemannianBundle (g t)
    refine integral_riemannianVolume_eq_sum_of_support_subset (I := I) hψ_sum hψ_comp ?_
      fun x hx ↦ by simp [hf_supp t htU x hx, hf'_supp x hx]
    exact (hf'_cont.comp_continuous (continuous_const.prodMk continuous_id)
      fun x ↦ ⟨htU, mem_univ x⟩).add (((continuous_const (y := (2⁻¹ : ℝ))).mul
        (htr_cont.comp_continuous (continuous_const.prodMk continuous_id)
          fun x ↦ ⟨htU, mem_univ x⟩)).smul
        (hf_cont.comp_continuous (continuous_const.prodMk continuous_id) fun x ↦ ⟨htU, mem_univ x⟩))
  have hLHS (τ : ℝ) (hτ : τ ∈ U) :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        ∫ x, f τ x ∂riemannianVolume I M) =
      ∑ i, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        ∫ x, ψ i x • f τ x ∂riemannianVolume I M) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      instIsContinuousRiemannianBundle (g τ)
    exact (integral_riemannianVolume_eq_sum_of_support_subset (I := I) (Φ := f τ) hψ_sum hψ_comp
      (hf_cont.comp_continuous (continuous_const.prodMk continuous_id) fun x ↦ ⟨hτ, mem_univ x⟩)
      (hf_supp τ hτ))
  rw [hRHS]
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.mono hU hLHS) (hLHS t htU)

/-- **Two-sided derivative of a Riemannian integral with compact support along a metric family.** -/
theorem hasDerivAt_integral_riemannianVolume_of_compact_support [LindelofSpace M]
    (g : ℝ → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)}
    {f f' : ℝ → M → F} {K : Set M}
    (hU : U ∈ 𝓝 t) (hK : IsCompact K)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x ∈ K, ∀ v w,
      HasDerivAt (fun τ' ↦ (g τ').inner x v w) (h τ x v w) τ)
    (htr_cont : ContinuousOn (fun q : ℝ × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
        bilinFormTrace (h q.1 q.2)) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x, HasDerivAt (fun τ' ↦ f τ' x) (f' τ x) τ)
    (hf_supp : ∀ τ ∈ U, ∀ x ∉ K, f τ x = 0) :
    HasDerivAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        ∫ x, f τ x ∂riemannianVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t);
        ∫ x, (f' t x + (2⁻¹ * bilinFormTrace (h t x)) • f t x) ∂riemannianVolume I M)
      t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_integral_riemannianVolume_of_compact_support g convex_univ (mem_univ t)
      (by rwa [nhdsWithin_univ]) hK hg_cont
      (fun τ hτ x hx v w ↦ (hg_deriv τ hτ x hx v w).hasDerivWithinAt) htr_cont hf_cont hf'_cont
      (fun τ hτ x ↦ (hf_deriv τ hτ x).hasDerivWithinAt) hf_supp

/-- **Differentiating a Riemannian integral on a compact manifold along a metric family.**
On a compact manifold `M`, no compact-support hypothesis is needed:

`∂_τ ∫ x, f_τ x dV_{g_τ} = ∫ x, (f'_t x + (½ tr_{g_t}(h_t x)) • f_t x) dV_{g_t}`

within any convex parameter set `s ⊆ ℝ` at `t ∈ s`. -/
theorem hasDerivWithinAt_integral_riemannianVolume [CompactSpace M]
    (g : ℝ → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)}
    {f f' : ℝ → M → F}
    (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w) (h τ x v w) s τ)
    (htr_cont : ContinuousOn (fun q : ℝ × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
        bilinFormTrace (h q.1 q.2)) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x, HasDerivWithinAt (fun τ' ↦ f τ' x) (f' τ x) s τ) :
    HasDerivWithinAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        ∫ x, f τ x ∂riemannianVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t);
        ∫ x, (f' t x + (2⁻¹ * bilinFormTrace (h t x)) • f t x) ∂riemannianVolume I M)
      s t :=
  hasDerivWithinAt_integral_riemannianVolume_of_compact_support g hs ht hU isCompact_univ hg_cont
    (fun τ hτ x _ ↦ hg_deriv τ hτ x) htr_cont hf_cont hf'_cont hf_deriv
    fun _ _ _ hx ↦ (hx (mem_univ _)).elim

/-- **Two-sided derivative of a Riemannian integral on a compact manifold along a metric family.**
-/
theorem hasDerivAt_integral_riemannianVolume [CompactSpace M]
    (g : ℝ → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)}
    {f f' : ℝ → M → F} (hU : U ∈ 𝓝 t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivAt (fun τ' ↦ (g τ').inner x v w) (h τ x v w) τ)
    (htr_cont : ContinuousOn (fun q : ℝ × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
        bilinFormTrace (h q.1 q.2)) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x, HasDerivAt (fun τ' ↦ f τ' x) (f' τ x) τ) :
    HasDerivAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        ∫ x, f τ x ∂riemannianVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t);
        ∫ x, (f' t x + (2⁻¹ * bilinFormTrace (h t x)) • f t x) ∂riemannianVolume I M)
      t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_integral_riemannianVolume g convex_univ (mem_univ t)
      (by rwa [nhdsWithin_univ]) hg_cont (fun τ hτ x v w ↦ (hg_deriv τ hτ x v w).hasDerivWithinAt)
      htr_cont hf_cont hf'_cont fun τ hτ x ↦ (hf_deriv τ hτ x).hasDerivWithinAt

/-- **Differentiating the integral of a fixed function on a compact manifold.** For a fixed
continuous `f : M → F`, `∂_τ ∫ x, f x dV_{g_τ} = ∫ x, (½ tr_{g_t}(h_t x)) • f x dV_{g_t}`. -/
theorem hasDerivWithinAt_integral_riemannianVolume_const [CompactSpace M]
    (g : ℝ → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)}
    {f : M → F} (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w) (h τ x v w) s τ)
    (htr_cont : ContinuousOn (fun q : ℝ × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
        bilinFormTrace (h q.1 q.2)) (U ×ˢ univ))
    (hf : Continuous f) :
    HasDerivWithinAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        ∫ x, f x ∂riemannianVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t);
        ∫ x, (2⁻¹ * bilinFormTrace (h t x)) • f x ∂riemannianVolume I M)
      s t := by
  simpa only [zero_add] using hasDerivWithinAt_integral_riemannianVolume g (f := fun _ ↦ f)
    (f' := fun _ _ ↦ 0) hs ht hU hg_cont hg_deriv htr_cont (hf.comp continuous_snd).continuousOn
    continuousOn_const fun τ _ _ ↦ hasDerivWithinAt_const τ s (f _)

/-- **Riemannian integrals under a conformal variation.** On a compact manifold of real dimension
`n`, if `∂_τ g = μ g` within `s` with jointly continuous conformal rate `μ`, then

`∂_τ ∫ x, f_τ x dV_{g_τ} = ∫ x, (f'_t x + (n μ_t x / 2) • f_t x) dV_{g_t}`. -/
theorem hasDerivWithinAt_integral_riemannianVolume_of_conformal [CompactSpace M]
    (g : ℝ → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {μ : ℝ → M → ℝ} {f f' : ℝ → M → F}
    (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w) (μ τ x * (g τ).inner x v w) s τ)
    (hμ_cont : ContinuousOn (Function.uncurry μ) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x, HasDerivWithinAt (fun τ' ↦ f τ' x) (f' τ x) s τ) :
    HasDerivWithinAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        ∫ x, f τ x ∂riemannianVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t);
        ∫ x, (f' t x + ((Module.finrank ℝ E : ℝ) * μ t x / 2) • f t x) ∂riemannianVolume I M)
      s t := by
  let h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x) := fun τ x ↦
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
    μ τ x • innerₗ (TangentSpace I x)
  have htr (τ : ℝ) (x : M) :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        bilinFormTrace (h τ x)) = μ τ x * Module.finrank ℝ E := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
    -- `TangentSpace I x` is definitionally `E`, so their real dimensions agree.
    have hn : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := (rfl)
    rw [map_smul, bilinFormTrace_inner, smul_eq_mul, hn]
  have htr_cont : ContinuousOn (fun q : ℝ × M ↦
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
      bilinFormTrace (h q.1 q.2)) (U ×ˢ univ) :=
    (hμ_cont.mul (continuousOn_const (c := (Module.finrank ℝ E : ℝ)))).congr
      fun q _ ↦ htr q.1 q.2
  refine (hasDerivWithinAt_integral_riemannianVolume g (h := h) hs ht hU hg_cont hg_deriv
    htr_cont hf_cont hf'_cont hf_deriv).congr_deriv ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle (g t)
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [htr t x]
  congr 2
  ring

end IntegralVariation

/-! ### Specializations along a Ricci flow -/

section RicciFlow

variable [IsManifold I ∞ M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s U : Set ℝ} {t : ℝ}

/-- **Differentiating a compactly supported Riemannian integral along a Ricci flow.**
Under the Ricci flow equation `∂_τ g = -2 Ric(g)` within `s`, the trace of the variation is
`-2 Scal(g)`, so

`∂_τ ∫ x, f_τ x dV_{g_τ} = ∫ x, (f'_t x - Scal(g_t)(x) • f_t x) dV_{g_t}`. -/
theorem hasDerivWithinAt_integral_riemannianVolume_of_compact_support_of_ricciFlow
    [LindelofSpace M]
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f f' : ℝ → M → F} {K : Set M}
    (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t) (hK : IsCompact K)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x ∈ K, ∀ v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s τ)
    (hscal_cont : ContinuousOn (fun q : ℝ × M ↦ (g q.1).scalarCurvature q.2) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x, HasDerivWithinAt (fun τ' ↦ f τ' x) (f' τ x) s τ)
    (hf_supp : ∀ τ ∈ U, ∀ x ∉ K, f τ x = 0) :
    HasDerivWithinAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ).toContinuousRiemannianMetric;
        ∫ x, f τ x ∂riemannianVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t).toContinuousRiemannianMetric;
        ∫ x, (f' t x - (g t).scalarCurvature x • f t x) ∂riemannianVolume I M)
      s t := by
  let h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x) := fun τ x ↦
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
    (-2 : ℝ) • (CovariantDerivative.leviCivitaConnection I M).ricciTensor x
  have htr (τ : ℝ) (x : M) :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        bilinFormTrace (h τ x)) = -2 * (g τ).scalarCurvature x := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
    rw [map_smul, ContMDiffRiemannianMetric.scalarCurvature_def,
      CovariantDerivative.scalarCurvature_apply, smul_eq_mul]
  have htr_cont : ContinuousOn (fun q : ℝ × M ↦
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
      bilinFormTrace (h q.1 q.2)) (U ×ˢ univ) :=
    ((continuousOn_const (c := (-2 : ℝ))).mul hscal_cont).congr fun q _ ↦ htr q.1 q.2
  refine (hasDerivWithinAt_integral_riemannianVolume_of_compact_support
    (fun τ ↦ (g τ).toContinuousRiemannianMetric) (h := h) hs ht hU hK hg_cont hg_deriv
    htr_cont hf_cont hf'_cont hf_deriv hf_supp).congr_deriv ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle (g t).toContinuousRiemannianMetric
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  have htr_x : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g t).toContinuousRiemannianMetric.toRiemannianMetric⟩;
    bilinFormTrace (h t x)) = -2 * (g t).scalarCurvature x := htr t x
  rw [htr_x, show (2⁻¹ : ℝ) * (-2 * (g t).scalarCurvature x) = -(g t).scalarCurvature x by ring,
    neg_smul, sub_eq_add_neg]

/-- **Differentiating a Riemannian integral on a compact manifold along a Ricci flow.** -/
theorem hasDerivWithinAt_integral_riemannianVolume_of_ricciFlow [CompactSpace M]
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f f' : ℝ → M → F} (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s τ)
    (hscal_cont : ContinuousOn (fun q : ℝ × M ↦ (g q.1).scalarCurvature q.2) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x, HasDerivWithinAt (fun τ' ↦ f τ' x) (f' τ x) s τ) :
    HasDerivWithinAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ).toContinuousRiemannianMetric;
        ∫ x, f τ x ∂riemannianVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t).toContinuousRiemannianMetric;
        ∫ x, (f' t x - (g t).scalarCurvature x • f t x) ∂riemannianVolume I M)
      s t :=
  hasDerivWithinAt_integral_riemannianVolume_of_compact_support_of_ricciFlow g hs ht hU
    isCompact_univ hg_cont (fun τ hτ x _ ↦ hg_deriv τ hτ x) hscal_cont hf_cont hf'_cont hf_deriv
    fun _ _ _ hx ↦ (hx (mem_univ _)).elim

/-- **Two-sided derivative of a Riemannian integral on a compact manifold along a Ricci flow.** -/
theorem hasDerivAt_integral_riemannianVolume_of_ricciFlow [CompactSpace M]
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f f' : ℝ → M → F} (hU : U ∈ 𝓝 t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivAt (fun τ' ↦ (g τ').inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) τ)
    (hscal_cont : ContinuousOn (fun q : ℝ × M ↦ (g q.1).scalarCurvature q.2) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x, HasDerivAt (fun τ' ↦ f τ' x) (f' τ x) τ) :
    HasDerivAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ).toContinuousRiemannianMetric;
        ∫ x, f τ x ∂riemannianVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t).toContinuousRiemannianMetric;
        ∫ x, (f' t x - (g t).scalarCurvature x • f t x) ∂riemannianVolume I M)
      t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_integral_riemannianVolume_of_ricciFlow g convex_univ (mem_univ t)
      (by rwa [nhdsWithin_univ]) hg_cont (fun τ hτ x v w ↦ (hg_deriv τ hτ x v w).hasDerivWithinAt)
      hscal_cont hf_cont hf'_cont fun τ hτ x ↦ (hf_deriv τ hτ x).hasDerivWithinAt

end RicciFlow

/-! ### Metric-indexed copy (`WithMetric`) forms -/

namespace WithMetric

section General

variable {n : ℕ∞ω} [IsManifold I 1 M] [T2Space M] [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Parametric continuity of `p ↦ ∫ x, f_p x.ofWithMetric dV_{WithMetric (g_p)}` on a compact
manifold. -/
theorem continuousOn_integral_riemannianVolume
    {P : Type*} [TopologicalSpace P] {U : Set P}
    (g : P → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : P → M → F}
    (hg_cont : ∀ α i j, ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ)) :
    ContinuousOn
      (fun p ↦ ∫ x, f p x.ofWithMetric ∂riemannianVolume I (WithMetric (g p))) U := by
  borelize M
  exact (TauCeti.continuousOn_integral_riemannianVolume
    (fun p ↦ (g p).toContinuousRiemannianMetric) (f := f) hg_cont hf_cont).congr fun p _ ↦
      WithMetric.integral_comp_ofWithMetric (g p) (f p)

/-- Differentiating `τ ↦ ∫ x, f_τ x.ofWithMetric dV_{WithMetric (g_τ)}` on a compact manifold
within a convex parameter set `s`, without local `letI` instances in the integral expressions. -/
theorem hasDerivWithinAt_integral_riemannianVolume {s U : Set ℝ} {t : ℝ}
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)}
    {f f' : ℝ → M → F} (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w) (h τ x v w) s τ)
    (htr_cont : ContinuousOn (fun q : ℝ × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
        bilinFormTrace (h q.1 q.2)) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x, HasDerivWithinAt (fun τ' ↦ f τ' x) (f' τ x) s τ) :
    HasDerivWithinAt
      (fun τ ↦ ∫ x, f τ x.ofWithMetric ∂riemannianVolume I (WithMetric (g τ)))
      (∫ x, (f' t x.ofWithMetric +
          (2⁻¹ * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
              ⟨(g t).toRiemannianMetric⟩;
            bilinFormTrace (h t x.ofWithMetric))) • f t x.ofWithMetric)
        ∂riemannianVolume I (WithMetric (g t)))
      s t := by
  borelize M
  have hmain := TauCeti.hasDerivWithinAt_integral_riemannianVolume
    (fun τ ↦ (g τ).toContinuousRiemannianMetric) (h := h) (f := f) (f' := f') hs ht hU hg_cont
    hg_deriv htr_cont hf_cont hf'_cont hf_deriv
  exact (hmain.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ ↦ WithMetric.integral_comp_ofWithMetric (g τ) (f τ))
    (WithMetric.integral_comp_ofWithMetric (g t) (f t))).congr_deriv
    (WithMetric.integral_comp_ofWithMetric (g t) fun x ↦ f' t x +
      (2⁻¹ * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩;
        bilinFormTrace (h t x))) • f t x).symm

end General

section RicciFlow

variable [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s U : Set ℝ} {t : ℝ}

/-- Differentiating `τ ↦ ∫ x, f_τ x.ofWithMetric dV_{WithMetric (g_τ)}` along a Ricci flow on a
compact manifold:

`∂_τ ∫ f_τ dV_{g_τ} = ∫ (∂_τ f - Scal(g) f) dV_g`. -/
theorem hasDerivWithinAt_integral_riemannianVolume_of_ricciFlow
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f f' : ℝ → M → F} (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s τ)
    (hscal_cont : ContinuousOn (fun q : ℝ × M ↦ (g q.1).scalarCurvature q.2) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x, HasDerivWithinAt (fun τ' ↦ f τ' x) (f' τ x) s τ) :
    HasDerivWithinAt
      (fun τ ↦ ∫ x, f τ x.ofWithMetric ∂riemannianVolume I (WithMetric (g τ)))
      (∫ x, (f' t x.ofWithMetric - (g t).scalarCurvature x.ofWithMetric • f t x.ofWithMetric)
        ∂riemannianVolume I (WithMetric (g t)))
      s t := by
  borelize M
  have hmain := TauCeti.hasDerivWithinAt_integral_riemannianVolume_of_ricciFlow g (f := f)
    (f' := f') hs ht hU hg_cont hg_deriv hscal_cont hf_cont hf'_cont hf_deriv
  exact (hmain.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ ↦ WithMetric.integral_comp_ofWithMetric (g τ) (f τ))
    (WithMetric.integral_comp_ofWithMetric (g t) (f t))).congr_deriv
    (WithMetric.integral_comp_ofWithMetric (g t) fun x ↦
      f' t x - (g t).scalarCurvature x • f t x).symm

/-- Two-sided derivative of `τ ↦ ∫ x, f_τ x.ofWithMetric dV_{WithMetric (g_τ)}` along a Ricci flow
on a compact manifold. -/
theorem hasDerivAt_integral_riemannianVolume_of_ricciFlow
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f f' : ℝ → M → F} (hU : U ∈ 𝓝 t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivAt (fun τ' ↦ (g τ').inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) τ)
    (hscal_cont : ContinuousOn (fun q : ℝ × M ↦ (g q.1).scalarCurvature q.2) (U ×ˢ univ))
    (hf_cont : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf'_cont : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf_deriv : ∀ τ ∈ U, ∀ x, HasDerivAt (fun τ' ↦ f τ' x) (f' τ x) τ) :
    HasDerivAt
      (fun τ ↦ ∫ x, f τ x.ofWithMetric ∂riemannianVolume I (WithMetric (g τ)))
      (∫ x, (f' t x.ofWithMetric - (g t).scalarCurvature x.ofWithMetric • f t x.ofWithMetric)
        ∂riemannianVolume I (WithMetric (g t)))
      t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_integral_riemannianVolume_of_ricciFlow g convex_univ (mem_univ t)
      (by rwa [nhdsWithin_univ]) hg_cont (fun τ hτ x v w ↦ (hg_deriv τ hτ x v w).hasDerivWithinAt)
      hscal_cont hf_cont hf'_cont fun τ hτ x ↦ (hf_deriv τ hτ x).hasDerivWithinAt

end RicciFlow

end WithMetric

end TauCeti
