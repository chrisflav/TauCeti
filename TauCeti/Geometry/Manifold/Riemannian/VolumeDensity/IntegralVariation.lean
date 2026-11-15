/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Topology
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Variation
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Calculus.ParametricIntegral.CompactSupport

/-!
# Continuity and first variation of Riemannian volume integrals

Let `g_p` be a family of `C^n` Riemannian metrics on a Hausdorff `σ`-compact manifold `M` and
`f_p : M → F` a family of continuous vector-valued functions supported in a fixed compact set `K`.
Decomposing `f_p` along a continuous partition of unity subordinate to the preferred charts writes
`∫ f_p dV_{g_p}` as a finite sum of coordinate integrals over compact subsets of the model space,
weighted by the chart volume densities `TauCeti.chartVolumeDensity`. Because those compact
coordinate sets depend only on `K` and the partition of unity, parametric continuity and
differentiation of the manifold integral reduce directly to the compact-set Lebesgue theorems
`TauCeti.continuousOn_setIntegral_of_isCompact` and
`Convex.hasDerivWithinAt_setIntegral_of_continuousOn`.

Combining this reduction with the pointwise formula `TauCeti.hasDerivWithinAt_chartVolumeDensity`
gives the global transport formula

`∂_τ ∫ f_τ dV_{g_τ} = ∫ (∂_τ f_τ + ½ tr_{g_τ}(∂_τ g_τ) f_τ) dV_{g_τ}`

within any convex parameter set `s ⊆ ℝ` (including closed intervals `[a, b]` with one-sided
endpoint derivatives), together with the first variation of total volume on a compact manifold,

`∂_τ Vol(g_τ) = ½ ∫ tr_{g_τ}(∂_τ g_τ) dV_{g_τ}`,

its conformal specialization `(N / 2) ∫ μ dV_g` under `∂_τ g = μ g`, and the Ricci-flow volume
identity `∂_τ Vol(g_τ) = -∫ Scal(g_τ) dV_{g_τ}` along `∂_τ g = -2 Ric(g)`. On a compact
boundaryless smooth manifold, the same coordinate decomposition shows that
`g ↦ riemannianTotalVolume I (WithMetric g)` is continuous in every chart `C^k` topology
`Bundle.ContMDiffRiemannianMetric.chartCkTopology k`.

## Main results

* `TauCeti.continuousOn_integral_riemannianVolume`: parametric continuity of `p ↦ ∫ f_p dV_{g_p}`
  for families supported in a fixed compact set.
* `Bundle.ContMDiffRiemannianMetric.continuous_integral_riemannianVolume_chartCk`,
  `Bundle.ContMDiffRiemannianMetric.continuous_riemannianTotalVolume_chartCk`,
  `Bundle.ContMDiffRiemannianMetric.continuous_riemannianTotalVolume_chartC2`,
  `Bundle.ContMDiffRiemannianMetric.continuous_riemannianTotalVolume_chartCInfty`: continuity of
  Riemannian integrals and total volume in the chart `C^k`, `C^2`, and `C^∞` topologies.
* `TauCeti.hasDerivWithinAt_integral_riemannianVolume_of_hasDerivWithinAt_chartVolumeDensity`,
  `TauCeti.hasDerivWithinAt_integral_riemannianVolume`: differentiation under the integral sign
  against a varying Riemannian volume measure.
* `TauCeti.hasDerivWithinAt_riemannianTotalVolume`,
  `TauCeti.hasDerivAt_riemannianTotalVolume`,
  `TauCeti.hasDerivWithinAt_riemannianTotalVolume_of_conformal`,
  `TauCeti.hasDerivWithinAt_integral_riemannianVolume_of_ricciFlow`,
  `TauCeti.hasDerivWithinAt_riemannianTotalVolume_of_ricciFlow`: first variation of total volume
  for general, conformal, and Ricci-flow metric variations.

## References

* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Section 2.3 and Lemma 2.3.1.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K.
-/

public section

open Bundle Filter Function MeasureTheory Metric Riemannian.Tensor Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

section Helpers

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- Multiplying a continuous vector-valued function supported in a closed set `K` by a scalar
function continuous on `K` produces a globally continuous function. -/
private theorem continuous_smul_of_support_subset {X : Type*} [TopologicalSpace X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set X} (hK : IsClosed K)
    {ψ : X → ℝ} (hψ : ContinuousOn ψ K) {φ : X → F} (hφ : Continuous φ)
    (hsupp : support φ ⊆ K) :
    Continuous fun x ↦ ψ x • φ x := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  by_cases hx₀ : x₀ ∈ K
  · rw [ContinuousAt, show 𝓝 x₀ = 𝓝[K] x₀ ⊔ 𝓝[Kᶜ] x₀ by
      rw [← nhdsWithin_union, union_compl_self, nhdsWithin_univ], tendsto_sup]
    refine ⟨(hψ x₀ hx₀).smul hφ.continuousAt.continuousWithinAt, ?_⟩
    rcases (𝓝[Kᶜ] x₀).eq_or_neBot with hbot | hne
    · simp [hbot]
    · have hzero : ∀ᶠ x in 𝓝[Kᶜ] x₀, φ x = 0 :=
        eventually_nhdsWithin_of_forall fun x hx ↦ notMem_support.1 fun h ↦ hx (hsupp h)
      have hφ0 : φ x₀ = 0 := tendsto_nhds_unique
        (hφ.continuousAt.mono_left nhdsWithin_le_nhds)
        (tendsto_const_nhds.congr' (hzero.mono fun _ hx ↦ hx.symm))
      rw [hφ0, smul_zero]
      exact tendsto_const_nhds.congr' (hzero.mono fun _ hx ↦ by simp [hx])
  · have hzero : ∀ᶠ x in 𝓝 x₀, ψ x • φ x = 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds hx₀] with x hx
      rw [notMem_support.1 fun h ↦ hx (hsupp h), smul_zero]
    rw [ContinuousAt, notMem_support.1 fun h ↦ hx₀ (hsupp h), smul_zero]
    exact tendsto_const_nhds.congr' (hzero.mono fun _ hx ↦ hx.symm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Decomposes the Riemannian integral of a continuous function supported in a compact set `K`
along a partition of unity subordinate to the preferred chart sources. -/
private theorem integral_riemannianVolume_eq_sum_setIntegral [IsManifold I 1 M] [T2Space M]
    [SigmaCompactSpace M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
    {K : Set M} (hK : IsCompact K) (ρ : PartitionOfUnity M M)
    (hρ : ρ.IsSubordinate fun α : M ↦ (chartAt H α).source) {A : Finset M}
    (hA : ∀ α, (tsupport (ρ α) ∩ K).Nonempty → α ∈ A)
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {φ : M → F} (hφ : Continuous φ) (hsupp : support φ ⊆ K) :
    ∫ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric g) =
      ∑ α ∈ A, ∫ y in extChartAt I α '' (K ∩ tsupport (ρ α)),
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) •
          (ρ α ((extChartAt I α).symm y) • φ ((extChartAt I α).symm y))
          ∂(Module.finBasis ℝ E).addHaar := by
  borelize M
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have hsum (x : M) : φ x = ∑ α ∈ A, ρ α x • φ x := by
    by_cases hx : φ x = 0
    · simp [hx]
    · have hsub : ρ.finsupport x ⊆ A := fun α hα ↦
        hA α ⟨x, subset_tsupport _ (by simpa using hα), hsupp hx⟩
      rw [← Finset.sum_smul, ρ.sum_finsupport' (mem_univ x) hsub, one_smul]
  have hint (α : M) : Integrable (fun x ↦ ρ α x • φ x) (riemannianVolume I M) :=
    ((ρ α).continuous.smul hφ).integrable_of_hasCompactSupport
      (hK.of_isClosed_subset (isClosed_tsupport _)
        ((tsupport_smul_subset_right _ _).trans (closure_minimal hsupp hK.isClosed)))
  rw [WithMetric.integral_comp_ofWithMetric g φ,
    integral_congr_ae (Eventually.of_forall hsum),
    integral_finsetSum A fun α _ ↦ hint α]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  have hS : IsCompact (K ∩ tsupport (ρ α)) := hK.inter_right (isClosed_tsupport _)
  have hsub : K ∩ tsupport (ρ α) ⊆ (chartAt H α).source := inter_subset_right.trans (hρ α)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K ∩ tsupport (ρ α)) fun x hx ↦ by
    by_cases hxK : x ∈ K
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx ⟨hxK, h⟩, zero_smul]
    · rw [notMem_support.1 fun h ↦ hxK (hsupp h), smul_zero]]
  exact setIntegral_riemannianVolume_of_subset (I := I) hsub hS.isClosed.measurableSet
    (fun x ↦ ρ α x • φ x)

include I in
/-- Existence of a continuous partition of unity subordinate to the preferred chart sources on a
Hausdorff `σ`-compact charted space. -/
private theorem exists_partitionOfUnity_chartAt_source [T2Space M]
    [SigmaCompactSpace M] :
    ∃ ρ : PartitionOfUnity M M, ρ.IsSubordinate fun α : M ↦ (chartAt H α).source := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  exact PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun α : M ↦ (chartAt H α).source) (fun α ↦ (chartAt H α).open_source)
    fun x _ ↦ mem_iUnion.2 ⟨x, mem_chart_source H x⟩

/-- Joint continuity of the determinant of a matrix family from joint continuity of its entries. -/
private theorem continuousOn_matrix_det {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : X → Matrix ι ι ℝ} {s : Set X}
    (hA : ∀ i j, ContinuousOn (fun x ↦ A x i j) s) :
    ContinuousOn (fun x ↦ (A x).det) s := by
  have hexp : (fun x ↦ (A x).det) =
      fun x ↦ ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℝ) * ∏ i, A x (σ i) i := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  exact continuousOn_finsetSum Finset.univ fun σ _ ↦
    continuousOn_const.mul (continuousOn_finsetProd Finset.univ fun i _ ↦ hA (σ i) i)

/-- Joint continuity of the chart volume density from joint continuity of the metric coefficients in
the chart-local frame. -/
private theorem continuousOn_chartVolumeDensity_of_inner [IsManifold I 1 M]
    {P : Type*} [TopologicalSpace P] {s : Set P}
    {g : P → RiemannianMetric (fun x : M ↦ TangentSpace I x)} (α : M)
    (hg : ∀ i j, ContinuousOn
      (fun q : P × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source)) :
    ContinuousOn
      (fun q : P × M ↦ letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩;
        chartVolumeDensity (I := I) α q.2)
      (s ×ˢ (chartAt H α).source) := by
  classical
  refine (Real.continuous_sqrt.comp_continuousOn (continuousOn_matrix_det
      (A := fun q ↦ Matrix.of fun i j ↦
        (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      hg)).congr fun q _ ↦ ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩
  have hG : chartGramMatrix (I := I) α q.2 =
      Matrix.of fun i j ↦
        (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2) :=
    Matrix.ext fun i j ↦ chartGramMatrix_apply α q.2 i j
  rw [Function.comp_apply, chartVolumeDensity_def, hG]

/-- Joint continuity of the inverse chart Gram matrix entries from joint continuity of the metric
coefficients in the chart-local frame. -/
private theorem continuousOn_chartInvGramMatrix_of_inner [IsManifold I 1 M]
    {P : Type*} [TopologicalSpace P] {s : Set P}
    {g : P → RiemannianMetric (fun x : M ↦ TangentSpace I x)} (α : M)
    (hg : ∀ i j, ContinuousOn
      (fun q : P × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source))
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : P × M ↦ letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩;
        chartInvGramMatrix (I := I) α q.2 i j)
      (s ×ˢ (chartAt H α).source) := by
  classical
  let G : P × M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun q ↦ letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩;
      chartGramMatrix (I := I) α q.2
  have hg' (k l : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun q ↦ G q k l) (s ×ˢ (chartAt H α).source) :=
    (hg k l).congr fun q _ ↦ by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩
      exact chartGramMatrix_apply α q.2 k l
  have hdet : ContinuousOn (fun q ↦ (G q).det) (s ×ˢ (chartAt H α).source) :=
    continuousOn_matrix_det hg'
  have hadj : ContinuousOn (fun q ↦ (G q).adjugate i j) (s ×ˢ (chartAt H α).source) := by
    have hexp : (fun q ↦ (G q).adjugate i j) =
        fun q ↦ ((G q).updateRow j (Pi.single i (1 : ℝ))).det :=
      funext fun q ↦ Matrix.adjugate_apply _ _ _
    rw [hexp]
    refine continuousOn_matrix_det fun k l ↦ ?_
    by_cases hkj : k = j
    · subst k; simpa only [Matrix.updateRow_self] using continuousOn_const
    · simpa only [Matrix.updateRow_apply, hkj, ite_false] using hg' k l
  refine ((hdet.inv₀ ?_).mul hadj).congr fun q _ ↦ ?_
  · intro q hq
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩
    exact (chartGramMatrix_det_pos (I := I) α
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hq.2)).ne'
  · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩
    rw [chartInvGramMatrix_def, Matrix.inv_def]
    simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, Pi.mul_apply, Pi.inv_apply, G]

/-- Joint continuity of the metric trace `tr_{g_p}(h_p)` on `s ×ˢ K` from joint continuity of the
chart-frame coefficients of `g` and `h`. -/
private theorem continuousOn_bilinFormTrace_of_inner [IsManifold I 1 M]
    {P : Type*} [TopologicalSpace P] {s : Set P} {K : Set M}
    {g : P → RiemannianMetric (fun x : M ↦ TangentSpace I x)}
    {h : P → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)}
    (hg : ∀ α i j, ContinuousOn
      (fun q : P × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source))
    (hh : ∀ α i j, ContinuousOn
      (fun q : P × M ↦ h q.1 q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source)) :
    ContinuousOn
      (fun q : P × M ↦ letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩;
        bilinFormTrace (h q.1 q.2))
      (s ×ˢ K) := by
  intro ⟨p₀, x₀⟩ hpx₀
  have hchart : ContinuousOn
      (fun q : P × M ↦ ∑ i, ∑ j,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩;
          chartInvGramMatrix (I := I) x₀ q.2 i j) *
          h q.1 q.2 (chartLocalFrame (I := I) x₀ i q.2) (chartLocalFrame (I := I) x₀ j q.2))
      (s ×ˢ (chartAt H x₀).source) :=
    continuousOn_finsetSum Finset.univ fun i _ ↦ continuousOn_finsetSum Finset.univ fun j _ ↦
      (continuousOn_chartInvGramMatrix_of_inner x₀ (hg x₀) i j).mul (hh x₀ i j)
  have hcongr : ContinuousOn
      (fun q : P × M ↦ letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩;
        bilinFormTrace (h q.1 q.2))
      (s ×ˢ (chartAt H x₀).source) :=
    hchart.congr fun q hq ↦ by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g q.1⟩
      exact bilinFormTrace_eq_sum_chartInvGramMatrix x₀ hq.2 _
  refine (hcongr (p₀, x₀) ⟨hpx₀.1, mem_chart_source H x₀⟩).mono_of_mem_nhdsWithin ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds ((isOpen_univ.prod (chartAt H x₀).open_source).mem_nhds
      ⟨mem_univ _, mem_chart_source H x₀⟩)] with q hq₁ hq₂
  exact ⟨hq₁.1, hq₂.2⟩

end Helpers

/-! ### Parametric continuity of Riemannian integrals -/

section Continuity

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [T2Space M]

/-- **Parametric continuity of Riemannian volume integrals.** Let `g_p` be a family of `C^n`
Riemannian metrics whose chart-frame inner products depend continuously on `(p, x)` on
`s ×ˢ (chartAt H α).source`, and let `f_p : M → F` be continuous functions supported in a fixed
compact set `K` such that `(p, x) ↦ f_p(x)` is continuous on `s ×ˢ K`. Then
`p ↦ ∫ x, f_p(x) dV_{g_p}` is continuous on `s`. -/
theorem continuousOn_integral_riemannianVolume [SigmaCompactSpace M]
    {P : Type*} [TopologicalSpace P] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} {s : Set P} {K : Set M} (hK : IsCompact K)
    {g : P → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
    (hg : ∀ α i j, ContinuousOn
      (fun q : P × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source))
    {f : P → M → F} (hf_cont : ContinuousOn (uncurry f) (s ×ˢ K))
    (hf_mem : ∀ p ∈ s, Continuous (f p)) (hf_supp : ∀ p ∈ s, support (f p) ⊆ K) :
    ContinuousOn (fun p ↦ ∫ x, f p x.ofWithMetric ∂riemannianVolume I (WithMetric (g p))) s := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_partitionOfUnity_chartAt_source (I := I) (M := M)
  have hfin := ρ.locallyFinite_tsupport.finite_nonempty_inter_compact hK
  set A := hfin.toFinset
  have hsum : ContinuousOn
      (fun p ↦ ∑ α ∈ A, ∫ y in extChartAt I α '' (K ∩ tsupport (ρ α)),
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g p).toRiemannianMetric⟩;
          chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) •
          (ρ α ((extChartAt I α).symm y) • f p ((extChartAt I α).symm y))
          ∂(Module.finBasis ℝ E).addHaar) s := by
    refine continuousOn_finsetSum A fun α _ ↦ ?_
    set S := K ∩ tsupport (ρ α)
    have hS : IsCompact S := hK.inter_right (isClosed_tsupport _)
    have hS_src : S ⊆ (extChartAt I α).source := by
      simpa only [extChartAt_source] using inter_subset_right.trans (hρ α)
    have hL : IsCompact (extChartAt I α '' S) :=
      hS.image_of_continuousOn ((continuousOn_extChartAt α).mono hS_src)
    have hsymm_maps : MapsTo (extChartAt I α).symm (extChartAt I α '' S) S := by
      rintro _ ⟨x, hx, rfl⟩
      rwa [(extChartAt I α).left_inv (hS_src hx)]
    have hsymm_cont : ContinuousOn (extChartAt I α).symm (extChartAt I α '' S) :=
      (continuousOn_extChartAt_symm α).mono
        ((image_mono hS_src).trans_eq (PartialEquiv.image_source_eq_target _))
    have hmap_K : ContinuousOn (Prod.map id (extChartAt I α).symm)
        (s ×ˢ (extChartAt I α '' S)) := continuousOn_id.prodMap hsymm_cont
    refine continuousOn_setIntegral_of_isCompact hL hL.isClosed.measurableSet ?_
    exact ((continuousOn_chartVolumeDensity_of_inner (g := fun p ↦ (g p).toRiemannianMetric) α
        (hg α)).comp hmap_K (mapsTo_id _ |>.prodMap (hsymm_maps.mono_right
          (inter_subset_right.trans (hρ α))))).smul
      (((ρ α).continuous.comp_continuousOn (hsymm_cont.comp continuousOn_snd
        (mapsTo_snd_prod (s := s)))).smul
        (hf_cont.comp hmap_K (mapsTo_id _ |>.prodMap (hsymm_maps.mono_right inter_subset_left))))
  exact hsum.congr fun p hp ↦ integral_riemannianVolume_eq_sum_setIntegral hK ρ hρ
    (fun α hα ↦ hfin.mem_toFinset.2 hα) (g p) (hf_mem p hp) (hf_supp p hp)

/-- **Parametric continuity of Riemannian volume integrals on a compact manifold.** -/
theorem continuousOn_integral_riemannianVolume_of_compactSpace [CompactSpace M]
    {P : Type*} [TopologicalSpace P] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} {s : Set P}
    {g : P → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
    (hg : ∀ α i j, ContinuousOn
      (fun q : P × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source))
    {f : P → M → F} (hf : ContinuousOn (uncurry f) (s ×ˢ univ)) :
    ContinuousOn (fun p ↦ ∫ x, f p x.ofWithMetric ∂riemannianVolume I (WithMetric (g p))) s :=
  continuousOn_integral_riemannianVolume isCompact_univ hg hf
    (fun _ hp ↦ continuousOn_univ.1 <|
      hf.comp (continuousOn_const.prodMk continuousOn_id) fun _ hx ↦ ⟨hp, hx⟩)
    fun _ _ ↦ subset_univ _

end Continuity

/-! ### Differentiation under the Riemannian volume integral -/

section Variation

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- Differentiates a single chart's compactly supported coordinate integral with respect to `τ`. -/
private theorem hasDerivWithinAt_chartSetIntegral {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ∞ω} {s : Set ℝ} (hs : Convex ℝ s) {t : ℝ} (ht : t ∈ s)
    {K : Set M} (hK : IsCompact K) (ρ : PartitionOfUnity M M)
    (hρ : ρ.IsSubordinate fun α : M ↦ (chartAt H α).source) (α : M)
    {g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
    (hg_cont : ∀ i j, ContinuousOn
      (fun q : ℝ × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source))
    {κ : ℝ → M → ℝ} (hκ_cont : ContinuousOn (uncurry κ) (s ×ˢ K))
    (hρ_deriv : ∀ x ∈ K ∩ (chartAt H α).source, ∀ τ ∈ s,
      HasDerivWithinAt
        (fun r ↦ letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g r).toRiemannianMetric⟩;
          chartVolumeDensity (I := I) α x)
        (κ τ x *
          letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
          chartVolumeDensity (I := I) α x) s τ)
    {f f' : ℝ → M → F} (hf_cont : ContinuousOn (uncurry f) (s ×ˢ K))
    (hf'_cont : ContinuousOn (uncurry f') (s ×ˢ K))
    (hf_deriv : ∀ τ ∈ s, ∀ x ∈ K, HasDerivWithinAt (fun r ↦ f r x) (f' τ x) s τ) :
    HasDerivWithinAt
      (fun τ ↦ ∫ y in extChartAt I α '' (K ∩ tsupport (ρ α)),
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
          chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) •
          (ρ α ((extChartAt I α).symm y) • f τ ((extChartAt I α).symm y))
          ∂(Module.finBasis ℝ E).addHaar)
      (∫ y in extChartAt I α '' (K ∩ tsupport (ρ α)),
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
          chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) •
          (ρ α ((extChartAt I α).symm y) •
            (f' t ((extChartAt I α).symm y) +
              κ t ((extChartAt I α).symm y) • f t ((extChartAt I α).symm y)))
          ∂(Module.finBasis ℝ E).addHaar) s t := by
  set S := K ∩ tsupport (ρ α)
  have hS : IsCompact S := hK.inter_right (isClosed_tsupport _)
  have hS_src : S ⊆ (extChartAt I α).source := by
    simpa only [extChartAt_source] using inter_subset_right.trans (hρ α)
  have hL : IsCompact (extChartAt I α '' S) :=
    hS.image_of_continuousOn ((continuousOn_extChartAt α).mono hS_src)
  have hsymm_maps : MapsTo (extChartAt I α).symm (extChartAt I α '' S) S := by
    rintro _ ⟨x, hx, rfl⟩
    rwa [(extChartAt I α).left_inv (hS_src hx)]
  have hsymm_cont : ContinuousOn (extChartAt I α).symm (extChartAt I α '' S) :=
    (continuousOn_extChartAt_symm α).mono
      ((image_mono hS_src).trans_eq (PartialEquiv.image_source_eq_target _))
  have hmap : ContinuousOn (Prod.map id (extChartAt I α).symm)
      (s ×ˢ (extChartAt I α '' S)) := continuousOn_id.prodMap hsymm_cont
  have hd_cont := (continuousOn_chartVolumeDensity_of_inner
    (g := fun τ ↦ (g τ).toRiemannianMetric) α hg_cont).comp hmap
    (mapsTo_id _ |>.prodMap (hsymm_maps.mono_right (inter_subset_right.trans (hρ α))))
  have hρ_y : ContinuousOn (fun y ↦ ρ α ((extChartAt I α).symm y)) (extChartAt I α '' S) :=
    (ρ α).continuous.comp_continuousOn hsymm_cont
  have hf_y := hf_cont.comp hmap (mapsTo_id _ |>.prodMap (hsymm_maps.mono_right inter_subset_left))
  have hf'_y := hf'_cont.comp hmap
    (mapsTo_id _ |>.prodMap (hsymm_maps.mono_right inter_subset_left))
  have hκ_y := hκ_cont.comp hmap (mapsTo_id _ |>.prodMap (hsymm_maps.mono_right inter_subset_left))
  refine hs.hasDerivWithinAt_setIntegral_of_continuousOn
    (D := fun τ y ↦
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) •
        (ρ α ((extChartAt I α).symm y) • f τ ((extChartAt I α).symm y)))
    (D₁ := fun τ y ↦
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) •
        (ρ α ((extChartAt I α).symm y) •
          (f' τ ((extChartAt I α).symm y) +
            κ τ ((extChartAt I α).symm y) • f τ ((extChartAt I α).symm y))))
    hL hL.isClosed.measurableSet ?_ ?_ (fun τ hτ y hy ↦ ?_) ht
  · exact fun τ hτ ↦ ((hd_cont.comp (continuousOn_const.prodMk continuousOn_id)
        fun y hy ↦ ⟨hτ, hy⟩).smul
      (hρ_y.smul (hf_y.comp (continuousOn_const.prodMk continuousOn_id)
        fun y hy ↦ ⟨hτ, hy⟩))).congr fun _ _ ↦ rfl
  · exact (hd_cont.smul ((hρ_y.comp continuousOn_snd (mapsTo_snd_prod (s := s))).smul
      (hf'_y.add (hκ_y.smul hf_y)))).congr fun _ _ ↦ rfl
  · have hxS : (extChartAt I α).symm y ∈ S := hsymm_maps hy
    convert (hρ_deriv _ ⟨hxS.1, hρ α hxS.2⟩ τ hτ).smul
      ((hf_deriv τ hτ _ hxS.1).const_smul (ρ α ((extChartAt I α).symm y))) using 1
    simp only [Pi.smul_apply, smul_add, smul_smul]
    congr 2
    ring

variable [T2Space M]

/-- **Differentiation under a varying Riemannian volume integral, from a chart-density rate.**
Let `s ⊆ ℝ` be convex with `t ∈ s`, let `g_τ` be `C^n` metrics whose chart-frame inner products are
jointly continuous on `s ×ˢ (chartAt H α).source` and whose chart volume densities satisfy
`∂_τ ρ_τ = κ_τ ρ_τ` on `K ∩ (chartAt H α).source` for a scalar rate `κ` continuous on `s ×ˢ K`,
and let `f_τ : M → F` be supported in the compact set `K` with parameter derivative `f'_τ` on `K`.
Then `τ ↦ ∫ f_τ dV_{g_τ}` has derivative `∫ (f'_t + κ_t • f_t) dV_{g_t}` at `t` within `s`. -/
theorem hasDerivWithinAt_integral_riemannianVolume_of_hasDerivWithinAt_chartVolumeDensity
    [SigmaCompactSpace M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
    {s : Set ℝ} (hs : Convex ℝ s) {t : ℝ} (ht : t ∈ s) {K : Set M} (hK : IsCompact K)
    {g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
    (hg_cont : ∀ α i j, ContinuousOn
      (fun q : ℝ × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source))
    {κ : ℝ → M → ℝ} (hκ_cont : ContinuousOn (uncurry κ) (s ×ˢ K))
    (hρ_deriv : ∀ α, ∀ x ∈ K ∩ (chartAt H α).source, ∀ τ ∈ s,
      HasDerivWithinAt
        (fun r ↦ letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g r).toRiemannianMetric⟩;
          chartVolumeDensity (I := I) α x)
        (κ τ x *
          letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
          chartVolumeDensity (I := I) α x) s τ)
    {f f' : ℝ → M → F}
    (hf_cont : ContinuousOn (uncurry f) (s ×ˢ K))
    (hf_mem : ∀ τ ∈ s, Continuous (f τ)) (hf_supp : ∀ τ ∈ s, support (f τ) ⊆ K)
    (hf'_cont : ContinuousOn (uncurry f') (s ×ˢ K))
    (hf'_t : Continuous (f' t)) (hf'_supp : support (f' t) ⊆ K)
    (hf_deriv : ∀ τ ∈ s, ∀ x ∈ K, HasDerivWithinAt (fun r ↦ f r x) (f' τ x) s τ) :
    HasDerivWithinAt
      (fun τ ↦ ∫ x, f τ x.ofWithMetric ∂riemannianVolume I (WithMetric (g τ)))
      (∫ x, (f' t x.ofWithMetric + κ t x.ofWithMetric • f t x.ofWithMetric)
        ∂riemannianVolume I (WithMetric (g t))) s t := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_partitionOfUnity_chartAt_source (I := I) (M := M)
  have hfin := ρ.locallyFinite_tsupport.finite_nonempty_inter_compact hK
  have hκ_t : ContinuousOn (κ t) K :=
    hκ_cont.comp (continuousOn_const.prodMk continuousOn_id) fun x hx ↦ ⟨ht, hx⟩
  have hrhs_cont : Continuous (fun x ↦ f' t x + κ t x • f t x) :=
    hf'_t.add (continuous_smul_of_support_subset hK.isClosed hκ_t (hf_mem t ht) (hf_supp t ht))
  have hrhs_supp : support (fun x ↦ f' t x + κ t x • f t x) ⊆ K :=
    (support_add _ _).trans (union_subset hf'_supp
      ((support_smul_subset_right _ _).trans (hf_supp t ht)))
  have hsum := HasDerivWithinAt.fun_sum (u := hfin.toFinset) fun α _ ↦
    hasDerivWithinAt_chartSetIntegral hs ht hK ρ hρ α (hg_cont α) hκ_cont (hρ_deriv α)
      hf_cont hf'_cont hf_deriv
  rw [integral_riemannianVolume_eq_sum_setIntegral hK ρ hρ
    (fun α hα ↦ hfin.mem_toFinset.2 hα) (g t) hrhs_cont hrhs_supp]
  exact hsum.congr
    (fun τ hτ ↦ integral_riemannianVolume_eq_sum_setIntegral hK ρ hρ
      (fun α hα ↦ hfin.mem_toFinset.2 hα) (g τ) (hf_mem τ hτ) (hf_supp τ hτ))
    (integral_riemannianVolume_eq_sum_setIntegral hK ρ hρ
      (fun α hα ↦ hfin.mem_toFinset.2 hα) (g t) (hf_mem t ht) (hf_supp t ht))

/-- **Differentiation under a varying Riemannian volume integral.** Let `s ⊆ ℝ` be convex with
`t ∈ s`, let `g_τ` be `C^n` metrics with parameter derivative `h_τ = ∂_τ g_τ` on `K`, and let
`f_τ : M → F` be continuous functions supported in the compact set `K` with parameter derivative
`f'_τ`. Then

`∂_τ ∫ f_τ dV_{g_τ} = ∫ (f'_t + (½ tr_{g_t} h_t) • f_t) dV_{g_t}`

at `t` within `s`. -/
theorem hasDerivWithinAt_integral_riemannianVolume [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
    {s : Set ℝ} (hs : Convex ℝ s) {t : ℝ} (ht : t ∈ s) {K : Set M} (hK : IsCompact K)
    {g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
    {h : ℝ → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)}
    (hg_cont : ∀ α i j, ContinuousOn
      (fun q : ℝ × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source))
    (hh_cont : ∀ α i j, ContinuousOn
      (fun q : ℝ × M ↦ h q.1 q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ s, ∀ x ∈ K, ∀ v w,
      HasDerivWithinAt (fun r ↦ (g r).inner x v w) (h τ x v w) s τ)
    {f f' : ℝ → M → F}
    (hf_cont : ContinuousOn (uncurry f) (s ×ˢ K))
    (hf_mem : ∀ τ ∈ s, Continuous (f τ)) (hf_supp : ∀ τ ∈ s, support (f τ) ⊆ K)
    (hf'_cont : ContinuousOn (uncurry f') (s ×ˢ K))
    (hf'_t : Continuous (f' t)) (hf'_supp : support (f' t) ⊆ K)
    (hf_deriv : ∀ τ ∈ s, ∀ x ∈ K, HasDerivWithinAt (fun r ↦ f r x) (f' τ x) s τ) :
    HasDerivWithinAt
      (fun τ ↦ ∫ x, f τ x.ofWithMetric ∂riemannianVolume I (WithMetric (g τ)))
      (∫ x, (f' t x.ofWithMetric +
          (2⁻¹ * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
              ⟨(g t).toRiemannianMetric⟩;
            bilinFormTrace (h t x.ofWithMetric))) • f t x.ofWithMetric)
        ∂riemannianVolume I (WithMetric (g t))) s t :=
  hasDerivWithinAt_integral_riemannianVolume_of_hasDerivWithinAt_chartVolumeDensity hs ht hK
    hg_cont
    (κ := fun τ x ↦ 2⁻¹ *
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        bilinFormTrace (h τ x)))
    ((continuousOn_bilinFormTrace_of_inner (g := fun τ ↦ (g τ).toRiemannianMetric) hg_cont
      hh_cont).const_smul (2⁻¹ : ℝ))
    (fun α x hx τ hτ ↦ hasDerivWithinAt_chartVolumeDensity (g := fun r ↦ (g r).toRiemannianMetric)
      α hx.2 (hg_deriv τ hτ x hx.1))
    hf_cont hf_mem hf_supp hf'_cont hf'_t hf'_supp hf_deriv

/-- **First variation of total Riemannian volume.** On a compact manifold, if `g_τ` has parameter
derivative `h_τ = ∂_τ g_τ` on a convex set `s` containing `t`, then `Vol(g_τ)` has derivative
`½ ∫ tr_{g_t}(h_t) dV_{g_t}` at `t` within `s`. -/
theorem hasDerivWithinAt_riemannianTotalVolume [CompactSpace M] {n : ℕ∞ω}
    {s : Set ℝ} (hs : Convex ℝ s) {t : ℝ} (ht : t ∈ s)
    {g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
    {h : ℝ → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)}
    (hg_cont : ∀ α i j, ContinuousOn
      (fun q : ℝ × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source))
    (hh_cont : ∀ α i j, ContinuousOn
      (fun q : ℝ × M ↦ h q.1 q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ s, ∀ x v w,
      HasDerivWithinAt (fun r ↦ (g r).inner x v w) (h τ x v w) s τ) :
    HasDerivWithinAt
      (fun τ ↦ riemannianTotalVolume I (WithMetric (g τ)))
      (2⁻¹ * ∫ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          bilinFormTrace (h t x.ofWithMetric))
        ∂riemannianVolume I (WithMetric (g t))) s t := by
  have h1 := hasDerivWithinAt_integral_riemannianVolume hs ht isCompact_univ hg_cont hh_cont
    (fun τ hτ x _ v w ↦ hg_deriv τ hτ x v w)
    (f := fun _ _ ↦ (1 : ℝ)) (f' := fun _ _ ↦ (0 : ℝ))
    continuousOn_const (fun _ _ ↦ continuous_const) (fun _ _ ↦ subset_univ _)
    continuousOn_const continuous_const (subset_univ _)
    (fun _ _ _ _ ↦ hasDerivWithinAt_const _ _ _)
  simpa only [integral_const, smul_eq_mul, mul_one, zero_add, ← riemannianTotalVolume_def,
    integral_const_mul] using h1

/-- **Two-sided first variation of total Riemannian volume.** On a compact manifold, if `g_τ` has
two-sided parameter derivative `h_τ` on a neighbourhood `U` of `t`, then `Vol(g_τ)` has derivative
`½ ∫ tr_{g_t}(h_t) dV_{g_t}` at `t`. -/
theorem hasDerivAt_riemannianTotalVolume [CompactSpace M] {n : ℕ∞ω} {t : ℝ} {U : Set ℝ}
    (hU : U ∈ 𝓝 t)
    {g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
    {h : ℝ → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)}
    (hg_cont : ∀ α i j, ContinuousOn
      (fun q : ℝ × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hh_cont : ∀ α i j, ContinuousOn
      (fun q : ℝ × M ↦ h q.1 q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w, HasDerivAt (fun r ↦ (g r).inner x v w) (h τ x v w) τ) :
    HasDerivAt
      (fun τ ↦ riemannianTotalVolume I (WithMetric (g τ)))
      (2⁻¹ * ∫ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          bilinFormTrace (h t x.ofWithMetric))
        ∂riemannianVolume I (WithMetric (g t))) t := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  exact (hasDerivWithinAt_riemannianTotalVolume (convex_ball t δ) (mem_ball_self hδ)
    (fun α i j ↦ (hg_cont α i j).mono (prod_mono_left hball))
    (fun α i j ↦ (hh_cont α i j).mono (prod_mono_left hball))
    fun τ hτ x v w ↦ (hg_deriv τ (hball hτ) x v w).hasDerivWithinAt).hasDerivAt
    (ball_mem_nhds t hδ)

/-- **First variation of total volume under a conformal variation.** On a compact manifold of real
dimension `N`, if `∂_τ g = μ g` on a convex set `s` containing `t`, then `Vol(g_τ)` has derivative
`(N / 2) * ∫ μ_t dV_{g_t}` at `t` within `s`. -/
theorem hasDerivWithinAt_riemannianTotalVolume_of_conformal [CompactSpace M] {n : ℕ∞ω}
    {s : Set ℝ} (hs : Convex ℝ s) {t : ℝ} (ht : t ∈ s)
    {g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
    (hg_cont : ∀ α i j, ContinuousOn
      (fun q : ℝ × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source))
    {μ : ℝ → M → ℝ} (hμ_cont : ContinuousOn (uncurry μ) (s ×ˢ univ))
    (hg_deriv : ∀ τ ∈ s, ∀ x v w,
      HasDerivWithinAt (fun r ↦ (g r).inner x v w) (μ τ x * (g τ).inner x v w) s τ) :
    HasDerivWithinAt
      (fun τ ↦ riemannianTotalVolume I (WithMetric (g τ)))
      ((Module.finrank ℝ E : ℝ) / 2 *
        ∫ x, μ t x.ofWithMetric ∂riemannianVolume I (WithMetric (g t))) s t := by
  have h1 := hasDerivWithinAt_integral_riemannianVolume_of_hasDerivWithinAt_chartVolumeDensity
    hs ht isCompact_univ hg_cont
    (κ := fun τ x ↦ (Module.finrank ℝ E : ℝ) * μ τ x / 2)
    ((continuousOn_const.mul hμ_cont).div_const 2)
    (fun α x hx τ hτ ↦ hasDerivWithinAt_chartVolumeDensity_of_conformal
      (g := fun r ↦ (g r).toRiemannianMetric) α hx.2 (hg_deriv τ hτ x))
    (f := fun _ _ ↦ (1 : ℝ)) (f' := fun _ _ ↦ (0 : ℝ))
    continuousOn_const (fun _ _ ↦ continuous_const) (fun _ _ ↦ subset_univ _)
    continuousOn_const continuous_const (subset_univ _)
    (fun _ _ _ _ ↦ hasDerivWithinAt_const _ _ _)
  convert h1 using 1
  · funext τ
    simp only [integral_const, smul_eq_mul, mul_one, riemannianTotalVolume_def]
  · simp_rw [zero_add, smul_eq_mul, mul_one, mul_div_right_comm, integral_const_mul]

end Variation

end TauCeti

/-! ### Continuity in the chart `C^k` topologies and variation along Ricci flow -/

namespace Bundle.ContMDiffRiemannianMetric

-- Cache the canonical operator-space instances for the chart `C^k` topologies.
private local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Continuity of a family of metrics on `s` in `chartCkTopology k` implies joint continuity of its
chart-frame inner products on `s ×ˢ (chartAt H α).source`. -/
theorem continuousOn_inner_chartLocalFrame_chartCk (k : ℕ∞)
    {P : Type*} [TopologicalSpace P] {s : Set P}
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : letI := chartCkTopology (I := I) (M := M) k; ContinuousOn g s)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : P × M ↦ (g q.1).inner q.2 (chartLocalFrame (I := I) α i q.2)
        (chartLocalFrame (I := I) α j q.2))
      (s ×ˢ (chartAt H α).source) := by
  let _ := chartCkTopology (I := I) (M := M) k
  have h0 := (continuous_chartCk_iff (I := I) (M := M) k).1
    (continuousOn_iff_continuous_domRestrict.1 hg) α 0 zero_le
  have heval : Continuous (fun q : s × (extChartAt I α).target ↦
      ((g q.1.1).toNondegenerateMetric.chartMetric α) q.2
        (Module.finBasis ℝ E i) (Module.finBasis ℝ E j)) := by
    have h := (((continuous_eval_const (0 : Fin 0 → E)).comp h0).clm_apply
      (continuous_const (y := Module.finBasis ℝ E i))).clm_apply
        (continuous_const (y := Module.finBasis ℝ E j))
    simpa only [Function.comp_apply, Set.domRestrict_apply, iteratedFDeriv_zero_apply] using h
  rw [continuousOn_iff_continuous_domRestrict]
  have hΦ : Continuous (fun q : ↥(s ×ˢ (chartAt H α).source) ↦
      ((⟨q.1.1, q.2.1⟩ : s), (⟨extChartAt I α q.1.2,
        (extChartAt I α).map_source (by simpa only [extChartAt_source] using q.2.2)⟩ :
          (extChartAt I α).target))) :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk fun q ↦ q.2.1).prodMk
      (((continuousOn_extChartAt α).comp_continuous
        (continuous_snd.comp continuous_subtype_val) fun q ↦ by
          simpa only [Function.comp_apply, extChartAt_source] using q.2.2).subtype_mk _)
  refine (heval.comp hΦ).congr fun q ↦ ?_
  have hsrc : q.1.2 ∈ (extChartAt I α).source := by simpa only [extChartAt_source] using q.2.2
  simp only [Function.comp_apply, Set.domRestrict_apply,
    TauCeti.Manifold.ContMDiffNondegenerateMetric.chartMetric_extChartAt_apply_basis _
      (Module.finBasis ℝ E) hsrc,
    toNondegenerateMetric_apply]
  rw [← chartLocalFrame_def]

section Compact

variable [T2Space M] [CompactSpace M]

/-- **Continuity of Riemannian integrals in the chart `C^k` topology.** On a compact boundaryless
smooth manifold, if `(g, x) ↦ f g x` is continuous for `chartCkTopology k × M`, then
`g ↦ ∫ x, f g x dV_g` is continuous in `chartCkTopology k`. -/
theorem continuous_integral_riemannianVolume_chartCk (k : ℕ∞)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) → M → F}
    (hf : letI := chartCkTopology (I := I) (M := M) k; Continuous (uncurry f)) :
    letI := chartCkTopology (I := I) (M := M) k
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      ∫ x, f g x.ofWithMetric ∂TauCeti.riemannianVolume I (TauCeti.WithMetric g)) := by
  let _ := chartCkTopology (I := I) (M := M) k
  exact continuousOn_univ.1 <| TauCeti.continuousOn_integral_riemannianVolume_of_compactSpace
    (fun α i j ↦ continuousOn_inner_chartLocalFrame_chartCk k continuousOn_id α i j)
    hf.continuousOn

/-- **Continuity of total Riemannian volume in the chart `C^k` topology.** -/
theorem continuous_riemannianTotalVolume_chartCk (k : ℕ∞) :
    letI := chartCkTopology (I := I) (M := M) k
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      TauCeti.riemannianTotalVolume I (TauCeti.WithMetric g)) := by
  let _ := chartCkTopology (I := I) (M := M) k
  simpa only [integral_const, smul_eq_mul, mul_one, ← TauCeti.riemannianTotalVolume_def] using
    continuous_integral_riemannianVolume_chartCk (I := I) (M := M) k
      (f := fun _ _ ↦ (1 : ℝ)) continuous_const

open scoped TauCeti.MetricC2 in
/-- **Continuity of total Riemannian volume in the chart `C^2` topology.** -/
theorem continuous_riemannianTotalVolume_chartC2 :
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      TauCeti.riemannianTotalVolume I (TauCeti.WithMetric g)) :=
  continuous_riemannianTotalVolume_chartCk 2

open scoped TauCeti.MetricCInfty in
/-- **Continuity of total Riemannian volume in the chart `C^∞` topology.** -/
theorem continuous_riemannianTotalVolume_chartCInfty :
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      TauCeti.riemannianTotalVolume I (TauCeti.WithMetric g)) :=
  continuous_riemannianTotalVolume_chartCk ⊤

end Compact

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

section RicciFlow

open scoped TauCeti.MetricC2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Differentiation of Riemannian integrals along Ricci flow.** Let `s ⊆ ℝ` be convex with
`t ∈ s`, let `g_τ` be a `C^2`-continuous family of smooth metrics on `s` satisfying
`∂_τ g = -2 Ric(g)` on a compact set `K`, and let `f_τ : M → F` be supported in `K` with parameter
derivative `f'_τ`. Then

`∂_τ ∫ f_τ dV_{g_τ} = ∫ (f'_t - Scal(g_t) • f_t) dV_{g_t}`

at `t` within `s`. -/
theorem hasDerivWithinAt_integral_riemannianVolume_of_ricciFlow [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set ℝ} (hs : Convex ℝ s) {t : ℝ} (ht : t ∈ s) {K : Set M} (hK : IsCompact K)
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg_cont : ContinuousOn g s)
    (hg : ∀ τ ∈ s, ∀ x ∈ K, ∀ v w,
      HasDerivWithinAt (fun r ↦ (g r).inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s τ)
    {f f' : ℝ → M → F}
    (hf_cont : ContinuousOn (uncurry f) (s ×ˢ K))
    (hf_mem : ∀ τ ∈ s, Continuous (f τ)) (hf_supp : ∀ τ ∈ s, support (f τ) ⊆ K)
    (hf'_cont : ContinuousOn (uncurry f') (s ×ˢ K))
    (hf'_t : Continuous (f' t)) (hf'_supp : support (f' t) ⊆ K)
    (hf_deriv : ∀ τ ∈ s, ∀ x ∈ K, HasDerivWithinAt (fun r ↦ f r x) (f' τ x) s τ) :
    HasDerivWithinAt
      (fun τ ↦ ∫ x, f τ x.ofWithMetric ∂riemannianVolume I (WithMetric (g τ)))
      (∫ x, (f' t x.ofWithMetric - (g t).scalarCurvature x.ofWithMetric • f t x.ofWithMetric)
        ∂riemannianVolume I (WithMetric (g t))) s t := by
  have hscal : ContinuousOn (uncurry fun τ x ↦ -(g τ).scalarCurvature x) (s ×ˢ K) :=
    (ContMDiffRiemannianMetric.continuous_scalarCurvature_chartC2.comp_continuousOn
      (hg_cont.prodMap continuousOn_id)).neg
  have h1 := hasDerivWithinAt_integral_riemannianVolume_of_hasDerivWithinAt_chartVolumeDensity
    hs ht hK
    (fun α i j ↦ ContMDiffRiemannianMetric.continuousOn_inner_chartLocalFrame_chartCk 2 hg_cont
      α i j)
    (κ := fun τ x ↦ -(g τ).scalarCurvature x)
    hscal
    (fun α x hx τ hτ ↦ hasDerivWithinAt_chartVolumeDensity_of_ricciFlow α hx.2 (hg τ hτ x hx.1))
    hf_cont hf_mem hf_supp hf'_cont hf'_t hf'_supp hf_deriv
  simpa only [neg_smul, ← sub_eq_add_neg] using h1

/-- **Evolution of total volume along Ricci flow.** On a compact boundaryless smooth manifold, if a
`C^2`-continuous family of smooth metrics `g_τ` satisfies `∂_τ g = -2 Ric(g)` on a convex set `s`
containing `t`, then

`∂_τ Vol(g_τ) = -∫ Scal(g_t) dV_{g_t}`

at `t` within `s`. -/
theorem hasDerivWithinAt_riemannianTotalVolume_of_ricciFlow [CompactSpace M]
    {s : Set ℝ} (hs : Convex ℝ s) {t : ℝ} (ht : t ∈ s)
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg_cont : ContinuousOn g s)
    (hg : ∀ τ ∈ s, ∀ x v w,
      HasDerivWithinAt (fun r ↦ (g r).inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s τ) :
    HasDerivWithinAt
      (fun τ ↦ riemannianTotalVolume I (WithMetric (g τ)))
      (-∫ x, (g t).scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric (g t))) s t := by
  have h1 := hasDerivWithinAt_integral_riemannianVolume_of_ricciFlow hs ht isCompact_univ hg_cont
    (fun τ hτ x _ v w ↦ hg τ hτ x v w)
    (f := fun _ _ ↦ (1 : ℝ)) (f' := fun _ _ ↦ (0 : ℝ))
    continuousOn_const (fun _ _ ↦ continuous_const) (fun _ _ ↦ subset_univ _)
    continuousOn_const continuous_const (subset_univ _)
    (fun _ _ _ _ ↦ hasDerivWithinAt_const _ _ _)
  simpa only [integral_const, smul_eq_mul, mul_one, zero_sub, ← riemannianTotalVolume_def,
    integral_neg] using h1

end RicciFlow

end TauCeti
