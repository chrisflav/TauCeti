/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LinearSlice
public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless

/-!
# Linear-slice immersions into boundaryless manifolds

`TauCeti.isImmersionOfComplement_subtypeVal_linearSliceChartedSpace` assumes that the ambient
manifold `M` is self-modelled (`ChartedSpace E M`, `IsManifold 𝓘(𝕜, E) n M`). Many ambient
manifolds—such as products `M₁ × M₂` (`ModelProd`) or finite products `∀ i, M i` (`ModelPi`)—carry
a boundaryless model `I : ModelWithCorners 𝕜 E H` whose charted carrier `H` is not literally `E`.

Transporting the flattened ambient chart through `TauCeti.BoundarylessModel.originalChart` extends
both `isImmersionOfComplement_subtypeVal_linearSliceChartedSpace` and
`isSmoothEmbedding_subtypeVal_linearSliceChartedSpace` to any boundaryless model `I`.

## Main results

* `TauCeti.isImmersionOfComplement_subtypeVal_linearSliceChartedSpace_of_boundaryless`: smooth
  ambient slice charts on a boundaryless manifold make the inclusion an immersion with the
  transverse factor as complement.
* `TauCeti.isSmoothEmbedding_subtypeVal_linearSliceChartedSpace_of_boundaryless`: the resulting
  inclusion is a smooth embedding.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 5.8.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 E H F G M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [TopologicalSpace M] [ChartedSpace H M]
  {s : Set M} {n : ℕ∞ω} [IsManifold I n M]

/-- For smooth linear-slice charts on a manifold with a boundaryless model `I`, the inclusion of
the slice equipped with `TauCeti.linearSliceChartedSpace` is a `C^n` immersion with the transverse
space `G` as complement. -/
theorem isImmersionOfComplement_subtypeVal_linearSliceChartedSpace_of_boundaryless
    (e : s → OpenPartialHomeomorph M (F × G))
    (he : ∀ x, IsSliceChart (e x) ((univ : Set F) ×ˢ ({0} : Set G)) s)
    (A : s → (F × G) ≃L[𝕜] E)
    (hs : ∀ x, ContMDiffOn I 𝓘(𝕜, F × G) n (e x) (e x).source)
    (hi : ∀ x, ContMDiffOn 𝓘(𝕜, F × G) I n (e x).symm (e x).target)
    (hcover : ∀ x : s, (x : M) ∈ (e x).source) :
    letI := linearSliceChartedSpace e he hcover
    Manifold.IsImmersionOfComplement G 𝓘(𝕜, F) I n (Subtype.val : s → M) := by
  let := linearSliceChartedSpace e he hcover
  have := isManifold_linearSliceChartedSpace e he
    (fun x z hz ↦ (hs x).contMDiffAt ((e x).open_source.mem_nhds hz))
    (fun x z hz ↦ (hi x).contMDiffAt ((e x).open_target.mem_nhds hz)) hcover
  intro x
  let cFlat : OpenPartialHomeomorph (BoundarylessModel I M) E :=
    (BoundarylessModel.homeomorph I M).symm.toOpenPartialHomeomorph.trans
      ((e x).transHomeomorph (A x).toHomeomorph)
  have hcFlat : cFlat ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n (BoundarylessModel I M) := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · have hd := (BoundarylessModel.diffeomorph I (M := M) n).symm.contMDiff.contMDiffOn
        (s := cFlat.source)
      refine (((A x).contDiff.contMDiff.comp_contMDiffOn (hs x)).comp hd ?_).congr fun z _ ↦ ?_
      · intro z hz
        simpa [cFlat] using hz
      · simp [cFlat]
    · have hd := (BoundarylessModel.diffeomorph I (M := M) n).contMDiff
      refine (hd.comp_contMDiffOn
        ((hi x).comp (A x).symm.contDiff.contMDiff.contMDiffOn (s := cFlat.target) ?_)).congr
        fun z _ ↦ ?_
      · intro z hz
        simpa [cFlat] using hz
      · simp [cFlat]
        rfl
  let c : OpenPartialHomeomorph M H := BoundarylessModel.originalChart I cFlat
  have hc : c ∈ IsManifold.maximalAtlas I n M :=
    (BoundarylessModel.originalChart_mem_maximalAtlas_iff I cFlat n).2 hcFlat
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts (A x)
    (linearSliceChart e he x) c ?_ ?_ ?_ hc ?_ ?_
  · simpa only [linearSliceChart_source, mem_preimage] using hcover x
  · rw [BoundarylessModel.originalChart_source, mem_preimage]
    simpa [cFlat, -BoundarylessModel.homeomorph_apply] using hcover x
  · rw [← linearSliceChartedSpace_chartAt e he hcover x]
    exact IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, F)) x
  · intro y hy
    rw [mem_preimage, BoundarylessModel.originalChart_source, mem_preimage]
    simpa [cFlat, linearSliceChart_source, -BoundarylessModel.homeomorph_apply] using hy
  · intro v hv
    have hv' : (v, (0 : G)) ∈ (e x).target := by
      simpa only [OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, preimage_id, range_id, inter_univ,
        linearSliceChart_target, mem_preimage] using hv
    rw [comp_apply, comp_apply, BoundarylessModel.originalChart_extend_apply]
    simp [cFlat, -BoundarylessModel.homeomorph_apply,
      coe_linearSliceChart_symm_apply e he x hv', (e x).right_inv hv']

/-- The inclusion equipped with its smooth linear-slice atlas into a boundaryless manifold is a
smooth embedding. -/
theorem isSmoothEmbedding_subtypeVal_linearSliceChartedSpace_of_boundaryless
    (e : s → OpenPartialHomeomorph M (F × G))
    (he : ∀ x, IsSliceChart (e x) ((univ : Set F) ×ˢ ({0} : Set G)) s)
    (A : s → (F × G) ≃L[𝕜] E)
    (hs : ∀ x, ContMDiffOn I 𝓘(𝕜, F × G) n (e x) (e x).source)
    (hi : ∀ x, ContMDiffOn 𝓘(𝕜, F × G) I n (e x).symm (e x).target)
    (hcover : ∀ x : s, (x : M) ∈ (e x).source) :
    letI := linearSliceChartedSpace e he hcover
    Manifold.IsSmoothEmbedding 𝓘(𝕜, F) I n (Subtype.val : s → M) :=
  letI := linearSliceChartedSpace e he hcover
  ⟨(isImmersionOfComplement_subtypeVal_linearSliceChartedSpace_of_boundaryless
      e he A hs hi hcover).isImmersion,
    Topology.IsEmbedding.subtypeVal⟩

end TauCeti
