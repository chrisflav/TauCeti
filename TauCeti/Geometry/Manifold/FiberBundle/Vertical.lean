/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.FiberBundle.Basic

/-!
# The vertical tangent bundle of a smooth fibre bundle

Let `E` be a fibre bundle over a manifold `B` modelled on `IB`, whose model fibre `F` is a
manifold modelled on `IF`, and let `TauCeti.ManifoldTotalSpace F E` be its total space charted
through the trivializations of `E` and product charts of `B × F`. In the preferred charts at any
point `x` of the total space and at its base point, the bundle projection is the first coordinate
`(u, w) ↦ u`, so its manifold derivative at `x` is `ContinuousLinearMap.fst 𝕜 EB EF` without any
smoothness assumptions on the atlases.

When `B`, `F` and `E` are `C^1`, the tangent coordinate changes of `ManifoldTotalSpace F E` are
block-triangular with respect to the splitting `EB × EF`: their first coordinate depends only on
the first coordinate, through the tangent coordinate change of `B`. Consequently they preserve the
vertical subspace `0 × EF` and restrict there to continuous linear maps `EF →L[𝕜] EF` satisfying
the cocycle laws. Assembling these restrictions in a `VectorBundleCore` produces the vertical
tangent bundle `TauCeti.VerticalBundle IB IF F E`, a `C^n` vector bundle over
`ManifoldTotalSpace F E` whenever `B`, `F` and `E` are `C^(n+1)`.

At each point `x`, the inclusion `TauCeti.VerticalBundle.toTangent` embeds the vertical fibre into
the tangent space at `x` with image equal to the kernel of the derivative of the projection at `x`,
inducing a topological linear equivalence `TauCeti.VerticalBundle.equivKer` and, in the preferred
bundle charts, a `C^n` bundle morphism of total spaces for every `n`. When `E` is itself a `C^1`
vector bundle `V` with normed model fibre `F`, the vertical coordinate changes coincide with the
linear coordinate changes of `V` pulled back along the projection, and
`TauCeti.VerticalBundle.equivFiber` canonically identifies each vertical fibre `V_x V` with the
vector fibre `V (π x)`.

## Main definitions

* `TauCeti.VerticalBundle.coordChange`: the vertical tangent coordinate changes `EF →L[𝕜] EF` on
  chart overlaps of `ManifoldTotalSpace F E`.
* `TauCeti.verticalBundleCore` and `TauCeti.VerticalBundle`: the vector bundle core and the
  vertical tangent bundle `VE → E` over `ManifoldTotalSpace F E`.
* `TauCeti.VerticalBundle.toTangent`: the injective continuous linear map embedding each vertical
  fibre into `TangentSpace (IB.prod IF) x`.
* `TauCeti.VerticalBundle.equivKer`: the continuous linear equivalence between `VerticalBundle` at
  `x` and `(mfderiv (IB.prod IF) IB proj x).ker`.
* `TauCeti.VerticalBundle.equivFiber`: for a `C^1` vector bundle `V`, the canonical continuous
  linear equivalence `VerticalBundle IB 𝓘(𝕜, F) F V x ≃L[𝕜] V (((homeomorph F V).symm x).proj)`.

## Main results

* `TauCeti.ManifoldTotalSpace.hasMFDerivAt_proj` and `TauCeti.ManifoldTotalSpace.mfderiv_proj`:
  the manifold derivative of the bundle projection is `ContinuousLinearMap.fst 𝕜 EB EF`.
* `TauCeti.ManifoldTotalSpace.fst_comp_tangentCoordChange`: block-triangularity of the tangent
  coordinate changes on `ManifoldTotalSpace F E`.
* `TauCeti.VerticalBundle.contMDiffVectorBundle`: `VE → E` is a `C^n` vector bundle when `B`, `F`
  and `E` are `C^(n+1)`.
* `TauCeti.VerticalBundle.range_toTangent`: the image of `toTangent` at `x` is the kernel of the
  derivative of the projection at `x`.
* `TauCeti.VerticalBundle.contMDiff_toTangent`: the total-space inclusion `VE → TE` is `C^n` for
  every `n`.
* `TauCeti.VerticalBundle.contMDiff_equivFiber`: for a `C^1` vector bundle `V`, the map
  `(x, δw) ↦ ⟨π x, equivFiber x δw⟩` from `VV` to `V` is `C^n` for every `n`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§6.9, 9.1–9.3 (vertical tangent bundle of a fibred manifold and canonical vertical
  splitting on a vector bundle).
-/

public section

noncomputable section

open Bundle Set Filter ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace TauCeti

section DerivativeProj

variable {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

namespace ManifoldTotalSpace

/-- A point in the preferred chart source at `i` projects into the base set of the preferred
trivialization at the base point of `i` and into the preferred base chart source there. -/
theorem proj_mem_of_mem_chart_source {i x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source) :
    ((homeomorph F E).symm x).proj ∈
        (trivializationAt F E ((homeomorph F E).symm i).proj).baseSet ∧
      ((homeomorph F E).symm x).proj ∈ (chartAt HB ((homeomorph F E).symm i).proj).source := by
  obtain ⟨i₀, rfl⟩ := (homeomorph F E).surjective i
  obtain ⟨x₀, rfl⟩ := (homeomorph F E).surjective x
  rw [chartAt_homeomorph] at hx
  simp only [Homeomorph.transOpenPartialHomeomorph_source, mem_preimage,
    Homeomorph.symm_apply_apply, OpenPartialHomeomorph.trans_source,
    Trivialization.coe_coe, OpenPartialHomeomorph.prod_source] at hx ⊢
  refine ⟨(trivializationAt F E i₀.proj).mem_source.1 hx.1, ?_⟩
  have hx2 := hx.2.1
  rwa [(trivializationAt F E i₀.proj).coe_fst hx.1] at hx2

/-- In the preferred extended chart at `i`, the first coordinate of any point `x` in the chart
source is the extended base chart coordinate of its projection. -/
theorem extChartAt_fst_of_mem_chart_source {i x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source) :
    (extChartAt (IB.prod IF) i x).1 =
      extChartAt IB ((homeomorph F E).symm i).proj ((homeomorph F E).symm x).proj := by
  have hmem := (proj_mem_of_mem_chart_source hx).1
  obtain ⟨i₀, rfl⟩ := (homeomorph F E).surjective i
  obtain ⟨x₀, rfl⟩ := (homeomorph F E).surjective x
  simp only [Homeomorph.symm_apply_apply] at hmem ⊢
  rw [extChartAt_homeomorph_apply, (trivializationAt F E i₀.proj).coe_fst' hmem]

/-- The inverse of the preferred extended chart at `homeomorph F E i₀` sends the extended chart
coordinates of `b` and `v` to `homeomorph F E ((trivializationAt F E i₀.proj).symm (b, v))`. -/
theorem extChartAt_symm_homeomorph (i₀ : TotalSpace F E) {b : B} {v : F}
    (hb₁ : b ∈ (trivializationAt F E i₀.proj).baseSet)
    (hb₂ : b ∈ (chartAt HB i₀.proj).source)
    (hv : v ∈ (chartAt HF (trivializationAt F E i₀.proj i₀).2).source) :
    (extChartAt (IB.prod IF) (homeomorph F E i₀)).symm
        (extChartAt IB i₀.proj b, extChartAt IF (trivializationAt F E i₀.proj i₀).2 v) =
      homeomorph F E ((trivializationAt F E i₀.proj).toOpenPartialHomeomorph.symm (b, v)) := by
  set e := trivializationAt F E i₀.proj
  have hbv : (b, v) ∈ e.target := by rw [e.target_eq]; exact ⟨hb₁, mem_univ v⟩
  have hz_src : e.toOpenPartialHomeomorph.symm (b, v) ∈ e.source :=
    e.toOpenPartialHomeomorph.map_target hbv
  have hz_eq : e (e.toOpenPartialHomeomorph.symm (b, v)) = (b, v) :=
    e.toOpenPartialHomeomorph.right_inv hbv
  have hsrc : homeomorph F E (e.toOpenPartialHomeomorph.symm (b, v)) ∈
      (extChartAt (IB.prod IF) (homeomorph F E i₀)).source := by
    rw [extChartAt_source, chartAt_homeomorph]
    simp only [Homeomorph.transOpenPartialHomeomorph_source, mem_preimage,
      Homeomorph.symm_apply_apply, OpenPartialHomeomorph.trans_source,
      Trivialization.coe_coe, OpenPartialHomeomorph.prod_source]
    refine ⟨hz_src, ?_⟩
    rw [show trivializationAt F E i₀.proj = e from rfl, mem_preimage, hz_eq]
    exact ⟨hb₂, hv⟩
  have happ : extChartAt (IB.prod IF) (homeomorph F E i₀)
      (homeomorph F E (e.toOpenPartialHomeomorph.symm (b, v))) =
      (extChartAt IB i₀.proj b, extChartAt IF (e i₀).2 v) := by
    rw [extChartAt_homeomorph_apply, hz_eq]
  rw [← happ, (extChartAt (IB.prod IF) (homeomorph F E i₀)).left_inv hsrc]

/-- Read through the inverse of the preferred extended chart at `i`, the bundle projection is the
inverse of the base extended chart applied to the first coordinate. -/
theorem proj_extChartAt_symm (i : ManifoldTotalSpace F E) {y : EB × EF}
    (hy : y ∈ (extChartAt (IB.prod IF) i).target) :
    ((homeomorph F E).symm ((extChartAt (IB.prod IF) i).symm y)).proj =
      (extChartAt IB ((homeomorph F E).symm i).proj).symm y.1 := by
  obtain ⟨i₀, rfl⟩ := (homeomorph F E).surjective i
  have hsrc : (extChartAt (IB.prod IF) (homeomorph F E i₀)).symm y ∈
      (chartAt (ModelProd HB HF) (homeomorph F E i₀)).source := by
    rw [← extChartAt_source (IB.prod IF)]
    exact (extChartAt (IB.prod IF) (homeomorph F E i₀)).map_target hy
  have hb : ((homeomorph F E).symm ((extChartAt (IB.prod IF) (homeomorph F E i₀)).symm y)).proj ∈
      (extChartAt IB i₀.proj).source := by
    rw [extChartAt_source]
    simpa only [Homeomorph.symm_apply_apply] using (proj_mem_of_mem_chart_source hsrc).2
  have heq := extChartAt_proj_extChartAt_symm (IF := IF) i₀ hy
  simpa only [Homeomorph.symm_apply_apply, ← heq] using ((extChartAt IB i₀.proj).left_inv hb).symm

/-- **The bundle projection has `fst` as its manifold derivative.** In the preferred chart of
`ManifoldTotalSpace F E` at `x` and the preferred base chart at its projection, the bundle
projection is the first coordinate, so its manifold derivative is `ContinuousLinearMap.fst`. -/
theorem hasMFDerivAt_proj (x : ManifoldTotalSpace F E) :
    HasMFDerivAt (IB.prod IF) IB
      (fun y : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm y).proj) x
      (ContinuousLinearMap.fst 𝕜 EB EF) := by
  refine ⟨(contMDiff_proj 1 F E IB IF x).continuousAt, ?_⟩
  obtain ⟨x₀, rfl⟩ := (homeomorph F E).surjective x
  have hy₀ := mem_extChartAt_target (I := IB.prod IF) (homeomorph F E x₀)
  refine (hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := EF)).hasFDerivWithinAt.congr_of_eventuallyEq
    ?_ ?_
  · filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hy₀] with y hy
    simpa only [writtenInExtChartAt, Function.comp_apply, Homeomorph.symm_apply_apply] using
      extChartAt_proj_extChartAt_symm x₀ hy
  · simpa only [writtenInExtChartAt, Function.comp_apply, Homeomorph.symm_apply_apply] using
      extChartAt_proj_extChartAt_symm x₀ hy₀

/-- **The manifold derivative of the bundle projection is the first coordinate projection.** -/
theorem mfderiv_proj (x : ManifoldTotalSpace F E) :
    mfderiv (IB.prod IF) IB
      (fun y : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm y).proj) x =
      ContinuousLinearMap.fst 𝕜 EB EF :=
  (hasMFDerivAt_proj x).mfderiv

/-- The derivative of the bundle projection is surjective at every point. -/
theorem mfderiv_proj_surjective (x : ManifoldTotalSpace F E) :
    Function.Surjective
      (mfderiv (IB.prod IF) IB
        (fun y : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm y).proj) x) := by
  rw [mfderiv_proj]
  exact fun u ↦ ⟨(u, 0), rfl⟩

/-- A tangent vector at `x` lies in the kernel of the derivative of the projection if and only if
its first chart coordinate vanishes. -/
theorem mem_ker_mfderiv_proj_iff {x : ManifoldTotalSpace F E}
    {v : TangentSpace (IB.prod IF) x} :
    v ∈ (mfderiv (IB.prod IF) IB
      (fun y : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm y).proj) x).ker ↔
      (ContinuousLinearMap.fst 𝕜 EB EF) v = 0 := by
  rw [mfderiv_proj, LinearMap.mem_ker]
  rfl

/-! ### Block-triangularity of tangent coordinate changes -/

section CoordChange

variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- **Block-triangularity of tangent coordinate changes on `ManifoldTotalSpace F E`.** On the
intersection of two preferred chart sources, the first coordinate of the tangent coordinate change
depends only on the first coordinate, via the tangent coordinate change of the base. -/
theorem fst_comp_tangentCoordChange {i j x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source) :
    (ContinuousLinearMap.fst 𝕜 EB EF).comp (tangentCoordChange (IB.prod IF) i j x) =
      (tangentCoordChange IB ((homeomorph F E).symm i).proj ((homeomorph F E).symm j).proj
        ((homeomorph F E).symm x).proj).comp (ContinuousLinearMap.fst 𝕜 EB EF) := by
  have hxi : x ∈ (extChartAt (IB.prod IF) i).source := by rw [extChartAt_source]; exact hx.1
  have hxj : x ∈ (extChartAt (IB.prod IF) j).source := by rw [extChartAt_source]; exact hx.2
  have hbi : ((homeomorph F E).symm x).proj ∈
      (extChartAt IB ((homeomorph F E).symm i).proj).source := by
    rw [extChartAt_source]; exact (proj_mem_of_mem_chart_source hx.1).2
  have hbj : ((homeomorph F E).symm x).proj ∈
      (extChartAt IB ((homeomorph F E).symm j).proj).source := by
    rw [extChartAt_source]; exact (proj_mem_of_mem_chart_source hx.2).2
  set y₀ := extChartAt (IB.prod IF) i x
  have hLHS := hasFDerivAt_fst.comp_hasFDerivWithinAt y₀
    (hasFDerivWithinAt_tangentCoordChange (I := IB.prod IF) ⟨hxi, hxj⟩)
  have hbase : HasFDerivWithinAt
      (extChartAt IB ((homeomorph F E).symm j).proj ∘
        (extChartAt IB ((homeomorph F E).symm i).proj).symm)
      (tangentCoordChange IB ((homeomorph F E).symm i).proj ((homeomorph F E).symm j).proj
        ((homeomorph F E).symm x).proj) (range IB) y₀.1 := by
    rw [show y₀.1 = _ from extChartAt_fst_of_mem_chart_source hx.1]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hbi, hbj⟩
  have hRHS := hbase.comp y₀ (hasFDerivAt_fst.hasFDerivWithinAt (s := range (IB.prod IF)))
    fun y hy ↦ by rw [ModelWithCorners.range_prod] at hy; exact hy.1
  have heq : (Prod.fst ∘ (extChartAt (IB.prod IF) j ∘ (extChartAt (IB.prod IF) i).symm))
      =ᶠ[𝓝[range (IB.prod IF)] y₀]
      ((extChartAt IB ((homeomorph F E).symm j).proj ∘
        (extChartAt IB ((homeomorph F E).symm i).proj).symm) ∘ Prod.fst) := by
    filter_upwards [Filter.inter_mem (extChartAt_target_mem_nhdsWithin_of_mem
        ((extChartAt (IB.prod IF) i).map_source hxi))
      (mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds' hxi
        ((chartAt _ j).open_source.mem_nhds hx.2)))] with y hy
    simp only [Function.comp_apply, extChartAt_fst_of_mem_chart_source hy.2,
      proj_extChartAt_symm i hy.1]
  have hpt : (Prod.fst ∘ (extChartAt (IB.prod IF) j ∘ (extChartAt (IB.prod IF) i).symm)) y₀ =
      ((extChartAt IB ((homeomorph F E).symm j).proj ∘
        (extChartAt IB ((homeomorph F E).symm i).proj).symm) ∘ Prod.fst) y₀ := by
    simp only [Function.comp_apply, y₀, (extChartAt (IB.prod IF) i).left_inv hxi,
      extChartAt_fst_of_mem_chart_source hx.2, extChartAt_fst_of_mem_chart_source hx.1,
      (extChartAt IB _).left_inv hbi]
  have hs := (IB.prod IF).uniqueDiffOn _
    (extChartAt_target_subset_range i ((extChartAt (IB.prod IF) i).map_source hxi))
  exact hs.eq (hLHS.congr_of_eventuallyEq heq.symm hpt.symm) hRHS

/-- Tangent coordinate changes preserve vertical vectors: their first coordinate vanishes on
`0 × EF`. -/
theorem fst_comp_tangentCoordChange_comp_inr {i j x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source) :
    (ContinuousLinearMap.fst 𝕜 EB EF).comp
      ((tangentCoordChange (IB.prod IF) i j x).comp (ContinuousLinearMap.inr 𝕜 EB EF)) = 0 := by
  rw [← ContinuousLinearMap.comp_assoc, fst_comp_tangentCoordChange hx,
    ContinuousLinearMap.comp_assoc, ContinuousLinearMap.fst_comp_inr,
    ContinuousLinearMap.comp_zero]

end CoordChange

end ManifoldTotalSpace

end DerivativeProj

/-! ### The vertical tangent bundle -/

section VerticalBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  (IF : ModelWithCorners 𝕜 EF HF)
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (F : Type*) [TopologicalSpace F] [ChartedSpace HF F]
  (E : B → Type*) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]

namespace VerticalBundle

variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- The vertical tangent coordinate change from the chart at `i` to the chart at `j` at a point `x`
of `ManifoldTotalSpace F E`: the restriction of `tangentCoordChange (IB.prod IF) i j x` to the
vertical factor `0 × EF`. -/
def coordChange (i j x : ManifoldTotalSpace F E) : EF →L[𝕜] EF :=
  (ContinuousLinearMap.snd 𝕜 EB EF).comp
    ((tangentCoordChange (IB.prod IF) i j x).comp (ContinuousLinearMap.inr 𝕜 EB EF))

/-- Evaluating the vertical coordinate change extracts the second coordinate of the tangent
coordinate change on `(0, v)`. -/
theorem coordChange_apply (i j x : ManifoldTotalSpace F E) (v : EF) :
    coordChange IB IF F E i j x v = (tangentCoordChange (IB.prod IF) i j x (0, v)).2 :=
  (rfl)

variable {IB IF F E}

/-- **Intertwining of tangent and vertical coordinate changes.** On chart overlaps, the tangent
coordinate change carries `inr v` to `inr (coordChange i j x v)`. -/
theorem tangentCoordChange_comp_inr {i j x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source) :
    (tangentCoordChange (IB.prod IF) i j x).comp (ContinuousLinearMap.inr 𝕜 EB EF) =
      (ContinuousLinearMap.inr 𝕜 EB EF).comp (coordChange IB IF F E i j x) := by
  have h0 := ManifoldTotalSpace.fst_comp_tangentCoordChange_comp_inr (IB := IB) (IF := IF) hx
  ext v
  · exact DFunLike.congr_fun h0 v
  · rfl

/-- Pointwise form of `tangentCoordChange_comp_inr`. -/
theorem tangentCoordChange_inr {i j x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source)
    (v : EF) :
    tangentCoordChange (IB.prod IF) i j x (0, v) = (0, coordChange IB IF F E i j x v) :=
  DFunLike.congr_fun (tangentCoordChange_comp_inr hx) v

/-- The vertical coordinate change from a chart to itself is the identity on its source. -/
theorem coordChange_self {i x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source) (v : EF) :
    coordChange IB IF F E i i x v = v := by
  have hx' : x ∈ (extChartAt (IB.prod IF) i).source := by rwa [extChartAt_source]
  rw [coordChange_apply, tangentCoordChange_self hx']

/-- **Cocycle law for vertical coordinate changes.** -/
theorem coordChange_comp {i j k x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source ∩
      (chartAt (ModelProd HB HF) k).source) (v : EF) :
    coordChange IB IF F E j k x (coordChange IB IF F E i j x v) =
      coordChange IB IF F E i k x v := by
  have hx' : x ∈ (extChartAt (IB.prod IF) i).source ∩ (extChartAt (IB.prod IF) j).source ∩
      (extChartAt (IB.prod IF) k).source := by
    simp only [extChartAt_source]; exact hx
  have h := tangentCoordChange_comp (I := IB.prod IF) (v := ((0 : EB), v)) hx'
  rw [tangentCoordChange_inr ⟨hx.1.1, hx.1.2⟩, tangentCoordChange_inr ⟨hx.1.2, hx.2⟩,
    tangentCoordChange_inr ⟨hx.1.1, hx.2⟩] at h
  exact (Prod.mk.inj h).2

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
/-- The vertical coordinate changes of a `C^(n+1)` fibre bundle are `C^n`. -/
theorem contMDiffOn_coordChange {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] (i j : ManifoldTotalSpace F E) :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiffOn (IB.prod IF) 𝓘(𝕜, EF →L[𝕜] EF) n (coordChange IB IF F E i j)
      ((chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  have hT := (tangentBundleCore.isContMDiff (I := IB.prod IF)
    (M := ManifoldTotalSpace F E) (n := n)).contMDiffOn_coordChange
    (achart (ModelProd HB HF) i) (achart (ModelProd HB HF) j)
  let projL : ((EB × EF) →L[𝕜] (EB × EF)) →L[𝕜] (EF →L[𝕜] EF) :=
    (ContinuousLinearMap.compL 𝕜 EF (EB × EF) EF (ContinuousLinearMap.snd 𝕜 EB EF)).comp
      ((ContinuousLinearMap.compL 𝕜 EF (EB × EF) (EB × EF)).flip (ContinuousLinearMap.inr 𝕜 EB EF))
  exact projL.contDiff.contMDiff.comp_contMDiffOn hT

end VerticalBundle

section Core

variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- The vector bundle core of the vertical tangent bundle `VE → E` over `ManifoldTotalSpace F E`,
indexed by the points of `ManifoldTotalSpace F E` with their preferred chart sources as base sets
and `VerticalBundle.coordChange` as transition maps. -/
def verticalBundleCore :
    VectorBundleCore 𝕜 (ManifoldTotalSpace F E) EF (ManifoldTotalSpace F E) where
  baseSet i := (chartAt (ModelProd HB HF) i).source
  isOpen_baseSet i := (chartAt (ModelProd HB HF) i).open_source
  indexAt := id
  mem_baseSet_at := mem_chart_source (ModelProd HB HF)
  coordChange := VerticalBundle.coordChange IB IF F E
  coordChange_self _ _ hx v := VerticalBundle.coordChange_self hx v
  continuousOn_coordChange i j := by
    have : IsManifold IB (0 + 1) B := by simpa
    have : IsManifold IF (0 + 1) F := by simpa
    have : ContMDiffFiberBundle (0 + 1) F E IB IF := by simpa
    exact (VerticalBundle.contMDiffOn_coordChange (IB := IB) (IF := IF) (n := 0) i j).continuousOn
  coordChange_comp _ _ _ _ hx v := VerticalBundle.coordChange_comp hx v

/-- The base set of `verticalBundleCore` at `i` is the preferred chart source at `i`. -/
theorem verticalBundleCore_baseSet (i : ManifoldTotalSpace F E) :
    (verticalBundleCore IB IF F E).baseSet i = (chartAt (ModelProd HB HF) i).source :=
  (rfl)

@[simp]
theorem verticalBundleCore_indexAt (x : ManifoldTotalSpace F E) :
    (verticalBundleCore IB IF F E).indexAt x = x :=
  (rfl)

@[simp]
theorem verticalBundleCore_coordChange :
    (verticalBundleCore IB IF F E).coordChange = VerticalBundle.coordChange IB IF F E :=
  (rfl)

/-- **The vertical tangent bundle `VE` of a `C^1` fibre bundle `E → B`.** Its fibre over a point
`x : ManifoldTotalSpace F E` is the model vector space `EF` of the fibre `F`, glued across charts of
`ManifoldTotalSpace F E` by the vertical restrictions of the tangent coordinate changes. -/
abbrev VerticalBundle : ManifoldTotalSpace F E → Type _ :=
  (verticalBundleCore IB IF F E).Fiber

instance VerticalBundle.instIsTopologicalAddGroup (x : ManifoldTotalSpace F E) :
    IsTopologicalAddGroup (VerticalBundle IB IF F E x) :=
  inferInstanceAs <| IsTopologicalAddGroup EF

instance VerticalBundle.instContinuousSMul (x : ManifoldTotalSpace F E) :
    ContinuousSMul 𝕜 (VerticalBundle IB IF F E x) :=
  inferInstanceAs <| ContinuousSMul 𝕜 EF

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
/-- The core of the vertical tangent bundle of a `C^(n+1)` fibre bundle has `C^n` transition
functions. -/
theorem verticalBundleCore_isContMDiff {n : ℕ∞ω} [IsManifold IB (n + 1) B]
    [IsManifold IF (n + 1) F] [ContMDiffFiberBundle (n + 1) F E IB IF] :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    (verticalBundleCore IB IF F E).IsContMDiff (IB.prod IF) n :=
  ⟨VerticalBundle.contMDiffOn_coordChange⟩

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
/-- **The vertical tangent bundle of a `C^(n+1)` fibre bundle is a `C^n` vector bundle.** -/
theorem VerticalBundle.contMDiffVectorBundle {n : ℕ∞ω} [IsManifold IB (n + 1) B]
    [IsManifold IF (n + 1) F] [ContMDiffFiberBundle (n + 1) F E IB IF] :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiffVectorBundle n EF (VerticalBundle IB IF F E) (IB.prod IF) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  have := verticalBundleCore_isContMDiff IB IF F E (n := n)
  exact (verticalBundleCore IB IF F E).instContMDiffVectorBundle

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance VerticalBundle.instContMDiffVectorBundle_infty [IsManifold IB ∞ B] [IsManifold IF ∞ F]
    [ContMDiffFiberBundle ∞ F E IB IF] :
    ContMDiffVectorBundle ∞ EF (VerticalBundle IB IF F E) (IB.prod IF) := by
  have : IsManifold IB (∞ + 1) B := by simpa using (inferInstance : IsManifold IB ∞ B)
  have : IsManifold IF (∞ + 1) F := by simpa using (inferInstance : IsManifold IF ∞ F)
  have : ContMDiffFiberBundle (∞ + 1) F E IB IF := by
    simpa using (inferInstance : ContMDiffFiberBundle ∞ F E IB IF)
  exact VerticalBundle.contMDiffVectorBundle IB IF F E

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance VerticalBundle.instContMDiffVectorBundle_omega [IsManifold IB ω B] [IsManifold IF ω F]
    [ContMDiffFiberBundle ω F E IB IF] :
    ContMDiffVectorBundle ω EF (VerticalBundle IB IF F E) (IB.prod IF) := by
  have : IsManifold IB (ω + 1) B := by simpa using (inferInstance : IsManifold IB ω B)
  have : IsManifold IF (ω + 1) F := by simpa using (inferInstance : IsManifold IF ω F)
  have : ContMDiffFiberBundle (ω + 1) F E IB IF := by
    simpa using (inferInstance : ContMDiffFiberBundle ω F E IB IF)
  exact VerticalBundle.contMDiffVectorBundle IB IF F E

end Core

/-! ### Inclusion into the tangent bundle and exactness -/

namespace VerticalBundle

variable {IB IF F E} [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- The preferred trivialization of `VerticalBundle` at `i` has the preferred chart source at `i`
as its base set. -/
@[simp]
theorem trivializationAt_baseSet (i : ManifoldTotalSpace F E) :
    (trivializationAt EF (VerticalBundle IB IF F E) i).baseSet =
      (chartAt (ModelProd HB HF) i).source :=
  (rfl)

/-- The preferred trivialization of `VerticalBundle` at `i` applies `coordChange` from `p.proj`
to `i`. -/
theorem trivializationAt_apply_snd (i : ManifoldTotalSpace F E)
    (p : TotalSpace EF (VerticalBundle IB IF F E)) :
    (trivializationAt EF (VerticalBundle IB IF F E) i p).2 =
      coordChange IB IF F E p.proj i p.proj p.2 :=
  (rfl)

/-- **Canonical inclusion `V_x E →L[𝕜] T_x E`.** In the preferred chart at `x`, a vertical vector
`v` embeds as `(0, v)` in `TangentSpace (IB.prod IF) x`. -/
def toTangent (x : ManifoldTotalSpace F E) :
    VerticalBundle IB IF F E x →L[𝕜] TangentSpace (IB.prod IF) x :=
  ContinuousLinearMap.inr 𝕜 EB EF

/-- In the preferred chart at `x`, `toTangent x v` has model coordinates `(0, v)`. -/
theorem toTangent_apply (x : ManifoldTotalSpace F E) (v : VerticalBundle IB IF F E x) :
    toTangent x v = (0, v) :=
  (rfl)

/-- `toTangent` is injective on every fibre. -/
theorem toTangent_injective (x : ManifoldTotalSpace F E) :
    Function.Injective (toTangent (IB := IB) (IF := IF) (F := F) (E := E) x) :=
  fun _ _ h ↦ (Prod.mk.inj h).2

/-- The derivative of the bundle projection annihilates every vertical vector. -/
@[simp]
theorem mfderiv_proj_toTangent (x : ManifoldTotalSpace F E) (v : VerticalBundle IB IF F E x) :
    mfderiv (IB.prod IF) IB
      (fun y : ManifoldTotalSpace F E ↦ ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x
      (toTangent x v) = 0 := by
  rw [ManifoldTotalSpace.mfderiv_proj]
  rfl

/-- Composing the derivative of the bundle projection with `toTangent` gives zero. -/
@[simp]
theorem mfderiv_proj_comp_toTangent (x : ManifoldTotalSpace F E) :
    (mfderiv (IB.prod IF) IB
      (fun y : ManifoldTotalSpace F E ↦ ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x).comp
      (toTangent (IB := IB) (IF := IF) (F := F) (E := E) x) = 0 :=
  ContinuousLinearMap.ext (mfderiv_proj_toTangent x)

/-- **Exactness of `0 → V_x E → T_x E → T_{π(x)} B → 0` at `T_x E`.** The image of `toTangent` is
the kernel of the manifold derivative of the bundle projection. -/
theorem range_toTangent (x : ManifoldTotalSpace F E) :
    LinearMap.range (toTangent (IB := IB) (IF := IF) (F := F) (E := E) x).toLinearMap =
      (mfderiv (IB.prod IF) IB
        (fun y : ManifoldTotalSpace F E ↦
          ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x).ker := by
  ext w
  rw [LinearMap.mem_range, ManifoldTotalSpace.mem_ker_mfderiv_proj_iff]
  refine ⟨?_, fun hw ↦ ⟨w.2, Prod.ext hw.symm rfl⟩⟩
  rintro ⟨v, rfl⟩
  rfl

/-- **Canonical topological linear equivalence `V_x E ≃L[𝕜] ker (dπ_x)`.** -/
def equivKer (x : ManifoldTotalSpace F E) :
    VerticalBundle IB IF F E x ≃L[𝕜]
      (mfderiv (IB.prod IF) IB
        (fun y : ManifoldTotalSpace F E ↦
          ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x).ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((toTangent x).codRestrict _ fun v ↦ by
      rw [ManifoldTotalSpace.mem_ker_mfderiv_proj_iff]; rfl)
    ((ContinuousLinearMap.snd 𝕜 EB EF).comp (Submodule.subtypeL _))
    (fun _ ↦ rfl)
    (fun ⟨w, hw⟩ ↦ Subtype.ext (Prod.ext
      ((ManifoldTotalSpace.mem_ker_mfderiv_proj_iff.1 hw).symm) rfl))

@[simp]
theorem coe_equivKer_apply (x : ManifoldTotalSpace F E) (v : VerticalBundle IB IF F E x) :
    (equivKer x v : TangentSpace (IB.prod IF) x) = toTangent x v :=
  (rfl)

@[simp]
theorem toTangent_equivKer_symm (x : ManifoldTotalSpace F E)
    (w : (mfderiv (IB.prod IF) IB
      (fun y : ManifoldTotalSpace F E ↦
        ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x).ker) :
    toTangent x ((equivKer x).symm w) = (w : TangentSpace (IB.prod IF) x) :=
  congrArg Subtype.val ((equivKer x).apply_symm_apply w)

/-- In any preferred chart `i` containing `x`, `toTangent` intertwines the preferred
trivializations of `VerticalBundle` and `TangentSpace`. -/
theorem trivializationAt_toTangent {i x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source) (v : VerticalBundle IB IF F E x) :
    (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i ⟨x, toTangent x v⟩).2 =
      ContinuousLinearMap.inr 𝕜 EB EF
        (trivializationAt EF (VerticalBundle IB IF F E) i ⟨x, v⟩).2 :=
  tangentCoordChange_inr (EF := EF) ⟨mem_chart_source _ x, hx⟩ v

/-- **Smoothness of the vertical subbundle inclusion `VE → TE`.** In the preferred bundle charts of
`VE` and `TE`, `toTangent` is the constant continuous linear inclusion `inr 𝕜 EB EF`, so the
total-space map `(x, v) ↦ (x, toTangent x v)` is `C^n` for every `n : ℕ∞ω` as soon as `B`, `F` and
`E` are `C^1`. -/
theorem contMDiff_toTangent (n : ℕ∞ω) :
    ContMDiff ((IB.prod IF).prod 𝓘(𝕜, EF)) (IB.prod IF).tangent n
      (fun p : TotalSpace EF (VerticalBundle IB IF F E) ↦
        (⟨p.proj, toTangent p.proj p.2⟩ :
          TangentBundle (IB.prod IF) (ManifoldTotalSpace F E))) := by
  intro p₀
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨Bundle.contMDiffAt_proj (IB := IB.prod IF) _, ?_⟩
  have hcoord := (Bundle.contMDiffAt_totalSpace_iff.1
    (contMDiffAt_id (I := (IB.prod IF).prod 𝓘(𝕜, EF)) (n := n) (x := p₀))).2
  have hU : TotalSpace.proj ⁻¹' (chartAt (ModelProd HB HF) p₀.proj).source ∈ 𝓝 p₀ :=
    ((FiberBundle.continuous_proj EF (VerticalBundle IB IF F E)).isOpen_preimage _
      (chartAt _ p₀.proj).open_source).mem_nhds (mem_chart_source (ModelProd HB HF) p₀.proj)
  refine ((ContinuousLinearMap.inr 𝕜 EB EF).contDiff.contMDiff.contMDiffAt.comp p₀
    hcoord).congr_of_eventuallyEq ?_
  filter_upwards [hU] with p hp
  exact trivializationAt_toTangent hp p.2

end VerticalBundle

end VerticalBundle

/-! ### Canonical vertical-fibre identification for a vector bundle -/

section VectorBundle

variable {𝕜 B F : Type*} {V : B → Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F V)] [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)]
  [∀ b, TopologicalSpace (V b)] [FiberBundle F V] [VectorBundle 𝕜 F V]

namespace VerticalBundle

/-- Along a vertical fibre in the preferred chart of `ManifoldTotalSpace F V`, the second
coordinate of the chart transition map is the linear coordinate change of `V`. -/
theorem extChartAt_snd_symm_eq_coordChangeL (i₀ j₀ : TotalSpace F V) {b : B}
    (hbi₁ : b ∈ (trivializationAt F V i₀.proj).baseSet)
    (hbi₂ : b ∈ (chartAt HB i₀.proj).source)
    (hbj : b ∈ (trivializationAt F V j₀.proj).baseSet) (w : F) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V j₀)
        ((extChartAt (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V i₀)).symm
          (extChartAt IB i₀.proj b, w))).2 =
      (trivializationAt F V i₀.proj).coordChangeL 𝕜 (trivializationAt F V j₀.proj) b w := by
  have hsymm := ManifoldTotalSpace.extChartAt_symm_homeomorph (IB := IB) (IF := 𝓘(𝕜, F))
    i₀ hbi₁ hbi₂ (mem_univ w)
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] at hsymm
  rw [hsymm, ManifoldTotalSpace.extChartAt_homeomorph_apply,
    ← Trivialization.coordChangeL_apply' (R := 𝕜) _ _ ⟨hbi₁, hbj⟩]
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]

variable [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F V IB]

/-- **Vertical coordinate changes of a vector bundle equal its linear coordinate changes.** On chart
overlaps of `ManifoldTotalSpace F V`, the vertical tangent coordinate change from `i` to `j` at `x`
is `(trivializationAt F V (π i)).coordChangeL 𝕜 (trivializationAt F V (π j)) (π x)`. -/
theorem coordChange_eq_coordChangeL {i j x : ManifoldTotalSpace F V}
    (hx : x ∈ (chartAt (ModelProd HB F) i).source ∩ (chartAt (ModelProd HB F) j).source) :
    coordChange IB 𝓘(𝕜, F) F V i j x =
      ((trivializationAt F V ((ManifoldTotalSpace.homeomorph F V).symm i).proj).coordChangeL 𝕜
        (trivializationAt F V ((ManifoldTotalSpace.homeomorph F V).symm j).proj)
        ((ManifoldTotalSpace.homeomorph F V).symm x).proj : F →L[𝕜] F) := by
  obtain ⟨i₀, rfl⟩ := (ManifoldTotalSpace.homeomorph F V).surjective i
  obtain ⟨j₀, rfl⟩ := (ManifoldTotalSpace.homeomorph F V).surjective j
  obtain ⟨x₀, rfl⟩ := (ManifoldTotalSpace.homeomorph F V).surjective x
  have hbi := ManifoldTotalSpace.proj_mem_of_mem_chart_source hx.1
  have hbj := ManifoldTotalSpace.proj_mem_of_mem_chart_source hx.2
  simp only [Homeomorph.symm_apply_apply] at hbi hbj ⊢
  let y₀ : EB × F := extChartAt (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V i₀)
    (ManifoldTotalSpace.homeomorph F V x₀)
  let f : EB × F → F := Prod.snd ∘ (extChartAt (IB.prod 𝓘(𝕜, F))
    (ManifoldTotalSpace.homeomorph F V j₀) ∘
    (extChartAt (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V i₀)).symm)
  have hy₀ : y₀ = (extChartAt IB i₀.proj x₀.proj, (trivializationAt F V i₀.proj x₀).2) := by
    dsimp only [y₀]
    rw [ManifoldTotalSpace.extChartAt_homeomorph_apply,
      (trivializationAt F V i₀.proj).coe_fst' hbi.1, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id_eq]
  have hLHS : HasFDerivAt (f ∘ fun w : F ↦ y₀ + ContinuousLinearMap.inr 𝕜 EB F w)
      (coordChange IB 𝓘(𝕜, F) F V (ManifoldTotalSpace.homeomorph F V i₀)
        (ManifoldTotalSpace.homeomorph F V j₀) (ManifoldTotalSpace.homeomorph F V x₀)) 0 := by
    have hmap : HasFDerivWithinAt f ((ContinuousLinearMap.snd 𝕜 EB F).comp
        (tangentCoordChange (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V i₀)
          (ManifoldTotalSpace.homeomorph F V j₀) (ManifoldTotalSpace.homeomorph F V x₀)))
        (range (IB.prod 𝓘(𝕜, F))) (y₀ + ContinuousLinearMap.inr 𝕜 EB F (0 : F)) := by
      rw [map_zero, add_zero]
      exact hasFDerivAt_snd.comp_hasFDerivWithinAt y₀ (hasFDerivWithinAt_tangentCoordChange
        ⟨by rw [extChartAt_source]; exact hx.1, by rw [extChartAt_source]; exact hx.2⟩)
    rw [coordChange, ← ContinuousLinearMap.comp_assoc, ← hasFDerivWithinAt_univ]
    exact HasFDerivWithinAt.comp (0 : F) hmap (HasFDerivWithinAt.const_add y₀
      ((ContinuousLinearMap.inr 𝕜 EB F).hasFDerivWithinAt (x := (0 : F)) (s := univ))) fun w _ ↦ by
      rw [hy₀, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, ModelWithCorners.range_prod]
      exact ⟨extChartAt_target_subset_range _ ((extChartAt IB i₀.proj).map_source
        (by rw [extChartAt_source]; exact hbi.2)), _, rfl⟩
  let L : F →L[𝕜] F :=
    (trivializationAt F V i₀.proj).coordChangeL 𝕜 (trivializationAt F V j₀.proj) x₀.proj
  have heq : (f ∘ fun w : F ↦ y₀ + ContinuousLinearMap.inr 𝕜 EB F w) =
      fun w : F ↦ L ((trivializationAt F V i₀.proj x₀).2) + L w := by
    funext w
    simp only [f, Function.comp_apply, hy₀, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
      add_zero, ← map_add]
    exact extChartAt_snd_symm_eq_coordChangeL i₀ j₀ hbi.1 hbi.2 hbj.1 _
  exact hLHS.unique (heq ▸ HasFDerivAt.const_add _ L.hasFDerivAt)

/-- **Canonical identification `V_x V ≃L[𝕜] V (π x)` for a `C^1` vector bundle.** Every fibre of
a vector bundle is a vector space, so its vertical tangent space at `x` is canonically isomorphic
to the fibre `V (π x)` itself, with no choice of connection. -/
def equivFiber (x : ManifoldTotalSpace F V) :
    VerticalBundle IB 𝓘(𝕜, F) F V x ≃L[𝕜] V ((ManifoldTotalSpace.homeomorph F V).symm x).proj :=
  ((trivializationAt F V
    ((ManifoldTotalSpace.homeomorph F V).symm x).proj).continuousLinearEquivAt 𝕜
    ((ManifoldTotalSpace.homeomorph F V).symm x).proj
    (mem_baseSet_trivializationAt F V _)).symm

/-- `equivFiber` reads a vertical vector in the preferred trivialization at `π x` via `symm`. -/
theorem equivFiber_apply (x : ManifoldTotalSpace F V) (v : VerticalBundle IB 𝓘(𝕜, F) F V x) :
    equivFiber x v =
      (trivializationAt F V ((ManifoldTotalSpace.homeomorph F V).symm x).proj).symm
        ((ManifoldTotalSpace.homeomorph F V).symm x).proj v :=
  (rfl)

/-- The inverse of `equivFiber` reads a vector of `V (π x)` in the preferred trivialization at
`π x`. -/
@[simp]
theorem equivFiber_symm_apply (x : ManifoldTotalSpace F V)
    (w : V ((ManifoldTotalSpace.homeomorph F V).symm x).proj) :
    (equivFiber (IB := IB) x).symm w =
      (trivializationAt F V ((ManifoldTotalSpace.homeomorph F V).symm x).proj
        ⟨((ManifoldTotalSpace.homeomorph F V).symm x).proj, w⟩).2 :=
  (rfl)

/-- **Naturality of `equivFiber` across charts.** In any preferred chart `i` containing `x`, the
trivialization of `V` at `π i` applied to `equivFiber x v` equals the vertical trivialization at
`i` applied to `(x, v)`. -/
theorem trivializationAt_equivFiber {i x : ManifoldTotalSpace F V}
    (hx : x ∈ (chartAt (ModelProd HB F) i).source) (v : VerticalBundle IB 𝓘(𝕜, F) F V x) :
    (trivializationAt F V ((ManifoldTotalSpace.homeomorph F V).symm i).proj
        ⟨((ManifoldTotalSpace.homeomorph F V).symm x).proj, equivFiber x v⟩).2 =
      (trivializationAt F (VerticalBundle IB 𝓘(𝕜, F) F V) i ⟨x, v⟩).2 := by
  have hbi := (ManifoldTotalSpace.proj_mem_of_mem_chart_source hx).1
  have hbx := mem_baseSet_trivializationAt F V ((ManifoldTotalSpace.homeomorph F V).symm x).proj
  let v₀ : F := v
  change _ = coordChange IB 𝓘(𝕜, F) F V x i x v₀
  rw [coordChange_eq_coordChangeL ⟨mem_chart_source _ x, hx⟩, ContinuousLinearEquiv.coe_coe,
    Trivialization.coordChangeL_apply _ _ ⟨hbx, hbi⟩, ← equivFiber_apply]

/-- **Smoothness of `equivFiber` on total spaces.** In the preferred bundle charts of `VV` and `V`,
`(x, v) ↦ ⟨π x, equivFiber x v⟩` drops the base-point fibre coordinate `((u, w), v) ↦ (u, v)`, so
it is `C^n` for every `n : ℕ∞ω` as soon as `B` and `V` are `C^1`. -/
theorem contMDiff_equivFiber (n : ℕ∞ω) :
    ContMDiff ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace F (VerticalBundle IB 𝓘(𝕜, F) F V) ↦
        (⟨((ManifoldTotalSpace.homeomorph F V).symm p.proj).proj, equivFiber p.proj p.2⟩ :
          TotalSpace F V)) := by
  intro p₀
  have hproj_v : ContMDiffAt ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      TotalSpace.proj p₀ := Bundle.contMDiffAt_proj (IB := IB.prod 𝓘(𝕜, F)) _
  have hbase : ContMDiffAt ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, F)) IB n
      (fun p : TotalSpace F (VerticalBundle IB 𝓘(𝕜, F) F V) ↦
        ((ManifoldTotalSpace.homeomorph F V).symm p.proj).proj) p₀ :=
    (ManifoldTotalSpace.contMDiff_proj n F V IB 𝓘(𝕜, F) p₀.proj).comp p₀ hproj_v
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hbase, ?_⟩
  have hcoord := (Bundle.contMDiffAt_totalSpace_iff.1
    (contMDiffAt_id (I := (IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, F)) (n := n) (x := p₀))).2
  have hU : TotalSpace.proj ⁻¹' (chartAt (ModelProd HB F) p₀.proj).source ∈ 𝓝 p₀ :=
    ((FiberBundle.continuous_proj F (VerticalBundle IB 𝓘(𝕜, F) F V)).isOpen_preimage _
      (chartAt _ p₀.proj).open_source).mem_nhds (mem_chart_source (ModelProd HB F) p₀.proj)
  refine hcoord.congr_of_eventuallyEq ?_
  filter_upwards [hU] with p hp
  exact trivializationAt_equivFiber hp p.2

end VerticalBundle

end VectorBundle

end TauCeti
