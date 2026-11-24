/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Boundary
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Boundary
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Combinatorial
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
import TauCeti.Geometry.Manifold.Boundary.Invariance
import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic

/-!
# Charted spaces from combinatorial manifolds

The weak realization of a positive-dimensional combinatorial manifold carries a charted-space
structure modelled on the Euclidean half-space. At an interior vertex, its combinatorial-sphere
link gives an open Euclidean ball chart; the standard open embedding of Euclidean space into the
interior of the half-space turns this into a half-space chart. At a boundary vertex, its
combinatorial-ball link directly gives an open half-ball chart. The open vertex stars cover the
realization, so choosing one such chart at each point produces an atlas.

For this charted space, the topological manifold boundary `(𝓡∂ (n + 1)).boundary (Realization K)`
coincides with the subpolyhedron of the combinatorial boundary `manifoldBoundary K`
(`IsCombinatorialManifold.boundary_realizationChartedSpace`), and in particular is empty if and
only if `manifoldBoundary K = ⊥`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2--3.
-/

public section

noncomputable section

open AbstractSimplicialComplex Set Topology
open scoped Manifold

namespace PreAbstractSimplicialComplex

universe u

variable {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {n : ℕ}

/-! ### A common half-space model -/

/-- Every vertex of a positive-dimensional combinatorial manifold supplies a half-space chart
whose source is its open star. Interior charts land in the interior of the half-space; boundary
charts are the half-ball charts coming from combinatorial-ball links. -/
theorem IsCombinatorialManifold.exists_openPartialHomeomorph_openStar_halfSpace
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1))
    (hv : ({v} : Finset ι) ∈ K) :
    ∃ c : OpenPartialHomeomorph (Realization K) (EuclideanHalfSpace (n + 1)),
      c.source = openStarRealization K v := by
  rcases (isCombinatorialManifold_succ_iff.mp h) hv with hsphere | hball
  · obtain ⟨c, hc, -, -, -⟩ := hsphere.exists_openPartialHomeomorph_openStar_ball
    let j : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1)))
        (EuclideanHalfSpace (n + 1)) :=
      (TauCeti.EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph
    refine ⟨c.trans j, ?_⟩
    simp [hc, j]
  · obtain ⟨c, hc, -, -, -⟩ :=
      hball.exists_openPartialHomeomorph_openStar_halfBall
    exact ⟨c, hc⟩

/-- Every point of the realization of a positive-dimensional combinatorial manifold lies in the
source of a half-space chart whose source is the open star of a vertex. -/
theorem IsCombinatorialManifold.exists_openPartialHomeomorph_mem_source
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1))
    (x : Realization K) :
    ∃ c : OpenPartialHomeomorph (Realization K) (EuclideanHalfSpace (n + 1)),
      ∃ v, ({v} : Finset ι) ∈ K ∧ c.source = openStarRealization K v ∧ x ∈ c.source := by
  obtain ⟨v, hx⟩ := K.exists_mem_openStarRealization x
  have hv : ({v} : Finset ι) ∈ K :=
    singleton_mem_of_mem (support_mem K x)
      ((K.mem_openStarRealization_iff_mem_support).mp hx)
  obtain ⟨c, hc⟩ := h.exists_openPartialHomeomorph_openStar_halfSpace hv
  exact ⟨c, v, hv, hc, hc.symm ▸ hx⟩

/-! ### The vertex-chart atlas -/

/-- The charted-space structure on the weak realization of a positive-dimensional combinatorial
manifold. Its preferred charts are chosen from the interior or boundary vertex charts supplied by
the link condition. -/
@[instance_reducible] noncomputable def IsCombinatorialManifold.realizationChartedSpace
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    ChartedSpace (EuclideanHalfSpace (n + 1)) (Realization K) where
  atlas := range fun x => Classical.choose (h.exists_openPartialHomeomorph_mem_source x)
  chartAt x := Classical.choose (h.exists_openPartialHomeomorph_mem_source x)
  mem_chart_source x :=
    (Classical.choose_spec (h.exists_openPartialHomeomorph_mem_source x)).choose_spec.2.2
  chart_mem_atlas _ := mem_range_self _

/-- The preferred chart at `x` of `IsCombinatorialManifold.realizationChartedSpace` has the open
star of a vertex as its source. -/
theorem IsCombinatorialManifold.exists_chartAt_source_eq_openStar
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1))
    (x : Realization K) :
    letI := h.realizationChartedSpace
    ∃ v, ({v} : Finset ι) ∈ K ∧
      (chartAt (EuclideanHalfSpace (n + 1)) x).source = openStarRealization K v := by
  obtain ⟨v, hv, hc, -⟩ :=
    Classical.choose_spec (h.exists_openPartialHomeomorph_mem_source x)
  exact ⟨v, hv, hc⟩

/-- Every chart in the atlas of `IsCombinatorialManifold.realizationChartedSpace` has the open
star of a vertex as its source. -/
theorem IsCombinatorialManifold.exists_source_eq_openStar_of_mem_atlas
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1))
    {c : OpenPartialHomeomorph (Realization K) (EuclideanHalfSpace (n + 1))} :
    letI := h.realizationChartedSpace
    c ∈ atlas (EuclideanHalfSpace (n + 1)) (Realization K) →
      ∃ v, ({v} : Finset ι) ∈ K ∧ c.source = openStarRealization K v := by
  rintro ⟨x, rfl⟩
  exact h.exists_chartAt_source_eq_openStar x

/-- The weak realization of a positive-dimensional combinatorial manifold is a topological
manifold with boundary, for the charted-space structure assembled from its vertex links. -/
theorem IsCombinatorialManifold.realization_isManifold
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    letI := h.realizationChartedSpace
    IsManifold (𝓡∂ (n + 1)) 0 (Realization K) := by
  let := h.realizationChartedSpace
  infer_instance

/-! ### Topological boundary equals combinatorial boundary -/

private theorem mem_boundary_iff_chart_apply_zero
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1))
    {c : OpenPartialHomeomorph (Realization K) (EuclideanHalfSpace (n + 1))}
    {x : Realization K} (hx : x ∈ c.source) :
    letI := h.realizationChartedSpace
    x ∈ (𝓡∂ (n + 1)).boundary (Realization K) ↔ (c x).val 0 = 0 := by
  let := h.realizationChartedSpace
  rw [ModelWithCorners.mem_boundary_iff_mem_frontier_range_of_finiteDimensional hx,
    frontier_range_modelWithCornersEuclideanHalfSpace]
  simp [eq_comm]

private theorem support_starLinkProjection
    (x : puncturedClosedStar K v) :
    (starLinkProjection K v x).val.val.support = x.val.val.support.erase v := by
  ext w
  simp only [Finsupp.mem_support_iff, starLinkProjection_apply, Finset.mem_erase, ne_eq]
  by_cases hwv : w = v
  · simp [hwv]
  · have hpos : (1 - x.val.val v)⁻¹ ≠ 0 :=
      inv_ne_zero (sub_pos.mpr ((mem_puncturedClosedStar K v x.val).mp x.property).2).ne'
    simp [hwv, hpos]

/-- The vertex link as an `AbstractSimplicialComplex` on the subtype of link vertices. -/
private def linkAbstractComplex (K : AbstractSimplicialComplex ι) (v : ι) :
    AbstractSimplicialComplex
      {w : ι // ({w} : Finset ι) ∈ link K.toPreAbstractSimplicialComplex {v}} where
  faces := {σ | σ.image Subtype.val ∈ link K.toPreAbstractSimplicialComplex {v}}
  isRelLowerSet_faces := by
    intro σ hσ
    refine ⟨(Finset.image_nonempty.mp
      ((link K.toPreAbstractSimplicialComplex {v}).isRelLowerSet_faces hσ).1),
      fun τ hτσ hτ => ?_⟩
    exact ((link K.toPreAbstractSimplicialComplex {v}).isRelLowerSet_faces hσ).2
      (Finset.image_subset_image hτσ) (hτ.image _)
  singleton_mem w := by
    change ({w} : Finset _).image Subtype.val ∈ link K.toPreAbstractSimplicialComplex {v}
    rw [Finset.image_singleton]
    exact w.property

private theorem map_linkAbstractComplex (K : AbstractSimplicialComplex ι) (v : ι) :
    (linkAbstractComplex K v).toPreAbstractSimplicialComplex.map Subtype.val =
      link K.toPreAbstractSimplicialComplex {v} := by
  classical
  refine SetLike.ext fun σ => ⟨?_, fun hσ => ?_⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact hτ
  · have hsub : ∀ w ∈ σ, ({w} : Finset ι) ∈ link K.toPreAbstractSimplicialComplex {v} := fun w hw =>
      singleton_mem_of_mem hσ hw
    let σ' : Finset {w : ι // ({w} : Finset ι) ∈ link K.toPreAbstractSimplicialComplex {v}} :=
      σ.preimage Subtype.val Subtype.val_injective.injOn
    have him : σ'.image Subtype.val = σ := by
      ext w
      simp only [σ', Finset.mem_image, Finset.mem_preimage, Subtype.exists, exists_and_right,
        exists_eq_right]
      exact ⟨fun ⟨_, h⟩ => h, fun hw => ⟨hsub w hw, hw⟩⟩
    refine ⟨σ', ?_, him⟩
    change σ'.image Subtype.val ∈ link K.toPreAbstractSimplicialComplex {v}
    rwa [him]

private theorem notMem_boundary_realizationChartedSpace_of_sphere
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1))
    {v : ι} {x : Realization K} (hvx : x ∈ openStarRealization K v)
    (hsphere : IsCombinatorialSphere (link K.toPreAbstractSimplicialComplex {v}) n) :
    letI := h.realizationChartedSpace
    x ∈ (𝓡∂ (n + 1)).boundary (Realization K) ↔
      x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex := by
  let := h.realizationChartedSpace
  have hv : ({v} : Finset ι) ∈ K :=
    singleton_mem_of_mem (support_mem K x) ((K.mem_openStarRealization_iff_mem_support).mp hvx)
  obtain ⟨c, hc, -, -, -⟩ := hsphere.exists_openPartialHomeomorph_openStar_ball
  let j : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanHalfSpace (n + 1)) :=
    (TauCeti.EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph
  have hsrc : x ∈ (c.trans j).source := by
    simpa [hc, j] using hvx
  rw [mem_boundary_iff_chart_apply_zero h hsrc]
  have hpos : ((c.trans j) x).val 0 ≠ 0 := by
    change (TauCeti.EuclideanHalfSpace.interiorEmbedding n (c x)).val 0 ≠ 0
    rw [TauCeti.EuclideanHalfSpace.interiorEmbedding_coe_apply_zero]
    exact (Real.exp_pos _).ne'
  have hnotbd : x.val.support ∉ manifoldBoundary K.toPreAbstractSimplicialComplex := by
    intro hxbd
    have hvbd : ({v} : Finset ι) ∈ manifoldBoundary K.toPreAbstractSimplicialComplex :=
      (manifoldBoundary K.toPreAbstractSimplicialComplex).isRelLowerSet_faces.mem_of_le
        hxbd (Finset.singleton_subset_iff.mpr
          ((K.mem_openStarRealization_iff_mem_support).mp hvx))
        (Finset.singleton_nonempty v)
    exact ((h.notMem_manifoldBoundary_iff hv (by simp)).mpr hsphere) hvbd
  exact iff_of_false hpos hnotbd

private theorem mem_boundary_realizationChartedSpace_vertex_of_ball
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1))
    {v : ι} (hball : IsCombinatorialBall (link K.toPreAbstractSimplicialComplex {v}) n) :
    letI := h.realizationChartedSpace
    vertex K v ∈ (𝓡∂ (n + 1)).boundary (Realization K) ↔
      (vertex K v).val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex := by
  let := h.realizationChartedSpace
  obtain ⟨c, hc, -, hc0, -⟩ := hball.exists_openPartialHomeomorph_openStar_halfBall
  have hsrc : vertex K v ∈ c.source := by
    simp [hc, mem_openStarRealization]
  rw [mem_boundary_iff_chart_apply_zero h hsrc, hc0]
  have hvbd : ({v} : Finset ι) ∈ manifoldBoundary K.toPreAbstractSimplicialComplex :=
    h.singleton_mem_manifoldBoundary_iff.mpr hball
  exact iff_of_true rfl (by simpa [vertex_val] using hvbd)

private theorem boundary_realizationChartedSpace_aux :
    ∀ (n : ℕ) {ι : Type u} [DecidableEq ι] {K : AbstractSimplicialComplex ι}
      (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)),
      letI := h.realizationChartedSpace
      (𝓡∂ (n + 1)).boundary (Realization K) =
        {x : Realization K |
          x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex} := by
  intro n
  induction n with
  | zero =>
    intro ι _ K h
    let := h.realizationChartedSpace
    ext x
    change x ∈ (𝓡∂ 1).boundary (Realization K) ↔
      x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex
    obtain ⟨v, hvx⟩ := K.exists_mem_openStarRealization x
    have hv : ({v} : Finset ι) ∈ K :=
      singleton_mem_of_mem (support_mem K x) ((K.mem_openStarRealization_iff_mem_support).mp hvx)
    rcases (isCombinatorialManifold_succ_iff.mp h) hv with hsphere | hball
    · exact notMem_boundary_realizationChartedSpace_of_sphere h hvx hsphere
    · by_cases hxv : x = vertex K v
      · subst hxv
        exact mem_boundary_realizationChartedSpace_vertex_of_ball h hball
      · have hxlt : x.val v < 1 :=
          lt_of_le_of_ne (Realization.le_one K x v)
            ((Realization.eq_vertex_iff K x v).not.mp hxv)
        let x' : puncturedClosedStar K v :=
          ⟨x, (mem_puncturedClosedStar K v x).mpr
            ⟨openStarRealization_subset_closedStarRealization K v hvx, hxlt⟩⟩
        let y := starLinkProjection K v x'
        obtain ⟨a⟩ := hball.nonempty_homeomorph_closedBall link_le
        obtain ⟨c, hc, -, -, -, hzero⟩ :=
          exists_openPartialHomeomorph_openStar_halfBall_of_homeomorph hball.finite_faces a
        have hsrc : x ∈ c.source := hc.symm ▸ hvx
        rw [mem_boundary_iff_chart_apply_zero h hsrc, hzero x' hvx]
        have hnorm : ‖(a ⟨y.val, (mem_geometricLink_iff K v _).mp y.property⟩ :
            EuclideanSpace ℝ (Fin 0))‖ ≠ 1 := by
          simp [Subsingleton.elim _ (0 : EuclideanSpace ℝ (Fin 0))]
        have hnotbd : x.val.support ∉ manifoldBoundary K.toPreAbstractSimplicialComplex := by
          intro hxbd
          have hlink : y.val.val.support ∈
              manifoldBoundary (link K.toPreAbstractSimplicialComplex {v}) := by
            rw [← h.link_manifoldBoundary {v}, mem_link_nonempty]
            refine ⟨(K.isRelLowerSet_faces (support_mem K y.val)).1, ?_, ?_⟩
            · rw [support_starLinkProjection]
              exact Finset.disjoint_singleton_right.mpr (Finset.notMem_erase v _)
            · have hu : x.val.support.erase v ∪ {v} = x.val.support := by
                simpa [Finset.union_singleton] using
                  Finset.insert_erase ((K.mem_openStarRealization_iff_mem_support).mp hvx)
              rwa [support_starLinkProjection, hu]
          rw [hball.manifoldBoundary_eq_bot_of_zero] at hlink
          exact hlink
        exact iff_of_false hnorm hnotbd
  | succ m ih =>
    intro ι _ K h
    let := h.realizationChartedSpace
    ext x
    change x ∈ (𝓡∂ (m + 2)).boundary (Realization K) ↔
      x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex
    obtain ⟨v, hvx⟩ := K.exists_mem_openStarRealization x
    have hv : ({v} : Finset ι) ∈ K :=
      singleton_mem_of_mem (support_mem K x) ((K.mem_openStarRealization_iff_mem_support).mp hvx)
    rcases (isCombinatorialManifold_succ_iff.mp h) hv with hsphere | hball
    · exact notMem_boundary_realizationChartedSpace_of_sphere h hvx hsphere
    · by_cases hxv : x = vertex K v
      · subst hxv
        exact mem_boundary_realizationChartedSpace_vertex_of_ball h hball
      · have hxlt : x.val v < 1 :=
          lt_of_le_of_ne (Realization.le_one K x v)
            ((Realization.eq_vertex_iff K x v).not.mp hxv)
        let x' : puncturedClosedStar K v :=
          ⟨x, (mem_puncturedClosedStar K v x).mpr
            ⟨openStarRealization_subset_closedStarRealization K v hvx, hxlt⟩⟩
        let y := starLinkProjection K v x'
        obtain ⟨a⟩ := hball.nonempty_homeomorph_closedBall link_le
        obtain ⟨c, hc, -, -, -, hzero⟩ :=
          exists_openPartialHomeomorph_openStar_halfBall_of_homeomorph hball.finite_faces a
        have hsrc : x ∈ c.source := hc.symm ▸ hvx
        let L := linkAbstractComplex K v
        have hLmap : L.toPreAbstractSimplicialComplex.map Subtype.val =
            link K.toPreAbstractSimplicialComplex {v} :=
          map_linkAbstractComplex K v
        have hLball : IsCombinatorialBall L.toPreAbstractSimplicialComplex (m + 1) := by
          rw [← isCombinatorialBall_map_iff Subtype.val_injective, hLmap]
          exact hball
        have hLman : IsCombinatorialManifold L.toPreAbstractSimplicialComplex (m + 1) :=
          hLball.isCombinatorialManifold
        let rel : Realization L ≃ₜ
            {z : Realization K // z.val.support ∈ link K.toPreAbstractSimplicialComplex {v}} :=
          L.toPreAbstractSimplicialComplex.realizationRelabelingHomeomorph
            (Function.Embedding.subtype _) hLmap rfl link_le
        let z : Realization L := rel.symm ⟨y.val, (mem_geometricLink_iff K v _).mp y.property⟩
        let φ : Realization L ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
          rel.trans a
        let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨by simp⟩
        let := hLman.realizationChartedSpace
        have hnorm_iff :
            ‖(a ⟨y.val, (mem_geometricLink_iff K v _).mp y.property⟩ :
                EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 ↔
              z.val.support ∈ manifoldBoundary L.toPreAbstractSimplicialComplex := by
          have hφz : (φ z : EuclideanSpace ℝ (Fin (m + 1))) =
              a ⟨y.val, (mem_geometricLink_iff K v _).mp y.property⟩ := by
            simp [φ, z]
          rw [← hφz, ← TauCeti.isBoundaryPoint_closedBall_iff (n := m + 1),
            ← φ.isBoundaryPoint_iff (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) rfl z]
          change z ∈ (𝓡∂ (m + 1)).boundary (Realization L) ↔
            z.val.support ∈ manifoldBoundary L.toPreAbstractSimplicialComplex
          rw [ih hLman]
          rfl
        have hsupp_rel : z.val.support.image Subtype.val = y.val.val.support := by
          have hrelz : (rel z).val.val = y.val.val := by
            have := congrArg (fun w => w.val.val) (rel.apply_symm_apply
              ⟨y.val, (mem_geometricLink_iff K v _).mp y.property⟩)
            simp [z]
          have hmapz : (rel z).val.val =
              Finsupp.mapDomain (Function.Embedding.subtype _) z.val :=
            L.toPreAbstractSimplicialComplex.realizationRelabelingHomeomorph_val
              (Function.Embedding.subtype _) hLmap rfl link_le z
          rw [← hrelz, hmapz, Finsupp.support_mapDomain_embedding, Finset.map_eq_image]
          rfl
        have hbdmap :
            (manifoldBoundary L.toPreAbstractSimplicialComplex).map Subtype.val =
              manifoldBoundary (link K.toPreAbstractSimplicialComplex {v}) := by
          rw [PreAbstractSimplicialComplex.map_manifoldBoundary _ Subtype.val_injective, hLmap]
        have hmem_link :
            y.val.val.support ∈ manifoldBoundary (link K.toPreAbstractSimplicialComplex {v}) ↔
              z.val.support ∈ manifoldBoundary L.toPreAbstractSimplicialComplex := by
          rw [← hbdmap, mem_map_iff]
          constructor
          · rintro ⟨σ, hσ, hσeq⟩
            have hseq : σ = z.val.support :=
              Finset.image_injective Subtype.val_injective (hσeq.trans hsupp_rel.symm)
            exact hseq ▸ hσ
          · exact fun hz => ⟨z.val.support, hz, hsupp_rel⟩
        have hmem_K : x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex ↔
            y.val.val.support ∈ manifoldBoundary (link K.toPreAbstractSimplicialComplex {v}) := by
          rw [← h.link_manifoldBoundary {v}, mem_link_nonempty]
          have hu : x.val.support.erase v ∪ {v} = x.val.support := by
            simpa [Finset.union_singleton] using
              Finset.insert_erase ((K.mem_openStarRealization_iff_mem_support).mp hvx)
          constructor
          · intro hxbd
            refine ⟨(K.isRelLowerSet_faces (support_mem K y.val)).1, ?_, ?_⟩
            · rw [support_starLinkProjection]
              exact Finset.disjoint_singleton_right.mpr (Finset.notMem_erase v _)
            · rwa [support_starLinkProjection, hu]
          · rintro ⟨-, -, hxy⟩
            rwa [support_starLinkProjection, hu] at hxy
        rw [mem_boundary_iff_chart_apply_zero h hsrc, hzero x' hvx, hnorm_iff, ← hmem_link,
          ← hmem_K]

/-- The topological manifold boundary of `IsCombinatorialManifold.realizationChartedSpace`
consists of the points whose barycentric support belongs to `manifoldBoundary K`. -/
theorem IsCombinatorialManifold.boundary_realizationChartedSpace
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    letI := h.realizationChartedSpace
    (𝓡∂ (n + 1)).boundary (Realization K) =
      {x : Realization K | x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex} :=
  boundary_realizationChartedSpace_aux n h

/-- A point of the weak realization of a positive-dimensional combinatorial manifold lies in the
topological manifold boundary if and only if its support belongs to `manifoldBoundary K`. -/
theorem IsCombinatorialManifold.mem_boundary_realizationChartedSpace_iff
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) (x : Realization K) :
    letI := h.realizationChartedSpace
    x ∈ (𝓡∂ (n + 1)).boundary (Realization K) ↔
      x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex := by
  let := h.realizationChartedSpace
  rw [h.boundary_realizationChartedSpace]
  rfl

/-- The topological manifold interior of `IsCombinatorialManifold.realizationChartedSpace`
consists of the points whose barycentric support does not belong to `manifoldBoundary K`. -/
theorem IsCombinatorialManifold.interior_realizationChartedSpace
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    letI := h.realizationChartedSpace
    (𝓡∂ (n + 1)).interior (Realization K) =
      {x : Realization K | x.val.support ∉ manifoldBoundary K.toPreAbstractSimplicialComplex} := by
  let := h.realizationChartedSpace
  rw [← ModelWithCorners.compl_boundary, h.boundary_realizationChartedSpace]
  rfl

/-- A point of the weak realization of a positive-dimensional combinatorial manifold lies in the
topological manifold interior if and only if its support does not belong to `manifoldBoundary K`. -/
theorem IsCombinatorialManifold.mem_interior_realizationChartedSpace_iff
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) (x : Realization K) :
    letI := h.realizationChartedSpace
    x ∈ (𝓡∂ (n + 1)).interior (Realization K) ↔
      x.val.support ∉ manifoldBoundary K.toPreAbstractSimplicialComplex := by
  let := h.realizationChartedSpace
  rw [h.interior_realizationChartedSpace]
  rfl

/-- The topological manifold boundary of a positive-dimensional combinatorial manifold realization
is empty if and only if its combinatorial boundary is `⊥`. -/
theorem IsCombinatorialManifold.boundary_realizationChartedSpace_eq_empty_iff
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    letI := h.realizationChartedSpace
    (𝓡∂ (n + 1)).boundary (Realization K) = ∅ ↔
      manifoldBoundary K.toPreAbstractSimplicialComplex = ⊥ := by
  let := h.realizationChartedSpace
  rw [h.boundary_realizationChartedSpace, Set.eq_empty_iff_forall_notMem]
  refine ⟨fun hnot => eq_bot_iff.mpr fun σ hσ => ?_, fun hbot x hx => ?_⟩
  · obtain ⟨v, hv⟩ := ((manifoldBoundary K.toPreAbstractSimplicialComplex).isRelLowerSet_faces hσ).1
    have hvbd : ({v} : Finset ι) ∈ manifoldBoundary K.toPreAbstractSimplicialComplex :=
      singleton_mem_of_mem hσ hv
    refine hnot (vertex K v) ?_
    simpa [vertex_val] using hvbd
  · rw [hbot] at hx
    exact hx

end PreAbstractSimplicialComplex
