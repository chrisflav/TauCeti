/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.ChartedSpace
public import TauCeti.Geometry.Manifold.Boundary.Invariance
public import TauCeti.Geometry.Manifold.Triangulation.Puncture
public import TauCeti.Topology.Triangulable.FiniteCWType

/-!
# Piecewise-linear structures on topological manifolds

A **PL structure** `TauCeti.PLStructure d M` of dimension `d` on a topological space `M` is a
triangulation of `M` by an abstract simplicial complex on a finite vertex type that is a
combinatorial `d`-manifold, together with a homeomorphism from its geometric realization onto `M`.
For compact surfaces (`d = 2`), `TauCeti.SurfacePLStructure M` is an abbreviation for
`PLStructure 2 M`.

The homeomorphism `s.e` is part of the data: precomposing `s.e` with a non-PL self-homeomorphism
of the realization produces a distinct PL structure on the same underlying complex. Every space
carrying a `PLStructure d M` is automatically compact, Hausdorff, triangulable, and of finite
CW type; in positive dimensions `d = n + 1`, its manifold boundary relative to any
`EuclideanHalfSpace (n + 1)` charted structure coincides with the image of `manifoldBoundary s.K`
under `s.e`, by topological invariance of the manifold boundary
(`Homeomorph.image_boundary`). Moreover, any finite subset of `M` can be made a set of vertices
in a refined `PLStructure d M` by point-by-point stellar subdivision, so complements of finite sets
also have finite CW type.

## Main definitions

* `TauCeti.PLStructure d M`: a `d`-dimensional finite combinatorial-manifold triangulation of `M`.
* `TauCeti.SurfacePLStructure M`: abbreviation for `TauCeti.PLStructure 2 M`.
* `TauCeti.PLStructure.map`: transport of a PL structure along a homeomorphism.

## Main results

* `TauCeti.PLStructure.compactSpace`, `t2Space`, `isTriangulable`, `finiteCWType`:
  spaces admitting a PL structure are compact Hausdorff triangulable and of finite CW type.
* `TauCeti.PLStructure.boundary_eq`, `boundary_eq_empty_iff`:
  identification of the topological manifold boundary with the realization of
  `PreAbstractSimplicialComplex.manifoldBoundary s.K`.
* `TauCeti.PLStructure.exists_plStructure_vertex_image`, `finiteCWType_compl`:
  finite subsets can be realized as vertex sets of a refined PL structure, and their complements
  have finite CW type.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 1–3.
-/

public section

open Set AbstractSimplicialComplex PreAbstractSimplicialComplex
open scoped Manifold

namespace TauCeti

universe u v w

open Classical in
/-- A `d`-dimensional **piecewise-linear structure** on a topological space `M`: a finite
combinatorial `d`-manifold `K` together with a homeomorphism from its realization onto `M`. The
homeomorphism is part of the data. -/
structure PLStructure (d : ℕ) (M : Type u) [TopologicalSpace M] where
  /-- The vertex type of the triangulating complex. -/
  ι : Type
  /-- The triangulation has finitely many vertices. -/
  finite_ι : Finite ι
  /-- The triangulating abstract simplicial complex. -/
  K : AbstractSimplicialComplex ι
  /-- The complex is a combinatorial `d`-manifold, possibly with boundary. -/
  isCombinatorialManifold : K.toPreAbstractSimplicialComplex.IsCombinatorialManifold d
  /-- The triangulation homeomorphism. -/
  e : Realization K ≃ₜ M

attribute [instance] PLStructure.finite_ι

/-- A two-dimensional piecewise-linear structure on `M`. -/
abbrev SurfacePLStructure (M : Type u) [TopologicalSpace M] := PLStructure 2 M

namespace PLStructure

section Map

variable {d : ℕ} {M : Type u} [TopologicalSpace M] {N : Type v} [TopologicalSpace N]

/-- Transport of a PL structure along a homeomorphism. -/
@[expose]
noncomputable def map (s : PLStructure d M) (f : M ≃ₜ N) : PLStructure d N where
  ι := s.ι
  finite_ι := s.finite_ι
  K := s.K
  isCombinatorialManifold := s.isCombinatorialManifold
  e := s.e.trans f

/-- The vertex index type of `s.map f` is `s.ι`. -/
@[simp]
theorem map_ι (s : PLStructure d M) (f : M ≃ₜ N) : (s.map f).ι = s.ι := rfl

/-- The underlying simplicial complex of `s.map f` is `s.K`. -/
@[simp]
theorem map_K (s : PLStructure d M) (f : M ≃ₜ N) : (s.map f).K = s.K := rfl

/-- The homeomorphism of `s.map f` is `s.e.trans f`. -/
@[simp]
theorem map_e (s : PLStructure d M) (f : M ≃ₜ N) : (s.map f).e = s.e.trans f := rfl

end Map

variable {d n : ℕ} {M : Type u} [TopologicalSpace M]

/-- A space carrying a PL structure is compact. -/
theorem compactSpace (s : PLStructure d M) : CompactSpace M :=
  s.e.compactSpace

/-- A space carrying a PL structure is Hausdorff. -/
theorem t2Space (s : PLStructure d M) : T2Space M :=
  s.e.t2Space

/-- A space carrying a PL structure is triangulable in any universe. -/
theorem isTriangulable (s : PLStructure d M) : IsTriangulable.{w} M := by
  have : CompactSpace M := s.compactSpace
  have h0 : IsTriangulable.{0} M := (isTriangulable_iff M).mpr ⟨s.ι, s.K, ⟨s.e⟩⟩
  exact h0.lift_of_compactSpace

/-- A space carrying a PL structure has finite CW type. -/
theorem finiteCWType (s : PLStructure d M) : FiniteCWType M := by
  have : CompactSpace M := s.compactSpace
  exact TauCeti.IsTriangulable.finiteCWType s.isTriangulable.{u, 0}

open Classical in
/-- The topological manifold boundary of a space equipped with a positive-dimensional PL structure
and a half-space charted structure is the image under `s.e` of the points whose barycentric support
lies in `manifoldBoundary s.K`. -/
theorem boundary_eq (s : PLStructure (n + 1) M)
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] :
    (𝓡∂ (n + 1)).boundary M =
      s.e '' {x : Realization s.K |
        x.val.support ∈ manifoldBoundary s.K.toPreAbstractSimplicialComplex} := by
  let := s.isCombinatorialManifold.realizationChartedSpace
  rw [← s.e.image_boundary (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) rfl,
    s.isCombinatorialManifold.boundary_realizationChartedSpace]

open Classical in
/-- The topological manifold boundary of a space with a positive-dimensional PL structure is empty
if and only if its combinatorial manifold boundary `manifoldBoundary s.K` is `⊥`. -/
theorem boundary_eq_empty_iff (s : PLStructure (n + 1) M)
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] :
    (𝓡∂ (n + 1)).boundary M = ∅ ↔
      manifoldBoundary s.K.toPreAbstractSimplicialComplex = ⊥ := by
  let := s.isCombinatorialManifold.realizationChartedSpace
  rw [← s.e.image_boundary (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) rfl, Set.image_eq_empty,
    s.isCombinatorialManifold.boundary_realizationChartedSpace_eq_empty_iff]

/-- Any finite subset `S ⊆ M` can be realized as a set of vertices in a refined PL structure of the
same dimension, obtained by point-by-point stellar subdivision. -/
theorem exists_plStructure_vertex_image (s : PLStructure d M) {S : Set M} (hS : S.Finite) :
    ∃ (s' : PLStructure d M) (v : Set s'.ι), s'.e '' (s'.K.vertex '' v) = S := by
  classical
  obtain ⟨ι', _, K', e', v, hι', hman', hv⟩ :=
    hS.exists_triangulation_vertex_image_of_finite s.K s.finite_ι s.e
  exact ⟨⟨ι', hι', K', by convert hman' d s.isCombinatorialManifold, e'⟩, v, hv⟩

/-- Removing any finite subset from a space carrying a PL structure leaves a space of finite CW
type. -/
theorem finiteCWType_compl (s : PLStructure d M) {S : Set M} (hS : S.Finite) :
    FiniteCWType ↥Sᶜ := by
  have : CompactSpace M := s.compactSpace
  exact hS.finiteCWType_compl_of_isTriangulable_of_compactSpace s.isTriangulable.{u, 0}

end PLStructure

end TauCeti
