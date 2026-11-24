/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Triangulable.Vertices
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Complement
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Point
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Configuration
import TauCeti.Geometry.Manifold.Connected

/-!
# Finite punctures of compact triangulated manifolds

In a connected smooth manifold of real dimension greater than one, a finite configuration
can be moved onto distinct vertices of a sufficiently subdivided triangulation. More generally,
for any compact triangulable space (even disconnected, nonsmooth, or with boundary), point-by-point
stellar subdivision realizes any finite subset as a set of vertices while preserving finiteness and
any combinatorial manifold structure. Thus a compact triangulable space remains of finite CW type
after deleting any finite set, not just a set already represented by vertices. This supplies finite
CW models for punctured surfaces used in Euler-characteristic calculations for branched covers.

We use finite-configuration homogeneity from `Diffeotopy.Configuration`, the derived subdivision
complement model from `Realization.Complement`, and point stellar subdivision from
`Subdivision.Stellar.Point`.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, §4 (homogeneity).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 3
  (complements of subpolyhedra).
-/

public noncomputable section

open Set AbstractSimplicialComplex TauCeti.SetLike TauCeti
open scoped Manifold ContDiff

namespace Set.Finite

universe u v w

section CompactTriangulable

/-- Given a finite triangulation of `M` and a finite subset `S ⊆ M`, iterated stellar subdivision
produces a finite triangulation (preserving any combinatorial manifold structure) in which `S` is
the image of a set of vertices. -/
theorem exists_triangulation_vertex_image_of_finite {M : Type u} [TopologicalSpace M]
    {ι : Type w} [DecidableEq ι] (K : AbstractSimplicialComplex ι) (hι : Finite ι)
    (e : Realization K ≃ₜ M) {S : Set M} (hS : S.Finite) :
    ∃ (ι' : Type w) (_ : DecidableEq ι') (K' : AbstractSimplicialComplex ι')
      (e' : Realization K' ≃ₜ M) (s : Set ι'),
      Finite ι' ∧
      (∀ d, PreAbstractSimplicialComplex.IsCombinatorialManifold
        K.toPreAbstractSimplicialComplex d →
          PreAbstractSimplicialComplex.IsCombinatorialManifold
            K'.toPreAbstractSimplicialComplex d) ∧
      e' '' (K'.vertex '' s) = S := by
  classical
  suffices h : ∀ T : Finset M,
      ∃ (ι' : Type w) (_ : DecidableEq ι') (K' : AbstractSimplicialComplex ι')
        (e' : Realization K' ≃ₜ M) (s : Set ι'),
        Finite ι' ∧
        (∀ d, PreAbstractSimplicialComplex.IsCombinatorialManifold
          K.toPreAbstractSimplicialComplex d →
            PreAbstractSimplicialComplex.IsCombinatorialManifold
              K'.toPreAbstractSimplicialComplex d) ∧
        e' '' (K'.vertex '' s) = (T : Set M) by
    obtain ⟨ι', inst, K', e', s, hι', hman, hs⟩ := h hS.toFinset
    exact ⟨ι', inst, K', e', s, hι', hman, by simpa using hs⟩
  intro T
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨ι, inferInstance, K, e, ∅, hι, fun _ h => h, by simp⟩
  | @insert x T hx ih =>
    obtain ⟨ι₁, inst₁, K₁, e₁, s₁, hι₁, hman₁, hs₁⟩ := ih
    let := Fintype.ofFinite ι₁
    have hfin₁ : K₁.faces.Finite := Set.toFinite K₁.faces
    obtain ⟨ι₂, inst₂, K₂, r, hman₂, -, hfinι₂, hold, ⟨v₀, hv₀⟩⟩ :=
      K₁.exists_pointStellarSubdivision hfin₁ (e₁.symm x)
    refine ⟨ι₂, inst₂, K₂, r.trans e₁,
      {j | j = v₀ ∨ ∃ i ∈ s₁, r (K₂.vertex j) = K₁.vertex i},
      hfinι₂ hι₁, fun d hd => hman₂ d (hman₁ d hd), ?_⟩
    ext z
    constructor
    · rintro ⟨_, ⟨j, rfl | ⟨i, hi, hij⟩, rfl⟩, rfl⟩
      · simp [hv₀]
      · refine Finset.mem_insert_of_mem ?_
        change (r.trans e₁) (K₂.vertex j) ∈ (T : Set M)
        rw [← hs₁]
        exact ⟨K₁.vertex i, ⟨i, hi, rfl⟩, by simp [hij]⟩
    · intro hz
      rcases Finset.mem_insert.mp hz with rfl | hzT
      · exact ⟨K₂.vertex v₀, ⟨v₀, Or.inl rfl, rfl⟩, by simp [hv₀]⟩
      · have hzT' : z ∈ (T : Set M) := hzT
        rw [← hs₁] at hzT'
        obtain ⟨_, ⟨i, hi, rfl⟩, rfl⟩ := hzT'
        obtain ⟨j, hj⟩ := hold i
        exact ⟨K₂.vertex j, ⟨j, Or.inr ⟨i, hi, hj⟩, rfl⟩, by simp [hj]⟩

/-- Every finite set in a compact triangulable space is the image of a set of vertices in some
finite triangulation, with no smoothness, connectedness, or dimension assumption. -/
theorem exists_triangulation_vertex_image_of_compactSpace {M : Type u} [TopologicalSpace M]
    [CompactSpace M] {S : Set M} (hS : S.Finite) (htri : IsTriangulable.{w} M) :
    ∃ (ι : Type w) (K : AbstractSimplicialComplex ι) (e : Realization K ≃ₜ M) (s : Set ι),
      Finite ι ∧ e '' (K.vertex '' s) = S := by
  classical
  obtain ⟨ι, K, ⟨e⟩⟩ := (isTriangulable_iff M).mp htri
  have := e.symm.compactSpace
  have hι : Finite ι := K.compactSpace_realization_iff_finite.mp inferInstance
  obtain ⟨ι', _, K', e', s, hι', -, hs⟩ := hS.exists_triangulation_vertex_image_of_finite K hι e
  exact ⟨ι', K', e', s, hι', hs⟩

/-- Deleting finitely many points from a compact triangulable space leaves a space of finite CW
type. -/
theorem finiteCWType_compl_of_isTriangulable_of_compactSpace {M : Type u} [TopologicalSpace M]
    [CompactSpace M] {S : Set M} (hS : S.Finite) (htri : IsTriangulable.{w} M) :
    FiniteCWType ↥Sᶜ := by
  classical
  have htri' : IsTriangulable.{u} M := htri.lift_of_compactSpace
  obtain ⟨ι, K, e, s, hι, hS⟩ := hS.exists_triangulation_vertex_image_of_compactSpace htri'
  let := Fintype.ofFinite ι
  have heq : e ⁻¹' Sᶜ = (K.vertex '' s)ᶜ := by
    rw [← hS, preimage_compl, e.injective.preimage_image]
  have := K.instFiniteCWTypeComplVertexImage s
  exact ((e.sets heq.symm).symm).finiteCWType

end CompactTriangulable

section Smooth

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [T2Space M] [ConnectedSpace M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) 2 M]

/-- Every finite set in a compact connected triangulable `C²` manifold of real dimension
greater than one is the image of a set of vertices in some finite topological triangulation.
The triangulation need not be smooth. -/
theorem exists_triangulation_vertex_image {S : Set M} (hS : S.Finite)
    (hdim : 1 < Module.rank ℝ E) (htri : IsTriangulable.{w} M) :
    ∃ (ι : Type w) (K : AbstractSimplicialComplex ι) (e : Realization K ≃ₜ M) (s : Set ι),
      Finite ι ∧ e '' (K.vertex '' s) = S := by
  classical
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).mp (lt_trans zero_lt_one hdim)
  have : Infinite M := infinite_of_nontrivial_model (E := E)
  have := hS.to_subtype
  obtain ⟨ι, K, hι, ⟨e⟩, hcard⟩ :=
    htri.exists_finite_triangulation_card_ge (Nat.card S)
  let := Fintype.ofFinite S
  let := Fintype.ofFinite ι
  obtain ⟨j⟩ : Nonempty (S ↪ ι) := Function.Embedding.nonempty_of_card_le (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨Φ, _, _, _, _, hΦ⟩ :=
    exists_diffeotopy_final_comp_eq_of_isPreconnected (E := E) (M := M) (n := 2) (m := 1)
      hdim le_rfl (by norm_num) isOpen_univ isPreconnected_univ
      (f := fun x : S => (x : M)) (g := fun x : S => e (K.vertex (j x)))
      Subtype.val_injective (e.injective.comp (K.vertex_injective.comp j.injective))
      (fun _ => mem_univ _) (fun _ => mem_univ _)
  let e' := e.trans Φ.final.toHomeomorph.symm
  refine ⟨ι, K, e', range j, hι, ?_⟩
  have hmarked (x : S) : e' (K.vertex (j x)) = x := by
    have hx := congrFun hΦ x
    exact Φ.final.injective (by simpa [e', Function.comp_def] using hx.symm)
  ext x
  constructor
  · rintro ⟨_, ⟨_, ⟨y, rfl⟩, rfl⟩, rfl⟩
    exact hmarked y ▸ y.property
  · intro hx
    exact ⟨K.vertex (j ⟨x, hx⟩), ⟨j ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩,
      hmarked ⟨x, hx⟩⟩

omit [FiniteDimensional ℝ E] [ChartedSpace E M] [T2Space M] [ConnectedSpace M]
  [IsManifold 𝓘(ℝ, E) 2 M] in
/-- Deleting finitely many points from a compact connected triangulable `C²` manifold of real
dimension greater than one leaves a space of finite CW type. The removed points need not be
vertices of the supplied triangulation. -/
theorem finiteCWType_compl_of_isTriangulable {S : Set M} (hS : S.Finite)
    (_hdim : 1 < Module.rank ℝ E) (htri : IsTriangulable.{w} M) : FiniteCWType ↥Sᶜ :=
  hS.finiteCWType_compl_of_isTriangulable_of_compactSpace htri

end Smooth

end Set.Finite
