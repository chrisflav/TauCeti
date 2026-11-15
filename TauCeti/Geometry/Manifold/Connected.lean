/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Topology.ConnectedComponents
import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Removing a discrete set from a connected manifold

A connected topological manifold modelled on a real seminormed space `E` of dimension greater than
one stays connected when a closed discrete set is removed. When the model space is normed, this
applies in particular to finite sets. For a compact Riemann surface this is the statement that the
complement of finitely many points, such as the preimage of the branch values of a holomorphic map,
is connected.

The local input is that every point has arbitrarily small neighbourhoods whose punctured versions
are connected: in a chart these are punctured balls of `E`
(`TauCeti.isConnected_ball_sdiff_singleton`). The global argument is
`TauCeti.isPreconnected_compl_of_isDiscrete`. Only the charted-space structure is used, with the
model space `E` itself; no smoothness of the transition maps is needed.

## Main declarations

* `TauCeti.exists_mem_nhds_subset_isConnected_sdiff_singleton`: every point of the manifold has
  arbitrarily small neighbourhoods whose punctured versions are connected.
* `TauCeti.isPreconnected_compl_of_isDiscrete_of_one_lt_rank`: removing a closed discrete set from
  a preconnected manifold leaves it preconnected.
* `TauCeti.isConnected_compl_of_isDiscrete_of_one_lt_rank`: removing a closed discrete set from a
  connected manifold leaves it connected.
* `TauCeti.isConnected_compl_of_finite_of_one_lt_rank`: the special case of a finite set.
* `TauCeti.isPathConnected_compl_of_isDiscrete_of_one_lt_rank`: since a manifold is locally path
  connected, the complement of a closed discrete set in a connected manifold is even path
  connected.
* `TauCeti.isPathConnected_compl_of_finite_of_one_lt_rank`: the special case of a finite set.
* `TauCeti.isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank`: closed discrete
  deletion inside a preconnected open subset.
* `TauCeti.IsFilledIn.union_finite_of_one_lt_rank`: adjoining a finite set preserves `IsFilledIn`
  when `Ω \ K` is open and the model space has real dimension greater than one.
-/

public section

open Metric Set Topology

namespace TauCeti

variable {E X : Type*} [TopologicalSpace X]

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E X]

/-- In a manifold modelled on a real seminormed space of dimension greater than one, every point `x`
has arbitrarily small neighbourhoods `V` with `V \ {x}` connected. -/
theorem exists_mem_nhds_subset_isConnected_sdiff_singleton (h : 1 < Module.rank ℝ E) (x : X)
    {U : Set X} (hU : U ∈ 𝓝 x) : ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x}) :=
  exists_mem_nhds_subset_isConnected_sdiff_singleton_of_mem_source h (chartAt E x)
    (mem_chart_source E x) hU

/-- **Removing a closed discrete set from a preconnected manifold leaves it preconnected**, when
the model is a real seminormed space of dimension greater than one. -/
theorem isPreconnected_compl_of_isDiscrete_of_one_lt_rank [PreconnectedSpace X]
    (h : 1 < Module.rank ℝ E) {s : Set X} (hs : IsClosed s) (hd : IsDiscrete s) :
    IsPreconnected sᶜ :=
  isPreconnected_compl_of_isDiscrete hs hd fun x _ _ hU ↦
    exists_mem_nhds_subset_isConnected_sdiff_singleton h x hU

/-- **Removing a closed discrete set from a connected manifold leaves it connected**, when the
model is a real seminormed space of dimension greater than one. -/
theorem isConnected_compl_of_isDiscrete_of_one_lt_rank [ConnectedSpace X]
    (h : 1 < Module.rank ℝ E) {s : Set X} (hs : IsClosed s) (hd : IsDiscrete s) :
    IsConnected sᶜ := by
  refine ⟨?_, isPreconnected_compl_of_isDiscrete_of_one_lt_rank h hs hd⟩
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := X)
  by_cases hx : x ∈ s
  · -- A punctured neighbourhood of `x` avoiding the rest of `s` supplies a point off `s`.
    obtain ⟨u, hu, hus⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hd x hx
    have hxu : x ∈ u := (hus.symm ▸ mem_singleton x : x ∈ u ∩ s).1
    obtain ⟨V, -, hVu, hc⟩ := exists_mem_nhds_subset_isConnected_sdiff_singleton h x
      (hu.mem_nhds hxu)
    obtain ⟨z, hz⟩ := hc.nonempty
    refine ⟨z, fun hzs ↦ hz.2 ?_⟩
    simpa [← hus] using And.intro (hVu hz.1) hzs
  · exact ⟨x, hx⟩

/-- Removing a closed discrete set from a preconnected open subset of a manifold of real
dimension greater than one leaves it preconnected. -/
theorem isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank
    (h : 1 < Module.rank ℝ E) {U s : Set X} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hs : IsClosed s) (hd : IsDiscrete s) : IsPreconnected (U \ s) := by
  let V : TopologicalSpace.Opens X := ⟨U, hU⟩
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hUc
  have hc := isPreconnected_compl_of_isDiscrete_of_one_lt_rank (E := E) h
    (hs.preimage (continuous_subtype_val : Continuous (Subtype.val : V → X)))
    (hd.preimage continuous_subtype_val.continuousOn Subtype.val_injective)
  have himage : Subtype.val '' (Subtype.val ⁻¹' s : Set V)ᶜ = U \ s := by
    rw [image_compl_preimage, Subtype.range_val, TopologicalSpace.Opens.coe_mk]
  rw [← himage]
  exact hc.image _ continuous_subtype_val.continuousOn

end Seminormed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E X]

/-- **Removing a finite set from a connected manifold leaves it connected**, when the model is a
real normed space of dimension greater than one. -/
theorem isConnected_compl_of_finite_of_one_lt_rank [ConnectedSpace X] (h : 1 < Module.rank ℝ E)
    {s : Set X} (hs : s.Finite) : IsConnected sᶜ :=
  have := ChartedSpace.t1Space E X
  isConnected_compl_of_isDiscrete_of_one_lt_rank h hs.isClosed hs.isDiscrete

/-- A nonempty manifold modelled on a nontrivial real normed space has infinitely many points. -/
theorem infinite_of_nontrivial_model [Nonempty X] [Nontrivial E] : Infinite X := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have := Module.punctured_nhds_neBot ℝ E (chartAt E x x)
  apply not_finite_iff_infinite.mp
  intro hfin
  have htarget := infinite_of_mem_nhds (chartAt E x x) (chart_target_mem_nhds E x)
  apply htarget
  rw [← (chartAt E x).image_source_eq_target]
  exact (Set.toFinite _).image _

/-- **Removing a closed discrete set from a connected manifold leaves it path connected**, when
the model is a real normed space of dimension greater than one. -/
theorem isPathConnected_compl_of_isDiscrete_of_one_lt_rank [ConnectedSpace X]
    (h : 1 < Module.rank ℝ E) {s : Set X} (hs : IsClosed s) (hd : IsDiscrete s) :
    IsPathConnected sᶜ :=
  have := ChartedSpace.locallyPathConnectedSpace E X
  hs.isOpen_compl.isConnected_iff_isPathConnected.1
    (isConnected_compl_of_isDiscrete_of_one_lt_rank h hs hd)

/-- **Removing a finite set from a connected manifold leaves it path connected**, when the model
is a real normed space of dimension greater than one. -/
theorem isPathConnected_compl_of_finite_of_one_lt_rank [ConnectedSpace X]
    (h : 1 < Module.rank ℝ E) {s : Set X} (hs : s.Finite) : IsPathConnected sᶜ :=
  have := ChartedSpace.t1Space E X
  isPathConnected_compl_of_isDiscrete_of_one_lt_rank h hs.isClosed hs.isDiscrete

/-- Adjoining a finite set preserves `TauCeti.IsFilledIn` on a manifold modelled on a real normed
space of dimension greater than one whenever `Ω \ K` is open: deleting finitely many points from an
open component neither disconnects it nor shrinks its closure. -/
theorem IsFilledIn.union_finite_of_one_lt_rank (h : 1 < Module.rank ℝ E) {K s Ω : Set X}
    (hfill : IsFilledIn K Ω) (hΩK : IsOpen (Ω \ K)) (hs : s.Finite) :
    IsFilledIn (K ∪ s) Ω := by
  have := ChartedSpace.t1Space E X
  have := ChartedSpace.locallyPathConnectedSpace E X
  rw [isFilledIn_iff] at hfill ⊢
  rintro x ⟨hxΩ, hxKs⟩ ⟨hcpt, hsub⟩
  have hxK : x ∈ Ω \ K := ⟨hxΩ, fun hK ↦ hxKs (Or.inl hK)⟩
  set C := connectedComponentIn (Ω \ K) x
  have hC_open : IsOpen C := hΩK.connectedComponentIn
  have hCs_conn : IsPreconnected (C \ s) :=
    isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank h hC_open
      isPreconnected_connectedComponentIn hs.isClosed hs.isDiscrete
  have hxCs : x ∈ C \ s := ⟨mem_connectedComponentIn hxK, fun hx ↦ hxKs (Or.inr hx)⟩
  have hCs_sub : C \ s ⊆ connectedComponentIn (Ω \ (K ∪ s)) x :=
    hCs_conn.subset_connectedComponentIn hxCs fun y hy ↦
      ⟨(connectedComponentIn_subset _ _ hy.1).1,
        fun h' ↦ h'.elim (connectedComponentIn_subset _ _ hy.1).2 hy.2⟩
  have hC_cl : C ⊆ closure (C \ s) := fun y hy ↦
    mem_closure_iff_nhds.mpr fun V hV ↦ by
      have hopen : IsOpen (s \ {y})ᶜ := hs.sdiff.isClosed.isOpen_compl
      have hmem : V ∩ C ∩ (s \ {y})ᶜ ∈ 𝓝 y :=
        Filter.inter_mem (Filter.inter_mem hV (hC_open.mem_nhds hy))
          (hopen.mem_nhds fun h' ↦ h'.2 rfl)
      obtain ⟨W, -, hW_sub, hW_conn⟩ := exists_mem_nhds_subset_isConnected_sdiff_singleton h y hmem
      obtain ⟨w, hwW, hwy⟩ := hW_conn.nonempty
      have hw := hW_sub hwW
      exact ⟨w, hw.1.1, hw.1.2, fun hws ↦ hw.2 ⟨hws, hwy⟩⟩
  have hcl_eq : closure C = closure (connectedComponentIn (Ω \ (K ∪ s)) x) :=
    Subset.antisymm ((closure_minimal hC_cl isClosed_closure).trans (closure_mono hCs_sub))
      (closure_mono (connectedComponentIn_mono x (sdiff_subset_sdiff subset_rfl subset_union_left)))
  exact hfill x hxK ⟨hcl_eq.symm ▸ hcpt, hcl_eq.symm ▸ hsub⟩

end TauCeti
