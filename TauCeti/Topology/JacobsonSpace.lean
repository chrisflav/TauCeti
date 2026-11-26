/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.JacobsonSpace

/-!
# Closed points of Jacobson spaces

For a continuous map from a Jacobson space, every point with locally closed singleton in its
image, in particular every closed point, has a closed lift. Indeed, its nonempty locally closed
fiber contains a closed point by `nonempty_inter_closedPoints`. This is the topological input for
closed-point lifting along morphisms locally of finite type into Jacobson schemes.

A locally closed subset of a Jacobson space with only finitely many closed points is finite, since
it lies in the closure of its closed points. For a scheme locally of finite type over a field,
this reduces the finiteness of a closed subset, such as a fibre of a morphism, to counting its
closed points.
-/

public section

namespace Continuous

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [JacobsonSpace X]
  {f : X → Y}

/-- Every point with locally closed singleton, in particular every closed point, in the image of a
continuous map from a Jacobson space has a closed lift. -/
theorem exists_isClosed_singleton_of_mem_range (hf : Continuous f) {y : Y}
    (hy : IsLocallyClosed {y}) (hyf : y ∈ Set.range f) :
    ∃ x : X, IsClosed {x} ∧ f x = y := by
  obtain ⟨x, hx⟩ := hyf
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := f ⁻¹' {y}) ⟨x, hx⟩ (hy.preimage hf)
  exact ⟨z, hzc, hz⟩

end Continuous

/-- **A locally closed subset of a Jacobson space with finitely many closed points is finite**: it
lies in the closure of its closed points, and a finite set of closed points is closed. -/
theorem IsLocallyClosed.finite_of_finite_inter_closedPoints {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {Z : Set X} (hZ : IsLocallyClosed Z) (h : (Z ∩ closedPoints X).Finite) :
    Z.Finite := by
  have hc : IsClosed (Z ∩ closedPoints X) := by
    rw [← (Z ∩ closedPoints X).biUnion_of_singleton]
    exact h.isClosed_biUnion fun _ hx ↦ hx.2
  refine h.subset (subset_closure.trans ?_)
  rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure hZ, hc.closure_eq]

/-- **A locally closed subset containing every closed point of a Jacobson space is the whole
space**: writing it as `U ∩ C` with `U` open and `C` closed, both `Uᶜ` (closed) and `Cᶜ`
(open) are locally closed subsets containing no closed point, hence empty. -/
theorem IsLocallyClosed.eq_univ_of_closedPoints_subset {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {Z : Set X} (hZ : IsLocallyClosed Z) (h : closedPoints X ⊆ Z) :
    Z = Set.univ := by
  obtain ⟨U, C, hU, hC, rfl⟩ := hZ
  have hUc : Uᶜ = ∅ := Set.eq_empty_of_forall_notMem fun x hx ↦ by
    obtain ⟨y, hyU, hyc⟩ :=
      nonempty_inter_closedPoints ⟨x, hx⟩ hU.isClosed_compl.isLocallyClosed
    exact hyU (h hyc).1
  have hCc : Cᶜ = ∅ := Set.eq_empty_of_forall_notMem fun x hx ↦ by
    obtain ⟨y, hyC, hyc⟩ :=
      nonempty_inter_closedPoints ⟨x, hx⟩ hC.isOpen_compl.isLocallyClosed
    exact hyC (h hyc).2
  rw [Set.compl_empty_iff.mp hUc, Set.compl_empty_iff.mp hCc, Set.inter_univ]
