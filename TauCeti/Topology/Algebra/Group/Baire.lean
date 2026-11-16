/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Baire.Lemmas

/-!
# Countable covers of Baire groups by closed subgroups

A subgroup of a topological group (even assuming only separately continuous multiplication) with
nonempty interior is open (`Subgroup.isOpen_of_mem_nhds`). Combined with the Baire category
theorem (`nonempty_interior_of_iUnion_of_closed`), any countable cover of a Baire group by closed
subgroups contains an open subgroup. For a compact Hausdorff group, every open subgroup has finite
index (`Subgroup.quotient_finite_of_isOpen`), which yields the Baire descent principle for
continuous homomorphisms of compact Hausdorff groups.

## Main results

* `Subgroup.exists_isOpen_of_iUnion_eq_univ`: a Baire group covered by countably many closed
  subgroups contains an open subgroup from the family.
* `Subgroup.exists_isOpen_of_biUnion_eq_univ`: the same for a family indexed by a countable set.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] [BaireSpace G]

/-- **A Baire group covered by countably many closed subgroups has an open member.** By the Baire
category theorem some member has nonempty interior, and a subgroup with nonempty interior is open
by translation. -/
@[to_additive /-- **A Baire additive group covered by countably many closed subgroups has an open
member.** By the Baire category theorem some member has nonempty interior, and a subgroup with
nonempty interior is open by translation. -/]
theorem exists_isOpen_of_iUnion_eq_univ {ι : Type*} [Countable ι] {H : ι → Subgroup G}
    (hc : ∀ i, IsClosed (H i : Set G)) (hcover : ⋃ i, (H i : Set G) = Set.univ) :
    ∃ i, IsOpen (H i : Set G) := by
  obtain ⟨i, _, hg⟩ := nonempty_interior_of_iUnion_of_closed hc hcover
  exact ⟨i, (H i).isOpen_of_mem_nhds (mem_interior_iff_mem_nhds.mp hg)⟩

/-- **A Baire group covered by a countable set-indexed family of closed subgroups has an open
member.** -/
@[to_additive /-- **A Baire additive group covered by a countable set-indexed family of closed
subgroups has an open member.** -/]
theorem exists_isOpen_of_biUnion_eq_univ {α : Type*} {s : Set α} (hs : s.Countable)
    {H : α → Subgroup G} (hc : ∀ i ∈ s, IsClosed (H i : Set G))
    (hcover : ⋃ i ∈ s, (H i : Set G) = Set.univ) :
    ∃ i ∈ s, IsOpen (H i : Set G) := by
  have : Countable s := hs.to_subtype
  obtain ⟨⟨i, hi⟩, hopen⟩ := exists_isOpen_of_iUnion_eq_univ (H := fun i : s ↦ H i.1)
    (fun i ↦ hc i.1 i.2) (by simpa only [Set.iUnion_coe_set] using hcover)
  exact ⟨i, hi, hopen⟩

end Subgroup
