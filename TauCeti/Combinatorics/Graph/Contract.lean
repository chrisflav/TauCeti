/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Maps
public import TauCeti.Combinatorics.Graph.Connectivity.Component
public import TauCeti.Combinatorics.Graph.Isomorphism

/-!
# Single-edge contraction of multigraphs

Contracting an edge `e` of a multigraph `G : Graph α β` deletes `e` and identifies any pair of
vertices linked by `e`, retaining every other edge identity. Parallel edges to `e` become loops at
the merged vertex, and existing loops remain loops.

To avoid endpoint choices and membership hypotheses, the vertex quotient is formed directly as
`Quot (G.IsLink e)`. Because at most one unordered pair of vertices can be linked by a single edge
identity `e`, the relation `fun x y ↦ x = y ∨ G.IsLink e x y` is already an equivalence relation on
`α` (`Graph.contractVertex_eq_iff`). Consequently:

* when `e ∉ E(G)` or `e` is a loop, `Graph.contractVertex G e` is injective and `G.contractEdge e`
  is canonically isomorphic to `G.deleteEdges {e}` (`Graph.IsLoopAt.contractEdgeIsoDeleteEdges`,
  `Graph.contractEdgeIsoOfNotMem`);
* when `e` links two distinct vertices, the actual vertex count drops by one
  (`Graph.IsLink.ncard_vertexSet_contractEdge`);
* for every edge `e` and every edge subset `F`, reachability and connected components of the
  spanning restriction `(G.contractEdge e).restrict F` correspond canonically to those of
  `G.restrict (insert e F)` (`Graph.reachable_contractEdge_restrict_iff`,
  `Graph.contractEdgeRestrictConnectedComponentEquiv`,
  `Graph.componentCount_contractEdge_restrict`).

## Main definitions

* `Graph.Iso.ofInjOnMap`: canonical multigraph isomorphism `Iso G (G.map f)` when `f` is injective
  on `V(G)`.
* `Graph.ContractVertex G e`, `Graph.contractVertex G e`: the quotient `Quot (G.IsLink e)` and its
  quotient map `α → Quot (G.IsLink e)`.
* `Graph.contractEdge G e`: the contracted multigraph
  `(G.deleteEdges {e}).map (G.contractVertex e)`.
* `Graph.contractEdgeRestrictConnectedComponentEquiv`: equivalence between the connected components
  of `(G.contractEdge e).restrict F` and those of `G.restrict (insert e F)`.
-/

public section

open Set

universe u v u'

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {G : Graph α β} {e d : β} {x y : α}

/-! ### Vertex maps, edge restrictions, and injective-on-vertices maps -/

/-- Mapping vertices commutes with restricting to an edge set. -/
@[simp]
theorem map_restrict (f : α → α') (G : Graph α β) (F : Set β) :
    (G.map f).restrict F = (G.restrict F).map f := by
  ext a b c <;> simp [Relation.map_apply]
  tauto

/-- Mapping vertices commutes with deleting an edge set. -/
@[simp]
theorem map_deleteEdges (f : α → α') (G : Graph α β) (F : Set β) :
    (G.map f).deleteEdges F = (G.deleteEdges F).map f := by
  rw [← restrict_edgeSet_sdiff_eq_deleteEdges, edgeSet_map, map_restrict,
    restrict_edgeSet_sdiff_eq_deleteEdges]

/-- Vertex maps preserve multigraph reachability. -/
protected theorem Reachable.map (f : α → α') (h : G.Reachable x y) :
    (G.map f).Reachable (f x) (f y) := by
  obtain ⟨hx, ⟨p⟩⟩ := reachable_def.mp h
  clear h
  induction p with
  | nil => exact Reachable.refl (mem_image_of_mem f hx)
  | cons e hlink _ ih => exact (hlink.map f).reachable.trans (ih hlink.right_mem)

/-- When `f` is injective on `V(G)`, `G.map f` is canonically isomorphic to `G`. -/
noncomputable def Iso.ofInjOnMap (G : Graph α β) {f : α → α'} (hf : InjOn f V(G)) :
    Iso G (G.map f) where
  vertexEquiv := (Equiv.Set.imageOfInjOn f V(G) hf).trans
    (Equiv.subtypeEquivRight fun _ ↦ by rw [vertexSet_map])
  edgeEquiv := Equiv.subtypeEquivRight fun _ ↦ by rw [edgeSet_map]
  map_isLink_iff ed u w := by
    simp only [Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe]
    have hu : ((Equiv.Set.imageOfInjOn f V(G) hf u) : α') = f u := rfl
    have hw : ((Equiv.Set.imageOfInjOn f V(G) hf w) : α') = f w := rfl
    rw [hu, hw, Graph.map_isLink, Relation.map_apply]
    refine ⟨?_, fun h ↦ ⟨u, w, h, rfl, rfl⟩⟩
    rintro ⟨a, b, hab, ha, hb⟩
    rwa [hf hab.left_mem u.2 ha, hf hab.right_mem w.2 hb] at hab

/-- The vertex equivalence of `Iso.ofInjOnMap` applies `f` to each actual vertex. -/
@[simp]
theorem Iso.coe_ofInjOnMap_vertexEquiv_apply {f : α → α'} (hf : InjOn f V(G)) (u : V(G)) :
    ((Iso.ofInjOnMap G hf).vertexEquiv u : α') = f u := (rfl)

/-- The edge equivalence of `Iso.ofInjOnMap` is the identity on actual edges. -/
@[simp]
theorem Iso.coe_ofInjOnMap_edgeEquiv_apply {f : α → α'} (hf : InjOn f V(G)) (ed : E(G)) :
    ((Iso.ofInjOnMap G hf).edgeEquiv ed : β) = ed := (rfl)

/-! ### Vertex quotient for single-edge contraction -/

/-- The ambient vertex type after identifying any pair of vertices linked by `e`. -/
def ContractVertex (G : Graph α β) (e : β) : Type u :=
  Quot (G.IsLink e)

/-- The quotient map identifying the endpoints of `e`. -/
def contractVertex (G : Graph α β) (e : β) : α → G.ContractVertex e :=
  Quot.mk (G.IsLink e)

private theorem isLink_eq_or_isLink_trans {u v w : α}
    (huv : u = v ∨ G.IsLink e u v) (hvw : v = w ∨ G.IsLink e v w) :
    u = w ∨ G.IsLink e u w := by
  rcases huv with rfl | huv
  · exact hvw
  rcases hvw with rfl | hvw
  · exact .inr huv
  rcases (huv.symm.isLink_iff).mp hvw with ⟨-, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .inl rfl

/-- Two ambient vertices have the same image under `G.contractVertex e` if and only if they are
equal or linked by `e` in `G`. -/
@[simp]
theorem contractVertex_eq_iff {x y : α} :
    G.contractVertex e x = G.contractVertex e y ↔ x = y ∨ G.IsLink e x y := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · let rel (w : G.ContractVertex e) : Prop :=
      Quot.lift (fun y ↦ x = y ∨ G.IsLink e x y)
        (fun a b hab ↦ propext
          ⟨fun hxa ↦ isLink_eq_or_isLink_trans hxa (.inr hab),
           fun hxb ↦ isLink_eq_or_isLink_trans hxb (.inr hab.symm)⟩) w
    exact (congrArg rel h).mp (.inl rfl)
  · rintro (rfl | h)
    · rfl
    · exact Quot.sound h

/-- Every ambient point in `G.ContractVertex e` is the image of an ambient vertex. -/
theorem contractVertex_surjective (G : Graph α β) (e : β) :
    Function.Surjective (G.contractVertex e) :=
  Quot.exists_rep

/-- The two ends of a link of `e` are identified by `G.contractVertex e`. -/
theorem IsLink.contractVertex_eq (h : G.IsLink e x y) :
    G.contractVertex e x = G.contractVertex e y :=
  contractVertex_eq_iff.mpr (.inr h)

/-- If `e` is not an edge of `G`, `G.contractVertex e` is injective on all ambient vertices. -/
theorem contractVertex_injective_of_notMem (he : e ∉ E(G)) :
    Function.Injective (G.contractVertex e) := by
  intro u w huw
  rcases contractVertex_eq_iff.mp huw with rfl | hlink
  · rfl
  · exact (he hlink.edge_mem).elim

/-- If `e` is a loop of `G`, `G.contractVertex e` is injective on all ambient vertices. -/
theorem IsLoopAt.contractVertex_injective (h : G.IsLoopAt e x) :
    Function.Injective (G.contractVertex e) := by
  intro u w huw
  rcases contractVertex_eq_iff.mp huw with rfl | hlink
  · rfl
  · rcases (h.isLink_iff).mp hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-! ### Single-edge contraction -/

/-- Contract an edge `e` of `G` by deleting `e` and identifying any pair of vertices linked by `e`.
Parallel edges to `e` become loops at the merged vertex, and all other edge identities are
retained. -/
def contractEdge (G : Graph α β) (e : β) : Graph (G.ContractVertex e) β :=
  (G.deleteEdges {e}).map (G.contractVertex e)

/-- Unfolding identity for `Graph.contractEdge`. -/
theorem contractEdge_def (G : Graph α β) (e : β) :
    G.contractEdge e = (G.deleteEdges {e}).map (G.contractVertex e) := (rfl)

/-- The actual vertices of `G.contractEdge e` are the images of `V(G)` under
`G.contractVertex e`. -/
@[simp]
theorem vertexSet_contractEdge (G : Graph α β) (e : β) :
    V(G.contractEdge e) = G.contractVertex e '' V(G) := by
  simp [contractEdge]

/-- Membership in `V(G.contractEdge e)` is witnessed by an actual vertex of `G`. -/
theorem mem_vertexSet_contractEdge_iff {z : G.ContractVertex e} :
    z ∈ V(G.contractEdge e) ↔ ∃ x ∈ V(G), G.contractVertex e x = z := by
  simp [vertexSet_contractEdge]

/-- The image of an ambient vertex lies in `V(G.contractEdge e)` exactly when the vertex lies in
`V(G)`. -/
theorem contractVertex_mem_vertexSet_contractEdge_iff {x : α} :
    G.contractVertex e x ∈ V(G.contractEdge e) ↔ x ∈ V(G) := by
  rw [mem_vertexSet_contractEdge_iff]
  refine ⟨?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
  rintro ⟨u, hu, hux⟩
  rcases contractVertex_eq_iff.mp hux with rfl | hlink
  · exact hu
  · exact hlink.right_mem

/-- The actual edges of `G.contractEdge e` are `E(G) \ {e}`. -/
@[simp]
theorem edgeSet_contractEdge (G : Graph α β) (e : β) :
    E(G.contractEdge e) = E(G) \ {e} := by
  simp [contractEdge]

/-- An edge lies in `E(G.contractEdge e)` precisely when it lies in `E(G)` and is distinct from
`e`. -/
theorem mem_edgeSet_contractEdge_iff :
    d ∈ E(G.contractEdge e) ↔ d ∈ E(G) ∧ d ≠ e := by
  simp [edgeSet_contractEdge]

/-- Every edge of `G.contractEdge e` is an edge of `G`. -/
theorem edgeSet_contractEdge_subset (G : Graph α β) (e : β) :
    E(G.contractEdge e) ⊆ E(G) := by
  rw [edgeSet_contractEdge]
  exact sdiff_subset

/-- Link characterization in `G.contractEdge e`. -/
@[simp]
theorem contractEdge_isLink {z w : G.ContractVertex e} :
    (G.contractEdge e).IsLink d z w ↔
      d ≠ e ∧ ∃ x y, G.IsLink d x y ∧ G.contractVertex e x = z ∧ G.contractVertex e y = w := by
  simp only [contractEdge, map_isLink, Relation.map_apply, deleteEdges_isLink, mem_singleton_iff]
  tauto

/-- A link of `d ≠ e` in `G` descends to a link of `d` in `G.contractEdge e`. -/
protected theorem IsLink.contractEdge (hd : d ≠ e) (h : G.IsLink d x y) :
    (G.contractEdge e).IsLink d (G.contractVertex e x) (G.contractVertex e y) :=
  contractEdge_isLink.mpr ⟨hd, x, y, h, rfl, rfl⟩

/-- Incidence characterization in `G.contractEdge e`. -/
@[simp]
theorem contractEdge_inc {z : G.ContractVertex e} :
    (G.contractEdge e).Inc d z ↔ d ≠ e ∧ ∃ x, G.Inc d x ∧ G.contractVertex e x = z := by
  simp only [Inc, contractEdge_isLink]
  constructor
  · rintro ⟨_, hd, x, y, hxy, rfl, rfl⟩
    exact ⟨hd, x, ⟨y, hxy⟩, rfl⟩
  · rintro ⟨hd, x, ⟨y, hxy⟩, rfl⟩
    exact ⟨G.contractVertex e y, hd, x, y, hxy, rfl, rfl⟩

/-- Loop characterization in `G.contractEdge e`: `d ≠ e` is a loop at `z` precisely when `d` links
two vertices of `G` whose images under `G.contractVertex e` both equal `z` (either an existing loop
or an edge parallel to `e`). -/
@[simp]
theorem contractEdge_isLoopAt {z : G.ContractVertex e} :
    (G.contractEdge e).IsLoopAt d z ↔
      d ≠ e ∧ ∃ x y, G.IsLink d x y ∧ G.contractVertex e x = z ∧ G.contractVertex e y = z := by
  rw [← isLink_self_iff, contractEdge_isLink]

instance [Finite V(G)] : Finite V(G.contractEdge e) := by
  rw [vertexSet_contractEdge]
  exact Set.Finite.to_subtype (Set.toFinite V(G) |>.image _)

instance [Finite E(G)] : Finite E(G.contractEdge e) := by
  rw [edgeSet_contractEdge]
  exact Set.Finite.to_subtype (Set.toFinite E(G) |>.sdiff)

/-- Contracting an edge between two distinct vertices reduces the number of actual vertices by
one. -/
theorem IsLink.ncard_vertexSet_contractEdge [Finite V(G)] (h : G.IsLink e x y) (hne : x ≠ y) :
    V(G.contractEdge e).ncard + 1 = V(G).ncard := by
  have hsub : V(G) \ {y} ⊆ V(G) := sdiff_subset
  have himg : G.contractVertex e '' (V(G) \ {y}) = V(G.contractEdge e) := by
    rw [vertexSet_contractEdge]
    refine Subset.antisymm (image_mono hsub) ?_
    rintro _ ⟨u, hu, rfl⟩
    by_cases huy : u = y
    · subst u
      exact ⟨x, ⟨h.left_mem, hne⟩, h.contractVertex_eq⟩
    · exact ⟨u, ⟨hu, huy⟩, rfl⟩
  have hinj : InjOn (G.contractVertex e) (V(G) \ {y}) := by
    rintro u ⟨-, huy⟩ w ⟨-, hwy⟩ huw
    rcases contractVertex_eq_iff.mp huw with rfl | hlink
    · rfl
    · rcases (h.isLink_iff).mp hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hwy rfl).elim
      · exact (huy rfl).elim
  rw [← himg, hinj.ncard_image, ncard_sdiff_singleton_add_one h.right_mem (Set.toFinite _)]

/-- Restricting `G.contractEdge e` to an edge set `F` not containing `e` is the vertex-quotient map
of `G.restrict F`. -/
theorem contractEdge_restrict_of_notMem {F : Set β} (he : e ∉ F) :
    (G.contractEdge e).restrict F = (G.restrict F).map (G.contractVertex e) := by
  rw [contractEdge_def, map_restrict]
  congr 1
  ext a b c
  · simp
  · simp only [restrict_isLink, deleteEdges_isLink, mem_singleton_iff]
    exact ⟨fun ⟨hbF, hlink, _⟩ ↦ ⟨hbF, hlink⟩,
      fun ⟨hbF, hlink⟩ ↦ ⟨hbF, hlink, fun hbe ↦ he (hbe ▸ hbF)⟩⟩

/-- Restricting `G.contractEdge e` to `F` ignores membership of `e` in `F`. -/
@[simp]
theorem contractEdge_restrict_sdiff_singleton (G : Graph α β) (e : β) (F : Set β) :
    (G.contractEdge e).restrict (F \ {e}) = (G.contractEdge e).restrict F := by
  refine (Compatible.of_le_le restrict_le restrict_le).ext (by simp) ?_
  simp only [edgeSet_restrict, edgeSet_contractEdge]
  ext d
  simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
  tauto

/-- When `e ∉ E(G)`, contracting `e` gives a multigraph canonically isomorphic to `G`. -/
noncomputable def contractEdgeIsoOfNotMem (he : e ∉ E(G)) :
    Iso G (G.contractEdge e) := by
  have hdel : G.deleteEdges {e} = G := by
    refine (Compatible.of_le deleteEdges_le).ext (by simp) ?_
    simp [sdiff_eq_left.mpr (disjoint_singleton_right.mpr he)]
  have hiso : Iso G (G.deleteEdges {e}) :=
    Eq.ndrec (motive := fun H ↦ Iso G H) (Iso.refl G) hdel.symm
  exact hiso.trans (Iso.ofInjOnMap (G.deleteEdges {e})
    ((contractVertex_injective_of_notMem (G := G) he).injOn))

/-- When `e` is a loop of `G`, contracting `e` gives a multigraph canonically isomorphic to
`G.deleteEdges {e}`. -/
noncomputable def IsLoopAt.contractEdgeIsoDeleteEdges (h : G.IsLoopAt e x) :
    Iso (G.deleteEdges {e}) (G.contractEdge e) :=
  Iso.ofInjOnMap (G.deleteEdges {e}) h.contractVertex_injective.injOn

/-- The edge equivalence of `IsLoopAt.contractEdgeIsoDeleteEdges` preserves edge identities. -/
@[simp]
theorem IsLoopAt.coe_contractEdgeIsoDeleteEdges_edgeEquiv_apply (h : G.IsLoopAt e x)
    (ed : E(G.deleteEdges {e})) :
    ((h.contractEdgeIsoDeleteEdges).edgeEquiv ed : β) = ed := (rfl)

/-! ### Reachability and connected components of spanning restrictions -/

private theorem reachable_restrict_insert_of_contractVertex_eq {F : Set β}
    (hx : x ∈ V(G)) (hxy : G.contractVertex e x = G.contractVertex e y) :
    (G.restrict (insert e F)).Reachable x y := by
  rcases contractVertex_eq_iff.mp hxy with rfl | hlink
  · exact Reachable.refl (by simpa using hx)
  · have hrl : (G.restrict (insert e F)).IsLink e x y := by
      rw [restrict_isLink]
      exact ⟨mem_insert e F, hlink⟩
    exact hrl.reachable

private theorem reachable_restrict_insert_of_walk_contractEdge_restrict {F : Set β}
    {z₁ z₂ : G.ContractVertex e} (p : ((G.contractEdge e).restrict F).Walk z₁ z₂)
    {u w : α} (hu : u ∈ V(G)) (hw : w ∈ V(G))
    (hu₁ : G.contractVertex e u = z₁) (hw₂ : G.contractVertex e w = z₂) :
    (G.restrict (insert e F)).Reachable u w := by
  induction p generalizing u w with
  | nil => exact reachable_restrict_insert_of_contractVertex_eq hu (hu₁.trans hw₂.symm)
  | @cons z₁ z' z₂ d hd _ ih =>
    rw [restrict_isLink, contractEdge_isLink] at hd
    obtain ⟨hdF, -, a, b, hab, ha, hb⟩ := hd
    have hua : (G.restrict (insert e F)).Reachable u a :=
      reachable_restrict_insert_of_contractVertex_eq hu (hu₁.trans ha.symm)
    have hab' : (G.restrict (insert e F)).Reachable a b := by
      have hrl : (G.restrict (insert e F)).IsLink d a b := by
        rw [restrict_isLink]
        exact ⟨mem_insert_of_mem e hdF, hab⟩
      exact hrl.reachable
    exact (hua.trans hab').trans (ih hab.right_mem hw hb hw₂)

/-- Two ambient vertices have reachable images in `(G.contractEdge e).restrict F` if and only if
they are reachable in `G.restrict (insert e F)`. Neither `e ∈ E(G)` nor `e ∉ F` is required. -/
@[simp]
theorem reachable_contractEdge_restrict_iff {F : Set β} {x y : α} :
    ((G.contractEdge e).restrict F).Reachable (G.contractVertex e x) (G.contractVertex e y) ↔
      (G.restrict (insert e F)).Reachable x y := by
  constructor
  · intro h
    obtain ⟨hz, ⟨p⟩⟩ := reachable_def.mp h
    have hx : x ∈ V(G) := by
      simpa only [vertexSet_restrict, contractVertex_mem_vertexSet_contractEdge_iff] using hz
    have hy : y ∈ V(G) := by
      simpa only [vertexSet_restrict, contractVertex_mem_vertexSet_contractEdge_iff] using
        h.right_mem
    exact reachable_restrict_insert_of_walk_contractEdge_restrict p hx hy rfl rfl
  · intro h
    obtain ⟨hx, ⟨p⟩⟩ := reachable_def.mp h
    clear h
    induction p with
    | nil =>
      refine Reachable.refl ?_
      simpa only [vertexSet_restrict, contractVertex_mem_vertexSet_contractEdge_iff] using hx
    | @cons a b c d hd _ ih =>
      rw [restrict_isLink] at hd
      obtain ⟨hdF, hab⟩ := hd
      rcases mem_insert_iff.mp hdF with rfl | hdF
      · rw [hab.contractVertex_eq]
        exact ih hab.right_mem
      · by_cases hde : d = e
        · subst d
          rw [hab.contractVertex_eq]
          exact ih hab.right_mem
        · have hlink : ((G.contractEdge e).restrict F).IsLink d
              (G.contractVertex e a) (G.contractVertex e b) := by
            rw [restrict_isLink]
            exact ⟨hdF, hab.contractEdge hde⟩
          exact hlink.reachable.trans (ih hab.right_mem)

/-- Reachability in `G.contractEdge e` between quotient images agrees with reachability in `G`. -/
@[simp]
theorem reachable_contractEdge_iff {x y : α} :
    (G.contractEdge e).Reachable (G.contractVertex e x) (G.contractVertex e y) ↔
      G.Reachable x y := by
  have h1 : (G.contractEdge e).restrict E(G) = G.contractEdge e :=
    (restrict_eq_self_iff _ _).mpr (G.edgeSet_contractEdge_subset e)
  have h2 : G.restrict (insert e E(G)) = G :=
    (restrict_eq_self_iff _ _).mpr (subset_insert e E(G))
  simpa only [h1, h2] using
    (reachable_contractEdge_restrict_iff (G := G) (e := e) (F := E(G)) (x := x) (y := y))

/-- The connected components of `(G.contractEdge e).restrict F` correspond canonically to the
connected components of `G.restrict (insert e F)` via `G.contractVertex e`. -/
noncomputable def contractEdgeRestrictConnectedComponentEquiv
    (G : Graph α β) (e : β) (F : Set β) :
    ((G.contractEdge e).restrict F).ConnectedComponent ≃
      (G.restrict (insert e F)).ConnectedComponent := by
  refine ((G.contractEdge e).restrict F).connectedComponentEquiv.trans
    ((Equiv.ofBijective ?_ ?_).symm.trans (G.restrict (insert e F)).connectedComponentEquiv.symm)
  · exact SimpleGraph.ConnectedComponent.lift
      (fun v : V(G.restrict (insert e F)) ↦
        ((G.contractEdge e).restrict F).toSimpleGraph.connectedComponentMk
          ⟨G.contractVertex e v.1, by
            simpa only [vertexSet_restrict, contractVertex_mem_vertexSet_contractEdge_iff] using
              v.2⟩)
      fun u w hwalk _ ↦ by
        rw [toSimpleGraph_connectedComponentMk_eq_iff, reachable_contractEdge_restrict_iff]
        exact toSimpleGraph_reachable_iff.mp hwalk.reachable
  · constructor
    · intro C D hCD
      induction C using SimpleGraph.ConnectedComponent.ind with | h u => ?_
      induction D using SimpleGraph.ConnectedComponent.ind with | h w => ?_
      simp only [SimpleGraph.ConnectedComponent.lift_mk,
        toSimpleGraph_connectedComponentMk_eq_iff,
        reachable_contractEdge_restrict_iff] at hCD ⊢
      exact hCD
    · intro C
      induction C using SimpleGraph.ConnectedComponent.ind with | h z => ?_
      obtain ⟨x, hx, hxz⟩ : ∃ x ∈ V(G), G.contractVertex e x = z.1 := by
        simpa only [vertexSet_restrict, mem_vertexSet_contractEdge_iff] using z.2
      refine ⟨(G.restrict (insert e F)).toSimpleGraph.connectedComponentMk ⟨x, hx⟩, ?_⟩
      simp only [SimpleGraph.ConnectedComponent.lift_mk]
      congr 1
      exact Subtype.ext hxz

/-- Contracting `e` and restricting to `F` has the same component count as restricting `G` to
`insert e F`. -/
@[simp]
theorem componentCount_contractEdge_restrict (G : Graph α β) (e : β) (F : Set β) :
    ((G.contractEdge e).restrict F).componentCount =
      (G.restrict (insert e F)).componentCount := by
  rw [componentCount_def, componentCount_def]
  exact Nat.card_congr (G.contractEdgeRestrictConnectedComponentEquiv e F)

/-- Contracting any edge preserves the number of connected components of a multigraph. -/
@[simp]
theorem componentCount_contractEdge (G : Graph α β) (e : β) :
    (G.contractEdge e).componentCount = G.componentCount := by
  have h1 : (G.contractEdge e).restrict E(G) = G.contractEdge e :=
    (restrict_eq_self_iff _ _).mpr (G.edgeSet_contractEdge_subset e)
  have h2 : G.restrict (insert e E(G)) = G :=
    (restrict_eq_self_iff _ _).mpr (subset_insert e E(G))
  simpa only [h1, h2] using G.componentCount_contractEdge_restrict e E(G)

end Graph

end
