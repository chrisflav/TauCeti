/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Isomorphism
public import TauCeti.Combinatorics.Graph.Contract
public import TauCeti.Combinatorics.Graph.Union

/-!
# Potts and Fortuin–Kasteleyn partition functions on multigraphs

For a multigraph `G : Graph V E` with finite vertex and edge sets (whose ambient types `V` and `E`
need not be finite), a commutative semiring `R`, a parameter `Q : R`, a colour count `q : ℕ`, and
edge weights `v : E(G) → R`, this file defines:

* the **`q`-state Potts partition function** `Graph.pottsPartition G q v`,
  $$Z_{\mathrm{Potts}}(G; q, v) =
    \sum_{\sigma : V(G) \to \mathrm{Fin}\, q} \prod_{e \in E(G)}
      (1 + [\text{$e$ monochromatic under $\sigma$}]\, v_e);$$
* the **Fortuin–Kasteleyn (random-cluster) partition function** `Graph.fkPartition G Q v`,
  $$Z_{\mathrm{FK}}(G; Q, v) =
    \sum_{A \subseteq E(G)} Q^{k(A)} \prod_{e \in A} v_e,$$
  where $k(A)$ is `Graph.componentCount (G.restrict (Subtype.val '' A))`, counting isolated
  vertices as components while retaining loops and parallel-edge identities in the edge product.

Expanding the edge product over subsets `A ⊆ E(G)` and identifying vertex colourings monochromatic
on `A` with unconstrained colourings of the connected components of `G.restrict (Subtype.val '' A)`
(`Graph.monochromaticColoringEquiv`) gives the Fortuin–Kasteleyn identity
`Graph.pottsPartition_eq_fkPartition` for all `q : ℕ` (including `q = 0`).

We also establish:

* invariance under commutative-semiring homomorphisms (`Graph.map_fkPartition`,
  `Graph.map_pottsPartition`) and multigraph isomorphisms (`Graph.Iso.fkPartition_eq`,
  `Graph.Iso.pottsPartition_eq`);
* evaluations on the empty graph, edgeless graphs (`Q ^ V(G).ncard`), `q = 0`, `q = 1`, and two
  vertices joined by parallel edges (`Graph.fkPartition_banana_of_ne`);
* multiplicativity on vertex-disjoint compatible unions (`Graph.Compatible.fkPartition_union`,
  `Graph.Compatible.pottsPartition_union`);
* deletion–contraction (`Graph.fkPartition_eq_deleteEdges_add_contractEdge`, holding for every
  actual edge without a non-loop assumption because loop contraction is isomorphic to loop
  deletion), loop factorisation (`Graph.IsLoopAt.fkPartition_eq`), and bridge factorisation
  (`Graph.IsBridge.fkPartition_eq`).

## Main definitions and results

* `Graph.IsMonochromaticEdge G σ e`: every pair of actual vertices linked by `e` receives the same
  colour under `σ`.
* `Graph.monochromaticColoringEquiv G A γ`: equivalence between vertex colourings `V(G) → γ`
  monochromatic on `A ⊆ E(G)` and component colourings
  `(G.restrict (Subtype.val '' A)).ConnectedComponent → γ`.
* `Graph.pottsPartition G q v`, `Graph.fkPartition G Q v`: the Potts and Fortuin–Kasteleyn
  partition functions.
* `Graph.pottsPartition_eq_fkPartition`: `G.pottsPartition q v = G.fkPartition (q : R) v`.
* `Graph.fkPartition_eq_deleteEdges_add_contractEdge`, `Graph.IsLoopAt.fkPartition_eq`,
  `Graph.IsBridge.fkPartition_eq`: the deletion–contraction, loop, and bridge recursions.

## References

* C. M. Fortuin and P. W. Kasteleyn, *On the random-cluster model. I. Introduction and relation to
  other models*, Physica 57 (1972), 536–564.
* H. N. V. Temperley and E. H. Lieb, *Relations between the 'percolation' and 'colouring' problem
  and other graph-theoretical problems associated with regular planar lattices: some exact results
  for the 'percolation' problem*, Proc. Roy. Soc. London Ser. A 322 (1971), 251–280.
* R. J. Baxter, S. B. Kelland, and F. Y. Wu, *Equivalence of the Potts model or Whitney polynomial
  with an ice-type model*, J. Phys. A 9 (1976), 397–406.
-/

public section

open Set

universe u v u' v' w

namespace Graph

variable {V : Type u} {E : Type v} {V' : Type u'} {E' : Type v'}
variable {R : Type w} [CommSemiring R]

/-! ### Carrier finiteness instances for standard graph constructions -/

instance : Finite V((⊥ : Graph V E)) := by
  rw [vertexSet_bot]
  infer_instance

instance : Finite E((⊥ : Graph V E)) := by
  rw [edgeSet_bot]
  infer_instance

instance (S : Set V) [Finite S] : Finite V(noEdge S E) := by
  rwa [vertexSet_noEdge]

instance (S : Set V) : Finite E(noEdge S E) := by
  rw [edgeSet_noEdge]
  infer_instance

instance (G : Graph V E) [Finite V(G)] (F : Set E) : Finite V(G.restrict F) := by
  rwa [vertexSet_restrict]

instance (G : Graph V E) [Finite E(G)] (F : Set E) : Finite E(G.restrict F) := by
  rw [edgeSet_restrict]
  exact Set.Finite.to_subtype ((Set.toFinite E(G)).inter_of_left F)

instance (G : Graph V E) [Finite V(G)] (F : Set E) : Finite V(G.deleteEdges F) := by
  rwa [vertexSet_deleteEdges]

instance (G : Graph V E) [Finite E(G)] (F : Set E) : Finite E(G.deleteEdges F) := by
  rw [edgeSet_deleteEdges]
  exact Set.Finite.to_subtype (Set.toFinite E(G) |>.sdiff)

instance (x y : V) (F : Set E) : Finite V(banana x y F) := by
  rw [vertexSet_banana]
  exact Set.Finite.to_subtype (Set.finite_singleton y |>.insert x)

instance (x y : V) (F : Set E) [Finite F] : Finite E(banana x y F) := by
  rwa [edgeSet_banana]

/-! ### Monochromatic edges and component colourings -/

/-- An actual edge `e : E(G)` is monochromatic under a vertex colouring `σ : V(G) → γ` when every
pair of actual vertices linked by `e` receives the same colour. A loop is monochromatic under every
colouring. -/
def IsMonochromaticEdge (G : Graph V E) {γ : Type*} (σ : V(G) → γ) (e : E(G)) : Prop :=
  ∀ u w : V(G), G.IsLink e u w → σ u = σ w

/-- Unfolding characterization of `Graph.IsMonochromaticEdge`. -/
theorem isMonochromaticEdge_iff {G : Graph V E} {γ : Type*} {σ : V(G) → γ} {e : E(G)} :
    G.IsMonochromaticEdge σ e ↔ ∀ u w : V(G), G.IsLink e u w → σ u = σ w :=
  Iff.rfl

/-- Given a specific link `G.IsLink e u w`, `e` is monochromatic under `σ` precisely when
`σ u = σ w`. -/
theorem IsLink.isMonochromaticEdge_iff {G : Graph V E} {γ : Type*} {σ : V(G) → γ}
    {e : E(G)} {u w : V(G)} (h : G.IsLink e u w) :
    G.IsMonochromaticEdge σ e ↔ σ u = σ w := by
  refine ⟨fun hm ↦ hm u w h, fun hσ u' w' h' ↦ ?_⟩
  rcases (h.isLink_iff).mp h' with ⟨hu, hw⟩ | ⟨hu, hw⟩
  · rw [← Subtype.ext hu, ← Subtype.ext hw, hσ]
  · rw [← Subtype.ext hu, ← Subtype.ext hw, hσ.symm]

/-- Every loop is monochromatic under every vertex colouring. -/
theorem IsLoopAt.isMonochromaticEdge {G : Graph V E} {γ : Type*} (σ : V(G) → γ)
    {e : E(G)} {x : V} (h : G.IsLoopAt e x) : G.IsMonochromaticEdge σ e := by
  intro u w hlink
  rcases (h.isLink_iff).mp hlink with ⟨hu, hw⟩ | ⟨hw, hu⟩ <;>
    exact congrArg σ (Subtype.ext (hu.symm.trans hw))

/-- A vertex colouring monochromatic on every edge in `A` is constant along walks in
`G.restrict (Subtype.val '' A)`. -/
theorem Reachable.apply_eq_of_isMonochromaticEdge {G : Graph V E} {γ : Type*}
    {σ : V(G) → γ} {A : Set E(G)} (hA : ∀ e ∈ A, G.IsMonochromaticEdge σ e)
    {u w : V(G)} (hreach : (G.restrict (Subtype.val '' A)).Reachable u w) :
    σ u = σ w := by
  obtain ⟨-, ⟨p⟩⟩ := reachable_def.mp hreach
  clear hreach
  suffices ∀ {a b : V}, (G.restrict (Subtype.val '' A)).Walk a b →
      ∀ (ha : a ∈ V(G)) (hb : b ∈ V(G)), σ ⟨a, ha⟩ = σ ⟨b, hb⟩ from
    this p u.2 w.2
  intro a b p
  induction p with
  | nil => intro _ _; rfl
  | @cons a c b d hd _ ih =>
    intro ha hb
    rw [restrict_isLink] at hd
    obtain ⟨⟨e, heA, rfl⟩, hac⟩ := hd
    exact (hA e heA ⟨a, ha⟩ ⟨c, hac.right_mem⟩ hac).trans (ih hac.right_mem hb)

/-- A vertex colouring `σ` is monochromatic on every edge in `A` if and only if `σ` is constant on
each reachable class of `G.restrict (Subtype.val '' A)`. -/
theorem forall_isMonochromaticEdge_iff_reachable_imp {G : Graph V E} {γ : Type*}
    {σ : V(G) → γ} {A : Set E(G)} :
    (∀ e ∈ A, G.IsMonochromaticEdge σ e) ↔
      ∀ u w : V(G), (G.restrict (Subtype.val '' A)).Reachable u w → σ u = σ w := by
  refine ⟨fun hA u w hr ↦ hr.apply_eq_of_isMonochromaticEdge hA, fun hr e heA u w hlink ↦ ?_⟩
  apply hr u w
  have hrl : (G.restrict (Subtype.val '' A)).IsLink e u w := by
    rw [restrict_isLink]
    exact ⟨⟨e, heA, rfl⟩, hlink⟩
  exact hrl.reachable

/-- Vertex colourings `V(G) → γ` monochromatic on every edge in `A` correspond bijectively to
unconstrained colourings of the connected components of `G.restrict (Subtype.val '' A)`. -/
noncomputable def monochromaticColoringEquiv (G : Graph V E) (A : Set E(G)) (γ : Type*) :
    {σ : V(G) → γ // ∀ e ∈ A, G.IsMonochromaticEdge σ e} ≃
      ((G.restrict (Subtype.val '' A)).ConnectedComponent → γ) where
  toFun σ C :=
    σ.1 ⟨Classical.choose C.2.nonempty,
      by simpa only [vertexSet_restrict] using
        C.2.le.vertexSet_mono (Classical.choose_spec C.2.nonempty)⟩
  invFun τ :=
    ⟨fun u ↦ τ ((G.restrict (Subtype.val '' A)).connectedComponentOf u
      (by simpa only [vertexSet_restrict] using u.2)),
     forall_isMonochromaticEdge_iff_reachable_imp.mpr fun u w hr ↦
       congrArg τ ((connectedComponentOf_eq_connectedComponentOf_iff _ _).mpr hr)⟩
  left_inv σ := by
    ext u
    let K := G.restrict (Subtype.val '' A)
    let C : K.ConnectedComponent := K.connectedComponentOf u
      (by simpa only [K, vertexSet_restrict] using u.2)
    have hxC : Classical.choose C.2.nonempty ∈ V(C.1) := Classical.choose_spec C.2.nonempty
    have huC : (u : V) ∈ V(C.1) := mem_vertexSet_connectedComponentOf_self _
    have hreach : K.Reachable (Classical.choose C.2.nonempty) u :=
      (C.2.connected.reachable hxC huC).mono C.2.le
    exact Reachable.apply_eq_of_isMonochromaticEdge σ.2 hreach
  right_inv τ := by
    ext C
    dsimp only
    congr 1
    exact (C.eq_connectedComponentOf (Classical.choose_spec C.2.nonempty)).symm

/-- Applying the inverse of `monochromaticColoringEquiv` reads off the colour assigned to each
vertex's connected component in `G.restrict (Subtype.val '' A)`. -/
@[simp]
theorem monochromaticColoringEquiv_symm_apply (G : Graph V E) (A : Set E(G)) {γ : Type*}
    (τ : (G.restrict (Subtype.val '' A)).ConnectedComponent → γ) (u : V(G)) :
    ((G.monochromaticColoringEquiv A γ).symm τ).1 u =
      τ ((G.restrict (Subtype.val '' A)).connectedComponentOf u
        (by simpa only [vertexSet_restrict] using u.2)) := (rfl)

/-! ### Partition functions and `[Fintype]` formulas -/

/-- **The `q`-state Potts partition function** `Z_Potts(G; q, v)` of a multigraph `G` with finite
vertex and edge sets: the sum over vertex colourings `σ : V(G) → Fin q` of the product over actual
edges `e : E(G)` of `1 + v e` when `e` is monochromatic under `σ` and `1` otherwise. -/
noncomputable def pottsPartition (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) (v : E(G) → R) : R := by
  classical
  have := Fintype.ofFinite V(G)
  have := Fintype.ofFinite E(G)
  exact ∑ σ : V(G) → Fin q, ∏ e : E(G),
    (1 + if G.IsMonochromaticEdge σ e then v e else 0)

/-- **The Fortuin–Kasteleyn (random-cluster) partition function** `Z_FK(G; Q, v)` of a multigraph
`G` with finite edge set: the sum over edge subsets `A ⊆ E(G)` of
`Q ^ k(A) * ∏ e ∈ A, v e`, where `k(A)` is `(G.restrict (Subtype.val '' A)).componentCount`. -/
noncomputable def fkPartition (G : Graph V E) [Finite E(G)]
    (Q : R) (v : E(G) → R) : R := by
  classical
  have := Fintype.ofFinite E(G)
  exact ∑ A : Finset E(G),
    Q ^ (G.restrict (Subtype.val '' (A : Set E(G)))).componentCount * ∏ e ∈ A, v e

/-- Explicit `Finset.univ` formula for `Graph.pottsPartition` when `V(G)` and `E(G)` carry
`Fintype` instances. -/
theorem pottsPartition_eq_sum_fintype (G : Graph V E) [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] (q : ℕ) (v : E(G) → R) :
    G.pottsPartition q v =
      ∑ σ : V(G) → Fin q, ∏ e : E(G),
        (1 + open Classical in if G.IsMonochromaticEdge σ e then v e else 0) := by
  unfold pottsPartition
  convert rfl

/-- Explicit `Finset.univ` formula for `Graph.fkPartition` when `E(G)` carries a `Fintype`
instance. -/
theorem fkPartition_eq_sum_fintype (G : Graph V E) [Fintype E(G)]
    (Q : R) (v : E(G) → R) :
    G.fkPartition Q v =
      ∑ A : Finset E(G),
        Q ^ (G.restrict (Subtype.val '' (A : Set E(G)))).componentCount * ∏ e ∈ A, v e := by
  unfold fkPartition
  convert rfl

/-- **The Potts–Fortuin–Kasteleyn identity.** For every multigraph `G` with finite vertex and edge
sets, every number of colours `q : ℕ` (including `q = 0`), and all weights `v : E(G) → R` in a
commutative semiring, `Z_Potts(G; q, v) = Z_FK(G; q, v)`. -/
theorem pottsPartition_eq_fkPartition (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) (v : E(G) → R) :
    G.pottsPartition q v = G.fkPartition (q : R) v := by
  classical
  have := Fintype.ofFinite V(G)
  have := Fintype.ofFinite E(G)
  rw [pottsPartition_eq_sum_fintype, fkPartition_eq_sum_fintype]
  -- Expand each edge product `∏ e, (1 + ...)` over subsets `A : Finset E(G)`.
  have hexpand : ∀ σ : V(G) → Fin q,
      (∏ e : E(G), (1 + if G.IsMonochromaticEdge σ e then v e else 0)) =
        ∑ A : Finset E(G), if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, v e else 0 := by
    intro σ
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun A _ ↦ ?_
    by_cases hA : ∀ e ∈ A, G.IsMonochromaticEdge σ e
    · rw [ite_eq_left_iff.mpr fun h ↦ (h hA).elim]
      exact Finset.prod_congr rfl fun e he ↦ ite_eq_left_iff.mpr fun h ↦ (h (hA e he)).elim
    · rw [ite_eq_right_iff.mpr fun h ↦ (hA h).elim]
      push Not at hA
      obtain ⟨e, heA, hne⟩ := hA
      exact Finset.prod_eq_zero heA (ite_eq_right_iff.mpr fun h ↦ (hne h).elim)
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  congr 1
  -- Count colourings monochromatic on `A` via `monochromaticColoringEquiv`.
  let K := G.restrict (Subtype.val '' (A : Set E(G)))
  have := Fintype.ofFinite K.ConnectedComponent
  have hcard :
      (Finset.univ.filter fun σ : V(G) → Fin q ↦ ∀ e ∈ A, G.IsMonochromaticEdge σ e).card =
        q ^ K.componentCount := by
    rw [← Fintype.card_coe]
    have heq : {σ : V(G) → Fin q //
        σ ∈ Finset.univ.filter fun σ ↦ ∀ e ∈ A, G.IsMonochromaticEdge σ e} ≃
        {σ : V(G) → Fin q // ∀ e ∈ (A : Set E(G)), G.IsMonochromaticEdge σ e} :=
      Equiv.subtypeEquivRight fun _ ↦ by simp
    rw [Fintype.card_congr (heq.trans (G.monochromaticColoringEquiv (A : Set E(G)) (Fin q))),
      Fintype.card_fun, Fintype.card_fin, K.componentCount_def, Nat.card_eq_fintype_card]
  rw [hcard, Nat.cast_pow]

/-! ### Base change and multigraph isomorphism invariance -/

/-- Commutative-semiring homomorphisms commute with `Graph.fkPartition`. -/
theorem map_fkPartition {S : Type*} [CommSemiring S] {F : Type*} [FunLike F R S]
    [RingHomClass F R S] (φ : F) (G : Graph V E) [Finite E(G)]
    (Q : R) (v : E(G) → R) :
    φ (G.fkPartition Q v) = G.fkPartition (φ Q) (φ ∘ v) := by
  classical
  have := Fintype.ofFinite E(G)
  simp [fkPartition_eq_sum_fintype, map_sum, map_mul, map_pow, map_prod]

/-- Commutative-semiring homomorphisms commute with `Graph.pottsPartition`. -/
theorem map_pottsPartition {S : Type*} [CommSemiring S] {F : Type*} [FunLike F R S]
    [RingHomClass F R S] (φ : F) (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) (v : E(G) → R) :
    φ (G.pottsPartition q v) = G.pottsPartition q (φ ∘ v) := by
  rw [pottsPartition_eq_fkPartition, map_fkPartition, map_natCast, pottsPartition_eq_fkPartition]

namespace Iso

variable {G : Graph V E} {H : Graph V' E'}

/-- Reachability in a spanning edge restriction is preserved along a multigraph isomorphism. -/
theorem reachable_restrict_image_iff (f : Iso G H) (A : Set E(G)) (x y : V(G)) :
    (H.restrict (Subtype.val '' (f.edgeEquiv '' A))).Reachable
        (f.vertexEquiv x) (f.vertexEquiv y) ↔
      (G.restrict (Subtype.val '' A)).Reachable x y := by
  have hmap : f.mapEdgeSet (E(G) \ (Subtype.val '' A)) =
      E(H) \ (Subtype.val '' (f.edgeEquiv '' A)) := by
    ext e'
    by_cases he' : e' ∈ E(H)
    · let ed : E(H) := ⟨e', he'⟩
      have hm := f.mem_mapEdgeSet_iff (E(G) \ (Subtype.val '' A)) ed
      simp only [ed, mem_sdiff, Subtype.coe_prop, true_and, mem_image, he'] at hm ⊢
      refine hm.trans ⟨fun h ⟨_, ⟨a, ha, rfl⟩, hbe⟩ ↦ h ⟨a, ha, by simp [← hbe]⟩,
        fun h ⟨a, ha, hae⟩ ↦ h ⟨f.edgeEquiv a, ⟨a, ha, rfl⟩,
          congrArg Subtype.val ((f.edgeEquiv.eq_symm_apply).mp (Subtype.ext hae))⟩⟩
    · exact iff_of_false (fun h ↦ he' (f.mapEdgeSet_subset_edgeSet _ h)) (fun h ↦ he' h.1)
  rw [restrict_eq_deleteEdges, restrict_eq_deleteEdges, ← hmap]
  exact f.reachable_deleteEdges_mapEdgeSet_iff _ x y

/-- Transporting an edge subset `A ⊆ E(G)` along a multigraph isomorphism `f : Iso G H` preserves
the component count of the corresponding spanning restriction. -/
theorem componentCount_restrict_image (f : Iso G H) (A : Set E(G)) :
    (G.restrict (Subtype.val '' A)).componentCount =
      (H.restrict (Subtype.val '' (f.edgeEquiv '' A))).componentCount := by
  rw [componentCount_eq_natCard_toSimpleGraph, componentCount_eq_natCard_toSimpleGraph]
  refine Nat.card_congr (Equiv.ofBijective
    (SimpleGraph.ConnectedComponent.lift
      (fun x : V(G.restrict (Subtype.val '' A)) ↦
        (H.restrict (Subtype.val '' (f.edgeEquiv '' A))).toSimpleGraph.connectedComponentMk
          ⟨f.vertexEquiv ⟨x.1, by simpa using x.2⟩, by simp⟩)
      fun x y hw _ ↦ by
        rw [toSimpleGraph_connectedComponentMk_eq_iff]
        exact (f.reachable_restrict_image_iff A
          ⟨x.1, by simpa using x.2⟩ ⟨y.1, by simpa using y.2⟩).mpr
          (toSimpleGraph_reachable_iff.mp hw.reachable)) ⟨?_, ?_⟩)
  · intro C D hCD
    induction C using SimpleGraph.ConnectedComponent.ind with | h x => ?_
    induction D using SimpleGraph.ConnectedComponent.ind with | h y => ?_
    simp only [SimpleGraph.ConnectedComponent.lift_mk,
      toSimpleGraph_connectedComponentMk_eq_iff] at hCD ⊢
    exact (f.reachable_restrict_image_iff A
      ⟨x.1, by simpa using x.2⟩ ⟨y.1, by simpa using y.2⟩).mp hCD
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with | h z => ?_
    let x := f.vertexEquiv.symm ⟨z.1, by simpa using z.2⟩
    refine ⟨(G.restrict (Subtype.val '' A)).toSimpleGraph.connectedComponentMk
      ⟨x.1, by simp⟩, ?_⟩
    simp only [SimpleGraph.ConnectedComponent.lift_mk, x, Subtype.coe_eta, Equiv.apply_symm_apply]

/-- `Graph.fkPartition` is invariant under multigraph isomorphism. -/
theorem fkPartition_eq (f : Iso G H) [Finite E(G)] [Finite E(H)]
    (Q : R) (v : E(H) → R) :
    G.fkPartition Q (v ∘ f.edgeEquiv) = H.fkPartition Q v := by
  classical
  have := Fintype.ofFinite E(G)
  have := Fintype.ofFinite E(H)
  rw [fkPartition_eq_sum_fintype, fkPartition_eq_sum_fintype]
  refine Fintype.sum_equiv (Equiv.finsetCongr f.edgeEquiv) _ _ fun A ↦ ?_
  have hset : ((Equiv.finsetCongr f.edgeEquiv A : Finset E(H)) : Set E(H)) =
      f.edgeEquiv '' (A : Set E(G)) := by
    ext e'
    simp [Equiv.finsetCongr_apply]
  rw [hset, ← f.componentCount_restrict_image (A : Set E(G))]
  congr 1
  simp [Equiv.finsetCongr_apply, Finset.prod_map]

/-- `Graph.pottsPartition` is invariant under multigraph isomorphism. -/
theorem pottsPartition_eq (f : Iso G H) [Finite V(G)] [Finite E(G)] [Finite V(H)] [Finite E(H)]
    (q : ℕ) (v : E(H) → R) :
    G.pottsPartition q (v ∘ f.edgeEquiv) = H.pottsPartition q v := by
  rw [pottsPartition_eq_fkPartition, f.fkPartition_eq, pottsPartition_eq_fkPartition]

end Iso

/-! ### Empty, edgeless, small-`q`, and parallel-edge evaluations -/

/-- Restricting a multigraph to the empty edge set leaves one connected component per actual
vertex. -/
@[simp]
theorem componentCount_restrict_empty (G : Graph V E) :
    (G.restrict ∅).componentCount = V(G).ncard := by
  rw [componentCount_eq_natCard_toSimpleGraph, ← Nat.card_coe_set_eq]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : V(G) ↦
      (G.restrict ∅).toSimpleGraph.connectedComponentMk ⟨x.1, by simp⟩) ⟨?_, ?_⟩)).symm
  · intro x y hxy
    rw [toSimpleGraph_connectedComponentMk_eq_iff] at hxy
    obtain ⟨-, ⟨p⟩⟩ := reachable_def.mp hxy
    suffices ∀ {a b : V}, (G.restrict ∅).Walk a b → a = b from Subtype.ext (this p)
    intro a b q
    cases q with
    | nil => rfl
    | cons _ hd _ => simp at hd
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with | h x => ?_
    exact ⟨⟨x.1, by simpa using x.2⟩, rfl⟩

/-- An edgeless multigraph has `componentCount` equal to `V(G).ncard`. -/
theorem componentCount_of_edgeSet_eq_empty {G : Graph V E} (hE : E(G) = ∅) :
    G.componentCount = V(G).ncard := by
  have h : G.restrict ∅ = G := (restrict_eq_self_iff G ∅).mpr (hE ▸ Subset.rfl)
  rw [← componentCount_restrict_empty G, h]

/-- On an edgeless multigraph, `Z_FK(G; Q, v) = Q ^ V(G).ncard`. -/
theorem fkPartition_of_edgeSet_eq_empty {G : Graph V E} [Finite E(G)]
    (hE : E(G) = ∅) (Q : R) (v : E(G) → R) :
    G.fkPartition Q v = Q ^ V(G).ncard := by
  classical
  have := Fintype.ofFinite E(G)
  have : IsEmpty E(G) := by rw [hE]; infer_instance
  rw [fkPartition_eq_sum_fintype, Fintype.sum_unique]
  have hemp : (default : Finset E(G)) = ∅ := Subsingleton.elim _ _
  simp [hemp]

/-- On an edgeless multigraph, `Z_Potts(G; q, v) = q ^ V(G).ncard`. -/
theorem pottsPartition_of_edgeSet_eq_empty {G : Graph V E} [Finite V(G)] [Finite E(G)]
    (hE : E(G) = ∅) (q : ℕ) (v : E(G) → R) :
    G.pottsPartition q v = (q : R) ^ V(G).ncard := by
  rw [pottsPartition_eq_fkPartition, fkPartition_of_edgeSet_eq_empty hE]

/-- `Z_FK(⊥; Q, v) = 1` on the empty graph. -/
@[simp]
theorem fkPartition_bot (Q : R) (v : E((⊥ : Graph V E)) → R) :
    (⊥ : Graph V E).fkPartition Q v = 1 := by
  rw [fkPartition_of_edgeSet_eq_empty edgeSet_bot, vertexSet_bot, ncard_empty, pow_zero]

/-- `Z_Potts(⊥; q, v) = 1` on the empty graph. -/
@[simp]
theorem pottsPartition_bot (q : ℕ) (v : E((⊥ : Graph V E)) → R) :
    (⊥ : Graph V E).pottsPartition q v = 1 := by
  rw [pottsPartition_eq_fkPartition, fkPartition_bot]

/-- On `noEdge S E`, `Z_FK = Q ^ S.ncard`. -/
@[simp]
theorem fkPartition_noEdge (S : Set V) (Q : R) (v : E(noEdge S E) → R) :
    (noEdge S E).fkPartition Q v = Q ^ S.ncard := by
  rw [fkPartition_of_edgeSet_eq_empty (edgeSet_noEdge S E), vertexSet_noEdge]

/-- At `q = 0`, `pottsPartition` vanishes whenever `G` has at least one actual vertex. -/
theorem pottsPartition_zero_of_nonempty {G : Graph V E} [Finite V(G)] [Finite E(G)]
    (hV : V(G).Nonempty) (v : E(G) → R) :
    G.pottsPartition 0 v = 0 := by
  classical
  have := Fintype.ofFinite V(G)
  have := Fintype.ofFinite E(G)
  have : Nonempty V(G) := hV.to_subtype
  have : IsEmpty (V(G) → Fin 0) := inferInstance
  rw [pottsPartition_eq_sum_fintype]
  simp

/-- At `q = 0`, `pottsPartition` is `1` when `V(G) = ∅`. -/
theorem pottsPartition_zero_of_vertexSet_eq_empty {G : Graph V E} [Finite V(G)] [Finite E(G)]
    (hV : V(G) = ∅) (v : E(G) → R) :
    G.pottsPartition 0 v = 1 := by
  have hE : E(G) = ∅ := eq_empty_iff_forall_notMem.mpr fun e he ↦ by
    obtain ⟨x, _, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    exact (hV ▸ hxy.left_mem).elim
  rw [pottsPartition_of_edgeSet_eq_empty hE, hV, ncard_empty, pow_zero]

/-- At `q = 1`, every edge is monochromatic under the unique `1`-colouring, so `pottsPartition` is
the product of `1 + v e` over all edges. -/
theorem pottsPartition_one (G : Graph V E) [Finite V(G)] [Fintype E(G)] (v : E(G) → R) :
    G.pottsPartition 1 v = ∏ e : E(G), (1 + v e) := by
  classical
  have := Fintype.ofFinite V(G)
  rw [pottsPartition_eq_sum_fintype, Fintype.sum_unique]
  refine Finset.prod_congr rfl fun e _ ↦ ?_
  have hm : G.IsMonochromaticEdge (default : V(G) → Fin 1) e :=
    fun _ _ _ ↦ Subsingleton.elim _ _
  rw [ite_eq_left_iff.mpr fun h ↦ (h hm).elim]

/-- On `banana x y F` with `x ≠ y` and `F` finite, the empty subset has two components and every
nonempty subset has one component, so `Z_FK = Q ^ 2 + Q * ∑_{A ≠ ∅} ∏_{e ∈ A} v_e`. -/
theorem fkPartition_banana_of_ne {x y : V} (hne : x ≠ y) (F : Set E)
    [Fintype E(banana x y F)] [DecidableEq E(banana x y F)]
    (Q : R) (v : E(banana x y F) → R) :
    (banana x y F).fkPartition Q v =
      Q ^ 2 + Q * ∑ A ∈ (Finset.univ : Finset (Finset E(banana x y F))).erase ∅,
        ∏ e ∈ A, v e := by
  rw [fkPartition_eq_sum_fintype, ← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset _))]
  congr 1
  · simp only [Finset.coe_empty, image_empty, componentCount_restrict_empty, Finset.prod_empty,
      mul_one, vertexSet_banana]
    rw [ncard_pair hne]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    obtain ⟨hA0, -⟩ := Finset.mem_erase.mp hA
    have hneA : (Subtype.val '' (A : Set E(banana x y F))).Nonempty := by
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hA0
      exact ⟨e.1, e, he, rfl⟩
    have hrest : (banana x y F).restrict (Subtype.val '' (A : Set E(banana x y F))) =
        banana x y (Subtype.val '' (A : Set E(banana x y F))) := by
      ext a b c
      · simp
      · simp only [restrict_isLink, banana_isLink, mem_image, Finset.mem_coe]
        refine ⟨fun ⟨⟨e, he, hea⟩, _, hxy⟩ ↦ ⟨⟨e, he, hea⟩, hxy⟩,
          fun ⟨⟨e, he, hea⟩, hxy⟩ ↦ ⟨⟨e, he, hea⟩, hea ▸ by simpa using e.2, hxy⟩⟩
    rw [hrest, componentCount_banana hneA, pow_one]

/-- Over a commutative ring, `Z_FK(banana x y F; Q, v) = Q ^ 2 + Q * ((∏ e, (1 + v e)) - 1)` when
`x ≠ y`. -/
theorem fkPartition_banana_eq_add_mul_prod_sub_one {S : Type*} [CommRing S] {x y : V}
    (hne : x ≠ y) (F : Set E) [Fintype E(banana x y F)]
    (Q : S) (v : E(banana x y F) → S) :
    (banana x y F).fkPartition Q v =
      Q ^ 2 + Q * ((∏ e : E(banana x y F), (1 + v e)) - 1) := by
  classical
  rw [fkPartition_banana_of_ne hne F Q v]
  congr 2
  rw [Finset.prod_one_add, Finset.powerset_univ,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset _)), Finset.prod_empty,
    add_sub_cancel_left]

/-! ### Vertex-disjoint compatible unions -/

namespace Compatible

instance {G H : Graph V E} (h : G.Compatible H) [Finite V(G)] [Finite V(H)] :
    Finite V(h.union) := by
  rw [h.vertexSet_union]
  exact Set.Finite.to_subtype ((Set.toFinite V(G)).union (Set.toFinite V(H)))

instance {G H : Graph V E} (h : G.Compatible H) [Finite E(G)] [Finite E(H)] :
    Finite E(h.union) := by
  rw [h.edgeSet_union]
  exact Set.Finite.to_subtype ((Set.toFinite E(G)).union (Set.toFinite E(H)))

/-- Compatible multigraphs on disjoint vertex sets automatically have disjoint edge sets. -/
theorem disjoint_edgeSet_of_disjoint_vertexSet {G H : Graph V E} (h : G.Compatible H)
    (hd : Disjoint V(G) V(H)) : Disjoint E(G) E(H) := by
  rw [Set.disjoint_left]
  intro e heG heH
  obtain ⟨x, y, hxyG⟩ := G.exists_isLink_of_mem_edgeSet heG
  have hxyH : H.IsLink e x y := (h.isLink_congr heG heH).mp hxyG
  exact Set.disjoint_left.mp hd hxyG.left_mem hxyH.left_mem

/-- On a vertex-disjoint compatible union, no walk in `h.union` crosses between `V(G)` and
`V(H)`, and reachability within each piece agrees with reachability in that piece. -/
theorem reachable_union_iff {G H : Graph V E} (h : G.Compatible H)
    (hd : Disjoint V(G) V(H)) {x y : V} :
    h.union.Reachable x y ↔ G.Reachable x y ∨ H.Reachable x y := by
  refine ⟨fun hr ↦ ?_, fun hr ↦ hr.elim (Reachable.mono h.left_le_union)
    (Reachable.mono h.right_le_union)⟩
  obtain ⟨hx, ⟨p⟩⟩ := reachable_def.mp hr
  clear hr
  induction p with
  | nil =>
    have hx' : _ ∈ V(G) ∪ V(H) := h.vertexSet_union ▸ hx
    rcases hx' with hxG | hxH
    · exact .inl (Reachable.refl hxG)
    · exact .inr (Reachable.refl hxH)
  | @cons a b c e hab _ ih =>
    rcases h.union_isLink.mp hab with habG | habH
    · rcases ih hab.right_mem with hbcG | hbcH
      · exact .inl (habG.reachable.trans hbcG)
      · exact (Set.disjoint_left.mp hd habG.right_mem hbcH.left_mem).elim
    · rcases ih hab.right_mem with hbcG | hbcH
      · exact (Set.disjoint_left.mp hd hbcG.left_mem habH.right_mem).elim
      · exact .inr (habH.reachable.trans hbcH)

private theorem mapOfLE_left_ne_mapOfLE_right {G H : Graph V E} (h : G.Compatible H)
    (hd : Disjoint V(G) V(H)) (C : G.ConnectedComponent) (D : H.ConnectedComponent) :
    ConnectedComponent.mapOfLE h.left_le_union C ≠
      ConnectedComponent.mapOfLE h.right_le_union D := by
  intro hCD
  obtain ⟨x, hx⟩ := C.2.nonempty
  obtain ⟨y, hy⟩ := D.2.nonempty
  have hxG : x ∈ V(G) := C.2.le.vertexSet_mono hx
  have hyH : y ∈ V(H) := D.2.le.vertexSet_mono hy
  have hxK : x ∈ V((ConnectedComponent.mapOfLE h.right_le_union D).1) :=
    hCD ▸ C.mem_vertexSet_mapOfLE h.left_le_union hx
  have hyK : y ∈ V((ConnectedComponent.mapOfLE h.right_le_union D).1) :=
    D.mem_vertexSet_mapOfLE h.right_le_union hy
  have hr : h.union.Reachable x y :=
    ((ConnectedComponent.mapOfLE h.right_le_union D).2.connected.reachable hxK hyK).mono
      (ConnectedComponent.mapOfLE h.right_le_union D).2.le
  rcases (h.reachable_union_iff hd).mp hr with hG | hH
  · exact Set.disjoint_left.mp hd hG.right_mem hyH
  · exact Set.disjoint_left.mp hd hxG hH.left_mem

/-- Canonical equivalence between the disjoint union of connected components of `G` and `H` and the
connected components of a vertex-disjoint compatible union `h.union`. -/
noncomputable def connectedComponentEquiv {G H : Graph V E} (h : G.Compatible H)
    (hd : Disjoint V(G) V(H)) :
    G.ConnectedComponent ⊕ H.ConnectedComponent ≃ h.union.ConnectedComponent := by
  refine Equiv.ofBijective
    (Sum.elim (ConnectedComponent.mapOfLE h.left_le_union)
      (ConnectedComponent.mapOfLE h.right_le_union)) ⟨?_, ?_⟩
  · rintro (C | C) (D | D) hCD
    · obtain ⟨x, hx⟩ := C.2.nonempty
      obtain ⟨y, hy⟩ := D.2.nonempty
      have hxG := C.2.le.vertexSet_mono hx
      rw [C.eq_connectedComponentOf hx, D.eq_connectedComponentOf hy] at hCD ⊢
      simp only [Sum.elim_inl, Sum.inl.injEq, ConnectedComponent.mapOfLE_connectedComponentOf,
        connectedComponentOf_eq_connectedComponentOf_iff] at hCD ⊢
      exact ((h.reachable_union_iff hd).mp hCD).resolve_right fun hH ↦
        Set.disjoint_left.mp hd hxG hH.left_mem
    · exact (mapOfLE_left_ne_mapOfLE_right h hd C D hCD).elim
    · exact (mapOfLE_left_ne_mapOfLE_right h hd D C hCD.symm).elim
    · obtain ⟨x, hx⟩ := C.2.nonempty
      obtain ⟨y, hy⟩ := D.2.nonempty
      have hxH := C.2.le.vertexSet_mono hx
      rw [C.eq_connectedComponentOf hx, D.eq_connectedComponentOf hy] at hCD ⊢
      simp only [Sum.elim_inr, Sum.inr.injEq, ConnectedComponent.mapOfLE_connectedComponentOf,
        connectedComponentOf_eq_connectedComponentOf_iff] at hCD ⊢
      exact ((h.reachable_union_iff hd).mp hCD).resolve_left fun hG ↦
        Set.disjoint_left.mp hd hG.left_mem hxH
  · intro C
    obtain ⟨z, hz⟩ := C.2.nonempty
    have hzU : z ∈ V(G) ∪ V(H) := h.vertexSet_union ▸ C.2.le.vertexSet_mono hz
    rcases hzU with hzG | hzH
    · exact ⟨.inl (G.connectedComponentOf z hzG), by
        rw [Sum.elim_inl, ConnectedComponent.mapOfLE_connectedComponentOf,
          ← C.eq_connectedComponentOf hz]⟩
    · exact ⟨.inr (H.connectedComponentOf z hzH), by
        rw [Sum.elim_inr, ConnectedComponent.mapOfLE_connectedComponentOf,
          ← C.eq_connectedComponentOf hz]⟩

/-- Component count is additive across a vertex-disjoint compatible union when both pieces have
finitely many connected components. -/
theorem componentCount_union {G H : Graph V E} (h : G.Compatible H)
    (hd : Disjoint V(G) V(H)) [Finite G.ConnectedComponent] [Finite H.ConnectedComponent] :
    h.union.componentCount = G.componentCount + H.componentCount := by
  rw [componentCount_def, componentCount_def, componentCount_def,
    ← Nat.card_congr (h.connectedComponentEquiv hd), Nat.card_sum]

/-- Component count of a spanning restriction of a vertex-disjoint compatible union splits across
subsets of `E(G)` and `E(H)` when both restricted graphs have finitely many connected components. -/
theorem componentCount_union_restrict {G H : Graph V E} (h : G.Compatible H)
    (hd : Disjoint V(G) V(H)) {F₁ F₂ : Set E} (hF₁ : F₁ ⊆ E(G)) (hF₂ : F₂ ⊆ E(H))
    [Finite (G.restrict F₁).ConnectedComponent] [Finite (H.restrict F₂).ConnectedComponent] :
    (h.union.restrict (F₁ ∪ F₂)).componentCount =
      (G.restrict F₁).componentCount + (H.restrict F₂).componentCount := by
  have hdE : Disjoint E(G) E(H) := h.disjoint_edgeSet_of_disjoint_vertexSet hd
  have hGrest : G.restrict (F₁ ∪ F₂) = G.restrict F₁ := by
    refine (Compatible.of_le_le restrict_le restrict_le).ext (by simp) ?_
    ext d
    simp only [edgeSet_restrict, mem_inter_iff, mem_union]
    exact ⟨fun ⟨hdG, hd'⟩ ↦ ⟨hdG, hd'.resolve_right fun hd₂ ↦
      Set.disjoint_left.mp hdE hdG (hF₂ hd₂)⟩, fun ⟨hdG, hd₁⟩ ↦ ⟨hdG, .inl hd₁⟩⟩
  have hHrest : H.restrict (F₁ ∪ F₂) = H.restrict F₂ := by
    refine (Compatible.of_le_le restrict_le restrict_le).ext (by simp) ?_
    ext d
    simp only [edgeSet_restrict, mem_inter_iff, mem_union]
    exact ⟨fun ⟨hdH, hd'⟩ ↦ ⟨hdH, hd'.resolve_left fun hd₁ ↦
      Set.disjoint_left.mp hdE (hF₁ hd₁) hdH⟩, fun ⟨hdH, hd₂⟩ ↦ ⟨hdH, .inr hd₂⟩⟩
  have hcompatRest : (G.restrict (F₁ ∪ F₂)).Compatible (H.restrict (F₁ ∪ F₂)) :=
    fun e heG heH x y ↦ by
      simp only [restrict_isLink]
      exact and_congr_right' (h (restrict_le.edgeSet_mono heG) (restrict_le.edgeSet_mono heH) x y)
  have hunionRest : h.union.restrict (F₁ ∪ F₂) = hcompatRest.union := by
    ext a b c <;> simp [and_or_left]
  have : Finite (G.restrict (F₁ ∪ F₂)).ConnectedComponent := by rwa [hGrest]
  have : Finite (H.restrict (F₁ ∪ F₂)).ConnectedComponent := by rwa [hHrest]
  rw [hunionRest, hcompatRest.componentCount_union (by simpa using hd), hGrest, hHrest]

/-- Edge-carrier equivalence `E(G) ⊕ E(H) ≃ E(h.union)` for compatible graphs with disjoint edge
sets. -/
private noncomputable def edgeSumEquiv {G H : Graph V E} (h : G.Compatible H)
    (hdE : Disjoint E(G) E(H)) : E(G) ⊕ E(H) ≃ E(h.union) := by
  classical
  exact
    { toFun
        | .inl a => Set.inclusion h.left_le_union.edgeSet_mono a
        | .inr b => Set.inclusion h.right_le_union.edgeSet_mono b
      invFun := fun x ↦
        if hxG : x.1 ∈ E(G) then .inl ⟨x.1, hxG⟩
        else .inr ⟨x.1, (show x.1 ∈ E(G) ∪ E(H) from h.edgeSet_union ▸ x.2).resolve_left hxG⟩
      left_inv := fun
        | .inl a => by dsimp only; rw [dite_eq_left a.2]
        | .inr b => by dsimp only; rw [dite_eq_right (Set.disjoint_right.mp hdE b.2)]
      right_inv := fun x ↦ by dsimp only; split_ifs <;> rfl }

/-- **Multiplicativity of `fkPartition` on vertex-disjoint compatible unions.** -/
theorem fkPartition_union {G H : Graph V E} (h : G.Compatible H) (hd : Disjoint V(G) V(H))
    [Finite V(G)] [Finite E(G)] [Finite V(H)] [Finite E(H)]
    (Q : R) (v : E(h.union) → R) :
    h.union.fkPartition Q v =
      G.fkPartition Q (v ∘ Set.inclusion h.left_le_union.edgeSet_mono) *
        H.fkPartition Q (v ∘ Set.inclusion h.right_le_union.edgeSet_mono) := by
  classical
  have := Fintype.ofFinite E(G)
  have := Fintype.ofFinite E(H)
  have := Fintype.ofFinite E(h.union)
  let eEquiv := edgeSumEquiv h (h.disjoint_edgeSet_of_disjoint_vertexSet hd)
  let finsetEquiv : Finset E(G) × Finset E(H) ≃ Finset E(h.union) :=
    Finset.sumEquiv.toEquiv.symm.trans (Equiv.finsetCongr eEquiv)
  rw [fkPartition_eq_sum_fintype, fkPartition_eq_sum_fintype, fkPartition_eq_sum_fintype,
    Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv finsetEquiv _ _ fun p ↦ ?_).symm
  rcases p with ⟨AG, AH⟩
  let A : Finset E(h.union) := finsetEquiv (AG, AH)
  have hdisj : A = (AG.disjSum AH).map eEquiv.toEmbedding := by rfl
  have hAimg : Subtype.val '' (A : Set E(h.union)) =
      (Subtype.val '' (AG : Set E(G))) ∪ (Subtype.val '' (AH : Set E(H))) := by
    ext d
    simp only [hdisj, Finset.coe_map, Equiv.coe_toEmbedding, mem_image, Finset.mem_coe,
      Sum.exists, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, mem_union]
    constructor
    · rintro ⟨_, (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩), rfl⟩
      · exact .inl ⟨a, ha, by rfl⟩
      · exact .inr ⟨b, hb, by rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact ⟨eEquiv (.inl a), .inl ⟨a, ha, by rfl⟩, by rfl⟩
      · exact ⟨eEquiv (.inr b), .inr ⟨b, hb, by rfl⟩, by rfl⟩
  have hprod : ∏ d ∈ A, v d =
      (∏ a ∈ AG, v (Set.inclusion h.left_le_union.edgeSet_mono a)) *
        (∏ b ∈ AH, v (Set.inclusion h.right_le_union.edgeSet_mono b)) := by
    rw [hdisj, Finset.prod_map, Finset.prod_disjSum]
    rfl
  dsimp only
  rw [show finsetEquiv (AG, AH) = A by rfl, hAimg,
    h.componentCount_union_restrict hd (Subtype.coe_image_subset _ _)
      (Subtype.coe_image_subset _ _),
    pow_add, hprod, mul_mul_mul_comm]
  rfl

/-- **Multiplicativity of `pottsPartition` on vertex-disjoint compatible unions.** -/
theorem pottsPartition_union {G H : Graph V E} (h : G.Compatible H) (hd : Disjoint V(G) V(H))
    [Finite V(G)] [Finite E(G)] [Finite V(H)] [Finite E(H)]
    (q : ℕ) (v : E(h.union) → R) :
    h.union.pottsPartition q v =
      G.pottsPartition q (v ∘ Set.inclusion h.left_le_union.edgeSet_mono) *
        H.pottsPartition q (v ∘ Set.inclusion h.right_le_union.edgeSet_mono) := by
  rw [pottsPartition_eq_fkPartition, pottsPartition_eq_fkPartition,
    pottsPartition_eq_fkPartition, h.fkPartition_union hd]

end Compatible

/-! ### Deletion–contraction, loop, and bridge recursions -/

/-- Equivalence splitting `Finset α` into subsets avoiding `a` and subsets containing `a`. -/
private def finsetSplitAtEquiv {α : Type*} [DecidableEq α] (a : α) :
    Finset {x : α // x ≠ a} ⊕ Finset {x : α // x ≠ a} ≃ Finset α where
  toFun
    | .inl B => B.map (Function.Embedding.subtype (· ≠ a))
    | .inr B => insert a (B.map (Function.Embedding.subtype (· ≠ a)))
  invFun A := if a ∈ A then .inr (A.subtype (· ≠ a)) else .inl (A.subtype (· ≠ a))
  left_inv x := by
    dsimp only
    rcases x with B | B
    · have ha : a ∉ B.map (Function.Embedding.subtype (· ≠ a)) := by
        simp only [Finset.mem_map, Function.Embedding.subtype_apply, not_exists, not_and]
        exact fun b _ hb ↦ b.2 hb
      rw [ite_eq_right_iff.mpr fun h ↦ (ha h).elim]
      congr 1
      ext b
      simp [b.2]
    · have ha : a ∈ insert a (B.map (Function.Embedding.subtype (· ≠ a))) :=
        Finset.mem_insert_self a _
      rw [ite_eq_left_iff.mpr fun h ↦ (h ha).elim]
      congr 1
      ext b
      simp [b.2]
  right_inv A := by
    dsimp only
    by_cases ha : a ∈ A
    · rw [ite_eq_left_iff.mpr fun h ↦ (h ha).elim]
      dsimp only
      rw [Finset.subtype_map]
      ext x
      by_cases hxa : x = a
      · subst x
        simp [ha]
      · simp [hxa]
    · rw [ite_eq_right_iff.mpr fun h ↦ (ha h).elim]
      dsimp only
      rw [Finset.subtype_map]
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ h.1, fun hx ↦ ⟨hx, fun hxa ↦ ha (hxa ▸ hx)⟩⟩

private def edgeDeleteSingletonEquiv {G : Graph V E} {e : E} (he : e ∈ E(G)) :
    {a : E(G) // a ≠ ⟨e, he⟩} ≃ E(G.deleteEdges {e}) where
  toFun x := ⟨x.1.1, by
    rw [edgeSet_deleteEdges, mem_sdiff, mem_singleton_iff]
    exact ⟨x.1.2, fun h ↦ x.2 (Subtype.ext h)⟩⟩
  invFun y := ⟨⟨y.1, deleteEdges_le.edgeSet_mono y.2⟩, fun h ↦ by
    have hy : y.1 ∈ E(G) \ {e} := edgeSet_deleteEdges G {e} ▸ y.2
    exact hy.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def edgeContractSingletonEquiv {G : Graph V E} {e : E} (he : e ∈ E(G)) :
    {a : E(G) // a ≠ ⟨e, he⟩} ≃ E(G.contractEdge e) where
  toFun x := ⟨x.1.1, by
    rw [edgeSet_contractEdge, mem_sdiff, mem_singleton_iff]
    exact ⟨x.1.2, fun h ↦ x.2 (Subtype.ext h)⟩⟩
  invFun y := ⟨⟨y.1, G.edgeSet_contractEdge_subset e y.2⟩, fun h ↦
    (mem_edgeSet_contractEdge_iff.mp y.2).2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem fkPartition_sum_notMem {G : Graph V E} [Fintype E(G)]
    {e : E} (he : e ∈ E(G)) [DecidableEq E(G)]
    (Q : R) (v : E(G) → R) :
    (∑ B : Finset {x : E(G) // x ≠ ⟨e, he⟩},
        Q ^ (G.restrict (Subtype.val ''
            ((B.map (Function.Embedding.subtype _)) : Set E(G)))).componentCount *
          ∏ x ∈ B.map (Function.Embedding.subtype _), v x) =
      (G.deleteEdges {e}).fkPartition Q (v ∘ Set.inclusion deleteEdges_le.edgeSet_mono) := by
  classical
  have := Fintype.ofFinite E(G.deleteEdges {e})
  rw [fkPartition_eq_sum_fintype]
  refine Fintype.sum_equiv (Equiv.finsetCongr (edgeDeleteSingletonEquiv he)) _ _ fun B ↦ ?_
  let B' := Equiv.finsetCongr (edgeDeleteSingletonEquiv he) B
  have hset : Subtype.val '' ((B.map (Function.Embedding.subtype _)) : Set E(G)) =
      Subtype.val '' (B' : Set E(G.deleteEdges {e})) := by
    ext d
    simp only [B', edgeDeleteSingletonEquiv, Equiv.finsetCongr_apply, Finset.coe_map,
      Equiv.coe_toEmbedding, Function.Embedding.subtype, mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
  have henot : e ∉ Subtype.val '' (B' : Set E(G.deleteEdges {e})) := by
    rintro ⟨y, _, hy⟩
    have hy2 : y.1 ∈ E(G) \ {e} := edgeSet_deleteEdges G {e} ▸ y.2
    exact hy2.2 hy
  have hrest : (G.deleteEdges {e}).restrict (Subtype.val '' (B' : Set E(G.deleteEdges {e}))) =
      G.restrict (Subtype.val '' (B' : Set E(G.deleteEdges {e}))) := by
    refine (Compatible.of_le_le (restrict_le.trans deleteEdges_le) restrict_le).ext (by simp) ?_
    ext d
    simp only [edgeSet_restrict, edgeSet_deleteEdges, mem_inter_iff, mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨⟨hdG, _⟩, hdB⟩ ↦ ⟨hdG, hdB⟩,
      fun ⟨hdG, hdB⟩ ↦ ⟨⟨hdG, fun hde ↦ henot (hde ▸ hdB)⟩, hdB⟩⟩
  rw [show Equiv.finsetCongr (edgeDeleteSingletonEquiv he) B = B' from rfl, hset, hrest]
  congr 1
  simp [B', edgeDeleteSingletonEquiv, Equiv.finsetCongr_apply, Finset.prod_map]

private theorem fkPartition_sum_mem {G : Graph V E} [Fintype E(G)]
    {e : E} (he : e ∈ E(G)) [DecidableEq E(G)]
    (Q : R) (v : E(G) → R) :
    (∑ B : Finset {x : E(G) // x ≠ ⟨e, he⟩},
        Q ^ (G.restrict (Subtype.val ''
            ((insert (⟨e, he⟩ : E(G)) (B.map (Function.Embedding.subtype _)) :
              Finset E(G)) : Set E(G)))).componentCount *
          ∏ x ∈ insert ⟨e, he⟩ (B.map (Function.Embedding.subtype _)), v x) =
      v ⟨e, he⟩ *
        (G.contractEdge e).fkPartition Q
          (v ∘ Set.inclusion (G.edgeSet_contractEdge_subset e)) := by
  classical
  have := Fintype.ofFinite E(G.contractEdge e)
  rw [fkPartition_eq_sum_fintype, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.finsetCongr (edgeContractSingletonEquiv he)) _ _ fun B ↦ ?_
  let A0 := B.map (Function.Embedding.subtype (· ≠ (⟨e, he⟩ : E(G))))
  let B' := Equiv.finsetCongr (edgeContractSingletonEquiv he) B
  have heA0 : (⟨e, he⟩ : E(G)) ∉ A0 := by
    simp only [A0, Finset.mem_map, Function.Embedding.subtype_apply, not_exists, not_and]
    exact fun x _ hx ↦ x.2 hx
  have hset : Subtype.val '' ((insert (⟨e, he⟩ : E(G)) A0 : Finset E(G)) : Set E(G)) =
      insert e (Subtype.val '' (B' : Set E(G.contractEdge e))) := by
    ext d
    simp only [Finset.coe_insert, image_insert_eq, A0, B', edgeContractSingletonEquiv,
      Equiv.finsetCongr_apply, Finset.coe_map, Equiv.coe_toEmbedding, Function.Embedding.subtype,
      mem_insert_iff, mem_image, Finset.mem_coe]
    constructor
    · rintro (rfl | ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
      · exact .inl rfl
      · exact .inr ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro (rfl | ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
      · exact .inl rfl
      · exact .inr ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
  rw [show B.map (Function.Embedding.subtype _) = A0 from rfl,
    show Equiv.finsetCongr (edgeContractSingletonEquiv he) B = B' from rfl, hset,
    ← G.componentCount_contractEdge_restrict e (Subtype.val '' (B' : Set E(G.contractEdge e))),
    Finset.prod_insert heA0]
  have hprod : ∏ x ∈ A0, v x =
      ∏ x ∈ B', (v ∘ Set.inclusion (G.edgeSet_contractEdge_subset e)) x := by
    simp [A0, B', edgeContractSingletonEquiv, Equiv.finsetCongr_apply, Finset.prod_map]
  rw [hprod, mul_left_comm]

/-- **Deletion–contraction recursion for `fkPartition`.** For every actual edge `e ∈ E(G)` (whether
or not `e` is a loop), `Z_FK(G) = Z_FK(G \ {e}) + v_e * Z_FK(G / e)`. -/
theorem fkPartition_eq_deleteEdges_add_contractEdge {G : Graph V E} [Finite E(G)]
    {e : E} (he : e ∈ E(G)) (Q : R) (v : E(G) → R) :
    G.fkPartition Q v =
      (G.deleteEdges {e}).fkPartition Q (v ∘ Set.inclusion deleteEdges_le.edgeSet_mono) +
        v ⟨e, he⟩ *
          (G.contractEdge e).fkPartition Q
            (v ∘ Set.inclusion (G.edgeSet_contractEdge_subset e)) := by
  classical
  have := Fintype.ofFinite E(G)
  rw [fkPartition_eq_sum_fintype,
    ← (Fintype.sum_equiv (finsetSplitAtEquiv (⟨e, he⟩ : E(G))) _ _ fun _ ↦ rfl),
    Fintype.sum_sum_type]
  dsimp only [finsetSplitAtEquiv, Equiv.coe_fn_mk]
  rw [fkPartition_sum_notMem he, fkPartition_sum_mem he]

/-- **Deletion–contraction recursion for `pottsPartition`.** -/
theorem pottsPartition_eq_deleteEdges_add_contractEdge {G : Graph V E} [Finite V(G)] [Finite E(G)]
    {e : E} (he : e ∈ E(G)) (q : ℕ) (v : E(G) → R) :
    G.pottsPartition q v =
      (G.deleteEdges {e}).pottsPartition q (v ∘ Set.inclusion deleteEdges_le.edgeSet_mono) +
        v ⟨e, he⟩ *
          (G.contractEdge e).pottsPartition q
            (v ∘ Set.inclusion (G.edgeSet_contractEdge_subset e)) := by
  rw [pottsPartition_eq_fkPartition, pottsPartition_eq_fkPartition, pottsPartition_eq_fkPartition]
  exact G.fkPartition_eq_deleteEdges_add_contractEdge he (q : R) v

/-- Contracting a loop preserves `fkPartition` relative to deleting the loop. -/
theorem IsLoopAt.fkPartition_contractEdge_eq {G : Graph V E} [Finite E(G)]
    {e : E} {x : V} (h : G.IsLoopAt e x) (Q : R) (v : E(G) → R) :
    (G.contractEdge e).fkPartition Q (v ∘ Set.inclusion (G.edgeSet_contractEdge_subset e)) =
      (G.deleteEdges {e}).fkPartition Q (v ∘ Set.inclusion deleteEdges_le.edgeSet_mono) := by
  have hw : (v ∘ Set.inclusion (G.edgeSet_contractEdge_subset e)) ∘
      h.contractEdgeIsoDeleteEdges.edgeEquiv =
      v ∘ Set.inclusion deleteEdges_le.edgeSet_mono := by
    ext d
    simp only [Function.comp_apply]
    congr 1
    apply Subtype.ext
    simp
  rw [← h.contractEdgeIsoDeleteEdges.fkPartition_eq Q, hw]

/-- **Loop factorisation for `fkPartition`.** If `e` is a loop of `G`,
`Z_FK(G) = (1 + v_e) * Z_FK(G \ {e})`. -/
theorem IsLoopAt.fkPartition_eq {G : Graph V E} [Finite E(G)]
    {e : E} {x : V} (h : G.IsLoopAt e x) (Q : R) (v : E(G) → R) :
    G.fkPartition Q v =
      (1 + v ⟨e, h.edge_mem⟩) *
        (G.deleteEdges {e}).fkPartition Q (v ∘ Set.inclusion deleteEdges_le.edgeSet_mono) := by
  rw [G.fkPartition_eq_deleteEdges_add_contractEdge h.edge_mem, h.fkPartition_contractEdge_eq,
    one_add_mul]

/-- **Loop factorisation for `pottsPartition`.** If `e` is a loop of `G`,
`Z_Potts(G) = (1 + v_e) * Z_Potts(G \ {e})`. -/
theorem IsLoopAt.pottsPartition_eq {G : Graph V E} [Finite V(G)] [Finite E(G)]
    {e : E} {x : V} (h : G.IsLoopAt e x) (q : ℕ) (v : E(G) → R) :
    G.pottsPartition q v =
      (1 + v ⟨e, h.edge_mem⟩) *
        (G.deleteEdges {e}).pottsPartition q (v ∘ Set.inclusion deleteEdges_le.edgeSet_mono) := by
  rw [pottsPartition_eq_fkPartition, pottsPartition_eq_fkPartition, h.fkPartition_eq]

/-- Deleting a bridge multiplies the Fortuin–Kasteleyn sum of its contraction by `Q`:
`Z_FK(G \ {e}) = Q * Z_FK(G / e)`. -/
theorem IsBridge.fkPartition_deleteEdges_eq {G : Graph V E} [Finite V(G)] [Finite E(G)]
    {e : E} (h : G.IsBridge e) (Q : R) (v : E(G) → R) :
    (G.deleteEdges {e}).fkPartition Q (v ∘ Set.inclusion deleteEdges_le.edgeSet_mono) =
      Q * (G.contractEdge e).fkPartition Q
        (v ∘ Set.inclusion (G.edgeSet_contractEdge_subset e)) := by
  classical
  have := Fintype.ofFinite E(G.deleteEdges {e})
  have := Fintype.ofFinite E(G.contractEdge e)
  rw [fkPartition_eq_sum_fintype, fkPartition_eq_sum_fintype, Finset.mul_sum]
  let edgeEq : E(G.deleteEdges {e}) ≃ E(G.contractEdge e) :=
    { toFun := fun x ↦ ⟨x.1, (edgeSet_contractEdge G e).symm ▸ edgeSet_deleteEdges G {e} ▸ x.2⟩
      invFun := fun y ↦ ⟨y.1, (edgeSet_deleteEdges G {e}).symm ▸ edgeSet_contractEdge G e ▸ y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine Fintype.sum_equiv (Equiv.finsetCongr edgeEq) _ _ fun B ↦ ?_
  let B' := Equiv.finsetCongr edgeEq B
  let F : Set E := Subtype.val '' (B' : Set E(G.contractEdge e))
  have hF : Subtype.val '' (B : Set E(G.deleteEdges {e})) = F := by
    ext d
    simp [B', F, edgeEq, Equiv.finsetCongr_apply]
  have hdelRest : (G.deleteEdges {e}).restrict F = (G.restrict (insert e F)).deleteEdges {e} := by
    refine (Compatible.of_le_le (restrict_le.trans deleteEdges_le)
      (deleteEdges_le.trans restrict_le)).ext (by simp) ?_
    ext d
    simp only [edgeSet_restrict, edgeSet_deleteEdges, mem_inter_iff, mem_sdiff, mem_insert_iff,
      mem_singleton_iff]
    refine ⟨fun ⟨⟨hdG, hde⟩, hdF⟩ ↦ ⟨⟨hdG, .inr hdF⟩, hde⟩,
      fun ⟨⟨hdG, hd'⟩, hde⟩ ↦ ⟨⟨hdG, hde⟩, hd'.resolve_left hde⟩⟩
  have hbridge : (G.restrict (insert e F)).IsBridge e :=
    h.anti_of_mem restrict_le (by simp [h.mem_edgeSet])
  have hcomp : ((G.deleteEdges {e}).restrict F).componentCount =
      ((G.contractEdge e).restrict F).componentCount + 1 := by
    rw [hdelRest, hbridge.componentCount_deleteEdges, ← G.componentCount_contractEdge_restrict]
  have hprod : ∏ d ∈ B, (v ∘ Set.inclusion deleteEdges_le.edgeSet_mono) d =
      ∏ d ∈ B', (v ∘ Set.inclusion (G.edgeSet_contractEdge_subset e)) d := by
    simp [B', edgeEq, Equiv.finsetCongr_apply, Finset.prod_map]
  rw [show Equiv.finsetCongr edgeEq B = B' from rfl, hF,
    show Subtype.val '' (B' : Set E(G.contractEdge e)) = F from rfl,
    hcomp, pow_succ', hprod, mul_assoc]

/-- **Bridge factorisation for `fkPartition`.** If `e` is a bridge of `G`,
`Z_FK(G) = (Q + v_e) * Z_FK(G / e)`. -/
theorem IsBridge.fkPartition_eq {G : Graph V E} [Finite V(G)] [Finite E(G)]
    {e : E} (h : G.IsBridge e) (Q : R) (v : E(G) → R) :
    G.fkPartition Q v =
      (Q + v ⟨e, h.mem_edgeSet⟩) *
        (G.contractEdge e).fkPartition Q (v ∘ Set.inclusion (G.edgeSet_contractEdge_subset e)) := by
  rw [G.fkPartition_eq_deleteEdges_add_contractEdge h.mem_edgeSet, h.fkPartition_deleteEdges_eq,
    add_mul]

/-- **Bridge factorisation for `pottsPartition`.** If `e` is a bridge of `G`,
`Z_Potts(G) = (q + v_e) * Z_Potts(G / e)`. -/
theorem IsBridge.pottsPartition_eq {G : Graph V E} [Finite V(G)] [Finite E(G)]
    {e : E} (h : G.IsBridge e) (q : ℕ) (v : E(G) → R) :
    G.pottsPartition q v =
      ((q : R) + v ⟨e, h.mem_edgeSet⟩) *
        (G.contractEdge e).pottsPartition q
          (v ∘ Set.inclusion (G.edgeSet_contractEdge_subset e)) := by
  rw [pottsPartition_eq_fkPartition, pottsPartition_eq_fkPartition, h.fkPartition_eq]

end Graph

end
