/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Cut-minimal graphs

A graph is cut-minimal if every cut contains at most as many edges as non-edges.
Equivalently, toggling all pairs across any cut cannot decrease its edge count.
This is the graph-theoretic minimality condition for binary cochains: a binary gauge
changes the edge set by symmetric difference with a cut.

The cut-minimality convention follows D. N. Kozlov, *The first Cheeger constant of a
simplex*, arXiv:1610.07136v2, Section 2. The characterizations here isolate isomorphism
invariance and the finite edge-count and vertex-count criteria, independently of any cochain
or coefficient group.

## Main definitions and results

* `SimpleGraph.IsCutMinimal`: every cut `(S, Sᶜ)` contains at most as many edges as non-edges.
* `SimpleGraph.Iso.isCutMinimal_iff`: cut-minimality is invariant under graph isomorphism.
* `SimpleGraph.isCutMinimal_iff_two_mul_card_between_le`: finite cut-minimality in terms of
  vertex counts, `2 * (G.between S Sᶜ).edgeFinset.card ≤ S.toFinset.card * Sᶜ.toFinset.card`.
* `SimpleGraph.isCutMinimal_iff_card_le_card_symmDiff`: switching any cut does not decrease the
  edge count.
* `SimpleGraph.IsCutMinimal.two_mul_degree_le`: every vertex of a finite cut-minimal graph has
  `2 * G.degree v ≤ Fintype.card V - 1`.
* `SimpleGraph.IsCutMinimal.two_mul_card_edgeFinset_le_choose_two`: a finite cut-minimal graph has
  at most half of all vertex pairs as edges, `2 * #G.edgeFinset ≤ (Fintype.card V).choose 2`.
* `SimpleGraph.IsCutMinimal.two_mul_card_edgeFinset_lt_choose_two`: on at least two vertices, a
  cut-minimal graph uses strictly fewer than half of all vertex pairs,
  `2 * #G.edgeFinset < (Fintype.card V).choose 2`.
-/

public section

open scoped symmDiff Finset

namespace SimpleGraph

variable {V : Type*}

section Finite

/-- Every cut contains at most as many edges of `G` as non-edges of `G`. -/
def IsCutMinimal (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, (G.between S Sᶜ).edgeSet.encard ≤
    ((⊤ : SimpleGraph V).between S Sᶜ \ G).edgeSet.encard

/-- The defining cut inequality for cut-minimality, with no finiteness assumptions. -/
theorem isCutMinimal_def (G : SimpleGraph V) :
    G.IsCutMinimal ↔ ∀ S : Set V, (G.between S Sᶜ).edgeSet.encard ≤
      ((⊤ : SimpleGraph V).between S Sᶜ \ G).edgeSet.encard := (Iff.rfl)

private theorem isCutMinimal_of_iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (hG : G.IsCutMinimal) : H.IsCutMinimal := fun T ↦ by
  let S : Set V := f ⁻¹' T
  have hpre : Sᶜ = f ⁻¹' Tᶜ := rfl
  let iso₁ : G.between S Sᶜ ≃g H.between T Tᶜ :=
    { f.toEquiv with
      map_rel_iff' := fun {x y} ↦ by
        simp only [S, hpre, between_adj, Set.mem_preimage, RelIso.coe_fn_toEquiv, f.map_adj_iff] }
  let iso₂ : (⊤ : SimpleGraph V).between S Sᶜ \ G ≃g
      (⊤ : SimpleGraph W).between T Tᶜ \ H :=
    { f.toEquiv with
      map_rel_iff' := fun {x y} ↦ by
        simp only [S, hpre, sdiff_adj, between_adj, top_adj, Set.mem_preimage, ne_eq,
          RelIso.coe_fn_toEquiv, f.apply_eq_iff_eq, f.map_adj_iff] }
  rw [← Set.encard_congr iso₁.mapEdgeSet, ← Set.encard_congr iso₂.mapEdgeSet]
  exact hG S

/-- Cut-minimality is invariant under graph isomorphism. -/
theorem Iso.isCutMinimal_iff {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    G.IsCutMinimal ↔ H.IsCutMinimal :=
  ⟨isCutMinimal_of_iso f, isCutMinimal_of_iso f.symm⟩

variable [Fintype V] [DecidableEq V]

/-- The defining cut inequality for cut-minimality, using decidable edge finsets. -/
theorem isCutMinimal_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsCutMinimal ↔
      ∀ (S : Set V) [DecidablePred (· ∈ S)], (G.between S Sᶜ).edgeFinset.card ≤
        ((⊤ : SimpleGraph V).between S Sᶜ \ G).edgeFinset.card := by
  have hcut (S : Set V) [DecidablePred (· ∈ S)] :
      (G.between S Sᶜ).edgeSet.encard ≤
          ((⊤ : SimpleGraph V).between S Sᶜ \ G).edgeSet.encard ↔
        (G.between S Sᶜ).edgeFinset.card ≤
          ((⊤ : SimpleGraph V).between S Sᶜ \ G).edgeFinset.card := by
    rw [← coe_edgeFinset, ← coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard,
      Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
  constructor
  · intro h S _
    exact (hcut S).mp (h S)
  · intro h S
    -- The definition quantifies over all sets, without a decidability assumption.
    classical
    exact (hcut S).mpr (h S)

/-- Cut-minimality says that at most half of each cut consists of edges. -/
theorem isCutMinimal_iff_two_mul_card_inter_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsCutMinimal ↔ ∀ (S : Set V) [DecidablePred (· ∈ S)],
      2 * (G.edgeFinset ∩ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset).card ≤
        ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset.card := by
  rw [isCutMinimal_iff]
  apply forall_congr'
  intro S
  apply forall_congr'
  intro _
  rw [edgeFinset_between, edgeFinset_sdiff]
  have h := Finset.card_sdiff_add_card_inter
    ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset G.edgeFinset
  rw [Finset.inter_comm] at h
  omega

omit [DecidableEq V] in
/-- Cut-minimality in terms of vertex counts: twice the number of edges of `G` across `(S, Sᶜ)` is
at most `S.toFinset.card * Sᶜ.toFinset.card`. -/
theorem isCutMinimal_iff_two_mul_card_between_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsCutMinimal ↔ ∀ (S : Set V) [DecidablePred (· ∈ S)],
      2 * (G.between S Sᶜ).edgeFinset.card ≤ S.toFinset.card * Sᶜ.toFinset.card := by
  classical
  rw [isCutMinimal_iff_two_mul_card_inter_le]
  refine forall_congr' fun S ↦ forall_congr' fun _ ↦ ?_
  rw [← edgeFinset_between, card_edgeFinset_top_between disjoint_compl_right]

/-- A graph is cut-minimal exactly when switching any cut does not reduce its edge count.
This is the cardinality criterion used to identify minimal binary cochains. -/
theorem isCutMinimal_iff_card_le_card_symmDiff (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsCutMinimal ↔ ∀ (S : Set V) [DecidablePred (· ∈ S)],
      G.edgeFinset.card ≤ (G.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset).card := by
  rw [isCutMinimal_iff_two_mul_card_inter_le]
  apply forall_congr'
  intro S
  apply forall_congr'
  intro _
  have h := Finset.card_symmDiff_add_two_mul_card_inter
    G.edgeFinset ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset
  omega

/-- Cut-minimality counted from one side of each cut: for every finite set `s`, twice the number
of edges from `s` to its complement is at most the number `#s * #sᶜ` of pairs across the cut. -/
theorem isCutMinimal_iff_two_mul_sum_card_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsCutMinimal ↔ ∀ s : Finset V, 2 * ∑ v ∈ s, #{w ∈ sᶜ | G.Adj v w} ≤ #s * #sᶜ := by
  have key (s : Finset V) [DecidablePred (· ∈ (s : Set V))] :
      2 * #(G.edgeFinset ∩ ((⊤ : SimpleGraph V).between ↑s (↑s)ᶜ).edgeFinset) ≤
          #((⊤ : SimpleGraph V).between ↑s (↑s)ᶜ).edgeFinset ↔
        2 * ∑ v ∈ s, #{w ∈ sᶜ | G.Adj v w} ≤ #s * #sᶜ := by
    have hfin : (G.between ↑s (↑s)ᶜ).edgeFinset =
        (G ⊓ (⊤ : SimpleGraph V).between ↑s (↑s)ᶜ).edgeFinset :=
      edgeFinset_inj.mpr (between_eq_inf_top_between G _ _)
    have htop : ∑ v ∈ s, #{w ∈ sᶜ | (⊤ : SimpleGraph V).Adj v w} = #s * #sᶜ := by
      rw [Finset.sum_congr rfl fun v hv ↦ congrArg Finset.card <| Finset.filter_true_of_mem
        fun w hw ↦ (top_adj _ _).mpr (ne_of_mem_of_not_mem hv (Finset.mem_compl.mp hw))]
      simp
    rw [← edgeFinset_inf, ← hfin, card_edgeFinset_between_compl,
      card_edgeFinset_between_compl, htop]
  rw [isCutMinimal_iff_two_mul_card_inter_le]
  constructor
  · intro h s
    exact (key s).mp (h s)
  · intro h S _
    obtain ⟨s, rfl⟩ : ∃ s : Finset V, (s : Set V) = S := ⟨S.toFinset, by simp⟩
    exact (key s).mpr (h s)

omit [DecidableEq V] in
/-- In a cut-minimal finite graph, every vertex satisfies `2 * G.degree v ≤ Fintype.card V - 1`. -/
theorem IsCutMinimal.two_mul_degree_le {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsCutMinimal) (v : V) :
    2 * G.degree v ≤ Fintype.card V - 1 := by
  classical
  have hcut := (isCutMinimal_iff_two_mul_sum_card_le G).mp hG {v}
  have hnb : {w ∈ ({v} : Finset V)ᶜ | G.Adj v w} = G.neighborFinset v := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_singleton, mem_neighborFinset,
      and_iff_right_iff_imp]
    exact fun h => (G.ne_of_adj h).symm
  rw [Finset.sum_singleton, hnb, card_neighborFinset_eq_degree, Finset.card_singleton, one_mul,
    Finset.card_compl, Finset.card_singleton] at hcut
  exact hcut

omit [DecidableEq V] in
/-- In a cut-minimal finite graph, at most half of the vertex pairs are edges:
`2 * #G.edgeFinset ≤ (Fintype.card V).choose 2`. -/
theorem IsCutMinimal.two_mul_card_edgeFinset_le_choose_two {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsCutMinimal) :
    2 * #G.edgeFinset ≤ (Fintype.card V).choose 2 := by
  have hsum : 2 * ∑ v : V, G.degree v ≤ Fintype.card V * (Fintype.card V - 1) := by
    calc 2 * ∑ v : V, G.degree v
        = ∑ v : V, 2 * G.degree v := Finset.mul_sum _ _ _
      _ ≤ ∑ _v : V, (Fintype.card V - 1) := Finset.sum_le_sum fun v _ => hG.two_mul_degree_le v
      _ = Fintype.card V * (Fintype.card V - 1) := by simp
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  obtain ⟨k, hk⟩ := Nat.even_mul_pred_self (Fintype.card V)
  rw [Nat.choose_two_right, hk]
  omega

omit [DecidableEq V] in
/-- On at least two vertices, a cut-minimal finite graph uses strictly fewer than half of all
vertex pairs: `2 * #G.edgeFinset < (Fintype.card V).choose 2`. -/
theorem IsCutMinimal.two_mul_card_edgeFinset_lt_choose_two {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsCutMinimal) (hV : 2 ≤ Fintype.card V) :
    2 * #G.edgeFinset < (Fintype.card V).choose 2 := by
  classical
  -- Equality forces every vertex to have degree `(card V - 1) / 2`, violating cut-minimality on
  -- any non-adjacent pair `{u, v}`.
  refine lt_of_le_of_ne hG.two_mul_card_edgeFinset_le_choose_two fun heq => ?_
  have hch : 2 * (Fintype.card V).choose 2 = Fintype.card V * (Fintype.card V - 1) := by
    obtain ⟨k, hk⟩ := Nat.even_mul_pred_self (Fintype.card V)
    rw [Nat.choose_two_right, hk]
    omega
  have hsum_eq : ∑ v : V, 2 * G.degree v = ∑ _v : V, (Fintype.card V - 1) := by
    rw [← Finset.mul_sum, G.sum_degrees_eq_twice_card_edges]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have hreg : ∀ v : V, 2 * G.degree v = Fintype.card V - 1 := fun v =>
    (Finset.sum_eq_sum_iff_of_le fun w _ => hG.two_mul_degree_le w).mp hsum_eq v (Finset.mem_univ v)
  obtain ⟨u⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hdu := hreg u
  have hlt : #(G.neighborFinset u) < #(({u} : Finset V)ᶜ) := by
    rw [card_neighborFinset_eq_degree, Finset.card_compl, Finset.card_singleton]
    omega
  obtain ⟨v, hv_compl, hv_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have huv : u ≠ v := by simpa [eq_comm] using Finset.mem_compl.mp hv_compl
  have hnot_adj : ¬ G.Adj u v := by simpa [mem_neighborFinset] using hv_not
  have hcut := (isCutMinimal_iff_two_mul_sum_card_le G).mp hG {u, v}
  have hnb (x y : V) (hxy : ¬ G.Adj x y) :
      {w ∈ ({x, y} : Finset V)ᶜ | G.Adj x w} = G.neighborFinset x := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton,
      not_or, mem_neighborFinset, and_iff_right_iff_imp]
    intro h; exact ⟨(G.ne_of_adj h).symm, fun h' => hxy (h' ▸ h)⟩
  have hnu := hnb u v hnot_adj
  have hnv : {w ∈ ({u, v} : Finset V)ᶜ | G.Adj v w} = G.neighborFinset v := by
    rw [Finset.pair_comm]
    exact hnb v u fun h => hnot_adj h.symm
  rw [Finset.sum_pair huv, hnu, hnv, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree,
    Finset.card_compl, Finset.card_pair huv] at hcut
  have hdv := hreg v
  omega

end Finite

/-- The empty graph is cut-minimal. -/
@[simp] theorem isCutMinimal_bot : (⊥ : SimpleGraph V).IsCutMinimal := by
  intro S
  have h : (⊥ : SimpleGraph V).between S Sᶜ = ⊥ := by
    ext u v
    simp [between_adj]
  simp [h]

end SimpleGraph
