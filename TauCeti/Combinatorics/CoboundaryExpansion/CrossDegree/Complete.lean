/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Constant
public import TauCeti.Combinatorics.SimpleGraph.CutMinimal
public import TauCeti.Combinatorics.SimpleGraph.OddTriangles
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Basic
import TauCeti.Combinatorics.CoboundaryExpansion.StarBound
import TauCeti.Combinatorics.SimpleGraph.OddTriple
import TauCeti.Combinatorics.SimpleGraph.Staircase
import TauCeti.GroupTheory.Perm.FinThree.Basic
import TauCeti.GroupTheory.Perm.ParityRetract

/-!
# The cross-degree and symmetric-group Cheeger constants of complete two-complexes

This file evaluates the Chapman–Lubotzky cross-degree Cheeger constant `h1Err (complete V)` and,
as a squeeze corollary, the same-degree symmetric-group constant `h1Sym (complete V)` for every
finite vertex type `V`:

* When `Fintype.card V ≤ 2`, every cochain on any two-complex `X` is a coboundary, so both
  constants are `0` (`h1Err_eq_zero_of_card_le_two` in `CrossDegree/Constant.lean`, and
  `h1Sym_eq_zero_of_card_le_two` in `CheegerConstant.lean`).
* When `3 ≤ Fintype.card V`, both constants equal `(Fintype.card V : ℝ) / 3`
  (`h1Err_complete` and `h1Sym_complete`), and `h1Sym (complete V) = h1Err (complete V)` holds
  unconditionally (`h1Sym_complete_eq_h1Err_complete`). In the normalized convention, multiplying
  `h1Err (complete V)` by `#edges / #triangles` yields `card V / (card V - 2)`
  (`card_edges_div_card_triangles_mul_h1Err_complete`).

## Proof overview

By `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt`, every integer `k ≥ 3` is either divisible
by `4` or divisible by an odd integer `2 * t + 1 ≥ 3`:

1. **Multiples of four (`h1Err_complete_of_four_dvd`)**: any degree-`3` cochain `α` on
   `complete (Fin 4)` trivial on edges incident to `0` and assigning transpositions of
   `Perm (Fin 3)` to `{1, 2}`, `{1, 3}`, `{2, 3}` has `defect = 8`
   (`Cochain.defect_fin_four_of_isSwap`); when all three transpositions appear, it has
   `gaugeDist = 6` and global cross-degree `gaugeDistErr = 2`
   (`Cochain.gaugeDist_fin_four_of_eq_setOf_isSwap`,
   `Cochain.gaugeDistErr_fin_four_of_eq_setOf_isSwap`). Replicating the explicit witness
   `Cochain.threeSwapSeed` along `Fin 4 ×ₗ Fin c` preserves the optimal cross-degree ratio via
   `h1Err_complete_lex_le_card_mul_div`, yielding `h1Err (complete V) ≤ card V / 3`.
2. **Multiples of odd integers ≥ 3 (`h1Err_complete_of_mul_odd`)**: for any nonempty finite
   cut-minimal simple graph `G` on `V`, embedding `G` as a transposition-valued cochain of degree
   `n := 2 * #G.edgeFinset` has `defect = 2 * #G.oddTriangleFinset` and same-degree
   `gaugeDist = 2 * #G.edgeFinset` (by parity retraction via `Equiv.Perm.parityRetract` and
   `SimpleGraph.isCutMinimal_iff_card_le_card_symmDiff`). Since every cut-minimal graph on at
   least two vertices satisfies `2 * #G.edgeFinset < (Fintype.card V).choose 2`
   (`SimpleGraph.IsCutMinimal.two_mul_card_edgeFinset_lt_choose_two`), at degree
   `n = 2 * #G.edgeFinset` the normalized same-degree distance `gaugeDist / n = 1` does not exceed
   the cross-degree mismatch baseline `#edges / (n + 1) ≥ 1`, so `gaugeDistErr = 1` and
   `h1Err (complete V) ≤ #G.oddTriangleFinset / #G.edgeFinset` unconditionally
   (`h1Err_complete_le_of_isCutMinimal`). Applying this to Kozlov's staircase graph
   `SimpleGraph.staircase c t` (`card V = c * (2 * t + 1)`, `t ≥ 1`) gives
   `h1Err (complete V) ≤ card V / 3`.
3. **Lower bound and squeeze**: the cross-degree star bound `card_div_three_le_h1Err` matches both
   upper bounds, giving `h1Err_complete`; squeezing with `card_div_three_le_h1Sym` and
   `h1Sym_le_h1Err` immediately yields `h1Sym_complete`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117, equations
  (2.8)–(2.9) and Proposition 3.2.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4:
  Including the Powers of Two, with Four Hamming-Native Readings That Do Not Obstruct*, Zenodo,
  doi:10.5281/zenodo.23245792, version 7, Proposition 5, Lemma 6, Corollary 7, Theorem 8, and
  Proposition 10.
* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136v2, Definition 3.2,
  equation (2.5), Lemmas 3.8 and 3.10, and Corollary 3.13.
-/

public section

open scoped symmDiff
open Finset Equiv Equiv.Perm

namespace TauCeti

open TwoComplex

/-! ### Three-transposition seed on `complete (Fin 4)` and multiples of four -/

namespace Cochain

/-- Any degree-`3` cochain on `complete (Fin 4)` that is trivial on edges from `0` and assigns a
transposition in `Perm (Fin 3)` to each of `(1, 2)`, `(1, 3)`, and `(2, 3)` has moved-point
defect `8`. -/
theorem defect_fin_four_of_isSwap (α : Cochain (complete (Fin 4)) (Perm (Fin 3)))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (h12 : (α 1 2).IsSwap) (h13 : (α 1 3).IsSwap) (h23 : (α 2 3).IsSwap) :
    α.defect (movedNorm (Fin 3)) = 8 := by
  have htris :
      (univ.filter (fun p : Fin 4 × Fin 4 × Fin 4 => p.1 < p.2.1 ∧ p.2.1 < p.2.2) :
        Finset (Fin 4 × Fin 4 × Fin 4)) = {(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)} := by
    decide
  have h01 : α 0 1 = 1 := h0 1 (by decide)
  have h02 : α 0 2 = 1 := h0 2 (by decide)
  have h03 : α 0 3 = 1 := h0 3 (by decide)
  have h20 : α 2 0 = 1 := by rw [α.apply_swap 0 2, h02, inv_one]
  have h30 : α 3 0 = 1 := by rw [α.apply_swap 0 3, h03, inv_one]
  have h123_sign : sign (α.holonomy 1 2 3) = -1 := by
    rw [holonomy_def, map_mul, map_mul, α.apply_swap 1 3, map_inv, h12.sign_eq, h23.sign_eq,
      h13.sign_eq]
    decide
  have h123_norm : movedNorm (Fin 3) (α.holonomy 1 2 3) = 2 := by
    rw [movedNorm_apply]
    exact_mod_cast (by decide : ∀ σ : Perm (Fin 3), sign σ = -1 → #σ.support = 2) _ h123_sign
  rw [defect_complete, htris, sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  have hn012 : movedNorm (Fin 3) (α.holonomy 0 1 2) = 2 := by
    simp [holonomy_def, h01, h20, h12.movedNorm]
  have hn013 : movedNorm (Fin 3) (α.holonomy 0 1 3) = 2 := by
    simp [holonomy_def, h01, h30, h13.movedNorm]
  have hn023 : movedNorm (Fin 3) (α.holonomy 0 2 3) = 2 := by
    simp [holonomy_def, h02, h30, h23.movedNorm]
  rw [hn012, hn013, hn023, h123_norm]
  norm_num

/-- Any three-transposition configuration on `complete (Fin 4)` has same-degree `movedNorm`
gauge distance `6`. -/
theorem gaugeDist_fin_four_of_eq_setOf_isSwap (α : Cochain (complete (Fin 4)) (Perm (Fin 3)))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    α.gaugeDist (movedNorm (Fin 3)) = 6 := by
  have hdiv := α.iInf_costErr_eq_gaugeDist_div
  simp_rw [costErr_complete] at hdiv
  have hval := ciInf_sum_distErr_fin_four_three_of_eq_setOf_isSwap α.toFun h0 hswaps
  rw [hval] at hdiv
  norm_num at hdiv
  linarith

/-- Any three-transposition configuration on `complete (Fin 4)` has cross-degree gauge distance `2`,
attained in its own degree `3`. -/
theorem gaugeDistErr_fin_four_of_eq_setOf_isSwap (α : Cochain (complete (Fin 4)) (Perm (Fin 3)))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    α.gaugeDistErr = 2 := by
  rw [gaugeDistErr_def]
  simp_rw [costErr_complete]
  exact ciInf₂_sum_distErr_fin_four_of_eq_setOf_isSwap α.toFun h0 hswaps

/-- Replicating any three-transposition configuration on `complete (Fin 4)` along `Fin 4 ×ₗ ι`
gives exact cross-degree gauge distance `2 * (Fintype.card ι) ^ 2`. -/
theorem gaugeDistErr_replicate_fin_four_of_eq_setOf_isSwap {ι : Type*} [Fintype ι] [LinearOrder ι]
    (α : Cochain (complete (Fin 4)) (Perm (Fin 3)))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (α.replicate ι).gaugeDistErr = 2 * (Fintype.card ι : ℝ) ^ 2 := by
  have hmin : α.gaugeDistErr = α.gaugeDist (movedNorm (Fin 3)) / 3 := by
    rw [α.gaugeDistErr_fin_four_of_eq_setOf_isSwap h0 hswaps,
      α.gaugeDist_fin_four_of_eq_setOf_isSwap h0 hswaps]
    norm_num
  rw [α.gaugeDistErr_replicate_eq (by omega) hmin,
    α.gaugeDistErr_fin_four_of_eq_setOf_isSwap h0 hswaps, mul_comm]

/-- An explicit degree-`3` cochain on `complete (Fin 4)` assigning `1` to edges incident to `0` and
the three distinct transpositions `(0 1)`, `(0 2)`, `(1 2)` to `{1, 2}`, `{1, 3}`, `{2, 3}`. -/
def threeSwapSeed : Cochain (complete (Fin 4)) (Perm (Fin 3)) where
  toFun u v := match u, v with
    | 1, 2 | 2, 1 => Equiv.swap 0 1
    | 1, 3 | 3, 1 => Equiv.swap 0 2
    | 2, 3 | 3, 2 => Equiv.swap 1 2
    | _, _ => 1
  inv_symm u v _ := by fin_cases u <;> fin_cases v <;> decide
  apply_eq_one_of_not_adj' u v huv := by
    obtain rfl : u = v := not_ne_iff.mp (mt (adj_complete u v).mpr huv)
    fin_cases u <;> rfl

/-- `threeSwapSeed` is trivial on every edge incident to `0`. -/
@[simp]
theorem threeSwapSeed_zero (v : Fin 4) : threeSwapSeed 0 v = 1 := by
  fin_cases v <;> rfl

/-- On `{1, 2, 3}`, `threeSwapSeed` takes the three transpositions of `Perm (Fin 3)`. -/
theorem threeSwapSeed_swaps :
    ({threeSwapSeed 1 2, threeSwapSeed 1 3, threeSwapSeed 2 3} : Set (Perm (Fin 3))) =
      {σ | σ.IsSwap} :=
  setOf_isSwap_perm_fin_three.symm

end Cochain

/-- On any complete complex whose vertex count is divisible by `4`, the cross-degree Cheeger
constant equals `card V / 3` (including `card V = 0`, where both sides are `0`). -/
theorem h1Err_complete_of_four_dvd {V : Type*} [Fintype V] [LinearOrder V]
    (h4 : 4 ∣ Fintype.card V) :
    h1Err (complete V) = (Fintype.card V : ℝ) / 3 := by
  obtain ⟨c, hc⟩ := h4
  rcases eq_or_ne c 0 with rfl | hc0
  · simp only [mul_zero] at hc
    rw [h1Err_eq_zero_of_card_le_two (complete V) (by omega), hc, Nat.cast_zero, zero_div]
  · refine le_antisymm ?_ (card_div_three_le_h1Err (by omega))
    have hcard : Fintype.card V = Fintype.card (Fin 4 ×ₗ Fin c) := by
      simp [hc]
    rw [h1Err_complete_eq_of_card_eq hcard]
    have h0 : ∀ v : Fin 4, 0 < v → Cochain.threeSwapSeed 0 v = 1 :=
      fun v _ => Cochain.threeSwapSeed_zero v
    have hswaps := Cochain.threeSwapSeed_swaps
    have hdef : Cochain.threeSwapSeed.defect (movedNorm (Fin 3)) = 8 :=
      Cochain.defect_fin_four_of_isSwap _ h0
        ⟨0, 1, by decide, rfl⟩ ⟨0, 2, by decide, rfl⟩ ⟨1, 2, by decide, rfl⟩
    have hgd := Cochain.gaugeDist_fin_four_of_eq_setOf_isSwap _ h0 hswaps
    have hgde := Cochain.gaugeDistErr_fin_four_of_eq_setOf_isSwap _ h0 hswaps
    have hmin : Cochain.threeSwapSeed.gaugeDistErr =
        Cochain.threeSwapSeed.gaugeDist (movedNorm (Fin 3)) / 3 := by
      rw [hgde, hgd]; norm_num
    have hle := h1Err_complete_lex_le_card_mul_div (V := Fin 4) (ι := Fin c) (by omega)
      (α := Cochain.threeSwapSeed) (by rw [hgde]; norm_num) hmin
    refine hle.trans_eq ?_
    rw [hdef, hgde, hc]
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    ring

/-! ### Transposition-valued cochains of cut-minimal graphs and staircase witnesses -/

section CutMinimal

private def graphCochain {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (τ : Perm (Fin n)) (hτ : τ.IsSwap) :
    Cochain (complete V) (Perm (Fin n)) where
  toFun u v := if G.Adj u v then τ else 1
  inv_symm u v _ := by
    have hinv : τ⁻¹ = τ := by obtain ⟨a, b, _, rfl⟩ := hτ; simp
    by_cases h : G.Adj u v
    · simp [h, h.symm, hinv]
    · simp [h, mt (fun h' : G.Adj v u => h'.symm) h]
  apply_eq_one_of_not_adj' u v huv := by
    obtain rfl : u = v := not_ne_iff.mp (mt (adj_complete u v).mpr huv)
    simp

private theorem graphCochain_apply {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (τ : Perm (Fin n)) (hτ : τ.IsSwap) (u v : V) :
    graphCochain G τ hτ u v = if G.Adj u v then τ else 1 := rfl

private theorem defect_graphCochain {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (τ : Perm (Fin n)) (hτ : τ.IsSwap) :
    (graphCochain G τ hτ).defect (movedNorm (Fin n)) = 2 * (#G.oddTriangleFinset : ℝ) := by
  have hsq : τ * τ = 1 := by obtain ⟨a, b, _, rfl⟩ := hτ; simp
  have heq : G.oddTriangleFinset = G.oddTripleFinset := by
    ext t; simp [SimpleGraph.filter_edgeFinset_toFinset_subset]
  rw [Cochain.defect_eq_sum_triangles isConjInvariant_movedNorm]
  have hterm (t : Finset V) (ht : t ∈ (complete V).triangles) :
      (graphCochain G τ hτ).triangleDefect (movedNorm (Fin n)) t =
        if t ∈ G.oddTriangleFinset then (2 : ℝ) else 0 := by
    obtain ⟨a, b, c, _, _, _, rfl⟩ := card_eq_three.mp ((mem_triangles_complete t).mp ht)
    rw [(graphCochain G τ hτ).triangleDefect_triple isConjInvariant_movedNorm ht,
      Cochain.holonomy_def, graphCochain_apply, graphCochain_apply, graphCochain_apply]
    simp only [heq, SimpleGraph.triple_mem_oddTripleFinset_iff]
    by_cases h₁ : G.Adj a b <;> by_cases h₂ : G.Adj a c <;> by_cases h₃ : G.Adj b c <;>
      simp [h₁, h₂, h₃, G.adj_comm c a, hsq, hτ.movedNorm, xor_def]
  rw [sum_congr rfl hterm, sum_ite_mem]
  have hsub : G.oddTriangleFinset ⊆ (complete V).triangles := fun t ht =>
    (mem_triangles_complete t).mpr (SimpleGraph.mem_oddTriangleFinset.mp ht).1
  rw [inter_eq_right.mpr hsub, sum_const, nsmul_eq_mul, mul_comm]

private theorem cost_graphCochain_cut {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (τ : Perm (Fin n)) (hτ : τ.IsSwap)
    (S : Set V) [DecidablePred (· ∈ S)] :
    (graphCochain G τ hτ).cost (movedNorm (Fin n)) (fun v => if v ∈ S then τ else 1) =
      2 * (#(G.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset) : ℝ) := by
  have hsq : τ * τ = 1 := by obtain ⟨a, b, _, rfl⟩ := hτ; simp
  have hinv : τ⁻¹ = τ := by obtain ⟨a, b, _, rfl⟩ := hτ; simp
  set F : Finset (Sym2 V) := G.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset
  have hto_inj : Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := fun s₁ s₂ h => by
    induction s₁ using Sym2.ind with
    | _ x₁ y₁ => induction s₂ using Sym2.ind with
      | _ x₂ y₂ =>
        simp only [Sym2.toFinset_mk_eq, ← coe_inj, coe_pair, Set.pair_eq_pair_iff] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
  have hsub : F.image Sym2.toFinset ⊆ (complete V).edges := by
    intro e he
    obtain ⟨s, hs, rfl⟩ := mem_image.mp he
    refine (mem_edges_complete _).mpr (Sym2.card_toFinset_of_not_isDiag s ?_)
    rcases mem_symmDiff.mp hs with ⟨h, _⟩ | ⟨h, _⟩
    · exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp h)
    · exact ((⊤ : SimpleGraph V).between S Sᶜ).not_isDiag_of_mem_edgeSet
        (SimpleGraph.mem_edgeFinset.mp h)
  rw [Cochain.cost_eq_sum_edges]
  have hterm (e : Finset V) (he : e ∈ (complete V).edges) :
      (graphCochain G τ hτ).edgeCost (movedNorm (Fin n)) (fun v => if v ∈ S then τ else 1) e =
        if e ∈ F.image Sym2.toFinset then (2 : ℝ) else 0 := by
    obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp ((mem_edges_complete e).mp he)
    rw [(graphCochain G τ hτ).edgeCost_pair _ _ he, graphCochain_apply]
    have hmem : ({u, v} : Finset V) ∈ F.image Sym2.toFinset ↔ s(u, v) ∈ F := by
      rw [← Sym2.toFinset_mk_eq, mem_image]
      exact ⟨fun ⟨s, hs, h⟩ => hto_inj h ▸ hs, fun h => ⟨s(u, v), h, rfl⟩⟩
    simp only [hmem]
    by_cases hG : G.Adj u v <;> by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
      simp [F, hG, hu, hv, huv, mem_symmDiff, SimpleGraph.between_adj, hinv, hsq, hτ.movedNorm]
  rw [sum_congr rfl hterm, sum_ite_mem, inter_eq_right.mpr hsub, sum_const, nsmul_eq_mul,
    card_image_of_injective F hto_inj, mul_comm]

private theorem gaugeDist_graphCochain_of_isCutMinimal {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcut : G.IsCutMinimal)
    {n : ℕ} (τ : Perm (Fin n)) (hτ : τ.IsSwap) :
    (graphCochain G τ hτ).gaugeDist (movedNorm (Fin n)) = 2 * (#G.edgeFinset : ℝ) := by
  let α := graphCochain G τ hτ
  have hmap : α.map (parityRetract hτ) = α := by
    refine Cochain.ext fun u v _ => ?_
    rw [Cochain.map_apply, graphCochain_apply]
    by_cases h : G.Adj u v <;> simp [h, parityRetract_self hτ]
  refine le_antisymm ?_ ?_
  · have h1 := α.gaugeDist_le_cost (movedNorm (Fin n)) (fun v => if v ∈ (∅ : Set V) then τ else 1)
    have hcost := cost_graphCochain_cut G τ hτ (∅ : Set V)
    have hbot : ((⊤ : SimpleGraph V).between (∅ : Set V) (∅ : Set V)ᶜ).edgeFinset = ∅ := by
      ext e
      induction e using Sym2.ind with
      | _ u v => simp [SimpleGraph.between_adj]
    rw [hbot] at hcost
    simp only [← bot_eq_empty, symmDiff_bot] at hcost
    exact h1.trans_eq hcost
  · rw [α.le_gaugeDist_iff]
    intro β
    have hret : α.cost (movedNorm (Fin n)) (parityRetract hτ ∘ β) ≤
        α.cost (movedNorm (Fin n)) β := by
      simpa [hmap] using α.cost_map_le (movedNorm_parityRetract_le hτ) β
    classical
    let S : Set V := {v : V | sign (β v) ≠ 1}
    have hfun : (parityRetract hτ ∘ β) = fun v => if v ∈ S then τ else 1 := by
      ext v
      simp only [Function.comp_apply, parityRetract_apply, S, Set.mem_ofPred_eq]
      by_cases h : sign (β v) = 1 <;> simp [h]
    have hcost : α.cost (movedNorm (Fin n)) (parityRetract hτ ∘ β) =
        2 * (#(G.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset) : ℝ) := by
      rw [hfun]
      exact cost_graphCochain_cut G τ hτ S
    have hle : (#G.edgeFinset : ℝ) ≤
        (#(G.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset) : ℝ) := by
      exact_mod_cast (SimpleGraph.isCutMinimal_iff_card_le_card_symmDiff G).mp hcut S
    linarith

/-- Every nonempty finite cut-minimal simple graph `G` on `V` bounds `h1Err (complete V)` by its
odd-triangle-to-edge ratio `#G.oddTriangleFinset / #G.edgeFinset`, with no density hypothesis. -/
theorem h1Err_complete_le_of_isCutMinimal {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcut : G.IsCutMinimal)
    (hpos : 0 < #G.edgeFinset) :
    h1Err (complete V) ≤ (#G.oddTriangleFinset : ℝ) / #G.edgeFinset := by
  -- Embed `G` via a single transposition in degree `n := 2 * #G.edgeFinset`, where
  -- `gaugeDist / n = 1 ≤ #(complete V).edges / (n + 1)` by strict half-density.
  have h2V : 2 ≤ Fintype.card V := by
    obtain ⟨e, he⟩ := card_pos.mp hpos
    induction e using Sym2.ind with
    | _ u v =>
      exact Fintype.one_lt_card_iff.mpr ⟨u, v, G.ne_of_adj (SimpleGraph.mem_edgeFinset.mp he)⟩
  have hdense : 2 * #G.edgeFinset < (Fintype.card V).choose 2 :=
    hcut.two_mul_card_edgeFinset_lt_choose_two h2V
  let n : ℕ := 2 * #G.edgeFinset
  have hn : 2 ≤ n := by omega
  let τ : Perm (Fin n) := Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩
  have hτ : τ.IsSwap := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], rfl⟩
  let α := graphCochain G τ hτ
  have hdef : α.defect (movedNorm (Fin n)) = 2 * (#G.oddTriangleFinset : ℝ) :=
    defect_graphCochain G τ hτ
  have hgd : α.gaugeDist (movedNorm (Fin n)) = (n : ℝ) := by
    simpa [n] using gaugeDist_graphCochain_of_isCutMinimal G hcut τ hτ
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hgde_le : α.gaugeDist (movedNorm (Fin n)) / n ≤
      (#(complete V).edges : ℝ) / ((n : ℝ) + 1) := by
    rw [hgd, div_self hn_pos.ne', one_le_div (by positivity), card_edges_complete]
    exact_mod_cast Nat.succ_le_of_lt hdense
  have hgde : α.gaugeDistErr = 1 := by
    rw [α.gaugeDistErr_eq_gaugeDist_div_of_le hn hgde_le, hgd, div_self hn_pos.ne']
  have hle := h1Err_le_div_of_le hn (α := α) (by rw [hgde]; norm_num)
  refine hle.trans_eq ?_
  rw [hdef, hgde, div_one]
  have hE_ne : (#G.edgeFinset : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnc : (n : ℝ) = 2 * (#G.edgeFinset : ℝ) := by simp [n]
  rw [hnc]
  field_simp [hE_ne]

/-- On any complete complex whose vertex count has the form `c * (2 * t + 1)` with `1 ≤ t`, the
cross-degree Cheeger constant equals `card V / 3` (including `c = 0`, where both sides are `0`). -/
theorem h1Err_complete_of_mul_odd {V : Type*} [Fintype V] [LinearOrder V] {c t : ℕ}
    (ht : 1 ≤ t) (hcard : Fintype.card V = c * (2 * t + 1)) :
    h1Err (complete V) = (Fintype.card V : ℝ) / 3 := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp only [zero_mul] at hcard
    rw [h1Err_eq_zero_of_card_le_two (complete V) (by omega), hcard, Nat.cast_zero, zero_div]
  · have hc1 : 1 ≤ c := Nat.pos_of_ne_zero hc0
    refine le_antisymm ?_ (card_div_three_le_h1Err (by nlinarith))
    let W := Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c
    let lW : LinearOrder W :=
      LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
    have hcardW : Fintype.card V = Fintype.card W := by
      rw [hcard]
      simp only [W, Fintype.card_sum, Fintype.card_fin]
      ring
    rw [h1Err_complete_eq_of_card_eq hcardW]
    have hpos : 0 < #(SimpleGraph.staircase c t).edgeFinset := by
      have h2 := SimpleGraph.two_mul_card_edgeFinset_staircase c t
      have : 0 < c ^ 2 * t * (t + 1) := by positivity
      omega
    have hle := @h1Err_complete_le_of_isCutMinimal W _ lW (SimpleGraph.staircase c t) _
      (SimpleGraph.isCutMinimal_staircase c t) hpos
    refine hle.trans_eq ?_
    have hodd :
        (#(@SimpleGraph.oddTriangleFinset W _ lW.toDecidableEq
            (SimpleGraph.staircase c t) _) : ℝ) =
          (c * (2 * t + 1) : ℝ) / 3 * #(SimpleGraph.staircase c t).edgeFinset := by
      convert SimpleGraph.card_oddTriangleFinset_staircase c t
    rw [hodd, hcard]
    have hE_ne : (#(SimpleGraph.staircase c t).edgeFinset : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hpos.ne'
    push_cast
    field_simp [hE_ne]

end CutMinimal

/-! ### Headline theorems for `complete V` -/

/-- **Cross-degree Cheeger constant of the complete two-complex**: for every finite vertex type
with `3 ≤ Fintype.card V`, `h1Err (complete V) = card V / 3` (for `card V ≤ 2`, see
`h1Err_eq_zero_of_card_le_two`). -/
theorem h1Err_complete {V : Type*} [Fintype V] [LinearOrder V] (hV : 3 ≤ Fintype.card V) :
    h1Err (complete V) = (Fintype.card V : ℝ) / 3 := by
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (by omega : 2 < Fintype.card V) with
    h4 | ⟨p, hp, hdvd, hodd⟩
  · exact h1Err_complete_of_four_dvd h4
  · obtain ⟨t, rfl⟩ := hodd
    have ht : 1 ≤ t := by
      have h2 := hp.two_le
      omega
    obtain ⟨c, hc⟩ := hdvd
    exact h1Err_complete_of_mul_odd ht (by rw [hc, mul_comm])

/-- Normalized form of `h1Err_complete`: multiplying `h1Err (complete V)` by `#edges / #triangles`
yields `card V / (card V - 2)` for `3 ≤ Fintype.card V`. -/
theorem card_edges_div_card_triangles_mul_h1Err_complete {V : Type*} [Fintype V] [LinearOrder V]
    (hV : 3 ≤ Fintype.card V) :
    ((complete V).edges.card / (complete V).triangles.card : ℝ) * h1Err (complete V) =
      (Fintype.card V : ℝ) / (Fintype.card V - 2) := by
  rw [card_edges_div_card_triangles_complete hV, h1Err_complete hV]
  ring

/-- **Same-degree permutation Cheeger constant of the complete two-complex**: for every finite
vertex type with `3 ≤ Fintype.card V`, `h1Sym (complete V) = card V / 3` (for `card V ≤ 2`, see
`h1Sym_eq_zero_of_card_le_two`). -/
theorem h1Sym_complete {V : Type*} [Fintype V] [LinearOrder V] (hV : 3 ≤ Fintype.card V) :
    h1Sym (complete V) = (Fintype.card V : ℝ) / 3 :=
  le_antisymm ((h1Sym_le_h1Err (complete V)).trans_eq (h1Err_complete hV))
    (card_div_three_le_h1Sym hV)

/-- On every finite complete two-complex, the same-degree and cross-degree permutation Cheeger
constants agree: `h1Sym (complete V) = h1Err (complete V)`. -/
theorem h1Sym_complete_eq_h1Err_complete {V : Type*} [Fintype V] [LinearOrder V] :
    h1Sym (complete V) = h1Err (complete V) := by
  by_cases hV : 3 ≤ Fintype.card V
  · rw [h1Sym_complete hV, h1Err_complete hV]
  · rw [h1Sym_eq_zero_of_card_le_two (complete V) (by omega),
      h1Err_eq_zero_of_card_le_two (complete V) (by omega)]

end TauCeti

end
