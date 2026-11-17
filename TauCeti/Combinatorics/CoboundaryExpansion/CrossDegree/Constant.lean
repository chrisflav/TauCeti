/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Replication
public import TauCeti.GroupTheory.Perm.DistErr.Invariance
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Basic
import TauCeti.Combinatorics.CoboundaryExpansion.StarBound

/-!
# The cross-degree coboundary cost, gauge distance, and Cheeger constant

In the cross-degree convention of Chapman and Lubotzky, a permutation-valued 1-cochain `α` of
degree `n` on a finite two-complex `X` may be approximated by a vertex gauge `β` of a possibly
different degree `m`, measuring each edge `(u, v)` by the distance with errors
`Equiv.Perm.distErr (α u v) (β u * (β v)⁻¹)`.

This file defines the cochain-level cross-degree invariants and proves their basic properties,
invariances, replication bounds, and relation to the same-degree permutation constant:

* `TauCeti.Cochain.edgeCostErr`: the orientation-independent edge contribution of a cross-degree
  gauge `β` on an unoriented edge `e ∈ X.edges`, equal to `0` off `X.edges`.
* `TauCeti.Cochain.costErr`: the cross-degree cost of `β` against `α`, summed over edges `u < v`.
  In equal degree `m = n`, `(n : ℝ) * α.costErr β = α.cost (movedNorm (Fin n)) β` for every `n`,
  and for `n ≤ m` a degree-`n` gauge transformation on `α` is absorbed into `β` via `Fin.castLEEmb`.
* `TauCeti.Cochain.gaugeDistErr`: the infimum of `α.costErr β` over all gauge degrees `m + 2 ≥ 2`
  and all gauges `β : V → Equiv.Perm (Fin (m + 2))`. For every `n : ℕ`, this infimum is attained
  by some finite-degree gauge (`Cochain.exists_costErr_eq_gaugeDistErr`). For `2 ≤ n`, it is
  bounded above by `α.gaugeDist (movedNorm (Fin n)) / n`, bounded below by
  `min (α.gaugeDist (movedNorm (Fin n)) / n) (#X.edges / (n + 1))`, and vanishes precisely on
  coboundaries (`Cochain.gaugeDistErr_eq_zero_iff_isCoboundary`). Under balanced replication
  `α.replicate ι` on `complete V`, `gaugeDistErr` multiplies by at least `(Fintype.card ι) ^ 2`,
  with equality whenever `α` attains its cross-degree infimum in its own degree.
* `TauCeti.h1Err`: the cross-degree Cheeger constant, defined as the infimum of
  `(α.defect (movedNorm (Fin (n + 2))) / (n + 2)) / α.gaugeDistErr` over degrees `n + 2 ≥ 2` and
  cochains with `0 < α.gaugeDistErr`. When `Fintype.card V ≤ 2`, `h1Err X = 0` for every
  `X : TwoComplex V` (`TauCeti.h1Err_eq_zero_of_card_le_two`).
* **Comparison and star bound**: `TauCeti.h1Sym_le_h1Err` shows `h1Sym X ≤ h1Err X` unconditionally
  for every two-complex `X`, because allowing cross-degree gauges can only decrease the denominator.
  Consequently, on `complete V`, `(Fintype.card V : ℝ) / 3 ≤ h1Err (complete V)` holds for
  `3 ≤ Fintype.card V` (`TauCeti.card_div_three_le_h1Err`).

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles I: equivalence*,
  arXiv:2310.17474v2, Eur. J. Math. 11 (2025), art. 13, §5.1.
* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117, equations
  (2.8)–(2.9) and Proposition 3.2.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4:
  Including the Powers of Two, with Four Hamming-Native Readings That Do Not Obstruct*, Zenodo,
  doi:10.5281/zenodo.23245792, version 7, Lemma 6 and Proposition 10.
-/

public section

open Finset Equiv Equiv.Perm

namespace TauCeti

open TwoComplex

namespace Cochain

/-! ### Unoriented edge cost with errors -/

section Unoriented

variable {V W : Type*} {X : TwoComplex V} {n m : ℕ}

/-- The cross-degree cost contribution of an unoriented edge `e`, or `0` if `e ∉ X.edges`. -/
noncomputable def edgeCostErr (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m))
    (e : Finset V) : ℝ := by
  classical
  exact if he : e ∈ X.edges then
    distErr (α (X.exists_vertices_of_mem_edges he).choose
        (X.exists_vertices_of_mem_edges he).choose_spec.choose)
      (β (X.exists_vertices_of_mem_edges he).choose *
        (β (X.exists_vertices_of_mem_edges he).choose_spec.choose)⁻¹)
  else 0

/-- Evaluating `edgeCostErr` on any edge `e ∈ X.edges` via its two distinct endpoints. -/
theorem edgeCostErr_of_mem_edges (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m))
    {e : Finset V} (he : e ∈ X.edges) {u v : V} (huv : u ≠ v) (hu : u ∈ e) (hv : v ∈ e) :
    α.edgeCostErr β e = distErr (α u v) (β u * (β v)⁻¹) := by
  classical
  simp only [edgeCostErr, he, ↓reduceDIte]
  obtain ⟨hu'v', hu', hv'⟩ := (X.exists_vertices_of_mem_edges he).choose_spec.choose_spec
  have he₁ :
      ({(X.exists_vertices_of_mem_edges he).choose,
        (X.exists_vertices_of_mem_edges he).choose_spec.choose} : Finset V) = e :=
    eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hu', singleton_subset_iff.mpr hv'⟩)
      (by rw [X.edge_card e he, card_pair hu'v'])
  have he₂ : ({u, v} : Finset V) = e :=
    eq_of_subset_of_card_le (by simp [insert_subset_iff, hu, hv])
      (by rw [X.edge_card e he, card_pair huv])
  have hpair := he₁.trans he₂.symm
  rw [← coe_inj, coe_pair, coe_pair, Set.pair_eq_pair_iff] at hpair
  rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₂, h₁]
  · rw [h₂, h₁, α.apply_swap u v, distErr_inv_mul_inv]

/-- Evaluating `edgeCostErr` directly on a pair `{u, v} ∈ X.edges`. -/
@[simp, grind =]
theorem edgeCostErr_pair [DecidableEq V] (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m))
    {u v : V} (he : ({u, v} : Finset V) ∈ X.edges) :
    α.edgeCostErr β {u, v} = distErr (α u v) (β u * (β v)⁻¹) :=
  α.edgeCostErr_of_mem_edges β he ((X.adj_iff_pair_mem_edges u v).mpr he).ne (by simp) (by simp)

@[simp]
theorem edgeCostErr_of_notMem_edges (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m))
    {e : Finset V} (he : e ∉ X.edges) : α.edgeCostErr β e = 0 := by
  classical simp [edgeCostErr, he]

theorem edgeCostErr_nonneg (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m))
    (e : Finset V) : 0 ≤ α.edgeCostErr β e := by
  classical
  by_cases he : e ∈ X.edges <;> simp [edgeCostErr, he, distErr_nonneg]

theorem edgeCostErr_le_one (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m))
    (e : Finset V) : α.edgeCostErr β e ≤ 1 := by
  classical
  by_cases he : e ∈ X.edges <;> simp [edgeCostErr, he, distErr_le_one]

/-- In equal degree `n`, rescaling `edgeCostErr` by `n` recovers `edgeCost` for `movedNorm`,
including `n = 0`. -/
theorem mul_edgeCostErr_eq_edgeCost (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n))
    (e : Finset V) :
    (n : ℝ) * α.edgeCostErr β e = α.edgeCost (movedNorm (Fin n)) β e := by
  by_cases he : e ∈ X.edges
  · obtain ⟨u, v, huv, hu, hv⟩ := X.exists_vertices_of_mem_edges he
    rw [α.edgeCostErr_of_mem_edges β he huv hu hv,
      α.edgeCost_of_mem_edges (movedNorm (Fin n)) β he huv hu hv]
    exact mul_distErr_mul_inv_eq_movedNorm (α u v) (β u) (β v)
  · simp [he]

/-- When `n ≤ m`, a degree-`n` gauge action on `α` is absorbed into a degree-`m` gauge via
`Fin.castLEEmb` on each edge. -/
theorem edgeCostErr_smul_of_le (α : Cochain X (Perm (Fin n))) (γ : V → Perm (Fin n))
    (β : V → Perm (Fin m)) (hnm : n ≤ m) (e : Finset V) :
    (γ • α).edgeCostErr β e =
      α.edgeCostErr (fun v => (γ v).viaEmbedding (Fin.castLEEmb hnm) * β v) e := by
  by_cases he : e ∈ X.edges
  · obtain ⟨u, v, huv, hu, hv⟩ := X.exists_vertices_of_mem_edges he
    rw [(γ • α).edgeCostErr_of_mem_edges β he huv hu hv,
      α.edgeCostErr_of_mem_edges _ he huv hu hv,
      smul_apply_of_adj γ α (X.adj_of_mem_edges he hu hv huv)]
    exact distErr_inv_mul_mul_mul_inv (α u v) (γ u) (γ v) (β u) (β v) hnm
  · simp [he]

@[simp]
theorem edgeCostErr_relabel (α : Cochain X (Perm (Fin n))) (γ : W → Perm (Fin m)) (e : V ≃ W)
    (s : Finset W) :
    (α.relabel e).edgeCostErr γ s = α.edgeCostErr (γ ∘ e) (s.map e.symm.toEmbedding) := by
  by_cases hs : s ∈ (X.relabel e).edges
  · obtain ⟨u, v, huv, hu, hv⟩ := (X.relabel e).exists_vertices_of_mem_edges hs
    rw [(α.relabel e).edgeCostErr_of_mem_edges γ hs huv hu hv,
      α.edgeCostErr_of_mem_edges (γ ∘ e) ((X.mem_edges_relabel e s).mp hs)
        (e.symm.injective.ne huv) (mem_map_of_mem _ hu) (mem_map_of_mem _ hv)]
    simp
  · rw [edgeCostErr_of_notMem_edges _ _ hs,
      edgeCostErr_of_notMem_edges _ _ (mt (X.mem_edges_relabel e s).mpr hs)]

@[simp 1100]
theorem edgeCostErr_relabel_map (α : Cochain X (Perm (Fin n))) (γ : W → Perm (Fin m)) (e : V ≃ W)
    (s : Finset V) :
    (α.relabel e).edgeCostErr γ (s.map e.toEmbedding) = α.edgeCostErr (γ ∘ e) s := by
  rw [α.edgeCostErr_relabel γ e]
  congr 1; ext; simp

end Unoriented

/-! ### Cross-degree gauge cost `costErr` -/

section CostErr

variable {V W : Type*} {X : TwoComplex V} {n m : ℕ}

/-- The cross-degree cost of a degree-`m` gauge `β` against a degree-`n` cochain `α`: the sum of
`distErr (α u v) (β u * (β v)⁻¹)` over all edges `u < v`. -/
noncomputable def costErr [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) : ℝ :=
  ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
    distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹)

theorem costErr_def [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) :
    α.costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) := (rfl)

/-- On the complete complex, `costErr` sums over all strictly increasing vertex pairs `u < v`. -/
theorem costErr_complete [Fintype V] [LinearOrder V] (α : Cochain (complete V) (Perm (Fin n)))
    (β : V → Perm (Fin m)) :
    α.costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2),
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) := by
  rw [costErr_def]
  refine sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_edges_complete, card_pair_eq_two_iff,
    and_iff_left_iff_imp]
  exact LT.lt.ne

/-- `costErr` equals the sum of `edgeCostErr` over the unoriented edges `X.edges`. -/
theorem costErr_eq_sum_edges [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) :
    α.costErr β = ∑ e ∈ X.edges, α.edgeCostErr β e := by
  rw [costErr_def]
  refine sum_bij (fun p _ => ({p.1, p.2} : Finset V)) (fun p hp => (mem_filter.mp hp).2.2) ?_ ?_
    (fun p hp => (α.edgeCostErr_pair β (mem_filter.mp hp).2.2).symm)
  · rintro ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ hpair
    have hlt₁ : u₁ < v₁ := (mem_filter.mp hp₁).2.1
    have hlt₂ : u₂ < v₂ := (mem_filter.mp hp₂).2.1
    rw [← coe_inj, coe_pair, coe_pair, Set.pair_eq_pair_iff] at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (lt_asymm hlt₁ hlt₂).elim
  · intro e he
    obtain ⟨u, v, hlt, hset⟩ := X.exists_increasing_of_mem_edges he
    exact ⟨(u, v), mem_filter.mpr ⟨mem_univ _, hlt, hset ▸ he⟩, hset⟩

theorem costErr_nonneg [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) : 0 ≤ α.costErr β :=
  sum_nonneg fun _ _ => distErr_nonneg _ _

theorem costErr_le_card_edges [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) : α.costErr β ≤ (#X.edges : ℝ) := by
  rw [costErr_eq_sum_edges]
  exact (sum_le_sum fun e _ => α.edgeCostErr_le_one β e).trans_eq (by simp)

/-- In equal degree `n`, rescaling `costErr` by `n` recovers `cost` for `movedNorm (Fin n)`,
including `n = 0`. -/
theorem mul_costErr_eq_cost [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin n)) :
    (n : ℝ) * α.costErr β = α.cost (movedNorm (Fin n)) β := by
  rw [costErr_eq_sum_edges, cost_eq_sum_edges, mul_sum]
  exact sum_congr rfl fun e _ => α.mul_edgeCostErr_eq_edgeCost β e

/-- In equal nonzero degree `n`, `costErr` is `cost` divided by `n`. -/
theorem costErr_eq_cost_div [Fintype V] [LinearOrder V] [NeZero n]
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    α.costErr β = α.cost (movedNorm (Fin n)) β / n := by
  rw [← α.mul_costErr_eq_cost β, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne n))]

/-- Evaluating `costErr` on the trivial cochain and trivial gauge yields `#X.edges` times the
degree-mismatch baseline `1 - min n m / max n m`. -/
theorem costErr_one_one [Fintype V] [LinearOrder V] :
    (1 : Cochain X (Perm (Fin n))).costErr (1 : V → Perm (Fin m)) =
      (#X.edges : ℝ) * (1 - (min n m : ℝ) / max n m) := by
  rw [costErr_eq_sum_edges]
  have hterm : ∀ e ∈ X.edges,
      (1 : Cochain X (Perm (Fin n))).edgeCostErr (1 : V → Perm (Fin m)) e =
        1 - (min n m : ℝ) / max n m := by
    intro e he
    obtain ⟨u, v, huv, hu, hv⟩ := X.exists_vertices_of_mem_edges he
    rw [edgeCostErr_of_mem_edges _ _ he huv hu hv]
    simp
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]

@[simp]
theorem costErr_one_one_self [Fintype V] [LinearOrder V] [NeZero n] :
    (1 : Cochain X (Perm (Fin n))).costErr (1 : V → Perm (Fin n)) = 0 := by
  rw [costErr_eq_cost_div, cost_one_one, zero_div]

/-- Every cross-degree gauge cost is at least `#X.edges * (1 - min n m / max n m)`. -/
theorem card_edges_mul_one_sub_min_div_max_le_costErr [Fintype V] [LinearOrder V]
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    (#X.edges : ℝ) * (1 - (min n m : ℝ) / max n m) ≤ α.costErr β := by
  rw [costErr_eq_sum_edges]
  calc (#X.edges : ℝ) * (1 - (min n m : ℝ) / max n m)
      = ∑ _e ∈ X.edges, (1 - (min n m : ℝ) / max n m) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ e ∈ X.edges, α.edgeCostErr β e := by
        refine sum_le_sum fun e he => ?_
        obtain ⟨u, v, huv, hu, hv⟩ := X.exists_vertices_of_mem_edges he
        rw [α.edgeCostErr_of_mem_edges β he huv hu hv]
        exact one_sub_min_div_max_le_distErr _ _

/-- For unequal degrees `n ≠ m`, every cross-degree gauge cost is at least `#X.edges / (n + 1)`. -/
theorem card_edges_div_add_one_le_costErr_of_ne [Fintype V] [LinearOrder V]
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) (hnm : n ≠ m) :
    (#X.edges : ℝ) / ((n : ℝ) + 1) ≤ α.costErr β := by
  rw [costErr_eq_sum_edges]
  calc (#X.edges : ℝ) / ((n : ℝ) + 1)
      = ∑ _e ∈ X.edges, (1 / ((n : ℝ) + 1)) := by simp [div_eq_mul_inv]
    _ ≤ ∑ e ∈ X.edges, α.edgeCostErr β e := by
        refine sum_le_sum fun e he => ?_
        obtain ⟨u, v, huv, hu, hv⟩ := X.exists_vertices_of_mem_edges he
        rw [α.edgeCostErr_of_mem_edges β he huv hu hv]
        exact one_div_add_one_le_distErr_of_ne _ _ hnm

/-- When `n ≤ m`, transforming `α` by a degree-`n` gauge `γ` shifts `costErr` by left-multiplying
`β` by the initial-segment extension of `γ`. -/
theorem costErr_smul_of_le [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n)))
    (γ : V → Perm (Fin n)) (β : V → Perm (Fin m)) (hnm : n ≤ m) :
    (γ • α).costErr β =
      α.costErr (fun v => (γ v).viaEmbedding (Fin.castLEEmb hnm) * β v) := by
  rw [costErr_eq_sum_edges, costErr_eq_sum_edges]
  exact sum_congr rfl fun e _ => α.edgeCostErr_smul_of_le γ β hnm e

/-- `costErr` does not depend on the `LinearOrder` chosen on `V`. -/
theorem costErr_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V)
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    @costErr V X n m _ l₁ α β = @costErr V X n m _ l₂ α β :=
  (@costErr_eq_sum_edges V X n m _ l₁ α β).trans (@costErr_eq_sum_edges V X n m _ l₂ α β).symm

/-- Relabelling `α` along `e : V ≃ W` pulls a cross-degree gauge back along `e` in `costErr`. -/
@[simp]
theorem costErr_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (α : Cochain X (Perm (Fin n))) (γ : W → Perm (Fin m)) (e : V ≃ W) :
    (α.relabel e).costErr γ = α.costErr (γ ∘ e) := by
  rw [costErr_eq_sum_edges, costErr_eq_sum_edges, X.sum_edges_relabel e]
  exact sum_congr rfl fun s _ => α.edgeCostErr_relabel_map γ e s

private theorem congr_complex_perm {γ : Sort*}
    (F : ∀ X : TwoComplex W, Cochain X (Perm (Fin n)) → γ)
    {X₁ X₂ : TwoComplex W} (hX : X₁ = X₂)
    {α₁ : Cochain X₁ (Perm (Fin n))} {α₂ : Cochain X₂ (Perm (Fin n))}
    (hα : ∀ u v, α₁ u v = α₂ u v) : F X₁ α₁ = F X₂ α₂ := by
  subst hX; congr 1; exact Cochain.ext fun u v _ => hα u v

@[simp]
theorem costErr_relabelComplete [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (α : Cochain (complete V) (Perm (Fin n))) (γ : W → Perm (Fin m)) (e : V ≃ W) :
    (α.relabelComplete e).costErr γ = α.costErr (γ ∘ e) :=
  (congr_complex_perm (fun _ δ => δ.costErr γ) (relabel_complete e).symm
    fun _ _ => by simp).trans (α.costErr_relabel γ e)

/-- In equal nonzero degree `n`, `costErr` vanishes if and only if the gauge trivializes `α`. -/
theorem costErr_eq_zero_iff [Fintype V] [LinearOrder V] [NeZero n]
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    α.costErr β = 0 ↔ β • α = 1 := by
  rw [costErr_eq_cost_div, div_eq_zero_iff, Nat.cast_eq_zero, or_iff_left (NeZero.ne n),
    cost_eq_zero_iff]

/-- Whenever `X` has at least one edge and `n ≠ 0`, some degree-`n` gauge makes at least one edge
agree identically, achieving `costErr ≤ #X.edges - 1`. -/
theorem exists_costErr_le_card_edges_sub_one [Fintype V] [LinearOrder V] [NeZero n]
    (α : Cochain X (Perm (Fin n))) (he : X.edges.Nonempty) :
    ∃ β : V → Perm (Fin n), α.costErr β ≤ (#X.edges : ℝ) - 1 := by
  obtain ⟨e₀, he₀⟩ := he
  obtain ⟨u₀, v₀, huv₀, hu₀, hv₀⟩ := X.exists_vertices_of_mem_edges he₀
  let β : V → Perm (Fin n) := fun x => if x = u₀ then α u₀ v₀ else 1
  refine ⟨β, ?_⟩
  rw [costErr_eq_sum_edges, ← add_sum_erase _ _ he₀]
  have hzero : α.edgeCostErr β e₀ = 0 := by
    rw [α.edgeCostErr_of_mem_edges β he₀ huv₀ hu₀ hv₀]
    simp [β, huv₀.symm]
  have hrest : ∑ e ∈ X.edges.erase e₀, α.edgeCostErr β e ≤ (#(X.edges.erase e₀) : ℝ) :=
    (sum_le_sum fun e _ => α.edgeCostErr_le_one β e).trans_eq (by simp)
  have hcard : (#(X.edges.erase e₀) : ℝ) = (#X.edges : ℝ) - 1 := by
    rw [card_erase_of_mem he₀, Nat.cast_sub (Finset.one_le_card.mpr ⟨e₀, he₀⟩), Nat.cast_one]
  linarith

end CostErr

/-! ### Cross-degree gauge distance `gaugeDistErr` -/

section GaugeDistErr

variable {V W : Type*} {X : TwoComplex V} {n m : ℕ}

/-- The cross-degree gauge distance of `α`: the infimum of `α.costErr β` over all gauge degrees
`m + 2 ≥ 2` and all gauges `β : V → Perm (Fin (m + 2))`. -/
noncomputable def gaugeDistErr [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n))) : ℝ :=
  ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β

theorem gaugeDistErr_def [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n))) :
    α.gaugeDistErr = ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β := (rfl)

theorem bddBelow_range_costErr [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n))) :
    BddBelow (Set.range (α.costErr (m := m))) :=
  ⟨0, by rintro _ ⟨β, rfl⟩; exact α.costErr_nonneg β⟩

theorem bddBelow_range_iInf_costErr [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n))) :
    BddBelow (Set.range fun m : ℕ => ⨅ β : V → Perm (Fin (m + 2)), α.costErr β) :=
  ⟨0, by rintro _ ⟨m, rfl⟩; exact Real.iInf_nonneg fun β => α.costErr_nonneg β⟩

theorem gaugeDistErr_nonneg [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n))) :
    0 ≤ α.gaugeDistErr :=
  Real.iInf_nonneg fun _ => Real.iInf_nonneg fun _ => α.costErr_nonneg _

/-- Every gauge of degree `m + 2 ≥ 2` bounds `gaugeDistErr` from above. -/
theorem gaugeDistErr_le_costErr [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin (m + 2))) : α.gaugeDistErr ≤ α.costErr β :=
  (ciInf_le α.bddBelow_range_iInf_costErr m).trans (ciInf_le α.bddBelow_range_costErr β)

theorem gaugeDistErr_le_card_edges [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n))) :
    α.gaugeDistErr ≤ (#X.edges : ℝ) :=
  (α.gaugeDistErr_le_costErr (1 : V → Perm (Fin 2))).trans (α.costErr_le_card_edges _)

/-- Every gauge of degree `m ≥ 2` bounds `gaugeDistErr` from above. -/
theorem gaugeDistErr_le_costErr_of_le [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n)))
    (hm : 2 ≤ m) (β : V → Perm (Fin m)) : α.gaugeDistErr ≤ α.costErr β := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact α.gaugeDistErr_le_costErr β

/-- Every degree-`m + 2` infimum bounds `gaugeDistErr` from above. -/
theorem gaugeDistErr_le_iInf_costErr [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n)))
    (m : ℕ) : α.gaugeDistErr ≤ ⨅ β : V → Perm (Fin (m + 2)), α.costErr β :=
  ciInf_le α.bddBelow_range_iInf_costErr m

theorem le_gaugeDistErr_iff [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n))) {c : ℝ} :
    c ≤ α.gaugeDistErr ↔ ∀ (m : ℕ) (β : V → Perm (Fin (m + 2))), c ≤ α.costErr β := by
  rw [gaugeDistErr_def, le_ciInf_iff α.bddBelow_range_iInf_costErr]
  exact forall_congr' fun m => le_ciInf_iff α.bddBelow_range_costErr

theorem gaugeDistErr_lt_iff [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin n))) {c : ℝ} :
    α.gaugeDistErr < c ↔ ∃ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β < c := by
  rw [gaugeDistErr_def, ciInf_lt_iff α.bddBelow_range_iInf_costErr]
  exact exists_congr fun m => ciInf_lt_iff α.bddBelow_range_costErr

/-- For `n ≠ 0`, the degree-`n` cross-degree cost infimum equals the normalized same-degree gauge
distance `α.gaugeDist (movedNorm (Fin n)) / n`. -/
theorem iInf_costErr_eq_gaugeDist_div [Fintype V] [LinearOrder V] [NeZero n]
    (α : Cochain X (Perm (Fin n))) :
    (⨅ β : V → Perm (Fin n), α.costErr β) = α.gaugeDist (movedNorm (Fin n)) / n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  rw [gaugeDist_def, div_eq_mul_inv, mul_comm, Real.mul_iInf_of_nonneg (inv_nonneg.mpr hn.le)]
  refine iInf_congr fun β => ?_
  rw [α.costErr_eq_cost_div β, div_eq_mul_inv, mul_comm]

/-- Allowing cross-degree gauges can only decrease the normalized gauge distance when `2 ≤ n`. -/
theorem gaugeDistErr_le_gaugeDist_div [Fintype V] [LinearOrder V]
    (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n) :
    α.gaugeDistErr ≤ α.gaugeDist (movedNorm (Fin n)) / n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [← α.iInf_costErr_eq_gaugeDist_div]
  exact α.gaugeDistErr_le_iInf_costErr k

/-- Universal lower bound on `gaugeDistErr` valid for every degree `n : ℕ`: either the gauge has
equal degree `n` (costing at least `gaugeDist / n`) or a distinct degree `m + 2 ≠ n` (costing at
least `#X.edges / (n + 1)`). -/
theorem min_gaugeDist_div_card_edges_div_le_gaugeDistErr [Fintype V] [LinearOrder V]
    (α : Cochain X (Perm (Fin n))) :
    min (α.gaugeDist (movedNorm (Fin n)) / n) ((#X.edges : ℝ) / ((n : ℝ) + 1)) ≤
      α.gaugeDistErr := by
  rw [α.le_gaugeDistErr_iff]
  intro m β
  by_cases hnm : n = m + 2
  · subst hnm
    refine (min_le_left _ _).trans ?_
    rw [α.costErr_eq_cost_div β]
    exact div_le_div_of_nonneg_right (α.gaugeDist_le_cost _ β) (Nat.cast_nonneg _)
  · exact (min_le_right _ _).trans (α.card_edges_div_add_one_le_costErr_of_ne β hnm)

/-- When the normalized same-degree gauge distance does not exceed the cross-degree mismatch
baseline `#X.edges / (n + 1)`, no gauge of any other degree beats the cochain's own degree `n`. -/
theorem gaugeDistErr_eq_gaugeDist_div_of_le [Fintype V] [LinearOrder V]
    (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n)
    (hle : α.gaugeDist (movedNorm (Fin n)) / n ≤ (#X.edges : ℝ) / ((n : ℝ) + 1)) :
    α.gaugeDistErr = α.gaugeDist (movedNorm (Fin n)) / n :=
  le_antisymm (α.gaugeDistErr_le_gaugeDist_div hn)
    ((min_eq_left hle ▸ α.min_gaugeDist_div_card_edges_div_le_gaugeDistErr))

private theorem card_edges_sub_one_le_costErr_of_mul_lt [Fintype V] [LinearOrder V]
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m))
    (hne : X.edges.Nonempty) (hnm : n * #X.edges < m) :
    (#X.edges : ℝ) - 1 ≤ α.costErr β := by
  have hle : n ≤ m := (Nat.le_mul_of_pos_right n (card_pos.mpr hne)).trans hnm.le
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hnm)
  have hcast : (n : ℝ) * #X.edges < m := by exact_mod_cast hnm
  have hdiv : (#X.edges : ℝ) * n / m ≤ 1 := (div_le_one hm_pos).mpr (by linarith)
  have hbase := α.card_edges_mul_one_sub_min_div_max_le_costErr β
  rw [← Nat.cast_min, Nat.min_eq_left hle, Nat.max_eq_right hle] at hbase
  have hexp : (#X.edges : ℝ) * (1 - (n : ℝ) / m) = #X.edges - (#X.edges : ℝ) * n / m := by ring
  linarith

private theorem exists_costErr_eq_gaugeDistErr_of_two_le [Fintype V] [LinearOrder V]
    (α : Cochain X (Perm (Fin (j + 2)))) (hne : X.edges.Nonempty) :
    ∃ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β = α.gaugeDistErr := by
  -- Once `m + 2 > (j + 2) * #X.edges`, the mismatch baseline exceeds `#X.edges - 1`.
  obtain ⟨β₀, hβ₀⟩ := α.exists_costErr_le_card_edges_sub_one hne
  let f (m : ℕ) : ℝ := ⨅ β : V → Perm (Fin (m + 2)), α.costErr β
  let N : ℕ := (j + 2) * #X.edges
  have hjN : j < N + 1 := by
    have : j + 2 ≤ N := Nat.le_mul_of_pos_right (j + 2) (card_pos.mpr hne)
    omega
  obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun i : Fin (N + 1) => f i.1)
  have hfk_le_all : ∀ m : ℕ, f k.1 ≤ f m := by
    intro m
    by_cases hm : m ≤ N
    · exact hk.trans_le
        (ciInf_le (f := fun i : Fin (N + 1) => f i.1) (Set.finite_range _).bddBelow
          ⟨m, by omega⟩)
    · have hkj : f k.1 ≤ f j :=
        hk.trans_le (ciInf_le (f := fun i : Fin (N + 1) => f i.1) (Set.finite_range _).bddBelow
          ⟨j, hjN⟩)
      have hfj : f j ≤ α.costErr β₀ := ciInf_le α.bddBelow_range_costErr β₀
      have hbase : (#X.edges : ℝ) - 1 ≤ f m :=
        le_ciInf fun β => α.card_edges_sub_one_le_costErr_of_mul_lt β hne (by omega)
      exact (hkj.trans hfj).trans (hβ₀.trans hbase)
  obtain ⟨β, hβ⟩ :=
    exists_eq_ciInf_of_finite (f := fun β : V → Perm (Fin (k.1 + 2)) => α.costErr β)
  refine ⟨k.1, β, le_antisymm ?_ (α.gaugeDistErr_le_costErr β)⟩
  rw [hβ, gaugeDistErr_def]
  exact le_ciInf hfk_le_all

/-- For every degree `n : ℕ`, the infimum defining `gaugeDistErr` is attained by some gauge of
finite degree `m + 2 ≥ 2`. -/
theorem exists_costErr_eq_gaugeDistErr [Fintype V] [LinearOrder V]
    (α : Cochain X (Perm (Fin n))) :
    ∃ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β = α.gaugeDistErr := by
  rcases X.edges.eq_empty_or_nonempty with hempty | hne
  · refine ⟨0, 1, le_antisymm ?_ (α.gaugeDistErr_le_costErr 1)⟩
    rw [α.costErr_eq_sum_edges, hempty, sum_empty]
    exact α.gaugeDistErr_nonneg
  · match n, α with
    | 0, α =>
      refine ⟨0, 1, le_antisymm ?_ (α.gaugeDistErr_le_costErr 1)⟩
      refine (α.costErr_le_card_edges 1).trans ((α.le_gaugeDistErr_iff).mpr fun m β => ?_)
      have h := α.card_edges_mul_one_sub_min_div_max_le_costErr β
      rw [← Nat.cast_min, Nat.min_eq_left (Nat.zero_le _), Nat.cast_zero, zero_div, sub_zero,
        mul_one] at h
      exact h
    | 1, α =>
      obtain rfl : α = 1 := Subsingleton.elim α 1
      refine ⟨0, 1, le_antisymm ?_ (gaugeDistErr_le_costErr _ 1)⟩
      rw [le_gaugeDistErr_iff]
      intro m β
      have h1 : (1 : Cochain X (Perm (Fin 1))).costErr (1 : V → Perm (Fin 2)) =
          (#X.edges : ℝ) * (1 - (1 : ℝ) / 2) := by
        rw [costErr_one_one]; norm_num
      have h2 : (#X.edges : ℝ) * (1 - (1 : ℝ) / 2) ≤
          (#X.edges : ℝ) * (1 - (1 : ℝ) / ((m + 2 : ℕ) : ℝ)) := by
        have hm2 : (2 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by norm_cast; omega
        gcongr
      have h3 := (1 : Cochain X (Perm (Fin 1))).card_edges_mul_one_sub_min_div_max_le_costErr β
      rw [← Nat.cast_min, Nat.min_eq_left (by omega : 1 ≤ m + 2),
        Nat.max_eq_right (by omega : 1 ≤ m + 2), Nat.cast_one] at h3
      linarith
    | _ + 2, α => exact α.exists_costErr_eq_gaugeDistErr_of_two_le hne

/-- Every coboundary of degree `n ≥ 2` has cross-degree gauge distance zero. -/
theorem IsCoboundary.gaugeDistErr_eq_zero [Fintype V] [LinearOrder V]
    {α : Cochain X (Perm (Fin n))} (hα : α.IsCoboundary) (hn : 2 ≤ n) :
    α.gaugeDistErr = 0 :=
  le_antisymm
    ((α.gaugeDistErr_le_gaugeDist_div hn).trans_eq
      (by rw [hα.gaugeDist_eq_zero (movedNorm (Fin n)), zero_div]))
    α.gaugeDistErr_nonneg

@[simp]
theorem gaugeDistErr_one [Fintype V] [LinearOrder V] :
    (1 : Cochain X (Perm (Fin (n + 2)))).gaugeDistErr = 0 :=
  (isCoboundary_one (X := X)).gaugeDistErr_eq_zero (by omega)

/-- For `2 ≤ n`, a cochain has cross-degree gauge distance zero if and only if it is a
coboundary. -/
theorem gaugeDistErr_eq_zero_iff_isCoboundary [Fintype V] [LinearOrder V]
    (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n) :
    α.gaugeDistErr = 0 ↔ α.IsCoboundary := by
  refine ⟨fun h0 => ?_, fun h => h.gaugeDistErr_eq_zero hn⟩
  by_contra hnc
  rcases X.edges.eq_empty_or_nonempty with hempty | hne
  · exact hnc (α.isCoboundary_def.mpr ⟨1, fun u v huv => by
      obtain ⟨e, he, _, _⟩ := huv.exists_mem_edges
      exact absurd he (hempty ▸ notMem_empty e)⟩)
  · have hg : 0 < α.gaugeDist (movedNorm (Fin n)) :=
      (α.gaugeDist_pos_iff_not_isCoboundary _).mpr hnc
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have he_pos : (0 : ℝ) < #X.edges := Nat.cast_pos.mpr (card_pos.mpr hne)
    have hpos : 0 < min (α.gaugeDist (movedNorm (Fin n)) / n) ((#X.edges : ℝ) / ((n : ℝ) + 1)) :=
      lt_min (div_pos hg hn_pos) (div_pos he_pos (by positivity))
    linarith [α.min_gaugeDist_div_card_edges_div_le_gaugeDistErr]

/-- For `2 ≤ n`, a cochain has strictly positive cross-degree gauge distance if and only if it is
not a coboundary. -/
theorem gaugeDistErr_pos_iff_not_isCoboundary [Fintype V] [LinearOrder V]
    (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n) :
    0 < α.gaugeDistErr ↔ ¬ α.IsCoboundary := by
  rw [← α.gaugeDistErr_eq_zero_iff_isCoboundary hn]
  exact α.gaugeDistErr_nonneg.lt_iff_ne'

/-- For `2 ≤ n`, positivity of `gaugeDistErr` is equivalent to positivity of the same-degree
`gaugeDist`. -/
theorem gaugeDistErr_pos_iff_gaugeDist_pos [Fintype V] [LinearOrder V]
    (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n) :
    0 < α.gaugeDistErr ↔ 0 < α.gaugeDist (movedNorm (Fin n)) := by
  rw [α.gaugeDistErr_pos_iff_not_isCoboundary hn, α.gaugeDist_pos_iff_not_isCoboundary]

/-- In degree `2`, every admissible gauge has degree `m + 2 ≥ 2`, so `gaugeDistErr` is invariant
under degree-`2` gauge transformations. -/
@[simp]
theorem gaugeDistErr_smul_two [Fintype V] [LinearOrder V] (α : Cochain X (Perm (Fin 2)))
    (γ : V → Perm (Fin 2)) : (γ • α).gaugeDistErr = α.gaugeDistErr := by
  rw [gaugeDistErr_def, gaugeDistErr_def]
  refine iInf_congr fun m => ?_
  let emb : (V → Perm (Fin (m + 2))) ≃ (V → Perm (Fin (m + 2))) :=
    Equiv.mulLeft fun v => (γ v).viaEmbedding (Fin.castLEEmb (by omega))
  exact emb.iInf_congr fun β => (α.costErr_smul_of_le γ β (by omega)).symm

/-- `gaugeDistErr` does not depend on the `LinearOrder` chosen on `V`. -/
theorem gaugeDistErr_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V)
    (α : Cochain X (Perm (Fin n))) :
    @gaugeDistErr V X n _ l₁ α = @gaugeDistErr V X n _ l₂ α := by
  simp only [@gaugeDistErr_def V X n _ l₁ α, @gaugeDistErr_def V X n _ l₂ α,
    costErr_congr_linearOrder l₁ l₂ α]

/-- Relabelling `α` along `e : V ≃ W` preserves `gaugeDistErr`. -/
@[simp]
theorem gaugeDistErr_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (α : Cochain X (Perm (Fin n))) (e : V ≃ W) :
    (α.relabel e).gaugeDistErr = α.gaugeDistErr := by
  rw [gaugeDistErr_def, gaugeDistErr_def]
  refine iInf_congr fun m => ?_
  exact (Equiv.arrowCongr e.symm (Equiv.refl (Perm (Fin (m + 2))))).iInf_congr fun γ =>
    (α.costErr_relabel γ e).symm

@[simp]
theorem gaugeDistErr_relabelComplete [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (α : Cochain (complete V) (Perm (Fin n))) (e : V ≃ W) :
    (α.relabelComplete e).gaugeDistErr = α.gaugeDistErr :=
  (congr_complex_perm (fun _ δ => δ.gaugeDistErr) (relabel_complete e).symm
    fun _ _ => by simp).trans (α.gaugeDistErr_relabel e)

/-! ### Balanced replication of `gaugeDistErr` -/

/-- Replicating `α` along `V ×ₗ ι` multiplies `gaugeDistErr` by at least `(Fintype.card ι) ^ 2`. -/
theorem card_sq_mul_gaugeDistErr_le_replicate {ι : Type*} [Fintype V] [LinearOrder V] [Fintype ι]
    [LinearOrder ι] (α : Cochain (complete V) (Perm (Fin n))) :
    (Fintype.card ι : ℝ) ^ 2 * α.gaugeDistErr ≤ (α.replicate ι).gaugeDistErr := by
  rw [gaugeDistErr_def]
  refine le_ciInf fun m => ?_
  have hrep (β : (V ×ₗ ι) → Perm (Fin (m + 2))) :
      (α.replicate ι).costErr β =
        ∑ e ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι))),
          distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
            (β e.1 * (β e.2)⁻¹) := by
    rw [costErr_complete]
    refine sum_congr rfl fun e _ => ?_
    rw [replicate_apply]
    split_ifs with h
    · rw [h, α.apply_self]
    · rfl
  simp_rw [hrep]
  refine (mul_le_mul_of_nonneg_left (α.gaugeDistErr_le_iInf_costErr m) (sq_nonneg _)).trans ?_
  simp_rw [costErr_complete]
  exact card_sq_mul_ciInf_le_ciInf_sum_distErr_lex (ι := ι) α.toFun (m + 2)

/-- When a cochain of degree `n ≥ 2` attains its cross-degree gauge distance at its own degree `n`,
balanced replication along `V ×ₗ ι` multiplies `gaugeDistErr` by exactly `(Fintype.card ι) ^ 2`. -/
theorem gaugeDistErr_replicate_eq {ι : Type*} [Fintype V] [LinearOrder V] [Fintype ι]
    [LinearOrder ι] (α : Cochain (complete V) (Perm (Fin n))) (hn : 2 ≤ n)
    (hmin : α.gaugeDistErr = α.gaugeDist (movedNorm (Fin n)) / n) :
    (α.replicate ι).gaugeDistErr = (Fintype.card ι : ℝ) ^ 2 * α.gaugeDistErr := by
  refine le_antisymm ?_ (α.card_sq_mul_gaugeDistErr_le_replicate)
  calc (α.replicate ι).gaugeDistErr
      ≤ (α.replicate ι).gaugeDist (movedNorm (Fin n)) / n :=
        (α.replicate ι).gaugeDistErr_le_gaugeDist_div hn
    _ = ((Fintype.card ι : ℝ) ^ 2 * α.gaugeDist (movedNorm (Fin n))) / n := by
        rw [gaugeDist_replicate]
    _ = (Fintype.card ι : ℝ) ^ 2 * α.gaugeDistErr := by
        rw [hmin]; ring

end GaugeDistErr

end Cochain

/-! ### The cross-degree Cheeger constant `h1Err` -/

section Constant

variable {V W : Type*}

/-- The Chapman–Lubotzky cross-degree Cheeger constant in the counting convention: the infimum of
`(α.defect (movedNorm (Fin (n + 2))) / (n + 2)) / α.gaugeDistErr` over cochains of degree
`n + 2 ≥ 2` at strictly positive cross-degree gauge distance. -/
noncomputable def h1Err [Fintype V] [LinearOrder V] (X : TwoComplex V) : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
    r = α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr}

theorem h1Err_def [Fintype V] [LinearOrder V] (X : TwoComplex V) :
    h1Err X =
      sInf {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
        r = α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr} := (rfl)

section FixedOrder

variable [Fintype V] [LinearOrder V]

private theorem bddBelow_setOf_defect_div_gaugeDistErr (X : TwoComplex V) :
    BddBelow {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
      r = α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr} :=
  ⟨0, by
    rintro r ⟨n, α, hα, rfl⟩
    exact div_nonneg (div_nonneg (α.defect_nonneg _) (Nat.cast_nonneg _)) hα.le⟩

/-- The cross-degree Cheeger constant is nonnegative. -/
theorem h1Err_nonneg (X : TwoComplex V) : 0 ≤ h1Err X :=
  Real.sInf_nonneg fun _ ⟨_, α, hα, hr⟩ =>
    hr ▸ div_nonneg (div_nonneg (α.defect_nonneg _) (Nat.cast_nonneg _)) hα.le

/-- Every cochain of degree `n + 2 ≥ 2` at positive cross-degree gauge distance gives an upper
bound on `h1Err X`. -/
theorem h1Err_le_div {X : TwoComplex V} {n : ℕ} {α : Cochain X (Perm (Fin (n + 2)))}
    (hα : 0 < α.gaugeDistErr) :
    h1Err X ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr :=
  csInf_le (bddBelow_setOf_defect_div_gaugeDistErr X) ⟨n, α, hα, rfl⟩

/-- Every cochain of degree `n ≥ 2` at positive cross-degree gauge distance gives an upper bound on
`h1Err X`. -/
theorem h1Err_le_div_of_le {X : TwoComplex V} {n : ℕ} (hn : 2 ≤ n)
    {α : Cochain X (Perm (Fin n))} (hα : 0 < α.gaugeDistErr) :
    h1Err X ≤ α.defect (movedNorm (Fin n)) / n / α.gaugeDistErr := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact h1Err_le_div hα

theorem le_h1Err_iff {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ} :
    c ≤ h1Err X ↔
      ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr →
        c ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr := by
  obtain ⟨n₀, α₀, hα₀⟩ := hne
  rw [h1Err_def, le_csInf_iff (bddBelow_setOf_defect_div_gaugeDistErr X)
    ⟨_, n₀, α₀, hα₀, rfl⟩]
  exact ⟨fun h n α hα => h _ ⟨n, α, hα, rfl⟩,
    fun h _ ⟨n, α, hα, hr⟩ => hr ▸ h n α hα⟩

theorem h1Err_lt_iff {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ} :
    h1Err X < c ↔
      ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
        α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr < c := by
  obtain ⟨n₀, α₀, hα₀⟩ := hne
  rw [h1Err_def, csInf_lt_iff (bddBelow_setOf_defect_div_gaugeDistErr X)
    ⟨_, n₀, α₀, hα₀, rfl⟩]
  exact ⟨fun ⟨_, ⟨n, α, hα, hr⟩, hlt⟩ => ⟨n, α, hα, hr ▸ hlt⟩,
    fun ⟨n, α, hα, hlt⟩ => ⟨_, ⟨n, α, hα, rfl⟩, hlt⟩⟩

theorem le_h1Err_of_forall {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ}
    (hc : ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr →
      c ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr) :
    c ≤ h1Err X :=
  (le_h1Err_iff hne).mpr hc

/-- When every cochain of degree `≥ 2` has cross-degree gauge distance zero, the ratio set is
empty and `h1Err X = 0`. -/
theorem h1Err_eq_zero_of_forall_gaugeDistErr_eq_zero {X : TwoComplex V}
    (h : ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), α.gaugeDistErr = 0) :
    h1Err X = 0 := by
  simp [h1Err_def, h]

/-- On a finite two-complex with at most two vertices, every cochain is a coboundary, so
`h1Err X = 0`. -/
theorem h1Err_eq_zero_of_card_le_two (X : TwoComplex V) (hV : Fintype.card V ≤ 2) :
    h1Err X = 0 :=
  h1Err_eq_zero_of_forall_gaugeDistErr_eq_zero fun _ α =>
    (α.isCoboundary_of_card_le_two hV).gaugeDistErr_eq_zero (by omega)

/-- Comparing `h1Sym` and `h1Err`: allowing cross-degree gauges can only decrease the denominator
`gaugeDistErr ≤ gaugeDist / (n + 2)`, so `h1Sym X ≤ h1Err X` holds unconditionally for every
two-complex `X`. -/
theorem h1Sym_le_h1Err (X : TwoComplex V) : h1Sym X ≤ h1Err X := by
  by_cases hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr
  · refine le_h1Err_of_forall hne fun n α hα => ?_
    have hdeg_pos : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    have hle : α.gaugeDistErr ≤ α.gaugeDist (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) :=
      α.gaugeDistErr_le_gaugeDist_div (by omega)
    have hgd_pos : 0 < α.gaugeDist (movedNorm (Fin (n + 2))) :=
      (α.gaugeDistErr_pos_iff_gaugeDist_pos (by omega)).mp hα
    calc h1Sym X
        ≤ h1 X (movedNorm (Fin (n + 2))) := h1Sym_le_h1_movedNorm_add_two X n
      _ ≤ α.defect (movedNorm (Fin (n + 2))) / α.gaugeDist (movedNorm (Fin (n + 2))) :=
          h1_le_div hgd_pos
      _ = α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) /
            (α.gaugeDist (movedNorm (Fin (n + 2))) / (n + 2 : ℕ)) := by
          field_simp [hdeg_pos.ne']
      _ ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr :=
          div_le_div_of_nonneg_left (div_nonneg (α.defect_nonneg _) hdeg_pos.le) hα hle
  · push Not at hne
    have hzero : ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), α.gaugeDistErr = 0 := fun n α =>
      le_antisymm (hne n α) α.gaugeDistErr_nonneg
    have h1zero : ∀ n : ℕ, h1 X (movedNorm (Fin (n + 2))) = 0 := fun n =>
      h1_eq_zero_of_forall_gaugeDist_eq_zero fun α =>
        ((α.gaugeDist_eq_zero_iff_isCoboundary _).mpr
          ((α.gaugeDistErr_eq_zero_iff_isCoboundary (by omega)).mp (hzero n α)))
    have hsym0 : h1Sym X = 0 := by simp [h1Sym_def, h1zero]
    rw [hsym0, h1Err_eq_zero_of_forall_gaugeDistErr_eq_zero hzero]

end FixedOrder

/-! ### Order independence and vertex relabelling -/

/-- `h1Err X` does not depend on the `LinearOrder` chosen on `V`. -/
theorem h1Err_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V) (X : TwoComplex V) :
    @h1Err V _ l₁ X = @h1Err V _ l₂ X := by
  simp only [@h1Err_def V _ l₁ X, @h1Err_def V _ l₂ X,
    Cochain.gaugeDistErr_congr_linearOrder l₁ l₂,
    Cochain.defect_congr_linearOrder l₁ l₂ isConjInvariant_movedNorm]

/-- Relabelling `X` along `e : V ≃ W` preserves `h1Err`. -/
@[simp]
theorem h1Err_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (X : TwoComplex V) (e : V ≃ W) : h1Err (X.relabel e) = h1Err X := by
  rw [h1Err_def, h1Err_def]
  congr 1; ext r
  refine exists_congr fun n => ?_
  exact ((Cochain.relabelEquiv X e).exists_congr fun α => by
    simp [α.defect_relabel isConjInvariant_movedNorm e]).symm

/-- `h1Err` on the complete complex is preserved along any bijection `V ≃ W`. -/
theorem h1Err_complete_congr [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (e : V ≃ W) : h1Err (complete V) = h1Err (complete W) := by
  rw [← relabel_complete e, h1Err_relabel (complete V) e]

/-- `h1Err (complete V)` depends on `V` only through `Fintype.card V`. -/
theorem h1Err_complete_eq_of_card_eq [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (hcard : Fintype.card V = Fintype.card W) : h1Err (complete V) = h1Err (complete W) :=
  h1Err_complete_congr (Fintype.equivOfCardEq hcard)

/-! ### Star bound, boundary cases, and replication on the complete complex -/

section CompleteBounds

variable [Fintype V] [LinearOrder V]

/-- The cross-degree star bound in counting form: for every cochain of degree `n ≥ 2` on
`complete V`, `card V * gaugeDistErr α ≤ 3 * (defect α / n)`. -/
theorem card_mul_gaugeDistErr_le {n : ℕ} (hn : 2 ≤ n) (α : Cochain (complete V) (Perm (Fin n))) :
    (Fintype.card V : ℝ) * α.gaugeDistErr ≤ 3 * (α.defect (movedNorm (Fin n)) / n) := by
  calc (Fintype.card V : ℝ) * α.gaugeDistErr
      ≤ (Fintype.card V : ℝ) * (α.gaugeDist (movedNorm (Fin n)) / n) :=
        mul_le_mul_of_nonneg_left (α.gaugeDistErr_le_gaugeDist_div hn) (Nat.cast_nonneg _)
    _ = ((Fintype.card V : ℝ) * α.gaugeDist (movedNorm (Fin n))) / n := by ring
    _ ≤ (3 * α.defect (movedNorm (Fin n))) / n :=
        div_le_div_of_nonneg_right (card_mul_gaugeDist_le _ isConjInvariant_movedNorm α)
          (Nat.cast_nonneg _)
    _ = 3 * (α.defect (movedNorm (Fin n)) / n) := by ring

/-- Pointwise ratio form of the cross-degree star bound. -/
theorem Cochain.card_div_three_le_defect_div_gaugeDistErr {n : ℕ} (hn : 2 ≤ n)
    {α : Cochain (complete V) (Perm (Fin n))} (hα : 0 < α.gaugeDistErr) :
    (Fintype.card V : ℝ) / 3 ≤ α.defect (movedNorm (Fin n)) / n / α.gaugeDistErr := by
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hα, mul_comm _ (3 : ℝ)]
  exact card_mul_gaugeDistErr_le hn α

/-- On `complete V`, a cochain of degree `≥ 2` at positive cross-degree gauge distance exists if
and only if `3 ≤ Fintype.card V`. -/
theorem exists_gaugeDistErr_pos_complete_iff :
    (∃ (n : ℕ) (α : Cochain (complete V) (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) ↔
      3 ≤ Fintype.card V := by
  constructor
  · rintro ⟨n, α, hα⟩
    by_contra hlt
    have hle : Fintype.card V ≤ 2 := by omega
    have h0 := (α.isCoboundary_of_card_le_two hle).gaugeDistErr_eq_zero (by omega)
    linarith
  · intro hV
    have : Nontrivial (Perm (Fin 2)) := ⟨⟨1, Equiv.swap 0 1, by decide⟩⟩
    obtain ⟨α, hα⟩ := exists_not_isCoboundary_complete (G := Perm (Fin 2)) hV
    exact ⟨0, α, (α.gaugeDistErr_pos_iff_not_isCoboundary (by omega)).mpr hα⟩

/-- The cross-degree star bound on `complete V`: for `3 ≤ Fintype.card V`,
`Fintype.card V / 3 ≤ h1Err (complete V)`. -/
theorem card_div_three_le_h1Err (hV : 3 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) / 3 ≤ h1Err (complete V) :=
  (card_div_three_le_h1Sym hV).trans (h1Sym_le_h1Err (complete V))

/-- Replicating a cochain of degree `n ≥ 2` on `complete V` that attains its cross-degree gauge
distance at its own degree `n` bounds `h1Err (complete (V ×ₗ ι))` by `Fintype.card ι` times its
cross-degree expansion ratio. -/
theorem h1Err_complete_lex_le_card_mul_div {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (hn : 2 ≤ n) {α : Cochain (complete V) (Perm (Fin n))} (hα : 0 < α.gaugeDistErr)
    (hmin : α.gaugeDistErr = α.gaugeDist (movedNorm (Fin n)) / n) :
    h1Err (complete (V ×ₗ ι)) ≤
      Fintype.card ι * (α.defect (movedNorm (Fin n)) / n / α.gaugeDistErr) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hcard : Fintype.card (V ×ₗ ι) ≤ 2 := by simp [Fintype.card_eq_zero]
    rw [Fintype.card_eq_zero, Nat.cast_zero, zero_mul,
      h1Err_eq_zero_of_card_le_two (complete (V ×ₗ ι)) hcard]
  · have hpos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
    have hrep_gd : (α.replicate ι).gaugeDistErr = (Fintype.card ι : ℝ) ^ 2 * α.gaugeDistErr :=
      α.gaugeDistErr_replicate_eq hn hmin
    have hrep_pos : 0 < (α.replicate ι).gaugeDistErr := by
      rw [hrep_gd]; positivity
    refine (h1Err_le_div_of_le hn hrep_pos).trans_eq ?_
    rw [Cochain.defect_replicate, hrep_gd]
    have hne : (Fintype.card ι : ℝ) ≠ 0 := hpos.ne'
    field_simp [hne]

end CompleteBounds

end Constant

end TauCeti

end
