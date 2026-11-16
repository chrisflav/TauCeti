/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Sequence
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Topology.Algebra.Group.FirstCountable

/-!
# Removing the closure from the open mapping approximation

The Baire step of the open mapping theorem produces a point of `closure (f '' U)`, not of
`f '' U`, and every step after it inherits that closure. This file removes it: over a complete
first-countable uniform additive group `M`, if the closure of the image of every neighbourhood of
zero is a neighbourhood of zero, then the image itself is a neighbourhood of zero and `f` is open.

Three ingredients meet here, and each supplies exactly one thing.

* The approximating sequence of `TauCeti/Topology/Algebra/OpenMapping/Sequence.lean` gives
  errors `x n ∈ V n` whose partial sums leave a residual in `closure (f '' V (n + 1))`.
* Completeness turns those errors into an actual limit: along a halving basis
  `V (n + 1) + V (n + 1) ⊆ V n` (`IsTopologicalAddGroup.exists_antitone_basis_nhds_zero`), every
  tail `∑ i ∈ Finset.Ico m (m + d), x i` lies in `V m`, so the partial sums form a Cauchy sequence
  staying in `V 0` and converging to a point of `closure (V 0)`. When `V` consists of open
  subgroups, the errors are directly summable and their sum lies in `V 0` itself with no index
  shift.
* Regularity of the target sends the residuals to zero. Continuity controls `f '' V (n + 1)`
  and never its closure, so it cannot do this alone; what does it is that a neighbourhood of
  zero in `N` contains the closure of a neighbourhood (`hasBasis_nhds_closure`).

## Main results

* `TauCeti.mem_image_of_mem_closure_image`: `closure (f '' V 0) ⊆ f '' V 0`, in the presence of
  a basis of subgroups, completeness, and the neighbourhood hypothesis the Baire step supplies.
* `TauCeti.mem_image_closure_of_mem_closure_image`: `closure (f '' V 1) ⊆ f '' closure (V 0)` for
  any antitone neighbourhood basis satisfying `V (n + 1) + V (n + 1) ⊆ V n`.
* `TauCeti.isOpenMap_of_closure_image_mem_nhds`: an additive map out of a complete
  first-countable uniform additive group is open once the closures of the images of neighbourhoods
  of zero are neighbourhoods of zero.

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapter I, §3, no. 3, Lemma 1 and Theorem 1.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
-/

public section

open Filter Topology
open scoped Pointwise Uniformity

namespace TauCeti

variable {M N : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [AddGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N] [T0Space N]

/-- **Henkel's approximation converges.** Let `V` be an antitone basis of subgroups at zero in a
complete group `M`, let `f : M → N` be an additive map continuous at zero, and suppose each
`closure (f '' V (n + 1))` is a neighbourhood of zero — which is what the Baire step of Henkel's
theorem provides. Then every point of `closure (f '' V 0)` is already the image of a point of
`V 0`.

`M` is not assumed nonarchimedean: a basis of subgroups at zero is exactly that condition, and
the proof reconstructs the instance from `hV`. `N` need not be commutative, and separation of it
is used only to identify the two limits of the partial sums. -/
theorem mem_image_of_mem_closure_image {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (hf : ContinuousAt (f : M → N) 0) {V : ℕ → AddSubgroup M}
    (hV : (𝓝 (0 : M)).HasAntitoneBasis fun n ↦ (V n : Set M))
    (hVN : ∀ n, closure ((f : M → N) '' (V (n + 1) : Set M)) ∈ 𝓝 (0 : N))
    {y : N} (hy : y ∈ closure ((f : M → N) '' (V 0 : Set M))) :
    y ∈ (f : M → N) '' (V 0 : Set M) := by
  have hf' : Continuous (f : M → N) := continuous_of_continuousAt_zero f hf
  obtain ⟨x, hxV, hxres⟩ :=
    exists_seq_mem_and_sub_sum_mem f (fun n ↦ (V n : Set M)) hVN hy
  -- A basis of subgroups at zero *is* nonarchimedeanness, so the instance need not be assumed.
  have : NonarchimedeanAddGroup M :=
    ⟨fun U hU ↦ by
      obtain ⟨n, -, hn⟩ := hV.toHasBasis.mem_iff.mp hU
      exact ⟨⟨V n, (V n).isOpen_of_mem_nhds (hV.toHasBasis.mem_of_mem trivial)⟩, hn⟩⟩
  -- The errors tend to zero along the basis, so in a complete group they are summable.
  have hsummable : Summable x :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (by rw [Nat.cofinite_eq_atTop]; exact hV.tendsto hxV)
  -- Their sum stays in `V 0`: an open subgroup is closed, and every error lies in it.
  refine ⟨∑' n, x n, tsum_mem ((V 0).isClosed_of_isOpen
    ((V 0).isOpen_of_mem_nhds (hV.toHasBasis.mem_of_mem trivial)))
    (fun n ↦ hV.antitone (Nat.zero_le n) (hxV n)), ?_⟩
  -- The partial sums have two limits under `f`: its value at the sum, and `y`.
  have hpart : Tendsto (fun n ↦ (f : M → N) (∑ i ∈ Finset.range (n + 1), x i)) atTop
      (𝓝 ((f : M → N) (∑' n, x n))) :=
    ((hf'.tendsto _).comp hsummable.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  refine tendsto_nhds_unique hpart ?_
  -- The residuals tend to zero: the sets holding them shrink because `N` is regular.
  have hres : Tendsto (fun n ↦ y - (f : M → N) (∑ i ∈ Finset.range (n + 1), x i)) atTop
      (𝓝 (0 : N)) := by
    refine (hasBasis_nhds_closure (0 : N)).tendsto_right_iff.mpr fun U hU ↦ ?_
    have hpre : (f : M → N) ⁻¹' U ∈ 𝓝 (0 : M) :=
      hf (by rw [map_zero]; exact hU)
    obtain ⟨n₀, -, hn₀⟩ := hV.toHasBasis.mem_iff.mp hpre
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact closure_mono ((Set.image_mono
      ((hV.antitone (hn.trans (Nat.le_succ n))).trans hn₀)).trans
      (Set.image_preimage_subset _ _)) (hxres n)
  -- `-(y - f s) + y = f s` reassociates without commuting anything in `N`.
  simpa using hres.neg.add_const y

/-- **Successive approximation converges in any complete uniform additive group.** Let `V` be an
antitone basis of neighbourhoods of zero in a complete uniform additive group `M` satisfying
`V (n + 1) + V (n + 1) ⊆ V n`, let `f : M → N` be an additive map continuous at zero, and suppose
each `closure (f '' V (n + 2))` is a neighbourhood of zero. Then every point of
`closure (f '' V 1)` is the image of a point of `closure (V 0)`.

Unlike `TauCeti.mem_image_of_mem_closure_image`, no subgroup basis is required: the halving
condition `V (n + 1) + V (n + 1) ⊆ V n` controls the Cauchy tails of the partial sums and keeps
every partial sum inside `V 0`. -/
theorem mem_image_closure_of_mem_closure_image {F : Type*} [FunLike F M N]
    [AddMonoidHomClass F M N] (f : F) (hf : ContinuousAt (f : M → N) 0) {V : ℕ → Set M}
    (hV : (𝓝 (0 : M)).HasAntitoneBasis V) (hVadd : ∀ n, V (n + 1) + V (n + 1) ⊆ V n)
    (hVN : ∀ n, closure ((f : M → N) '' V (n + 2)) ∈ 𝓝 (0 : N))
    {y : N} (hy : y ∈ closure ((f : M → N) '' V 1)) :
    y ∈ (f : M → N) '' closure (V 0) := by
  have hf' : Continuous (f : M → N) := continuous_of_continuousAt_zero f hf
  obtain ⟨x, hxV, hxres⟩ :=
    exists_seq_mem_and_sub_sum_mem f (fun n ↦ V (n + 1)) hVN hy
  -- Every finite block `∑ i ∈ Ico m (m + d), x i` stays inside `V m` by induction on `d`.
  have hIco : ∀ d m, ∑ i ∈ Finset.Ico m (m + d), x i ∈ V m := by
    intro d
    induction d with
    | zero =>
      intro m
      simpa using mem_of_mem_nhds (hV.toHasBasis.mem_of_mem (i := m) trivial)
    | succ d ih =>
      intro m
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      have htail : ∑ i ∈ Finset.Ico (m + 1) (m + (d + 1)), x i ∈ V (m + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm 1 d] using ih (m + 1)
      exact hVadd m (Set.add_mem_add (hxV m) htail)
  -- The partial sums form a Cauchy sequence in the complete group `M`.
  let s : ℕ → M := fun n ↦ ∑ i ∈ Finset.range n, x i
  have hs_cauchy : CauchySeq s := by
    rw [cauchySeq_iff]
    intro U hU
    rw [uniformity_eq_comap_nhds_zero, Filter.mem_comap] at hU
    obtain ⟨W, hW, hWU⟩ := hU
    have hWsym : W ∩ (-W) ∈ 𝓝 (0 : M) :=
      Filter.inter_mem hW (neg_mem_nhds_zero M hW)
    obtain ⟨m, -, hm⟩ := hV.toHasBasis.mem_iff.mp hWsym
    refine ⟨m, fun p hp q hq ↦ hWU ?_⟩
    rw [Set.mem_preimage]
    rcases le_total p q with hpq | hqp
    · have hsub : s q - s p = ∑ i ∈ Finset.Ico p (p + (q - p)), x i := by
        rw [Nat.add_sub_of_le hpq, Finset.sum_Ico_eq_sub _ hpq]
      exact (hm (hV.antitone hp (hsub.symm ▸ hIco (q - p) p))).1
    · have hsub : s p - s q = ∑ i ∈ Finset.Ico q (q + (p - q)), x i := by
        rw [Nat.add_sub_of_le hqp, Finset.sum_Ico_eq_sub _ hqp]
      have hneg : s p - s q ∈ -W := (hm (hV.antitone hq (hsub.symm ▸ hIco (p - q) q))).2
      simpa [neg_sub] using Set.mem_neg.mp hneg
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hs_cauchy
  have ha_mem : a ∈ closure (V 0) :=
    mem_closure_of_tendsto ha <| Eventually.of_forall fun n ↦ by
      simpa [s, Nat.Ico_zero_eq_range] using hIco n 0
  refine ⟨a, ha_mem, ?_⟩
  have hpart : Tendsto (fun n ↦ (f : M → N) (s (n + 1))) atTop (𝓝 ((f : M → N) a)) :=
    ((hf'.tendsto a).comp ha).comp (tendsto_add_atTop_nat 1)
  refine tendsto_nhds_unique hpart ?_
  have hres : Tendsto (fun n ↦ y - (f : M → N) (s (n + 1))) atTop (𝓝 (0 : N)) := by
    refine (hasBasis_nhds_closure (0 : N)).tendsto_right_iff.mpr fun U hU ↦ ?_
    have hpre : (f : M → N) ⁻¹' U ∈ 𝓝 (0 : M) :=
      hf (by rw [map_zero]; exact hU)
    obtain ⟨n₀, -, hn₀⟩ := hV.toHasBasis.mem_iff.mp hpre
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact closure_mono ((Set.image_mono
      ((hV.antitone (hn.trans (by omega))).trans hn₀)).trans
      (Set.image_preimage_subset _ _)) (hxres n)
  simpa using hres.neg.add_const y

/-- **Openness from the closure step.** Let `f : M → N` be an additive map, continuous at zero,
out of a complete first-countable uniform additive group. If the closure of the image of every
neighbourhood of zero is a neighbourhood of zero, then `f` is open.

The hypothesis is what the Baire step of the open mapping theorem provides, and it can also be
checked directly by approximating a dense subset of a neighbourhood of zero in `N` with control
(as in Schwartz's finiteness theorem). -/
theorem isOpenMap_of_closure_image_mem_nhds [(𝓝 (0 : M)).IsCountablyGenerated]
    {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N] (f : F)
    (hfc : ContinuousAt (f : M → N) 0)
    (h : ∀ U ∈ 𝓝 (0 : M), closure ((f : M → N) '' U) ∈ 𝓝 (0 : N)) :
    IsOpenMap (f : M → N) := by
  have : FirstCountableTopology M := ContinuousConstVAdd.toFirstCountableTopology
  refine IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr fun S hS ↦ ?_
  rw [Filter.mem_map] at hS
  obtain ⟨T, hT, hTcl⟩ := (hasBasis_nhds_closure (0 : M)).mem_iff.mp hS
  obtain ⟨V, hV, hVadd⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero M
  obtain ⟨n₀, -, hn₀⟩ := hV.toHasBasis.mem_iff.mp hT
  -- Shift the basis so that the closure of its zeroth term already lies inside `f ⁻¹' S`.
  have hW : (𝓝 (0 : M)).HasAntitoneBasis fun n ↦ V (n₀ + n) :=
    hV.comp_mono (fun _ _ hab ↦ Nat.add_le_add_left hab _)
      (by simpa [Nat.add_comm] using tendsto_add_atTop_nat n₀)
  have hWadd : ∀ n, V (n₀ + (n + 1)) + V (n₀ + (n + 1)) ⊆ V (n₀ + n) := fun n ↦ by
    simpa [Nat.add_assoc] using hVadd (n₀ + n)
  have hnhds : ∀ n, closure ((f : M → N) '' V (n₀ + n)) ∈ 𝓝 (0 : N) := fun n ↦
    h _ (hW.toHasBasis.mem_of_mem (i := n) trivial)
  refine Filter.mem_of_superset (hnhds 1) fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ :=
    mem_image_closure_of_mem_closure_image f hfc hW hWadd (fun n ↦ hnhds (n + 2)) hy
  exact hTcl (closure_mono hn₀ hx)

end TauCeti

end
