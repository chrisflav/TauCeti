/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import TauCeti.Combinatorics.Graph.Potts.Basic
public import TauCeti.Probability.ProbabilityMassFunction.Finite

/-!
# Boltzmann weights and the Edwards–Sokal coupling for finite Potts models

This file connects the algebraic Potts and Fortuin–Kasteleyn sums from
`TauCeti.Combinatorics.Graph.Potts.Basic` to statistical mechanics and probability on multigraphs
with finite vertex and edge sets:

* **Boltzmann weights** `Graph.pottsBoltzmannWeight G β J e = exp (β * J e) - 1`, rewriting
  `Graph.pottsPartition` as the Gibbs sum
  $$\sum_{\sigma : V(G) \to \mathrm{Fin}\, q}
      \exp\!\left(\beta \sum_{e \in E(G)} [\text{$e$ monochromatic under $\sigma$}]\, J_e\right)$$
  (`Graph.pottsPartition_pottsBoltzmannWeight`), with nonnegativity under ferromagnetic couplings
  `0 ≤ β * J e` (`Graph.pottsBoltzmannWeight_nonneg`).
* **Marginal and joint probability mass functions** for `q : ℕ` with `[NeZero q]` and nonnegative
  weights `v : E(G) → ℝ≥0`:
  * `Graph.pottsPMF G q v : PMF (V(G) → Fin q)`;
  * `Graph.fkPMF G q v : PMF (Finset E(G))`;
  * `Graph.edwardsSokalPMF G q v : PMF ((V(G) → Fin q) × Finset E(G))`, assigning mass
    $(\prod_{e \in A} v_e) / Z_{\mathrm{FK}}(G; q, v)$ when every edge of $A$ is monochromatic
    under $\sigma$ and $0$ otherwise.
* **Both marginals** (`Graph.map_fst_edwardsSokalPMF`, `Graph.map_snd_edwardsSokalPMF`), **both
  conditional distributions** (`Graph.edwardsSokalGivenColoringPMF` with its independent-percolation
  product formula `Graph.edwardsSokalGivenColoringPMF_apply_eq_prod`, and
  `Graph.edwardsSokalGivenClusterPMF` with uniform component colouring), their **generative `bind`
  identities**, **posterior `PMF.filter` characterizations**, and **Swendsen–Wang Markov kernel
  invariance** (`Graph.swendsenWang_pottsPMF`, `Graph.swendsenWang_fkPMF`).

## References

* R. G. Edwards and A. D. Sokal, *Generalization of the Fortuin–Kasteleyn–Swendsen–Wang
  representation and Monte Carlo algorithm*, Phys. Rev. D 38 (1988), 2009–2012.
* R. H. Swendsen and J.-S. Wang, *Nonuniversal critical dynamics in Monte Carlo simulations*,
  Phys. Rev. Lett. 58 (1987), 86–88.
* C. M. Fortuin and P. W. Kasteleyn, *On the random-cluster model. I. Introduction and relation to
  other models*, Physica 57 (1972), 536–564.
-/

public section

open Set
open scoped BigOperators ENNReal NNReal

universe u v w

namespace Graph

variable {V : Type u} {E : Type v} {R : Type w} [CommSemiring R]

/-! ### Unnormalized single-colouring Potts weight and Boltzmann specialisation -/

/-- The unnormalized Potts weight of a single vertex colouring `σ : V(G) → γ`: the product over
actual edges `e : E(G)` of `1 + v e` when `e` is monochromatic under `σ` and `1` otherwise. -/
noncomputable def pottsWeight (G : Graph V E) [Finite E(G)] {γ : Type*}
    (σ : V(G) → γ) (v : E(G) → R) : R := by
  classical
  have := Fintype.ofFinite E(G)
  exact ∏ e : E(G), (1 + if G.IsMonochromaticEdge σ e then v e else 0)

/-- Explicit `Finset.univ` product formula for `Graph.pottsWeight` when `E(G)` carries a `Fintype`
instance. -/
theorem pottsWeight_eq_prod_fintype (G : Graph V E) [Fintype E(G)] {γ : Type*}
    (σ : V(G) → γ) (v : E(G) → R) :
    G.pottsWeight σ v =
      ∏ e : E(G), (1 + open Classical in if G.IsMonochromaticEdge σ e then v e else 0) := by
  unfold pottsWeight
  convert rfl

/-- Subset expansion of `Graph.pottsWeight` over monochromatic edge subsets `A ⊆ E(G)`. -/
theorem pottsWeight_eq_sum_monochromatic (G : Graph V E) [Fintype E(G)] {γ : Type*}
    (σ : V(G) → γ) (v : E(G) → R) :
    G.pottsWeight σ v =
      ∑ A : Finset E(G),
        open Classical in if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, v e else 0 := by
  classical
  rw [pottsWeight_eq_prod_fintype, Finset.prod_one_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  by_cases hA : ∀ e ∈ A, G.IsMonochromaticEdge σ e
  · rw [ite_eq_left_iff.mpr fun h ↦ (h hA).elim]
    exact Finset.prod_congr rfl fun e he ↦ ite_eq_left_iff.mpr fun h ↦ (h (hA e he)).elim
  · rw [ite_eq_right_iff.mpr fun h ↦ (hA h).elim]
    push Not at hA
    obtain ⟨e, heA, hne⟩ := hA
    exact Finset.prod_eq_zero heA (ite_eq_right_iff.mpr fun h ↦ (hne h).elim)

/-- Summing `Graph.pottsWeight` over all `q`-colourings gives `Graph.pottsPartition`. -/
theorem sum_pottsWeight_eq_pottsPartition (G : Graph V E) [Fintype V(G)] [DecidableEq V(G)]
    [Finite E(G)] (q : ℕ) (v : E(G) → R) :
    ∑ σ : V(G) → Fin q, G.pottsWeight σ v = G.pottsPartition q v := by
  classical
  have := Fintype.ofFinite E(G)
  simp_rw [pottsWeight_eq_prod_fintype, pottsPartition_eq_sum_fintype]

/-- Commutative-semiring homomorphisms commute with `Graph.pottsWeight`. -/
theorem map_pottsWeight {S : Type*} [CommSemiring S] {F : Type*} [FunLike F R S]
    [RingHomClass F R S] (φ : F) (G : Graph V E) [Finite E(G)] {γ : Type*}
    (σ : V(G) → γ) (v : E(G) → R) :
    φ (G.pottsWeight σ v) = G.pottsWeight σ (φ ∘ v) := by
  classical
  have := Fintype.ofFinite E(G)
  rw [pottsWeight_eq_prod_fintype, pottsWeight_eq_prod_fintype, map_prod]
  refine Finset.prod_congr rfl fun e _ ↦ ?_
  split_ifs <;> simp

/-- **Boltzmann edge weight** `v_e = exp (β * J e) - 1` associated to inverse temperature `β : ℝ`
and edge couplings `J : E(G) → ℝ`. -/
noncomputable def pottsBoltzmannWeight (G : Graph V E) (β : ℝ) (J : E(G) → ℝ) (e : E(G)) : ℝ :=
  Real.exp (β * J e) - 1

/-- Evaluation of `Graph.pottsBoltzmannWeight`. -/
@[simp]
theorem pottsBoltzmannWeight_apply (G : Graph V E) (β : ℝ) (J : E(G) → ℝ) (e : E(G)) :
    G.pottsBoltzmannWeight β J e = Real.exp (β * J e) - 1 := (rfl)

/-- Adding `1` to `Graph.pottsBoltzmannWeight` recovers the Boltzmann factor `exp (β * J e)`. -/
theorem one_add_pottsBoltzmannWeight (G : Graph V E) (β : ℝ) (J : E(G) → ℝ) (e : E(G)) :
    1 + G.pottsBoltzmannWeight β J e = Real.exp (β * J e) :=
  add_sub_cancel 1 (Real.exp (β * J e))

/-- Ferromagnetic couplings `0 ≤ β * J e` yield nonnegative random-cluster weights `0 ≤ v_e`. -/
theorem pottsBoltzmannWeight_nonneg (G : Graph V E) {β : ℝ} {J : E(G) → ℝ} {e : E(G)}
    (h : 0 ≤ β * J e) : 0 ≤ G.pottsBoltzmannWeight β J e :=
  sub_nonneg.mpr (Real.one_le_exp h)

/-- Under Boltzmann edge weights `v_e = exp (β * J e) - 1`, `Graph.pottsPartition` equals the
statistical-mechanical Gibbs sum over spin configurations `σ : V(G) → Fin q`. -/
theorem pottsPartition_pottsBoltzmannWeight (G : Graph V E) [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] (q : ℕ) (β : ℝ) (J : E(G) → ℝ) :
    G.pottsPartition q (G.pottsBoltzmannWeight β J) =
      ∑ σ : V(G) → Fin q,
        Real.exp (β * ∑ e : E(G), open Classical in
          if G.IsMonochromaticEdge σ e then J e else 0) := by
  rw [pottsPartition_eq_sum_fintype]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun e _ ↦ ?_
  split_ifs
  · exact G.one_add_pottsBoltzmannWeight β J e
  · simp

/-! ### Positivity on `ℝ≥0` and `ℝ≥0∞` normalization helpers -/

/-- For nonnegative weights `v : E(G) → ℝ≥0`, every single-colouring Potts weight is at least `1`,
hence strictly positive. -/
theorem one_le_pottsWeight (G : Graph V E) [Finite E(G)] {γ : Type*}
    (σ : V(G) → γ) (v : E(G) → ℝ≥0) : 1 ≤ G.pottsWeight σ v := by
  classical
  have := Fintype.ofFinite E(G)
  rw [pottsWeight_eq_prod_fintype]
  exact Finset.one_le_prod fun _ _ ↦ le_self_add

/-- Strict positivity of `Graph.pottsWeight` on `ℝ≥0`. -/
theorem pottsWeight_pos (G : Graph V E) [Finite E(G)] {γ : Type*}
    (σ : V(G) → γ) (v : E(G) → ℝ≥0) : 0 < G.pottsWeight σ v :=
  zero_lt_one.trans_le (G.one_le_pottsWeight σ v)

/-- Strict positivity of `Graph.fkPartition` on `ℝ≥0` when `q ≠ 0`. -/
theorem fkPartition_pos (G : Graph V E) [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) : 0 < G.fkPartition (q : ℝ≥0) v := by
  classical
  have := Fintype.ofFinite E(G)
  rw [fkPartition_eq_sum_fintype]
  have hq : (0 : ℝ≥0) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have h0 : 0 < (q : ℝ≥0) ^
      (G.restrict (Subtype.val '' ((∅ : Finset E(G)) : Set E(G)))).componentCount *
      ∏ e ∈ (∅ : Finset E(G)), v e := by
    simp [pow_pos hq]
  exact h0.trans_le (Finset.single_le_sum
    (f := fun A : Finset E(G) ↦
      (q : ℝ≥0) ^ (G.restrict (Subtype.val '' (A : Set E(G)))).componentCount * ∏ e ∈ A, v e)
    (fun _ _ ↦ zero_le) (Finset.mem_univ ∅))

/-- Strict positivity of `Graph.pottsPartition` on `ℝ≥0` when `q ≠ 0`. -/
theorem pottsPartition_pos (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) : 0 < G.pottsPartition q v := by
  rw [pottsPartition_eq_fkPartition]
  exact G.fkPartition_pos q v

private theorem card_monochromatic_eq_pow_componentCount (G : Graph V E) [Fintype V(G)]
    [DecidableEq V(G)] (q : ℕ) (A : Finset E(G))
    [DecidablePred fun σ : V(G) → Fin q ↦ ∀ e ∈ A, G.IsMonochromaticEdge σ e] :
    (Finset.univ.filter fun σ : V(G) → Fin q ↦ ∀ e ∈ A, G.IsMonochromaticEdge σ e).card =
      q ^ (G.restrict (Subtype.val '' (A : Set E(G)))).componentCount := by
  classical
  let K := G.restrict (Subtype.val '' (A : Set E(G)))
  have := Fintype.ofFinite K.ConnectedComponent
  rw [← Fintype.card_coe]
  have heq : {σ : V(G) → Fin q //
      σ ∈ Finset.univ.filter fun σ ↦ ∀ e ∈ A, G.IsMonochromaticEdge σ e} ≃
      {σ : V(G) → Fin q // ∀ e ∈ (A : Set E(G)), G.IsMonochromaticEdge σ e} :=
    Equiv.subtypeEquivRight fun _ ↦ by simp
  rw [Fintype.card_congr (heq.trans (G.monochromaticColoringEquiv (A : Set E(G)) (Fin q))),
    Fintype.card_fun, Fintype.card_fin, K.componentCount_def, Nat.card_eq_fintype_card]

private theorem tsum_pottsWeight_coe (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) (v : E(G) → ℝ≥0) :
    (∑' σ : V(G) → Fin q, (↑(G.pottsWeight σ v) : ℝ≥0∞)) =
      (↑(G.pottsPartition q v) : ℝ≥0∞) := by
  classical
  have := Fintype.ofFinite V(G)
  rw [tsum_fintype, ← ENNReal.ofNNReal_finsetSum, G.sum_pottsWeight_eq_pottsPartition]

private theorem tsum_fkWeight_coe (G : Graph V E) [Finite E(G)]
    (q : ℕ) (v : E(G) → ℝ≥0) :
    (∑' A : Finset E(G),
        (((q : ℝ≥0) ^ (G.restrict (Subtype.val '' (A : Set E(G)))).componentCount *
          ∏ e ∈ A, v e : ℝ≥0) : ℝ≥0∞)) =
      (↑(G.fkPartition (q : ℝ≥0) v) : ℝ≥0∞) := by
  classical
  have := Fintype.ofFinite E(G)
  rw [tsum_fintype, ← ENNReal.ofNNReal_finsetSum, ← fkPartition_eq_sum_fintype]

private theorem sum_edwardsSokalWeight_snd (G : Graph V E) [Fintype V(G)] [DecidableEq V(G)]
    (q : ℕ) (v : E(G) → ℝ≥0) (A : Finset E(G)) :
    (∑ σ : V(G) → Fin q,
        open Classical in
        if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) =
      (q : ℝ≥0∞) ^ (G.restrict (Subtype.val '' (A : Set E(G)))).componentCount *
        ∏ e ∈ A, (v e : ℝ≥0∞) := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    G.card_monochromatic_eq_pow_componentCount q A, Nat.cast_pow]

private theorem sum_edwardsSokalWeight_fst (G : Graph V E) [Fintype E(G)]
    {γ : Type*} (σ : V(G) → γ) (v : E(G) → ℝ≥0) :
    (∑ A : Finset E(G),
        open Classical in
        if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) =
      (↑(G.pottsWeight σ v) : ℝ≥0∞) := by
  rw [G.pottsWeight_eq_sum_monochromatic σ v, ENNReal.ofNNReal_finsetSum]
  symm
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  split_ifs <;> simp [ENNReal.ofNNReal_finsetProd]

private theorem tsum_edwardsSokalWeight_fst (G : Graph V E) [Finite E(G)]
    {γ : Type*} (σ : V(G) → γ) (v : E(G) → ℝ≥0) :
    (∑' A : Finset E(G),
        open Classical in
        if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) =
      (↑(G.pottsWeight σ v) : ℝ≥0∞) := by
  have := Fintype.ofFinite E(G)
  rw [tsum_fintype]
  convert G.sum_edwardsSokalWeight_fst σ v

private theorem tsum_edwardsSokalWeight (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) (v : E(G) → ℝ≥0) :
    (∑' p : (V(G) → Fin q) × Finset E(G),
        open Classical in
        if ∀ e ∈ p.2, G.IsMonochromaticEdge p.1 e then ∏ e ∈ p.2, (v e : ℝ≥0∞) else 0) =
      (↑(G.fkPartition (q : ℝ≥0) v) : ℝ≥0∞) := by
  classical
  have := Fintype.ofFinite V(G)
  have := Fintype.ofFinite E(G)
  rw [tsum_fintype, Fintype.sum_prod_type_right]
  dsimp only
  simp_rw [G.sum_edwardsSokalWeight_snd q v]
  rw [fkPartition_eq_sum_fintype, ENNReal.ofNNReal_finsetSum]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  simp [ENNReal.ofNNReal_finsetProd]

/-! ### Potts, Fortuin–Kasteleyn, and Edwards–Sokal probability mass functions -/

/-- **The `q`-state Potts probability mass function** on vertex colourings `V(G) → Fin q`. -/
noncomputable def pottsPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) : PMF (V(G) → Fin q) :=
  PMF.normalize (fun σ ↦ (↑(G.pottsWeight σ v) : ℝ≥0∞))
    (by
      rw [G.tsum_pottsWeight_coe]
      exact ENNReal.coe_ne_zero.mpr (G.pottsPartition_pos q v).ne')
    (by
      rw [G.tsum_pottsWeight_coe]
      exact ENNReal.coe_ne_top)

/-- Point mass of `Graph.pottsPMF`. -/
@[simp]
theorem pottsPMF_apply (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) (σ : V(G) → Fin q) :
    G.pottsPMF q v σ =
      (↑(G.pottsWeight σ v) : ℝ≥0∞) * (↑(G.pottsPartition q v) : ℝ≥0∞)⁻¹ := by
  rw [pottsPMF, PMF.normalize_apply, G.tsum_pottsWeight_coe]

/-- **The Fortuin–Kasteleyn (random-cluster) probability mass function** on edge subsets
`Finset E(G)`. -/
noncomputable def fkPMF (G : Graph V E) [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) : PMF (Finset E(G)) :=
  PMF.normalize
    (fun A ↦ (((q : ℝ≥0) ^ (G.restrict (Subtype.val '' (A : Set E(G)))).componentCount *
      ∏ e ∈ A, v e : ℝ≥0) : ℝ≥0∞))
    (by
      rw [G.tsum_fkWeight_coe]
      exact ENNReal.coe_ne_zero.mpr (G.fkPartition_pos q v).ne')
    (by
      rw [G.tsum_fkWeight_coe]
      exact ENNReal.coe_ne_top)

/-- Point mass of `Graph.fkPMF`. -/
@[simp]
theorem fkPMF_apply (G : Graph V E) [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) (A : Finset E(G)) :
    G.fkPMF q v A =
      ((q : ℝ≥0∞) ^ (G.restrict (Subtype.val '' (A : Set E(G)))).componentCount *
        ∏ e ∈ A, (v e : ℝ≥0∞)) * (↑(G.fkPartition (q : ℝ≥0) v) : ℝ≥0∞)⁻¹ := by
  rw [fkPMF, PMF.normalize_apply, G.tsum_fkWeight_coe]
  simp [ENNReal.ofNNReal_finsetProd]

/-- **The Edwards–Sokal joint probability mass function** on `(V(G) → Fin q) × Finset E(G)`,
assigning mass `(∏ e ∈ A, v e) / Z_FK(G; q, v)` when every edge in `A` is monochromatic under `σ`
and `0` otherwise. -/
noncomputable def edwardsSokalPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) : PMF ((V(G) → Fin q) × Finset E(G)) :=
  PMF.normalize
    (fun p ↦ open Classical in
      if ∀ e ∈ p.2, G.IsMonochromaticEdge p.1 e then ∏ e ∈ p.2, (v e : ℝ≥0∞) else 0)
    (by
      rw [G.tsum_edwardsSokalWeight]
      exact ENNReal.coe_ne_zero.mpr (G.fkPartition_pos q v).ne')
    (by
      rw [G.tsum_edwardsSokalWeight]
      exact ENNReal.coe_ne_top)

/-- Point mass of `Graph.edwardsSokalPMF`. -/
@[simp]
theorem edwardsSokalPMF_apply (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) (σ : V(G) → Fin q) (A : Finset E(G)) :
    G.edwardsSokalPMF q v (σ, A) =
      (open Classical in
        if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
        (↑(G.fkPartition (q : ℝ≥0) v) : ℝ≥0∞)⁻¹ := by
  rw [edwardsSokalPMF, PMF.normalize_apply, G.tsum_edwardsSokalWeight]

/-- Every vertex colouring lies in the support of `pottsPMF`. -/
theorem mem_support_pottsPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) (σ : V(G) → Fin q) :
    σ ∈ (G.pottsPMF q v).support := by
  rw [PMF.mem_support_iff, pottsPMF_apply]
  exact mul_ne_zero (ENNReal.coe_ne_zero.mpr (G.pottsWeight_pos σ v).ne')
    (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top)

/-- An edge subset `A` lies in the support of `fkPMF` if and only if every edge in `A` has nonzero
weight. -/
theorem mem_support_fkPMF_iff (G : Graph V E) [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) (A : Finset E(G)) :
    A ∈ (G.fkPMF q v).support ↔ ∀ e ∈ A, v e ≠ 0 := by
  have hq : (q : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [PMF.mem_support_iff, fkPMF_apply, mul_ne_zero_iff, mul_ne_zero_iff, Finset.prod_ne_zero_iff]
  simp [pow_ne_zero _ hq, ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top]

/-- A pair `(σ, A)` lies in the support of `edwardsSokalPMF` if and only if `A` is monochromatic
under `σ` and every edge in `A` has nonzero weight. -/
theorem mem_support_edwardsSokalPMF_iff (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) (σ : V(G) → Fin q) (A : Finset E(G)) :
    (σ, A) ∈ (G.edwardsSokalPMF q v).support ↔
      (∀ e ∈ A, G.IsMonochromaticEdge σ e) ∧ ∀ e ∈ A, v e ≠ 0 := by
  have hZ : (↑(G.fkPartition (q : ℝ≥0) v) : ℝ≥0∞)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  rw [PMF.mem_support_iff, edwardsSokalPMF_apply, mul_ne_zero_iff, and_iff_left hZ]
  split_ifs with hA
  · rw [and_iff_right hA]
    simp [Finset.prod_ne_zero_iff]
  · exact iff_of_false (by simp) fun h ↦ hA h.1

/-- Every colouring paired with the empty edge subset lies in the support of `edwardsSokalPMF`. -/
theorem edwardsSokalPMF_empty_mem_support (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) (σ : V(G) → Fin q) :
    (σ, ∅) ∈ (G.edwardsSokalPMF q v).support :=
  (G.mem_support_edwardsSokalPMF_iff q v σ ∅).mpr ⟨by simp, by simp⟩

/-! ### Both marginals of the Edwards–Sokal coupling -/

/-- **First marginal of `edwardsSokalPMF`:** projecting onto the vertex colouring recovers
`pottsPMF`. -/
@[simp]
theorem map_fst_edwardsSokalPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) :
    (G.edwardsSokalPMF q v).map Prod.fst = G.pottsPMF q v := by
  classical
  have := Fintype.ofFinite E(G)
  rw [PMF.map_fst_eq_iff_fintype]
  intro σ
  rw [pottsPMF_apply, G.pottsPartition_eq_fkPartition]
  simp_rw [edwardsSokalPMF_apply, ← Finset.sum_mul]
  congr 1
  convert G.sum_edwardsSokalWeight_fst σ v

/-- **Second marginal of `edwardsSokalPMF`:** projecting onto the open-edge subset recovers
`fkPMF`. -/
@[simp]
theorem map_snd_edwardsSokalPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) :
    (G.edwardsSokalPMF q v).map Prod.snd = G.fkPMF q v := by
  classical
  have := Fintype.ofFinite V(G)
  rw [PMF.map_snd_eq_iff_fintype]
  intro A
  simp_rw [edwardsSokalPMF_apply, ← Finset.sum_mul, G.sum_edwardsSokalWeight_snd, fkPMF_apply]

/-! ### Conditional distributions, generative binds, posterior filters, and Swendsen–Wang -/

/-- **Conditional cluster distribution given a vertex colouring `σ`:** independent percolation on
monochromatic edges with retention odds `v e` (so retention probability `v e / (1 + v e)`) and
automatic deletion of bichromatic edges. -/
noncomputable def edwardsSokalGivenColoringPMF (G : Graph V E) [Finite E(G)]
    (v : E(G) → ℝ≥0) {γ : Type*} (σ : V(G) → γ) : PMF (Finset E(G)) :=
  PMF.normalize
    (fun A ↦ open Classical in
      if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0)
    (by
      rw [G.tsum_edwardsSokalWeight_fst]
      exact ENNReal.coe_ne_zero.mpr (G.pottsWeight_pos σ v).ne')
    (by
      rw [G.tsum_edwardsSokalWeight_fst]
      exact ENNReal.coe_ne_top)

/-- Point mass of `Graph.edwardsSokalGivenColoringPMF`. -/
@[simp]
theorem edwardsSokalGivenColoringPMF_apply (G : Graph V E) [Finite E(G)]
    (v : E(G) → ℝ≥0) {γ : Type*} (σ : V(G) → γ) (A : Finset E(G)) :
    G.edwardsSokalGivenColoringPMF v σ A =
      (open Classical in
        if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
        (↑(G.pottsWeight σ v) : ℝ≥0∞)⁻¹ := by
  rw [edwardsSokalGivenColoringPMF, PMF.normalize_apply, G.tsum_edwardsSokalWeight_fst]

/-- **Independent Bernoulli-percolation product formula** for `edwardsSokalGivenColoringPMF`: each
monochromatic edge `e` is retained independently with probability `v e / (1 + v e)` and omitted
with probability `1 / (1 + v e)`, while bichromatic edges are retained with probability `0`. -/
theorem edwardsSokalGivenColoringPMF_apply_eq_prod (G : Graph V E) [Fintype E(G)]
    [DecidableEq E(G)] (v : E(G) → ℝ≥0) {γ : Type*} (σ : V(G) → γ) (A : Finset E(G)) :
    G.edwardsSokalGivenColoringPMF v σ A =
      ∏ e : E(G),
        open Classical in
        if G.IsMonochromaticEdge σ e then
          (if e ∈ A then (v e : ℝ≥0∞) else 1) * (1 + (v e : ℝ≥0∞))⁻¹
        else
          if e ∈ A then 0 else 1 := by
  rw [edwardsSokalGivenColoringPMF_apply]
  classical
  have hfactor : ∀ e : E(G),
      (if G.IsMonochromaticEdge σ e then
          (if e ∈ A then (v e : ℝ≥0∞) else 1) * (1 + (v e : ℝ≥0∞))⁻¹
        else if e ∈ A then 0 else 1) =
        (if e ∈ A then (if G.IsMonochromaticEdge σ e then (v e : ℝ≥0∞) else 0) else 1) *
          (1 + if G.IsMonochromaticEdge σ e then (v e : ℝ≥0∞) else 0)⁻¹ := by
    intro e
    split_ifs <;> simp
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, ← ENNReal.prod_inv_distrib (fun _ _ _ _ _ ↦ Or.inl (by simp))]
  congr 1
  · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter,
      Finset.univ_inter]
    split_ifs with hA
    · exact Finset.prod_congr rfl fun e he ↦
        (ite_eq_left_iff.mpr fun h ↦ (h (hA e he)).elim).symm
    · push Not at hA
      obtain ⟨e, heA, hne⟩ := hA
      exact (Finset.prod_eq_zero heA (ite_eq_right_iff.mpr fun h ↦ (hne h).elim)).symm
  · congr 1
    rw [G.pottsWeight_eq_prod_fintype σ v, ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun e _ ↦ ?_
    split_ifs <;> simp

/-- **Conditional colouring distribution given an open-edge subset `A`:** uniform over vertex
colourings `V(G) → Fin q` monochromatic on `A` (equivalently, independent uniform colours on the
connected components of `G.restrict (Subtype.val '' A)`). -/
noncomputable def edwardsSokalGivenClusterPMF (G : Graph V E) [Finite V(G)]
    (q : ℕ) [NeZero q] (A : Finset E(G)) : PMF (V(G) → Fin q) :=
  PMF.normalize
    (fun σ ↦ open Classical in if ∀ e ∈ A, G.IsMonochromaticEdge σ e then 1 else 0)
    (by
      classical
      have := Fintype.ofFinite V(G)
      rw [tsum_fintype, Finset.sum_boole, G.card_monochromatic_eq_pow_componentCount]
      exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (NeZero.ne q)))
    (by
      classical
      have := Fintype.ofFinite V(G)
      rw [tsum_fintype, Finset.sum_boole]
      exact ENNReal.natCast_ne_top _)

/-- Point mass of `Graph.edwardsSokalGivenClusterPMF`. -/
@[simp]
theorem edwardsSokalGivenClusterPMF_apply (G : Graph V E) [Finite V(G)]
    (q : ℕ) [NeZero q] (A : Finset E(G)) (σ : V(G) → Fin q) :
    G.edwardsSokalGivenClusterPMF q A σ =
      open Classical in
      if ∀ e ∈ A, G.IsMonochromaticEdge σ e then
        ((q : ℝ≥0∞) ^ (G.restrict (Subtype.val '' (A : Set E(G)))).componentCount)⁻¹
      else 0 := by
  classical
  have := Fintype.ofFinite V(G)
  rw [edwardsSokalGivenClusterPMF, PMF.normalize_apply, tsum_fintype, Finset.sum_boole,
    G.card_monochromatic_eq_pow_componentCount, Nat.cast_pow]
  split_ifs <;> simp

/-- **Generative `bind` from `pottsPMF`:** sampling `σ ~ pottsPMF` and percolating
`A ~ edwardsSokalGivenColoringPMF v σ` produces `edwardsSokalPMF`. -/
theorem pottsPMF_bind_edwardsSokalGivenColoringPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) :
    (G.pottsPMF q v).bind (fun σ ↦ (G.edwardsSokalGivenColoringPMF v σ).map (σ, ·)) =
      G.edwardsSokalPMF q v := by
  classical
  ext ⟨σ, A⟩
  rw [PMF.bind_apply, tsum_eq_single σ]
  · rw [PMF.map_apply, tsum_eq_single A]
    · simp only [ite_true, pottsPMF_apply, edwardsSokalGivenColoringPMF_apply,
        edwardsSokalPMF_apply, G.pottsPartition_eq_fkPartition]
      let w : ℝ≥0 := G.pottsWeight σ v
      let Z : ℝ≥0 := G.fkPartition (q : ℝ≥0) v
      have hw0 : (w : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (G.pottsWeight_pos σ v).ne'
      have hwt : (w : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
      change (w : ℝ≥0∞) * (Z : ℝ≥0∞)⁻¹ *
          ((if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
            (w : ℝ≥0∞)⁻¹) =
        (if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
          (Z : ℝ≥0∞)⁻¹
      calc
        (w : ℝ≥0∞) * (Z : ℝ≥0∞)⁻¹ *
            ((if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
              (w : ℝ≥0∞)⁻¹) =
          ((w : ℝ≥0∞) * (w : ℝ≥0∞)⁻¹) *
            ((if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
              (Z : ℝ≥0∞)⁻¹) := by ring
        _ = (if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
              (Z : ℝ≥0∞)⁻¹ := by rw [ENNReal.mul_inv_cancel hw0 hwt, one_mul]
    · intro B hBA
      simp [hBA.symm]
  · intro σ' hσ'
    rw [PMF.map_apply]
    simp [hσ'.symm]

/-- **Generative `bind` from `fkPMF`:** sampling `A ~ fkPMF` and colouring components
`σ ~ edwardsSokalGivenClusterPMF q A` produces `edwardsSokalPMF`. -/
theorem fkPMF_bind_edwardsSokalGivenClusterPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) :
    (G.fkPMF q v).bind (fun A ↦ (G.edwardsSokalGivenClusterPMF q A).map (·, A)) =
      G.edwardsSokalPMF q v := by
  classical
  ext ⟨σ, A⟩
  rw [PMF.bind_apply, tsum_eq_single A]
  · rw [PMF.map_apply, tsum_eq_single σ]
    · simp only [ite_true, fkPMF_apply, edwardsSokalGivenClusterPMF_apply, edwardsSokalPMF_apply]
      let c : ℝ≥0∞ := (q : ℝ≥0∞) ^ (G.restrict (Subtype.val '' (A : Set E(G)))).componentCount
      let Z : ℝ≥0 := G.fkPartition (q : ℝ≥0) v
      have hc0 : c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne q))
      have hct : c ≠ ∞ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top q)
      by_cases hA : ∀ e ∈ A, G.IsMonochromaticEdge σ e
      · rw [ite_eq_left_iff.mpr fun h ↦ (h hA).elim, ite_eq_left_iff.mpr fun h ↦ (h hA).elim]
        change (c * ∏ e ∈ A, (v e : ℝ≥0∞)) * (Z : ℝ≥0∞)⁻¹ * c⁻¹ =
          (∏ e ∈ A, (v e : ℝ≥0∞)) * (Z : ℝ≥0∞)⁻¹
        calc
          (c * ∏ e ∈ A, (v e : ℝ≥0∞)) * (Z : ℝ≥0∞)⁻¹ * c⁻¹ =
            (c * c⁻¹) * ((∏ e ∈ A, (v e : ℝ≥0∞)) * (Z : ℝ≥0∞)⁻¹) := by ring
          _ = (∏ e ∈ A, (v e : ℝ≥0∞)) * (Z : ℝ≥0∞)⁻¹ := by
            rw [ENNReal.mul_inv_cancel hc0 hct, one_mul]
      · rw [ite_eq_right_iff.mpr fun h ↦ (hA h).elim, ite_eq_right_iff.mpr fun h ↦ (hA h).elim]
        simp
    · intro σ' hσ'
      simp [hσ'.symm]
  · intro B hBA
    rw [PMF.map_apply]
    simp [hBA.symm]

private theorem tsum_indicator_fst_edwardsSokalPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) (σ : V(G) → Fin q) :
    (∑' p, ({p : (V(G) → Fin q) × Finset E(G) | p.1 = σ} : Set _).indicator
      (G.edwardsSokalPMF q v) p) = G.pottsPMF q v σ := by
  classical
  have := Fintype.ofFinite V(G)
  have := Fintype.ofFinite E(G)
  rw [tsum_fintype, Fintype.sum_prod_type, Finset.sum_eq_single σ]
  · have hind : ∀ B : Finset E(G),
        ({p : (V(G) → Fin q) × Finset E(G) | p.1 = σ} : Set _).indicator
          (G.edwardsSokalPMF q v) (σ, B) = G.edwardsSokalPMF q v (σ, B) :=
      fun _ ↦ Set.indicator_of_mem rfl _
    simp_rw [hind]
    rw [← G.map_fst_edwardsSokalPMF q v, PMF.map_fst_apply_fintype]
  · intro σ' _ hσ'
    refine Finset.sum_eq_zero fun B _ ↦ Set.indicator_of_notMem ?_ _
    simpa using hσ'
  · intro h
    exact (h (Finset.mem_univ σ)).elim

private theorem tsum_indicator_snd_edwardsSokalPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) (A : Finset E(G)) :
    (∑' p, ({p : (V(G) → Fin q) × Finset E(G) | p.2 = A} : Set _).indicator
      (G.edwardsSokalPMF q v) p) = G.fkPMF q v A := by
  classical
  have := Fintype.ofFinite V(G)
  have := Fintype.ofFinite E(G)
  rw [tsum_fintype, Fintype.sum_prod_type_right, Finset.sum_eq_single A]
  · have hind : ∀ σ : V(G) → Fin q,
        ({p : (V(G) → Fin q) × Finset E(G) | p.2 = A} : Set _).indicator
          (G.edwardsSokalPMF q v) (σ, A) = G.edwardsSokalPMF q v (σ, A) :=
      fun _ ↦ Set.indicator_of_mem rfl _
    simp_rw [hind]
    rw [← G.map_snd_edwardsSokalPMF q v, PMF.map_snd_apply_fintype]
  · intro B _ hBA
    refine Finset.sum_eq_zero fun σ _ ↦ Set.indicator_of_notMem ?_ _
    simpa using hBA
  · intro h
    exact (h (Finset.mem_univ A)).elim

/-- **Posterior conditioning of `edwardsSokalPMF` on a vertex colouring `σ`:** filtering the joint
law on `{p | p.1 = σ}` and projecting onto the cluster coordinate yields
`edwardsSokalGivenColoringPMF v σ`. -/
theorem map_snd_filter_fst_edwardsSokalPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) (σ : V(G) → Fin q) :
    ((G.edwardsSokalPMF q v).filter {p | p.1 = σ}
      ⟨(σ, ∅), rfl, G.edwardsSokalPMF_empty_mem_support q v σ⟩).map Prod.snd =
      G.edwardsSokalGivenColoringPMF v σ := by
  classical
  have := Fintype.ofFinite V(G)
  ext A
  rw [PMF.map_snd_apply_fintype, Finset.sum_eq_single σ]
  · rw [PMF.filter_apply, G.tsum_indicator_fst_edwardsSokalPMF, Set.indicator_of_mem rfl,
      edwardsSokalPMF_apply, pottsPMF_apply, G.pottsPartition_eq_fkPartition,
      edwardsSokalGivenColoringPMF_apply, ENNReal.mul_inv]
    · let w : ℝ≥0 := G.pottsWeight σ v
      let Z : ℝ≥0 := G.fkPartition (q : ℝ≥0) v
      have hZ0 : (Z : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (G.fkPartition_pos q v).ne'
      have hZt : (Z : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
      rw [inv_inv]
      change (if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
          (Z : ℝ≥0∞)⁻¹ * ((w : ℝ≥0∞)⁻¹ * (Z : ℝ≥0∞)) =
        (if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
          (w : ℝ≥0∞)⁻¹
      calc
        (if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
            (Z : ℝ≥0∞)⁻¹ * ((w : ℝ≥0∞)⁻¹ * (Z : ℝ≥0∞)) =
          ((Z : ℝ≥0∞) * (Z : ℝ≥0∞)⁻¹) *
            ((if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
              (w : ℝ≥0∞)⁻¹) := by ring
        _ = (if ∀ e ∈ A, G.IsMonochromaticEdge σ e then ∏ e ∈ A, (v e : ℝ≥0∞) else 0) *
              (w : ℝ≥0∞)⁻¹ := by rw [ENNReal.mul_inv_cancel hZ0 hZt, one_mul]
    · exact Or.inl (ENNReal.coe_ne_zero.mpr (G.pottsWeight_pos σ v).ne')
    · exact Or.inl ENNReal.coe_ne_top
  · intro σ' _ hσ'
    exact PMF.filter_apply_eq_zero_of_notMem _ hσ'
  · intro h
    exact (h (Finset.mem_univ σ)).elim

/-- **Posterior conditioning of `edwardsSokalPMF` on an open-edge subset `A`:** whenever `A` has
positive probability under `fkPMF`, filtering the joint law on `{p | p.2 = A}` and projecting onto
the colouring coordinate yields `edwardsSokalGivenClusterPMF q A`. -/
theorem map_fst_filter_snd_edwardsSokalPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) {A : Finset E(G)}
    (hA : ∃ p ∈ ({p : (V(G) → Fin q) × Finset E(G) | p.2 = A} : Set _),
      p ∈ (G.edwardsSokalPMF q v).support) :
    ((G.edwardsSokalPMF q v).filter {p | p.2 = A} hA).map Prod.fst =
      G.edwardsSokalGivenClusterPMF q A := by
  classical
  have := Fintype.ofFinite E(G)
  have hfk0 : G.fkPMF q v A ≠ 0 := by
    obtain ⟨⟨σ, B⟩, rfl, hps⟩ := hA
    exact (PMF.mem_support_iff _ _).mp
      ((G.mem_support_fkPMF_iff q v B).mpr ((G.mem_support_edwardsSokalPMF_iff q v σ B).mp hps).2)
  ext σ
  rw [PMF.map_fst_apply_fintype, Finset.sum_eq_single A]
  · rw [PMF.filter_apply, G.tsum_indicator_snd_edwardsSokalPMF, Set.indicator_of_mem rfl,
      edwardsSokalPMF_apply, edwardsSokalGivenClusterPMF_apply]
    split_ifs with hm
    · rw [fkPMF_apply] at hfk0 ⊢
      let c : ℝ≥0∞ := (q : ℝ≥0∞) ^ (G.restrict (Subtype.val '' (A : Set E(G)))).componentCount
      let Z : ℝ≥0 := G.fkPartition (q : ℝ≥0) v
      let w : ℝ≥0∞ := (∏ e ∈ A, (v e : ℝ≥0∞)) * (Z : ℝ≥0∞)⁻¹
      have hcw : (c * ∏ e ∈ A, (v e : ℝ≥0∞)) * (Z : ℝ≥0∞)⁻¹ = c * w := mul_assoc _ _ _
      change (c * ∏ e ∈ A, (v e : ℝ≥0∞)) * (Z : ℝ≥0∞)⁻¹ ≠ 0 at hfk0
      rw [hcw] at hfk0
      have hw0 : w ≠ 0 := right_ne_zero_of_mul hfk0
      have hct : c ≠ ∞ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top q)
      have hwt : w ≠ ∞ := ENNReal.mul_ne_top
        (ENNReal.prod_ne_top fun _ _ ↦ ENNReal.coe_ne_top)
        (ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr (G.fkPartition_pos q v).ne'))
      change w * ((c * ∏ e ∈ A, (v e : ℝ≥0∞)) * (Z : ℝ≥0∞)⁻¹)⁻¹ = c⁻¹
      rw [hcw, ENNReal.mul_inv (Or.inr hwt) (Or.inl hct)]
      calc
        w * (c⁻¹ * w⁻¹) = (w * w⁻¹) * c⁻¹ := by ring
        _ = c⁻¹ := by rw [ENNReal.mul_inv_cancel hw0 hwt, one_mul]
    · simp
  · intro B _ hBA
    exact PMF.filter_apply_eq_zero_of_notMem _ hBA
  · intro h
    exact (h (Finset.mem_univ A)).elim

/-- **Swendsen–Wang stationarity for `pottsPMF`:** one full cycle of monochromatic bond percolation
followed by uniform component recolouring leaves `pottsPMF` invariant. -/
theorem swendsenWang_pottsPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) :
    (G.pottsPMF q v).bind (fun σ ↦
        (G.edwardsSokalGivenColoringPMF v σ).bind (G.edwardsSokalGivenClusterPMF q)) =
      G.pottsPMF q v := by
  calc
    (G.pottsPMF q v).bind (fun σ ↦
        (G.edwardsSokalGivenColoringPMF v σ).bind (G.edwardsSokalGivenClusterPMF q))
      = (((G.pottsPMF q v).bind fun σ ↦
          (G.edwardsSokalGivenColoringPMF v σ).map (σ, ·)).map Prod.snd).bind
          (G.edwardsSokalGivenClusterPMF q) := by
          simp [PMF.map_bind, PMF.map_comp, Function.comp_def, ← Function.id_def, PMF.map_id]
    _ = (G.fkPMF q v).bind (G.edwardsSokalGivenClusterPMF q) := by
          rw [G.pottsPMF_bind_edwardsSokalGivenColoringPMF, G.map_snd_edwardsSokalPMF]
    _ = ((G.fkPMF q v).bind fun A ↦
          (G.edwardsSokalGivenClusterPMF q A).map (·, A)).map Prod.fst := by
          simp [PMF.map_bind, PMF.map_comp, Function.comp_def, ← Function.id_def, PMF.map_id]
    _ = G.pottsPMF q v := by
          rw [G.fkPMF_bind_edwardsSokalGivenClusterPMF, G.map_fst_edwardsSokalPMF]

/-- **Swendsen–Wang stationarity for `fkPMF`:** one full cycle of uniform component colouring
followed by monochromatic bond percolation leaves `fkPMF` invariant. -/
theorem swendsenWang_fkPMF (G : Graph V E) [Finite V(G)] [Finite E(G)]
    (q : ℕ) [NeZero q] (v : E(G) → ℝ≥0) :
    (G.fkPMF q v).bind (fun A ↦
        (G.edwardsSokalGivenClusterPMF q A).bind (G.edwardsSokalGivenColoringPMF v)) =
      G.fkPMF q v := by
  calc
    (G.fkPMF q v).bind (fun A ↦
        (G.edwardsSokalGivenClusterPMF q A).bind (G.edwardsSokalGivenColoringPMF v))
      = (((G.fkPMF q v).bind fun A ↦
          (G.edwardsSokalGivenClusterPMF q A).map (·, A)).map Prod.fst).bind
          (G.edwardsSokalGivenColoringPMF v) := by
          simp [PMF.map_bind, PMF.map_comp, Function.comp_def, ← Function.id_def, PMF.map_id]
    _ = (G.pottsPMF q v).bind (G.edwardsSokalGivenColoringPMF v) := by
          rw [G.fkPMF_bind_edwardsSokalGivenClusterPMF, G.map_fst_edwardsSokalPMF]
    _ = ((G.pottsPMF q v).bind fun σ ↦
          (G.edwardsSokalGivenColoringPMF v σ).map (σ, ·)).map Prod.snd := by
          simp [PMF.map_bind, PMF.map_comp, Function.comp_def, ← Function.id_def, PMF.map_id]
    _ = G.fkPMF q v := by
          rw [G.pottsPMF_bind_edwardsSokalGivenColoringPMF, G.map_snd_edwardsSokalPMF]

end Graph

end
