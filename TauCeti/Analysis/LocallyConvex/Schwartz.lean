/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
import TauCeti.Topology.Algebra.OpenMapping.Converse
import TauCeti.Topology.Algebra.OpenMapping.Henkel

/-!
# Schwartz's compact-perturbation finiteness theorem for Fréchet spaces

Laurent Schwartz's finiteness theorem (1953) states that if `g : E →L[𝕜] F` is a surjective
continuous linear map between Fréchet spaces (over `ℝ` or `ℂ`, or more generally any topological
ring `𝕜` carrying a continuous scalar action of `ℝ`) and `h : E →L[𝕜] F` is a compact operator
(`IsCompactOperator h`), then `g + h` has closed range of finite codimension and is open onto its
range (a strict morphism). No finite-dimensionality or complementability of `ker g` is assumed.

The theorem holds in greater generality than metrisable Fréchet spaces:

* The source `E` need only be a complete first-countable uniform additive group carrying a locally
  convex `ℝ`-vector space structure (in particular, neither Hausdorffness nor metrisability of `E`
  is needed).
* The target `F` need only be a `T0` Baire topological `𝕜`-module (in particular, neither a
  uniform structure, nor completeness, nor first countability, nor local convexity of `F` is
  needed). The complete first-countable uniform target forms (covering Fréchet spaces) follow via
  `IsUniformAddGroup.uniformity_countably_generated` and `BaireSpace.of_completelyPseudoMetrizable`.

## Proof outline

Everything reduces by restriction of scalars to `𝕜 = ℝ`, where `u := g + h`:

1. By the open mapping theorem (`ContinuousLinearMap.isOpenMap_of_hasZeroSequenceOfUnits`), `g` is
   open. Compactness of `h` gives an open absolutely convex neighbourhood `V` of `0` in `E` with
   `K := closure (h '' V)` compact.
2. For any open absolutely convex neighbourhood `U ⊆ V` of `0`, covering `K` by finitely many
   translates of `(2⁻¹ : ℝ) • (g '' U)` and iterating the resulting approximation yields a finite
   set `s : Finset F` and a compact set `L ⊆ Submodule.span ℝ (s : Set F)` such that
   `g '' U ⊆ closure (u '' ((2 : ℝ) • U)) + L`.
3. Taking `U = V` already shows that `Z := u.range.topologicalClosure` has finite codimension in
   `F`.
4. Passing to the corestriction `u_Z : E →L[ℝ] Z`, for every `U' ∈ 𝓝 (0 : E)` we find `U ⊆ V` with
   `(2 : ℝ) • U ⊆ U'` and decompose the finite-dimensional span of `L ∩ Z` inside `Z` relative to
   the dense subspace `Z₀ := Submodule.span ℝ A_Z` spanned by
   `A_Z := closure (u_Z '' ((2 : ℝ) • U))`. A finite-dimensional compactness bound absorbs the
   `Z₀`-component of `L ∩ Z` into a multiple of `A_Z`, and density of `Z₀` kills the complementary
   finite-dimensional summand, proving `closure (u_Z '' U') ∈ 𝓝 (0 : Z)`.
5. `TauCeti.isOpenMap_of_closure_image_mem_nhds` concludes that `u_Z` is open, hence surjective by
   `LinearMap.surjective_of_isOpenMap`. Therefore `u.range = Z` is closed, `u.rangeRestrict` is
   open, and `F ⧸ u.range` is finitely generated over `ℝ` (hence also over `𝕜`).

## Main results

* `ContinuousLinearMap.isOpenMap_rangeRestrict_add_of_isCompactOperator_of_baireSpace`: `g + h` is
  open onto its range for a `T0` Baire target.
* `ContinuousLinearMap.isClosed_range_add_of_isCompactOperator_of_baireSpace`: `(g + h).range` is
  closed for a `T0` Baire target.
* `ContinuousLinearMap.finite_quotient_range_add_of_isCompactOperator_of_baireSpace`:
  `F ⧸ (g + h).range` is a finitely generated `𝕜`-module (hence finite-dimensional when `𝕜` is a
  division ring, e.g. `ℝ` or `ℂ`) for a `T0` Baire target.
* `ContinuousLinearMap.isOpenMap_rangeRestrict_add_of_isCompactOperator_of_completeSpace`,
  `ContinuousLinearMap.isClosed_range_add_of_isCompactOperator_of_completeSpace`, and
  `ContinuousLinearMap.finite_quotient_range_add_of_isCompactOperator_of_completeSpace`:
  specialisations to complete first-countable uniform targets (Fréchet spaces).

## References

* L. Schwartz, *Homomorphismes et applications complètement continues*,
  C. R. Acad. Sci. Paris **236** (1953), 2472–2473.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter IX, Theorems 1.8–1.9.
-/

public section

open Filter Set Topology
open scoped Pointwise Uniformity

namespace ContinuousLinearMap

section RealCore

/-- Any finite `ℝ`-linear combination of elements of an absolutely convex set containing `0` whose
coefficient `ℓ¹`-sum is at most `S > 0` lies in `S • A`. -/
private lemma sum_smul_mem_smul_of_absConvex {ι M : Type*} [AddCommGroup M] [Module ℝ M]
    {A : Set M} (h0 : (0 : M) ∈ A) (hA : AbsConvex ℝ A) {s : Finset ι}
    {c : ι → ℝ} {x : ι → M} (hx : ∀ i ∈ s, x i ∈ A) {S : ℝ} (hS : 0 < S)
    (hsum : ∑ i ∈ s, |c i| ≤ S) :
    (∑ i ∈ s, c i • x i) ∈ S • A := by
  let t : Finset (Option ι) :=
    Finset.cons none (s.map ⟨some, Option.some_injective _⟩) (by simp)
  let w : Option ι → ℝ := fun o ↦
    match o with
    | none => 1 - (∑ i ∈ s, |c i|) / S
    | some i => |c i| / S
  let y : Option ι → M := fun o ↦
    match o with
    | none => 0
    | some i => (if 0 ≤ c i then (1 : ℝ) else -1) • x i
  have hw_nonneg : ∀ o ∈ t, 0 ≤ w o := by
    intro o ho
    rcases Finset.mem_cons.mp ho with rfl | ho'
    · exact sub_nonneg.mpr ((div_le_one hS).mpr hsum)
    · rcases Finset.mem_map.mp ho' with ⟨i, _, rfl⟩
      exact div_nonneg (abs_nonneg _) hS.le
  have hw_sum : ∑ o ∈ t, w o = 1 := by
    rw [Finset.sum_cons, Finset.sum_map]
    simp only [w, Function.Embedding.coeFn_mk, div_eq_mul_inv, ← Finset.sum_mul]
    ring
  have hy_mem : ∀ o ∈ t, y o ∈ A := by
    intro o ho
    rcases Finset.mem_cons.mp ho with rfl | ho'
    · exact h0
    · rcases Finset.mem_map.mp ho' with ⟨i, hi, rfl⟩
      have hnorm : ‖(if 0 ≤ c i then (1 : ℝ) else -1)‖ ≤ 1 := by
        split_ifs <;> norm_num
      exact hA.1 _ hnorm (Set.smul_mem_smul_set (hx i hi))
  have hcomb : ∑ o ∈ t, w o • y o ∈ A := hA.2.sum_mem hw_nonneg hw_sum hy_mem
  have heq : ∑ o ∈ t, w o • y o = S⁻¹ • ∑ i ∈ s, c i • x i := by
    rw [Finset.sum_cons, Finset.sum_map, Finset.smul_sum]
    simp only [w, y, smul_zero, zero_add, Function.Embedding.coeFn_mk, smul_smul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    by_cases hci : 0 ≤ c i
    · simp only [hci, ↓reduceIte, abs_of_nonneg hci]
      ring
    · simp only [hci, ↓reduceIte, abs_of_neg (lt_of_not_ge hci)]
      ring
  rw [heq] at hcomb
  exact ⟨S⁻¹ • ∑ i ∈ s, c i • x i, hcomb, smul_inv_smul₀ hS.ne' _⟩

/-- Every element of the `ℝ`-linear span of an absolutely convex set containing `0` lies in a
positive scalar multiple of that set. -/
private lemma exists_pos_smul_mem_of_mem_span_absConvex {M : Type*} [AddCommGroup M] [Module ℝ M]
    {A : Set M} (h0 : (0 : M) ∈ A) (hA : AbsConvex ℝ A) {x : M}
    (hx : x ∈ Submodule.span ℝ A) :
    ∃ r : ℝ, 0 < r ∧ x ∈ r • A := by
  induction hx using Submodule.span_induction with
  | mem a ha => exact ⟨1, one_pos, by simpa using ha⟩
  | zero => exact ⟨1, one_pos, by simpa using h0⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨r₁, hr₁, a₁, ha₁, rfl⟩ := ihx
    obtain ⟨r₂, hr₂, a₂, ha₂, rfl⟩ := ihy
    have hr : 0 < r₁ + r₂ := add_pos hr₁ hr₂
    refine ⟨r₁ + r₂, hr, (r₁ / (r₁ + r₂)) • a₁ + (r₂ / (r₁ + r₂)) • a₂,
      hA.2 ha₁ ha₂ (div_nonneg hr₁.le hr.le) (div_nonneg hr₂.le hr.le)
        (by rw [← add_div, div_self hr.ne']), ?_⟩
    dsimp only
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hr.ne', mul_div_cancel₀ _ hr.ne']
  | smul c x _ ihx =>
    obtain ⟨r, hr, a, ha, rfl⟩ := ihx
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨1, one_pos, by simpa using h0⟩
    · refine ⟨|c| * r, mul_pos (abs_pos.mpr hc) hr, (c / |c|) • a, ?_, ?_⟩
      · have hnorm : ‖c / |c|‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_div, abs_abs, div_self (abs_pos.mpr hc).ne']
        exact hA.1 _ hnorm (Set.smul_mem_smul_set ha)
      · dsimp only
        rw [smul_smul, smul_smul]
        congr 1
        field_simp

/-- Key compact-perturbation approximation step: for an open map `g` and compact
`K := closure (h '' V)`, every open absolutely convex `U ⊆ V` satisfies
`g '' U ⊆ closure ((g + h) '' (2 • U)) + L` for a compact subset `L` of a finitely generated
`ℝ`-subspace of `F`. -/
private lemma image_subset_closure_image_two_smul_add_compact
    {E F : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module ℝ F] [ContinuousSMul ℝ F]
    (g h : E →L[ℝ] F) (hg_open : IsOpenMap g)
    {V : Set E} (hK : IsCompact (closure (h '' V)))
    {U : Set E} (hU0 : (0 : E) ∈ U) (hUopen : IsOpen U) (hUac : AbsConvex ℝ U) (hUV : U ⊆ V) :
    ∃ (s : Finset F) (L : Set F),
      IsCompact L ∧ L ⊆ (Submodule.span ℝ (s : Set F) : Set F) ∧
        g '' U ⊆ closure ((g + h) '' ((2 : ℝ) • U)) + L := by
  classical
  let u : E →L[ℝ] F := g + h
  let K : Set F := closure (h '' V)
  let W : Set F := (2⁻¹ : ℝ) • (g '' U)
  have hWopen : IsOpen W := (hg_open U hUopen).smul₀ (by norm_num : (2⁻¹ : ℝ) ≠ 0)
  have hW0 : (0 : F) ∈ W := ⟨0, ⟨0, hU0, map_zero g⟩, smul_zero _⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun y : F ↦ y +ᵥ W) (fun y ↦ hWopen.vadd y)
    (fun y _ ↦ Set.mem_iUnion.mpr ⟨y, 0, hW0, add_zero y⟩)
  let box : Set (s → ℝ) := Set.univ.pi fun _ : s ↦ Set.Icc (-2 : ℝ) 2
  let lin : (s → ℝ) → F := fun c ↦ ∑ y : s, c y • (y : F)
  let L : Set F := lin '' box
  have hL_comp : IsCompact L :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).image (by fun_prop)
  have hL_span : L ⊆ (Submodule.span ℝ (s : Set F) : Set F) := by
    rintro _ ⟨c, _, rfl⟩
    exact Submodule.sum_mem _ fun y _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span y.2)
  refine ⟨s, L, hL_comp, hL_span, fun z hz ↦ ?_⟩
  -- For any `x ∈ U`, `h x ∈ K` is approximated modulo `s` by `-(2⁻¹) • g x'` with `x' ∈ U`.
  have hstep : ∀ x : { x : E // x ∈ U },
      ∃ p : s × { x : E // x ∈ U }, h x.1 + (2⁻¹ : ℝ) • g p.2.1 = (p.1 : F) := by
    intro x
    have hxK : h x.1 ∈ K := subset_closure ⟨x.1, hUV x.2, rfl⟩
    have hxCov := hs hxK
    simp only [Set.mem_iUnion, exists_prop] at hxCov
    obtain ⟨y, hy, w, ⟨_, ⟨x', hx', rfl⟩, rfl⟩, hyw⟩ := hxCov
    have hneg : -x' ∈ U := hUac.1.neg_mem_iff.mpr hx'
    refine ⟨(⟨y, hy⟩, ⟨-x', hneg⟩), ?_⟩
    rw [map_neg, smul_neg]
    have hyw' : y + (2⁻¹ : ℝ) • g x' = h x.1 := hyw
    rw [← hyw']
    abel
  let step : { x : E // x ∈ U } → s × { x : E // x ∈ U } := fun x ↦ Classical.choose (hstep x)
  have hstep_spec : ∀ x, h x.1 + (2⁻¹ : ℝ) • g (step x).2.1 = ((step x).1 : F) :=
    fun x ↦ Classical.choose_spec (hstep x)
  obtain ⟨x₀, hx₀U, hx₀z⟩ := hz
  let seq : ℕ → { x : E // x ∈ U } := Nat.rec ⟨x₀, hx₀U⟩ fun _ prev ↦ (step prev).2
  let pick : ℕ → s := fun n ↦ (step (seq n)).1
  have hrec : ∀ n, h (seq n).1 + (2⁻¹ : ℝ) • g (seq (n + 1)).1 = (pick n : F) :=
    fun n ↦ hstep_spec (seq n)
  -- Telescoping identity for the partial sums `∑ k < n + 1, (2⁻¹)^k • u (seq k)`.
  have htele : ∀ n : ℕ,
      u (∑ k ∈ Finset.range (n + 1), (2⁻¹ : ℝ) ^ k • (seq k).1) =
        z + (∑ k ∈ Finset.range n, (2⁻¹ : ℝ) ^ k • (pick k : F)) +
          (2⁻¹ : ℝ) ^ n • h (seq n).1 := by
    intro n
    induction n with
    | zero =>
      simp [u, seq, hx₀z]
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add, map_smul, ih, Finset.sum_range_succ]
      have hu_succ : u (seq (n + 1)).1 = g (seq (n + 1)).1 + h (seq (n + 1)).1 := rfl
      rw [hu_succ, smul_add]
      have hg_step : (2⁻¹ : ℝ) ^ (n + 1) • g (seq (n + 1)).1 =
          (2⁻¹ : ℝ) ^ n • ((2⁻¹ : ℝ) • g (seq (n + 1)).1) := by
        rw [pow_succ, mul_smul]
      rw [hg_step]
      calc
        z + ∑ k ∈ Finset.range n, (2⁻¹ : ℝ) ^ k • (pick k : F) + (2⁻¹ : ℝ) ^ n • h (seq n).1 +
            ((2⁻¹ : ℝ) ^ n • (2⁻¹ : ℝ) • g (seq (n + 1)).1 +
              (2⁻¹ : ℝ) ^ (n + 1) • h (seq (n + 1)).1)
          = z + ∑ k ∈ Finset.range n, (2⁻¹ : ℝ) ^ k • (pick k : F) +
              (2⁻¹ : ℝ) ^ n • (h (seq n).1 + (2⁻¹ : ℝ) • g (seq (n + 1)).1) +
              (2⁻¹ : ℝ) ^ (n + 1) • h (seq (n + 1)).1 := by
            rw [smul_add]
            abel
        _ = z + (∑ k ∈ Finset.range n, (2⁻¹ : ℝ) ^ k • (pick k : F) +
              (2⁻¹ : ℝ) ^ n • (pick n : F)) +
              (2⁻¹ : ℝ) ^ (n + 1) • h (seq (n + 1)).1 := by
            rw [hrec n]
            abel
  -- Each partial sum `∑ k < n + 1, (2⁻¹)^k • seq k` lies in `2 • U`.
  have hgeom : ∀ m : ℕ, ∑ k ∈ Finset.range m, (2⁻¹ : ℝ) ^ k ≤ 2 := fun m ↦ by
    rw [geom_sum_eq (by norm_num : (2⁻¹ : ℝ) ≠ 1)]
    have hpow : (0 : ℝ) ≤ (2⁻¹ : ℝ) ^ m := by positivity
    have hring : ((2⁻¹ : ℝ) ^ m - 1) / (2⁻¹ - 1) = 2 - 2 * (2⁻¹ : ℝ) ^ m := by ring
    linarith
  have hS_mem : ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1), (2⁻¹ : ℝ) ^ k • (seq k).1) ∈ (2 : ℝ) • U := fun n ↦
    sum_smul_mem_smul_of_absConvex hU0 hUac (fun k _ ↦ (seq k).2) two_pos <| by
      simpa only [abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) _)] using hgeom (n + 1)
  -- The negated error combination `∑ k < n, -(2⁻¹)^k • pick k` lies in the compact set `L`.
  have hl_mem : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, (-((2⁻¹ : ℝ) ^ k)) • (pick k : F)) ∈ L := by
    intro n
    let c : s → ℝ := fun y ↦ ∑ k ∈ (Finset.range n).filter (fun k ↦ pick k = y), -((2⁻¹ : ℝ) ^ k)
    refine ⟨c, fun y _ ↦ ⟨?_, ?_⟩, ?_⟩
    · have hle : ∑ k ∈ (Finset.range n).filter (fun k ↦ pick k = y), (2⁻¹ : ℝ) ^ k ≤ 2 :=
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ ↦ by positivity)).trans (hgeom n)
      have hneg : c y = -∑ k ∈ (Finset.range n).filter (fun k ↦ pick k = y), (2⁻¹ : ℝ) ^ k := by
        simp [c]
      linarith
    · have hnonpos : c y ≤ 0 :=
        Finset.sum_nonpos fun k _ ↦ neg_nonpos.mpr (by positivity)
      linarith
    · simp only [lin, c]
      rw [← Finset.sum_fiberwise (Finset.range n) pick
        (fun k ↦ (-((2⁻¹ : ℝ) ^ k)) • (pick k : F))]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [(Finset.mem_filter.mp hk).2]
  -- Hence `z + (2⁻¹)^n • h (seq n) ∈ u '' (2 • U) + L`, and the remainder tends to `0`.
  have hmem_add : ∀ n : ℕ,
      z + (2⁻¹ : ℝ) ^ n • h (seq n).1 ∈ u '' ((2 : ℝ) • U) + L := by
    intro n
    refine ⟨u (∑ k ∈ Finset.range (n + 1), (2⁻¹ : ℝ) ^ k • (seq k).1), ⟨_, hS_mem n, rfl⟩,
      ∑ k ∈ Finset.range n, (-((2⁻¹ : ℝ) ^ k)) • (pick k : F), hl_mem n, ?_⟩
    rw [htele n]
    simp only [neg_smul, Finset.sum_neg_distrib]
    abel
  have hrem_zero : Tendsto (fun n : ℕ ↦ (2⁻¹ : ℝ) ^ n • h (seq n).1) atTop (𝓝 (0 : F)) :=
    (hK.isVonNBounded ℝ).smul_tendsto_zero
      (Eventually.of_forall fun n ↦ subset_closure ⟨(seq n).1, hUV (seq n).2, rfl⟩)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have htend : Tendsto (fun n : ℕ ↦ z + (2⁻¹ : ℝ) ^ n • h (seq n).1) atTop (𝓝 z) := by
    simpa only [add_zero] using tendsto_const_nhds.add hrem_zero
  have hz_cl : z ∈ closure (u '' ((2 : ℝ) • U) + L) :=
    mem_closure_of_tendsto htend (Eventually.of_forall hmem_add)
  have hclosed : IsClosed (closure (u '' ((2 : ℝ) • U)) + L) :=
    isClosed_closure.add_right_of_isCompact hL_comp
  exact closure_minimal (Set.add_subset_add_right subset_closure) hclosed hz_cl

/-- A compact subset of a finite-dimensional subspace contained in `Submodule.span ℝ A` (for
absolutely convex `A` containing `0`) is absorbed by a positive scalar multiple of `A`. -/
private lemma exists_pos_smul_subset_of_isCompact_finiteDimensional
    {Z : Type*} [AddCommGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [T0Space Z]
    [Module ℝ Z] [ContinuousSMul ℝ Z]
    {A : Set Z} (hA0 : (0 : Z) ∈ A) (hAac : AbsConvex ℝ A)
    {W₁ : Submodule ℝ Z} [FiniteDimensional ℝ W₁] (hW₁ : W₁ ≤ Submodule.span ℝ A)
    {K₁ : Set Z} (hK₁ : IsCompact K₁) (hK₁W : K₁ ⊆ (W₁ : Set Z)) :
    ∃ S : ℝ, 0 < S ∧ K₁ ⊆ S • A := by
  have : Module.Free ℝ W₁ := Module.Free.of_divisionRing ℝ W₁
  let b := Module.finBasis ℝ W₁
  have hbasis_abs : ∀ i, ∃ r : ℝ, 0 < r ∧ (b i : Z) ∈ r • A := fun i ↦
    exists_pos_smul_mem_of_mem_span_absConvex hA0 hAac (hW₁ (b i).2)
  choose r hr_pos hr_mem using hbasis_abs
  have hK₁_sub : IsCompact (W₁.subtype ⁻¹' K₁) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK₁ <| by
      simpa [Submodule.coe_subtype, Subtype.range_coe] using hK₁W
  have hcoord_bdd : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ W₁.subtype ⁻¹' K₁, |b.repr v i| ≤ C := by
    intro i
    have hcont_i : Continuous (fun v : W₁ ↦ |b.coord i v|) :=
      continuous_abs.comp
        (LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) (E := W₁) (F' := ℝ) (b.coord i))
    obtain ⟨C, hC⟩ := (hK₁_sub.image hcont_i).isBounded.subset_closedBall 0
    refine ⟨max C 0, le_max_right _ _, fun v hv ↦ ?_⟩
    have hmem : |b.coord i v| ∈ Metric.closedBall (0 : ℝ) C := hC ⟨v, hv, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_abs] at hmem
    exact (by simpa [Module.Basis.coord_apply] using hmem : |b.repr v i| ≤ C).trans
      (le_max_left _ _)
  choose C hC_nonneg hC_bound using hcoord_bdd
  refine ⟨1 + ∑ i, C i * r i, add_pos_of_pos_of_nonneg one_pos
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hC_nonneg i) (hr_pos i).le), fun z hz ↦ ?_⟩
  let v : W₁ := ⟨z, hK₁W hz⟩
  choose a ha_mem ha_eq using hr_mem
  have hsum_eq : z = ∑ i, (b.repr v i * r i) • a i := by
    have hv_eq : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
    change (v : Z) = _
    conv_lhs => rw [hv_eq]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, ← ha_eq, mul_smul]
  rw [hsum_eq]
  refine sum_smul_mem_smul_of_absConvex hA0 hAac (fun i _ ↦ ha_mem i)
    (add_pos_of_pos_of_nonneg one_pos
      (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hC_nonneg i) (hr_pos i).le)) ?_
  have hle : ∑ i, |b.repr v i * r i| ≤ ∑ i, C i * r i := by
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [abs_mul, abs_of_pos (hr_pos i)]
    exact mul_le_mul_of_nonneg_right (hC_bound i v hz) (hr_pos i).le
  linarith

/-- If a closed absolutely convex set `A` with `0 ∈ A` has dense `ℝ`-span in a `T0` topological
`ℝ`-vector space `Z`, and an open neighbourhood `O` of `0` satisfies `O ⊆ A + K` for a compact
subset `K` of a finite-dimensional subspace `W`, then `A ∈ 𝓝 (0 : Z)`. -/
private lemma mem_nhds_zero_of_open_subset_add_compact_finiteDimensional
    {Z : Type*} [AddCommGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [T0Space Z]
    [Module ℝ Z] [ContinuousSMul ℝ Z]
    {A O K : Set Z} (hA_closed : IsClosed A) (hA0 : (0 : Z) ∈ A) (hAac : AbsConvex ℝ A)
    (hA_dense : Dense (Submodule.span ℝ A : Set Z))
    (hO_open : IsOpen O) (hO0 : (0 : Z) ∈ O)
    {W : Submodule ℝ Z} [FiniteDimensional ℝ W]
    (hK_comp : IsCompact K) (hKW : K ⊆ (W : Set Z)) (hO_sub : O ⊆ A + K) :
    A ∈ 𝓝 (0 : Z) := by
  let Z₀ : Submodule ℝ Z := Submodule.span ℝ A
  let W₁' : Submodule ℝ W := Z₀.comap W.subtype
  obtain ⟨W₂', hcompl⟩ := Submodule.exists_isCompl W₁'
  let W₁ : Submodule ℝ Z := W₁'.map W.subtype
  let W₂ : Submodule ℝ Z := W₂'.map W.subtype
  have hZ₀_inf_W₂ : Z₀ ⊓ W₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz₀, ⟨w, hw₂, rfl⟩⟩
    have hw0 : w ∈ W₁' ⊓ W₂' := ⟨hz₀, hw₂⟩
    rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hw0
    simp [hw0]
  -- Project `K` continuously onto `W₁ ≤ Z₀` and absorb its image into `S • A`.
  let p₁ : W →ₗ[ℝ] W₁' := W₁'.projectionOnto W₂' hcompl
  have hp₁_cont : Continuous p₁ :=
    LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) (E := W) (F' := W₁') p₁
  have hK_W_comp : IsCompact (W.subtype ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK_comp <| by
      simpa [Submodule.coe_subtype, Subtype.range_coe] using hKW
  let K₁ : Set Z := (fun v : W₁' ↦ ((v : W) : Z)) '' (p₁ '' (W.subtype ⁻¹' K))
  have hK₁_comp : IsCompact K₁ :=
    (hK_W_comp.image hp₁_cont).image (continuous_subtype_val.comp continuous_subtype_val)
  have : FiniteDimensional ℝ W₁ := Module.Finite.of_surjective
    (W.subtype.comp W₁'.subtype |>.codRestrict W₁ fun v ↦ ⟨v.1, v.2, rfl⟩)
    (fun ⟨_, w, hw, rfl⟩ ↦ ⟨⟨w, hw⟩, rfl⟩)
  have hW₁_le : W₁ ≤ Z₀ := by
    rintro _ ⟨w, hw, rfl⟩
    exact hw
  have hK₁_W₁ : K₁ ⊆ (W₁ : Set Z) := by
    rintro _ ⟨v, _, rfl⟩
    exact ⟨v.1, v.2, rfl⟩
  obtain ⟨S, hS_pos, hK₁_abs⟩ :=
    exists_pos_smul_subset_of_isCompact_finiteDimensional hA0 hAac hW₁_le hK₁_comp hK₁_W₁
  -- Hence `O ⊆ B + W₂`, where `B := (1 + S) • A` is closed and contained in `Z₀`.
  let B : Set Z := (1 + S) • A
  have h1S_pos : 0 < 1 + S := by linarith
  have hB_closed : IsClosed B := isClosedMap_smul_of_ne_zero h1S_pos.ne' _ hA_closed
  have hB_sub_Z₀ : B ⊆ (Z₀ : Set Z) := by
    rintro _ ⟨a, ha, rfl⟩
    exact Z₀.smul_mem (1 + S) (Submodule.subset_span ha)
  have hO_sub_BW₂ : O ⊆ B + (W₂ : Set Z) := by
    intro z hz
    obtain ⟨a, ha, k, hk, rfl⟩ := hO_sub hz
    let kW : W := ⟨k, hKW hk⟩
    have hp₁k : ((p₁ kW : W) : Z) ∈ K₁ := ⟨p₁ kW, ⟨kW, hk, rfl⟩, rfl⟩
    obtain ⟨a', ha', ha'_eq⟩ := hK₁_abs hp₁k
    have hdiff_mem : kW - (p₁ kW : W) ∈ W₂' := by
      rw [← W₁'.projectionOnto_apply_eq_zero_iff (q := W₂') hcompl, map_sub,
        W₁'.projectionOnto_apply_left hcompl, sub_self]
    have hadd_mem : a + ((p₁ kW : W) : Z) ∈ B := by
      rw [← ha'_eq]
      refine ⟨(1 / (1 + S)) • a + (S / (1 + S)) • a',
        hAac.2 ha ha' (div_nonneg zero_le_one h1S_pos.le) (div_nonneg hS_pos.le h1S_pos.le)
          (by rw [← add_div, div_self h1S_pos.ne']), ?_⟩
      dsimp only
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h1S_pos.ne',
        mul_div_cancel₀ _ h1S_pos.ne', one_smul]
    refine ⟨a + ((p₁ kW : W) : Z), hadd_mem,
      ((kW - (p₁ kW : W) : W) : Z), ⟨kW - (p₁ kW : W), hdiff_mem, rfl⟩, ?_⟩
    change a + ((p₁ kW : W) : Z) + (k - ((p₁ kW : W) : Z)) = a + k
    abel
  -- Density of `Z₀` forces the complementary finite-dimensional summand `W₂` to vanish.
  have hW₂_bot : W₂ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hw_cl : w ∈ closure B := by
      rw [mem_closure_iff]
      intro N hN hwN
      have hnhds : N ∩ (fun x : Z ↦ x - w) ⁻¹' O ∈ 𝓝 w := by
        refine Filter.inter_mem (hN.mem_nhds hwN) ?_
        have hcont : Continuous (fun x : Z ↦ x - w) := continuous_id.sub continuous_const
        exact hcont.continuousAt (by simpa [sub_self] using hO_open.mem_nhds hO0)
      obtain ⟨x, hxZ₀, hxN, hxsub⟩ := hA_dense.inter_nhds_nonempty hnhds
      obtain ⟨b', hb', w', hw', hxw⟩ := hO_sub_BW₂ hxsub
      have hdiff : x - b' = w + w' := by
        have h : x - w = b' + w' := hxw.symm
        rw [sub_eq_iff_eq_add] at h ⊢
        rw [h]
        abel
      have hmem_inf : x - b' ∈ Z₀ ⊓ W₂ :=
        ⟨Z₀.sub_mem hxZ₀ (hB_sub_Z₀ hb'), hdiff ▸ W₂.add_mem hw hw'⟩
      rw [hZ₀_inf_W₂, Submodule.mem_bot, sub_eq_zero] at hmem_inf
      exact ⟨x, hxN, hmem_inf ▸ hb'⟩
    rw [hB_closed.closure_eq] at hw_cl
    have hmem_inf : w ∈ Z₀ ⊓ W₂ := ⟨hB_sub_Z₀ hw_cl, hw⟩
    rwa [hZ₀_inf_W₂] at hmem_inf
  -- Therefore `O ⊆ (1 + S) • A`, so `(1 + S)⁻¹ • O ⊆ A` and `A ∈ 𝓝 0`.
  have hscaled : (1 + S)⁻¹ • O ⊆ A := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨b', hb', w, hw, rfl⟩ := hO_sub_BW₂ hz
    rw [hW₂_bot, SetLike.mem_coe, Submodule.mem_bot] at hw
    obtain ⟨a, ha, rfl⟩ := hb'
    dsimp only
    rw [hw, add_zero, inv_smul_smul₀ h1S_pos.ne']
    exact ha
  exact Filter.mem_of_superset
    ((hO_open.smul₀ (inv_ne_zero h1S_pos.ne')).mem_nhds ⟨0, hO0, smul_zero _⟩) hscaled

variable {E F : Type*}
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T0Space F]
  [Module ℝ F] [ContinuousSMul ℝ F]

/-- Real core of Schwartz's finiteness theorem: for a surjective continuous `ℝ`-linear map `g` and
compact `h` into a `T0` Baire target, `(g + h).range` is closed, `(g + h).rangeRestrict` is open,
and `(g + h).range` has a finite `ℝ`-spanning complement. -/
private lemma schwartz_real [BaireSpace F] (g h : E →L[ℝ] F)
    (hg : Function.Surjective g) (hh : IsCompactOperator h) :
    IsClosed ((g + h).range : Set F) ∧ IsOpenMap (g + h).rangeRestrict ∧
      ∃ s : Finset F, (g + h).range ⊔ Submodule.span ℝ (s : Set F) = ⊤ := by
  let u : E →L[ℝ] F := g + h
  have hg_open : IsOpenMap g := g.isOpenMap_of_hasZeroSequenceOfUnits hg
  -- Step 1: pick an open absolutely convex neighbourhood `V` of `0` with `closure (h '' V)`
  -- compact.
  obtain ⟨V₀, hV₀_nhds, hV₀_comp⟩ :=
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image h).mp hh
  obtain ⟨V, ⟨hV0, hVopen, hVac⟩, hVV₀⟩ :=
    (nhds_hasBasis_absConvex_open ℝ E).mem_iff.mp hV₀_nhds
  have hK_comp : IsCompact (closure (h '' V)) :=
    hV₀_comp.of_isClosed_subset isClosed_closure (closure_mono (Set.image_mono hVV₀))
  -- Step 2: `Z := u.range.topologicalClosure` has finite codimension in `F`.
  let Z : Submodule ℝ F := u.range.topologicalClosure
  have hZ_closed : IsClosed (Z : Set F) := u.range.isClosed_topologicalClosure
  obtain ⟨s₀, L₀, _, hL₀_span, hV_sub⟩ :=
    image_subset_closure_image_two_smul_add_compact g h hg_open hK_comp hV0 hVopen hVac Subset.rfl
  have hZ_codim : Z ⊔ Submodule.span ℝ (s₀ : Set F) = ⊤ := by
    have hclZ : closure (u '' ((2 : ℝ) • V)) ⊆ (Z : Set F) :=
      closure_minimal (fun _ ⟨x, _, hx⟩ ↦ subset_closure ⟨x, hx⟩) hZ_closed
    have hsub : g '' V ⊆ ((Z ⊔ Submodule.span ℝ (s₀ : Set F) : Submodule ℝ F) : Set F) := by
      intro y hy
      obtain ⟨a, ha, l, hl, rfl⟩ := hV_sub hy
      exact Submodule.add_mem _ (Submodule.mem_sup_left (hclZ ha))
        (Submodule.mem_sup_right (hL₀_span hl))
    exact Submodule.eq_top_of_nonempty_interior' _
      ⟨0, mem_interior.mpr ⟨g '' V, hsub, hg_open V hVopen, ⟨0, hV0, map_zero g⟩⟩⟩
  -- Step 3: show `closure (uZ '' U') ∈ 𝓝 (0 : Z)` for every `U' ∈ 𝓝 (0 : E)`.
  let uZ : E →L[ℝ] Z := u.codRestrict Z fun x ↦ subset_closure ⟨x, rfl⟩
  have huZ_nhds : ∀ U' ∈ 𝓝 (0 : E), closure (uZ '' U') ∈ 𝓝 (0 : Z) := by
    intro U' hU'
    have hpre2 : (fun x : E ↦ (2 : ℝ) • x) ⁻¹' U' ∈ 𝓝 (0 : E) :=
      (continuous_const_smul (2 : ℝ)).continuousAt (by simpa using hU')
    obtain ⟨U, ⟨hU0, hUopen, hUac⟩, hUsub⟩ :=
      (nhds_hasBasis_absConvex_open ℝ E).mem_iff.mp (Filter.inter_mem hpre2 (hVopen.mem_nhds hV0))
    have h2U : (2 : ℝ) • U ⊆ U' := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hUsub hx).1
    have hUV : U ⊆ V := fun x hx ↦ (hUsub hx).2
    obtain ⟨s, L, hL_comp, hL_span, hU_approx⟩ :=
      image_subset_closure_image_two_smul_add_compact g h hg_open hK_comp hU0 hUopen hUac hUV
    -- Pull `g '' U`, `closure (u '' (2 • U))`, `L`, and `span ℝ s` back to the closed subspace `Z`.
    let OZ : Set Z := Subtype.val ⁻¹' (g '' U)
    let AZ : Set Z := closure (uZ '' ((2 : ℝ) • U))
    let KZ : Set Z := Subtype.val ⁻¹' L
    have hOZ_open : IsOpen OZ := (hg_open U hUopen).preimage continuous_subtype_val
    have hOZ_0 : (0 : Z) ∈ OZ := ⟨0, hU0, map_zero g⟩
    have hAZ_eq : AZ = Subtype.val ⁻¹' closure (u '' ((2 : ℝ) • U)) := by
      dsimp only [AZ]
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, ← Set.image_comp]
      rfl
    have hA_sub_Z : closure (u '' ((2 : ℝ) • U)) ⊆ (Z : Set F) :=
      closure_minimal (fun _ ⟨x, _, hx⟩ ↦ subset_closure ⟨x, hx⟩) hZ_closed
    have hAZ_0 : (0 : Z) ∈ AZ :=
      subset_closure ⟨0, ⟨0, hU0, smul_zero _⟩, map_zero uZ⟩
    have hAZ_ac : AbsConvex ℝ AZ := by
      have himg_bal : Balanced ℝ (uZ '' ((2 : ℝ) • U)) := by
        intro a ha
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        change a • uZ x ∈ uZ '' ((2 : ℝ) • U)
        rw [← map_smul]
        exact ⟨a • x, (hUac.1.smul (2 : ℝ)) a ha (Set.smul_mem_smul_set hx), rfl⟩
      exact AbsConvex.closure ⟨himg_bal, (hUac.2.smul (2 : ℝ)).linear_image uZ.toLinearMap⟩
    have hKZ_comp : IsCompact KZ :=
      hZ_closed.isClosedEmbedding_subtypeVal.isCompact_preimage hL_comp
    have hOZ_sub : OZ ⊆ AZ + KZ := by
      intro z hz
      obtain ⟨a, ha, l, hl, hal⟩ := hU_approx hz
      have hal' : a + l = (z : F) := hal
      have haZ : a ∈ Z := hA_sub_Z ha
      have hlZ : l ∈ Z := by
        have : l = (z : F) - a := by rw [← hal']; abel
        rw [this]
        exact Z.sub_mem z.2 haZ
      refine ⟨⟨a, haZ⟩, ?_, ⟨l, hlZ⟩, hl, Subtype.ext hal'⟩
      rw [hAZ_eq]
      exact ha
    have hZ₀_dense : Dense (Submodule.span ℝ AZ : Set Z) := by
      have huZ_dense : Dense (Set.range uZ) := by
        intro z
        rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
        have himg : Subtype.val '' Set.range (uZ : E → Z) = (u.range : Set F) := by
          ext y
          simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, SetLike.mem_coe,
            LinearMap.mem_range, ContinuousLinearMap.coe_coe]
          exact Iff.rfl
        have hcl : closure (Subtype.val '' Set.range (uZ : E → Z)) = (Z : Set F) :=
          congrArg closure himg
        exact hcl.symm ▸ z.2
      refine huZ_dense.mono ?_
      rintro _ ⟨x, rfl⟩
      have h2U_nhds : (2 : ℝ) • U ∈ 𝓝 (0 : E) :=
        (hUopen.smul₀ (by norm_num : (2 : ℝ) ≠ 0)).mem_nhds ⟨0, hU0, smul_zero _⟩
      obtain ⟨r, habs⟩ := absorbs_iff_norm.mp (absorbent_nhds_zero (𝕜 := ℝ) h2U_nhds x)
      let c : ℝ := max r 1
      have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right r 1)
      have hx_mem : x ∈ c • ((2 : ℝ) • U) := by
        have hnorm : r ≤ ‖c‖ := by
          rw [Real.norm_eq_abs, abs_of_pos hc]
          exact le_max_left r 1
        exact habs c hnorm rfl
      obtain ⟨y, hy, rfl⟩ := hx_mem
      rw [map_smul]
      exact Submodule.smul_mem _ c (Submodule.subset_span (subset_closure ⟨y, hy, rfl⟩))
    let WZ : Submodule ℝ Z := (Submodule.span ℝ (s : Set F)).comap Z.subtype
    have : FiniteDimensional ℝ (Submodule.span ℝ (s : Set F)) :=
      FiniteDimensional.span_of_finite ℝ s.finite_toSet
    have : FiniteDimensional ℝ WZ := by
      let incl : WZ →ₗ[ℝ] Submodule.span ℝ (s : Set F) :=
        (Z.subtype.domRestrict WZ).codRestrict (Submodule.span ℝ (s : Set F)) fun w ↦ w.2
      have hinj : Function.Injective incl := fun x y hxy ↦
        Subtype.ext (Subtype.ext (congrArg (fun a : Submodule.span ℝ (s : Set F) ↦ (a : F)) hxy))
      exact Module.Finite.of_injective incl hinj
    have hAZ_nhds : AZ ∈ 𝓝 (0 : Z) :=
      mem_nhds_zero_of_open_subset_add_compact_finiteDimensional isClosed_closure hAZ_0 hAZ_ac
        hZ₀_dense hOZ_open hOZ_0 (W := WZ) hKZ_comp (fun _ hz ↦ hL_span hz) hOZ_sub
    exact Filter.mem_of_superset hAZ_nhds (closure_mono (Set.image_mono h2U))
  -- Step 4: apply the open mapping approximation theorem to `uZ`.
  have huZ_open : IsOpenMap uZ :=
    TauCeti.isOpenMap_of_closure_image_mem_nhds uZ uZ.continuous.continuousAt huZ_nhds
  have huZ_surj : Function.Surjective uZ :=
    uZ.toLinearMap.surjective_of_isOpenMap huZ_open
  have hrange_eq : u.range = Z := by
    refine le_antisymm (fun y hy ↦ subset_closure hy) fun y hy ↦ ?_
    obtain ⟨x, hx⟩ := huZ_surj ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  refine ⟨hrange_eq.symm ▸ hZ_closed, ?_, s₀, hrange_eq.symm ▸ hZ_codim⟩
  let e : Z ≃ₜ u.range := Homeomorph.setCongr (congrArg SetLike.coe hrange_eq.symm)
  have hcomp : (u.rangeRestrict : E → u.range) = e ∘ uZ := by
    ext x
    rfl
  rw [hcomp]
  exact e.isOpenMap.comp huZ_open

end RealCore

section Baire

variable {𝕜 E F : Type*} [Ring 𝕜] [TopologicalSpace 𝕜] [SMul ℝ 𝕜] [ContinuousSMul ℝ 𝕜]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T0Space F] [BaireSpace F]
  [Module ℝ F] [Module 𝕜 F] [IsScalarTower ℝ 𝕜 F] [ContinuousSMul 𝕜 F]

/-- **Schwartz's finiteness theorem (openness onto the range, Baire target).**
If `g : E →L[𝕜] F` is surjective and `h : E →L[𝕜] F` is compact, then `g + h` is open onto its
range (hence a strict morphism). -/
theorem isOpenMap_rangeRestrict_add_of_isCompactOperator_of_baireSpace
    (g h : E →L[𝕜] F) (hg : Function.Surjective g) (hh : IsCompactOperator h) :
    IsOpenMap (g + h).rangeRestrict := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  have hopen := (schwartz_real (g.restrictScalars ℝ) (h.restrictScalars ℝ) hg hh).2.1
  let e : ((g.restrictScalars ℝ + h.restrictScalars ℝ).range : Set F) ≃ₜ ((g + h).range : Set F) :=
    Homeomorph.setCongr rfl
  have hcomp : ((g + h).rangeRestrict : E → (g + h).range) =
      e ∘ (g.restrictScalars ℝ + h.restrictScalars ℝ).rangeRestrict := by
    ext x
    rfl
  rw [hcomp]
  exact e.isOpenMap.comp hopen

/-- **Schwartz's finiteness theorem (closed range, Baire target).**
If `g : E →L[𝕜] F` is surjective and `h : E →L[𝕜] F` is compact, then `g + h` has closed range. -/
theorem isClosed_range_add_of_isCompactOperator_of_baireSpace
    (g h : E →L[𝕜] F) (hg : Function.Surjective g) (hh : IsCompactOperator h) :
    IsClosed ((g + h).range : Set F) := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  exact (schwartz_real (g.restrictScalars ℝ) (h.restrictScalars ℝ) hg hh).1

/-- **Schwartz's finiteness theorem (finite-codimension range, Baire target).**
If `g : E →L[𝕜] F` is surjective and `h : E →L[𝕜] F` is compact, then the cokernel
`F ⧸ (g + h).range` is a finitely generated `𝕜`-module (in particular `FiniteDimensional 𝕜` when
`𝕜` is a division ring such as `ℝ` or `ℂ`). -/
theorem finite_quotient_range_add_of_isCompactOperator_of_baireSpace
    (g h : E →L[𝕜] F) (hg : Function.Surjective g) (hh : IsCompactOperator h) :
    Module.Finite 𝕜 (F ⧸ (g + h).range) := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  obtain ⟨s, hs⟩ := (schwartz_real (g.restrictScalars ℝ) (h.restrictScalars ℝ) hg hh).2.2
  classical
  have hspan_le : ∀ b ∈ Submodule.span ℝ (s : Set F), b ∈ Submodule.span 𝕜 (s : Set F) := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x₁ x₂ _ _ ih₁ ih₂ => exact add_mem ih₁ ih₂
    | smul r x _ ih =>
      rw [← smul_one_smul 𝕜 r x]
      exact Submodule.smul_mem _ _ ih
  refine Module.finite_def.mpr ⟨s.image (g + h).range.mkQ, ?_⟩
  rw [eq_top_iff]
  intro q _
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hy : y ∈ (g.restrictScalars ℝ + h.restrictScalars ℝ).range ⊔ Submodule.span ℝ (s : Set F) :=
    hs.symm ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  have ha' : a ∈ (g + h).range := ha
  have hmk : (Submodule.Quotient.mk (a + b) : F ⧸ (g + h).range) = (g + h).range.mkQ b := by
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).mpr ha', zero_add]
    rfl
  rw [hmk, Finset.coe_image, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem (hspan_le b hb)

end Baire

section CompleteTarget

variable {𝕜 E F : Type*} [Ring 𝕜] [TopologicalSpace 𝕜] [SMul ℝ 𝕜] [ContinuousSMul ℝ 𝕜]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]
  [(𝓝 (0 : F)).IsCountablyGenerated] [T0Space F]
  [Module ℝ F] [Module 𝕜 F] [IsScalarTower ℝ 𝕜 F] [ContinuousSMul 𝕜 F]

/-- **Schwartz's finiteness theorem (openness onto the range, Fréchet / complete uniform target).**
For a surjective continuous linear map `g : E →L[𝕜] F` and a compact operator `h : E →L[𝕜] F`
into a complete first-countable `T0` uniform module, `g + h` is open onto its range. -/
theorem isOpenMap_rangeRestrict_add_of_isCompactOperator_of_completeSpace
    (g h : E →L[𝕜] F) (hg : Function.Surjective g) (hh : IsCompactOperator h) :
    IsOpenMap (g + h).rangeRestrict := by
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace F := BaireSpace.of_completelyPseudoMetrizable
  exact g.isOpenMap_rangeRestrict_add_of_isCompactOperator_of_baireSpace h hg hh

/-- **Schwartz's finiteness theorem (closed range, Fréchet / complete uniform target).**
For a surjective continuous linear map `g : E →L[𝕜] F` and a compact operator `h : E →L[𝕜] F`
into a complete first-countable `T0` uniform module, `g + h` has closed range. -/
theorem isClosed_range_add_of_isCompactOperator_of_completeSpace
    (g h : E →L[𝕜] F) (hg : Function.Surjective g) (hh : IsCompactOperator h) :
    IsClosed ((g + h).range : Set F) := by
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace F := BaireSpace.of_completelyPseudoMetrizable
  exact g.isClosed_range_add_of_isCompactOperator_of_baireSpace h hg hh

/-- **Schwartz's finiteness theorem (finite-codimension range, Fréchet / complete uniform target).**
For a surjective continuous linear map `g : E →L[𝕜] F` and a compact operator `h : E →L[𝕜] F`
into a complete first-countable `T0` uniform module, `F ⧸ (g + h).range` is a finitely generated
`𝕜`-module (hence finite-dimensional over `ℝ` or `ℂ`). -/
theorem finite_quotient_range_add_of_isCompactOperator_of_completeSpace
    (g h : E →L[𝕜] F) (hg : Function.Surjective g) (hh : IsCompactOperator h) :
    Module.Finite 𝕜 (F ⧸ (g + h).range) := by
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace F := BaireSpace.of_completelyPseudoMetrizable
  exact g.finite_quotient_range_add_of_isCompactOperator_of_baireSpace h hg hh

end CompleteTarget

end ContinuousLinearMap

end
