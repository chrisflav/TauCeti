/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Cell-partition quadrature and uniform Riemann sums on planar sets

When a finite-measure set `K` is covered by a finite pairwise-disjoint family of measurable cells
`S i`, replacing the Bochner integral `∫ x in K, g x ∂μ` by the weighted cell sum
`∑ i, μ.real (S i ∩ K) • g (ζ i)` incurs an error bounded by `μ.real K * ω`, provided `g` varies by
at most `ω` from `g (ζ i)` on each positive-measure intersection `S i ∩ K`. Cells whose intersection
with `K` has measure zero carry weight `μ.real (S i ∩ K) = 0` and contribute nothing regardless of
the sample tag, so restricting the sum to positive-measure cells produces the exact same value
(`TauCeti.sum_filter_pos_measureReal_smul_eq_sum`) and extracts positive weights `0 < c j` summing
to `μ.real K` with sample points `ζ j ∈ K` (`TauCeti.exists_pos_quadrature_of_partition`).

In the complex plane `ℂ`, the half-open coordinate squares
`TauCeti.planeGridCell a c δ j k = [a + j δ, a + (j + 1) δ) ×ℂ [c + k δ, c + (k + 1) δ)` form a
pairwise-disjoint measurable grid of diameter at most `√2 * δ` and area `δ ^ 2`. Covering a bounded
set `K₁ ⊆ ℂ` by finitely many cells of mesh `δ > 0` yields a positive-weight finite quadrature rule
whose nodes and weights depend only on `K₁` and `δ`, bounding the quadrature error uniformly across
all integrands of given modulus of continuity
(`Bornology.IsBounded.exists_planeQuadrature_of_oscillation` and
`Bornology.IsBounded.exists_planeQuadrature_norm_sub_setIntegral_le`), and hence giving `< ε`
uniform Riemann-sum approximation on compact products `K₁ ×ˢ K₂`
(`IsCompact.exists_planeQuadrature_norm_sub_setIntegral_lt`).

## Main definitions

* `TauCeti.planeGridCell a c δ j k`: the `(j, k)`-th half-open square cell
  `[a + j δ, a + (j + 1) δ) ×ℂ [c + k δ, c + (k + 1) δ)` of mesh `δ` anchored at `(a, c)`.

## Main results

* `TauCeti.sum_filter_pos_measureReal_smul_eq_sum`: retaining only positive-measure cell
  intersections leaves the Riemann sum unchanged.
* `TauCeti.norm_sum_measureReal_smul_sub_setIntegral_le`: quantitative cell-partition quadrature
  bound `≤ μ.real K * ω` on any measure space.
* `TauCeti.exists_pos_quadrature_of_partition`: extracts a positive-weight `Fin N` quadrature rule
  supported in `K`, universal over all integrands on `K`.
* `TauCeti.dist_le_sqrt_two_mul_of_mem_planeGridCell` and
  `TauCeti.reProdIm_Icc_subset_iUnion_planeGridCell`: diameter `≤ √2 * δ` and box-covering
  properties of planar half-open square grids.
* `Bornology.IsBounded.exists_planeQuadrature_of_oscillation`,
  `Bornology.IsBounded.exists_planeQuadrature_norm_sub_setIntegral_le`, and
  `IsCompact.exists_planeQuadrature_norm_sub_setIntegral_lt`: uniform planar quadrature on bounded
  sets and compact products.

## References

* A. Rainer, *Advanced Complex Analysis*, Lemma 10.2 and Theorem 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., §1.3.
-/

public noncomputable section

open MeasureTheory Metric Set Function Filter Complex Topology
open scoped ENNReal NNReal

namespace TauCeti

section GeneralMeasure

variable {X E ι : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Boundary-cell convention.** Zero-measure intersections `μ (S i ∩ K) = 0` have real measure
`0`, so retaining only cells with `0 < μ (S i ∩ K)` leaves the weighted cell sum unchanged. -/
theorem sum_filter_pos_measureReal_smul_eq_sum [Fintype ι] (μ : Measure X) (S : ι → Set X)
    (K : Set X) (v : ι → E) [DecidablePred fun i ↦ 0 < μ (S i ∩ K)] :
    (∑ i with 0 < μ (S i ∩ K), μ.real (S i ∩ K) • v i) =
      ∑ i, μ.real (S i ∩ K) • v i := by
  refine Finset.sum_filter_of_ne fun i _ hne ↦ pos_iff_ne_zero.mpr fun h0 ↦ hne ?_
  simp [Measure.real, h0]

/-- The real measures of the intersections `S i ∩ K` of a pairwise-disjoint measurable cover of a
finite-measure set `K` add up to `μ.real K` (with no measurability assumption on `K`). -/
theorem sum_measureReal_inter_eq [Fintype ι] {μ : Measure X} {S : ι → Set X} {K : Set X}
    (hKfin : μ K ≠ ∞) (hS_meas : ∀ i, MeasurableSet (S i))
    (hS_disj : Pairwise (Disjoint on S)) (hS_cover : K ⊆ ⋃ i, S i) :
    ∑ i, μ.real (S i ∩ K) = μ.real K := by
  have hfin (i : ι) : (μ.restrict K) (S i) ≠ ∞ := by
    rw [Measure.restrict_apply (hS_meas i)]
    exact ne_top_of_le_ne_top hKfin (measure_mono inter_subset_right)
  have hU : (μ.restrict K) (⋃ i, S i) = μ K := by
    rw [Measure.restrict_apply (MeasurableSet.iUnion hS_meas), inter_eq_right.mpr hS_cover]
  calc ∑ i, μ.real (S i ∩ K)
      = ∑ i, (μ.restrict K).real (S i) :=
        Finset.sum_congr rfl fun i _ ↦ by simp [Measure.real, Measure.restrict_apply (hS_meas i)]
    _ = ((μ.restrict K) (⋃ i, S i)).toReal := by
        rw [measure_iUnion hS_disj hS_meas, tsum_fintype, ENNReal.toReal_sum fun i _ ↦ hfin i]
        rfl
    _ = μ.real K := by rw [hU, measureReal_def]

/-- **Quantitative cell-partition quadrature bound.** If `K` has finite measure and is covered by
pairwise-disjoint measurable cells `S i`, and on each positive-measure cell `S i ∩ K` the integrable
map `g` deviates from `g (ζ i)` by at most `ω`, then the weighted cell sum approximates
`∫ x in K, g x ∂μ` within `μ.real K * ω`. -/
theorem norm_sum_measureReal_smul_sub_setIntegral_le [CompleteSpace E] [Fintype ι]
    {μ : Measure X} {S : ι → Set X} {K : Set X}
    (hKfin : μ K ≠ ∞) (hS_meas : ∀ i, MeasurableSet (S i))
    (hS_disj : Pairwise (Disjoint on S)) (hS_cover : K ⊆ ⋃ i, S i)
    {g : X → E} (hg : IntegrableOn g K μ) {ζ : ι → X} {ω : ℝ}
    (hosc : ∀ i, 0 < μ (S i ∩ K) → ∀ x ∈ S i ∩ K, ‖g x - g (ζ i)‖ ≤ ω) :
    ‖(∑ i, μ.real (S i ∩ K) • g (ζ i)) - ∫ x in K, g x ∂μ‖ ≤ μ.real K * ω := by
  have hint : ∫ x in K, g x ∂μ = ∑ i, ∫ x in S i ∩ K, g x ∂μ := by
    have hres : (μ.restrict K).restrict (⋃ i, S i) = μ.restrict K := by
      rw [Measure.restrict_restrict (MeasurableSet.iUnion hS_meas), inter_eq_right.mpr hS_cover]
    have hsplit : ∫ x in ⋃ i, S i, g x ∂(μ.restrict K) =
        ∑ i, ∫ x in S i, g x ∂(μ.restrict K) :=
      integral_iUnion_fintype hS_meas hS_disj fun i ↦ by
        rw [IntegrableOn, Measure.restrict_restrict (hS_meas i)]
        exact hg.mono_set inter_subset_right
    rw [← hres, hsplit]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Measure.restrict_restrict (hS_meas i)]
  rw [hint, ← Finset.sum_sub_distrib, ← sum_measureReal_inter_eq hKfin hS_meas hS_disj hS_cover,
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  by_cases hpos : 0 < μ (S i ∩ K)
  · have hfin_i : μ (S i ∩ K) < ∞ :=
      (measure_mono inter_subset_right).trans_lt hKfin.lt_top
    have hconst : μ.real (S i ∩ K) • g (ζ i) = ∫ _ in S i ∩ K, g (ζ i) ∂μ :=
      (setIntegral_const (g (ζ i))).symm
    rw [hconst, ← integral_sub (integrableOn_const hfin_i.ne) (hg.mono_set inter_subset_right),
      mul_comm]
    refine norm_setIntegral_le_of_norm_le_const hfin_i fun x hx ↦ ?_
    rw [norm_sub_rev]
    exact hosc i hpos x hx
  · have hzero : μ (S i ∩ K) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hpos)
    simp [Measure.real, hzero, setIntegral_measure_zero _ hzero]

/-- Auxiliary bound on the positive-measure filtered cell sum once a fallback element `x₀ : X` is
available. -/
private theorem norm_sum_subtype_pos_sub_setIntegral_le [CompleteSpace E] [Finite ι]
    {μ : Measure X} {S : ι → Set X} {K : Set X}
    (hKfin : μ K ≠ ∞) (hS_meas : ∀ i, MeasurableSet (S i))
    (hS_disj : Pairwise (Disjoint on S)) (hS_cover : K ⊆ ⋃ i, S i)
    (P : Finset ι) (hP : ∀ i, i ∈ P ↔ 0 < μ (S i ∩ K))
    (pick : P → X) (hpick : ∀ i : P, pick i ∈ S i.1 ∩ K) (x₀ : X)
    {g : X → E} (hg : IntegrableOn g K μ) {ω : ℝ}
    (hosc : ∀ i, ∀ x ∈ S i ∩ K, ∀ y ∈ S i ∩ K, ‖g x - g y‖ ≤ ω) :
    ‖(∑ i : P, μ.real (S i.1 ∩ K) • g (pick i)) - ∫ x in K, g x ∂μ‖ ≤ μ.real K * ω := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let tag : ι → X := fun i ↦ if hi : i ∈ P then pick ⟨i, hi⟩ else x₀
  have hP_eq : P = Finset.univ.filter (fun i ↦ 0 < μ (S i ∩ K)) := by
    ext i
    simp [hP]
  have hsum : (∑ i : P, μ.real (S i.1 ∩ K) • g (pick i)) =
      ∑ i, μ.real (S i ∩ K) • g (tag i) := by
    have h1 : (∑ i : P, μ.real (S i.1 ∩ K) • g (pick i)) =
        ∑ i : P, μ.real (S i.1 ∩ K) • g (tag i.1) :=
      Finset.sum_congr rfl fun i _ ↦ by simp [tag, i.2]
    rw [h1, Finset.sum_coe_sort P fun i ↦ μ.real (S i ∩ K) • g (tag i), hP_eq,
      sum_filter_pos_measureReal_smul_eq_sum]
  rw [hsum]
  refine norm_sum_measureReal_smul_sub_setIntegral_le hKfin hS_meas hS_disj hS_cover hg
    fun i hpos x hx ↦ ?_
  have hiP : i ∈ P := (hP i).mpr hpos
  have htag : tag i ∈ S i ∩ K := by
    simp only [tag, hiP, dite_true]
    exact hpick ⟨i, hiP⟩
  exact hosc i x hx (tag i) htag

/-- **Positive-weight quadrature extraction from a measurable cover.** Retaining only the cells
`S i` whose intersection with `K` has positive measure produces `N` sample points `ζ j ∈ K` and
strictly positive weights `c j > 0` summing to `μ.real K` that depend only on `μ`, `K`, and `S`,
and approximate every integrable `g : X → E` within `μ.real K * ω` whenever `g` has pairwise
oscillation at most `ω` on each cell intersection `S i ∩ K`. -/
theorem exists_pos_quadrature_of_partition [CompleteSpace E] [Finite ι]
    {μ : Measure X} {S : ι → Set X} {K : Set X}
    (hKfin : μ K ≠ ∞) (hS_meas : ∀ i, MeasurableSet (S i))
    (hS_disj : Pairwise (Disjoint on S)) (hS_cover : K ⊆ ⋃ i, S i) :
    ∃ (N : ℕ) (ζ : Fin N → X) (c : Fin N → ℝ),
      (∀ j, ∃ i, ζ j ∈ S i ∩ K) ∧ (∀ j, 0 < c j) ∧ ∑ j, c j = μ.real K ∧
        ∀ (g : X → E) (ω : ℝ), IntegrableOn g K μ →
          (∀ i, ∀ x ∈ S i ∩ K, ∀ y ∈ S i ∩ K, ‖g x - g y‖ ≤ ω) →
          ‖(∑ j, c j • g (ζ j)) - ∫ x in K, g x ∂μ‖ ≤ μ.real K * ω := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let P : Finset ι := Finset.univ.filter fun i ↦ 0 < μ (S i ∩ K)
  let N : ℕ := P.card
  let e : Fin N ≃ P := P.equivFin.symm
  have hne (i : P) : (S i.1 ∩ K).Nonempty :=
    nonempty_of_measure_ne_zero (pos_iff_ne_zero.mp (Finset.mem_filter.mp i.2).2)
  let ζ : Fin N → X := fun j ↦ (hne (e j)).some
  let c : Fin N → ℝ := fun j ↦ μ.real (S (e j).1 ∩ K)
  have hc_pos (j : Fin N) : 0 < c j :=
    ENNReal.toReal_pos (pos_iff_ne_zero.mp (Finset.mem_filter.mp (e j).2).2)
      (ne_top_of_le_ne_top hKfin (measure_mono inter_subset_right))
  have hc_sum : ∑ j, c j = μ.real K := by
    calc ∑ j, c j
        = ∑ i : P, μ.real (S i.1 ∩ K) := Equiv.sum_comp e fun i : P ↦ μ.real (S i.1 ∩ K)
      _ = ∑ i ∈ P, μ.real (S i ∩ K) := Finset.sum_coe_sort P fun i ↦ μ.real (S i ∩ K)
      _ = ∑ i, μ.real (S i ∩ K) := by
          refine Finset.sum_filter_of_ne fun i _ h0 ↦ pos_iff_ne_zero.mpr fun hm ↦ h0 ?_
          simp [Measure.real, hm]
      _ = μ.real K := sum_measureReal_inter_eq hKfin hS_meas hS_disj hS_cover
  refine ⟨N, ζ, c, fun j ↦ ⟨(e j).1, (hne (e j)).some_mem⟩, hc_pos, hc_sum,
    fun g ω hg hosc ↦ ?_⟩
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have hP0 : P = ∅ := Finset.card_eq_zero.mp hN0
    have hμ0 : μ K = 0 := by
      have hunion : (⋃ i, S i ∩ K) = K := by
        rw [← iUnion_inter, inter_eq_right.mpr hS_cover]
      rw [← hunion]
      refine measure_iUnion_null fun i ↦ nonpos_iff_eq_zero.mp (not_lt.mp fun hpos ↦ ?_)
      have : i ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpos⟩
      simp [hP0] at this
    have hempty : IsEmpty (Fin N) := by
      rw [hN0]
      infer_instance
    simp [Measure.real, hμ0, setIntegral_measure_zero _ hμ0]
  · rw [Equiv.sum_comp e fun i : P ↦ μ.real (S i.1 ∩ K) • g ((hne i).some)]
    exact norm_sum_subtype_pos_sub_setIntegral_le hKfin hS_meas hS_disj hS_cover P
      (fun i ↦ by simp [P]) (fun i ↦ (hne i).some) (fun i ↦ (hne i).some_mem)
      (ζ ⟨0, hNpos⟩) hg hosc

end GeneralMeasure

section PlaneGrid

/-- The `(j, k)`-th half-open square cell
`[a + j δ, a + (j + 1) δ) ×ℂ [c + k δ, c + (k + 1) δ)` of the planar grid anchored at `(a, c)` with
mesh `δ`. -/
def planeGridCell (a c δ : ℝ) (j k : ℕ) : Set ℂ :=
  Ico (a + j * δ) (a + (j + 1 : ℕ) * δ) ×ℂ Ico (c + k * δ) (c + (k + 1 : ℕ) * δ)

/-- Unfolding `TauCeti.planeGridCell`. -/
theorem planeGridCell_def (a c δ : ℝ) (j k : ℕ) :
    planeGridCell a c δ j k =
      Ico (a + j * δ) (a + (j + 1 : ℕ) * δ) ×ℂ Ico (c + k * δ) (c + (k + 1 : ℕ) * δ) :=
  (rfl)

@[simp]
theorem mem_planeGridCell {a c δ : ℝ} {j k : ℕ} {z : ℂ} :
    z ∈ planeGridCell a c δ j k ↔
      (a + j * δ ≤ z.re ∧ z.re < a + (j + 1 : ℕ) * δ) ∧
        (c + k * δ ≤ z.im ∧ z.im < c + (k + 1 : ℕ) * δ) :=
  Iff.rfl

/-- For nonpositive mesh `δ ≤ 0`, every planar grid cell is empty. -/
@[simp]
theorem planeGridCell_eq_empty_of_nonpos {a c δ : ℝ} (hδ : δ ≤ 0) (j k : ℕ) :
    planeGridCell a c δ j k = ∅ := by
  refine eq_empty_of_forall_notMem fun z hz ↦ ?_
  rw [mem_planeGridCell] at hz
  push_cast at hz
  linarith [hz.1.1, hz.1.2]

/-- Every planar grid cell is Borel measurable. -/
theorem measurableSet_planeGridCell (a c δ : ℝ) (j k : ℕ) :
    MeasurableSet (planeGridCell a c δ j k) :=
  measurableSet_Ico.reProdIm measurableSet_Ico

/-- Distinct planar grid cells are disjoint, for any anchor `(a, c)` and any real `δ`. -/
theorem pairwiseDisjoint_planeGridCell (a c δ : ℝ) :
    Pairwise (Disjoint on fun p : ℕ × ℕ ↦ planeGridCell a c δ p.1 p.2) := by
  intro p q hpq
  refine Set.disjoint_left.mpr fun z hzp hzq ↦ ?_
  rw [mem_planeGridCell] at hzp hzq
  have hδ : 0 < δ := by
    push_cast at hzp
    linarith [hzp.1.1, hzp.1.2]
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h ↦ hpq (Prod.ext h1 h)
    rcases lt_or_gt_of_ne h2 with hlt | hgt
    · have hle : (p.2 + 1 : ℝ) ≤ q.2 := by exact_mod_cast Nat.succ_le_of_lt hlt
      have hm := mul_le_mul_of_nonneg_right hle hδ.le
      push_cast at hzp hzq
      linarith [hzp.2.2, hzq.2.1]
    · have hle : (q.2 + 1 : ℝ) ≤ p.2 := by exact_mod_cast Nat.succ_le_of_lt hgt
      have hm := mul_le_mul_of_nonneg_right hle hδ.le
      push_cast at hzp hzq
      linarith [hzq.2.2, hzp.2.1]
  · rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have hle : (p.1 + 1 : ℝ) ≤ q.1 := by exact_mod_cast Nat.succ_le_of_lt hlt
      have hm := mul_le_mul_of_nonneg_right hle hδ.le
      push_cast at hzp hzq
      linarith [hzp.1.2, hzq.1.1]
    · have hle : (q.1 + 1 : ℝ) ≤ p.1 := by exact_mod_cast Nat.succ_le_of_lt hgt
      have hm := mul_le_mul_of_nonneg_right hle hδ.le
      push_cast at hzp hzq
      linarith [hzq.1.2, hzp.1.1]

/-- A planar grid cell of nonnegative mesh `δ` has Lebesgue area `δ ^ 2`. -/
theorem volume_planeGridCell {a c δ : ℝ} (hδ : 0 ≤ δ) (j k : ℕ) :
    volume (planeGridCell a c δ j k) = ENNReal.ofReal (δ ^ 2) := by
  have ht := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
    (Ico (a + j * δ) (a + (j + 1 : ℕ) * δ) ×ˢ Ico (c + k * δ) (c + (k + 1 : ℕ) * δ))
  have hpre : Complex.measurableEquivRealProd ⁻¹'
      (Ico (a + j * δ) (a + (j + 1 : ℕ) * δ) ×ˢ Ico (c + k * δ) (c + (k + 1 : ℕ) * δ)) =
      planeGridCell a c δ j k := rfl
  rw [← hpre, ht, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico]
  have h1 : a + (j + 1 : ℕ) * δ - (a + j * δ) = δ := by push_cast; ring
  have h2 : c + (k + 1 : ℕ) * δ - (c + k * δ) = δ := by push_cast; ring
  rw [h1, h2, ← ENNReal.ofReal_mul hδ, sq]

/-- Real Lebesgue area of a planar grid cell of nonnegative mesh `δ`. -/
theorem volumeReal_planeGridCell {a c δ : ℝ} (hδ : 0 ≤ δ) (j k : ℕ) :
    volume.real (planeGridCell a c δ j k) = δ ^ 2 := by
  rw [measureReal_def, volume_planeGridCell hδ, ENNReal.toReal_ofReal (sq_nonneg δ)]

/-- Any two points in the same planar grid cell lie at Euclidean distance at most `√2 * δ`. -/
theorem dist_le_sqrt_two_mul_of_mem_planeGridCell {a c δ : ℝ} {j k : ℕ} {z w : ℂ}
    (hz : z ∈ planeGridCell a c δ j k) (hw : w ∈ planeGridCell a c δ j k) :
    dist z w ≤ √2 * δ := by
  rw [mem_planeGridCell] at hz hw
  have hδ : 0 ≤ δ := by
    push_cast at hz
    linarith [hz.1.1, hz.1.2]
  have hre : |z.re - w.re| ≤ δ := by
    rw [abs_sub_le_iff]
    push_cast at hz hw
    exact ⟨by linarith [hz.1.2, hw.1.1], by linarith [hw.1.2, hz.1.1]⟩
  have him : |z.im - w.im| ≤ δ := by
    rw [abs_sub_le_iff]
    push_cast at hz hw
    exact ⟨by linarith [hz.2.2, hw.2.1], by linarith [hw.2.2, hz.2.1]⟩
  have hsq_re : (z.re - w.re) ^ 2 ≤ δ ^ 2 :=
    sq_le_sq.mpr (hre.trans_eq (abs_of_nonneg hδ).symm)
  have hsq_im : (z.im - w.im) ^ 2 ≤ δ ^ 2 :=
    sq_le_sq.mpr (him.trans_eq (abs_of_nonneg hδ).symm)
  rw [dist_eq_norm, Complex.norm_def]
  have hnsq : Complex.normSq (z - w) ≤ 2 * δ ^ 2 := by
    rw [Complex.normSq_apply, sub_re, sub_im, ← sq, ← sq]
    linarith
  calc √(Complex.normSq (z - w))
      ≤ √(2 * δ ^ 2) := Real.sqrt_le_sqrt hnsq
    _ = √2 * δ := by rw [Real.sqrt_mul zero_le_two, Real.sqrt_sq hδ]

/-- Every closed rectangle `[a, b] ×ℂ [c, d]` (empty when `b < a` or `d < c`) is covered by the
first `(⌊(b - a) / δ⌋₊ + 1) × (⌊(d - c) / δ⌋₊ + 1)` half-open grid cells of mesh `δ > 0`. -/
theorem reProdIm_Icc_subset_iUnion_planeGridCell {a b c d δ : ℝ} (hδ : 0 < δ) :
    Icc a b ×ℂ Icc c d ⊆
      ⋃ p : Fin (⌊(b - a) / δ⌋₊ + 1) × Fin (⌊(d - c) / δ⌋₊ + 1),
        planeGridCell a c δ p.1 p.2 := by
  intro z hz
  have hzre : a ≤ z.re ∧ z.re ≤ b := hz.1
  have hzim : c ≤ z.im ∧ z.im ≤ d := hz.2
  let j : ℕ := ⌊(z.re - a) / δ⌋₊
  let k : ℕ := ⌊(z.im - c) / δ⌋₊
  have hj_lt : j < ⌊(b - a) / δ⌋₊ + 1 :=
    Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ.le))
  have hk_lt : k < ⌊(d - c) / δ⌋₊ + 1 :=
    Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ.le))
  refine mem_iUnion.mpr ⟨(⟨j, hj_lt⟩, ⟨k, hk_lt⟩), ?_⟩
  rw [mem_planeGridCell]
  have hj1 : (j : ℝ) * δ ≤ z.re - a :=
    (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg (by linarith) hδ.le))
  have hj2 : z.re - a < (j + 1 : ℕ) * δ := by
    push_cast
    exact (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one _)
  have hk1 : (k : ℝ) * δ ≤ z.im - c :=
    (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg (by linarith) hδ.le))
  have hk2 : z.im - c < (k + 1 : ℕ) * δ := by
    push_cast
    exact (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one _)
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Every bounded subset of `ℂ` is covered by finitely many half-open square grid cells of any
prescribed positive mesh `δ > 0`. -/
theorem _root_.Bornology.IsBounded.exists_subset_iUnion_planeGridCell {K : Set ℂ}
    (hK : Bornology.IsBounded K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a c : ℝ) (m n : ℕ), K ⊆ ⋃ p : Fin m × Fin n, planeGridCell a c δ p.1 p.2 := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  let M : ℝ := max R 0
  have hsub : K ⊆ Icc (-M) M ×ℂ Icc (-M) M := by
    intro z hz
    have hzn : ‖z‖ ≤ M := (mem_closedBall_zero_iff.mp (hR hz)).trans (le_max_left R 0)
    exact ⟨abs_le.mp ((Complex.abs_re_le_norm z).trans hzn),
      abs_le.mp ((Complex.abs_im_le_norm z).trans hzn)⟩
  exact ⟨-M, -M, ⌊(M - -M) / δ⌋₊ + 1, ⌊(M - -M) / δ⌋₊ + 1,
    hsub.trans (reProdIm_Icc_subset_iUnion_planeGridCell hδ)⟩

end PlaneGrid

section CompactQuadrature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Quantitative planar quadrature on a bounded set.** For any bounded `K₁ ⊆ ℂ` and any mesh
`δ > 0`, partitioning a bounding box of `K₁` into half-open squares of mesh `δ` and retaining the
positive-area intersections produces `N` nodes `ζ j ∈ K₁` and strictly positive weights `c j > 0`
summing to `volume.real K₁`, independent of the integrand, such that every integrable `g : ℂ → E`
whose oscillation at scale `√2 * δ` on `K₁` is at most `ω` is approximated within
`volume.real K₁ * ω`. -/
theorem _root_.Bornology.IsBounded.exists_planeQuadrature_of_oscillation (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {K₁ : Set ℂ}
    (hK₁ : Bornology.IsBounded K₁) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (c : Fin N → ℝ),
      (∀ j, ζ j ∈ K₁) ∧ (∀ j, 0 < c j) ∧ ∑ j, c j = volume.real K₁ ∧
        ∀ (g : ℂ → E) (ω : ℝ), IntegrableOn g K₁ volume →
          (∀ z ∈ K₁, ∀ w ∈ K₁, dist z w ≤ √2 * δ → ‖g z - g w‖ ≤ ω) →
          ‖(∑ j, c j • g (ζ j)) - ∫ z in K₁, g z‖ ≤ volume.real K₁ * ω := by
  obtain ⟨a, c₀, m, n, hcover⟩ := hK₁.exists_subset_iUnion_planeGridCell hδ
  have hdisj : Pairwise (Disjoint on fun p : Fin m × Fin n ↦
      planeGridCell a c₀ δ p.1 p.2) := by
    intro p q hpq
    refine @pairwiseDisjoint_planeGridCell a c₀ δ (p.1, p.2) (q.1, q.2) ?_
    rintro h
    exact hpq (Prod.ext (Fin.ext (Prod.mk.inj h).1) (Fin.ext (Prod.mk.inj h).2))
  obtain ⟨N, ζ, c, hζ, hc_pos, hc_sum, hbound⟩ :=
    exists_pos_quadrature_of_partition (E := E) (μ := volume)
      (hK₁.measure_lt_top (μ := volume)).ne
      (fun p : Fin m × Fin n ↦ measurableSet_planeGridCell a c₀ δ p.1 p.2) hdisj hcover
  refine ⟨N, ζ, c, fun j ↦ ?_, hc_pos, hc_sum, fun g ω hg hosc ↦
    hbound g ω hg fun p x hx y hy ↦
      hosc x hx.2 y hy.2 (dist_le_sqrt_two_mul_of_mem_planeGridCell hx.1 hy.1)⟩
  obtain ⟨p, hp⟩ := hζ j
  exact hp.2

/-- **Parameterized planar quadrature bound.** Under a modulus bound `ω` at scale `√2 * δ` on a
bounded set `K₁ ⊆ ℂ` that holds uniformly in an external parameter `ξ ∈ K₂` (with no topology
required on `Y`), a single finite positive-weight quadrature rule on `K₁` approximates
`∫ z in K₁, G z ξ` within `volume.real K₁ * ω` uniformly for all `ξ ∈ K₂`. -/
theorem _root_.Bornology.IsBounded.exists_planeQuadrature_norm_sub_setIntegral_le {Y : Type*}
    {K₁ : Set ℂ} {K₂ : Set Y} (hK₁ : Bornology.IsBounded K₁) {δ : ℝ} (hδ : 0 < δ)
    {G : ℂ → Y → E} {ω : ℝ}
    (hG_int : ∀ ξ ∈ K₂, IntegrableOn (fun z ↦ G z ξ) K₁ volume)
    (hG_osc : ∀ z ∈ K₁, ∀ w ∈ K₁, ∀ ξ ∈ K₂, dist z w ≤ √2 * δ → ‖G z ξ - G w ξ‖ ≤ ω) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (c : Fin N → ℝ),
      (∀ j, ζ j ∈ K₁) ∧ (∀ j, 0 < c j) ∧ ∑ j, c j = volume.real K₁ ∧
        ∀ ξ ∈ K₂, ‖(∑ j, c j • G (ζ j) ξ) - ∫ z in K₁, G z ξ‖ ≤ volume.real K₁ * ω := by
  obtain ⟨N, ζ, c, hζ, hc_pos, hc_sum, hbound⟩ := hK₁.exists_planeQuadrature_of_oscillation E hδ
  exact ⟨N, ζ, c, hζ, hc_pos, hc_sum, fun ξ hξ ↦
    hbound (fun z ↦ G z ξ) ω (hG_int ξ hξ) fun z hz w hw hzw ↦ hG_osc z hz w hw ξ hξ hzw⟩

/-- Uniform fiberwise continuity on a compact product `K₁ ×ˢ K₂`, where `K₁` lies in a pseudometric
space and `K₂` is compact in any topological space. -/
private theorem exists_pos_forall_norm_sub_lt_of_continuousOn_prod
    {X Y F : Type*} [PseudoMetricSpace X] [TopologicalSpace Y] [SeminormedAddCommGroup F]
    {K₁ : Set X} {K₂ : Set Y} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    {G : X → Y → F} (hG : ContinuousOn (uncurry G) (K₁ ×ˢ K₂)) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ K₁, ∀ x' ∈ K₁, ∀ y ∈ K₂, dist x x' < δ → ‖G x y - G x' y‖ < η := by
  rcases K₁.eq_empty_or_nonempty with rfl | hK₁ne
  · exact ⟨1, one_pos, by simp⟩
  have hloc (x : K₁) : ∃ r > 0, ∀ x' ∈ K₁, dist x' x.1 < r → ∀ y ∈ K₂,
      ‖G x' y - G x.1 y‖ < η / 2 := by
    obtain ⟨v, hv, hball⟩ :=
      hK₂.mem_uniformity_of_prod hG x.2 (Metric.dist_mem_uniformity (half_pos hη))
    obtain ⟨r, hr_pos, hr⟩ := Metric.mem_nhdsWithin_iff.mp hv
    refine ⟨r, hr_pos, fun x' hx' hdist y hy ↦ ?_⟩
    simpa only [mem_ofPred_eq, dist_eq_norm] using hball x' (hr ⟨hdist, hx'⟩) y hy
  choose r hr_pos hr using hloc
  have hcov : K₁ ⊆ ⋃ x : K₁, ball x.1 (r x / 2) := fun z hz ↦
    mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (half_pos (hr_pos ⟨z, hz⟩))⟩
  obtain ⟨s, hs_cov⟩ := hK₁.elim_finite_subcover (fun x : K₁ ↦ ball x.1 (r x / 2))
    (fun _ ↦ isOpen_ball) hcov
  obtain ⟨z₀, hz₀⟩ := hK₁ne
  obtain ⟨x₀, hx₀s, _⟩ := mem_iUnion₂.mp (hs_cov hz₀)
  have hs_ne : s.Nonempty := ⟨x₀, hx₀s⟩
  let δ : ℝ := s.inf' hs_ne fun x ↦ r x / 2
  have hδ_pos : 0 < δ := (Finset.lt_inf'_iff hs_ne).mpr fun x _ ↦ half_pos (hr_pos x)
  refine ⟨δ, hδ_pos, fun x hx x' hx' y hy hxx' ↦ ?_⟩
  obtain ⟨x₁, hx₁s, hx₁⟩ := mem_iUnion₂.mp (hs_cov hx)
  have hδ_le : δ ≤ r x₁ / 2 := Finset.inf'_le (fun x ↦ r x / 2) hx₁s
  have hdx : dist x x₁.1 < r x₁ := lt_trans hx₁ (half_lt_self (hr_pos x₁))
  have hdx' : dist x' x₁.1 < r x₁ := by
    calc dist x' x₁.1
        ≤ dist x' x + dist x x₁.1 := dist_triangle x' x x₁.1
      _ < δ + r x₁ / 2 := add_lt_add (by rwa [dist_comm]) hx₁
      _ ≤ r x₁ / 2 + r x₁ / 2 := add_le_add_left hδ_le _
      _ = r x₁ := add_halves (r x₁)
  calc ‖G x y - G x' y‖
      = ‖(G x y - G x₁.1 y) + (G x₁.1 y - G x' y)‖ := by abel_nf
    _ ≤ ‖G x y - G x₁.1 y‖ + ‖G x₁.1 y - G x' y‖ := norm_add_le _ _
    _ < η / 2 + η / 2 := by
        rw [norm_sub_rev (G x₁.1 y)]
        exact add_lt_add (hr x₁ x hx hdx y hy) (hr x₁ x' hx' hdx' y hy)
    _ = η := add_halves η

/-- **Uniform Riemann-sum quadrature on compact planar products.** For compact `K₁ ⊆ ℂ`, compact
`K₂` in any topological space `Y`, `G : ℂ → Y → E` continuous on `K₁ ×ˢ K₂`, and `ε > 0`, there
exist finitely many nodes `ζ j ∈ K₁` and strictly positive area weights `c j > 0` summing to
`volume.real K₁` such that `∑ j, c j • G (ζ j) ξ` approximates `∫ z in K₁, G z ξ` within `< ε`
uniformly for all `ξ ∈ K₂`. -/
theorem _root_.IsCompact.exists_planeQuadrature_norm_sub_setIntegral_lt
    {Y : Type*} [TopologicalSpace Y] {K₁ : Set ℂ} {K₂ : Set Y}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) {G : ℂ → Y → E}
    (hG : ContinuousOn (uncurry G) (K₁ ×ˢ K₂)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (c : Fin N → ℝ),
      (∀ j, ζ j ∈ K₁) ∧ (∀ j, 0 < c j) ∧ ∑ j, c j = volume.real K₁ ∧
        ∀ ξ ∈ K₂, ‖(∑ j, c j • G (ζ j) ξ) - ∫ z in K₁, G z ξ‖ < ε := by
  have hden : 0 < volume.real K₁ + 1 := add_pos_of_nonneg_of_pos measureReal_nonneg one_pos
  let η : ℝ := ε / (volume.real K₁ + 1)
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ₀, hδ₀, hosc⟩ :=
    exists_pos_forall_norm_sub_lt_of_continuousOn_prod hK₁ hK₂ hG hη
  let δ : ℝ := δ₀ / 2
  have hδ : 0 < δ := half_pos hδ₀
  have hsqrt : √2 * δ < δ₀ := by
    have hsqrt2 : √2 < 2 := by
      rw [Real.sqrt_lt' zero_lt_two]
      norm_num
    calc √2 * (δ₀ / 2) < 2 * (δ₀ / 2) := mul_lt_mul_of_pos_right hsqrt2 hδ
      _ = δ₀ := mul_div_cancel₀ δ₀ two_ne_zero
  have hG_int (ξ : Y) (hξ : ξ ∈ K₂) : IntegrableOn (fun z ↦ G z ξ) K₁ volume := by
    have hcont : ContinuousOn (fun z ↦ G z ξ) K₁ :=
      hG.comp (continuousOn_id.prodMk continuousOn_const) fun z hz ↦ ⟨hz, hξ⟩
    exact hcont.integrableOn_compact hK₁
  obtain ⟨N, ζ, c, hζ, hc_pos, hc_sum, hbound⟩ :=
    hK₁.isBounded.exists_planeQuadrature_norm_sub_setIntegral_le (K₂ := K₂) hδ hG_int
      fun z hz w hw ξ hξ hzw ↦ (hosc z hz w hw ξ hξ (hzw.trans_lt hsqrt)).le
  refine ⟨N, ζ, c, hζ, hc_pos, hc_sum, fun ξ hξ ↦ (hbound ξ hξ).trans_lt ?_⟩
  calc volume.real K₁ * (ε / (volume.real K₁ + 1))
      < (volume.real K₁ + 1) * (ε / (volume.real K₁ + 1)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) hη
    _ = ε := mul_div_cancel₀ ε hden.ne'

end CompactQuadrature

end TauCeti
