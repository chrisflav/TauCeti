/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.Process.TimeMeasure
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Process.Indistinguishable
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Elementary predictable integrands and the Itô integral specification

An `ElementaryIntegrand ℱ` packages a finite nondecreasing deterministic grid `grid 0 ≤ ⋯ ≤ grid n`
together with uniformly bounded heights `height i` measurable at the left endpoint `ℱ (grid i)`.
Its represented process `K.toProcess` is `TauCeti.Finance.simpleHolding` and its elementary
stochastic integral `K.integral W` is `TauCeti.Finance.simpleGains`. Common-grid refinement equips
elementary integrands with addition, scaling, subtraction, and horizon clipping while preserving
both processes and integrals pointwise everywhere.

`IsItoIntegral ℱ P W H I` characterizes a stochastic integral process `I` of a strongly predictable
integrand `H` against `W`: `I` has almost surely continuous paths, and at every horizon `t` some
sequence of elementary integrands approximates `H` in pathwise square energy in probability on
`(0, t]` while their elementary integrals at `t` converge in probability to `I t`. The error energy
is measured by the nonnegative lower Lebesgue integral against `TauCeti.Probability.timeMeasure t`,
so infinite square energy is faithfully recorded rather than collapsed to zero by Bochner defaults.

Linearity, congruence under indistinguishable processes and product-a.e. equal predictable
integrands, and initial vanishing hold directly from the specification. Against a filtered
pre-Brownian motion `W`, the elementary energy-to-probability estimate yields uniqueness up to
indistinguishability (`IsItoIntegral.indist`) and independence of the product-a.e. integrand
representative (`IsItoIntegral.indist_of_ae_eq`), without path continuity of `W` or usual
conditions on `ℱ`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}

/-! ### Elementary predictable integrands -/

/-- A bounded elementary predictable integrand on a finite nondecreasing deterministic grid: on each
interval `(grid i, grid (i + 1)]` (`i < n`) it holds the uniformly bounded `ℱ (grid i)`-measurable
random height `height i`. -/
structure ElementaryIntegrand (ℱ : Filtration ℝ≥0 mΩ) where
  /-- The number of intervals in the partition. -/
  n : ℕ
  /-- The deterministic grid times, monotone through index `n`. -/
  grid : ℕ → ℝ≥0
  /-- Monotonicity of the grid up to its last index `n`. -/
  mono : MonotoneOn grid (Set.Iic n)
  /-- The random height held on `(grid i, grid (i + 1)]`. -/
  height : ℕ → Ω → ℝ
  /-- Each height is measurable at the left endpoint of its interval. -/
  stronglyMeasurable : ∀ i < n, StronglyMeasurable[ℱ (grid i)] (height i)
  /-- Each height is uniformly bounded. -/
  bounded : ∀ i < n, ∃ C : ℝ, ∀ ω, ‖height i ω‖ ≤ C

namespace ElementaryIntegrand

variable {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- The predictable step process `t ↦ ∑ i < K.n, K.height i · 1_{(K.grid i, K.grid (i + 1)]}(t)`. -/
def toProcess (K : ElementaryIntegrand ℱ) : ℝ≥0 → Ω → ℝ :=
  Finance.simpleHolding K.grid K.n K.height

/-- Unfolding lemma for `ElementaryIntegrand.toProcess`. -/
theorem toProcess_def (K : ElementaryIntegrand ℱ) :
    K.toProcess = Finance.simpleHolding K.grid K.n K.height := (rfl)

/-- The elementary stochastic integral process
`t ↦ ∑ i < K.n, K.height i · (W (min (K.grid (i + 1)) t) - W (min (K.grid i) t))`. -/
def integral (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  Finance.simpleGains K.grid K.n K.height W

/-- Unfolding lemma for `ElementaryIntegrand.integral`. -/
theorem integral_def (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) :
    K.integral W = Finance.simpleGains K.grid K.n K.height W := (rfl)

/-- The process represented by an elementary integrand is strongly predictable. -/
theorem isStronglyPredictable (K : ElementaryIntegrand ℱ) :
    IsStronglyPredictable ℱ K.toProcess :=
  Finance.isStronglyPredictable_simpleHolding K.stronglyMeasurable

/-- Each height of an elementary integrand belongs to every `Lᵖ` space of a finite measure. -/
theorem memLp_height [IsFiniteMeasure P] (K : ElementaryIntegrand ℱ) {i : ℕ} (hi : i < K.n)
    (p : ℝ≥0∞) : MemLp (K.height i) p P := by
  obtain ⟨C, hC⟩ := K.bounded i hi
  exact MemLp.of_bound ((K.stronglyMeasurable i hi).mono (ℱ.le _)).aestronglyMeasurable C
    (Eventually.of_forall hC)

/-- Every elementary integrand belongs to the expected-square-energy domain under a finite
measure. -/
theorem brownianIntegrable [IsFiniteMeasure P] (K : ElementaryIntegrand ℱ) :
    BrownianIntegrable ℱ P K.toProcess := by
  refine ⟨K.isStronglyPredictable, fun T ↦ ?_⟩
  rw [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def]
  exact (ℱ.memLp_predictableMeasure_iff P K.isStronglyPredictable T 2).mp
    (Finance.memLp_simpleHolding_predictableMeasure K.stronglyMeasurable
      (fun i hi ↦ K.memLp_height hi 2) T)

/-- Every elementary stochastic integral vanishes at time zero. -/
@[simp]
theorem integral_zero_time (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    K.integral W 0 ω = 0 :=
  Finance.simpleGains_of_le K.mono bot_le W ω

/-- The elementary integral against a strongly adapted integrator is strongly adapted. -/
theorem stronglyAdapted_integral (K : ElementaryIntegrand ℱ) (hW : StronglyAdapted ℱ W) :
    StronglyAdapted ℱ (K.integral W) :=
  Finance.stronglyAdapted_simpleGains K.mono K.stronglyMeasurable hW

/-- Almost surely continuous integrator paths yield almost surely continuous elementary integral
paths. -/
theorem ae_continuous_integral (K : ElementaryIntegrand ℱ)
    (hW : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) :
    ∀ᵐ ω ∂P, Continuous (fun t ↦ K.integral W t ω) := by
  filter_upwards [hW] with ω hω
  simp only [integral_def, Finance.simpleGains_def]
  exact continuous_finsetSum _ fun _ _ ↦ continuous_const.mul
    ((hω.comp (continuous_const.min continuous_id)).sub
      (hω.comp (continuous_const.min continuous_id)))

/-- The elementary integral of a bounded elementary integrand against a martingale is a
martingale. -/
theorem martingale_integral [SigmaFiniteFiltration P ℱ] (K : ElementaryIntegrand ℱ)
    (hM : Martingale W ℱ P) : Martingale (K.integral W) ℱ P := by
  refine hM.simpleGains_of_bdd K.mono K.stronglyMeasurable fun i hi ↦ ?_
  obtain ⟨C, hC⟩ := K.bounded i hi
  exact ⟨C, Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hC ω⟩

/-- The zero elementary integrand (empty grid). -/
def zero : ElementaryIntegrand ℱ where
  n := 0
  grid := fun _ ↦ 0
  mono := fun _ _ _ _ _ ↦ le_rfl
  height := fun _ _ ↦ 0
  stronglyMeasurable := fun _ hi ↦ (Nat.not_lt_zero _ hi).elim
  bounded := fun _ hi ↦ (Nat.not_lt_zero _ hi).elim

/-- The zero elementary integrand represents the zero process. -/
@[simp]
theorem toProcess_zero : (zero (ℱ := ℱ)).toProcess = 0 := by
  ext t ω
  simp [toProcess_def, Finance.simpleHolding_def, zero]

/-- The elementary integral of the zero integrand vanishes identically. -/
@[simp]
theorem integral_zero (W : ℝ≥0 → Ω → ℝ) : (zero (ℱ := ℱ)).integral W = 0 := by
  ext t ω
  simp [integral_def, Finance.simpleGains_def, zero]

/-- A one-interval elementary integrand holding `ξ` on `(s, t]`. -/
def single (s t : ℝ≥0) (hst : s ≤ t) (ξ : Ω → ℝ) (hξ : StronglyMeasurable[ℱ s] ξ)
    (hb : ∃ C : ℝ, ∀ ω, ‖ξ ω‖ ≤ C) : ElementaryIntegrand ℱ where
  n := 1
  grid := fun i ↦ if i = 0 then s else t
  mono := by
    intro i _ j _ hij
    dsimp only
    split_ifs with hi hj
    · exact le_rfl
    · exact hst
    · omega
    · exact le_rfl
  height := fun _ ↦ ξ
  stronglyMeasurable := fun i hi ↦ by
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst hi0
    simpa using hξ
  bounded := fun _ _ ↦ hb

/-- The process represented by a one-interval elementary integrand is the indicator of `(s, t]`. -/
@[simp]
theorem toProcess_single (s t : ℝ≥0) (hst : s ≤ t) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ s] ξ) (hb : ∃ C : ℝ, ∀ ω, ‖ξ ω‖ ≤ C) (u : ℝ≥0) (ω : Ω) :
    (single s t hst ξ hξ hb).toProcess u ω = (Set.Ioc s t).indicator (fun _ ↦ ξ ω) u := by
  simp [toProcess_def, Finance.simpleHolding_def, single]

/-- The elementary integral of a one-interval integrand is the single stopped increment. -/
@[simp]
theorem integral_single (s t : ℝ≥0) (hst : s ≤ t) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ s] ξ) (hb : ∃ C : ℝ, ∀ ω, ‖ξ ω‖ ≤ C)
    (W : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) :
    (single s t hst ξ hξ hb).integral W u ω = ξ ω * (W (min t u) ω - W (min s u) ω) := by
  simp [integral_def, Finance.simpleGains_def, single]

/-- Scale an elementary integrand by a real constant without changing its grid. -/
def smul (c : ℝ) (K : ElementaryIntegrand ℱ) : ElementaryIntegrand ℱ where
  n := K.n
  grid := K.grid
  mono := K.mono
  height := c • K.height
  stronglyMeasurable := fun i hi ↦ (K.stronglyMeasurable i hi).const_mul c
  bounded := fun i hi ↦ by
    obtain ⟨C, hC⟩ := K.bounded i hi
    refine ⟨‖c‖ * C, fun ω ↦ ?_⟩
    simpa only [Pi.smul_apply, smul_eq_mul, norm_mul] using
      mul_le_mul_of_nonneg_left (hC ω) (norm_nonneg c)

/-- Scaling an elementary integrand scales its represented process pointwise. -/
@[simp]
theorem toProcess_smul (c : ℝ) (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    (K.smul c).toProcess t ω = c * K.toProcess t ω :=
  Finance.simpleHolding_smul K.grid K.n c K.height t ω

/-- Scaling an elementary integrand scales its elementary integral pointwise. -/
@[simp]
theorem integral_smul (c : ℝ) (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (K.smul c).integral W t ω = c * K.integral W t ω :=
  Finance.simpleGains_smul K.grid K.n c K.height W t ω

/-- Negate an elementary integrand without changing its grid. -/
def neg (K : ElementaryIntegrand ℱ) : ElementaryIntegrand ℱ := K.smul (-1)

/-- Negating an elementary integrand negates its represented process pointwise. -/
@[simp]
theorem toProcess_neg (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    K.neg.toProcess t ω = -K.toProcess t ω := by
  simp [neg]

/-- Negating an elementary integrand negates its elementary integral pointwise. -/
@[simp]
theorem integral_neg (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    K.neg.integral W t ω = -K.integral W t ω := by
  simp [neg]

/-- Auxiliary refinement data realizing the pointwise sum of two elementary integrands on a
common strictly increasing grid. -/
private theorem exists_add_repr (K L : ElementaryIntegrand ℱ) :
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (b : ℕ → Ω → ℝ),
      MonotoneOn τ (Set.Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (b j)) ∧
      (∀ j < n, ∃ C : ℝ, ∀ ω, ‖b j ω‖ ≤ C) ∧
      (∀ t ω, Finance.simpleHolding τ n b t ω = K.toProcess t ω + L.toProcess t ω) ∧
      ∀ (W : ℝ≥0 → Ω → ℝ) t ω,
        Finance.simpleGains τ n b W t ω = K.integral W t ω + L.integral W t ω := by
  let l : Fin K.n ⊕ Fin L.n → ℝ≥0 := Sum.elim (fun i ↦ K.grid i) (fun j ↦ L.grid j)
  let u : Fin K.n ⊕ Fin L.n → ℝ≥0 :=
    Sum.elim (fun i ↦ K.grid (i.1 + 1)) (fun j ↦ L.grid (j.1 + 1))
  let a : Fin K.n ⊕ Fin L.n → Ω → ℝ := Sum.elim (fun i ↦ K.height i) (fun j ↦ L.height j)
  have ha : ∀ x ∈ (Finset.univ : Finset (Fin K.n ⊕ Fin L.n)),
      StronglyMeasurable[ℱ (l x)] (a x) := by
    rintro (i | j) _
    · exact K.stronglyMeasurable i.1 i.2
    · exact L.stronglyMeasurable j.1 j.2
  have hle : ∀ x : Fin K.n ⊕ Fin L.n, l x ≤ u x := by
    rintro (i | j)
    · exact K.mono i.2.le i.2 (Nat.le_succ _)
    · exact L.mono j.2.le j.2 (Nat.le_succ _)
  choose CK hCK using K.bounded
  choose CL hCL using L.bounded
  obtain ⟨n, τ, b, -, hτ, hb, hbound, hhold, hgain⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ Finset.univ l u a ha
  refine ⟨n, τ, b, hτ.monotoneOn, hb, fun j hj ↦ ?_, fun t ω ↦ ?_, fun W t ω ↦ ?_⟩
  · refine ⟨(∑ i : Fin K.n, CK i.1 i.2) + ∑ j : Fin L.n, CL j.1 j.2, fun ω ↦ ?_⟩
    refine (hbound j hj ω).trans ?_
    rw [Fintype.sum_sum_type]
    exact add_le_add (sum_le_sum fun i _ ↦ hCK i.1 i.2 ω) (sum_le_sum fun j _ ↦ hCL j.1 j.2 ω)
  · rw [hhold, Fintype.sum_sum_type]
    simp only [toProcess_def, Finance.simpleHolding_def, l, u, a, Sum.elim_inl, Sum.elim_inr]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ (Set.Ioc (K.grid j) (K.grid (j + 1))).indicator
      (fun _ ↦ K.height j ω) t),
      Fin.sum_univ_eq_sum_range (fun j ↦ (Set.Ioc (L.grid j) (L.grid (j + 1))).indicator
      (fun _ ↦ L.height j ω) t)]
  · rw [hgain]
    simp only [hle, ↓reduceIte]
    rw [Fintype.sum_sum_type]
    simp only [integral_def, Finance.simpleGains_def, l, u, a, Sum.elim_inl, Sum.elim_inr]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ K.height j ω * (W (min (K.grid (j + 1)) t) ω -
      W (min (K.grid j) t) ω)),
      Fin.sum_univ_eq_sum_range (fun j ↦ L.height j ω * (W (min (L.grid (j + 1)) t) ω -
      W (min (L.grid j) t) ω))]

/-- Sum of two elementary integrands, constructed on a common refined grid. -/
def add (K L : ElementaryIntegrand ℱ) : ElementaryIntegrand ℱ where
  n := (exists_add_repr K L).choose
  grid := (exists_add_repr K L).choose_spec.choose
  height := (exists_add_repr K L).choose_spec.choose_spec.choose
  mono := (exists_add_repr K L).choose_spec.choose_spec.choose_spec.1
  stronglyMeasurable := (exists_add_repr K L).choose_spec.choose_spec.choose_spec.2.1
  bounded := (exists_add_repr K L).choose_spec.choose_spec.choose_spec.2.2.1

/-- Adding two elementary integrands adds their represented processes pointwise. -/
@[simp]
theorem toProcess_add (K L : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    (K.add L).toProcess t ω = K.toProcess t ω + L.toProcess t ω :=
  (exists_add_repr K L).choose_spec.choose_spec.choose_spec.2.2.2.1 t ω

/-- Adding two elementary integrands adds their elementary integrals pointwise. -/
@[simp]
theorem integral_add (K L : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (K.add L).integral W t ω = K.integral W t ω + L.integral W t ω :=
  (exists_add_repr K L).choose_spec.choose_spec.choose_spec.2.2.2.2 W t ω

/-- Difference of two elementary integrands, constructed on a common refined grid. -/
def sub (K L : ElementaryIntegrand ℱ) : ElementaryIntegrand ℱ := K.add L.neg

/-- Subtracting two elementary integrands subtracts their represented processes pointwise. -/
@[simp]
theorem toProcess_sub (K L : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    (K.sub L).toProcess t ω = K.toProcess t ω - L.toProcess t ω := by
  simp [sub, sub_eq_add_neg]

/-- Subtracting two elementary integrands subtracts their elementary integrals pointwise. -/
@[simp]
theorem integral_sub (K L : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (K.sub L).integral W t ω = K.integral W t ω - L.integral W t ω := by
  simp [sub, sub_eq_add_neg]

/-- Clip an elementary integrand to the horizon `T`: every grid date is replaced by `min · T`, and
intervals starting after `T` are zeroed out. -/
def clip (K : ElementaryIntegrand ℱ) (T : ℝ≥0) : ElementaryIntegrand ℱ where
  n := K.n
  grid := fun i ↦ min (K.grid i) T
  mono := fun _ hi _ hj hij ↦ min_le_min_right T (K.mono hi hj hij)
  height := fun i ↦ if K.grid i ≤ T then K.height i else 0
  stronglyMeasurable := fun i hi ↦ by
    split_ifs with hle
    · rw [min_eq_left hle]
      exact K.stronglyMeasurable i hi
    · exact stronglyMeasurable_const
  bounded := fun i hi ↦ by
    split_ifs with hle
    · exact K.bounded i hi
    · exact ⟨0, fun _ ↦ by simp⟩

/-- Up to the clipping horizon, the clipped elementary integrand agrees pointwise with the original
one. -/
theorem toProcess_clip_of_le (K : ElementaryIntegrand ℱ) {T s : ℝ≥0} (hs : s ≤ T) (ω : Ω) :
    (K.clip T).toProcess s ω = K.toProcess s ω := by
  simp only [toProcess_def, Finance.simpleHolding_def, clip]
  refine sum_congr rfl fun j _ ↦ ?_
  by_cases hj : K.grid j ≤ T
  · simp only [hj, ↓reduceIte, min_eq_left hj, Set.indicator_apply, Set.mem_Ioc, le_min_iff, hs,
      and_true]
  · have hsj : ¬ K.grid j < s := not_lt.mpr (hs.trans (le_of_not_ge hj))
    simp [hj, hsj]

/-- Up to the clipping horizon, the clipped elementary integral agrees pointwise with the original
one. -/
theorem integral_clip_of_le (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) {T t : ℝ≥0}
    (ht : t ≤ T) (ω : Ω) : (K.clip T).integral W t ω = K.integral W t ω := by
  simp only [integral_def, Finance.simpleGains_def, clip]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' := mem_range.mp hj
  have hmin (x : ℝ≥0) : min (min x T) t = min x t := by rw [min_assoc, min_eq_right ht]
  by_cases hle : K.grid j ≤ T
  · simp only [hle, ↓reduceIte, hmin]
  · have hTj : T ≤ K.grid j := le_of_not_ge hle
    have hTj1 : T ≤ K.grid (j + 1) := hTj.trans (K.mono hj'.le hj' (Nat.le_succ j))
    simp [hle, min_eq_right (ht.trans hTj), min_eq_right (ht.trans hTj1)]

/-- At its clipping horizon, the clipped elementary integral is an unclipped increment sum over the
clipped grid. -/
theorem integral_clip_eq_sum (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    K.integral W T ω = ∑ i ∈ range (K.clip T).n,
      (K.clip T).height i ω * (W ((K.clip T).grid (i + 1)) ω - W ((K.clip T).grid i) ω) := by
  rw [← K.integral_clip_of_le W le_rfl ω]
  simp only [integral_def, Finance.simpleGains_def]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [clip, min_eq_left (min_le_right _ _)]

/-- On `(0, T]`, the lower square-energy integral of an elementary integrand equals the finite-grid
`Probability.elementaryEnergy` of its clipped grid. -/
theorem lintegral_enorm_sq_toProcess_clip (K : ElementaryIntegrand ℱ) (T : ℝ≥0) (ω : Ω) :
    ∫⁻ s, ‖K.toProcess s ω‖ₑ ^ 2 ∂Probability.timeMeasure T =
      ENNReal.ofReal (Probability.elementaryEnergy (K.clip T).grid (K.clip T).height
        (K.clip T).n ω) := by
  have hcongr : (fun s ↦ ‖K.toProcess s ω‖ₑ ^ 2) =ᵐ[Probability.timeMeasure T]
      fun s ↦ ‖(K.clip T).toProcess s ω‖ₑ ^ 2 := by
    filter_upwards [Probability.ae_mem_Ioc_timeMeasure T] with s hs
    rw [K.toProcess_clip_of_le hs.2 ω]
  rw [lintegral_congr_ae hcongr, toProcess_def,
    Finance.lintegral_enorm_sq_simpleHolding_timeMeasure (K.clip T).mono T ω,
    Probability.elementaryEnergy_def, ENNReal.ofReal_sum_of_nonneg]
  · refine sum_congr rfl fun j _ ↦ ?_
    have hmin : min ((K.clip T).grid (j + 1)) T = (K.clip T).grid (j + 1) :=
      min_eq_left (min_le_right _ _)
    rw [hmin, ENNReal.ofReal_mul (sq_nonneg _), ← sq_abs ((K.clip T).height j ω),
      ENNReal.ofReal_pow (abs_nonneg _)]
    simp only [Real.eNorm_eq_ofReal_abs]
  · intro j hj
    have hj' := mem_range.mp hj
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
      ((K.clip T).mono hj'.le hj' (Nat.le_succ j))))

end ElementaryIntegrand

/-! ### Private convergence-in-measure helpers -/

private theorem tendstoInMeasure_const_self {α ι E : Type*} [MeasurableSpace α] {μ : Measure α}
    [PseudoEMetricSpace E] {l : Filter ι} (f : α → E) :
    TendstoInMeasure μ (fun _ ↦ f) l f := by
  intro ε hε
  simpa [hε.ne'] using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0∞)) l (𝓝 0))

private theorem tendstoInMeasure_add {α ι E : Type*} [MeasurableSpace α] {μ : Measure α}
    [SeminormedAddCommGroup E] {l : Filter ι} {f₁ f₂ : ι → α → E} {g₁ g₂ : α → E}
    (h₁ : TendstoInMeasure μ f₁ l g₁) (h₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i x ↦ f₁ i x + f₂ i x) l (fun x ↦ g₁ x + g₂ x) := by
  rw [tendstoInMeasure_iff_norm] at h₁ h₂ ⊢
  intro ε hε
  have hsum := (h₁ (ε / 2) (half_pos hε)).add (h₂ (ε / 2) (half_pos hε))
  rw [zero_add] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le) fun i ↦
    (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
  simp only [mem_ofPred_eq, mem_union] at hx ⊢
  by_contra! h
  have htri : ‖f₁ i x + f₂ i x - (g₁ x + g₂ x)‖ ≤ ‖f₁ i x - g₁ x‖ + ‖f₂ i x - g₂ x‖ := by
    simpa only [add_sub_add_comm] using norm_add_le (f₁ i x - g₁ x) (f₂ i x - g₂ x)
  linarith

private theorem tendstoInMeasure_const_mul {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} {f : ι → α → ℝ} {g : α → ℝ} (h : TendstoInMeasure μ f l g) (c : ℝ) :
    TendstoInMeasure μ (fun i x ↦ c * f i x) l (fun x ↦ c * g x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa only [zero_mul] using tendstoInMeasure_const_self (μ := μ) (l := l) (fun _ : α ↦ (0 : ℝ))
  · rw [tendstoInMeasure_iff_norm] at h ⊢
    intro ε hε
    have hdiv : 0 < ε / ‖c‖ := div_pos hε (norm_pos_iff.mpr hc)
    refine (h (ε / ‖c‖) hdiv).congr fun i ↦ ?_
    congr 1
    ext x
    simp only [mem_ofPred_eq, ← mul_sub, norm_mul, div_le_iff₀' (norm_pos_iff.mpr hc)]

private theorem tendstoInMeasure_sub {α ι E : Type*} [MeasurableSpace α] {μ : Measure α}
    [SeminormedAddCommGroup E] {l : Filter ι} {f₁ f₂ : ι → α → E} {g₁ g₂ : α → E}
    (h₁ : TendstoInMeasure μ f₁ l g₁) (h₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i x ↦ f₁ i x - f₂ i x) l (fun x ↦ g₁ x - g₂ x) := by
  have hneg : TendstoInMeasure μ (fun i x ↦ -f₂ i x) l (fun x ↦ -g₂ x) := by
    rw [tendstoInMeasure_iff_norm] at h₂ ⊢
    intro ε hε
    simpa only [neg_sub_neg, norm_sub_rev] using h₂ ε hε
  simpa only [sub_eq_add_neg] using tendstoInMeasure_add h₁ hneg

private theorem enorm_add_sq_le_two_mul (a b : ℝ) :
    ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have h := ENNReal.ofReal_le_ofReal (norm_sub_sq_le_two_mul a (-b) 0)
  simp only [sub_neg_eq_add, sub_zero, norm_neg,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_ofNat] at h
  simpa only [mul_add] using h

private theorem tendsto_measure_lintegral_two_mul_add {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} {E₁ E₂ : ι → α → ℝ≥0∞}
    (h₁ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ μ {x | ε ≤ E₁ i x}) l (𝓝 0))
    (h₂ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ μ {x | ε ≤ E₂ i x}) l (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun i ↦ μ {x | ε ≤ 2 * E₁ i x + 2 * E₂ i x}) l (𝓝 0) := by
  have hε4 : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  have hsum := (h₁ (ε / 4) hε4).add (h₂ (ε / 4) hε4)
  rw [zero_add] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le) fun i ↦
    (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
  simp only [mem_ofPred_eq, mem_union] at hx ⊢
  by_contra! h
  rcases h with ⟨hx₁, hx₂⟩
  rcases eq_or_ne ε ∞ with rfl | _
  · simp only [ENNReal.top_div_of_ne_top (by norm_num : (4 : ℝ≥0∞) ≠ ∞)] at hx₁ hx₂
    have hlt : 2 * E₁ i x + 2 * E₂ i x < ∞ :=
      ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hx₁,
        ENNReal.mul_lt_top (by norm_num) hx₂⟩
    exact hlt.not_ge hx
  · have h2 : 2 * E₁ i x < 2 * (ε / 4) :=
      ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hx₁
    have h2' : 2 * E₂ i x < 2 * (ε / 4) :=
      ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hx₂
    have hadd : 2 * E₁ i x + 2 * E₂ i x < 2 * (ε / 4) + 2 * (ε / 4) :=
      ENNReal.add_lt_add h2 h2'
    have heq : 2 * (ε / 4) + 2 * (ε / 4) = ε := by
      rw [← add_mul, show (2 : ℝ≥0∞) + 2 = 4 by norm_num,
        ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    rw [heq] at hadd
    exact hadd.not_ge hx

private theorem indist_of_ae_eq_of_ae_continuous {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}
    (hX : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    (hY : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω))
    (heq : ∀ t : ℝ≥0, X t =ᵐ[P] Y t) : X ≡ᵐ[P] Y := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hD : ∀ᵐ ω ∂P, ∀ t ∈ D, X t ω = Y t ω := (ae_ball_iff hDc).mpr fun t _ ↦ heq t
  filter_upwards [hX, hY, hD] with ω hXω hYω hDω t
  exact congrFun (hXω.ext_on hDd hYω hDω) t

/-! ### The Itô integral specification -/

/-- `I` is an **Itô integral** of the strongly predictable integrand `H` against `W` under `P` if
`I` has almost surely continuous paths and, at every horizon `t`, some sequence of bounded
elementary integrands approximates `H` in pathwise square energy in probability on `(0, t]` while
their elementary integrals at `t` converge in probability to `I t`. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W H I : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is strongly predictable for `ℱ`. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- Almost every sample path of the integral is continuous. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous fun t ↦ I t ω
  /-- At every horizon `t`, some sequence of elementary integrands approximates `H` in pathwise
  square energy in probability on `(0, t]` while their elementary integrals at `t` converge in
  probability to `I t`. -/
  approx : ∀ t : ℝ≥0, ∃ K : ℕ → ElementaryIntegrand ℱ,
    (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n ↦ P {ω | ε ≤
      ∫⁻ s, ‖(K n).toProcess s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0)) ∧
    TendstoInMeasure P (fun n ↦ (K n).integral W t) atTop (I t)

variable {P : Measure Ω} {W H H₁ H₂ I I₁ I₂ J : ℝ≥0 → Ω → ℝ}

/-- The elementary integral of an elementary integrand against an almost surely continuous
integrator satisfies the Itô integral specification. -/
theorem IsItoIntegral.of_elementaryIntegrand (K : ElementaryIntegrand ℱ)
    (hW : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) :
    IsItoIntegral ℱ P W K.toProcess (K.integral W) where
  isStronglyPredictable := K.isStronglyPredictable
  ae_continuous := K.ae_continuous_integral hW
  approx t := ⟨fun _ ↦ K, fun ε hε ↦ by simp [hε.ne'], tendstoInMeasure_const_self _⟩

/-- The zero process is an Itô integral of the zero integrand, with no hypotheses on `W` or `P`. -/
theorem isItoIntegral_zero : IsItoIntegral ℱ P W 0 0 where
  isStronglyPredictable := by
    simpa only [ElementaryIntegrand.toProcess_zero] using
      (ElementaryIntegrand.zero (ℱ := ℱ)).isStronglyPredictable
  ae_continuous := Eventually.of_forall fun _ ↦ continuous_const
  approx t := ⟨fun _ ↦ ElementaryIntegrand.zero, fun ε hε ↦ by simp [hε.ne'], by
    simp only [ElementaryIntegrand.integral_zero]
    exact tendstoInMeasure_const_self _⟩

/-- Replacing the integral process by an indistinguishable process preserves `IsItoIntegral`. -/
theorem IsItoIntegral.congr_process (hI : IsItoIntegral ℱ P W H I) (hIJ : I ≡ᵐ[P] J) :
    IsItoIntegral ℱ P W H J where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hIJ] with ω hω heq
    exact hω.congr fun t ↦ heq t
  approx t := by
    obtain ⟨K, hE, hM⟩ := hI.approx t
    exact ⟨K, hE, hM.congr_right (hIJ.ae_eq_eval t)⟩

/-- Integrating a deterministic constant `c` against an almost surely continuous process `W` yields
`t ↦ c * (W t - W 0)`. -/
theorem isItoIntegral_const_sub_zero (hW : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (c : ℝ) :
    IsItoIntegral ℱ P W (fun _ _ ↦ c) (fun t ω ↦ c * (W t ω - W 0 ω)) where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := by
    filter_upwards [hW] with ω hω
    exact continuous_const.mul (hω.sub continuous_const)
  approx t := by
    let K : ElementaryIntegrand ℱ :=
      ElementaryIntegrand.single 0 t bot_le (fun _ ↦ c) stronglyMeasurable_const
        ⟨‖c‖, fun _ ↦ le_rfl⟩
    refine ⟨fun _ ↦ K, fun ε hε ↦ ?_, ?_⟩
    · have hzero (ω : Ω) :
          ∫⁻ s, ‖K.toProcess s ω - c‖ₑ ^ 2 ∂Probability.timeMeasure t = 0 := by
        refine (lintegral_congr_ae ?_).trans lintegral_zero
        filter_upwards [Probability.ae_mem_Ioc_timeMeasure t] with s hs
        simp [K, ElementaryIntegrand.toProcess_single, hs]
      simp [hzero, hε.ne']
    · have hK : K.integral W t = fun ω ↦ c * (W t ω - W 0 ω) := by
        ext ω
        simp [K, ElementaryIntegrand.integral_single]
      dsimp only
      rw [hK]
      exact tendstoInMeasure_const_self _

/-- Integrating a deterministic constant `c` against an almost surely continuous process started
almost surely at zero yields `t ↦ c * W t`. -/
theorem isItoIntegral_const (hW : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (h0 : ∀ᵐ ω ∂P, W 0 ω = 0) (c : ℝ) :
    IsItoIntegral ℱ P W (fun _ _ ↦ c) (fun t ω ↦ c * W t ω) := by
  refine (isItoIntegral_const_sub_zero (ℱ := ℱ) hW c).congr_process ?_
  filter_upwards [h0] with ω hω t
  simp [hω]

/-- Every Itô integral vanishes almost surely at time zero. -/
theorem IsItoIntegral.ae_eq_zero_at_zero (hI : IsItoIntegral ℱ P W H I) :
    I 0 =ᵐ[P] 0 := by
  obtain ⟨K, -, hM⟩ := hI.approx 0
  have hzero : (fun n ↦ (K n).integral W 0) = fun _ ↦ (0 : Ω → ℝ) := by
    ext n ω
    exact (K n).integral_zero_time W ω
  rw [hzero] at hM
  exact tendstoInMeasure_ae_unique hM (tendstoInMeasure_const_self (0 : Ω → ℝ))

/-- Replacing the integrand by a strongly predictable process agreeing with it `dt × P`-almost
everywhere on every finite horizon preserves `IsItoIntegral`. -/
theorem IsItoIntegral.congr_integrand [SFinite P] (hI : IsItoIntegral ℱ P W H₁ I)
    (hH₂ : IsStronglyPredictable ℱ H₂)
    (hH : ∀ T : ℝ≥0, Function.uncurry H₁ =ᵐ[(Probability.timeMeasure T).prod P]
      Function.uncurry H₂) :
    IsItoIntegral ℱ P W H₂ I where
  isStronglyPredictable := hH₂
  ae_continuous := hI.ae_continuous
  approx t := by
    obtain ⟨K, hE, hM⟩ := hI.approx t
    have hae : ∀ᵐ ω ∂P, (fun s ↦ H₁ s ω) =ᵐ[Probability.timeMeasure t] (fun s ↦ H₂ s ω) :=
      Measure.ae_ae_of_ae_prod
        ((Measure.measurePreserving_swap
          (μ := P) (ν := Probability.timeMeasure t)).quasiMeasurePreserving.ae_eq_comp (hH t))
    refine ⟨K, fun ε hε ↦ (hE ε hε).congr fun n ↦ measure_congr ?_, hM⟩
    filter_upwards [hae] with ω hω
    have hlint : ∫⁻ s, ‖(K n).toProcess s ω - H₁ s ω‖ₑ ^ 2 ∂Probability.timeMeasure t =
        ∫⁻ s, ‖(K n).toProcess s ω - H₂ s ω‖ₑ ^ 2 ∂Probability.timeMeasure t :=
      lintegral_congr_ae (hω.mono fun s hs ↦ by simp [hs])
    simp [hlint]

/-- Linearity of the Itô integral specification: addition. -/
theorem IsItoIntegral.add (h₁ : IsItoIntegral ℱ P W H₁ I₁)
    (h₂ : IsItoIntegral ℱ P W H₂ I₂) :
    IsItoIntegral ℱ P W (fun t ω ↦ H₁ t ω + H₂ t ω) (fun t ω ↦ I₁ t ω + I₂ t ω) where
  isStronglyPredictable := h₁.isStronglyPredictable.add h₂.isStronglyPredictable
  ae_continuous := by
    filter_upwards [h₁.ae_continuous, h₂.ae_continuous] with ω hω₁ hω₂
    exact hω₁.add hω₂
  approx t := by
    obtain ⟨K₁, hE₁, hM₁⟩ := h₁.approx t
    obtain ⟨K₂, hE₂, hM₂⟩ := h₂.approx t
    refine ⟨fun n ↦ (K₁ n).add (K₂ n), fun ε hε ↦ ?_, ?_⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_measure_lintegral_two_mul_add hE₁ hE₂ hε) (fun _ ↦ zero_le) fun n ↦
        measure_mono fun ω hω ↦ ?_
      simp only [mem_ofPred_eq] at hω ⊢
      refine hω.trans ?_
      have hm₁ : Measurable (fun s ↦ ‖(K₁ n).toProcess s ω - H₁ s ω‖ₑ ^ 2) :=
        ((((K₁ n).isStronglyPredictable.sub h₁.isStronglyPredictable).mono
          ℱ.predictable_le_prod).measurable.comp (measurable_id.prodMk measurable_const))
          |>.eNorm.pow_const 2
      calc
        ∫⁻ s, ‖((K₁ n).add (K₂ n)).toProcess s ω - (H₁ s ω + H₂ s ω)‖ₑ ^ 2
            ∂Probability.timeMeasure t
          ≤ ∫⁻ s, (2 * ‖(K₁ n).toProcess s ω - H₁ s ω‖ₑ ^ 2 +
              2 * ‖(K₂ n).toProcess s ω - H₂ s ω‖ₑ ^ 2) ∂Probability.timeMeasure t := by
            refine lintegral_mono fun s ↦ ?_
            rw [ElementaryIntegrand.toProcess_add, add_sub_add_comm]
            exact enorm_add_sq_le_two_mul _ _
        _ = 2 * ∫⁻ s, ‖(K₁ n).toProcess s ω - H₁ s ω‖ₑ ^ 2 ∂Probability.timeMeasure t +
            2 * ∫⁻ s, ‖(K₂ n).toProcess s ω - H₂ s ω‖ₑ ^ 2 ∂Probability.timeMeasure t := by
            rw [lintegral_add_left (hm₁.const_mul 2),
              lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    · refine (tendstoInMeasure_add hM₁ hM₂).congr_left fun n ↦ Eventually.of_forall fun ω ↦ ?_
      exact ((K₁ n).integral_add (K₂ n) W t ω).symm

/-- Linearity of the Itô integral specification: scalar multiplication. -/
theorem IsItoIntegral.const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_mul]
    exact isItoIntegral_zero
  · refine ⟨hI.isStronglyPredictable.const_mul c, ?_, fun t ↦ ?_⟩
    · filter_upwards [hI.ae_continuous] with ω hω
      exact continuous_const.mul hω
    · obtain ⟨K, hE, hM⟩ := hI.approx t
      refine ⟨fun n ↦ (K n).smul c, fun ε hε ↦ ?_, ?_⟩
      · have hc2_pos : (0 : ℝ≥0∞) < ‖c‖ₑ ^ 2 := ENNReal.pow_pos (eNorm_pos.mpr hc) 2
        have hc2_top : ‖c‖ₑ ^ 2 ≠ ∞ := ENNReal.pow_ne_top eNorm_ne_top
        have hε' : 0 < ε / ‖c‖ₑ ^ 2 := ENNReal.div_pos hε.ne' hc2_top
        refine (hE (ε / ‖c‖ₑ ^ 2) hε').congr fun n ↦ ?_
        congr 1
        ext ω
        simp only [mem_ofPred_eq, ElementaryIntegrand.toProcess_smul, ← mul_sub, eNorm_mul,
          mul_pow, lintegral_const_mul' _ _ hc2_top, ENNReal.div_le_iff_le_mul (.inl hc2_pos.ne')
          (.inl hc2_top), mul_comm]
      · refine (tendstoInMeasure_const_mul hM c).congr_left fun n ↦ Eventually.of_forall fun ω ↦ ?_
        exact ((K n).integral_smul c W t ω).symm

/-- Linearity of the Itô integral specification: negation. -/
theorem IsItoIntegral.neg (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ -H t ω) (fun t ω ↦ -I t ω) := by
  simpa only [neg_one_mul] using hI.const_mul (-1)

/-- Linearity of the Itô integral specification: subtraction. -/
theorem IsItoIntegral.sub (h₁ : IsItoIntegral ℱ P W H₁ I₁)
    (h₂ : IsItoIntegral ℱ P W H₂ I₂) :
    IsItoIntegral ℱ P W (fun t ω ↦ H₁ t ω - H₂ t ω) (fun t ω ↦ I₁ t ω - I₂ t ω) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-! ### Uniqueness and integrand congruence -/

/-- If a sequence of elementary integrands approximates `H` in pathwise square energy in
probability on `(0, t]` while their elementary integrals at `t` converge in probability to `X`,
then any Itô integral `I` of `H` against a filtered pre-Brownian motion `W` agrees almost surely
with `X` at time `t`. -/
theorem IsItoIntegral.ae_eq_of_approx (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0} {L : ℕ → ElementaryIntegrand ℱ} {X : Ω → ℝ}
    (hEL : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n ↦ P {ω | ε ≤
      ∫⁻ s, ‖(L n).toProcess s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0))
    (hML : TendstoInMeasure P (fun n ↦ (L n).integral W t) atTop X) :
    I t =ᵐ[P] X := by
  obtain ⟨K, hEK, hMK⟩ := hI.approx t
  let D : ℕ → ElementaryIntegrand ℱ := fun n ↦ (K n).sub (L n)
  let C : ℕ → ElementaryIntegrand ℱ := fun n ↦ (D n).clip t
  have hED (ε : ℝ≥0∞) (hε : 0 < ε) :
      Tendsto (fun n ↦ P {ω | ε ≤ ∫⁻ s, ‖(D n).toProcess s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_measure_lintegral_two_mul_add hEK hEL hε) (fun _ ↦ zero_le) fun n ↦
      measure_mono fun ω hω ↦ ?_
    simp only [mem_ofPred_eq] at hω ⊢
    refine hω.trans ?_
    have hmK : Measurable (fun s ↦ ‖(K n).toProcess s ω - H s ω‖ₑ ^ 2) :=
      ((((K n).isStronglyPredictable.sub hI.isStronglyPredictable).mono
        ℱ.predictable_le_prod).measurable.comp (measurable_id.prodMk measurable_const))
        |>.eNorm.pow_const 2
    calc
      ∫⁻ s, ‖(D n).toProcess s ω‖ₑ ^ 2 ∂Probability.timeMeasure t
        ≤ ∫⁻ s, (2 * ‖(K n).toProcess s ω - H s ω‖ₑ ^ 2 +
            2 * ‖(L n).toProcess s ω - H s ω‖ₑ ^ 2) ∂Probability.timeMeasure t := by
          refine lintegral_mono fun s ↦ ?_
          have hdecomp : (D n).toProcess s ω =
              ((K n).toProcess s ω - H s ω) + -((L n).toProcess s ω - H s ω) := by
            simp [D]
          rw [hdecomp]
          simpa only [eNorm_neg] using enorm_add_sq_le_two_mul
            ((K n).toProcess s ω - H s ω) (-((L n).toProcess s ω - H s ω))
      _ = 2 * ∫⁻ s, ‖(K n).toProcess s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t +
          2 * ∫⁻ s, ‖(L n).toProcess s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t := by
          rw [lintegral_add_left (hmK.const_mul 2),
            lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
  have henergy : TendstoInMeasure P
      (fun n ↦ Probability.elementaryEnergy (C n).grid (C n).height (C n).n) atTop (fun _ ↦ 0) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    refine (hED (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)).congr fun n ↦ ?_
    congr 1
    ext ω
    have hnn : 0 ≤ Probability.elementaryEnergy (C n).grid (C n).height (C n).n ω :=
      Probability.elementaryEnergy_nonneg (C n).mono ω
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn,
      (D n).lintegral_enorm_sq_toProcess_clip t ω, ENNReal.ofReal_le_ofReal_iff hnn, C]
  have hdiff_zero : TendstoInMeasure P
      (fun n ω ↦ (K n).integral W t ω - (L n).integral W t ω) atTop (fun _ ↦ 0) := by
    have hsum := hW.tendstoInMeasure_sum_mul_sub_of_energy (fun n ↦ (C n).mono)
      (fun n i hi ↦ (C n).stronglyMeasurable i hi) henergy
    refine hsum.congr_left fun n ↦ Eventually.of_forall fun ω ↦ ?_
    rw [← (D n).integral_clip_eq_sum W t ω, ElementaryIntegrand.integral_sub]
  have hdiff_IX : TendstoInMeasure P
      (fun n ω ↦ (K n).integral W t ω - (L n).integral W t ω) atTop (fun ω ↦ I t ω - X ω) :=
    tendstoInMeasure_sub hMK hML
  filter_upwards [tendstoInMeasure_ae_unique hdiff_IX hdiff_zero] with ω hω
  exact sub_eq_zero.mp hω

/-- **Uniqueness of the Brownian Itô integral.** Against a filtered pre-Brownian motion, any two
processes satisfying `IsItoIntegral` for the same integrand are indistinguishable. Neither path
continuity of `W` nor usual conditions on `ℱ` are required. -/
theorem IsItoIntegral.indist (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) :
    I ≡ᵐ[P] J := by
  refine indist_of_ae_eq_of_ae_continuous hI.ae_continuous hJ.ae_continuous fun t ↦ ?_
  obtain ⟨L, hEL, hML⟩ := hJ.approx t
  exact hI.ae_eq_of_approx hW hEL hML

/-- **Integrand congruence for the Brownian Itô integral.** If two strongly predictable integrands
agree `dt × P`-almost everywhere on every finite horizon, then their Itô integrals against a
filtered pre-Brownian motion are indistinguishable. -/
theorem IsItoIntegral.indist_of_ae_eq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H₁ I) (hJ : IsItoIntegral ℱ P W H₂ J)
    (hH : ∀ T : ℝ≥0, Function.uncurry H₁ =ᵐ[(Probability.timeMeasure T).prod P]
      Function.uncurry H₂) :
    I ≡ᵐ[P] J := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (hI.congr_integrand hJ.isStronglyPredictable hH).indist hW hJ

end TauCeti
