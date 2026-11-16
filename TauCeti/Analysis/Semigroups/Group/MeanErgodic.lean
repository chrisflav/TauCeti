/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import TauCeti.Analysis.Semigroups.Group.PhaseShift
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Bochner.CharFun.Bochner

/-!
# Continuous-time mean ergodic projection and spectral atomic mass

For a strongly continuous unitary group `U : ℝ → H →L[ℝ] H` on a complex Hilbert space `H` and an
angular frequency `ω : ℝ`, the **common eigenspace** at frequency `ω` is the closed complex
subspace

`{x : H | ∀ t : ℝ, U t x = Complex.exp (ω * t * Complex.I) • x}`.

The continuous-time **von Neumann mean ergodic theorem** (`tendsto_timeAverage`) states that for
every `v : H`, the Cesàro time averages `T⁻¹ • ∫ t in (0 : ℝ)..T, U t v` converge in norm as
`T → ∞` to the orthogonal projection of `v` onto the fixed-point subspace. Applying this to the
phase-shifted group `U.phaseShift hU.isComplexLinear ω` yields convergence of the twisted averages
`(T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-i ω t) • U t v` to the orthogonal projection onto the
`ω`-eigenspace (`tendsto_twistedAverage`).

For any `v : H`, the correlation function `t ↦ ⟪v, U t v⟫_ℂ` is continuous and positive definite,
so Bochner's theorem supplies a unique finite Borel measure `U.spectralMeasure hU v` on `ℝ` whose
characteristic function is `t ↦ ⟪v, U t v⟫_ℂ`. Fubini's theorem expresses the squared norm of a
time average as the integral of a Fejér-type kernel against this spectral measure, and dominated
convergence shows that its limit `‖P_ω v‖²` equals the atomic mass
`(U.spectralMeasure hU v).real {ω}` (`norm_starProjection_eigenspace_sq_eq_measureReal_singleton`).

## Main definitions

* `TauCeti.Semigroups.StronglyContinuousGroup.eigenspace`: the closed complex subspace of vectors
  transforming as `U t x = exp (i ω t) • x` for all `t : ℝ`.
* `TauCeti.Semigroups.StronglyContinuousGroup.timeAverage`: the continuous-time Cesàro average
  `T⁻¹ • ∫ t in (0 : ℝ)..T, U t v`.
* `TauCeti.Semigroups.StronglyContinuousGroup.spectralMeasure`: the unique finite Borel measure
  on `ℝ` whose characteristic function is `t ↦ ⟪v, U t v⟫_ℂ`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousGroup.eigenspace_zero_eq_orthogonal_coboundaries` and
  `orthogonal_eigenspace_zero`: the fixed-point subspace and the closed span of coboundaries
  `U s w - w` are orthogonal complements.
* `TauCeti.Semigroups.StronglyContinuousGroup.tendsto_timeAverage`: continuous-time von Neumann
  mean ergodic theorem for a unitary C₀-group.
* `TauCeti.Semigroups.StronglyContinuousGroup.tendsto_twistedAverage`: convergence of twisted
  time averages to the orthogonal projection onto the `ω`-eigenspace.
* `TauCeti.Semigroups.StronglyContinuousGroup.isPositiveDefiniteSub_inner_orbit` and
  `existsUnique_spectralMeasure`: positive definiteness of unitary orbit correlations and
  existence and uniqueness of the Bochner spectral measure.
* `norm_starProjection_eigenspace_sq_eq_measureReal_singleton` and
  `spectralMeasure_real_singleton`: the squared norm of the eigenspace projection equals the atomic
  mass of the spectral measure.
* `TauCeti.Semigroups.StronglyContinuousGroup.exists_tendsto_twistedAverage`: bundled projection,
  convergence, and spectral-mass statement at frequency `2πa`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section V.4 (mean ergodic semigroups).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Theorem II.11 (von Neumann ergodic theorem) and Section VII.4.
* M. Hochman, *Lectures on Dynamics* (2012), Lemma 6.6.2 and Proposition 6.6.3 (discrete-time
  analogues).
-/

public section

noncomputable section

open ComplexConjugate Filter MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

/-! ## Common eigenspaces -/

section Eigenspace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The common eigenspace of a complex-linear C₀-group at angular frequency `ω : ℝ`: the complex
submodule of vectors `x` satisfying `U t x = exp (i ω t) • x` for all `t : ℝ`. -/
def eigenspace (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    Submodule ℂ X where
  carrier := {x : X | ∀ t : ℝ, U t x = Complex.exp (ω * t * Complex.I) • x}
  zero_mem' t := by simp
  add_mem' hx hy t := by simp [hx t, hy t, smul_add]
  smul_mem' c x hx t := by
    rw [U.map_smul_of_isComplexLinear hU t c x, hx t, smul_comm]

/-- Membership in `U.eigenspace hU ω` means transforming by `exp (i ω t)` at every time `t`. -/
@[simp]
theorem mem_eigenspace_iff (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω : ℝ) (x : X) :
    x ∈ U.eigenspace hU ω ↔ ∀ t : ℝ, U t x = Complex.exp (ω * t * Complex.I) • x :=
  Iff.rfl

/-- The eigenspace at frequency `0` consists of the vectors fixed by every group operator. -/
theorem mem_eigenspace_zero_iff (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (x : X) :
    x ∈ U.eigenspace hU 0 ↔ ∀ t : ℝ, U t x = x := by
  simp [mem_eigenspace_iff]

/-- Every common eigenspace of a complex-linear C₀-group is closed. -/
theorem isClosed_eigenspace (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω : ℝ) :
    IsClosed (U.eigenspace hU ω : Set X) := by
  have hset : (U.eigenspace hU ω : Set X) =
      ⋂ t : ℝ, {x : X | U t x = Complex.exp (ω * t * Complex.I) • x} := by
    ext x
    simp
  rw [hset]
  exact isClosed_iInter fun t => isClosed_eq (U t).continuous (continuous_const_smul _)

/-- On a complete space, every common eigenspace of a complex-linear C₀-group is complete. -/
instance completeSpace_eigenspace [CompleteSpace X] (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    CompleteSpace (U.eigenspace hU ω) :=
  (U.isClosed_eigenspace hU ω).completeSpace_coe

/-- Phase shifting by `ω₁` shifts the `ω₂`-eigenspace to the `(ω₁ + ω₂)`-eigenspace. -/
@[simp]
theorem eigenspace_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω₁ ω₂ : ℝ) :
    (U.phaseShift hU ω₁).eigenspace (U.phaseShift_isComplexLinear hU ω₁) ω₂ =
      U.eigenspace hU (ω₁ + ω₂) := by
  ext x
  simp only [mem_eigenspace_iff, phaseShift_apply_apply]
  refine forall_congr' fun t => ?_
  have hcancel :
      Complex.exp (ω₁ * t * Complex.I) * Complex.exp (-(ω₁ * t) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have hzero : (ω₁ : ℂ) * t * Complex.I + -((ω₁ : ℂ) * t) * Complex.I = 0 := by ring
    rw [hzero, Complex.exp_zero]
  have hadd :
      Complex.exp (ω₁ * t * Complex.I) * Complex.exp (ω₂ * t * Complex.I) =
        Complex.exp (((ω₁ + ω₂ : ℝ) : ℂ) * t * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  constructor
  · intro h
    have h' := congrArg (fun y => Complex.exp (ω₁ * t * Complex.I) • y) h
    rw [smul_smul, hcancel, one_smul, smul_smul, hadd] at h'
    exact h'
  · intro h
    rw [h, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- Time reversal negates the frequency of every common eigenspace. -/
@[simp]
theorem eigenspace_reflect (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω : ℝ) :
    U.reflect.eigenspace (U.reflect_isComplexLinear hU) ω = U.eigenspace hU (-ω) := by
  ext x
  simp only [mem_eigenspace_iff, reflect_apply]
  constructor
  · intro h t
    simpa [mul_neg, neg_mul] using h (-t)
  · intro h t
    simpa [mul_neg, neg_mul] using h (-t)

end Eigenspace

section EigenspaceUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Common eigenspaces of a unitary C₀-group at distinct angular frequencies are orthogonal. -/
theorem isOrtho_eigenspace_of_ne (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    {ω₁ ω₂ : ℝ} (hω : ω₁ ≠ ω₂) :
    U.eigenspace hU.isComplexLinear ω₁ ⟂ U.eigenspace hU.isComplexLinear ω₂ := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  let t : ℝ := Real.pi / (ω₂ - ω₁)
  have hdiff : ω₂ - ω₁ ≠ 0 := sub_ne_zero.mpr hω.symm
  have hphase :
      conj (Complex.exp (ω₁ * t * Complex.I)) * Complex.exp (ω₂ * t * Complex.I) = -1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    have hexp :
        conj ((ω₁ : ℂ) * (t : ℂ) * Complex.I) + (ω₂ : ℂ) * (t : ℂ) * Complex.I =
          Real.pi * Complex.I := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      have ht : (ω₂ - ω₁) * t = Real.pi := mul_div_cancel₀ Real.pi hdiff
      have hcast : ((ω₂ : ℂ) - (ω₁ : ℂ)) * (t : ℂ) = Real.pi := by exact_mod_cast ht
      linear_combination hcast * Complex.I
    rw [hexp, Complex.exp_pi_mul_I]
  have hinner : ⟪u, v⟫_ℂ = -⟪u, v⟫_ℂ := by
    calc ⟪u, v⟫_ℂ = ⟪U t u, U t v⟫_ℂ := (hU.inner_map_map t u v).symm
      _ = ⟪Complex.exp (ω₁ * t * Complex.I) • u, Complex.exp (ω₂ * t * Complex.I) • v⟫_ℂ := by
            rw [hu t, hv t]
      _ = (conj (Complex.exp (ω₁ * t * Complex.I)) * Complex.exp (ω₂ * t * Complex.I)) *
            ⟪u, v⟫_ℂ := by
            rw [inner_smul_left, inner_smul_right]
            ring
      _ = -⟪u, v⟫_ℂ := by rw [hphase, neg_one_mul]
  exact CharZero.eq_neg_self_iff.mp hinner

/-- The fixed-point subspace of a unitary C₀-group is the orthogonal complement of the span of
all coboundaries `U s w - w`. -/
theorem eigenspace_zero_eq_orthogonal_coboundaries (U : StronglyContinuousGroup H)
    (hU : U.IsUnitary) :
    U.eigenspace hU.isComplexLinear 0 =
      (Submodule.span ℂ {y : H | ∃ (s : ℝ) (w : H), y = U s w - w})ᗮ := by
  ext u
  rw [U.mem_eigenspace_zero_iff hU.isComplexLinear, Submodule.mem_orthogonal]
  constructor
  · intro hu y hy
    refine Submodule.span_induction ?_ (inner_zero_left u)
      (fun a b _ _ ha hb => by rw [inner_add_left, ha, hb, add_zero])
      (fun c a _ ha => by rw [inner_smul_left, ha, mul_zero]) hy
    rintro _ ⟨s, w, rfl⟩
    rw [inner_sub_left, ← hu s, hU.inner_map_map, hu s, sub_self]
  · intro hu s
    have hmem : U s u - u ∈ Submodule.span ℂ {y : H | ∃ (t : ℝ) (w : H), y = U t w - w} :=
      Submodule.subset_span ⟨s, u, rfl⟩
    have horth : ⟪U s u - u, u⟫_ℂ = 0 := hu _ hmem
    have heq : ⟪U s u, u⟫_ℂ = ⟪u, u⟫_ℂ := sub_eq_zero.mp (by rwa [inner_sub_left] at horth)
    have heq' : ⟪u, U s u⟫_ℂ = ⟪u, u⟫_ℂ := by
      simpa [inner_conj_symm] using congrArg conj heq
    have hself : ⟪U s u - u, U s u - u⟫_ℂ = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, hU.inner_map_map, heq, heq']
      ring
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)

/-- On a complete complex Hilbert space, the orthogonal complement of the fixed-point subspace of
a unitary C₀-group is the closed complex linear span of the coboundaries `U s w - w`. -/
theorem orthogonal_eigenspace_zero [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.IsUnitary) :
    (U.eigenspace hU.isComplexLinear 0)ᗮ =
      (Submodule.span ℂ {y : H | ∃ (s : ℝ) (w : H), y = U s w - w}).topologicalClosure := by
  rw [U.eigenspace_zero_eq_orthogonal_coboundaries hU, Submodule.orthogonal_orthogonal_eq_closure]

end EigenspaceUnitary

/-! ## Continuous-time averages and the mean ergodic theorem -/

section TimeAverage

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The continuous-time Cesàro average of a C₀-group orbit over `[0, T]`:
`T⁻¹ • ∫ t in (0 : ℝ)..T, U t v`. -/
def timeAverage (U : StronglyContinuousGroup X) (T : ℝ) (v : X) : X :=
  T⁻¹ • ∫ t in (0 : ℝ)..T, U t v

/-- Unfolding lemma for `StronglyContinuousGroup.timeAverage`. -/
theorem timeAverage_def (U : StronglyContinuousGroup X) (T : ℝ) (v : X) :
    U.timeAverage T v = T⁻¹ • ∫ t in (0 : ℝ)..T, U t v :=
  (rfl)

/-- The time average over the degenerate interval `[0, 0]` is `0`. -/
@[simp]
theorem timeAverage_zero (U : StronglyContinuousGroup X) (v : X) : U.timeAverage 0 v = 0 := by
  simp [timeAverage_def]

/-- The time average of the zero vector is `0`. -/
@[simp]
theorem timeAverage_apply_zero (U : StronglyContinuousGroup X) (T : ℝ) :
    U.timeAverage T 0 = 0 := by
  simp [timeAverage_def]

/-- Time averaging is additive in the vector argument. -/
theorem timeAverage_add (U : StronglyContinuousGroup X) (T : ℝ) (u v : X) :
    U.timeAverage T (u + v) = U.timeAverage T u + U.timeAverage T v := by
  rw [timeAverage_def, timeAverage_def, timeAverage_def]
  simp_rw [_root_.map_add]
  rw [intervalIntegral.integral_add ((U.continuous_orbit u).intervalIntegrable 0 T)
    ((U.continuous_orbit v).intervalIntegrable 0 T), smul_add]

/-- Time averaging commutes with subtraction in the vector argument. -/
theorem timeAverage_sub (U : StronglyContinuousGroup X) (T : ℝ) (u v : X) :
    U.timeAverage T (u - v) = U.timeAverage T u - U.timeAverage T v := by
  rw [timeAverage_def, timeAverage_def, timeAverage_def]
  simp_rw [map_sub]
  rw [intervalIntegral.integral_sub ((U.continuous_orbit u).intervalIntegrable 0 T)
    ((U.continuous_orbit v).intervalIntegrable 0 T), smul_sub]

/-- Time averaging commutes with real scalar multiplication. -/
theorem timeAverage_smul (U : StronglyContinuousGroup X) (T : ℝ) (c : ℝ) (v : X) :
    U.timeAverage T (c • v) = c • U.timeAverage T v := by
  rw [timeAverage_def, timeAverage_def]
  simp_rw [map_smul]
  rw [intervalIntegral.integral_smul, smul_comm]

/-- The time average of a fixed vector over any nonzero interval `[0, T]` is the vector itself. -/
theorem timeAverage_eq_self_of_forall_eq [CompleteSpace X] (U : StronglyContinuousGroup X)
    {T : ℝ} (hT : T ≠ 0) {v : X} (hv : ∀ t : ℝ, U t v = v) :
    U.timeAverage T v = v := by
  simp only [timeAverage_def, hv, intervalIntegral.integral_const, sub_zero, smul_smul,
    inv_mul_cancel₀ hT, one_smul]

/-- Uniform norm estimate for time averages of a C₀-group uniformly bounded on `[0, ∞)`. -/
theorem norm_timeAverage_le (U : StronglyContinuousGroup X) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, 0 ≤ t → ‖U t‖ ≤ C) {T : ℝ} (hT : 0 ≤ T) (v : X) :
    ‖U.timeAverage T v‖ ≤ C * ‖v‖ := by
  rcases hT.eq_or_lt with rfl | hTpos
  · rw [timeAverage_zero, norm_zero]
    exact mul_nonneg hC (norm_nonneg v)
  · rw [timeAverage_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hTpos.le)]
    have hint : ‖∫ t in (0 : ℝ)..T, U t v‖ ≤ C * ‖v‖ * |T - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [Set.uIoc_of_le hTpos.le] at ht
      exact ((U t).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hb t ht.1.le) (norm_nonneg v))
    calc T⁻¹ * ‖∫ t in (0 : ℝ)..T, U t v‖
        ≤ T⁻¹ * (C * ‖v‖ * |T - 0|) := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hTpos.le)
      _ = C * ‖v‖ := by
            rw [sub_zero, abs_of_pos hTpos]
            field_simp [hTpos.ne']

/-- Uniform Lipschitz bound for time averages of a C₀-group uniformly bounded on `[0, ∞)`. -/
theorem norm_timeAverage_sub_le (U : StronglyContinuousGroup X) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, 0 ≤ t → ‖U t‖ ≤ C) {T : ℝ} (hT : 0 ≤ T) (u v : X) :
    ‖U.timeAverage T u - U.timeAverage T v‖ ≤ C * ‖u - v‖ := by
  rw [← U.timeAverage_sub]
  exact U.norm_timeAverage_le hC hb hT (u - v)

/-- For a C₀-group uniformly bounded on `[0, ∞)`, the set of vectors whose time averages vanish
at infinity is closed. -/
theorem isClosed_setOf_tendsto_timeAverage_zero (U : StronglyContinuousGroup X) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ t : ℝ, 0 ≤ t → ‖U t‖ ≤ C) :
    IsClosed {v : X | Tendsto (fun T : ℝ => U.timeAverage T v) atTop (𝓝 0)} := by
  rw [← isSeqClosed_iff_isClosed]
  intro x v hx hv
  rw [Set.mem_ofPred_eq, Metric.tendsto_atTop]
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.mp hv) (ε / (2 * (C + 1))) (by positivity)
  have hdist : ‖x n - v‖ < ε / (2 * (C + 1)) := by
    simpa [dist_eq_norm] using hn n le_rfl
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp (hx n)) (ε / 2) (half_pos hε)
  refine ⟨max T₀ 0, fun T hT => ?_⟩
  have h1 : ‖U.timeAverage T (x n)‖ < ε / 2 := by
    simpa [dist_eq_norm] using hT₀ T (le_of_max_le_left hT)
  have h2 : ‖U.timeAverage T v - U.timeAverage T (x n)‖ ≤ C * ‖v - x n‖ :=
    U.norm_timeAverage_sub_le hC hb (le_of_max_le_right hT) v (x n)
  have h3 : C * ‖v - x n‖ < ε / 2 := by
    rw [norm_sub_rev]
    calc C * ‖x n - v‖ ≤ (C + 1) * ‖x n - v‖ := by nlinarith [norm_nonneg (x n - v)]
      _ < (C + 1) * (ε / (2 * (C + 1))) := mul_lt_mul_of_pos_left hdist hC1
      _ = ε / 2 := by field_simp [hC1.ne']
  rw [dist_zero_right]
  calc ‖U.timeAverage T v‖
      = ‖(U.timeAverage T v - U.timeAverage T (x n)) + U.timeAverage T (x n)‖ := by abel_nf
    _ ≤ ‖U.timeAverage T v - U.timeAverage T (x n)‖ + ‖U.timeAverage T (x n)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (h2.trans_lt h3) h1
    _ = ε := add_halves ε

/-- For a uniformly bounded C₀-group, the time average of any coboundary `U s v - v` tends to `0`
as `T → ∞`. -/
theorem tendsto_timeAverage_coboundary (U : StronglyContinuousGroup X) {C : ℝ}
    (hb : ∀ t : ℝ, ‖U t‖ ≤ C) (s : ℝ) (v : X) :
    Tendsto (fun T : ℝ => U.timeAverage T (U s v - v)) atTop (𝓝 0) := by
  have hbound : ∀ T : ℝ, 0 < T →
      ‖U.timeAverage T (U s v - v)‖ ≤ T⁻¹ * (2 * (C * ‖v‖ * |s|)) := by
    intro T hT
    have horb := U.continuous_orbit v
    have hshift : ∫ t in (0 : ℝ)..T, U t (U s v) = ∫ t in s..(T + s), U t v := by
      have hfun : (fun t : ℝ => U t (U s v)) = fun t : ℝ => U (t + s) v :=
        funext fun t => (U.map_add_apply t s v).symm
      rw [hfun, intervalIntegral.integral_comp_add_right (f := fun t : ℝ => U t v) s, zero_add]
    have hsplit1 : (∫ t in (0 : ℝ)..s, U t v) + ∫ t in s..(T + s), U t v =
        ∫ t in (0 : ℝ)..(T + s), U t v :=
      intervalIntegral.integral_add_adjacent_intervals
        (horb.intervalIntegrable 0 s) (horb.intervalIntegrable s (T + s))
    have hsplit2 : (∫ t in (0 : ℝ)..T, U t v) + ∫ t in T..(T + s), U t v =
        ∫ t in (0 : ℝ)..(T + s), U t v :=
      intervalIntegral.integral_add_adjacent_intervals
        (horb.intervalIntegrable 0 T) (horb.intervalIntegrable T (T + s))
    have hdiff : (∫ t in (0 : ℝ)..T, U t (U s v - v)) =
        (∫ t in T..(T + s), U t v) - ∫ t in (0 : ℝ)..s, U t v := by
      simp_rw [map_sub]
      rw [intervalIntegral.integral_sub ((U.continuous_orbit (U s v)).intervalIntegrable 0 T)
        (horb.intervalIntegrable 0 T), hshift]
      exact sub_eq_sub_iff_add_eq_add.mpr (by rw [add_comm, hsplit1, ← hsplit2, add_comm])
    have hest : ∀ a b : ℝ, ‖∫ t in a..b, U t v‖ ≤ C * ‖v‖ * |b - a| := fun a b =>
      intervalIntegral.norm_integral_le_of_norm_le_const fun t _ =>
        ((U t).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hb t) (norm_nonneg v))
    rw [timeAverage_def, hdiff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hT.le)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hT.le)
    calc ‖(∫ t in T..(T + s), U t v) - ∫ t in (0 : ℝ)..s, U t v‖
        ≤ ‖∫ t in T..(T + s), U t v‖ + ‖∫ t in (0 : ℝ)..s, U t v‖ := norm_sub_le _ _
      _ ≤ C * ‖v‖ * |(T + s) - T| + C * ‖v‖ * |s - 0| := add_le_add (hest T (T + s)) (hest 0 s)
      _ = 2 * (C * ‖v‖ * |s|) := by rw [add_sub_cancel_left, sub_zero]; ring
  have hlim : Tendsto (fun T : ℝ => T⁻¹ * (2 * (C * ‖v‖ * |s|))) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const (2 * (C * ‖v‖ * |s|))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact hbound T hT

end TimeAverage

section TimeAverageComplex

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Time averaging commutes with complex scalar multiplication for a complex-linear C₀-group. -/
theorem timeAverage_smul_complex (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (T : ℝ) (c : ℂ) (v : X) :
    U.timeAverage T (c • v) = c • U.timeAverage T v := by
  rw [timeAverage_def, timeAverage_def]
  simp_rw [U.map_smul_of_isComplexLinear hU]
  rw [intervalIntegral.integral_smul, smul_comm]

/-- The time average of a phase-shifted C₀-group is the twisted integral average
`(T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-i ω t) • U t v`. -/
theorem timeAverage_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω T : ℝ) (v : X) :
    (U.phaseShift hU ω).timeAverage T v =
      (T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v := by
  rw [timeAverage_def, ← algebraMap_smul ℂ T⁻¹, Complex.coe_algebraMap, Complex.ofReal_inv]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [phaseShift_apply_apply]
  congr 2
  ring

end TimeAverageComplex

section MeanErgodic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Continuous-time von Neumann mean ergodic theorem.** For a strongly continuous unitary group
`U` on a complex Hilbert space and any vector `v`, the Cesàro time averages
`T⁻¹ • ∫ t in (0 : ℝ)..T, U t v` converge in norm as `T → ∞` to the orthogonal projection of `v`
onto the fixed-point subspace `U.eigenspace hU.isComplexLinear 0`. -/
theorem tendsto_timeAverage (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (v : H) :
    Tendsto (fun T : ℝ => U.timeAverage T v) atTop
      (𝓝 ((U.eigenspace hU.isComplexLinear 0).starProjection v)) := by
  set K := U.eigenspace hU.isComplexLinear 0
  set w := K.starProjection v
  have hw_fixed : ∀ t : ℝ, U t w = w :=
    (U.mem_eigenspace_zero_iff hU.isComplexLinear w).mp (K.starProjection_apply_mem v)
  have hsub_orth : v - w ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  let Z : Submodule ℂ H :=
    { carrier := {z : H | Tendsto (fun T : ℝ => U.timeAverage T z) atTop (𝓝 0)}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simpa only [Set.mem_ofPred_eq, U.timeAverage_add, add_zero] using ha.add hb
      smul_mem' := fun c a ha => by
        simpa only [Set.mem_ofPred_eq, U.timeAverage_smul_complex hU.isComplexLinear, smul_zero]
          using ha.const_smul c }
  have hZ_closed : IsClosed (Z : Set H) :=
    U.isClosed_setOf_tendsto_timeAverage_zero zero_le_one fun t _ => hU.opNorm_le_one t
  have hspan_le : Submodule.span ℂ {y : H | ∃ (s : ℝ) (x : H), y = U s x - x} ≤ Z := by
    rw [Submodule.span_le]
    rintro _ ⟨s, x, rfl⟩
    exact U.tendsto_timeAverage_coboundary hU.opNorm_le_one s x
  have hKorth_le : Kᗮ ≤ Z := by
    rw [U.orthogonal_eigenspace_zero hU]
    exact Submodule.topologicalClosure_minimal _ hspan_le hZ_closed
  have hrem : Tendsto (fun T : ℝ => U.timeAverage T (v - w)) atTop (𝓝 0) := hKorth_le hsub_orth
  have hsum : Tendsto (fun T : ℝ => w + U.timeAverage T (v - w)) atTop (𝓝 w) := by
    simpa only [add_zero] using tendsto_const_nhds.add hrem
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hsplit : v = w + (v - w) := by abel
  conv_rhs => rw [hsplit, U.timeAverage_add, U.timeAverage_eq_self_of_forall_eq hT.ne' hw_fixed]

/-- **Continuous-time mean ergodic projection at frequency `ω`.** For a strongly continuous unitary
group `U` on a complex Hilbert space, an angular frequency `ω : ℝ`, and any vector `v`, the
twisted time averages `(T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-i ω t) • U t v` converge in norm as
`T → ∞` to the orthogonal projection of `v` onto `U.eigenspace hU.isComplexLinear ω`. -/
theorem tendsto_twistedAverage (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (ω : ℝ) (v : H) :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) •
        ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v)
      atTop (𝓝 ((U.eigenspace hU.isComplexLinear ω).starProjection v)) := by
  have h := (U.phaseShift hU.isComplexLinear ω).tendsto_timeAverage (hU.phaseShift ω) v
  simp_rw [U.timeAverage_phaseShift hU.isComplexLinear ω] at h
  simpa only [eigenspace_phaseShift, add_zero] using h

end MeanErgodic

/-! ## Spectral measure and spectral atomic mass -/

section SpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Every matrix coefficient `t ↦ ⟪u, U t v⟫_ℂ` of a C₀-group on a complex inner-product space is
continuous on `ℝ`. -/
theorem continuous_inner_orbit (U : StronglyContinuousGroup H) (u v : H) :
    Continuous fun t : ℝ => ⟪u, U t v⟫_ℂ :=
  continuous_const.inner (U.continuous_orbit v)

/-- The orbit correlation function `t ↦ ⟪v, U t v⟫_ℂ` of a unitary C₀-group is positive definite
in subtraction form. -/
theorem isPositiveDefiniteSub_inner_orbit (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    (v : H) :
    IsPositiveDefiniteSub fun t : ℝ => ⟪v, U t v⟫_ℂ := by
  rw [isPositiveDefiniteSub_iff_forall_sum_nonneg]
  intro n c t
  have hterm : ∀ i j : Fin n,
      c i * conj (c j) * ⟪v, U (t i - t j) v⟫_ℂ = ⟪c j • U (t j) v, c i • U (t i) v⟫_ℂ := by
    intro i j
    have hgroup : ⟪v, U (t i - t j) v⟫_ℂ = ⟪U (t j) v, U (t i) v⟫_ℂ := by
      calc ⟪v, U (t i - t j) v⟫_ℂ
          = ⟪U (t j) v, U (t j) (U (t i - t j) v)⟫_ℂ := (hU.inner_map_map (t j) _ _).symm
        _ = ⟪U (t j) v, U (t i) v⟫_ℂ := by rw [← U.map_add_apply, add_sub_cancel]
    rw [hgroup, inner_smul_left, inner_smul_right]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hsum :
      ∑ j : Fin n, ∑ i : Fin n, ⟪c j • U (t j) v, c i • U (t i) v⟫_ℂ =
        ⟪∑ j : Fin n, c j • U (t j) v, ∑ i : Fin n, c i • U (t i) v⟫_ℂ := by
    rw [sum_inner]
    simp_rw [inner_sum]
  rw [hsum, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow]
  exact Complex.nonneg_iff.mpr ⟨sq_nonneg _, rfl⟩

/-- **Bochner spectral measure of a unitary C₀-group.** For every vector `v`, there is a unique
finite Borel measure `σ` on `ℝ` whose characteristic function is the orbit correlation
`t ↦ ⟪v, U t v⟫_ℂ`. -/
theorem existsUnique_spectralMeasure (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (v : H) :
    ∃! σ : Measure ℝ, IsFiniteMeasure σ ∧ ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t := by
  have hboch := (bochner_charFun (fun t : ℝ => ⟪v, U t v⟫_ℂ)).mp
    ⟨U.continuous_inner_orbit v v, U.isPositiveDefiniteSub_inner_orbit hU v⟩
  obtain ⟨σ, ⟨hσfin, hσeq⟩, hσuniq⟩ := hboch
  refine ⟨σ, ⟨hσfin, fun t => (congrFun hσeq t).symm⟩, ?_⟩
  rintro τ ⟨hτfin, hτeq⟩
  exact hσuniq τ ⟨hτfin, funext fun t => (hτeq t).symm⟩

/-- The spectral measure of a unitary C₀-group `U` at a vector `v`: the unique finite Borel
measure on `ℝ` whose characteristic function is `t ↦ ⟪v, U t v⟫_ℂ`. -/
def spectralMeasure (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (v : H) : Measure ℝ :=
  (U.existsUnique_spectralMeasure hU v).choose

/-- The spectral measure of a unitary C₀-group at any vector is a finite Borel measure. -/
instance isFiniteMeasure_spectralMeasure (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    (v : H) :
    IsFiniteMeasure (U.spectralMeasure hU v) :=
  (U.existsUnique_spectralMeasure hU v).choose_spec.1.1

/-- The characteristic function of `U.spectralMeasure hU v` is the orbit correlation
`t ↦ ⟪v, U t v⟫_ℂ`. -/
@[simp]
theorem charFun_spectralMeasure (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (v : H)
    (t : ℝ) :
    charFun (U.spectralMeasure hU v) t = ⟪v, U t v⟫_ℂ :=
  ((U.existsUnique_spectralMeasure hU v).choose_spec.1.2 t).symm

/-- Any finite Borel measure on `ℝ` whose characteristic function is `t ↦ ⟪v, U t v⟫_ℂ` equals
`U.spectralMeasure hU v`. -/
theorem spectralMeasure_eq_of_charFun (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (v : H)
    {σ : Measure ℝ} [IsFiniteMeasure σ] (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) :
    σ = U.spectralMeasure hU v :=
  (U.existsUnique_spectralMeasure hU v).choose_spec.2 σ ⟨inferInstance, hσ⟩

/-- The total mass of the spectral measure at `v` is `‖v‖²`. -/
@[simp]
theorem spectralMeasure_real_univ (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (v : H) :
    (U.spectralMeasure hU v).real Set.univ = ‖v‖ ^ 2 := by
  have h := U.charFun_spectralMeasure hU v 0
  rw [charFun_zero, U.map_zero_apply, inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by simpa [Complex.ofReal_pow] using h)

/-- The spectral measure at the zero vector is the zero measure. -/
@[simp]
theorem spectralMeasure_zero (U : StronglyContinuousGroup H) (hU : U.IsUnitary) :
    U.spectralMeasure hU 0 = 0 :=
  (U.spectralMeasure_eq_of_charFun hU 0 fun t => by simp).symm

/-- Scaling the vector by `c : ℂ` scales its spectral measure by `‖c‖²`. -/
theorem spectralMeasure_smul (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (c : ℂ) (v : H) :
    U.spectralMeasure hU (c • v) = ENNReal.ofReal (‖c‖ ^ 2) • U.spectralMeasure hU v := by
  have : IsFiniteMeasure (ENNReal.ofReal (‖c‖ ^ 2) • U.spectralMeasure hU v) :=
    ⟨by simp [ENNReal.mul_lt_top, measure_lt_top]⟩
  refine (U.spectralMeasure_eq_of_charFun hU (c • v) fun t => ?_).symm
  rw [charFun_apply_real, integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _),
    ← charFun_apply_real, U.charFun_spectralMeasure hU v t, hU.map_smul, inner_smul_left,
    inner_smul_right, ← mul_assoc, Complex.conj_mul', Complex.real_smul, Complex.ofReal_pow]

/-- Phase shifting a unitary C₀-group by `ω` translates its spectral measure by `-ω`. -/
theorem spectralMeasure_phaseShift (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    (ω : ℝ) (v : H) :
    (U.phaseShift hU.isComplexLinear ω).spectralMeasure (hU.phaseShift ω) v =
      (U.spectralMeasure hU v).map (fun ξ : ℝ => ξ - ω) := by
  have : IsFiniteMeasure ((U.spectralMeasure hU v).map (fun ξ : ℝ => ξ - ω)) :=
    Measure.isFiniteMeasure_map _ (fun ξ : ℝ => ξ - ω)
  refine ((U.phaseShift hU.isComplexLinear ω).spectralMeasure_eq_of_charFun
    (hU.phaseShift ω) v fun t => ?_).symm
  rw [charFun_apply_real, integral_map (measurable_sub_const ω).aemeasurable
    (by fun_prop : Continuous fun ξ : ℝ => Complex.exp (t * ξ * Complex.I)).aestronglyMeasurable]
  rw [phaseShift_apply_apply, inner_smul_right, ← U.charFun_spectralMeasure hU v t,
    charFun_apply_real, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  dsimp only
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Time reversal reflects the spectral measure through the origin. -/
theorem spectralMeasure_reflect (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (v : H) :
    U.reflect.spectralMeasure hU.reflect v = (U.spectralMeasure hU v).map Neg.neg := by
  have : IsFiniteMeasure ((U.spectralMeasure hU v).map Neg.neg) :=
    Measure.isFiniteMeasure_map _ Neg.neg
  refine (U.reflect.spectralMeasure_eq_of_charFun hU.reflect v fun t => ?_).symm
  rw [charFun_apply_real, integral_map measurable_neg.aemeasurable
    (by fun_prop : Continuous fun ξ : ℝ => Complex.exp (t * ξ * Complex.I)).aestronglyMeasurable]
  rw [reflect_apply, ← U.charFun_spectralMeasure hU v (-t), charFun_apply_real]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  dsimp only
  congr 1
  push_cast
  ring

end SpectralMeasure

section SpectralAtomicMass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Fubini exchange for the double correlation integral of a unitary orbit over `(0, T]`. -/
private theorem double_integral_inner_orbit (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    (v : H) {σ : Measure ℝ} [IsFiniteMeasure σ] (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t)
    {T : ℝ} (hT : 0 < T) :
    ∫ t, ∫ s, ⟪U s v, U t v⟫_ℂ ∂(volume.restrict (Set.Ioc (0 : ℝ) T))
        ∂(volume.restrict (Set.Ioc (0 : ℝ) T)) =
      ∫ ξ, (∫ t, Complex.exp (t * ξ * Complex.I) ∂(volume.restrict (Set.Ioc (0 : ℝ) T))) *
        conj (∫ s, Complex.exp (s * ξ * Complex.I) ∂(volume.restrict (Set.Ioc (0 : ℝ) T))) ∂σ := by
  set μT : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  have : IsFiniteMeasure μT := ⟨by simp [μT, Real.volume_Ioc]⟩
  have hnorm_exp : ∀ (r ξ : ℝ), ‖Complex.exp (r * ξ * Complex.I)‖ = 1 := fun r ξ => by
    rw [Complex.norm_exp]; simp
  have hinner_eq : ∀ s t : ℝ, ⟪U s v, U t v⟫_ℂ =
      ∫ ξ, Complex.exp (t * ξ * Complex.I) * conj (Complex.exp (s * ξ * Complex.I)) ∂σ := by
    intro s t
    have hgroup : ⟪U s v, U t v⟫_ℂ = ⟪v, U (t - s) v⟫_ℂ := by
      calc ⟪U s v, U t v⟫_ℂ
          = ⟪U s v, U s (U (t - s) v)⟫_ℂ := by rw [← U.map_add_apply, add_sub_cancel]
        _ = ⟪v, U (t - s) v⟫_ℂ := hU.inner_map_map s _ _
    rw [hgroup, hσ (t - s), charFun_apply_real]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    dsimp only
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  -- Swap the inner `s` and `ξ` integrals.
  have hswap1 : ∀ t : ℝ,
      ∫ s, (∫ ξ, Complex.exp (t * ξ * Complex.I) *
          conj (Complex.exp (s * ξ * Complex.I)) ∂σ) ∂μT =
        ∫ ξ, Complex.exp (t * ξ * Complex.I) *
          (∫ s, conj (Complex.exp (s * ξ * Complex.I)) ∂μT) ∂σ := by
    intro t
    have hint : Integrable (Function.uncurry fun s ξ : ℝ =>
        Complex.exp (t * ξ * Complex.I) * conj (Complex.exp (s * ξ * Complex.I))) (μT.prod σ) := by
      refine Integrable.of_bound
        (Continuous.aestronglyMeasurable (by fun_prop)) 1 (ae_of_all _ fun p => ?_)
      dsimp only [Function.uncurry]
      rw [norm_mul, RCLike.norm_conj, hnorm_exp, hnorm_exp, one_mul]
    rw [integral_integral_swap hint]
    refine integral_congr_ae (ae_of_all _ fun ξ => integral_const_mul _ _)
  -- Swap the outer `t` and `ξ` integrals.
  have hsm_inner :
      StronglyMeasurable fun ξ : ℝ => ∫ s, conj (Complex.exp (s * ξ * Complex.I)) ∂μT :=
    (Continuous.stronglyMeasurable (by fun_prop :
      Continuous fun p : ℝ × ℝ => conj (Complex.exp (p.1 * p.2 * Complex.I)))).integral_prod_left
  have hint2 : Integrable (Function.uncurry fun t ξ : ℝ =>
      Complex.exp (t * ξ * Complex.I) *
        (∫ s, conj (Complex.exp (s * ξ * Complex.I)) ∂μT)) (μT.prod σ) := by
    refine Integrable.of_bound ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (hsm_inner.comp_measurable measurable_snd).aestronglyMeasurable) T (ae_of_all _ fun p => ?_)
    dsimp only [Function.uncurry]
    rw [norm_mul, hnorm_exp, one_mul]
    have hle := norm_integral_le_of_norm_le_const (μ := μT) (C := 1)
      (f := fun s : ℝ => conj (Complex.exp (s * p.2 * Complex.I)))
      (ae_of_all _ fun s => by rw [RCLike.norm_conj, hnorm_exp])
    simpa [μT, Measure.real_def, Real.volume_Ioc, hT.le] using hle
  simp_rw [hinner_eq, hswap1]
  rw [integral_integral_swap hint2]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  dsimp only
  rw [integral_mul_const, integral_conj]

/-- Explicit evaluation of the oscillatory integral `∫ t in 0..T, exp (t * ξ * I)`. -/
private theorem integral_exp_mul_I (T ξ : ℝ) :
    ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I) =
      if ξ = 0 then (T : ℂ) else (Complex.exp (T * ξ * Complex.I) - 1) / (ξ * Complex.I) := by
  split_ifs with hξ
  · simp [hξ]
  · have hc : (ξ : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hξ) Complex.I_ne_zero
    have hmul : (fun t : ℝ => Complex.exp (t * ξ * Complex.I)) =
        fun t : ℝ => Complex.exp (((ξ : ℂ) * Complex.I) * t) :=
      funext fun t => by congr 1; ring
    rw [hmul, integral_exp_mul_complex hc]
    have harg : (ξ : ℂ) * Complex.I * T = T * ξ * Complex.I := by ring
    simp [harg]

/-- Pointwise convergence of the squared Dirichlet-type kernel to the indicator of `{0}`. -/
private theorem tendsto_norm_inv_mul_integral_exp_sq (ξ : ℝ) :
    Tendsto (fun T : ℝ => ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖ ^ 2)
      atTop (𝓝 (({0} : Set ℝ).indicator (1 : ℝ → ℝ) ξ)) := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [Set.indicator_of_mem (Set.mem_singleton (0 : ℝ)), Pi.one_apply]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [integral_exp_mul_I]
    simp only [↓reduceIte]
    rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hT.ne'), norm_one, one_pow]
  · simp only [Set.indicator_of_notMem (Set.notMem_singleton_iff.mpr hξ)]
    have h0 : Tendsto (fun T : ℝ => 2 * T⁻¹ / |ξ|) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.const_mul (2 : ℝ)).div_const |ξ|
    have h1 : Tendsto (fun T : ℝ => 2 / (T * |ξ|)) atTop (𝓝 0) := h0.congr fun T => by ring
    have hlim : Tendsto (fun T : ℝ => (2 / (T * |ξ|)) ^ 2) atTop (𝓝 0) := by
      simpa using h1.pow 2
    refine squeeze_zero' (Eventually.of_forall fun T => sq_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hnorm :
        ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖ ≤ 2 / (T * |ξ|) := by
      rw [integral_exp_mul_I, ite_eq_right_iff.mpr (fun h => (hξ h).elim), norm_mul, norm_div,
        norm_inv, Complex.norm_real, Real.norm_of_nonneg hT.le, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, mul_one]
      have hnum : ‖Complex.exp (T * ξ * Complex.I) - 1‖ ≤ 2 := by
        calc ‖Complex.exp (T * ξ * Complex.I) - 1‖
            ≤ ‖Complex.exp (T * ξ * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [Complex.norm_exp]; norm_num
      calc T⁻¹ * (‖Complex.exp (T * ξ * Complex.I) - 1‖ / |ξ|)
          ≤ T⁻¹ * (2 / |ξ|) := by gcongr
        _ = 2 / (T * |ξ|) := by ring
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

variable [CompleteSpace H]

/-- Expand `⟪∫ s, U s v, ∫ t, U t v⟫_ℂ` as a double integral over `(0, T]`. -/
private theorem inner_integral_orbit (U : StronglyContinuousGroup H) (v : H) (T : ℝ) :
    ⟪∫ s, U s v ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      ∫ t, U t v ∂(volume.restrict (Set.Ioc (0 : ℝ) T))⟫_ℂ =
      ∫ t, ∫ s, ⟪U s v, U t v⟫_ℂ ∂(volume.restrict (Set.Ioc (0 : ℝ) T))
        ∂(volume.restrict (Set.Ioc (0 : ℝ) T)) := by
  set μT : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  have horb_int : Integrable (fun t : ℝ => U t v) μT :=
    (U.continuous_orbit v).integrableOn_Ioc
  rw [← integral_inner horb_int]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  calc ⟪∫ s, U s v ∂μT, U t v⟫_ℂ
      = conj ⟪U t v, ∫ s, U s v ∂μT⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj (∫ s, ⟪U t v, U s v⟫_ℂ ∂μT) := by rw [← integral_inner horb_int]
    _ = ∫ s, conj ⟪U t v, U s v⟫_ℂ ∂μT := (integral_conj (f := fun s => ⟪U t v, U s v⟫_ℂ)).symm
    _ = ∫ s, ⟪U s v, U t v⟫_ℂ ∂μT := by simp_rw [inner_conj_symm]

/-- **Spectral representation of squared time-average norms.** For any unitary C₀-group `U`,
vector `v`, and finite measure `σ` with `charFun σ t = ⟪v, U t v⟫_ℂ`, the squared norm of the
time average over `[0, T]` (`T > 0`) equals the integral against `σ` of the squared modulus of the
Dirichlet-type kernel `ξ ↦ T⁻¹ ∫₀ᵀ exp (i t ξ) dt`. -/
theorem norm_timeAverage_sq_eq_integral (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (v : H)
    {σ : Measure ℝ} [IsFiniteMeasure σ] (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t)
    {T : ℝ} (hT : 0 < T) :
    ‖U.timeAverage T v‖ ^ 2 =
      ∫ ξ, ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖ ^ 2 ∂σ := by
  have hcomplex :
      ((‖U.timeAverage T v‖ ^ 2 : ℝ) : ℂ) =
        ∫ ξ, ((‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖ ^ 2 : ℝ) : ℂ)
          ∂σ := by
    have hself :
        ((‖U.timeAverage T v‖ ^ 2 : ℝ) : ℂ) = ⟪U.timeAverage T v, U.timeAverage T v⟫_ℂ := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [hself, timeAverage_def, ← algebraMap_smul ℂ T⁻¹, Complex.coe_algebraMap,
      Complex.ofReal_inv, intervalIntegral.integral_of_le hT.le, inner_smul_left,
      inner_smul_right, map_inv₀, Complex.conj_ofReal, U.inner_integral_orbit v T,
      U.double_integral_inner_orbit hU v hσ hT, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    dsimp only
    rw [intervalIntegral.integral_of_le hT.le, Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    ring
  rw [integral_complex_ofReal] at hcomplex
  exact Complex.ofReal_injective hcomplex

/-- For a unitary C₀-group `U`, vector `v`, and finite measure `σ` with
`charFun σ t = ⟪v, U t v⟫_ℂ`, the squared norm of the time average converges to the atomic mass
`σ.real {0}` as `T → ∞`. -/
theorem tendsto_norm_timeAverage_sq (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (v : H)
    {σ : Measure ℝ} [IsFiniteMeasure σ] (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) :
    Tendsto (fun T : ℝ => ‖U.timeAverage T v‖ ^ 2) atTop (𝓝 (σ.real {0})) := by
  let K : ℝ → ℝ → ℝ := fun T ξ =>
    ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖ ^ 2
  have hK_meas : ∀ᶠ T : ℝ in atTop, AEStronglyMeasurable (K T) σ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have heq : K T = fun ξ : ℝ =>
        if ξ = 0 then 1
        else ‖(T⁻¹ : ℂ) * ((Complex.exp (T * ξ * Complex.I) - 1) / ((ξ : ℂ) * Complex.I))‖ ^ 2 := by
      funext ξ
      simp only [K, integral_exp_mul_I]
      split_ifs with hξ
      · rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hT.ne'), norm_one, one_pow]
      · rfl
    rw [heq]
    exact (Measurable.ite (measurableSet_singleton 0) measurable_const
      (by fun_prop)).aestronglyMeasurable
  have hK_bound : ∀ᶠ T : ℝ in atTop, ∀ᵐ ξ ∂σ, ‖K T ξ‖ ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    refine ae_of_all _ fun ξ => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hint : ‖∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖ ≤ T := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)
        (C := 1) (f := fun t : ℝ => Complex.exp (t * ξ * Complex.I)) fun t _ => by
          rw [Complex.norm_exp]; simp
      simpa [abs_of_pos hT] using h
    have hle1 : ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖ ≤ 1 := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hT.le]
      calc T⁻¹ * ‖∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖
          ≤ T⁻¹ * T := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hT.le)
        _ = 1 := inv_mul_cancel₀ hT.ne'
    nlinarith [norm_nonneg ((T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I))]
  have hdct := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
    hK_meas hK_bound (integrable_const 1) (ae_of_all _ tendsto_norm_inv_mul_integral_exp_sq)
  rw [integral_indicator_one (measurableSet_singleton (0 : ℝ))] at hdct
  refine hdct.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact (U.norm_timeAverage_sq_eq_integral hU v hσ hT).symm

/-- **Spectral atomic-mass identity.** For a unitary C₀-group `U`, angular frequency `ω : ℝ`,
vector `v`, and any finite Borel measure `σ` with `charFun σ t = ⟪v, U t v⟫_ℂ`, the squared norm
of the orthogonal projection of `v` onto `U.eigenspace hU.isComplexLinear ω` equals the atomic
mass `σ.real {ω}`. -/
theorem norm_starProjection_eigenspace_sq_eq_measureReal_singleton
    (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (ω : ℝ) (v : H) {σ : Measure ℝ}
    [IsFiniteMeasure σ] (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) :
    ‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 2 = σ.real {ω} := by
  have hσ_eq : σ = U.spectralMeasure hU v := U.spectralMeasure_eq_of_charFun hU v hσ
  subst hσ_eq
  let Uω := U.phaseShift hU.isComplexLinear ω
  have hUω : Uω.IsUnitary := hU.phaseShift ω
  have hlim1 : Tendsto (fun T : ℝ => ‖Uω.timeAverage T v‖ ^ 2) atTop
      (𝓝 (‖(Uω.eigenspace hUω.isComplexLinear 0).starProjection v‖ ^ 2)) :=
    ((Uω.tendsto_timeAverage hUω v).norm).pow 2
  have hlim2 : Tendsto (fun T : ℝ => ‖Uω.timeAverage T v‖ ^ 2) atTop
      (𝓝 ((Uω.spectralMeasure hUω v).real {0})) :=
    Uω.tendsto_norm_timeAverage_sq hUω v fun t => (Uω.charFun_spectralMeasure hUω v t).symm
  have heq := tendsto_nhds_unique hlim1 hlim2
  have hpre : (fun ξ : ℝ => ξ - ω) ⁻¹' {0} = {ω} := by
    ext ξ
    simp [sub_eq_zero]
  have hmass : (Uω.spectralMeasure hUω v).real {0} = (U.spectralMeasure hU v).real {ω} := by
    rw [U.spectralMeasure_phaseShift hU ω v, Measure.real_def,
      Measure.map_apply (measurable_sub_const ω) (measurableSet_singleton 0), hpre,
      ← Measure.real_def]
  rw [hmass] at heq
  simpa only [Uω, eigenspace_phaseShift, add_zero] using heq

/-- The atomic mass of `U.spectralMeasure hU v` at `ω` is the squared norm of the orthogonal
projection of `v` onto the `ω`-eigenspace. -/
theorem spectralMeasure_real_singleton (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (v : H)
    (ω : ℝ) :
    (U.spectralMeasure hU v).real {ω} =
      ‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 2 :=
  (U.norm_starProjection_eigenspace_sq_eq_measureReal_singleton hU ω v fun t =>
    (U.charFun_spectralMeasure hU v t).symm).symm

/-- **Continuous-time mean ergodic projection theorem.** For a strongly continuous unitary group
`U` on a complex Hilbert space, a frequency `a : ℝ`, and a vector `v`, the twisted averages
`(T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-2πiat) • U t v` converge in norm to the orthogonal
projection `w` of `v` onto the common eigenspace `{u | ∀ t, U t u = exp (2πiat) • u}`, and
`‖w‖²` equals `σ.real {2πa}` for every finite Borel measure `σ` with
`charFun σ t = ⟪v, U t v⟫_ℂ`. -/
theorem exists_tendsto_twistedAverage (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    (a : ℝ) (v : H) :
    ∃ w : H, (∀ t : ℝ, U t w = Complex.exp (2 * Real.pi * a * t * Complex.I) • w) ∧
      (∀ u : H, (∀ t : ℝ, U t u = Complex.exp (2 * Real.pi * a * t * Complex.I) • u) →
        ⟪u, v - w⟫_ℂ = 0) ∧
      Tendsto (fun T : ℝ => (T⁻¹ : ℂ) •
          ∫ t in (0 : ℝ)..T, Complex.exp (-(2 * Real.pi * a * t * Complex.I)) • U t v)
        atTop (𝓝 w) ∧
      ∀ σ : Measure ℝ, IsFiniteMeasure σ →
        (∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) →
        ‖w‖ ^ 2 = σ.real {2 * Real.pi * a} := by
  let K := U.eigenspace hU.isComplexLinear (2 * Real.pi * a)
  have hcast : ∀ t : ℝ,
      ((2 * Real.pi * a : ℝ) : ℂ) * (t : ℂ) * Complex.I =
        2 * Real.pi * a * t * Complex.I := fun t => by
    push_cast
    ring
  refine ⟨K.starProjection v, ?_, ?_, ?_, ?_⟩
  · intro t
    simpa only [hcast t] using
      (U.mem_eigenspace_iff hU.isComplexLinear (2 * Real.pi * a) _).mp
        (K.starProjection_apply_mem v) t
  · intro u hu
    have hu' : u ∈ K := (U.mem_eigenspace_iff hU.isComplexLinear (2 * Real.pi * a) u).mpr
      fun t => by simpa only [hcast t] using hu t
    exact Submodule.inner_right_of_mem_orthogonal hu' (K.sub_starProjection_mem_orthogonal v)
  · simpa only [hcast] using U.tendsto_twistedAverage hU (2 * Real.pi * a) v
  · intro σ _ hσ
    exact U.norm_starProjection_eigenspace_sq_eq_measureReal_singleton hU (2 * Real.pi * a) v hσ

end SpectralAtomicMass

end TauCeti.Semigroups.StronglyContinuousGroup

end
