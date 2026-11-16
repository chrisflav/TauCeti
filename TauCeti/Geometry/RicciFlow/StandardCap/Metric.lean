/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Radius
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.RicciFlow.StandardCap.Profile

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Riemannian.Coercive

/-!
# The smooth standard cap metric on a vector space

Given a standard cap profile `f` (`TauCeti.IsStandardCapProfile f`), the warped-product metric
`dr² + f(r)² g_(Sⁿ)` away from the origin extends to a smooth (`C^∞`) rotationally symmetric
Riemannian metric on the whole real inner product space `V`:

`g_x(v, w) = A(‖x‖) ⟪v, w⟫ + B(‖x‖) ⟪x, v⟫ ⟪x, w⟫`,

where `A(r) = f(r)² / r²` and `B(r) = (1 - A(r)) / r²` for `r ≠ 0`, with `A(0) = 1` and
`B(0) = 1 / 12`. Near the origin, `f(r) = 2 sin (r / 2)` gives
`A(r) = 2 (1 - cos r) / r²` and `B(r) = (1 - A(r)) / r²`, which are entire power series in `r²`,
so `x ↦ A(‖x‖)` and `x ↦ B(‖x‖)` are smooth across `0`. Since `0 < f(r) ≤ r` for `r > 0`, the
form `g_x` is symmetric and coercive at every point of `V`.

This file constructs the metric `TauCeti.IsStandardCapProfile.metric`, establishes its rotational
symmetry under all linear isometries of `V`, and proves that on any ball `Metric.ball (0 : V) r₀`
where `f(r) = 2 sin (r / 2)` the exponential-style tip map
`x ↦ ((sin (‖x‖ / 2) / ‖x‖) • x, cos (‖x‖ / 2))` into the unit sphere of `V × ℝ` is a local
Riemannian isometry onto the round sphere of radius `2`.

Finally, `TauCeti.not_exists_continuousRiemannianMetric_of_apply_zero_ne_zero` records the
obstruction at the origin: in dimension at least `2`, no continuous Riemannian metric on `V` can
agree with `dr² + f(r)² g_(Sⁿ)` on tangential vectors away from `0` if `f` is continuous at `0`
with `f(0) ≠ 0`.

## Main definitions

* `TauCeti.IsStandardCapProfile.metric`: the smooth rotationally symmetric standard cap metric on
  any real inner product space `V`.
* `TauCeti.IsStandardCapProfile.linearIsometryEquivIsometry`: rotational symmetry of the standard
  cap under linear isometric equivalences of `V`.
* `TauCeti.IsStandardCapProfile.tipSphereMap`: the smooth map `V → S^{n + 1} ⊂ V × ℝ` realizing
  the spherical cap near the origin.

## Main results

* `TauCeti.IsStandardCapProfile.metric_inner_zero`,
  `TauCeti.IsStandardCapProfile.metric_inner_of_ne_zero`: the inner product at and away from `0`.
* `TauCeti.IsStandardCapProfile.metric_inner_self_le` and
  `TauCeti.IsStandardCapProfile.radial_sq_div_norm_sq_le_metric_inner_self`: comparison with the
  Euclidean norm and the radial projection.
* `TauCeti.IsStandardCapProfile.isLocalRiemannianIsometry_tip`: the tip ball is locally isometric
  to the round sphere of radius `2`.
* `TauCeti.not_exists_continuousRiemannianMetric_of_apply_zero_ne_zero`: obstruction to extending
  `dr² + f(r)² g_(Sⁿ)` continuously across the origin when `f(0) ≠ 0`.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics Monographs 3
  (2007), Definition 12.1.
* G. Perelman, *Ricci flow with surgery on three-manifolds*, arXiv:math/0303109 (2003), §2.
-/

public noncomputable section

open Bundle Filter Metric Module Real Set TopologicalSpace
open TauCeti.Manifold
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal Topology

namespace TauCeti

/-! ### Alternating even-factorial power series -/

/-- Coefficients `(-1)^k / (2k + m)!` of the entire series `altSeries m`. -/
private def altSeriesCoeff (m k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k / ((2 * k + m).factorial : ℝ)

/-- The entire scalar power series `∑_{k ≥ 0} (-1)^k s^k / (2k + m)!`, used to express `cos √s`,
`sin √s / √s`, `2 (1 - cos √s) / s`, and `(1 - 2 (1 - cos √s) / s) / s` smoothly across `0`. -/
private def altSeries (m : ℕ) (s : ℝ) : ℝ :=
  (FormalMultilinearSeries.ofScalars ℝ (altSeriesCoeff m)).sum s

private theorem altSeries_eq_tsum (m : ℕ) (s : ℝ) :
    altSeries m s = ∑' k : ℕ, (-1 : ℝ) ^ k / ((2 * k + m).factorial : ℝ) * s ^ k := by
  rw [show altSeries m s = FormalMultilinearSeries.ofScalarsSum (altSeriesCoeff m) s from rfl]
  simpa only [altSeriesCoeff, smul_eq_mul] using
    congr_fun (FormalMultilinearSeries.ofScalarsSum_eq_tsum (E := ℝ) (altSeriesCoeff m)) s

private theorem radius_ofScalars_altSeriesCoeff (m : ℕ) :
    (FormalMultilinearSeries.ofScalars ℝ (altSeriesCoeff m)).radius = ⊤ := by
  rw [eq_top_iff]
  refine ENNReal.le_of_forall_nnreal_lt fun r _ ↦ ?_
  apply FormalMultilinearSeries.le_radius_of_summable
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_)
    (Real.summable_pow_div_factorial (r : ℝ))
  rw [FormalMultilinearSeries.ofScalars_norm, altSeriesCoeff, norm_div, norm_pow, norm_neg,
    norm_one, one_pow, Real.norm_natCast, div_mul_eq_mul_div, one_mul]
  gcongr
  omega

private theorem contDiff_altSeries (m : ℕ) : ContDiff ℝ ∞ (altSeries m) := by
  have hr : (FormalMultilinearSeries.ofScalars ℝ (altSeriesCoeff m)).radius = ⊤ :=
    radius_ofScalars_altSeriesCoeff m
  have hp : HasFPowerSeriesOnBall (altSeries m)
      (FormalMultilinearSeries.ofScalars ℝ (altSeriesCoeff m)) 0 ⊤ := by
    have h := (FormalMultilinearSeries.ofScalars ℝ (altSeriesCoeff m)).hasFPowerSeriesOnBall
      (by rw [hr]; exact ENNReal.zero_lt_top)
    rwa [hr] at h
  have han : AnalyticOnNhd ℝ (altSeries m) Set.univ := by
    simpa [Metric.eball_top] using hp.analyticOnNhd
  exact contDiffOn_univ.1 (han.contDiffOn uniqueDiffOn_univ)

private theorem summable_altSeries (m : ℕ) (s : ℝ) :
    Summable fun k : ℕ ↦ (-1 : ℝ) ^ k / ((2 * k + m).factorial : ℝ) * s ^ k := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
    (Real.summable_pow_div_factorial ‖s‖)
  rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast, norm_pow,
    div_mul_eq_mul_div, one_mul]
  gcongr
  omega

private theorem altSeries_zero (m : ℕ) : altSeries m 0 = 1 / (m.factorial : ℝ) := by
  rw [altSeries_eq_tsum, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

private theorem mul_altSeries_add_two (m : ℕ) (s : ℝ) :
    s * altSeries (m + 2) s = 1 / (m.factorial : ℝ) - altSeries m s := by
  rw [altSeries_eq_tsum, altSeries_eq_tsum, ← tsum_mul_left,
    (summable_altSeries m s).tsum_eq_zero_add]
  simp only [pow_zero, mul_zero, zero_add, mul_one, one_div]
  have hterm (k : ℕ) :
      s * ((-1 : ℝ) ^ k / ((2 * k + (m + 2)).factorial : ℝ) * s ^ k) =
        -((-1 : ℝ) ^ (k + 1) / ((2 * (k + 1) + m).factorial : ℝ) * s ^ (k + 1)) := by
    have hidx : 2 * k + (m + 2) = 2 * (k + 1) + m := by omega
    rw [hidx, pow_succ, pow_succ]
    ring
  simp_rw [hterm, tsum_neg]
  ring

private theorem altSeries_zero_sq (r : ℝ) : altSeries 0 (r ^ 2) = cos r := by
  rw [altSeries_eq_tsum, Real.cos_eq_tsum]
  refine tsum_congr fun k ↦ ?_
  rw [add_zero, ← pow_mul, div_mul_eq_mul_div]

private theorem mul_altSeries_one_sq (r : ℝ) : r * altSeries 1 (r ^ 2) = sin r := by
  rw [altSeries_eq_tsum, Real.sin_eq_tsum, ← tsum_mul_left]
  refine tsum_congr fun k ↦ ?_
  rw [pow_succ r (2 * k), ← pow_mul]
  ring

private theorem sq_mul_two_mul_altSeries_two (r : ℝ) :
    r ^ 2 * (2 * altSeries 2 (r ^ 2)) = (2 * sin (r / 2)) ^ 2 := by
  have h1 := mul_altSeries_add_two 0 (r ^ 2)
  rw [altSeries_zero_sq] at h1
  norm_num [Nat.factorial] at h1
  have hcos : cos r = 1 - 2 * sin (r / 2) ^ 2 := by
    have := Real.cos_two_mul' (r / 2)
    have htrig := Real.sin_sq_add_cos_sq (r / 2)
    have h2 : 2 * (r / 2) = r := by ring
    rw [h2] at this
    nlinarith
  nlinarith

private theorem sq_mul_two_mul_altSeries_four (r : ℝ) :
    r ^ 2 * (2 * altSeries 4 (r ^ 2)) = 1 - 2 * altSeries 2 (r ^ 2) := by
  have h := mul_altSeries_add_two 2 (r ^ 2)
  norm_num [Nat.factorial] at h
  linarith

namespace IsStandardCapProfile

/-! ### The smooth standard cap metric on a real inner product space -/

section MetricCoeffs

/-- The tangential metric coefficient `A(r) = f(r)² / r²` for `r ≠ 0` and `A(0) = 1`. -/
private def capCoeffA (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then 1 else (f r / r) ^ 2

/-- The radial correction coefficient `B(r) = (1 - A(r)) / r²` for `r ≠ 0` and `B(0) = 1 / 12`. -/
private def capCoeffB (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then 1 / 12 else (1 - (f r / r) ^ 2) / r ^ 2

private theorem capCoeffA_eq_tip {f : ℝ → ℝ} {r : ℝ} (h : f r = 2 * sin (r / 2)) :
    capCoeffA f r = 2 * altSeries 2 (r ^ 2) := by
  unfold capCoeffA
  split_ifs with h0
  · subst h0
    simp [altSeries_zero, Nat.factorial]
  · have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 h0
    have hsq := sq_mul_two_mul_altSeries_two r
    rw [h, div_pow, eq_comm, eq_div_iff hr2]
    linarith

private theorem capCoeffB_eq_tip {f : ℝ → ℝ} {r : ℝ} (h : f r = 2 * sin (r / 2)) :
    capCoeffB f r = 2 * altSeries 4 (r ^ 2) := by
  unfold capCoeffB
  split_ifs with h0
  · subst h0
    norm_num [altSeries_zero, Nat.factorial]
  · have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 h0
    have hA : (f r / r) ^ 2 = 2 * altSeries 2 (r ^ 2) := by
      simpa [capCoeffA, h0] using capCoeffA_eq_tip h
    have hsq := sq_mul_two_mul_altSeries_four r
    rw [hA, eq_comm, eq_div_iff hr2]
    linarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The real inner product viewed as a bilinear continuous map `V →L[ℝ] V →L[ℝ] ℝ`. -/
private def realInnerBL (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    V →L[ℝ] V →L[ℝ] ℝ :=
  innerSL ℝ

private theorem realInnerBL_apply (v w : V) : realInnerBL V v w = ⟪v, w⟫_ℝ :=
  rfl

/-- The bilinear form of the standard cap metric at `x ∈ V`:
`g_x(v, w) = A(‖x‖) ⟪v, w⟫ + B(‖x‖) ⟪x, v⟫ ⟪x, w⟫`. -/
private def capForm (f : ℝ → ℝ) (x : V) : V →L[ℝ] V →L[ℝ] ℝ :=
  capCoeffA f ‖x‖ • realInnerBL V +
    (capCoeffB f ‖x‖ • realInnerBL V x).smulRight (realInnerBL V x)

private theorem capForm_apply (f : ℝ → ℝ) (x v w : V) :
    capForm f x v w =
      capCoeffA f ‖x‖ * ⟪v, w⟫_ℝ + capCoeffB f ‖x‖ * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) := by
  simp only [capForm, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    realInnerBL_apply, smul_eq_mul]
  ring

end MetricCoeffs

section MetricConstruction

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
include hf

private theorem capCoeffA_pos {r : ℝ} (hr : 0 ≤ r) : 0 < capCoeffA f r := by
  unfold capCoeffA
  split_ifs with h0
  · exact one_pos
  · exact sq_pos_of_pos (div_pos (hf.apply_pos (hr.lt_of_ne' h0)) (hr.lt_of_ne' h0))

private theorem capCoeffA_le_one {r : ℝ} (hr : 0 ≤ r) : capCoeffA f r ≤ 1 := by
  unfold capCoeffA
  split_ifs with h0
  · exact le_rfl
  · have hpos : 0 < r := hr.lt_of_ne' h0
    have hle : f r / r ≤ 1 := (div_le_one hpos).2 (hf.apply_le_self hr)
    have hnn : 0 ≤ f r / r := div_nonneg (hf.apply_nonneg hr) hr
    nlinarith

private theorem capCoeffB_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ capCoeffB f r := by
  unfold capCoeffB
  split_ifs with h0
  · norm_num
  · have hA : (f r / r) ^ 2 ≤ 1 := by
      simpa [capCoeffA, h0] using hf.capCoeffA_le_one hr
    exact div_nonneg (sub_nonneg.2 hA) (sq_nonneg r)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem contDiff_capCoeffA_norm : ContDiff ℝ ∞ fun x : V ↦ capCoeffA f ‖x‖ := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · obtain ⟨r₀, hr₀, htip⟩ := hf.exists_eq_two_mul_sin
    have hev : (fun z : V ↦ capCoeffA f ‖z‖) =ᶠ[𝓝 (0 : V)]
        fun z ↦ 2 * altSeries 2 (‖z‖ ^ 2) := by
      filter_upwards [Metric.ball_mem_nhds (0 : V) hr₀] with z hz
      exact capCoeffA_eq_tip (htip ‖z‖ ⟨norm_nonneg z, by simpa [mem_ball_zero_iff] using hz⟩)
    exact ((contDiff_const.mul ((contDiff_altSeries 2).comp
      (contDiff_norm_sq ℝ))).contDiffAt).congr_of_eventuallyEq hev
  · have hev : (fun z : V ↦ capCoeffA f ‖z‖) =ᶠ[𝓝 x] fun z ↦ (f ‖z‖ / ‖z‖) ^ 2 := by
      filter_upwards [isOpen_ne.mem_nhds hx] with z hz
      simp [capCoeffA, norm_ne_zero_iff.2 hz]
    have hnorm : ContDiffAt ℝ ∞ (fun z : V ↦ ‖z‖) x := contDiffAt_norm ℝ hx
    exact (((hf.contDiff.contDiffAt.comp x hnorm).div hnorm
      (norm_ne_zero_iff.2 hx)).pow 2).congr_of_eventuallyEq hev

private theorem contDiff_capCoeffB_norm : ContDiff ℝ ∞ fun x : V ↦ capCoeffB f ‖x‖ := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · obtain ⟨r₀, hr₀, htip⟩ := hf.exists_eq_two_mul_sin
    have hev : (fun z : V ↦ capCoeffB f ‖z‖) =ᶠ[𝓝 (0 : V)]
        fun z ↦ 2 * altSeries 4 (‖z‖ ^ 2) := by
      filter_upwards [Metric.ball_mem_nhds (0 : V) hr₀] with z hz
      exact capCoeffB_eq_tip (htip ‖z‖ ⟨norm_nonneg z, by simpa [mem_ball_zero_iff] using hz⟩)
    exact ((contDiff_const.mul ((contDiff_altSeries 4).comp
      (contDiff_norm_sq ℝ))).contDiffAt).congr_of_eventuallyEq hev
  · have hev : (fun z : V ↦ capCoeffB f ‖z‖) =ᶠ[𝓝 x]
        fun z ↦ (1 - (f ‖z‖ / ‖z‖) ^ 2) / ‖z‖ ^ 2 := by
      filter_upwards [isOpen_ne.mem_nhds hx] with z hz
      simp [capCoeffB, norm_ne_zero_iff.2 hz]
    have hnorm : ContDiffAt ℝ ∞ (fun z : V ↦ ‖z‖) x := contDiffAt_norm ℝ hx
    exact ((contDiffAt_const.sub (((hf.contDiff.contDiffAt.comp x hnorm).div hnorm
      (norm_ne_zero_iff.2 hx)).pow 2)).div (hnorm.pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.2 hx))).congr_of_eventuallyEq hev

private theorem contDiff_capForm : ContDiff ℝ ∞ (capForm (V := V) f) := by
  have hA : ContDiff ℝ ∞ fun x : V ↦ capCoeffA f ‖x‖ • realInnerBL V := by
    have hcomp :
        (fun x : V ↦ capCoeffA f ‖x‖ • realInnerBL V) =
          fun x ↦ (realInnerBL V).comp (capCoeffA f ‖x‖ • ContinuousLinearMap.id ℝ V) := by
      ext x v w
      simp [realInnerBL_apply]
    rw [hcomp]
    exact contDiff_const.clm_comp
      (hf.contDiff_capCoeffA_norm.smul (contDiff_const (c := ContinuousLinearMap.id ℝ V)))
  exact hA.add
    ((hf.contDiff_capCoeffB_norm.smul (realInnerBL V).contDiff).smulRight (realInnerBL V).contDiff)

private theorem isCoercive_capForm (x : V) : IsCoercive (capForm f x) := by
  refine ⟨capCoeffA f ‖x‖, hf.capCoeffA_pos (norm_nonneg x), fun v ↦ ?_⟩
  rw [capForm_apply, real_inner_self_eq_norm_sq]
  have hB : 0 ≤ capCoeffB f ‖x‖ * (⟪x, v⟫_ℝ * ⟪x, v⟫_ℝ) :=
    mul_nonneg (hf.capCoeffB_nonneg (norm_nonneg x)) (mul_self_nonneg _)
  linarith

variable (V) in
/-- The **standard cap metric** on a real inner product space `V` associated to a standard cap
profile `f`: the smooth rotationally symmetric Riemannian metric extending `dr² + f(r)² g_(Sⁿ)`
across the origin `0 ∈ V`. -/
def metric :
    ContMDiffRiemannianMetric 𝓘(ℝ, V) ∞ V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) :=
  coerciveRiemannianMetric (capForm (V := V) f) hf.contDiff_capForm
    (fun x v w ↦ by
      simp only [capForm_apply, real_inner_comm v w, mul_comm ⟪x, v⟫_ℝ])
    hf.isCoercive_capForm

/-- At the origin, the standard cap metric coincides with the Euclidean inner product of `V`. -/
@[simp]
theorem metric_inner_zero (v w : TangentSpace 𝓘(ℝ, V) (0 : V)) :
    (hf.metric V).inner 0 v w =
      ⟪NormedSpace.fromTangentSpace (0 : V) v, NormedSpace.fromTangentSpace (0 : V) w⟫_ℝ := by
  rw [metric, coerciveRiemannianMetric_inner, capForm_apply]
  simp only [norm_zero, capCoeffA, ite_true, one_mul, inner_zero_left, mul_zero, add_zero]
  rfl

/-- Away from the origin, the standard cap metric splits into tangential and radial parts
according to `(f(‖x‖) / ‖x‖)² ⟪v, w⟫ + ((1 - (f(‖x‖) / ‖x‖)²) / ‖x‖²) ⟪x, v⟫ ⟪x, w⟫`. -/
theorem metric_inner_of_ne_zero {x : V} (hx : x ≠ 0) (v w : TangentSpace 𝓘(ℝ, V) x) :
    (hf.metric V).inner x v w =
      (f ‖x‖ / ‖x‖) ^ 2 *
          ⟪NormedSpace.fromTangentSpace x v, NormedSpace.fromTangentSpace x w⟫_ℝ +
        (1 - (f ‖x‖ / ‖x‖) ^ 2) / ‖x‖ ^ 2 *
          (⟪x, NormedSpace.fromTangentSpace x v⟫_ℝ * ⟪x, NormedSpace.fromTangentSpace x w⟫_ℝ) := by
  rw [metric, coerciveRiemannianMetric_inner, capForm_apply]
  simp only [capCoeffA, capCoeffB, norm_ne_zero_iff.2 hx, ite_false]
  rfl

/-- The standard cap metric is bounded above by the Euclidean inner product everywhere on `V`. -/
theorem metric_inner_self_le (x : V) (v : TangentSpace 𝓘(ℝ, V) x) :
    (hf.metric V).inner x v v ≤ ‖NormedSpace.fromTangentSpace x v‖ ^ 2 := by
  set u : V := NormedSpace.fromTangentSpace x v
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hf.metric_inner_zero, real_inner_self_eq_norm_sq]
  · rw [hf.metric_inner_of_ne_zero hx, real_inner_self_eq_norm_sq]
    have hA : (f ‖x‖ / ‖x‖) ^ 2 ≤ 1 := by
      simpa [capCoeffA, norm_ne_zero_iff.2 hx] using hf.capCoeffA_le_one (norm_nonneg x)
    have hcs : ⟪x, u⟫_ℝ * ⟪x, u⟫_ℝ ≤ ‖x‖ ^ 2 * ‖u‖ ^ 2 := by
      have hsq := mul_self_le_mul_self (abs_nonneg ⟪x, u⟫_ℝ) (abs_real_inner_le_norm x u)
      rw [abs_mul_abs_self] at hsq
      linarith
    have hdiv : ⟪x, u⟫_ℝ * ⟪x, u⟫_ℝ / ‖x‖ ^ 2 ≤ ‖u‖ ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.2 hx))).2 (by linarith)
    have _ : 0 ≤ 1 - (f ‖x‖ / ‖x‖) ^ 2 := sub_nonneg.2 hA
    calc (f ‖x‖ / ‖x‖) ^ 2 * ‖u‖ ^ 2 + (1 - (f ‖x‖ / ‖x‖) ^ 2) / ‖x‖ ^ 2 * (⟪x, u⟫_ℝ * ⟪x, u⟫_ℝ)
        = (f ‖x‖ / ‖x‖) ^ 2 * ‖u‖ ^ 2 +
            (1 - (f ‖x‖ / ‖x‖) ^ 2) * (⟪x, u⟫_ℝ * ⟪x, u⟫_ℝ / ‖x‖ ^ 2) := by ring
      _ ≤ (f ‖x‖ / ‖x‖) ^ 2 * ‖u‖ ^ 2 + (1 - (f ‖x‖ / ‖x‖) ^ 2) * ‖u‖ ^ 2 := by gcongr
      _ = ‖u‖ ^ 2 := by ring

/-- Away from the origin, the squared radial component `⟪x, v⟫² / ‖x‖²` is bounded above by the
standard cap metric norm squared. -/
theorem radial_sq_div_norm_sq_le_metric_inner_self {x : V} (hx : x ≠ 0)
    (v : TangentSpace 𝓘(ℝ, V) x) :
    ⟪x, NormedSpace.fromTangentSpace x v⟫_ℝ ^ 2 / ‖x‖ ^ 2 ≤ (hf.metric V).inner x v v := by
  set u : V := NormedSpace.fromTangentSpace x v
  rw [hf.metric_inner_of_ne_zero hx, real_inner_self_eq_norm_sq]
  have hpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.2 hx)
  have hcs : ⟪x, u⟫_ℝ ^ 2 / ‖x‖ ^ 2 ≤ ‖u‖ ^ 2 :=
    (div_le_iff₀ hpos).2 <| by
      have hsq := mul_self_le_mul_self (abs_nonneg ⟪x, u⟫_ℝ) (abs_real_inner_le_norm x u)
      rw [abs_mul_abs_self] at hsq
      nlinarith
  have hA : 0 ≤ (f ‖x‖ / ‖x‖) ^ 2 := sq_nonneg _
  have hdiff : 0 ≤ (f ‖x‖ / ‖x‖) ^ 2 * (‖u‖ ^ 2 - ⟪x, u⟫_ℝ ^ 2 / ‖x‖ ^ 2) :=
    mul_nonneg hA (sub_nonneg.2 hcs)
  have hrewrite :
      (f ‖x‖ / ‖x‖) ^ 2 * ‖u‖ ^ 2 + (1 - (f ‖x‖ / ‖x‖) ^ 2) / ‖x‖ ^ 2 * (⟪x, u⟫_ℝ * ⟪x, u⟫_ℝ) =
        ⟪x, u⟫_ℝ ^ 2 / ‖x‖ ^ 2 + (f ‖x‖ / ‖x‖) ^ 2 * (‖u‖ ^ 2 - ⟪x, u⟫_ℝ ^ 2 / ‖x‖ ^ 2) := by
    field_simp
    ring
  linarith

/-- Along any ray `t ↦ t • x`, the radial vector `x` has standard cap norm equal to its Euclidean
norm `‖x‖`. -/
theorem metric_inner_self_smul (t : ℝ) (x : V) :
    (hf.metric V).inner (t • x) ((NormedSpace.fromTangentSpace (t • x)).symm x)
      ((NormedSpace.fromTangentSpace (t • x)).symm x) = ‖x‖ ^ 2 := by
  rcases eq_or_ne (t • x) 0 with h0 | h0
  · rw [h0, hf.metric_inner_zero, ContinuousLinearEquiv.apply_symm_apply,
      real_inner_self_eq_norm_sq]
  · rw [hf.metric_inner_of_ne_zero h0, ContinuousLinearEquiv.apply_symm_apply,
      real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    have ht : t ≠ 0 := fun h ↦ h0 (by simp [h])
    have hx : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 fun h ↦ h0 (by simp [h])
    field_simp
    ring

/-! ### Rotational symmetry -/

/-- The standard cap metric is invariant under every linear isometric equivalence of `V`. -/
theorem metric_inner_linearIsometryEquiv (U : V ≃ₗᵢ[ℝ] V) (x : V)
    (v w : TangentSpace 𝓘(ℝ, V) x) :
    (hf.metric V).inner (U x)
      ((NormedSpace.fromTangentSpace (U x)).symm (U (NormedSpace.fromTangentSpace x v)))
      ((NormedSpace.fromTangentSpace (U x)).symm (U (NormedSpace.fromTangentSpace x w))) =
      (hf.metric V).inner x v w := by
  rw [metric, coerciveRiemannianMetric_inner, coerciveRiemannianMetric_inner, capForm_apply,
    capForm_apply]
  change capCoeffA f ‖U x‖ * ⟪U (NormedSpace.fromTangentSpace x v),
        U (NormedSpace.fromTangentSpace x w)⟫_ℝ +
      capCoeffB f ‖U x‖ * (⟪U x, U (NormedSpace.fromTangentSpace x v)⟫_ℝ *
        ⟪U x, U (NormedSpace.fromTangentSpace x w)⟫_ℝ) = _
  simp only [U.norm_map, U.inner_map_map]
  rfl

/-- Every linear isometric equivalence of a finite-dimensional real inner product space `V` induces
a smooth Riemannian isometry of the standard cap fixing the origin. -/
def linearIsometryEquivIsometry [FiniteDimensional ℝ V] (U : V ≃ₗᵢ[ℝ] V) :
    RiemannianIsometry 𝓘(ℝ, V) 𝓘(ℝ, V) (WithMetric (hf.metric V)) (WithMetric (hf.metric V)) where
  toDiffeomorph :=
    (WithMetric.diffeomorph (hf.metric V) ∞).trans
      (U.toContinuousLinearEquiv.toDiffeomorph.trans
        (WithMetric.diffeomorph (hf.metric V) ∞).symm)
  inner_mfderiv' x v w := by
    let Φ : WithMetric (hf.metric V) → WithMetric (hf.metric V) :=
      fun p ↦ WithMetric.toWithMetric (hf.metric V) (U p.ofWithMetric)
    have hΦ_eq : (⇑((WithMetric.diffeomorph (hf.metric V) ∞).trans
        (U.toContinuousLinearEquiv.toDiffeomorph.trans
          (WithMetric.diffeomorph (hf.metric V) ∞).symm))) = Φ := by
      ext p
      simp [Φ, WithMetric.coe_diffeomorph, WithMetric.coe_diffeomorph_symm]
    rw [hΦ_eq, WithMetric.inner_def, WithMetric.inner_def]
    have hd : ∀ u : TangentSpace 𝓘(ℝ, V) x,
        mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric (Φ x) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) Φ x u) =
          (NormedSpace.fromTangentSpace (U x.ofWithMetric)).symm
            (U (NormedSpace.fromTangentSpace x.ofWithMetric
              (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric x u))) := fun u ↦ by
      have hcomp : WithMetric.ofWithMetric ∘ Φ = U ∘ WithMetric.ofWithMetric := rfl
      have hΦ_smooth : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ Φ :=
        (WithMetric.contMDiff_toWithMetric (k := ∞)).comp
          (U.toContinuousLinearEquiv.contDiff.contMDiff.comp
            (WithMetric.contMDiff_ofWithMetric (k := ∞)))
      have h1 : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric (Φ x)
            (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) Φ x u) =
          mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (U ∘ WithMetric.ofWithMetric) x u := by
        rw [← hcomp, mfderiv_comp_apply x
          (WithMetric.hasMFDerivAt_ofWithMetric (Φ x)).mdifferentiableAt
          (hΦ_smooth.mdifferentiableAt (by simp))]
      rw [h1, WithMetric.mfderiv_comp_ofWithMetric, ContinuousLinearMap.comp_apply]
      apply (NormedSpace.fromTangentSpace (U x.ofWithMetric)).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, ← mvfderiv_apply_eq_mfderiv_apply,
        NormedSpace.fromTangentSpace_apply]
      have hU : mvfderiv 𝓘(ℝ, V) U x.ofWithMetric =
          U.toContinuousLinearMap ∘L
            (NormedSpace.fromTangentSpace x.ofWithMetric).toContinuousLinearMap := by
        ext z
        have hfU : HasFDerivAt (⇑U) U.toContinuousLinearMap x.ofWithMetric :=
          U.toContinuousLinearMap.hasFDerivAt
        simp [mvfderiv, mfderiv_eq_fderiv, hfU.fderiv]
      simp only [hU, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      rfl
    rw [hd v, hd w]
    exact hf.metric_inner_linearIsometryEquiv U x.ofWithMetric _ _

/-- Evaluation of the rotational symmetry `linearIsometryEquivIsometry`. -/
@[simp]
theorem linearIsometryEquivIsometry_apply [FiniteDimensional ℝ V] (U : V ≃ₗᵢ[ℝ] V)
    (x : WithMetric (hf.metric V)) :
    hf.linearIsometryEquivIsometry U x =
      WithMetric.toWithMetric (hf.metric V) (U x.ofWithMetric) := by
  change ((WithMetric.diffeomorph (hf.metric V) ∞).trans
    (U.toContinuousLinearEquiv.toDiffeomorph.trans
      (WithMetric.diffeomorph (hf.metric V) ∞).symm)) x = _
  simp [WithMetric.coe_diffeomorph, WithMetric.coe_diffeomorph_symm]

/-- Every rotational symmetry `linearIsometryEquivIsometry` fixes the origin `0`. -/
theorem linearIsometryEquivIsometry_zero [FiniteDimensional ℝ V] (U : V ≃ₗᵢ[ℝ] V) :
    hf.linearIsometryEquivIsometry U (WithMetric.toWithMetric (hf.metric V) 0) =
      WithMetric.toWithMetric (hf.metric V) 0 := by
  simp [linearIsometryEquivIsometry_apply]

end MetricConstruction

/-! ### Round spherical tip local isometry -/

section Tip

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The smooth ambient map `x ↦ ((sin (‖x‖ / 2) / ‖x‖) • x, cos (‖x‖ / 2))` into `V × ℝ`,
taking values on the unit sphere of `WithLp 2 (V × ℝ)`. -/
private def tipSphereAmbientMap (x : V) : WithLp 2 (V × ℝ) :=
  WithLp.toLp 2 (((1 / 2 : ℝ) * altSeries 1 ((1 / 4 : ℝ) * ‖x‖ ^ 2)) • x,
    altSeries 0 ((1 / 4 : ℝ) * ‖x‖ ^ 2))

private theorem tipSphereAmbientMap_eq_trig {x : V} (hx : x ≠ 0) :
    tipSphereAmbientMap x =
      WithLp.toLp 2 ((sin (‖x‖ / 2) / ‖x‖) • x, cos (‖x‖ / 2)) := by
  have hsq : (1 / 4 : ℝ) * ‖x‖ ^ 2 = (‖x‖ / 2) ^ 2 := by ring
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hsin : (1 / 2 : ℝ) * altSeries 1 ((1 / 4 : ℝ) * ‖x‖ ^ 2) = sin (‖x‖ / 2) / ‖x‖ := by
    rw [hsq, ← mul_altSeries_one_sq (‖x‖ / 2)]
    field_simp
  have hcos : altSeries 0 ((1 / 4 : ℝ) * ‖x‖ ^ 2) = cos (‖x‖ / 2) := by
    rw [hsq, altSeries_zero_sq]
  simp only [tipSphereAmbientMap, hsin, hcos]

private theorem norm_tipSphereAmbientMap (x : V) : ‖tipSphereAmbientMap x‖ = 1 := by
  have hsq : ‖tipSphereAmbientMap x‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    rcases eq_or_ne x 0 with rfl | hx
    · simp [tipSphereAmbientMap, altSeries_zero, Nat.factorial]
    · rw [tipSphereAmbientMap_eq_trig hx]
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_smul, Real.norm_eq_abs, mul_pow,
        sq_abs, div_pow]
      have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      rw [div_mul_cancel₀ _ (pow_ne_zero 2 hnorm), Real.sin_sq_add_cos_sq]
  nlinarith [norm_nonneg (tipSphereAmbientMap x)]

private theorem contDiff_tipSphereAmbientMap : ContDiff ℝ ∞ (tipSphereAmbientMap (V := V)) := by
  have harg : ContDiff ℝ ∞ fun x : V ↦ (1 / 4 : ℝ) * ‖x‖ ^ 2 :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  have h1 : ContDiff ℝ ∞ fun x : V ↦ ((1 / 2 : ℝ) * altSeries 1 ((1 / 4 : ℝ) * ‖x‖ ^ 2)) • x :=
    (contDiff_const.mul ((contDiff_altSeries 1).comp harg)).smul contDiff_id
  have h2 : ContDiff ℝ ∞ fun x : V ↦ altSeries 0 ((1 / 4 : ℝ) * ‖x‖ ^ 2) :=
    (contDiff_altSeries 0).comp harg
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm.contDiff.comp (h1.prodMk h2)

private theorem four_mul_inner_fderiv_tipSphereAmbientMap_zero (v w : V) :
    4 * ⟪fderiv ℝ (tipSphereAmbientMap (V := V)) 0 v,
        fderiv ℝ (tipSphereAmbientMap (V := V)) 0 w⟫_ℝ = ⟪v, w⟫_ℝ := by
  have harg : HasFDerivAt (fun x : V ↦ (1 / 4 : ℝ) * ‖x‖ ^ 2) (0 : V →L[ℝ] ℝ) 0 := by
    simpa using ((hasStrictFDerivAt_norm_sq (0 : V)).hasFDerivAt).const_mul (1 / 4 : ℝ)
  have h0_eq : (1 / 4 : ℝ) * ‖(0 : V)‖ ^ 2 = 0 := by simp
  have h1 : HasFDerivAt (fun x : V ↦ ((1 / 2 : ℝ) * altSeries 1 ((1 / 4 : ℝ) * ‖x‖ ^ 2)) • x)
      ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ V) 0 := by
    have hcoeff : HasFDerivAt (fun x : V ↦ (1 / 2 : ℝ) * altSeries 1 ((1 / 4 : ℝ) * ‖x‖ ^ 2))
        (0 : V →L[ℝ] ℝ) 0 := by
      have hd := (((contDiff_altSeries 1).differentiable (by simp))
        ((1 / 4 : ℝ) * ‖(0 : V)‖ ^ 2)).hasDerivAt
      simpa [Function.comp_def] using (hd.comp_hasFDerivAt 0 harg).const_mul (1 / 2 : ℝ)
    have hsm := hcoeff.fun_smul (hasFDerivAt_id (0 : V))
    simpa [h0_eq, altSeries_zero, Nat.factorial] using hsm
  have h2 : HasFDerivAt (fun x : V ↦ altSeries 0 ((1 / 4 : ℝ) * ‖x‖ ^ 2)) (0 : V →L[ℝ] ℝ) 0 := by
    have hd := (((contDiff_altSeries 0).differentiable (by simp))
      ((1 / 4 : ℝ) * ‖(0 : V)‖ ^ 2)).hasDerivAt
    simpa [Function.comp_def] using hd.comp_hasFDerivAt 0 harg
  have htot : HasFDerivAt (tipSphereAmbientMap (V := V))
      ((WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm.toContinuousLinearMap.comp
        (((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ V).prod (0 : V →L[ℝ] ℝ))) 0 :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm.hasFDerivAt.comp 0 (h1.prodMk h2)
  rw [htot.fderiv]
  simp [WithLp.prod_inner_apply, real_inner_smul_left, real_inner_smul_right]
  ring

private theorem four_mul_inner_fderiv_tipSphereAmbientMap_of_ne_zero {x : V} (hx : x ≠ 0)
    (v w : V) :
    4 * ⟪fderiv ℝ (tipSphereAmbientMap (V := V)) x v,
        fderiv ℝ (tipSphereAmbientMap (V := V)) x w⟫_ℝ =
      (2 * sin (‖x‖ / 2) / ‖x‖) ^ 2 * ⟪v, w⟫_ℝ +
        (1 - (2 * sin (‖x‖ / 2) / ‖x‖) ^ 2) / ‖x‖ ^ 2 * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hev : tipSphereAmbientMap =ᶠ[𝓝 x]
      fun z : V ↦ WithLp.toLp 2 ((sin (‖z‖ / 2) / ‖z‖) • z, cos (‖z‖ / 2)) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with z hz using tipSphereAmbientMap_eq_trig hz
  have hdn : HasFDerivAt (fun z : V ↦ ‖z‖) (‖x‖⁻¹ • innerSL ℝ x) x :=
    hasFDerivAt_norm_of_ne hx
  have hsin_div : HasDerivAt (fun r : ℝ ↦ sin (r / 2) / r)
      ((cos (‖x‖ / 2) * (1 / 2) * ‖x‖ - sin (‖x‖ / 2)) / ‖x‖ ^ 2) ‖x‖ := by
    have h := (((hasDerivAt_id' ‖x‖).div_const 2).sin).div (hasDerivAt_id' ‖x‖) hnorm
    convert h using 1
    ring
  have hcos_half : HasDerivAt (fun r : ℝ ↦ cos (r / 2)) (-(sin (‖x‖ / 2) * (1 / 2))) ‖x‖ := by
    have h := ((hasDerivAt_id' ‖x‖).div_const 2).cos
    convert h using 1
    ring
  have h1 := (hsin_div.comp_hasFDerivAt x hdn).smul (hasFDerivAt_id x)
  have h2 := hcos_half.comp_hasFDerivAt x hdn
  have htot := ((WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm.hasFDerivAt.comp x
    (h1.prodMk h2)).congr_of_eventuallyEq hev
  rw [htot.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    WithLp.prodContinuousLinearEquiv_symm_apply, ContinuousLinearMap.prod_apply,
    add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    Function.comp_apply, id_eq, coe_innerSL_apply, WithLp.prod_inner_apply, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    RCLike.inner_apply, conj_trivial, smul_eq_mul]
  rw [real_inner_comm x v]
  have htrig : cos (‖x‖ / 2) ^ 2 = 1 - sin (‖x‖ / 2) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (‖x‖ / 2)]
  field_simp
  linear_combination 4 * ‖x‖ ^ 2 * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ * htrig

/-- The tip sphere map `V → S^{n + 1} ⊂ V × ℝ`, sending `x` to
`((sin (‖x‖ / 2) / ‖x‖) • x, cos (‖x‖ / 2))`. On the tip ball where `f(r) = 2 sin (r / 2)`, it
pulls the round metric of radius `2` back to `hf.metric V`. -/
def tipSphereMap (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x : V) :
    Metric.sphere (0 : WithLp 2 (V × ℝ)) 1 :=
  ⟨tipSphereAmbientMap x, mem_sphere_zero_iff_norm.2 (norm_tipSphereAmbientMap x)⟩

/-- Away from the origin, `tipSphereMap` agrees with
`((sin (‖x‖ / 2) / ‖x‖) • x, cos (‖x‖ / 2))`. -/
theorem coe_tipSphereMap_of_ne_zero {x : V} (hx : x ≠ 0) :
    (tipSphereMap V x : WithLp 2 (V × ℝ)) =
      WithLp.toLp 2 ((sin (‖x‖ / 2) / ‖x‖) • x, cos (‖x‖ / 2)) :=
  tipSphereAmbientMap_eq_trig hx

/-- At the origin, `tipSphereMap` maps `0` to the north pole `(0, 1)`. -/
@[simp]
theorem coe_tipSphereMap_zero :
    (tipSphereMap V (0 : V) : WithLp 2 (V × ℝ)) = WithLp.toLp 2 (0, 1) := by
  simp [tipSphereMap, tipSphereAmbientMap, altSeries_zero, Nat.factorial]

private theorem mvfderiv_tipSphereMap_apply {n : ℕ}
    [Fact (Module.finrank ℝ (WithLp 2 (V × ℝ)) = (n + 1) + 1)]
    {r₀ : ℝ} (x : (⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩ : Opens V))
    (u : TangentSpace 𝓘(ℝ, V) x) :
    mvfderiv (𝓡 (n + 1)) ((↑) : Metric.sphere (0 : WithLp 2 (V × ℝ)) 1 → WithLp 2 (V × ℝ))
        (tipSphereMap V x)
        (mfderiv 𝓘(ℝ, V) (𝓡 (n + 1))
          (fun z : (⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩ : Opens V) ↦
            tipSphereMap V (z : V)) x u) =
      fderiv ℝ (tipSphereAmbientMap (V := V)) (x : V)
        (NormedSpace.fromTangentSpace (x : V) (tangentSpaceOpenEquiv (I := 𝓘(ℝ, V)) x u)) := by
  let B : Opens V := ⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩
  have hB_smooth : ContMDiff 𝓘(ℝ, V) (𝓡 (n + 1)) ∞ (fun z : B ↦ tipSphereMap V (z : V)) :=
    (contDiff_tipSphereAmbientMap.contMDiff.codRestrict_sphere _).comp contMDiff_subtype_val
  have hcomp : ((↑) : Metric.sphere (0 : WithLp 2 (V × ℝ)) 1 → WithLp 2 (V × ℝ)) ∘
      (fun z : B ↦ tipSphereMap V (z : V)) = tipSphereAmbientMap ∘ Subtype.val := rfl
  have h1 := mvfderiv_comp_apply x
    ((contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero)
    (hB_smooth.mdifferentiableAt (by simp)) u
  rw [← h1, hcomp, mvfderiv_comp_apply x
    (contDiff_tipSphereAmbientMap.contMDiff.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (U := B) (n := ∞)).mdifferentiableAt (by simp)),
    Manifold.mfderiv_subtype_val, mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
  rfl

private theorem inner_mfderiv_tipSphereMap {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
    {n : ℕ} [Fact (Module.finrank ℝ (WithLp 2 (V × ℝ)) = (n + 1) + 1)] {r₀ : ℝ}
    (htip : ∀ r ∈ Ico 0 r₀, f r = 2 * sin (r / 2))
    (x : (⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩ : Opens V))
    (v w : TangentSpace 𝓘(ℝ, V) x) :
    (sphereRoundMetricOfRadius (E := WithLp 2 (V × ℝ)) (n := n + 1) 2 two_pos).inner
        (tipSphereMap V x)
        (mfderiv 𝓘(ℝ, V) (𝓡 (n + 1))
          (fun z : (⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩ : Opens V) ↦
            tipSphereMap V (z : V)) x v)
        (mfderiv 𝓘(ℝ, V) (𝓡 (n + 1))
          (fun z : (⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩ : Opens V) ↦
            tipSphereMap V (z : V)) x w) =
      ((hf.metric V).restrictOpenTangentSpace
        ⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩).inner x v w := by
  rw [sphereRoundMetricOfRadius_inner, inner_tangentSpace_sphere,
    ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
    mvfderiv_tipSphereMap_apply x v, mvfderiv_tipSphereMap_apply x w,
    show (2 : ℝ) ^ 2 = 4 by norm_num]
  rcases eq_or_ne (x : V) 0 with hx0 | hx0
  · have hv_eq : ((hf.metric V).inner (x : V) (tangentSpaceOpenEquiv (I := 𝓘(ℝ, V)) x v)
        (tangentSpaceOpenEquiv (I := 𝓘(ℝ, V)) x w)) =
      ⟪NormedSpace.fromTangentSpace (x : V) (tangentSpaceOpenEquiv (I := 𝓘(ℝ, V)) x v),
        NormedSpace.fromTangentSpace (x : V) (tangentSpaceOpenEquiv (I := 𝓘(ℝ, V)) x w)⟫_ℝ := by
      cases x with
      | mk xv hxv =>
        dsimp only at hx0 ⊢
        subst hx0
        exact hf.metric_inner_zero _ _
    rw [hv_eq, hx0]
    exact four_mul_inner_fderiv_tipSphereAmbientMap_zero _ _
  · rw [hf.metric_inner_of_ne_zero hx0,
      htip ‖(x : V)‖ ⟨norm_nonneg _, mem_ball_zero_iff.1 x.2⟩]
    exact four_mul_inner_fderiv_tipSphereAmbientMap_of_ne_zero hx0 _ _

/-- On any open ball `Metric.ball (0 : V) r₀` where the profile satisfies `f(r) = 2 sin (r / 2)`,
the tip map `TauCeti.IsStandardCapProfile.tipSphereMap` is a local Riemannian isometry from the
restricted standard cap metric to the round sphere of radius `2`. -/
theorem isLocalRiemannianIsometry_tip {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
    {n : ℕ} [Fact (Module.finrank ℝ (WithLp 2 (V × ℝ)) = (n + 1) + 1)] {r₀ : ℝ}
    (htip : ∀ r ∈ Ico 0 r₀, f r = 2 * sin (r / 2)) :
    let B : Opens V := ⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩
    letI : RiemannianBundle (fun x : B ↦ TangentSpace 𝓘(ℝ, V) x) :=
      ⟨((hf.metric V).restrictOpenTangentSpace B).toRiemannianMetric⟩
    letI : RiemannianBundle (fun y : Metric.sphere (0 : WithLp 2 (V × ℝ)) 1 ↦
      TangentSpace (𝓡 (n + 1)) y) :=
      ⟨(sphereRoundMetricOfRadius (E := WithLp 2 (V × ℝ))
        (n := n + 1) 2 two_pos).toRiemannianMetric⟩
    IsLocalRiemannianIsometry 𝓘(ℝ, V) (𝓡 (n + 1)) (fun x : B ↦ tipSphereMap V (x : V)) := by
  let B : Opens V := ⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩
  let : RiemannianBundle (fun x : B ↦ TangentSpace 𝓘(ℝ, V) x) :=
    ⟨((hf.metric V).restrictOpenTangentSpace B).toRiemannianMetric⟩
  let : RiemannianBundle (fun y : Metric.sphere (0 : WithLp 2 (V × ℝ)) 1 ↦
    TangentSpace (𝓡 (n + 1)) y) :=
    ⟨(sphereRoundMetricOfRadius (E := WithLp 2 (V × ℝ)) (n := n + 1) 2 two_pos).toRiemannianMetric⟩
  have hB_smooth : ContMDiff 𝓘(ℝ, V) (𝓡 (n + 1)) ∞ (fun x : B ↦ tipSphereMap V (x : V)) :=
    (contDiff_tipSphereAmbientMap.contMDiff.codRestrict_sphere _).comp contMDiff_subtype_val
  have hinner (x : B) (v w : TangentSpace 𝓘(ℝ, V) x) :
      inner ℝ (mfderiv 𝓘(ℝ, V) (𝓡 (n + 1)) (fun z : B ↦ tipSphereMap V (z : V)) x v)
        (mfderiv 𝓘(ℝ, V) (𝓡 (n + 1)) (fun z : B ↦ tipSphereMap V (z : V)) x w) =
        inner ℝ v w :=
    hf.inner_mfderiv_tipSphereMap htip x v w
  refine ⟨hB_smooth, fun x ↦ ?_, hinner⟩
  -- Since the differential preserves positive-definite inner products, it is injective between
  -- finite-dimensional spaces of equal dimension `n + 1`, hence invertible.
  have hfinProd : FiniteDimensional ℝ (WithLp 2 (V × ℝ)) := .of_fact_finrank_eq_succ (n + 1)
  have hfinProd' : FiniteDimensional ℝ (V × ℝ) :=
    (WithLp.linearEquiv 2 ℝ (V × ℝ)).finiteDimensional
  have : FiniteDimensional ℝ V := FiniteDimensional.of_injective
    (LinearMap.inl ℝ V ℝ) fun _ _ h ↦ (Prod.mk.inj h).1
  have hfinV : Module.finrank ℝ V = n + 1 := by
    have h := Fact.out (p := Module.finrank ℝ (WithLp 2 (V × ℝ)) = (n + 1) + 1)
    rw [(WithLp.linearEquiv 2 ℝ (V × ℝ)).finrank_eq, Module.finrank_prod, Module.finrank_self] at h
    omega
  set L : TangentSpace 𝓘(ℝ, V) x →L[ℝ] TangentSpace (𝓡 (n + 1)) (tipSphereMap V x) :=
    mfderiv 𝓘(ℝ, V) (𝓡 (n + 1)) (fun z : B ↦ tipSphereMap V (z : V)) x
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    have hpos : 0 < inner ℝ v v := real_inner_self_pos.2 hv0
    have h0 : inner ℝ v v = 0 := by rw [← hinner x v v, hv, inner_zero_left]
    linarith
  have hfin : Module.finrank ℝ (TangentSpace 𝓘(ℝ, V) x) =
      Module.finrank ℝ (TangentSpace (𝓡 (n + 1)) (tipSphereMap V x)) := by
    change Module.finrank ℝ V = Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
    rw [hfinV, finrank_euclideanSpace_fin]
  have hbij : Function.Bijective L.toLinearMap :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj⟩
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv, rfl⟩

end Tip

end IsStandardCapProfile

/-! ### Obstruction at the origin when `f(0) ≠ 0` -/

section Obstruction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem continuousAt_inner_ray
    (g : ContinuousRiemannianMetric V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x)) (u v : V) :
    ContinuousAt (fun t : ℝ ↦
      g.inner (t • u) ((NormedSpace.fromTangentSpace (t • u)).symm v)
        ((NormedSpace.fromTangentSpace (t • u)).symm v)) 0 := by
  let : RiemannianBundle (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) :=
    Bundle.instIsContinuousRiemannianBundle g
  have hsec : Continuous (fun t : ℝ ↦
      TotalSpace.mk' V (E := fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) (t • u)
        ((NormedSpace.fromTangentSpace (t • u)).symm v)) := by
    rw [continuous_iff_continuousAt]
    intro t
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(continuous_id.smul continuous_const).continuousAt, ?_⟩
    have heq : (fun s : ℝ ↦
        (trivializationAt V (TangentSpace 𝓘(ℝ, V)) (t • u)
          ⟨s • u, (NormedSpace.fromTangentSpace (s • u)).symm v⟩).2) = fun _ ↦ v := by
      ext s
      simp [NormedSpace.fromTangentSpace_symm_apply (𝕜 := ℝ) (s • u) v]
    exact heq ▸ continuousAt_const
  exact (hsec.inner_bundle hsec).continuousAt

/-- If `f` is continuous at `0` with `f 0 ≠ 0` and `V` contains two orthogonal unit vectors, then
no continuous Riemannian metric on `V` can agree with `dr² + f(r)² g_(Sⁿ)` on tangential vectors
away from `0`. -/
theorem not_exists_continuousRiemannianMetric_of_apply_zero_ne_zero_of_exists_orth
    {f : ℝ → ℝ} (hf_cont : ContinuousAt f 0) (hf0 : f 0 ≠ 0)
    (horth : ∃ u v : V, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪u, v⟫_ℝ = 0) :
    ¬ ∃ g : ContinuousRiemannianMetric V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x),
        ∀ (x : V), x ≠ 0 → ∀ (v : V), ⟪x, v⟫_ℝ = 0 →
          g.inner x ((NormedSpace.fromTangentSpace x).symm v)
            ((NormedSpace.fromTangentSpace x).symm v) = (f ‖x‖ / ‖x‖) ^ 2 * ‖v‖ ^ 2 := by
  rintro ⟨g, hg⟩
  obtain ⟨u, v, hu, hv, huv⟩ := horth
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  let φ : ℝ → ℝ := fun t ↦
    g.inner (t • u) ((NormedSpace.fromTangentSpace (t • u)).symm v)
      ((NormedSpace.fromTangentSpace (t • u)).symm v)
  have hlim_fin : Tendsto φ (𝓝[>] 0) (𝓝 (φ 0)) :=
    (continuousAt_inner_ray g u v).tendsto.mono_left nhdsWithin_le_nhds
  have hev : φ =ᶠ[𝓝[>] 0] fun t : ℝ ↦ f t ^ 2 / t ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htu : t • u ≠ 0 := smul_ne_zero (ne_of_gt ht) hu0
    have hnorm : ‖t • u‖ = t := by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg ht.le]
    have horth' : ⟪t • u, v⟫_ℝ = 0 := by rw [real_inner_smul_left, huv, mul_zero]
    dsimp only [φ]
    rw [hg (t • u) htu v horth', hnorm, hv, one_pow, mul_one, div_pow]
  have hlim_top : Tendsto φ (𝓝[>] 0) atTop := by
    refine Filter.Tendsto.congr' hev.symm ?_
    have hnum : Tendsto (fun t : ℝ ↦ f t ^ 2) (𝓝[>] 0) (𝓝 (f 0 ^ 2)) :=
      (hf_cont.pow 2).tendsto.mono_left nhdsWithin_le_nhds
    have hden : Tendsto (fun t : ℝ ↦ t ^ 2) (𝓝[>] 0) (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_pow 2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.trans
          (by simp))
        (by filter_upwards [self_mem_nhdsWithin] with t ht using sq_pos_of_pos ht)
    exact Filter.Tendsto.pos_mul_atTop (sq_pos_of_ne_zero hf0) hnum
      (tendsto_inv_nhdsGT_zero.comp hden)
  exact not_tendsto_nhds_of_tendsto_atTop hlim_top (φ 0) hlim_fin

/-- In dimension at least `2`, if `f` is continuous at `0` with `f 0 ≠ 0`, then no continuous
Riemannian metric on `V` can agree with `dr² + f(r)² g_(Sⁿ)` on tangential vectors away from `0`. -/
theorem not_exists_continuousRiemannianMetric_of_apply_zero_ne_zero
    (hdim : 2 ≤ Module.finrank ℝ V)
    {f : ℝ → ℝ} (hf_cont : ContinuousAt f 0) (hf0 : f 0 ≠ 0) :
    ¬ ∃ g : ContinuousRiemannianMetric V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x),
        ∀ (x : V), x ≠ 0 → ∀ (v : V), ⟪x, v⟫_ℝ = 0 →
          g.inner x ((NormedSpace.fromTangentSpace x).symm v)
            ((NormedSpace.fromTangentSpace x).symm v) = (f ‖x‖ / ‖x‖) ^ 2 * ‖v‖ ^ 2 := by
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by omega)
  let b := stdOrthonormalBasis ℝ V
  have h0 : 0 < Module.finrank ℝ V := by omega
  have h1 : 1 < Module.finrank ℝ V := by omega
  refine not_exists_continuousRiemannianMetric_of_apply_zero_ne_zero_of_exists_orth hf_cont hf0
    ⟨b ⟨0, h0⟩, b ⟨1, h1⟩, b.orthonormal.1 _, b.orthonormal.1 _, ?_⟩
  exact b.orthonormal.2 (by simp [Fin.ext_iff])

end Obstruction

end TauCeti
