/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.HopfRinow
public import TauCeti.Geometry.RicciFlow.StandardCap.Metric

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Metric and geodesic completeness of the standard cap

This file establishes exact radial distance bounds, properness, metric completeness, and geodesic
completeness for the smooth standard cap metric `TauCeti.IsStandardCapProfile.metric` on any
finite-dimensional real inner product space `V`, equipped with its Riemannian metric-space
structure `TauCeti.MetricSpace.ofRiemannianMetric`.

Because `0 < f(r) ≤ r` for `r > 0`, the standard cap metric satisfies
`(⟪x, v⟫ / ‖x‖)² ≤ g_x(v, v) ≤ ‖v‖²` everywhere. The upper bound makes the tautological map
`V → WithMetric (hf.metric V)` 1-Lipschitz; the lower bound makes the smooth regularizations
`p ↦ √(‖p‖² + ε²)` 1-Lipschitz for every `ε > 0`, and letting `ε → 0⁺` shows that `x ↦ ‖x‖` is
1-Lipschitz for the Riemannian distance. Consequently:

* the Riemannian distance from the tip `0` to `x` equals `‖x‖`;
* closed Riemannian balls are contained in Euclidean closed balls, hence are compact
  (`ProperSpace`);
* the standard cap is metrically complete (`CompleteSpace`) and geodesically complete
  (`IsGeodesicallyCompleteAt`) by the Hopf–Rinow theorem.

## Main results

In the namespace `TauCeti.IsStandardCapProfile`:

* `lipschitzWith_toWithMetric_metric`: the identification `V → WithMetric (hf.metric V)` is
  1-Lipschitz.
* `abs_norm_sub_norm_le_dist_metric`: `|‖x‖ - ‖y‖| ≤ dist x y` for the standard cap metric.
* `dist_metric_zero`: the Riemannian distance from the origin `0` to `x` equals `‖x‖`.
* `properSpace_withMetric_metric`: closed balls of `(V, hf.metric V)` are compact.
* `completeSpace_withMetric_metric`: `(V, hf.metric V)` is a complete metric space.
* `isGeodesicallyCompleteAt_withMetric_metric`: every maximal geodesic of `(V, hf.metric V)` is
  defined for all time.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics Monographs 3
  (2007), Definition 12.1.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2 (Hopf–Rinow theorem).
-/

public noncomputable section

open Bundle Filter Metric Real Set
open TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold NNReal Topology

namespace TauCeti.IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

include hf

/-- The map `V → WithMetric (hf.metric V)` is 1-Lipschitz: the standard cap metric is bounded above
by the Euclidean inner product everywhere on `V`. -/
theorem lipschitzWith_toWithMetric_metric :
    letI : MetricSpace (WithMetric (hf.metric V)) :=
      TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
    LipschitzWith 1 (WithMetric.toWithMetric (hf.metric V)) := by
  let _ : MetricSpace (WithMetric (hf.metric V)) :=
    TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  refine IsRiemannianManifold.lipschitzWith_of_norm_mfderiv_le (I := 𝓘(ℝ, V)) (J := 𝓘(ℝ, V))
    (WithMetric.contMDiff_toWithMetric (k := 1)) one_ne_zero fun x v ↦ ?_
  rw [NNReal.coe_one, one_mul]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq v, WithMetric.inner_def, WithMetric.ofWithMetric_toWithMetric,
    WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric]
  exact (hf.metric_inner_self_le x v).trans_eq (real_inner_self_eq_norm_sq _).symm

omit hf [FiniteDimensional ℝ V] in
private theorem hasFDerivAt_sqrt_norm_sq_add {ε : ℝ} (hε : 0 < ε) (z : V) :
    HasFDerivAt (fun x : V ↦ √(‖x‖ ^ 2 + ε ^ 2))
      ((√(‖z‖ ^ 2 + ε ^ 2))⁻¹ • innerSL ℝ z) z := by
  have hsq : HasFDerivAt (fun x : V ↦ ‖x‖ ^ 2 + ε ^ 2) (2 • innerSL ℝ z) z := by
    have h1 : (fun x : V ↦ ‖x‖ ^ 2 + ε ^ 2) = fun x : V ↦ ⟪x, x⟫_ℝ + ε ^ 2 :=
      funext fun x ↦ by rw [real_inner_self_eq_norm_sq]
    rw [h1]
    refine (((hasFDerivAt_id z).inner ℝ (hasFDerivAt_id z)).add_const (ε ^ 2)).congr_fderiv ?_
    ext w
    simp [two_mul, real_inner_comm]
  have hpos : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  have hsqrt_ne : √(‖z‖ ^ 2 + ε ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  refine ((Real.hasDerivAt_sqrt hpos.ne').comp_hasFDerivAt z hsq).congr_fderiv ?_
  ext w
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  field_simp

private theorem lipschitzWith_sqrt_norm_sq_add {ε : ℝ} (hε : 0 < ε) :
    letI : MetricSpace (WithMetric (hf.metric V)) :=
      TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
    LipschitzWith 1 (fun p : WithMetric (hf.metric V) ↦ √(‖p.ofWithMetric‖ ^ 2 + ε ^ 2)) := by
  let _ : MetricSpace (WithMetric (hf.metric V)) :=
    TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  let φ : WithMetric (hf.metric V) → ℝ := fun p ↦ √(‖p.ofWithMetric‖ ^ 2 + ε ^ 2)
  have hφ_smooth : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ) 1 φ :=
    (((contDiff_norm_sq ℝ).add contDiff_const).sqrt fun z ↦ by positivity).contMDiff.comp
      (WithMetric.contMDiff_ofWithMetric (k := 1))
  refine IsRiemannianManifold.lipschitzWith_of_norm_mfderiv_le (I := 𝓘(ℝ, V)) (J := 𝓘(ℝ))
    hφ_smooth one_ne_zero fun p v ↦ ?_
  rw [NNReal.coe_one, one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have hmf : NormedSpace.fromTangentSpace (φ p) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ) φ p v) =
      (√(‖p.ofWithMetric‖ ^ 2 + ε ^ 2))⁻¹ *
        ⟪p.ofWithMetric, NormedSpace.fromTangentSpace p.ofWithMetric
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v)⟫_ℝ := by
    change mfderiv 𝓘(ℝ, V) 𝓘(ℝ)
        ((fun z : V ↦ √(‖z‖ ^ 2 + ε ^ 2)) ∘ WithMetric.ofWithMetric) p v = _
    rw [WithMetric.mfderiv_comp_ofWithMetric, ContinuousLinearMap.comp_apply,
      (hasFDerivAt_sqrt_norm_sq_add hε p.ofWithMetric).hasMFDerivAt.mfderiv]
    rfl
  have hnorm_sq : ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ) φ p v‖ ^ 2 =
      ((√(‖p.ofWithMetric‖ ^ 2 + ε ^ 2))⁻¹ *
        ⟪p.ofWithMetric, NormedSpace.fromTangentSpace p.ofWithMetric
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v)⟫_ℝ) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    have hinner : ⟪mfderiv 𝓘(ℝ, V) 𝓘(ℝ) φ p v, mfderiv 𝓘(ℝ, V) 𝓘(ℝ) φ p v⟫_ℝ =
        ⟪NormedSpace.fromTangentSpace (φ p) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ) φ p v),
          NormedSpace.fromTangentSpace (φ p) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ) φ p v)⟫_ℝ := rfl
    rw [hinner, hmf, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [hnorm_sq, ← real_inner_self_eq_norm_sq v, WithMetric.inner_def]
  set z : V := p.ofWithMetric
  set u : TangentSpace 𝓘(ℝ, V) z := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v
  have hpos : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  have hlhs : ((√(‖z‖ ^ 2 + ε ^ 2))⁻¹ * ⟪z, NormedSpace.fromTangentSpace z u⟫_ℝ) ^ 2 =
      ⟪z, NormedSpace.fromTangentSpace z u⟫_ℝ ^ 2 / (‖z‖ ^ 2 + ε ^ 2) := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hpos.le, inv_mul_eq_div]
  rw [hlhs]
  rcases eq_or_ne z 0 with hz | hz
  · have h0 : ⟪z, NormedSpace.fromTangentSpace z u⟫_ℝ ^ 2 / (‖z‖ ^ 2 + ε ^ 2) = 0 := by
      simp [hz]
    rw [h0, ← WithMetric.inner_def, real_inner_self_eq_norm_sq]
    exact sq_nonneg _
  · exact (div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos (norm_pos_iff.2 hz) 2)
      (by nlinarith)).trans (hf.radial_sq_div_norm_sq_le_metric_inner_self hz u)

/-- The radial coordinate `x ↦ ‖x‖` is 1-Lipschitz with respect to the Riemannian distance of the
standard cap metric. -/
theorem abs_norm_sub_norm_le_dist_metric (x y : V) :
    letI : MetricSpace (WithMetric (hf.metric V)) :=
      TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
    |‖x‖ - ‖y‖| ≤
      dist (WithMetric.toWithMetric (hf.metric V) x)
        (WithMetric.toWithMetric (hf.metric V) y) := by
  let _ : MetricSpace (WithMetric (hf.metric V)) :=
    TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  have hbound : ∀ ε : ℝ, 0 < ε →
      |√(‖x‖ ^ 2 + ε ^ 2) - √(‖y‖ ^ 2 + ε ^ 2)| ≤
        dist (WithMetric.toWithMetric (hf.metric V) x)
          (WithMetric.toWithMetric (hf.metric V) y) := fun ε hε ↦ by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, WithMetric.ofWithMetric_toWithMetric] using
      (hf.lipschitzWith_sqrt_norm_sq_add hε).dist_le_mul
        (WithMetric.toWithMetric (hf.metric V) x) (WithMetric.toWithMetric (hf.metric V) y)
  have htend : Tendsto (fun ε : ℝ ↦ |√(‖x‖ ^ 2 + ε ^ 2) - √(‖y‖ ^ 2 + ε ^ 2)|)
      (𝓝[>] (0 : ℝ)) (𝓝 |‖x‖ - ‖y‖|) := by
    have hcont : Continuous fun ε : ℝ ↦ |√(‖x‖ ^ 2 + ε ^ 2) - √(‖y‖ ^ 2 + ε ^ 2)| := by
      fun_prop
    have h0 : |√(‖x‖ ^ 2 + (0 : ℝ) ^ 2) - √(‖y‖ ^ 2 + (0 : ℝ) ^ 2)| = |‖x‖ - ‖y‖| := by
      simp [Real.sqrt_sq (norm_nonneg _)]
    rw [← h0]
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto htend (eventually_nhdsWithin_of_forall hbound)

/-- The Riemannian distance from the origin `0 ∈ V` to any point `x ∈ V` under the standard cap
metric equals the radial coordinate `‖x‖`. -/
@[simp]
theorem dist_metric_zero (x : V) :
    letI : MetricSpace (WithMetric (hf.metric V)) :=
      TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
    dist (WithMetric.toWithMetric (hf.metric V) (0 : V))
      (WithMetric.toWithMetric (hf.metric V) x) = ‖x‖ := by
  let _ : MetricSpace (WithMetric (hf.metric V)) :=
    TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  refine le_antisymm ?_ ?_
  · simpa using hf.lipschitzWith_toWithMetric_metric.dist_le_mul (0 : V) x
  · simpa [norm_zero, abs_of_nonneg (norm_nonneg x)] using
      hf.abs_norm_sub_norm_le_dist_metric (0 : V) x

/-- Closed Riemannian balls of the smooth standard cap are compact. -/
theorem properSpace_withMetric_metric :
    letI : MetricSpace (WithMetric (hf.metric V)) :=
      TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
    ProperSpace (WithMetric (hf.metric V)) := by
  let _ : MetricSpace (WithMetric (hf.metric V)) :=
    TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  refine ⟨fun p r ↦ ?_⟩
  have hsub : Metric.closedBall p r ⊆
      WithMetric.toWithMetric (hf.metric V) ''
        Metric.closedBall (0 : V) (‖p.ofWithMetric‖ + r) := by
    intro q hq
    refine ⟨q.ofWithMetric, ?_, WithMetric.toWithMetric_ofWithMetric _ q⟩
    have hdist : |‖q.ofWithMetric‖ - ‖p.ofWithMetric‖| ≤ dist q p := by
      simpa using hf.abs_norm_sub_norm_le_dist_metric q.ofWithMetric p.ofWithMetric
    rw [Metric.mem_closedBall, dist_zero_right]
    have hqp : dist q p ≤ r := Metric.mem_closedBall.1 hq
    linarith [(le_abs_self (‖q.ofWithMetric‖ - ‖p.ofWithMetric‖)).trans (hdist.trans hqp)]
  exact ((isCompact_closedBall (0 : V) (‖p.ofWithMetric‖ + r)).image
    WithMetric.continuous_toWithMetric).of_isClosed_subset Metric.isClosed_closedBall hsub

/-- The smooth standard cap is a complete metric space for its Riemannian distance. -/
theorem completeSpace_withMetric_metric :
    letI : MetricSpace (WithMetric (hf.metric V)) :=
      TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
    CompleteSpace (WithMetric (hf.metric V)) := by
  let _ : MetricSpace (WithMetric (hf.metric V)) :=
    TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  have : ProperSpace (WithMetric (hf.metric V)) := hf.properSpace_withMetric_metric
  exact complete_of_proper

/-- Every maximal geodesic of the smooth standard cap is defined for all time. -/
theorem isGeodesicallyCompleteAt_withMetric_metric (p : WithMetric (hf.metric V)) :
    IsGeodesicallyCompleteAt 𝓘(ℝ, V) (WithMetric (hf.metric V)) p := by
  let _ : MetricSpace (WithMetric (hf.metric V)) :=
    TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  have : CompleteSpace (WithMetric (hf.metric V)) := hf.completeSpace_withMetric_metric
  exact isGeodesicallyCompleteAt_of_completeSpace p

end TauCeti.IsStandardCapProfile
