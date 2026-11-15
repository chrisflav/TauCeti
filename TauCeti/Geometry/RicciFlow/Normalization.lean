/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Geometry.Manifold.Riemannian.AverageScalarCurvature
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.IntervalIntegral.Inverse
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Geometry.Manifold.Riemannian.Scaling
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.IntegralVariation
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Rescale

/-!
# Scaling and volume normalization of the Ricci flow

On a closed smooth manifold `M` of real dimension `n`, Hamilton's unnormalized Ricci flow is
`∂_t g = -2 Ric(g)`, while the volume-normalized Ricci flow is

`∂_τ ĝ = -2 Ric(ĝ) + (2 / n) r(ĝ) ĝ`,

where `r(g) = Vol(g)⁻¹ ∫ Scal(g) dV_g` is the average scalar curvature
(`Bundle.ContMDiffRiemannianMetric.averageScalarCurvature`). Along an unnormalized flow, total
volume evolves by `∂_t Vol(g_t) = -r(g_t) Vol(g_t)`, whereas along a volume-normalized flow total
volume has zero time derivative and is therefore constant on every preconnected time set.

Following Hamilton (1982) and Topping (§1.2.3), the two equations are related by the spatial scale
`a(t) = (Vol(g(t₀)) / Vol(g(t))) ^ (2 / n)` (`TauCeti.ricciFlowVolumeScale`) and the accumulated
normalized time `τ(t) = ∫_{t₀}^t a(r) dr`:

* If `g` solves the unnormalized equation and `ψ` reparametrizes time with `ψ'(σ) = a(ψ(σ))⁻¹`,
  then `ĝ(σ) = a(ψ(σ)) g(ψ(σ))` has constant total volume `Vol(g(t₀))` and solves the
  volume-normalized equation
  (`TauCeti.IsRicciFlowEquationOn.isVolumeNormalizedRicciFlowEquationOn_rescale_comp`), giving
  existence of the normalized flow on `[0, ∫_{t₀}^{t₁} a(r) dr]` from `[t₀, t₁]` and on the image
  of `[t₀, T)` (which equals `[0, ∞)` whenever `τ(t) → ∞` as `t ↑ T`).
* Conversely, given a solution `ĝ` of the volume-normalized equation on `[σ₀, σ₁]`, setting
  `c(σ) = exp(-(2 / n) ∫_{σ₀}^σ r(ĝ(u)) du)` and inverting `t(σ) = ∫_{σ₀}^σ c(u) du` recovers a
  solution `g(t) = c(φ(t)) ĝ(φ(t))` of the unnormalized equation on `[0, ∫_{σ₀}^{σ₁} c(u) du]`.

Both equations are invariant under time translation and under parabolic rescaling `τ ↦ c g(τ / c)`
(`c > 0`). Every Einstein metric `Ric(g₀) = c g₀` gives a stationary solution of the
volume-normalized equation; for the shrinking Einstein family `g(t) = (1 - 2 c t) g₀` (`c > 0`),
`a(t) = (1 - 2 c t)⁻¹`, rescaling by `a(t)` recovers `g₀`, and normalized time
`∫_0^t (1 - 2 c r)⁻¹ dr = -(2 c)⁻¹ log(1 - 2 c t)` tends to `+∞` as `t ↑ (2 c)⁻¹`.

## Main definitions

* `TauCeti.IsRicciFlowEquationOn`: pointwise evolution equation `∂_t g = -2 Ric(g)` within a time
  set `s`.
* `TauCeti.IsVolumeNormalizedRicciFlowEquationOn`: pointwise volume-normalized evolution equation
  `∂_τ g = -2 Ric(g) + (2 / n) r(g) g` within `s`.
* `TauCeti.ricciFlowVolumeScale`: spatial scale `(Vol(g t₀) / Vol(g t)) ^ (2 / n)` normalizing
  `Vol(a(t) g(t))` to `Vol(g t₀)`.

## Main results

* `TauCeti.IsRicciFlowEquationOn.rescale_comp_div`,
  `TauCeti.IsVolumeNormalizedRicciFlowEquationOn.rescale_comp_div`: parabolic scaling symmetry
  `τ ↦ c g(τ / c)` of both equations.
* `TauCeti.IsRicciFlowEquationOn.hasDerivWithinAt_riemannianTotalVolume`:
  `∂_t Vol(g_t) = -r(g_t) Vol(g_t)`.
* `TauCeti.IsVolumeNormalizedRicciFlowEquationOn.hasDerivWithinAt_riemannianTotalVolume`,
  `TauCeti.IsVolumeNormalizedRicciFlowEquationOn.riemannianTotalVolume_eq`: conservation of total
  volume along volume-normalized Ricci flow.
* `TauCeti.IsRicciFlowEquationOn.exists_isVolumeNormalizedRicciFlowEquationOn_Icc`,
  `TauCeti.IsRicciFlowEquationOn.exists_isVolumeNormalizedRicciFlowEquationOn_Ico`,
  `TauCeti.IsVolumeNormalizedRicciFlowEquationOn.exists_isRicciFlowEquationOn_Icc`: equivalence
  between unnormalized and volume-normalized Ricci flows on compact and half-open time intervals.
* `TauCeti.isVolumeNormalizedRicciFlowEquationOn_const_of_ricciTensor_eq_smul_inner`,
  `TauCeti.ricciFlowVolumeScale_of_eq_rescale_one_sub_two_mul`,
  `TauCeti.intervalIntegral_inv_one_sub_two_mul`,
  `TauCeti.tendsto_intervalIntegral_inv_one_sub_two_mul_atTop`: Einstein stationary and shrinking
  normalization formulas.

## References

* R. S. Hamilton, *Three-manifolds with positive Ricci curvature*, J. Differential Geom. 17 (1982),
  255–306, Section 3.
* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Sections 1.2.1–1.2.3.
-/

public section

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti

section RescaleContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open scoped TauCeti.MetricC2 in
/-- Constant rescaling of a `C^2`-continuous family of smooth metrics on `s` by a continuous
positive scale function remains `C^2`-continuous on `s`. -/
theorem continuousOn_rescale_const_chartC2 {P : Type*} [TopologicalSpace P] {s : Set P}
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {c : P → ℝ} (hc : ∀ p, 0 < c p) (hg : ContinuousOn g s) (hc_cont : ContinuousOn c s) :
    ContinuousOn (fun p ↦ (g p).rescale (fun _ ↦ c p) contMDiff_const (fun _ ↦ hc p)) s := by
  rw [continuousOn_iff_continuous_domRestrict] at hg hc_cont ⊢
  exact ContMDiffRiemannianMetric.continuous_rescale_const_chartCk 2 (fun p : s ↦ hc p) hg hc_cont

end RescaleContinuity

section Equations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A family of smooth Riemannian metrics `g` satisfies the **unnormalized Ricci-flow equation**
`∂_t g = -2 Ric(g)` within `s` if at every `t ∈ s`, `x : M`, and `v, w ∈ T_x M`, the scalar inner
product `τ ↦ (g τ).inner x v w` has derivative `-2 Ric(g_t)_x(v, w)` within `s` at `t`. -/
def IsRicciFlowEquationOn
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ (x : M) (v w : TangentSpace I x),
    HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s t

/-- Unfolds `TauCeti.IsRicciFlowEquationOn`. -/
theorem isRicciFlowEquationOn_def
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ} :
    IsRicciFlowEquationOn g s ↔
      ∀ t ∈ s, ∀ (x : M) (v w : TangentSpace I x),
        HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
          (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
              ⟨(g t).toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s t :=
  Iff.rfl

/-- Restricting the time set preserves `IsRicciFlowEquationOn`. -/
theorem IsRicciFlowEquationOn.mono
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s s' : Set ℝ}
    (hg : IsRicciFlowEquationOn g s) (h : s' ⊆ s) :
    IsRicciFlowEquationOn g s' :=
  fun t ht x v w ↦ (hg t (h ht) x v w).mono h

/-- `IsRicciFlowEquationOn` depends only on the values of the metric family on `s`. -/
theorem IsRicciFlowEquationOn.congr_of_mem
    {g₁ g₂ : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (h : ∀ t ∈ s, g₁ t = g₂ t) (hg₁ : IsRicciFlowEquationOn g₁ s) :
    IsRicciFlowEquationOn g₂ s := by
  intro t ht x v w
  have hD := congrArg
    (fun γ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      -2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨γ.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w))
    (h t ht)
  exact ((hg₁ t ht x v w).congr (fun τ hτ ↦ by rw [h τ hτ]) (by rw [h t ht])).congr_deriv hD

/-- Two metric families agreeing on `s` satisfy `IsRicciFlowEquationOn` on `s` simultaneously. -/
theorem isRicciFlowEquationOn_congr
    {g₁ g₂ : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (h : ∀ t ∈ s, g₁ t = g₂ t) :
    IsRicciFlowEquationOn g₁ s ↔ IsRicciFlowEquationOn g₂ s :=
  ⟨IsRicciFlowEquationOn.congr_of_mem h,
    IsRicciFlowEquationOn.congr_of_mem fun t ht ↦ (h t ht).symm⟩

/-- **Time translation of Ricci flow.** Shifting time by `t₀` maps solutions on `s` to solutions on
`(· + t₀) ⁻¹' s`. -/
theorem IsRicciFlowEquationOn.comp_add_right
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (hg : IsRicciFlowEquationOn g s) (t₀ : ℝ) :
    IsRicciFlowEquationOn (fun τ ↦ g (τ + t₀)) ((· + t₀) ⁻¹' s) := by
  intro t ht x v w
  have hd : HasDerivWithinAt (fun τ ↦ τ + t₀) 1 ((· + t₀) ⁻¹' s) t :=
    (hasDerivWithinAt_id t _).add_const t₀
  exact ((hg (t + t₀) ht x v w).comp t hd (mapsTo_preimage _ _)).congr_deriv (mul_one _)

/-- **Parabolic scaling of Ricci flow.** For `c > 0`, if `g` satisfies `∂_t g = -2 Ric(g)` on `s`,
then `τ ↦ c g(τ / c)` satisfies `∂_τ g = -2 Ric(g)` on `(· / c) ⁻¹' s`. -/
theorem IsRicciFlowEquationOn.rescale_comp_div
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (hg : IsRicciFlowEquationOn g s) {c : ℝ} (hc : 0 < c) :
    IsRicciFlowEquationOn
      (fun τ ↦ (g (τ / c)).rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc))
      ((· / c) ⁻¹' s) := by
  intro t ht x v w
  have hd : HasDerivWithinAt (fun τ ↦ τ / c) c⁻¹ ((· / c) ⁻¹' s) t :=
    ((hasDerivWithinAt_id t ((· / c) ⁻¹' s)).div_const c).congr_deriv (one_div c)
  have hcomp := ((hg (t / c) ht x v w).comp t hd (mapsTo_preimage _ _)).const_mul c
  simp only [ContMDiffRiemannianMetric.rescale_inner,
    (g (t / c)).ricciTensor_leviCivitaConnection_rescale_const hc x]
  refine hcomp.congr_deriv ?_
  have hc0 : c ≠ 0 := hc.ne'
  field_simp

end Equations

section NormalizedEquations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A family of smooth Riemannian metrics `g` on a compact manifold satisfies the
**volume-normalized Ricci-flow equation** `∂_τ g = -2 Ric(g) + (2 / n) r(g) g` within `s` if at
every `t ∈ s`, `x : M`, and `v, w ∈ T_x M`, `τ ↦ (g τ).inner x v w` has derivative
`-2 Ric(g_t)_x(v, w) + (2 / n) r(g_t) (g_t)_x(v, w)` within `s` at `t`. -/
def IsVolumeNormalizedRicciFlowEquationOn
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ (x : M) (v w : TangentSpace I x),
    HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w) +
        2 / (Module.finrank ℝ E : ℝ) * (g t).averageScalarCurvature * (g t).inner x v w) s t

/-- Unfolds `TauCeti.IsVolumeNormalizedRicciFlowEquationOn`. -/
theorem isVolumeNormalizedRicciFlowEquationOn_def
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ} :
    IsVolumeNormalizedRicciFlowEquationOn g s ↔
      ∀ t ∈ s, ∀ (x : M) (v w : TangentSpace I x),
        HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
          (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
              ⟨(g t).toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w) +
            2 / (Module.finrank ℝ E : ℝ) * (g t).averageScalarCurvature *
              (g t).inner x v w) s t :=
  Iff.rfl

/-- Restricting the time set preserves `IsVolumeNormalizedRicciFlowEquationOn`. -/
theorem IsVolumeNormalizedRicciFlowEquationOn.mono
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s s' : Set ℝ}
    (hg : IsVolumeNormalizedRicciFlowEquationOn g s) (h : s' ⊆ s) :
    IsVolumeNormalizedRicciFlowEquationOn g s' :=
  fun t ht x v w ↦ (hg t (h ht) x v w).mono h

/-- `IsVolumeNormalizedRicciFlowEquationOn` depends only on the values of the family on `s`. -/
theorem IsVolumeNormalizedRicciFlowEquationOn.congr_of_mem
    {g₁ g₂ : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (h : ∀ t ∈ s, g₁ t = g₂ t) (hg₁ : IsVolumeNormalizedRicciFlowEquationOn g₁ s) :
    IsVolumeNormalizedRicciFlowEquationOn g₂ s := by
  intro t ht x v w
  have hD := congrArg
    (fun γ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      -2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨γ.toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w) +
        2 / (Module.finrank ℝ E : ℝ) * γ.averageScalarCurvature * γ.inner x v w)
    (h t ht)
  exact ((hg₁ t ht x v w).congr (fun τ hτ ↦ by rw [h τ hτ]) (by rw [h t ht])).congr_deriv hD

/-- Two families agreeing on `s` satisfy `IsVolumeNormalizedRicciFlowEquationOn` simultaneously. -/
theorem isVolumeNormalizedRicciFlowEquationOn_congr
    {g₁ g₂ : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (h : ∀ t ∈ s, g₁ t = g₂ t) :
    IsVolumeNormalizedRicciFlowEquationOn g₁ s ↔ IsVolumeNormalizedRicciFlowEquationOn g₂ s :=
  ⟨IsVolumeNormalizedRicciFlowEquationOn.congr_of_mem h,
    IsVolumeNormalizedRicciFlowEquationOn.congr_of_mem fun t ht ↦ (h t ht).symm⟩

/-- **Time translation of volume-normalized Ricci flow.** -/
theorem IsVolumeNormalizedRicciFlowEquationOn.comp_add_right
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (hg : IsVolumeNormalizedRicciFlowEquationOn g s) (t₀ : ℝ) :
    IsVolumeNormalizedRicciFlowEquationOn (fun τ ↦ g (τ + t₀)) ((· + t₀) ⁻¹' s) := by
  intro t ht x v w
  have hd : HasDerivWithinAt (fun τ ↦ τ + t₀) 1 ((· + t₀) ⁻¹' s) t :=
    (hasDerivWithinAt_id t _).add_const t₀
  exact ((hg (t + t₀) ht x v w).comp t hd (mapsTo_preimage _ _)).congr_deriv (mul_one _)

/-- **Parabolic scaling of volume-normalized Ricci flow.** Because `r(c g) = c⁻¹ r(g)` while `c g`
scales by `c`, the nonlocal drift `(2 / n) r(g) g` is scale-invariant just like `-2 Ric(g)`, so
`τ ↦ c g(τ / c)` (`c > 0`) preserves `IsVolumeNormalizedRicciFlowEquationOn`. -/
theorem IsVolumeNormalizedRicciFlowEquationOn.rescale_comp_div
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (hg : IsVolumeNormalizedRicciFlowEquationOn g s) {c : ℝ} (hc : 0 < c) :
    IsVolumeNormalizedRicciFlowEquationOn
      (fun τ ↦ (g (τ / c)).rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc))
      ((· / c) ⁻¹' s) := by
  intro t ht x v w
  have hd : HasDerivWithinAt (fun τ ↦ τ / c) c⁻¹ ((· / c) ⁻¹' s) t :=
    ((hasDerivWithinAt_id t ((· / c) ⁻¹' s)).div_const c).congr_deriv (one_div c)
  have hcomp := ((hg (t / c) ht x v w).comp t hd (mapsTo_preimage _ _)).const_mul c
  simp only [ContMDiffRiemannianMetric.rescale_inner,
    (g (t / c)).ricciTensor_leviCivitaConnection_rescale_const hc x,
    ContMDiffRiemannianMetric.averageScalarCurvature_rescale_const _ hc]
  refine hcomp.congr_deriv ?_
  have hc0 : c ≠ 0 := hc.ne'
  field_simp

/-- **Einstein metrics are stationary for the volume-normalized Ricci flow.** If `Ric(g₀) = c g₀`
everywhere on a compact manifold `M`, then the constant family `fun _ ↦ g₀` solves the
volume-normalized Ricci-flow equation on every time set `s`. -/
theorem isVolumeNormalizedRicciFlowEquationOn_const_of_ricciTensor_eq_smul_inner
    (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {c : ℝ}
    (hRic : ∀ x,
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x =
          c • innerₗ (TangentSpace I x)))
    (s : Set ℝ) :
    IsVolumeNormalizedRicciFlowEquationOn (fun _ ↦ g₀) s := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact fun _ _ x ↦ hM.elim x
  · intro t _ x v w
    have h0 :
        -2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w) +
          2 / (Module.finrank ℝ E : ℝ) * g₀.averageScalarCurvature * g₀.inner x v w = 0 := by
      by_cases hE : Module.finrank ℝ E = 0
      · have hsubE : Subsingleton E := Module.finrank_zero_iff.1 hE
        have hsub : Subsingleton (TangentSpace I x) := hsubE
        rw [hsub.elim v 0]
        simp
      · have hE' : (Module.finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hE
        have hR : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨g₀.toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w) =
            c * g₀.inner x v w := by
          let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
          simp [hRic x, innerₗ_apply_apply, ContMDiffRiemannianMetric.inner_riemannianBundle]
        rw [hR, g₀.averageScalarCurvature_eq_of_ricciTensor_eq_smul_inner hRic]
        field_simp
        ring
    rw [h0]
    exact hasDerivWithinAt_const t s (g₀.inner x v w)

/-- **Recovering an unnormalized Ricci flow from a volume-normalized flow by rescaling and time
change.** If `ĝ` satisfies `IsVolumeNormalizedRicciFlowEquationOn ĝ s`, `c > 0` satisfies
`c'(σ) = -(2 / n) r(ĝ_σ) c(σ)` within `s`, and `φ` maps `J` into `s` with derivative
`(c (φ t))⁻¹` within `J`, then `g(t) = c(φ t) ĝ(φ t)` satisfies `IsRicciFlowEquationOn g J`. -/
theorem IsVolumeNormalizedRicciFlowEquationOn.isRicciFlowEquationOn_rescale_comp
    {ĝ : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s J : Set ℝ}
    (hĝ : IsVolumeNormalizedRicciFlowEquationOn ĝ s)
    {c : ℝ → ℝ} (hc_pos : ∀ σ, 0 < c σ)
    (hc_deriv : ∀ σ ∈ s, HasDerivWithinAt c
      (-(2 / (Module.finrank ℝ E : ℝ)) * (ĝ σ).averageScalarCurvature * c σ) s σ)
    {φ : ℝ → ℝ} (hmaps : MapsTo φ J s)
    (hφ : ∀ t ∈ J, HasDerivWithinAt φ (c (φ t))⁻¹ J t) :
    IsRicciFlowEquationOn
      (fun t ↦ (ĝ (φ t)).rescale (fun _ ↦ c (φ t)) contMDiff_const (fun _ ↦ hc_pos (φ t))) J := by
  intro t ht x v w
  have hσ : φ t ∈ s := hmaps ht
  have hc0 : c (φ t) ≠ 0 := (hc_pos (φ t)).ne'
  have hc_comp : HasDerivWithinAt (fun r ↦ c (φ r))
      (-(2 / (Module.finrank ℝ E : ℝ)) * (ĝ (φ t)).averageScalarCurvature) J t :=
    ((hc_deriv (φ t) hσ).comp t (hφ t ht) hmaps).congr_deriv (by field_simp)
  have hĝ_comp : HasDerivWithinAt (fun r ↦ (ĝ (φ r)).inner x v w)
      ((-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
              ⟨(ĝ (φ t)).toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w) +
          2 / (Module.finrank ℝ E : ℝ) * (ĝ (φ t)).averageScalarCurvature *
            (ĝ (φ t)).inner x v w) * (c (φ t))⁻¹) J t :=
    (hĝ (φ t) hσ x v w).comp t (hφ t ht) hmaps
  simp only [ContMDiffRiemannianMetric.rescale_inner,
    (ĝ (φ t)).ricciTensor_leviCivitaConnection_rescale_const (hc_pos (φ t)) x]
  exact (hc_comp.fun_mul hĝ_comp).congr_deriv (by field_simp; ring)

end NormalizedEquations

section VolumeScale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- In dimension zero, all smooth Riemannian metrics on `M` coincide. -/
private theorem contMDiffRiemannianMetric_eq_of_finrank_eq_zero
    (hE : Module.finrank ℝ E = 0)
    (g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g₁ = g₂ := by
  have hsubE : Subsingleton E := Module.finrank_zero_iff.1 hE
  ext x v w
  have hsub : Subsingleton (TangentSpace I x) := hsubE
  rw [hsub.elim v 0]
  simp

variable [CompactSpace M]

/-- The spatial rescaling factor `a(t) = (Vol(g t₀) / Vol(g t)) ^ (2 / n)` that normalizes the
volume of `g t` to `Vol(g t₀)` in real dimension `n` (Topping, §1.2.3). -/
def ricciFlowVolumeScale
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (t₀ t : ℝ) : ℝ :=
  (riemannianTotalVolume I (WithMetric (g t₀)) /
    riemannianTotalVolume I (WithMetric (g t))) ^ (2 / (Module.finrank ℝ E : ℝ))

/-- Unfolds `TauCeti.ricciFlowVolumeScale`. -/
theorem ricciFlowVolumeScale_def
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (t₀ t : ℝ) :
    ricciFlowVolumeScale g t₀ t =
      (riemannianTotalVolume I (WithMetric (g t₀)) /
        riemannianTotalVolume I (WithMetric (g t))) ^ (2 / (Module.finrank ℝ E : ℝ)) :=
  (rfl)

/-- At the base time `t = t₀`, the volume normalization factor is `1`. -/
@[simp]
theorem ricciFlowVolumeScale_self [Nonempty M]
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (t₀ : ℝ) :
    ricciFlowVolumeScale g t₀ t₀ = 1 := by
  have hV : 0 < riemannianTotalVolume I (WithMetric (g t₀)) := riemannianTotalVolume_pos
  rw [ricciFlowVolumeScale_def, div_self hV.ne', Real.one_rpow]

/-- On a nonempty compact manifold, `ricciFlowVolumeScale g t₀ t` is strictly positive. -/
theorem ricciFlowVolumeScale_pos [Nonempty M]
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (t₀ t : ℝ) :
    0 < ricciFlowVolumeScale g t₀ t :=
  Real.rpow_pos_of_pos (div_pos riemannianTotalVolume_pos riemannianTotalVolume_pos) _

/-- Rescaling `g t` by `ricciFlowVolumeScale g t₀ t` restores the initial total volume
`Vol(g t₀)` in every dimension. -/
theorem riemannianTotalVolume_rescale_ricciFlowVolumeScale [Nonempty M]
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (t₀ t : ℝ) :
    riemannianTotalVolume I
      (WithMetric ((g t).rescale (fun _ ↦ ricciFlowVolumeScale g t₀ t) contMDiff_const
        (fun _ ↦ ricciFlowVolumeScale_pos g t₀ t))) =
      riemannianTotalVolume I (WithMetric (g t₀)) := by
  by_cases hE : Module.finrank ℝ E = 0
  · exact congrArg (fun γ ↦ riemannianTotalVolume I (WithMetric γ))
      (contMDiffRiemannianMetric_eq_of_finrank_eq_zero hE _ (g t₀))
  · exact WithMetric.riemannianTotalVolume_rescale_const_div_rpow hE riemannianTotalVolume_pos

/-- **Volume scale of a homothetic Einstein solution.** In nonzero dimension on a nonempty compact
manifold, if `g 0 = g₀` and `g t = (1 - 2 c t) g₀` with `2 c t < 1`, then
`ricciFlowVolumeScale g 0 t = (1 - 2 c t)⁻¹`. -/
theorem ricciFlowVolumeScale_of_eq_rescale_one_sub_two_mul [Nonempty M]
    (hE : Module.finrank ℝ E ≠ 0)
    {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg0 : g 0 = g₀) {c t : ℝ} (ht : 2 * c * t < 1)
    (hgt : g t = g₀.rescale (fun _ ↦ 1 - 2 * c * t) contMDiff_const (fun _ ↦ sub_pos.2 ht)) :
    ricciFlowVolumeScale g 0 t = (1 - 2 * c * t)⁻¹ := by
  have hpos : 0 < 1 - 2 * c * t := sub_pos.2 ht
  have hV : 0 < riemannianTotalVolume I (WithMetric g₀) := riemannianTotalVolume_pos
  have hE' : (Module.finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hE
  rw [ricciFlowVolumeScale_def, hg0, hgt, WithMetric.riemannianTotalVolume_rescale_const,
    div_mul_cancel_right₀ hV.ne', ← Real.rpow_neg hpos.le, ← Real.rpow_mul hpos.le,
    show -((Module.finrank ℝ E : ℝ) / 2) * (2 / (Module.finrank ℝ E : ℝ)) = -1 by field_simp,
    Real.rpow_neg_one]

/-- **Rescaling a homothetic Einstein metric by `ricciFlowVolumeScale` recovers `g₀`.** -/
theorem rescale_ricciFlowVolumeScale_of_eq_rescale_one_sub_two_mul [Nonempty M]
    {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg0 : g 0 = g₀) {c t : ℝ} (ht : 2 * c * t < 1)
    (hgt : g t = g₀.rescale (fun _ ↦ 1 - 2 * c * t) contMDiff_const (fun _ ↦ sub_pos.2 ht)) :
    (g t).rescale (fun _ ↦ ricciFlowVolumeScale g 0 t) contMDiff_const
      (fun _ ↦ ricciFlowVolumeScale_pos g 0 t) = g₀ := by
  by_cases hE : Module.finrank ℝ E = 0
  · exact contMDiffRiemannianMetric_eq_of_finrank_eq_zero hE _ g₀
  · have ha := ricciFlowVolumeScale_of_eq_rescale_one_sub_two_mul hE hg0 ht hgt
    have hpos : 0 < 1 - 2 * c * t := sub_pos.2 ht
    ext x v w
    simp [hgt, ha, inv_mul_cancel₀ hpos.ne']

end VolumeScale

section Boundaryless

open scoped TauCeti.MetricC2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- Pointwise chart-density derivative along a volume-normalized Ricci flow: in every chart around
`x`, the coordinate volume density `ρ` satisfies
`∂_τ ρ = (-Scal(g_t)(x) + n * (2 / n * r(g_t)) / 2) ρ`. -/
private theorem hasDerivWithinAt_chartVolumeDensity_of_volumeNormalizedRicciFlow
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    {t : ℝ} (α : M) {x : M} (hx : x ∈ (chartAt H α).source)
    (hg : ∀ v w, HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w) +
        2 / (Module.finrank ℝ E : ℝ) * (g t).averageScalarCurvature * (g t).inner x v w) s t) :
    HasDerivWithinAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        chartVolumeDensity (I := I) α x)
      ((-(g t).scalarCurvature x +
          (Module.finrank ℝ E : ℝ) *
            (2 / (Module.finrank ℝ E : ℝ) * (g t).averageScalarCurvature) / 2) *
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        chartVolumeDensity (I := I) α x) s t := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  have hn : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := (rfl)
  refine (hasDerivWithinAt_chartVolumeDensity (g := fun τ ↦ (g τ).toRiemannianMetric) α hx
    (h := (-2 : ℝ) • (CovariantDerivative.leviCivitaConnection I M).ricciTensor x +
      (2 / (Module.finrank ℝ E : ℝ) * (g t).averageScalarCurvature) • innerₗ (TangentSpace I x))
    (fun v w ↦ (hg v w).congr_deriv ?_)).congr_deriv ?_
  · simp [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, innerₗ_apply_apply,
      ContMDiffRiemannianMetric.inner_riemannianBundle]
  · rw [map_add, map_smul, map_smul, bilinFormTrace_inner,
      ContMDiffRiemannianMetric.scalarCurvature_def,
      CovariantDerivative.scalarCurvature_apply, smul_eq_mul, smul_eq_mul, hn]
    ring

/-- The volume integral of the pointwise volume-normalized chart-density rate vanishes in every
dimension (including `0`). -/
private theorem integral_volumeNormalizedDrift_eq_zero
    (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    ∫ x : WithMetric g₀,
      ((0 : ℝ) + (-(g₀.scalarCurvature x.ofWithMetric) +
          (Module.finrank ℝ E : ℝ) *
            (2 / (Module.finrank ℝ E : ℝ) * g₀.averageScalarCurvature) / 2) • (1 : ℝ))
      ∂riemannianVolume I (WithMetric g₀) = 0 := by
  by_cases hE : Module.finrank ℝ E = 0
  · have h0 : ∀ x : WithMetric g₀, g₀.scalarCurvature x.ofWithMetric = 0 := by
      intro x
      have hle : Module.finrank ℝ E ≤ 1 := by omega
      let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g₀.toRiemannianMetric⟩
      let cov := CovariantDerivative.leviCivitaConnection I M
      rw [ContMDiffRiemannianMetric.scalarCurvature_def]
      exact cov.scalarCurvature_eq_zero_of_ricciTensor_eq_zero x.ofWithMetric
        (cov.ricciTensor_eq_zero_of_finrank_le_one x.ofWithMetric hle)
    simp [hE, h0]
  · have hE' : (Module.finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hE
    have hκ_eq (x : WithMetric g₀) :
        (0 : ℝ) + (-(g₀.scalarCurvature x.ofWithMetric) +
            (Module.finrank ℝ E : ℝ) *
              (2 / (Module.finrank ℝ E : ℝ) * g₀.averageScalarCurvature) / 2) • (1 : ℝ) =
          -g₀.scalarCurvature x.ofWithMetric + g₀.averageScalarCurvature := by
      simp only [zero_add, smul_eq_mul, mul_one]
      field_simp
    simp_rw [hκ_eq]
    have hcont : Continuous (fun x : WithMetric g₀ ↦ g₀.scalarCurvature x.ofWithMetric) :=
      g₀.contMDiff_scalarCurvature.continuous.comp WithMetric.continuous_ofWithMetric
    have hint : Integrable (fun x : WithMetric g₀ ↦ -g₀.scalarCurvature x.ofWithMetric)
        (riemannianVolume I (WithMetric g₀)) :=
      (hcont.integrable_of_hasCompactSupport (.of_compactSpace _)).neg
    rw [integral_add hint (integrable_const _), integral_neg, integral_const, smul_eq_mul,
      ← riemannianTotalVolume_def, mul_comm _ g₀.averageScalarCurvature,
      g₀.averageScalarCurvature_mul_riemannianTotalVolume, neg_add_cancel]

variable [I.Boundaryless]

/-- If `g` is `C^2`-continuous on `s`, then `ricciFlowVolumeScale g t₀` is continuous on `s`. -/
theorem continuousOn_ricciFlowVolumeScale_chartC2 [Nonempty M]
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (hg_cont : ContinuousOn g s) (t₀ : ℝ) :
    ContinuousOn (ricciFlowVolumeScale g t₀) s := by
  have hvol : ContinuousOn (fun t ↦ riemannianTotalVolume I (WithMetric (g t))) s :=
    ContMDiffRiemannianMetric.continuous_riemannianTotalVolume_chartC2.comp_continuousOn hg_cont
  exact (continuousOn_const.div hvol fun _ _ ↦ riemannianTotalVolume_pos.ne').rpow_const
    fun t _ ↦ Or.inl (div_pos riemannianTotalVolume_pos riemannianTotalVolume_pos).ne'

/-- **Evolution of total volume in terms of average scalar curvature.** Along an unnormalized Ricci
flow on a convex time set `s`, `∂_t Vol(g_t) = -r(g_t) Vol(g_t)` within `s`. -/
theorem IsRicciFlowEquationOn.hasDerivWithinAt_riemannianTotalVolume
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (hg : IsRicciFlowEquationOn g s) (hs : Convex ℝ s) {t : ℝ} (ht : t ∈ s)
    (hg_cont : ContinuousOn g s) :
    HasDerivWithinAt (fun τ ↦ riemannianTotalVolume I (WithMetric (g τ)))
      (-(g t).averageScalarCurvature * riemannianTotalVolume I (WithMetric (g t))) s t := by
  have h := hasDerivWithinAt_riemannianTotalVolume_of_ricciFlow hs ht hg_cont hg
  rwa [← (g t).averageScalarCurvature_mul_riemannianTotalVolume, ← neg_mul] at h

/-- **Zero derivative of total volume along volume-normalized Ricci flow.** On a compact
boundaryless smooth manifold (in every dimension, including `0`), a `C^2`-continuous solution of
`IsVolumeNormalizedRicciFlowEquationOn` on a convex set `s` has `∂_τ Vol(g_τ) = 0` at every
`t ∈ s`. -/
theorem IsVolumeNormalizedRicciFlowEquationOn.hasDerivWithinAt_riemannianTotalVolume
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (hg : IsVolumeNormalizedRicciFlowEquationOn g s) (hs : Convex ℝ s) {t : ℝ} (ht : t ∈ s)
    (hg_cont : ContinuousOn g s) :
    HasDerivWithinAt (fun τ ↦ riemannianTotalVolume I (WithMetric (g τ))) 0 s t := by
  set κ : ℝ → M → ℝ := fun τ x ↦ -(g τ).scalarCurvature x +
    (Module.finrank ℝ E : ℝ) * (2 / (Module.finrank ℝ E : ℝ) * (g τ).averageScalarCurvature) / 2
  have hκ_cont : ContinuousOn (uncurry κ) (s ×ˢ univ) := by
    have hscal : ContinuousOn (uncurry fun τ x ↦ -(g τ).scalarCurvature x) (s ×ˢ univ) :=
      (ContMDiffRiemannianMetric.continuous_scalarCurvature_chartC2.comp_continuousOn
        (hg_cont.prodMap continuousOn_id)).neg
    have havg_s : ContinuousOn (fun τ ↦ (g τ).averageScalarCurvature) s :=
      ContMDiffRiemannianMetric.continuous_averageScalarCurvature_chartC2.comp_continuousOn hg_cont
    have havg : ContinuousOn
        (fun q : ℝ × M ↦ (Module.finrank ℝ E : ℝ) *
          (2 / (Module.finrank ℝ E : ℝ) * (g q.1).averageScalarCurvature) / 2) (s ×ˢ univ) :=
      (continuousOn_const.mul (continuousOn_const.mul
        (havg_s.comp continuous_fst.continuousOn (mapsTo_fst_prod (s := s))))).div_const 2
    exact hscal.add havg
  have h1 := hasDerivWithinAt_integral_riemannianVolume_of_hasDerivWithinAt_chartVolumeDensity
    hs ht isCompact_univ
    (fun α i j ↦ ContMDiffRiemannianMetric.continuousOn_inner_chartLocalFrame_chartCk 2 hg_cont
      α i j)
    (κ := κ) hκ_cont
    (fun α x hx τ hτ ↦ hasDerivWithinAt_chartVolumeDensity_of_volumeNormalizedRicciFlow
      α hx.2 (hg τ hτ x))
    (f := fun _ _ ↦ (1 : ℝ)) (f' := fun _ _ ↦ (0 : ℝ))
    continuousOn_const (fun _ _ ↦ continuous_const) (fun _ _ ↦ subset_univ _)
    continuousOn_const continuous_const (subset_univ _)
    (fun _ _ _ _ ↦ hasDerivWithinAt_const _ _ _)
  have hfun : (fun τ ↦ ∫ _, (1 : ℝ) ∂riemannianVolume I (WithMetric (g τ))) =
      fun τ ↦ riemannianTotalVolume I (WithMetric (g τ)) := by
    ext τ
    simp [riemannianTotalVolume_def]
  rw [hfun] at h1
  exact h1.congr_deriv (integral_volumeNormalizedDrift_eq_zero (g t))

/-- **Conservation of total volume along volume-normalized Ricci flow.** On a preconnected time set
`s`, total Riemannian volume is constant along any `C^2`-continuous solution of
`IsVolumeNormalizedRicciFlowEquationOn g s`. -/
theorem IsVolumeNormalizedRicciFlowEquationOn.riemannianTotalVolume_eq
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (hg : IsVolumeNormalizedRicciFlowEquationOn g s) (hs : IsPreconnected s)
    (hg_cont : ContinuousOn g s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    riemannianTotalVolume I (WithMetric (g a)) = riemannianTotalVolume I (WithMetric (g b)) :=
  hs.eq_of_hasDerivWithinAt_zero
    (fun _ ht ↦ hg.hasDerivWithinAt_riemannianTotalVolume
      (Real.convex_iff_isPreconnected.2 hs) ht hg_cont) ha hb

/-- **Time derivative of `ricciFlowVolumeScale` along unnormalized Ricci flow.** Along an
unnormalized Ricci flow `g` on a convex time set `s`, `a(t) = ricciFlowVolumeScale g t₀ t` solves
`a'(t) = (2 / n) r(g_t) a(t)` within `s`. -/
theorem IsRicciFlowEquationOn.hasDerivWithinAt_ricciFlowVolumeScale [Nonempty M]
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s : Set ℝ}
    (hg : IsRicciFlowEquationOn g s) (hs : Convex ℝ s) {t : ℝ} (ht : t ∈ s)
    (hg_cont : ContinuousOn g s) (t₀ : ℝ) :
    HasDerivWithinAt (ricciFlowVolumeScale g t₀)
      (2 / (Module.finrank ℝ E : ℝ) * (g t).averageScalarCurvature *
        ricciFlowVolumeScale g t₀ t) s t := by
  set V : ℝ → ℝ := fun τ ↦ riemannianTotalVolume I (WithMetric (g τ))
  have hVt₀ : 0 < V t₀ := riemannianTotalVolume_pos
  have hVt : 0 < V t := riemannianTotalVolume_pos
  have hq : 0 < V t₀ / V t := div_pos hVt₀ hVt
  have hV_deriv : HasDerivWithinAt V (-(g t).averageScalarCurvature * V t) s t :=
    hg.hasDerivWithinAt_riemannianTotalVolume hs ht hg_cont
  have hdiv : HasDerivWithinAt (fun τ ↦ V t₀ / V τ)
      ((g t).averageScalarCurvature * (V t₀ / V t)) s t := by
    refine ((hasDerivWithinAt_const t s (V t₀)).fun_div hV_deriv hVt.ne').congr_deriv ?_
    have hVt0 : V t ≠ 0 := hVt.ne'
    field_simp
    ring
  set p : ℝ := 2 / (Module.finrank ℝ E : ℝ)
  have hrpow : (V t₀ / V t) ^ p = (V t₀ / V t) * (V t₀ / V t) ^ (p - 1) := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring, Real.rpow_add hq, Real.rpow_one]
  refine (hdiv.rpow_const (p := p) (Or.inl hq.ne')).congr_deriv ?_
  rw [ricciFlowVolumeScale_def]
  change (g t).averageScalarCurvature * (V t₀ / V t) * p * (V t₀ / V t) ^ (p - 1) =
    p * (g t).averageScalarCurvature * (V t₀ / V t) ^ p
  rw [hrpow]
  ring

/-- **Reparametrizing and rescaling an unnormalized Ricci flow into a volume-normalized flow.**
Let `g` satisfy `IsRicciFlowEquationOn g s` on a convex set `s` with `C^2` time continuity, and let
`ψ : ℝ → ℝ` map `J` into `s` with derivative `(ricciFlowVolumeScale g t₀ (ψ σ))⁻¹` within `J`.
Then `ĝ(σ) = ricciFlowVolumeScale g t₀ (ψ σ) • g(ψ σ)` satisfies
`IsVolumeNormalizedRicciFlowEquationOn ĝ J` (Topping, §1.2.3). -/
theorem IsRicciFlowEquationOn.isVolumeNormalizedRicciFlowEquationOn_rescale_comp [Nonempty M]
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {s J : Set ℝ}
    (hg : IsRicciFlowEquationOn g s) (hs : Convex ℝ s) (hg_cont : ContinuousOn g s) (t₀ : ℝ)
    {ψ : ℝ → ℝ} (hmaps : MapsTo ψ J s)
    (hψ : ∀ σ ∈ J, HasDerivWithinAt ψ (ricciFlowVolumeScale g t₀ (ψ σ))⁻¹ J σ) :
    IsVolumeNormalizedRicciFlowEquationOn
      (fun σ ↦ (g (ψ σ)).rescale (fun _ ↦ ricciFlowVolumeScale g t₀ (ψ σ)) contMDiff_const
        (fun _ ↦ ricciFlowVolumeScale_pos g t₀ (ψ σ))) J := by
  intro σ hσ x v w
  have ht : ψ σ ∈ s := hmaps hσ
  have ha_pos : 0 < ricciFlowVolumeScale g t₀ (ψ σ) := ricciFlowVolumeScale_pos g t₀ (ψ σ)
  have ha0 : ricciFlowVolumeScale g t₀ (ψ σ) ≠ 0 := ha_pos.ne'
  have ha_deriv : HasDerivWithinAt (fun u ↦ ricciFlowVolumeScale g t₀ (ψ u))
      (2 / (Module.finrank ℝ E : ℝ) * (g (ψ σ)).averageScalarCurvature) J σ :=
    ((hg.hasDerivWithinAt_ricciFlowVolumeScale hs ht hg_cont t₀).comp σ (hψ σ hσ)
      hmaps).congr_deriv (by field_simp)
  have hg_deriv : HasDerivWithinAt (fun u ↦ (g (ψ u)).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g (ψ σ)).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w) *
        (ricciFlowVolumeScale g t₀ (ψ σ))⁻¹) J σ :=
    (hg (ψ σ) ht x v w).comp σ (hψ σ hσ) hmaps
  simp only [ContMDiffRiemannianMetric.rescale_inner,
    (g (ψ σ)).ricciTensor_leviCivitaConnection_rescale_const ha_pos x,
    ContMDiffRiemannianMetric.averageScalarCurvature_rescale_const _ ha_pos]
  exact (ha_deriv.fun_mul hg_deriv).congr_deriv (by field_simp; ring)

/-- **Compact-interval volume normalization of Ricci flow.** Given a `C^2`-continuous solution `g`
of `IsRicciFlowEquationOn g (Icc t₀ t₁)` (`t₀ ≤ t₁`) on a nonempty compact boundaryless manifold,
the accumulated normalized time `t ↦ ∫ r in t₀..t, ricciFlowVolumeScale g t₀ r` admits a strictly
increasing `C¹` inverse `ψ` such that `ĝ(σ) = a(ψ σ) g(ψ σ)` on
`[0, ∫ r in t₀..t₁, ricciFlowVolumeScale g t₀ r]` starts at `g t₀`, is `C^2`-continuous, has
constant total volume `Vol(g t₀)`, and solves `IsVolumeNormalizedRicciFlowEquationOn`. -/
theorem IsRicciFlowEquationOn.exists_isVolumeNormalizedRicciFlowEquationOn_Icc [Nonempty M]
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {t₀ t₁ : ℝ}
    (ht₀₁ : t₀ ≤ t₁) (hg_cont : ContinuousOn g (Icc t₀ t₁))
    (hg : IsRicciFlowEquationOn g (Icc t₀ t₁)) :
    ∃ ψ : ℝ → ℝ, StrictMono ψ ∧ ContDiff ℝ 1 ψ ∧
      (∀ t ∈ Icc t₀ t₁, ψ (∫ r in t₀..t, ricciFlowVolumeScale g t₀ r) = t) ∧
      let T' := ∫ r in t₀..t₁, ricciFlowVolumeScale g t₀ r
      let ĝ : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) := fun σ ↦
        (g (ψ σ)).rescale (fun _ ↦ ricciFlowVolumeScale g t₀ (ψ σ)) contMDiff_const
          (fun _ ↦ ricciFlowVolumeScale_pos g t₀ (ψ σ))
      (∀ σ ∈ Icc 0 T', ψ σ ∈ Icc t₀ t₁ ∧
        (∫ r in t₀..ψ σ, ricciFlowVolumeScale g t₀ r) = σ) ∧
      ĝ 0 = g t₀ ∧
      ContinuousOn ĝ (Icc 0 T') ∧
      (∀ σ, riemannianTotalVolume I (WithMetric (ĝ σ)) =
        riemannianTotalVolume I (WithMetric (g t₀))) ∧
      IsVolumeNormalizedRicciFlowEquationOn ĝ (Icc 0 T') := by
  have ha_cont : ContinuousOn (ricciFlowVolumeScale g t₀) (Icc t₀ t₁) :=
    continuousOn_ricciFlowVolumeScale_chartC2 hg_cont t₀
  obtain ⟨ψ, hmono, hC1, hleft, hright⟩ := exists_contDiff_inverse_intervalIntegral ht₀₁ ha_cont
    fun t _ ↦ ricciFlowVolumeScale_pos g t₀ t
  refine ⟨ψ, hmono, hC1, hleft, ?_⟩
  dsimp only
  set T' := ∫ r in t₀..t₁, ricciFlowVolumeScale g t₀ r
  have hmaps : MapsTo ψ (Icc 0 T') (Icc t₀ t₁) := fun σ hσ ↦ (hright σ hσ).1
  have hψ0 : ψ 0 = t₀ := by
    simpa only [intervalIntegral.integral_same] using hleft t₀ (left_mem_Icc.2 ht₀₁)
  refine ⟨fun σ hσ ↦ ⟨(hright σ hσ).1, (hright σ hσ).2.1⟩, ?_, ?_,
    fun σ ↦ riemannianTotalVolume_rescale_ricciFlowVolumeScale g t₀ (ψ σ), ?_⟩
  · simp [hψ0]
  · exact continuousOn_rescale_const_chartC2 (fun σ ↦ ricciFlowVolumeScale_pos g t₀ (ψ σ))
      (hg_cont.comp hC1.continuous.continuousOn hmaps)
      (ha_cont.comp hC1.continuous.continuousOn hmaps)
  · exact hg.isVolumeNormalizedRicciFlowEquationOn_rescale_comp (convex_Icc t₀ t₁) hg_cont t₀
      hmaps fun σ hσ ↦ ((hright σ hσ).2.2).hasDerivWithinAt

end Boundaryless

section HalfOpenInverse

/-- If `a ≥ 0` is continuous on `[t₀, T)` (`t₀ < T`) and `∫ r in t₀..t, a r → +∞` as `t ↑ T`, then
the image of `[t₀, T)` under `t ↦ ∫ r in t₀..t, a r` is `[0, ∞)`. -/
private theorem image_intervalIntegral_Ico_eq_Ici {a : ℝ → ℝ} {t₀ T : ℝ} (ht₀T : t₀ < T)
    (ha_cont : ContinuousOn a (Ico t₀ T)) (ha_nonneg : ∀ r ∈ Ico t₀ T, 0 ≤ a r)
    (htop : Tendsto (fun t ↦ ∫ r in t₀..t, a r) (𝓝[<] T) atTop) :
    (fun t ↦ ∫ r in t₀..t, a r) '' Ico t₀ T = Ici 0 := by
  refine Subset.antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨r, hr, rfl⟩
    exact intervalIntegral.integral_nonneg hr.1 fun u hu ↦ ha_nonneg u ⟨hu.1, hu.2.trans_lt hr.2⟩
  · have hev : ∀ᶠ r in 𝓝[<] T, t₀ < r ∧ (y < ∫ u in t₀..r, a u) ∧ r < T :=
      (eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds ht₀T)).and
        ((htop.eventually_gt_atTop y).and self_mem_nhdsWithin)
    have : (𝓝[<] T).NeBot := nhdsLT_neBot T
    obtain ⟨r, ht₀r, hyr, hrT⟩ := hev.exists
    have ha_sub : ContinuousOn a (Icc t₀ r) := ha_cont.mono (Icc_subset_Ico_right hrT)
    have hτ_cont : ContinuousOn (fun t ↦ ∫ u in t₀..t, a u) (Icc t₀ r) := fun u hu ↦ by
      have : Fact (u ∈ Icc t₀ r) := ⟨hu⟩
      exact (intervalIntegral.integral_hasDerivWithinAt_right
        (ha_sub.mono (uIcc_subset_Icc (left_mem_Icc.2 ht₀r.le) hu)).intervalIntegrable
        (ha_sub.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc u)
        (ha_sub u hu)).continuousWithinAt
    exact image_mono (Icc_subset_Ico_right hrT)
      (intermediate_value_Icc ht₀r.le hτ_cont ⟨by simpa using mem_Ici.1 hy, hyr.le⟩)

/-- For `a > 0` continuous on `[t₀, T)`, `τ(t) = ∫ r in t₀..t, a r` is strictly increasing on
`[t₀, T)` and its `invFunOn` on `J = τ '' Ico t₀ T` has derivative `(a (ψ σ))⁻¹` within `J`. -/
private theorem strictMonoOn_and_hasDerivWithinAt_invFunOn_intervalIntegral_Ico
    {a : ℝ → ℝ} {t₀ T : ℝ} (ha_cont : ContinuousOn a (Ico t₀ T))
    (ha_pos : ∀ r ∈ Ico t₀ T, 0 < a r) :
    let τ : ℝ → ℝ := fun t ↦ ∫ r in t₀..t, a r
    let J : Set ℝ := τ '' Ico t₀ T
    let ψ : ℝ → ℝ := invFunOn τ (Ico t₀ T)
    StrictMonoOn τ (Ico t₀ T) ∧ ∀ σ ∈ J, HasDerivWithinAt ψ (a (ψ σ))⁻¹ J σ := by
  dsimp only
  have hτ_mono : StrictMonoOn (fun t ↦ ∫ r in t₀..t, a r) (Ico t₀ T) := by
    intro r₁ hr₁ r₂ hr₂ hlt
    obtain ⟨ψ₁, hψ₁_mono, _, hψ₁_left, _⟩ := exists_contDiff_inverse_intervalIntegral hr₂.1
      (ha_cont.mono (Icc_subset_Ico_right hr₂.2))
      fun r hr ↦ ha_pos r (Icc_subset_Ico_right hr₂.2 hr)
    rw [← hψ₁_left r₁ ⟨hr₁.1, hlt.le⟩, ← hψ₁_left r₂ ⟨hr₂.1, le_rfl⟩] at hlt
    exact hψ₁_mono.lt_iff_lt.1 hlt
  refine ⟨hτ_mono, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hleft : ∀ r ∈ Ico t₀ T,
      invFunOn (fun u ↦ ∫ r in t₀..u, a r) (Ico t₀ T) (∫ u in t₀..r, a u) = r :=
    hτ_mono.injOn.leftInvOn_invFunOn
  have htt₁ : t < (t + T) / 2 := by linarith [ht.2]
  have ht₁T : (t + T) / 2 < T := by linarith [ht.2]
  set t₁ : ℝ := (t + T) / 2
  have ht₀t₁ : t₀ ≤ t₁ := ht.1.trans htt₁.le
  obtain ⟨ψ₁, _, _, _, hψ₁_right⟩ := exists_contDiff_inverse_intervalIntegral ht₀t₁
    (ha_cont.mono (Icc_subset_Ico_right ht₁T))
    fun r hr ↦ ha_pos r (Icc_subset_Ico_right ht₁T hr)
  have hτ_nonneg : ∀ r ∈ Ico t₀ T, 0 ≤ ∫ u in t₀..r, a u := fun r hr ↦
    intervalIntegral.integral_nonneg hr.1 fun u hu ↦ (ha_pos u ⟨hu.1, hu.2.trans_lt hr.2⟩).le
  have hτ_lt : (∫ u in t₀..t, a u) < ∫ u in t₀..t₁, a u := hτ_mono ht ⟨ht₀t₁, ht₁T⟩ htt₁
  have hσ_sub : (∫ u in t₀..t, a u) ∈ Icc 0 (∫ u in t₀..t₁, a u) := ⟨hτ_nonneg t ht, hτ_lt.le⟩
  have heq_on : ∀ u ∈ Icc 0 (∫ r in t₀..t₁, a r),
      invFunOn (fun v ↦ ∫ r in t₀..v, a r) (Ico t₀ T) u = ψ₁ u := fun u hu ↦ by
    have h1 := hleft (ψ₁ u) (Icc_subset_Ico_right ht₁T (hψ₁_right u hu).1)
    rwa [(hψ₁_right u hu).2.1] at h1
  have hev : invFunOn (fun v ↦ ∫ r in t₀..v, a r) (Ico t₀ T) =ᶠ[
      𝓝[(fun v ↦ ∫ r in t₀..v, a r) '' Ico t₀ T] (∫ u in t₀..t, a u)] ψ₁ := by
    filter_upwards [inter_mem_nhdsWithin _ (Iio_mem_nhds hτ_lt)] with u hu
    rcases hu with ⟨⟨r, hr, rfl⟩, hu_lt⟩
    exact heq_on _ ⟨hτ_nonneg r hr, hu_lt.le⟩
  have hd := ((hψ₁_right (∫ u in t₀..t, a u) hσ_sub).2.2).hasDerivWithinAt
    (s := (fun v ↦ ∫ r in t₀..v, a r) '' Ico t₀ T)
  rw [← heq_on _ hσ_sub] at hd
  exact hd.congr_of_eventuallyEq hev (heq_on _ hσ_sub)

end HalfOpenInverse

section BoundarylessEquivalence

open scoped TauCeti.MetricC2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Half-open / maximal interval volume normalization of Ricci flow.** Let `g` be a
`C^2`-continuous solution of `IsRicciFlowEquationOn g (Ico t₀ T)` (`t₀ < T`) on a nonempty compact
boundaryless manifold, and let `τ(t) = ∫ r in t₀..t, ricciFlowVolumeScale g t₀ r` with image
`J = τ '' Ico t₀ T`. Then `τ` has a strictly increasing continuous inverse `ψ` on `J` mapping `0`
to `t₀`, the normalized family `ĝ(σ) = a(ψ σ) g(ψ σ)` is `C^2`-continuous and solves
`IsVolumeNormalizedRicciFlowEquationOn ĝ J` with constant volume `Vol(g t₀)`, and if
`τ(t) → +∞` as `t ↑ T` then `J = [0, ∞)`. -/
theorem IsRicciFlowEquationOn.exists_isVolumeNormalizedRicciFlowEquationOn_Ico [Nonempty M]
    {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {t₀ T : ℝ}
    (ht₀T : t₀ < T) (hg_cont : ContinuousOn g (Ico t₀ T))
    (hg : IsRicciFlowEquationOn g (Ico t₀ T)) :
    let τ : ℝ → ℝ := fun t ↦ ∫ r in t₀..t, ricciFlowVolumeScale g t₀ r
    let J : Set ℝ := τ '' Ico t₀ T
    ∃ ψ : ℝ → ℝ,
      MapsTo ψ J (Ico t₀ T) ∧
      (∀ t ∈ Ico t₀ T, ψ (τ t) = t) ∧
      (∀ σ ∈ J, τ (ψ σ) = σ) ∧
      StrictMonoOn ψ J ∧
      ContinuousOn ψ J ∧
      (Tendsto τ (𝓝[<] T) atTop → J = Ici 0) ∧
      let ĝ : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) := fun σ ↦
        (g (ψ σ)).rescale (fun _ ↦ ricciFlowVolumeScale g t₀ (ψ σ)) contMDiff_const
          (fun _ ↦ ricciFlowVolumeScale_pos g t₀ (ψ σ))
      ĝ 0 = g t₀ ∧
      ContinuousOn ĝ J ∧
      (∀ σ, riemannianTotalVolume I (WithMetric (ĝ σ)) =
        riemannianTotalVolume I (WithMetric (g t₀))) ∧
      IsVolumeNormalizedRicciFlowEquationOn ĝ J := by
  dsimp only
  set a := ricciFlowVolumeScale g t₀
  set τ : ℝ → ℝ := fun t ↦ ∫ r in t₀..t, a r
  set J : Set ℝ := τ '' Ico t₀ T
  have ha_cont : ContinuousOn a (Ico t₀ T) := continuousOn_ricciFlowVolumeScale_chartC2 hg_cont t₀
  obtain ⟨hτ_mono, hψ_deriv⟩ := strictMonoOn_and_hasDerivWithinAt_invFunOn_intervalIntegral_Ico
    ha_cont fun r _ ↦ ricciFlowVolumeScale_pos g t₀ r
  set ψ : ℝ → ℝ := invFunOn τ (Ico t₀ T)
  have hleft : ∀ r ∈ Ico t₀ T, ψ (τ r) = r := hτ_mono.injOn.leftInvOn_invFunOn
  have hmem : MapsTo ψ J (Ico t₀ T) := fun _ hσ ↦ invFunOn_mem hσ
  have hright : ∀ σ ∈ J, τ (ψ σ) = σ := fun _ hσ ↦ invFunOn_eq hσ
  have hψ_cont : ContinuousOn ψ J := fun σ hσ ↦ (hψ_deriv σ hσ).continuousWithinAt
  have hψ_mono : StrictMonoOn ψ J := fun σ₁ hσ₁ σ₂ hσ₂ hlt ↦ by
    by_contra! hle
    rcases hle.eq_or_lt with heq | hgt
    · exact hlt.ne (by rw [← hright σ₁ hσ₁, ← hright σ₂ hσ₂, heq])
    · exact not_lt_of_ge (hτ_mono (hmem hσ₂) (hmem hσ₁) hgt).le
        (by change τ (ψ σ₁) < τ (ψ σ₂); rwa [hright σ₁ hσ₁, hright σ₂ hσ₂])
  have hJ_Ici : Tendsto τ (𝓝[<] T) atTop → J = Ici 0 :=
    image_intervalIntegral_Ico_eq_Ici ht₀T ha_cont fun r _ ↦ (ricciFlowVolumeScale_pos g t₀ r).le
  have hψ0 : ψ 0 = t₀ := by simpa [τ] using hleft t₀ ⟨le_rfl, ht₀T⟩
  refine ⟨ψ, hmem, hleft, hright, hψ_mono, hψ_cont, hJ_Ici, by simp [hψ0], ?_,
    fun σ ↦ riemannianTotalVolume_rescale_ricciFlowVolumeScale g t₀ (ψ σ),
    hg.isVolumeNormalizedRicciFlowEquationOn_rescale_comp (convex_Ico t₀ T) hg_cont t₀ hmem
      hψ_deriv⟩
  exact continuousOn_rescale_const_chartC2 (fun σ ↦ ricciFlowVolumeScale_pos g t₀ (ψ σ))
    (hg_cont.comp hψ_cont hmem) (ha_cont.comp hψ_cont hmem)

/-- **Converse compact-interval transformation: volume-normalized to unnormalized Ricci flow.**
Given a `C^2`-continuous solution `ĝ` of `IsVolumeNormalizedRicciFlowEquationOn ĝ (Icc σ₀ σ₁)`
(`σ₀ ≤ σ₁`) on a compact boundaryless manifold, let
`c(σ) = exp(-(2 / n) ∫ u in σ₀..σ, r(ĝ u))`. Then `σ ↦ ∫ u in σ₀..σ, c u` admits a strictly
increasing `C¹` inverse `φ` such that `g(t) = c(φ t) ĝ(φ t)` on
`[0, ∫ u in σ₀..σ₁, c u]` starts at `ĝ σ₀`, is `C^2`-continuous, and solves
`IsRicciFlowEquationOn`. -/
theorem IsVolumeNormalizedRicciFlowEquationOn.exists_isRicciFlowEquationOn_Icc
    {ĝ : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {σ₀ σ₁ : ℝ}
    (hσ₀₁ : σ₀ ≤ σ₁) (hĝ_cont : ContinuousOn ĝ (Icc σ₀ σ₁))
    (hĝ : IsVolumeNormalizedRicciFlowEquationOn ĝ (Icc σ₀ σ₁)) :
    let c : ℝ → ℝ := fun σ ↦
      Real.exp (-(2 / (Module.finrank ℝ E : ℝ)) * ∫ u in σ₀..σ, (ĝ u).averageScalarCurvature)
    ∃ φ : ℝ → ℝ, StrictMono φ ∧ ContDiff ℝ 1 φ ∧
      (∀ σ ∈ Icc σ₀ σ₁, φ (∫ u in σ₀..σ, c u) = σ) ∧
      let T := ∫ u in σ₀..σ₁, c u
      let g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) := fun t ↦
        (ĝ (φ t)).rescale (fun _ ↦ c (φ t)) contMDiff_const (fun _ ↦ Real.exp_pos _)
      (∀ t ∈ Icc 0 T, φ t ∈ Icc σ₀ σ₁ ∧ (∫ u in σ₀..φ t, c u) = t) ∧
      g 0 = ĝ σ₀ ∧
      ContinuousOn g (Icc 0 T) ∧
      IsRicciFlowEquationOn g (Icc 0 T) := by
  dsimp only
  set rbar : ℝ → ℝ := fun u ↦ (ĝ u).averageScalarCurvature
  have hrbar_cont : ContinuousOn rbar (Icc σ₀ σ₁) :=
    ContMDiffRiemannianMetric.continuous_averageScalarCurvature_chartC2.comp_continuousOn hĝ_cont
  set c : ℝ → ℝ := fun σ ↦ Real.exp (-(2 / (Module.finrank ℝ E : ℝ)) * ∫ u in σ₀..σ, rbar u)
  have hc_deriv : ∀ σ ∈ Icc σ₀ σ₁, HasDerivWithinAt c
      (-(2 / (Module.finrank ℝ E : ℝ)) * rbar σ * c σ) (Icc σ₀ σ₁) σ := by
    intro σ hσ
    have : Fact (σ ∈ Icc σ₀ σ₁) := ⟨hσ⟩
    have hI : HasDerivWithinAt (fun u ↦ ∫ r in σ₀..u, rbar r) (rbar σ) (Icc σ₀ σ₁) σ :=
      intervalIntegral.integral_hasDerivWithinAt_right
        (hrbar_cont.mono (uIcc_subset_Icc (left_mem_Icc.2 hσ₀₁) hσ)).intervalIntegrable
        (hrbar_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc σ)
        (hrbar_cont σ hσ)
    exact ((hI.const_mul (-(2 / (Module.finrank ℝ E : ℝ)))).exp).congr_deriv
      (by simp only [c]; ring)
  have hc_cont : ContinuousOn c (Icc σ₀ σ₁) := fun σ hσ ↦ (hc_deriv σ hσ).continuousWithinAt
  obtain ⟨φ, hmono, hC1, hleft, hright⟩ := exists_contDiff_inverse_intervalIntegral hσ₀₁ hc_cont
    fun σ _ ↦ Real.exp_pos _
  refine ⟨φ, hmono, hC1, hleft, ?_⟩
  set T := ∫ u in σ₀..σ₁, c u
  have hmaps : MapsTo φ (Icc 0 T) (Icc σ₀ σ₁) := fun t ht ↦ (hright t ht).1
  have hφ0 : φ 0 = σ₀ := by
    simpa only [intervalIntegral.integral_same] using hleft σ₀ (left_mem_Icc.2 hσ₀₁)
  refine ⟨fun t ht ↦ ⟨(hright t ht).1, (hright t ht).2.1⟩, ?_, ?_, ?_⟩
  · simp [hφ0]
  · exact continuousOn_rescale_const_chartC2 (fun _ ↦ Real.exp_pos _)
      (hĝ_cont.comp hC1.continuous.continuousOn hmaps)
      (hc_cont.comp hC1.continuous.continuousOn hmaps)
  · exact hĝ.isRicciFlowEquationOn_rescale_comp (fun _ ↦ Real.exp_pos _) hc_deriv hmaps
      fun t ht ↦ ((hright t ht).2.2).hasDerivWithinAt

end BoundarylessEquivalence

section ShrinkingTimeIntegral

/-- **Normalized time integral for a homothetic Einstein solution.** For `c ≠ 0` and `2 c t < 1`,
`∫ r in 0..t, (1 - 2 c r)⁻¹ = -(2 c)⁻¹ log(1 - 2 c t)`. -/
theorem intervalIntegral_inv_one_sub_two_mul {c t : ℝ} (hc : c ≠ 0) (ht : 2 * c * t < 1) :
    (∫ r in (0 : ℝ)..t, (1 - 2 * c * r)⁻¹) = -(2 * c)⁻¹ * Real.log (1 - 2 * c * t) := by
  have hpos : ∀ r ∈ uIcc (0 : ℝ) t, 0 < 1 - 2 * c * r := by
    intro r hr
    rcases le_total 0 t with h0t | ht0
    · rw [uIcc_of_le h0t] at hr
      rcases lt_or_gt_of_ne hc with hc_neg | hc_pos
      · nlinarith [hr.1]
      · nlinarith [hr.2]
    · rw [uIcc_of_ge ht0] at hr
      rcases lt_or_gt_of_ne hc with hc_neg | hc_pos
      · nlinarith [hr.1]
      · nlinarith [hr.2]
  set F : ℝ → ℝ := fun r ↦ -(2 * c)⁻¹ * Real.log (1 - 2 * c * r)
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) t, HasDerivAt F (1 - 2 * c * r)⁻¹ r := by
    intro r hr
    have hlin : HasDerivAt (fun u ↦ 1 - 2 * c * u) (-2 * c) r :=
      ((hasDerivAt_const r (1 : ℝ)).fun_sub ((hasDerivAt_id r).const_mul (2 * c))).congr_deriv
        (by ring)
    exact (((Real.hasDerivAt_log (hpos r hr).ne').comp r hlin).const_mul
      (-(2 * c)⁻¹)).congr_deriv (by field_simp)
  have hint : IntervalIntegrable (fun r ↦ (1 - 2 * c * r)⁻¹) volume 0 t :=
    ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).inv₀
      fun r hr ↦ (hpos r hr).ne').intervalIntegrable
  simpa [F] using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- **Infinite normalized lifetime of a shrinking Einstein solution.** For `c > 0`, as
unnormalized time `t` approaches the finite extinction time `(2 c)⁻¹` from below, normalized time
`∫ r in 0..t, (1 - 2 c r)⁻¹` tends to `+∞`. -/
theorem tendsto_intervalIntegral_inv_one_sub_two_mul_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t ↦ ∫ r in (0 : ℝ)..t, (1 - 2 * c * r)⁻¹) (𝓝[<] (2 * c)⁻¹) atTop := by
  have hc2 : 0 < 2 * c := by positivity
  have hev : (fun t ↦ ∫ r in (0 : ℝ)..t, (1 - 2 * c * r)⁻¹) =ᶠ[𝓝[<] (2 * c)⁻¹]
      fun t ↦ -(2 * c)⁻¹ * Real.log (1 - 2 * c * t) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < (2 * c)⁻¹)
    exact intervalIntegral_inv_one_sub_two_mul hc.ne'
      (by calc 2 * c * t < 2 * c * (2 * c)⁻¹ := mul_lt_mul_of_pos_left ht hc2
            _ = 1 := mul_inv_cancel₀ hc2.ne')
  have hsub : Tendsto (fun t ↦ 1 - 2 * c * t) (𝓝[<] (2 * c)⁻¹) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hcont : Continuous (fun t ↦ 1 - 2 * c * t) :=
        continuous_const.sub (continuous_const.mul continuous_id)
      have htend := (hcont.continuousAt (x := (2 * c)⁻¹)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Iio (2 * c)⁻¹))
      rwa [mul_inv_cancel₀ hc2.ne', sub_self] at htend
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t < (2 * c)⁻¹)
      have : 2 * c * t < 1 := by
        calc 2 * c * t < 2 * c * (2 * c)⁻¹ := mul_lt_mul_of_pos_left ht hc2
          _ = 1 := mul_inv_cancel₀ hc2.ne'
      exact sub_pos.2 this
  have hlog : Tendsto (fun t ↦ -(2 * c)⁻¹ * Real.log (1 - 2 * c * t))
      (𝓝[<] (2 * c)⁻¹) atTop :=
    (Real.tendsto_log_nhdsGT_zero.comp hsub).const_mul_atBot_of_neg
      (neg_lt_zero.2 (inv_pos.2 hc2))
  exact hlog.congr' hev.symm

end ShrinkingTimeIntegral

end TauCeti
