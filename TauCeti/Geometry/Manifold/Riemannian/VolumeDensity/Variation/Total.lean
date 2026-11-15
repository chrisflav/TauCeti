/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Variation.Integral
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Continuity and first variation of total Riemannian volume

On a compact `C¹` manifold `M`, the total Riemannian volume `TauCeti.riemannianTotalVolume` is the
integral of the constant function `1` against `TauCeti.riemannianVolume`. Specializing the
parametric continuity and differentiation formulas for Riemannian integrals yields:

* **Parametric and chart-topology continuity:** `p ↦ Vol(g_p)` is continuous whenever the
  chart-frame entries of `g_p` are jointly continuous, and in particular `g ↦ Vol(WithMetric g)` is
  continuous in `Bundle.ContMDiffRiemannianMetric.chartCkTopology k` for every `k : ℕ∞` (hence in
  both the chart `C²` and chart `C∞` topologies) on a compact smooth boundaryless manifold.
* **First variation of total volume:** along a family of continuous metrics with within-`s`
  derivative `h = ∂_τ g` at `τ = t` on a convex parameter set `s ⊆ ℝ`,
  `∂_τ Vol(g_τ) = ½ ∫ tr_g(h) dV_g`, with no orientation or boundaryless assumption.
* **Conformal and constant-rescaling specializations:** under `∂_τ g = μ g` in real dimension `n`,
  `∂_τ Vol(g_τ) = (n / 2) ∫ μ dV_g`; for `g_τ = c(τ) g₀` with `c(τ) > 0`, both the power form
  `(n / 2) c^(n / 2 - 1) c' Vol(g₀)` and the logarithmic-derivative form `(n c' / (2 c)) Vol(c g₀)`
  hold.
* **Unnormalized and volume-normalized Ricci flow:** under `∂_τ g = -2 Ric(g)`,
  `∂_τ Vol(g_τ) = -∫ Scal(g) dV_g`; under the volume-normalized Ricci flow
  `∂_τ g = -2 Ric(g) + (2 / n) r(g) g` on a nonempty compact manifold of positive dimension `n`,
  where `r(g) = Vol(g)⁻¹ ∫ Scal(g) dV_g`, total volume has zero derivative.

## Main results

* `TauCeti.continuousOn_riemannianTotalVolume`,
  `TauCeti.WithMetric.continuousOn_riemannianTotalVolume`: parametric continuity of total volume.
* `Bundle.ContMDiffRiemannianMetric.continuousOn_inner_chartLocalFrame_chartCk`,
  `Bundle.ContMDiffRiemannianMetric.continuous_riemannianTotalVolume_chartCk`: joint continuity of
  chart-frame inner products and continuity of `g ↦ Vol(WithMetric g)` in `chartCkTopology k`.
* `TauCeti.hasDerivWithinAt_riemannianTotalVolume`, `TauCeti.hasDerivAt_riemannianTotalVolume`,
  `TauCeti.WithMetric.hasDerivWithinAt_riemannianTotalVolume`,
  `TauCeti.WithMetric.hasDerivAt_riemannianTotalVolume`: `∂_τ Vol(g_τ) = ½ ∫ tr_g(h) dV_g`.
* `TauCeti.hasDerivWithinAt_riemannianTotalVolume_of_conformal`,
  `TauCeti.WithMetric.hasDerivWithinAt_riemannianTotalVolume_rescale_const`,
  `TauCeti.WithMetric.hasDerivWithinAt_riemannianTotalVolume_rescale_const'`: conformal and
  constant-rescaling variations of total volume.
* `TauCeti.hasDerivWithinAt_riemannianTotalVolume_of_ricciFlow`,
  `TauCeti.hasDerivAt_riemannianTotalVolume_of_ricciFlow`,
  `TauCeti.WithMetric.hasDerivWithinAt_riemannianTotalVolume_of_ricciFlow`,
  `TauCeti.WithMetric.hasDerivAt_riemannianTotalVolume_of_ricciFlow`:
  `∂_τ Vol(g_τ) = -∫ Scal(g) dV_g` along a Ricci flow.
* `TauCeti.WithMetric.hasDerivWithinAt_riemannianTotalVolume_of_normalizedRicciFlow`: conservation
  (`∂_τ Vol(g_τ) = 0`) of total volume along a volume-normalized Ricci flow.

## References

* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Sections 1.2.3 and 2.3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 2.44.
-/

public section

open Bundle MeasureTheory Riemannian.Tensor Set Filter
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]

private theorem integral_one_eq_riemannianTotalVolume [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] :
    ∫ _ : M, (1 : ℝ) ∂riemannianVolume I M = riemannianTotalVolume I M := by
  rw [integral_const, smul_eq_mul, mul_one, riemannianTotalVolume_def]

/-! ### Parametric continuity of total volume -/

/-- **Parametric continuity of total Riemannian volume.** On a compact `C¹` manifold `M`, if the
chart-frame entries of a metric family `g_p` are jointly continuous on `U × (chartAt H α).source`
for every chart `α`, then `p ↦ riemannianTotalVolume I M` is continuous on `U`. -/
theorem continuousOn_riemannianTotalVolume [IsManifold I 1 M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] {P : Type*} [TopologicalSpace P] {U : Set P}
    (g : P → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    (hg_cont : ∀ α i j, ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source)) :
    ContinuousOn
      (fun p ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g p).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g p);
        riemannianTotalVolume I M)
      U :=
  (continuousOn_integral_riemannianVolume g (f := fun _ _ ↦ (1 : ℝ)) hg_cont
    continuousOn_const).congr fun p _ ↦ by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g p).toRiemannianMetric⟩
      let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle (g p)
      exact integral_one_eq_riemannianTotalVolume.symm

/-! ### First variation of total volume -/

section Variation

variable [IsManifold I 1 M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  {s U : Set ℝ} {t : ℝ}

/-- **First variation of total Riemannian volume.** Along a family of continuous Riemannian metrics
`g_τ` on a compact `C¹` manifold `M` with within-`s` derivative `h = ∂_τ g` on `U ∈ 𝓝[s] t` for a
convex parameter set `s ⊆ ℝ`,

`∂_τ Vol(g_τ) = ½ ∫ x, tr_{g_t}(h_t x) dV_{g_t}`. -/
theorem hasDerivWithinAt_riemannianTotalVolume
    (g : ℝ → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)}
    (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w) (h τ x v w) s τ)
    (htr_cont : ContinuousOn (fun q : ℝ × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
        bilinFormTrace (h q.1 q.2)) (U ×ˢ univ)) :
    HasDerivWithinAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        riemannianTotalVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t);
        2⁻¹ * ∫ x, bilinFormTrace (h t x) ∂riemannianVolume I M)
      s t := by
  have hmain := hasDerivWithinAt_integral_riemannianVolume_const g (f := fun _ ↦ (1 : ℝ)) hs ht hU
    hg_cont hg_deriv htr_cont continuous_const
  refine (hmain.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ ↦ by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
      let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle (g τ)
      exact integral_one_eq_riemannianTotalVolume.symm)
    (by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle (g t)
      exact integral_one_eq_riemannianTotalVolume.symm)).congr_deriv ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle (g t)
  simp only [smul_eq_mul, mul_one, integral_const_mul]

/-- **Two-sided first variation of total Riemannian volume.** -/
theorem hasDerivAt_riemannianTotalVolume
    (g : ℝ → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x))
    {h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)} (hU : U ∈ 𝓝 t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivAt (fun τ' ↦ (g τ').inner x v w) (h τ x v w) τ)
    (htr_cont : ContinuousOn (fun q : ℝ × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
        bilinFormTrace (h q.1 q.2)) (U ×ˢ univ)) :
    HasDerivAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        riemannianTotalVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t);
        2⁻¹ * ∫ x, bilinFormTrace (h t x) ∂riemannianVolume I M)
      t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_riemannianTotalVolume g convex_univ (mem_univ t) (by rwa [nhdsWithin_univ])
      hg_cont (fun τ hτ x v w ↦ (hg_deriv τ hτ x v w).hasDerivWithinAt) htr_cont

/-- **Total volume under a conformal variation.** On a compact manifold of real dimension `n`, if
`∂_τ g = μ g` within `s` on `U ∈ 𝓝[s] t` with jointly continuous conformal rate `μ`, then

`∂_τ Vol(g_τ) = (n / 2) ∫ x, μ_t x dV_{g_t}`. -/
theorem hasDerivWithinAt_riemannianTotalVolume_of_conformal
    (g : ℝ → ContinuousRiemannianMetric E (fun x : M ↦ TangentSpace I x)) {μ : ℝ → M → ℝ}
    (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w) (μ τ x * (g τ).inner x v w) s τ)
    (hμ_cont : ContinuousOn (Function.uncurry μ) (U ×ˢ univ)) :
    HasDerivWithinAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ);
        riemannianTotalVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t);
        (Module.finrank ℝ E : ℝ) / 2 * ∫ x, μ t x ∂riemannianVolume I M)
      s t := by
  have hmain := hasDerivWithinAt_integral_riemannianVolume_of_conformal g (μ := μ)
    (f := fun _ _ ↦ (1 : ℝ)) (f' := fun _ _ ↦ (0 : ℝ)) hs ht hU hg_cont hg_deriv hμ_cont
    continuousOn_const continuousOn_const fun τ _ _ ↦ hasDerivWithinAt_const τ s (1 : ℝ)
  refine (hmain.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ ↦ by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
      let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle (g τ)
      exact integral_one_eq_riemannianTotalVolume.symm)
    (by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle (g t)
      exact integral_one_eq_riemannianTotalVolume.symm)).congr_deriv ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle (g t)
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun _ ↦ by dsimp only; rw [smul_eq_mul]; ring)

end Variation

/-! ### Total volume along a Ricci flow -/

section RicciFlow

variable [IsManifold I ∞ M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  {s U : Set ℝ} {t : ℝ}

/-- **Variation of total volume along a Ricci flow.** Under `∂_τ g = -2 Ric(g)` within a convex
parameter set `s ⊆ ℝ` on `U ∈ 𝓝[s] t`,

`∂_τ Vol(g_τ) = -∫ x, Scal(g_t)(x) dV_{g_t}`. -/
theorem hasDerivWithinAt_riemannianTotalVolume_of_ricciFlow
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s τ)
    (hscal_cont : ContinuousOn (fun q : ℝ × M ↦ (g q.1).scalarCurvature q.2) (U ×ˢ univ)) :
    HasDerivWithinAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ).toContinuousRiemannianMetric;
        riemannianTotalVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t).toContinuousRiemannianMetric;
        -∫ x, (g t).scalarCurvature x ∂riemannianVolume I M)
      s t := by
  have hmain := hasDerivWithinAt_integral_riemannianVolume_of_ricciFlow g
    (f := fun _ _ ↦ (1 : ℝ)) (f' := fun _ _ ↦ (0 : ℝ)) hs ht hU hg_cont hg_deriv hscal_cont
    continuousOn_const continuousOn_const fun τ _ _ ↦ hasDerivWithinAt_const τ s (1 : ℝ)
  refine (hmain.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ ↦ by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
      let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle (g τ).toContinuousRiemannianMetric
      exact integral_one_eq_riemannianTotalVolume.symm)
    (by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle (g t).toContinuousRiemannianMetric
      exact integral_one_eq_riemannianTotalVolume.symm)).congr_deriv ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle (g t).toContinuousRiemannianMetric
  simp only [zero_sub, smul_eq_mul, mul_one, integral_neg]

/-- **Two-sided variation of total volume along a Ricci flow.** -/
theorem hasDerivAt_riemannianTotalVolume_of_ricciFlow
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (hU : U ∈ 𝓝 t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivAt (fun τ' ↦ (g τ').inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) τ)
    (hscal_cont : ContinuousOn (fun q : ℝ × M ↦ (g q.1).scalarCurvature q.2) (U ×ˢ univ)) :
    HasDerivAt
      (fun τ ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g τ).toContinuousRiemannianMetric;
        riemannianTotalVolume I M)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle (g t).toContinuousRiemannianMetric;
        -∫ x, (g t).scalarCurvature x ∂riemannianVolume I M)
      t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_riemannianTotalVolume_of_ricciFlow g convex_univ (mem_univ t)
      (by rwa [nhdsWithin_univ]) hg_cont
      (fun τ hτ x v w ↦ (hg_deriv τ hτ x v w).hasDerivWithinAt) hscal_cont

end RicciFlow

end General

/-! ### Metric-indexed copy (`WithMetric`) forms -/

namespace WithMetric

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]

/-- Parametric continuity of `p ↦ riemannianTotalVolume I (WithMetric (g p))` on a compact `C¹`
manifold. -/
theorem continuousOn_riemannianTotalVolume [IsManifold I 1 M] [T2Space M]
    {P : Type*} [TopologicalSpace P] {U : Set P}
    (g : P → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (hg_cont : ∀ α i j, ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source)) :
    ContinuousOn (fun p ↦ riemannianTotalVolume I (WithMetric (g p))) U := by
  borelize M
  exact (TauCeti.continuousOn_riemannianTotalVolume
    (fun p ↦ (g p).toContinuousRiemannianMetric) hg_cont).congr fun p _ ↦
      WithMetric.riemannianTotalVolume_eq (g p)

/-- First variation of `τ ↦ riemannianTotalVolume I (WithMetric (g τ))` on a compact `C¹`
manifold. -/
theorem hasDerivWithinAt_riemannianTotalVolume [IsManifold I 1 M] [T2Space M]
    {s U : Set ℝ} {t : ℝ}
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)}
    (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w) (h τ x v w) s τ)
    (htr_cont : ContinuousOn (fun q : ℝ × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
        bilinFormTrace (h q.1 q.2)) (U ×ˢ univ)) :
    HasDerivWithinAt
      (fun τ ↦ riemannianTotalVolume I (WithMetric (g τ)))
      (2⁻¹ * ∫ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          bilinFormTrace (h t x.ofWithMetric))
        ∂riemannianVolume I (WithMetric (g t)))
      s t := by
  borelize M
  have hmain := TauCeti.hasDerivWithinAt_riemannianTotalVolume
    (fun τ ↦ (g τ).toContinuousRiemannianMetric) (h := h) hs ht hU hg_cont hg_deriv htr_cont
  exact (hmain.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ ↦ WithMetric.riemannianTotalVolume_eq (g τ))
    (WithMetric.riemannianTotalVolume_eq (g t))).congr_deriv <|
      congrArg (2⁻¹ * ·) (WithMetric.integral_comp_ofWithMetric (g t) fun x ↦
        letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(g t).toRiemannianMetric⟩;
        bilinFormTrace (h t x)).symm

/-- Two-sided first variation of `τ ↦ riemannianTotalVolume I (WithMetric (g τ))` on a compact `C¹`
manifold. -/
theorem hasDerivAt_riemannianTotalVolume [IsManifold I 1 M] [T2Space M] {U : Set ℝ} {t : ℝ}
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x)} (hU : U ∈ 𝓝 t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivAt (fun τ' ↦ (g τ').inner x v w) (h τ x v w) τ)
    (htr_cont : ContinuousOn (fun q : ℝ × M ↦
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
        bilinFormTrace (h q.1 q.2)) (U ×ˢ univ)) :
    HasDerivAt
      (fun τ ↦ riemannianTotalVolume I (WithMetric (g τ)))
      (2⁻¹ * ∫ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          bilinFormTrace (h t x.ofWithMetric))
        ∂riemannianVolume I (WithMetric (g t)))
      t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_riemannianTotalVolume g convex_univ (mem_univ t) (by rwa [nhdsWithin_univ])
      hg_cont (fun τ hτ x v w ↦ (hg_deriv τ hτ x v w).hasDerivWithinAt) htr_cont

/-- **Derivative of total volume along a path of constantly rescaled metrics (power form).**
For a fixed metric `g₀` on a compact manifold of real dimension `N` and a positive scale function
`c : ℝ → ℝ` with within-`s` derivative `c'` at `t`,

`∂_τ Vol(c(τ) g₀) = (N / 2) c(t) ^ (N / 2 - 1) c' Vol(g₀)`. -/
theorem hasDerivWithinAt_riemannianTotalVolume_rescale_const' [IsManifold I 1 M]
    {g₀ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
    {c : ℝ → ℝ} {c' : ℝ} {s : Set ℝ} {t : ℝ} (hc_pos : ∀ τ, 0 < c τ)
    (hc_deriv : HasDerivWithinAt c c' s t) :
    HasDerivWithinAt
      (fun τ ↦ riemannianTotalVolume I
        (WithMetric (g₀.rescale (fun _ ↦ c τ) contMDiff_const (fun _ ↦ hc_pos τ))))
      (((Module.finrank ℝ E : ℝ) / 2 * c t ^ ((Module.finrank ℝ E : ℝ) / 2 - 1) * c') *
        riemannianTotalVolume I (WithMetric g₀))
      s t := by
  have hd := (hc_deriv.rpow_const (p := (Module.finrank ℝ E : ℝ) / 2)
    (Or.inl (hc_pos t).ne')).mul_const (riemannianTotalVolume I (WithMetric g₀))
  exact (hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ ↦ riemannianTotalVolume_rescale_const (hc_pos τ))
    (riemannianTotalVolume_rescale_const (hc_pos t))).congr_deriv (by ring)

/-- **Derivative of total volume along a path of constantly rescaled metrics (logarithmic form).**
For `g_τ = c(τ) g₀` with `c(τ) > 0` and within-`s` derivative `c'` at `t` in real dimension `N`,

`∂_τ Vol(c(τ) g₀) = (N c' / (2 c(t))) Vol(c(t) g₀)`,

matching `½ tr_{c(t) g₀}(c' g₀) Vol(c(t) g₀)` since `tr_{c g₀}(c' g₀) = N c' / c`. -/
theorem hasDerivWithinAt_riemannianTotalVolume_rescale_const [IsManifold I 1 M]
    {g₀ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
    {c : ℝ → ℝ} {c' : ℝ} {s : Set ℝ} {t : ℝ} (hc_pos : ∀ τ, 0 < c τ)
    (hc_deriv : HasDerivWithinAt c c' s t) :
    HasDerivWithinAt
      (fun τ ↦ riemannianTotalVolume I
        (WithMetric (g₀.rescale (fun _ ↦ c τ) contMDiff_const (fun _ ↦ hc_pos τ))))
      (((Module.finrank ℝ E : ℝ) * c' / (2 * c t)) *
        riemannianTotalVolume I
          (WithMetric (g₀.rescale (fun _ ↦ c t) contMDiff_const (fun _ ↦ hc_pos t))))
      s t := by
  refine (hasDerivWithinAt_riemannianTotalVolume_rescale_const' (g₀ := g₀) hc_pos
    hc_deriv).congr_deriv ?_
  rw [riemannianTotalVolume_rescale_const (hc_pos t)]
  have hpow : c t ^ ((Module.finrank ℝ E : ℝ) / 2 - 1) * c t =
      c t ^ ((Module.finrank ℝ E : ℝ) / 2) := by
    rw [← Real.rpow_add_one (hc_pos t).ne', sub_add_cancel]
  have hct : c t ≠ 0 := (hc_pos t).ne'
  calc ((Module.finrank ℝ E : ℝ) / 2 * c t ^ ((Module.finrank ℝ E : ℝ) / 2 - 1) * c') *
        riemannianTotalVolume I (WithMetric g₀)
      = ((Module.finrank ℝ E : ℝ) * c' / (2 * c t)) *
          ((c t ^ ((Module.finrank ℝ E : ℝ) / 2 - 1) * c t) *
            riemannianTotalVolume I (WithMetric g₀)) := by
        field_simp [hct]
    _ = ((Module.finrank ℝ E : ℝ) * c' / (2 * c t)) *
          (c t ^ ((Module.finrank ℝ E : ℝ) / 2) * riemannianTotalVolume I (WithMetric g₀)) := by
        rw [hpow]

end General

section RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] {s U : Set ℝ} {t : ℝ}

/-- Variation of `τ ↦ riemannianTotalVolume I (WithMetric (g τ))` along a Ricci flow on a compact
manifold: `∂_τ Vol(g_τ) = -∫ Scal(g_t) dV_{g_t}`. -/
theorem hasDerivWithinAt_riemannianTotalVolume_of_ricciFlow
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s τ)
    (hscal_cont : ContinuousOn (fun q : ℝ × M ↦ (g q.1).scalarCurvature q.2) (U ×ˢ univ)) :
    HasDerivWithinAt
      (fun τ ↦ riemannianTotalVolume I (WithMetric (g τ)))
      (-∫ x, (g t).scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric (g t)))
      s t := by
  borelize M
  have hmain := TauCeti.hasDerivWithinAt_riemannianTotalVolume_of_ricciFlow g hs ht hU hg_cont
    hg_deriv hscal_cont
  exact (hmain.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ ↦ WithMetric.riemannianTotalVolume_eq (g τ))
    (WithMetric.riemannianTotalVolume_eq (g t))).congr_deriv <|
      congrArg Neg.neg (WithMetric.integral_comp_ofWithMetric (g t) (g t).scalarCurvature).symm

/-- Two-sided variation of `τ ↦ riemannianTotalVolume I (WithMetric (g τ))` along a Ricci flow on a
compact manifold. -/
theorem hasDerivAt_riemannianTotalVolume_of_ricciFlow
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (hU : U ∈ 𝓝 t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivAt (fun τ' ↦ (g τ').inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) τ)
    (hscal_cont : ContinuousOn (fun q : ℝ × M ↦ (g q.1).scalarCurvature q.2) (U ×ˢ univ)) :
    HasDerivAt
      (fun τ ↦ riemannianTotalVolume I (WithMetric (g τ)))
      (-∫ x, (g t).scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric (g t)))
      t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_riemannianTotalVolume_of_ricciFlow g convex_univ (mem_univ t)
      (by rwa [nhdsWithin_univ]) hg_cont
      (fun τ hτ x v w ↦ (hg_deriv τ hτ x v w).hasDerivWithinAt) hscal_cont

/-- **Conservation of total volume along a volume-normalized Ricci flow.** On a nonempty compact
smooth manifold of positive real dimension `n`, if `g_τ` satisfies the volume-normalized Ricci flow
equation `∂_τ g = -2 Ric(g) + (2 / n) r(g) g` within `s` on `U ∈ 𝓝[s] t`, where
`r(g) = Vol(g)⁻¹ ∫ Scal(g) dV_g` is the average scalar curvature, then
`τ ↦ riemannianTotalVolume I (WithMetric (g τ))` has within-`s` derivative `0` at `t`. -/
theorem hasDerivWithinAt_riemannianTotalVolume_of_normalizedRicciFlow [Nonempty M]
    (hn : Module.finrank ℝ E ≠ 0)
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hs : Convex ℝ s) (ht : t ∈ s) (hU : U ∈ 𝓝[s] t)
    (hg_cont : ∀ α i j, ContinuousOn (fun q : ℝ × M ↦ (g q.1).inner q.2
        (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
      (U ×ˢ (chartAt H α).source))
    (hg_deriv : ∀ τ ∈ U, ∀ x v w,
      HasDerivWithinAt (fun τ' ↦ (g τ').inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g τ).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w) +
          (2 / (Module.finrank ℝ E : ℝ)) *
            ((riemannianTotalVolume I (WithMetric (g τ)))⁻¹ *
              ∫ y, (g τ).scalarCurvature y.ofWithMetric
                ∂riemannianVolume I (WithMetric (g τ))) *
            (g τ).inner x v w) s τ)
    (hscal_cont : ContinuousOn (fun q : ℝ × M ↦ (g q.1).scalarCurvature q.2) (U ×ˢ univ)) :
    HasDerivWithinAt (fun τ ↦ riemannianTotalVolume I (WithMetric (g τ))) 0 s t := by
  let rbar : ℝ → ℝ := fun τ ↦
    (riemannianTotalVolume I (WithMetric (g τ)))⁻¹ *
      ∫ y, (g τ).scalarCurvature y.ofWithMetric ∂riemannianVolume I (WithMetric (g τ))
  have hrbar_cont : ContinuousOn rbar U :=
    ((continuousOn_riemannianTotalVolume g hg_cont).inv₀ fun τ _ ↦
      (riemannianTotalVolume_pos (I := I) (M := WithMetric (g τ))).ne').mul
      (continuousOn_integral_riemannianVolume g
        (f := fun τ y ↦ (g τ).scalarCurvature y) hg_cont hscal_cont)
  let h : ℝ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x) := fun τ x ↦
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
    (-2 : ℝ) • (CovariantDerivative.leviCivitaConnection I M).ricciTensor x +
      ((2 / (Module.finrank ℝ E : ℝ)) * rbar τ) • innerₗ (TangentSpace I x)
  have hnR : (Module.finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have htr (τ : ℝ) (x : M) :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩;
        bilinFormTrace (h τ x)) = -2 * (g τ).scalarCurvature x + 2 * rbar τ := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g τ).toRiemannianMetric⟩
    have hn' : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := (rfl)
    rw [map_add, map_smul, map_smul, ContMDiffRiemannianMetric.scalarCurvature_def,
      CovariantDerivative.scalarCurvature_apply, bilinFormTrace_inner, smul_eq_mul, smul_eq_mul,
      hn']
    field_simp [hnR]
  have htr_cont : ContinuousOn (fun q : ℝ × M ↦
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g q.1).toRiemannianMetric⟩;
      bilinFormTrace (h q.1 q.2)) (U ×ˢ univ) :=
    (((continuousOn_const (c := (-2 : ℝ))).mul hscal_cont).add
      ((continuousOn_const (c := (2 : ℝ))).mul
        (hrbar_cont.comp continuousOn_fst fun _ hq ↦ hq.1))).congr fun q _ ↦ htr q.1 q.2
  refine (hasDerivWithinAt_riemannianTotalVolume g (h := h) hs ht hU hg_cont hg_deriv
    htr_cont).congr_deriv ?_
  have hint : ∫ x : WithMetric (g t),
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(g t).toRiemannianMetric⟩;
        bilinFormTrace (h t x.ofWithMetric)) ∂riemannianVolume I (WithMetric (g t)) =
      ∫ x : WithMetric (g t), (-2 * (g t).scalarCurvature x.ofWithMetric + 2 * rbar t)
        ∂riemannianVolume I (WithMetric (g t)) :=
    integral_congr_ae (ae_of_all _ fun x ↦ htr t x.ofWithMetric)
  have hsc_int : Integrable (fun x : WithMetric (g t) ↦
      -2 * (g t).scalarCurvature x.ofWithMetric) (riemannianVolume I (WithMetric (g t))) :=
    (continuous_const.mul ((g t).continuous_scalarCurvature.comp
      continuous_ofWithMetric)).integrable_of_hasCompactSupport (.of_compactSpace _)
  rw [hint, integral_add hsc_int (integrable_const _), integral_const_mul, integral_const,
    smul_eq_mul, ← riemannianTotalVolume_def]
  dsimp only [rbar]
  field_simp [(riemannianTotalVolume_pos (I := I) (M := WithMetric (g t))).ne']
  ring

end RicciFlow

end WithMetric

end TauCeti

/-! ### Continuity in the chart `Cᵏ` metric topologies -/

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

/-- A family of smooth Riemannian metrics that is `ContinuousOn` in `chartCkTopology k` (for any
`k : ℕ∞`, including `k = 0`, `k = 2`, and `k = ⊤`) has jointly continuous chart-frame inner
products on `U × (chartAt H α).source` for every chart `α`. This discharges the `hg_cont`
hypothesis of the Riemannian integral and total-volume variation theorems. -/
theorem continuousOn_inner_chartLocalFrame_chartCk (k : ℕ∞)
    {P : Type*} [TopologicalSpace P] {U : Set P}
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} :
    letI := chartCkTopology (I := I) (M := M) k
    ContinuousOn g U → ∀ α i j,
      ContinuousOn (fun q : P × M ↦ (g q.1).inner q.2
          (chartLocalFrame (I := I) α i q.2) (chartLocalFrame (I := I) α j q.2))
        (U ×ˢ (chartAt H α).source) := by
  let _ := chartCkTopology (I := I) (M := M) k
  intro hg α i j q hq
  have hqsrc : q.2 ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hq.2
  have hz₀ : extChartAt I α q.2 ∈ (extChartAt I α).target := (extChartAt I α).mapsTo hqsrc
  have h0 := continuousAt_iteratedFDeriv_chartMetric (I := I) (M := M) k α (m := 0) (by simp)
    (g q.1) hz₀
  have heval : ContinuousAt
      (fun r : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) × E ↦
        iteratedFDeriv ℝ 0 (r.1.toNondegenerateMetric.chartMetric α) r.2 0
          (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))
      (g q.1, extChartAt I α q.2) := by
    have h1 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 ↦ E)
      (E →L[ℝ] E →L[ℝ] ℝ) 0).continuous.continuousAt).comp h0
    have h2 := ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)
      (Module.finBasis ℝ E i)).continuous.continuousAt).comp h1
    exact ((ContinuousLinearMap.apply ℝ ℝ
      (Module.finBasis ℝ E j)).continuous.continuousAt).comp h2
  have hfst : ContinuousWithinAt (fun r : P × M ↦ g r.1) (U ×ˢ (chartAt H α).source) q :=
    (hg q.1 hq.1).comp continuousWithinAt_fst mapsTo_fst_prod
  have hsnd : ContinuousWithinAt (fun r : P × M ↦ extChartAt I α r.2)
      (U ×ˢ (chartAt H α).source) q :=
    ContinuousAt.comp_continuousWithinAt (f := Prod.snd)
      (continuousAt_extChartAt' hqsrc) continuousWithinAt_snd
  have heq (r : P × M) (hr : r ∈ U ×ˢ (chartAt H α).source) :
      (g r.1).inner r.2 (chartLocalFrame (I := I) α i r.2) (chartLocalFrame (I := I) α j r.2) =
        iteratedFDeriv ℝ 0 ((g r.1).toNondegenerateMetric.chartMetric α) (extChartAt I α r.2) 0
          (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) := by
    have hrsrc : r.2 ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hr.2
    rw [iteratedFDeriv_zero_apply,
      (g r.1).toNondegenerateMetric.chartMetric_extChartAt_apply_basis (Module.finBasis ℝ E) hrsrc,
      toNondegenerateMetric_apply, ← chartLocalFrame_def (I := I)]
  exact (ContinuousAt.comp₂_continuousWithinAt
    (g := fun r : P × M ↦ g r.1) (h := fun r : P × M ↦ extChartAt I α r.2)
    heval hfst hsnd).congr_of_mem heq hq

/-- On a compact smooth boundaryless manifold, a Riemannian integral `p ↦ ∫ f_p dV_{g_p}` varies
continuously whenever `p ↦ g_p` is continuous in `chartCkTopology k` (for any `k : ℕ∞`) and `f` is
jointly continuous. -/
theorem continuous_integral_riemannianVolume_chartCk [T2Space M] [CompactSpace M] (k : ℕ∞)
    {P : Type*} [TopologicalSpace P] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {f : P → M → F} :
    letI := chartCkTopology (I := I) (M := M) k
    Continuous g → Continuous (Function.uncurry f) →
      Continuous (fun p ↦ ∫ x, f p x.ofWithMetric
        ∂TauCeti.riemannianVolume I (TauCeti.WithMetric (g p))) := by
  let _ := chartCkTopology (I := I) (M := M) k
  intro hg hf
  exact continuousOn_univ.1 <|
    TauCeti.WithMetric.continuousOn_integral_riemannianVolume g
      (continuousOn_inner_chartLocalFrame_chartCk k hg.continuousOn) hf.continuousOn

/-- **Continuity of total Riemannian volume in every chart `Cᵏ` topology.** On a compact smooth
boundaryless manifold, `g ↦ Vol(WithMetric g)` is continuous in `chartCkTopology k` for every
`k : ℕ∞` (and hence in `chartC2Topology` and `chartCInftyTopology`). -/
@[fun_prop]
theorem continuous_riemannianTotalVolume_chartCk [T2Space M] [CompactSpace M] (k : ℕ∞) :
    letI := chartCkTopology (I := I) (M := M) k
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      TauCeti.riemannianTotalVolume I (TauCeti.WithMetric g)) := by
  let _ := chartCkTopology (I := I) (M := M) k
  exact continuousOn_univ.1 <|
    TauCeti.WithMetric.continuousOn_riemannianTotalVolume id
      (continuousOn_inner_chartLocalFrame_chartCk k continuousOn_id)

end Bundle.ContMDiffRiemannianMetric
