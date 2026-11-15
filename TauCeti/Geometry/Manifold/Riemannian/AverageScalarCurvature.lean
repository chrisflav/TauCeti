/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Topology
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric
import TauCeti.Geometry.Manifold.Riemannian.Scaling
import TauCeti.Geometry.Manifold.Riemannian.TotalCurvature
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.IntegralVariation

/-!
# Average scalar curvature of a compact Riemannian manifold

For a smooth Riemannian metric `g` on a compact Hausdorff manifold `M`, the **average scalar
curvature**

`r(g) = Vol(g)⁻¹ ∫ Scal(g) dV_g`

is the volume mean of scalar curvature against the Riemannian volume measure of the metric-indexed
copy `TauCeti.WithMetric g`. It is the nonlocal coefficient `(2 / n) r(g) g` that keeps total
volume constant along Hamilton's volume-normalized Ricci flow `∂_t g = -2 Ric(g) + (2 / n) r(g) g`.

Under constant rescaling `c g` (`c > 0`), both the volume density and the total volume scale by
`c ^ (N / 2)` while `Scal(c g) = c⁻¹ Scal(g)`, so those volume factors cancel in every dimension
and `r(c g) = c⁻¹ r(g)`. On a nonempty manifold, a metric of constant scalar curvature `κ` has
`r(g) = κ`; in particular an Einstein metric `Ric(g) = c g` has `r(g) = N c`, so the normalized
Ricci-flow drift `(2 / N) r(g) g = 2 c g` cancels `-2 Ric(g)`. On a closed surface (`N = 2`), the
product `r(g) Vol(g) = ∫ Scal(g) dV_g` is conformally invariant. Finally, `g ↦ r(g)` is continuous
in both the chart `C^2` and chart `C^∞` topologies on smooth metrics.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.averageScalarCurvature`: the volume mean
  `Vol(g)⁻¹ * ∫ Scal(g) dV_g`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.averageScalarCurvature_mul_riemannianTotalVolume`:
  `r(g) * Vol(g) = ∫ Scal(g) dV_g`.
* `Bundle.ContMDiffRiemannianMetric.averageScalarCurvature_rescale_const`:
  `r(c g) = c⁻¹ * r(g)` for `c > 0`.
* `Bundle.ContMDiffRiemannianMetric.averageScalarCurvature_eq_of_scalarCurvature_eq`,
  `Bundle.ContMDiffRiemannianMetric.averageScalarCurvature_eq_of_ricciTensor_eq_smul_inner`,
  `Bundle.ContMDiffRiemannianMetric.averageScalarCurvature_eq_zero_of_finrank_le_one`: evaluation
  for constant-scalar-curvature, Einstein, and low-dimensional metrics.
* `averageScalarCurvature_mul_riemannianTotalVolume_rescale_of_finrank_eq_two` (in
  `Bundle.ContMDiffRiemannianMetric`): conformal invariance of `r(g) * Vol(g)` on a closed
  surface.
* `Bundle.ContMDiffRiemannianMetric.continuous_averageScalarCurvature_chartC2`,
  `Bundle.ContMDiffRiemannianMetric.continuous_averageScalarCurvature_chartCInfty`: continuity of
  `g ↦ r(g)` in the chart `C^2` and `C^∞` topologies.

## References

* R. S. Hamilton, *Three-manifolds with positive Ricci curvature*, J. Differential Geom. 17 (1982),
  255–306, Section 3.
* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Section 1.2.3.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Chapter 4.
-/

public section

open Bundle Function MeasureTheory TauCeti
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- The **average scalar curvature** `r(g) = Vol(g)⁻¹ ∫ Scal(g) dV_g` of a smooth Riemannian
metric `g` on a compact manifold `M`. On the empty manifold both `Vol(g)` and the integral vanish,
so `r(g) = 0`. -/
def averageScalarCurvature : ℝ :=
  (riemannianTotalVolume I (WithMetric g))⁻¹ *
    ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g)

/-- Unfolds `Bundle.ContMDiffRiemannianMetric.averageScalarCurvature`. -/
theorem averageScalarCurvature_def :
    g.averageScalarCurvature =
      (riemannianTotalVolume I (WithMetric g))⁻¹ *
        ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) :=
  (rfl)

/-- When `M` carries its Borel `σ`-algebra, `g.averageScalarCurvature` is computed directly against
the Riemannian volume of `M` with `g` installed. -/
theorem averageScalarCurvature_eq_of_borelSpace [MeasurableSpace M] [BorelSpace M] :
    g.averageScalarCurvature =
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
      (riemannianTotalVolume I M)⁻¹ * ∫ x, g.scalarCurvature x ∂riemannianVolume I M := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have hvol : riemannianTotalVolume I (WithMetric g) = riemannianTotalVolume I M :=
    (WithMetric.homeomorph g).riemannianTotalVolume_eq fun x v w ↦ by
      rw [WithMetric.coe_homeomorph]
      exact (WithMetric.inner_def x v w).symm
  rw [averageScalarCurvature_def, hvol, WithMetric.integral_comp_ofWithMetric g g.scalarCurvature]

/-- Multiplying the average scalar curvature by the total volume recovers the total scalar
curvature `∫ Scal(g) dV_g`, including on the empty manifold. -/
theorem averageScalarCurvature_mul_riemannianTotalVolume :
    g.averageScalarCurvature * riemannianTotalVolume I (WithMetric g) =
      ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · have : IsEmpty (WithMetric g) := (WithMetric.equiv g).isEmpty
    simp [averageScalarCurvature_def, integral_of_isEmpty]
  · have hV : 0 < riemannianTotalVolume I (WithMetric g) := riemannianTotalVolume_pos
    rw [averageScalarCurvature_def, mul_comm, ← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]

/-- **Scaling of average scalar curvature.** Multiplying a smooth metric by a positive constant `c`
multiplies its average scalar curvature by `c⁻¹`, in every dimension. -/
@[simp]
theorem averageScalarCurvature_rescale_const {c : ℝ} (hc : 0 < c) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).averageScalarCurvature =
      c⁻¹ * g.averageScalarCurvature := by
  have hc0 : c ^ ((Module.finrank ℝ E : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hc ((Module.finrank ℝ E : ℝ) / 2)).ne'
  rw [averageScalarCurvature_def, averageScalarCurvature_def,
    WithMetric.riemannianTotalVolume_rescale_const,
    WithMetric.integral_riemannianVolume_rescale_const]
  simp only [scalarCurvature_rescale_const, integral_const_mul, mul_inv]
  calc (c ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ * (riemannianTotalVolume I (WithMetric g))⁻¹ *
        (c ^ ((Module.finrank ℝ E : ℝ) / 2) *
          (c⁻¹ * ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g)))
      = (c ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
          (c ^ ((Module.finrank ℝ E : ℝ) / 2) *
            (c⁻¹ * ((riemannianTotalVolume I (WithMetric g))⁻¹ *
              ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g)))) := by
          ring
    _ = c⁻¹ * ((riemannianTotalVolume I (WithMetric g))⁻¹ *
          ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g)) :=
        inv_mul_cancel_left₀ hc0 _

/-- If `g` has constant scalar curvature `κ` on a nonempty compact manifold, its average scalar
curvature is `κ`. -/
theorem averageScalarCurvature_eq_of_scalarCurvature_eq [Nonempty M] {κ : ℝ}
    (h : ∀ x, g.scalarCurvature x = κ) :
    g.averageScalarCurvature = κ := by
  have hV : 0 < riemannianTotalVolume I (WithMetric g) := riemannianTotalVolume_pos
  simp only [averageScalarCurvature_def, h, integral_const, smul_eq_mul,
    ← riemannianTotalVolume_def, inv_mul_cancel_left₀ hV.ne']

/-- **Average scalar curvature of an Einstein metric.** On a nonempty compact manifold of real
dimension `N`, if `Ric(g) = c g` everywhere then `r(g) = N c`. -/
theorem averageScalarCurvature_eq_of_ricciTensor_eq_smul_inner [Nonempty M] {c : ℝ}
    (h : ∀ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x =
        c • innerₗ (TangentSpace I x))) :
    g.averageScalarCurvature = (Module.finrank ℝ E : ℝ) * c := by
  refine g.averageScalarCurvature_eq_of_scalarCurvature_eq fun x ↦ ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hn : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := (rfl)
  rw [scalarCurvature_def,
    (CovariantDerivative.leviCivitaConnection I M).scalarCurvature_eq_of_ricciTensor_eq_smul_inner
      x c (h x),
    hn]

/-- In dimension at most one, the average scalar curvature vanishes. -/
@[simp]
theorem averageScalarCurvature_eq_zero_of_finrank_le_one (hE : Module.finrank ℝ E ≤ 1) :
    g.averageScalarCurvature = 0 := by
  have h0 (x : M) : g.scalarCurvature x = 0 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    rw [scalarCurvature_def]
    exact
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature_eq_zero_of_ricciTensor_eq_zero
        x ((CovariantDerivative.leviCivitaConnection I M).ricciTensor_eq_zero_of_finrank_le_one
          x hE)
  simp [averageScalarCurvature_def, h0]

/-- **Conformal invariance of `r(g) Vol(g)` on a closed surface.** In real dimension two on a
compact boundaryless manifold, `r(f g) * Vol(f g) = r(g) * Vol(g)` for every smooth positive
conformal factor `f`. -/
theorem averageScalarCurvature_mul_riemannianTotalVolume_rescale_of_finrank_eq_two
    [I.Boundaryless] (hE : Module.finrank ℝ E = 2) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_pos : ∀ x, 0 < f x) :
    (g.rescale f hf hf_pos).averageScalarCurvature *
        riemannianTotalVolume I (WithMetric (g.rescale f hf hf_pos)) =
      g.averageScalarCurvature * riemannianTotalVolume I (WithMetric g) := by
  rw [averageScalarCurvature_mul_riemannianTotalVolume,
    averageScalarCurvature_mul_riemannianTotalVolume,
    g.integral_scalarCurvature_rescale_of_finrank_eq_two hE hf hf_pos]

section Topology

variable [I.Boundaryless]

open scoped TauCeti.MetricC2 in
/-- **Continuity of average scalar curvature in the chart `C^2` topology.** On a compact
boundaryless smooth manifold, `g ↦ r(g)` is continuous for `chartC2Topology`. -/
theorem continuous_averageScalarCurvature_chartC2 :
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      g.averageScalarCurvature) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · have h0 (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
        g.averageScalarCurvature = 0 := by
      have : IsEmpty (WithMetric g) := (WithMetric.equiv g).isEmpty
      simp [averageScalarCurvature_def, integral_of_isEmpty]
    simpa only [h0] using continuous_const
  · exact (continuous_riemannianTotalVolume_chartC2.inv₀ fun _ ↦
      riemannianTotalVolume_pos.ne').mul
      (continuous_integral_riemannianVolume_chartCk 2 continuous_scalarCurvature_chartC2)

open scoped TauCeti.MetricCInfty in
/-- **Continuity of average scalar curvature in the chart `C^∞` topology.** On a compact
boundaryless smooth manifold, `g ↦ r(g)` is continuous for `chartCInftyTopology`. -/
theorem continuous_averageScalarCurvature_chartCInfty :
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      g.averageScalarCurvature) :=
  @Continuous.comp _ _ _ chartCInftyTopology chartC2Topology _ _ _
    continuous_averageScalarCurvature_chartC2
    (continuous_id_of_le chartCInftyTopology_le_chartC2Topology)

end Topology

end Bundle.ContMDiffRiemannianMetric
