/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
public import TauCeti.Geometry.RicciFlow.StandardCap.Metric

import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
import TauCeti.Geometry.RicciFlow.StandardCap.Polar
import TauCeti.Geometry.RicciFlow.StandardCap.SectionalCurvature

/-!
# Curvature of the smooth standard cap metric

This file computes the curvature of the smooth standard cap metric
`TauCeti.IsStandardCapProfile.metric` on any finite-dimensional real inner product space `V`,
covering both the origin (via the round-sphere tip isometry) and the punctured space (via polar
coordinates and the warped-product formulas).

## Main results

In the namespace `TauCeti.IsStandardCapProfile`:

* `isConstantCurvatureTensor_restrictOpenTangentSpace_ball`: on any open ball `Metric.ball 0 r₀`
  where `f(r) = 2 sin (r / 2)`, the restricted standard cap metric has constant curvature tensor
  `1 / 4`.
* `hasSectionalCurvatureAt_metric_of_mem_ball` and `hasSectionalCurvatureAt_metric_zero`: every
  tangent two-plane in the spherical tip ball, and in particular at `0`, has sectional curvature
  `1 / 4`.
* `scalarCurvature_metric_of_mem_ball` and `scalarCurvature_metric_zero`: the scalar curvature on
  the spherical tip ball is `dim(V) (dim(V) - 1) / 4`.
* `scalarCurvature_metric_of_ne_zero`: away from `0`, the scalar curvature is given by the
  warped-product formula in terms of `f ‖x‖`, `f' ‖x‖`, and `f'' ‖x‖`.
* `scalarCurvature_metric_of_eq_sqrt_two` and `exists_scalarCurvature_metric_eq_cylinder`: outside
  a sufficiently large radius, the scalar curvature equals `(dim(V) - 1) (dim(V) - 2) / 2` (in
  particular `1` when `dim(V) = 3`).
* `sectionalCurvature_metric_nonneg`: the standard cap metric has nonnegative sectional curvature
  on every tangent pair at every point of `V`.
* `scalarCurvature_metric_nonneg`: the standard cap metric has nonnegative scalar curvature
  everywhere on `V`.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics Monographs 3
  (2007), Definition 12.1.
* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7, Proposition 42.
-/

public noncomputable section

open Bundle CovariantDerivative Metric Real Set TopologicalSpace
open TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

include hf

omit hf in
private theorem finrank_prodL2_real_eq_succ {n : ℕ} (hn : Module.finrank ℝ V = n + 1) :
    Module.finrank ℝ (WithLp 2 (V × ℝ)) = (n + 1) + 1 := by
  rw [(WithLp.linearEquiv 2 ℝ (V × ℝ)).finrank_eq, Module.finrank_prod, hn, Module.finrank_self]

/-- On any open ball `Metric.ball 0 r₀` where `f(r) = 2 sin (r / 2)`, the restricted standard cap
metric has constant curvature tensor `1 / 4`. -/
theorem isConstantCurvatureTensor_restrictOpenTangentSpace_ball
    {r₀ : ℝ} (htip : ∀ r ∈ Ico 0 r₀, f r = 2 * sin (r / 2)) :
    ((hf.metric V).restrictOpenTangentSpace
      ⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩).IsConstantCurvatureTensor (1 / 4) := by
  let B : Opens V := ⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩
  rw [ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff]
  let _ : RiemannianBundle (fun x : B ↦ TangentSpace 𝓘(ℝ, V) x) :=
    ⟨((hf.metric V).restrictOpenTangentSpace B).toRiemannianMetric⟩
  intro x w u v
  cases hn : Module.finrank ℝ V with
  | zero =>
    have : Subsingleton V := Module.finrank_zero_iff.1 hn
    apply (tangentSpaceOpenEquiv (I := 𝓘(ℝ, V)) x).injective
    apply (NormedSpace.fromTangentSpace (x : V)).injective
    exact Subsingleton.elim _ _
  | succ n =>
    have : Fact (Module.finrank ℝ (WithLp 2 (V × ℝ)) = (n + 1) + 1) :=
      ⟨finrank_prodL2_real_eq_succ hn⟩
    let _ : RiemannianBundle
        (fun p : Metric.sphere (0 : WithLp 2 (V × ℝ)) 1 ↦ TangentSpace (𝓡 (n + 1)) p) :=
      ⟨(sphereRoundMetricOfRadius (E := WithLp 2 (V × ℝ)) (n := n + 1) 2
        two_pos).toRiemannianMetric⟩
    have hloc := hf.isLocalRiemannianIsometry_tip (V := V) (n := n) htip
    have hconst :=
      (isConstantCurvatureTensor_sphereRoundMetricOfRadius (E := WithLp 2 (V × ℝ)) (n := n + 1)
        (r := 2) two_pos).curvatureTensor_eq _ _
    obtain ⟨e, he⟩ := hloc.exists_linearIsometryEquiv_eq_mfderiv x
    apply e.injective
    rw [he, hloc.mfderiv_curvatureTensor, hconst, map_smul, map_sub, map_smul, map_smul,
      he, he, hloc.inner_mfderiv, hloc.inner_mfderiv]
    norm_num

/-- Every tangent two-plane at a point of a spherical tip ball `Metric.ball 0 r₀` has sectional
curvature `1 / 4`. -/
theorem hasSectionalCurvatureAt_metric_of_mem_ball
    {r₀ : ℝ} (htip : ∀ r ∈ Ico 0 r₀, f r = 2 * sin (r / 2))
    {x : V} (hx : x ∈ Metric.ball (0 : V) r₀) :
    letI : RiemannianBundle (fun y : V ↦ TangentSpace 𝓘(ℝ, V) y) :=
      ⟨(hf.metric V).toRiemannianMetric⟩
    (leviCivitaConnection 𝓘(ℝ, V) V).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) x (1 / 4) := by
  let B : Opens V := ⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩
  let _ : RiemannianBundle (fun y : V ↦ TangentSpace 𝓘(ℝ, V) y) :=
    ⟨(hf.metric V).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun y : B ↦ TangentSpace 𝓘(ℝ, V) y) :=
    ⟨((hf.metric V).restrictOpenTangentSpace B).toRiemannianMetric⟩
  have hloc := (hf.metric V).isLocalRiemannianIsometry_restrictOpenTangentSpace B
  have hB : (leviCivitaConnection 𝓘(ℝ, V) B).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) ⟨x, hx⟩ (1 / 4) :=
    hasSectionalCurvatureAt_of_curvatureTensor_eq_smul_inner_sub _ _ _ _
      ((hf.isConstantCurvatureTensor_restrictOpenTangentSpace_ball htip).curvatureTensor_eq
        _ _ ⟨x, hx⟩)
  obtain ⟨e, he⟩ := hloc.exists_linearIsometryEquiv_eq_mfderiv ⟨x, hx⟩
  rw [hasSectionalCurvatureAt_iff]
  intro u v huv
  obtain ⟨u', rfl⟩ := e.surjective u
  obtain ⟨v', rfl⟩ := e.surjective v
  have huv' : LinearIndependent ℝ ![u', v'] := by
    have hcomp : (e.toLinearEquiv : TangentSpace 𝓘(ℝ, V) (⟨x, hx⟩ : B) →ₗ[ℝ]
        TangentSpace 𝓘(ℝ, V) x) ∘ ![u', v'] = ![e u', e v'] := by
      ext i; fin_cases i <;> rfl
    rw [← hcomp] at huv
    exact (e.toLinearEquiv.toLinearMap.linearIndependent_iff (LinearEquiv.ker _)).1 huv
  rw [he u', he v']
  exact (hloc.sectionalCurvature_mfderiv ⟨x, hx⟩ u' v').trans
    ((hasSectionalCurvatureAt_iff ..).1 hB u' v' huv')

/-- Every tangent two-plane at the origin `0 ∈ V` has sectional curvature `1 / 4`. -/
theorem hasSectionalCurvatureAt_metric_zero :
    letI : RiemannianBundle (fun y : V ↦ TangentSpace 𝓘(ℝ, V) y) :=
      ⟨(hf.metric V).toRiemannianMetric⟩
    (leviCivitaConnection 𝓘(ℝ, V) V).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) (0 : V) (1 / 4) := by
  obtain ⟨r₀, hr₀, htip⟩ := hf.exists_eq_two_mul_sin
  exact hf.hasSectionalCurvatureAt_metric_of_mem_ball htip (Metric.mem_ball_self hr₀)

/-- On any spherical tip ball `Metric.ball 0 r₀`, the scalar curvature of `hf.metric V` is
`dim(V) (dim(V) - 1) / 4`. -/
theorem scalarCurvature_metric_of_mem_ball
    {r₀ : ℝ} (htip : ∀ r ∈ Ico 0 r₀, f r = 2 * sin (r / 2))
    {x : V} (hx : x ∈ Metric.ball (0 : V) r₀) :
    (hf.metric V).scalarCurvature x =
      (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1) / 4 := by
  let B : Opens V := ⟨Metric.ball (0 : V) r₀, Metric.isOpen_ball⟩
  rw [← (hf.metric V).scalarCurvature_restrictOpenTangentSpace B ⟨x, hx⟩,
    ContMDiffRiemannianMetric.scalarCurvature_def]
  let _ : RiemannianBundle (fun y : B ↦ TangentSpace 𝓘(ℝ, V) y) :=
    ⟨((hf.metric V).restrictOpenTangentSpace B).toRiemannianMetric⟩
  rw [(leviCivitaConnection 𝓘(ℝ, V) B).scalarCurvature_eq_of_curvatureTensor_eq_smul_inner_sub
      ⟨x, hx⟩ (1 / 4)
      ((hf.isConstantCurvatureTensor_restrictOpenTangentSpace_ball htip).curvatureTensor_eq
        _ _ ⟨x, hx⟩),
    TauCeti.finrank_tangentSpace]
  ring

/-- At the origin `0 ∈ V`, the scalar curvature of `hf.metric V` is `dim(V) (dim(V) - 1) / 4`. -/
@[simp]
theorem scalarCurvature_metric_zero :
    (hf.metric V).scalarCurvature (0 : V) =
      (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1) / 4 := by
  obtain ⟨r₀, hr₀, htip⟩ := hf.exists_eq_two_mul_sin
  exact hf.scalarCurvature_metric_of_mem_ball htip (Metric.mem_ball_self hr₀)

omit hf [FiniteDimensional ℝ V] in
/-- Polar preimage of a nonzero point `x ∈ V` in `(0, ∞) × Sⁿ`. -/
private def polarPreimage {x : V} (hx : x ≠ 0) :
    standardCapRadialDomain × Metric.sphere (0 : V) 1 :=
  (⟨‖x‖, norm_pos_iff.2 hx⟩,
    ⟨‖x‖⁻¹ • x, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]⟩)

omit hf [FiniteDimensional ℝ V] in
private theorem polarPreimage_smul {x : V} (hx : x ≠ 0) :
    ((polarPreimage hx).1 : ℝ) • ((polarPreimage hx).2 : V) = x := by
  simp [polarPreimage, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx)]

/-- Away from the origin, the scalar curvature of `hf.metric V` is given by the warped-product
formula in terms of `f ‖x‖`, `deriv f ‖x‖`, and `deriv (deriv f) ‖x‖`. -/
theorem scalarCurvature_metric_of_ne_zero {x : V} (hx : x ≠ 0) :
    (hf.metric V).scalarCurvature x =
      ((Module.finrank ℝ V : ℝ) - 1) * ((Module.finrank ℝ V : ℝ) - 2) *
          (1 - deriv f ‖x‖ ^ 2) / f ‖x‖ ^ 2 -
        2 * ((Module.finrank ℝ V : ℝ) - 1) * deriv (deriv f) ‖x‖ / f ‖x‖ := by
  have hpos : 0 < Module.finrank ℝ V :=
    Module.finrank_pos_iff.2 ⟨⟨x, 0, hx⟩⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have : Fact (Module.finrank ℝ V = n + 1) := ⟨hn⟩
  let _ : RiemannianBundle (fun p : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
    TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun y : V ↦ TangentSpace 𝓘(ℝ, V) y) :=
    ⟨(hf.metric V).toRiemannianMetric⟩
  have hloc := hf.isLocalRiemannianIsometry_polar (V := V) (n := n)
  have hmap := hloc.scalarCurvature_map (polarPreimage hx)
  rw [polarPreimage_smul hx] at hmap
  rw [ContMDiffRiemannianMetric.scalarCurvature_def, hmap,
    ← ContMDiffRiemannianMetric.scalarCurvature_def, hf.scalarCurvature_puncturedMetric (n := n),
    hn]
  push_cast
  simp only [polarPreimage]
  ring

/-- On the cylindrical end `{x : V | R < ‖x‖}` where `f = √2` on `[R, ∞)`, the scalar curvature
of `hf.metric V` equals `(dim(V) - 1) (dim(V) - 2) / 2` (in particular `1` when `dim(V) = 3`). -/
theorem scalarCurvature_metric_of_eq_sqrt_two {R : ℝ} (hR : ∀ r, R ≤ r → f r = √2)
    {x : V} (hx0 : x ≠ 0) (hx : R < ‖x‖) :
    (hf.metric V).scalarCurvature x =
      ((Module.finrank ℝ V : ℝ) - 1) * ((Module.finrank ℝ V : ℝ) - 2) / 2 := by
  have heq : f =ᶠ[𝓝 ‖x‖] fun _ ↦ √2 := by
    filter_upwards [Ioi_mem_nhds hx] with s hs using hR s hs.le
  have hd : deriv f =ᶠ[𝓝 ‖x‖] fun _ ↦ 0 := by
    filter_upwards [heq.deriv] with s hs
    simpa only [deriv_const] using hs
  rw [hf.scalarCurvature_metric_of_ne_zero hx0, heq.eq_of_nhds, hd.eq_of_nhds,
    hd.deriv_eq, deriv_const, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Outside a sufficiently large radius, the scalar curvature of `hf.metric V` equals the constant
cylinder value `(dim(V) - 1) (dim(V) - 2) / 2` (in particular `1` when `dim(V) = 3`). -/
theorem exists_scalarCurvature_metric_eq_cylinder :
    ∃ R > 0, ∀ x : V, R ≤ ‖x‖ →
      (hf.metric V).scalarCurvature x =
        ((Module.finrank ℝ V : ℝ) - 1) * ((Module.finrank ℝ V : ℝ) - 2) / 2 := by
  obtain ⟨R, hR⟩ := hf.exists_eq_sqrt_two
  refine ⟨max R 0 + 1, by positivity, fun x hx ↦
    hf.scalarCurvature_metric_of_eq_sqrt_two hR
      (norm_pos_iff.1 (by linarith [le_max_right R 0])) (by linarith [le_max_left R 0])⟩

/-- The smooth standard cap metric has nonnegative sectional curvature on every tangent pair at
every point of `V`, including dependent spanning vectors. -/
theorem sectionalCurvature_metric_nonneg (x : V) (u v : TangentSpace 𝓘(ℝ, V) x) :
    letI : RiemannianBundle (fun y : V ↦ TangentSpace 𝓘(ℝ, V) y) :=
      ⟨(hf.metric V).toRiemannianMetric⟩
    0 ≤ (leviCivitaConnection 𝓘(ℝ, V) V).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) x u v := by
  let _ : RiemannianBundle (fun y : V ↦ TangentSpace 𝓘(ℝ, V) y) :=
    ⟨(hf.metric V).toRiemannianMetric⟩
  rcases eq_or_ne x 0 with rfl | hx
  · by_cases huv : LinearIndependent ℝ ![u, v]
    · rw [(hasSectionalCurvatureAt_iff ..).1 hf.hasSectionalCurvatureAt_metric_zero u v huv]
      norm_num
    · have hdet : (Matrix.gram ℝ ![u, v]).det = 0 :=
        not_not.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr huv)
      rw [sectionalCurvature_apply, hdet, div_zero]
  · have hpos : 0 < Module.finrank ℝ V := Module.finrank_pos_iff.2 ⟨⟨x, 0, hx⟩⟩
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have : Fact (Module.finrank ℝ V = n + 1) := ⟨hn⟩
    let _ : RiemannianBundle (fun p : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    have hloc := hf.isLocalRiemannianIsometry_polar (V := V) (n := n)
    set p := polarPreimage hx
    have hsmul : (p.1 : ℝ) • (p.2 : V) = x := polarPreimage_smul hx
    clear_value p
    clear hx
    revert u v
    rw [← hsmul]
    intro u v
    obtain ⟨e, he⟩ := hloc.exists_linearIsometryEquiv_eq_mfderiv p
    obtain ⟨u', rfl⟩ := e.surjective u
    obtain ⟨v', rfl⟩ := e.surjective v
    rw [he u', he v', hloc.sectionalCurvature_mfderiv]
    exact hf.sectionalCurvature_puncturedMetric_nonneg (V := V) (n := n) p u' v'

/-- The smooth standard cap metric has nonnegative scalar curvature everywhere on `V`. -/
theorem scalarCurvature_metric_nonneg (x : V) :
    0 ≤ (hf.metric V).scalarCurvature x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hf.scalarCurvature_metric_zero]
    cases Module.finrank ℝ V with
    | zero => norm_num
    | succ n =>
      push_cast
      rw [add_sub_cancel_right]
      positivity
  · have hpos : 0 < Module.finrank ℝ V := Module.finrank_pos_iff.2 ⟨⟨x, 0, hx⟩⟩
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have : Fact (Module.finrank ℝ V = n + 1) := ⟨hn⟩
    let _ : RiemannianBundle (fun p : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    let _ : RiemannianBundle (fun y : V ↦ TangentSpace 𝓘(ℝ, V) y) :=
      ⟨(hf.metric V).toRiemannianMetric⟩
    have hmap := (hf.isLocalRiemannianIsometry_polar (V := V) (n := n)).scalarCurvature_map
      (polarPreimage hx)
    rw [polarPreimage_smul hx] at hmap
    rw [ContMDiffRiemannianMetric.scalarCurvature_def, hmap,
      ← ContMDiffRiemannianMetric.scalarCurvature_def]
    exact hf.scalarCurvature_puncturedMetric_nonneg (V := V) (n := n) (polarPreimage hx)

end TauCeti.IsStandardCapProfile
