/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Parallel.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

/-!
# Isometric parallel transport for metric-compatible connections

For a smooth metric-compatible connection on a Riemannian tangent bundle, parallel transport along
any `C¹` curve preserves the fibrewise inner product and norm, and therefore packages as a linear
isometric equivalence `T_{γ(a)} M ≃ₗᵢ[ℝ] T_{γ(b)} M`. No torsion-free assumption is needed.

## Main definitions and results

* `CovariantDerivative.IsMetricCompatible.inner_parallelTransportWithin` and
  `CovariantDerivative.IsMetricCompatible.inner_parallelTransport`: parallel transport preserves
  the inner product.
* `CovariantDerivative.IsMetricCompatible.norm_parallelTransportWithin` and
  `CovariantDerivative.IsMetricCompatible.norm_parallelTransport`: parallel transport preserves
  the norm.
* `CovariantDerivative.IsMetricCompatible.parallelTransportWithinLinearIsometryEquiv` and
  `CovariantDerivative.IsMetricCompatible.parallelTransportLinearIsometryEquiv`: parallel transport
  packaged as a `LinearIsometryEquiv`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5,
  Proposition 5.5.
-/

public section

open Bundle FiberBundle Set TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

/-- **Parallel transport preserves the inner product** within a preconnected parameter set. -/
theorem IsMetricCompatible.inner_parallelTransportWithin
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s) (v w : TangentSpace I (γ a)) :
    inner ℝ (cov.parallelTransportWithin γ s a b v) (cov.parallelTransportWithin γ s a b w) =
      inner ℝ v w := by
  have h := hcov.inner_eq_of_alongCurveWithin_eq_zero hconn
    (hγ.mdifferentiableOn one_ne_zero)
    (fun t ht ↦ cov.differentiableWithinAt_sectionCoord_parallelTransportWithin hconn hγ ha ht
      (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)) v)
    (fun t ht ↦ cov.differentiableWithinAt_sectionCoord_parallelTransportWithin hconn hγ ha ht
      (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)) w)
    (fun _ ht ↦ cov.alongCurveWithin_parallelTransportWithin hconn hγ ha ht v)
    (fun _ ht ↦ cov.alongCurveWithin_parallelTransportWithin hconn hγ ha ht w)
    hb ha
  rwa [cov.parallelTransportWithin_self_apply hconn hγ ha v,
    cov.parallelTransportWithin_self_apply hconn hγ ha w] at h

/-- **Unrestricted parallel transport preserves the inner product.** -/
theorem IsMetricCompatible.inner_parallelTransport
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) (v w : TangentSpace I (γ a)) :
    inner ℝ (cov.parallelTransport γ a b v) (cov.parallelTransport γ a b w) = inner ℝ v w := by
  simpa only [parallelTransportWithin_univ] using
    hcov.inner_parallelTransportWithin isPreconnected_univ hγ.contMDiffOn
      (mem_univ a) (mem_univ b) v w

/-- **Parallel transport preserves the norm** within a preconnected parameter set. -/
theorem IsMetricCompatible.norm_parallelTransportWithin
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s) (v : TangentSpace I (γ a)) :
    ‖cov.parallelTransportWithin γ s a b v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    hcov.inner_parallelTransportWithin hconn hγ ha hb]

/-- **Unrestricted parallel transport preserves the norm.** -/
theorem IsMetricCompatible.norm_parallelTransport
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) (v : TangentSpace I (γ a)) :
    ‖cov.parallelTransport γ a b v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hcov.inner_parallelTransport hγ a b]

/-- **Parallel transport within a preconnected set packaged as a linear isometric equivalence.** -/
def IsMetricCompatible.parallelTransportWithinLinearIsometryEquiv
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s) :
    TangentSpace I (γ a) ≃ₗᵢ[ℝ] TangentSpace I (γ b) where
  toLinearEquiv := (cov.parallelTransportWithinEquiv hconn hγ ha hb).toLinearEquiv
  norm_map' v := by
    rw [ContinuousLinearEquiv.coe_toLinearEquiv, cov.parallelTransportWithinEquiv_apply]
    exact hcov.norm_parallelTransportWithin hconn hγ ha hb v

/-- Applying `parallelTransportWithinLinearIsometryEquiv` evaluates `parallelTransportWithin`. -/
@[simp]
theorem IsMetricCompatible.parallelTransportWithinLinearIsometryEquiv_apply
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s) (v : TangentSpace I (γ a)) :
    hcov.parallelTransportWithinLinearIsometryEquiv hconn hγ ha hb v =
      cov.parallelTransportWithin γ s a b v :=
  cov.parallelTransportWithinEquiv_apply hconn hγ ha hb v

/-- The inverse of `parallelTransportWithinLinearIsometryEquiv` from `a` to `b` is isometric
parallel transport from `b` to `a`. -/
@[simp]
theorem IsMetricCompatible.parallelTransportWithinLinearIsometryEquiv_symm
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s) :
    (hcov.parallelTransportWithinLinearIsometryEquiv hconn hγ ha hb).symm =
      hcov.parallelTransportWithinLinearIsometryEquiv hconn hγ hb ha := by
  ext w
  rw [LinearIsometryEquiv.symm_apply_eq]
  simp [cov.parallelTransportWithin_trans_apply hconn hγ hb ha hb,
    cov.parallelTransportWithin_self_apply hconn hγ hb]

/-- **Unrestricted parallel transport packaged as a linear isometric equivalence.** -/
def IsMetricCompatible.parallelTransportLinearIsometryEquiv
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    TangentSpace I (γ a) ≃ₗᵢ[ℝ] TangentSpace I (γ b) where
  toLinearEquiv := (cov.parallelTransportEquiv hγ a b).toLinearEquiv
  norm_map' v := by
    rw [ContinuousLinearEquiv.coe_toLinearEquiv, cov.parallelTransportEquiv_apply]
    exact hcov.norm_parallelTransport hγ a b v

/-- Applying `parallelTransportLinearIsometryEquiv` evaluates `parallelTransport`. -/
@[simp]
theorem IsMetricCompatible.parallelTransportLinearIsometryEquiv_apply
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) (v : TangentSpace I (γ a)) :
    hcov.parallelTransportLinearIsometryEquiv hγ a b v = cov.parallelTransport γ a b v :=
  cov.parallelTransportEquiv_apply hγ a b v

/-- The inverse of `parallelTransportLinearIsometryEquiv` from `a` to `b` is isometric parallel
transport from `b` to `a`. -/
@[simp]
theorem IsMetricCompatible.parallelTransportLinearIsometryEquiv_symm
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    (hcov.parallelTransportLinearIsometryEquiv hγ a b).symm =
      hcov.parallelTransportLinearIsometryEquiv hγ b a := by
  ext w
  rw [LinearIsometryEquiv.symm_apply_eq]
  simp [cov.parallelTransport_trans_apply hγ b a b, cov.parallelTransport_self_apply hγ b]

end CovariantDerivative

end
