/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Cylinder
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.Riemannian.Prod.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Radius
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.RicciFlow.StandardCap.Metric
public import TauCeti.Geometry.RicciFlow.StandardCap.PuncturedMetric

import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Polar coordinates and the cylindrical end of the standard cap

This file identifies the smooth standard cap metric `TauCeti.IsStandardCapProfile.metric` away from
the origin with the warped-product metric `dr² + f(r)² g_(Sⁿ)` and with a round product cylinder
outside a finite radius:

* **Polar coordinates** away from `0`: `(r, u) ↦ r • u` is a local Riemannian isometry from
  `hf.puncturedMetric V` into `(V, hf.metric V)` and a global Riemannian isometry onto the
  restriction of `hf.metric V` to `V ∖ {0}`.
* **Cylindrical end**: for any `R ≥ 0` beyond which `f = √2`, polar coordinates give a smooth
  Riemannian isometry between the Riemannian product `(R, ∞) × Sⁿ(√2)` and the restriction of
  `hf.metric V` to `{x : V | R < ‖x‖}`.

## Main definitions

* `TauCeti.IsStandardCapProfile.polarIsometry`: the polar-coordinate Riemannian isometry from
  `hf.puncturedMetric V` onto the restriction of `hf.metric V` to `V ∖ {0}`.
* `TauCeti.IsStandardCapProfile.cylindricalEndIsometry`: the Riemannian isometry between the
  product half-cylinder `(R, ∞) × Sⁿ(√2)` and the cylindrical end `{x : V | R < ‖x‖}` of
  `hf.metric V`.

## Main results

* `TauCeti.IsStandardCapProfile.isLocalRiemannianIsometry_polar`: polar coordinates form a local
  Riemannian isometry from `hf.puncturedMetric V` into `hf.metric V`.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics Monographs 3
  (2007), Definition 12.1.
* G. Perelman, *Ricci flow with surgery on three-manifolds*, arXiv:math/0303109 (2003), §2.
-/

public noncomputable section

open Bundle Metric Real Set TopologicalSpace
open TauCeti.Manifold
open scoped ContDiff ENNReal InnerProductSpace Manifold Topology

namespace TauCeti.IsStandardCapProfile

section Polar

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (Module.finrank ℝ V = n + 1)]

/-- Arclength polar coordinates `(r, u) ↦ r • u` as a smooth diffeomorphism from
`radDom × Sⁿ` onto `extDom`, for any open `radDom ⊆ ℝ` and `extDom ⊆ V` corresponding to
`R < r` and `R < ‖x‖` with `0 ≤ R`. -/
private def radialPolarDiffeomorph (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] {R : ℝ} (hR0 : 0 ≤ R)
    (radDom : Opens ℝ) (extDom : Opens V)
    (hrad : ∀ r : ℝ, r ∈ radDom ↔ R < r) (hext : ∀ x : V, x ∈ extDom ↔ R < ‖x‖) :
    (radDom × Metric.sphere (0 : V) 1) ≃ₘ⟮𝓘(ℝ).prod (𝓡 n), 𝓘(ℝ, V)⟯ extDom where
  toFun p := ⟨(p.1 : ℝ) • (p.2 : V), by
    have hr : R < (p.1 : ℝ) := (hrad _).1 p.1.2
    have hr0 : 0 < (p.1 : ℝ) := hR0.trans_lt hr
    have hu : ‖(p.2 : V)‖ = 1 := norm_eq_of_mem_sphere p.2
    rw [hext, norm_smul, hu, mul_one, Real.norm_of_nonneg hr0.le]
    exact hr⟩
  invFun x :=
    (⟨‖(x : V)‖, (hrad _).2 ((hext _).1 x.2)⟩,
      ⟨‖(x : V)‖⁻¹ • (x : V), by
        have hx : ‖(x : V)‖ ≠ 0 := (hR0.trans_lt ((hext _).1 x.2)).ne'
        simp [norm_smul, inv_mul_cancel₀ hx]⟩)
  left_inv p := by
    obtain ⟨⟨r, hr⟩, u⟩ := p
    have hr0 : 0 < r := hR0.trans_lt ((hrad _).1 hr)
    have hu : ‖(u : V)‖ = 1 := norm_eq_of_mem_sphere u
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp [norm_smul, hu, abs_of_pos hr0]
    · simp [norm_smul, hu, abs_of_pos hr0, smul_smul, hr0.ne']
  right_inv x := by
    have hx : ‖(x : V)‖ ≠ 0 := (hR0.trans_lt ((hext _).1 x.2)).ne'
    refine Subtype.ext ?_
    simp [smul_smul, mul_inv_cancel₀ hx]
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff extDom _).1
      ((contMDiff_subtype_val.comp contMDiff_fst).smul (contMDiff_coe_sphere.comp contMDiff_snd))
  contMDiff_invFun := by
    refine ContMDiff.prodMk ?_ ?_
    · refine (ContMDiff.subtypeVal_comp_iff radDom _).1 fun x ↦ ?_
      refine (contMDiffAt_subtype_iff (f := fun z : V ↦ ‖z‖)).2 ?_
      exact (contDiffAt_norm ℝ (norm_pos_iff.1 (hR0.trans_lt ((hext _).1 x.2)))).contMDiffAt
    · refine ContMDiff.codRestrict_sphere (f := fun x : extDom ↦ ‖(x : V)‖⁻¹ • (x : V))
        (fun x ↦ (contMDiffAt_subtype_iff (f := fun z : V ↦ ‖z‖⁻¹ • z)).2 ?_) _
      have hx : (x : V) ≠ 0 := norm_pos_iff.1 (hR0.trans_lt ((hext _).1 x.2))
      exact (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.2 hx)).smul contDiffAt_id).contMDiffAt

/-- The differential of the polar map `(r, u) ↦ r • u` on any open radial domain `radDom ⊆ ℝ`. -/
private theorem mvfderiv_radialPolar_apply (radDom : Opens ℝ)
    (p : radDom × Metric.sphere (0 : V) 1) (v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    mvfderiv (𝓘(ℝ).prod (𝓡 n))
        (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p v =
      (p.1 : ℝ) • mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : V) 1 → V) p.2
          (tangentSpaceProdEquiv p v).2 +
        NormedSpace.fromTangentSpace (p.1 : ℝ)
          (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p v).1) • (p.2 : V) := by
  have hd₁ : MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ)
      (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ)) p :=
    ((contMDiff_subtype_val (U := radDom) (n := ∞)).comp contMDiff_fst).mdifferentiableAt (by simp)
  have hd₂ : MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.2 : V)) p :=
    ((contMDiff_coe_sphere (m := ∞)).comp contMDiff_snd).mdifferentiableAt (by simp)
  have h₁ : mvfderiv (𝓘(ℝ).prod (𝓡 n))
      (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ)) p v =
      NormedSpace.fromTangentSpace (p.1 : ℝ)
        (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p v).1) := by
    rw [mvfderiv, ContinuousLinearMap.comp_apply,
      show (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ)) = Subtype.val ∘ Prod.fst from rfl,
      mfderiv_comp_apply p
        ((contMDiff_subtype_val (I := 𝓘(ℝ)) (U := radDom) (n := ∞)).mdifferentiableAt (by simp))
        mdifferentiableAt_fst,
      Manifold.mfderiv_subtype_val, mfderiv_fst, tangentSpaceProdEquiv_apply]
    rfl
  have h₂ : mvfderiv (𝓘(ℝ).prod (𝓡 n))
      (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.2 : V)) p v =
      mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : V) 1 → V) p.2 (tangentSpaceProdEquiv p v).2 := by
    rw [mvfderiv, mvfderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      show (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.2 : V)) = Subtype.val ∘ Prod.snd from rfl,
      mfderiv_comp_apply p ((contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp))
        mdifferentiableAt_snd,
      mfderiv_snd, tangentSpaceProdEquiv_apply]
    rfl
  rw [mvfderiv_fun_smul hd₁ hd₂]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, h₁, h₂]

/-- Pullback formula for `hf.metric V` along `(r, u) ↦ r • u` on any open radial domain
`radDom ⊆ (0, ∞)`. -/
private theorem metric_inner_mfderiv_radialPolar (radDom : Opens ℝ)
    (p : radDom × Metric.sphere (0 : V) 1) (hr : 0 < (p.1 : ℝ))
    (v w : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    (hf.metric V).inner ((p.1 : ℝ) • (p.2 : V))
      (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
        (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p v)
      (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
        (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p w) =
      NormedSpace.fromTangentSpace (p.1 : ℝ)
          (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p v).1) *
        NormedSpace.fromTangentSpace (p.1 : ℝ)
          (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p w).1) +
        f (p.1 : ℝ) ^ 2 *
          ⟪mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : V) 1 → V) p.2 (tangentSpaceProdEquiv p v).2,
            mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : V) 1 → V) p.2
              (tangentSpaceProdEquiv p w).2⟫_ℝ := by
  set r : ℝ := (p.1 : ℝ)
  set u : V := (p.2 : V)
  have hu : ‖u‖ = 1 := norm_eq_of_mem_sphere p.2
  have huu : ⟪u, u⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hru : r • u ≠ 0 := smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere p.2)
  have hnorm : ‖r • u‖ = r := by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le]
  set vₜ : V := mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : V) 1 → V) p.2
    (tangentSpaceProdEquiv p v).2
  set wₜ : V := mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : V) 1 → V) p.2
    (tangentSpaceProdEquiv p w).2
  set a : ℝ := NormedSpace.fromTangentSpace r
    (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p v).1)
  set b : ℝ := NormedSpace.fromTangentSpace r
    (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p w).1)
  have hv_orth : ⟪u, vₜ⟫_ℝ = 0 := inner_coe_mvfderiv_subtypeVal_sphere p.2 _
  have hw_orth : ⟪u, wₜ⟫_ℝ = 0 := inner_coe_mvfderiv_subtypeVal_sphere p.2 _
  have hv_orth' : ⟪vₜ, u⟫_ℝ = 0 := by rw [real_inner_comm, hv_orth]
  have hv_eq : NormedSpace.fromTangentSpace (r • u)
      (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
        (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p v) =
      r • vₜ + a • u := by
    rw [← mvfderiv_apply_eq_mfderiv_apply]
    exact mvfderiv_radialPolar_apply radDom p v
  have hw_eq : NormedSpace.fromTangentSpace (r • u)
      (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
        (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p w) =
      r • wₜ + b • u := by
    rw [← mvfderiv_apply_eq_mfderiv_apply]
    exact mvfderiv_radialPolar_apply radDom p w
  rw [hf.metric_inner_of_ne_zero hru, hv_eq, hw_eq, hnorm]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hv_orth, hw_orth, hv_orth', huu]
  have hr0 : r ≠ 0 := hr.ne'
  field_simp
  ring

/-- Helper computing the differential of `WithMetric.toWithMetric ∘ d ∘ WithMetric.ofWithMetric`
composed with the open-subset inclusion `extDom → V`. -/
private theorem tangentSpaceOpenEquiv_mfderiv_withMetric_radialPolar
    {radDom : Opens ℝ} {extDom : Opens V}
    {g : ContMDiffRiemannianMetric (𝓘(ℝ).prod (𝓡 n)) ∞ (ℝ × EuclideanSpace ℝ (Fin n))
      (fun p : radDom × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) p)}
    (d : (radDom × Metric.sphere (0 : V) 1) ≃ₘ⟮𝓘(ℝ).prod (𝓡 n), 𝓘(ℝ, V)⟯ extDom)
    (hd_val : ∀ q, (d q : V) = (q.1 : ℝ) • (q.2 : V))
    (p : WithMetric g) (u : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    let Φ : WithMetric g → WithMetric ((hf.metric V).restrictOpenTangentSpace extDom) :=
      fun q ↦ WithMetric.toWithMetric _ (d q.ofWithMetric)
    tangentSpaceOpenEquiv (I := 𝓘(ℝ, V)) (Φ p).ofWithMetric
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric (Φ p)
        (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) Φ p u)) =
      mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
        (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V))
        p.ofWithMetric (mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n))
          WithMetric.ofWithMetric p u) := by
  intro Φ
  have hsub : Subtype.val ∘ WithMetric.ofWithMetric ∘ Φ =
      (fun q : radDom × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) ∘
        WithMetric.ofWithMetric := by
    ext q
    exact hd_val q.ofWithMetric
  have hdΦ : MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) Φ p :=
    ((WithMetric.contMDiff_toWithMetric (k := ∞)).comp
      (d.contMDiff.comp (WithMetric.contMDiff_ofWithMetric (k := ∞)))).mdifferentiableAt (by simp)
  have hdo := (WithMetric.hasMFDerivAt_ofWithMetric (Φ p)).mdifferentiableAt
  have hds := (contMDiff_subtype_val (I := 𝓘(ℝ, V)) (U := extDom) (n := ∞)).mdifferentiableAt
    (by simp) (x := (Φ p).ofWithMetric)
  have h1 : tangentSpaceOpenEquiv (I := 𝓘(ℝ, V)) (Φ p).ofWithMetric
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric (Φ p)
          (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) Φ p u)) =
      mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) (Subtype.val ∘ WithMetric.ofWithMetric ∘ Φ) p u := by
    rw [mfderiv_comp_apply p hds (hdo.comp p hdΦ),
      mfderiv_comp_apply p hdo hdΦ, Manifold.mfderiv_subtype_val]
    rfl
  rw [h1, hsub, WithMetric.mfderiv_comp_ofWithMetric, ContinuousLinearMap.comp_apply]

private theorem inner_radial_factor (radDom : Opens ℝ) (r : radDom)
    (v w : TangentSpace 𝓘(ℝ) r) :
    (((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace radDom).inner
      r v w =
      NormedSpace.fromTangentSpace (r : ℝ) (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) r v) *
        NormedSpace.fromTangentSpace (r : ℝ) (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) r w) := by
  rw [ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
    ContMDiffRiemannianMetric.ofLE_inner]
  change ⟪NormedSpace.fromTangentSpace (r : ℝ) (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) r v),
    NormedSpace.fromTangentSpace (r : ℝ) (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) r w)⟫_ℝ = _
  rw [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, mul_comm]

/-- Polar coordinates `(r, u) ↦ r • u` form a local Riemannian isometry from the punctured
standard cap `hf.puncturedMetric V` into `(V, hf.metric V)`. -/
theorem isLocalRiemannianIsometry_polar :
    letI : RiemannianBundle (fun p : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) :=
      ⟨(hf.metric V).toRiemannianMetric⟩
    IsLocalRiemannianIsometry (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) := by
  let : RiemannianBundle (fun p : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
    TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) :=
    ⟨(hf.metric V).toRiemannianMetric⟩
  let d := radialPolarDiffeomorph (n := n) V le_rfl standardCapRadialDomain (puncturedSpace V)
    (fun _ ↦ Iff.rfl) (fun _ ↦ by rw [mem_puncturedSpace, norm_pos_iff])
  refine ⟨(contMDiff_subtype_val.comp contMDiff_fst).smul (contMDiff_coe_sphere.comp contMDiff_snd),
    fun p ↦ ?_, fun p v w ↦ ?_⟩
  · rw [show (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) =
      Subtype.val ∘ d from rfl]
    exact isInvertible_mfderiv_comp (by rw [Manifold.mfderiv_subtype_val]; exact ⟨_, rfl⟩)
      (d.isInvertible_mfderiv (by simp))
  · change (hf.metric V).inner _ _ _ = (hf.puncturedMetric (n := n) V).inner p v w
    rw [hf.metric_inner_mfderiv_radialPolar standardCapRadialDomain p p.1.2,
      hf.puncturedMetric_inner, inner_radial_factor, ContMDiffRiemannianMetric.ofLE_inner,
      sphereRoundMetric_inner]

/-- Common Riemannian isometry builder for polar coordinates `(r, u) ↦ r • u` on any open radial
region `R < r` (`0 ≤ R`) carrying a metric `g` matching `dr² + f(r)² g_(Sⁿ)`. -/
private def radialPolarRiemannianIsometry {R : ℝ} (hR0 : 0 ≤ R)
    (radDom : Opens ℝ) (extDom : Opens V)
    (hrad : ∀ r : ℝ, r ∈ radDom ↔ R < r) (hext : ∀ x : V, x ∈ extDom ↔ R < ‖x‖)
    (g : ContMDiffRiemannianMetric (𝓘(ℝ).prod (𝓡 n)) ∞ (ℝ × EuclideanSpace ℝ (Fin n))
      (fun p : radDom × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) p))
    (hg : ∀ (p : radDom × Metric.sphere (0 : V) 1) (v w : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p),
      g.inner p v w =
        NormedSpace.fromTangentSpace (p.1 : ℝ)
            (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p v).1) *
          NormedSpace.fromTangentSpace (p.1 : ℝ)
            (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p w).1) +
          f (p.1 : ℝ) ^ 2 *
            ⟪mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : V) 1 → V) p.2 (tangentSpaceProdEquiv p v).2,
              mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : V) 1 → V) p.2
                (tangentSpaceProdEquiv p w).2⟫_ℝ) :
    letI : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
    RiemannianIsometry (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (WithMetric g) (WithMetric ((hf.metric V).restrictOpenTangentSpace extDom)) :=
  letI : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  let d := radialPolarDiffeomorph (n := n) V hR0 radDom extDom hrad hext
  { toDiffeomorph :=
      (WithMetric.diffeomorph g ∞).trans
        (d.trans (WithMetric.diffeomorph ((hf.metric V).restrictOpenTangentSpace extDom) ∞).symm)
    inner_mfderiv' := fun p v w ↦ by
      have hΦ : (⇑((WithMetric.diffeomorph g ∞).trans
          (d.trans (WithMetric.diffeomorph
            ((hf.metric V).restrictOpenTangentSpace extDom) ∞).symm))) =
          fun q ↦ WithMetric.toWithMetric _ (d q.ofWithMetric) := by
        ext q; simp [WithMetric.coe_diffeomorph, WithMetric.coe_diffeomorph_symm]
      rw [hΦ, WithMetric.inner_def, WithMetric.inner_def,
        ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
        hf.tangentSpaceOpenEquiv_mfderiv_withMetric_radialPolar d (fun _ ↦ rfl) p v,
        hf.tangentSpaceOpenEquiv_mfderiv_withMetric_radialPolar d (fun _ ↦ rfl) p w]
      change (hf.metric V).inner ((p.ofWithMetric.1 : ℝ) • (p.ofWithMetric.2 : V)) _ _ = _
      rw [hf.metric_inner_mfderiv_radialPolar radDom p.ofWithMetric
          (hR0.trans_lt ((hrad _).1 p.ofWithMetric.1.2)), hg] }

private theorem radialPolarRiemannianIsometry_apply {R : ℝ} (hR0 : 0 ≤ R)
    (radDom : Opens ℝ) (extDom : Opens V)
    (hrad : ∀ r : ℝ, r ∈ radDom ↔ R < r) (hext : ∀ x : V, x ∈ extDom ↔ R < ‖x‖)
    (g : ContMDiffRiemannianMetric (𝓘(ℝ).prod (𝓡 n)) ∞ (ℝ × EuclideanSpace ℝ (Fin n))
      (fun p : radDom × Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) p))
    (hg : ∀ (p : radDom × Metric.sphere (0 : V) 1) (v w : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p),
      g.inner p v w =
        NormedSpace.fromTangentSpace (p.1 : ℝ)
            (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p v).1) *
          NormedSpace.fromTangentSpace (p.1 : ℝ)
            (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p w).1) +
          f (p.1 : ℝ) ^ 2 *
            ⟪mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : V) 1 → V) p.2 (tangentSpaceProdEquiv p v).2,
              mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : V) 1 → V) p.2
                (tangentSpaceProdEquiv p w).2⟫_ℝ)
    (p : WithMetric g) :
    ((hf.radialPolarRiemannianIsometry hR0 radDom extDom hrad hext g hg p).ofWithMetric : V) =
      (p.ofWithMetric.1 : ℝ) • (p.ofWithMetric.2 : V) := by
  let _ : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  rw [← RiemannianIsometry.coe_toDiffeomorph]
  simp only [radialPolarRiemannianIsometry, Diffeomorph.coe_trans, Function.comp_apply,
    WithMetric.coe_diffeomorph, WithMetric.coe_diffeomorph_symm,
    WithMetric.ofWithMetric_toWithMetric]
  rfl

/-- Polar coordinates `(r, u) ↦ r • u` give a smooth Riemannian isometry from the punctured
standard cap `hf.puncturedMetric V` onto the restriction of `hf.metric V` to `V ∖ {0}`. -/
def polarIsometry :
    letI : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
    RiemannianIsometry (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (WithMetric (hf.puncturedMetric (n := n) V))
      (WithMetric ((hf.metric V).restrictOpenTangentSpace (puncturedSpace V))) :=
  hf.radialPolarRiemannianIsometry le_rfl standardCapRadialDomain (puncturedSpace V)
    (fun _ ↦ Iff.rfl) (fun _ ↦ by rw [mem_puncturedSpace, norm_pos_iff])
    (hf.puncturedMetric (n := n) V) fun p v w ↦ by
      rw [hf.puncturedMetric_inner, inner_radial_factor, ContMDiffRiemannianMetric.ofLE_inner,
        sphereRoundMetric_inner]

/-- Evaluation of `polarIsometry` in ambient coordinates of `V`. -/
@[simp]
theorem polarIsometry_apply (p : WithMetric (hf.puncturedMetric (n := n) V)) :
    ((hf.polarIsometry (V := V) (n := n) p).ofWithMetric : V) =
      (p.ofWithMetric.1 : ℝ) • (p.ofWithMetric.2 : V) :=
  hf.radialPolarRiemannianIsometry_apply ..

/-- On the exterior `{x : V | R < ‖x‖}` where `f = √2`, polar coordinates give a smooth Riemannian
isometry between the Riemannian product `(R, ∞) × Sⁿ(√2)` and the restriction of `hf.metric V`. -/
def cylindricalEndIsometry {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ r, R ≤ r → f r = √2) :
    letI : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
    RiemannianIsometry (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (WithMetric
        ((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace
          ⟨Ioi R, isOpen_Ioi⟩).prodTangentSpace
            (sphereRoundMetricOfRadius (E := V) (n := n) √2 (Real.sqrt_pos.2 two_pos))))
      (WithMetric
        ((hf.metric V).restrictOpenTangentSpace
          ⟨{x : V | R < ‖x‖}, isOpen_lt continuous_const continuous_norm⟩)) :=
  hf.radialPolarRiemannianIsometry hR0 ⟨Ioi R, isOpen_Ioi⟩
    ⟨{x : V | R < ‖x‖}, isOpen_lt continuous_const continuous_norm⟩
    (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    ((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace
      ⟨Ioi R, isOpen_Ioi⟩).prodTangentSpace
        (sphereRoundMetricOfRadius (E := V) (n := n) √2 (Real.sqrt_pos.2 two_pos)))
    fun p v w ↦ by
      rw [ContMDiffRiemannianMetric.prodTangentSpace_inner, inner_radial_factor,
        sphereRoundMetricOfRadius_inner, inner_tangentSpace_sphere,
        hR (p.1 : ℝ) p.1.2.le, Real.sq_sqrt (by norm_num)]

/-- Evaluation of `cylindricalEndIsometry` in ambient coordinates of `V`. -/
@[simp]
theorem cylindricalEndIsometry_apply {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ r, R ≤ r → f r = √2)
    (p : WithMetric
      ((((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace
        ⟨Ioi R, isOpen_Ioi⟩).prodTangentSpace
          (sphereRoundMetricOfRadius (E := V) (n := n) √2 (Real.sqrt_pos.2 two_pos)))) :
    ((hf.cylindricalEndIsometry (V := V) (n := n) hR0 hR p).ofWithMetric : V) =
      (p.ofWithMetric.1 : ℝ) • (p.ofWithMetric.2 : V) :=
  hf.radialPolarRiemannianIsometry_apply ..

end Polar

end TauCeti.IsStandardCapProfile
