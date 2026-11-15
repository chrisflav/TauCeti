/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Parallel.Deriv
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Parallel.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.AlongCurve
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Analysis.Calculus.TangentCone.Basic

/-!
# Parallel-transport characterization of parallel curvature

A smooth connection `∇` on the tangent bundle of a boundaryless manifold has parallel curvature
(`∇R = 0`, `CovariantDerivative.HasParallelCurvature`) if and only if parallel transport along
every smooth curve intertwines its curvature tensor.

In one direction, for any smooth connection (even on a manifold with boundary or corners), if
`∇R = 0` then applying `R` to three parallel tangent fields along a `C¹` curve produces a parallel
tangent field, so uniqueness of parallel fields implies that parallel transport commutes with `R`
(`CovariantDerivative.HasParallelCurvature.parallelTransportWithin_curvatureTensor`).

Conversely, pulling `R` along a curve back to a fixed parameter `t` by parallel transport yields a
curve in `T_{γ(t)} M` whose derivative at `r = t` is `(∇_{γ'(t)} R)(u, v)w`
(`CovariantDerivative.hasDerivWithinAt_parallelTransportWithin_curvatureTensor`). On a boundaryless
manifold every tangent vector is realized as the velocity at `0` of a smooth curve `ℝ → M`, so
parallel-transport invariance along all smooth curves (or along all smooth paths on `[0, 1]`)
forces `∇R = 0`.

For a metric-compatible connection, isometric parallel transport translates this equivalence to the
metric-lowered `(0,4)` Riemann curvature tensor `Rm`; when the connection is also torsion-free,
polarization further equates `∇R = 0` to parallel-transport invariance of sectional curvature on
all tangent two-planes.

## Main results

* `CovariantDerivative.hasDerivWithinAt_parallelTransportWithin_curvatureTensor` and
  `CovariantDerivative.hasDerivAt_parallelTransport_curvatureTensor`:
  `(d/dr)|_{r = t} P_{r → t}(R(P_{t → r} u, P_{t → r} v)(P_{t → r} w)) = (∇_{γ'(t)} R)(u, v)w`.
* `CovariantDerivative.HasParallelCurvature.parallelTransportWithin_curvatureTensor` and
  `CovariantDerivative.HasParallelCurvature.parallelTransport_curvatureTensor`:
  parallel curvature implies parallel transport intertwines `R` along any `C¹` curve.
* `CovariantDerivative.hasParallelCurvature_iff_parallelTransport` and
  `CovariantDerivative.hasParallelCurvature_iff_parallelTransportWithin_Icc`:
  `∇R = 0` iff parallel transport along every smooth curve (on `ℝ` or on `[0, 1]`) intertwines `R`.
* `IsMetricCompatible.hasParallelCurvature_iff_riemannCurvatureTensor_parallelTransport` and
  `..._parallelTransportWithin_Icc`, in `CovariantDerivative`: metric-compatible `(0,4)`-tensor
  characterization.
* `IsMetricCompatible.hasParallelCurvature_iff_sectionalCurvature_parallelTransport` and
  `..._parallelTransportWithin_Icc`, in `CovariantDerivative`: metric-compatible torsion-free
  sectional-curvature characterization.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7
  (covariant derivatives of tensors and locally symmetric spaces) and Proposition 4.33 / Theorem
  4.34.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific (2020),
  §3.3.2, equation (3.3.7), pp. 103–104.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience (1963),
  Chapter II, Proposition 3.2, and Vol. II (1969), Chapter XI.
-/

public section

open Bundle FiberBundle Filter Set TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold Matrix Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

section Affine

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

/-- **Differentiating curvature conjugated by parallel transport.**
Along a `C¹` curve `γ` on a preconnected parameter set `s` with unique derivatives at `t ∈ s`,
pulling `R(P_{t → r} u, P_{t → r} v)(P_{t → r} w)` back to `T_{γ(t)} M` by `P_{r → t}` has
derivative `(∇_{γ'(t)} R)(u, v)w` within `s` at `t`. -/
theorem hasDerivWithinAt_parallelTransportWithin_curvatureTensor
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hconn : IsPreconnected s) (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ht : t ∈ s)
    (u v w : TangentSpace I (γ t)) :
    HasDerivWithinAt
      (fun r ↦ cov.parallelTransportWithin γ s r t
        (cov.curvatureTensor (γ r)
          (cov.parallelTransportWithin γ s t r u)
          (cov.parallelTransportWithin γ s t r v)
          (cov.parallelTransportWithin γ s t r w)))
      (cov.derivCurvatureTensor cov (γ t) (curveVelocityWithin I γ s t) u v w) s t := by
  let U := fun r ↦ cov.parallelTransportWithin γ s t r u
  let V := fun r ↦ cov.parallelTransportWithin γ s t r v
  let W := fun r ↦ cov.parallelTransportWithin γ s t r w
  have hx : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hγt : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t :=
    (hγ t ht).mdifferentiableWithinAt one_ne_zero
  have hU := cov.differentiableWithinAt_sectionCoord_parallelTransportWithin hconn hγ ht ht hx u
  have hV := cov.differentiableWithinAt_sectionCoord_parallelTransportWithin hconn hγ ht ht hx v
  have hW := cov.differentiableWithinAt_sectionCoord_parallelTransportWithin hconn hγ ht ht hx w
  have hR := cov.differentiableWithinAt_sectionCoord_curvatureTensor hγt hU hV hW
  have hderiv := cov.hasDerivWithinAt_parallelTransportWithin hconn hγ ht hR
  suffices cov.alongCurveWithin γ
      (fun r ↦ cov.curvatureTensor (γ r) (U r) (V r) (W r)) s t =
      cov.derivCurvatureTensor cov (γ t) (curveVelocityWithin I γ s t) u v w by
    rwa [← this]
  rw [cov.alongCurveWithin_curvatureTensor hu hγt hU hV hW,
    cov.alongCurveWithin_parallelTransportWithin hconn hγ ht ht u,
    cov.alongCurveWithin_parallelTransportWithin hconn hγ ht ht v,
    cov.alongCurveWithin_parallelTransportWithin hconn hγ ht ht w]
  simp [cov.parallelTransportWithin_self_apply hconn hγ ht]

/-- **Unrestricted derivative of curvature conjugated by parallel transport.** -/
theorem hasDerivAt_parallelTransport_curvatureTensor
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (t : ℝ)
    (u v w : TangentSpace I (γ t)) :
    HasDerivAt
      (fun r ↦ cov.parallelTransport γ r t
        (cov.curvatureTensor (γ r)
          (cov.parallelTransport γ t r u)
          (cov.parallelTransport γ t r v)
          (cov.parallelTransport γ t r w)))
      (cov.derivCurvatureTensor cov (γ t) (curveVelocity I γ t) u v w) t := by
  rw [← congrFun (curveVelocityWithin_univ (I := I) (γ := γ)) t]
  simpa only [HasDerivWithinAt, HasDerivAt, nhdsWithin_univ, parallelTransportWithin_univ] using
    cov.hasDerivWithinAt_parallelTransportWithin_curvatureTensor
      isPreconnected_univ uniqueDiffWithinAt_univ hγ.contMDiffOn (mem_univ t) u v w

variable {cov} in
/-- **Parallel curvature implies parallel transport intertwines the curvature tensor** along any
`C¹` curve on a preconnected parameter set. Neither metric compatibility, torsion-freeness, nor
boundarylessness of the manifold is needed. -/
theorem HasParallelCurvature.parallelTransportWithin_curvatureTensor
    (h : cov.HasParallelCurvature) {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s) (u v w : TangentSpace I (γ a)) :
    cov.parallelTransportWithin γ s a b (cov.curvatureTensor (γ a) u v w) =
      cov.curvatureTensor (γ b)
        (cov.parallelTransportWithin γ s a b u)
        (cov.parallelTransportWithin γ s a b v)
        (cov.parallelTransportWithin γ s a b w) := by
  rcases eq_or_ne a b with rfl | hab
  · simp [cov.parallelTransportWithin_self_apply hconn hγ ha]
  have hs : UniqueDiffOn ℝ s := hconn.uniqueDiffOn ha hb hab
  let U := fun r ↦ cov.parallelTransportWithin γ s a r u
  let V := fun r ↦ cov.parallelTransportWithin γ s a r v
  let W := fun r ↦ cov.parallelTransportWithin γ s a r w
  have hcoord (z : TangentSpace I (γ a)) (t : ℝ) (ht : t ∈ s) :=
    cov.differentiableWithinAt_sectionCoord_parallelTransportWithin hconn hγ ha ht
      (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)) z
  have hzero (z : TangentSpace I (γ a)) {t : ℝ} (ht : t ∈ s) :=
    cov.alongCurveWithin_parallelTransportWithin hconn hγ ha ht z
  symm
  refine (cov.eq_parallelTransportWithin_of_alongCurveWithin_eq_zero hconn hγ
    (V := fun r ↦ cov.curvatureTensor (γ r) (U r) (V r) (W r))
    (fun t ht ↦ cov.differentiableWithinAt_sectionCoord_curvatureTensor
      ((hγ t ht).mdifferentiableWithinAt one_ne_zero)
      (hcoord u t ht) (hcoord v t ht) (hcoord w t ht))
    (fun t ht ↦ h.alongCurveWithin_curvatureTensor_eq_zero cov (hs t ht)
      ((hγ t ht).mdifferentiableWithinAt one_ne_zero)
      (hcoord u t ht) (hcoord v t ht) (hcoord w t ht)
      (hzero u ht) (hzero v ht) (hzero w ht)) ha hb).trans ?_
  simp [U, V, W, cov.parallelTransportWithin_self_apply hconn hγ ha]

variable {cov} in
/-- **Parallel curvature implies unrestricted parallel transport intertwines the curvature
tensor.** -/
theorem HasParallelCurvature.parallelTransport_curvatureTensor
    (h : cov.HasParallelCurvature) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (a b : ℝ) (u v w : TangentSpace I (γ a)) :
    cov.parallelTransport γ a b (cov.curvatureTensor (γ a) u v w) =
      cov.curvatureTensor (γ b)
        (cov.parallelTransport γ a b u)
        (cov.parallelTransport γ a b v)
        (cov.parallelTransport γ a b w) := by
  simpa only [parallelTransportWithin_univ] using
    h.parallelTransportWithin_curvatureTensor isPreconnected_univ hγ.contMDiffOn
      (mem_univ a) (mem_univ b) u v w

/-- **Parallel-transport characterization of parallel curvature (on `ℝ`).**
On a boundaryless manifold, a smooth connection on the tangent bundle has parallel curvature
(`∇R = 0`) if and only if parallel transport along every smooth curve `γ : ℝ → M` intertwines its
curvature tensor. -/
theorem hasParallelCurvature_iff_parallelTransport [I.Boundaryless] :
    cov.HasParallelCurvature ↔
      ∀ ⦃γ : ℝ → M⦄, CMDiff ∞ γ → ∀ (a b : ℝ) (u v w : TangentSpace I (γ a)),
        cov.parallelTransport γ a b (cov.curvatureTensor (γ a) u v w) =
          cov.curvatureTensor (γ b)
            (cov.parallelTransport γ a b u)
            (cov.parallelTransport γ a b v)
            (cov.parallelTransport γ a b w) := by
  refine ⟨fun h γ hγ a b u v w ↦
    h.parallelTransport_curvatureTensor (hγ.of_le (by simp)) a b u v w,
    fun h ↦ cov.hasParallelCurvature_iff.2 fun x ↦ ?_⟩
  ext ξ u v w
  obtain ⟨γ, hγ0, hγ, hvel⟩ := exists_contMDiff_curveVelocity_eq (I := I) (n := ∞) (by simp) x ξ 0
  subst hγ0
  have hγ1 : ContMDiff 𝓘(ℝ, ℝ) I 1 γ := hγ.of_le (by simp)
  have hconst_fn :
      (fun r ↦ cov.parallelTransport γ r 0
        (cov.curvatureTensor (γ r)
          (cov.parallelTransport γ 0 r u)
          (cov.parallelTransport γ 0 r v)
          (cov.parallelTransport γ 0 r w))) =
      fun _ ↦ cov.curvatureTensor (γ 0) u v w := by
    ext1 r
    rw [← h hγ 0 r u v w, cov.parallelTransport_trans_apply hγ1 0 r 0,
      cov.parallelTransport_self_apply hγ1 0]
  have hd := cov.hasDerivAt_parallelTransport_curvatureTensor hγ1 0 u v w
  rw [hconst_fn] at hd
  let _ : NormedAddCommGroup (TangentSpace I (γ 0)) := inferInstanceAs (NormedAddCommGroup E)
  let _ : NormedSpace ℝ (TangentSpace I (γ 0)) := inferInstanceAs (NormedSpace ℝ E)
  have hd' : HasDerivAt (fun _ : ℝ ↦ cov.curvatureTensor (γ 0) u v w)
      (cov.derivCurvatureTensor cov (γ 0) (curveVelocity I γ 0) u v w) 0 := by
    simpa using! hd
  rw [LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply,
    ← hvel]
  exact hd'.unique (hasDerivAt_const 0 (cov.curvatureTensor (γ 0) u v w))

/-- **Parallel-transport characterization of parallel curvature (on `[0, 1]`).**
On a boundaryless manifold, a smooth connection on the tangent bundle has parallel curvature
(`∇R = 0`) if and only if parallel transport from `0` to `1` along every smooth path on `Icc 0 1`
intertwines its curvature tensor. -/
theorem hasParallelCurvature_iff_parallelTransportWithin_Icc [I.Boundaryless] :
    cov.HasParallelCurvature ↔
      ∀ ⦃γ : ℝ → M⦄, CMDiff[Icc 0 1] ∞ γ → ∀ (u v w : TangentSpace I (γ 0)),
        cov.parallelTransportWithin γ (Icc 0 1) 0 1 (cov.curvatureTensor (γ 0) u v w) =
          cov.curvatureTensor (γ 1)
            (cov.parallelTransportWithin γ (Icc 0 1) 0 1 u)
            (cov.parallelTransportWithin γ (Icc 0 1) 0 1 v)
            (cov.parallelTransportWithin γ (Icc 0 1) 0 1 w) := by
  refine ⟨fun h γ hγ u v w ↦
    h.parallelTransportWithin_curvatureTensor isPreconnected_Icc (hγ.of_le (by simp))
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ u v w,
    fun h ↦ cov.hasParallelCurvature_iff_parallelTransport.2 fun γ hγ a b ↦ ?_⟩
  let φ : ℝ → ℝ := fun r ↦ a + r * (b - a)
  have hφ : ContDiff ℝ ∞ φ := contDiff_const.add (contDiff_id.mul contDiff_const)
  have hφ0 : φ 0 = a := by simp [φ]
  have hφ1 : φ 1 = b := by simp [φ]
  rw [← hφ0, ← hφ1]
  intro u v w
  have hγ1 : ContMDiff 𝓘(ℝ, ℝ) I 1 γ := hγ.of_le (by simp)
  have hφ_c1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have heq : cov.parallelTransport γ (φ 0) (φ 1) =
      cov.parallelTransportWithin (γ ∘ φ) (Icc 0 1) 0 1 := by
    rw [← cov.parallelTransport_comp hφ_c1 hγ1 0 1,
      cov.parallelTransportWithin_eq_parallelTransport isPreconnected_Icc
        (hγ1.comp hφ_c1.contMDiff) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩]
  rw [heq]
  exact h (hγ.comp hφ.contMDiff).contMDiffOn u v w

end Affine

section Riemannian

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

section RiemannTensor

variable [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **Parallel curvature preserves the `(0,4)` Riemann curvature tensor** under parallel transport
along any `C¹` curve on a preconnected parameter set. -/
theorem HasParallelCurvature.riemannCurvatureTensor_parallelTransportWithin
    (h : cov.HasParallelCurvature)
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s) (u v w z : TangentSpace I (γ a)) :
    cov.riemannCurvatureTensor (γ b)
        (cov.parallelTransportWithin γ s a b u)
        (cov.parallelTransportWithin γ s a b v)
        (cov.parallelTransportWithin γ s a b w)
        (cov.parallelTransportWithin γ s a b z) =
      cov.riemannCurvatureTensor (γ a) u v w z := by
  rw [riemannCurvatureTensor_apply, riemannCurvatureTensor_apply,
    ← h.parallelTransportWithin_curvatureTensor hconn hγ ha hb u v w,
    hcov.inner_parallelTransportWithin hconn hγ ha hb]

/-- **Parallel curvature preserves the `(0,4)` Riemann curvature tensor** under unrestricted
parallel transport. -/
theorem HasParallelCurvature.riemannCurvatureTensor_parallelTransport
    (h : cov.HasParallelCurvature)
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ)
    (u v w z : TangentSpace I (γ a)) :
    cov.riemannCurvatureTensor (γ b)
        (cov.parallelTransport γ a b u)
        (cov.parallelTransport γ a b v)
        (cov.parallelTransport γ a b w)
        (cov.parallelTransport γ a b z) =
      cov.riemannCurvatureTensor (γ a) u v w z := by
  simpa only [parallelTransportWithin_univ] using
    h.riemannCurvatureTensor_parallelTransportWithin hcov isPreconnected_univ hγ.contMDiffOn
      (mem_univ a) (mem_univ b) u v w z

/-- Recovering `curvatureTensor` intertwining from `riemannCurvatureTensor` invariance by
nondegeneracy of the inner product and invertibility of parallel transport. -/
private theorem parallelTransportWithin_curvatureTensor_of_riemannCurvatureTensor
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s)
    (hRm : ∀ u v w z : TangentSpace I (γ a),
      cov.riemannCurvatureTensor (γ b)
          (cov.parallelTransportWithin γ s a b u)
          (cov.parallelTransportWithin γ s a b v)
          (cov.parallelTransportWithin γ s a b w)
          (cov.parallelTransportWithin γ s a b z) =
        cov.riemannCurvatureTensor (γ a) u v w z)
    (u v w : TangentSpace I (γ a)) :
    cov.parallelTransportWithin γ s a b (cov.curvatureTensor (γ a) u v w) =
      cov.curvatureTensor (γ b)
        (cov.parallelTransportWithin γ s a b u)
        (cov.parallelTransportWithin γ s a b v)
        (cov.parallelTransportWithin γ s a b w) := by
  refine ext_inner_right ℝ fun y ↦ ?_
  let z := cov.parallelTransportWithin γ s b a y
  have hz : cov.parallelTransportWithin γ s a b z = y := by
    rw [cov.parallelTransportWithin_trans_apply hconn hγ hb ha hb,
      cov.parallelTransportWithin_self_apply hconn hγ hb]
  rw [← hz, hcov.inner_parallelTransportWithin hconn hγ ha hb,
    ← riemannCurvatureTensor_apply, ← riemannCurvatureTensor_apply, (hRm u v w z).symm]

/-- **Metric-lowered `(0,4)`-tensor characterization of parallel curvature (on `ℝ`).**
For a metric-compatible connection on a boundaryless manifold, `∇R = 0` if and only if parallel
transport along every smooth curve `γ : ℝ → M` preserves the `(0,4)` Riemann curvature tensor. -/
theorem IsMetricCompatible.hasParallelCurvature_iff_riemannCurvatureTensor_parallelTransport
    [I.Boundaryless]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov) :
    cov.HasParallelCurvature ↔
      ∀ ⦃γ : ℝ → M⦄, CMDiff ∞ γ → ∀ (a b : ℝ) (u v w z : TangentSpace I (γ a)),
        cov.riemannCurvatureTensor (γ b)
            (cov.parallelTransport γ a b u)
            (cov.parallelTransport γ a b v)
            (cov.parallelTransport γ a b w)
            (cov.parallelTransport γ a b z) =
          cov.riemannCurvatureTensor (γ a) u v w z := by
  refine ⟨fun h γ hγ a b u v w z ↦
    h.riemannCurvatureTensor_parallelTransport hcov (hγ.of_le (by simp)) a b u v w z,
    fun h ↦ cov.hasParallelCurvature_iff_parallelTransport.2 fun γ hγ a b u v w ↦ ?_⟩
  simpa only [parallelTransportWithin_univ] using
    parallelTransportWithin_curvatureTensor_of_riemannCurvatureTensor hcov isPreconnected_univ
      (hγ.of_le (by simp)).contMDiffOn (mem_univ a) (mem_univ b)
      (by simpa only [parallelTransportWithin_univ] using h hγ a b) u v w

namespace IsMetricCompatible

/-- **Metric-lowered `(0,4)`-tensor characterization of parallel curvature (on `[0, 1]`).** -/
theorem hasParallelCurvature_iff_riemannCurvatureTensor_parallelTransportWithin_Icc
    [I.Boundaryless]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov) :
    cov.HasParallelCurvature ↔
      ∀ ⦃γ : ℝ → M⦄, CMDiff[Icc 0 1] ∞ γ → ∀ (u v w z : TangentSpace I (γ 0)),
        cov.riemannCurvatureTensor (γ 1)
            (cov.parallelTransportWithin γ (Icc 0 1) 0 1 u)
            (cov.parallelTransportWithin γ (Icc 0 1) 0 1 v)
            (cov.parallelTransportWithin γ (Icc 0 1) 0 1 w)
            (cov.parallelTransportWithin γ (Icc 0 1) 0 1 z) =
          cov.riemannCurvatureTensor (γ 0) u v w z := by
  refine ⟨fun h γ hγ u v w z ↦
    h.riemannCurvatureTensor_parallelTransportWithin hcov isPreconnected_Icc (hγ.of_le (by simp))
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ u v w z,
    fun h ↦ cov.hasParallelCurvature_iff_parallelTransportWithin_Icc.2 fun γ hγ u v w ↦ ?_⟩
  exact parallelTransportWithin_curvatureTensor_of_riemannCurvatureTensor hcov isPreconnected_Icc
    (hγ.of_le (by simp)) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ (h hγ) u v w

end IsMetricCompatible

end RiemannTensor

section Sectional

variable [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]

/-- **Parallel curvature preserves sectional curvature** under parallel transport along any `C¹`
curve on a preconnected parameter set. No torsion-free or linear-independence hypothesis is
required. -/
theorem HasParallelCurvature.sectionalCurvature_parallelTransportWithin
    (h : cov.HasParallelCurvature)
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s) (u v : TangentSpace I (γ a)) :
    cov.sectionalCurvature hcov (γ b)
        (cov.parallelTransportWithin γ s a b u) (cov.parallelTransportWithin γ s a b v) =
      cov.sectionalCurvature hcov (γ a) u v := by
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    .of_le (show (1 : ℕ∞ω) ≤ 2 by simp)
  rw [sectionalCurvature_apply, sectionalCurvature_apply,
    Matrix.real_det_gram_fin_two, Matrix.real_det_gram_fin_two,
    ← riemannCurvatureTensor_apply, ← riemannCurvatureTensor_apply,
    h.riemannCurvatureTensor_parallelTransportWithin hcov hconn hγ ha hb,
    hcov.inner_parallelTransportWithin hconn hγ ha hb,
    hcov.inner_parallelTransportWithin hconn hγ ha hb,
    hcov.inner_parallelTransportWithin hconn hγ ha hb]

/-- **Parallel curvature preserves sectional curvature** under unrestricted parallel transport. -/
theorem HasParallelCurvature.sectionalCurvature_parallelTransport
    (h : cov.HasParallelCurvature)
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ)
    (u v : TangentSpace I (γ a)) :
    cov.sectionalCurvature hcov (γ b)
        (cov.parallelTransport γ a b u) (cov.parallelTransport γ a b v) =
      cov.sectionalCurvature hcov (γ a) u v := by
  simpa only [parallelTransportWithin_univ] using
    h.sectionalCurvature_parallelTransportWithin hcov isPreconnected_univ hγ.contMDiffOn
      (mem_univ a) (mem_univ b) u v

/-- Polarizing sectional-curvature invariance on linearly independent pairs into invariance of the
`(0,4)` Riemann curvature tensor for a metric-compatible torsion-free connection. -/
private theorem riemannCurvatureTensor_parallelTransportWithin_of_sectionalCurvature
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s)
    (hsec : ∀ u v : TangentSpace I (γ a), LinearIndependent ℝ ![u, v] →
      cov.sectionalCurvature hcov (γ b)
          (cov.parallelTransportWithin γ s a b u) (cov.parallelTransportWithin γ s a b v) =
        cov.sectionalCurvature hcov (γ a) u v)
    (u v w z : TangentSpace I (γ a)) :
    cov.riemannCurvatureTensor (γ b)
        (cov.parallelTransportWithin γ s a b u)
        (cov.parallelTransportWithin γ s a b v)
        (cov.parallelTransportWithin γ s a b w)
        (cov.parallelTransportWithin γ s a b z) =
      cov.riemannCurvatureTensor (γ a) u v w z := by
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    .of_le (show (1 : ℕ∞ω) ≤ 2 by simp)
  let P := cov.parallelTransportWithin γ s a b
  let T : TangentSpace I (γ a) →ₗ[ℝ] TangentSpace I (γ a) →ₗ[ℝ]
      TangentSpace I (γ a) →ₗ[ℝ] TangentSpace I (γ a) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun u' v' ↦ LinearMap.mk₂ ℝ
        (fun w' z' ↦ cov.riemannCurvatureTensor (γ b) (P u') (P v') (P w') (P z'))
        (fun _ _ _ ↦ by simp only [map_add, LinearMap.add_apply])
        (fun _ _ _ ↦ by simp only [map_smul, LinearMap.smul_apply])
        (fun _ _ _ ↦ by simp only [map_add])
        (fun _ _ _ ↦ by simp only [map_smul]))
      (fun _ _ _ ↦ by ext; simp only [LinearMap.mk₂_apply, LinearMap.add_apply, map_add])
      (fun _ _ _ ↦ by ext; simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, map_smul])
      (fun _ _ _ ↦ by ext; simp only [LinearMap.mk₂_apply, LinearMap.add_apply, map_add])
      (fun _ _ _ ↦ by ext; simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, map_smul])
  have hT_eq : cov.riemannCurvatureTensor (γ a) = T :=
    hcov.riemannCurvatureTensor_eq_of_forall_linearIndependent ht (γ a)
      (fun u' v' w' z' ↦
        cov.riemannCurvatureTensor_antisymm_first (γ b) (P u') (P v') (P w') (P z'))
      (fun u' v' w' z' ↦
        hcov.riemannCurvatureTensor_antisymm_last cov (γ b) (P u') (P v') (P w') (P z'))
      (fun u' v' w' z' ↦
        cov.riemannCurvatureTensor_cyclic_eq_zero ht (γ b) (P u') (P v') (P w') (P z'))
      fun u' v' huv ↦ by
        have hd_eq : (Matrix.gram ℝ ![P u', P v']).det = (Matrix.gram ℝ ![u', v']).det := by
          simp only [P, Matrix.real_det_gram_fin_two,
            hcov.inner_parallelTransportWithin hconn hγ ha hb]
        dsimp only [P] at hd_eq
        have hd_ne : (Matrix.gram ℝ ![u', v']).det ≠ 0 :=
          Matrix.det_gram_ne_zero_iff_linearIndependent.2 huv
        have hm := congrArg (· * (Matrix.gram ℝ ![u', v']).det) (hsec u' v' huv).symm
        simpa only [P, sectionalCurvature_apply, hd_eq, div_mul_cancel₀ _ hd_ne,
          ← riemannCurvatureTensor_apply, T, LinearMap.mk₂_apply] using hm
  exact (congr($hT_eq u v w z)).symm

/-- **Sectional-curvature characterization of parallel curvature (on `ℝ`).**
For a metric-compatible torsion-free connection (such as the Levi-Civita connection) on a
boundaryless manifold, `∇R = 0` if and only if parallel transport along every smooth curve
`γ : ℝ → M` preserves sectional curvature on all linearly independent tangent pairs. -/
theorem IsMetricCompatible.hasParallelCurvature_iff_sectionalCurvature_parallelTransport
    [I.Boundaryless]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) :
    cov.HasParallelCurvature ↔
      ∀ ⦃γ : ℝ → M⦄, CMDiff ∞ γ → ∀ (a b : ℝ) (u v : TangentSpace I (γ a)),
        LinearIndependent ℝ ![u, v] →
          cov.sectionalCurvature hcov (γ b)
              (cov.parallelTransport γ a b u) (cov.parallelTransport γ a b v) =
            cov.sectionalCurvature hcov (γ a) u v := by
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    .of_le (show (1 : ℕ∞ω) ≤ 2 by simp)
  refine ⟨fun h γ hγ a b u v _ ↦
    h.sectionalCurvature_parallelTransport hcov (hγ.of_le (by simp)) a b u v,
    fun h ↦ hcov.hasParallelCurvature_iff_riemannCurvatureTensor_parallelTransport.2
      fun γ hγ a b u v w z ↦ ?_⟩
  simpa only [parallelTransportWithin_univ] using
    riemannCurvatureTensor_parallelTransportWithin_of_sectionalCurvature hcov ht
      isPreconnected_univ (hγ.of_le (by simp)).contMDiffOn (mem_univ a) (mem_univ b)
      (by simpa only [parallelTransportWithin_univ] using h hγ a b) u v w z

/-- **Sectional-curvature characterization of parallel curvature (on `[0, 1]`).** -/
theorem IsMetricCompatible.hasParallelCurvature_iff_sectionalCurvature_parallelTransportWithin_Icc
    [I.Boundaryless]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) :
    cov.HasParallelCurvature ↔
      ∀ ⦃γ : ℝ → M⦄, CMDiff[Icc 0 1] ∞ γ → ∀ (u v : TangentSpace I (γ 0)),
        LinearIndependent ℝ ![u, v] →
          cov.sectionalCurvature hcov (γ 1)
              (cov.parallelTransportWithin γ (Icc 0 1) 0 1 u)
              (cov.parallelTransportWithin γ (Icc 0 1) 0 1 v) =
            cov.sectionalCurvature hcov (γ 0) u v := by
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    .of_le (show (1 : ℕ∞ω) ≤ 2 by simp)
  refine ⟨fun h γ hγ u v _ ↦
    h.sectionalCurvature_parallelTransportWithin hcov isPreconnected_Icc (hγ.of_le (by simp))
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ u v,
    fun h ↦ hcov.hasParallelCurvature_iff_riemannCurvatureTensor_parallelTransportWithin_Icc.2
      fun γ hγ u v w z ↦ ?_⟩
  exact riemannCurvatureTensor_parallelTransportWithin_of_sectionalCurvature hcov ht
    isPreconnected_Icc (hγ.of_le (by simp)) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    (h hγ) u v w z

end Sectional

end Riemannian

end CovariantDerivative

end
