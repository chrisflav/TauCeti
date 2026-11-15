/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Parallel.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Covariant derivative via parallel transport

Pulling a differentiable tangent field `V` along a `C¹` curve `γ` back to a fixed parameter `t` by
parallel transport `r ↦ P_{r → t} (V r)` produces a curve in the single vector space
`T_{γ(t)} M` whose ordinary derivative at `r = t` is the covariant derivative `D_t V(t)`
(`CovariantDerivative.hasDerivWithinAt_parallelTransportWithin` and
`CovariantDerivative.hasDerivAt_parallelTransport`).

In the canonical trivialization at `γ(t)`, transporting a basis of the model space `E` forward
from `t` to `r` gives a differentiable family of endomorphisms `A(r) : E →L[ℝ] E` with `A(t) = 1`.
Since algebra inversion `Ring.inverse` on `E →L[ℝ] E` is differentiable at `1`, the pullback
`r ↦ P_{r → t} (V r)` has differentiable coordinate components `c_i(r)` in the parallel frame
`E_i(r) = P_{t → r} e_i`, and expanding `V(r) = ∑_i c_i(r) • E_i(r)` identifies `D_t V(t)` with
`∑_i c_i'(t) • E_i(t)`.

## Main results

* `CovariantDerivative.hasDerivWithinAt_parallelTransportWithin`:
  `(d/dr)|_{r = t} P_{r → t}(V(r)) = D_t V(t)` within any preconnected parameter set `s`.
* `CovariantDerivative.hasDerivAt_parallelTransport`:
  the unrestricted (`s = Set.univ`) form on `ℝ`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 4,
  Theorem 4.34.
-/

public section

open Bundle ContinuousLinearMap FiberBundle Filter Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov ∞]

/-- Forward parallel transport `P_{t → r}` read in the canonical trivialization at `γ(t)` is
differentiable in `r` within `s` at `t` and equals `1` at `r = t`. -/
private theorem exists_differentiableWithinAt_parallelTransportWithin_chart
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ht : t ∈ s) :
    let e := trivializationAt E (TangentSpace I) (γ t)
    ∃ A : ℝ → E →L[ℝ] E, DifferentiableWithinAt ℝ A s t ∧ A t = 1 ∧
      ∀ r u, A r u = e.continuousLinearMapAt ℝ (γ r)
        (cov.parallelTransportWithin γ s t r (e.symmL ℝ (γ t) u)) := by
  intro e
  let b := Module.finBasis ℝ E
  let E_frame (i : Fin (Module.finrank ℝ E)) (r : ℝ) : TangentSpace I (γ r) :=
    cov.parallelTransportWithin γ s t r (e.symmL ℝ (γ t) (b i))
  have hx : γ t ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  let A (r : ℝ) : E →L[ℝ] E :=
    ∑ i, ((b.coord i).toContinuousLinearMap).smulRight
      (sectionCoord (F := E) γ (E_frame i) (γ t) r)
  have hA_apply (r : ℝ) (u : E) :
      A r u = e.continuousLinearMapAt ℝ (γ r)
        (cov.parallelTransportWithin γ s t r (e.symmL ℝ (γ t) u)) := by
    have hu : ∑ i, b.coord i u • b i = u := by simpa only [b.coord_apply] using b.sum_repr u
    conv_rhs => rw [← hu]
    simp only [A, e, sum_apply, smulRight_apply, LinearMap.coe_toContinuousLinearMap',
      sectionCoord_apply, E_frame, map_sum, map_smul]
  have hA_diff : DifferentiableWithinAt ℝ A s t :=
    (DifferentiableWithinAt.sum (u := Finset.univ) fun i _ ↦
      (ContinuousLinearMap.smulRightL ℝ E E ((b.coord i).toContinuousLinearMap)).differentiableAt
        |>.comp_differentiableWithinAt t
          (cov.differentiableWithinAt_sectionCoord_parallelTransportWithin hconn hγ ht ht hx
            (e.symmL ℝ (γ t) (b i)))).congr
      (fun r _ ↦ by ext u; simp only [A, E_frame, Finset.sum_apply, sum_apply,
        Function.comp_apply, smulRightL_apply_apply, smulRight_apply])
      (by ext u; simp only [A, E_frame, Finset.sum_apply, sum_apply,
        Function.comp_apply, smulRightL_apply_apply, smulRight_apply])
  have hAt : A t = 1 := by
    ext u
    rw [hA_apply, one_apply_eq_self, cov.parallelTransportWithin_self_apply hconn hγ ht,
      e.continuousLinearMapAt_symmL hx]
  exact ⟨A, hA_diff, hAt, hA_apply⟩

/-- Pulling a field `V` with differentiable coordinate reading back to `t` via parallel transport
produces a differentiable curve in the model space `E`. -/
private theorem differentiableWithinAt_parallelTransportWithin_pullback
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {V : ∀ r, TangentSpace I (γ r)}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ht : t ∈ s)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t) :
    DifferentiableWithinAt ℝ (fun r ↦
      (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ t)
        (cov.parallelTransportWithin γ s r t (V r))) s t := by
  let e := trivializationAt E (TangentSpace I) (γ t)
  have hx : γ t ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  obtain ⟨A, hA_diff, hAt, hA_apply⟩ :=
    exists_differentiableWithinAt_parallelTransportWithin_chart cov hconn hγ ht
  have hnear : ∀ᶠ r in 𝓝[s] t, r ∈ s ∧ γ r ∈ e.baseSet :=
    inter_mem self_mem_nhdsWithin
      ((hγ t ht).continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx))
  have hinv_eq {r : ℝ} (hrs : r ∈ s) (hxr : γ r ∈ e.baseSet) :
      Ring.inverse (A r) =
        (e.continuousLinearMapAt ℝ (γ t)).comp
          ((cov.parallelTransportWithin γ s r t).comp (e.symmL ℝ (γ r))) := by
    let B : E →L[ℝ] E :=
      (e.continuousLinearMapAt ℝ (γ t)).comp
        ((cov.parallelTransportWithin γ s r t).comp (e.symmL ℝ (γ r)))
    let u_r : (E →L[ℝ] E)ˣ := ⟨A r, B, by
      ext u
      rw [mul_apply_eq_comp, comp_apply, hA_apply, one_apply_eq_self]
      simp only [e, comp_apply,
        Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hx,
        cov.parallelTransportWithin_trans_apply hconn hγ hrs ht hrs,
        cov.parallelTransportWithin_self_apply hconn hγ hrs,
        Trivialization.continuousLinearMapAt_symmL (R := ℝ) _ hxr],
      by
      ext u
      rw [mul_apply_eq_comp, comp_apply, one_apply_eq_self]
      simp only [e, comp_apply, hA_apply,
        Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hxr,
        cov.parallelTransportWithin_trans_apply hconn hγ ht hrs ht,
        cov.parallelTransportWithin_self_apply hconn hγ ht,
        Trivialization.continuousLinearMapAt_symmL (R := ℝ) _ hx]⟩
    exact Ring.inverse_unit u_r
  refine ((hA_diff.inverse (hAt ▸ isUnit_one)).clm_apply hV).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hnear] with r ⟨hrs, hxr⟩
    rw [hinv_eq hrs hxr]
    simp only [e, comp_apply, sectionCoord_apply,
      Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hxr]
  · rw [hinv_eq ht hx]
    simp only [e, comp_apply, sectionCoord_apply,
      Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hx]

/-- **Covariant derivative recovered by differentiating parallel transport.**
Along a `C¹` curve `γ` on a preconnected parameter set `s`, for any tangent field `V` whose
coordinate reading at `t ∈ s` is differentiable within `s`, the curve
`r ↦ P_{r → t}(V(r))` in the fixed tangent space `T_{γ(t)} M` has derivative `D_t V(t)` within `s`
at `t`. -/
theorem hasDerivWithinAt_parallelTransportWithin
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {V : ∀ r, TangentSpace I (γ r)}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ht : t ∈ s)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t) :
    HasDerivWithinAt (fun r ↦ cov.parallelTransportWithin γ s r t (V r))
      (cov.alongCurveWithin γ V s t) s t := by
  let e := trivializationAt E (TangentSpace I) (γ t)
  let b := Module.finBasis ℝ E
  let E_frame (i : Fin (Module.finrank ℝ E)) (r : ℝ) : TangentSpace I (γ r) :=
    cov.parallelTransportWithin γ s t r (e.symmL ℝ (γ t) (b i))
  have hx : γ t ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  let g (r : ℝ) : E := e.continuousLinearMapAt ℝ (γ t) (cov.parallelTransportWithin γ s r t (V r))
  have hg_diff : DifferentiableWithinAt ℝ g s t :=
    differentiableWithinAt_parallelTransportWithin_pullback cov hconn hγ ht hV
  let c (i : Fin (Module.finrank ℝ E)) (r : ℝ) : ℝ := b.coord i (g r)
  have hc_diff (i) : DifferentiableWithinAt ℝ (c i) s t :=
    (b.coord i).toContinuousLinearMap.differentiableAt.comp_differentiableWithinAt t hg_diff
  have hV_exp {r : ℝ} (hrs : r ∈ s) : V r = ∑ i, c i r • E_frame i r := by
    have hsum : ∑ i, c i r • b i = g r := by simpa only [c, b.coord_apply] using b.sum_repr (g r)
    simpa only [g, E_frame, map_sum, map_smul, e.symmL_continuousLinearMapAt (R := ℝ) hx,
      cov.parallelTransportWithin_trans_apply hconn hγ hrs ht hrs,
      cov.parallelTransportWithin_self_apply hconn hγ hrs] using
      congrArg (fun u ↦ cov.parallelTransportWithin γ s t r (e.symmL ℝ (γ t) u)) hsum.symm
  have hE_coord (i) : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (E_frame i) (γ t)) s t :=
    cov.differentiableWithinAt_sectionCoord_parallelTransportWithin hconn hγ ht ht hx _
  have hD_eq : cov.alongCurveWithin γ V s t =
      e.symmL ℝ (γ t) (∑ i, derivWithin (c i) s t • b i) := by
    rw [alongCurveWithin_congr cov γ V
      (eventually_nhdsWithin_of_forall fun r hr ↦ hV_exp hr) (hV_exp ht),
      alongCurveWithin_sum cov γ Finset.univ (fun i r ↦ c i r • E_frame i r) fun i _ ↦ by
        rw [sectionCoord_smul]; exact (hc_diff i).smul (hE_coord i),
      map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [alongCurveWithin_smul cov γ (E_frame i) (c i) s (hc_diff i) (hE_coord i)]
    dsimp only [E_frame]
    rw [cov.alongCurveWithin_parallelTransportWithin hconn hγ ht ht, smul_zero, add_zero, map_smul,
      cov.parallelTransportWithin_self_apply hconn hγ ht]
  have hg_sum : g = fun r ↦ ∑ i, c i r • b i :=
    funext fun r ↦ by simpa only [c, b.coord_apply] using (b.sum_repr (g r)).symm
  have hg_deriv : HasDerivWithinAt g (∑ i, derivWithin (c i) s t • b i) s t := by
    rw [hg_sum]
    exact (HasDerivWithinAt.sum (u := Finset.univ) fun i _ ↦
      (hc_diff i).hasDerivWithinAt.smul_const (b i)).congr (fun _ _ ↦ by simp) (by simp)
  let _ : NormedAddCommGroup (TangentSpace I (γ t)) := inferInstanceAs (NormedAddCommGroup E)
  let _ : NormedSpace ℝ (TangentSpace I (γ t)) := inferInstanceAs (NormedSpace ℝ E)
  have hsymm_deriv := (e.symmL ℝ (γ t)).hasFDerivAt.comp_hasDerivWithinAt t hg_deriv
  simpa only [Function.comp_def, g, e.symmL_continuousLinearMapAt (R := ℝ) hx,
    ContinuousLinearMap.coe_coe, hD_eq] using! hsymm_deriv

/-- **Covariant derivative recovered by differentiating unrestricted parallel transport.** -/
theorem hasDerivAt_parallelTransport
    {γ : ℝ → M} {t : ℝ} {V : ∀ r, TangentSpace I (γ r)}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t) :
    HasDerivAt (fun r ↦ cov.parallelTransport γ r t (V r)) (cov.alongCurve γ V t) t := by
  rw [← alongCurveWithin_univ]
  simpa only [HasDerivWithinAt, HasDerivAt, nhdsWithin_univ, parallelTransportWithin_univ] using
    cov.hasDerivWithinAt_parallelTransportWithin isPreconnected_univ
      hγ.contMDiffOn (mem_univ t) hV.differentiableWithinAt

end CovariantDerivative

end
