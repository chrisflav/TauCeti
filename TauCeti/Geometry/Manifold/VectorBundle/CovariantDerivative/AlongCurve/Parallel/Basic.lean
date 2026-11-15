/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Chart
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Order.ProjIcc
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.ODE.DysonSeries
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Regularity

/-!
# Parallel transport of tangent vectors along curves

For a connection `∇` on the tangent bundle of a real manifold and a `C¹` curve `γ : ℝ → M` on a
preconnected parameter set `s`, every tangent vector `v ∈ T_{γ(a)} M` (`a ∈ s`) extends uniquely
to a parallel tangent field `V` along `γ` on `s`, solving the linear initial-value problem
`D_t V = 0` with `V(a) = v`. Evaluating that parallel field at `b ∈ s` defines the parallel
transport operator `CovariantDerivative.parallelTransportWithin cov γ s a b`, a continuous linear
map `T_{γ(a)} M →L[ℝ] T_{γ(b)} M`, with `CovariantDerivative.parallelTransport` its unrestricted
case `s = Set.univ`.

No metric or torsion condition is needed for existence, uniqueness, invertibility, transitivity,
higher `C^k` regularity, parameter-set restriction, or reparametrization invariance. Differentiating
parallel transport with respect to its initial parameter and metric-compatible isometry properties
are proved in `AlongCurve/Parallel/Deriv.lean` and `AlongCurve/Parallel/Metric.lean`.

In a single chart around a compact parameter subinterval, reading `D_t V = 0` in the preferred
trivialization turns it into a linear operator ODE on the model space `E`, solved via the left
Dyson series `TauCeti.dysonSeriesLeft` after clamping the continuous Christoffel operator to the
subinterval. Connectedness propagates uniqueness and existence across arbitrary compact intervals
and then across any preconnected parameter set.

## Main definitions and results

* `CovariantDerivative.parallelTransportWithin` and `CovariantDerivative.parallelTransport`:
  parallel transport of tangent vectors along a curve within a parameter set `s` and on `ℝ`.
* `CovariantDerivative.eq_of_alongCurveWithin_eq_zero` and
  `CovariantDerivative.eq_of_alongCurve_eq_zero`: uniqueness of parallel tangent fields along a
  `C¹` curve on a preconnected set, without any metric assumption.
* `CovariantDerivative.exists_alongCurveWithin_eq_zero`: existence of `C¹` parallel tangent fields
  along a `C¹` curve on a preconnected set, assuming only continuity of Christoffel symbols.
* `CovariantDerivative.parallelTransportWithin_self`,
  `CovariantDerivative.alongCurveWithin_parallelTransportWithin`, and
  `CovariantDerivative.contMDiffOn_parallelTransportWithin`: initial value, parallel equation, and
  `C^k` (`1 ≤ k ≤ ∞`) regularity of parallel transport.
* `CovariantDerivative.eq_parallelTransportWithin_of_alongCurveWithin_eq_zero` and
  `CovariantDerivative.forall_alongCurveWithin_eq_zero_iff_parallelTransportWithin`: parallel
  fields are precisely the parallel transports of their initial values.
* `CovariantDerivative.parallelTransportWithin_trans`,
  `CovariantDerivative.parallelTransportWithinEquiv`,
  `CovariantDerivative.parallelTransportWithin_subset`, and
  `CovariantDerivative.parallelTransportWithin_comp`: functorial composition, continuous linear
  equivalence packaging, parameter-set restriction, and reparametrization invariance.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 4,
  Theorem 4.32 and Proposition 4.33.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience (1963),
  Chapter II, Section 3.
-/

public section

open Bundle ContinuousLinearMap FiberBundle Filter Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

section Defs

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-- A `C¹` family of continuous linear maps `P t : T_{γ(a)} M →L[ℝ] T_{γ(t)} M` solving the
parallel-transport initial-value problem on `s` from `a`. -/
def IsParallelPropagatorOn
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (γ : ℝ → M) (s : Set ℝ) (a : ℝ)
    (P : ∀ t, TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ t)) : Prop :=
  (∀ v, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
    (fun t ↦ TotalSpace.mk' E (γ t) (P t v)) s) ∧
  (∀ v, P a v = v) ∧
  (∀ v, ∀ t ∈ s, alongCurveWithin cov γ (fun r ↦ P r v) s t = 0)

/-- **Parallel transport of tangent vectors along a curve within a parameter set.**
For a preconnected parameter set `s` containing `a` and `b`, a `C¹` curve `γ` on `s`, and a
connection `cov` with continuous Christoffel symbols along `γ(s)`,
`cov.parallelTransportWithin γ s a b v` is the value at `b` of the unique parallel tangent field
along `γ` on `s` taking the value `v` at `a`. Outside those hypotheses it carries the junk value
`0`. -/
def parallelTransportWithin
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (γ : ℝ → M) (s : Set ℝ) (a b : ℝ) :
    TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ b) :=
  open Classical in
  if h : IsPreconnected s ∧ a ∈ s ∧ ∃ P, IsParallelPropagatorOn cov γ s a P then
    if b ∈ s then h.2.2.choose b else 0
  else 0

/-- **Parallel transport of tangent vectors along a curve on `ℝ`.**
This is the unrestricted (`s = Set.univ`) case of `CovariantDerivative.parallelTransportWithin`. -/
def parallelTransport
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (γ : ℝ → M) (a b : ℝ) :
    TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ b) :=
  cov.parallelTransportWithin γ Set.univ a b

/-- Parallel transport within `Set.univ` is unrestricted parallel transport. -/
@[simp]
theorem parallelTransportWithin_univ
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (γ : ℝ → M) (a b : ℝ) :
    cov.parallelTransportWithin γ Set.univ a b = cov.parallelTransport γ a b :=
  (rfl)

/-- Unrestricted parallel transport is parallel transport within `Set.univ`. -/
theorem parallelTransport_def
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (γ : ℝ → M) (a b : ℝ) :
    cov.parallelTransport γ a b = cov.parallelTransportWithin γ Set.univ a b :=
  (rfl)

/-- Parallel transport within `s` vanishes when the initial parameter lies outside `s`. -/
theorem parallelTransportWithin_of_notMem_left
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ} (ha : a ∉ s) :
    cov.parallelTransportWithin γ s a b = 0 := by
  simp [parallelTransportWithin, ha]

/-- Parallel transport within `s` vanishes when the target parameter lies outside `s`. -/
theorem parallelTransportWithin_of_notMem_right
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ} (hb : b ∉ s) :
    cov.parallelTransportWithin γ s a b = 0 := by
  simp [parallelTransportWithin, hb]

/-- Parallel transport within `s` vanishes when `s` is not preconnected. -/
theorem parallelTransportWithin_of_not_isPreconnected
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ} (hs : ¬ IsPreconnected s) :
    cov.parallelTransportWithin γ s a b = 0 := by
  simp [parallelTransportWithin, hs]

end Defs

/-! ### Local and global ODE theory in affine generality -/

section LocalODE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))

omit [FiniteDimensional ℝ E] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- Differentiability of `sectionCoord` transfers from the moving chart at `γ t` to any fixed chart
whose base set contains `γ t`. -/
private theorem differentiableWithinAt_sectionCoord_of_mem_baseSet
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {s : Set ℝ} {t : ℝ} {x : M}
    (hx : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t) :
    DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V x) s t := by
  have hc0 : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hxsrc : γ t ∈ (extChartAt I x).source := by rwa [extChartAt_source]
  have hAmd : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E) (tangentCoordChange I (γ t) x) (γ t) := by
    have : IsManifold I (1 + 1) M := inferInstanceAs (IsManifold I 2 M)
    exact (contMDiffAt_tangentCoordChange (I := I) (n := 1) (x := γ t) (y := x)
      hxsrc).mdifferentiableAt one_ne_zero
  exact (((hAmd.comp_mdifferentiableWithinAt t hγ).differentiableWithinAt).clm_apply hV)
    |>.congr_of_eventuallyEq
      (sectionCoord_eventuallyEq_coordChange γ V hγ.continuousWithinAt hc0 hx)
      (sectionCoord_coordChange γ V hc0 hx)

/-- The clamped model-space connection operator `-Γ(γ(r))(·, u'(r))` on a compact interval
`Icc p q` contained in the chart at `x`. -/
private def chartConnectionOperator (γ : ℝ → M) (x : M) {p q : ℝ} (hpq : p ≤ q) (r : ℝ) :
    E →L[ℝ] E :=
  let t : ℝ := projIcc p q hpq r;
  -(christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet))
      (γ t)).flip (derivWithin (extChartAt I x ∘ γ) (Icc p q) t)

private theorem continuous_chartConnectionOperator {γ : ℝ → M} {x : M} {p q : ℝ} (hpq : p < q)
    (hbase : ∀ t ∈ Icc p q, γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc p q))
    (hΓ : ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet)))
      (trivializationAt E (TangentSpace I) x).baseSet) :
    Continuous (chartConnectionOperator cov γ x hpq.le) := by
  have hu : ContDiffOn ℝ 1 (extChartAt I x ∘ γ) (Icc p q) := fun t ht ↦
    ((contMDiffAt_extChartAt' (by
      simpa only [TangentBundle.trivializationAt_baseSet] using hbase t ht)).comp_contMDiffWithinAt
      t (hγ t ht)).contDiffWithinAt
  have hdu : ContinuousOn (derivWithin (extChartAt I x ∘ γ) (Icc p q)) (Icc p q) :=
    hu.continuousOn_derivWithin (uniqueDiffOn_Icc hpq) le_rfl
  have hΓγ : ContinuousOn (fun t ↦ (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet))
      (γ t)).flip) (Icc p q) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E E).continuous.comp_continuousOn
      (hΓ.comp hγ.continuousOn hbase)
  have h_on : ContinuousOn (fun t ↦ -(christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet))
      (γ t)).flip (derivWithin (extChartAt I x ∘ γ) (Icc p q) t)) (Icc p q) :=
    (hΓγ.clm_apply hdu).neg
  exact h_on.domRestrict.comp continuous_projIcc

private theorem chartConnectionOperator_of_mem {γ : ℝ → M} {x : M} {p q t : ℝ} (hpq : p ≤ q)
    (ht : t ∈ Icc p q) (w : E) :
    chartConnectionOperator cov γ x hpq t w =
      -christoffelMap (Module.finBasis ℝ E)
        (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet))
        (γ t) w (derivWithin (extChartAt I x ∘ γ) (Icc p q) t) := by
  simp [chartConnectionOperator, projIcc_of_mem hpq ht]

/-- Single-chart uniqueness: a parallel tangent field on `Icc p q` inside one chart that vanishes
at one parameter vanishes on the whole interval. -/
private theorem eq_zero_of_alongCurveWithin_eq_zero_chart {γ : ℝ → M} {x : M} {p q : ℝ}
    (hpq : p < q)
    (hbase : ∀ t ∈ Icc p q, γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc p q))
    (hΓ : ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet)))
      (trivializationAt E (TangentSpace I) x).baseSet)
    {V : ∀ r, TangentSpace I (γ r)}
    (hV : ∀ t ∈ Icc p q, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) (Icc p q) t)
    (hV₀ : ∀ t ∈ Icc p q, alongCurveWithin cov γ V (Icc p q) t = 0)
    {a b : ℝ} (ha : a ∈ Icc p q) (hb : b ∈ Icc p q) (hVa : V a = 0) :
    V b = 0 := by
  let e := trivializationAt E (TangentSpace I) x
  let M_op := chartConnectionOperator cov γ x hpq.le
  have hM : Continuous M_op := continuous_chartConnectionOperator cov hpq hbase hγ hΓ
  let w := sectionCoord (F := E) γ V x
  have hw_deriv : ∀ t ∈ Icc p q, HasDerivWithinAt w (M_op t (w t)) (Icc p q) t := by
    intro t ht
    have hγt := (hγ t ht).mdifferentiableWithinAt one_ne_zero
    have hwx := differentiableWithinAt_sectionCoord_of_mem_baseSet (hbase t ht) hγt (hV t ht)
    have hchart := symmL_alongCurveInChartWithin cov γ V (hbase t ht) hγt (hV t ht)
    rw [hV₀ t ht] at hchart
    have hinChart : alongCurveInChartWithin cov γ V (Icc p q) x t = 0 := by
      simpa only [e, Trivialization.continuousLinearMapAt_symmL _ (hbase t ht), map_zero] using
        congrArg (e.continuousLinearMapAt ℝ (γ t)) hchart
    rw [alongCurveInChartWithin_apply, add_eq_zero_iff_eq_neg] at hinChart
    exact hwx.hasDerivWithinAt.congr_deriv
      (hinChart.trans (chartConnectionOperator_of_mem cov hpq.le ht (w t)).symm)
  have hg : ∀ t ∈ Icc p q,
      HasDerivWithinAt (fun r ↦ TauCeti.dysonSeries (-M_op) r (w r)) 0 (Icc p q) t := by
    intro t ht
    refine (((TauCeti.hasDerivAt_dysonSeries hM.neg t).hasDerivWithinAt).clm_apply
      (hw_deriv t ht)).congr_deriv ?_
    simp [mul_apply_eq_comp]
  have hgb : TauCeti.dysonSeries (-M_op) b (w b) = 0 := by
    rw [IsPreconnected.eq_of_hasDerivWithinAt_zero isPreconnected_Icc hg hb ha]
    simp [w, hVa]
  have hwb : w b = 0 := by
    have hinv := congrArg (fun v ↦ TauCeti.dysonSeriesLeft M_op b v) hgb
    simpa [← mul_apply_eq_comp, TauCeti.dysonSeriesLeft_mul_dysonSeries_neg hM b,
      one_apply_eq_self] using hinv
  rw [← e.symmL_continuousLinearMapAt (R := ℝ) (hbase b hb) (V b)]
  dsimp only [w] at hwb
  simp only [e, ← sectionCoord_apply, hwb, map_zero]

/-- Compact-interval uniqueness of parallel tangent fields with zero initial value. -/
private theorem eq_zero_of_alongCurveWithin_eq_zero_Icc {γ : ℝ → M} {p₀ q₀ : ℝ} (hpq : p₀ < q₀)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc p₀ q₀))
    (hΓ : ∀ t ∈ Icc p₀ q₀, ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)))
      (trivializationAt E (TangentSpace I) (γ t)).baseSet)
    {U : ∀ r, TangentSpace I (γ r)}
    (hU : ∀ t ∈ Icc p₀ q₀,
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ U (γ t)) (Icc p₀ q₀) t)
    (hU₀ : ∀ t ∈ Icc p₀ q₀, alongCurveWithin cov γ U (Icc p₀ q₀) t = 0)
    {a b : ℝ} (ha : a ∈ Icc p₀ q₀) (hb : b ∈ Icc p₀ q₀) (hUa : U a = 0) :
    U b = 0 := by
  let S : Set (Icc p₀ q₀) := {t | U t.1 = 0}
  have hopen : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro t₀ ht₀
    let e := trivializationAt E (TangentSpace I) (γ t₀.1)
    have hcont : Continuous fun t : Icc p₀ q₀ ↦ γ t.1 := hγ.continuousOn.domRestrict
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (e.open_baseSet.preimage hcont) t₀
      (mem_baseSet_trivializationAt E (TangentSpace I) (γ t₀.1))
    let l := max p₀ (t₀.1 - δ / 2)
    let r := min q₀ (t₀.1 + δ / 2)
    have hlr : l < r := lt_min
      (max_lt hpq (by linarith [t₀.2.2])) (max_lt (by linarith [t₀.2.1]) (by linarith))
    have hsub : Icc l r ⊆ Icc p₀ q₀ := Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hbase : ∀ s ∈ Icc l r, γ s ∈ e.baseSet := fun s hs ↦ by
      refine @hball ⟨s, hsub hs⟩ ?_
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1, le_max_right p₀ (t₀.1 - δ / 2)],
        by linarith [hs.2, min_le_right q₀ (t₀.1 + δ / 2)]⟩
    refine ⟨δ / 2, half_pos hδ, fun t ht ↦ ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt] at ht
    have htlr : t.1 ∈ Icc l r := ⟨max_le t.2.1 (by linarith), le_min t.2.2 (by linarith)⟩
    have ht₀lr : t₀.1 ∈ Icc l r := ⟨max_le t₀.2.1 (by linarith), le_min t₀.2.2 (by linarith)⟩
    refine eq_zero_of_alongCurveWithin_eq_zero_chart cov hlr hbase (hγ.mono hsub)
      (hΓ t₀.1 t₀.2) (fun s hs ↦ (hU s (hsub hs)).mono hsub) (fun s hs ↦ ?_) ht₀lr htlr ht₀
    have hγs : DifferentiableWithinAt ℝ (extChartAt I (γ s) ∘ γ) (Icc p₀ q₀) s :=
      ((mdifferentiableAt_extChartAt (mem_chart_source H (γ s))).comp_mdifferentiableWithinAt s
        ((hγ s (hsub hs)).mdifferentiableWithinAt one_ne_zero)).differentiableWithinAt
    rw [alongCurveWithin_subset cov γ U hsub (uniqueDiffOn_Icc hlr s hs) (hU s (hsub hs)) hγs,
      hU₀ s (hsub hs)]
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro t₀ ht₀
    have hUt₀ : U t₀.1 ≠ 0 := ht₀
    have hne : sectionCoord (F := E) γ U (γ t₀.1) t₀.1 ≠ 0 := fun h0 ↦ hUt₀ <| by
      rw [← (trivializationAt E (TangentSpace I) (γ t₀.1)).symmL_continuousLinearMapAt (R := ℝ)
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ t₀.1)) (U t₀.1)]
      simp only [← sectionCoord_apply, h0, map_zero]
    have hcont : ContinuousAt (fun t : Icc p₀ q₀ ↦ sectionCoord (F := E) γ U (γ t₀.1) t.1) t₀ :=
      (continuousWithinAt_iff_continuousAt_domRestrict _ t₀.2).1 (hU t₀.1 t₀.2).continuousWithinAt
    refine Filter.mem_of_superset
      (hcont.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hne)) fun t ht hUt ↦ ?_
    have hUt' : U t.1 = 0 := hUt
    exact ht (by simp [sectionCoord_apply, hUt'])
  have : Nonempty (Icc p₀ q₀) := ⟨⟨p₀, left_mem_Icc.2 hpq.le⟩⟩
  have : ConnectedSpace (Icc p₀ q₀) := Subtype.connectedSpace (isConnected_Icc hpq.le)
  have hS : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨a, ha⟩, hUa⟩
  exact Set.eq_univ_iff_forall.1 hS ⟨b, hb⟩

/-- **Uniqueness of parallel tangent fields (affine generality).** On a preconnected parameter set,
two parallel tangent fields along a `C¹` curve that agree at one parameter agree at every parameter
of the set, assuming only that the Christoffel symbols of the connection are continuous on the
canonical chart around each point of the curve. No metric or torsion condition is required. -/
theorem eq_of_alongCurveWithin_eq_zero {γ : ℝ → M} {s : Set ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (hΓ : ∀ t ∈ s, ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)))
      (trivializationAt E (TangentSpace I) (γ t)).baseSet)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t)
    (hV₀ : ∀ t ∈ s, alongCurveWithin cov γ V s t = 0)
    (hW₀ : ∀ t ∈ s, alongCurveWithin cov γ W s t = 0)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hinit : V a = W a) :
    V b = W b := by
  rcases eq_or_ne a b with rfl | hab
  · exact hinit
  have hpq : min a b < max a b := min_lt_max.2 hab
  have hsub : Icc (min a b) (max a b) ⊆ s := hconn.ordConnected.uIcc_subset ha hb
  let U : ∀ r, TangentSpace I (γ r) := fun r ↦ V r - W r
  have hU_zero : U b = 0 := by
    refine eq_zero_of_alongCurveWithin_eq_zero_Icc cov hpq (hγ.mono hsub)
      (fun t ht ↦ hΓ t (hsub ht))
      (fun t ht ↦ by
        rw [sectionCoord_sub]
        exact ((hV t (hsub ht)).sub (hW t (hsub ht))).mono hsub)
      (fun t ht ↦ ?_)
      ⟨min_le_left a b, le_max_left a b⟩ ⟨min_le_right a b, le_max_right a b⟩
      (sub_eq_zero.2 hinit)
    have hγt : DifferentiableWithinAt ℝ (extChartAt I (γ t) ∘ γ) s t :=
      ((mdifferentiableAt_extChartAt (mem_chart_source H (γ t))).comp_mdifferentiableWithinAt t
        ((hγ t (hsub ht)).mdifferentiableWithinAt one_ne_zero)).differentiableWithinAt
    have hUt : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ U (γ t)) s t := by
      rw [sectionCoord_sub]
      exact (hV t (hsub ht)).sub (hW t (hsub ht))
    rw [alongCurveWithin_subset cov γ U hsub (uniqueDiffOn_Icc hpq t ht) hUt hγt,
      alongCurveWithin_sub cov γ V W s (hV t (hsub ht)) (hW t (hsub ht)),
      hV₀ t (hsub ht), hW₀ t (hsub ht), sub_self]
  exact sub_eq_zero.1 hU_zero

/-- **Uniqueness of parallel tangent fields**, for the unrestricted covariant derivative along a
`C¹` curve on a preconnected parameter set. -/
theorem eq_of_alongCurve_eq_zero {γ : ℝ → M} {s : Set ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hΓ : ∀ t ∈ s, ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)))
      (trivializationAt E (TangentSpace I) (γ t)).baseSet)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : ∀ t ∈ s, DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : ∀ t ∈ s, DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t)
    (hV₀ : ∀ t ∈ s, alongCurve cov γ V t = 0)
    (hW₀ : ∀ t ∈ s, alongCurve cov γ W t = 0)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hinit : V a = W a) :
    V b = W b := by
  rcases eq_or_ne a b with rfl | hab
  · exact hinit
  have hs := hconn.uniqueDiffOn ha hb hab
  have hrestrict (Y : ∀ r, TangentSpace I (γ r))
      (hY : ∀ t ∈ s, DifferentiableAt ℝ (sectionCoord (F := E) γ Y (γ t)) t)
      (hY₀ : ∀ t ∈ s, alongCurve cov γ Y t = 0) (t : ℝ) (ht : t ∈ s) :
      alongCurveWithin cov γ Y s t = 0 := by
    have hγt : DifferentiableAt ℝ (extChartAt I (γ t) ∘ γ) t :=
      ((mdifferentiableAt_extChartAt (mem_chart_source H (γ t))).comp t
        ((hγ t).mdifferentiableAt one_ne_zero)).differentiableAt
    rw [alongCurveWithin_subset cov γ Y (subset_univ s) (hs t ht)
      (hY t ht).differentiableWithinAt hγt.differentiableWithinAt, alongCurveWithin_univ, hY₀ t ht]
  exact cov.eq_of_alongCurveWithin_eq_zero hconn hγ.contMDiffOn hΓ
    (fun t ht ↦ (hV t ht).differentiableWithinAt)
    (fun t ht ↦ (hW t ht).differentiableWithinAt)
    (hrestrict V hV hV₀) (hrestrict W hW hW₀) ha hb hinit

/-- Restricting a parallel propagator from an interval `Icc p r` to a subinterval `Icc p' r'`. -/
private theorem IsParallelPropagatorOn.mono_Icc {γ : ℝ → M} {p r p' r' a : ℝ}
    {P : ∀ t, TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ t)}
    (hP : IsParallelPropagatorOn cov γ (Icc p r) a P)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc p r))
    (hsub : Icc p' r' ⊆ Icc p r) (hp'r' : p' < r') :
    IsParallelPropagatorOn cov γ (Icc p' r') a P := by
  refine ⟨fun v ↦ (hP.1 v).mono hsub, hP.2.1, fun v t ht ↦ ?_⟩
  have hVt : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (fun s ↦ P s v) (γ t))
      (Icc p r) t :=
    differentiableWithinAt_sectionCoord γ _
      (((hP.1 v) t (hsub ht)).mdifferentiableWithinAt one_ne_zero)
      (mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hγt : DifferentiableWithinAt ℝ (extChartAt I (γ t) ∘ γ) (Icc p r) t :=
    ((mdifferentiableAt_extChartAt (mem_chart_source H (γ t))).comp_mdifferentiableWithinAt t
      ((hγ t (hsub ht)).mdifferentiableWithinAt one_ne_zero)).differentiableWithinAt
  rw [alongCurveWithin_subset cov γ _ hsub (uniqueDiffOn_Icc hp'r' t ht) hVt hγt]
  exact hP.2.2 v t (hsub ht)

/-- Single-chart existence of the parallel propagator on `Icc p q` inside `e.baseSet`. -/
private theorem exists_isParallelPropagatorOn_chart {γ : ℝ → M} {x : M} {p q a : ℝ}
    (hpq : p < q) (ha : a ∈ Icc p q)
    (hbase : ∀ t ∈ Icc p q, γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc p q))
    (hΓ : ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet)))
      (trivializationAt E (TangentSpace I) x).baseSet) :
    ∃ P, IsParallelPropagatorOn cov γ (Icc p q) a P := by
  let e := trivializationAt E (TangentSpace I) x
  let M_op := chartConnectionOperator cov γ x hpq.le
  have hM : Continuous M_op := continuous_chartConnectionOperator cov hpq hbase hγ hΓ
  let W : ℝ → E →L[ℝ] E := fun t ↦
    (TauCeti.dysonSeriesLeft M_op t).comp (TauCeti.dysonSeries (-M_op) a)
  let P : ∀ t, TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ t) := fun t ↦
    (e.symmL ℝ (γ t)).comp ((W t).comp (e.continuousLinearMapAt ℝ (γ a)))
  have hW_smooth (w₀ : E) : ContDiff ℝ 1 (fun r ↦ W r w₀) :=
    (TauCeti.contDiff_dysonSeriesLeft (contDiff_zero.2 hM)).clm_apply contDiff_const
  have hcoord (v : TangentSpace I (γ a)) {r : ℝ} (hr : r ∈ Icc p q) :
      sectionCoord (F := E) γ (fun s ↦ P s v) x r =
        W r (e.continuousLinearMapAt ℝ (γ a) v) := by
    simp only [P, e, sectionCoord_apply, comp_apply,
      Trivialization.continuousLinearMapAt_symmL _ (hbase r hr)]
  have hP1 : ∀ v, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (P t v)) (Icc p q) := by
    intro v t ht
    refine (contDiffWithinAt_sectionCoord_iff γ (fun s ↦ P s v) (hγ t ht) (hbase t ht)).1 ?_
    exact ((hW_smooth (e.continuousLinearMapAt ℝ (γ a) v)).contDiffWithinAt).congr
      (fun r hr ↦ hcoord v hr) (hcoord v ht)
  refine ⟨P, hP1, fun v ↦ ?_, fun v t ht ↦ ?_⟩
  · have hWa : W a = 1 := TauCeti.dysonSeriesLeft_mul_dysonSeries_neg hM a
    simp only [P, hWa, one_apply_eq_self, comp_apply, e.symmL_continuousLinearMapAt (hbase a ha)]
  · have hVt : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (fun s ↦ P s v) (γ t))
        (Icc p q) t :=
      differentiableWithinAt_sectionCoord γ _
        ((hP1 v t ht).mdifferentiableWithinAt one_ne_zero)
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
    rw [← symmL_alongCurveInChartWithin cov γ _ (hbase t ht)
      ((hγ t ht).mdifferentiableWithinAt one_ne_zero) hVt]
    suffices alongCurveInChartWithin cov γ (fun s ↦ P s v) (Icc p q) x t = 0 by simp [this]
    let w₀ := TauCeti.dysonSeries (-M_op) a (e.continuousLinearMapAt ℝ (γ a) v)
    have hderiv : HasDerivWithinAt (sectionCoord (F := E) γ (fun s ↦ P s v) x)
        (M_op t (TauCeti.dysonSeriesLeft M_op t w₀)) (Icc p q) t :=
      ((TauCeti.hasDerivAt_dysonSeriesLeft_apply hM w₀ t).hasDerivWithinAt).congr
        (fun r hr ↦ hcoord v hr) (hcoord v ht)
    rw [alongCurveInChartWithin_apply, hderiv.derivWithin (uniqueDiffOn_Icc hpq t ht),
      hcoord v ht, chartConnectionOperator_of_mem cov hpq.le ht]
    simp [W, w₀]

/-- Local transfer of the `C¹` bundle-lift and `alongCurveWithin = 0` conditions across an open
neighborhood `U` on which `s ∩ U = s' ∩ U` and two sections agree on `s'`. -/
private theorem contMDiffWithinAt_and_alongCurveWithin_of_inter_eq
    {γ : ℝ → M} {s s' U : Set ℝ} {t : ℝ} (hU : U ∈ 𝓝 t) (hinter : s ∩ U = s' ∩ U)
    {V V' : ∀ r, TangentSpace I (γ r)} (heq : ∀ r ∈ s', V r = V' r) (ht' : t ∈ s')
    (hV'₁ : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (V' r)) s' t)
    (hV'₀ : alongCurveWithin cov γ V' s' t = 0) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t ∧
      alongCurveWithin cov γ V s t = 0 := by
  constructor
  · rw [← contMDiffWithinAt_inter hU, hinter, contMDiffWithinAt_inter hU]
    exact hV'₁.congr (fun r hr ↦ congrArg (TotalSpace.mk' E (γ r)) (heq r hr))
      (congrArg (TotalSpace.mk' E (γ t)) (heq t ht'))
  · rw [← alongCurveWithin_inter cov γ V hU, hinter, alongCurveWithin_inter cov γ V hU,
      alongCurveWithin_congr cov γ V (W := V')
        (eventually_nhdsWithin_of_forall fun r (hr : r ∈ s') ↦ heq r hr) (heq t ht')]
    exact hV'₀

/-- Gluing a parallel propagator on `Icc p₀ m` with a single-chart propagator on `Icc l r` across
an overlap `l < m`. -/
private theorem glue_isParallelPropagatorOn {γ : ℝ → M} {p₀ l m r : ℝ}
    (hp₀l : p₀ ≤ l) (hlm : l < m) (hmr : m ≤ r)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc p₀ r))
    (hΓ : ∀ t ∈ Icc p₀ r, ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)))
      (trivializationAt E (TangentSpace I) (γ t)).baseSet)
    {P₁ : ∀ t, TangentSpace I (γ p₀) →L[ℝ] TangentSpace I (γ t)}
    {P_chart : ∀ t, TangentSpace I (γ m) →L[ℝ] TangentSpace I (γ t)}
    (hP₁ : IsParallelPropagatorOn cov γ (Icc p₀ m) p₀ P₁)
    (hPc : IsParallelPropagatorOn cov γ (Icc l r) m P_chart) :
    ∃ P, IsParallelPropagatorOn cov γ (Icc p₀ r) p₀ P := by
  let P₂ : ∀ t, TangentSpace I (γ p₀) →L[ℝ] TangentSpace I (γ t) :=
    fun t ↦ (P_chart t).comp (P₁ m)
  have hoverlap (v : TangentSpace I (γ p₀)) {t : ℝ} (ht : t ∈ Icc l m) : P₁ t v = P₂ t v := by
    have h₁ := hP₁.mono_Icc cov (hγ.mono (Icc_subset_Icc_right hmr))
      (Icc_subset_Icc_left hp₀l) hlm
    have h₂ := hPc.mono_Icc cov (hγ.mono (Icc_subset_Icc_left hp₀l))
      (Icc_subset_Icc_right hmr) hlm
    exact cov.eq_of_alongCurveWithin_eq_zero isPreconnected_Icc
      (hγ.mono (Icc_subset_Icc hp₀l hmr))
      (fun s hs ↦ hΓ s ⟨hp₀l.trans hs.1, hs.2.trans hmr⟩)
      (fun s hs ↦ differentiableWithinAt_sectionCoord γ _
        (((h₁.1 v) s hs).mdifferentiableWithinAt one_ne_zero)
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ s)))
      (fun s hs ↦ differentiableWithinAt_sectionCoord γ _
        (((h₂.1 (P₁ m v)) s hs).mdifferentiableWithinAt one_ne_zero)
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ s)))
      (h₁.2.2 v) (h₂.2.2 (P₁ m v)) ⟨hlm.le, le_rfl⟩ ht (hPc.2.1 (P₁ m v)).symm
  let P : ∀ t, TangentSpace I (γ p₀) →L[ℝ] TangentSpace I (γ t) :=
    fun t ↦ if t ≤ m then P₁ t else P₂ t
  have hboth (v : TangentSpace I (γ p₀)) {t : ℝ} (ht : t ∈ Icc p₀ r) :
      ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 1 (fun s ↦ TotalSpace.mk' E (γ s) (P s v))
        (Icc p₀ r) t ∧ alongCurveWithin cov γ (fun s ↦ P s v) (Icc p₀ r) t = 0 := by
    by_cases htm : t < m
    · refine contMDiffWithinAt_and_alongCurveWithin_of_inter_eq cov (s' := Icc p₀ m)
        (Iio_mem_nhds htm) ?_ (fun s hs ↦ by simp [P, hs.2]) ⟨ht.1, htm.le⟩
        ((hP₁.1 v) t ⟨ht.1, htm.le⟩) (hP₁.2.2 v t ⟨ht.1, htm.le⟩)
      ext s; simp only [mem_inter_iff, mem_Icc, mem_Iio]; constructor <;>
        rintro ⟨⟨h1, _⟩, h3⟩ <;> exact ⟨⟨h1, by linarith⟩, h3⟩
    · have hlt : l < t := by linarith
      refine contMDiffWithinAt_and_alongCurveWithin_of_inter_eq cov (s' := Icc l r)
        (Ioi_mem_nhds hlt) ?_
        (fun s hs ↦ by
          by_cases hsm : s ≤ m
          · simpa [P, P₂, hsm] using hoverlap v ⟨hs.1, hsm⟩
          · simp [P, P₂, hsm])
        ⟨hlt.le, ht.2⟩ ((hPc.1 (P₁ m v)) t ⟨hlt.le, ht.2⟩) (hPc.2.2 (P₁ m v) t ⟨hlt.le, ht.2⟩)
      ext s; simp only [mem_inter_iff, mem_Icc, mem_Ioi]; constructor <;>
        rintro ⟨⟨_, h2⟩, h3⟩ <;> exact ⟨⟨by linarith, h2⟩, h3⟩
  exact ⟨P, fun v t ht ↦ (hboth v ht).1, fun v ↦ by simp [P, hp₀l.trans hlm.le, hP₁.2.1],
    fun v t ht ↦ (hboth v ht).2⟩

/-- Around any `t₀ ∈ Icc p₀ q₀` with `p₀ < t₀.1`, a single chart supplies an open neighborhood `U`
in `Icc p₀ q₀` across which solvability from `p₀` propagates in both directions. -/
private theorem step_isParallelPropagatorOn_Icc_left {γ : ℝ → M} {p₀ q₀ : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc p₀ q₀))
    (hΓ : ∀ t ∈ Icc p₀ q₀, ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)))
      (trivializationAt E (TangentSpace I) (γ t)).baseSet)
    (t₀ : Icc p₀ q₀) (ht₀ : p₀ < t₀.1) :
    let S : Set (Icc p₀ q₀) :=
      {q | p₀ < q.1 → ∃ P, IsParallelPropagatorOn cov γ (Icc p₀ q.1) p₀ P}
    ∃ U : Set (Icc p₀ q₀), IsOpen U ∧ t₀ ∈ U ∧ ((U ∩ S).Nonempty → U ⊆ S) := by
  intro S
  let e := trivializationAt E (TangentSpace I) (γ t₀.1)
  have hcont : Continuous fun t : Icc p₀ q₀ ↦ γ t.1 := hγ.continuousOn.domRestrict
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 (e.open_baseSet.preimage hcont) t₀
    (mem_baseSet_trivializationAt E (TangentSpace I) (γ t₀.1))
  let δ := min (δ₀ / 2) ((t₀.1 - p₀) / 2)
  have hδ : 0 < δ := lt_min (half_pos hδ₀) (half_pos (sub_pos.2 ht₀))
  let l := t₀.1 - δ
  let r := min q₀ (t₀.1 + δ)
  have hp₀l : p₀ < l := by
    have : δ ≤ (t₀.1 - p₀) / 2 := min_le_right _ _
    linarith
  have hlr : l < r := lt_min (by linarith [t₀.2.2]) (by linarith)
  have hsub : Icc l r ⊆ Icc p₀ q₀ := Icc_subset_Icc hp₀l.le (min_le_left _ _)
  have hbase : ∀ s ∈ Icc l r, γ s ∈ e.baseSet := fun s hs ↦ by
    refine @hball ⟨s, hsub hs⟩ ?_
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
    have hδle : δ ≤ δ₀ / 2 := min_le_left _ _
    exact ⟨by linarith [hs.1], by linarith [hs.2, min_le_right q₀ (t₀.1 + δ)]⟩
  let U : Set (Icc p₀ q₀) := (fun q : Icc p₀ q₀ ↦ q.1) ⁻¹' Ioo l (t₀.1 + δ)
  refine ⟨U, isOpen_Ioo.preimage continuous_subtype_val, ⟨by linarith, by linarith⟩, ?_⟩
  rintro ⟨m, hmU, hmS⟩ q hqU hp₀q
  have hlm : l < m.1 := hmU.1
  have hmr : m.1 ≤ r := le_min m.2.2 hmU.2.le
  obtain ⟨P₁, hP₁⟩ := hmS (hp₀l.trans hlm)
  obtain ⟨Pc, hPc⟩ := exists_isParallelPropagatorOn_chart cov hlr ⟨hlm.le, hmr⟩ hbase
    (hγ.mono hsub) (hΓ t₀.1 t₀.2)
  obtain ⟨P, hP⟩ := glue_isParallelPropagatorOn cov hp₀l.le hlm hmr
    (hγ.mono (Icc_subset_Icc_right (min_le_left _ _)))
    (fun s hs ↦ hΓ s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩) hP₁ hPc
  exact ⟨P, hP.mono_Icc cov (hγ.mono (Icc_subset_Icc_right (min_le_left _ _)))
    (Icc_subset_Icc_right (le_min q.2.2 hqU.2.le)) hp₀q⟩

/-- Propagator existence from the left endpoint `p₀` on `Icc p₀ q₀`. -/
private theorem exists_isParallelPropagatorOn_Icc_left {γ : ℝ → M} {p₀ q₀ : ℝ} (hpq : p₀ < q₀)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc p₀ q₀))
    (hΓ : ∀ t ∈ Icc p₀ q₀, ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)))
      (trivializationAt E (TangentSpace I) (γ t)).baseSet) :
    ∃ P, IsParallelPropagatorOn cov γ (Icc p₀ q₀) p₀ P := by
  let S : Set (Icc p₀ q₀) :=
    {q | p₀ < q.1 → ∃ P, IsParallelPropagatorOn cov γ (Icc p₀ q.1) p₀ P}
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    rcases eq_or_lt_of_le t₀.2.1 with hp₀t | hp₀t
    · let e := trivializationAt E (TangentSpace I) (γ p₀)
      have hcont : Continuous fun t : Icc p₀ q₀ ↦ γ t.1 := hγ.continuousOn.domRestrict
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (e.open_baseSet.preimage hcont)
        ⟨p₀, left_mem_Icc.2 hpq.le⟩ (mem_baseSet_trivializationAt E (TangentSpace I) (γ p₀))
      let r := min q₀ (p₀ + δ / 2)
      have hp₀r : p₀ < r := lt_min hpq (by linarith)
      have hsub : Icc p₀ r ⊆ Icc p₀ q₀ := Icc_subset_Icc_right (min_le_left _ _)
      have hbase : ∀ s ∈ Icc p₀ r, γ s ∈ e.baseSet := fun s hs ↦ by
        refine @hball ⟨s, hsub hs⟩ ?_
        rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hs.1], by linarith [hs.2, min_le_right q₀ (p₀ + δ / 2)]⟩
      obtain ⟨P, hP⟩ := exists_isParallelPropagatorOn_chart cov hp₀r ⟨le_rfl, hp₀r.le⟩ hbase
        (hγ.mono hsub) (hΓ p₀ ⟨le_rfl, hpq.le⟩)
      have ht₀_lt : t₀.1 < p₀ + δ / 2 := by linarith
      have hmem : ((fun q : Icc p₀ q₀ ↦ q.1) ⁻¹' Iio (p₀ + δ / 2)) ∈ 𝓝 t₀ :=
        (isOpen_Iio.preimage continuous_subtype_val).mem_nhds ht₀_lt
      refine Filter.mem_of_superset hmem fun q hq hp₀q ↦ ?_
      exact ⟨P, hP.mono_Icc cov (hγ.mono hsub)
        (Icc_subset_Icc_right (le_min q.2.2 (le_of_lt hq))) hp₀q⟩
    · obtain ⟨U, hUopen, ht₀U, hUS⟩ := step_isParallelPropagatorOn_Icc_left cov hγ hΓ t₀ hp₀t
      exact Filter.mem_of_superset (hUopen.mem_nhds ht₀U) (hUS ⟨t₀, ht₀U, ht₀⟩)
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro t₀ ht₀
    have hp₀t : p₀ < t₀.1 := lt_of_le_of_ne t₀.2.1 fun h ↦ ht₀ fun hlt ↦ (hlt.ne h).elim
    obtain ⟨U, hUopen, ht₀U, hUS⟩ := step_isParallelPropagatorOn_Icc_left cov hγ hΓ t₀ hp₀t
    refine Filter.mem_of_superset (hUopen.mem_nhds ht₀U) fun q hqU hqS ↦ ?_
    exact ht₀ (hUS ⟨q, hqU, hqS⟩ ht₀U)
  have : Nonempty (Icc p₀ q₀) := ⟨⟨p₀, left_mem_Icc.2 hpq.le⟩⟩
  have : ConnectedSpace (Icc p₀ q₀) := Subtype.connectedSpace (isConnected_Icc hpq.le)
  have hS : S = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨p₀, left_mem_Icc.2 hpq.le⟩, fun h ↦ (h.ne rfl).elim⟩
  exact Set.eq_univ_iff_forall.1 hS ⟨q₀, right_mem_Icc.2 hpq.le⟩ hpq

/-- Propagator existence from any parameter `a ∈ Icc p₀ q₀`. -/
private theorem exists_isParallelPropagatorOn_Icc {γ : ℝ → M} {p₀ q₀ a : ℝ}
    (hpq : p₀ < q₀) (ha : a ∈ Icc p₀ q₀)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc p₀ q₀))
    (hΓ : ∀ t ∈ Icc p₀ q₀, ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)))
      (trivializationAt E (TangentSpace I) (γ t)).baseSet) :
    ∃ P, IsParallelPropagatorOn cov γ (Icc p₀ q₀) a P := by
  obtain ⟨P₀, hP₀⟩ := exists_isParallelPropagatorOn_Icc_left cov hpq hγ hΓ
  let _ : NormedAddCommGroup (TangentSpace I (γ p₀)) := inferInstanceAs (NormedAddCommGroup E)
  let _ : NormedSpace ℝ (TangentSpace I (γ p₀)) := inferInstanceAs (NormedSpace ℝ E)
  let _ : FiniteDimensional ℝ (TangentSpace I (γ p₀)) := inferInstanceAs (FiniteDimensional ℝ E)
  let _ : NormedAddCommGroup (TangentSpace I (γ a)) := inferInstanceAs (NormedAddCommGroup E)
  let _ : NormedSpace ℝ (TangentSpace I (γ a)) := inferInstanceAs (NormedSpace ℝ E)
  let _ : FiniteDimensional ℝ (TangentSpace I (γ a)) := inferInstanceAs (FiniteDimensional ℝ E)
  have hinj : Function.Injective (P₀ a).toLinearMap := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have h0 := cov.eq_of_alongCurveWithin_eq_zero isPreconnected_Icc hγ hΓ
      (fun t ht ↦ differentiableWithinAt_sectionCoord γ _
        (((hP₀.1 v) t ht).mdifferentiableWithinAt one_ne_zero)
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
      (fun t _ ↦ by rw [sectionCoord_zero]; exact differentiableWithinAt_const 0)
      (hP₀.2.2 v) (fun t _ ↦ alongCurveWithin_zero cov γ _ t)
      ha ⟨le_rfl, hpq.le⟩ hv
    simpa [hP₀.2.1 v] using h0
  have hbij : Function.Bijective (P₀ a).toLinearMap :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).1 hinj⟩
  let Q : TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ p₀) :=
    (LinearEquiv.ofBijective (P₀ a).toLinearMap
      hbij).toContinuousLinearEquiv.symm.toContinuousLinearMap
  have hQa (w : TangentSpace I (γ a)) : P₀ a (Q w) = w :=
    (LinearEquiv.ofBijective (P₀ a).toLinearMap hbij).apply_symm_apply w
  exact ⟨fun t ↦ (P₀ t).comp Q, fun w ↦ hP₀.1 (Q w), hQa, fun w t ht ↦ hP₀.2.2 (Q w) t ht⟩

/-- Every point `t₀` of a nontrivial preconnected set `s ⊆ ℝ` containing distinct points `a, a₁`
has a compact subinterval `Icc p q ⊆ s` containing `a`, `a₁`, and a neighborhood of `t₀` in `s`. -/
private theorem exists_nhdsWithin_Icc_of_isPreconnected {s : Set ℝ} {a a₁ t₀ : ℝ}
    (hconn : IsPreconnected s) (ha : a ∈ s) (ha₁ : a₁ ∈ s) (hne : a₁ ≠ a) (ht₀ : t₀ ∈ s) :
    ∃ p q, p < q ∧ Icc p q ⊆ s ∧ a ∈ Icc p q ∧ a₁ ∈ Icc p q ∧
      ∃ U, IsOpen U ∧ t₀ ∈ U ∧ s ∩ U = Icc p q ∩ U := by
  have hmin {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) : min x y ∈ s := by
    rcases min_cases x y with ⟨h, _⟩ | ⟨h, _⟩ <;> rwa [h]
  have hmax {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) : max x y ∈ s := by
    rcases max_cases x y with ⟨h, _⟩ | ⟨h, _⟩ <;> rwa [h]
  by_cases hl : ∃ l ∈ s, l < t₀
  · obtain ⟨l, hls, hlt⟩ := hl
    by_cases hr : ∃ r ∈ s, t₀ < r
    · obtain ⟨r, hrs, hrt⟩ := hr
      let p := min l (min a a₁)
      let q := max r (max a a₁)
      have hpt : p < t₀ := lt_of_le_of_lt (min_le_left _ _) hlt
      have htq : t₀ < q := lt_of_lt_of_le hrt (le_max_left _ _)
      have hpqs : Icc p q ⊆ s := hconn.ordConnected.out (hmin hls (hmin ha ha₁))
        (hmax hrs (hmax ha ha₁))
      refine ⟨p, q, hpt.trans htq, hpqs,
        ⟨(min_le_right l (min a a₁)).trans (min_le_left a a₁),
          (le_max_left a a₁).trans (le_max_right r (max a a₁))⟩,
        ⟨(min_le_right l (min a a₁)).trans (min_le_right a a₁),
          (le_max_right a a₁).trans (le_max_right r (max a a₁))⟩,
        Ioo p q, isOpen_Ioo, ⟨hpt, htq⟩, ?_⟩
      ext x
      exact ⟨fun ⟨_, hxU⟩ ↦ ⟨⟨hxU.1.le, hxU.2.le⟩, hxU⟩, fun ⟨hxI, hxU⟩ ↦ ⟨hpqs hxI, hxU⟩⟩
    · push Not at hr
      let p := min l (min a a₁)
      have hpt : p < t₀ := lt_of_le_of_lt (min_le_left _ _) hlt
      have hpqs : Icc p t₀ ⊆ s := hconn.ordConnected.out (hmin hls (hmin ha ha₁)) ht₀
      refine ⟨p, t₀, hpt, hpqs,
        ⟨(min_le_right l (min a a₁)).trans (min_le_left a a₁), hr a ha⟩,
        ⟨(min_le_right l (min a a₁)).trans (min_le_right a a₁), hr a₁ ha₁⟩,
        Ioi p, isOpen_Ioi, hpt, ?_⟩
      ext x
      exact ⟨fun ⟨hxs, hxU⟩ ↦ ⟨⟨hxU.le, hr x hxs⟩, hxU⟩, fun ⟨hxI, hxU⟩ ↦ ⟨hpqs hxI, hxU⟩⟩
  · push Not at hl
    let q := max a a₁
    have htq : t₀ < q := lt_of_le_of_lt (le_min (hl a ha) (hl a₁ ha₁)) (min_lt_max.2 hne.symm)
    have hpqs : Icc t₀ q ⊆ s := hconn.ordConnected.out ht₀ (hmax ha ha₁)
    refine ⟨t₀, q, htq, hpqs, ⟨hl a ha, le_max_left _ _⟩, ⟨hl a₁ ha₁, le_max_right _ _⟩,
      Iio q, isOpen_Iio, htq, ?_⟩
    ext x
    exact ⟨fun ⟨hxs, hxU⟩ ↦ ⟨⟨hl x hxs, hxU.le⟩, hxU⟩, fun ⟨hxI, hxU⟩ ↦ ⟨hpqs hxI, hxU⟩⟩

/-- Propagator existence on any preconnected parameter set `s ⊆ ℝ`. -/
private theorem exists_isParallelPropagatorOn {γ : ℝ → M} {s : Set ℝ} {a : ℝ}
    (hconn : IsPreconnected s) (ha : a ∈ s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (hΓ : ∀ t ∈ s, ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)))
      (trivializationAt E (TangentSpace I) (γ t)).baseSet) :
    ∃ P, IsParallelPropagatorOn cov γ s a P := by
  by_cases hsub : s.Subsingleton
  · let P : ∀ t, TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ t) :=
      fun t ↦ if h : a = t then h ▸ ContinuousLinearMap.id ℝ (TangentSpace I (γ a)) else 0
    refine ⟨P, fun v ↦ ?_, fun v ↦ by simp [P], fun v t ht ↦ ?_⟩
    · refine contMDiffOn_const (c := TotalSpace.mk' E (γ a) v).congr fun t ht ↦ ?_
      rcases hsub ha ht with rfl
      simp [P]
    · refine alongCurveWithin_of_not_uniqueDiffWithinAt cov γ _ fun hu ↦
        (one_ne_zero (α := ℝ)) ?_
      exact hu.eq_deriv s (hasDerivWithinAt_id t s)
        ((hasDerivWithinAt_const t s t).congr (fun r hr ↦ hsub hr ht) rfl)
  · obtain ⟨a₁, ha₁, hne⟩ := (Set.not_subsingleton_iff.1 hsub).exists_ne a
    have hmin {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) : min x y ∈ s := by
      rcases min_cases x y with ⟨h, _⟩ | ⟨h, _⟩ <;> rwa [h]
    have hmax {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) : max x y ∈ s := by
      rcases max_cases x y with ⟨h, _⟩ | ⟨h, _⟩ <;> rwa [h]
    let p_of (r : ℝ) : ℝ := min a (min a₁ r)
    let q_of (r : ℝ) : ℝ := max a (max a₁ r)
    have hpq (r : ℝ) : p_of r < q_of r :=
      lt_of_le_of_lt (min_le_min le_rfl (min_le_left _ _))
        (lt_of_lt_of_le (min_lt_max.2 hne.symm) (max_le_max le_rfl (le_max_left _ _)))
    have hKsub {r : ℝ} (hr : r ∈ s) : Icc (p_of r) (q_of r) ⊆ s :=
      hconn.ordConnected.out (hmin ha (hmin ha₁ hr)) (hmax ha (hmax ha₁ hr))
    have haK (r : ℝ) : a ∈ Icc (p_of r) (q_of r) := ⟨min_le_left _ _, le_max_left _ _⟩
    have hrK (r : ℝ) : r ∈ Icc (p_of r) (q_of r) :=
      ⟨(min_le_right _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
    have hex {r : ℝ} (hr : r ∈ s) :
        ∃ P, IsParallelPropagatorOn cov γ (Icc (p_of r) (q_of r)) a P :=
      exists_isParallelPropagatorOn_Icc cov (hpq r) (haK r) (hγ.mono (hKsub hr))
        (fun t ht ↦ hΓ t (hKsub hr ht))
    open Classical in
    let P : ∀ r, TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ r) :=
      fun r ↦ if hr : r ∈ s then (hex hr).choose r else 0
    have hboth (v : TangentSpace I (γ a)) {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
        ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (P r v)) s t₀ ∧
          alongCurveWithin cov γ (fun r ↦ P r v) s t₀ = 0 := by
      obtain ⟨p, q, hpq₀, hpqs, hapq, ha₁pq, U, hU, ht₀U, hUeq⟩ :=
        exists_nhdsWithin_Icc_of_isPreconnected hconn ha ha₁ hne ht₀
      have ht₀pq : t₀ ∈ Icc p q := ((Set.ext_iff.1 hUeq t₀).1 ⟨ht₀, ht₀U⟩).1
      obtain ⟨P_pq, hP_pq⟩ := exists_isParallelPropagatorOn_Icc cov hpq₀ hapq (hγ.mono hpqs)
        (fun t ht ↦ hΓ t (hpqs ht))
      refine contMDiffWithinAt_and_alongCurveWithin_of_inter_eq cov (hU.mem_nhds ht₀U) hUeq
        (fun r hr ↦ ?_) ht₀pq ((hP_pq.1 v) t₀ ht₀pq) (hP_pq.2.2 v t₀ ht₀pq)
      have hrs : r ∈ s := hpqs hr
      have hKr : Icc (p_of r) (q_of r) ⊆ Icc p q :=
        Icc_subset_Icc (le_min hapq.1 (le_min ha₁pq.1 hr.1))
          (max_le hapq.2 (max_le ha₁pq.2 hr.2))
      have hPr := (hex hrs).choose_spec
      have hP_res := hP_pq.mono_Icc cov (hγ.mono hpqs) hKr (hpq r)
      simp only [P, hrs, ↓reduceDIte]
      exact cov.eq_of_alongCurveWithin_eq_zero isPreconnected_Icc (hγ.mono (hKsub hrs))
        (fun t ht ↦ hΓ t (hKsub hrs ht))
        (fun t ht ↦ differentiableWithinAt_sectionCoord γ _
          (((hPr.1 v) t ht).mdifferentiableWithinAt one_ne_zero)
          (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
        (fun t ht ↦ differentiableWithinAt_sectionCoord γ _
          (((hP_res.1 v) t ht).mdifferentiableWithinAt one_ne_zero)
          (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
        (hPr.2.2 v) (hP_res.2.2 v) (haK r) (hrK r) ((hPr.2.1 v).trans (hP_pq.2.1 v).symm)
    exact ⟨P, fun v t₀ ht₀ ↦ (hboth v ht₀).1, fun v ↦ by simp [P, ha, (hex ha).choose_spec.2.1],
      fun v t₀ ht₀ ↦ (hboth v ht₀).2⟩

/-- **Existence of parallel tangent fields (affine generality).** Along a `C¹` curve on a
preconnected parameter set `s`, if the Christoffel symbols of `cov` are continuous on the canonical
chart around each point of `γ(s)`, every initial vector `v ∈ T_{γ(a)} M` (`a ∈ s`) extends to a
`C¹` parallel tangent field along `γ` on `s`. -/
theorem exists_alongCurveWithin_eq_zero {γ : ℝ → M} {s : Set ℝ} {a : ℝ}
    (hconn : IsPreconnected s) (ha : a ∈ s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (hΓ : ∀ t ∈ s, ContinuousOn (christoffelMap (Module.finBasis ℝ E)
      (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)))
      (trivializationAt E (TangentSpace I) (γ t)).baseSet)
    (v : TangentSpace I (γ a)) :
    ∃ V : ∀ r, TangentSpace I (γ r),
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun t ↦ TotalSpace.mk' E (γ t) (V t)) s ∧
      V a = v ∧ ∀ t ∈ s, alongCurveWithin cov γ V s t = 0 := by
  obtain ⟨P, hP⟩ := exists_isParallelPropagatorOn cov hconn ha hγ hΓ
  exact ⟨fun t ↦ P t v, hP.1 v, hP.2.1 v, hP.2.2 v⟩

end LocalODE

/-! ### Smooth-connection parallel transport API -/

section Smooth

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov ∞]

/-- The Christoffel map of a smooth connection is smooth on every canonical trivialization base
set. -/
private theorem contMDiffOn_christoffelMap_infty (x : M) :
    let e := trivializationAt E (TangentSpace I) x
    CMDiff[e.baseSet] ∞
      (christoffelMap (Module.finBasis ℝ E) (cov.isCovariantDerivativeOn (s := e.baseSet))) := by
  intro e
  have : ContMDiffCovariantDerivativeOn E ∞ cov.toFun e.baseSet :=
    cov.contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) e.open_baseSet
  have : IsManifold I (∞ + 1 + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle (∞ + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact contMDiffOn_christoffelMap (n := ∞) (Module.finBasis ℝ E)
    (cov.isCovariantDerivativeOn (s := e.baseSet))

private theorem continuousOn_christoffelMap (x : M) :
    let e := trivializationAt E (TangentSpace I) x
    ContinuousOn
      (christoffelMap (Module.finBasis ℝ E) (cov.isCovariantDerivativeOn (s := e.baseSet)))
      e.baseSet :=
  (contMDiffOn_christoffelMap_infty cov x).continuousOn

/-- Unfolding helper identifying `parallelTransportWithin` on `s` with its chosen parallel
propagator. -/
private theorem exists_parallelTransportWithin_eq {γ : ℝ → M} {s : Set ℝ} {a : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ha : a ∈ s) :
    ∃ P, IsParallelPropagatorOn cov γ s a P ∧
      ∀ b ∈ s, cov.parallelTransportWithin γ s a b = P b := by
  have hex : ∃ P, IsParallelPropagatorOn cov γ s a P :=
    exists_isParallelPropagatorOn cov hconn ha hγ fun t _ ↦ continuousOn_christoffelMap cov (γ t)
  have hcond : IsPreconnected s ∧ a ∈ s ∧ ∃ P, IsParallelPropagatorOn cov γ s a P :=
    ⟨hconn, ha, hex⟩
  refine ⟨hcond.2.2.choose, hcond.2.2.choose_spec, fun b hb ↦ ?_⟩
  simp [parallelTransportWithin, hcond, hb]

/-- **Parallel transport from a parameter to itself is the identity.** -/
theorem parallelTransportWithin_self {γ : ℝ → M} {s : Set ℝ} {a : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ha : a ∈ s) :
    cov.parallelTransportWithin γ s a a = ContinuousLinearMap.id ℝ (TangentSpace I (γ a)) := by
  obtain ⟨P, hP, heq⟩ := exists_parallelTransportWithin_eq cov hconn hγ ha
  rw [heq a ha]
  ext v
  exact hP.2.1 v

/-- Applying parallel transport from a parameter to itself returns the original vector. -/
theorem parallelTransportWithin_self_apply {γ : ℝ → M} {s : Set ℝ} {a : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ha : a ∈ s)
    (v : TangentSpace I (γ a)) :
    cov.parallelTransportWithin γ s a a v = v := by
  rw [cov.parallelTransportWithin_self hconn hγ ha, ContinuousLinearMap.id_apply]

/-- Unrestricted parallel transport from a parameter to itself is the identity. -/
theorem parallelTransport_self {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a : ℝ) :
    cov.parallelTransport γ a a = ContinuousLinearMap.id ℝ (TangentSpace I (γ a)) :=
  cov.parallelTransportWithin_self isPreconnected_univ hγ.contMDiffOn (mem_univ a)

/-- Applying unrestricted parallel transport from a parameter to itself returns the original
vector. -/
theorem parallelTransport_self_apply {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a : ℝ)
    (v : TangentSpace I (γ a)) :
    cov.parallelTransport γ a a v = v :=
  cov.parallelTransportWithin_self_apply isPreconnected_univ hγ.contMDiffOn (mem_univ a) v

/-- **Parallel transport solves the parallel equation `D_t V = 0`.** -/
theorem alongCurveWithin_parallelTransportWithin {γ : ℝ → M} {s : Set ℝ} {a t : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (ht : t ∈ s) (v : TangentSpace I (γ a)) :
    cov.alongCurveWithin γ (fun r ↦ cov.parallelTransportWithin γ s a r v) s t = 0 := by
  obtain ⟨P, hP, heq⟩ := exists_parallelTransportWithin_eq cov hconn hγ ha
  rw [alongCurveWithin_congr cov γ (fun r ↦ cov.parallelTransportWithin γ s a r v)
    (W := fun r ↦ P r v)
    (eventually_nhdsWithin_of_forall fun r (hr : r ∈ s) ↦ DFunLike.congr_fun (heq r hr) v)
    (DFunLike.congr_fun (heq t ht) v)]
  exact hP.2.2 v t ht

/-- Unrestricted parallel transport solves `D_t V = 0` everywhere on `ℝ`. -/
theorem alongCurve_parallelTransport {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a t : ℝ)
    (v : TangentSpace I (γ a)) :
    cov.alongCurve γ (fun r ↦ cov.parallelTransport γ a r v) t = 0 := by
  rw [← alongCurveWithin_univ]
  exact cov.alongCurveWithin_parallelTransportWithin isPreconnected_univ hγ.contMDiffOn
    (mem_univ a) (mem_univ t) v

/-- `C¹` regularity of parallel transport along a `C¹` curve. -/
private theorem contMDiffOn_one_parallelTransportWithin {γ : ℝ → M} {s : Set ℝ} {a : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ha : a ∈ s)
    (v : TangentSpace I (γ a)) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (cov.parallelTransportWithin γ s a t v)) s := by
  obtain ⟨P, hP, heq⟩ := exists_parallelTransportWithin_eq cov hconn hγ ha
  refine (hP.1 v).congr fun t ht ↦ ?_
  exact congrArg (TotalSpace.mk' E (γ t)) (congr($(heq t ht) v))

/-- Bootstrapping a `C¹` parallel section along a `C^(n + 1)` curve to `C^(n + 1)` regularity. -/
private theorem contMDiffOn_nat_parallel_of_one {n : ℕ} {γ : ℝ → M} {s : Set ℝ}
    {V : ∀ t, TangentSpace I (γ t)} (hs : UniqueDiffOn ℝ s)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I (n + 1 : ℕ) γ s)
    (hV₁ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun t ↦ TotalSpace.mk' E (γ t) (V t)) s)
    (hV₀ : ∀ t ∈ s, cov.alongCurveWithin γ V s t = 0) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (n + 1 : ℕ) (fun t ↦ TotalSpace.mk' E (γ t) (V t)) s := by
  induction n with
  | zero => simpa using hV₁
  | succ m ih =>
    have hm_le : ((m + 1 : ℕ) : ℕ∞ω) ≤ (m + 1 + 1 : ℕ) := by exact_mod_cast Nat.le_succ (m + 1)
    have hVm := ih (hγ.of_le hm_le)
    intro t ht
    let e := trivializationAt E (TangentSpace I) (γ t)
    let Γ := christoffelMap (Module.finBasis ℝ E) (cov.isCovariantDerivativeOn (s := e.baseSet))
    let v := sectionCoord (F := E) γ V (γ t)
    let u := extChartAt I (γ t) ∘ γ
    have hx : γ t ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
    have hγm : ContMDiffWithinAt 𝓘(ℝ, ℝ) I (m + 1 : ℕ) γ s t := (hγ t ht).of_le hm_le
    have hv : ContDiffWithinAt ℝ (m + 1 : ℕ) v s t :=
      (contDiffWithinAt_sectionCoord_iff γ V hγm hx).2 (hVm t ht)
    have hu : ContDiffWithinAt ℝ (m + 1 + 1 : ℕ) u s t :=
      ((contMDiffAt_extChartAt' (by
        simpa only [e, TangentBundle.trivializationAt_baseSet] using hx)).comp_contMDiffWithinAt
        t (hγ t ht)).contDiffWithinAt
    have hΓ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) (m + 1 : ℕ) Γ (γ t) :=
      ((contMDiffOn_christoffelMap_infty cov (γ t)).contMDiffAt
        (e.open_baseSet.mem_nhds hx)).of_le (by simp)
    have hcand : ContDiffWithinAt ℝ (m + 1 : ℕ)
        (fun r ↦ -Γ (γ r) (v r) (derivWithin u s r)) s t :=
      (((hΓ.comp_contMDiffWithinAt t hγm).contDiffWithinAt.clm_apply hv).clm_apply
        (hu.derivWithin hs (by push_cast; rfl) ht)).neg
    apply (contDiffWithinAt_sectionCoord_iff γ V (hγ t ht) hx).1
    rw [show ((m + 1 + 1 : ℕ) : ℕ∞ω) = ((m + 1 : ℕ) : ℕ∞ω) + 1 by push_cast; rfl,
      contDiffWithinAt_succ_iff_hasFDerivWithinAt' (by simp)]
    have hbase : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
      (hγ t ht).continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx)
    have hdeq := eventuallyEq_sectionCoord_alongCurveWithin cov γ V hx (hV₁ t ht)
    refine ⟨{r | r ∈ s ∧ γ r ∈ e.baseSet ∧
      sectionCoord (F := E) γ (alongCurveWithin cov γ V s) (γ t) r =
        alongCurveInChartWithin cov γ V s (γ t) r}, ?_, ?_, by simp,
      fun r ↦ ContinuousLinearMap.toSpanSingleton ℝ (-Γ (γ r) (v r) (derivWithin u s r)),
      ?_, ?_⟩
    · rw [insert_eq_of_mem ht]
      exact inter_mem self_mem_nhdsWithin (inter_mem hbase hdeq)
    · exact fun r hr ↦ subset_insert t s hr.1
    · intro r hr
      have hVr : DifferentiableWithinAt ℝ v s r :=
        differentiableWithinAt_sectionCoord γ V
          ((hV₁ r hr.1).mdifferentiableWithinAt one_ne_zero) hr.2.1
      have hzero : sectionCoord (F := E) γ (alongCurveWithin cov γ V s) (γ t) r = 0 := by
        simp [sectionCoord_apply, hV₀ r hr.1]
      have h0 : alongCurveInChartWithin cov γ V s (γ t) r = 0 := hr.2.2.symm.trans hzero
      rw [alongCurveInChartWithin_apply] at h0
      simpa only [v, eq_neg_of_add_eq_zero_left h0] using hVr.hasDerivWithinAt.hasFDerivWithinAt
    · exact ContinuousLinearMap.toSpanSingletonCLE.contDiff.comp_contDiffWithinAt hcand

/-- **`C^k` regularity of parallel transport (`1 ≤ k ≤ ∞`).** For a smooth connection on `TM` and a
`C^k` curve `γ` on a preconnected set `s`, parallel transport of any initial vector `v` lifts to a
`C^k` curve in the tangent bundle on `s`. -/
theorem contMDiffOn_parallelTransportWithin {k : ℕ∞ω} (hk1 : 1 ≤ k) (hk : k ≤ ∞)
    {γ : ℝ → M} {s : Set ℝ} {a : ℝ} (hconn : IsPreconnected s)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I k γ s) (ha : a ∈ s) (v : TangentSpace I (γ a)) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent k
      (fun t ↦ TotalSpace.mk' E (γ t) (cov.parallelTransportWithin γ s a t v)) s := by
  by_cases hsub : s.Subsingleton
  · refine contMDiffOn_const (c := TotalSpace.mk' E (γ a) v).congr fun t ht ↦ ?_
    rcases hsub ha ht with rfl
    rw [cov.parallelTransportWithin_self_apply hconn (hγ.of_le hk1) ha v]
  · obtain ⟨a₁, ha₁, hne⟩ := (Set.not_subsingleton_iff.1 hsub).exists_ne a
    have hs : UniqueDiffOn ℝ s := hconn.uniqueDiffOn ha₁ ha hne
    have hV₁ := contMDiffOn_one_parallelTransportWithin cov hconn (hγ.of_le hk1) ha v
    have hV₀ : ∀ t ∈ s,
        cov.alongCurveWithin γ (fun r ↦ cov.parallelTransportWithin γ s a r v) s t = 0 :=
      fun _ ht ↦ cov.alongCurveWithin_parallelTransportWithin hconn (hγ.of_le hk1) ha ht v
    match k with
    | (⊤ : ℕ∞ω) => exact absurd hk (by simp)
    | ((⊤ : ℕ∞) : ℕ∞ω) =>
      exact contMDiffOn_infty.2 fun n ↦
        (contMDiffOn_nat_parallel_of_one cov (n := n) hs (hγ.of_le (by simp)) hV₁ hV₀).of_le
          (by exact_mod_cast Nat.le_succ n)
    | ((n : ℕ) : ℕ∞ω) =>
      have hn1 : 1 ≤ n := by exact_mod_cast hk1
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.2 hn1
      exact contMDiffOn_nat_parallel_of_one cov hs hγ hV₁ hV₀

/-- **`C^k` regularity of unrestricted parallel transport (`1 ≤ k ≤ ∞`).** -/
theorem contMDiff_parallelTransport {k : ℕ∞ω} (hk1 : 1 ≤ k) (hk : k ≤ ∞)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I k γ) (a : ℝ) (v : TangentSpace I (γ a)) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent k
      (fun t ↦ TotalSpace.mk' E (γ t) (cov.parallelTransport γ a t v)) :=
  contMDiffOn_univ.1
    (cov.contMDiffOn_parallelTransportWithin hk1 hk isPreconnected_univ hγ.contMDiffOn
      (mem_univ a) v)

/-- Coordinate reading of parallel transport within `s` is differentiable at every point of `s`. -/
theorem differentiableWithinAt_sectionCoord_parallelTransportWithin
    {γ : ℝ → M} {s : Set ℝ} {a t : ℝ} {x : M}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (ht : t ∈ s) (hx : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (v : TangentSpace I (γ a)) :
    DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ cov.parallelTransportWithin γ s a r v) x) s t :=
  differentiableWithinAt_sectionCoord γ _
    (((contMDiffOn_one_parallelTransportWithin cov hconn hγ ha v) t ht).mdifferentiableWithinAt
      one_ne_zero) hx

/-- Coordinate reading of unrestricted parallel transport is differentiable everywhere. -/
theorem differentiableAt_sectionCoord_parallelTransport
    {γ : ℝ → M} {a t : ℝ} {x : M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hx : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet) (v : TangentSpace I (γ a)) :
    DifferentiableAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ cov.parallelTransport γ a r v) x) t :=
  differentiableWithinAt_univ.1
    (cov.differentiableWithinAt_sectionCoord_parallelTransportWithin isPreconnected_univ
      hγ.contMDiffOn (mem_univ a) (mem_univ t) hx v)

/-- **Universal property of parallel transport.** Every parallel tangent field along a `C¹` curve
on a preconnected set `s` is obtained by parallel transport from its value at `a ∈ s`. -/
theorem eq_parallelTransportWithin_of_alongCurveWithin_eq_zero
    {γ : ℝ → M} {s : Set ℝ} {V : ∀ r, TangentSpace I (γ r)}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (hV : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hV₀ : ∀ t ∈ s, cov.alongCurveWithin γ V s t = 0)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    V b = cov.parallelTransportWithin γ s a b (V a) :=
  cov.eq_of_alongCurveWithin_eq_zero hconn hγ (fun t _ ↦ continuousOn_christoffelMap cov (γ t))
    hV (fun t ht ↦ cov.differentiableWithinAt_sectionCoord_parallelTransportWithin
      hconn hγ ha ht (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)) (V a))
    hV₀ (fun _ ht ↦ cov.alongCurveWithin_parallelTransportWithin hconn hγ ha ht (V a))
    ha hb (cov.parallelTransportWithin_self_apply hconn hγ ha (V a)).symm

/-- Every parallel tangent field along a `C¹` curve on `ℝ` is the parallel transport of its initial
value. -/
theorem eq_parallelTransport_of_alongCurve_eq_zero
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ∀ t, DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hV₀ : ∀ t, cov.alongCurve γ V t = 0) (a b : ℝ) :
    V b = cov.parallelTransport γ a b (V a) := by
  rw [parallelTransport_def]
  exact cov.eq_parallelTransportWithin_of_alongCurveWithin_eq_zero isPreconnected_univ
    hγ.contMDiffOn (fun t _ ↦ (hV t).differentiableWithinAt)
    (fun t _ ↦ by rw [alongCurveWithin_univ]; exact hV₀ t) (mem_univ a) (mem_univ b)

/-- **Characterization of parallel fields by parallel transport.** For a tangent field `V` along a
`C¹` curve `γ` on a preconnected set `s` with differentiable coordinate readings, `D_t V = 0` on
`s` if and only if `V` equals the parallel transport of `V a` (`a ∈ s`) throughout `s`. -/
theorem forall_alongCurveWithin_eq_zero_iff_parallelTransportWithin
    {γ : ℝ → M} {s : Set ℝ} {V : ∀ r, TangentSpace I (γ r)}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (hV : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    {a : ℝ} (ha : a ∈ s) :
    (∀ t ∈ s, cov.alongCurveWithin γ V s t = 0) ↔
      ∀ t ∈ s, V t = cov.parallelTransportWithin γ s a t (V a) := by
  refine ⟨fun hV₀ t ht ↦
    cov.eq_parallelTransportWithin_of_alongCurveWithin_eq_zero hconn hγ hV hV₀ ha ht,
    fun h t ht ↦ ?_⟩
  rw [alongCurveWithin_congr cov γ V
    (eventually_nhdsWithin_of_forall fun r (hr : r ∈ s) ↦ h r hr) (h t ht)]
  exact cov.alongCurveWithin_parallelTransportWithin hconn hγ ha ht (V a)

/-- Unrestricted characterization of parallel fields on `ℝ` by parallel transport. -/
theorem forall_alongCurve_eq_zero_iff_parallelTransport
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ∀ t, DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t) (a : ℝ) :
    (∀ t, cov.alongCurve γ V t = 0) ↔ ∀ t, V t = cov.parallelTransport γ a t (V a) := by
  simpa only [alongCurveWithin_univ, parallelTransportWithin_univ, mem_univ, true_imp_iff] using
    cov.forall_alongCurveWithin_eq_zero_iff_parallelTransportWithin
      isPreconnected_univ hγ.contMDiffOn (fun t _ ↦ (hV t).differentiableWithinAt) (mem_univ a)

/-- **Functoriality (transitivity) of parallel transport.** Transporting from `a` to `b` and then
from `b` to `c` within a preconnected set `s` equals transporting directly from `a` to `c`. -/
theorem parallelTransportWithin_trans {γ : ℝ → M} {s : Set ℝ} {a b c : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    (cov.parallelTransportWithin γ s b c).comp (cov.parallelTransportWithin γ s a b) =
      cov.parallelTransportWithin γ s a c := by
  ext v
  symm
  exact cov.eq_parallelTransportWithin_of_alongCurveWithin_eq_zero hconn hγ
    (V := fun r ↦ cov.parallelTransportWithin γ s a r v)
    (fun t ht ↦ cov.differentiableWithinAt_sectionCoord_parallelTransportWithin hconn hγ ha ht
      (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)) v)
    (fun _ ht ↦ cov.alongCurveWithin_parallelTransportWithin hconn hγ ha ht v) hb hc

/-- Pointwise form of `CovariantDerivative.parallelTransportWithin_trans`. -/
theorem parallelTransportWithin_trans_apply {γ : ℝ → M} {s : Set ℝ} {a b c : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (v : TangentSpace I (γ a)) :
    cov.parallelTransportWithin γ s b c (cov.parallelTransportWithin γ s a b v) =
      cov.parallelTransportWithin γ s a c v :=
  congr($(cov.parallelTransportWithin_trans hconn hγ ha hb hc) v)

/-- Transitivity of unrestricted parallel transport. -/
theorem parallelTransport_trans {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b c : ℝ) :
    (cov.parallelTransport γ b c).comp (cov.parallelTransport γ a b) =
      cov.parallelTransport γ a c :=
  cov.parallelTransportWithin_trans isPreconnected_univ hγ.contMDiffOn
    (mem_univ a) (mem_univ b) (mem_univ c)

/-- Pointwise transitivity of unrestricted parallel transport. -/
theorem parallelTransport_trans_apply {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b c : ℝ)
    (v : TangentSpace I (γ a)) :
    cov.parallelTransport γ b c (cov.parallelTransport γ a b v) =
      cov.parallelTransport γ a c v :=
  congr($(cov.parallelTransport_trans hγ a b c) v)

/-- **Parallel transport packaged as a continuous linear equivalence** between endpoint tangent
spaces along a `C¹` curve on a preconnected parameter set. -/
def parallelTransportWithinEquiv {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ha : a ∈ s) (hb : b ∈ s) :
    TangentSpace I (γ a) ≃L[ℝ] TangentSpace I (γ b) :=
  ContinuousLinearEquiv.equivOfInverse
    (cov.parallelTransportWithin γ s a b)
    (cov.parallelTransportWithin γ s b a)
    (fun v ↦ by
      rw [cov.parallelTransportWithin_trans_apply hconn hγ ha hb ha,
        cov.parallelTransportWithin_self_apply hconn hγ ha])
    (fun w ↦ by
      rw [cov.parallelTransportWithin_trans_apply hconn hγ hb ha hb,
        cov.parallelTransportWithin_self_apply hconn hγ hb])

/-- Applying `parallelTransportWithinEquiv` evaluates `parallelTransportWithin`. -/
@[simp]
theorem parallelTransportWithinEquiv_apply {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ha : a ∈ s) (hb : b ∈ s)
    (v : TangentSpace I (γ a)) :
    cov.parallelTransportWithinEquiv hconn hγ ha hb v =
      cov.parallelTransportWithin γ s a b v :=
  (rfl)

/-- The inverse of `parallelTransportWithinEquiv` from `a` to `b` is parallel transport from `b` to
`a`. -/
@[simp]
theorem parallelTransportWithinEquiv_symm {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ha : a ∈ s) (hb : b ∈ s) :
    (cov.parallelTransportWithinEquiv hconn hγ ha hb).symm =
      cov.parallelTransportWithinEquiv hconn hγ hb ha := by
  ext w
  rfl

/-- **Unrestricted parallel transport packaged as a continuous linear equivalence.** -/
def parallelTransportEquiv {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    TangentSpace I (γ a) ≃L[ℝ] TangentSpace I (γ b) :=
  cov.parallelTransportWithinEquiv isPreconnected_univ hγ.contMDiffOn (mem_univ a) (mem_univ b)

/-- Applying `parallelTransportEquiv` evaluates `parallelTransport`. -/
@[simp]
theorem parallelTransportEquiv_apply {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ)
    (v : TangentSpace I (γ a)) :
    cov.parallelTransportEquiv hγ a b v = cov.parallelTransport γ a b v :=
  (rfl)

/-- The inverse of `parallelTransportEquiv` from `a` to `b` is parallel transport from `b` to
`a`. -/
@[simp]
theorem parallelTransportEquiv_symm {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    (cov.parallelTransportEquiv hγ a b).symm = cov.parallelTransportEquiv hγ b a :=
  cov.parallelTransportWithinEquiv_symm isPreconnected_univ hγ.contMDiffOn (mem_univ a) (mem_univ b)

/-- **Parameter-set restriction invariance of parallel transport.** On preconnected parameter sets
`s₁ ⊆ s₂` containing `a` and `b`, parallel transport within `s₁` equals parallel transport within
`s₂`. -/
theorem parallelTransportWithin_subset {γ : ℝ → M} {s₁ s₂ : Set ℝ} {a b : ℝ}
    (hsub : s₁ ⊆ s₂) (hconn₁ : IsPreconnected s₁) (hconn₂ : IsPreconnected s₂)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s₂) (ha : a ∈ s₁) (hb : b ∈ s₁) :
    cov.parallelTransportWithin γ s₁ a b = cov.parallelTransportWithin γ s₂ a b := by
  ext v
  rcases eq_or_ne a b with rfl | hab
  · rw [cov.parallelTransportWithin_self_apply hconn₁ (hγ.mono hsub) ha,
      cov.parallelTransportWithin_self_apply hconn₂ hγ (hsub ha)]
  · have hs₁ : UniqueDiffOn ℝ s₁ := hconn₁.uniqueDiffOn ha hb hab
    symm
    refine cov.eq_parallelTransportWithin_of_alongCurveWithin_eq_zero hconn₁ (hγ.mono hsub)
      (V := fun r ↦ cov.parallelTransportWithin γ s₂ a r v)
      (fun t ht ↦ (cov.differentiableWithinAt_sectionCoord_parallelTransportWithin
        hconn₂ hγ (hsub ha) (hsub ht)
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)) v).mono hsub)
      (fun t ht ↦ ?_) ha hb |>.trans
        (congrArg (cov.parallelTransportWithin γ s₁ a b)
          (cov.parallelTransportWithin_self_apply hconn₂ hγ (hsub ha) v))
    have hVt := cov.differentiableWithinAt_sectionCoord_parallelTransportWithin
      hconn₂ hγ (hsub ha) (hsub ht) (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)) v
    have hγt : DifferentiableWithinAt ℝ (extChartAt I (γ t) ∘ γ) s₂ t :=
      ((mdifferentiableAt_extChartAt (mem_chart_source H (γ t))).comp_mdifferentiableWithinAt t
        ((hγ t (hsub ht)).mdifferentiableWithinAt one_ne_zero)).differentiableWithinAt
    rw [alongCurveWithin_subset cov γ _ hsub (hs₁ t ht) hVt hγt]
    exact cov.alongCurveWithin_parallelTransportWithin hconn₂ hγ (hsub ha) (hsub ht) v

/-- Along a globally `C¹` curve, parallel transport within any preconnected parameter set `s`
containing `a` and `b` agrees with unrestricted parallel transport. -/
theorem parallelTransportWithin_eq_parallelTransport {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}
    (hconn : IsPreconnected s) (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (ha : a ∈ s) (hb : b ∈ s) :
    cov.parallelTransportWithin γ s a b = cov.parallelTransport γ a b :=
  cov.parallelTransportWithin_subset (subset_univ s) hconn isPreconnected_univ hγ.contMDiffOn ha hb

/-- **Reparametrization invariance of parallel transport.** For a `C¹` map `φ : ℝ → ℝ` sending a
preconnected set `s'` into a preconnected set `s`, parallel transport along `γ ∘ φ` from `a'` to
`b'` equals parallel transport along `γ` from `φ a'` to `φ b'`. -/
theorem parallelTransportWithin_comp {γ : ℝ → M} {φ : ℝ → ℝ} {s s' : Set ℝ} {a' b' : ℝ}
    (hconn : IsPreconnected s) (hconn' : IsPreconnected s')
    (hφ : ContDiffOn ℝ 1 φ s') (hmaps : MapsTo φ s' s)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (ha' : a' ∈ s') (hb' : b' ∈ s') :
    cov.parallelTransportWithin (γ ∘ φ) s' a' b' =
      cov.parallelTransportWithin γ s (φ a') (φ b') := by
  ext v
  have hγφ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ φ) s' := hγ.comp hφ.contMDiffOn hmaps
  let V' : ∀ r, TangentSpace I ((γ ∘ φ) r) :=
    fun r ↦ cov.parallelTransportWithin γ s (φ a') (φ r) v
  have hV'_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E ((γ ∘ φ) r) (V' r)) s' :=
    (contMDiffOn_one_parallelTransportWithin cov hconn hγ (hmaps ha') v).comp
      hφ.contMDiffOn hmaps
  have hV'_eq := cov.eq_parallelTransportWithin_of_alongCurveWithin_eq_zero hconn' hγφ
    (V := V')
    (fun t ht ↦ differentiableWithinAt_sectionCoord (γ ∘ φ) V'
      ((hV'_smooth t ht).mdifferentiableWithinAt one_ne_zero)
      (mem_baseSet_trivializationAt E (TangentSpace I) ((γ ∘ φ) t)))
    (fun t ht ↦ ?_) ha' hb'
  · dsimp only [V', Function.comp_apply] at hV'_eq
    rw [cov.parallelTransportWithin_self_apply hconn hγ (hmaps ha') v] at hV'_eq
    exact hV'_eq.symm
  · have hγt : DifferentiableWithinAt ℝ (extChartAt I (γ (φ t)) ∘ γ) s (φ t) :=
      ((mdifferentiableAt_extChartAt (mem_chart_source H (γ (φ t)))).comp_mdifferentiableWithinAt
        (φ t) ((hγ (φ t) (hmaps ht)).mdifferentiableWithinAt one_ne_zero)).differentiableWithinAt
    have hVt := cov.differentiableWithinAt_sectionCoord_parallelTransportWithin
      hconn hγ (hmaps ha') (hmaps ht)
      (mem_baseSet_trivializationAt E (TangentSpace I) (γ (φ t))) v
    rw [alongCurveWithin_comp cov γ (fun r ↦ cov.parallelTransportWithin γ s (φ a') r v) φ
      (hφ.differentiableOn one_ne_zero t ht) hmaps hγt hVt,
      cov.alongCurveWithin_parallelTransportWithin hconn hγ (hmaps ha') (hmaps ht) v, smul_zero]

/-- Reparametrization invariance of unrestricted parallel transport. -/
theorem parallelTransport_comp {γ : ℝ → M} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a' b' : ℝ) :
    cov.parallelTransport (γ ∘ φ) a' b' = cov.parallelTransport γ (φ a') (φ b') :=
  cov.parallelTransportWithin_comp isPreconnected_univ isPreconnected_univ
    hφ.contDiffOn (mapsTo_univ φ univ) hγ.contMDiffOn (mem_univ a') (mem_univ b')

end Smooth

end CovariantDerivative
