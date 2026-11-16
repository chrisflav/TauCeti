/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Local.Reflection
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.Analysis.SpecialFunctions.Integrability.Rpow
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Holomorphic
import TauCeti.Analysis.Sobolev.Local.LinearEquiv
import TauCeti.Analysis.Sobolev.Local.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Membership and non-membership examples for local Sobolev classes

This file tests `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` against explicit functions on
finite-dimensional real normed spaces and on the plane.

* The identity of any finite-dimensional real normed space `E` is in every local Sobolev class
  (`TauCeti.memWkpLoc_id`), although when `E` is nontrivial it is not globally `Lᵖ` for any
  `p ≠ 0` (`TauCeti.not_memLp_id`).
* The norm `x ↦ ‖x‖` is in every local `W^{1,p}` class, as a Lipschitz map
  (`TauCeti.memWkpLoc_one_norm`), with `‖fderiv ℝ (fun y => ‖y‖) x‖ ≤ 1`
  (`TauCeti.norm_fderiv_norm_le_one`). On `ℝ × ℝ` with its supremum norm `max |x₁| |x₂|`, the
  derivative at `(1, 1 / 2)` is the first projection (so it vanishes on `(0, 1)`), while the
  coordinate equivalence to `EuclideanSpace ℝ (Fin 2)` identifies their local Sobolev classes
  (`TauCeti.memWkpLoc_prod_iff_euclideanSpaceFinTwo`).
* For a fixed vector `v` in the infinite-dimensional Banach space `ℓ² = lp (fun _ : ℕ => ℝ) 2`,
  `x ↦ ‖x‖ • v` lies in every local `W^{1,p}` class with weak derivative
  `x ↦ (fderiv ℝ (fun y => ‖y‖) x).smulRight v`, using no basis of the target
  (`TauCeti.memWkpLoc_one_norm_smul_lpTwo`).
* On any finite-dimensional real inner product space `E` of dimension at least `2`, the unit
  radial field `x ↦ ‖x‖⁻¹ • x` lies in `W^{1,p}_loc` near the origin exactly when
  `p < Module.finrank ℝ E` (`TauCeti.memWkpLoc_one_norm_inv_smul_iff`).
* Polynomials are in every local Sobolev class on every set, as holomorphic maps on the plane
  (`Polynomial.memWkpLoc`).
* The planar map `z ↦ ‖z‖` is in the local class `W^{2,p}` exactly when `p < 2`, on every set
  whose interior contains the origin: away from the origin its second derivative has norm between
  `‖z‖⁻¹` and `2 ‖z‖⁻¹`, and `‖z‖ ^ (-p)` is integrable near the origin of the plane exactly when
  `p < 2`. For `p < 2` the weak second derivative across the origin is that of the unit radial
  field `z / ‖z‖` (`TauCeti.hasWeakFDerivOn_norm_rpow_neg_one_mul_inner`).
* For any nonzero continuous linear functional `ℓ : E →L[ℝ] ℝ`, the half-space indicator
  `{x | 0 < ℓ x}.indicator 1` is locally `Lᵖ` for every exponent
  (`TauCeti.memLpLoc_indicator_pos_clm`) but has no weak derivative on any open set meeting
  `ker ℓ`, so it lies in no local `W^{k,p}` class of positive order there
  (`TauCeti.not_memWkpLoc_indicator_pos_clm`).
* On the closed upper half-disc `D⁺ = ball 0 1 ∩ {z | 0 ≤ z.im}`, the map `z ↦ √z.im` is in the
  local class `W^{1,p}` exactly when `p < 2`, because the `Lᵖ` bounds reach the real axis. On the
  open half-disc it is in that class for every `p`, although it is continuous up to the axis.
* On any nontrivial finite-dimensional real normed space `E`, `x ↦ ‖x‖⁻¹` is locally `Lᵖ` near
  the origin exactly when `p < Module.finrank ℝ E` (`TauCeti.memLpLoc_norm_inv_iff`). On the plane,
  the components `Re z / ‖z‖²` and `Im z / ‖z‖²` of the gradient of `log ‖z‖` and `log ‖z‖` itself
  lie in the corresponding local classes near the origin exactly when `p < 2`. These are the
  exponents of the divergence-form equation `Δ log ‖z‖ = ∂ₛ(Re z / ‖z‖²) + ∂ₜ(Im z / ‖z‖²)`
  (`TauCeti.integral_log_norm_mul_laplacian`).
* The even reflection does not extend `u = Im z` from the upper half-disc to a local `W^{2,p}`
  map, for any exponent: it gives `|Im z|`, whose first derivative jumps across the real axis. The
  order-two reflection `u(s, -t) = -3 u(s, t) + 4 u(s, t / 2)` gives `Im z` back.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped Topology Distributions RealInnerProductSpace

namespace TauCeti

/-! ### The identity, the norm, non-Euclidean norms, and Banach targets -/

section GeneralNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ENNReal} {U : Set E}

/-- The identity of any finite-dimensional real normed space is in every local Sobolev class on
every set, although for nontrivial `E` and `p ≠ 0` it is not globally `Lᵖ`
(`TauCeti.not_memLp_id`): the local class imposes no bound at infinity. -/
theorem memWkpLoc_id (p : ENNReal) (U : Set E) (k : ℕ) :
    MemWkpLoc p U k (fun x : E => x) μ :=
  (contDiff_id.contDiffOn : ContDiffOn ℝ k id ((⊤ : Opens E) : Set E)).memWkpLoc (subset_univ U)

/-- On a nontrivial finite-dimensional real normed space, the identity map is not globally `Lᵖ`
for any `p ≠ 0` (including `p = ∞`). Together with `TauCeti.memWkpLoc_id`, this shows that local
Sobolev membership imposes no growth bound at infinity. -/
theorem not_memLp_id [Nontrivial E] (hp : p ≠ 0) : ¬ MemLp (fun x : E => x) p μ := by
  intro h
  by_cases htop : p = ⊤
  · subst htop
    set C : ℝ := (eLpNorm (fun x : E => x) ⊤ μ).toReal
    have hC : ∀ᵐ x ∂μ, ‖x‖ ≤ C := by
      filter_upwards [eNorm_ae_le_eLpNormEssSup (fun x : E => x) μ] with x hx
      have hx' : ‖x‖ₑ ≤ eLpNorm (fun y : E => y) ⊤ μ := by
        simpa [eLpNorm_exponent_top h.aestronglyMeasurable] using hx
      rw [← ENNReal.toReal_ofReal (norm_nonneg x)]
      exact ENNReal.toReal_mono h.eLpNorm_lt_top.ne (by simpa [ofReal_norm] using hx')
    obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
    have hne : ({x : E | C < ‖x‖}).Nonempty := by
      refine ⟨((max C 0 + 1) / ‖x₀‖) • x₀, ?_⟩
      have hpos : 0 < ‖x₀‖ := norm_pos_iff.2 hx₀
      have hm : 0 ≤ max C 0 + 1 := by positivity
      rw [mem_ofPred_eq, norm_smul, Real.norm_of_nonneg (div_nonneg hm hpos.le),
        div_mul_cancel₀ _ hpos.ne']
      linarith [le_max_left C 0]
    have hpos : μ {x : E | C < ‖x‖} ≠ 0 :=
      (isOpen_lt continuous_const continuous_norm).measure_ne_zero μ hne
    have hzero : μ {x : E | C < ‖x‖} = 0 := by
      simpa [ae_iff, not_le] using hC
    exact hpos hzero
  · have hint : Integrable (fun x : E => ‖x‖ ^ p.toReal) μ :=
      (integrable_norm_rpow_iff h.aestronglyMeasurable hp htop).2 h
    exact μ.not_integrable_norm_sub_rpow p.toReal (0 : E) (by simpa using hint)

/-- The norm `x ↦ ‖x‖` on any finite-dimensional real normed space is in the local class
`W^{1,p}` on every set, for every exponent: it is `1`-Lipschitz. -/
theorem memWkpLoc_one_norm : MemWkpLoc p U 1 (fun x : E => ‖x‖) μ :=
  lipschitzWith_one_norm.memWkpLoc_one

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The classical derivative of the norm has operator norm at most `1` everywhere. -/
theorem norm_fderiv_norm_le_one (x : E) : ‖fderiv ℝ (fun y : E => ‖y‖) x‖ ≤ 1 := by
  simpa using norm_fderiv_le_of_lipschitzOn ℝ (s := univ) univ_mem
    ((lipschitzWith_one_norm (E := E)).lipschitzOnWith)

/-- **`‖x‖⁻¹` is locally `Lᵖ` near the origin exactly for `p < dim E`.** On a nontrivial
finite-dimensional real normed space `E` with an additive Haar measure `μ`, the singular kernel
`x ↦ ‖x‖⁻¹` lies in `MemLpLoc p U · μ` on any neighbourhood `U` of `0` if and only if
`p < Module.finrank ℝ E`. -/
theorem memLpLoc_norm_inv_iff [Nontrivial E] (hU : U ∈ 𝓝 (0 : E)) :
    MemLpLoc p U (fun x : E => ‖x‖⁻¹) μ ↔ p < Module.finrank ℝ E := by
  refine ⟨fun h => ?_, fun h => memLpLoc_iff.2 fun K _ hK => hK.memLp_norm_inv_restrict h⟩
  by_contra! hp
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hε hp (memLpLoc_iff.1 h _ hεU (isCompact_closedBall 0 ε))

/-- For a fixed vector `v` in the infinite-dimensional Banach space `lp (fun _ : ℕ => ℝ) 2`,
the map `x ↦ ‖x‖ • v` lies in `W^{1,p}_loc` for every exponent `p`, with weak derivative
`x ↦ (fderiv ℝ (fun y => ‖y‖) x).smulRight v`; no basis of the target is used. -/
theorem memWkpLoc_one_norm_smul_lpTwo {Ω : Opens E} (v : lp (fun _ : ℕ => ℝ) 2) :
    MemWkpLoc p Ω 1 (fun x : E => ‖x‖ • v) μ ∧
      HasWeakFDerivOn μ Ω (fun x : E => ‖x‖ • v)
        (fun x => (fderiv ℝ (fun y : E => ‖y‖) x).smulRight v) := by
  have : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  refine ⟨(memWkpLoc_one_norm (E := E) (μ := μ) (p := p) (U := Ω)).smul_const v, ?_⟩
  have hN : HasWeakFDerivOn μ Ω (fun y : E => ‖y‖) (fderiv ℝ fun y : E => ‖y‖) :=
    lipschitzWith_one_norm.locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn_fderiv
  have hsmul := hN.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)
  convert hsmul using 1
  · funext x; simp
  · funext x; ext w; simp

end GeneralNormed

/-- On `ℝ × ℝ` with its supremum norm `max |x₁| |x₂|`, wherever `|x.2| < x.1` the norm coincides
locally with the first projection, so its derivative is `ContinuousLinearMap.fst`. -/
theorem hasFDerivAt_norm_prod_of_abs_lt {x : ℝ × ℝ} (hx : |x.2| < x.1) :
    HasFDerivAt (fun y : ℝ × ℝ => ‖y‖) (ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
  refine (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.congr_of_eventuallyEq ?_
  have hopen : IsOpen {y : ℝ × ℝ | |y.2| < y.1} :=
    isOpen_lt (continuous_abs.comp continuous_snd) continuous_fst
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hy1 : 0 < y.1 := (abs_nonneg y.2).trans_lt hy
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy1, max_eq_left hy.le]
  rfl

/-- On `ℝ × ℝ` with its supremum norm, the derivative of the norm at `(1, 1 / 2)` annihilates
`(0, 1)`, unlike the inner-product formula `x ↦ ⟪x / ‖x‖, ·⟫`. -/
theorem fderiv_norm_prod_one_half_apply :
    fderiv ℝ (fun y : ℝ × ℝ => ‖y‖) (1, (1 : ℝ) / 2) (0, 1) = 0 := by
  have h : HasFDerivAt (fun y : ℝ × ℝ => ‖y‖) (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (1, (1 : ℝ) / 2) :=
    hasFDerivAt_norm_prod_of_abs_lt (by norm_num)
  rw [h.fderiv]
  rfl

/-- The coordinate continuous linear equivalence identifying `ℝ × ℝ` (with the supremum norm) and
`EuclideanSpace ℝ (Fin 2)` (with the Euclidean norm). -/
def prodEquivEuclideanSpaceFinTwo : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (LinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).symm

/-- Local Sobolev classes on `ℝ × ℝ` (with the supremum norm and product Lebesgue measure) agree
with those on `EuclideanSpace ℝ (Fin 2)` under the coordinate equivalence
`TauCeti.prodEquivEuclideanSpaceFinTwo`. -/
theorem memWkpLoc_prod_iff_euclideanSpaceFinTwo {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {p : ENNReal} {U : Set (ℝ × ℝ)} {V : Set (EuclideanSpace ℝ (Fin 2))}
    {k : ℕ} {f : EuclideanSpace ℝ (Fin 2) → F}
    (hUV : U = prodEquivEuclideanSpaceFinTwo ⁻¹' V) :
    MemWkpLoc p U k (f ∘ prodEquivEuclideanSpaceFinTwo) ↔ MemWkpLoc p V k f := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  exact prodEquivEuclideanSpaceFinTwo.memWkpLoc_comp_iff hUV

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal} {U : Set ℂ}

/-! ### Polynomials -/

/-- Every complex polynomial is in every local Sobolev class on every set. -/
protected theorem _root_.Polynomial.memWkpLoc (P : Polynomial ℂ) (U : Set ℂ) (k : ℕ) :
    MemWkpLoc p U k (fun z => P.eval z) :=
  P.differentiable.memWkpLoc

/-! ### The norm is not in `W^{2,p}` for `p ≥ 2` -/

/-- The norm `z ↦ ‖z‖` is not in the local class `W^{2,p}` on any set whose interior contains the
origin, for `p ≥ 2`. Its second weak derivative has size `‖z‖⁻¹`, and `‖z‖ ^ (-2)` is not
integrable near the origin of the plane. A definition omitting the `Lᵖ` bound on the top
derivative would accept it. -/
theorem not_memWkpLoc_two_norm (hp : 2 ≤ p) (h0 : (0 : ℂ) ∈ interior U) :
    ¬ MemWkpLoc p U 2 (fun z : ℂ => ‖z‖) := by
  intro h
  obtain ⟨-, D₁, hD₁, h₁⟩ := memWkpLoc_succ_iff.1 h
  obtain ⟨-, D₂, hD₂, h₂⟩ := memWkpLoc_succ_iff.1 h₁
  have hL := memWkpLoc_zero_iff.1 h₂
  set Ω : Opens ℂ := Opens.interior U
  set N : ℂ → ℂ →L[ℝ] ℝ := fderiv ℝ fun y : ℂ => ‖y‖
  -- The first weak derivative is the classical derivative of the norm.
  have hN : HasWeakFDerivOn volume Ω (fun y : ℂ => ‖y‖) N :=
    lipschitzWith_one_norm.locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn_fderiv
  have hD₂N : HasWeakFDerivOn volume Ω N D₂ := hD₂.congr_ae (hD₁.ae_eq hN)
  -- Away from the origin, `N` is smooth.
  set Ω' : Opens ℂ := Ω ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hNsmooth : ContDiffOn ℝ 1 N (Ω' : Set ℂ) := by
    intro z hz
    have hz0 : z ≠ 0 := hz.2
    exact ((contDiffAt_norm ℝ hz0 : ContDiffAt ℝ 2 (fun y : ℂ => ‖y‖) z).fderiv_right
      (by norm_num)).contDiffWithinAt
  have hNw : HasWeakFDerivOn volume Ω' N (fderiv ℝ N) := by
    apply hasWeakFDerivOn_of_differentiableOn
    · exact (hNsmooth.continuousOn_fderiv_of_isOpen Ω'.isOpen le_rfl).locallyIntegrableOn
        Ω'.isOpen.measurableSet
    · exact fun z hz => (hNsmooth.differentiableOn one_ne_zero).differentiableAt
        (Ω'.isOpen.mem_nhds hz)
  have hae : D₂ =ᵐ[volume.restrict Ω'] fderiv ℝ N := (hD₂N.mono inf_le_left).ae_eq hNw
  -- Integrate on a small ball around the origin.
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
  have hK : closedBall (0 : ℂ) (r / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans (hrU.trans interior_subset)
  have hfin : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) (r / 2))) :=
    ⟨by simpa using (isCompact_closedBall (0 : ℂ) (r / 2)).measure_lt_top⟩
  have hD₂2 := ((memLpLoc_iff.1 hL _ hK (isCompact_closedBall 0 _)).mono_exponent hp).mono_measure
    (Measure.restrict_mono ball_subset_closedBall le_rfl :
      volume.restrict (ball (0 : ℂ) (r / 2)) ≤ volume.restrict (closedBall (0 : ℂ) (r / 2)))
  have hball : ball (0 : ℂ) (r / 2) ⊆ Ω ∪ {0} := fun z hz =>
    Or.inl (interior_mono subset_rfl (hrU (ball_subset_ball (by linarith) hz)))
  have hnull : ∀ᵐ z ∂volume, z ≠ (0 : ℂ) := by
    simp [ae_iff, measure_singleton]
  have hae' : D₂ =ᵐ[volume.restrict (ball (0 : ℂ) (r / 2))] fderiv ℝ N := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
    have h1 := (ae_restrict_iff' Ω'.isOpen.measurableSet).1 hae
    filter_upwards [h1, hnull] with z hz hz0 hzb
    rcases hball hzb with hzΩ | hz
    · exact hz ⟨hzΩ, hz0⟩
    · exact absurd hz hz0
  have hG := hD₂2.ae_eq hae'
  have hint := (integrable_norm_rpow_iff hG.norm.aestronglyMeasurable two_ne_zero
    ENNReal.ofNat_ne_top).2 hG.norm
  have hsing : IntegrableOn (fun z : ℂ => ‖z‖ ^ (-2 : ℝ)) (ball (0 : ℂ) (r / 2)) := by
    refine hint.mono' (by fun_prop : Measurable fun z : ℂ => ‖z‖ ^ (-2 : ℝ)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_ball).2 ?_)
    filter_upwards [hnull] with z hz0 _
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), Real.rpow_neg (norm_nonneg z),
      ← Real.inv_rpow (norm_nonneg z)]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    rw [norm_norm]
    -- The tangential direction `I * z` is orthogonal to `z`.
    refine inv_norm_le_norm_fderiv_fderiv_norm hz0 (mul_ne_zero Complex.I_ne_zero hz0) ?_
    simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have := (integrableOn_norm_rpow_ball_iff (E := ℂ) (mu := volume) (s := -2)
    (half_pos hr)).1 hsing
  simp [Complex.finrank_real_complex] at this

/-! ### The unit radial field and the planar norm in `W^{2,p}` -/

section UnitRadial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ENNReal} {U : Set E}

/-- For `1 < dim E` and `p < dim E`, the coordinate `x ↦ ‖x‖⁻¹ ⟪x, e⟫` of the unit radial field
`x / ‖x‖` lies in `W^{1,p}_loc` on every set: it is bounded, and its weak derivative has size at
most `2 ‖e‖ ‖x‖⁻¹`. -/
private theorem memWkpLoc_one_norm_rpow_neg_one_mul_inner (hd : 1 < Module.finrank ℝ E)
    (hp : p < Module.finrank ℝ E) (e : E) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ (-1 : ℝ) * ⟪x, e⟫) μ := by
  refine memWkpLoc_one_iff.2 ⟨memLpLoc_iff.2 fun K _ hK => ?_, _,
    hasWeakFDerivOn_norm_rpow_neg_one_mul_inner hd e _, memLpLoc_iff.2 fun K _ hK => ?_⟩
  · have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact MemLp.of_bound (by fun_prop : Measurable _).aestronglyMeasurable ‖e‖
      (Eventually.of_forall fun x => abs_norm_rpow_neg_one_mul_inner_le e x)
  · have hker : MemLp (fun x : E => ‖x‖⁻¹) p (μ.restrict K) := hK.memLp_norm_inv_restrict hp
    refine (hker.const_mul (2 * ‖e‖)).of_le (by fun_prop : Measurable _).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_neg_one]
    exact norm_norm_rpow_neg_one_smul_innerSL_sub_le e x

/-- On a finite-dimensional real inner product space of dimension at least `2`, the unit radial
field `x ↦ ‖x‖⁻¹ • x` lies in `W^{1,p}_loc` on every set for `p < dim E`. -/
theorem memWkpLoc_one_norm_inv_smul (hd : 1 < Module.finrank ℝ E)
    (hp : p < Module.finrank ℝ E) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) μ := by
  let b := stdOrthonormalBasis ℝ E
  refine b.toBasis.memWkpLoc_iff.2 fun i => ?_
  have hcoord : (fun x : E => b.toBasis.repr (‖x‖⁻¹ • x) i) =
      fun x : E => ‖x‖ ^ (-1 : ℝ) * ⟪x, b i⟫ := by
    funext x
    rw [OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply, inner_smul_right,
      real_inner_comm, Real.rpow_neg_one]
  rw [hcoord]
  exact memWkpLoc_one_norm_rpow_neg_one_mul_inner hd hp (b i)

private theorem ae_sum_inner_weakFDeriv_norm_inv_smul (hd : 1 < Module.finrank ℝ E)
    {Ω : Opens E} {D : E → E →L[ℝ] E}
    (hD : HasWeakFDerivOn μ Ω (fun x : E => ‖x‖⁻¹ • x) D) :
    let b := stdOrthonormalBasis ℝ E
    (fun x : E => ∑ i, ⟪b i, D x (b i)⟫) =ᵐ[μ.restrict Ω]
      fun x : E => ((Module.finrank ℝ E : ℝ) - 1) * ‖x‖⁻¹ := by
  intro b
  have hcoord : ∀ i, (fun x : E => ⟪b i, D x (b i)⟫) =ᵐ[μ.restrict Ω]
      fun x : E => ‖x‖ ^ (-1 : ℝ) - ‖x‖ ^ (-3 : ℝ) * ⟪x, b i⟫ ^ 2 := fun i => by
    have hDi : HasWeakFDerivOn μ Ω (fun x : E => ‖x‖ ^ (-1 : ℝ) * ⟪x, b i⟫)
        (fun x => (innerSL ℝ (b i)).comp (D x)) := by
      have hc := hD.clm_comp (innerSL ℝ (b i))
      convert hc using 1
      funext x
      rw [innerSL_apply_apply, inner_smul_right, real_inner_comm, Real.rpow_neg_one]
    have hae := hDi.ae_eq (hasWeakFDerivOn_norm_rpow_neg_one_mul_inner hd (b i) Ω)
    filter_upwards [hae] with x hx
    have hxi := DFunLike.congr_fun hx (b i)
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, sub_apply, smul_apply,
      smul_eq_mul, real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow, mul_one] at hxi
    rw [hxi, sq, mul_assoc]
  filter_upwards [ae_all_iff.2 hcoord] with x hx
  calc ∑ i, ⟪b i, D x (b i)⟫
      = ∑ i, (‖x‖ ^ (-1 : ℝ) - ‖x‖ ^ (-3 : ℝ) * ⟪x, b i⟫ ^ 2) :=
        Finset.sum_congr rfl fun i _ => hx i
    _ = (Module.finrank ℝ E : ℝ) * ‖x‖ ^ (-1 : ℝ) - ‖x‖ ^ (-3 : ℝ) * ∑ i, ⟪x, b i⟫ ^ 2 := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
    _ = (Module.finrank ℝ E : ℝ) * ‖x‖⁻¹ - ‖x‖ ^ (-3 : ℝ) * ‖x‖ ^ (2 : ℝ) := by
        have hparse : ∑ i, ⟪x, b i⟫ ^ 2 = ‖x‖ ^ 2 := by
          simpa only [real_inner_comm, b.repr_apply_apply, Real.norm_eq_abs, sq_abs] using
            b.sum_sq_norm_inner_right x
        rw [hparse, Real.rpow_neg_one, Real.rpow_two]
    _ = ((Module.finrank ℝ E : ℝ) - 1) * ‖x‖⁻¹ := by
        rcases eq_or_ne x 0 with rfl | hx0
        · simp
        rw [← Real.rpow_add (norm_pos_iff.2 hx0), show (-3 : ℝ) + 2 = -1 by norm_num,
          Real.rpow_neg_one]
        ring

/-- **The unit radial field `x ↦ ‖x‖⁻¹ • x` is in `W^{1,p}_loc` near the origin exactly for
`p < dim E`.** In dimension `d ≥ 2`, the divergence of the weak derivative is `(d - 1) ‖x‖⁻¹`,
which lies in `Lᵖ_loc` near `0` precisely when `p < d`. -/
theorem memWkpLoc_one_norm_inv_smul_iff (hd : 1 < Module.finrank ℝ E)
    (h0 : (0 : E) ∈ interior U) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) μ ↔ p < Module.finrank ℝ E := by
  refine ⟨fun h => ?_, memWkpLoc_one_norm_inv_smul hd⟩
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (zero_lt_one.trans hd)
  let b := stdOrthonormalBasis ℝ E
  obtain ⟨-, D, hD, hDLp⟩ := memWkpLoc_one_iff.1 h
  have htr_Lp : MemLpLoc p (interior U) (fun x => ∑ i, ⟪b i, D x (b i)⟫) μ :=
    MemLpLoc.sum _ fun i _ => (hDLp.mono_set interior_subset).clm_comp
      ((innerSL ℝ (b i)).comp (ContinuousLinearMap.apply ℝ E (b i)))
  have htr_ae := ae_sum_inner_weakFDeriv_norm_inv_smul hd hD
  have hd_ne : ((Module.finrank ℝ E : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
    linarith
  have hinv : MemLpLoc p (interior U) (fun x : E => ‖x‖⁻¹) μ := by
    have hsmul := (htr_Lp.congr_ae htr_ae).const_smul ((Module.finrank ℝ E : ℝ) - 1)⁻¹
    convert hsmul using 1
    funext x
    simp [hd_ne]
  exact (memLpLoc_norm_inv_iff (isOpen_interior.mem_nhds h0)).1 hinv

end UnitRadial

/-- The norm `z ↦ ‖z‖` is in the local class `W^{2,p}` on every set for `p < 2`: its second
weak derivative has size `‖z‖⁻¹`, which is `Lᵖ` near the origin of the plane exactly when
`p < 2`. -/
theorem memWkpLoc_two_norm (hp : p < 2) : MemWkpLoc p U 2 (fun z : ℂ => ‖z‖) := by
  have hd : 1 < Module.finrank ℝ ℂ := by simp [Complex.finrank_real_complex]
  have hp' : p < Module.finrank ℝ ℂ := by simpa [Complex.finrank_real_complex] using hp
  have hD := hasWeakFDerivOn_norm_rpow (μ := volume) (s := 1)
    (by norm_num [Complex.finrank_real_complex]) (Opens.interior U)
  norm_num only [Real.rpow_one, one_mul] at hD
  refine continuous_norm.continuousOn.memLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn hD ?_ ?_
  · simpa only [smul_apply, innerSL_apply_apply, smul_eq_mul] using
      memWkpLoc_one_norm_rpow_neg_one_mul_inner (U := U) hd hp' 1
  · simpa only [smul_apply, innerSL_apply_apply, smul_eq_mul] using
      memWkpLoc_one_norm_rpow_neg_one_mul_inner (U := U) hd hp' Complex.I

/-- The norm `z ↦ ‖z‖` is in the local class `W^{2,p}` on a set whose interior contains the
origin exactly when `p < 2`. -/
theorem memWkpLoc_two_norm_iff (h0 : (0 : ℂ) ∈ interior U) :
    MemWkpLoc p U 2 (fun z : ℂ => ‖z‖) ↔ p < 2 :=
  ⟨fun h => not_le.1 fun hp => not_memWkpLoc_two_norm hp h0 h, memWkpLoc_two_norm⟩

/-! ### A jump across a hyperplane -/

section HalfSpaceJump

private theorem integral_deriv_bump_indicator_Ioi (a : ContDiffBump (0 : ℝ)) :
    ∫ x : ℝ, deriv a x * (Ioi (0 : ℝ)).indicator 1 x = -1 := by
  have hda : ∀ x, HasDerivAt a (deriv a x) x := fun x =>
    ((a.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have hfun : (fun x : ℝ => deriv a x * (Ioi (0 : ℝ)).indicator 1 x) =
      (Ioi (0 : ℝ)).indicator (deriv a) := by
    funext x
    by_cases hx : 0 < x <;> simp [Set.indicator, hx]
  rw [hfun, integral_indicator measurableSet_Ioi]
  have hdc : Continuous (deriv a) := (a.contDiff (n := 1)).continuous_deriv le_rfl
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (m := 0) a.continuous.continuousWithinAt
    (fun x _ => hda x)
    (hdc.integrable_of_hasCompactSupport a.hasCompactSupport.deriv).integrableOn ?_,
    a.one_of_mem_closedBall (mem_closedBall_self a.rIn_pos.le)]
  · simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop a.rOut] with x hx
    refine (a.zero_of_le_dist ?_).symm
    rw [Real.dist_eq, sub_zero]
    exact hx.trans (le_abs_self x)

private theorem hasWeakFDerivOn_indicator_fst_pos_ae_zero {m : ℕ}
    {Ω : Opens (ℝ × EuclideanSpace ℝ (Fin m))}
    {D : (ℝ × EuclideanSpace ℝ (Fin m)) → (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ}
    (hD : HasWeakFDerivOn volume Ω
      ({q : ℝ × EuclideanSpace ℝ (Fin m) | 0 < q.1}.indicator fun _ => (1 : ℝ)) D) :
    D =ᵐ[volume.restrict Ω] 0 := by
  let K := EuclideanSpace ℝ (Fin m)
  have : (volume : Measure (ℝ × K)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  let u : ℝ × K → ℝ := {q : ℝ × K | 0 < q.1}.indicator fun _ => (1 : ℝ)
  let Ωp : Opens (ℝ × K) := Ω ⊓ ⟨{q | 0 < q.1}, isOpen_lt continuous_const continuous_fst⟩
  let Ωn : Opens (ℝ × K) := Ω ⊓ ⟨{q | q.1 < 0}, isOpen_lt continuous_fst continuous_const⟩
  have hconst : HasWeakFDerivOn volume Ωp (fun _ => (1 : ℝ)) 0 := hasWeakFDerivOn_iff.2 fun v => by
    simpa using (hasWeakLineDerivOn_const (1 : ℝ) :
      HasWeakLineDerivOn volume Ωp (fun _ => (1 : ℝ)) (fun _ => 0) v)
  have hp : HasWeakFDerivOn volume Ωp u 0 := hconst.congr_ae <|
    (ae_restrict_iff' Ωp.isOpen.measurableSet).2 <| Eventually.of_forall fun q hq => by
      simp [u, Set.indicator_of_mem (show q ∈ {q : ℝ × K | 0 < q.1} from hq.2)]
  have hn : HasWeakFDerivOn volume Ωn u 0 := (hasWeakFDerivOn_zero (μ := volume)).congr_ae <|
    (ae_restrict_iff' Ωn.isOpen.measurableSet).2 <| Eventually.of_forall fun q hq => by
      have hq' : ¬ 0 < q.1 := not_lt.2 (le_of_lt hq.2)
      simp [u, hq']
  have hDp := (ae_restrict_iff' Ωp.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hp)
  have hDn := (ae_restrict_iff' Ωn.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hn)
  have hnull : volume {q : ℝ × K | q.1 = 0} = 0 := by
    have hset : {q : ℝ × K | q.1 = 0} = ({0} : Set ℝ) ×ˢ (univ : Set K) := by ext q; simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
  filter_upwards [hDp, hDn, measure_eq_zero_iff_ae_notMem.1 hnull] with q hqp hqn hq0 hqΩ
  rcases lt_or_gt_of_ne hq0 with h | h
  · exact hqn ⟨hqΩ, h⟩
  · exact hqp ⟨hqΩ, h⟩

private noncomputable def prodBumpTestFunction {m : ℕ}
    {Ω : Opens (ℝ × EuclideanSpace ℝ (Fin m))} {y₀ : EuclideanSpace ℝ (Fin m)}
    {ε : ℝ} (hε : 0 < ε) (hball : ball ((0 : ℝ), y₀) ε ⊆ Ω) :
    let a : ContDiffBump (0 : ℝ) := ⟨ε / 3, ε / 2, by positivity, by linarith⟩
    let b : ContDiffBump y₀ := ⟨ε / 3, ε / 2, by positivity, by linarith⟩
    { φ : 𝓓(Ω, ℝ) // ∀ q, (φ : ℝ × EuclideanSpace ℝ (Fin m) → ℝ) q = a q.1 * b q.2 } := by
  let K := EuclideanSpace ℝ (Fin m)
  let a : ContDiffBump (0 : ℝ) := ⟨ε / 3, ε / 2, by positivity, by linarith⟩
  let b : ContDiffBump y₀ := ⟨ε / 3, ε / 2, by positivity, by linarith⟩
  let f : ℝ × K → ℝ := ((a : ℝ → ℝ) ∘ Prod.fst) * ((b : K → ℝ) ∘ Prod.snd)
  have hfs : tsupport f ⊆ closedBall (0, y₀) (ε / 2) := fun q hq => by
    have hq1 : q ∈ Prod.fst ⁻¹' tsupport a :=
      tsupport_comp_subset_preimage (a : ℝ → ℝ) continuous_fst (tsupport_mul_subset_left hq)
    have hq2 : q ∈ Prod.snd ⁻¹' tsupport b :=
      tsupport_comp_subset_preimage (b : K → ℝ) continuous_snd (tsupport_mul_subset_right hq)
    rw [mem_preimage, a.tsupport_eq, mem_closedBall] at hq1
    rw [mem_preimage, b.tsupport_eq, mem_closedBall] at hq2
    exact mem_closedBall.2 (by rw [Prod.dist_eq]; exact max_le hq1 hq2)
  exact ⟨⟨f, (a.contDiff.comp (ContinuousLinearMap.fst ℝ ℝ K).contDiff).mul
      (b.contDiff.comp (ContinuousLinearMap.snd ℝ ℝ K).contDiff),
    (isCompact_closedBall ((0 : ℝ), y₀) _).of_isClosed_subset (isClosed_tsupport f) hfs,
    fun q hq => hball (closedBall_subset_ball (by linarith) (hfs hq))⟩, fun _ => rfl⟩

private theorem not_hasWeakFDerivOn_indicator_fst_pos {m : ℕ}
    {Ω : Opens (ℝ × EuclideanSpace ℝ (Fin m))} {y₀ : EuclideanSpace ℝ (Fin m)}
    (h0 : ((0 : ℝ), y₀) ∈ Ω)
    (D : (ℝ × EuclideanSpace ℝ (Fin m)) → (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn volume Ω
      ({q : ℝ × EuclideanSpace ℝ (Fin m) | 0 < q.1}.indicator fun _ => (1 : ℝ)) D := by
  intro hD
  let K := EuclideanSpace ℝ (Fin m)
  let u : ℝ × K → ℝ := {q : ℝ × K | 0 < q.1}.indicator fun _ => (1 : ℝ)
  have hline :=
    (hD.congr_ae_deriv (hasWeakFDerivOn_indicator_fst_pos_ae_zero hD)).hasWeakLineDerivOn
      ((1 : ℝ), (0 : K))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen (0, y₀) h0
  let a : ContDiffBump (0 : ℝ) := ⟨ε / 3, ε / 2, by positivity, by linarith⟩
  let b : ContDiffBump y₀ := ⟨ε / 3, ε / 2, by positivity, by linarith⟩
  obtain ⟨φ, hφ⟩ := prodBumpTestFunction hε hball
  have hkey := hline.integral_lineDeriv_smul_eq_neg_integral_smul φ
  simp only [Pi.zero_apply, zero_apply, smul_zero, integral_zero, neg_zero] at hkey
  have hda : ∀ x, HasDerivAt a (deriv a x) x := fun x =>
    ((a.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have hldf : ∀ q : ℝ × K, lineDeriv ℝ (φ : ℝ × K → ℝ) q (1, 0) = deriv a q.1 * b q.2 := by
    intro q
    refine HasLineDerivAt.lineDeriv
      (?_ : HasDerivAt (fun t : ℝ => (φ : ℝ × K → ℝ) (q + t • ((1 : ℝ), (0 : K)))) _ 0)
    have h := ((hda (q.1 + 0)).comp_const_add q.1 0).mul_const (b q.2)
    simp only [add_zero] at h
    convert h using 1
    funext t
    simp [hφ, a, b]
  have hint : ∫ q : ℝ × K, lineDeriv ℝ (φ : ℝ × K → ℝ) q (1, 0) • u q =
      (∫ x : ℝ, deriv a x * (Ioi (0 : ℝ)).indicator 1 x) * ∫ y : K, b y := by
    rw [Measure.volume_eq_prod, ← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [hldf, smul_eq_mul, u]
    by_cases hq : 0 < q.1 <;> simp [Set.indicator, hq]
  rw [hint, integral_deriv_bump_indicator_Ioi a] at hkey
  have hb := b.integral_pos (μ := volume)
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ENNReal} {U : Set E}

omit [FiniteDimensional ℝ E] in
/-- The indicator of an open half-space `{x | 0 < ℓ x}` is locally `Lᵖ` on every set, for every
exponent and every continuous linear functional `ℓ`. -/
theorem memLpLoc_indicator_pos_clm (ℓ : E →L[ℝ] ℝ) :
    MemLpLoc p U ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) μ := by
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact memLp_indicator_const p
    (measurableSet_lt measurable_const ℓ.continuous.measurable).nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem exists_continuousLinearEquiv_clm_eq_fst {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ∃ (m : ℕ) (e : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] E), ∀ q, ℓ (e q) = q.1 := by
  obtain ⟨w, hw⟩ : ∃ w : E, ℓ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (ContinuousLinearMap.ext h)
  let v : E := (ℓ w)⁻¹ • w
  have hℓv : ℓ v = 1 := by simp [v, hw]
  let m := Module.finrank ℝ (LinearMap.ker ℓ.toLinearMap)
  let eK : EuclideanSpace ℝ (Fin m) ≃L[ℝ] LinearMap.ker ℓ.toLinearMap :=
    (EuclideanSpace.equiv (Fin m) ℝ).trans (Module.finBasis ℝ _).equivFunL.symm
  refine ⟨m,
    { toFun := fun q => q.1 • v + (eK q.2 : E)
      map_add' := fun q₁ q₂ => by simp [add_smul]; abel
      map_smul' := fun c q => by simp [smul_add, mul_smul]
      invFun := fun x => (ℓ x, eK.symm ⟨x - ℓ x • v, by simp [LinearMap.mem_ker, hℓv]⟩)
      left_inv := fun q => by
        have hq2 : ℓ (eK q.2 : E) = 0 := (eK q.2).2
        ext <;> simp [hq2, hℓv]
      right_inv := fun x => by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }, fun q => by
        have hq2 : ℓ (eK q.2 : E) = 0 := (eK q.2).2
        simp [hq2, hℓv]⟩

/-- The indicator of a half-space `{x | 0 < ℓ x}` (for nonzero `ℓ : E →L[ℝ] ℝ`) has no weak
derivative on any open set meeting `ker ℓ`: its distributional derivative is a measure carried by
the hyperplane `ker ℓ`. -/
theorem not_hasWeakFDerivOn_indicator_pos_clm {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {Ω : Opens E}
    {x₀ : E} (hx₀ : x₀ ∈ Ω) (hker : ℓ x₀ = 0) (D : E → E →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn μ Ω ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) D := by
  intro hD
  obtain ⟨m, e, hℓe⟩ := exists_continuousLinearEquiv_clm_eq_fst hℓ
  let q₀ := e.symm x₀
  have hq₀1 : q₀.1 = 0 := by rw [← hℓe q₀, e.apply_symm_apply, hker]
  have hq₀ : ((0 : ℝ), q₀.2) = q₀ := Prod.ext hq₀1.symm rfl
  let Ω' : Opens (ℝ × EuclideanSpace ℝ (Fin m)) := ⟨e ⁻¹' Ω, Ω.isOpen.preimage e.continuous⟩
  have : (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hD' := hD.comp_continuousLinearEquiv volume e (U := Ω') (mapsTo_preimage e Ω)
  have hcomp : ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) ∘ e =
      ({q : ℝ × EuclideanSpace ℝ (Fin m) | 0 < q.1}.indicator fun _ => (1 : ℝ)) := by
    funext q
    simp [Set.indicator, hℓe]
  rw [hcomp] at hD'
  exact not_hasWeakFDerivOn_indicator_fst_pos (Ω := Ω') (y₀ := q₀.2)
    (by simpa [Ω', hq₀, q₀] using hx₀) _ hD'

/-- The indicator of a half-space `{x | 0 < ℓ x}` (for nonzero `ℓ : E →L[ℝ] ℝ`) is in no local
Sobolev class of positive order on a set whose interior meets `ker ℓ`, although it is locally
`Lᵖ` there (`TauCeti.memLpLoc_indicator_pos_clm`). -/
theorem not_memWkpLoc_indicator_pos_clm {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {k : ℕ} {x₀ : E}
    (hx₀ : x₀ ∈ interior U) (hker : ℓ x₀ = 0) :
    ¬ MemWkpLoc p U (k + 1) ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) μ := fun h => by
  obtain ⟨-, D, hD, -⟩ := memWkpLoc_succ_iff.1 h
  exact not_hasWeakFDerivOn_indicator_pos_clm hℓ (Ω := Opens.interior U) hx₀ hker D hD

end HalfSpaceJump

/-- The indicator of the right half-plane is locally `Lᵖ` on every set, for every exponent. -/
theorem memLpLoc_indicator_re_pos :
    MemLpLoc p U ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) :=
  memLpLoc_indicator_pos_clm Complex.reCLM

/-- The indicator of the right half-plane has no weak derivative on any open set meeting the
imaginary axis: its distributional derivative is a measure carried by the axis. -/
theorem not_hasWeakFDerivOn_indicator_re_pos {Ω : Opens ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hre : z₀.re = 0) (D : ℂ → ℂ →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn volume Ω ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) D :=
  not_hasWeakFDerivOn_indicator_pos_clm (ℓ := Complex.reCLM)
    (fun h => by simpa using DFunLike.congr_fun h 1) hz₀ hre D

/-- The indicator of the right half-plane is in no local Sobolev class of positive order on a
set whose interior meets the imaginary axis, although it is locally `Lᵖ` there. -/
theorem not_memWkpLoc_indicator_re_pos {k : ℕ} {z₀ : ℂ} (hz₀ : z₀ ∈ interior U)
    (hre : z₀.re = 0) :
    ¬ MemWkpLoc p U (k + 1) ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) := fun h => by
  obtain ⟨-, D, hD, -⟩ := memWkpLoc_succ_iff.1 h
  exact not_hasWeakFDerivOn_indicator_re_pos (Ω := Opens.interior U) hz₀ hre D hD

/-! ### A square-root profile on the half-disc -/

/-- The open upper half-plane. -/
private def openUpperHalfPlane : Opens ℂ := ⟨{z | 0 < z.im}, isOpen_lt continuous_const
  Complex.continuous_im⟩

private theorem hasWeakFDerivOn_sqrt_im :
    HasWeakFDerivOn volume openUpperHalfPlane (fun z : ℂ => √z.im)
      (fun z => (1 / (2 * √z.im)) • Complex.imCLM) := by
  have hD : ContinuousOn (fun z : ℂ => (1 / (2 * √z.im)) • Complex.imCLM) {z | 0 < z.im} := by
    fun_prop (disch := exact fun z hz => mul_ne_zero two_ne_zero (Real.sqrt_pos.2 hz).ne')
  exact hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
    (by fun_prop : Continuous fun z : ℂ => √z.im).continuousOn
    (hD.locallyIntegrableOn openUpperHalfPlane.isOpen.measurableSet)
    fun z hz => Complex.imCLM.hasFDerivAt.sqrt hz.1.ne'

/-- On the closed upper half-disc `ball 0 1 ∩ {z | 0 ≤ z.im}`, the map `z ↦ √z.im` is in the
local class `W^{1,p}` exactly when `p < 2`. The `Lᵖ` bounds are imposed on compact sets reaching
the real axis, where the derivative `(2 √(Im z))⁻¹` is not square integrable. A definition that
only tested compact subsets of the open half-disc would accept it for every `p`. -/
theorem memWkpLoc_sqrt_im_iff :
    MemWkpLoc p (ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im}) 1 (fun z : ℂ => √z.im) ↔ p < 2 := by
  set U : Set ℂ := ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im}
  set D : ℂ → ℂ →L[ℝ] ℝ := fun z => (1 / (2 * √z.im)) • Complex.imCLM
  have hint : interior U = ball (0 : ℂ) 1 ∩ {z | 0 < z.im} := by
    rw [interior_inter, isOpen_ball.interior_eq, Complex.interior_setOfPred_le_im]
  have hDU : HasWeakFDerivOn volume (Opens.interior U) (fun z : ℂ => √z.im) D :=
    hasWeakFDerivOn_sqrt_im.mono fun z hz => by
      rw [Opens.mem_interior, hint] at hz
      exact hz.2
  constructor
  · intro h
    by_contra hp
    have hp : 2 ≤ p := not_lt.1 hp
    obtain ⟨-, D', hD', h₀⟩ := memWkpLoc_succ_iff.1 h
    have hL := memWkpLoc_zero_iff.1 h₀
    have hae := (ae_restrict_iff' (Opens.interior U).isOpen.measurableSet).1 (hD'.ae_eq hDU)
    set K : Set ℂ := Icc (-1 / 2) (1 / 2) ×ℂ Icc 0 (1 / 4)
    have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
    have hKU : K ⊆ U := fun z hz => by
      obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := hz
      have h1 : |z.re| ≤ 1 / 2 := abs_le.2 ⟨by linarith, hr2⟩
      have h2 : |z.im| ≤ 1 / 4 := abs_le.2 ⟨by linarith, hi2⟩
      exact ⟨mem_ball_zero_iff.2 ((Complex.norm_le_abs_re_add_abs_im z).trans_lt
        (by linarith)), hi1⟩
    have hfinK : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hKc.measure_lt_top⟩
    have hD'2 := (memLpLoc_iff.1 hL K hKU hKc).mono_exponent hp
    have haeK : D' =ᵐ[volume.restrict K] D := by
      rw [EventuallyEq, ae_restrict_iff' hKc.isClosed.measurableSet]
      filter_upwards [hae, measure_eq_zero_iff_ae_notMem.1 (Complex.volume_setOf_im_eq 0)]
        with z hz hz0 hzK
      refine hz ?_
      rw [Opens.coe_interior, hint]
      exact ⟨(hKU hzK).1, lt_of_le_of_ne (hKU hzK).2 (Ne.symm hz0)⟩
    have hgK : MemLp (fun z : ℂ => 1 / (2 * √z.im)) 2 (volume.restrict K) :=
      (hD'2.ae_eq haeK).congr_norm
        (by fun_prop : Measurable fun z : ℂ => 1 / (2 * √z.im)).aestronglyMeasurable
        (Eventually.of_forall fun z => by rw [norm_smul, Complex.imCLM_norm, mul_one])
    have hiK := (integrable_norm_rpow_iff hgK.aestronglyMeasurable two_ne_zero
      ENNReal.ofNat_ne_top).2 hgK
    have hg : IntegrableOn (fun t : ℝ => ‖1 / (2 * √t)‖ ^ (2 : ENNReal).toReal)
        (Icc 0 (1 / 4)) :=
      Complex.integrableOn_of_integrableOn_comp_im_reProdIm measurableSet_Icc measurableSet_Icc
        (by simp [Real.volume_Icc]; norm_num) hiK
    have hinv : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 (1 / 4)) := by
      refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioo).1
        ((hg.mono_set Ioo_subset_Icc_self).const_mul 4)
      have ht0 : 0 < t := ht.1
      rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_of_nonneg (by positivity), div_pow,
        mul_pow, Real.sq_sqrt ht0.le, Real.rpow_neg_one]
      field_simp
      norm_num
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1 / 4)).1 hinv
    linarith
  · intro hp
    refine memWkpLoc_succ_iff.2
      ⟨(by fun_prop : Continuous fun z : ℂ => √z.im).continuousOn.memLpLoc, D, hDU,
        memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKU _ => ?_)⟩
    have hKR : K ⊆ Icc (-1) 1 ×ℂ Icc 0 1 := fun z hz => by
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 (hKU hz).1
      have hre := (Complex.abs_re_le_norm z).trans hz1.le
      have him := (Complex.abs_im_le_norm z).trans hz1.le
      exact ⟨abs_le.1 hre, (hKU hz).2, (abs_le.1 him).2⟩
    have : IsFiniteMeasure (volume.restrict (Icc (-1 : ℝ) 1)) := ⟨by simp⟩
    have hp' : p ≠ ⊤ := ne_top_of_lt hp
    have hp2 : p.toReal < 2 := by
      simpa using (ENNReal.toReal_lt_toReal hp' (by simp)).2 hp
    -- The derivative profile `t ↦ (2 √t)⁻¹` is in `Lᵖ(0, 1)` for `p < 2`.
    have hsq : MemLp (fun t : ℝ => 1 / (2 * √t)) p (volume.restrict (Icc 0 1)) := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
      refine ((memLp_rpow_neg_restrict_Ioo one_pos hp' (by linarith : 1 / 2 * p.toReal < 1))
        |>.const_mul (1 / 2)).ae_eq
        ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => ?_))
      dsimp only
      rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.1.le]
      field_simp
    have hR : MemLp (fun z : ℂ => 1 / (2 * √z.im)) p
        (volume.restrict (Icc (-1) 1 ×ℂ Icc 0 1)) :=
      (hsq.comp_snd (volume.restrict (Icc (-1 : ℝ) 1)))
        |>.comp_measurePreserving
          (Complex.measurePreserving_measurableEquivRealProd_reProdIm measurableSet_Icc
            measurableSet_Icc)
    refine (hR.congr_norm ?_ (Eventually.of_forall fun z => by
      rw [norm_smul, Complex.imCLM_norm, mul_one]))
      |>.mono_measure (Measure.restrict_mono hKR le_rfl)
    exact ((by fun_prop : Measurable fun z : ℂ => 1 / (2 * √z.im)).smul_const
      Complex.imCLM).aestronglyMeasurable

/-- On the open upper half-disc, the map `z ↦ √z.im` is in the local class `W^{1,p}` for every
exponent, although it extends continuously to the real axis. Together with
`TauCeti.memWkpLoc_sqrt_im_iff`, a map can be continuous on the closed half-disc and locally
`W^{1,p}` on the open half-disc, with `p > 2`, without being locally `W^{1,p}` on the closed one. -/
theorem memWkpLoc_sqrt_im_ball_inter_im_pos :
    MemWkpLoc p (ball (0 : ℂ) 1 ∩ {z | 0 < z.im}) 1 (fun z : ℂ => √z.im) := by
  set V : Set ℂ := ball (0 : ℂ) 1 ∩ {z | 0 < z.im}
  refine memWkpLoc_succ_iff.2
    ⟨(by fun_prop : Continuous fun z : ℂ => √z.im).continuousOn.memLpLoc, _,
      hasWeakFDerivOn_sqrt_im.mono fun z hz => (interior_subset (s := V) hz).2,
      memWkpLoc_zero_iff.2 (ContinuousOn.memLpLoc ?_)⟩
  fun_prop (disch := exact fun z hz => mul_ne_zero two_ne_zero (Real.sqrt_pos.2 hz.2).ne')

/-! ### The logarithm of the norm and its gradient -/

/-- **The components of the gradient of `log ‖z‖` are locally `Lᵖ` near the origin exactly for
`p < 2`.** These are `Re z / ‖z‖²` and `Im z / ‖z‖²`, the divergence-form data of `log ‖z‖`. -/
theorem memLpLoc_re_div_and_im_div_iff (hU : U ∈ 𝓝 0) :
    (MemLpLoc p U (fun z : ℂ => z.re / ‖z‖ ^ 2) ∧ MemLpLoc p U fun z : ℂ => z.im / ‖z‖ ^ 2) ↔
      p < 2 := by
  have hinv : MemLpLoc p U (fun z : ℂ => ‖z‖⁻¹) ↔ p < 2 := by
    simpa [Complex.finrank_real_complex] using
      memLpLoc_norm_inv_iff (E := ℂ) (μ := volume) (p := p) hU
  rw [← hinv]
  have hdiv (a : ℝ) (z : ℂ) (hz : |a| ≤ ‖z‖) :
      ‖a / ‖z‖ ^ 2‖ ≤ ‖‖z‖⁻¹‖ := by
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    rw [norm_div, norm_pow, norm_norm, Real.norm_eq_abs,
      Real.norm_of_nonneg (inv_nonneg.2 hn.le), div_le_iff₀ (pow_pos hn 2)]
    calc |a| ≤ ‖z‖ := hz
      _ = ‖z‖⁻¹ * ‖z‖ ^ 2 := by field_simp
  constructor
  · rintro ⟨hf, hg⟩
    refine memLpLoc_iff.2 fun K hKU hK => ?_
    refine ((memLpLoc_iff.1 hf K hKU hK).norm.add
      (memLpLoc_iff.1 hg K hKU hK).norm).of_le (by fun_prop) ?_
    filter_upwards with z
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have key : ‖z‖⁻¹ ≤ |z.re| / ‖z‖ ^ 2 + |z.im| / ‖z‖ ^ 2 := by
      rw [← add_div, le_div_iff₀ (pow_pos hn 2)]
      calc ‖z‖⁻¹ * ‖z‖ ^ 2 = ‖z‖ := by field_simp
        _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    rw [Real.norm_of_nonneg (inv_nonneg.2 hn.le), Pi.add_apply,
      Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    simpa only [Real.norm_eq_abs, abs_div, abs_pow, abs_norm] using key
  · intro h
    exact ⟨memLpLoc_iff.2 fun K hKU hK => (memLpLoc_iff.1 h K hKU hK).of_le
        (by fun_prop : Measurable fun z : ℂ => z.re / ‖z‖ ^ 2).aestronglyMeasurable
        (ae_of_all _ fun z => hdiv _ z (Complex.abs_re_le_norm z)),
      memLpLoc_iff.2 fun K hKU hK => (memLpLoc_iff.1 h K hKU hK).of_le
        (by fun_prop : Measurable fun z : ℂ => z.im / ‖z‖ ^ 2).aestronglyMeasurable
        (ae_of_all _ fun z => hdiv _ z (Complex.abs_im_le_norm z))⟩

/-- **`log ‖z‖` is locally `W^{1,p}` near the origin exactly for `p < 2`.** -/
theorem memWkpLoc_one_log_norm_iff {Ω : Opens ℂ} (h0 : (0 : ℂ) ∈ Ω) :
    MemWkpLoc p Ω 1 (fun z : ℂ => Real.log ‖z‖) ↔ p < 2 := by
  have hU : (Ω : Set ℂ) ∈ 𝓝 0 := Ω.isOpen.mem_nhds h0
  have hmeas : AEStronglyMeasurable (fun z : ℂ => (‖z‖ ^ 2)⁻¹ • innerSL ℝ z) := by
    fun_prop
  -- Pointwise, the weak derivative of `log ‖z‖` has norm `‖z‖⁻¹`, both sides being `0` at `0`.
  have hnorm (z : ℂ) : ‖(‖z‖ ^ 2)⁻¹ • innerSL ℝ z‖ = ‖z‖⁻¹ := by
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    rw [← (hasFDerivAt_log_norm_of_ne hz).fderiv, norm_fderiv_log_norm_of_ne hz]
  simp only [memWkpLoc_succ_iff_of_isOpen, memWkpLoc_zero_iff]
  have hinv : MemLpLoc p (Ω : Set ℂ) (fun z : ℂ => ‖z‖⁻¹) ↔ p < 2 := by
    simpa [Complex.finrank_real_complex] using
      memLpLoc_norm_inv_iff (E := ℂ) (μ := volume) (p := p) hU
  rw [← hinv]
  constructor
  · rintro ⟨-, D, hD, hDp⟩
    have hae := hD.ae_eq (hasWeakFDerivOn_log_norm Ω)
    refine memLpLoc_iff.2 fun K hKU hK => ?_
    have := (memLpLoc_iff.1 (hDp.congr_ae hae) K hKU hK).norm
    simpa only [hnorm] using this
  · intro h
    refine ⟨memLpLoc_iff.2 fun K hKU hK => ?_, _, hasWeakFDerivOn_log_norm Ω,
      memLpLoc_iff.2 fun K hKU hK => ?_⟩
    · have hn : MemLp (fun z : ℂ => ‖z‖) p (volume.restrict K) :=
        memLpLoc_iff.1 (continuous_norm.continuousOn.memLpLoc (p := p)) K subset_rfl hK
      refine ((memLpLoc_iff.1 h K hKU hK).add hn).of_le
        (Real.measurable_log.comp measurable_norm).aestronglyMeasurable (ae_of_all _ fun z => ?_)
      rw [Pi.add_apply, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
      rcases eq_or_ne z 0 with rfl | hz0
      · simp
      have hn0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
      rw [abs_le]
      constructor
      · have := Real.log_le_sub_one_of_pos (inv_pos.2 hn0)
        rw [Real.log_inv] at this
        linarith
      · linarith [Real.log_le_sub_one_of_pos hn0, inv_pos.2 hn0]
    · exact (memLpLoc_iff.1 h K hKU hK).of_le hmeas.restrict
        (ae_of_all _ fun z => by
          rw [hnorm, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg z))])

/-! ### The even reflection fails at order two -/

/-- The even extension `z ↦ |Im z|` of the normal coordinate `Im z` is not in the local class
`W^{2,p}` on any set whose interior meets the real axis, for any exponent: its first derivative
jumps from `-Im` to `Im` across the axis, so its second derivative is a measure carried by the
axis. -/
theorem not_memWkpLoc_two_abs_im {z₀ : ℂ} (hz₀ : z₀ ∈ interior U) (him : z₀.im = 0) :
    ¬ MemWkpLoc p U 2 (fun z : ℂ => |z.im|) := by
  intro h
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_interior z₀ hz₀
  -- Rotate by a quarter turn, so that the axis becomes the imaginary axis.
  let A : ℂ ≃L[ℝ] ℂ := ((LinearEquiv.smulOfNeZero ℂ ℂ Complex.I Complex.I_ne_zero).restrictScalars
    ℝ).toContinuousLinearEquiv
  have hA : ∀ z, A z = Complex.I * z := fun z => by simp [A]
  have hmaps : MapsTo (fun z => A z + z₀) (ball 0 r) U := fun z hz => by
    refine interior_subset (hrU ?_)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right, hA, norm_mul, Complex.norm_I, one_mul]
    simpa using hz
  have h' : MemWkpLoc p (ball 0 r) 2 (fun z : ℂ => |z.re|) := by
    convert h.comp_continuousLinearEquiv_add A z₀ hmaps using 2 with z
    simp [hA, him]
  obtain ⟨-, D, hD, hD1⟩ := memWkpLoc_succ_iff.1 h'
  -- `|Re z|` is Lipschitz, so its weak derivative is the classical one, `± re`, off the
  -- imaginary axis.
  have hlip : LocallyLipschitz fun z : ℂ => |z.re| :=
    (lipschitzWith_one_norm.comp (RCLike.lipschitzWith_re (K := ℂ))).locallyLipschitz
  have hae := (ae_restrict_iff' (Opens.interior (ball (0 : ℂ) r)).isOpen.measurableSet).1
    (hD.ae_eq hlip.locallyLipschitzOn.hasWeakFDerivOn_fderiv)
  -- So `(D · 1 + 1) / 2` is the indicator of the right half-plane, which is not `W^{1,p}`.
  have hind : MemWkpLoc p (ball 0 r) 1 ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) := by
    refine (((hD1.clm_comp (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ))).add
      (memWkpLoc_const (1 : ℝ))).const_smul (1 / 2)).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_ball).2 ?_
    filter_upwards [hae, measure_eq_zero_iff_ae_notMem.1 (Complex.volume_setOf_re_eq 0)]
      with z hz hz0 hzb
    rw [Opens.coe_interior, isOpen_ball.interior_eq] at hz
    simp only [Pi.smul_apply, Pi.add_apply, ContinuousLinearMap.apply_apply, hz hzb, smul_eq_mul]
    have hre : HasFDerivAt Complex.re Complex.reCLM z := Complex.reCLM.hasFDerivAt
    rcases lt_or_gt_of_ne hz0 with h | h
    · rw [(hre.abs_of_neg h).fderiv,
        indicator_of_notMem (s := {z : ℂ | 0 < z.re}) (not_lt.2 h.le)]
      norm_num
    · rw [(hre.abs_of_pos h).fderiv,
        indicator_of_mem (s := {z : ℂ | 0 < z.re}) h]
      norm_num
  exact not_memWkpLoc_indicator_re_pos (k := 0) (z₀ := 0)
    (by rw [isOpen_ball.interior_eq]; exact mem_ball_self hr) rfl hind


/-- The order-one reflection across the real axis is the even reflection, and it does not extend
the normal coordinate `u = Im z` from the upper half-disc to a `W^{2,p}` map on the unit disc, for
any exponent: it gives `|Im z|`. -/
theorem not_memWkpLoc_two_planarReflection_higherReflectionCoeff_one_im :
    ¬ MemWkpLoc p (ball (0 : ℂ) 1) 2
      (planarReflection (higherReflectionCoeff 1) fun z => z.im) := by
  have h : planarReflection (higherReflectionCoeff 1) (fun z : ℂ => z.im) = fun z => |z.im| :=
    funext fun z => planarReflection_higherReflectionCoeff_one _ z
  rw [h]
  exact not_memWkpLoc_two_abs_im (by rw [isOpen_ball.interior_eq]; exact mem_ball_self one_pos) rfl

/-- The order-two reflection `u(s, -t) = -3 u(s, t) + 4 u(s, t / 2)` extends the normal coordinate
`u = Im z` to itself, which is in every local Sobolev class on every set. -/
theorem memWkpLoc_planarReflection_higherReflectionCoeff_two_im (U : Set ℂ) (k : ℕ) :
    MemWkpLoc p U k (planarReflection (higherReflectionCoeff 2) fun z => z.im) := by
  rw [planarReflection_higherReflectionCoeff_two_im]
  exact Complex.imCLM.contDiff.memWkpLoc

end TauCeti
