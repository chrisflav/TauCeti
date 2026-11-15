/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.Conformal.NormalFamilies
import TauCeti.Analysis.Complex.Pompeiu.Cutoff
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Geometry.Manifold.Connected
import TauCeti.MeasureTheory.Integral.Quadrature
import TauCeti.Topology.ConnectedComponents

/-!
# Finite-rank Runge approximation operators and scalar Runge equivalences

Let `K` be a compact subset of an open set `Ω ⊆ ℂ`. When `K` is filled in `Ω`
(`TauCeti.IsFilledIn K Ω`, meaning that no connected component of `Ω \ K` has compact closure
contained in `Ω`), every simple fraction `(z - ζ)⁻¹` with `ζ ∉ K` is uniformly approximable on `K`
by functions holomorphic on `Ω` (`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`).

This file combines that pole-pushing input with the cutoff Cauchy–Green representation
(`DifferentiableOn.eq_setIntegral_conjWirtingerDeriv_ofReal_smul_of_subset_interior`), Cauchy's
local Lipschitz bound (`TauCeti.dist_le_of_forall_mem_closedBall_two_mul_norm_le`), and positive
planar quadrature (`Bornology.IsBounded.exists_planeQuadrature_of_oscillation`) to construct
**uniform finite-rank linear Runge approximation operators**: given any collar `L ⊆ U` with
`K ⊆ interior L` and any `ε > 0`, there exist finitely many evaluation points
`ζ j ∈ interior L \ K`, scalar weights `w j : ℂ`, and ambient holomorphic functions `g j` on
`Ω`—chosen independently of `f`—such that

`∀ z ∈ K, ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B`

whenever `f` is holomorphic on `U` and bounded in norm by `B ≥ 0` on `L`. Because the nodes,
weights, and output functions are fixed ahead of `f`, this finite-rank formula commutes with smooth
or holomorphic dependence on external parameters.

Combining the operator with the maximum modulus principle on relatively compact components of
`Ω \ K` and finite-set stability of filledness (`TauCeti.IsFilledIn.union_finite_of_one_lt_rank`)
yields the full equivalence between topological filledness, uniform holomorphic approximation,
point-separation bounds, and—when `Ω = univ`—classical polynomial Runge approximation.

## Main results

* `TauCeti.IsFilledIn.exists_finite_rank_runge_operator_of_collar` and
  `TauCeti.IsFilledIn.exists_finite_rank_runge_operator`: uniform finite-rank linear Runge
  approximation with operator bound `ε * B` in terms of a sup bound `B` on a collar `L`.
* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`: scalar Runge approximation on `K` by
  functions holomorphic on `Ω`.
* `TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt`: `K` is filled in `Ω` if and
  only if every function holomorphic on an open neighborhood of `K` is uniformly approximable on `K`
  by functions holomorphic on `Ω`.
* `TauCeti.isFilledIn_iff_forall_sdiff_exists_differentiableOn_norm_le_lt`: point-separation
  characterization of `IsFilledIn K Ω`.
* `IsCompact.exists_polynomial_norm_sub_lt_of_filledHull_eq_self` and
  `TauCeti.filledHull_eq_self_iff_forall_exists_polynomial_norm_sub_lt`: classical polynomial
  Runge theorem on `ℂ`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1 and Lemma 11.3.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorems 13.5–13.9.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped NNReal ContDiff

namespace TauCeti

section FiniteRankOperator

/-- Uniform Lipschitz oscillation bound on the Cauchy–Green integrand
`ζ ↦ (z - ζ)⁻¹ * (φ ζ * f ζ)` across a collar `S` separated from `K` by radius `r > 0`, linear in
any sup bound `B` of `f` on the `2 r`-neighborhood of `S`. -/
private theorem norm_sub_inv_mul_oscillation_le {K S V : Set ℂ} {φ : ℂ → ℂ} {r M Lφ : ℝ}
    (hV : IsOpen V) (hr : 0 < r) (hball : ∀ ζ ∈ S, closedBall ζ (2 * r) ⊆ V)
    (hsep : ∀ ζ ∈ S, ∀ z ∈ K, r ≤ ‖z - ζ‖) (hM0 : 0 ≤ M) (hM : ∀ ζ ∈ S, ‖φ ζ‖ ≤ M)
    (hLφ0 : 0 ≤ Lφ) (hLφ : ∀ ζ₁ ∈ S, ∀ ζ₂ ∈ S, ‖φ ζ₁ - φ ζ₂‖ ≤ Lφ * dist ζ₁ ζ₂)
    {f : ℂ → ℂ} {B : ℝ} (hf : DifferentiableOn ℂ f V)
    (hBf : ∀ ζ ∈ S, ∀ w ∈ closedBall ζ (2 * r), ‖f w‖ ≤ B)
    {ζ₁ ζ₂ z : ℂ} (hζ₁ : ζ₁ ∈ S) (hζ₂ : ζ₂ ∈ S) (hz : z ∈ K) (hdist : dist ζ₁ ζ₂ < r) :
    ‖(z - ζ₁)⁻¹ * (φ ζ₁ * f ζ₁) - (z - ζ₂)⁻¹ * (φ ζ₂ * f ζ₂)‖ ≤
      ((2 * r⁻¹ ^ 2 * M + r⁻¹ * Lφ) * dist ζ₁ ζ₂) * B := by
  have h1_pos : 0 < ‖z - ζ₁‖ := hr.trans_le (hsep ζ₁ hζ₁ z hz)
  have h2_pos : 0 < ‖z - ζ₂‖ := hr.trans_le (hsep ζ₂ hζ₂ z hz)
  have hk2 : ‖(z - ζ₂)⁻¹‖ ≤ r⁻¹ := (norm_inv _).trans_le (inv_anti₀ hr (hsep ζ₂ hζ₂ z hz))
  have hk_diff : ‖(z - ζ₁)⁻¹ - (z - ζ₂)⁻¹‖ ≤ r⁻¹ ^ 2 * dist ζ₁ ζ₂ := by
    have ha : z - ζ₁ ≠ 0 := norm_ne_zero_iff.mp h1_pos.ne'
    have hb : z - ζ₂ ≠ 0 := norm_ne_zero_iff.mp h2_pos.ne'
    have hsub : (z - ζ₁)⁻¹ - (z - ζ₂)⁻¹ = (ζ₁ - ζ₂) * ((z - ζ₁)⁻¹ * (z - ζ₂)⁻¹) := by
      field_simp [ha, hb]; ring
    rw [hsub, norm_mul, norm_mul, norm_inv, norm_inv, ← dist_eq_norm, sq, mul_comm (r⁻¹ * r⁻¹)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (inv_anti₀ hr (hsep ζ₁ hζ₁ z hz)) (inv_anti₀ hr (hsep ζ₂ hζ₂ z hz))
        (inv_nonneg.mpr h2_pos.le) (inv_nonneg.mpr hr.le)) dist_nonneg
  have hf_lip : ‖f ζ₁ - f ζ₂‖ ≤ r⁻¹ * dist ζ₁ ζ₂ * B := by
    have hd := dist_le_of_forall_mem_closedBall_two_mul_norm_le hV hf hr (hball ζ₁ hζ₁)
      (hBf ζ₁ hζ₁) (mem_ball_self hr) (by rwa [mem_ball, dist_comm])
    exact (dist_eq_norm (f ζ₁) (f ζ₂) ▸ hd).trans_eq (by ring)
  have hf1 : ‖f ζ₁‖ ≤ B := hBf ζ₁ hζ₁ ζ₁ (mem_closedBall_self (by positivity))
  have htel : (z - ζ₁)⁻¹ * (φ ζ₁ * f ζ₁) - (z - ζ₂)⁻¹ * (φ ζ₂ * f ζ₂) =
      ((z - ζ₁)⁻¹ - (z - ζ₂)⁻¹) * φ ζ₁ * f ζ₁ + (z - ζ₂)⁻¹ * (φ ζ₁ - φ ζ₂) * f ζ₁ +
        (z - ζ₂)⁻¹ * φ ζ₂ * (f ζ₁ - f ζ₂) := by ring
  rw [htel]
  refine (norm_add₃_le.trans ?_).trans_eq (by ring :
    (r⁻¹ ^ 2 * dist ζ₁ ζ₂) * M * B + r⁻¹ * (Lφ * dist ζ₁ ζ₂) * B +
      r⁻¹ * M * (r⁻¹ * dist ζ₁ ζ₂ * B) = ((2 * r⁻¹ ^ 2 * M + r⁻¹ * Lφ) * dist ζ₁ ζ₂) * B)
  simp only [norm_mul]
  exact add_le_add
    (add_le_add
      (mul_le_mul (mul_le_mul hk_diff (hM ζ₁ hζ₁) (norm_nonneg _) (by positivity))
        hf1 (norm_nonneg _) (mul_nonneg (by positivity) hM0))
      (mul_le_mul (mul_le_mul hk2 (hLφ ζ₁ hζ₁ ζ₂ hζ₂) (norm_nonneg _) (by positivity))
        hf1 (norm_nonneg _) (mul_nonneg (by positivity) (mul_nonneg hLφ0 dist_nonneg))))
    (mul_le_mul (mul_le_mul hk2 (hM ζ₂ hζ₂) (norm_nonneg _) (by positivity))
      hf_lip (norm_nonneg _) (mul_nonneg (by positivity) hM0))

/-- Smooth cutoff derivative data on an open collar around a compact set `K`: produces `χ : ℂ → ℝ`
supported in `V` and equal to `1` near `K`, together with sup and Lipschitz bounds on
`ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1` and a uniform separation radius `r > 0`. -/
private theorem exists_cutoff_collar_bounds {K V : Set ℂ} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) :
    ∃ (χ : ℂ → ℝ) (r M Lφ : ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧ K ⊆ interior (χ ⁻¹' {1}) ∧
      0 < r ∧ 0 ≤ M ∧ 0 ≤ Lφ ∧
      (∀ ζ ∈ tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1),
        closedBall ζ (2 * r) ⊆ V) ∧
      (∀ ζ ∈ tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1),
        ∀ z ∈ K, r ≤ ‖z - ζ‖) ∧
      (∀ ζ, ‖conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1‖ ≤ M) ∧
      ∀ ζ₁ ζ₂, ‖conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ₁ 1 -
        conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ₂ 1‖ ≤ Lφ * dist ζ₁ ζ₂ := by
  obtain ⟨χ, hχ_cd, -, hχ_one, hχ_cs, hχ_supp⟩ := hK.exists_contDiff_cutoff hV hKV
  let α : ℂ → ℂ := fun w ↦ (χ w : ℂ)
  let φ : ℂ → ℂ := fun ζ ↦ conjWirtingerDeriv α ζ 1
  have hα_cd : ContDiff ℝ ∞ α := Complex.ofRealCLM.contDiff.comp hχ_cd
  have hφ_cd : ContDiff ℝ ∞ φ :=
    contDiff_iff_contDiffAt.mpr fun _ ↦ hα_cd.contDiffAt.conjWirtingerDeriv_apply (by simp) 1
  have hS_sub : tsupport φ ⊆ tsupport χ :=
    (tsupport_conjWirtingerDeriv_apply_subset α 1).trans <|
      closure_minimal ((Function.support_comp_subset ofReal_zero χ).trans (subset_tsupport χ))
        (isClosed_tsupport χ)
  have hφ_cs : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact hχ_cs.isCompact
      ((subset_tsupport φ).trans hS_sub)
  have hK' : K ⊆ interior (α ⁻¹' {1}) :=
    hχ_one.trans (interior_mono fun _ hw ↦
      mem_preimage.mpr (mem_singleton_iff.mpr (ofReal_eq_one.mpr (mem_singleton_iff.mp hw))))
  have hdisj : Disjoint (tsupport φ) K :=
    disjoint_tsupport_conjWirtingerDeriv_apply_of_subset_interior hK' 1
  obtain ⟨δ, hδ, hthick⟩ := hφ_cs.isCompact.exists_cthickening_subset_open
    (hV.sdiff hK.isClosed) (subset_sdiff.mpr ⟨hS_sub.trans hχ_supp, hdisj⟩)
  obtain ⟨M₀, hM₀⟩ := hφ_cd.continuous.bounded_above_of_compact_support hφ_cs
  obtain ⟨Kφ, hKφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ_cs hφ_cd (by simp)
  refine ⟨χ, δ / 2, max M₀ 0, Kφ, hχ_cd, hχ_cs, hχ_supp, hχ_one, half_pos hδ, le_max_right _ _,
    Kφ.coe_nonneg, fun ζ hζ ↦ ?_, fun ζ hζ z hz ↦ ?_, fun ζ ↦ (hM₀ ζ).trans (le_max_left _ _),
    fun ζ₁ ζ₂ ↦ by simpa only [dist_eq_norm] using hKφ.dist_le_mul ζ₁ ζ₂⟩
  · rw [mul_div_cancel₀ δ two_ne_zero]
    exact (closedBall_subset_cthickening hζ δ).trans (hthick.trans sdiff_subset)
  · by_contra! hlt
    have hz_ball : z ∈ closedBall ζ δ := by
      rw [mem_closedBall, dist_eq_norm]
      linarith
    exact (hthick (closedBall_subset_cthickening hζ δ hz_ball)).2 hz

/-- Error bound between `f z` and its discretized cutoff Cauchy–Green sum over quadrature nodes on
`tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1)` at mesh threshold `√2 * δ < r`. -/
private theorem norm_sub_rational_quadrature_le {K V : Set ℂ} {χ : ℂ → ℝ} {r M Lφ δ : ℝ}
    (hV : IsOpen V) (hχ_cd : ContDiff ℝ ∞ χ) (hχ_cs : HasCompactSupport χ)
    (hχ_supp : tsupport χ ⊆ V) (hχ_one : K ⊆ interior (χ ⁻¹' {1}))
    (hr : 0 < r) (hM0 : 0 ≤ M) (hLφ0 : 0 ≤ Lφ)
    (hball : ∀ ζ ∈ tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1),
      closedBall ζ (2 * r) ⊆ V)
    (hsep : ∀ ζ ∈ tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1),
      ∀ z ∈ K, r ≤ ‖z - ζ‖)
    (hM : ∀ ζ, ‖conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1‖ ≤ M)
    (hLφ : ∀ ζ₁ ζ₂, ‖conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ₁ 1 -
      conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ₂ 1‖ ≤ Lφ * dist ζ₁ ζ₂)
    (hsqrt_r : √2 * δ < r) {N : ℕ} {ζ : Fin N → ℂ} {c : Fin N → ℝ}
    (hS_cpt : IsCompact (tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1)))
    (hquad : ∀ (g : ℂ → ℂ) (ε₀ : ℝ),
      IntegrableOn g (tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1)) volume →
      (∀ ζ₁ ∈ tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1),
        ∀ ζ₂ ∈ tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1),
        dist ζ₁ ζ₂ ≤ √2 * δ → ‖g ζ₁ - g ζ₂‖ ≤ ε₀) →
      ‖(∑ j, c j • g (ζ j)) -
        ∫ w in tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1), g w‖ ≤
        volume.real (tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1)) * ε₀)
    {f : ℂ → ℂ} {B : ℝ} (hf : DifferentiableOn ℂ f V) (hB0 : 0 ≤ B)
    (hBf : ∀ ζ ∈ tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1),
      ∀ w ∈ closedBall ζ (2 * r), ‖f w‖ ≤ B)
    {z : ℂ} (hz : z ∈ K) :
    ‖f z - ∑ j, (Real.pi : ℂ)⁻¹ * (c j : ℂ) *
        conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) (ζ j) 1 * f (ζ j) * (z - ζ j)⁻¹‖ ≤
      Real.pi⁻¹ * volume.real (tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1)) *
        (2 * r⁻¹ ^ 2 * M + r⁻¹ * Lφ) * (√2 * δ) * B := by
  let φ : ℂ → ℂ := fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1
  let S : Set ℂ := tsupport φ
  have hS_sub : S ⊆ V := fun w hw ↦ hball w hw (mem_closedBall_self (by positivity))
  have hrep := hf.eq_setIntegral_conjWirtingerDeriv_ofReal_smul_of_subset_interior
    ((hχ_cd.of_le (by simp)).contDiffOn) hχ_cs (hV.interior_eq.symm ▸ hχ_supp) hχ_one hz
  let g : ℂ → ℂ := fun ζ ↦ (z - ζ)⁻¹ * (φ ζ * f ζ)
  have hg_int : IntegrableOn g S volume := by
    have hφ_cont : ContinuousOn φ S :=
      (((Complex.ofRealCLM.contDiff.comp hχ_cd).of_le
        (by simp)).continuous_conjWirtingerDeriv_apply 1).continuousOn
    have hk_cont : ContinuousOn (fun ζ ↦ (z - ζ)⁻¹) S :=
      (continuous_const.sub continuous_id).continuousOn.inv₀ fun w hw h0 ↦
        (hr.trans_le (hsep w hw z hz)).ne' (by simpa using congrArg norm h0)
    exact (hk_cont.mul (hφ_cont.mul (hf.continuousOn.mono hS_sub))).integrableOn_compact hS_cpt
  have hC₀ : 0 ≤ 2 * r⁻¹ ^ 2 * M + r⁻¹ * Lφ := by positivity
  have hq := hquad g (((2 * r⁻¹ ^ 2 * M + r⁻¹ * Lφ) * (√2 * δ)) * B) hg_int
    fun ζ₁ hζ₁ ζ₂ hζ₂ hdist ↦
      (norm_sub_inv_mul_oscillation_le hV hr hball hsep hM0 (fun w _ ↦ hM w) hLφ0
        (fun w₁ _ w₂ _ ↦ hLφ w₁ w₂) hf hBf hζ₁ hζ₂ hz (hdist.trans_lt hsqrt_r)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist hC₀) hB0)
  have hsum_eq : f z - ∑ j, (Real.pi : ℂ)⁻¹ * (c j : ℂ) * φ (ζ j) * f (ζ j) * (z - ζ j)⁻¹ =
      (Real.pi : ℂ)⁻¹ • ((∫ ζ in S, g ζ) - ∑ j, c j • g (ζ j)) := by
    rw [hrep, smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [g, Complex.real_smul, smul_eq_mul]
    ring
  rw [hsum_eq, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    norm_sub_rev]
  exact (mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr Real.pi_pos.le)).trans_eq (by ring)

/-- Rational-kernel finite-rank quadrature on a collar `K ⊆ interior L`: before pushing poles to
`Ωᶜ`, discretizing the cutoff Cauchy–Green integral yields nodes `ζ j ∈ interior L \ K` and weights
`w j : ℂ` approximating `f` within `ε * B` on `K` by simple fractions `(z - ζ j)⁻¹`. -/
private theorem exists_rational_runge_quadrature {K U L : Set ℂ} (hK : IsCompact K)
    (hKL : K ⊆ interior L) (hLU : L ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ w : Fin N → ℂ),
      (∀ j, ζ j ∈ interior L \ K) ∧
      ∀ (f : ℂ → ℂ) (B : ℝ), DifferentiableOn ℂ f U → 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
        ∀ z ∈ K, ‖f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹‖ ≤ ε * B := by
  obtain ⟨L', hL', hKL', hL'L⟩ := exists_compact_between hK isOpen_interior hKL
  obtain ⟨χ, r, M, Lφ, hχ_cd, hχ_cs, hχ_supp, hχ_one, hr, hM0, hLφ0, hball, hsep, hM, hLφ⟩ :=
    exists_cutoff_collar_bounds hK isOpen_interior hKL'
  let φ : ℂ → ℂ := fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1
  let S : Set ℂ := tsupport φ
  have hS_sub : S ⊆ interior L' := fun ζ hζ ↦ hball ζ hζ (mem_closedBall_self (by positivity))
  have hS_cpt : IsCompact S :=
    hL'.of_isClosed_subset (isClosed_tsupport φ) (hS_sub.trans interior_subset)
  let C₀ : ℝ := 2 * r⁻¹ ^ 2 * M + r⁻¹ * Lφ
  let D : ℝ := Real.pi⁻¹ * volume.real S * C₀ + 1
  have hD : 0 < D := add_pos_of_nonneg_of_pos (by positivity) one_pos
  let δ : ℝ := min (r / 2) (ε / (2 * D))
  have hδ : 0 < δ := lt_min (half_pos hr) (div_pos hε (mul_pos zero_lt_two hD))
  have h2 : √2 < 2 := (Real.sqrt_lt' zero_lt_two).mpr (by norm_num)
  have hsqrt_r : √2 * δ < r :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.sqrt_nonneg 2)).trans_lt
      ((mul_lt_mul_of_pos_right h2 (half_pos hr)).trans_eq (mul_div_cancel₀ r two_ne_zero))
  obtain ⟨N, ζ, c, hζS, -, -, hquad⟩ :=
    hS_cpt.isBounded.exists_planeQuadrature_of_oscillation ℂ hδ
  refine ⟨N, ζ, fun j ↦ (Real.pi : ℂ)⁻¹ * (c j : ℂ) * φ (ζ j), fun j ↦ ?_,
    fun f B hf hB0 hBf z hz ↦ ?_⟩
  · refine ⟨hL'L (interior_subset (hS_sub (hζS j))), fun hK' ↦ ?_⟩
    have := hsep (ζ j) (hζS j) (ζ j) hK'
    simp only [sub_self, norm_zero] at this
    linarith
  · have hle := norm_sub_rational_quadrature_le isOpen_interior hχ_cd hχ_cs hχ_supp hχ_one hr
      hM0 hLφ0 hball hsep hM hLφ hsqrt_r hS_cpt hquad
      (hf.mono (interior_subset.trans (hL'L.trans (interior_subset.trans hLU)))) hB0
      (fun w hw u hu ↦ hBf u (interior_subset (hL'L (interior_subset (hball w hw hu))))) hz
    calc ‖f z - ∑ j, (Real.pi : ℂ)⁻¹ * (c j : ℂ) * φ (ζ j) * f (ζ j) * (z - ζ j)⁻¹‖
        ≤ (Real.pi⁻¹ * volume.real S * C₀) * (√2 * δ) * B := hle
      _ ≤ D * (2 * (ε / (2 * D))) * B := by
          have hδ_le : √2 * δ ≤ 2 * (ε / (2 * D)) :=
            (mul_le_mul_of_nonneg_right h2.le hδ.le).trans
              (mul_le_mul_of_nonneg_left (min_le_right _ _) zero_le_two)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (le_add_of_nonneg_right zero_le_one) hδ_le (by positivity) hD.le) hB0
      _ = ε * B := by field_simp [hD.ne']

variable {K Ω : Set ℂ}

/-- **Finite-rank Runge approximation operator on a fixed collar.** If `K` is compact and filled in
an open set `Ω ⊆ ℂ` with `K ⊆ Ω`, then for any collar `L ⊆ U` satisfying `K ⊆ interior L` and any
`ε > 0`, there exist finitely many evaluation points `ζ j ∈ interior L \ K`, weights `w j : ℂ`, and
functions `g j` holomorphic on `Ω`—independent of `f`—such that every `f` holomorphic on `U` with
`‖f‖ ≤ B` (`0 ≤ B`) on `L` is approximated on `K` within `ε * B` by `∑ j, w j * f (ζ j) * g j`. -/
theorem IsFilledIn.exists_finite_rank_runge_operator_of_collar (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {U L : Set ℂ} (hKL : K ⊆ interior L)
    (hLU : L ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ w : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ j, ζ j ∈ interior L \ K) ∧ (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
      ∀ (f : ℂ → ℂ) (B : ℝ), DifferentiableOn ℂ f U → 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
        ∀ z ∈ K, ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B := by
  obtain ⟨N, ζ, w, hζ, hrat⟩ := exists_rational_runge_quadrature hK hKL hLU (half_pos hε)
  let W : ℝ := ∑ j, ‖w j‖
  have hW_pos : 0 < W + 1 := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    one_pos
  let η : ℝ := (ε / 2) / (W + 1)
  have hη : 0 < η := div_pos (half_pos hε) hW_pos
  choose g hg_diff hg_approx using fun j : Fin N ↦
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ j).2 hη
  refine ⟨N, ζ, w, g, hζ, hg_diff, fun f B hf hB0 hBf z hz ↦ ?_⟩
  have hsum : ∑ j, w j * f (ζ j) * g j z + ∑ j, w j * f (ζ j) * ((z - ζ j)⁻¹ - g j z) =
      ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hsplit : f z - ∑ j, w j * f (ζ j) * g j z =
      (f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹) +
        ∑ j, w j * f (ζ j) * ((z - ζ j)⁻¹ - g j z) := by rw [← hsum]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have htail : ‖∑ j, w j * f (ζ j) * ((z - ζ j)⁻¹ - g j z)‖ ≤ (ε / 2) * B := by
    calc ‖∑ j, w j * f (ζ j) * ((z - ζ j)⁻¹ - g j z)‖
        ≤ ∑ j, ‖w j * f (ζ j) * ((z - ζ j)⁻¹ - g j z)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖w j‖ * B * η := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left
            (hBf (ζ j) (interior_subset (hζ j).1)) (norm_nonneg _))
            (hg_approx j z hz).le (norm_nonneg _) (mul_nonneg (norm_nonneg _) hB0)
      _ = (W * η) * B := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
      _ ≤ (ε / 2) * B := by
          refine mul_le_mul_of_nonneg_right ?_ hB0
          calc W * ((ε / 2) / (W + 1))
              ≤ (W + 1) * ((ε / 2) / (W + 1)) := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right
                zero_le_one) hη.le
            _ = ε / 2 := mul_div_cancel₀ (ε / 2) hW_pos.ne'
  linarith [hrat f B hf hB0 hBf z hz]

/-- **Finite-rank Runge approximation operator.** For a compact set `K` filled in an open set
`Ω ⊆ ℂ` with `K ⊆ Ω` and any open neighborhood `U ⊇ K`, there exists a compact collar
`L ⊆ U ∩ Ω` with `K ⊆ interior L` such that for every `ε > 0`, a single finite-rank evaluation
formula approximates all `U`-holomorphic functions on `K` with operator norm at most `ε` relative
to `sup_L ‖f‖`. -/
theorem IsFilledIn.exists_finite_rank_runge_operator (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∩ Ω ∧
      ∀ ε > 0, ∃ (N : ℕ) (ζ w : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
        (∀ j, ζ j ∈ interior L \ K) ∧ (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
        ∀ (f : ℂ → ℂ) (B : ℝ), DifferentiableOn ℂ f U → 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
          ∀ z ∈ K, ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B := by
  obtain ⟨L, hL, hKL, hLUΩ⟩ := exists_compact_between hK (hU.inter hΩ) (subset_inter hKU hKΩ)
  exact ⟨L, hL, hKL, hLUΩ, fun _ hε ↦
    hfill.exists_finite_rank_runge_operator_of_collar hΩ hK hKΩ hKL
      (hLUΩ.trans inter_subset_left) hε⟩

end FiniteRankOperator

section ScalarRunge

variable {K Ω : Set ℂ}

/-- **Runge's approximation theorem.** If a compact set `K ⊆ Ω` is filled in an open set `Ω ⊆ ℂ`,
then every function `f` holomorphic on an open neighborhood `U ⊇ K` is uniformly approximable on
`K` by functions holomorphic on all of `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨L, hL, -, hLUΩ, hop⟩ := hfill.exists_finite_rank_runge_operator hΩ hK hKΩ hU hKU
  have hf_cont : ContinuousOn (fun z ↦ ‖f z‖) L :=
    (hf.continuousOn.mono (hLUΩ.trans inter_subset_left)).norm
  obtain ⟨M, hM⟩ := hL.bddAbove_image hf_cont
  let B : ℝ := max M 0 + 1
  have hB_pos : 0 < B := add_pos_of_nonneg_of_pos (le_max_right M 0) one_pos
  have hBf (z : ℂ) (hz : z ∈ L) : ‖f z‖ ≤ B :=
    ((hM (mem_image_of_mem _ hz)).trans (le_max_left M 0)).trans
      (le_add_of_nonneg_right zero_le_one)
  obtain ⟨N, ζ, w, g, -, hg, hbound⟩ :=
    hop (ε / (2 * B)) (div_pos hε (mul_pos zero_lt_two hB_pos))
  refine ⟨fun z ↦ ∑ j, w j * f (ζ j) * g j z,
    DifferentiableOn.fun_sum fun j _ ↦ (hg j).const_mul (w j * f (ζ j)), fun z hz ↦ ?_⟩
  calc ‖f z - ∑ j, w j * f (ζ j) * g j z‖
      ≤ (ε / (2 * B)) * B := hbound f B hf hB_pos.le hBf z hz
    _ = ε / 2 := by field_simp [hB_pos.ne']
    _ < ε := half_lt_self hε

/-- **Universal Runge characterization of filledness.** For a compact subset `K` of an open set
`Ω ⊆ ℂ`, `K` is filled in `Ω` if and only if every function holomorphic on an open neighborhood of
`K` can be approximated uniformly on `K` by functions holomorphic on `Ω`. -/
theorem isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
        ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
          ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  refine ⟨fun hfill _ hU hKU _ hf _ hε ↦
    hfill.exists_differentiableOn_norm_sub_lt hΩ hK hKΩ hU hKU hf hε,
    fun happrox ↦ isFilledIn_iff.mpr fun a ha ⟨hcpt, hsub⟩ ↦ ?_⟩
  set C := connectedComponentIn (Ω \ K) a
  let M : ℝ := Metric.diam (closure C) + 1
  have hM : 0 < M := add_pos_of_nonneg_of_pos Metric.diam_nonneg one_pos
  have hf : DifferentiableOn ℂ (fun z ↦ (z - a)⁻¹) {a}ᶜ :=
    (differentiableOn_id.sub (differentiableOn_const a)).inv fun _ hz ↦
      sub_ne_zero.mpr (mem_compl_singleton_iff.mp hz)
  obtain ⟨g, hg, hgK⟩ := happrox {a}ᶜ isOpen_compl_singleton
    (fun z hz hza ↦ ha.2 (mem_singleton_iff.mp hza ▸ hz)) _ hf
    (1 / (2 * M)) (div_pos one_pos (mul_pos zero_lt_two hM))
  let φ : ℂ → ℂ := fun z ↦ 1 - (z - a) * g z
  have hφ : DifferentiableOn ℂ φ Ω :=
    (differentiableOn_const 1).sub ((differentiableOn_id.sub (differentiableOn_const a)).mul hg)
  have hφ_dc : DiffContOnCl ℂ φ C :=
    ⟨hφ.mono (subset_closure.trans hsub), hφ.continuousOn.mono hsub⟩
  have ha_cl : a ∈ closure C := subset_closure (mem_connectedComponentIn ha)
  have hfront (z : ℂ) (hz : z ∈ frontier C) : ‖φ z‖ ≤ 1 / 2 := by
    have hz_compl := frontier_connectedComponentIn_subset_compl (hΩ.sdiff hK.isClosed) a hz
    have hzK : z ∈ K := by_contra fun hnotK ↦ hz_compl ⟨hsub hz.1, hnotK⟩
    have hza : z - a ≠ 0 := sub_ne_zero.mpr fun h ↦ ha.2 (h ▸ hzK)
    have hφ_eq : φ z = (z - a) * ((z - a)⁻¹ - g z) := by simp only [φ]; field_simp [hza]
    have hdist : ‖z - a‖ ≤ M := dist_eq_norm z a ▸
      (Metric.dist_le_diam_of_mem hcpt.isBounded hz.1 ha_cl).trans
        (le_add_of_nonneg_right zero_le_one)
    rw [hφ_eq, norm_mul]
    exact (mul_le_mul hdist (hgK z hzK).le (norm_nonneg _) hM.le).trans_eq (by field_simp [hM.ne'])
  have hle := Complex.norm_le_of_forall_mem_frontier_norm_le
    (hcpt.isBounded.subset subset_closure) hφ_dc hfront ha_cl
  have hφa : ‖φ a‖ = 1 := by simp [φ]
  linarith

end ScalarRunge

section PointSeparation

/-- **Point-separation characterization of filledness.** For a compact subset `K` of an open set
`Ω ⊆ ℂ`, `K` is filled in `Ω` if and only if every point `a ∈ Ω \ K` can be separated from `K` by a
function `g` holomorphic on `Ω` with `sup_K ‖g‖ < ‖g a‖`. -/
theorem isFilledIn_iff_forall_sdiff_exists_differentiableOn_norm_le_lt {K Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔
      ∀ a ∈ Ω \ K, ∃ (g : ℂ → ℂ) (B : ℝ),
        DifferentiableOn ℂ g Ω ∧ (∀ z ∈ K, ‖g z‖ ≤ B) ∧ B < ‖g a‖ := by
  refine ⟨fun hfill a ha ↦ ?_, fun hsep ↦ isFilledIn_iff.mpr fun a ha ⟨hcpt, hsub⟩ ↦ ?_⟩
  · have hfill' : IsFilledIn (K ∪ {a}) Ω :=
      hfill.union_finite_of_one_lt_rank (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num)
        (hΩ.sdiff hK.isClosed) (finite_singleton a)
    obtain ⟨U₀, U₁, hU₀, hU₁, hKU₀, haU₁, hdisj⟩ :=
      SeparatedNhds.of_isCompact_isCompact hK isCompact_singleton
        (disjoint_singleton_right.mpr ha.2)
    let f : ℂ → ℂ := U₁.indicator 1
    have hf : DifferentiableOn ℂ f (U₀ ∪ U₁) := fun z hz ↦ by
      rcases hz with hz₀ | hz₁
      · have heq : f =ᶠ[𝓝 z] 0 := eventuallyEq_iff_exists_mem.mpr ⟨U₀, hU₀.mem_nhds hz₀,
          fun w hw ↦ indicator_of_notMem (disjoint_left.mp hdisj hw) 1⟩
        exact (heq.differentiableAt_iff.mpr (differentiableAt_const 0)).differentiableWithinAt
      · have heq : f =ᶠ[𝓝 z] 1 := eventuallyEq_iff_exists_mem.mpr ⟨U₁, hU₁.mem_nhds hz₁,
          fun w hw ↦ indicator_of_mem hw 1⟩
        exact (heq.differentiableAt_iff.mpr (differentiableAt_const 1)).differentiableWithinAt
    obtain ⟨g, hg, happrox⟩ := hfill'.exists_differentiableOn_norm_sub_lt hΩ
      (hK.union isCompact_singleton) (union_subset hKΩ (singleton_subset_iff.mpr ha.1))
      (hU₀.union hU₁) (union_subset_union hKU₀ haU₁) hf (ε := 1 / 3) (by norm_num)
    refine ⟨g, 1 / 3, hg, fun z hz ↦ ?_, ?_⟩
    · have h := happrox z (Or.inl hz)
      rw [show f z = 0 from indicator_of_notMem (disjoint_left.mp hdisj (hKU₀ hz)) 1,
        zero_sub, norm_neg] at h
      exact h.le
    · have h := happrox a (Or.inr (mem_singleton a))
      rw [show f a = 1 from indicator_of_mem (haU₁ (mem_singleton a)) 1] at h
      have h1 : (1 : ℝ) - ‖g a‖ ≤ ‖(1 : ℂ) - g a‖ := by simpa using norm_sub_norm_le (1 : ℂ) (g a)
      linarith
  · obtain ⟨g, B, hg, hgK, hBa⟩ := hsep a ha
    set C := connectedComponentIn (Ω \ K) a
    have hg_dc : DiffContOnCl ℂ g C :=
      ⟨hg.mono (subset_closure.trans hsub), hg.continuousOn.mono hsub⟩
    have hfront (z : ℂ) (hz : z ∈ frontier C) : ‖g z‖ ≤ B :=
      hgK z (by_contra fun hnotK ↦
        frontier_connectedComponentIn_subset_compl (hΩ.sdiff hK.isClosed) a hz ⟨hsub hz.1, hnotK⟩)
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le
      (hcpt.isBounded.subset subset_closure) hg_dc hfront
      (subset_closure (mem_connectedComponentIn ha))
    linarith

end PointSeparation

section PolynomialRunge

/-- **Polynomial Runge approximation.** If a compact set `K ⊆ ℂ` has no bounded complementary
components (`filledHull K = K`), then every function holomorphic on an open neighborhood of `K` is
uniformly approximable on `K` by complex polynomials. -/
theorem _root_.IsCompact.exists_polynomial_norm_sub_lt_of_filledHull_eq_self {K U : Set ℂ}
    (hK : IsCompact K) (hfill : filledHull K = K) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  have hfill_univ : IsFilledIn K univ := (isFilledIn_univ_iff hK.isClosed).mpr hfill
  obtain ⟨g, hg_on, hg_approx⟩ := hfill_univ.exists_differentiableOn_norm_sub_lt isOpen_univ hK
    (subset_univ K) hU hKU hf (half_pos hε)
  have hg : Differentiable ℂ g := differentiableOn_univ.mp hg_on
  obtain ⟨r, hrK⟩ := hK.isBounded.subset_ball (0 : ℂ)
  let R : ℝ≥0 := max r.toNNReal 1
  have hKR : K ⊆ ball 0 R := hrK.trans <| ball_subset_ball <|
    (Real.le_coe_toNNReal r).trans (NNReal.coe_le_coe.mpr (le_max_left _ _))
  have hps := hg.hasFPowerSeriesOnBall 0 one_pos
  have hu := hps.tendstoUniformlyOn' (r' := R) ENNReal.coe_lt_top
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (half_pos hε)).exists
  let ps := cauchyPowerSeries g 0 (1 : ℝ≥0)
  let p : Polynomial ℂ := ∑ k ∈ Finset.range N, Polynomial.C (ps.coeff k) * Polynomial.X ^ k
  have hp_eval (z : ℂ) : p.eval z = ps.partialSum N (z - 0) := by
    rw [← Polynomial.coe_evalRingHom, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, sub_zero,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  refine ⟨p, fun z hz ↦ ?_⟩
  rw [hp_eval]
  have hz_ps : ‖g z - ps.partialSum N (z - 0)‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hN z (hKR hz)
  calc ‖f z - ps.partialSum N (z - 0)‖
      = ‖(f z - g z) + (g z - ps.partialSum N (z - 0))‖ := by abel_nf
    _ ≤ ‖f z - g z‖ + ‖g z - ps.partialSum N (z - 0)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hg_approx z hz) hz_ps
    _ = ε := add_halves ε

/-- **Classical polynomial Runge characterization.** A compact set `K ⊆ ℂ` equals its filled hull
(its complement is connected) if and only if every function holomorphic on an open neighborhood of
`K` is uniformly approximable on `K` by complex polynomials. -/
theorem filledHull_eq_self_iff_forall_exists_polynomial_norm_sub_lt {K : Set ℂ}
    (hK : IsCompact K) :
    filledHull K = K ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
        ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
          ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  refine ⟨fun hfill _ hU hKU _ hf _ hε ↦
    hK.exists_polynomial_norm_sub_lt_of_filledHull_eq_self hfill hU hKU hf hε, fun hpoly ↦ ?_⟩
  rw [← isFilledIn_univ_iff hK.isClosed,
    isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt isOpen_univ hK (subset_univ K)]
  intro U hU hKU f hf ε hε
  obtain ⟨p, hp⟩ := hpoly U hU hKU f hf ε hε
  exact ⟨fun z ↦ p.eval z, p.differentiableOn, hp⟩

end PolynomialRunge

end TauCeti
