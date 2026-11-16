/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.Asymptotics.LaplaceMethod.Basic
public import TauCeti.Analysis.Asymptotics.LaplaceMethod.LocalInverse

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Laplace's method on the real line

This file proves Laplace's method for real-variable integrals on `(a, ∞)` and `(a, b)`
(DLMF §2.3(iii), formulas 2.3.13–2.3.15; Olver 1997, Chapter 3, §7), together with worked
specializations to `p(t) = t²`, `q = 1` and `p(t) = t`, `μ = 1`.

## Main results

* `Asymptotics.isBigO_laplace_method_sub_sum`: Laplace's method on `(a, ∞)` (DLMF 2.3.13–2.3.15).
* `Asymptotics.isBigO_laplace_method_Ioo_sub_sum`: Laplace's method on a finite interval `(a, b)`.
* `Asymptotics.isBigO_integral_exp_neg_mul_sq_sub`: specialization to `p(t) = t²`, `q = 1`.
* `Asymptotics.isBigO_laplace_method_id_sub_sum`: specialization to `p(t) = t`, `μ = 1` (Watson's
  lemma for exponents `s + λ`).

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.3(iii),
  <https://dlmf.nist.gov/2.3.iii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 3, §7.
-/

public section

noncomputable section

open Complex Filter Topology Set MeasureTheory Finset PowerSeries
open scoped Real Nat

namespace Asymptotics

/-! ### Local Watson's lemma and integral helpers -/

private theorem norm_cexp_neg_mul (x v : ℝ) :
    ‖cexp (-((x : ℂ) * (v : ℂ)))‖ = Real.exp (-(x * v)) := by
  rw [Complex.norm_exp]; simp [mul_re]

private theorem norm_setIntegral_le_mul_of_le {s t : Set ℝ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : s ⊆ t) {f : ℝ → ℂ} {g : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : IntegrableOn f s) (hg : IntegrableOn g t) (hg0 : ∀ v ∈ t, 0 ≤ g v)
    (hfg : ∀ v ∈ s, ‖f v‖ ≤ c * g v) :
    ‖∫ v in s, f v‖ ≤ c * ∫ v in t, g v := by
  have hle := (norm_integral_le_integral_norm _).trans <|
    (setIntegral_mono_on hf.norm ((hg.mono_set hst).const_mul c) hs hfg).trans <|
    setIntegral_mono_set (hg.const_mul c)
      ((ae_restrict_iff' ht).mpr (Eventually.of_forall fun v hv ↦ mul_nonneg hc (hg0 v hv)))
      (Eventually.of_forall fun _ h ↦ hst h)
  rwa [integral_const_mul] at hle

private theorem integrableOn_cexp_neg_mul_cpow_Ioi {α : ℂ} (hα : 0 < α.re) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun v : ℝ ↦ cexp (-(x * v)) * (v : ℂ) ^ (α - 1)) (Ioi 0) := by
  have hsc := (integrableOn_Ioi_comp_mul_left_iff
    (fun v : ℝ ↦ (Real.exp (-v) : ℂ) * (v : ℂ) ^ (α - 1)) 0 hx).mpr
    (by simpa using Complex.GammaIntegral_convergent hα)
  refine IntegrableOn.congr_fun (hsc.const_mul (((x : ℂ) ^ (α - 1))⁻¹))
    (fun v hv ↦ ?_) measurableSet_Ioi
  have hne : (x : ℂ) ^ (α - 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  rw [ofReal_mul, mul_cpow_ofReal_nonneg hx.le hv.le, ofReal_exp, ofReal_neg, ofReal_mul]
  field_simp [hne]

private theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    IntegrableOn (fun v : ℝ ↦ v ^ (s - 1) * Real.exp (-(x * v))) (Ioi 0) := by
  have hsc := (integrableOn_Ioi_comp_mul_left_iff
    (fun v : ℝ ↦ Real.exp (-v) * v ^ (s - 1)) 0 hx).mpr
    (by simpa using Real.GammaIntegral_convergent hs)
  refine IntegrableOn.congr_fun (hsc.const_mul ((x ^ (s - 1))⁻¹))
    (fun v hv ↦ ?_) measurableSet_Ioi
  rw [Real.mul_rpow hx.le hv.le]
  field_simp [(Real.rpow_pos_of_pos hx (s - 1)).ne']

private theorem isBigO_exp_neg_mul_cpow {η : ℝ} (hη : 0 < η) (α : ℂ) :
    (fun x : ℝ ↦ Real.exp (-η * x)) =O[atTop] fun x : ℝ ↦ (x : ℂ) ^ (-α) := by
  refine isBigO_norm_right.mp <|
    (isLittleO_exp_neg_mul_rpow_atTop hη (-α.re)).isBigO.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]

/-- Local Watson's lemma on `(0, δ)`: if `g` is integrable on `(0, δ)` and admits a power-series
expansion `g(v) ~ ∑ bₛ v^{(s + λ - μ)/μ}` as `v → 0+` (`μ > 0`, `Re λ > 0`), then its finite
Laplace transform has the asymptotic expansion `∑ Γ((s + λ)/μ) bₛ x^{-(s + λ)/μ}` as `x → +∞`. -/
private theorem isBigO_laplace_Ioo_sub_sum {δ μ : ℝ} (hδ : 0 < δ) (hμ : 0 < μ) {lam : ℂ}
    (hlam : 0 < lam.re) {g : ℝ → ℂ} {b : ℕ → ℂ}
    (hg_int : IntegrableOn g (Ioo 0 δ))
    (hg_exp : ∀ N : ℕ,
      (fun v : ℝ ↦ g v - ∑ s ∈ range N, b s * (v : ℂ) ^ (((s : ℂ) + lam - μ) / μ)) =O[𝓝[>] 0]
        fun v ↦ v ^ (((N : ℝ) + lam.re - μ) / μ))
    (N : ℕ) :
    (fun x : ℝ ↦ (∫ v in Ioo 0 δ, cexp (-(x * v)) * g v) -
      ∑ s ∈ range N,
        (x : ℂ) ^ (-(((s : ℂ) + lam) / μ)) * (Complex.Gamma (((s : ℂ) + lam) / μ) * b s))
      =O[atTop] fun x ↦ (x : ℂ) ^ (-(((N : ℂ) + lam) / μ)) := by
  set α : ℕ → ℂ := fun s ↦ ((s : ℂ) + lam) / μ
  have hμc : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  have hα_pos : ∀ s : ℕ, 0 < (α s).re := fun s ↦ by
    simp only [α, div_ofReal_re, add_re, natCast_re]
    exact div_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg s) hlam) hμ
  have hα_sub : ∀ s : ℕ, α s - 1 = ((s : ℂ) + lam - μ) / μ := fun s ↦ by
    simp only [α]; field_simp [hμc]
  have hα_sub_re : ∀ s : ℕ, (α s).re - 1 = ((s : ℝ) + lam.re - μ) / μ := fun s ↦ by
    simp only [α, div_ofReal_re, add_re, natCast_re]; field_simp [hμ.ne']
  obtain ⟨C, hC⟩ := isBigO_iff.mp (hg_exp N)
  obtain ⟨r, hr, hr_bound⟩ := Metric.mem_nhdsWithin_iff.mp hC
  set C₀ : ℝ := max C 0
  set δ₁ : ℝ := min (r / 2) (δ / 2)
  have hδ₁_pos : 0 < δ₁ := lt_min (half_pos hr) (half_pos hδ)
  have hδ₁_lt_r : δ₁ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hδ₁_lt_δ : δ₁ < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  set rem : ℝ → ℂ := fun v ↦ g v - ∑ s ∈ range N, b s * (v : ℂ) ^ (α s - 1)
  have hrem_bound : ∀ v ∈ Ioo 0 δ₁, ‖rem v‖ ≤ C₀ * v ^ ((α N).re - 1) := fun v ⟨hv0, hv1⟩ ↦ by
    have hb := hr_bound ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hv0]; linarith,
      hv0⟩
    rw [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hv0 _)] at hb
    simp only [rem, hα_sub, hα_sub_re]
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_pos_of_pos hv0 _).le)
  have hInt_g_Ioo : ∀ {x : ℝ}, 0 < x →
      IntegrableOn (fun v : ℝ ↦ cexp (-(x * v)) * g v) (Ioo 0 δ) := fun {x} hx ↦
    hg_int.norm.mono'
      ((Complex.continuous_exp.comp
        ((continuous_const.mul continuous_ofReal).neg)).aestronglyMeasurable.mul
        hg_int.aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun v hv ↦ by
        rw [norm_mul, norm_cexp_neg_mul]
        nlinarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_pos hx hv.1).le),
          norm_nonneg (g v)]))
  have hInt_term : ∀ {x : ℝ}, 0 < x → ∀ s : ℕ,
      IntegrableOn (fun v : ℝ ↦ cexp (-(x * v)) * (b s * (v : ℂ) ^ (α s - 1))) (Ioi 0) :=
    fun hx s ↦ IntegrableOn.congr_fun
      ((integrableOn_cexp_neg_mul_cpow_Ioi (hα_pos s) hx).const_mul (b s))
      (fun _ _ ↦ by ring) measurableSet_Ioi
  have hInt_sum_Ioo1 : ∀ {x : ℝ}, 0 < x →
      IntegrableOn
        (fun v : ℝ ↦ cexp (-(x * v)) * ∑ s ∈ range N, b s * (v : ℂ) ^ (α s - 1)) (Ioo 0 δ₁) :=
    fun hx ↦ IntegrableOn.congr_fun
      (integrable_finsetSum (range N) fun s _ ↦ (hInt_term hx s).mono_set Ioo_subset_Ioi_self)
      (fun _ _ ↦ by rw [Finset.mul_sum]) measurableSet_Ioo
  have hInt_rem_Ioo1 : ∀ {x : ℝ}, 0 < x →
      IntegrableOn (fun v : ℝ ↦ cexp (-(x * v)) * rem v) (Ioo 0 δ₁) := fun hx ↦
    IntegrableOn.congr_fun
      (((hInt_g_Ioo hx).mono_set (Ioo_subset_Ioo_right hδ₁_lt_δ.le)).sub (hInt_sum_Ioo1 hx))
      (fun _ _ ↦ by dsimp only [rem, Pi.sub_apply]; rw [mul_sub]) measurableSet_Ioo
  have hdecomp : ∀ {x : ℝ}, 0 < x →
      (∫ v in Ioo 0 δ, cexp (-(x * v)) * g v) -
        ∑ s ∈ range N, (x : ℂ) ^ (-α s) * (Complex.Gamma (α s) * b s) =
      (∫ v in Ioo 0 δ₁, cexp (-(x * v)) * rem v) +
      (∫ v in Ico δ₁ δ, cexp (-(x * v)) * g v) -
      ∑ s ∈ range N, b s * (∫ v in Ici δ₁, cexp (-(x * v)) * (v : ℂ) ^ (α s - 1)) := fun {x} hx ↦ by
    have hsplit1 : ∫ v in Ioo 0 δ, cexp (-(x * v)) * g v =
        (∫ v in Ioo 0 δ₁, cexp (-(x * v)) * g v) + (∫ v in Ico δ₁ δ, cexp (-(x * v)) * g v) := by
      rw [← Ioo_union_Ico_eq_Ioo hδ₁_pos hδ₁_lt_δ.le]
      exact setIntegral_union (Set.disjoint_left.mpr fun _ h1 h2 ↦ h1.2.not_ge h2.1)
        measurableSet_Ico ((hInt_g_Ioo hx).mono_set (Ioo_subset_Ioo_right hδ₁_lt_δ.le))
        ((hInt_g_Ioo hx).mono_set (Set.Ico_subset_Ioo_left hδ₁_pos))
    have hsplit2 : ∫ v in Ioo 0 δ₁, cexp (-(x * v)) * g v =
        (∫ v in Ioo 0 δ₁, cexp (-(x * v)) * rem v) +
        ∑ s ∈ range N, b s * (∫ v in Ioo 0 δ₁, cexp (-(x * v)) * (v : ℂ) ^ (α s - 1)) := by
      rw [setIntegral_congr_fun measurableSet_Ioo (fun _ _ ↦ by dsimp only [rem]; ring :
            ∀ v ∈ Ioo 0 δ₁, cexp (-(x * v)) * g v = cexp (-(x * v)) * rem v +
              cexp (-(x * v)) * ∑ s ∈ range N, b s * (v : ℂ) ^ (α s - 1)),
        integral_add (hInt_rem_Ioo1 hx) (hInt_sum_Ioo1 hx)]
      congr 1
      rw [setIntegral_congr_fun measurableSet_Ioo fun _ _ ↦ Finset.mul_sum _ _ _,
        integral_finsetSum (range N) fun s _ ↦ (hInt_term hx s).mono_set Ioo_subset_Ioi_self]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioo fun _ _ ↦ by ring
    have hsplit3 : ∀ s : ℕ,
        ∫ v in Ioo 0 δ₁, cexp (-(x * v)) * (v : ℂ) ^ (α s - 1) =
        (x : ℂ) ^ (-α s) * Complex.Gamma (α s) -
          ∫ v in Ici δ₁, cexp (-(x * v)) * (v : ℂ) ^ (α s - 1) := fun s ↦ by
      have hfull : ∫ v in Ioi (0 : ℝ), cexp (-(x * v)) * (v : ℂ) ^ (α s - 1) =
          (x : ℂ) ^ (-α s) * Complex.Gamma (α s) := by
        rw [setIntegral_congr_fun measurableSet_Ioi fun _ _ ↦ mul_comm _ _,
          Complex.integral_cpow_mul_exp_neg_mul_Ioi (hα_pos s) hx, one_div,
          inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm), ← cpow_neg]
      have hunion : ∫ v in Ioi (0 : ℝ), cexp (-(x * v)) * (v : ℂ) ^ (α s - 1) =
          (∫ v in Ioo 0 δ₁, cexp (-(x * v)) * (v : ℂ) ^ (α s - 1)) +
          (∫ v in Ici δ₁, cexp (-(x * v)) * (v : ℂ) ^ (α s - 1)) := by
        rw [← Ioo_union_Ici_eq_Ioi hδ₁_pos]
        exact setIntegral_union (Set.disjoint_left.mpr fun _ h1 h2 ↦ h1.2.not_ge h2)
          measurableSet_Ici
          ((integrableOn_cexp_neg_mul_cpow_Ioi (hα_pos s) hx).mono_set Ioo_subset_Ioi_self)
          ((integrableOn_cexp_neg_mul_cpow_Ioi (hα_pos s) hx).mono_set (Ici_subset_Ioi.mpr hδ₁_pos))
      linear_combination hfull - hunion
    rw [hsplit1, hsplit2,
      (by rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun s _ ↦ by rw [hsplit3 s]; ring :
        ∑ s ∈ range N, b s * (∫ v in Ioo 0 δ₁, cexp (-(x * v)) * (v : ℂ) ^ (α s - 1)) =
          (∑ s ∈ range N, (x : ℂ) ^ (-α s) * (Complex.Gamma (α s) * b s)) -
          ∑ s ∈ range N, b s * (∫ v in Ici δ₁, cexp (-(x * v)) * (v : ℂ) ^ (α s - 1)))]; ring
  have hP1 : (fun x : ℝ ↦ ∫ v in Ioo 0 δ₁, cexp (-(x * v)) * rem v) =O[atTop]
      fun x ↦ (x : ℂ) ^ (-α N) := by
    refine isBigO_iff.mpr ⟨C₀ * Real.Gamma (α N).re,
      (eventually_gt_atTop (0 : ℝ)).mono fun x hx ↦ ?_⟩
    have hle := norm_setIntegral_le_mul_of_le measurableSet_Ioo measurableSet_Ioi
      Ioo_subset_Ioi_self (le_max_right C 0) (hInt_rem_Ioo1 hx)
      (integrableOn_rpow_mul_exp_neg_mul_Ioi (hα_pos N) hx)
      (fun v hv ↦ mul_nonneg (Real.rpow_pos_of_pos hv _).le (Real.exp_pos _).le) fun v hv ↦ by
        rw [norm_mul, norm_cexp_neg_mul]
        linarith [mul_le_mul_of_nonneg_left (hrem_bound v hv) (Real.exp_pos (-(x * v))).le]
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (hα_pos N) hx, one_div, Real.inv_rpow hx.le,
      ← Real.rpow_neg hx.le] at hle
    rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]; linarith
  have hP2 : (fun x : ℝ ↦ ∫ v in Ico δ₁ δ, cexp (-(x * v)) * g v) =O[atTop]
      fun x ↦ (x : ℂ) ^ (-α N) :=
    (isBigO_iff.mpr ⟨∫ v in Ioo 0 δ, ‖g v‖,
      (eventually_gt_atTop (0 : ℝ)).mono fun x hx ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
        exact norm_setIntegral_le_mul_of_le measurableSet_Ico measurableSet_Ioo
          (Set.Ico_subset_Ioo_left hδ₁_pos) (Real.exp_pos _).le
          ((hInt_g_Ioo hx).mono_set (Set.Ico_subset_Ioo_left hδ₁_pos)) hg_int.norm
          (fun _ _ ↦ norm_nonneg _) fun v hv ↦ by
            rw [norm_mul, norm_cexp_neg_mul]
            exact mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.mpr (by nlinarith [hv.1])) (norm_nonneg _)⟩ :
      (fun x : ℝ ↦ ∫ v in Ico δ₁ δ, cexp (-(x * v)) * g v) =O[atTop]
        fun x ↦ Real.exp (-δ₁ * x)).trans (isBigO_exp_neg_mul_cpow hδ₁_pos (α N))
  have hP3 : (fun x : ℝ ↦ ∑ s ∈ range N,
      b s * (∫ v in Ici δ₁, cexp (-(x * v)) * (v : ℂ) ^ (α s - 1))) =O[atTop]
      fun x ↦ (x : ℂ) ^ (-α N) := by
    refine (IsBigO.sum (s := range N) (g := fun x : ℝ ↦ (x : ℂ) ^ (-α N)) (A := fun s x ↦
      b s * (∫ v in Ici δ₁, cexp (-(x * v)) * (v : ℂ) ^ (α s - 1))) fun s _ ↦
        IsBigO.const_mul_left ?_ (b s)).congr_left fun x ↦ Finset.sum_apply x (range N) _
    refine (isBigO_iff.mpr
        ⟨Real.exp δ₁ * ∫ v in Ioi (0 : ℝ), Real.exp (-v) * v ^ ((α s).re - 1),
        (eventually_ge_atTop (1 : ℝ)).mono fun x hx1 ↦ ?_⟩ :
        (fun x : ℝ ↦ ∫ v in Ici δ₁, cexp (-(x * v)) * (v : ℂ) ^ (α s - 1)) =O[atTop]
          fun x ↦ Real.exp (-δ₁ * x)).trans (isBigO_exp_neg_mul_cpow hδ₁_pos (α N))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hle := norm_setIntegral_le_mul_of_le measurableSet_Ici measurableSet_Ioi
      (Ici_subset_Ioi.mpr hδ₁_pos) (c := Real.exp δ₁ * Real.exp (-δ₁ * x))
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      ((integrableOn_cexp_neg_mul_cpow_Ioi (hα_pos s) (by linarith)).mono_set
        (Ici_subset_Ioi.mpr hδ₁_pos))
      (Real.GammaIntegral_convergent (hα_pos s))
      (fun v hv ↦ mul_nonneg (Real.exp_pos _).le (Real.rpow_pos_of_pos hv _).le) fun v hv ↦ by
        have hv0 : 0 < v := hδ₁_pos.trans_le hv
        rw [norm_mul, norm_cexp_neg_mul, norm_cpow_eq_rpow_re_of_pos hv0, sub_re, one_re,
          ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hv0 _).le
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith [mem_Ici.mp hv])
    linarith
  exact ((hP1.add hP2).sub hP3).congr'
    ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ (hdecomp hx).symm) EventuallyEq.rfl

/-! ### Laplace's method on `(a, ∞)` and `(a, b)` (DLMF 2.3.13–2.3.15) -/

/-- **Laplace's method on the half-line `(a, ∞)` (DLMF 2.3.13–2.3.15).** Let `μ > 0`, `Re λ > 0`,
and let `p : ℝ → ℝ`, `q : ℝ → ℂ` satisfy as `t → a+`:
* `p(t) - p(a) ~ ∑ pₛ (t - a)^{s + μ}` with `p₀ > 0`, and its termwise derivative
  `p'(t) ~ ∑ (s + μ) pₛ (t - a)^{s + μ - 1}`;
* `q(t) ~ ∑ qₛ (t - a)^{s + λ - 1}`;
* `p` is a.e. measurable on `(a, ∞)` and strictly bounded away from `p(a)` on every `[c, ∞)` with
  `c > a`;
* `t ↦ exp(-x₀ p(t)) q(t)` is integrable on `(a, ∞)` for some `x₀ : ℝ`.

Then as `x → +∞`, for every `N : ℕ`,
`exp(x p(a)) ∫_a^∞ exp(-x p(t)) q(t) dt - ∑_{s < N} x^{-(s + λ)/μ} Γ((s + λ)/μ) bₛ`
`= O(x^{-(N + λ)/μ})`, where `bₛ = laplaceCoeff μ lam (Real.log (ps 0)) P Q s`. -/
theorem isBigO_laplace_method_sub_sum {a μ x₀ : ℝ} (hμ : 0 < μ) {lam : ℂ} (hlam : 0 < lam.re)
    {p : ℝ → ℝ} {q : ℝ → ℂ} {ps : ℕ → ℝ} (hp0 : 0 < ps 0) {qs : ℕ → ℂ}
    (hp : ∀ N : ℕ,
      (fun t : ℝ ↦ p t - p a - ∑ s ∈ range N, ps s * (t - a) ^ ((s : ℝ) + μ)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((N : ℝ) + μ))
    (hp' : ∀ N : ℕ,
      (fun t : ℝ ↦ deriv p t -
        ∑ s ∈ range N, ((s : ℝ) + μ) * ps s * (t - a) ^ ((s : ℝ) + μ - 1)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((N : ℝ) + μ - 1))
    (hq : ∀ N : ℕ,
      (fun t : ℝ ↦ q t - ∑ s ∈ range N, qs s * ((t - a : ℝ) : ℂ) ^ ((s : ℂ) + lam - 1)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((N : ℝ) + lam.re - 1))
    (hpm : AEMeasurable p (volume.restrict (Ioi a)))
    (hmin : ∀ c > a, ∃ η > 0, ∀ t ≥ c, p a + η ≤ p t)
    (hconv : IntegrableOn (fun t : ℝ ↦ cexp (-(x₀ * p t)) * q t) (Ioi a))
    (N : ℕ) :
    (fun x : ℝ ↦ cexp (x * p a) * (∫ t in Ioi a, cexp (-(x * p t)) * q t) -
      ∑ s ∈ range N,
        (x : ℂ) ^ (-(((s : ℂ) + lam) / μ)) *
          (Complex.Gamma (((s : ℂ) + lam) / μ) *
            laplaceCoeff μ lam (Real.log (ps 0)) (PowerSeries.mk fun n ↦ (ps n : ℂ))
              (PowerSeries.mk qs) s)) =O[atTop]
      fun x ↦ (x : ℂ) ^ (-(((N : ℂ) + lam) / μ)) := by
  obtain ⟨ε, hε, T, hp_cont, hp_strict, hder_Ioc, himg_Ioo, hT_left, _, hT_exp⟩ :=
    exists_localInverse_laplace_expansion hμ hp0 hp hp' hq
  set δ : ℝ := p (a + ε) - p a
  have hδ : 0 < δ := sub_pos.mpr
    (hp_strict (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith)) (by linarith))
  set ψ : ℝ → ℝ := fun t ↦ p t - p a
  set g : ℝ → ℂ := fun v ↦ q (T (p a + v)) / ((deriv p (T (p a + v)) : ℝ) : ℂ)
  have hψ_img : ψ '' Ioo a (a + ε) = Ioo 0 δ := by
    ext y; constructor
    · rintro ⟨t, ht, rfl⟩
      have hmem : p t ∈ Ioo (p a) (p (a + ε)) := himg_Ioo ▸ mem_image_of_mem p ht
      exact ⟨sub_pos.mpr hmem.1, sub_lt_sub_right hmem.2 (p a)⟩
    · intro ⟨hy0, hyδ⟩
      have hmem : p a + y ∈ Ioo (p a) (p (a + ε)) := ⟨by linarith, by linarith⟩
      obtain ⟨t, ht, hpt⟩ := himg_Ioo.symm.subset hmem
      exact ⟨t, ht, by dsimp only [ψ]; linarith⟩
  have hψ_inj : InjOn ψ (Ioo a (a + ε)) := fun _ ht₁ _ ht₂ hEq ↦
    hp_strict.injOn (Ioo_subset_Icc_self ht₁) (Ioo_subset_Icc_self ht₂) (sub_left_inj.mp hEq)
  have hψ_deriv : ∀ t ∈ Ioo a (a + ε), HasDerivWithinAt ψ (deriv p t) (Ioo a (a + ε)) t :=
    fun t ht ↦ ((not_imp_comm.mp (deriv_zero_of_not_differentiableAt (f := p) (x := t))
      (hder_Ioc t ⟨ht.1, ht.2.le⟩).ne').hasDerivAt.sub_const (p a)).hasDerivWithinAt
  have hjacob : ∀ t ∈ Ioo a (a + ε), |deriv p t| • g (ψ t) = q t := fun t ht ↦ by
    have hpos : 0 < deriv p t := hder_Ioc t ⟨ht.1, ht.2.le⟩
    have hTpt : T (p a + ψ t) = t := by
      dsimp only [ψ]; rw [add_sub_cancel]; exact hT_left (Ioo_subset_Icc_self ht)
    dsimp only [g]
    rw [abs_of_pos hpos, Complex.real_smul, hTpt, mul_div_cancel₀ _ (ofReal_ne_zero.mpr hpos.ne')]
  have hq_int : IntegrableOn q (Ioo a (a + ε)) := by
    have hcont_exp : ContinuousOn (fun t : ℝ ↦ cexp ((x₀ * p t : ℝ))) (Icc a (a + ε)) :=
      Complex.continuous_exp.comp_continuousOn
        (continuous_ofReal.comp_continuousOn (continuousOn_const.mul hp_cont))
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_exp
    have hconv_Ioo := hconv.mono_set (Ioo_subset_Ioi_self : Ioo a (a + ε) ⊆ Ioi a)
    have hq_eq : ∀ t, cexp ((x₀ * p t : ℝ)) * (cexp (-(x₀ * p t)) * q t) = q t := fun t ↦ by
      rw [← mul_assoc, ← Complex.exp_add, ofReal_mul]; simp
    refine (hconv_Ioo.norm.const_mul (max M 0)).mono'
      ((((hcont_exp.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo).mul
        hconv_Ioo.aestronglyMeasurable).congr (Eventually.of_forall fun t ↦ hq_eq t))
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht ↦ by
        conv_lhs => rw [← hq_eq t]
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          ((hM t (Ioo_subset_Icc_self ht)).trans (le_max_left M 0)) (norm_nonneg _)))
  have hg_int : IntegrableOn g (Ioo 0 δ) := by
    rw [← hψ_img, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hψ_deriv
      hψ_inj g]
    exact hq_int.congr_fun (fun t ht ↦ (hjacob t ht).symm) measurableSet_Ioo
  have hfact : ∀ (x t : ℝ),
      cexp (-(x * (p t - p a))) * q t =
        cexp (-((x - x₀) * (p t - p a))) * (cexp (x₀ * p a) * (cexp (-(x₀ * p t)) * q t)) :=
    fun x t ↦ by rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]; congr 2; ring
  have hshift_int : ∀ {x : ℝ}, x₀ ≤ x →
      IntegrableOn (fun t : ℝ ↦ cexp (-(x * (p t - p a))) * q t) (Ioi a) := fun {x} hx ↦ by
    have hbase := hconv.const_mul (cexp (x₀ * p a))
    have hcont : Continuous fun y : ℝ ↦ cexp (-(((x : ℂ) - (x₀ : ℂ)) * ((y : ℂ) - (p a : ℂ)))) :=
      Complex.continuous_exp.comp
        ((continuous_const.mul (continuous_ofReal.sub continuous_const)).neg)
    refine hbase.norm.mono'
      (((hcont.comp_aestronglyMeasurable hpm.aestronglyMeasurable).mul
        hbase.aestronglyMeasurable).congr (Eventually.of_forall fun t ↦ (hfact x t).symm))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ by
        rw [hfact x t, norm_mul, ← ofReal_sub, ← ofReal_sub, norm_cexp_neg_mul]
        obtain ⟨_, _, hpt⟩ := hmin t ht
        have hexp : Real.exp (-((x - x₀) * (p t - p a))) ≤ 1 := Real.exp_le_one_iff.mpr
          (neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr hx) (by linarith [hpt t le_rfl])))
        nlinarith [norm_nonneg (cexp (x₀ * p a) * (cexp (-(x₀ * p t)) * q t))]))
  have hcov : ∀ x : ℝ,
      ∫ t in Ioo a (a + ε), cexp (-(x * (p t - p a))) * q t =
        ∫ v in Ioo 0 δ, cexp (-(x * v)) * g v := fun x ↦ by
    rw [← hψ_img, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hψ_deriv hψ_inj
      (fun v ↦ cexp (-(x * v)) * g v)]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
    rw [← hjacob t ht, Complex.real_smul, Complex.real_smul]; simp only [ψ, ofReal_sub]; ring
  have hsplit : ∀ {x : ℝ}, x₀ ≤ x →
      cexp (x * p a) * (∫ t in Ioi a, cexp (-(x * p t)) * q t) =
        (∫ v in Ioo 0 δ, cexp (-(x * v)) * g v) +
        (∫ t in Ici (a + ε), cexp (-(x * (p t - p a))) * q t) := fun {x} hx ↦ by
    have hpull : cexp (x * p a) * (∫ t in Ioi a, cexp (-(x * p t)) * q t) =
        ∫ t in Ioi a, cexp (-(x * (p t - p a))) * q t := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun _ _ ↦ by
        rw [← mul_assoc, ← Complex.exp_add]; congr 2; ring
    have hdisj : Disjoint (Ioo a (a + ε)) (Ici (a + ε)) :=
      Set.disjoint_left.mpr fun _ h1 h2 ↦ h1.2.not_ge h2
    rw [hpull, ← Ioo_union_Ici_eq_Ioi (by linarith : a < a + ε),
      setIntegral_union hdisj measurableSet_Ici ((hshift_int hx).mono_set Ioo_subset_Ioi_self)
        ((hshift_int hx).mono_set (Ici_subset_Ioi.mpr (by linarith))), hcov x]
  have hmain := isBigO_laplace_Ioo_sub_sum hδ hμ hlam hg_int hT_exp N
  obtain ⟨η, hη, hmin_ε⟩ := hmin (a + ε) (by linarith)
  have htail : (fun x : ℝ ↦ ∫ t in Ici (a + ε), cexp (-(x * (p t - p a))) * q t) =O[atTop]
      fun x ↦ (x : ℂ) ^ (-(((N : ℂ) + lam) / μ)) := by
    refine (isBigO_iff.mpr
        ⟨Real.exp (x₀ * (η + p a)) * ∫ t in Ioi a, ‖cexp (-(x₀ * p t)) * q t‖,
        (eventually_ge_atTop x₀).mono fun x hx ↦ ?_⟩ :
        (fun x : ℝ ↦ ∫ t in Ici (a + ε), cexp (-(x * (p t - p a))) * q t) =O[atTop]
          fun x ↦ Real.exp (-η * x)).trans (isBigO_exp_neg_mul_cpow hη _)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hle := norm_setIntegral_le_mul_of_le measurableSet_Ici measurableSet_Ioi
      (Ici_subset_Ioi.mpr (lt_add_of_pos_right a hε))
      (c := Real.exp (x₀ * (η + p a)) * Real.exp (-η * x))
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      ((hshift_int hx).mono_set (Ici_subset_Ioi.mpr (lt_add_of_pos_right a hε))) hconv.norm
      (fun _ _ ↦ norm_nonneg _) fun t ht ↦ by
        have hpt : η ≤ p t - p a := by linarith [hmin_ε t ht]
        rw [hfact x t, norm_mul, norm_mul, ← ofReal_sub, ← ofReal_sub, norm_cexp_neg_mul,
          Complex.norm_exp, ← mul_assoc]
        simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
    linarith
  exact (hmain.add htail).congr'
    ((eventually_ge_atTop x₀).mono fun _ hx ↦ by dsimp only; rw [hsplit hx]; ring) EventuallyEq.rfl

/-- **Laplace's method on a finite interval `(a, b)` (DLMF 2.3.13–2.3.15).** Follows from
`isBigO_laplace_method_sub_sum` by extending `q` by `0` and `p` by `p(a) + 1` on `[b, ∞)`. -/
theorem isBigO_laplace_method_Ioo_sub_sum {a b μ x₀ : ℝ} (hab : a < b) (hμ : 0 < μ)
    {lam : ℂ} (hlam : 0 < lam.re) {p : ℝ → ℝ} {q : ℝ → ℂ} {ps : ℕ → ℝ} (hp0 : 0 < ps 0)
    {qs : ℕ → ℂ}
    (hp : ∀ N : ℕ,
      (fun t : ℝ ↦ p t - p a - ∑ s ∈ range N, ps s * (t - a) ^ ((s : ℝ) + μ)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((N : ℝ) + μ))
    (hp' : ∀ N : ℕ,
      (fun t : ℝ ↦ deriv p t -
        ∑ s ∈ range N, ((s : ℝ) + μ) * ps s * (t - a) ^ ((s : ℝ) + μ - 1)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((N : ℝ) + μ - 1))
    (hq : ∀ N : ℕ,
      (fun t : ℝ ↦ q t - ∑ s ∈ range N, qs s * ((t - a : ℝ) : ℂ) ^ ((s : ℂ) + lam - 1)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((N : ℝ) + lam.re - 1))
    (hpm : AEMeasurable p (volume.restrict (Ioo a b)))
    (hmin : ∀ c ∈ Ioo a b, ∃ η > 0, ∀ t ∈ Ico c b, p a + η ≤ p t)
    (hconv : IntegrableOn (fun t : ℝ ↦ cexp (-(x₀ * p t)) * q t) (Ioo a b))
    (N : ℕ) :
    (fun x : ℝ ↦ cexp (x * p a) * (∫ t in Ioo a b, cexp (-(x * p t)) * q t) -
      ∑ s ∈ range N,
        (x : ℂ) ^ (-(((s : ℂ) + lam) / μ)) *
          (Complex.Gamma (((s : ℂ) + lam) / μ) *
            laplaceCoeff μ lam (Real.log (ps 0)) (PowerSeries.mk fun n ↦ (ps n : ℂ))
              (PowerSeries.mk qs) s)) =O[atTop]
      fun x ↦ (x : ℂ) ^ (-(((N : ℂ) + lam) / μ)) := by
  let p' : ℝ → ℝ := fun t ↦ if t < b then p t else p a + 1
  let q' : ℝ → ℂ := fun t ↦ if t < b then q t else 0
  have hp'a : p' a = p a := by simp [p', hab]
  have hderiv'_eq : deriv p' =ᶠ[𝓝[>] a] deriv p :=
    Filter.eventually_of_mem (Ioo_mem_nhdsGT hab) fun t ht ↦
      Filter.EventuallyEq.deriv_eq
        (Filter.eventually_of_mem (isOpen_Iio.mem_nhds ht.2) fun _ hs ↦ by
          simp [p', mem_Iio.mp hs])
  have hpm_ext : AEMeasurable p' (volume.restrict (Ioi a)) := by
    have hdisj : Disjoint (Ioo a b) (Ici b) := Set.disjoint_left.mpr fun _ h1 h2 ↦ h1.2.not_ge h2
    rw [← Ioo_union_Ici_eq_Ioi hab, Measure.restrict_union hdisj measurableSet_Ici,
      aemeasurable_add_measure_iff]
    exact ⟨hpm.congr ((ae_restrict_iff' measurableSet_Ioo).mpr
        (Eventually.of_forall fun _ ht ↦ by simp [p', ht.2])),
      (measurable_const (a := p a + 1)).aemeasurable.congr ((ae_restrict_iff' measurableSet_Ici).mpr
        (Eventually.of_forall fun _ ht ↦ by simp [p', not_lt.mpr (mem_Ici.mp ht)]))⟩
  have hmin_ext : ∀ c > a, ∃ η > 0, ∀ t ≥ c, p' a + η ≤ p' t := fun c hc ↦ by
    by_cases hcb : c < b
    · obtain ⟨η, hη, hη_le⟩ := hmin c ⟨hc, hcb⟩
      refine ⟨min η 1, lt_min hη one_pos, fun t ht ↦ ?_⟩
      rw [hp'a]; dsimp only [p']; split_ifs with htb
      · linarith [min_le_left η 1, hη_le t ⟨ht, htb⟩]
      · linarith [min_le_right η 1]
    · exact ⟨1, one_pos, fun t ht ↦ by
        rw [hp'a]; dsimp only [p']; rw [ite_eq_right (by linarith)]⟩
  have hconv_ext : IntegrableOn (fun t : ℝ ↦ cexp (-(x₀ * p' t)) * q' t) (Ioi a) := by
    rw [← Ioo_union_Ici_eq_Ioi hab, integrableOn_union]
    exact ⟨hconv.congr_fun (fun _ ht ↦ by simp [p', q', ht.2]) measurableSet_Ioo,
      (integrableOn_zero (s := Ici b)).congr_fun
        (fun _ ht ↦ by simp [q', not_lt.mpr (mem_Ici.mp ht)]) measurableSet_Ici⟩
  have hres := isBigO_laplace_method_sub_sum (qs := qs) hμ hlam hp0
    (fun M ↦ (hp M).congr'
      (Filter.eventually_of_mem (Ioo_mem_nhdsGT hab) fun _ ht ↦ by simp [p', hp'a, ht.2])
      EventuallyEq.rfl)
    (fun M ↦ (hp' M).congr' (hderiv'_eq.mono fun _ ht ↦ by simp only [ht]) EventuallyEq.rfl)
    (fun M ↦ (hq M).congr'
      (Filter.eventually_of_mem (Ioo_mem_nhdsGT hab) fun _ ht ↦ by simp [q', ht.2])
      EventuallyEq.rfl)
    hpm_ext hmin_ext hconv_ext N
  refine hres.congr_left fun x ↦ ?_
  have hind : (fun t : ℝ ↦ cexp (-(x * p' t)) * q' t) =
      (Iio b).indicator (fun t : ℝ ↦ cexp (-(x * p t)) * q t) := by
    ext t; by_cases htb : t < b <;> simp [p', q', htb, Set.indicator]
  rw [hp'a, hind, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]

/-! ### Worked examples -/

private theorem isBigO_rpow_sub_sum_single (c α : ℝ) (M : ℕ) :
    (fun t : ℝ ↦ c * (t - 0) ^ α -
      ∑ s ∈ range M, (if s = 0 then c else 0) * (t - 0) ^ ((s : ℝ) + α)) =O[𝓝[>] 0]
      fun t ↦ (t - 0) ^ ((M : ℝ) + α) := by
  cases M with
  | zero => simpa using (isBigO_refl (fun t : ℝ ↦ t ^ α) (𝓝[>] 0)).const_mul_left c
  | succ M =>
    refine (isBigO_zero _ _).congr' (Eventually.of_forall fun t ↦ ?_) EventuallyEq.rfl
    dsimp only; rw [Finset.sum_eq_single 0 (fun s _ hs ↦ by simp [hs]) (by simp)]; simp

/-- **Gaussian half-line specialization of Laplace's method (`p(t) = t²`, `q = 1`).**
With `a = 0`, `μ = 2`, `λ = 1`, `p₀ = 1`, the Laplace coefficients are `b₀ = 1/2` and `bₛ = 0` for
`s ≥ 1`, so for every `N ≥ 1`,
`∫_0^∞ exp(-x t²) dt - x^{-1/2} (√π / 2) = O(x^{-(N + 1)/2})` as `x → +∞`. -/
theorem isBigO_integral_exp_neg_mul_sq_sub (N : ℕ) (hN : 1 ≤ N) :
    (fun x : ℝ ↦ (∫ t in Ioi (0 : ℝ), cexp (-(x * (t : ℂ) ^ 2))) -
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * ((Real.sqrt π : ℂ) / 2)) =O[atTop]
      fun x ↦ (x : ℂ) ^ (-(((N : ℂ) + 1) / 2)) := by
  let ps : ℕ → ℝ := fun n ↦ if n = 0 then 1 else 0
  let qs : ℕ → ℂ := fun n ↦ if n = 0 then 1 else 0
  have hps_mk : PowerSeries.mk (fun n ↦ (ps n : ℂ)) = 1 := by
    ext n; simp only [coeff_mk, coeff_one, ps]; split_ifs <;> simp
  have hqs_mk : PowerSeries.mk qs = 1 := by ext n; simp [qs, coeff_one]
  have hp' : ∀ M : ℕ,
      (fun t : ℝ ↦ deriv (fun u : ℝ ↦ u ^ 2) t -
        ∑ s ∈ range M, ((s : ℝ) + 2) * ps s * (t - 0) ^ ((s : ℝ) + 2 - 1))
        =O[𝓝[>] 0] fun t ↦ (t - 0) ^ ((M : ℝ) + 2 - 1) := fun M ↦
    (isBigO_rpow_sub_sum_single 2 1 M).congr (fun t ↦ by
      have hd : deriv (fun u : ℝ ↦ u ^ 2) t = 2 * t := by simp
      rw [hd]; simp only [ps, sub_zero, Real.rpow_one]
      congr 1; refine Finset.sum_congr rfl fun s _ ↦ ?_
      split_ifs with hs
      · simp [hs]; norm_num
      · simp) (fun t ↦ by congr 1; ring)
  have hq : ∀ M : ℕ,
      (fun t : ℝ ↦ (1 : ℂ) - ∑ s ∈ range M, qs s * ((t - 0 : ℝ) : ℂ) ^ ((s : ℂ) + 1 - 1))
        =O[𝓝[>] 0] fun t ↦ (t - 0) ^ ((M : ℝ) + (1 : ℂ).re - 1) := fun M ↦ by
    cases M with
    | zero => exact isBigO_iff.mpr ⟨1, Eventually.of_forall fun _ ↦ by simp⟩
    | succ M =>
      refine (isBigO_zero _ _).congr' (Eventually.of_forall fun t ↦ ?_) EventuallyEq.rfl
      dsimp only; rw [Finset.sum_eq_single 0 (fun s _ hs ↦ by simp [qs, hs]) (by simp)]; simp [qs]
  have hres := isBigO_laplace_method_sub_sum (a := 0) (μ := 2) (x₀ := 1) (lam := 1)
    (p := fun t : ℝ ↦ t ^ 2) (q := fun _ ↦ (1 : ℂ)) (ps := ps) (qs := qs)
    two_pos (by simp) (by simp [ps])
    (fun M ↦ (isBigO_rpow_sub_sum_single 1 2 M).congr_left fun t ↦ by simp [ps]) hp' hq
    (continuous_pow 2).measurable.aemeasurable
    (fun c hc ↦ ⟨c ^ 2, sq_pos_of_pos hc, fun t ht ↦ by nlinarith⟩)
    (((integrable_cexp_neg_mul_sq (b := (1 : ℂ)) (by simp)).integrableOn (s := Ioi 0)).congr_fun
      (fun _ _ ↦ by simp [sq]) measurableSet_Ioi) N
  refine hres.congr_left fun x ↦ ?_
  have hsum : ∑ s ∈ range N, (x : ℂ) ^ (-(((s : ℂ) + 1) / (2 : ℝ))) *
      (Complex.Gamma (((s : ℂ) + 1) / (2 : ℝ)) *
        laplaceCoeff 2 1 (Real.log (ps 0)) (PowerSeries.mk fun n ↦ (ps n : ℂ))
          (PowerSeries.mk qs) s) =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * ((Real.sqrt π : ℂ) / 2) := by
    rw [hps_mk, hqs_mk, (by simp [ps] : Real.log (ps 0) = 0), ofReal_zero,
      Finset.sum_eq_single 0 (fun s _ hs ↦ by simp [hs])
        (fun h0 ↦ absurd (Finset.mem_range.mpr (by omega)) h0), laplaceCoeff_one_one]
    simp only [ite_true, Nat.cast_zero, zero_add, ofReal_ofNat]
    rw [(by norm_num : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ)), Complex.Gamma_ofReal,
      Real.Gamma_one_half_eq]; ring
  simp only [zero_pow two_ne_zero, ofReal_zero, mul_zero, Complex.exp_zero, one_mul, mul_one,
    ofReal_pow, hsum]

/-- **Linear-phase specialization of Laplace's method (`p(t) = t`, `μ = 1`, Watson's lemma).**
With `a = 0`, `μ = 1`, `p(t) = t`, `p₀ = 1`, we have `laplaceCoeff 1 lam 0 1 Q s = qs s`,
recovering Watson's lemma for the exponent sequence `s + λ`. -/
theorem isBigO_laplace_method_id_sub_sum {x₀ : ℝ} {lam : ℂ} (hlam : 0 < lam.re)
    {q : ℝ → ℂ} {qs : ℕ → ℂ}
    (hq : ∀ N : ℕ,
      (fun t : ℝ ↦ q t - ∑ s ∈ range N, qs s * (t : ℂ) ^ ((s : ℂ) + lam - 1)) =O[𝓝[>] 0]
        fun t ↦ t ^ ((N : ℝ) + lam.re - 1))
    (hconv : IntegrableOn (fun t : ℝ ↦ cexp (-(x₀ * t)) * q t) (Ioi 0))
    (N : ℕ) :
    (fun x : ℝ ↦ (∫ t in Ioi (0 : ℝ), cexp (-(x * t)) * q t) -
      ∑ s ∈ range N, (x : ℂ) ^ (-((s : ℂ) + lam)) * (Complex.Gamma ((s : ℂ) + lam) * qs s))
      =O[atTop] fun x ↦ (x : ℂ) ^ (-((N : ℂ) + lam)) := by
  let ps : ℕ → ℝ := fun n ↦ if n = 0 then 1 else 0
  have hps_mk : PowerSeries.mk (fun n ↦ (ps n : ℂ)) = 1 := by
    ext n; simp only [coeff_mk, coeff_one, ps]; split_ifs <;> simp
  have hp' : ∀ M : ℕ,
      (fun t : ℝ ↦ deriv (fun u : ℝ ↦ u) t -
        ∑ s ∈ range M, ((s : ℝ) + 1) * ps s * (t - 0) ^ ((s : ℝ) + 1 - 1)) =O[𝓝[>] 0]
        fun t ↦ (t - 0) ^ ((M : ℝ) + 1 - 1) := fun M ↦
    (isBigO_rpow_sub_sum_single 1 0 M).congr (fun t ↦ by
      simp only [ps, deriv_id'', sub_zero, Real.rpow_zero, mul_one, add_zero, add_sub_cancel_right]
      congr 1; refine Finset.sum_congr rfl fun s _ ↦ ?_; split_ifs with hs <;> simp [hs])
      (fun _ ↦ by simp)
  have hres := isBigO_laplace_method_sub_sum (a := 0) (μ := 1) (x₀ := x₀) (lam := lam)
    (p := fun t ↦ t) (q := q) (ps := ps) (qs := qs)
    one_pos hlam (by simp [ps])
    (fun M ↦ (isBigO_rpow_sub_sum_single 1 1 M).congr_left fun t ↦ by simp [ps]) hp'
    (fun M ↦ by simpa [sub_zero] using hq M)
    measurable_id.aemeasurable (fun c hc ↦ ⟨c, hc, fun t ht ↦ by simp [ht]⟩) hconv N
  refine hres.congr (fun x ↦ ?_) (fun _ ↦ by simp)
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, one_mul, hps_mk,
    (by simp [ps] : Real.log (ps 0) = 0), ofReal_one, div_one, laplaceCoeff_one_left, inv_one,
    coeff_mk]

end Asymptotics
