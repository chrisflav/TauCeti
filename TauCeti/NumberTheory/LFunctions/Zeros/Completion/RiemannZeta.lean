/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Zeros.Divisor
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# The entire completion of the Riemann zeta function

The explicit function `zetaEntireCompletion` is twice Riemann's ξ-function. It agrees with
`s * (s - 1) * completedRiemannZeta s` away from the two poles, but takes the value `1` at
both `0` and `1`. In particular, clearing the poles introduces no artificial zeros.

The identity with `riemannZetaData.entireCompletion` connects this formula and its reflection
symmetry to the general pole-clearing construction. Complex conjugation commutes with
`zetaEntireCompletion`, so it is real-valued on the real axis; since `riemannZeta` has no zeros on
`Re s ≥ 1` and is strictly negative on `(0, 1)`, `zetaEntireCompletion` is strictly positive on all
of `ℝ` and all its zeros lie in `0 < Re s < 1` off the real axis. Its logarithmic derivative
satisfies the reflection and conjugation symmetries and splits into the polar, `Γ_ℝ`, and `ζ`
logarithmic derivatives on `Re s > 0` away from `1` and the zeros of `ζ`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §12.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§2.12, 9.2–9.3.
-/

public section

open Complex ComplexConjugate Filter Polynomial Set
open scoped Topology ComplexOrder

namespace TauCeti.LFunctions

/-- Twice Riemann's ξ-function, with its removable values at `0` and `1` filled in. -/
noncomputable def zetaEntireCompletion (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

theorem zetaEntireCompletion_def (s : ℂ) :
    zetaEntireCompletion s = s * (s - 1) * completedRiemannZeta₀ s + 1 := (rfl)

/-- The explicit entire completion is entire. -/
theorem differentiable_zetaEntireCompletion : Differentiable ℂ zetaEntireCompletion := by
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

@[simp]
theorem zetaEntireCompletion_zero : zetaEntireCompletion 0 = 1 := by
  simp [zetaEntireCompletion_def]

@[simp]
theorem zetaEntireCompletion_one : zetaEntireCompletion 1 = 1 := by
  simp [zetaEntireCompletion_def]

/-- The entire completion retains the reflection symmetry about the critical line. -/
theorem zetaEntireCompletion_one_sub (s : ℂ) :
    zetaEntireCompletion (1 - s) = zetaEntireCompletion s := by
  simp only [zetaEntireCompletion_def, completedRiemannZeta₀_one_sub]
  ring

/-- Away from the poles the explicit completion is the usual pole-cleared product. -/
theorem zetaEntireCompletion_eq_mul {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    zetaEntireCompletion s = s * (s - 1) * completedRiemannZeta s := by
  rw [zetaEntireCompletion_def, completedRiemannZeta_eq]
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- Complex conjugation commutes with `zetaEntireCompletion`. -/
theorem zetaEntireCompletion_conj (s : ℂ) :
    zetaEntireCompletion (conj s) = conj (zetaEntireCompletion s) := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  rcases eq_or_ne s 1 with rfl | hs1
  · simp
  have hcs0 : conj s ≠ 0 := map_ne_zero_iff _ (starRingEnd ℂ).injective |>.2 hs0
  have hcs1 : conj s ≠ 1 := by
    intro h
    apply hs1
    simpa using congrArg conj h
  rw [zetaEntireCompletion_eq_mul hcs0 hcs1, zetaEntireCompletion_eq_mul hs0 hs1,
    completedRiemannZeta_conj]
  simp

/-- On the real line, `zetaEntireCompletion` has zero imaginary part. -/
@[simp]
theorem zetaEntireCompletion_ofReal_im (x : ℝ) : (zetaEntireCompletion x).im = 0 := by
  have h := zetaEntireCompletion_conj x
  rw [conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

/-- The Riemann zeta record clears precisely the simple poles at `0` and `1`. -/
@[simp]
theorem riemannZetaData_polarPolynomial :
    riemannZetaData.polarPolynomial = X * (X - 1) := by
  simp [AnalyticLFunctionData.polarPolynomial_def, Finsupp.prod_add_index', pow_add]

/-- The general removable extension recovers the explicit entire completion of zeta. -/
@[simp]
theorem riemannZetaData_entireCompletion :
    riemannZetaData.entireCompletion = zetaEntireCompletion := by
  symm
  apply riemannZetaData_hasMeromorphicContinuation.entireCompletion_unique
    differentiable_zetaEntireCompletion.continuous
  intro s hs
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  simpa using zetaEntireCompletion_eq_mul hs0 hs1

/-- The entire completion has a zero of positive multiplicity exactly where
`completedRiemannZeta` has one: clearing the poles at `0` and `1` creates no zeros. -/
theorem zero_lt_divisor_zetaEntireCompletion_iff {s : ℂ} :
    0 < MeromorphicOn.divisor zetaEntireCompletion Set.univ s ↔
      0 < MeromorphicOn.divisor completedRiemannZeta Set.univ s := by
  have h := riemannZetaData_hasMeromorphicContinuation.toNat_divisor_entireCompletion s
  rw [riemannZetaData_entireCompletion, riemannZetaData_completed] at h
  omega

/-- Since `zetaEntireCompletion` is entire and `zetaEntireCompletion 0 = 1`, it vanishes at `s` if
and only if `completedRiemannZeta` has positive divisor at `s`. -/
theorem zetaEntireCompletion_eq_zero_iff {s : ℂ} :
    zetaEntireCompletion s = 0 ↔ 0 < MeromorphicOn.divisor completedRiemannZeta Set.univ s := by
  have hana : AnalyticOnNhd ℂ zetaEntireCompletion univ :=
    fun z _ ↦ differentiable_zetaEntireCompletion.analyticAt z
  have h0 : analyticOrderAt zetaEntireCompletion 0 ≠ ⊤ := by
    rw [(hana 0 (mem_univ 0)).analyticOrderAt_eq_zero.2 (by simp)]
    exact ENat.zero_ne_top
  have htop : meromorphicOrderAt zetaEntireCompletion s ≠ ⊤ := by
    rw [(hana s (mem_univ s)).meromorphicOrderAt_eq]
    simpa using hana.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ 0) (mem_univ s) h0
  rw [← hana.meromorphicOn.zero_lt_divisor_iff_of_analyticAt (hana s (mem_univ s))
    (mem_univ s) htop, zero_lt_divisor_zetaEntireCompletion_iff]

/-- `zetaEntireCompletion` has no zeros on the closed half-plane `1 ≤ Re s`. -/
theorem zetaEntireCompletion_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    zetaEntireCompletion s ≠ 0 := by
  intro h0
  obtain ⟨hζ, -, -⟩ :=
    TauCeti.zero_lt_divisor_completedRiemannZeta_iff.1 (zetaEntireCompletion_eq_zero_iff.1 h0)
  exact riemannZeta_ne_zero_of_one_le_re hs hζ

/-- `zetaEntireCompletion` has no zeros on the closed half-plane `Re s ≤ 0`. -/
theorem zetaEntireCompletion_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0) :
    zetaEntireCompletion s ≠ 0 := by
  rw [← zetaEntireCompletion_one_sub]
  exact zetaEntireCompletion_ne_zero_of_one_le_re (by simp; linarith)

/-- `zetaEntireCompletion` is nowhere zero on the real axis. -/
theorem zetaEntireCompletion_ofReal_ne_zero (x : ℝ) : zetaEntireCompletion x ≠ 0 := by
  rcases le_or_gt x 0 with hx0 | hx0
  · exact zetaEntireCompletion_ne_zero_of_re_le_zero (by simpa using hx0)
  rcases le_or_gt 1 x with hx1 | hx1
  · exact zetaEntireCompletion_ne_zero_of_one_le_re (by simpa using hx1)
  intro h0
  obtain ⟨hζ, -, -⟩ :=
    TauCeti.zero_lt_divisor_completedRiemannZeta_iff.1 (zetaEntireCompletion_eq_zero_iff.1 h0)
  exact (TauCeti.riemannZeta_lt_zero hx0 hx1).ne hζ

/-- `zetaEntireCompletion` is strictly positive on the entire real axis: it is real, continuous,
nowhere zero on `ℝ`, and equal to `1` at `0`. -/
theorem zetaEntireCompletion_ofReal_re_pos (x : ℝ) : 0 < (zetaEntireCompletion x).re := by
  by_contra hnot
  rw [not_lt] at hnot
  have hcont : ContinuousOn (fun y : ℝ ↦ (zetaEntireCompletion y).re) univ :=
    (Complex.continuous_re.comp
      (differentiable_zetaEntireCompletion.continuous.comp continuous_ofReal)).continuousOn
  have h0 : (0 : ℝ) ≤ (zetaEntireCompletion (0 : ℝ)).re := by simp
  obtain ⟨y, -, hy0⟩ :=
    isPreconnected_univ.intermediate_value (mem_univ x) (mem_univ (0 : ℝ)) hcont ⟨hnot, h0⟩
  exact zetaEntireCompletion_ofReal_ne_zero y (Complex.ext hy0 (zetaEntireCompletion_ofReal_im y))

/-- Every zero of `zetaEntireCompletion` lies in the open critical strip `0 < Re s < 1` off the
real axis. -/
theorem re_mem_Ioo_and_im_ne_zero_of_zetaEntireCompletion_eq_zero {s : ℂ}
    (hs : zetaEntireCompletion s = 0) : s.re ∈ Ioo 0 1 ∧ s.im ≠ 0 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_contra hle
    exact zetaEntireCompletion_ne_zero_of_re_le_zero (not_lt.1 hle) hs
  · by_contra hge
    exact zetaEntireCompletion_ne_zero_of_one_le_re (not_lt.1 hge) hs
  · intro him
    have hreal : (s.re : ℂ) = s := Complex.ext rfl him.symm
    exact zetaEntireCompletion_ofReal_ne_zero s.re (hreal ▸ hs)

/-- Every zero of `completedRiemannZeta` (in the divisor sense) lies in the open critical strip
`0 < Re s < 1` off the real axis. -/
theorem re_mem_Ioo_and_im_ne_zero_of_zero_lt_divisor_completedRiemannZeta {s : ℂ}
    (hs : 0 < MeromorphicOn.divisor completedRiemannZeta univ s) :
    s.re ∈ Ioo 0 1 ∧ s.im ≠ 0 :=
  re_mem_Ioo_and_im_ne_zero_of_zetaEntireCompletion_eq_zero (zetaEntireCompletion_eq_zero_iff.2 hs)

/-- Reflection symmetry of the logarithmic derivative of `zetaEntireCompletion`. -/
theorem logDeriv_zetaEntireCompletion_one_sub (s : ℂ) :
    logDeriv zetaEntireCompletion (1 - s) = -logDeriv zetaEntireCompletion s := by
  have h : logDeriv (fun z ↦ zetaEntireCompletion (1 - z)) s =
      -logDeriv zetaEntireCompletion (1 - s) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_comp_const_sub, neg_div]
  rw [← neg_neg (logDeriv _ (1 - s)), ← h, funext zetaEntireCompletion_one_sub]

/-- Conjugation symmetry of the logarithmic derivative of `zetaEntireCompletion`. -/
theorem logDeriv_zetaEntireCompletion_conj (s : ℂ) :
    logDeriv zetaEntireCompletion (conj s) = conj (logDeriv zetaEntireCompletion s) := by
  have h : zetaEntireCompletion = conj ∘ zetaEntireCompletion ∘ conj :=
    funext fun z ↦ by simp [zetaEntireCompletion_conj]
  conv_rhs => rw [h]
  rw [logDeriv_apply, logDeriv_apply, deriv_conj_conj]
  simp [zetaEntireCompletion_conj]

/-- On the real axis, `logDeriv zetaEntireCompletion` has zero imaginary part. -/
@[simp]
theorem logDeriv_zetaEntireCompletion_ofReal_im (x : ℝ) :
    (logDeriv zetaEntireCompletion x).im = 0 := by
  have h := logDeriv_zetaEntireCompletion_conj x
  rw [conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

/-- On `Re s > 0` away from `1` and the zeros of `riemannZeta`, the logarithmic derivative of
`zetaEntireCompletion` splits into the polar, archimedean, and Dirichlet-series logarithmic
derivatives. -/
theorem logDeriv_zetaEntireCompletion {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    logDeriv zetaEntireCompletion s =
      logDeriv (fun z : ℂ ↦ z * (z - 1)) s + logDeriv Gammaℝ s + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have heq : zetaEntireCompletion =ᶠ[𝓝 s]
      fun z : ℂ ↦ (z * (z - 1) * Gammaℝ z) * riemannZeta z := by
    filter_upwards [((isOpen_lt continuous_const continuous_re).inter isOpen_ne).mem_nhds
      ⟨hs, hs1⟩] with z ⟨hz, hz1⟩
    have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
    have hΓz : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hz
    rw [zetaEntireCompletion_eq_mul hz0 hz1, riemannZeta_def_of_ne_zero hz0]
    field_simp [hΓz]
  have hΓ_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hΓ_diff : DifferentiableAt ℂ Gammaℝ s := by
    have h := (differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero hΓ_ne)
    have hinv : (fun z ↦ (Gammaℝ z)⁻¹)⁻¹ = Gammaℝ := funext fun z ↦ inv_inv _
    exact (hinv ▸ h).differentiableAt
  have hp_ne : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.2 hs1)
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_fun_mul (f := fun z : ℂ ↦ z * (z - 1) * Gammaℝ z) (g := riemannZeta) s
      (mul_ne_zero hp_ne hΓ_ne) hζ
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hΓ_diff)
      (differentiableAt_riemannZeta hs1),
    logDeriv_fun_mul (f := fun z : ℂ ↦ z * (z - 1)) (g := Gammaℝ) s hp_ne hΓ_ne
      (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hΓ_diff]

end TauCeti.LFunctions
