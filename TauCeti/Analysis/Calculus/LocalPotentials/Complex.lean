/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.SimplyConnected
public import Mathlib.Analysis.Complex.HasPrimitives

import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Calculus.LocalPotentials.CurveIntegral
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Planar and complex one-forms with local potentials

This file connects `TauCeti.HasLocalPotentials` and `TauCeti.localPotentialIntegral` on open
subsets of `ℂ` with holomorphic and Morera-conservative functions (`Complex.IsExactOn`,
`Complex.IsConservativeOn`, `DifferentiableOn ℂ`), and constructs the standard planar separating
examples:

* `TauCeti.hasLocalPotentials_toSpanSingleton_restrictScalars_iff`: for a complete complex normed
  space `F`, the `ℂ`-linear covector field `z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ`
  has local potentials on `s` if and only if `s` is open and `f` is holomorphic on `s`.
* `DifferentiableOn.hasLocalPotentials` and `Complex.IsConservativeOn.hasLocalPotentials`: local
  potentials of holomorphic and continuous conservative functions on open subsets of `ℂ`.
* `TauCeti.not_hasLocalPotentials_re_smul_imCLM`: the smooth `1`-form `x dy` (`z ↦ z.re • Im`)
  has no local potentials on any nonempty set (in particular on `ℂ` or any open disc of positive
  radius).
* `TauCeti.angularForm`: the punctured-plane angular `1`-form `dθ = Im(dz / z)`, which has global
  `C¹` potential `Complex.arg` on `Complex.slitPlane`, satisfies `HasLocalPotentials ({0}ᶜ)
  angularForm`, integrates to `2π` along `TauCeti.unitCircleLoop` (hence `-2π` along its reversal
  and `4π` when traversed twice), and therefore admits no global potential on `{0}ᶜ` (confirming in
  particular `¬ IsSimplyConnected ({0}ᶜ : Set ℂ)`).
-/

public section

open Set Metric ContinuousLinearMap unitInterval
open scoped Topology ContDiff

namespace TauCeti

section ComplexScalars

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- If `f : ℂ → F` is continuous on an open set `s` and admits a complex primitive on `s`, then
its `ℂ`-linear real covector field has local potentials on `s` (without completeness of `F`). -/
theorem _root_.Complex.IsExactOn.hasLocalPotentials {s : Set ℂ} {f : ℂ → F}
    (hf : Complex.IsExactOn f s) (hs : IsOpen s) (hf_cont : ContinuousOn f s) :
    HasLocalPotentials s (fun z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ) := by
  obtain ⟨g, hg⟩ := hf
  have hd : ∀ z ∈ s, HasFDerivAt g ((toSpanSingleton ℂ (f z)).restrictScalars ℝ) z :=
    fun z hz ↦ (hasDerivAt_iff_hasFDerivAt_restrictScalars ℝ).mp (hg z hz)
  have hg_c1 : ContDiffOn ℝ 1 g s := by
    rw [← zero_add (1 : ℕ∞ω), contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact (((continuous_restrictScalars ℝ).comp
      (toSpanSingletonLIE ℂ F).continuous).comp_continuousOn hf_cont).congr
      fun z hz ↦ (hd z hz).fderiv
  exact hasLocalPotentials_of_hasFDerivAt hs hg_c1 hd

section CompleteSpace

variable [CompleteSpace F] {s : Set ℂ} {f : ℂ → F}

/-- On an open subset `s ⊆ ℂ`, a holomorphic function `f : ℂ → F` into a complete complex normed
space defines a covector field with local potentials. -/
theorem _root_.DifferentiableOn.hasLocalPotentials (hf : DifferentiableOn ℂ f s) (hs : IsOpen s) :
    HasLocalPotentials s (fun z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ) := by
  rw [hasLocalPotentials_iff]
  intro z hz
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs z hz
  have hball := ((hf.mono hrs).isExactOn_ball).hasLocalPotentials isOpen_ball
    (hf.continuousOn.mono hrs)
  obtain ⟨δ, hδ, hδr, g, hg_c1, hd⟩ := hasLocalPotentials_iff.mp hball z (mem_ball_self hr)
  exact ⟨δ, hδ, hδr.trans hrs, g, hg_c1, hd⟩

/-- On an open subset `s ⊆ ℂ`, a continuous `Complex.IsConservativeOn` function into a complete
complex normed space defines a covector field with local potentials. -/
theorem _root_.Complex.IsConservativeOn.hasLocalPotentials (hf : Complex.IsConservativeOn f s)
    (hs : IsOpen s) (hf_cont : ContinuousOn f s) :
    HasLocalPotentials s (fun z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ) :=
  ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hs).mp
    ⟨hf, hf_cont⟩).hasLocalPotentials hs

/-- For a complete complex normed space `F`, the `ℂ`-linear covector field associated to `f : ℂ → F`
has local potentials on `s` if and only if `s` is open and `f` is holomorphic on `s`. -/
theorem hasLocalPotentials_toSpanSingleton_restrictScalars_iff :
    HasLocalPotentials s (fun z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ) ↔
      IsOpen s ∧ DifferentiableOn ℂ f s := by
  refine ⟨fun hφ ↦ ⟨hφ.isOpen, fun z hz ↦ ?_⟩, fun ⟨hs, hf⟩ ↦ hf.hasLocalPotentials hs⟩
  obtain ⟨r, hr, -, g, -, hg⟩ := hasLocalPotentials_iff.mp hφ z hz
  have hexact : Complex.IsExactOn f (ball z r) :=
    ⟨g, fun w hw ↦ (hasDerivAt_iff_hasFDerivAt_restrictScalars ℝ).mpr (hg w hw)⟩
  exact ((hexact.differentiableOn isOpen_ball z (mem_ball_self hr)).differentiableAt
    (ball_mem_nhds z hr)).differentiableWithinAt

end CompleteSpace

end ComplexScalars

section NonConservativeExample

/-- The smooth `1`-form `x dy` (`z ↦ z.re • Complex.imCLM`) has no local potentials on any
nonempty subset of `ℂ`. -/
theorem not_hasLocalPotentials_re_smul_imCLM {s : Set ℂ} (hs : s.Nonempty) :
    ¬ HasLocalPotentials s (fun z : ℂ ↦ z.re • Complex.imCLM) := by
  -- Integrating a putative local potential around an axis-aligned square of side `ε = δ / 3`
  -- inside a potential ball yields a nonzero `ε²` area discrepancy.
  obtain ⟨c, hc⟩ := hs
  intro h
  obtain ⟨δ, hδ, -, g, -, hg⟩ := hasLocalPotentials_iff.mp h c hc
  let φ : ℂ → ℂ →L[ℝ] ℝ := fun z ↦ z.re • Complex.imCLM
  have hφ_cont : Continuous φ := Complex.continuous_re.smul continuous_const
  let ε : ℝ := δ / 3
  have hε : 0 < ε := by positivity
  let p₀₀ : ℂ := c
  let p₁₀ : ℂ := c + ε
  let p₁₁ : ℂ := c + ε + ε * Complex.I
  let p₀₁ : ℂ := c + ε * Complex.I
  have hp₀₀ : p₀₀ ∈ ball c δ := mem_ball_self hδ
  have hp₁₀ : p₁₀ ∈ ball c δ := by
    simp only [p₁₀, mem_ball, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε]
    dsimp [ε]; linarith
  have hp₀₁ : p₀₁ ∈ ball c δ := by
    simp only [p₀₁, mem_ball, dist_self_add_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos hε]
    dsimp [ε]; linarith
  have hp₁₁ : p₁₁ ∈ ball c δ := by
    have hp₁₁_sub : p₁₁ - c = (ε : ℂ) + ε * Complex.I := by dsimp [p₁₁]; ring
    rw [mem_ball, dist_eq_norm, hp₁₁_sub]
    calc
      ‖(ε : ℂ) + ε * Complex.I‖ ≤ ‖(ε : ℂ)‖ + ‖ε * Complex.I‖ := norm_add_le _ _
      _ = ε + ε := by simp [abs_of_pos hε]
      _ < δ := by dsimp [ε]; linarith
  have seg_ftc {a b : ℂ} (ha : a ∈ ball c δ) (hb : b ∈ ball c δ) :
      ∫ᶜ z in .segment a b, φ z = g b - g a := by
    have hmem : ∀ t, Path.segment a b t ∈ ball c δ :=
      range_subset_iff.mp (Path.range_segment a b ▸ (convex_ball c δ).segment_subset ha hb)
    have hline_c1 : ContDiff ℝ 1 (AffineMap.lineMap a b : ℝ → ℂ) := by
      rw [funext (AffineMap.lineMap_apply_module a b)]
      fun_prop
    have hc1 : ContDiffOn ℝ 1 (Path.segment a b).extend I :=
      hline_c1.contDiffOn.congr (Path.eqOn_extend_segment a b)
    exact curveIntegral_eq_sub_of_hasFDerivAt hφ_cont.continuousOn hc1 hmem hg
  have h_bot : ∫ᶜ z in .segment p₀₀ p₁₀, φ z = 0 := by
    rw [curveIntegral_segment]
    have : (p₁₀ - p₀₀).im = 0 := by simp [p₁₀, p₀₀]
    simp [φ, this]
  have h_top : ∫ᶜ z in .segment p₀₁ p₁₁, φ z = 0 := by
    rw [curveIntegral_segment]
    have : (p₁₁ - p₀₁).im = 0 := by dsimp [p₁₁, p₀₁]; simp
    simp [φ, this]
  have h_left : ∫ᶜ z in .segment p₀₀ p₀₁, φ z = c.re * ε := by
    rw [curveIntegral_segment]
    have him : (p₀₁ - p₀₀).im = ε := by dsimp [p₀₁, p₀₀]; simp
    have hre (t : ℝ) : (AffineMap.lineMap p₀₀ p₀₁ t).re = c.re := by
      simp [AffineMap.lineMap_apply_module, p₀₀, p₀₁]
      ring
    simp [φ, him, hre]
  have h_right : ∫ᶜ z in .segment p₁₀ p₁₁, φ z = (c.re + ε) * ε := by
    rw [curveIntegral_segment]
    have him : (p₁₁ - p₁₀).im = ε := by
      have : p₁₁ - p₁₀ = ε * Complex.I := by dsimp [p₁₁, p₁₀]; ring
      simp [this]
    have hre (t : ℝ) : (AffineMap.lineMap p₁₀ p₁₁ t).re = c.re + ε := by
      simp [AffineMap.lineMap_apply_module, p₁₀, p₁₁]
      ring
    simp [φ, him, hre]
  rw [seg_ftc hp₀₀ hp₁₀] at h_bot
  rw [seg_ftc hp₀₁ hp₁₁] at h_top
  rw [seg_ftc hp₀₀ hp₀₁] at h_left
  rw [seg_ftc hp₁₀ hp₁₁] at h_right
  have hsq : ε ^ 2 = 0 := by linarith
  exact (pow_ne_zero 2 hε.ne') hsq

end NonConservativeExample

section AngularForm

/-- The punctured-plane angular `1`-form `dθ = Im(dz / z) = (x dy - y dx) / (x² + y²)`, defined as a
total map `ℂ → ℂ →L[ℝ] ℝ` with value `0` at `0`. -/
noncomputable def angularForm (z : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM.comp ((toSpanSingleton ℂ z⁻¹).restrictScalars ℝ)

/-- `angularForm z` is the composition of `Complex.imCLM` with real-scalar-restricted multiplication
by `z⁻¹`. -/
theorem angularForm_def (z : ℂ) :
    angularForm z = Complex.imCLM.comp ((toSpanSingleton ℂ z⁻¹).restrictScalars ℝ) := (rfl)

/-- Evaluates `angularForm z` on a tangent vector `v : ℂ` as `(v * z⁻¹).im`. -/
@[simp]
theorem angularForm_apply (z v : ℂ) : angularForm z v = (v * z⁻¹).im := by
  simp [angularForm]

/-- Explicit real-coordinate formula `(x v_y - y v_x) / (x² + y²)` for `angularForm z v`. -/
theorem angularForm_apply_re_im (z v : ℂ) :
    angularForm z v = (z.re * v.im - z.im * v.re) / Complex.normSq z := by
  simp only [angularForm_apply, Complex.inv_def, ← mul_assoc, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  ring

/-- `angularForm` has local potentials on `Complex.slitPlane`. -/
theorem hasLocalPotentials_angularForm_slitPlane :
    HasLocalPotentials Complex.slitPlane angularForm :=
  hasLocalPotentials_of_hasFDerivAt Complex.isOpen_slitPlane Complex.contDiffOn_arg
    fun z hz ↦ (angularForm_def z).symm ▸ Complex.hasFDerivAt_arg hz

/-- `angularForm` has local potentials on the punctured plane `{0}ᶜ : Set ℂ`. -/
theorem hasLocalPotentials_angularForm : HasLocalPotentials ({0}ᶜ : Set ℂ) angularForm := by
  -- Cover `{0}ᶜ` by `Complex.slitPlane` and its negation `(· * -1)⁻¹' slitPlane`.
  have hneg : HasLocalPotentials ((fun z : ℂ ↦ -z) ⁻¹' Complex.slitPlane) angularForm := by
    have hpull := hasLocalPotentials_angularForm_slitPlane.pullback
      (Complex.isOpen_slitPlane.preimage continuous_neg) contDiff_neg.contDiffOn
      (mapsTo_preimage _ _)
    refine hpull.congr fun z _ ↦ ?_
    ext v
    have hfderiv : fderiv ℝ (fun p : ℂ ↦ -p) z = -ContinuousLinearMap.id ℝ ℂ :=
      (hasFDerivAt_id z).neg.fderiv
    dsimp only
    rw [hfderiv, ContinuousLinearMap.comp_apply, _root_.neg_apply,
      ContinuousLinearMap.id_apply, angularForm_apply, angularForm_apply, inv_neg, neg_mul_neg]
  have hcov : ({0}ᶜ : Set ℂ) = Complex.slitPlane ∪ (fun z : ℂ ↦ -z) ⁻¹' Complex.slitPlane := by
    ext z
    simp only [mem_compl_iff, mem_singleton_iff, mem_union, mem_preimage]
    refine ⟨Complex.mem_slitPlane_or_neg_mem_slitPlane, fun h hz ↦ ?_⟩
    rcases h with h | h <;> simp [hz] at h
  rw [hcov, union_eq_iUnion]
  exact hasLocalPotentials_iUnion
    (Bool.forall_bool.mpr ⟨hneg, hasLocalPotentials_angularForm_slitPlane⟩)

/-- Counterclockwise parametrization `t ↦ exp(2π i t)` of the unit circle as a loop based at `1`. -/
noncomputable def unitCircleLoop : Path (1 : ℂ) 1 :=
  ((Path.segment (0 : ℂ) (2 * Real.pi * Complex.I)).map Complex.continuous_exp).cast
    Complex.exp_zero.symm Complex.exp_two_pi_mul_I.symm

/-- Explicit formula `unitCircleLoop t = exp(2π t i)`. -/
theorem unitCircleLoop_apply (t : I) :
    unitCircleLoop t = Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I) := by
  simp only [unitCircleLoop, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module, Complex.real_smul]
  congr 1
  ring

/-- `unitCircleLoop` stays in the punctured plane `{0}ᶜ`. -/
theorem unitCircleLoop_mem_compl_zero (t : I) : unitCircleLoop t ∈ ({0}ᶜ : Set ℂ) := by
  rw [mem_compl_iff, mem_singleton_iff, unitCircleLoop_apply]
  exact Complex.exp_ne_zero _

/-- The continuous path integral of `angularForm` once counterclockwise around the unit circle is
`2π`. -/
@[simp]
theorem localPotentialIntegral_angularForm_unitCircleLoop :
    localPotentialIntegral angularForm unitCircleLoop = 2 * Real.pi := by
  dsimp only [unitCircleLoop]
  rw [localPotentialIntegral_cast,
    ← hasLocalPotentials_angularForm.localPotentialIntegral_map Complex.contDiff_exp
      (Path.segment (0 : ℂ) (2 * Real.pi * Complex.I))
      (fun _ ↦ Complex.exp_ne_zero _)]
  have hpull : EqOn (fun w ↦ (angularForm (Complex.exp w)).comp (fderiv ℝ Complex.exp w))
      (fun _ ↦ Complex.imCLM) univ := by
    intro w _
    have hfderiv : fderiv ℝ Complex.exp w =
        (toSpanSingleton ℂ (Complex.exp w)).restrictScalars ℝ :=
      ((hasDerivAt_iff_hasFDerivAt_restrictScalars ℝ).mp (Complex.hasDerivAt_exp w)).fderiv
    ext v
    simp [hfderiv]
  rw [localPotentialIntegral_congr_of_isOpen isOpen_univ (fun _ ↦ mem_univ _) hpull,
    localPotentialIntegral_const]
  simp

/-- Reversing `unitCircleLoop` negates the path integral of `angularForm` to `-2π`. -/
theorem localPotentialIntegral_angularForm_unitCircleLoop_symm :
    localPotentialIntegral angularForm unitCircleLoop.symm = -(2 * Real.pi) := by
  simp

/-- Traversing `unitCircleLoop` twice yields path integral `4π`. -/
theorem localPotentialIntegral_angularForm_unitCircleLoop_trans :
    localPotentialIntegral angularForm (unitCircleLoop.trans unitCircleLoop) = 4 * Real.pi := by
  rw [hasLocalPotentials_angularForm.localPotentialIntegral_trans
    unitCircleLoop unitCircleLoop unitCircleLoop_mem_compl_zero unitCircleLoop_mem_compl_zero,
    localPotentialIntegral_angularForm_unitCircleLoop]
  ring

/-- The punctured-plane angular `1`-form admits no global potential on `{0}ᶜ : Set ℂ`, separating
`HasLocalPotentials` from global exactness. -/
theorem not_exists_hasFDerivAt_angularForm_compl_zero :
    ¬ ∃ g : ℂ → ℝ, ∀ z ∈ ({0}ᶜ : Set ℂ), HasFDerivAt g (angularForm z) z := by
  rintro ⟨g, hg⟩
  have hzero : localPotentialIntegral angularForm unitCircleLoop = 0 := by
    rw [localPotentialIntegral_eq_sub_of_hasFDerivAt isOpen_compl_singleton
      unitCircleLoop_mem_compl_zero hg, sub_self]
  rw [localPotentialIntegral_angularForm_unitCircleLoop] at hzero
  exact (mul_ne_zero two_ne_zero Real.pi_ne_zero) hzero

/-- The punctured complex plane `{0}ᶜ : Set ℂ` is not simply connected. -/
theorem not_isSimplyConnected_compl_zero : ¬ IsSimplyConnected ({0}ᶜ : Set ℂ) := by
  intro hsc
  obtain ⟨g, -, hg⟩ := hasLocalPotentials_angularForm.exists_hasFDerivAt_of_isSimplyConnected hsc
  exact not_exists_hasFDerivAt_angularForm_compl_zero ⟨g, hg⟩

end AngularForm

end TauCeti
