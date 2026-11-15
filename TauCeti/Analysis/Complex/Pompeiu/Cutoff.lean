/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Cutoff Cauchy–Green representation of holomorphic functions

Let `f : ℂ → F` be complex differentiable on a set `U ⊆ ℂ` with values in a complex Banach space
`F`, and let `α : ℂ → ℂ` be compactly supported inside `interior U` and `C¹` on `U`. Extending
`α • f` by zero outside `tsupport α` produces a globally `C¹` map of compact support whose
conjugate Wirtinger derivative is `(\bar∂α) • f` everywhere on `ℂ`, regardless of the values of `f`
outside `U`. Applying the Cauchy–Pompeiu left inverse
(`HasCompactSupport.cauchyTransform_conjWirtingerDeriv`) recovers `α • f` as the Cauchy transform
of `(\bar∂α) • f`, which integrates only over
`tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1) ⊆ tsupport α ⊆ interior U`.

When `α = 1` on a neighborhood of a set `K ⊆ U`, the derivative support
`tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1)` is disjoint from `K`, and for every `ξ ∈ K` one
obtains the singularity-free kernel representation

`f ξ = π⁻¹ • ∫ ζ in tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1), (ξ - ζ)⁻¹ • (\bar∂α ζ • f ζ)`.

Discretizing this smooth integral over a compact collar is the analytic core of finite-rank Runge
approximation.

## Main results

* `TauCeti.tsupport_conjWirtingerDeriv_subset` and
  `TauCeti.disjoint_tsupport_conjWirtingerDeriv_of_subset_interior`: `\bar∂α` is supported inside
  `tsupport α` and has topological support disjoint from any set on a neighborhood of which `α` is
  constant.
* `TauCeti.conjWirtingerDeriv_smul_of_tsupport_subset`: if `f` is complex differentiable on `U` and
  `α` is real-differentiable on `U` with `tsupport α ⊆ interior U`, then
  `\bar∂(α • f) = (\bar∂α) • f` globally.
* `DifferentiableOn.contDiff_smul_of_tsupport_subset`: under `[CompleteSpace F]`, `α • f` is
  globally `C^k` over `ℝ` when `f` is holomorphic on `U` and `α` is `C^k` on `U` with
  `tsupport α ⊆ interior U`.
* `DifferentiableOn.smul_eq_cauchyTransform_conjWirtingerDeriv_smul` and
  `DifferentiableOn.smul_eq_setIntegral_conjWirtingerDeriv_smul`: global reproduction of `α • f`
  from `(\bar∂α) • f`.
* `DifferentiableOn.eq_cauchyTransform_conjWirtingerDeriv_smul_of_subset_interior`,
  `DifferentiableOn.eq_setIntegral_conjWirtingerDeriv_smul_of_subset_interior`, and
  `DifferentiableOn.eq_setIntegral_conjWirtingerDeriv_ofReal_smul_of_subset_interior`: exact
  reproduction of `f` on `K` when the cutoff equals `1` on a neighborhood of `K`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 10.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., §1.3.
-/

public noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace TauCeti

section SupportAndLeibniz

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The topological support of the conjugate Wirtinger derivative is contained in the topological
support of the map. -/
theorem tsupport_conjWirtingerDeriv_subset (α : V → W) :
    tsupport (fun z ↦ conjWirtingerDeriv α z) ⊆ tsupport α :=
  closure_minimal
    (fun _ hz ↦ by_contra fun hnot ↦ hz (conjWirtingerDeriv_of_notMem_tsupport hnot))
    (isClosed_tsupport α)

/-- In any fixed direction `v`, the topological support of `z ↦ conjWirtingerDeriv α z v` is
contained in `tsupport α`. -/
theorem tsupport_conjWirtingerDeriv_apply_subset (α : V → W) (v : V) :
    tsupport (fun z ↦ conjWirtingerDeriv α z v) ⊆ tsupport α :=
  closure_minimal
    (fun _ hz ↦ by_contra fun hnot ↦ hz (by simp [conjWirtingerDeriv_of_notMem_tsupport hnot]))
    (isClosed_tsupport α)

/-- If `α` takes a constant value `c` on a neighborhood of `K`, the topological support of its
conjugate Wirtinger derivative is disjoint from `K`. -/
theorem disjoint_tsupport_conjWirtingerDeriv_of_subset_interior {α : V → W} {K : Set V} {c : W}
    (hK : K ⊆ interior (α ⁻¹' {c})) :
    Disjoint (tsupport fun z ↦ conjWirtingerDeriv α z) K := by
  have hsub : tsupport (fun z ↦ conjWirtingerDeriv α z) ⊆ (interior (α ⁻¹' {c}))ᶜ := by
    refine closure_minimal (fun z hz hzO ↦ hz ?_) isOpen_interior.isClosed_compl
    have heq : α =ᶠ[𝓝 z] fun _ ↦ c :=
      eventuallyEq_iff_exists_mem.mpr ⟨interior (α ⁻¹' {c}), isOpen_interior.mem_nhds hzO,
        fun _ hw ↦ interior_subset hw⟩
    dsimp only
    rw [heq.conjWirtingerDeriv_eq]
    exact (differentiableAt_const c).conjWirtingerDeriv_eq_zero
  exact Disjoint.mono hsub hK disjoint_compl_left

/-- Directional form of `disjoint_tsupport_conjWirtingerDeriv_of_subset_interior`. -/
theorem disjoint_tsupport_conjWirtingerDeriv_apply_of_subset_interior {α : V → W} {K : Set V}
    {c : W} (hK : K ⊆ interior (α ⁻¹' {c})) (v : V) :
    Disjoint (tsupport fun z ↦ conjWirtingerDeriv α z v) K := by
  refine (disjoint_tsupport_conjWirtingerDeriv_of_subset_interior hK).mono_left ?_
  exact closure_minimal (fun _ hz ↦ subset_tsupport _ fun h0 ↦ hz (by simp [h0]))
    (isClosed_tsupport _)

/-- **Global Wirtinger cutoff identity.** If `f` is complex differentiable on `U` and `α` is
real-differentiable on `U` with `tsupport α ⊆ interior U`, then `\bar∂(α • f) = (\bar∂α) • f` holds
at every point of the ambient space, with no assumption on `f` outside `U`. -/
theorem conjWirtingerDeriv_smul_of_tsupport_subset {α : V → ℂ} {f : V → W} {U : Set V}
    (hf : DifferentiableOn ℂ f U) (hα : DifferentiableOn ℝ α U)
    (hαU : tsupport α ⊆ interior U) (z : V) (v : V) :
    conjWirtingerDeriv (fun w ↦ α w • f w) z v = conjWirtingerDeriv α z v • f z := by
  by_cases hz : z ∈ interior U
  · have hnhds : U ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
    have hf_at : DifferentiableAt ℂ f z := (hf z (interior_subset hz)).differentiableAt hnhds
    have hα_at : DifferentiableAt ℝ α z := (hα z (interior_subset hz)).differentiableAt hnhds
    rw [conjWirtingerDeriv_smul_apply hα_at (hf_at.restrictScalars ℝ) v,
      hf_at.conjWirtingerDeriv_eq_zero, zero_apply, smul_zero, zero_add]
  · have hnot : z ∉ tsupport α := fun h ↦ hz (hαU h)
    have hnot_smul : z ∉ tsupport (fun w ↦ α w • f w) := fun h ↦
      hnot (closure_minimal ((Function.support_smul_subset_left α f).trans (subset_tsupport α))
        (isClosed_tsupport α) h)
    simp [conjWirtingerDeriv_of_notMem_tsupport hnot_smul,
      conjWirtingerDeriv_of_notMem_tsupport hnot]

/-- Real-valued cutoff specialization of `conjWirtingerDeriv_smul_of_tsupport_subset`. -/
theorem conjWirtingerDeriv_real_smul_of_tsupport_subset {χ : V → ℝ} {f : V → W} {U : Set V}
    (hf : DifferentiableOn ℂ f U) (hχ : DifferentiableOn ℝ χ U)
    (hχU : tsupport χ ⊆ interior U) (z : V) (v : V) :
    conjWirtingerDeriv (fun w ↦ χ w • f w) z v =
      conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) z v • f z := by
  have hts : tsupport (fun w ↦ (χ w : ℂ)) ⊆ interior U := by
    refine (closure_minimal (fun w hw ↦ subset_tsupport χ ?_) (isClosed_tsupport χ)).trans hχU
    exact fun h0 ↦ hw (by simp [h0])
  simp_rw [← Complex.coe_smul]
  exact conjWirtingerDeriv_smul_of_tsupport_subset hf
    (Complex.ofRealCLM.differentiable.comp_differentiableOn hχ) hts z v

end SupportAndLeibniz

section CauchyGreenCutoff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {f : ℂ → F} {α : ℂ → ℂ} {χ : ℂ → ℝ} {U K : Set ℂ}

/-- Multiplying a map `f : ℂ → F` that is complex differentiable on `U` by a complex cutoff `α`
that is `C^k` over `ℝ` on `U` with `tsupport α ⊆ interior U` yields a globally `C^k` map on `ℂ`.
Outside `tsupport α` the product vanishes regardless of the values of `f`. -/
theorem _root_.DifferentiableOn.contDiff_smul_of_tsupport_subset {k : WithTop ℕ∞}
    (hf : DifferentiableOn ℂ f U) (hα : ContDiffOn ℝ k α U) (hαU : tsupport α ⊆ interior U) :
    ContDiff ℝ k (fun z ↦ α z • f z) :=
  ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F).flip).contDiff_of_tsupport_subset_right
    (((hf.mono interior_subset).contDiffOn isOpen_interior).restrict_scalars ℝ)
    (hα.mono interior_subset) isOpen_interior hαU

/-- **Holomorphic cutoff Cauchy–Green formula.** If `f : ℂ → F` is holomorphic on `U` and
`α : ℂ → ℂ` is compactly supported with `tsupport α ⊆ interior U` and `C¹` on `U`, then `α • f` is
the normalized Cauchy transform of `(\bar∂α) • f` at every point of `ℂ`. -/
theorem _root_.DifferentiableOn.smul_eq_cauchyTransform_conjWirtingerDeriv_smul
    (hf : DifferentiableOn ℂ f U) (hα : ContDiffOn ℝ 1 α U)
    (hαc : HasCompactSupport α) (hαU : tsupport α ⊆ interior U) (ξ : ℂ) :
    α ξ • f ξ = cauchyTransform (fun ζ ↦ conjWirtingerDeriv α ζ 1 • f ζ) ξ := by
  have hu_cd : ContDiff ℝ 1 (fun z ↦ α z • f z) :=
    hf.contDiff_smul_of_tsupport_subset hα hαU
  have hu_cs : HasCompactSupport (fun z ↦ α z • f z) :=
    HasCompactSupport.of_support_subset_isCompact hαc.isCompact
      ((Function.support_smul_subset_left α f).trans (subset_tsupport α))
  rw [← hu_cs.cauchyTransform_conjWirtingerDeriv hu_cd ξ]
  congr 1 with ζ
  exact conjWirtingerDeriv_smul_of_tsupport_subset hf (hα.differentiableOn one_ne_zero) hαU ζ 1

/-- Set-integral form of `DifferentiableOn.smul_eq_cauchyTransform_conjWirtingerDeriv_smul`,
restricted to the topological support of `ζ ↦ conjWirtingerDeriv α ζ 1`. -/
theorem _root_.DifferentiableOn.smul_eq_setIntegral_conjWirtingerDeriv_smul
    (hf : DifferentiableOn ℂ f U) (hα : ContDiffOn ℝ 1 α U)
    (hαc : HasCompactSupport α) (hαU : tsupport α ⊆ interior U) (ξ : ℂ) :
    α ξ • f ξ = (Real.pi : ℂ)⁻¹ •
      ∫ ζ in tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1),
        (ξ - ζ)⁻¹ • (conjWirtingerDeriv α ζ 1 • f ζ) := by
  rw [hf.smul_eq_cauchyTransform_conjWirtingerDeriv_smul hα hαc hαU ξ, cauchyTransform_apply,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro ζ hζ
  rw [image_eq_zero_of_notMem_tsupport hζ, zero_smul, smul_zero]

/-- When the cutoff `α` equals `1` on a neighborhood of `K`, `f` agrees on `K` with the Cauchy
transform of `(\bar∂α) • f`. -/
theorem _root_.DifferentiableOn.eq_cauchyTransform_conjWirtingerDeriv_smul_of_subset_interior
    (hf : DifferentiableOn ℂ f U) (hα : ContDiffOn ℝ 1 α U)
    (hαc : HasCompactSupport α) (hαU : tsupport α ⊆ interior U) (hK : K ⊆ interior (α ⁻¹' {1}))
    {ξ : ℂ} (hξ : ξ ∈ K) :
    f ξ = cauchyTransform (fun ζ ↦ conjWirtingerDeriv α ζ 1 • f ζ) ξ := by
  have h1 : α ξ = 1 := interior_subset (hK hξ)
  simpa only [h1, one_smul] using
    hf.smul_eq_cauchyTransform_conjWirtingerDeriv_smul hα hαc hαU ξ

/-- **Cutoff Cauchy–Green reproduction on `K`.** When `α` is compactly supported in `interior U`,
`C¹` on `U`, and equal to `1` on a neighborhood of `K`, every `f` holomorphic on `U` is represented
at `ξ ∈ K` by the integral of `(ξ - ζ)⁻¹ • (\bar∂α ζ • f ζ)` over the compact set
`tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1) ⊆ interior U \ K`. -/
theorem _root_.DifferentiableOn.eq_setIntegral_conjWirtingerDeriv_smul_of_subset_interior
    (hf : DifferentiableOn ℂ f U) (hα : ContDiffOn ℝ 1 α U)
    (hαc : HasCompactSupport α) (hαU : tsupport α ⊆ interior U) (hK : K ⊆ interior (α ⁻¹' {1}))
    {ξ : ℂ} (hξ : ξ ∈ K) :
    f ξ = (Real.pi : ℂ)⁻¹ •
      ∫ ζ in tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1),
        (ξ - ζ)⁻¹ • (conjWirtingerDeriv α ζ 1 • f ζ) := by
  have h1 : α ξ = 1 := interior_subset (hK hξ)
  simpa only [h1, one_smul] using
    hf.smul_eq_setIntegral_conjWirtingerDeriv_smul hα hαc hαU ξ

/-- Real-valued cutoff version of
`DifferentiableOn.eq_setIntegral_conjWirtingerDeriv_smul_of_subset_interior`, matching the smooth
cutoffs produced by `IsCompact.exists_contDiff_cutoff`. -/
theorem _root_.DifferentiableOn.eq_setIntegral_conjWirtingerDeriv_ofReal_smul_of_subset_interior
    (hf : DifferentiableOn ℂ f U) (hχ : ContDiffOn ℝ 1 χ U)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ interior U) (hK : K ⊆ interior (χ ⁻¹' {1}))
    {ξ : ℂ} (hξ : ξ ∈ K) :
    f ξ = (Real.pi : ℂ)⁻¹ •
      ∫ ζ in tsupport (fun ζ ↦ conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1),
        (ξ - ζ)⁻¹ • (conjWirtingerDeriv (fun w ↦ (χ w : ℂ)) ζ 1 • f ζ) := by
  have hα : ContDiffOn ℝ 1 (fun w ↦ (χ w : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hχ
  have hαc : HasCompactSupport (fun w ↦ (χ w : ℂ)) :=
    HasCompactSupport.of_support_subset_isCompact hχc.isCompact
      ((Function.support_comp_subset ofReal_zero χ).trans (subset_tsupport χ))
  have hαU : tsupport (fun w ↦ (χ w : ℂ)) ⊆ interior U :=
    (closure_minimal ((Function.support_comp_subset ofReal_zero χ).trans (subset_tsupport χ))
      (isClosed_tsupport χ)).trans hχU
  have hK' : K ⊆ interior ((fun w ↦ (χ w : ℂ)) ⁻¹' {1}) :=
    hK.trans (interior_mono fun _ hw ↦
      mem_preimage.mpr (mem_singleton_iff.mpr (ofReal_eq_one.mpr (mem_singleton_iff.mp hw))))
  exact hf.eq_setIntegral_conjWirtingerDeriv_smul_of_subset_interior hα hαc hαU hK' hξ

end CauchyGreenCutoff

end TauCeti
