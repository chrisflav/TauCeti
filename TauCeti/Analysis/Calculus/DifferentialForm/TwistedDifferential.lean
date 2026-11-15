/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.DifferentialForm.Wedge
import TauCeti.Analysis.Normed.Module.Alternating.Basic
import TauCeti.LinearAlgebra.Complex.Determinant
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The twisted differential of a real function

Given an almost complex structure `J` on a finite-dimensional real normed space, or more generally
a varying continuous-linear endomorphism field `J : E → E →L[ℝ] E` on any real normed space, the
twisted differential of a real function `f` is the one-form `d^c_J f = -(1/2) df ∘ J`.

## Main definitions

* `TauCeti.AlmostComplexStructure.twistedDifferential J f`: the one-form `d^c_J f = -(1/2) df ∘ J`
  for a constant almost complex structure `J`.
* `TauCeti.twistedDifferentialForm J f`: the one-form `x ↦ -(1/2) df(x) ∘ J(x)` for a varying
  continuous-linear endomorphism field `J : E → E →L[ℝ] E` on any real normed space.

## Main results

* `TauCeti.AlmostComplexStructure.twistedDifferential_comp`, `TauCeti.twistedDifferentialForm_comp`:
  the chain rule `d^c_J (H ∘ f) = H'(f) • d^c_J f`.
* `TauCeti.twistedDifferentialForm_comp_of_comp_eq`: pullback naturality along a differentiable map
  intertwining two endomorphism fields.
* `TauCeti.AlmostComplexStructure.extDeriv_twistedDifferential_apply`: the second-derivative
  formula `d d^c_J f (v, w) = (D²f(w, J v) - D²f(v, J w)) / 2`.
* `TauCeti.AlmostComplexStructure.sum_extDeriv_twistedDifferential_apply_eq_laplacian`: for an
  orthogonal `J` and an orthonormal basis `(eᵢ)`, `∑ᵢ d d^c_J f (eᵢ, J eᵢ) = Δ f`. For the
  standard structure on `ℂ` this is `d d^c f = (Δ f / 2) dx ∧ dy`.
* `TauCeti.AlmostComplexStructure.integral_twistedDifferential_wedge_eq`,
  `Module.Basis.integral_twistedDifferentialForm_wedge_eq`: integration by parts.
  For a compactly supported form `η` of complementary degree and a varying `C¹` almost complex
  structure `J` on `tsupport η`, `∫ d^c_J g ∧ η = (1/2) ∫ g d((-J)^* η)`, where
  `((-J)^* η)(x)(v₁, …, vₘ) = η(x)(-J(x) v₁, …, -J(x) vₘ)` precomposes each value of `η` with
  `-J(x)` and `det(J(x)) = 1` because `J(x)² = -1`. The right side involves `g` and the first
  derivatives of `η` and `J`, but not `dg`.
* `TauCeti.AlmostComplexStructure.exists_abs_integral_twistedDifferential_wedge_le`,
  `Module.Basis.exists_abs_integral_twistedDifferentialForm_wedge_le`: the resulting bounds of
  `∫ d^c_J g ∧ η` in terms of `∫_K G`.
-/

public section

noncomputable section

open ContinuousAlternatingMap

namespace TauCeti.AlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (J : AlmostComplexStructure E)

/-- The twisted differential `d^c_J f = -(1/2) df ∘ J` of a real function `f`. -/
def twistedDifferential (f : E → ℝ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ofSubsingletonLIE (0 : Fin 1)
    ((-2⁻¹ : ℝ) • (fderiv ℝ f x).comp (LinearMap.toContinuousLinearMap J.toLinearMap))

/-- The twisted differential evaluated on a vector. -/
@[simp]
theorem twistedDifferential_apply (f : E → ℝ) (x : E) (v : Fin 1 → E) :
    J.twistedDifferential f x v = -2⁻¹ * fderiv ℝ f x (J (v 0)) := by
  simp [twistedDifferential]

/-- The twisted differential of a constant function vanishes. -/
@[simp]
theorem twistedDifferential_fun_const (c : ℝ) : J.twistedDifferential (fun _ ↦ c) = 0 := by
  ext x v
  simp

/-- The twisted differential of a constant function vanishes. -/
@[simp]
theorem twistedDifferential_const (c : ℝ) : J.twistedDifferential (Function.const E c) = 0 :=
  J.twistedDifferential_fun_const c

/-- The twisted differential of the zero function vanishes. -/
@[simp]
theorem twistedDifferential_zero : J.twistedDifferential (0 : E → ℝ) = 0 :=
  J.twistedDifferential_fun_const 0

/-- **Chain rule for the twisted differential.** If `H` has derivative `h'` at `f x`, then
`d^c_J (H ∘ f) = h' • d^c_J f` at `x`. -/
theorem twistedDifferential_comp {H : ℝ → ℝ} {h' : ℝ} {f : E → ℝ} {x : E}
    (hH : HasDerivAt H h' (f x)) (hf : DifferentiableAt ℝ f x) :
    J.twistedDifferential (H ∘ f) x = h' • J.twistedDifferential f x := by
  ext v
  simp [(hH.comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  ring

/-- The twisted differential is additive on functions differentiable at the point. -/
theorem twistedDifferential_add {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    J.twistedDifferential (f + g) x = J.twistedDifferential f x + J.twistedDifferential g x := by
  ext v
  simp [fderiv_add hf hg]
  ring

/-- The twisted differential commutes with scalar multiplication. -/
theorem twistedDifferential_const_smul (c : ℝ) (f : E → ℝ) (x : E) :
    J.twistedDifferential (c • f) x = c • J.twistedDifferential f x := by
  ext v
  simp [fderiv_const_smul_field]
  ring

/-- The twisted differential of a function that is `C^m` at a point is `C^n` at that point, for
`n + 1 ≤ m`. -/
theorem contDiffAt_twistedDifferential {m n : WithTop ℕ∞} {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ m f x) (hnm : n + 1 ≤ m) : ContDiffAt ℝ n (J.twistedDifferential f) x := by
  unfold twistedDifferential
  exact (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).contDiff.contDiffAt.comp x
    (((hf.fderiv_right hnm).clm_comp contDiffAt_const).const_smul _)

/-- The twisted differential of a `C^m` function is `C^n`, for `n + 1 ≤ m`. -/
theorem contDiff_twistedDifferential {m n : WithTop ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ m f)
    (hnm : n + 1 ≤ m) : ContDiff ℝ n (J.twistedDifferential f) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ J.contDiffAt_twistedDifferential hf.contDiffAt hnm

/-- **The exterior derivative of the twisted differential.**
`d d^c_J f (v, w) = (D²f(w, J v) - D²f(v, J w)) / 2`. -/
theorem extDeriv_twistedDifferential_apply (f : E → ℝ) (x v w : E) :
    extDeriv (J.twistedDifferential f) x ![v, w] =
      2⁻¹ * (fderiv ℝ (fderiv ℝ f) x w (J v) - fderiv ℝ (fderiv ℝ f) x v (J w)) := by
  by_cases hd : DifferentiableAt ℝ (fderiv ℝ f) x
  · have hω : DifferentiableAt ℝ (J.twistedDifferential f) x := by
      unfold twistedDifferential
      exact (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).differentiableAt.comp x
        ((hd.clm_comp (differentiableAt_const
          (LinearMap.toContinuousLinearMap J.toLinearMap))).const_smul (-2⁻¹ : ℝ))
    have hcoef (u : E) : (fun y ↦ J.twistedDifferential f y (fun _ ↦ u)) =
        fun y ↦ -2⁻¹ * fderiv ℝ f y (J u) := by
      funext y
      simp
    rw [extDeriv_apply_pair_of_differentiableAt hω, hcoef, hcoef,
      fderiv_const_mul (hd.clm_apply (differentiableAt_const _)),
      fderiv_const_mul (hd.clm_apply (differentiableAt_const _)),
      fderiv_clm_apply hd (differentiableAt_const _),
      fderiv_clm_apply hd (differentiableAt_const _)]
    simp
    ring
  · -- `df = 2 (d^c_J f) ∘ J`, so `d^c_J f` is not differentiable at `x` either.
    have hω : ¬DifferentiableAt ℝ (J.twistedDifferential f) x := fun hω ↦ hd <| by
      have hdf : fderiv ℝ f = fun y ↦ (2 : ℝ) • ((ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
          (0 : Fin 1)).symm (J.twistedDifferential f y)).comp
            (LinearMap.toContinuousLinearMap J.toLinearMap) := by
        funext y
        ext u
        simp [twistedDifferential, J.apply_apply]
      rw [hdf]
      exact (((ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).symm.differentiableAt.comp
        x hω).clm_comp (differentiableAt_const
          (LinearMap.toContinuousLinearMap J.toLinearMap))).const_smul (2 : ℝ)
    rw [extDeriv_apply_pair, fderiv_zero_of_not_differentiableAt hω,
      fderiv_zero_of_not_differentiableAt hd]
    simp

open MeasureTheory in
/-- **Integration by parts for the twisted differential.** For a C1 function `g` and a compactly
supported C1 form `η` of degree `m` on a space of dimension `1 + m`,
`∫ d^c_J g ∧ η = (det J / 2) ∫ g d((-J)^* η)`, the top-degree coefficients being taken on a basis
`b` and integrated against its Haar measure. Here `(-J)^* η` is the form
`x ↦ η(x)(-J v₁, …, -J vₘ)`, which precomposes each value of `η` with the inverse `-J` of `J` and
keeps the base point fixed. -/
theorem integral_twistedDifferential_wedge_eq [MeasurableSpace E] [BorelSpace E] {m : ℕ}
    (b : Module.Basis (Fin (1 + m)) ℝ E) {g : E → ℝ} {η : E → E [⋀^Fin m]→L[ℝ] ℝ}
    (hg : ContDiff ℝ 1 g) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    ∫ x, wedge (J.twistedDifferential g x) (η x) b ∂b.addHaar =
      LinearMap.det J.toLinearMap / 2 * ∫ x, g x * extDeriv
        (fun y ↦ (η y).compContinuousLinearMap (-LinearMap.toContinuousLinearMap J.toLinearMap)) x
        (b ∘ Fin.cast (by omega)) ∂b.addHaar := by
  set J' := LinearMap.toContinuousLinearMap J.toLinearMap
  set η' := fun y ↦ (η y).compContinuousLinearMap (-J')
  -- Pointwise, precomposing with `J` in the fibre turns `d^c_J g ∧ η` into `-(det J / 2) dg ∧ η'`.
  have hpt (x : E) : wedge (J.twistedDifferential g x) (η x) b =
      -(LinearMap.det J.toLinearMap / 2) *
        wedge (ofSubsingleton ℝ E ℝ (0 : Fin 1) (fderiv ℝ g x)) (η' x) b := by
    have h₁ : J.twistedDifferential g x = (-2⁻¹ : ℝ) •
        (ofSubsingleton ℝ E ℝ (0 : Fin 1) (fderiv ℝ g x)).compContinuousLinearMap J' := by
      ext v
      simp [J']
    have h₂ : η x = (η' x).compContinuousLinearMap J' := by
      ext v
      simp only [η', compContinuousLinearMap_apply]
      congr 1
      funext i
      simp [J', J.apply_apply]
    rw [h₁, h₂, wedge_smul_left, wedge_compContinuousLinearMap,
      ContinuousAlternatingMap.smul_apply, compContinuousLinearMap_apply_basis]
    simp [J']
    ring
  have hη' : ContDiff ℝ 1 η' :=
    (compContinuousLinearMapCLM (F := ℝ) (ι := Fin m) (-J')).contDiff.comp hη
  have hcη' : HasCompactSupport η' := hc.mono fun x hx h ↦ hx (by ext; simp [η', h])
  have hg' : ContDiff ℝ 1 fun x ↦ constOfIsEmpty ℝ E (Fin 0) (g x) :=
    (constOfIsEmptyLIE ℝ E ℝ (Fin 0)).contDiff.comp hg
  -- Integrate by parts the degree-zero form `g` against `η'`.
  have hibp := b.integral_extDeriv_wedge_eq_integral_wedge_extDeriv (by omega) hg' hη' hcη'
  simp only [extDeriv_constOfIsEmpty, wedge_def, pairedWedge_apply_zero_left] at hibp
  -- The index casts produced by the two wedges are the identity, up to the cast `m + 1 = 1 + m`.
  have e₁ : ⇑b ∘ Fin.cast (show 0 + 1 + m = 1 + m by omega) = ⇑b := rfl
  have e₂ : (⇑b ∘ Fin.cast (show 0 + (m + 1) = 1 + m by omega)) ∘
      Fin.cast (Nat.zero_add (m + 1)).symm = ⇑b ∘ Fin.cast (show m + 1 = 1 + m by omega) := rfl
  rw [e₁, e₂] at hibp
  simp only [ContinuousLinearMap.mul_apply', constOfIsEmpty_apply, pow_zero] at hibp
  simp only [hpt, integral_const_mul]
  simp only [wedge_def, hibp]
  ring

open MeasureTheory in
/-- The integral of `d^c_J g ∧ η`, for a C1 function `g` with `|g| ≤ G` on a compact set `K` and
a C1 form `η` supported in `K` with `‖Dη‖ ≤ A`, is at most a constant depending only on `J` and
the basis `b` times `A ∫_K G`. Integration by parts moves the derivative from `g` onto `η`. -/
theorem exists_abs_integral_twistedDifferential_wedge_le [MeasurableSpace E] [BorelSpace E]
    {m : ℕ} (b : Module.Basis (Fin (1 + m)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃g : E → ℝ⦄ ⦃η : E → E [⋀^Fin m]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃G : E → ℝ⦄
      ⦃A : ℝ⦄, ContDiff ℝ 1 g → ContDiff ℝ 1 η → IsCompact K → tsupport η ⊆ K →
      IntegrableOn G K b.addHaar → (∀ x ∈ K, |g x| ≤ G x) → (∀ x, ‖fderiv ℝ η x‖ ≤ A) →
      |∫ x, wedge (J.twistedDifferential g x) (η x) b ∂b.addHaar| ≤
        C * (A * ∫ x in K, G x ∂b.addHaar) := by
  let J' := LinearMap.toContinuousLinearMap J.toLinearMap
  let L := compContinuousLinearMapCLM (F := ℝ) (ι := Fin m) (-J')
  let b' := ⇑b ∘ Fin.cast (show m + 1 = 1 + m by omega)
  refine ⟨|LinearMap.det J.toLinearMap| / 2 * ((m + 1) * ‖L‖ * ∏ i, ‖b' i‖), by positivity, ?_⟩
  intro g η K G A hg hη hK hηK hG hgG hηA
  have hDη0 (x) (hx : x ∉ K) : fderiv ℝ η x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hηK (tsupport_fderiv_subset ℝ h))
  rw [J.integral_twistedDifferential_wedge_eq b hg hη
    (hK.of_isClosed_subset (isClosed_tsupport η) hηK)]
  set η' := fun y ↦ (η y).compContinuousLinearMap (-J')
  have hDη' (x : E) : fderiv ℝ η' x = L.comp (fderiv ℝ η x) :=
    (L.hasFDerivAt.comp x (hη.differentiable one_ne_zero x).hasFDerivAt).fderiv
  have hnorm (x : E) : ‖extDeriv η' x‖ ≤ (m + 1) * ‖L‖ * A :=
    calc ‖extDeriv η' x‖ ≤ (m + 1) * ‖fderiv ℝ η' x‖ := norm_alternatizeUncurryFin_le _
      _ ≤ (m + 1) * (‖L‖ * A) := by
          rw [hDη']
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact hηA x)
      _ = _ := by ring
  have hvan (x : E) (hx : x ∉ K) : g x * extDeriv η' x b' = 0 := by
    simp [extDeriv, hDη', hDη0 x hx, ← alternatizeUncurryFinCLM_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, abs_mul, abs_div, abs_two]
  calc |LinearMap.det J.toLinearMap| / 2 * |∫ x in K, g x * extDeriv η' x b' ∂b.addHaar|
      ≤ |LinearMap.det J.toLinearMap| / 2 *
          ∫ x in K, (m + 1) * ‖L‖ * A * (∏ i, ‖b' i‖) * G x ∂b.addHaar := by
        gcongr
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (hG.const_mul _)
          (ae_restrict_of_forall_mem hK.measurableSet fun x hx ↦ ?_)
        have hD : |extDeriv η' x b'| ≤ (m + 1) * ‖L‖ * A * ∏ i, ‖b' i‖ := by
          rw [← Real.norm_eq_abs]
          exact ((extDeriv η' x).le_opNorm b').trans (by gcongr; exact hnorm x)
        rw [Real.norm_eq_abs, abs_mul, mul_comm _ (G x)]
        exact mul_le_mul (hgG x hx) hD (abs_nonneg _) ((abs_nonneg _).trans (hgG x hx))
    _ = _ := by
        rw [integral_const_mul]
        ring

/-! ### The Laplacian as the `J`-trace of `d d^c_J` -/

section Laplacian

open InnerProductSpace Laplacian
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The `J`-trace of `d d^c_J f` is the Laplacian of `f`.** For an orthogonal almost complex
structure `J` and an orthonormal basis `(eᵢ)`, `∑ᵢ d d^c_J f (eᵢ, J eᵢ) = Δ f`. Each term is
`(D²f(eᵢ, eᵢ) + D²f(J eᵢ, J eᵢ)) / 2`, and `(J eᵢ)` is again an orthonormal basis. -/
theorem sum_extDeriv_twistedDifferential_apply_eq_laplacian (J : AlmostComplexStructure V)
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (f : V → ℝ) (x : V)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V) :
    ∑ i, extDeriv (J.twistedDifferential f) x ![e i, J (e i)] = Δ f x := by
  have hΔ := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f e) x
  have hΔJ := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (e.map (J.linearEquiv.isometryOfInner hJ))) x
  simp only [iteratedFDeriv_two_apply, OrthonormalBasis.map_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hΔ hΔJ
  have hJe (v : V) : J.linearEquiv.isometryOfInner hJ v = J v :=
    congrFun (LinearEquiv.coe_isometryOfInner J.linearEquiv hJ) v
  simp only [hJe] at hΔJ
  simp only [J.extDeriv_twistedDifferential_apply, J.apply_apply, map_neg]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← hΔJ, hΔ]
  simp only [Finset.sum_neg_distrib]
  ring

end Laplacian

end TauCeti.AlmostComplexStructure

/-! ### Varying endomorphism fields -/

namespace TauCeti

open Filter MeasureTheory Set Topology

section Varying

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The twisted differential for a varying endomorphism field.** Given `J : E → E →L[ℝ] E` on
any real normed space and `f : E → ℝ`, the one-form `d^c_J f (x) = -(1/2) df(x) ∘ J(x)`. -/
def twistedDifferentialForm (J : E → E →L[ℝ] E) (f : E → ℝ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ofSubsingletonLIE (0 : Fin 1) ((-2⁻¹ : ℝ) • (fderiv ℝ f x).comp (J x))

/-- Pointwise evaluation of `twistedDifferentialForm`. -/
@[simp]
theorem twistedDifferentialForm_apply (J : E → E →L[ℝ] E) (f : E → ℝ) (x : E) (v : Fin 1 → E) :
    twistedDifferentialForm J f x v = -2⁻¹ * fderiv ℝ f x (J x (v 0)) := by
  simp [twistedDifferentialForm]

/-- The twisted differential of a constant function vanishes. -/
@[simp]
theorem twistedDifferentialForm_fun_const (J : E → E →L[ℝ] E) (c : ℝ) :
    twistedDifferentialForm J (fun _ ↦ c) = 0 := by
  ext x v
  simp

/-- The twisted differential of `Function.const` vanishes. -/
@[simp]
theorem twistedDifferentialForm_const (J : E → E →L[ℝ] E) (c : ℝ) :
    twistedDifferentialForm J (Function.const E c) = 0 :=
  twistedDifferentialForm_fun_const J c

/-- The twisted differential of the zero function vanishes. -/
@[simp]
theorem twistedDifferentialForm_zero (J : E → E →L[ℝ] E) :
    twistedDifferentialForm J (0 : E → ℝ) = 0 :=
  twistedDifferentialForm_fun_const J 0

/-- A constant `AlmostComplexStructure` gives a special case of `twistedDifferentialForm`. -/
theorem AlmostComplexStructure.twistedDifferential_eq_twistedDifferentialForm
    [FiniteDimensional ℝ E] (J : AlmostComplexStructure E) (f : E → ℝ) :
    J.twistedDifferential f =
      twistedDifferentialForm (fun _ ↦ LinearMap.toContinuousLinearMap J.toLinearMap) f := by
  funext x
  ext v
  simp

/-- **Chain rule for `twistedDifferentialForm`.** If `H` has derivative `h'` at `f x`, then
`d^c_J (H ∘ f) x = h' • d^c_J f x`. -/
theorem twistedDifferentialForm_comp (J : E → E →L[ℝ] E) {H : ℝ → ℝ} {h' : ℝ} {f : E → ℝ} {x : E}
    (hH : HasDerivAt H h' (f x)) (hf : DifferentiableAt ℝ f x) :
    twistedDifferentialForm J (H ∘ f) x = h' • twistedDifferentialForm J f x := by
  ext v
  simp [(hH.comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  ring

/-- `twistedDifferentialForm` is additive on functions differentiable at the point. -/
theorem twistedDifferentialForm_add (J : E → E →L[ℝ] E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    twistedDifferentialForm J (f + g) x =
      twistedDifferentialForm J f x + twistedDifferentialForm J g x := by
  ext v
  simp [fderiv_add hf hg]
  ring

/-- `twistedDifferentialForm` commutes with scalar multiplication. -/
theorem twistedDifferentialForm_const_smul (J : E → E →L[ℝ] E) (c : ℝ) (f : E → ℝ) (x : E) :
    twistedDifferentialForm J (c • f) x = c • twistedDifferentialForm J f x := by
  ext v
  simp [fderiv_const_smul_field]
  ring

/-- **Pullback naturality of `twistedDifferentialForm`.** If `φ : E → F` is differentiable at `x`,
`f : F → ℝ` is differentiable at `φ x`, and `Dφ(x)` intertwines `J₁(x)` with `J₂(φ x)`, then
`d^c_{J₁}(f ∘ φ)(x) = (Dφ(x))^* (d^c_{J₂} f (φ x))`. -/
theorem twistedDifferentialForm_comp_of_comp_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {J₁ : E → E →L[ℝ] E} {J₂ : F → F →L[ℝ] F} {φ : E → F} {f : F → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hf : DifferentiableAt ℝ f (φ x))
    (hJ : (fderiv ℝ φ x).comp (J₁ x) = (J₂ (φ x)).comp (fderiv ℝ φ x)) :
    twistedDifferentialForm J₁ (f ∘ φ) x =
      (twistedDifferentialForm J₂ f (φ x)).compContinuousLinearMap (fderiv ℝ φ x) := by
  ext v
  have hchain : fderiv ℝ (f ∘ φ) x = (fderiv ℝ f (φ x)).comp (fderiv ℝ φ x) :=
    fderiv_comp x hf hφ
  have hv : (fderiv ℝ φ x) (J₁ x (v 0)) = J₂ (φ x) (fderiv ℝ φ x (v 0)) :=
    congrArg (fun L : E →L[ℝ] F ↦ L (v 0)) hJ
  simp only [twistedDifferentialForm_apply, compContinuousLinearMap_apply, hchain,
    ContinuousLinearMap.comp_apply, Function.comp_apply, hv]

/-- `twistedDifferentialForm J f` is `C^n` at `x` when `f` is `C^m` at `x` (`n + 1 ≤ m`) and `J`
is `C^n` at `x`. -/
theorem contDiffAt_twistedDifferentialForm {m n : WithTop ℕ∞} {J : E → E →L[ℝ] E} {f : E → ℝ}
    {x : E} (hf : ContDiffAt ℝ m f x) (hJ : ContDiffAt ℝ n J x) (hnm : n + 1 ≤ m) :
    ContDiffAt ℝ n (twistedDifferentialForm J f) x := by
  unfold twistedDifferentialForm
  exact (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).contDiff.contDiffAt.comp x
    (((hf.fderiv_right hnm).clm_comp hJ).const_smul _)

private theorem contDiff_pullback_neg {m : ℕ} {η : E → E [⋀^Fin m]→L[ℝ] ℝ} {J : E → E →L[ℝ] E}
    (hη : ContDiff ℝ 1 η) (hJ : ∀ x ∈ tsupport η, ContDiffAt ℝ 1 J x) :
    ContDiff ℝ 1 fun y ↦ (η y).compContinuousLinearMap (-J y) := by
  let : NormedAddCommGroup ((E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin m]→L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ ((E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin m]→L[ℝ] ℝ) := inferInstance
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  by_cases hx : x ∈ tsupport η
  · have hC : ContDiffAt ℝ 1
        (fun y ↦ (compContinuousLinearMapCLM (-J y) :
          (E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin m]→L[ℝ] ℝ)) x :=
      (contDiff_compContinuousLinearMapCLM 1).contDiffAt.comp x (hJ x hx).neg
    exact hC.clm_apply hη.contDiffAt
  · refine (contDiffAt_const (c := (0 : E [⋀^Fin m]→L[ℝ] ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
    ext v
    simp [image_eq_zero_of_notMem_tsupport hy]

private theorem norm_extDeriv_pullback_neg_le {m : ℕ} {η : E → E [⋀^Fin m]→L[ℝ] ℝ}
    {J : E → E →L[ℝ] E} {K : Set E} {M₀ M₁ A₁ A₂ : ℝ} (hη : ContDiff ℝ 1 η)
    (hηK : tsupport η ⊆ K) (hJ : ∀ x ∈ K, ContDiffAt ℝ 1 J x) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hJ₀ : ∀ x ∈ K, ‖J x‖ ≤ M₀)
    (hJ₁ : ∀ x ∈ K, ‖fderiv ℝ J x‖ ≤ M₁) (hη₁ : ∀ x ∈ K, ‖η x‖ ≤ A₁)
    (hη₂ : ∀ x ∈ K, ‖fderiv ℝ η x‖ ≤ A₂) (x : E) :
    ‖extDeriv (fun y ↦ (η y).compContinuousLinearMap (-J y)) x‖ ≤
      (m + 1) * (M₀ ^ m * A₂ + m * M₀ ^ (m - 1) * M₁ * A₁) := by
  set η' := fun y ↦ (η y).compContinuousLinearMap (-J y)
  by_cases hx : x ∈ tsupport η
  · have hxK : x ∈ K := hηK hx
    have hfderiv : fderiv ℝ η' x =
        compContinuousLinearMapCLM (-J x) ∘L fderiv ℝ η x +
          (η x).fderivCompContinuousLinearMap (-J x) ∘L fderiv ℝ (fun y ↦ -J y) x :=
      fderiv_continuousAlternatingMapCompContinuousLinearMap (hη.differentiable one_ne_zero x)
        (((hJ x hxK).differentiableAt one_ne_zero).neg)
    have h₁ : ‖compContinuousLinearMapCLM (-J x) ∘L fderiv ℝ η x‖ ≤ M₀ ^ m * A₂ := by
      calc ‖compContinuousLinearMapCLM (-J x) ∘L fderiv ℝ η x‖
          ≤ ‖-J x‖ ^ Fintype.card (Fin m) * ‖fderiv ℝ η x‖ :=
            (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_compContinuousLinearMapCLM_le (-J x))
                (ContinuousLinearMap.opNorm_nonneg _))
        _ ≤ M₀ ^ m * A₂ := by
            rw [Fintype.card_fin, norm_neg]
            exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hJ₀ x hxK) m) (hη₂ x hxK)
              (ContinuousLinearMap.opNorm_nonneg _) (pow_nonneg hM₀ m)
    have h₂ : ‖(η x).fderivCompContinuousLinearMap (-J x) ∘L fderiv ℝ (fun y ↦ -J y) x‖ ≤
        m * M₀ ^ (m - 1) * M₁ * A₁ := by
      have hdfJ : ‖fderiv ℝ (fun y ↦ -J y) x‖ ≤ M₁ := by
        rw [fderiv_fun_neg, ContinuousLinearMap.opNorm_neg]; exact hJ₁ x hxK
      calc ‖(η x).fderivCompContinuousLinearMap (-J x) ∘L fderiv ℝ (fun y ↦ -J y) x‖
          ≤ (Fintype.card (Fin m) * ‖-J x‖ ^ (Fintype.card (Fin m) - 1) * ‖η x‖) * M₁ :=
            (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
              ((η x).norm_fderivCompContinuousLinearMap_le (-J x)) hdfJ
              (ContinuousLinearMap.opNorm_nonneg _) (by positivity))
        _ ≤ (m * M₀ ^ (m - 1) * A₁) * M₁ := by
            rw [Fintype.card_fin, norm_neg]; gcongr; exacts [hJ₀ x hxK, hη₁ x hxK]
        _ = m * M₀ ^ (m - 1) * M₁ * A₁ := by ring
    calc ‖extDeriv η' x‖ ≤ (m + 1) * ‖fderiv ℝ η' x‖ := norm_alternatizeUncurryFin_le _
      _ ≤ (m + 1) * (M₀ ^ m * A₂ + m * M₀ ^ (m - 1) * M₁ * A₁) := by
          gcongr; rw [hfderiv]; exact (norm_add_le _ _).trans (add_le_add h₁ h₂)
  · have h0 : η' =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
      ext v
      simp [η', image_eq_zero_of_notMem_tsupport hy]
    rw [h0.extDeriv_eq, Pi.zero_def, extDeriv, fderiv_const_apply 0,
      ← alternatizeUncurryFinCLM_apply, ContinuousLinearMap.map_zero, norm_zero]
    positivity

private theorem extDeriv_eq_zero_of_eventuallyEq_zero {k : ℕ} {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} {x : E}
    (h : ω =ᶠ[𝓝 x] 0) : extDeriv ω x = 0 := by
  rw [h.extDeriv_eq, Pi.zero_def, extDeriv, fderiv_const_apply 0, ← alternatizeUncurryFinCLM_apply,
    ContinuousLinearMap.map_zero]

private theorem wedge_twistedDifferentialForm_eq {m : ℕ} (b : Module.Basis (Fin (1 + m)) ℝ E)
    {J : E → E →L[ℝ] E} {g : E → ℝ} {η : E → E [⋀^Fin m]→L[ℝ] ℝ}
    (hg : ∀ x ∈ tsupport η, ContDiffAt ℝ 1 g x) (hη : ContDiff ℝ 1 η)
    (hJ : ∀ x ∈ tsupport η, ContDiffAt ℝ 1 J x) (hJsq : ∀ x ∈ tsupport η, ∀ v, J x (J x v) = -v)
    (x : E) :
    wedge (twistedDifferentialForm J g x) (η x) b =
      -2⁻¹ * extDeriv (fun y ↦ wedge (constOfIsEmpty ℝ E (Fin 0) (g y))
          ((η y).compContinuousLinearMap (-J y))) x (b ∘ Fin.cast (by omega)) +
        2⁻¹ * (g x * extDeriv (fun y ↦ (η y).compContinuousLinearMap (-J y)) x
          (b ∘ Fin.cast (by omega))) := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  set η' := fun y ↦ (η y).compContinuousLinearMap (-J y)
  have hm₁ : m + 1 = 1 + m := by omega
  have hm₂ : 0 + m + 1 = 1 + m := by omega
  set b' := ⇑b ∘ Fin.cast hm₁
  have hη' : ContDiff ℝ 1 η' := contDiff_pullback_neg hη hJ
  by_cases hx : x ∈ tsupport η
  · have hdet : LinearMap.det (J x).toLinearMap = 1 :=
      LinearMap.det_eq_one_of_comp_self_eq_neg_id (LinearMap.ext (hJsq x hx))
    have h₁ : twistedDifferentialForm J g x =
        (-2⁻¹ : ℝ) • (ofSubsingleton ℝ E ℝ (0 : Fin 1) (fderiv ℝ g x)).compContinuousLinearMap
          (J x) := by ext v; simp
    have h₂ : η x = (η' x).compContinuousLinearMap (J x) := by
      ext v; simp only [η', compContinuousLinearMap_apply]; congr 1; funext i; simp [hJsq x hx]
    have hw : wedge (twistedDifferentialForm J g x) (η x) b =
        -2⁻¹ * wedge (ofSubsingleton ℝ E ℝ (0 : Fin 1) (fderiv ℝ g x)) (η' x) b := by
      rw [h₁, h₂, wedge_smul_left, wedge_compContinuousLinearMap,
        ContinuousAlternatingMap.smul_apply, compContinuousLinearMap_apply_basis, hdet, smul_eq_mul]
      ring
    have hdg : DifferentiableAt ℝ (fun y ↦ constOfIsEmpty ℝ E (Fin 0) (g y)) x :=
      (constOfIsEmptyLIE ℝ E ℝ (Fin 0)).differentiableAt.comp x
        ((hg x hx).differentiableAt one_ne_zero)
    have hL := extDeriv_pairedWedge (ContinuousLinearMap.mul ℝ ℝ) hdg
      (hη'.differentiable one_ne_zero x) (b ∘ Fin.cast hm₂)
    simp only [extDeriv_constOfIsEmpty, pairedWedge_apply_zero_left,
      ContinuousLinearMap.mul_apply', constOfIsEmpty_apply, pow_zero, one_smul] at hL
    have cast₁ : (⇑b ∘ Fin.cast hm₂) ∘ Fin.cast (by omega : 0 + 1 + m = 0 + m + 1) = ⇑b := rfl
    have cast₂ : ((⇑b ∘ Fin.cast hm₂) ∘ Fin.cast (by omega : 0 + (m + 1) = 0 + m + 1)) ∘
        Fin.cast (Nat.zero_add (m + 1)).symm = b' := rfl
    rw [cast₁, cast₂] at hL
    simp only [wedge_def] at hw ⊢
    rw [hw, hL]
    ring
  · have h0η' : η' =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
      ext v
      simp [η', image_eq_zero_of_notMem_tsupport hy]
    have h0ω : (fun y ↦ wedge (constOfIsEmpty ℝ E (Fin 0) (g y)) (η' y)) =ᶠ[𝓝 x] 0 :=
      h0η'.mono fun y hy ↦ by simp [hy, wedge_def]
    rw [image_eq_zero_of_notMem_tsupport hx, extDeriv_eq_zero_of_eventuallyEq_zero h0η',
      extDeriv_eq_zero_of_eventuallyEq_zero h0ω]
    simp [wedge_def]

/-- **Localized integration by parts for `twistedDifferentialForm`.** For a compactly supported
`C¹` `m`-form `η` on a real normed space with basis `b : Module.Basis (Fin (1 + m)) ℝ E`, a
function `g` that is `C¹` on `tsupport η`, and an endomorphism field `J` that is `C¹` and squares
to `-1` on `tsupport η`,
`∫ d^c_J g ∧ η = (1/2) ∫ g d((-J)^* η)`,
where `((-J)^* η)(y) = (η y).compContinuousLinearMap (-J y)` pulls `η y` back along `-J y` in each
fibre and `det(J x) = 1` because `J x` squares to `-id`. Neither `g` nor `J` need be smooth or
almost complex outside `tsupport η`. -/
theorem _root_.Module.Basis.integral_twistedDifferentialForm_wedge_eq [MeasurableSpace E]
    [BorelSpace E] {m : ℕ} (b : Module.Basis (Fin (1 + m)) ℝ E) {J : E → E →L[ℝ] E} {g : E → ℝ}
    {η : E → E [⋀^Fin m]→L[ℝ] ℝ} (hg : ∀ x ∈ tsupport η, ContDiffAt ℝ 1 g x) (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) (hJ : ∀ x ∈ tsupport η, ContDiffAt ℝ 1 J x)
    (hJsq : ∀ x ∈ tsupport η, ∀ v, J x (J x v) = -v) :
    ∫ x, wedge (twistedDifferentialForm J g x) (η x) b ∂b.addHaar =
      2⁻¹ * ∫ x, g x * extDeriv (fun y ↦ (η y).compContinuousLinearMap (-J y)) x
        (b ∘ Fin.cast (by omega)) ∂b.addHaar := by
  set η' := fun y ↦ (η y).compContinuousLinearMap (-J y)
  have hm₁ : m + 1 = 1 + m := by omega
  have hm₂ : 1 + m = (0 + m) + 1 := by omega
  set b' := ⇑b ∘ Fin.cast hm₁
  have hη' : ContDiff ℝ 1 η' := contDiff_pullback_neg hη hJ
  have hsubη' : tsupport η' ⊆ tsupport η :=
    closure_mono fun y hy h0 ↦ hy (by ext v; simp [η', h0])
  set ω := fun y ↦ wedge (constOfIsEmpty ℝ E (Fin 0) (g y)) (η' y)
  have hω : ContDiff ℝ 1 ω := by
    refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
    by_cases hx : x ∈ tsupport η
    · have hg₀ : ContDiffAt ℝ 1 (fun y ↦ constOfIsEmpty ℝ E (Fin 0) (g y)) x :=
        (constOfIsEmptyLIE ℝ E ℝ (Fin 0)).contDiff.contDiffAt.comp x (hg x hx)
      simpa only [ω, wedge_def] using contDiffAt_const.pairedWedge hg₀ hη'.contDiffAt
    · refine (contDiffAt_const (c := (0 : E [⋀^Fin (0 + m)]→L[ℝ] ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
      ext v
      simp [ω, η', image_eq_zero_of_notMem_tsupport hy, wedge_def]
  have hcω : HasCompactSupport ω :=
    (hc.mono fun y hy h0 ↦ hy (by ext v; simp [η', h0])).wedge_left
  let b'' : Module.Basis (Fin ((0 + m) + 1)) ℝ E := b.reindex (finCongr hm₂)
  have hb'' : b''.addHaar = b.addHaar := b.addHaar_reindex _
  have hb''_coe : ⇑b'' = ⇑b ∘ Fin.cast hm₂.symm := by ext i; simp [b'']
  obtain ⟨hint₁, hzero₁⟩ := b''.integral_extDeriv_eq_zero hω hcω
  rw [hb'', hb''_coe] at hint₁ hzero₁
  have hcont₂ : Continuous fun x ↦ g x * extDeriv η' x b' := by
    refine continuous_iff_continuousAt.2 fun x ↦ ?_
    by_cases hx : x ∈ tsupport η
    · exact (hg x hx).continuousAt.mul (continuousAt_extDeriv_apply hη'.contDiffAt b')
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
      have hy' : y ∉ tsupport (extDeriv η') := fun h ↦ hy (hsubη' (tsupport_extDeriv_subset h))
      simp [image_eq_zero_of_notMem_tsupport hy']
  have hc₂ : HasCompactSupport fun x ↦ g x * extDeriv η' x b' := by
    refine HasCompactSupport.of_support_subset_isCompact hc fun x hx ↦ ?_
    rw [Function.mem_support] at hx
    by_contra hxη
    have hx' : x ∉ tsupport (extDeriv η') := fun h ↦ hxη (hsubη' (tsupport_extDeriv_subset h))
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hx'])
  have hint₂ : Integrable (fun x ↦ g x * extDeriv η' x b') b.addHaar :=
    hcont₂.integrable_of_hasCompactSupport hc₂
  simp_rw [wedge_twistedDifferentialForm_eq b hg hη hJ hJsq]
  rw [integral_add (hint₁.const_mul _) (hint₂.const_mul _), integral_const_mul, integral_const_mul,
    hzero₁, mul_zero, zero_add]

/-- **Bound on `∫ d^c_J g ∧ η` for a varying `C¹` almost complex structure.** On a space with basis
`b : Module.Basis (Fin (1 + m)) ℝ E`, there is a constant `C ≥ 0` depending only on `b` such that
whenever `η` is a `C¹` `m`-form with `tsupport η ⊆ K` (`K` compact), `g` and `J` are `C¹` on `K`,
`J` squares to `-1` on `K`, `|g| ≤ G` on `K`, `‖J‖ ≤ M₀` and `‖DJ‖ ≤ M₁` on `K`, and `‖η‖ ≤ A₁`
and `‖Dη‖ ≤ A₂` on `K`,
`|∫ d^c_J g ∧ η| ≤ C * ((M₀ ^ m * A₂ + m * M₀ ^ (m - 1) * M₁ * A₁) * ∫_K G)`. -/
theorem _root_.Module.Basis.exists_abs_integral_twistedDifferentialForm_wedge_le
    [MeasurableSpace E] [BorelSpace E] {m : ℕ} (b : Module.Basis (Fin (1 + m)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃J : E → E →L[ℝ] E⦄ ⦃g : E → ℝ⦄ ⦃η : E → E [⋀^Fin m]→L[ℝ] ℝ⦄ ⦃K : Set E⦄
      ⦃G : E → ℝ⦄ ⦃M₀ M₁ A₁ A₂ : ℝ⦄,
      (∀ x ∈ K, ContDiffAt ℝ 1 g x) → ContDiff ℝ 1 η → IsCompact K → tsupport η ⊆ K →
      (∀ x ∈ K, ContDiffAt ℝ 1 J x) → (∀ x ∈ K, ∀ v, J x (J x v) = -v) →
      IntegrableOn G K b.addHaar → (∀ x ∈ K, |g x| ≤ G x) →
      (∀ x ∈ K, ‖J x‖ ≤ M₀) → (∀ x ∈ K, ‖fderiv ℝ J x‖ ≤ M₁) →
      (∀ x ∈ K, ‖η x‖ ≤ A₁) → (∀ x ∈ K, ‖fderiv ℝ η x‖ ≤ A₂) →
      |∫ x, wedge (twistedDifferentialForm J g x) (η x) b ∂b.addHaar| ≤
        C * ((M₀ ^ m * A₂ + m * M₀ ^ (m - 1) * M₁ * A₁) * ∫ x in K, G x ∂b.addHaar) := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  have hm₁ : m + 1 = 1 + m := by omega
  let b' := ⇑b ∘ Fin.cast hm₁
  refine ⟨2⁻¹ * ((m + 1) * ∏ i, ‖b' i‖), by positivity, ?_⟩
  intro J g η K G M₀ M₁ A₁ A₂ hg hη hK hηK hJ hJsq hG hgG hJ₀ hJ₁ hη₁ hη₂
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have hη0 : ∀ x, η x = 0 := fun x ↦
      image_eq_zero_of_notMem_tsupport fun hx ↦ hηK hx
    simp [hη0, wedge_def]
  have hM₀ : 0 ≤ M₀ := (norm_nonneg _).trans (hJ₀ x₀ hx₀)
  have hM₁ : 0 ≤ M₁ := (ContinuousLinearMap.opNorm_nonneg _).trans (hJ₁ x₀ hx₀)
  have hA₁ : 0 ≤ A₁ := (norm_nonneg _).trans (hη₁ x₀ hx₀)
  have hA₂ : 0 ≤ A₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hη₂ x₀ hx₀)
  have hcη : HasCompactSupport η := hK.of_isClosed_subset (isClosed_tsupport η) hηK
  rw [b.integral_twistedDifferentialForm_wedge_eq (fun x hx ↦ hg x (hηK hx)) hη hcη
    (fun x hx ↦ hJ x (hηK hx)) (fun x hx ↦ hJsq x (hηK hx))]
  set η' := fun y ↦ (η y).compContinuousLinearMap (-J y)
  have hvan (x : E) (hx : x ∉ K) : g x * extDeriv η' x b' = 0 := by
    have hxη : x ∉ tsupport η := fun h ↦ hx (hηK h)
    have h0 : η' =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hxη] with y hy
      ext v
      simp [η', image_eq_zero_of_notMem_tsupport hy]
    have hed : extDeriv η' x = 0 := by
      rw [h0.extDeriv_eq, Pi.zero_def, extDeriv, fderiv_const_apply 0,
        ← alternatizeUncurryFinCLM_apply, ContinuousLinearMap.map_zero]
    simp [hed]
  set B := M₀ ^ m * A₂ + m * M₀ ^ (m - 1) * M₁ * A₁
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)]
  calc 2⁻¹ * |∫ x in K, g x * extDeriv η' x b' ∂b.addHaar|
      ≤ 2⁻¹ * ∫ x in K, ((m + 1) * B * ∏ i, ‖b' i‖) * G x ∂b.addHaar := by
        gcongr
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (hG.const_mul _)
          (ae_restrict_of_forall_mem hK.measurableSet fun x hx ↦ ?_)
        have hD : |extDeriv η' x b'| ≤ (m + 1) * B * ∏ i, ‖b' i‖ := by
          rw [← Real.norm_eq_abs]
          exact ((extDeriv η' x).le_opNorm b').trans (mul_le_mul_of_nonneg_right
            (norm_extDeriv_pullback_neg_le hη hηK hJ hM₀ hM₁ hA₁ hA₂ hJ₀ hJ₁ hη₁ hη₂ x)
            (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))
        rw [Real.norm_eq_abs, abs_mul, mul_comm _ (G x)]
        exact mul_le_mul (hgG x hx) hD (abs_nonneg _) ((abs_nonneg _).trans (hgG x hx))
    _ = 2⁻¹ * ((m + 1) * ∏ i, ‖b' i‖) * (B * ∫ x in K, G x ∂b.addHaar) := by
        rw [integral_const_mul]
        ring

end Varying

end TauCeti
