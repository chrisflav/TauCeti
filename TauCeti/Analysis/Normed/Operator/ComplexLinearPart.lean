/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Complex-linear and complex-antilinear parts of bounded real-linear operators

Every continuous real-linear operator `L : M →L[ℝ] N` between complex seminormed spaces splits
canonically into a bounded complex-linear part and a bounded complex-antilinear part,
```
L.complexLinearPart v     = (L v - I • L (I • v)) / 2,
L.complexAntilinearPart v = (L v + I • L (I • v)) / 2,
```
each of operator norm at most `‖L‖`. These are the continuous-operator counterparts of
`TauCeti.complexLinearPart` and `TauCeti.complexAntilinearPart`, specialized to multiplication by
`Complex.I`. When `L = fderiv ℝ g x`, they coincide with the Wirtinger derivatives
`TauCeti.wirtingerDeriv g x` and `TauCeti.conjWirtingerDeriv g x`.

We also bundle the two projections as bounded real-linear endomorphisms
`ContinuousLinearMap.complexLinearPartCLM` and `ContinuousLinearMap.complexAntilinearPartCLM` of
`M →L[ℝ] N`, so that curried real-bilinear maps `E →L[ℝ] E' →L[ℝ] F` decompose into four bounded
pieces of types `(1, 0)` and `(0, 1)` in each variable.

## Main definitions

* `ContinuousLinearMap.complexLinearPart L`: the `(1, 0)` part of `L : M →L[ℝ] N`, bundled as
  `M →L[ℂ] N`.
* `ContinuousLinearMap.complexAntilinearPart L`: the `(0, 1)` part of `L : M →L[ℝ] N`, bundled as
  `M →L⋆[ℂ] N`.
* `ContinuousLinearMap.complexLinearPartCLM M N` and
  `ContinuousLinearMap.complexAntilinearPartCLM M N`: the two projections as continuous real-linear
  endomorphisms of `M →L[ℝ] N`.

## Main statements

* `ContinuousLinearMap.complexLinearPart_add_complexAntilinearPart` and
  `ContinuousLinearMap.apply_smul_eq_complexLinearPart_add_complexAntilinearPart`: `L = L¹⁰ + L⁰¹`
  and `L (z • v) = z • L¹⁰ v + conj z • L⁰¹ v`.
* `ContinuousLinearMap.norm_complexLinearPart_le` and
  `ContinuousLinearMap.norm_complexAntilinearPart_le`: both parts have operator norm at most `‖L‖`.
* `ContinuousLinearMap.complexLinearPart_eq_and_complexAntilinearPart_eq`: uniqueness of the
  `(1, 0) + (0, 1)` decomposition along a vector.
-/

public section

noncomputable section

open Complex ComplexConjugate

namespace ContinuousLinearMap

variable {M N : Type*} [SeminormedAddCommGroup M] [NormedSpace ℂ M]
  [SeminormedAddCommGroup N] [NormedSpace ℂ N]

/-- The **complex-linear part** `v ↦ (L v - I • L (I • v)) / 2` of a continuous real-linear map
`L : M →L[ℝ] N` between complex seminormed spaces, bundled as a continuous complex-linear map. -/
def complexLinearPart (L : M →L[ℝ] N) : M →L[ℂ] N where
  toFun v := (2 : ℂ)⁻¹ • (L v - I • L (I • v))
  map_add' v w := by simp only [smul_add, map_add]; module
  map_smul' c v := by
    rw [← re_smul_add_im_smul c v]
    simp only [smul_add, smul_comm I, smul_smul, I_mul_I, neg_smul, one_smul, map_add,
      map_smul, map_neg, RingHom.id_apply]
    match_scalars <;> apply Complex.ext <;> simp <;> ring
  cont := by fun_prop

/-- The **complex-antilinear part** `v ↦ (L v + I • L (I • v)) / 2` of a continuous real-linear map
`L : M →L[ℝ] N` between complex seminormed spaces, bundled as a continuous conjugate-linear map. -/
def complexAntilinearPart (L : M →L[ℝ] N) : M →L⋆[ℂ] N where
  toFun v := (2 : ℂ)⁻¹ • (L v + I • L (I • v))
  map_add' v w := by simp only [smul_add, map_add]; module
  map_smul' c v := by
    rw [← re_smul_add_im_smul c v]
    simp only [smul_add, smul_comm I, smul_smul, I_mul_I, neg_smul, one_smul, map_add,
      map_smul, map_neg, starRingEnd_apply]
    match_scalars <;> apply Complex.ext <;> simp <;> ring
  cont := by fun_prop

/-- The defining formula of `ContinuousLinearMap.complexLinearPart`. -/
theorem complexLinearPart_apply (L : M →L[ℝ] N) (v : M) :
    L.complexLinearPart v = (2 : ℂ)⁻¹ • (L v - I • L (I • v)) :=
  (rfl)

/-- The defining formula of `ContinuousLinearMap.complexAntilinearPart`. -/
theorem complexAntilinearPart_apply (L : M →L[ℝ] N) (v : M) :
    L.complexAntilinearPart v = (2 : ℂ)⁻¹ • (L v + I • L (I • v)) :=
  (rfl)

/-- `ContinuousLinearMap.complexLinearPart` agrees pointwise with `TauCeti.complexLinearPart` for
the complex structures given by multiplication by `I`. -/
theorem coe_complexLinearPart_eq_complexLinearPart (L : M →L[ℝ] N) :
    ⇑L.complexLinearPart =
      TauCeti.complexLinearPart (DistribSMul.toLinearMap ℝ M I) (DistribSMul.toLinearMap ℝ N I)
        (L : M →ₗ[ℝ] N) := by
  ext v
  simp only [complexLinearPart_apply, TauCeti.complexLinearPart_apply, coe_coe,
    DistribSMul.toLinearMap_apply]
  module

/-- `ContinuousLinearMap.complexAntilinearPart` agrees pointwise with
`TauCeti.complexAntilinearPart` for the complex structures given by multiplication by `I`. -/
theorem coe_complexAntilinearPart_eq_complexAntilinearPart (L : M →L[ℝ] N) :
    ⇑L.complexAntilinearPart =
      TauCeti.complexAntilinearPart (DistribSMul.toLinearMap ℝ M I) (DistribSMul.toLinearMap ℝ N I)
        (L : M →ₗ[ℝ] N) := by
  ext v
  simp only [complexAntilinearPart_apply, TauCeti.complexAntilinearPart_apply, coe_coe,
    DistribSMul.toLinearMap_apply]
  module

/-- A continuous real-linear map is the sum of its complex-linear and complex-antilinear parts. -/
@[simp]
theorem complexLinearPart_add_complexAntilinearPart (L : M →L[ℝ] N) (v : M) :
    L.complexLinearPart v + L.complexAntilinearPart v = L v := by
  rw [complexLinearPart_apply, complexAntilinearPart_apply]
  module

/-- Action of a continuous real-linear map on a complex scalar multiple `z • v` in terms of its
complex-linear and complex-antilinear parts. -/
theorem apply_smul_eq_complexLinearPart_add_complexAntilinearPart (L : M →L[ℝ] N) (z : ℂ) (v : M) :
    L (z • v) = z • L.complexLinearPart v + conj z • L.complexAntilinearPart v := by
  rw [← L.complexLinearPart.map_smul z v, ← L.complexAntilinearPart.map_smulₛₗ z v,
    complexLinearPart_add_complexAntilinearPart]

/-- The operator norm of `L.complexLinearPart` is at most `‖L‖`. -/
theorem norm_complexLinearPart_le (L : M →L[ℝ] N) : ‖L.complexLinearPart‖ ≤ ‖L‖ := by
  refine L.complexLinearPart.opNorm_le_bound (norm_nonneg L) fun v ↦ ?_
  rw [complexLinearPart_apply, norm_smul]
  have h1 : ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
  have h2 : ‖I • L (I • v)‖ ≤ ‖L‖ * ‖v‖ := by
    rw [norm_smul, norm_I, one_mul]
    exact (L.le_opNorm (I • v)).trans_eq (by rw [norm_smul, norm_I, one_mul])
  have hinv : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by simp
  rw [hinv]
  linarith [norm_sub_le (L v) (I • L (I • v))]

/-- The operator norm of `L.complexAntilinearPart` is at most `‖L‖`. -/
theorem norm_complexAntilinearPart_le (L : M →L[ℝ] N) : ‖L.complexAntilinearPart‖ ≤ ‖L‖ := by
  refine L.complexAntilinearPart.opNorm_le_bound (norm_nonneg L) fun v ↦ ?_
  rw [complexAntilinearPart_apply, norm_smul]
  have h1 : ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
  have h2 : ‖I • L (I • v)‖ ≤ ‖L‖ * ‖v‖ := by
    rw [norm_smul, norm_I, one_mul]
    exact (L.le_opNorm (I • v)).trans_eq (by rw [norm_smul, norm_I, one_mul])
  have hinv : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by simp
  rw [hinv]
  linarith [norm_add_le (L v) (I • L (I • v))]

/-- Uniqueness of the `(1, 0) + (0, 1)` decomposition along a vector `v`: if
`L (z • v) = z • a + conj z • b` for all `z : ℂ`, then `L.complexLinearPart v = a` and
`L.complexAntilinearPart v = b`. -/
theorem complexLinearPart_eq_and_complexAntilinearPart_eq {L : M →L[ℝ] N} {v : M} {a b : N}
    (h : ∀ z : ℂ, L (z • v) = z • a + conj z • b) :
    L.complexLinearPart v = a ∧ L.complexAntilinearPart v = b := by
  have h1 : L v = a + b := by simpa using h 1
  have hI : L (I • v) = I • a - I • b := by simpa [sub_eq_add_neg] using h I
  constructor
  · rw [complexLinearPart_apply, h1, hI]
    simp only [smul_sub, smul_smul, I_mul_I]
    module
  · rw [complexAntilinearPart_apply, h1, hI]
    simp only [smul_sub, smul_smul, I_mul_I]
    module

/-- Restricting scalars of a complex-linear operator and taking `complexLinearPart` recovers the
original operator. -/
@[simp]
theorem complexLinearPart_restrictScalars (L : M →L[ℂ] N) :
    (L.restrictScalars ℝ).complexLinearPart = L := by
  ext v
  exact (complexLinearPart_eq_and_complexAntilinearPart_eq (L := L.restrictScalars ℝ) (v := v)
    (a := L v) (b := 0) fun z ↦ by simp).1

/-- The complex-antilinear part of a complex-linear operator vanishes. -/
@[simp]
theorem complexAntilinearPart_restrictScalars (L : M →L[ℂ] N) :
    (L.restrictScalars ℝ).complexAntilinearPart = 0 := by
  ext v
  exact (complexLinearPart_eq_and_complexAntilinearPart_eq (L := L.restrictScalars ℝ) (v := v)
    (a := L v) (b := 0) fun z ↦ by simp).2

/-- Multiplication by `Complex.I` as a bounded real-linear operator of norm at most `1`. -/
private def smulICLM (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℂ E] : E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun v := I • v
      map_add' u v := smul_add I u v
      map_smul' r v := by simp [smul_comm I r v] }
    1 fun v ↦ by simp [norm_smul]

@[simp]
private theorem smulICLM_apply (v : M) : smulICLM M v = I • v :=
  (rfl)

/-- Projection onto the complex-linear part as a bounded real-linear operator on `M →L[ℝ] N`. -/
def complexLinearPartCLM (M N : Type*) [SeminormedAddCommGroup M] [NormedSpace ℂ M]
    [SeminormedAddCommGroup N] [NormedSpace ℂ N] : (M →L[ℝ] N) →L[ℝ] (M →L[ℝ] N) :=
  (2 : ℝ)⁻¹ • (.id ℝ (M →L[ℝ] N) -
    (compL ℝ M N N (smulICLM N)).comp (compL ℝ M M N |>.flip (smulICLM M)))

/-- Projection onto the complex-antilinear part as a bounded real-linear operator on `M →L[ℝ] N`. -/
def complexAntilinearPartCLM (M N : Type*) [SeminormedAddCommGroup M] [NormedSpace ℂ M]
    [SeminormedAddCommGroup N] [NormedSpace ℂ N] : (M →L[ℝ] N) →L[ℝ] (M →L[ℝ] N) :=
  (2 : ℝ)⁻¹ • (.id ℝ (M →L[ℝ] N) +
    (compL ℝ M N N (smulICLM N)).comp (compL ℝ M M N |>.flip (smulICLM M)))

@[simp]
theorem complexLinearPartCLM_apply_apply (L : M →L[ℝ] N) (v : M) :
    complexLinearPartCLM M N L v = L.complexLinearPart v := by
  simp only [complexLinearPartCLM, complexLinearPart_apply, smul_apply, sub_apply, id_apply,
    comp_apply, compL_apply, flip_apply, smulICLM_apply, ← coe_smul]
  push_cast
  rfl

@[simp]
theorem complexAntilinearPartCLM_apply_apply (L : M →L[ℝ] N) (v : M) :
    complexAntilinearPartCLM M N L v = L.complexAntilinearPart v := by
  simp only [complexAntilinearPartCLM, complexAntilinearPart_apply, smul_apply, add_apply,
    id_apply, comp_apply, compL_apply, flip_apply, smulICLM_apply, ← coe_smul]
  push_cast
  rfl

theorem norm_complexLinearPartCLM_apply_le (L : M →L[ℝ] N) :
    ‖complexLinearPartCLM M N L‖ ≤ ‖L‖ :=
  (complexLinearPartCLM M N L).opNorm_le_bound (norm_nonneg L) fun v ↦ by
    rw [complexLinearPartCLM_apply_apply]
    exact (L.complexLinearPart.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right L.norm_complexLinearPart_le (norm_nonneg v))

theorem norm_complexAntilinearPartCLM_apply_le (L : M →L[ℝ] N) :
    ‖complexAntilinearPartCLM M N L‖ ≤ ‖L‖ :=
  (complexAntilinearPartCLM M N L).opNorm_le_bound (norm_nonneg L) fun v ↦ by
    rw [complexAntilinearPartCLM_apply_apply]
    exact (L.complexAntilinearPart.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right L.norm_complexAntilinearPart_le (norm_nonneg v))

@[simp]
theorem complexLinearPartCLM_restrictScalars (L : M →L[ℂ] N) :
    complexLinearPartCLM M N (L.restrictScalars ℝ) = L.restrictScalars ℝ := by
  ext v
  simp

@[simp]
theorem complexAntilinearPartCLM_restrictScalars (L : M →L[ℂ] N) :
    complexAntilinearPartCLM M N (L.restrictScalars ℝ) = 0 := by
  ext v
  simp

end ContinuousLinearMap
