/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.Ideal
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import Mathlib.Topology.Algebra.Module.Star

/-!
# Positive contractive approximate identities in algebraic one-sided ideals

Every complex left ideal `L : Submodule ℂ A` (`∀ a : A, ∀ x ∈ L, a * x ∈ L`) of a (possibly
nonunital) complex C⋆-algebra `A` — **not assumed to be norm-closed** — admits an order-increasing
net of positive strict contractions inside `L` itself that acts as a right approximate identity on
`L`: `x * e i → x` for every `x ∈ L`.

Unlike the C⋆-subalgebra approximate-unit construction on `closure L`, which only places
approximants in the closure, the construction here works algebraically inside `L`. Indexed by pairs
`(F, δ)` with `F : Finset L` ordered by inclusion and `δ : (Set.Ioi (0 : ℝ))ᵒᵈ` ordered by
decreasing `δ > 0`, one sets
`b_F = ∑ x ∈ F, star (x : A) * (x : A) ∈ L` and
`e_{F,δ} = (b_F * (δ • 1 + b_F)⁻¹ʳ).snd` in `Unitization ℂ A`.
Commutativity of `b_F` with `(δ • 1 + b_F)⁻¹ʳ` in `A⁺¹` rewrites `e_{F,δ}` as
`((δ • 1 + b_F)⁻¹ʳ * b_F).snd`, which belongs to `L` via `Submodule.snd_mul_inr_mem` (corresponding
to the algebraic left action `Submodule.unitizationLeftAction` of `A⁺¹` on `L`), never invoking
topological closure. On positive elements `b` and `0 < δ`, `e_{F,δ}` agrees with
`cfcₙ (fun t : ℝ => t / (δ + t)) b_F`, yielding positivity, strict contractivity `‖e_{F,δ}‖ < 1`,
order monotonicity in `(F, δ)`, and for every `x ∈ F` the sharp quantitative bound
`‖x - x * e_{F,δ}‖ ^ 2 ≤ δ / 4`
coming from `star x * x ≤ b_F` and `sup_{t ≥ 0} δ ^ 2 * t / (δ + t) ^ 2 = δ / 4` (attained at
`t = δ`). Retaining the independent `δ > 0` coordinate ensures convergence even when `L` is
finite-dimensional or `L = ⊥` (where the net is identically `0`).

When `L` is norm-separable (`[TopologicalSpace.SeparableSpace L]`), taking initial segments of a
countable dense sequence in `L` together with `δ_n = 1 / (n + 1)` produces an increasing sequence
of positive strict contractions in `L` that right-approximates every element of `L`. Star duality
via `Submodule.comap (starLinearEquiv ℂ)` yields the corresponding positive contractive left
approximate identities (net and sequential) inside arbitrary, not necessarily closed, complex right
ideals. Finally, for a closed two-sided ideal `I : TwoSidedIdeal A`, the resulting filter on `I`
refines `CStarAlgebra.approximateUnit I` (cf. `CStarAlgebra.increasingApproximateUnit`), hence is an
`IsIncreasingApproximateUnit` of `I` and yields two-sided convergence on `I`.

## Main declarations

* `TauCeti.CStarAlgebra.sq_mul_div_add_sq_le` and
  `TauCeti.CStarAlgebra.isGreatest_sq_mul_div_add_sq`: the sharp scalar bound
  `δ ^ 2 * t / (δ + t) ^ 2 ≤ δ / 4` for `0 ≤ δ` and `t : ℝ`, attained at `t = δ`.
* `TauCeti.CStarAlgebra.resolventApprox`: the building block
  `((b : A⁺¹) * (δ • 1 + b)⁻¹ʳ).snd : A`, with unitization identities, `zero_resolventApprox`,
  algebraic ideal absorption, functional-calculus formulas `resolventApprox_eq_cfcₙ` and
  `resolventApprox_eq_cfcₙ_one_sub_inv`, positivity, strict norm bound `< 1`, joint monotonicity
  `resolventApprox_le_resolventApprox`, and sharp error estimates
  `norm_sub_mul_resolventApprox_sq_le` and `norm_sub_resolventApprox_mul_sq_le`.
* `Submodule.leftIdealSumSq` and `Submodule.rightApproxUnit`: the net `(F, δ) ↦ e_{F,δ}` on
  `Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ`, with `Submodule.rightApproxUnit_mem`,
  `Submodule.rightApproxUnit_mono`, `Submodule.norm_sub_mul_rightApproxUnit_sq_le`, and
  `Submodule.tendsto_mul_rightApproxUnit`.
* `Submodule.rightApproxUnitSeq` and `Submodule.exists_seq_rightApproxUnit`: sequential positive
  contractive right approximate identity inside a separable complex left ideal `L`.
* `Submodule.rightIdealSumSq`, `Submodule.leftApproxUnit`, `Submodule.tendsto_leftApproxUnit_mul`,
  `Submodule.leftApproxUnitSeq`, and `Submodule.exists_seq_leftApproxUnit`: right-ideal duals.
* `Ideal.rightApproxUnit_mem`, `Ideal.tendsto_mul_rightApproxUnit`, and
  `Ideal.exists_seq_rightApproxUnit`: specializations to algebraic left ideals `I : Ideal A` of a
  unital C⋆-algebra.
* `TwoSidedIdeal.approxUnit`, `TwoSidedIdeal.map_approxUnit_le_approximateUnit`,
  `TwoSidedIdeal.isIncreasingApproximateUnit_map_approxUnit`,
  `TwoSidedIdeal.tendsto_approxUnit_mul`, and `TwoSidedIdeal.tendsto_mul_approxUnit`: comparison
  with `CStarAlgebra.approximateUnit I` and two-sided convergence for closed two-sided ideals.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Proposition II.5.3.3 and Corollary II.5.3.13.
-/

public section

noncomputable section

open Filter Topology Unitization NNReal
open scoped CStarAlgebra Ring

namespace TauCeti.CStarAlgebra

/-! ### Sharp scalar estimate -/

/-- For `0 ≤ δ` and any `t : ℝ`, `δ ^ 2 * t / (δ + t) ^ 2 ≤ δ / 4`, with equality at `t = δ`. -/
theorem sq_mul_div_add_sq_le {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    δ ^ 2 * t / (δ + t) ^ 2 ≤ δ / 4 := by
  by_cases h : δ + t = 0
  · simp [h, div_nonneg hδ (by norm_num : (0 : ℝ) ≤ 4)]
  · have hpos : 0 < (δ + t) ^ 2 := sq_pos_of_ne_zero h
    rw [div_le_iff₀ hpos]
    have : δ * (δ + t) ^ 2 - δ ^ 2 * t * 4 = δ * (δ - t) ^ 2 := by ring
    linarith [mul_nonneg hδ (sq_nonneg (δ - t))]

/-- At `t = δ`, `δ ^ 2 * t / (δ + t) ^ 2` equals `δ / 4` for every `δ : ℝ`. -/
@[simp]
theorem sq_mul_div_add_sq_self (δ : ℝ) :
    δ ^ 2 * δ / (δ + δ) ^ 2 = δ / 4 := by
  by_cases hδ : δ = 0
  · simp [hδ]
  · field_simp
    ring

/-- For `0 ≤ δ`, the maximum of `t ↦ δ ^ 2 * t / (δ + t) ^ 2` over `t ≥ 0` is `δ / 4`, attained at
`t = δ`. -/
theorem isGreatest_sq_mul_div_add_sq {δ : ℝ} (hδ : 0 ≤ δ) :
    IsGreatest ((fun t : ℝ => δ ^ 2 * t / (δ + t) ^ 2) '' Set.Ici 0) (δ / 4) :=
  ⟨⟨δ, hδ, sq_mul_div_add_sq_self δ⟩,
    by rintro _ ⟨t, _, rfl⟩; exact sq_mul_div_add_sq_le hδ t⟩

/-! ### Resolvent approximant `b * (δ • 1 + b)⁻¹` in the unitization -/

section Algebraic

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The resolvent approximant `b * (δ • 1 + b)⁻¹` of `b : A` at parameter `δ : ℝ`, computed in the
unitization `A⁺¹ = Unitization ℂ A` via `Ring.inverse` and projected back to `A`. -/
def resolventApprox (δ : ℝ) (b : A) : A :=
  ((b : A⁺¹) * (δ • (1 : A⁺¹) + (b : A⁺¹))⁻¹ʳ).snd

/-- Unfolding formula for `resolventApprox`. -/
theorem resolventApprox_def (δ : ℝ) (b : A) :
    resolventApprox δ b = ((b : A⁺¹) * (δ • (1 : A⁺¹) + (b : A⁺¹))⁻¹ʳ).snd :=
  (rfl)

/-- At `b = 0`, `resolventApprox δ 0 = 0` for every `δ`. -/
@[simp]
theorem resolventApprox_zero (δ : ℝ) : resolventApprox δ (0 : A) = 0 := by
  simp [resolventApprox]

/-- At `δ = 0`, `resolventApprox 0 b = 0` for every `b : A`, since `(b : A⁺¹)` has zero scalar part
and is therefore never invertible in `A⁺¹`. -/
@[simp]
theorem zero_resolventApprox (b : A) : resolventApprox 0 b = 0 := by
  have hnu : ¬ IsUnit (b : A⁺¹) := by
    rintro ⟨u, hu⟩
    have hfst := congrArg (fun x : A⁺¹ => x.fst) u.val_inv
    rw [hu, Unitization.fst_inr_mul, Unitization.fst_one] at hfst
    exact zero_ne_one hfst
  rw [resolventApprox, zero_smul, zero_add, Ring.inverse_non_unit _ hnu, mul_zero, snd_zero]

/-- Embedding `resolventApprox δ b` into `A⁺¹` recovers `(b : A⁺¹) * (δ • 1 + b)⁻¹ʳ`. -/
@[simp]
theorem inr_resolventApprox (δ : ℝ) (b : A) :
    ((resolventApprox δ b : A) : A⁺¹) = (b : A⁺¹) * (δ • (1 : A⁺¹) + (b : A⁺¹))⁻¹ʳ :=
  Unitization.inr_snd_inr_mul b (δ • (1 : A⁺¹) + (b : A⁺¹))⁻¹ʳ

/-- In `A⁺¹`, `(b : A⁺¹)` commutes with `(δ • 1 + b)⁻¹ʳ`, so `resolventApprox δ b` also equals
`((δ • 1 + b)⁻¹ʳ * (b : A⁺¹)).snd`. -/
theorem inr_resolventApprox_eq_inv_mul (δ : ℝ) (b : A) :
    ((resolventApprox δ b : A) : A⁺¹) = (δ • (1 : A⁺¹) + (b : A⁺¹))⁻¹ʳ * (b : A⁺¹) := by
  rw [inr_resolventApprox]
  have hcomm : Commute (b : A⁺¹) (δ • (1 : A⁺¹) + (b : A⁺¹)) :=
    ((Commute.one_right (b : A⁺¹)).smul_right δ).add_right (Commute.refl (b : A⁺¹))
  by_cases hu : IsUnit (δ • (1 : A⁺¹) + (b : A⁺¹))
  · obtain ⟨u, hu⟩ := hu
    rw [← hu] at hcomm ⊢
    rw [Ring.inverse_unit]
    exact hcomm.units_inv_right.eq
  · rw [Ring.inverse_non_unit _ hu, mul_zero, zero_mul]

/-- `resolventApprox δ b` equals the `A`-coordinate of `(δ • 1 + b)⁻¹ʳ * (b : A⁺¹)`. -/
theorem resolventApprox_eq_snd_inv_mul (δ : ℝ) (b : A) :
    resolventApprox δ b = ((δ • (1 : A⁺¹) + (b : A⁺¹))⁻¹ʳ * (b : A⁺¹)).snd := by
  rw [← Unitization.snd_inr ℂ (resolventApprox δ b), inr_resolventApprox_eq_inv_mul]

/-- Algebraic left-ideal absorption: if `L : Submodule ℂ A` is closed under ambient left
multiplication and `b ∈ L`, then `resolventApprox δ b ∈ L`, without any closedness assumption on
`L`. -/
theorem resolventApprox_mem_of_mul_mem_left {L : Submodule ℂ A}
    (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) (δ : ℝ) {b : A} (hb : b ∈ L) :
    resolventApprox δ b ∈ L := by
  rw [resolventApprox_eq_snd_inv_mul]
  exact L.snd_mul_inr_mem hL (δ • (1 : A⁺¹) + (b : A⁺¹))⁻¹ʳ hb

/-- Algebraic right-ideal absorption: if `M : Submodule ℂ A` is closed under ambient right
multiplication and `b ∈ M`, then `resolventApprox δ b ∈ M`, without any closedness assumption on
`M`. -/
theorem resolventApprox_mem_of_mul_mem_right {M : Submodule ℂ A}
    (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M) (δ : ℝ) {b : A} (hb : b ∈ M) :
    resolventApprox δ b ∈ M :=
  M.snd_inr_mul_mem hM hb (δ • (1 : A⁺¹) + (b : A⁺¹))⁻¹ʳ

end Algebraic

section OrderAndNorm

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For `0 < δ` and `0 ≤ b`, `δ • 1 + (b : A⁺¹)` is invertible in `A⁺¹`. -/
theorem isUnit_smul_one_add_inr {δ : ℝ} (hδ : 0 < δ) {b : A} (hb : 0 ≤ b) :
    IsUnit (δ • (1 : A⁺¹) + (b : A⁺¹)) := by
  have hb' : 0 ≤ (b : A⁺¹) := Unitization.inr_nonneg_iff.mpr hb
  have hsa : IsSelfAdjoint (b : A⁺¹) := hb'.isSelfAdjoint
  rw [← Algebra.algebraMap_eq_smul_one, ← cfc_id' ℝ (b : A⁺¹),
    ← cfc_const_add δ (fun t : ℝ => t) (b : A⁺¹)]
  refine (cfcUnits (fun t : ℝ => δ + t) (b : A⁺¹) (fun t ht => ?_)).isUnit
  have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hb' ht
  linarith

/-- For `0 < δ` and `0 ≤ b`, `resolventApprox δ b` agrees with the nonunital continuous functional
calculus `cfcₙ (fun t : ℝ => t / (δ + t)) b`. -/
theorem resolventApprox_eq_cfcₙ {δ : ℝ} (hδ : 0 < δ) {b : A} (hb : 0 ≤ b) :
    resolventApprox δ b = cfcₙ (fun t : ℝ => t / (δ + t)) b := by
  have hb' : 0 ≤ (b : A⁺¹) := Unitization.inr_nonneg_iff.mpr hb
  have hsa : IsSelfAdjoint (b : A⁺¹) := hb'.isSelfAdjoint
  have hne : ∀ t ∈ spectrum ℝ (b : A⁺¹), δ + t ≠ 0 := fun t ht => by
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hb' ht
    linarith
  apply Unitization.inr_injective (R := ℂ)
  rw [inr_resolventApprox, Unitization.real_cfcₙ_eq_cfc_inr b (fun t : ℝ => t / (δ + t)) (by simp),
    cfc_map_div (fun t : ℝ => t) (fun t : ℝ => δ + t) (b : A⁺¹) hne,
    cfc_const_add δ (fun t : ℝ => t) (b : A⁺¹), cfc_id' ℝ (b : A⁺¹),
    Algebra.algebraMap_eq_smul_one]

/-- For `0 ≤ δ` and `0 ≤ b`, `resolventApprox δ b` is positive (`0 ≤ resolventApprox δ b`). -/
theorem resolventApprox_nonneg {δ : ℝ} (hδ : 0 ≤ δ) {b : A} (hb : 0 ≤ b) :
    0 ≤ resolventApprox δ b := by
  rcases hδ.eq_or_lt with rfl | hδ
  · simp
  · rw [resolventApprox_eq_cfcₙ hδ hb]
    refine cfcₙ_nonneg fun t ht => ?_
    have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg b hb t ht
    exact div_nonneg ht0 (by linarith)

/-- For `0 ≤ δ` and `0 ≤ b`, `resolventApprox δ b` is self-adjoint. -/
theorem isSelfAdjoint_resolventApprox {δ : ℝ} (hδ : 0 ≤ δ) {b : A} (hb : 0 ≤ b) :
    IsSelfAdjoint (resolventApprox δ b) :=
  (resolventApprox_nonneg hδ hb).isSelfAdjoint

/-- For `0 ≤ δ` and `0 ≤ b`, `star (resolventApprox δ b) = resolventApprox δ b`. -/
theorem star_resolventApprox {δ : ℝ} (hδ : 0 ≤ δ) {b : A} (hb : 0 ≤ b) :
    star (resolventApprox δ b) = resolventApprox δ b :=
  (isSelfAdjoint_resolventApprox hδ hb).star_eq

/-- For `0 ≤ δ` and `0 ≤ b`, `resolventApprox δ b` is a strict contraction
(`‖resolventApprox δ b‖ < 1`). -/
theorem norm_resolventApprox_lt_one {δ : ℝ} (hδ : 0 ≤ δ) {b : A} (hb : 0 ≤ b) :
    ‖resolventApprox δ b‖ < 1 := by
  rcases hδ.eq_or_lt with rfl | hδ
  · simp
  · rw [resolventApprox_eq_cfcₙ hδ hb]
    refine norm_cfcₙ_lt fun t ht => ?_
    have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg b hb t ht
    have hdiv : 0 ≤ t / (δ + t) := div_nonneg ht0 (by linarith)
    rw [Real.norm_of_nonneg hdiv, div_lt_one (by linarith)]
    linarith

/-- For `0 ≤ δ` and `0 ≤ b`, `‖resolventApprox δ b‖ ≤ 1`. -/
theorem norm_resolventApprox_le_one {δ : ℝ} (hδ : 0 ≤ δ) {b : A} (hb : 0 ≤ b) :
    ‖resolventApprox δ b‖ ≤ 1 :=
  (norm_resolventApprox_lt_one hδ hb).le

/-- Rescaled functional-calculus formula for `resolventApprox δ b` in terms of `δ⁻¹ • b` and
`s ↦ 1 - (1 + s)⁻¹`. -/
theorem resolventApprox_eq_cfcₙ_one_sub_inv {δ : ℝ} (hδ : 0 < δ) {b : A} (hb : 0 ≤ b) :
    resolventApprox δ b = cfcₙ (fun s : ℝ => 1 - (1 + s)⁻¹) (δ⁻¹ • b) := by
  have hg : ContinuousOn (fun s : ℝ => 1 - (1 + s)⁻¹) ((δ⁻¹ * ·) '' quasispectrum ℝ b) := by
    refine continuousOn_const.sub (continuousOn_const.add continuousOn_id |>.inv₀ ?_)
    rintro _ ⟨t, ht, rfl⟩
    dsimp only [Pi.add_apply, id_eq]
    have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg b hb t ht
    have hmul : 0 ≤ δ⁻¹ * t := mul_nonneg (inv_nonneg.mpr hδ.le) ht0
    linarith
  rw [resolventApprox_eq_cfcₙ hδ hb,
    ← cfcₙ_comp_const_mul δ⁻¹ (fun s : ℝ => 1 - (1 + s)⁻¹) b hg (by simp)]
  refine cfcₙ_congr fun t ht => ?_
  have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg b hb t ht
  have : δ ≠ 0 := hδ.ne'
  have : δ + t ≠ 0 := by linarith
  have : 1 + δ⁻¹ * t ≠ 0 := by positivity
  field_simp
  ring

/-- Joint monotonicity of `resolventApprox`: enlarging a positive element `b₁ ≤ b₂` and decreasing
`0 < δ₂ ≤ δ₁` increases `resolventApprox` in the C⋆-algebra order. -/
theorem resolventApprox_le_resolventApprox {δ₁ δ₂ : ℝ} (hδ₂ : 0 < δ₂) (hδ : δ₂ ≤ δ₁)
    {b₁ b₂ : A} (hb₁ : 0 ≤ b₁) (hb : b₁ ≤ b₂) :
    resolventApprox δ₁ b₁ ≤ resolventApprox δ₂ b₂ := by
  have hδ₁ : 0 < δ₁ := hδ₂.trans_le hδ
  have hb₂ : 0 ≤ b₂ := hb₁.trans hb
  calc
    resolventApprox δ₁ b₁ = cfcₙ (fun s : ℝ => 1 - (1 + s)⁻¹) (δ₁⁻¹ • b₁) :=
      resolventApprox_eq_cfcₙ_one_sub_inv hδ₁ hb₁
    _ ≤ cfcₙ (fun s : ℝ => 1 - (1 + s)⁻¹) (δ₁⁻¹ • b₂) :=
      CFC.monotoneOn_one_sub_one_add_inv_real
        (smul_nonneg (inv_nonneg.mpr hδ₁.le) hb₁)
        (smul_nonneg (inv_nonneg.mpr hδ₁.le) hb₂)
        (smul_le_smul_of_nonneg_left hb (inv_nonneg.mpr hδ₁.le))
    _ = resolventApprox δ₁ b₂ := (resolventApprox_eq_cfcₙ_one_sub_inv hδ₁ hb₂).symm
    _ = cfcₙ (fun t : ℝ => t / (δ₁ + t)) b₂ := resolventApprox_eq_cfcₙ hδ₁ hb₂
    _ ≤ cfcₙ (fun t : ℝ => t / (δ₂ + t)) b₂ := by
      have hf₁ : ContinuousOn (fun t : ℝ => t / (δ₁ + t)) (quasispectrum ℝ b₂) :=
        continuousOn_id.div (continuousOn_const.add continuousOn_id) fun t ht => by
          have := quasispectrum_nonneg_of_nonneg b₂ hb₂ t ht; linarith
      have hf₂ : ContinuousOn (fun t : ℝ => t / (δ₂ + t)) (quasispectrum ℝ b₂) :=
        continuousOn_id.div (continuousOn_const.add continuousOn_id) fun t ht => by
          have := quasispectrum_nonneg_of_nonneg b₂ hb₂ t ht; linarith
      refine (cfcₙ_le_iff (fun t : ℝ => t / (δ₁ + t)) (fun t : ℝ => t / (δ₂ + t)) b₂
        hf₁ hf₂).mpr fun t ht => ?_
      have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg b₂ hb₂ t ht
      exact div_le_div_of_nonneg_left ht0 (by linarith) (by linarith)
    _ = resolventApprox δ₂ b₂ := (resolventApprox_eq_cfcₙ hδ₂ hb₂).symm

/-- Functional-calculus formula for `(1 - e) * b * (1 - e)` in `A⁺¹`, where
`e = resolventApprox δ b`. -/
private theorem one_sub_inr_resolventApprox_mul_eq_cfc {δ : ℝ} (hδ : 0 < δ) {b : A} (hb : 0 ≤ b) :
    (1 - ((resolventApprox δ b : A) : A⁺¹)) * (b : A⁺¹) *
        (1 - ((resolventApprox δ b : A) : A⁺¹)) =
      cfc (fun t : ℝ => δ ^ 2 * t / (δ + t) ^ 2) (b : A⁺¹) := by
  have hb' : 0 ≤ (b : A⁺¹) := Unitization.inr_nonneg_iff.mpr hb
  have hne : ∀ t ∈ spectrum ℝ (b : A⁺¹), δ + t ≠ 0 := fun t ht => by
    have := spectrum_nonneg_of_nonneg hb' ht; linarith
  have hcont_f : ContinuousOn (fun t : ℝ => t / (δ + t)) (spectrum ℝ (b : A⁺¹)) :=
    continuousOn_id.div (continuousOn_const.add continuousOn_id) hne
  have hcont_g : ContinuousOn (fun t : ℝ => δ / (δ + t)) (spectrum ℝ (b : A⁺¹)) :=
    continuousOn_const.div (continuousOn_const.add continuousOn_id) hne
  have h1e : 1 - ((resolventApprox δ b : A) : A⁺¹) =
      cfc (fun t : ℝ => δ / (δ + t)) (b : A⁺¹) := by
    rw [resolventApprox_eq_cfcₙ hδ hb,
      Unitization.real_cfcₙ_eq_cfc_inr b (fun t : ℝ => t / (δ + t)) (by simp),
      ← cfc_const_one (R := ℝ) (b : A⁺¹), ← cfc_sub _ _ (b : A⁺¹) continuousOn_const hcont_f]
    refine cfc_congr fun t ht => ?_
    have := hne t ht
    field_simp
    ring
  rw [h1e]
  nth_rw 2 [← cfc_id ℝ (b : A⁺¹)]
  rw [← cfc_mul _ _ (b : A⁺¹) hcont_g continuousOn_id,
    ← cfc_mul (fun x : ℝ => δ / (δ + x) * id x) (fun t : ℝ => δ / (δ + t)) (b : A⁺¹)
      (hcont_g.mul continuousOn_id) hcont_g]
  refine cfc_congr fun t ht => ?_
  dsimp only [id_eq]
  have := hne t ht
  field_simp

/-- **Sharp right-approximation bound.** If `0 < δ` and `star x * x ≤ b`, then
`‖x - x * resolventApprox δ b‖ ^ 2 ≤ δ / 4`. -/
theorem norm_sub_mul_resolventApprox_sq_le {δ : ℝ} (hδ : 0 < δ) {b x : A}
    (hxb : star x * x ≤ b) :
    ‖x - x * resolventApprox δ b‖ ^ 2 ≤ δ / 4 := by
  have hb : 0 ≤ b := (star_mul_self_nonneg x).trans hxb
  have hb' : 0 ≤ (b : A⁺¹) := Unitization.inr_nonneg_iff.mpr hb
  have hsa : IsSelfAdjoint (1 - ((resolventApprox δ b : A) : A⁺¹)) :=
    (IsSelfAdjoint.one A⁺¹).sub ((isSelfAdjoint_resolventApprox hδ.le hb).inr ℂ)
  have hy_eq : ((x - x * resolventApprox δ b : A) : A⁺¹) =
      (x : A⁺¹) * (1 - ((resolventApprox δ b : A) : A⁺¹)) := by
    rw [Unitization.inr_sub, Unitization.inr_mul, mul_sub, mul_one]
  have hy_le :
      star ((x : A⁺¹) * (1 - ((resolventApprox δ b : A) : A⁺¹))) *
          ((x : A⁺¹) * (1 - ((resolventApprox δ b : A) : A⁺¹))) ≤
        cfc (fun t : ℝ => δ ^ 2 * t / (δ + t) ^ 2) (b : A⁺¹) := by
    have hconj :
        star ((x : A⁺¹) * (1 - ((resolventApprox δ b : A) : A⁺¹))) *
            ((x : A⁺¹) * (1 - ((resolventApprox δ b : A) : A⁺¹))) =
          (1 - ((resolventApprox δ b : A) : A⁺¹)) * ((star x * x : A) : A⁺¹) *
            (1 - ((resolventApprox δ b : A) : A⁺¹)) := by
      simp only [star_mul, hsa.star_eq, Unitization.inr_mul, Unitization.inr_star, mul_assoc]
    rw [hconj, ← one_sub_inr_resolventApprox_mul_eq_cfc hδ hb]
    exact hsa.conjugate_le_conjugate (Unitization.inr_le_inr_iff.mpr hxb)
  have hcfc_norm : ‖cfc (fun t : ℝ => δ ^ 2 * t / (δ + t) ^ 2) (b : A⁺¹)‖ ≤ δ / 4 := by
    refine norm_cfc_le (by positivity) fun t ht => ?_
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hb' ht
    rw [Real.norm_of_nonneg (div_nonneg (by positivity) (by positivity))]
    exact sq_mul_div_add_sq_le hδ.le t
  rw [← Unitization.norm_inr (𝕜 := ℂ), hy_eq, sq, ← CStarRing.norm_star_mul_self]
  exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg hy_le (star_mul_self_nonneg _)).trans hcfc_norm

/-- Norm form of `norm_sub_mul_resolventApprox_sq_le`: if `0 < δ` and `star x * x ≤ b`, then
`‖x - x * resolventApprox δ b‖ ≤ Real.sqrt δ / 2`. -/
theorem norm_sub_mul_resolventApprox_le {δ : ℝ} (hδ : 0 < δ) {b x : A}
    (hxb : star x * x ≤ b) :
    ‖x - x * resolventApprox δ b‖ ≤ Real.sqrt δ / 2 := by
  have hsqrt : Real.sqrt (δ / 4) = Real.sqrt δ / 2 := by
    rw [Real.sqrt_div hδ.le, (by norm_num : (4 : ℝ) = 2 ^ 2), Real.sqrt_sq (by norm_num)]
  rw [← hsqrt]
  exact Real.le_sqrt_of_sq_le (norm_sub_mul_resolventApprox_sq_le hδ hxb)

/-- **Sharp left-approximation bound.** If `0 < δ` and `x * star x ≤ b`, then
`‖x - resolventApprox δ b * x‖ ^ 2 ≤ δ / 4`. -/
theorem norm_sub_resolventApprox_mul_sq_le {δ : ℝ} (hδ : 0 < δ) {b x : A}
    (hxb : x * star x ≤ b) :
    ‖x - resolventApprox δ b * x‖ ^ 2 ≤ δ / 4 := by
  have hb : 0 ≤ b := (mul_star_self_nonneg x).trans hxb
  have hstar : ‖x - resolventApprox δ b * x‖ = ‖star x - star x * resolventApprox δ b‖ := by
    rw [← norm_star, star_sub, star_mul, star_resolventApprox hδ.le hb]
  rw [hstar]
  exact norm_sub_mul_resolventApprox_sq_le hδ (by simpa only [star_star] using hxb)

/-- Norm form of `norm_sub_resolventApprox_mul_sq_le`: if `0 < δ` and `x * star x ≤ b`, then
`‖x - resolventApprox δ b * x‖ ≤ Real.sqrt δ / 2`. -/
theorem norm_sub_resolventApprox_mul_le {δ : ℝ} (hδ : 0 < δ) {b x : A}
    (hxb : x * star x ≤ b) :
    ‖x - resolventApprox δ b * x‖ ≤ Real.sqrt δ / 2 := by
  have hsqrt : Real.sqrt (δ / 4) = Real.sqrt δ / 2 := by
    rw [Real.sqrt_div hδ.le, (by norm_num : (4 : ℝ) = 2 ^ 2), Real.sqrt_sq (by norm_num)]
  rw [← hsqrt]
  exact Real.le_sqrt_of_sq_le (norm_sub_resolventApprox_mul_sq_le hδ hxb)

end OrderAndNorm

end TauCeti.CStarAlgebra

/-! ### Nets and sequences in algebraic complex left and right ideals -/

namespace Submodule

open TauCeti.CStarAlgebra

section LeftIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The finite sum of squares `b_F = ∑ x ∈ F, star x * x` associated to a finite subset `F` of a
complex submodule `L : Submodule ℂ A`. -/
def leftIdealSumSq (L : Submodule ℂ A) (F : Finset L) : A :=
  ∑ x ∈ F, star (x : A) * (x : A)

theorem leftIdealSumSq_def (L : Submodule ℂ A) (F : Finset L) :
    L.leftIdealSumSq F = ∑ x ∈ F, star (x : A) * (x : A) :=
  (rfl)

@[simp]
theorem leftIdealSumSq_empty (L : Submodule ℂ A) : L.leftIdealSumSq ∅ = 0 :=
  Finset.sum_empty

@[simp]
theorem leftIdealSumSq_singleton (L : Submodule ℂ A) (x : L) :
    L.leftIdealSumSq {x} = star (x : A) * (x : A) :=
  Finset.sum_singleton _ _

@[simp]
theorem bot_leftIdealSumSq (F : Finset (⊥ : Submodule ℂ A)) :
    (⊥ : Submodule ℂ A).leftIdealSumSq F = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  have hx : (x : A) = 0 := (Submodule.mem_bot ℂ).mp x.2
  simp [hx]

/-- If `L` absorbs ambient left multiples, `L.leftIdealSumSq F` lies in `L` for every `F`. -/
theorem leftIdealSumSq_mem (L : Submodule ℂ A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) (F : Finset L) :
    L.leftIdealSumSq F ∈ L :=
  L.sum_mem fun x _ => hL (star (x : A)) (x : A) x.2

/-- The positive contractive right approximate identity net `(F, δ) ↦ b_F * (δ • 1 + b_F)⁻¹`
indexed by `Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ`, ordered by enlarging `F` and decreasing `δ > 0`. -/
def rightApproxUnit (L : Submodule ℂ A) (i : Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ) : A :=
  resolventApprox (OrderDual.ofDual i.2).1 (L.leftIdealSumSq i.1)

theorem rightApproxUnit_def (L : Submodule ℂ A) (F : Finset L) (δ : (Set.Ioi (0 : ℝ))ᵒᵈ) :
    L.rightApproxUnit (F, δ) = resolventApprox (OrderDual.ofDual δ).1 (L.leftIdealSumSq F) :=
  (rfl)

@[simp]
theorem rightApproxUnit_empty (L : Submodule ℂ A) (δ : (Set.Ioi (0 : ℝ))ᵒᵈ) :
    L.rightApproxUnit (∅, δ) = 0 := by
  simp [rightApproxUnit]

/-- On the zero submodule `⊥`, the `rightApproxUnit` net is identically zero. -/
@[simp]
theorem bot_rightApproxUnit (i : Finset (⊥ : Submodule ℂ A) × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    (⊥ : Submodule ℂ A).rightApproxUnit i = 0 := by
  simp [rightApproxUnit]

/-- Every term of `L.rightApproxUnit` belongs to `L` itself whenever `L` is a complex left ideal
(no closedness assumption on `L`). -/
theorem rightApproxUnit_mem (L : Submodule ℂ A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    (i : Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    L.rightApproxUnit i ∈ L :=
  resolventApprox_mem_of_mul_mem_left hL _ (L.leftIdealSumSq_mem hL i.1)

/-- Every term of `L.rightApproxUnit` is self-adjoint. -/
theorem isSelfAdjoint_rightApproxUnit (L : Submodule ℂ A) (i : Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    IsSelfAdjoint (L.rightApproxUnit i) := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  exact isSelfAdjoint_resolventApprox (OrderDual.ofDual i.2).2.le
    (Finset.sum_nonneg fun x _ => star_mul_self_nonneg (x : A))

@[simp]
theorem star_rightApproxUnit (L : Submodule ℂ A) (i : Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    star (L.rightApproxUnit i) = L.rightApproxUnit i :=
  (L.isSelfAdjoint_rightApproxUnit i).star_eq

/-- Every term of `L.rightApproxUnit` has norm strictly less than `1`. -/
theorem norm_rightApproxUnit_lt_one (L : Submodule ℂ A) (i : Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    ‖L.rightApproxUnit i‖ < 1 := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  exact norm_resolventApprox_lt_one (OrderDual.ofDual i.2).2.le
    (Finset.sum_nonneg fun x _ => star_mul_self_nonneg (x : A))

/-- Every term of `L.rightApproxUnit` is contractive (`‖L.rightApproxUnit i‖ ≤ 1`). -/
theorem norm_rightApproxUnit_le_one (L : Submodule ℂ A) (i : Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    ‖L.rightApproxUnit i‖ ≤ 1 :=
  (L.norm_rightApproxUnit_lt_one i).le

/-- **Sharp finite-set estimate.** For every `x ∈ F`,
`‖x - x * L.rightApproxUnit (F, δ)‖ ^ 2 ≤ δ / 4`. -/
theorem norm_sub_mul_rightApproxUnit_sq_le (L : Submodule ℂ A)
    {i : Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ} {x : L} (hx : x ∈ i.1) :
    ‖(x : A) - (x : A) * L.rightApproxUnit i‖ ^ 2 ≤ (OrderDual.ofDual i.2).1 / 4 := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  exact norm_sub_mul_resolventApprox_sq_le (OrderDual.ofDual i.2).2
    (Finset.single_le_sum (f := fun y : L => star (y : A) * (y : A))
      (fun y _ => star_mul_self_nonneg (y : A)) hx)

/-- Norm form of `norm_sub_mul_rightApproxUnit_sq_le`. -/
theorem norm_sub_mul_rightApproxUnit_le (L : Submodule ℂ A)
    {i : Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ} {x : L} (hx : x ∈ i.1) :
    ‖(x : A) - (x : A) * L.rightApproxUnit i‖ ≤ Real.sqrt (OrderDual.ofDual i.2).1 / 2 := by
  have hδ : 0 ≤ (OrderDual.ofDual i.2).1 := (OrderDual.ofDual i.2).2.le
  have hsqrt : Real.sqrt ((OrderDual.ofDual i.2).1 / 4) =
      Real.sqrt (OrderDual.ofDual i.2).1 / 2 := by
    rw [Real.sqrt_div hδ, (by norm_num : (4 : ℝ) = 2 ^ 2), Real.sqrt_sq (by norm_num)]
  rw [← hsqrt]
  exact Real.le_sqrt_of_sq_le (L.norm_sub_mul_rightApproxUnit_sq_le hx)

/-- **Right approximate identity convergence.** Along `atTop` on `Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ`,
`x * L.rightApproxUnit i → x` for every `x ∈ L`. -/
theorem tendsto_mul_rightApproxUnit (L : Submodule ℂ A) {x : A} (hx : x ∈ L) :
    Tendsto (fun i => x * L.rightApproxUnit i) atTop (𝓝 x) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_atTop]
  let x₀ : L := ⟨x, hx⟩
  let δ₀ : Set.Ioi (0 : ℝ) := ⟨2 * ε ^ 2, Set.mem_Ioi.mpr (by positivity)⟩
  refine ⟨({x₀}, OrderDual.toDual δ₀), fun i hi => ?_⟩
  have hx₀ : x₀ ∈ i.1 := hi.1 (Finset.mem_singleton_self x₀)
  have hδ : (OrderDual.ofDual i.2).1 ≤ 2 * ε ^ 2 := hi.2
  have hsq : ‖x - x * L.rightApproxUnit i‖ ^ 2 < ε ^ 2 :=
    calc
      ‖x - x * L.rightApproxUnit i‖ ^ 2 ≤ (OrderDual.ofDual i.2).1 / 4 :=
        L.norm_sub_mul_rightApproxUnit_sq_le hx₀
      _ ≤ 2 * ε ^ 2 / 4 := by linarith
      _ < ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
  rw [dist_eq_norm, norm_sub_rev]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq

/-! ### Sequential right approximate identities in separable left ideals -/

/-- Explicit sequential positive contractive right approximate identity inside a norm-separable
complex left ideal `L`, formed from initial segments of `TopologicalSpace.denseSeq L` and
`δ_n = 1 / (n + 1)`. -/
def rightApproxUnitSeq (L : Submodule ℂ A) [TopologicalSpace.SeparableSpace L] (n : ℕ) : A :=
  open Classical in
  L.rightApproxUnit ((Finset.range n).image (TopologicalSpace.denseSeq L),
    OrderDual.toDual ⟨1 / ((n : ℝ) + 1), Set.mem_Ioi.mpr (by positivity)⟩)

theorem rightApproxUnitSeq_def (L : Submodule ℂ A) [TopologicalSpace.SeparableSpace L] (n : ℕ) :
    L.rightApproxUnitSeq n =
      open Classical in
      L.rightApproxUnit ((Finset.range n).image (TopologicalSpace.denseSeq L),
        OrderDual.toDual ⟨1 / ((n : ℝ) + 1), Set.mem_Ioi.mpr (by positivity)⟩) :=
  (rfl)

@[simp]
theorem bot_rightApproxUnitSeq (n : ℕ) : (⊥ : Submodule ℂ A).rightApproxUnitSeq n = 0 := by
  simp [rightApproxUnitSeq]

theorem rightApproxUnitSeq_mem (L : Submodule ℂ A) [TopologicalSpace.SeparableSpace L]
    (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) (n : ℕ) :
    L.rightApproxUnitSeq n ∈ L :=
  L.rightApproxUnit_mem hL _

theorem isSelfAdjoint_rightApproxUnitSeq (L : Submodule ℂ A) [TopologicalSpace.SeparableSpace L]
    (n : ℕ) : IsSelfAdjoint (L.rightApproxUnitSeq n) :=
  L.isSelfAdjoint_rightApproxUnit _

@[simp]
theorem star_rightApproxUnitSeq (L : Submodule ℂ A) [TopologicalSpace.SeparableSpace L] (n : ℕ) :
    star (L.rightApproxUnitSeq n) = L.rightApproxUnitSeq n :=
  L.star_rightApproxUnit _

theorem norm_rightApproxUnitSeq_lt_one (L : Submodule ℂ A) [TopologicalSpace.SeparableSpace L]
    (n : ℕ) : ‖L.rightApproxUnitSeq n‖ < 1 :=
  L.norm_rightApproxUnit_lt_one _

theorem norm_rightApproxUnitSeq_le_one (L : Submodule ℂ A) [TopologicalSpace.SeparableSpace L]
    (n : ℕ) : ‖L.rightApproxUnitSeq n‖ ≤ 1 :=
  L.norm_rightApproxUnit_le_one _

/-- For norm-separable `L`, `x * L.rightApproxUnitSeq n → x` for every `x ∈ L`
(including `L = ⊥`). -/
theorem tendsto_mul_rightApproxUnitSeq (L : Submodule ℂ A) [TopologicalSpace.SeparableSpace L]
    {x : A} (hx : x ∈ L) :
    Tendsto (fun n => x * L.rightApproxUnitSeq n) atTop (𝓝 x) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq L)
    ⟨x, hx⟩ (ε / 3) (by positivity)
  let y : L := TopologicalSpace.denseSeq L k
  have hyx : ‖(y : A) - x‖ < ε / 3 := by rwa [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] at hk
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (3 / ε ^ 2)
  refine ⟨max (k + 1) N₀, fun n hn => ?_⟩
  have hkn : k < n := Nat.lt_of_succ_le ((le_max_left _ _).trans hn)
  have hN : 3 < ((n : ℝ) + 1) * ε ^ 2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp <|
    hN₀.trans_le (by exact_mod_cast (le_max_right (k + 1) N₀).trans (hn.trans (n.le_add_right 1)))
  have hy_mem : y ∈ (Finset.range n).image (TopologicalSpace.denseSeq L) :=
    Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkn, rfl⟩
  have hy_err : ‖(y : A) - (y : A) * L.rightApproxUnitSeq n‖ < ε / 3 := by
    let idx : Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ :=
      ((Finset.range n).image (TopologicalSpace.denseSeq L),
        OrderDual.toDual ⟨1 / ((n : ℝ) + 1), Set.mem_Ioi.mpr (by positivity)⟩)
    refine (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp <|
      (L.norm_sub_mul_rightApproxUnit_sq_le (i := idx) hy_mem).trans_lt ?_
    dsimp only [idx, OrderDual.ofDual_toDual]
    rw [div_pow, div_lt_iff₀ (by norm_num : (0 : ℝ) < 4), div_lt_iff₀ (by positivity)]
    nlinarith
  rw [dist_eq_norm]
  calc
    ‖x * L.rightApproxUnitSeq n - x‖ ≤
        ‖(x - (y : A)) * L.rightApproxUnitSeq n‖ +
          ‖(y : A) * L.rightApproxUnitSeq n - (y : A)‖ + ‖(y : A) - x‖ := by
      simpa only [sub_mul, sub_add_sub_cancel, add_sub_cancel_left] using
        norm_add₃_le (a := (x - (y : A)) * L.rightApproxUnitSeq n)
          (b := (y : A) * L.rightApproxUnitSeq n - (y : A)) (c := (y : A) - x)
    _ ≤ ‖(y : A) - x‖ * 1 + ‖(y : A) - (y : A) * L.rightApproxUnitSeq n‖ + ‖(y : A) - x‖ := by
      gcongr
      · rw [norm_sub_rev (y : A) x]
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left (L.norm_rightApproxUnitSeq_le_one n) (norm_nonneg _))
      · rw [norm_sub_rev]
    _ < ε / 3 * 1 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

section Order

variable [PartialOrder A] [StarOrderedRing A]

theorem leftIdealSumSq_nonneg (L : Submodule ℂ A) (F : Finset L) : 0 ≤ L.leftIdealSumSq F :=
  Finset.sum_nonneg fun x _ => star_mul_self_nonneg (x : A)

theorem leftIdealSumSq_mono (L : Submodule ℂ A) : Monotone L.leftIdealSumSq :=
  fun _ _ h => Finset.sum_le_sum_of_subset_of_nonneg h fun x _ _ => star_mul_self_nonneg (x : A)

theorem star_mul_self_le_leftIdealSumSq (L : Submodule ℂ A) {F : Finset L} {x : L} (hx : x ∈ F) :
    star (x : A) * (x : A) ≤ L.leftIdealSumSq F := by
  rw [leftIdealSumSq]
  exact Finset.single_le_sum (f := fun y : L => star (y : A) * (y : A))
    (fun y _ => star_mul_self_nonneg (y : A)) hx

/-- Every term of `L.rightApproxUnit` is positive (`0 ≤ L.rightApproxUnit i`). -/
theorem rightApproxUnit_nonneg (L : Submodule ℂ A) (i : Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    0 ≤ L.rightApproxUnit i :=
  resolventApprox_nonneg (OrderDual.ofDual i.2).2.le (L.leftIdealSumSq_nonneg i.1)

/-- The net `L.rightApproxUnit` is monotone increasing in `(F, δ)` with respect to the C⋆-order. -/
theorem rightApproxUnit_mono (L : Submodule ℂ A) : Monotone L.rightApproxUnit :=
  fun i j hij => resolventApprox_le_resolventApprox (OrderDual.ofDual j.2).2 hij.2
    (L.leftIdealSumSq_nonneg i.1) (L.leftIdealSumSq_mono hij.1)

theorem rightApproxUnitSeq_nonneg (L : Submodule ℂ A) [TopologicalSpace.SeparableSpace L] (n : ℕ) :
    0 ≤ L.rightApproxUnitSeq n :=
  L.rightApproxUnit_nonneg _

/-- The sequence `L.rightApproxUnitSeq` is monotone increasing in the C⋆-order. -/
theorem rightApproxUnitSeq_mono (L : Submodule ℂ A) [TopologicalSpace.SeparableSpace L] :
    Monotone L.rightApproxUnitSeq := by
  classical
  intro m n hmn
  refine L.rightApproxUnit_mono ⟨Finset.image_subset_image (Finset.range_mono hmn), ?_⟩
  rw [OrderDual.toDual_le_toDual, Subtype.mk_le_mk]
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

/-- Every norm-separable complex left ideal `L` of `A` (not necessarily closed, including `L = ⊥`)
contains a monotone increasing sequence of positive strict contractions that acts as a right
approximate identity on `L`. -/
theorem exists_seq_rightApproxUnit (L : Submodule ℂ A) [TopologicalSpace.SeparableSpace L]
    (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    ∃ e : ℕ → A, Monotone e ∧ (∀ n, e n ∈ L) ∧ (∀ n, 0 ≤ e n) ∧ (∀ n, ‖e n‖ < 1) ∧
      ∀ x ∈ L, Tendsto (fun n => x * e n) atTop (𝓝 x) :=
  ⟨L.rightApproxUnitSeq, L.rightApproxUnitSeq_mono, L.rightApproxUnitSeq_mem hL,
    L.rightApproxUnitSeq_nonneg, L.norm_rightApproxUnitSeq_lt_one,
    fun _ hx => L.tendsto_mul_rightApproxUnitSeq hx⟩

end Order

end LeftIdeal

/-! ### Right-ideal duals -/

section RightIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The finite sum of squares `c_F = ∑ x ∈ F, x * star x` associated to a finite subset `F` of a
complex submodule `M : Submodule ℂ A`. -/
def rightIdealSumSq (M : Submodule ℂ A) (F : Finset M) : A :=
  ∑ x ∈ F, (x : A) * star (x : A)

theorem rightIdealSumSq_def (M : Submodule ℂ A) (F : Finset M) :
    M.rightIdealSumSq F = ∑ x ∈ F, (x : A) * star (x : A) :=
  (rfl)

@[simp]
theorem rightIdealSumSq_empty (M : Submodule ℂ A) : M.rightIdealSumSq ∅ = 0 :=
  Finset.sum_empty

@[simp]
theorem rightIdealSumSq_singleton (M : Submodule ℂ A) (x : M) :
    M.rightIdealSumSq {x} = (x : A) * star (x : A) :=
  Finset.sum_singleton _ _

@[simp]
theorem bot_rightIdealSumSq (F : Finset (⊥ : Submodule ℂ A)) :
    (⊥ : Submodule ℂ A).rightIdealSumSq F = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  have hx : (x : A) = 0 := (Submodule.mem_bot ℂ).mp x.2
  simp [hx]

/-- If `M` absorbs ambient right multiples, `M.rightIdealSumSq F` lies in `M` for every `F`. -/
theorem rightIdealSumSq_mem (M : Submodule ℂ A) (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M) (F : Finset M) :
    M.rightIdealSumSq F ∈ M :=
  M.sum_mem fun x _ => hM (star (x : A)) (x : A) x.2

/-- The positive contractive left approximate identity net `(F, δ) ↦ (δ • 1 + c_F)⁻¹ * c_F` inside
a complex right ideal `M`, where `c_F = M.rightIdealSumSq F`. -/
def leftApproxUnit (M : Submodule ℂ A) (i : Finset M × (Set.Ioi (0 : ℝ))ᵒᵈ) : A :=
  (M.comap (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap).rightApproxUnit
    (i.1.map (((starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).ofSubmodule' M).symm.toEquiv.toEmbedding), i.2)

theorem leftApproxUnit_def (M : Submodule ℂ A) (F : Finset M) (δ : (Set.Ioi (0 : ℝ))ᵒᵈ) :
    M.leftApproxUnit (F, δ) =
      (M.comap (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap).rightApproxUnit
        (F.map (((starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).ofSubmodule' M).symm.toEquiv.toEmbedding), δ) :=
  (rfl)

theorem leftApproxUnit_eq_resolventApprox (M : Submodule ℂ A) (F : Finset M)
    (δ : (Set.Ioi (0 : ℝ))ᵒᵈ) :
    M.leftApproxUnit (F, δ) = resolventApprox (OrderDual.ofDual δ).1 (M.rightIdealSumSq F) := by
  simp [leftApproxUnit, rightApproxUnit, leftIdealSumSq, rightIdealSumSq]

@[simp]
theorem leftApproxUnit_empty (M : Submodule ℂ A) (δ : (Set.Ioi (0 : ℝ))ᵒᵈ) :
    M.leftApproxUnit (∅, δ) = 0 := by
  simp [leftApproxUnit]

@[simp]
theorem bot_leftApproxUnit (i : Finset (⊥ : Submodule ℂ A) × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    (⊥ : Submodule ℂ A).leftApproxUnit i = 0 := by
  rcases i with ⟨F, δ⟩
  simp [leftApproxUnit_eq_resolventApprox]

/-- Every term of `M.leftApproxUnit` lies in `M` whenever `M` is a complex right ideal (without any
closedness assumption on `M`). -/
theorem leftApproxUnit_mem (M : Submodule ℂ A) (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M)
    (i : Finset M × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    M.leftApproxUnit i ∈ M := by
  rcases i with ⟨F, δ⟩
  rw [leftApproxUnit_eq_resolventApprox]
  exact resolventApprox_mem_of_mul_mem_right hM _ (M.rightIdealSumSq_mem hM F)

theorem isSelfAdjoint_leftApproxUnit (M : Submodule ℂ A) (i : Finset M × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    IsSelfAdjoint (M.leftApproxUnit i) :=
  isSelfAdjoint_rightApproxUnit _ _

@[simp]
theorem star_leftApproxUnit (M : Submodule ℂ A) (i : Finset M × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    star (M.leftApproxUnit i) = M.leftApproxUnit i :=
  star_rightApproxUnit _ _

theorem norm_leftApproxUnit_lt_one (M : Submodule ℂ A) (i : Finset M × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    ‖M.leftApproxUnit i‖ < 1 :=
  norm_rightApproxUnit_lt_one _ _

theorem norm_leftApproxUnit_le_one (M : Submodule ℂ A) (i : Finset M × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    ‖M.leftApproxUnit i‖ ≤ 1 :=
  norm_rightApproxUnit_le_one _ _

/-- **Sharp finite-set left-approximation estimate.** For every `x ∈ F`,
`‖x - M.leftApproxUnit (F, δ) * x‖ ^ 2 ≤ δ / 4`. -/
theorem norm_sub_leftApproxUnit_mul_sq_le (M : Submodule ℂ A)
    {i : Finset M × (Set.Ioi (0 : ℝ))ᵒᵈ} {x : M} (hx : x ∈ i.1) :
    ‖(x : A) - M.leftApproxUnit i * (x : A)‖ ^ 2 ≤ (OrderDual.ofDual i.2).1 / 4 := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  rcases i with ⟨F, δ⟩
  rw [leftApproxUnit_eq_resolventApprox]
  exact norm_sub_resolventApprox_mul_sq_le (OrderDual.ofDual δ).2
    (Finset.single_le_sum (f := fun y : M => (y : A) * star (y : A))
      (fun y _ => mul_star_self_nonneg (y : A)) hx)

/-- Norm form of `norm_sub_leftApproxUnit_mul_sq_le`. -/
theorem norm_sub_leftApproxUnit_mul_le (M : Submodule ℂ A)
    {i : Finset M × (Set.Ioi (0 : ℝ))ᵒᵈ} {x : M} (hx : x ∈ i.1) :
    ‖(x : A) - M.leftApproxUnit i * (x : A)‖ ≤ Real.sqrt (OrderDual.ofDual i.2).1 / 2 := by
  have hδ : 0 ≤ (OrderDual.ofDual i.2).1 := (OrderDual.ofDual i.2).2.le
  have hsqrt : Real.sqrt ((OrderDual.ofDual i.2).1 / 4) =
      Real.sqrt (OrderDual.ofDual i.2).1 / 2 := by
    rw [Real.sqrt_div hδ, (by norm_num : (4 : ℝ) = 2 ^ 2), Real.sqrt_sq (by norm_num)]
  rw [← hsqrt]
  exact Real.le_sqrt_of_sq_le (M.norm_sub_leftApproxUnit_mul_sq_le hx)

/-- **Left approximate identity convergence.** Along `atTop` on `Finset M × (Set.Ioi (0 : ℝ))ᵒᵈ`,
`M.leftApproxUnit i * x → x` for every `x ∈ M`. -/
theorem tendsto_leftApproxUnit_mul (M : Submodule ℂ A) {x : A} (hx : x ∈ M) :
    Tendsto (fun i => M.leftApproxUnit i * x) atTop (𝓝 x) := by
  classical
  let L := M.comap (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap
  let e : M ≃ L := ((starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).ofSubmodule' M).symm.toEquiv
  have hxL : star x ∈ L := by simpa [L] using hx
  let φ : Finset L × (Set.Ioi (0 : ℝ))ᵒᵈ → Finset M × (Set.Ioi (0 : ℝ))ᵒᵈ :=
    fun j => (j.1.map e.symm.toEmbedding, j.2)
  have hco : Tendsto (fun i => star x * M.leftApproxUnit i) atTop (𝓝 (star x)) := by
    refine (L.tendsto_mul_rightApproxUnit hxL).comp (tendsto_atTop_atTop.mpr fun j => ?_)
    refine ⟨φ j, fun i hi => ⟨fun y hy => ?_, hi.2⟩⟩
    have hmem := Finset.mem_map_of_mem e.toEmbedding
      (hi.1 (Finset.mem_map_of_mem e.symm.toEmbedding hy))
    simpa only [Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using hmem
  have hstar := (continuous_star.tendsto (star x)).comp hco
  simpa only [Function.comp_def, star_mul, star_star, star_leftApproxUnit] using hstar

private instance separableSpace_comap_starLinearEquiv (M : Submodule ℂ A)
    [TopologicalSpace.SeparableSpace M] :
    TopologicalSpace.SeparableSpace (M.comap (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap) :=
  (((starL ℂ : A ≃L⋆[ℂ] A).ofSubmodule' M).symm.toHomeomorph).isQuotientMap.separableSpace

/-- Explicit sequential positive contractive left approximate identity inside a norm-separable
complex right ideal `M`. -/
def leftApproxUnitSeq (M : Submodule ℂ A) [TopologicalSpace.SeparableSpace M] (n : ℕ) : A :=
  (M.comap (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap).rightApproxUnitSeq n

@[simp]
theorem bot_leftApproxUnitSeq (n : ℕ) : (⊥ : Submodule ℂ A).leftApproxUnitSeq n = 0 := by
  rw [leftApproxUnitSeq, rightApproxUnitSeq, rightApproxUnit]
  have hsum : ∀ F, ((⊥ : Submodule ℂ A).comap
      (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap).leftIdealSumSq F = 0 :=
    fun F => Finset.sum_eq_zero fun x _ => by
      have hx : star (x : A) = 0 := (Submodule.mem_bot ℂ).mp x.2
      simp [star_eq_zero.mp hx]
  rw [hsum, resolventApprox_zero]

theorem leftApproxUnitSeq_mem (M : Submodule ℂ A) [TopologicalSpace.SeparableSpace M]
    (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M) (n : ℕ) :
    M.leftApproxUnitSeq n ∈ M := by
  have hmem := (M.comap (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap).rightApproxUnitSeq_mem
    (M.mul_mem_left_comap_starLinearEquiv hM) n
  rw [Submodule.mem_comap, LinearEquiv.coe_coe, starLinearEquiv_apply,
    star_rightApproxUnitSeq] at hmem
  exact hmem

theorem isSelfAdjoint_leftApproxUnitSeq (M : Submodule ℂ A) [TopologicalSpace.SeparableSpace M]
    (n : ℕ) : IsSelfAdjoint (M.leftApproxUnitSeq n) :=
  (M.comap (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap).isSelfAdjoint_rightApproxUnitSeq n

@[simp]
theorem star_leftApproxUnitSeq (M : Submodule ℂ A) [TopologicalSpace.SeparableSpace M] (n : ℕ) :
    star (M.leftApproxUnitSeq n) = M.leftApproxUnitSeq n :=
  (M.isSelfAdjoint_leftApproxUnitSeq n).star_eq

theorem norm_leftApproxUnitSeq_lt_one (M : Submodule ℂ A) [TopologicalSpace.SeparableSpace M]
    (n : ℕ) : ‖M.leftApproxUnitSeq n‖ < 1 :=
  (M.comap (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap).norm_rightApproxUnitSeq_lt_one n

theorem norm_leftApproxUnitSeq_le_one (M : Submodule ℂ A) [TopologicalSpace.SeparableSpace M]
    (n : ℕ) : ‖M.leftApproxUnitSeq n‖ ≤ 1 :=
  (M.norm_leftApproxUnitSeq_lt_one n).le

theorem tendsto_leftApproxUnitSeq_mul (M : Submodule ℂ A) [TopologicalSpace.SeparableSpace M]
    {x : A} (hx : x ∈ M) :
    Tendsto (fun n => M.leftApproxUnitSeq n * x) atTop (𝓝 x) := by
  let L := M.comap (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap
  have hxL : star x ∈ L := by simpa [L] using hx
  have hstar := (continuous_star.tendsto (star x)).comp (L.tendsto_mul_rightApproxUnitSeq hxL)
  simpa only [Function.comp_def, star_mul, star_star, star_rightApproxUnitSeq,
    leftApproxUnitSeq] using hstar

section Order

variable [PartialOrder A] [StarOrderedRing A]

theorem rightIdealSumSq_nonneg (M : Submodule ℂ A) (F : Finset M) : 0 ≤ M.rightIdealSumSq F :=
  Finset.sum_nonneg fun x _ => mul_star_self_nonneg (x : A)

theorem rightIdealSumSq_mono (M : Submodule ℂ A) : Monotone M.rightIdealSumSq :=
  fun _ _ h => Finset.sum_le_sum_of_subset_of_nonneg h fun x _ _ => mul_star_self_nonneg (x : A)

theorem mul_star_self_le_rightIdealSumSq (M : Submodule ℂ A) {F : Finset M} {x : M} (hx : x ∈ F) :
    (x : A) * star (x : A) ≤ M.rightIdealSumSq F := by
  rw [rightIdealSumSq]
  exact Finset.single_le_sum (f := fun y : M => (y : A) * star (y : A))
    (fun y _ => mul_star_self_nonneg (y : A)) hx

theorem leftApproxUnit_nonneg (M : Submodule ℂ A) (i : Finset M × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    0 ≤ M.leftApproxUnit i :=
  rightApproxUnit_nonneg _ _

theorem leftApproxUnit_mono (M : Submodule ℂ A) : Monotone M.leftApproxUnit :=
  fun _ _ hij => rightApproxUnit_mono _ ⟨Finset.map_subset_map.mpr hij.1, hij.2⟩

theorem leftApproxUnitSeq_nonneg (M : Submodule ℂ A) [TopologicalSpace.SeparableSpace M] (n : ℕ) :
    0 ≤ M.leftApproxUnitSeq n :=
  (M.comap (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap).rightApproxUnitSeq_nonneg n

theorem leftApproxUnitSeq_mono (M : Submodule ℂ A) [TopologicalSpace.SeparableSpace M] :
    Monotone M.leftApproxUnitSeq :=
  (M.comap (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap).rightApproxUnitSeq_mono

/-- Every norm-separable complex right ideal `M` of `A` (not necessarily closed, including `M = ⊥`)
contains a monotone increasing sequence of positive strict contractions that acts as a left
approximate identity on `M`. -/
theorem exists_seq_leftApproxUnit (M : Submodule ℂ A) [TopologicalSpace.SeparableSpace M]
    (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M) :
    ∃ e : ℕ → A, Monotone e ∧ (∀ n, e n ∈ M) ∧ (∀ n, 0 ≤ e n) ∧ (∀ n, ‖e n‖ < 1) ∧
      ∀ x ∈ M, Tendsto (fun n => e n * x) atTop (𝓝 x) :=
  ⟨M.leftApproxUnitSeq, M.leftApproxUnitSeq_mono, M.leftApproxUnitSeq_mem hM,
    M.leftApproxUnitSeq_nonneg, M.norm_leftApproxUnitSeq_lt_one,
    fun _ hx => M.tendsto_leftApproxUnitSeq_mul hx⟩

end Order

end RightIdeal

end Submodule

/-! ### Unital `Ideal` specialization -/

namespace Ideal

variable {A : Type*} [CStarAlgebra A]

/-- For an arbitrary (not necessarily closed, not necessarily two-sided) left ideal `I : Ideal A`
of a unital C⋆-algebra, every term of `(I.restrictScalars ℂ).rightApproxUnit` lies in `I`. -/
theorem rightApproxUnit_mem (I : Ideal A)
    (i : Finset (I.restrictScalars ℂ) × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    (I.restrictScalars ℂ).rightApproxUnit i ∈ I :=
  (I.restrictScalars ℂ).rightApproxUnit_mem (fun a _ hx => I.mul_mem_left a hx) i

/-- Along `atTop`, `(I.restrictScalars ℂ).rightApproxUnit` right-approximates every element of an
algebraic left ideal `I : Ideal A`. -/
theorem tendsto_mul_rightApproxUnit (I : Ideal A) {x : A} (hx : x ∈ I) :
    Tendsto (fun i => x * (I.restrictScalars ℂ).rightApproxUnit i) atTop (𝓝 x) :=
  (I.restrictScalars ℂ).tendsto_mul_rightApproxUnit hx

/-- Every norm-separable algebraic left ideal `I : Ideal A` of a unital C⋆-algebra admits a
monotone increasing sequence of positive strict contractions in `I` acting as a right approximate
identity on `I`. -/
theorem exists_seq_rightApproxUnit [PartialOrder A] [StarOrderedRing A] (I : Ideal A)
    [TopologicalSpace.SeparableSpace I] :
    ∃ e : ℕ → A, Monotone e ∧ (∀ n, e n ∈ I) ∧ (∀ n, 0 ≤ e n) ∧ (∀ n, ‖e n‖ < 1) ∧
      ∀ x ∈ I, Tendsto (fun n => x * e n) atTop (𝓝 x) := by
  have _ : TopologicalSpace.SeparableSpace (I.restrictScalars ℂ) := ‹_›
  exact (I.restrictScalars ℂ).exists_seq_rightApproxUnit fun a _ hx => I.mul_mem_left a hx

end Ideal

/-! ### Comparison with `CStarAlgebra.approximateUnit` for closed two-sided ideals -/

namespace TwoSidedIdeal

open TauCeti.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]
  (I : TwoSidedIdeal A) [hI : IsClosed (I : Set A)]

/-- The `(F, δ)` approximate-identity net of `I.toSubmodule`, bundled as a net inside `(I : Type*)`
when `I` is a closed two-sided ideal. -/
def approxUnit (i : Finset I.toSubmodule × (Set.Ioi (0 : ℝ))ᵒᵈ) : I :=
  ⟨I.toSubmodule.rightApproxUnit i,
    I.toSubmodule.rightApproxUnit_mem (fun a x hx => I.mul_mem_left a x hx) i⟩

@[simp, norm_cast]
theorem coe_approxUnit (i : Finset I.toSubmodule × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    ((I.approxUnit i : I) : A) = I.toSubmodule.rightApproxUnit i :=
  (rfl)

theorem isSelfAdjoint_approxUnit (i : Finset I.toSubmodule × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    IsSelfAdjoint (I.approxUnit i) :=
  Subtype.ext (I.toSubmodule.star_rightApproxUnit i)

@[simp]
theorem star_approxUnit (i : Finset I.toSubmodule × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    star (I.approxUnit i) = I.approxUnit i :=
  (I.isSelfAdjoint_approxUnit i).star_eq

theorem norm_approxUnit_lt_one (i : Finset I.toSubmodule × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    ‖I.approxUnit i‖ < 1 :=
  I.toSubmodule.norm_rightApproxUnit_lt_one i

theorem norm_approxUnit_le_one (i : Finset I.toSubmodule × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    ‖I.approxUnit i‖ ≤ 1 :=
  (I.norm_approxUnit_lt_one i).le

section Order

variable [PartialOrder A] [StarOrderedRing A]

theorem approxUnit_mono : Monotone I.approxUnit :=
  I.toSubmodule.rightApproxUnit_mono

theorem approxUnit_nonneg (i : Finset I.toSubmodule × (Set.Ioi (0 : ℝ))ᵒᵈ) :
    0 ≤ I.approxUnit i :=
  I.toSubmodule.rightApproxUnit_nonneg i

/-- For a positive strict contraction `a ∈ I`, applying `resolventApprox 1` to
`cfcₙ (fun t : ℝ≥0 => t * (1 - t)⁻¹) a` recovers `a` inside `A`. -/
private theorem resolventApprox_one_cfcₙ_inv (a : I) (ha₀ : 0 ≤ a) (ha₁ : ‖a‖ < 1) :
    resolventApprox 1 (cfcₙ (fun t : ℝ≥0 => t * (1 - t)⁻¹) (a : A)) = (a : A) := by
  let g : ℝ≥0 → ℝ≥0 := fun t => t * (1 - t)⁻¹
  let f : ℝ≥0 → ℝ≥0 := fun t => 1 - (1 + t)⁻¹
  have haA₀ : 0 ≤ (a : A) := ha₀
  have haA₁ : ‖(a : A)‖₊ < 1 := ha₁
  have hg_nonneg : 0 ≤ cfcₙ g (a : A) := cfcₙ_nonneg_of_predicate
  have heq : resolventApprox 1 (cfcₙ g (a : A)) = cfcₙ f (cfcₙ g (a : A)) := by
    rw [resolventApprox_eq_cfcₙ_one_sub_inv zero_lt_one hg_nonneg, inv_one, one_smul,
      cfcₙ_nnreal_eq_real f (cfcₙ g (a : A)) hg_nonneg]
    refine cfcₙ_congr fun t ht => ?_
    have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg _ hg_nonneg t ht
    simp [f, ht0]
  rw [heq, ← cfcₙ_comp f g (a : A)
    (by fun_prop (disch := intro _ _; positivity)) (by simp [f, tsub_self])
    (by
      have (x : ℝ≥0) (hx : x ∈ quasispectrum ℝ≥0 (a : A)) : 1 - x ≠ 0 :=
        (tsub_pos_of_lt (lt_of_le_of_lt (CStarAlgebra.le_nnNorm_of_mem_quasispectrum hx) haA₁)).ne'
      fun_prop)
    (by simp [g]) haA₀]
  conv_rhs => rw [← cfcₙ_id ℝ≥0 (a : A)]
  exact cfcₙ_congr fun x hx =>
    Set.InvOn.one_sub_one_add_inv.1
      (lt_of_le_of_lt (CStarAlgebra.le_nnNorm_of_mem_quasispectrum hx) haA₁)

/-- **Comparison with `CStarAlgebra.approximateUnit`.** For a closed two-sided ideal `I`, the
filter pushed forward along `I.approxUnit` from `atTop` refines the canonical filter
`CStarAlgebra.approximateUnit I`. -/
theorem map_approxUnit_le_approximateUnit :
    Filter.map I.approxUnit atTop ≤ CStarAlgebra.approximateUnit I := by
  classical
  rw [(Filter.atTop_basis.map I.approxUnit).le_basis_iff
    (CStarAlgebra.hasBasis_approximateUnit I)]
  rintro a ⟨ha₀, ha₁⟩
  let g : ℝ≥0 → ℝ≥0 := fun t => t * (1 - t)⁻¹
  let b : A := cfcₙ g (a : A)
  have hb₀ : 0 ≤ b := cfcₙ_nonneg_of_predicate
  have hb_mem : b ∈ I.toNonUnitalStarSubalgebra :=
    cfcₙ_nnreal_mem g (I.mem_toNonUnitalStarSubalgebra.mpr a.2)
  let yA : A := cfcₙ Real.sqrt b
  have hy_mem : yA ∈ I.toSubmodule :=
    I.mem_toSubmodule.mpr (I.mem_toNonUnitalStarSubalgebra.mp (cfcₙ_mem Real.sqrt hb_mem))
  have hy_sq : star yA * yA = b := by
    rw [IsSelfAdjoint.star_eq (by cfc_tac), ← cfcₙ_mul ..]
    convert cfcₙ_id' ℝ b using 1
    exact cfcₙ_congr fun r hr => Real.mul_self_sqrt (quasispectrum_nonneg_of_nonneg b hb₀ r hr)
  let y : I.toSubmodule := ⟨yA, hy_mem⟩
  refine ⟨({y}, OrderDual.toDual ⟨1, zero_lt_one⟩), trivial, ?_⟩
  rintro _ ⟨i, hi, rfl⟩
  refine ⟨?_, mem_closedBall_zero_iff.mpr (I.norm_approxUnit_lt_one i).le⟩
  rw [Set.mem_ofPred_eq, ← Subtype.coe_le_coe, I.coe_approxUnit]
  calc
    (a : A) = resolventApprox 1 b := (I.resolventApprox_one_cfcₙ_inv a ha₀ ha₁).symm
    _ = I.toSubmodule.rightApproxUnit ({y}, OrderDual.toDual ⟨1, zero_lt_one⟩) := by
      simp [Submodule.rightApproxUnit, y, hy_sq]
    _ ≤ I.toSubmodule.rightApproxUnit i := I.toSubmodule.rightApproxUnit_mono hi

/-- For a closed two-sided ideal `I`, `Filter.map I.approxUnit atTop` is an increasing two-sided
approximate unit of `I` (cf. `CStarAlgebra.increasingApproximateUnit`). -/
theorem isIncreasingApproximateUnit_map_approxUnit :
    (Filter.map I.approxUnit atTop).IsIncreasingApproximateUnit where
  tendsto_mul_left m :=
    (CStarAlgebra.increasingApproximateUnit I).tendsto_mul_left m
      |>.mono_left I.map_approxUnit_le_approximateUnit
  tendsto_mul_right m :=
    (CStarAlgebra.increasingApproximateUnit I).tendsto_mul_right m
      |>.mono_left I.map_approxUnit_le_approximateUnit
  neBot := by classical exact Filter.atTop_neBot.map I.approxUnit
  eventually_nonneg :=
    (CStarAlgebra.increasingApproximateUnit I).eventually_nonneg.filter_mono
      I.map_approxUnit_le_approximateUnit
  eventually_norm :=
    (CStarAlgebra.increasingApproximateUnit I).eventually_norm.filter_mono
      I.map_approxUnit_le_approximateUnit

end Order

/-- Along `atTop`, `(I.approxUnit i : A) * x → x` for every `x` in a closed two-sided ideal `I`. -/
theorem tendsto_approxUnit_mul {x : A} (hx : x ∈ I) :
    Tendsto (fun i => (I.approxUnit i : A) * x) atTop (𝓝 x) := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  let x₀ : I := ⟨x, hx⟩
  have hl : Tendsto (fun i => I.approxUnit i * x₀) atTop (𝓝 x₀) :=
    Filter.tendsto_map'_iff.mp (I.isIncreasingApproximateUnit_map_approxUnit.tendsto_mul_right x₀)
  exact (continuous_subtype_val.tendsto x₀).comp hl

/-- Along `atTop`, `x * (I.approxUnit i : A) → x` for every `x` in a closed two-sided ideal `I`. -/
theorem tendsto_mul_approxUnit {x : A} (hx : x ∈ I) :
    Tendsto (fun i => x * (I.approxUnit i : A)) atTop (𝓝 x) := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  let x₀ : I := ⟨x, hx⟩
  have hr : Tendsto (fun i => x₀ * I.approxUnit i) atTop (𝓝 x₀) :=
    Filter.tendsto_map'_iff.mp (I.isIncreasingApproximateUnit_map_approxUnit.tendsto_mul_left x₀)
  exact (continuous_subtype_val.tendsto x₀).comp hr

end TwoSidedIdeal

end
