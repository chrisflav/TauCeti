/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.MapCLM
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Canonical surjection from `ℓ¹` of the closed unit ball

Every Banach space `E` over a nontrivially normed field `𝕜` receives a canonical contractive
surjection `TauCeti.unitBallSurjection 𝕜 E` from the scalar-valued `ℓ¹` space indexed by its
closed unit ball `Metric.closedBall (0 : E) 1`, sending an absolutely summable family `α` to
`∑' x, α x • (x : E)`.

Over a densely normed field `𝕜`, every vector `y` of norm strictly below `r` can be written as
`c • (c⁻¹ • y)` for a scalar `c` with `‖y‖ < ‖c‖ < r`, so a single coordinate vector lifts `y`
into the open ball of radius `r`. Thus `TauCeti.unitBallSurjection 𝕜 E` is a metric quotient map:
it maps every open ball centered at `0` onto the open ball of the same radius, and precomposing any
bounded semilinear operator with it preserves the operator norm. This places every Banach space as
a metric quotient of a canonical `ℓ¹` space, dual to `TauCeti.dualBallEmbedding`.

## Main declarations

* `TauCeti.unitBallSurjection`: the canonical contractive surjection
  `ℓ¹(closedBall (0 : E) 1, 𝕜) →L[𝕜] E`.
* `TauCeti.ball_subset_image_unitBallSurjection_ball` and
  `TauCeti.image_unitBallSurjection_ball`: over a densely normed field, `unitBallSurjection` is a
  metric quotient map.
* `ContinuousLinearMap.norm_comp_unitBallSurjection`: precomposing with `unitBallSurjection`
  preserves operator norms.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

section NontriviallyNormedField

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The canonical contractive surjection from scalar-valued `ℓ¹` on the closed unit ball of `E`
onto `E`, sending `α` to `∑' x, α x • (x : E)`. -/
noncomputable def unitBallSurjection :
    lp (fun _ : Metric.closedBall (0 : E) 1 ↦ 𝕜) 1 →L[𝕜] E :=
  ContinuousLinearMap.coprodLpOne
    (fun x : Metric.closedBall (0 : E) 1 ↦ ContinuousLinearMap.toSpanSingleton 𝕜 (x : E)) 1
    fun x ↦ by
      rw [← NNReal.coe_le_one, coe_nnNorm, ContinuousLinearMap.norm_toSpanSingleton]
      exact mem_closedBall_zero_iff.mp x.2

/-- The weighted unit-ball vectors `α x • (x : E)` sum unconditionally to
`unitBallSurjection 𝕜 E α`. -/
theorem hasSum_unitBallSurjection (α : lp (fun _ : Metric.closedBall (0 : E) 1 ↦ 𝕜) 1) :
    HasSum (fun x : Metric.closedBall (0 : E) 1 ↦ α x • (x : E)) (unitBallSurjection 𝕜 E α) := by
  rw [unitBallSurjection]
  exact (ContinuousLinearMap.hasSum_coprodLpOne _ 1 _ α).congr_fun fun _ ↦ by simp

/-- `unitBallSurjection` evaluates to the unconditional sum `∑' x, α x • (x : E)`. -/
theorem unitBallSurjection_apply (α : lp (fun _ : Metric.closedBall (0 : E) 1 ↦ 𝕜) 1) :
    unitBallSurjection 𝕜 E α = ∑' x : Metric.closedBall (0 : E) 1, α x • (x : E) := by
  simp [unitBallSurjection, ContinuousLinearMap.coprodLpOne_apply]

/-- On a coordinate vector `single 1 x c`, `unitBallSurjection` evaluates to `c • (x : E)`. -/
@[simp]
theorem unitBallSurjection_single [DecidableEq (Metric.closedBall (0 : E) 1)]
    (x : Metric.closedBall (0 : E) 1) (c : 𝕜) :
    unitBallSurjection 𝕜 E (lp.single 1 x c) = c • (x : E) := by
  simp [unitBallSurjection]

/-- Precomposing `unitBallSurjection` with the `x`-th coordinate inclusion gives scalar
multiplication of `(x : E)`. -/
@[simp]
theorem unitBallSurjection_comp_singleContinuousLinearMap
    [DecidableEq (Metric.closedBall (0 : E) 1)] (x : Metric.closedBall (0 : E) 1) :
    unitBallSurjection 𝕜 E ∘L
      lp.singleContinuousLinearMap 𝕜 (fun _ : Metric.closedBall (0 : E) 1 ↦ 𝕜) 1 x =
      ContinuousLinearMap.toSpanSingleton 𝕜 (x : E) := by
  simp [unitBallSurjection]

/-- `unitBallSurjection` is contractive in nonnegative operator norm. -/
theorem nnnorm_unitBallSurjection_le : ‖unitBallSurjection 𝕜 E‖₊ ≤ 1 :=
  ContinuousLinearMap.nnnorm_coprodLpOne_le _ 1 _

/-- `unitBallSurjection` has operator norm at most one. -/
theorem norm_unitBallSurjection_le : ‖unitBallSurjection 𝕜 E‖ ≤ 1 := by
  exact_mod_cast nnnorm_unitBallSurjection_le 𝕜 E

/-- `unitBallSurjection` is surjective over every nontrivially normed field. -/
theorem unitBallSurjection_surjective : Function.Surjective (unitBallSurjection 𝕜 E) := by
  classical
  intro y
  obtain ⟨c, hyc⟩ := NormedField.exists_lt_norm 𝕜 ‖y‖
  have hc0 : c ≠ 0 := norm_pos_iff.mp ((norm_nonneg y).trans_lt hyc)
  have hu : c⁻¹ • y ∈ Metric.closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
    exact inv_mul_le_one_of_le₀ hyc.le (norm_nonneg c)
  exact ⟨lp.single 1 ⟨c⁻¹ • y, hu⟩ c, by simp [smul_inv_smul₀ hc0]⟩

end NontriviallyNormedField

section DenselyNormedField

variable (𝕜 E : Type*) [DenselyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Over a densely normed field, `unitBallSurjection` lifts every vector of norm less than `r` to
a coordinate vector of norm less than `r`. -/
theorem ball_subset_image_unitBallSurjection_ball (r : ℝ) :
    Metric.ball (0 : E) r ⊆ unitBallSurjection 𝕜 E '' Metric.ball 0 r := by
  classical
  intro y hy
  have hyr : ‖y‖ < r := mem_ball_zero_iff.mp hy
  obtain ⟨c, hyc, hcr⟩ := NormedField.exists_lt_norm_lt 𝕜 (norm_nonneg y) hyr
  have hc0 : c ≠ 0 := norm_pos_iff.mp ((norm_nonneg y).trans_lt hyc)
  have hu : c⁻¹ • y ∈ Metric.closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
    exact inv_mul_le_one_of_le₀ hyc.le (norm_nonneg c)
  refine ⟨lp.single 1 ⟨c⁻¹ • y, hu⟩ c, ?_, ?_⟩
  · simpa [mem_ball_zero_iff, lp.norm_single zero_lt_one] using hcr
  · simp [smul_inv_smul₀ hc0]

/-- Over a densely normed field, `unitBallSurjection` maps each open ball about `0` onto the open
ball of the same radius. -/
theorem image_unitBallSurjection_ball (r : ℝ) :
    unitBallSurjection 𝕜 E '' Metric.ball 0 r = Metric.ball 0 r :=
  ContinuousLinearMap.image_ball_eq_ball (norm_unitBallSurjection_le 𝕜 E)
    (ball_subset_image_unitBallSurjection_ball 𝕜 E) r

/-- On a nontrivial space over a densely normed field, `unitBallSurjection` has norm one. -/
@[simp]
theorem norm_unitBallSurjection [Nontrivial E] : ‖unitBallSurjection 𝕜 E‖ = 1 := by
  simpa using (ContinuousLinearMap.id 𝕜 E).norm_comp_of_ball_subset_image_ball
    (norm_unitBallSurjection_le 𝕜 E) (ball_subset_image_unitBallSurjection_ball 𝕜 E)

/-- On a nontrivial space over a densely normed field, `unitBallSurjection` has nonnegative
operator norm one. -/
@[simp]
theorem nnnorm_unitBallSurjection [Nontrivial E] : ‖unitBallSurjection 𝕜 E‖₊ = 1 :=
  NNReal.eq (norm_unitBallSurjection 𝕜 E)

end DenselyNormedField

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ E F : Type*} [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- Precomposing a bounded semilinear map with `TauCeti.unitBallSurjection` preserves its operator
norm. -/
@[simp]
theorem norm_comp_unitBallSurjection (f : E →SL[σ₁₂] F) :
    ‖f.comp (TauCeti.unitBallSurjection 𝕜 E)‖ = ‖f‖ :=
  f.norm_comp_of_ball_subset_image_ball (TauCeti.norm_unitBallSurjection_le 𝕜 E)
    (TauCeti.ball_subset_image_unitBallSurjection_ball 𝕜 E)

/-- Precomposing a bounded semilinear map with `TauCeti.unitBallSurjection` preserves its
nonnegative operator norm. -/
@[simp]
theorem nnnorm_comp_unitBallSurjection (f : E →SL[σ₁₂] F) :
    ‖f.comp (TauCeti.unitBallSurjection 𝕜 E)‖₊ = ‖f‖₊ :=
  NNReal.eq f.norm_comp_unitBallSurjection

end ContinuousLinearMap
