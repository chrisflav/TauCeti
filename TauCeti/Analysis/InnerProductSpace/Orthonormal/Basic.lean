/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Pairwise distance and countability of orthonormal families

Distinct vectors of an orthonormal family in an inner-product space lie at distance `√2`
(`Orthonormal.norm_sub_eq_sqrt_two`, `Orthonormal.dist_eq_sqrt_two`). Consequently, the open balls
of radius `√2 / 2` around the vectors of an orthonormal family are pairwise disjoint, so any
orthonormal family in a separable inner-product space has countable index type
(`Orthonormal.countable_of_separableSpace`).
-/

public section

open scoped InnerProductSpace

namespace Orthonormal

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {v : ι → E}

/-- Distinct vectors in an orthonormal family satisfy `‖v i - v j‖ = √2`. -/
theorem norm_sub_eq_sqrt_two (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i - v j‖ = Real.sqrt 2 := by
  have hsq : ‖v i - v j‖ ^ 2 = 2 := by
    rw [norm_sub_sq (𝕜 := 𝕜), hv.1 i, hv.1 j, hv.2 hij, map_zero]
    norm_num
  rw [← Real.sqrt_sq (norm_nonneg (v i - v j)), hsq]

/-- Distinct vectors in an orthonormal family lie at distance `√2`. -/
theorem dist_eq_sqrt_two (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    dist (v i) (v j) = Real.sqrt 2 := by
  rw [dist_eq_norm, hv.norm_sub_eq_sqrt_two hij]

/-- Every orthonormal family in a separable inner-product space has countable index type. -/
theorem countable_of_separableSpace [TopologicalSpace.SeparableSpace E] (hv : Orthonormal 𝕜 v) :
    Countable ι := by
  have hpos : 0 < Real.sqrt 2 / 2 := by positivity
  have hdisj : Pairwise fun i j : ι ↦
      Disjoint (Metric.ball (v i) (Real.sqrt 2 / 2)) (Metric.ball (v j) (Real.sqrt 2 / 2)) := by
    intro i j hij
    exact Metric.ball_disjoint_ball (by rw [hv.dist_eq_sqrt_two hij]; ring_nf; exact le_rfl)
  exact hdisj.countable_of_isOpen_disjoint (fun _ ↦ Metric.isOpen_ball)
    fun i ↦ ⟨v i, Metric.mem_ball_self hpos⟩

end Orthonormal
