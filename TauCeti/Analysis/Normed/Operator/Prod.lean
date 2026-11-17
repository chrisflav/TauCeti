/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Operator norm of maps on a product

The continuous linear map `(x, y) ↦ f x + g y` out of a product (`ContinuousLinearMap.coprod`) has
operator norm at most `‖f‖ + ‖g‖` (`ContinuousLinearMap.opNorm_coprod_le`). This bounds solution
operators assembled from separate operators for each component of the data, for instance the
forcing and the initial datum of an evolution equation. The product map `(x, y) ↦ (f x, g y)`
(`ContinuousLinearMap.prodMap`) has operator norm `max ‖f‖ ‖g‖`
(`ContinuousLinearMap.opNorm_prodMap`), and a finite indexed product map `x ↦ fun i ↦ f i (x i)`
has operator norm `‖f‖` (`ContinuousLinearMap.opNorm_pi_comp_proj`). A continuous linear map out
of `𝕜 × 𝕜` has operator norm at most `‖f (1, 0)‖ + ‖f (0, 1)‖`
(`ContinuousLinearMap.opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one`).
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- The operator norm of the product map `(x, y) ↦ (f x, g y)` equals `max ‖f‖ ‖g‖`. -/
@[simp]
theorem opNorm_prodMap {H : Type*} [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
    (f : E →L[𝕜] F) (g : G →L[𝕜] H) : ‖f.prodMap g‖ = max ‖f‖ ‖g‖ := by
  refine le_antisymm ?_ (max_le ?_ ?_)
  · refine opNorm_le_bound _ (le_max_of_le_left (norm_nonneg f)) fun p ↦ ?_
    simp only [coe_prodMap', Prod.norm_def]
    exact max_le
      ((f.le_opNorm p.1).trans (mul_le_mul (le_max_left _ _) (le_max_left _ _)
        (norm_nonneg _) (le_max_of_le_left (norm_nonneg f))))
      ((g.le_opNorm p.2).trans (mul_le_mul (le_max_right _ _) (le_max_right _ _)
        (norm_nonneg _) (le_max_of_le_left (norm_nonneg f))))
  · refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    calc ‖f x‖ ≤ ‖(f.prodMap g) (x, (0 : G))‖ := by simp [Prod.norm_def]
      _ ≤ ‖f.prodMap g‖ * ‖(x, (0 : G))‖ := (f.prodMap g).le_opNorm _
      _ = ‖f.prodMap g‖ * ‖x‖ := by simp [Prod.norm_def]
  · refine opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_
    calc ‖g y‖ ≤ ‖(f.prodMap g) ((0 : E), y)‖ := by simp [Prod.norm_def]
      _ ≤ ‖f.prodMap g‖ * ‖((0 : E), y)‖ := (f.prodMap g).le_opNorm _
      _ = ‖f.prodMap g‖ * ‖y‖ := by simp [Prod.norm_def]

/-- The operator norm of a finite coordinatewise product map `x ↦ fun i ↦ f i (x i)` equals the
supremum norm `‖f‖` of the family of operators. -/
@[simp]
theorem opNorm_pi_comp_proj {ι : Type*} [Fintype ι] {M N : ι → Type*}
    [∀ i, SeminormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)]
    [∀ i, SeminormedAddCommGroup (N i)] [∀ i, NormedSpace 𝕜 (N i)]
    (f : ∀ i, M i →L[𝕜] N i) :
    ‖ContinuousLinearMap.pi fun i ↦ (f i).comp (ContinuousLinearMap.proj i)‖ = ‖f‖ := by
  classical
  refine le_antisymm ?_ ?_
  · refine norm_pi_le_of_le (fun i ↦ ?_) (norm_nonneg f)
    refine ((f i).opNorm_comp_le _).trans ?_
    refine (mul_le_of_le_one_right (norm_nonneg _)
      (opNorm_le_bound _ zero_le_one fun x ↦ ?_)).trans (norm_le_pi_norm f i)
    simpa only [one_mul, proj_apply] using norm_le_pi_norm x i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_
    refine (f i).opNorm_le_bound (norm_nonneg _) fun v ↦ ?_
    let L := ContinuousLinearMap.pi fun j ↦ (f j).comp (ContinuousLinearMap.proj j)
    calc ‖f i v‖ ≤ ‖L (Pi.single i v)‖ := by
          simpa [L, Pi.single_eq_same] using norm_le_pi_norm (L (Pi.single i v)) i
      _ ≤ ‖L‖ * ‖(Pi.single i v : ∀ j, M j)‖ := L.le_opNorm _
      _ ≤ ‖L‖ * ‖v‖ := by
          refine mul_le_mul_of_nonneg_left
            ((pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun j ↦ ?_) (norm_nonneg _)
          by_cases hji : j = i
          · subst hji; simp
          · simp [Pi.single_eq_of_ne hji]

/-- The operator norm of `(x, y) ↦ f x + g y` is at most `‖f‖ + ‖g‖`. -/
theorem opNorm_coprod_le (f : E →L[𝕜] G) (g : F →L[𝕜] G) : ‖f.coprod g‖ ≤ ‖f‖ + ‖g‖ := by
  rw [← comp_fst_add_comp_snd]
  exact (opNorm_add_le _ _).trans (add_le_add
    ((f.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_fst_le _ _ _)))
    ((g.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_snd_le _ _ _))))

/-- A continuous linear map out of `𝕜 × 𝕜` has operator norm at most the sum of the norms of its
values on the coordinate vectors. -/
theorem opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one (f : 𝕜 × 𝕜 →L[𝕜] G) :
    ‖f‖ ≤ ‖f (1, 0)‖ + ‖f (0, 1)‖ := by
  refine f.opNorm_le_bound (by positivity) fun p ↦ ?_
  have hp : f p = p.1 • f (1, 0) + p.2 • f (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    simp
  rw [hp, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, mul_comm]
  · exact mul_le_mul_of_nonneg_left (_root_.norm_fst_le p) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_left (_root_.norm_snd_le p) (norm_nonneg _)

end ContinuousLinearMap
