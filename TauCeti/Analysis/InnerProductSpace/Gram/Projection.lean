/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Gram matrices of orthogonal projections

For nested subspaces `U ≤ V` of a real or complex inner product space admitting orthogonal
projections `P_U` and `P_V`, the residual projections `P_{Uᗮ} v = P_{Vᗮ} v + (P_V v - P_U v)`
split orthogonally. Consequently, for any indexed family of vectors `v : ι → E`, the difference
of the Gram matrices of `P_{Uᗮ} ∘ v` and `P_{Vᗮ} ∘ v` is the Gram matrix of
`(P_V - P_U) ∘ v`, hence positive semidefinite.

Taking `U = ⊥` shows that projecting onto `Vᗮ` lowers the Gram matrix by the Gram matrix of
`P_V ∘ v`, with equality if and only if every vector `v i` is already orthogonal to `V`.

## Main results

* `Submodule.gram_starProjection_orthogonal_sub_of_le`: for `U ≤ V`,
  `gram 𝕜 (P_{Uᗮ} ∘ v) - gram 𝕜 (P_{Vᗮ} ∘ v) = gram 𝕜 ((P_V - P_U) ∘ v)`.
* `Submodule.posSemidef_gram_starProjection_orthogonal_sub_of_le`: for `U ≤ V`, the difference
  `gram 𝕜 (P_{Uᗮ} ∘ v) - gram 𝕜 (P_{Vᗮ} ∘ v)` is positive semidefinite.
* `Submodule.gram_sub_gram_starProjection_orthogonal`:
  `gram 𝕜 v - gram 𝕜 (P_{Vᗮ} ∘ v) = gram 𝕜 (P_V ∘ v)`.
* `Submodule.posSemidef_gram_sub_gram_starProjection_orthogonal`:
  `gram 𝕜 v - gram 𝕜 (P_{Vᗮ} ∘ v)` is positive semidefinite.
* `Submodule.gram_starProjection_orthogonal_eq_gram_iff`:
  `gram 𝕜 (P_{Vᗮ} ∘ v) = gram 𝕜 v` if and only if `∀ i, v i ∈ Vᗮ`.
-/

public section

open Matrix
open scoped ComplexOrder InnerProductSpace

namespace Submodule

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For nested projected subspaces `U ≤ V`, the difference of the Gram matrices of the residuals
in `Uᗮ` and `Vᗮ` equals the Gram matrix of the projection differences `P_V (v i) - P_U (v i)`. -/
theorem gram_starProjection_orthogonal_sub_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hUV : U ≤ V) (v : ι → E) :
    gram 𝕜 (fun i ↦ Uᗮ.starProjection (v i)) - gram 𝕜 (fun i ↦ Vᗮ.starProjection (v i)) =
      gram 𝕜 (fun i ↦ V.starProjection (v i) - U.starProjection (v i)) := by
  ext i j
  simp only [Matrix.sub_apply, gram_apply]
  have hsplit (x : E) :
      Uᗮ.starProjection x = Vᗮ.starProjection x + (V.starProjection x - U.starProjection x) := by
    simp only [starProjection_orthogonal_val]
    abel
  have hmem (x : E) : V.starProjection x - U.starProjection x ∈ V :=
    V.sub_mem (V.starProjection_apply_mem x) (hUV (U.starProjection_apply_mem x))
  have hcross₁ : ⟪Vᗮ.starProjection (v i), V.starProjection (v j) - U.starProjection (v j)⟫_𝕜 = 0 :=
    V.inner_left_of_mem_orthogonal (hmem (v j)) (Vᗮ.starProjection_apply_mem (v i))
  have hcross₂ : ⟪V.starProjection (v i) - U.starProjection (v i), Vᗮ.starProjection (v j)⟫_𝕜 = 0 :=
    V.inner_right_of_mem_orthogonal (hmem (v i)) (Vᗮ.starProjection_apply_mem (v j))
  rw [hsplit (v i), hsplit (v j), inner_add_left, inner_add_right, inner_add_right,
    hcross₁, hcross₂, add_zero, zero_add, add_sub_cancel_left]

/-- For nested projected subspaces `U ≤ V`, projecting onto `Vᗮ` yields a Gram matrix no larger
than projecting onto `Uᗮ` in the Loewner order. -/
theorem posSemidef_gram_starProjection_orthogonal_sub_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hUV : U ≤ V) (v : ι → E) :
    (gram 𝕜 (fun i ↦ Uᗮ.starProjection (v i)) -
      gram 𝕜 (fun i ↦ Vᗮ.starProjection (v i))).PosSemidef := by
  rw [gram_starProjection_orthogonal_sub_of_le hUV v]
  exact posSemidef_gram 𝕜 _

/-- The difference between the Gram matrix of a family `v` and the Gram matrix of its orthogonal
projection onto `Vᗮ` is the Gram matrix of its orthogonal projection onto `V`. -/
theorem gram_sub_gram_starProjection_orthogonal (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (v : ι → E) :
    gram 𝕜 v - gram 𝕜 (fun i ↦ Vᗮ.starProjection (v i)) =
      gram 𝕜 (fun i ↦ V.starProjection (v i)) := by
  simpa [starProjection_bot, starProjection_top] using
    gram_starProjection_orthogonal_sub_of_le (𝕜 := 𝕜) (bot_le : (⊥ : Submodule 𝕜 E) ≤ V) v

/-- Projecting a family of vectors onto `Vᗮ` lowers its Gram matrix in the Loewner order. -/
theorem posSemidef_gram_sub_gram_starProjection_orthogonal (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (v : ι → E) :
    (gram 𝕜 v - gram 𝕜 (fun i ↦ Vᗮ.starProjection (v i))).PosSemidef := by
  rw [V.gram_sub_gram_starProjection_orthogonal v]
  exact posSemidef_gram 𝕜 _

/-- Projecting a family of vectors onto `Vᗮ` preserves its Gram matrix if and only if every vector
in the family is already orthogonal to `V`. -/
theorem gram_starProjection_orthogonal_eq_gram_iff (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (v : ι → E) :
    gram 𝕜 (fun i ↦ Vᗮ.starProjection (v i)) = gram 𝕜 v ↔ ∀ i, v i ∈ Vᗮ := by
  rw [eq_comm, ← sub_eq_zero, V.gram_sub_gram_starProjection_orthogonal v]
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · have hdiag : ⟪V.starProjection (v i), V.starProjection (v i)⟫_𝕜 = 0 := by
      simpa using congrArg (fun M : Matrix ι ι 𝕜 ↦ M i i) h
    exact V.starProjection_apply_eq_zero_iff.mp (inner_self_eq_zero.mp hdiag)
  · ext i j
    simp [V.starProjection_apply_eq_zero_iff.mpr (h i)]

end Submodule
