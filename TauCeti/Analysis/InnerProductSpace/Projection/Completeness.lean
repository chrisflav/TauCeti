/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Closedness and completeness of projected subspaces

A subspace that admits an orthogonal projection is the range of a continuous idempotent and is
therefore closed. The sum of two orthogonal projected subspaces also admits an orthogonal
projection — given by the sum of the two projections — and is therefore closed, without requiring
the ambient inner product space to be complete. In a complete ambient inner-product space, a
projected subspace is itself complete, and closedness, completeness, and existence of an orthogonal
projection are equivalent.

The completeness observation also appears in
`ForTauCeti/Analysis/InnerProductSpace/ReducingSubspace.lean` of the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0).
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A subspace admitting an orthogonal projection is closed. -/
theorem isClosed_of_hasOrthogonalProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsClosed (U : Set E) := by
  rw [← U.range_starProjection]
  exact ContinuousLinearMap.IsIdempotentElem.isClosed_range U.isIdempotentElem_starProjection

private theorem IsOrtho.sub_add_starProjection_mem_orthogonal_sup {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⟂ V) (x : E) :
    x - (U.starProjection x + V.starProjection x) ∈ (U ⊔ V)ᗮ := by
  rw [← inf_orthogonal, mem_inf]
  refine ⟨?_, ?_⟩
  · have hV : V.starProjection x ∈ Uᗮ := h.symm (V.starProjection_apply_mem x)
    simpa [sub_add_eq_sub_sub] using Uᗮ.sub_mem (U.sub_starProjection_mem_orthogonal x) hV
  · have hU : U.starProjection x ∈ Vᗮ := h (U.starProjection_apply_mem x)
    simpa [sub_add_eq_sub_sub, sub_right_comm] using
      Vᗮ.sub_mem (V.sub_starProjection_mem_orthogonal x) hU

/-- The sum of two orthogonal subspaces admitting orthogonal projections also admits an orthogonal
projection. -/
theorem IsOrtho.hasOrthogonalProjection_sup {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⟂ V) :
    (U ⊔ V).HasOrthogonalProjection :=
  ⟨fun x ↦ ⟨U.starProjection x + V.starProjection x,
    add_mem_sup (U.starProjection_apply_mem x) (V.starProjection_apply_mem x),
    h.sub_add_starProjection_mem_orthogonal_sup x⟩⟩

/-- The sum of two orthogonal subspaces admitting orthogonal projections is closed. -/
theorem IsOrtho.isClosed_sup {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⟂ V) :
    IsClosed ((U ⊔ V : Submodule 𝕜 E) : Set E) :=
  have := h.hasOrthogonalProjection_sup
  (U ⊔ V).isClosed_of_hasOrthogonalProjection

/-- The orthogonal projection onto the sum of two orthogonal projected subspaces is the sum of
their orthogonal projections. -/
theorem IsOrtho.starProjection_sup {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [(U ⊔ V).HasOrthogonalProjection] (h : U ⟂ V) :
    (U ⊔ V).starProjection = U.starProjection + V.starProjection :=
  ContinuousLinearMap.ext fun x ↦ eq_starProjection_of_mem_orthogonal
    (add_mem_sup (U.starProjection_apply_mem x) (V.starProjection_apply_mem x))
    (h.sub_add_starProjection_mem_orthogonal_sup x)

/-- A subspace admitting an orthogonal projection is complete when the ambient space is. -/
theorem isComplete_coe_of_hasOrthogonalProjection [CompleteSpace E] (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : IsComplete (U : Set E) :=
  (U.isClosed_of_hasOrthogonalProjection).isComplete

variable [CompleteSpace E]

/-- In a complete space, a subspace admitting an orthogonal projection is a complete space.

This is not an instance, since `HasOrthogonalProjection.ofCompleteSpace` goes the other way. -/
theorem completeSpace_coe_of_hasOrthogonalProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : CompleteSpace U :=
  U.isComplete_coe_of_hasOrthogonalProjection.completeSpace_coe

/-- In a complete space, a subspace has an orthogonal projection exactly when it is closed. -/
theorem hasOrthogonalProjection_iff_isClosed {U : Submodule 𝕜 E} :
    U.HasOrthogonalProjection ↔ IsClosed (U : Set E) :=
  ⟨fun _ ↦ U.isClosed_of_hasOrthogonalProjection, fun h ↦
    have := h.isComplete.completeSpace_coe
    .ofCompleteSpace U⟩

/-- In a complete space, a subspace has an orthogonal projection exactly when it is complete. -/
theorem hasOrthogonalProjection_iff_completeSpace {U : Submodule 𝕜 E} :
    U.HasOrthogonalProjection ↔ CompleteSpace U :=
  ⟨fun _ ↦ U.completeSpace_coe_of_hasOrthogonalProjection, fun _ ↦ .ofCompleteSpace U⟩

end Submodule
