/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.RepresentationTheory.Continuous.RestrictScalars.Basic

/-!
# Operator-norm properties of scalar restriction

On seminormed spaces over compatible nontrivially normed fields `𝕜` and `𝕜'`, restricting scalars
of a continuous representation (`ContRepresentation.restrictScalars`) preserves the operator norm
of every action operator (`ContRepresentation.norm_restrictScalars`) and hence continuity into the
operator-norm topology (`ContRepresentation.continuous_restrictScalars_iff`).

These results are separated from `TauCeti.RepresentationTheory.Continuous.RestrictScalars.Basic`
so that purely algebraic and topological consumers (such as `TopRep` and continuous cohomology) do
not pull normed-space typeclass instances into their environment.

## Main results

* `ContRepresentation.norm_restrictScalars`: `‖π.restrictScalars 𝕜' g‖ = ‖π g‖`.
* `ContRepresentation.continuous_restrictScalars_iff`:
  `Continuous (π.restrictScalars 𝕜') ↔ Continuous π`.
-/

public section

namespace ContRepresentation

section Normed

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [Monoid G]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' V]
  [LinearMap.CompatibleSMul V V 𝕜' 𝕜]

/-- Restricting scalars between compatible nontrivially normed fields preserves the operator norm of
every action operator. -/
@[simp]
theorem norm_restrictScalars (π : ContRepresentation 𝕜 G V) (g : G) :
    ‖π.restrictScalars 𝕜' g‖ = ‖π g‖ := by
  rw [restrictScalars_apply]
  exact le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ (π g).le_opNorm x)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦
      ((π g).restrictScalars 𝕜').le_opNorm x)

/-- Restricting scalars between compatible nontrivially normed fields preserves continuity into
the operator-norm topology. -/
theorem continuous_restrictScalars_iff [TopologicalSpace G] (π : ContRepresentation 𝕜 G V) :
    Continuous (π.restrictScalars 𝕜') ↔ Continuous π := by
  have hisom : Isometry
      (ContinuousLinearMap.restrictScalars 𝕜' : (V →L[𝕜] V) → (V →L[𝕜'] V)) :=
    Isometry.of_dist_eq fun f g ↦ by
      rw [dist_eq_norm, dist_eq_norm]
      exact le_antisymm
        (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ (f - g).le_opNorm x)
        (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦
          (f.restrictScalars 𝕜' - g.restrictScalars 𝕜').le_opNorm x)
  have heq : ⇑(π.restrictScalars 𝕜') = ContinuousLinearMap.restrictScalars 𝕜' ∘ ⇑π :=
    funext fun g ↦ restrictScalars_apply 𝕜' π g
  rw [heq]
  exact (hisom.isUniformInducing.isInducing.continuous_iff (f := π)).symm

end Normed

end ContRepresentation
