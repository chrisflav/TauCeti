/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import TauCeti.Analysis.InnerProductSpace.Parseval
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Weak convergence of orthonormal families

By Bessel's inequality for continuous linear functionals (`Orthonormal.summable_norm_apply_sq`),
the values of every continuous linear functional on an orthonormal family are square summable and
therefore tend to zero along the cofinite filter. Consequently, every orthonormal family in an
inner-product space converges weakly to zero along `cofinite`
(`Orthonormal.tendsto_toWeakSpace_zero_cofinite`), with no completeness or norm-separation
assumption on the space.
-/

public section

open Filter Topology

namespace Orthonormal

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Every orthonormal family in a (possibly incomplete) inner-product space converges weakly to
zero along the cofinite filter. -/
theorem tendsto_toWeakSpace_zero_cofinite {v : ι → E} (hv : Orthonormal 𝕜 v) :
    Tendsto (fun i ↦ toWeakSpace 𝕜 E (v i)) cofinite (𝓝 (toWeakSpace 𝕜 E 0)) := by
  refine TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.2 fun φ ↦ ?_
  rw [map_zero, tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun i ↦ ‖φ (v i)‖ ^ 2) cofinite (𝓝 0) :=
    (hv.summable_norm_apply_sq φ).tendsto_cofinite_zero
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

end Orthonormal
