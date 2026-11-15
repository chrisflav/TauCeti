/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# The derivative of the pullback of an alternating map along a composite

For `f : F [⋀^ι]→L[𝕜] G` and `g : E →L[𝕜] F`, Mathlib's
`ContinuousAlternatingMap.fderivCompContinuousLinearMap f g` is the derivative of
`h ↦ f.compContinuousLinearMap h` at `g`. In the direction `B ∘ g` of a composite with an
endomorphism `B` of `F`, it is the pullback along `g` of the same derivative at the identity, which
is the action of `B` on `f` as a derivation:

`f.fderivCompContinuousLinearMap g (B ∘ g) = (f.fderivCompContinuousLinearMap id B) ∘ g`.

This is the form in which the derivation action of the derivative of a vector field, the second
term of the Lie derivative of a differential form, appears when a pullback along a flow is
differentiated in time. We also record the operator-norm bounds `‖compContinuousLinearMapCLM g‖ ≤
‖g‖ ^ |ι|` and `‖f.fderivCompContinuousLinearMap g‖ ≤ |ι| ‖g‖ ^ (|ι| - 1) ‖f‖` controlling both
terms of the Fréchet derivative of a varying pullback `(f x).compContinuousLinearMap (g x)`.
-/

public section

namespace ContinuousAlternatingMap

variable {𝕜 E F G ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Operator-norm bound on the pullback operator `f ↦ f.compContinuousLinearMap g`: its norm is at
most `‖g‖ ^ |ι|`. -/
theorem norm_compContinuousLinearMapCLM_le (g : E →L[𝕜] F) :
    ‖(compContinuousLinearMapCLM g : (F [⋀^ι]→L[𝕜] G) →L[𝕜] E [⋀^ι]→L[𝕜] G)‖ ≤
      ‖g‖ ^ Fintype.card ι :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f ↦ by
    rw [compContinuousLinearMapCLM_apply, mul_comm]
    exact f.norm_compContinuousLinearMap_le g

/-- Operator-norm bound on the derivative of `h ↦ f.compContinuousLinearMap h` at `g`: its norm is
at most `|ι| ‖g‖ ^ (|ι| - 1) ‖f‖`. -/
theorem norm_fderivCompContinuousLinearMap_le (f : F [⋀^ι]→L[𝕜] G) (g : E →L[𝕜] F) :
    ‖f.fderivCompContinuousLinearMap g‖ ≤ Fintype.card ι * ‖g‖ ^ (Fintype.card ι - 1) * ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun dg ↦ ?_
  refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [fderivCompContinuousLinearMap_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm (i : ι) : ‖f fun j ↦ Function.update (fun _ ↦ g) i dg j (v j)‖ ≤
      ‖g‖ ^ (Fintype.card ι - 1) * ‖f‖ * ‖dg‖ * ∏ j, ‖v j‖ := by
    refine (f.le_opNorm _).trans ?_
    rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun j ↦ ‖v j‖),
      Function.update_self]
    have hcompl : ∏ j ∈ ({i}ᶜ : Finset ι), ‖Function.update (fun _ : ι ↦ g) i dg j (v j)‖ ≤
        ‖g‖ ^ (Fintype.card ι - 1) * ∏ j ∈ ({i}ᶜ : Finset ι), ‖v j‖ := by
      rw [← Finset.card_singleton i, ← Finset.card_compl, ← Finset.prod_const,
        ← Finset.prod_mul_distrib]
      gcongr with j hj
      simpa only [Function.update_of_ne (by simpa using hj)] using g.le_opNorm (v j)
    calc ‖f‖ * (‖dg (v i)‖ * ∏ j ∈ ({i}ᶜ : Finset ι),
          ‖Function.update (fun _ ↦ g) i dg j (v j)‖)
        ≤ ‖f‖ * ((‖dg‖ * ‖v i‖) *
            (‖g‖ ^ (Fintype.card ι - 1) * ∏ j ∈ ({i}ᶜ : Finset ι), ‖v j‖)) := by
          gcongr
          exact dg.le_opNorm (v i)
      _ = ‖g‖ ^ (Fintype.card ι - 1) * ‖f‖ * ‖dg‖ *
          (‖v i‖ * ∏ j ∈ ({i}ᶜ : Finset ι), ‖v j‖) := by ring
  calc ∑ i : ι, ‖f fun j ↦ Function.update (fun _ ↦ g) i dg j (v j)‖
      ≤ ∑ _i : ι, (‖g‖ ^ (Fintype.card ι - 1) * ‖f‖ * ‖dg‖ * ∏ j, ‖v j‖) :=
        Finset.sum_le_sum fun i _ ↦ hterm i
    _ = Fintype.card ι * ‖g‖ ^ (Fintype.card ι - 1) * ‖f‖ * ‖dg‖ * ∏ j, ‖v j‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- The derivative of the pullback at `g` in the direction `B ∘ g` is the pullback along `g` of the
derivative at the identity in the direction `B`. -/
theorem fderivCompContinuousLinearMap_comp (f : F [⋀^ι]→L[𝕜] G) (g : E →L[𝕜] F)
    (B : F →L[𝕜] F) :
    f.fderivCompContinuousLinearMap g (B ∘L g) =
      (f.fderivCompContinuousLinearMap (.id 𝕜 F) B).compContinuousLinearMap g := by
  ext v
  simp only [fderivCompContinuousLinearMap_apply, compContinuousLinearMap_apply]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg f (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

end ContinuousAlternatingMap
