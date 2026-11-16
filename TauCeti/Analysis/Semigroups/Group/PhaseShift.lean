/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.ComplexLinear
public import TauCeti.Analysis.Semigroups.Group.Unitary
public import TauCeti.Analysis.Semigroups.PhaseShift

/-!
# Phase shifts of a complex-linear strongly continuous group

For a complex-linear C₀-group `U` on a complex normed space and a real angular frequency `ω`, the
*phase shift* is the C₀-group

`(U.phaseShift hU ω) t = exp (-i ω t) • U t`.

This is the two-sided counterpart of `TauCeti.Semigroups.StronglyContinuousSemigroup.phaseShift`:
its forward semigroup is the semigroup phase shift of `U.toSemigroup`, it preserves every two-sided
growth bound and unitarity, and it shifts any common eigenspace at frequency `ω` to the fixed-point
subspace at frequency `0`.

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift`: the phase-shifted C₀-group
  `t ↦ exp (-i ω t) • U t`.
* `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift_toSemigroup`: restriction to nonnegative
  times agrees with `StronglyContinuousSemigroup.phaseShift`.
* `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift_isComplexLinear`,
  `HasGrowthBound.phaseShift`, and `IsUnitary.phaseShift`: phase shifts preserve complex
  linearity, two-sided growth bounds, and unitarity.
* `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift_zero`, `phaseShift_phaseShift`, and
  `reflect_phaseShift`: algebraic laws of phase shifting.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section II.2.2 (rescaled semigroups).
-/

public section

noncomputable section

namespace TauCeti.Semigroups.StronglyContinuousGroup

section PhaseShift

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The phase shift of a complex-linear C₀-group by angular frequency `ω : ℝ`: the C₀-group
`t ↦ exp (-i ω t) • U t`. -/
def phaseShift (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    StronglyContinuousGroup X where
  toFun t := Complex.exp (-(ω * t) * Complex.I) • U t
  map_zero' := by
    simp
  map_add' s t := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, smul_apply]
    rw [U.map_add_apply, U.map_smul_of_isComplexLinear hU, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  continuousAt_zero' x := by
    have hphase : ContinuousAt (fun t : ℝ => Complex.exp (-(ω * t) * Complex.I)) 0 := by fun_prop
    have horbit : ContinuousAt (fun t : ℝ => U t x) 0 := U.continuousAt_zero' x
    simpa [ContinuousAt, U.map_zero_apply] using hphase.tendsto.smul horbit.tendsto

/-- The group operator of a phase shift at time `t`. -/
@[simp]
theorem phaseShift_apply (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω t : ℝ) :
    U.phaseShift hU ω t = Complex.exp (-(ω * t) * Complex.I) • U t := by
  rw [phaseShift]
  rfl

/-- Pointwise form of `StronglyContinuousGroup.phaseShift_apply`. -/
theorem phaseShift_apply_apply (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω t : ℝ) (x : X) :
    U.phaseShift hU ω t x = Complex.exp (-(ω * t) * Complex.I) • U t x := by
  rw [phaseShift_apply, smul_apply]

/-- The forward semigroup of a phase-shifted C₀-group is the phase shift of its forward
semigroup. -/
@[simp]
theorem phaseShift_toSemigroup (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    (U.phaseShift hU ω).toSemigroup = U.toSemigroup.phaseShift hU ω := by
  ext t x
  simp [phaseShift_apply]

/-- A phase shift of a complex-linear C₀-group is again complex linear. -/
theorem phaseShift_isComplexLinear (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    (U.phaseShift hU ω).toSemigroup.IsComplexLinear := by
  rw [phaseShift_toSemigroup]
  exact hU.phaseShift ω

/-- The zero phase shift leaves a C₀-group unchanged. -/
@[simp]
theorem phaseShift_zero (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) :
    U.phaseShift hU 0 = U := by
  ext t x
  simp

/-- Successive phase shifts add their angular frequencies. -/
@[simp]
theorem phaseShift_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω₁ ω₂ : ℝ) :
    (U.phaseShift hU ω₁).phaseShift (U.phaseShift_isComplexLinear hU ω₁) ω₂ =
      U.phaseShift hU (ω₁ + ω₂) := by
  ext t x
  simp only [phaseShift_apply_apply]
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Time reversal negates the frequency of a phase shift. -/
@[simp]
theorem reflect_phaseShift (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω : ℝ) :
    (U.phaseShift hU ω).reflect = U.reflect.phaseShift (U.reflect_isComplexLinear hU) (-ω) := by
  ext t x
  simp only [reflect_apply, phaseShift_apply_apply]
  congr 2
  push_cast
  ring

/-- A phase shift multiplies by a unimodular scalar, so it preserves every two-sided growth
bound. -/
theorem HasGrowthBound.phaseShift {U : StronglyContinuousGroup X} {r M : ℝ}
    (hb : U.HasGrowthBound r M) (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    (U.phaseShift hU ω).HasGrowthBound r M := by
  refine hasGrowthBound_of_bound hb.one_le fun t => ?_
  rw [phaseShift_apply]
  calc ‖Complex.exp (-(ω * t) * Complex.I) • U t‖
      ≤ ‖Complex.exp (-(ω * t) * Complex.I)‖ * ‖U t‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ = ‖U t‖ := by
        rw [Complex.norm_exp]
        simp
    _ ≤ M * Real.exp (r * |t|) := hb.bound t

end PhaseShift

section PhaseShiftUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A phase shift of a unitary C₀-group is again unitary. -/
theorem IsUnitary.phaseShift {U : StronglyContinuousGroup H} (hU : U.IsUnitary) (ω : ℝ) :
    (U.phaseShift hU.isComplexLinear ω).IsUnitary := by
  refine IsUnitary.intro fun t x y => ?_
  simp only [phaseShift_apply_apply, inner_smul_left, inner_smul_right, hU.inner_map_map]
  rw [← mul_assoc, ← Complex.exp_conj, ← Complex.exp_add]
  simp

end PhaseShiftUnitary

end TauCeti.Semigroups.StronglyContinuousGroup

end
