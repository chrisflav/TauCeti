/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Generator
public import TauCeti.Analysis.Semigroups.Generator.ComplexLinear

/-!
# Time reversal of complex-linear strongly continuous groups

Complex linearity of the forward operators implies complex linearity at negative times by
invertibility. The complex generator of the reflected group is the negative of the original
complex generator, just as for the real generator.

## Main results

* `StronglyContinuousGroup.reflect_isComplexLinear`: time reversal preserves complex linearity.
* `StronglyContinuousGroup.map_smul_of_isComplexLinear`: a complex-linear C₀-group commutes with
  complex scalar multiplication at every real time.
* `StronglyContinuousGroup.reflect_complexGenerator`: time reversal negates the complex generator.
-/

public section

namespace TauCeti.Semigroups.StronglyContinuousGroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- If the forward operators of a strongly continuous group are complex linear, so are the
forward operators of its time reversal. -/
theorem reflect_isComplexLinear (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) : U.reflect.toSemigroup.IsComplexLinear := by
  apply (StronglyContinuousSemigroup.isComplexLinear_iff _).mpr
  intro t z x
  apply (U.bijective (t : ℝ)).injective
  have hcomm := hU.map_smul t z (U (-(t : ℝ)) x)
  simpa only [toSemigroup_apply, reflect_apply, U.map_apply_map_neg_apply] using hcomm.symm

/-- If the forward semigroup of a strongly continuous group is complex linear, then every group
operator at every real time commutes with complex scalar multiplication. -/
theorem map_smul_of_isComplexLinear (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (t : ℝ) (z : ℂ) (x : X) :
    U t (z • x) = z • U t x := by
  rcases le_or_gt 0 t with ht | ht
  · rw [← U.toSemigroup_realOperator_of_nonneg ht]
    exact hU.realOperator_map_smul t z x
  · have hnt : 0 ≤ -t := neg_nonneg.mpr ht.le
    rw [← neg_neg t, ← U.reflect_toSemigroup_realOperator_of_nonneg hnt]
    exact (U.reflect_isComplexLinear hU).realOperator_map_smul (-t) z x

/-- Time reversal negates the complex generator of a complex-linear strongly continuous group.
The generator domain is preserved. -/
@[simp]
theorem reflect_complexGenerator [CompleteSpace X] (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) :
    U.reflect.toSemigroup.complexGenerator (U.reflect_isComplexLinear hU) =
      -U.toSemigroup.complexGenerator hU := by
  apply LinearPMap.restrictScalars_injective ℝ
  rw [StronglyContinuousSemigroup.complexGenerator_restrictScalars,
    ← generator_def, reflect_generator, LinearPMap.restrictScalars_neg,
    StronglyContinuousSemigroup.complexGenerator_restrictScalars, generator_def]

end TauCeti.Semigroups.StronglyContinuousGroup
