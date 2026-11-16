/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IntermediateField
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Topological ring instances and closedness on intermediate fields

Mathlib equips an intermediate field `E : IntermediateField K L` of a topological field extension
with the subspace topology inherited from `L` and continuous scalar actions
(`IntermediateField.continuousSMul`). This file records the corresponding subspace
`IsSemitopologicalRing`, `IsTopologicalRing`, and `IsTopologicalDivisionRing` instances (mirroring
`Subring.instIsTopologicalRing`), together with completeness and closedness of finite intermediate
fields over a complete nontrivially normed base field.

## Main results

* `IntermediateField.instIsSemitopologicalRing`: an intermediate field of a semitopological ring is
  a semitopological ring.
* `IntermediateField.instIsTopologicalRing`: an intermediate field of a topological ring is a
  topological ring.
* `IntermediateField.instIsTopologicalDivisionRing`: an intermediate field of a topological division
  ring is a topological division ring.
* `IntermediateField.isComplete_of_finiteDimensional`,
  `IntermediateField.isClosed_of_finiteDimensional`: finite intermediate fields over a complete
  nontrivially normed field are complete and closed.
-/

public section

namespace IntermediateField

section TopologicalRing

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [TopologicalSpace L]

instance instIsSemitopologicalRing [IsSemitopologicalRing L] (E : IntermediateField K L) :
    IsSemitopologicalRing E :=
  inferInstanceAs (IsSemitopologicalRing E.toSubring)

instance instIsTopologicalRing [IsTopologicalRing L] (E : IntermediateField K L) :
    IsTopologicalRing E :=
  inferInstanceAs (IsTopologicalRing E.toSubring)

instance instIsTopologicalDivisionRing [IsTopologicalDivisionRing L] (E : IntermediateField K L) :
    IsTopologicalDivisionRing E where
  continuousAt_inv₀ x hx := by
    refine Topology.IsInducing.subtypeVal.continuousAt_iff.mpr ?_
    have hx' : (x : L) ≠ 0 := fun h ↦ hx (Subtype.ext h)
    exact (continuousAt_inv₀ hx').comp continuous_subtype_val.continuousAt

end TopologicalRing

section FiniteDimensional

/-- **Every finite intermediate field over a complete nontrivially normed field is complete.** -/
theorem isComplete_of_finiteDimensional {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [UniformSpace L] [IsUniformAddGroup L] [ContinuousSMul K L]
    [T2Space L] (E : IntermediateField K L) [FiniteDimensional K E] :
    IsComplete (E : Set L) :=
  E.toSubmodule.isComplete_of_finiteDimensional

/-- **Every finite intermediate field over a complete nontrivially normed field is closed** in any
Hausdorff topological `K`-algebra `L`. -/
theorem isClosed_of_finiteDimensional {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul K L]
    [T2Space L] (E : IntermediateField K L) [FiniteDimensional K E] :
    IsClosed (E : Set L) :=
  E.toSubmodule.isClosed_of_finiteDimensional

end FiniteDimensional

end IntermediateField
