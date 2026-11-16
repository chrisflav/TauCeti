/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IntermediateField

/-!
# Topological ring instances for intermediate fields

This file provides the subspace `IsTopologicalRing` instance on an intermediate field
`E : IntermediateField K L` of a topological field extension, together with continuity of the
scalar action of `K` on `E` when `K` acts continuously on `L`. Together with Mathlib's
`IntermediateField.continuousSMul` (`ContinuousSMul E X`), these instances allow intermediate
fields to be used directly as coefficient rings in continuous representation theory and module
topologies.
-/

public section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [TopologicalSpace L]

/-- An intermediate field of a topological ring extension inherits the structure of a topological
ring for the subspace topology. -/
instance instIsTopologicalRing [IsTopologicalRing L] (E : IntermediateField K L) :
    IsTopologicalRing E :=
  inferInstanceAs (IsTopologicalRing E.toSubring)

/-- If the base field `K` acts continuously on `L`, then `K` acts continuously on every
intermediate field `E : IntermediateField K L` equipped with the subspace topology. -/
instance continuousSMul_base [TopologicalSpace K] [ContinuousSMul K L]
    (E : IntermediateField K L) : ContinuousSMul K E :=
  Topology.IsInducing.continuousSMul Topology.IsInducing.subtypeVal continuous_id rfl

end IntermediateField
