/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Continuity of derivations for the module topology

Let `R` be a commutative topological semiring, `L` a finite free commutative `R`-algebra carrying
the `R`-module topology (`[IsModuleTopology R L]`), and `N` a topological `L`-module with continuous
addition and continuous `L`-scalar multiplication. Expanding an element of `L` in a finite `R`-basis
and applying Leibniz's rule shows that any `k`-derivation `δ : L → N` is continuous on `L` if and
only if its restriction `r ↦ δ (algebraMap R L r)` to `R` is continuous
(`Derivation.continuous_iff_of_isModuleTopology`). No separability or étaleness of `L` over `R` is
required.
-/

public section

namespace Derivation

variable {k R L N : Type*} [CommSemiring k] [CommSemiring R] [TopologicalSpace R]
  [IsTopologicalSemiring R] [CommSemiring L] [Algebra R L] [Algebra k L]
  [Module.Free R L] [Module.Finite R L] [TopologicalSpace L] [IsModuleTopology R L]
  [AddCommMonoid N] [Module L N] [Module k N] [TopologicalSpace N]
  [ContinuousAdd N] [ContinuousSMul L N]

variable (R) in
/-- On a finite free `R`-algebra `L` carrying the `R`-module topology over a topological
commutative semiring `R`, a `k`-derivation `δ : L → N` into a topological `L`-module is continuous
on `L` if and only if its restriction to `R` is continuous. -/
theorem continuous_iff_of_isModuleTopology (δ : Derivation k L N) :
    Continuous δ ↔ Continuous fun r : R ↦ δ (algebraMap R L r) := by
  have : ContinuousAdd L := IsModuleTopology.toContinuousAdd R L
  have halg : Continuous (algebraMap R L) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap R L)
  refine ⟨fun hδ ↦ hδ.comp halg, fun hδ ↦ ?_⟩
  let b := Module.Free.chooseBasis R L
  have hsum (x : L) :
      δ x = ∑ i, (algebraMap R L (b.coord i x) • δ (b i) +
        b i • δ (algebraMap R L (b.coord i x))) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, δ.leibniz, Module.Basis.coord_apply, add_comm]
  refine (continuous_finsetSum _ fun i _ ↦ ?_).congr fun x ↦ (hsum x).symm
  have hcoord : Continuous (b.coord i) := IsModuleTopology.continuous_of_linearMap (b.coord i)
  exact ((halg.comp hcoord).smul continuous_const).add
    (continuous_const.smul (hδ.comp hcoord))

variable (R) in
/-- Variant of `Derivation.continuous_iff_of_isModuleTopology` phrased via
`Derivation.compAlgebraMap`. -/
theorem continuous_iff_continuous_compAlgebraMap_of_isModuleTopology
    [Algebra k R] [IsScalarTower k R L] [Module R N] [IsScalarTower R L N]
    (δ : Derivation k L N) :
    Continuous δ ↔ Continuous (δ.compAlgebraMap R) :=
  δ.continuous_iff_of_isModuleTopology R

end Derivation
