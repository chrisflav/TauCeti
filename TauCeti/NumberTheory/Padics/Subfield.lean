/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.LocalField
public import TauCeti.Analysis.Normed.Field.Krasner
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.NormedField

import TauCeti.NumberTheory.LocalField.Padic

/-!
# Finite subfields of `PadicAlgCl p`

Every finite intermediate field `ℚ_[p] ⊆ E ⊆ PadicAlgCl p` inherits the spectral norm of
`PadicAlgCl p`, which extends the `p`-adic norm of `ℚ_[p]` (its normalized absolute value). By
Krasner's lemma and the density of `ℚ` in `ℚ_[p]`:

* Every finite intermediate field `E / ℚ_[p]` inside `PadicAlgCl p` is generated over `ℚ_[p]` by an
  element algebraic over `ℚ` (`PadicAlgCl.exists_isAlgebraic_adjoin_simple_eq`).
* There are only countably many finite intermediate fields `ℚ_[p] ⊆ E ⊆ PadicAlgCl p`
  (`PadicAlgCl.countable_finiteDimensional`).
* Each finite intermediate field `E` is complete and closed in `PadicAlgCl p` (via
  `IntermediateField.isComplete_of_finiteDimensional` and
  `IntermediateField.isClosed_of_finiteDimensional`).
* Equipped with `TauCeti.algebraicExtensionValuativeRel ℚ_[p] E` and its existing subspace
  topology from `PadicAlgCl p`, `E` is a nonarchimedean local field whose integer ring is
  `{x : E | ‖(x : PadicAlgCl p)‖ ≤ 1}`.

## Main results

* `PadicAlgCl.exists_isAlgebraic_adjoin_simple_eq`: every finite `E / ℚ_[p]` in `PadicAlgCl p` is
  `ℚ_[p]⟮β⟯` with `β` algebraic over `ℚ`.
* `PadicAlgCl.countable_finiteDimensional`: the finite intermediate fields of `PadicAlgCl p / ℚ_[p]`
  are countable.
* `PadicAlgCl.algebraicExtensionNormedFieldTopology_eq`: the spectral-norm topology on a finite
  intermediate field `E` agrees with its subspace topology from `PadicAlgCl p`.
* `PadicAlgCl.isNonarchimedeanLocalField_of_finiteDimensional`: a finite intermediate field `E` is
  a nonarchimedean local field for its subspace topology and `algebraicExtensionValuativeRel`.
* `PadicAlgCl.mem_integerRing_iff_norm_le_one`: an element of `E` lies in `𝒪[E]` if and only if
  its norm in `PadicAlgCl p` is at most `1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 3.
-/

public section

open IntermediateField ValuativeRel

namespace PadicAlgCl

variable {p : ℕ} [Fact p.Prime]

private theorem denseRange_algebraMap_rat : DenseRange (algebraMap ℚ ℚ_[p]) := by
  have h : ⇑(algebraMap ℚ ℚ_[p]) = Rat.cast := funext (eq_ratCast _)
  rw [h]
  exact Padic.denseRange_ratCast p

private theorem norm_algebraMap_intermediateField (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    (x : ℚ_[p]) :
    ‖algebraMap ℚ_[p] E x‖ = TauCeti.normalizedAbsoluteValue ℚ_[p] x := by
  rw [norm_algebraMap', ← coe_nnNorm, ← Padic.normalizedAbsoluteValue_eq_nnnorm p x]
  norm_cast

/-- **Every finite intermediate field `ℚ_[p] ⊆ E ⊆ PadicAlgCl p` is generated over `ℚ_[p]` by an
element algebraic over `ℚ`.** -/
theorem exists_isAlgebraic_adjoin_simple_eq (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] E] :
    ∃ β : PadicAlgCl p, IsAlgebraic ℚ β ∧ ℚ_[p]⟮β⟯ = E :=
  E.exists_isAlgebraic_adjoin_simple_eq (denseRange_algebraMap_rat (p := p))

variable (p) in
/-- **There are countably many finite intermediate fields `ℚ_[p] ⊆ E ⊆ PadicAlgCl p`.** -/
theorem countable_finiteDimensional :
    Set.Countable {E : IntermediateField ℚ_[p] (PadicAlgCl p) | FiniteDimensional ℚ_[p] E} :=
  IntermediateField.countable_finiteDimensional ℚ ℚ_[p] (PadicAlgCl p)
    (denseRange_algebraMap_rat (p := p))

/-- The spectral-norm topology `TauCeti.algebraicExtensionNormedFieldTopology ℚ_[p] E` on an
intermediate field `E ⊆ PadicAlgCl p` agrees with the subspace topology inherited from
`PadicAlgCl p`. -/
theorem algebraicExtensionNormedFieldTopology_eq (E : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    TauCeti.algebraicExtensionNormedFieldTopology ℚ_[p] E =
      (inferInstance : TopologicalSpace E) :=
  TauCeti.algebraicExtensionNormedFieldTopology_eq_of_norm (norm_algebraMap_intermediateField E)

/-- A finite intermediate field `E ⊆ PadicAlgCl p`, equipped with its subspace topology from
`PadicAlgCl p` and `TauCeti.algebraicExtensionValuativeRel ℚ_[p] E`, is a nonarchimedean local
field. -/
theorem isNonarchimedeanLocalField_of_finiteDimensional
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] :
    letI := TauCeti.algebraicExtensionValuativeRel ℚ_[p] E
    IsNonarchimedeanLocalField E :=
  TauCeti.finiteExtension_isNonarchimedeanLocalField_of_norm (norm_algebraMap_intermediateField E)

/-- For `TauCeti.algebraicExtensionValuativeRel ℚ_[p] E` on an intermediate field
`E ⊆ PadicAlgCl p`, an element of `E` lies in `𝒪[E]` if and only if its norm in `PadicAlgCl p` is
at most `1`. -/
theorem mem_integerRing_iff_norm_le_one
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : E) :
    letI := TauCeti.algebraicExtensionValuativeRel ℚ_[p] E
    x ∈ 𝒪[E] ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 :=
  TauCeti.mem_integerRing_algebraicExtensionValuativeRel_iff
    (norm_algebraMap_intermediateField E) x

end PadicAlgCl
