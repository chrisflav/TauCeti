/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic

/-!
# Valuative extensions through algebraic intermediate fields

If a valuative relation on an ambient field extends that of a nonarchimedean local field `K`,
then it also extends any compatible valuative relation on an algebraic intermediate field.
This follows from uniqueness of the valuation class on algebraic extensions of `K`.

When the ambient field `Ω` is a normed field whose norm extends `TauCeti.normalizedAbsoluteValue K`,
the spectral norm on any algebraic intermediate field `E ⊆ Ω` coincides with the restriction of the
ambient norm, so its spectral-norm topology coincides with the subspace topology inherited from `Ω`
and its valuation ring `𝒪[E]` is the closed unit ball `{x ∈ E | ‖(x : Ω)‖ ≤ 1}`.

## Main results

* `IntermediateField.valuativeExtension`: the ambient field is a valuative extension of a
  compatible algebraic intermediate field.
* `IntermediateField.algebraicExtensionNormedField_norm_eq`: the spectral norm on an algebraic
  intermediate field agrees with the ambient norm.
* `IntermediateField.algebraicExtensionNormedFieldTopology_eq`: the spectral-norm topology on an
  algebraic intermediate field equals the subspace topology inherited from the ambient normed field.
* `IntermediateField.mem_integerRing_algebraicExtensionValuativeRel_iff`: membership in `𝒪[E]` is
  equivalent to having ambient norm at most `1`.
-/

public section

open ValuativeRel

namespace IntermediateField

variable {K Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

/-- If the valuative relations on an ambient field `Ω` and an algebraic intermediate field `E`
both extend that of the nonarchimedean local field `K`, then `Ω` is a valuative extension of `E`.
The extension `Ω / K` need not be algebraic. -/
theorem valuativeExtension [ValuativeRel Ω] [ValuativeExtension K Ω]
    (E : IntermediateField K Ω) [Algebra.IsAlgebraic K E] [ValuativeRel E]
    [ValuativeExtension K E] : ValuativeExtension E Ω := by
  have h := E.val.valuativeExtension
  exact ⟨fun {a b} ↦ h.vle_iff_vle (a := a) (b := b)⟩

section NormedAmbient

variable {Ω : Type*} [NormedField Ω] [Algebra K Ω]

/-- The spectral norm on an algebraic intermediate field `E ⊆ Ω` equals the restriction of the
ambient norm whenever the ambient norm extends `TauCeti.normalizedAbsoluteValue K`. -/
theorem algebraicExtensionNormedField_norm_eq (E : IntermediateField K Ω) [Algebra.IsAlgebraic K E]
    (hnorm : ∀ x : K, ‖algebraMap K Ω x‖ = TauCeti.normalizedAbsoluteValue K x) (x : E) :
    (letI := TauCeti.algebraicExtensionNormedField K E; ‖x‖) = ‖(x : Ω)‖ := by
  let f : AbsoluteValue E ℝ :=
    { toFun y := ‖(y : Ω)‖
      map_mul' y z := by simp
      nonneg' y := norm_nonneg _
      eq_zero' y := by simp
      add_le' y z := norm_add_le (y : Ω) (z : Ω) }
  exact (TauCeti.algebraicExtensionNormedField_norm_unique (K := K) (f := f) hnorm x).symm

/-- The spectral-norm topology on an algebraic intermediate field `E ⊆ Ω` coincides with the
subspace topology inherited from `Ω` when the ambient norm extends
`TauCeti.normalizedAbsoluteValue K`. -/
theorem algebraicExtensionNormedFieldTopology_eq (E : IntermediateField K Ω)
    [Algebra.IsAlgebraic K E]
    (hnorm : ∀ x : K, ‖algebraMap K Ω x‖ = TauCeti.normalizedAbsoluteValue K x) :
    TauCeti.algebraicExtensionNormedFieldTopology K E = (inferInstance : TopologicalSpace E) := by
  refine TopologicalSpace.ext_nhds fun x ↦ Filter.ext fun s ↦ ?_
  let nE := TauCeti.algebraicExtensionNormedField K E
  have hdist (y : E) : @dist E nE.toDist y x = dist y x := by
    rw [nE.dist_eq y x, Subtype.dist_eq, dist_eq_norm,
      E.algebraicExtensionNormedField_norm_eq hnorm, neg_add_eq_sub, norm_sub_rev]
    rfl
  rw [@Metric.mem_nhds_iff E nE.toPseudoMetricSpace, Metric.mem_nhds_iff]
  simp only [Set.subset_def, Metric.mem_ball, hdist]

/-- For an algebraic intermediate field `E ⊆ Ω` equipped with `algebraicExtensionValuativeRel K E`,
an element lies in the valuation ring `𝒪[E]` if and only if its ambient norm is at most `1`. -/
theorem mem_integerRing_algebraicExtensionValuativeRel_iff (E : IntermediateField K Ω)
    [Algebra.IsAlgebraic K E]
    (hnorm : ∀ x : K, ‖algebraMap K Ω x‖ = TauCeti.normalizedAbsoluteValue K x) (x : E) :
    letI := TauCeti.algebraicExtensionValuativeRel K E
    x ∈ 𝒪[E] ↔ ‖(x : Ω)‖ ≤ 1 := by
  let _ := TauCeti.algebraicExtensionValuativeRel K E
  rw [Valuation.mem_integer_iff, ← map_one (valuation E), ← (valuation E).vle_iff_le,
    TauCeti.algebraicExtensionValuativeRel_vle_iff,
    E.algebraicExtensionNormedField_norm_eq hnorm, E.algebraicExtensionNormedField_norm_eq hnorm,
    OneMemClass.coe_one, norm_one]

end NormedAmbient

end IntermediateField
