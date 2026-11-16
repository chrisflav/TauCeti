/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic

/-!
# Compatibility of the spectral norm with an existing normed-field structure

An algebraic extension `M / K` of a nonarchimedean local field carries the spectral-norm
structures `TauCeti.algebraicExtensionNormedField K M`,
`TauCeti.algebraicExtensionNormedFieldTopology K M`, and
`TauCeti.algebraicExtensionValuativeRel K M`. When `M` already carries a `NormedField` structure
extending the normalized absolute value of `K` (for example, a finite intermediate field of
`PadicAlgCl p` with its subspace norm), uniqueness of the extended absolute value
(`TauCeti.algebraicExtensionNormedField_norm_unique`) identifies the spectral norm with the
existing norm and its topology with the existing norm topology.

Installing `TauCeti.algebraicExtensionValuativeRel K M` locally therefore makes `M`, with its
existing topology and without introducing a topology diamond, a valuatively topologized field whose
valuation ring is the closed unit ball `{x : M | ‖x‖ ≤ 1}` — and, when `M / K` is finite, a
nonarchimedean local field.

## Main results

* `TauCeti.algebraicExtensionNormedField_norm_eq`: the spectral norm agrees with any existing
  normed-field norm on `M` extending `normalizedAbsoluteValue K`.
* `TauCeti.algebraicExtensionNormedFieldTopology_eq_of_norm`: the spectral-norm topology agrees
  with the existing norm topology on `M`.
* `TauCeti.algebraicExtension_isValuativeTopology_of_norm`: the existing topology on `M` is the
  valuative topology for `algebraicExtensionValuativeRel K M`.
* `TauCeti.mem_integerRing_algebraicExtensionValuativeRel_iff`: for
  `algebraicExtensionValuativeRel K M`, `x ∈ 𝒪[M]` if and only if `‖x‖ ≤ 1`.
* `TauCeti.finiteExtension_isNonarchimedeanLocalField_of_norm`: a finite extension `M / K` whose
  norm extends `normalizedAbsoluteValue K` is a nonarchimedean local field for its existing
  topology and `algebraicExtensionValuativeRel K M`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 (Theorem 4.8) and §6.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable {K M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [NormedField M] [Algebra K M] [Algebra.IsAlgebraic K M]

/-- If an algebraic extension `M` of a nonarchimedean local field `K` already carries a normed-field
structure extending the normalized absolute value of `K`, its norm agrees with the spectral norm of
`algebraicExtensionNormedField K M`. -/
theorem algebraicExtensionNormedField_norm_eq
    (hnorm : ∀ x : K, ‖algebraMap K M x‖ = normalizedAbsoluteValue K x) (x : M) :
    @norm M (algebraicExtensionNormedField K M).toNorm x = ‖x‖ := by
  let f : AbsoluteValue M ℝ :=
    { toFun := norm
      map_mul' := norm_mul
      nonneg' := norm_nonneg
      eq_zero' _ := norm_eq_zero
      add_le' := norm_add_le }
  exact (algebraicExtensionNormedField_norm_unique K (f := f) hnorm x).symm

/-- If the norm on an algebraic extension `M / K` extends the normalized absolute value of `K`, then
the spectral-norm topology `algebraicExtensionNormedFieldTopology K M` agrees with the existing
norm topology of `M`. -/
theorem algebraicExtensionNormedFieldTopology_eq_of_norm
    (hnorm : ∀ x : K, ‖algebraMap K M x‖ = normalizedAbsoluteValue K x) :
    algebraicExtensionNormedFieldTopology K M =
      ‹NormedField M›.toUniformSpace.toTopologicalSpace := by
  have hdist (y x : M) :
      @dist M (algebraicExtensionNormedField K M).toDist y x = dist y x := by
    rw [(algebraicExtensionNormedField K M).dist_eq y x,
      algebraicExtensionNormedField_norm_eq hnorm, dist_eq_norm, neg_add_eq_sub, norm_sub_rev]
  refine TopologicalSpace.ext_nhds fun x ↦ Filter.ext fun s ↦ ?_
  rw [@Metric.mem_nhds_iff M (algebraicExtensionNormedField K M).toPseudoMetricSpace,
    Metric.mem_nhds_iff]
  simp only [Metric.ball, Set.subset_def, Set.mem_ofPred_eq, hdist]

/-- If the norm on an algebraic extension `M / K` extends the normalized absolute value of `K`, then
the existing topology on `M` is the valuative topology for `algebraicExtensionValuativeRel K M`. -/
theorem algebraicExtension_isValuativeTopology_of_norm
    (hnorm : ∀ x : K, ‖algebraMap K M x‖ = normalizedAbsoluteValue K x) :
    letI := algebraicExtensionValuativeRel K M
    IsValuativeTopology M := by
  have h := algebraicExtension_isValuativeTopology K M
  rwa [algebraicExtensionNormedFieldTopology_eq_of_norm hnorm] at h

/-- For `algebraicExtensionValuativeRel K M`, when the existing norm on `M` extends the normalized
absolute value of `K`, an element lies in `𝒪[M]` if and only if its norm is at most `1`. -/
theorem mem_integerRing_algebraicExtensionValuativeRel_iff
    (hnorm : ∀ x : K, ‖algebraMap K M x‖ = normalizedAbsoluteValue K x) (x : M) :
    letI := algebraicExtensionValuativeRel K M
    x ∈ 𝒪[M] ↔ ‖x‖ ≤ 1 := by
  let _ := algebraicExtensionValuativeRel K M
  rw [Valuation.mem_integer_iff, ← map_one (valuation M), ← (valuation M).vle_iff_le,
    algebraicExtensionValuativeRel_vle_iff, algebraicExtensionNormedField_norm_eq hnorm,
    algebraicExtensionNormedField_norm_eq hnorm, norm_one]

/-- A finite normed extension `M` of a nonarchimedean local field `K` whose norm extends the
normalized absolute value of `K` is a nonarchimedean local field for its existing topology and
`algebraicExtensionValuativeRel K M`. -/
theorem finiteExtension_isNonarchimedeanLocalField_of_norm [Module.Finite K M]
    (hnorm : ∀ x : K, ‖algebraMap K M x‖ = normalizedAbsoluteValue K x) :
    letI := algebraicExtensionValuativeRel K M
    IsNonarchimedeanLocalField M := by
  have h := finiteExtension_isNonarchimedeanLocalField K M
  rwa [algebraicExtensionNormedFieldTopology_eq_of_norm hnorm] at h

end TauCeti
