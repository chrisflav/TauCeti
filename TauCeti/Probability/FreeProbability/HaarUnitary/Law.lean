/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.HaarUnitary.Basic
public import TauCeti.Probability.FreeProbability.Law.Unitary
public import TauCeti.RepresentationTheory.Compact.Haar
import TauCeti.MeasureTheory.Group.Circle

/-!
# The circle-valued spectral law of a Haar unitary

Let `A` be a unital C⋆-algebra and `φ : A →ₚ[ℂ] ℂ` a positive linear functional. An element
`u : A` is a **Haar unitary** for `φ` if and only if its circle-valued spectral measure
`φ.unitaryLaw u : Measure Circle` equals normalized Haar probability measure `haarProb Circle` on
`Circle` (`PositiveLinearMap.unitaryLaw_eq_haarProb_iff`). Neither `u ∈ unitary A` nor `φ 1 = 1`
needs to be assumed separately: both conditions are encoded in `φ.unitaryLaw u = haarProb Circle`
(since `φ.unitaryLaw u = 0 ≠ haarProb Circle` when `u ∉ unitary A`).

Consequences in C⋆-probability spaces:

* **Functional calculus integration** (`TauCeti.IsHaarUnitary.apply_cfc`): for every `f : ℂ → ℂ`
  continuous on `spectrum ℂ u`, `φ (cfc f u) = ∫ z : Circle, f z ∂haarProb Circle`.
* **Full circle spectrum** (`TauCeti.IsHaarUnitary.spectrum_eq_sphere`): because `haarProb Circle`
  is positive on nonempty open sets and concentrated on `spectrum ℂ u`, every Haar unitary in a
  C⋆-algebra has `spectrum ℂ u = Metric.sphere 0 1`, even without assuming `φ` is faithful.
* **Commutative C⋆-realization** (`TauCeti.isHaarUnitary_integralPositiveLinearMap_haarProb`): in
  `C(Circle, ℂ)` equipped with `ContinuousMap.integralPositiveLinearMap (haarProb Circle)`, the
  coordinate function `z ↦ (z : ℂ)` is a Haar unitary.

## Main declarations

* `TauCeti.integral_zpow_haarProb_circle`: Fourier moments of `haarProb Circle`.
* `PositiveLinearMap.unitaryLaw_eq_haarProb_iff`: `φ.unitaryLaw u = haarProb Circle` if and only if
  `IsHaarUnitary φ.toLinearMap u`.
* `TauCeti.IsHaarUnitary.unitaryLaw_eq_haarProb`, `TauCeti.IsHaarUnitary.apply_cfc`, and
  `TauCeti.IsHaarUnitary.spectrum_eq_sphere`: spectral law, functional calculus expectation, and
  full-circle spectrum of a Haar unitary.
* `TauCeti.isHaarUnitary_integralPositiveLinearMap_haarProb`: canonical commutative C⋆-realization
  on `C(Circle, ℂ)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Math. Soc.
  Lecture Note Ser. 335, Cambridge University Press (2006), Lectures 1 and 15.
-/

public section

open MeasureTheory Metric Set TauCeti
open scoped ComplexOrder

namespace TauCeti

/-- The Fourier (integer-power) moments of normalized Haar probability measure `haarProb Circle` on
`Circle` are `1` at `0` and `0` elsewhere. -/
@[simp]
theorem integral_zpow_haarProb_circle (n : ℤ) :
    ∫ z : Circle, (z : ℂ) ^ n ∂haarProb Circle = if n = 0 then 1 else 0 := by
  simp [integral_zpow_circle_of_isMulLeftInvariant]

end TauCeti

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ) {u : A}

/-- **The spectral law of a Haar unitary.** An element `u` of a C⋆-algebra has normalized Haar
probability measure `haarProb Circle` as its unitary law with respect to `φ` if and only if `u` is
a Haar unitary for `φ`.

Neither `u ∈ unitary A` nor `φ 1 = 1` needs to be assumed: when `u ∉ unitary A`,
`φ.unitaryLaw u = 0 ≠ haarProb Circle` and `¬ IsHaarUnitary φ.toLinearMap u`. -/
theorem unitaryLaw_eq_haarProb_iff :
    unitaryLaw φ u = haarProb Circle ↔ IsHaarUnitary φ.toLinearMap u := by
  by_cases hu : u ∈ unitary A
  · rw [eq_comm, eq_unitaryLaw_iff_forall_integral_zpow hu, isHaarUnitary_iff_apply_zpow]
    simp only [integral_zpow_haarProb_circle, hu, exists_true_left,
      PositiveLinearMap.coe_toLinearMap]
    exact forall_congr' fun _ => eq_comm
  · rw [unitaryLaw_of_not_mem_unitary φ hu]
    refine ⟨fun h => ?_, fun h => (hu h.mem_unitary).elim⟩
    have h0 : (0 : Measure Circle) univ = haarProb Circle univ :=
      congrArg (fun μ : Measure Circle => μ univ) h
    simp at h0

end PositiveLinearMap

namespace TauCeti

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A →ₚ[ℂ] ℂ} {u : A}

/-- The unitary law of a Haar unitary in a C⋆-probability space is normalized Haar measure on
`Circle`. -/
theorem IsHaarUnitary.unitaryLaw_eq_haarProb (h : IsHaarUnitary φ.toLinearMap u) :
    φ.unitaryLaw u = haarProb Circle :=
  (PositiveLinearMap.unitaryLaw_eq_haarProb_iff φ).2 h

/-- Evaluating `φ` on `cfc f u` for a Haar unitary `u` integrates `f` against normalized Haar
probability measure on `Circle`. -/
theorem IsHaarUnitary.apply_cfc (h : IsHaarUnitary φ.toLinearMap u) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ u) := by cfc_cont_tac) :
    φ (cfc f u) = ∫ z : Circle, f z ∂haarProb Circle := by
  rw [← φ.integral_unitaryLaw h.mem_unitary f hf, h.unitaryLaw_eq_haarProb]

/-- Every Haar unitary in a C⋆-algebra has the entire unit circle `Metric.sphere 0 1` as its
spectrum, even without assuming faithfulness of `φ`. -/
theorem IsHaarUnitary.spectrum_eq_sphere (h : IsHaarUnitary φ.toLinearMap u) :
    spectrum ℂ u = sphere (0 : ℂ) 1 := by
  have h0 : haarProb Circle (((↑) : Circle → ℂ) ⁻¹' (spectrum ℂ u)ᶜ) = 0 := by
    rw [← h.unitaryLaw_eq_haarProb, φ.unitaryLaw_preimage_compl_spectrum u]
  have hopen : IsOpen (((↑) : Circle → ℂ) ⁻¹' (spectrum ℂ u)ᶜ) :=
    (spectrum.isClosed u).isOpen_compl.preimage
      (continuous_subtype_val : Continuous fun z : Circle => (z : ℂ))
  have hempty : (((↑) : Circle → ℂ) ⁻¹' (spectrum ℂ u)ᶜ) = ∅ :=
    (@IsOpen.measure_eq_zero_iff Circle _ _ (haarProb Circle)
      (isHaarMeasure_haarProb Circle).toIsOpenPosMeasure _ hopen).mp h0
  ext z
  refine ⟨fun hz => mem_sphere_zero_iff_norm.mpr
    (CStarRing.norm_of_mem_unitary (spectrum_subset_unitary_of_mem_unitary h.mem_unitary hz)),
    fun hz => ?_⟩
  by_contra hns
  have hmem : (⟨z, hz⟩ : Circle) ∈ (((↑) : Circle → ℂ) ⁻¹' (spectrum ℂ u)ᶜ) := hns
  rw [hempty] at hmem
  exact hmem

end CStar

/-- **Commutative C⋆-realization of a Haar unitary.** In the commutative C⋆-algebra `C(Circle, ℂ)`
equipped with integration against normalized Haar measure `haarProb Circle`, the coordinate function
`z ↦ (z : ℂ)` is a Haar unitary. -/
theorem isHaarUnitary_integralPositiveLinearMap_haarProb :
    IsHaarUnitary (ContinuousMap.integralPositiveLinearMap (𝕜 := ℂ) (haarProb Circle)).toLinearMap
      (⟨(↑), continuous_subtype_val⟩ : C(Circle, ℂ)) :=
  (PositiveLinearMap.unitaryLaw_eq_haarProb_iff _).1
    (PositiveLinearMap.unitaryLaw_integralPositiveLinearMap_id (haarProb Circle))

end TauCeti
