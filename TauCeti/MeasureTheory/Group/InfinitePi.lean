/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.ProductMeasure

/-!
# Haar measure and group invariance for infinite products of probability measures

Let `μ : ∀ i, Measure (α i)` be an arbitrary (possibly uncountable) family of measures. Mathlib
provides subtype-splitting measure preservation
(`MeasureTheory.measurePreserving_piEquivPiSubtypeProd`), arbitrary-cylinder outer-measure
evaluation (`MeasureTheory.Measure.pi_pi`), left/right translation invariance, inversion invariance,
openness positivity, and the Haar measure instance for finite products `Measure.pi μ`
(`Mathlib.MeasureTheory.Constructions.Pi`). This file establishes the corresponding results for the
infinite product measure `Measure.infinitePi μ`:

* `Measure.measurePreserving_piEquivPiSubtypeProd_infinitePi`: splitting coordinates by any
  predicate `p : ι → Prop` via `MeasurableEquiv.piEquivPiSubtypeProd` pushes `Measure.infinitePi μ`
  to the product of the two subtype `infinitePi` measures.
* `Measure.infinitePi_pi'`: `Measure.infinitePi μ ((s : Set ι).pi t) = ∏ i ∈ s, μ i (t i)` for any
  finite set `s : Finset ι` and arbitrary (not necessarily measurable) sets `t i`.
* `Measure.infinitePi.isMulLeftInvariant`, `Measure.infinitePi.isMulRightInvariant`, and
  `Measure.infinitePi.isInvInvariant` (and their additive counterparts): coordinatewise translation
  and inversion invariance pass to `Measure.infinitePi μ` without any countability, topological, or
  probability assumption (since `infinitePi μ = 0` when not all factors are probability measures).
* `Measure.infinitePi.isOpenPosMeasure` and `Measure.infinitePi.isHaarMeasure` (with additive
  counterpart `Measure.infinitePi.isAddHaarMeasure`): an infinite product of probability measures
  positive on nonempty open sets is positive on nonempty open sets (without requiring
  `OpensMeasurableSpace`), and an infinite product of probability Haar measures is a Haar measure.

## References

* P. R. Halmos, *Measure Theory*, Springer (1974), §§38, 60.
* E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*, Vol. I, 2nd ed., Springer (1979), §15.17.
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace MeasureTheory.Measure

section SubtypeProd

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))

/-- Splitting an arbitrary product along a predicate `p : ι → Prop` via
`MeasurableEquiv.piEquivPiSubtypeProd` preserves `Measure.infinitePi`. -/
theorem measurePreserving_piEquivPiSubtypeProd_infinitePi (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α p) (infinitePi μ)
      ((infinitePi fun i : Subtype p ↦ μ i).prod (infinitePi fun i : {i // ¬ p i} ↦ μ i)) := by
  set e := (MeasurableEquiv.piEquivPiSubtypeProd α p).symm
  refine MeasurePreserving.symm e ⟨e.measurable, ?_⟩
  by_cases h : ∀ i, IsProbabilityMeasure (μ i)
  · classical
    have : ∀ i : Subtype p, IsProbabilityMeasure (μ i.1) := fun i ↦ h i.1
    have : ∀ i : {i // ¬ p i}, IsProbabilityMeasure (μ i.1) := fun i ↦ h i.1
    refine eq_infinitePi μ fun s t ht ↦ ?_
    have hpre : e ⁻¹' (s : Set ι).pi t =
        ((s.subtype p : Set (Subtype p)).pi fun i ↦ t i.1) ×ˢ
          ((s.subtype (fun i ↦ ¬ p i) : Set {i // ¬ p i}).pi fun i ↦ t i.1) := by
      ext ⟨y, z⟩
      change (Equiv.piEquivPiSubtypeProd p α).symm (y, z) ∈ (s : Set ι).pi t ↔ _
      simp only [Set.mem_pi, Finset.mem_coe, mem_prod, Finset.mem_subtype, Subtype.forall]
      refine ⟨fun h' ↦ ⟨fun i hp hs ↦ ?_, fun i hnp hs ↦ ?_⟩, fun ⟨h1, h2⟩ i hs ↦ ?_⟩
      · simpa [Equiv.piEquivPiSubtypeProd_symm_apply, hp] using h' i hs
      · simpa [Equiv.piEquivPiSubtypeProd_symm_apply, hnp] using h' i hs
      · by_cases hp : p i
        · simpa [Equiv.piEquivPiSubtypeProd_symm_apply, hp] using h1 i hp hs
        · simpa [Equiv.piEquivPiSubtypeProd_symm_apply, hp] using h2 i hp hs
    rw [e.map_apply, hpre, Measure.prod_prod,
      infinitePi_pi _ (fun i _ ↦ ht i.1), infinitePi_pi _ (fun i _ ↦ ht i.1),
      Finset.prod_subtype_eq_prod_filter (f := fun i ↦ μ i (t i)),
      Finset.prod_subtype_eq_prod_filter (f := fun i ↦ μ i (t i)),
      Finset.prod_filter_mul_prod_filter_not]
  · have h0 : infinitePi μ = 0 := dite_eq_right h
    obtain ⟨i₀, hi₀⟩ := Classical.not_forall.mp h
    by_cases hp : p i₀
    · have hp0 : infinitePi (fun i : Subtype p ↦ μ i) = 0 :=
        dite_eq_right fun hall ↦ hi₀ (hall ⟨i₀, hp⟩)
      simp [h0, hp0]
    · have hnp0 : infinitePi (fun i : {i // ¬ p i} ↦ μ i) = 0 :=
        dite_eq_right fun hall ↦ hi₀ (hall ⟨i₀, hp⟩)
      simp [h0, hnp0]

/-- `Measure.infinitePi` assigns `∏ i ∈ s, μ i (t i)` to every finite-dimensional cylinder
`(s : Set ι).pi t`, without requiring measurability of the factor sets `t i`. -/
theorem infinitePi_pi' [∀ i, IsProbabilityMeasure (μ i)] (s : Finset ι) (t : ∀ i, Set (α i)) :
    infinitePi μ ((s : Set ι).pi t) = ∏ i ∈ s, μ i (t i) := by
  classical
  let e := (MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ s)).symm
  have hmp := (measurePreserving_piEquivPiSubtypeProd_infinitePi μ (· ∈ s)).symm.map_eq
  have hpre : e ⁻¹' (s : Set ι).pi t =
      (Set.univ.pi fun i : {i // i ∈ s} ↦ t i.1) ×ˢ Set.univ := by
    ext ⟨y, z⟩
    change (Equiv.piEquivPiSubtypeProd (· ∈ s) α).symm (y, z) ∈ (s : Set ι).pi t ↔ _
    simp only [Set.mem_pi, Finset.mem_coe, mem_prod, mem_univ, forall_const, Subtype.forall,
      and_true]
    exact forall₂_congr fun i hi ↦ by simp [Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  rw [← hmp, e.map_apply, hpre, Measure.prod_prod, infinitePi_eq_pi, Measure.pi_pi, measure_univ,
    mul_one, Finset.prod_coe_sort s (fun i ↦ μ i (t i))]

end SubtypeProd

section Group

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))

/-- An infinite product of left-invariant measures is left-invariant. -/
@[to_additive /-- An infinite product of left-invariant measures on types with addition is
left-invariant. -/]
instance infinitePi.isMulLeftInvariant [∀ i, Mul (α i)] [∀ i, MeasurableMul (α i)]
    [∀ i, IsMulLeftInvariant (μ i)] : IsMulLeftInvariant (infinitePi μ) where
  map_mul_left_eq_self v := by
    by_cases h : ∀ i, IsProbabilityMeasure (μ i)
    · have : (v * · : (∀ i, α i) → ∀ i, α i) = fun x i ↦ v i * x i := rfl
      rw [this, infinitePi_map_pi μ fun i ↦ measurable_const_mul (v i)]
      simp_rw [map_mul_left_eq_self]
    · have h0 : infinitePi μ = 0 := dite_eq_right h
      simp [h0]

/-- An infinite product of right-invariant measures is right-invariant. -/
@[to_additive /-- An infinite product of right-invariant measures on types with addition is
right-invariant. -/]
instance infinitePi.isMulRightInvariant [∀ i, Mul (α i)] [∀ i, MeasurableMul (α i)]
    [∀ i, IsMulRightInvariant (μ i)] : IsMulRightInvariant (infinitePi μ) where
  map_mul_right_eq_self v := by
    by_cases h : ∀ i, IsProbabilityMeasure (μ i)
    · have : (· * v : (∀ i, α i) → ∀ i, α i) = fun x i ↦ x i * v i := rfl
      rw [this, infinitePi_map_pi μ fun i ↦ measurable_mul_const (v i)]
      simp_rw [map_mul_right_eq_self]
    · have h0 : infinitePi μ = 0 := dite_eq_right h
      simp [h0]

/-- An infinite product of inversion-invariant measures is inversion-invariant. -/
@[to_additive /-- An infinite product of negation-invariant measures is negation-invariant. -/]
instance infinitePi.isInvInvariant [∀ i, Inv (α i)] [∀ i, MeasurableInv (α i)]
    [∀ i, IsInvInvariant (μ i)] : IsInvInvariant (infinitePi μ) where
  inv_eq_self := by
    by_cases h : ∀ i, IsProbabilityMeasure (μ i)
    · have : (Inv.inv : (∀ i, α i) → ∀ i, α i) = fun x i ↦ (x i)⁻¹ := rfl
      rw [Measure.inv_def, this, infinitePi_map_pi μ fun _ ↦ measurable_inv]
      simp_rw [← Measure.inv_def, inv_eq_self]
    · have h0 : infinitePi μ = 0 := dite_eq_right h
      simp [h0, Measure.inv_def]

/-- An infinite product of probability measures positive on nonempty open sets is positive on
nonempty open sets. -/
instance infinitePi.isOpenPosMeasure [∀ i, TopologicalSpace (α i)]
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsOpenPosMeasure (μ i)] :
    IsOpenPosMeasure (infinitePi μ) where
  open_pos U hU := by
    rintro ⟨a, ha⟩
    obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hU a ha
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hIu))
    rw [infinitePi_pi' μ I u, CanonicallyOrderedAdd.prod_pos]
    exact fun i hi ↦ (hu i hi).1.measure_pos (μ i) ⟨a i, (hu i hi).2⟩

/-- **An infinite product of probability Haar measures is a Haar measure.** -/
@[to_additive /-- **An infinite product of probability additive Haar measures is an additive Haar
measure.** -/]
instance infinitePi.isHaarMeasure [∀ i, Group (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, MeasurableMul (α i)] [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsHaarMeasure (μ i)] :
    IsHaarMeasure (infinitePi μ) where

end Group

end MeasureTheory.Measure
