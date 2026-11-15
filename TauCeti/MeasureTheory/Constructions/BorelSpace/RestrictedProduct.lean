/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.SecondCountable

/-!
# Borel measurability and coordinate-box generation on restricted products

Let `R : ι → Type*` be a family of topological spaces with reference subsets `A i : Set (R i)`.
This file records the Borel measurability of the canonical maps associated with a restricted
product `Πʳ i, [R i, A i]_[𝓕]` and of coordinate boxes `restrictedProductBox C`:

* Coordinate evaluation `x ↦ x i`, coercion `(↑) : Πʳ i, [R i, A i]_[𝓕] → ∀ i, R i` into the
  product σ-algebra, and filter-change inclusions `RestrictedProduct.inclusion` are measurable.
* Over a countable index type `ι`, `restrictedProductBox C` is measurable for every family of
  measurable sets `C i`, with no openness or cofinite-agreement hypotheses
  (`measurableSet_restrictedProductBox`), and singletons are measurable whenever they are measurable
  in each factor (`instMeasurableSingletonClassRestrictedProduct`).
* Consequently, over a countable index type `ι`, principal-filter inclusions
  `RestrictedProduct.inclusion R A hS` (`𝓕 ≤ 𝓟 S`, with `A i` measurable for `i ∈ S`) and
  `RestrictedProduct.structureMap R A 𝓕` (with every `A i` measurable) are measurable embeddings
  between Borel spaces.
* Open boxes with `C i = A i` cofinitely form a π-system (`isPiSystem_open_restrictedProductBox`),
  and when `ι` is countable, each `R i` is second countable, and `A i` is open for all but finitely
  many `i`, they generate `borel (Πʳ i, [R i, A i])`
  (`borel_restrictedProduct_eq_generateFrom_open_box`).

## References

* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), §3.5.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Springer (1999), §5.1.
-/

public section

open Filter MeasureTheory Set Topology
open scoped RestrictedProduct

universe u v

namespace RestrictedProduct

section Maps

variable {ι : Type u} {R : ι → Type v} {A : ∀ i, Set (R i)} {𝓕 𝓖 : Filter ι}
  [∀ i, TopologicalSpace (R i)]

/-- Coordinate evaluation on a restricted product at index `i` is measurable into a Borel factor
`R i`. -/
@[fun_prop]
theorem measurable_eval (i : ι) [MeasurableSpace (R i)] [BorelSpace (R i)]
    [MeasurableSpace (Πʳ j, [R j, A j]_[𝓕])] [OpensMeasurableSpace (Πʳ j, [R j, A j]_[𝓕])] :
    Measurable fun x : Πʳ j, [R j, A j]_[𝓕] ↦ x i :=
  (continuous_eval i).measurable

/-- Coercion from a restricted product to the full product is measurable for the product σ-algebra
whenever open sets of the restricted product are measurable and each factor is a Borel space. -/
@[fun_prop]
theorem measurable_coe [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [MeasurableSpace (Πʳ i, [R i, A i]_[𝓕])] [OpensMeasurableSpace (Πʳ i, [R i, A i]_[𝓕])] :
    Measurable ((↑) : Πʳ i, [R i, A i]_[𝓕] → ∀ i, R i) :=
  Measurable.of_eval fun i ↦ measurable_eval i

/-- Changing the filter of a restricted product along `h : 𝓕 ≤ 𝓖` is measurable between spaces with
measurable open sets on the source and a Borel σ-algebra on the target. -/
@[fun_prop]
theorem measurable_inclusion
    [MeasurableSpace (Πʳ i, [R i, A i]_[𝓖])] [OpensMeasurableSpace (Πʳ i, [R i, A i]_[𝓖])]
    [MeasurableSpace (Πʳ i, [R i, A i]_[𝓕])] [BorelSpace (Πʳ i, [R i, A i]_[𝓕])]
    (h : 𝓕 ≤ 𝓖) :
    Measurable (inclusion R A h) :=
  (continuous_inclusion h).measurable

end Maps

end RestrictedProduct

namespace TauCeti

section MeasurableBox

variable {ι : Type u} {R : ι → Type v} {A : ∀ i, Set (R i)} {𝓕 : Filter ι}

/-- Every singleton `{x}` in a restricted product is the coordinate box of `{x i}`. -/
theorem singleton_eq_restrictedProductBox_singleton (x : Πʳ i, [R i, A i]_[𝓕]) :
    ({x} : Set (Πʳ i, [R i, A i]_[𝓕])) = restrictedProductBox fun i ↦ {x i} := by
  ext y
  simp [DFunLike.ext_iff]

/-- When `x i ∈ A i` for every `i`, the singleton `{x}` is the intersection over all finite sets
`F : Finset ι` of the boxes taking `{x i}` on `F` and `A i` outside `F`. -/
theorem singleton_eq_iInter_restrictedProductBox_of_forall_mem [DecidableEq ι]
    {x : Πʳ i, [R i, A i]_[𝓕]} (hx : ∀ i, x i ∈ A i) :
    ({x} : Set (Πʳ i, [R i, A i]_[𝓕])) =
      ⋂ F : Finset ι, restrictedProductBox fun i ↦ if i ∈ F then {x i} else A i := by
  ext y
  simp only [mem_singleton_iff, mem_iInter, mem_restrictedProductBox]
  refine ⟨?_, fun h ↦ DFunLike.ext y x fun i ↦ by simpa using h {i} i⟩
  rintro rfl F i
  split_ifs
  · rfl
  · exact hx i

variable [Countable ι] [∀ i, TopologicalSpace (R i)] [∀ i, MeasurableSpace (R i)]
  [∀ i, BorelSpace (R i)]

/-- Over a countable index type, `restrictedProductBox C` is measurable for any family of
measurable sets `C i`, with no openness or cofinite-agreement hypotheses. -/
theorem measurableSet_restrictedProductBox
    [MeasurableSpace (Πʳ i, [R i, A i]_[𝓕])] [OpensMeasurableSpace (Πʳ i, [R i, A i]_[𝓕])]
    {C : ∀ i, Set (R i)} (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (restrictedProductBox C : Set (Πʳ i, [R i, A i]_[𝓕])) := by
  rw [← preimage_coe_univ_pi_eq_restrictedProductBox]
  exact (MeasurableSet.univ_pi hC).preimage RestrictedProduct.measurable_coe

/-- Over a countable index type, singletons in `Πʳ i, [R i, A i]_[𝓕]` are measurable whenever
singletons are measurable in each Borel factor `R i` (including non-`T₁` factors). -/
instance instMeasurableSingletonClassRestrictedProduct
    [∀ i, MeasurableSingletonClass (R i)]
    [MeasurableSpace (Πʳ i, [R i, A i]_[𝓕])] [OpensMeasurableSpace (Πʳ i, [R i, A i]_[𝓕])] :
    MeasurableSingletonClass (Πʳ i, [R i, A i]_[𝓕]) where
  measurableSet_singleton x := by
    rw [singleton_eq_restrictedProductBox_singleton]
    exact measurableSet_restrictedProductBox fun i ↦ measurableSet_singleton (x i)

/-- Over a countable index type, when `hS : 𝓕 ≤ 𝓟 S` and `A i` is measurable for every `i ∈ S`, the
principal-stage inclusion `RestrictedProduct.inclusion R A hS` is a measurable embedding between
Borel spaces. -/
theorem _root_.RestrictedProduct.measurableEmbedding_inclusion_principal {S : Set ι}
    [MeasurableSpace (Πʳ i, [R i, A i]_[𝓟 S])] [BorelSpace (Πʳ i, [R i, A i]_[𝓟 S])]
    [MeasurableSpace (Πʳ i, [R i, A i]_[𝓕])] [BorelSpace (Πʳ i, [R i, A i]_[𝓕])]
    (hA : ∀ i ∈ S, MeasurableSet (A i)) (hS : 𝓕 ≤ 𝓟 S) :
    MeasurableEmbedding (RestrictedProduct.inclusion R A hS) := by
  classical
  refine (RestrictedProduct.isEmbedding_inclusion_principal hS).measurableEmbedding ?_
  have hrng : Set.range (RestrictedProduct.inclusion R A hS) =
      restrictedProductBox fun i ↦ if i ∈ S then A i else Set.univ := by
    ext x
    simp only [RestrictedProduct.range_inclusion, mem_ofPred_eq, eventually_principal,
      mem_restrictedProductBox]
    exact ⟨fun hx i ↦ by split_ifs with hi; exacts [hx i hi, trivial],
      fun hx i hi ↦ by simpa [hi] using hx i⟩
  rw [hrng]
  exact measurableSet_restrictedProductBox fun i ↦ by
    split_ifs with hi
    · exact hA i hi
    · exact MeasurableSet.univ

/-- Over a countable index type, when every `A i` is measurable, `RestrictedProduct.structureMap` is
a measurable embedding whenever both `∀ i, A i` and `Πʳ i, [R i, A i]_[𝓕]` carry their Borel
σ-algebras. -/
theorem _root_.RestrictedProduct.measurableEmbedding_structureMap
    [BorelSpace (∀ i, A i)]
    [MeasurableSpace (Πʳ i, [R i, A i]_[𝓕])] [BorelSpace (Πʳ i, [R i, A i]_[𝓕])]
    (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableEmbedding (RestrictedProduct.structureMap R A 𝓕) := by
  refine RestrictedProduct.isEmbedding_structureMap.measurableEmbedding ?_
  rw [← restrictedProductBox_self_eq_range_structureMap]
  exact measurableSet_restrictedProductBox hA

end MeasurableBox

section BorelGeneration

variable {ι : Type u} {R : ι → Type v} {A : ∀ i, Set (R i)} [∀ i, TopologicalSpace (R i)]

/-- Open coordinate boxes with `C i = A i` cofinitely form a π-system in `Πʳ i, [R i, A i]`. -/
theorem isPiSystem_open_restrictedProductBox :
    IsPiSystem
      {s : Set (Πʳ i, [R i, A i]) |
        ∃ C : ∀ i, Set (R i), (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧
          s = restrictedProductBox C} := by
  rintro _ ⟨C₁, hC₁, hCA₁, rfl⟩ _ ⟨C₂, hC₂, hCA₂, rfl⟩ -
  refine ⟨fun i ↦ C₁ i ∩ C₂ i, fun i ↦ (hC₁ i).inter (hC₂ i), ?_,
    (restrictedProductBox_inter C₁ C₂).symm⟩
  exact (hCA₁.and hCA₂).mono fun i ⟨h₁, h₂⟩ ↦ by simp [h₁, h₂]

/-- **Coordinate-box generation of the Borel σ-algebra.** Over a countable index type with
second-countable factors and cofinitely open reference sets `A i`, the Borel σ-algebra of
`Πʳ i, [R i, A i]` is generated by the open boxes `restrictedProductBox C` with `C i = A i`
cofinitely. -/
theorem borel_restrictedProduct_eq_generateFrom_open_box [Countable ι]
    [∀ i, SecondCountableTopology (R i)] (hA : ∀ᶠ i in cofinite, IsOpen (A i)) :
    borel (Πʳ i, [R i, A i]) =
      MeasurableSpace.generateFrom
        {s : Set (Πʳ i, [R i, A i]) |
          ∃ C : ∀ i, Set (R i), (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧
            s = restrictedProductBox C} := by
  have : SecondCountableTopology (Πʳ i, [R i, A i]) :=
    secondCountableTopology_restrictedProduct hA
  exact (isTopologicalBasis_open_restrictedProductBox hA).borel_eq_generateFrom

/-- In a Borel space `Πʳ i, [R i, A i]` over a countable index type with second-countable factors
and cofinitely open reference sets `A i`, the ambient σ-algebra is generated by the open boxes
`restrictedProductBox C` with `C i = A i` cofinitely. -/
theorem measurableSpace_restrictedProduct_eq_generateFrom_open_box [Countable ι]
    [∀ i, SecondCountableTopology (R i)]
    [m : MeasurableSpace (Πʳ i, [R i, A i])] [BorelSpace (Πʳ i, [R i, A i])]
    (hA : ∀ᶠ i in cofinite, IsOpen (A i)) :
    m = MeasurableSpace.generateFrom
      {s : Set (Πʳ i, [R i, A i]) |
        ∃ C : ∀ i, Set (R i), (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧
          s = restrictedProductBox C} :=
  BorelSpace.measurable_eq.trans (borel_restrictedProduct_eq_generateFrom_open_box hA)

end BorelGeneration

end TauCeti
