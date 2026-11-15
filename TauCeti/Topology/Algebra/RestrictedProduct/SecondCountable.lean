/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import TauCeti.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Logic.Equiv.List
import TauCeti.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Coordinate boxes and second countability of restricted products

A coordinate box `restrictedProductBox C` in a restricted product `Πʳ i, [R i, A i]_[𝓕]` is the set
`{x | ∀ i, x i ∈ C i}` of elements whose coordinates belong to `C i` at every index. Over the
cofinite filter:

* when every `C i` is open and `C i = A i` for all but finitely many `i`, `restrictedProductBox C`
  is open (`isOpen_restrictedProductBox`), without assuming openness of `A i` at the finitely many
  exceptional indices;
* when every `C i` is compact and `C i ⊆ A i` for all but finitely many `i`,
  `restrictedProductBox C` is compact (`isCompact_restrictedProductBox`);
* when `A i` is open for all but finitely many `i`, the open boxes with `C i = A i` cofinitely
  form a topological basis of `Πʳ i, [R i, A i]` (`isTopologicalBasis_open_restrictedProductBox`).

When the index type `ι` is countable and each factor `R i` is second countable, every principal
stage `Πʳ i, [R i, A i]_[𝓟 S]` embeds into the countable product `∀ i, R i` and is therefore second
countable (`instSecondCountableTopologyRestrictedProductPrincipal`). When `A i` is open for all but
finitely many `i`, the principal stages away from finite sets containing the non-open indices embed
as a countable open cover of `Πʳ i, [R i, A i]`, making `Πʳ i, [R i, A i]` second countable
(`secondCountableTopology_restrictedProduct`, `instSecondCountableTopologyRestrictedProduct`). No
algebraic structure on the factors is needed.

## References

* N. Bourbaki, *General Topology*.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), §3.5.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter Set Topology TopologicalSpace
open scoped RestrictedProduct

universe u v

section Box

variable {ι : Type u} {R : ι → Type v} {A : ∀ i, Set (R i)} {𝓕 : Filter ι}

/-- The coordinate box `{x | ∀ i, x i ∈ C i}` inside a restricted product `Πʳ i, [R i, A i]_[𝓕]`. -/
@[expose]
def restrictedProductBox (C : ∀ i, Set (R i)) : Set (Πʳ i, [R i, A i]_[𝓕]) :=
  {x | ∀ i, x i ∈ C i}

/-- An element of a restricted product belongs to `restrictedProductBox C` precisely when each of
its coordinates belongs to the corresponding factor `C i`. -/
@[simp]
theorem mem_restrictedProductBox {C : ∀ i, Set (R i)} {x : Πʳ i, [R i, A i]_[𝓕]} :
    x ∈ restrictedProductBox C ↔ ∀ i, x i ∈ C i :=
  Iff.rfl

/-- `restrictedProductBox C` is the preimage of `Set.univ.pi C` under coercion to the full
product. -/
theorem preimage_coe_univ_pi_eq_restrictedProductBox (C : ∀ i, Set (R i)) :
    ((↑) : Πʳ i, [R i, A i]_[𝓕] → ∀ i, R i) ⁻¹' Set.univ.pi C = restrictedProductBox C := by
  ext x
  simp

/-- The box with whole-space factors is the whole restricted product. -/
@[simp]
theorem restrictedProductBox_univ :
    (restrictedProductBox (fun _ ↦ Set.univ) : Set (Πʳ i, [R i, A i]_[𝓕])) = Set.univ := by
  ext x
  simp

/-- A box with an empty factor at some index is empty. -/
theorem restrictedProductBox_eq_empty_of_eq_empty {C : ∀ i, Set (R i)} {i : ι} (hC : C i = ∅) :
    (restrictedProductBox C : Set (Πʳ i, [R i, A i]_[𝓕])) = ∅ := by
  ext x
  simp only [mem_restrictedProductBox, mem_empty_iff_false, iff_false, not_forall]
  exact ⟨i, by simp [hC]⟩

/-- Coordinatewise intersection of factor families corresponds to intersection of boxes. -/
@[simp]
theorem restrictedProductBox_inter (C₁ C₂ : ∀ i, Set (R i)) :
    (restrictedProductBox (fun i ↦ C₁ i ∩ C₂ i) : Set (Πʳ i, [R i, A i]_[𝓕])) =
      restrictedProductBox C₁ ∩ restrictedProductBox C₂ := by
  ext x
  simp [forall_and]

/-- Coordinate boxes are monotone in the factor sets. -/
theorem restrictedProductBox_mono {C₁ C₂ : ∀ i, Set (R i)} (h : ∀ i, C₁ i ⊆ C₂ i) :
    (restrictedProductBox C₁ : Set (Πʳ i, [R i, A i]_[𝓕])) ⊆ restrictedProductBox C₂ :=
  fun _ hx i ↦ h i (hx i)

/-- The box of the reference sets themselves is the range of `RestrictedProduct.structureMap`. -/
theorem restrictedProductBox_self_eq_range_structureMap :
    (restrictedProductBox A : Set (Πʳ i, [R i, A i]_[𝓕])) =
      Set.range (RestrictedProduct.structureMap R A 𝓕) := by
  rw [RestrictedProduct.range_structureMap]
  rfl

end Box

section GroupBox

variable {ι : Type u} {G : ι → Type v} [∀ i, Group (G i)]

/-- The carrier of `integralSubgroupOf U V` is the coordinate box of the subgroups `V i`. -/
@[to_additive /-- The carrier of `integralAddSubgroupOf U V` is the coordinate box of the additive
subgroups `V i`. -/]
theorem coe_integralSubgroupOf_eq_restrictedProductBox (U V : ∀ i, Subgroup (G i)) :
    (integralSubgroupOf U V : Set (Πʳ i, [G i, (U i : Set (G i))])) =
      restrictedProductBox fun i ↦ (V i : Set (G i)) := by
  ext x
  simp

/-- The carrier of `integralSubgroup U` is the coordinate box of the reference subgroups `U i`. -/
@[to_additive /-- The carrier of `integralAddSubgroup U` is the coordinate box of the reference
additive subgroups `U i`. -/]
theorem coe_integralSubgroup_eq_restrictedProductBox (U : ∀ i, Subgroup (G i)) :
    (integralSubgroup U : Set (Πʳ i, [G i, (U i : Set (G i))])) =
      restrictedProductBox fun i ↦ (U i : Set (G i)) := by
  ext x
  simp

end GroupBox

section Topology

variable {ι : Type u} {R : ι → Type v} {A : ∀ i, Set (R i)} [∀ i, TopologicalSpace (R i)]

/-- A box in `Πʳ i, [R i, A i]` with open factors `C i` satisfying `C i = A i` for all but finitely
many `i` is open. -/
theorem isOpen_restrictedProductBox {C : ∀ i, Set (R i)} (hC : ∀ i, IsOpen (C i))
    (hCA : ∀ᶠ i in cofinite, C i = A i) :
    IsOpen (restrictedProductBox C : Set (Πʳ i, [R i, A i])) := by
  rw [isOpen_restrictedProduct_iff]
  intro T hT
  have hfin : ({i | C i = A i} ∩ T)ᶜ.Finite := mem_cofinite.mp (hCA.and (le_principal_iff.mp hT))
  convert (isOpen_set_pi hfin fun i _ ↦ hC i).preimage RestrictedProduct.continuous_coe using 1
  ext y
  simp only [mem_preimage, mem_restrictedProductBox, RestrictedProduct.inclusion_apply, Set.mem_pi]
  refine ⟨fun h i _ ↦ h i, fun h i ↦ ?_⟩
  by_cases hi : i ∈ {i | C i = A i} ∩ T
  · rw [hi.1]
    exact y.2 hi.2
  · exact h i hi

/-- A box in `Πʳ i, [R i, A i]` with compact factors `C i` satisfying `C i ⊆ A i` for all but
finitely many `i` is compact. -/
theorem isCompact_restrictedProductBox {C : ∀ i, Set (R i)} (hC : ∀ i, IsCompact (C i))
    (hCA : ∀ᶠ i in cofinite, C i ⊆ A i) :
    IsCompact (restrictedProductBox C : Set (Πʳ i, [R i, A i])) := by
  let S : Set ι := {i | C i ⊆ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr hCA
  have hK : IsCompact (((↑) : Πʳ i, [R i, A i]_[𝓟 S] → ∀ i, R i) ⁻¹' Set.univ.pi C) := by
    refine RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage'
      (isCompact_univ_pi hC) ?_
    rw [RestrictedProduct.range_coe_principal]
    exact fun x hx i hi ↦ hi (hx i trivial)
  convert hK.image (RestrictedProduct.continuous_inclusion hS) using 1
  ext x
  simp only [mem_restrictedProductBox, mem_image, mem_preimage, Set.mem_pi, mem_univ, forall_const]
  refine ⟨fun hx ↦ ⟨⟨x, fun i hi ↦ hi (hx i)⟩, hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact hy

/-- When `A i` is open for all but finitely many `i`, the boxes `restrictedProductBox C` with open
factors satisfying `C i = A i` cofinitely form a topological basis of `Πʳ i, [R i, A i]`. -/
theorem isTopologicalBasis_open_restrictedProductBox (hA : ∀ᶠ i in cofinite, IsOpen (A i)) :
    IsTopologicalBasis
      {s : Set (Πʳ i, [R i, A i]) |
        ∃ C : ∀ i, Set (R i), (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧
          s = restrictedProductBox C} := by
  classical
  refine isTopologicalBasis_of_isOpen_of_nhds
    (by rintro _ ⟨C, hC, hCA, rfl⟩; exact isOpen_restrictedProductBox hC hCA) ?_
  intro x W hxW hW
  let S : Set ι := {i | x i ∈ A i ∧ IsOpen (A i)}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr (x.2.and hA)
  let x' : Πʳ i, [R i, A i]_[𝓟 S] := ⟨x, eventually_principal.mpr fun _ hi ↦ hi.1⟩
  obtain ⟨V, hVopen, hVx⟩ := RestrictedProduct.isEmbedding_coe_of_principal.isOpen_iff.mp
    (hW.preimage (RestrictedProduct.continuous_inclusion hS))
  obtain ⟨F, u, hu, hFuV⟩ := isOpen_pi_iff.mp hVopen x
    (mem_preimage.mp ((Set.ext_iff.mp hVx x').mpr hxW))
  let C : ∀ i, Set (R i) := fun i ↦
    (if i ∈ F then u i else Set.univ) ∩ (if i ∈ S then A i else Set.univ)
  refine ⟨restrictedProductBox C, ⟨C, fun i ↦ ?_, ?_, rfl⟩, fun i ↦ ?_, fun y hy ↦ ?_⟩
  · exact IsOpen.inter (by split_ifs <;> [exact (hu i ‹_›).1; exact isOpen_univ])
      (by split_ifs with hiS <;> [exact hiS.2; exact isOpen_univ])
  · refine ((x.2.and hA).and F.finite_toSet.compl_mem_cofinite).mono fun i ⟨hiS, hiF⟩ ↦ ?_
    have hiS' : i ∈ S := hiS
    simp [C, hiS', Finset.mem_coe.not.mp hiF]
  · exact ⟨by split_ifs with hiF; exacts [(hu i hiF).2, trivial],
      by split_ifs with hiS; exacts [hiS.1, trivial]⟩
  · let y' : Πʳ i, [R i, A i]_[𝓟 S] := ⟨y, eventually_principal.mpr fun i hiS ↦ by
      simpa [C, hiS] using (hy i).2⟩
    have hyV : (y : ∀ i, R i) ∈ V := hFuV fun i hiF ↦ by
      simpa [C, Finset.mem_coe.mp hiF] using (hy i).1
    exact (Set.ext_iff.mp hVx y').mp hyV

/-- Every principal stage `Πʳ i, [R i, A i]_[𝓟 S]` over a countable index type with second-countable
factors is second countable. -/
instance instSecondCountableTopologyRestrictedProductPrincipal [Countable ι]
    [∀ i, SecondCountableTopology (R i)] {S : Set ι} :
    SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 S]) :=
  RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology

/-- **A restricted product of countably many second-countable spaces relative to cofinitely open
subsets is second countable.** -/
theorem secondCountableTopology_restrictedProduct [Countable ι]
    [∀ i, SecondCountableTopology (R i)] (hA : ∀ᶠ i in cofinite, IsOpen (A i)) :
    SecondCountableTopology (Πʳ i, [R i, A i]) := by
  classical
  have hF₀ : {i | ¬ IsOpen (A i)}.Finite := hA
  let S (F : Finset ι) : Set ι := ((F : Set ι) ∪ {i | ¬ IsOpen (A i)})ᶜ
  have hS (F : Finset ι) : (cofinite : Filter ι) ≤ 𝓟 (S F) :=
    le_principal_iff.mpr (F.finite_toSet.union hF₀).compl_mem_cofinite
  let U : Finset ι → Set (Πʳ i, [R i, A i]) := fun F ↦
    Set.range (RestrictedProduct.inclusion R A (hS F))
  have hUopen (F : Finset ι) : IsOpen (U F) := by
    have hbox : U F = restrictedProductBox fun i ↦ if i ∈ S F then A i else Set.univ := by
      ext x
      simp only [U, RestrictedProduct.range_inclusion, mem_ofPred_eq, eventually_principal,
        mem_restrictedProductBox]
      exact ⟨fun hx i ↦ by split_ifs with hi; exacts [hx i hi, trivial],
        fun hx i hi ↦ by simpa [hi] using hx i⟩
    rw [hbox]
    refine isOpen_restrictedProductBox (fun i ↦ ?_)
      (eventually_of_mem (le_principal_iff.mp (hS F)) fun i hi ↦ ite_eq_left hi)
    split_ifs with hi
    · exact Classical.not_not.mp fun hn ↦ hi (Or.inr hn)
    · exact isOpen_univ
  have hUsc : ∀ F : Finset ι, SecondCountableTopology (U F) := fun F ↦
    (RestrictedProduct.isEmbedding_inclusion_principal
      (hS F)).toHomeomorph.symm.secondCountableTopology
  refine secondCountableTopology_of_countable_cover hUopen ?_
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  have hxfin : {i | x i ∉ A i}.Finite := mem_cofinite.mp x.2
  refine ⟨hxfin.toFinset, ?_⟩
  dsimp only [U]
  rw [RestrictedProduct.range_inclusion]
  intro i hi
  by_contra hxA
  exact hi (Or.inl (Finset.mem_coe.mpr (hxfin.mem_toFinset.mpr hxA)))

/-- Typeclass instance for second countability of `Πʳ i, [R i, A i]` when every `A i` is open. -/
instance instSecondCountableTopologyRestrictedProduct [Countable ι]
    [∀ i, SecondCountableTopology (R i)] [hA : Fact (∀ i, IsOpen (A i))] :
    SecondCountableTopology (Πʳ i, [R i, A i]) :=
  secondCountableTopology_restrictedProduct (.of_forall hA.out)

end Topology

end TauCeti
