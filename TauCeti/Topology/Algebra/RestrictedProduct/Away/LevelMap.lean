/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Decomposition
public import TauCeti.Topology.Algebra.RestrictedProduct.SecondCountable

/-!
# Topological group decomposition and level embeddings away from a finite set

For a family of groups `G : ι → Type*` and subgroups `B i` (`SubgroupClass`), this file bundles:

* `RestrictedProduct.structureMapMonoidHom`: `RestrictedProduct.structureMap` as a monoid
  homomorphism `(∀ i, B i) →* Πʳ i, [G i, B i]_[𝓕]` (for any `SubmonoidClass` family).
* `TauCeti.awayContinuousMulEquiv`: `awayDecomposition` upgraded to a topological group isomorphism
  `Πʳ i, [G i, B i] ≃ₜ* ((∀ i : S, G i.1) × Πʳ j : {i // i ∉ S}, [G j.1, B j.1])` when `S` is
  finite and `B i` is open away from `S`, together with its coordinate box preimage formula
  `preimage_awayContinuousMulEquiv_symm_restrictedProductBox`.
* `TauCeti.restrictedProductLevelMap`: the level monoid homomorphism
  `((∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)) →* Πʳ i, [G i, B i]`, its range
  (`range_restrictedProductLevelMap`), and the fact that it is an open topological embedding when
  every `B i` outside `S` is open (`isOpenEmbedding_restrictedProductLevelMap`).

## References

* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), §3.5.
* A. Weil, *Basic Number Theory*, Springer (1995).
-/

public section

open Filter Set Topology
open scoped RestrictedProduct

universe u v w

namespace RestrictedProduct

/-- `RestrictedProduct.structureMap` bundled as a monoid homomorphism
`(∀ i, B i) →* Πʳ i, [R i, B i]_[𝓕]` when each `B i` is a submonoid of `R i`. -/
@[to_additive /-- `RestrictedProduct.structureMap` bundled as an additive monoid homomorphism
`(∀ i, B i) →+ Πʳ i, [R i, B i]_[𝓕]` when each `B i` is an additive submonoid of `R i`. -/]
def structureMapMonoidHom {ι : Type*} (R : ι → Type*) {S : ι → Type*} [∀ i, Monoid (R i)]
    [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] (B : ∀ i, S i) (𝓕 : Filter ι) :
    (∀ i, B i) →* Πʳ i, [R i, B i]_[𝓕] where
  toFun := structureMap R (fun i ↦ (B i : Set (R i))) 𝓕
  map_one' := by
    ext i
    rfl
  map_mul' _ _ := by
    ext i
    rfl

/-- Coercion of `structureMapMonoidHom` to a function recovers `structureMap`. -/
@[to_additive (attr := simp) /-- Coercion of `structureMapAddMonoidHom` to a function recovers
`structureMap`. -/]
theorem coe_structureMapMonoidHom {ι : Type*} (R : ι → Type*) {S : ι → Type*} [∀ i, Monoid (R i)]
    [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] (B : ∀ i, S i) (𝓕 : Filter ι) :
    (structureMapMonoidHom R B 𝓕 : (∀ i, B i) → Πʳ i, [R i, B i]_[𝓕]) =
      structureMap R (fun i ↦ (B i : Set (R i))) 𝓕 := by
  rfl

/-- Coordinatewise evaluation of `structureMapMonoidHom`.

Not a `simp` lemma: `simp` proves it from `coe_structureMapMonoidHom` and `structureMap_apply`. -/
@[to_additive /-- Coordinatewise evaluation of `structureMapAddMonoidHom`.

Not a `simp` lemma: `simp` proves it from `coe_structureMapAddMonoidHom` and
`structureMap_apply`. -/]
theorem structureMapMonoidHom_apply {ι : Type*} (R : ι → Type*) {S : ι → Type*} [∀ i, Monoid (R i)]
    [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] (B : ∀ i, S i) (𝓕 : Filter ι)
    (x : ∀ i, B i) (i : ι) :
    structureMapMonoidHom R B 𝓕 x i = x i := by
  rfl

end RestrictedProduct

namespace TauCeti

variable {ι : Type u} {G : ι → Type v} {S' : ι → Type w}
  [∀ i, Group (G i)] [∀ i, SetLike (S' i) (G i)] [∀ i, SubgroupClass (S' i) (G i)]

/-- When the reference subgroups away from a finite set `S` are open, `awayDecomposition` is a
topological group isomorphism between `Πʳ i, [G i, B i]` and
`(∀ i : S, G i.1) × Πʳ j : {i // i ∉ S}, [G j.1, B j.1]`. -/
@[to_additive addAwayContinuousAddEquiv /-- When the reference additive subgroups away from a finite
set `S` are open, `addAwayDecomposition` is a topological additive group isomorphism between
`Πʳ i, [G i, B i]` and `(∀ i : S, G i.1) × Πʳ j : {i // i ∉ S}, [G j.1, B j.1]`. -/]
noncomputable def awayContinuousMulEquiv [∀ i, TopologicalSpace (G i)]
    (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    Πʳ i, [G i, B i] ≃ₜ* ((∀ i : S, G i.1) × Πʳ j : {i // i ∉ S}, [G j.1, B j.1]) where
  __ := awayDecomposition S hS fun i ↦ Subgroup.ofClass (B i)
  continuous_toFun := continuous_awayDecomposition S hS fun i ↦ Subgroup.ofClass (B i)
  continuous_invFun := continuous_awayDecomposition_symm S hS
    (fun i ↦ Subgroup.ofClass (B i)) hB

/-- `awayContinuousMulEquiv` agrees with `awayDecomposition` on elements. -/
@[to_additive (attr := simp) addAwayContinuousAddEquiv_apply
  /-- `addAwayContinuousAddEquiv` agrees with `addAwayDecomposition` on elements. -/]
theorem awayContinuousMulEquiv_apply [∀ i, TopologicalSpace (G i)]
    (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i) (hB : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (x : Πʳ i, [G i, B i]) :
    awayContinuousMulEquiv S hS B hB x =
      awayDecomposition S hS (fun i ↦ Subgroup.ofClass (B i)) x := by
  rfl

/-- `(awayContinuousMulEquiv ...).symm` agrees with `(awayDecomposition ...).symm` on elements. -/
@[to_additive addAwayContinuousAddEquiv_symm_apply
  /-- `(addAwayContinuousAddEquiv ...).symm` agrees with `(addAwayDecomposition ...).symm` on
  elements. -/]
theorem awayContinuousMulEquiv_symm_apply [∀ i, TopologicalSpace (G i)]
    (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i) (hB : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (y : (∀ i : S, G i.1) × Πʳ j : {i // i ∉ S}, [G j.1, B j.1]) :
    (awayContinuousMulEquiv S hS B hB).symm y =
      (awayDecomposition S hS fun i ↦ Subgroup.ofClass (B i)).symm y := by
  rfl

/-- Coordinate at `i ∈ S` of `(awayContinuousMulEquiv S hS B hB).symm`. -/
@[to_additive (attr := simp) addAwayContinuousAddEquiv_symm_apply_of_mem
  /-- Coordinate at `i ∈ S` of `(addAwayContinuousAddEquiv S hS B hB).symm`. -/]
theorem awayContinuousMulEquiv_symm_apply_of_mem [∀ i, TopologicalSpace (G i)]
    (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i) (hB : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (y : (∀ i : S, G i.1) × Πʳ j : {i // i ∉ S}, [G j.1, B j.1]) {i : ι} (hi : i ∈ S) :
    (awayContinuousMulEquiv S hS B hB).symm y i = y.1 ⟨i, hi⟩ :=
  awayDecomposition_symm_apply_of_mem S hS (fun i ↦ Subgroup.ofClass (B i)) y i hi

/-- Coordinate at `i ∉ S` of `(awayContinuousMulEquiv S hS B hB).symm`. -/
@[to_additive (attr := simp) addAwayContinuousAddEquiv_symm_apply_of_notMem
  /-- Coordinate at `i ∉ S` of `(addAwayContinuousAddEquiv S hS B hB).symm`. -/]
theorem awayContinuousMulEquiv_symm_apply_of_notMem [∀ i, TopologicalSpace (G i)]
    (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i) (hB : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (y : (∀ i : S, G i.1) × Πʳ j : {i // i ∉ S}, [G j.1, B j.1]) {i : ι} (hi : i ∉ S) :
    (awayContinuousMulEquiv S hS B hB).symm y i = y.2 ⟨i, hi⟩ :=
  awayDecomposition_symm_apply_of_notMem S hS (fun i ↦ Subgroup.ofClass (B i)) y i hi

/-- Under `(awayContinuousMulEquiv S hS B hB).symm`, any coordinate box `restrictedProductBox C`
pulls back to `(Set.univ.pi fun i : S ↦ C i.1) ×ˢ restrictedProductBox (fun j ↦ C j.1)`. -/
@[to_additive preimage_addAwayContinuousAddEquiv_symm_restrictedProductBox]
theorem preimage_awayContinuousMulEquiv_symm_restrictedProductBox
    [∀ i, TopologicalSpace (G i)] (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (C : ∀ i, Set (G i)) :
    (awayContinuousMulEquiv S hS B hB).symm ⁻¹' restrictedProductBox C =
      (Set.univ.pi fun i : S ↦ C i.1) ×ˢ
        restrictedProductBox (fun j : {i // i ∉ S} ↦ C j.1) := by
  ext ⟨y, z⟩
  simp only [mem_preimage, mem_restrictedProductBox, mem_prod, Set.mem_pi, mem_univ, forall_const,
    Subtype.forall]
  refine ⟨fun h ↦ ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩, fun ⟨h1, h2⟩ i ↦ ?_⟩
  · simpa [awayContinuousMulEquiv_symm_apply_of_mem S hS B hB _ hi] using h i
  · simpa [awayContinuousMulEquiv_symm_apply_of_notMem S hS B hB _ hi] using h i
  · by_cases hi : i ∈ S
    · simpa [awayContinuousMulEquiv_symm_apply_of_mem S hS B hB _ hi] using h1 i hi
    · simpa [awayContinuousMulEquiv_symm_apply_of_notMem S hS B hB _ hi] using h2 i hi

/-- For a finite set `S : Set ι`, the level homomorphism embedding
`(∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)` into `Πʳ i, [G i, B i]` as the subgroup of elements
integral away from `S`. -/
@[to_additive restrictedProductAddLevelMap /-- For a finite set `S : Set ι`, the additive level
homomorphism embedding `(∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)` into `Πʳ i, [G i, B i]` as
the additive subgroup of elements integral away from `S`. -/]
noncomputable def restrictedProductLevelMap (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i) :
    ((∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)) →* Πʳ i, [G i, B i] :=
  (awayDecomposition S hS fun i ↦ Subgroup.ofClass (B i)).symm.toMonoidHom.comp
    ((MonoidHom.id (∀ i : S, G i.1)).prodMap
      (RestrictedProduct.structureMapMonoidHom (fun j : {i // i ∉ S} ↦ G j.1)
        (fun j ↦ B j.1) cofinite))

/-- Coordinate at `i ∈ S` of `restrictedProductLevelMap S hS B`. -/
@[to_additive (attr := simp) restrictedProductAddLevelMap_apply_of_mem
  /-- Coordinate at `i ∈ S` of `restrictedProductAddLevelMap S hS B`. -/]
theorem restrictedProductLevelMap_apply_of_mem (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i)
    (p : (∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)) {i : ι} (hi : i ∈ S) :
    restrictedProductLevelMap S hS B p i = p.1 ⟨i, hi⟩ :=
  awayDecomposition_symm_apply_of_mem S hS (fun i ↦ Subgroup.ofClass (B i))
    (p.1, RestrictedProduct.structureMapMonoidHom (fun j : {i // i ∉ S} ↦ G j.1)
      (fun j ↦ B j.1) cofinite p.2) i hi

/-- Coordinate at `i ∉ S` of `restrictedProductLevelMap S hS B`. -/
@[to_additive (attr := simp) restrictedProductAddLevelMap_apply_of_notMem
  /-- Coordinate at `i ∉ S` of `restrictedProductAddLevelMap S hS B`. -/]
theorem restrictedProductLevelMap_apply_of_notMem (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i)
    (p : (∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)) {i : ι} (hi : i ∉ S) :
    restrictedProductLevelMap S hS B p i = p.2 ⟨i, hi⟩ :=
  awayDecomposition_symm_apply_of_notMem S hS (fun i ↦ Subgroup.ofClass (B i))
    (p.1, RestrictedProduct.structureMapMonoidHom (fun j : {i // i ∉ S} ↦ G j.1)
      (fun j ↦ B j.1) cofinite p.2) i hi

/-- The range of `restrictedProductLevelMap S hS B` is the set of elements whose coordinates outside
`S` belong to `B i`. -/
@[to_additive range_restrictedProductAddLevelMap]
theorem range_restrictedProductLevelMap (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i) :
    Set.range (restrictedProductLevelMap S hS B) =
      {x : Πʳ i, [G i, B i] | ∀ i ∉ S, x i ∈ B i} := by
  ext x
  simp only [mem_range, mem_ofPred_eq]
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨p, rfl⟩ i hi
    rw [restrictedProductLevelMap_apply_of_notMem S hS B p hi]
    exact (p.2 ⟨i, hi⟩).2
  · refine ⟨(fun i ↦ x i.1, fun j ↦ ⟨x j.1, hx j.1 j.2⟩), DFunLike.ext _ _ fun i ↦ ?_⟩
    by_cases hi : i ∈ S
    · exact restrictedProductLevelMap_apply_of_mem S hS B _ hi
    · exact restrictedProductLevelMap_apply_of_notMem S hS B _ hi

/-- As a map, `restrictedProductLevelMap S hS B` factors as `Prod.map id structureMap` followed by
`(awayContinuousMulEquiv S hS B hB).symm`. -/
@[to_additive coe_restrictedProductAddLevelMap]
theorem coe_restrictedProductLevelMap [∀ i, TopologicalSpace (G i)]
    (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    (restrictedProductLevelMap S hS B : _ → Πʳ i, [G i, B i]) =
      (awayContinuousMulEquiv S hS B hB).symm ∘
        Prod.map id (RestrictedProduct.structureMap (fun j : {i // i ∉ S} ↦ G j.1)
          (fun j ↦ (B j.1 : Set (G j.1))) cofinite) := by
  ext p i
  rfl

/-- When every `B i` outside `S` is open, `restrictedProductLevelMap S hS B` is an open topological
embedding. -/
@[to_additive isOpenEmbedding_restrictedProductAddLevelMap]
theorem isOpenEmbedding_restrictedProductLevelMap [∀ i, TopologicalSpace (G i)]
    (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    IsOpenEmbedding (restrictedProductLevelMap S hS B) := by
  rw [coe_restrictedProductLevelMap S hS B hB]
  exact (awayContinuousMulEquiv S hS B hB).symm.toHomeomorph.isOpenEmbedding.comp
    (IsOpenEmbedding.id.prodMap (RestrictedProduct.isOpenEmbedding_structureMap fun j ↦ hB j.1 j.2))

end TauCeti
