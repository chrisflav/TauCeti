/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import TauCeti.MeasureTheory.Constructions.BorelSpace.RestrictedProduct
public import TauCeti.MeasureTheory.Group.InfinitePi
public import TauCeti.Topology.Algebra.RestrictedProduct.Away.LevelMap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.MeasureTheory.Group.Arithmetic
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Measure.Comap
import TauCeti.MeasureTheory.Measure.Haar.Unique

/-!
# Restricted products of Haar measures

Let `G : ι → Type*` be a countable family of second-countable locally compact topological groups,
`B i` an open subgroup of `G i` for every `i`, and `μ i` a left Haar measure on `G i` such that
`μ i (B i) = 1` for all but finitely many `i` (from which compactness of `B i` at those indices
follows automatically, since an open subgroup of finite Haar measure in a locally compact group is
compact).

This file constructs the normalized restricted product measure `restrictedHaar B μ` (and its
additive counterpart `restrictedAddHaar B μ`) on `Πʳ i, [G i, B i]` and proves its characteristic
properties:

* **Haar property** (`isHaarMeasure_restrictedHaar`): `restrictedHaar B μ` is a left Haar measure on
  `Πʳ i, [G i, B i]`.
* **Coordinate-box formula** (`restrictedHaar_box`): for any family of sets `C i ⊆ G i` (not
  necessarily measurable) satisfying `C i = B i` for all but finitely many `i`,
  `restrictedHaar B μ (restrictedProductBox C) = ∏ᶠ i, μ i (C i)`.
* **Level-subgroup pullback** (`comap_restrictedProductLevelMap_restrictedHaar`): for any finite set
  `I : Finset ι` outside which `μ i (B i) = 1`, pulling `restrictedHaar B μ` back along the open
  embedding `restrictedProductLevelMap` recovers
  `(Measure.pi fun i : I ↦ μ i.1).prod (Measure.infinitePi fun j ↦ (μ j.1).comap (↑))`.
* **Uniqueness** (`eq_restrictedHaar_of_open_box`, `eq_restrictedHaar_of_box`,
  `exists_unique_restrictedHaar` / `exists_unique_restrictedAddHaar`): any Borel measure on
  `Πʳ i, [G i, B i]` (with no left-invariance or σ-finiteness assumption) that assigns
  `∏ᶠ i, μ i (C i)` to every open box with `C i = B i` cofinitely coincides with
  `restrictedHaar B μ`.
* **Splitting away from a finite set** (`map_awayContinuousMulEquiv_restrictedHaar`,
  `map_awayDecomposition_restrictedHaar`): for *every* finite set `I : Finset ι`, splitting at `I`
  pushes `restrictedHaar B μ` forward to the product of `Measure.pi (fun i : I ↦ μ i.1)` with the
  restricted Haar product away from `I`.
* **σ-finiteness and group invariance** (`sigmaFinite_restrictedHaar`,
  `isMulLeftInvariant_restrictedHaar`, `isMulRightInvariant_restrictedHaar`,
  `isInvInvariant_restrictedHaar`): unconditional σ-finiteness and left, right, and inversion
  invariance on `restrictedHaar B μ`.

All results are stated for general `SubgroupClass` / `AddSubgroupClass` families `B : ∀ i, S' i`
(covering `Subgroup`, `AddSubgroup`, `OpenSubgroup`, `Subring`, and `ValuationSubring`) and without
assuming `T2Space` on the factors `G i`.

## References

* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, 2nd ed., London Mathematical
  Society (2010), Chapter XV (J. Tate, *Fourier analysis in number fields and Hecke's
  zeta-functions*), §3.3.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), §3.5.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Springer (1999), §5.2.
* A. Weil, *Basic Number Theory*, Springer (1995).
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RestrictedProduct

universe u v w

namespace TauCeti

private theorem eventually_cofinite_notMem_iff {ι : Type*} {p : ι → Prop} (I : Finset ι) :
    (∀ᶠ i in Filter.cofinite, p i) ↔
      ∀ᶠ j : {i // i ∉ (I : Set ι)} in Filter.cofinite, p j.1 := by
  refine ⟨fun h ↦ Subtype.coe_injective.tendsto_cofinite h, fun h ↦ ?_⟩
  rw [eventually_cofinite] at h ⊢
  refine (I.finite_toSet.union (h.image Subtype.val)).subset fun i hi ↦ ?_
  by_cases hiI : i ∈ (I : Set ι)
  · exact Or.inl hiI
  · exact Or.inr ⟨⟨i, hiI⟩, hi, rfl⟩

private theorem image_structureMap_pi {ι : Type u} [DecidableEq ι] {R : ι → Type v}
    {S' : ι → Type w} [∀ i, SetLike (S' i) (R i)] (B : ∀ i, S' i)
    (F : Finset ι) (t : ∀ i, Set (B i)) :
    RestrictedProduct.structureMap R (fun i ↦ (B i : Set (R i))) cofinite '' (F : Set ι).pi t =
      restrictedProductBox fun i ↦
        if i ∈ F then ((↑) : B i → R i) '' t i else (B i : Set (R i)) := by
  ext x
  simp only [mem_image, Set.mem_pi, Finset.mem_coe, mem_restrictedProductBox]
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨y, hy, rfl⟩ i
    rw [RestrictedProduct.structureMap_apply]
    split_ifs with hiF
    · exact ⟨y i, hy i hiF, rfl⟩
    · exact (y i).2
  · have hxB (i : ι) : x i ∈ B i := by
      have hxi := hx i
      split_ifs at hxi with hiF
      · rcases hxi with ⟨b, -, hb⟩
        exact hb ▸ b.2
      · exact hxi
    refine ⟨fun i ↦ ⟨x i, hxB i⟩, fun i hiF ↦ ?_, by ext i; rfl⟩
    have hxi := hx i
    simp only [hiF, ↓reduceIte, mem_image, Subtype.exists, exists_and_right,
      exists_eq_right] at hxi
    exact hxi.2

private theorem isProbabilityMeasure_comap_subtype_of_eq_one {α S : Type*} [MeasurableSpace α]
    [SetLike S α] {B : S} (hB : MeasurableSet (B : Set α)) {μ : Measure α} (hμ : μ B = 1) :
    IsProbabilityMeasure (μ.comap ((↑) : B → α)) where
  measure_univ := by
    have hme : MeasurableEmbedding ((↑) : B → α) := MeasurableEmbedding.subtype_coe hB
    rw [hme.comap_apply, image_univ, Subtype.range_coe, hμ]

section RestrictedHaar

variable {ι : Type u} {G : ι → Type v} {S' : ι → Type w}
  [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [∀ i, SetLike (S' i) (G i)] [∀ i, SubgroupClass (S' i) (G i)]

omit [∀ i, SecondCountableTopology (G i)] in
/-- An open subgroup of finite Haar measure in a locally compact Borel group is compact. -/
@[to_additive]
private theorem isCompact_subgroup_of_isOpen_of_measure_ne_top {i : ι} {B : ∀ i, S' i}
    (hB : IsOpen (B i : Set (G i))) (μ : Measure (G i)) [μ.IsHaarMeasure]
    (hμ : μ (B i) ≠ ∞) : IsCompact (B i : Set (G i)) := by
  rw [isCompact_iff_compactSpace]
  have : IsTopologicalGroup (B i) :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype (B i))
  have : LocallyCompactSpace (B i) := hB.locallyCompactSpace
  have : Measure.IsOpenPosMeasure (μ.comap ((↑) : B i → G i)) :=
    Measure.IsOpenPosMeasure.comap μ hB.isOpenEmbedding_subtypeVal
  by_contra hnc
  rw [not_compactSpace_iff] at hnc
  have huniv := measure_univ_of_isMulLeftInvariant (μ.comap ((↑) : B i → G i))
  have hme : MeasurableEmbedding ((↑) : B i → G i) :=
    MeasurableEmbedding.subtype_coe hB.measurableSet
  have hc : (μ.comap ((↑) : B i → G i)) Set.univ = μ (B i) := by
    rw [hme.comap_apply, image_univ, Subtype.range_coe]
  exact hμ (hc.symm.trans huniv)

/-! ### Auxiliary construction at a fixed finite exceptional set -/

section Aux

omit [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)] in
/-- The compact open everywhere-integral subgroup inside the tail restricted product away from `S`,
bundled as an element of `PositiveCompacts`. -/
@[to_additive]
private noncomputable def tailSubgroupPositiveCompacts
    (S : Set ι) (B : ∀ i, S' i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hS_comp : ∀ i ∉ S, IsCompact (B i : Set (G i))) :
    TopologicalSpace.PositiveCompacts (Πʳ j : {i // i ∉ S}, [G j.1, B j.1]) where
  carrier := restrictedProductBox fun j : {i // i ∉ S} ↦ (B j.1 : Set (G j.1))
  isCompact' :=
    isCompact_restrictedProductBox (fun j ↦ hS_comp j.1 j.2) (.of_forall fun _ ↦ Subset.rfl)
  interior_nonempty' := by
    have hopen : IsOpen (restrictedProductBox
        (fun j : {i // i ∉ S} ↦ (B j.1 : Set (G j.1))) :
        Set (Πʳ j : {i // i ∉ S}, [G j.1, B j.1])) :=
      isOpen_restrictedProductBox (fun j ↦ hBopen.out j.1) (.of_forall fun _ ↦ rfl)
    exact ⟨1, hopen.interior_eq.symm ▸ fun j ↦ one_mem (B j.1)⟩

omit [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  [∀ i, BorelSpace (G i)] in
/-- Auxiliary restricted Haar measure built by splitting at the finite set `S` and normalizing the
everywhere-integral subgroup away from `S` to mass `1`. -/
@[to_additive]
private noncomputable def auxRestrictedHaar
    (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])]
    (hS_comp : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) : Measure (Πʳ i, [G i, B i]) :=
  letI : Fintype S := hS.fintype
  let R_tail := Πʳ j : {i // i ∉ S}, [G j.1, B j.1]
  letI : Fact (∀ j : {i // i ∉ S}, IsOpen (B j.1 : Set (G j.1))) := ⟨fun j ↦ hBopen.out j.1⟩
  letI : MeasurableSpace R_tail := borel R_tail
  haveI : BorelSpace R_tail := ⟨rfl⟩
  let K₀ := tailSubgroupPositiveCompacts S B hS_comp
  ((Measure.pi fun i : S ↦ μ i.1).prod (Measure.haarMeasure K₀)).map
    (awayContinuousMulEquiv S hS B fun i _ ↦ hBopen.out i).symm

variable [Countable ι] (S : Set ι) (hS : S.Finite) (B : ∀ i, S' i)
  [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]

@[to_additive]
private theorem isHaarMeasure_auxRestrictedHaar
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (hS_comp : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] :
    (auxRestrictedHaar S hS B hS_comp μ).IsHaarMeasure := by
  let _ : Fintype S := hS.fintype
  let R_tail := Πʳ j : {i // i ∉ S}, [G j.1, B j.1]
  let _ : Fact (∀ j : {i // i ∉ S}, IsOpen (B j.1 : Set (G j.1))) := ⟨fun j ↦ hBopen.out j.1⟩
  let _ : MeasurableSpace R_tail := borel R_tail
  have : BorelSpace R_tail := ⟨rfl⟩
  have : SecondCountableTopology R_tail := inferInstance
  dsimp only [auxRestrictedHaar]
  infer_instance

omit [Countable ι] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)] in
/-- Under `(awayContinuousMulEquiv S hS B _).symm`, a box `restrictedProductBox C` with `C i = B i`
away from `S` pulls back to `(Set.univ.pi fun i : S ↦ C i.1) ×ˢ K₀`. -/
@[to_additive]
private theorem preimage_symm_awayMul_restrictedProductBox
    (hS_comp : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    {C : ∀ i, Set (G i)} (hCS : ∀ i ∉ S, C i = B i) :
    (awayContinuousMulEquiv S hS B fun i _ ↦ hBopen.out i).symm ⁻¹' restrictedProductBox C =
      (Set.univ.pi fun i : S ↦ C i.1) ×ˢ (tailSubgroupPositiveCompacts S B hS_comp : Set _) := by
  rw [preimage_awayContinuousMulEquiv_symm_restrictedProductBox]
  congr 1
  ext z
  exact forall_congr' fun j ↦ by
    dsimp only
    rw [hCS j.1 j.2]

/-- `auxRestrictedHaar` assigns `∏ᶠ i ∈ S, μ i (C i)` to every coordinate box `C` (not necessarily
measurable) that equals `B i` away from `S`. -/
@[to_additive]
private theorem auxRestrictedHaar_box_eq_finprod_mem
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (hS_comp : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    {C : ∀ i, Set (G i)} (hCS : ∀ i ∉ S, C i = B i) :
    auxRestrictedHaar S hS B hS_comp μ (restrictedProductBox C) = ∏ᶠ i ∈ S, μ i (C i) := by
  let _ : Fintype S := hS.fintype
  let R_tail := Πʳ j : {i // i ∉ S}, [G j.1, B j.1]
  let _ : Fact (∀ j : {i // i ∉ S}, IsOpen (B j.1 : Set (G j.1))) := ⟨fun j ↦ hBopen.out j.1⟩
  let _ : MeasurableSpace R_tail := borel R_tail
  have : BorelSpace R_tail := ⟨rfl⟩
  have : SecondCountableTopology R_tail := inferInstance
  let e :=
    (awayContinuousMulEquiv S hS B fun i _ ↦ hBopen.out i).symm.toHomeomorph.toMeasurableEquiv
  have he : ((awayContinuousMulEquiv S hS B fun i _ ↦ hBopen.out i).symm : _ → _) = e := rfl
  dsimp only [auxRestrictedHaar]
  rw [he, e.map_apply,
    show (e : _ → _) = (awayContinuousMulEquiv S hS B fun i _ ↦ hBopen.out i).symm from rfl,
    preimage_symm_awayMul_restrictedProductBox S hS B hS_comp hCS,
    Measure.prod_prod, Measure.pi_pi, Measure.haarMeasure_self, mul_one,
    ← finprod_set_coe_eq_finprod_mem, finprod_eq_prod_of_fintype]

/-- Compatibility of `auxRestrictedHaar` under enlarging the finite set `S ⊆ T`, provided
`μ i (B i) = 1` outside `S`. -/
@[to_additive]
private theorem auxRestrictedHaar_eq_of_subset
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    {T : Set ι} (hT : T.Finite) (hST : S ⊆ T)
    (hS_comp : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hS_one : ∀ i ∉ S, μ i (B i) = 1) :
    auxRestrictedHaar T hT B (fun i hi ↦ hS_comp i (hi ∘ @hST i)) μ =
      auxRestrictedHaar S hS B hS_comp μ := by
  classical
  have hB_cof : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)) :=
    Filter.eventually_of_mem hS.compl_mem_cofinite fun i hi ↦ hS_comp i hi
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.locallyCompactSpace_of_group _ hB_cof
  choose U h1U hUopen hUtop using fun i ↦ (μ i).exists_isOpen_measure_lt_top 1
  let E : ∀ i, Set (G i) := fun i ↦ if i ∈ S then U i else (B i : Set (G i))
  have hES : ∀ i ∉ S, E i = B i := fun i hi ↦ ite_eq_right hi
  have hET : ∀ i ∉ T, E i = B i := fun i hi ↦ ite_eq_right (hi ∘ @hST i)
  let νS := auxRestrictedHaar S hS B hS_comp μ
  let νT := auxRestrictedHaar T hT B (fun i hi ↦ hS_comp i (hi ∘ @hST i)) μ
  have : νS.IsHaarMeasure := isHaarMeasure_auxRestrictedHaar S hS B hS_comp μ
  have : νT.IsHaarMeasure := isHaarMeasure_auxRestrictedHaar T hT B _ μ
  have h_smul : νT = Measure.haarScalarFactor νT νS • νS :=
    Measure.isMulLeftInvariant_eq_smul νT νS
  have hE_S : νS (restrictedProductBox E) = ∏ᶠ i ∈ S, μ i (U i) := by
    rw [auxRestrictedHaar_box_eq_finprod_mem S hS B hS_comp μ hES]
    exact finprod_mem_congr rfl fun i hi ↦ by simp [E, hi]
  have hE_T : νT (restrictedProductBox E) = ∏ᶠ i ∈ S, μ i (U i) := by
    rw [auxRestrictedHaar_box_eq_finprod_mem T hT B _ μ hET, ← finprod_mem_mul_sdiff hST hT]
    have hdiff : ∏ᶠ i ∈ T \ S, μ i (E i) = 1 :=
      finprod_mem_eq_one_of_forall_eq_one fun i hi ↦ by simp [E, hi.2, hS_one i hi.2]
    rw [hdiff, mul_one]
    exact finprod_mem_congr rfl fun i hi ↦ by simp [E, hi]
  have hpos : νS (restrictedProductBox E) ≠ 0 := by
    rw [hE_S, finprod_mem_eq_finite_toFinset_prod _ hS]
    exact (CanonicallyOrderedAdd.prod_pos.mpr fun i _ ↦
      (hUopen i).measure_pos (μ i) ⟨1, h1U i⟩).ne'
  have htop : νS (restrictedProductBox E) ≠ ∞ := by
    rw [hE_S, finprod_mem_eq_finite_toFinset_prod _ hS]
    exact (ENNReal.prod_lt_top fun i _ ↦ hUtop i).ne
  have heval := congrArg (fun m : Measure (Πʳ i, [G i, B i]) ↦ m (restrictedProductBox E)) h_smul
  simp only [smul_apply, Measure.nnreal_smul_coe_apply] at heval
  rw [hE_T, ← hE_S] at heval
  have hc : (Measure.haarScalarFactor νT νS : ℝ≥0∞) = 1 := by
    have heval' : (Measure.haarScalarFactor νT νS : ℝ≥0∞) * νS (restrictedProductBox E) =
        1 * νS (restrictedProductBox E) := by
      rw [one_mul, ← heval]
    rwa [ENNReal.mul_left_inj hpos htop] at heval'
  have hc' : Measure.haarScalarFactor νT νS = 1 := by exact_mod_cast hc
  exact h_smul.trans (by rw [hc', one_smul])

omit [∀ i, LocallyCompactSpace (G i)] [hS : S.Finite] in
/-- Pulling the normalized tail Haar measure on `Πʳ j : {i // i ∉ S}, [G j.1, B j.1]` back along
`structureMap` recovers the infinite product `Measure.infinitePi` of the local pullbacks
`(μ j.1).comap ((↑) : B j.1 → G j.1)`. -/
@[to_additive]
private theorem comap_structureMap_tailHaar
    [Fact (∀ j : {i // i ∉ S}, IsOpen (B j.1 : Set (G j.1)))]
    [MeasurableSpace (Πʳ j : {i // i ∉ S}, [G j.1, B j.1])]
    [BorelSpace (Πʳ j : {i // i ∉ S}, [G j.1, B j.1])]
    (hS_comp : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hS_one : ∀ i ∉ S, μ i (B i) = 1) :
    (Measure.haarMeasure (tailSubgroupPositiveCompacts S B hS_comp)).comap
        (RestrictedProduct.structureMap (fun j : {i // i ∉ S} ↦ G j.1)
          (fun j ↦ (B j.1 : Set (G j.1))) cofinite) =
      Measure.infinitePi fun j : {i // i ∉ S} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1) := by
  let str := RestrictedProduct.structureMapMonoidHom (fun j : {i // i ∉ S} ↦ G j.1)
    (fun j ↦ B j.1) cofinite
  have hstr : IsOpenEmbedding str := by
    rw [RestrictedProduct.coe_structureMapMonoidHom]
    exact RestrictedProduct.isOpenEmbedding_structureMap fun j : {i // i ∉ S} ↦ hBopen.out j.1
  have : ∀ j : {i // i ∉ S}, SecondCountableTopology (B j.1) :=
    fun _ ↦ Topology.IsInducing.subtypeVal.secondCountableTopology
  have : ∀ j : {i // i ∉ S}, IsTopologicalGroup (B j.1) :=
    fun j ↦ Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype (B j.1))
  have : ∀ j : {i // i ∉ S}, CompactSpace (B j.1) :=
    fun j ↦ isCompact_iff_compactSpace.mp (hS_comp j.1 j.2)
  have : ∀ j : {i // i ∉ S}, LocallyCompactSpace (B j.1) := fun _ ↦ inferInstance
  have : ((Measure.haarMeasure
      (tailSubgroupPositiveCompacts S B hS_comp)).comap str).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) _ hstr
  have huniv : ((Measure.haarMeasure
      (tailSubgroupPositiveCompacts S B hS_comp)).comap str) Set.univ = 1 := by
    rw [hstr.measurableEmbedding.comap_apply, image_univ,
      RestrictedProduct.coe_structureMapMonoidHom,
      ← restrictedProductBox_self_eq_range_structureMap]
    exact Measure.haarMeasure_self
  have : IsProbabilityMeasure
      ((Measure.haarMeasure (tailSubgroupPositiveCompacts S B hS_comp)).comap str) :=
    ⟨huniv⟩
  have : ∀ j : {i // i ∉ S},
      IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    fun j ↦ isProbabilityMeasure_comap_subtype_of_eq_one
      (hBopen.out j.1).measurableSet (hS_one j.1 j.2)
  rw [← RestrictedProduct.coe_structureMapMonoidHom]
  symm
  exact Measure.isMulLeftInvariant_eq_of_measure_univ_eq _
    ((Measure.haarMeasure (tailSubgroupPositiveCompacts S B hS_comp)).comap str)
    (by rw [measure_univ, huniv])

end Aux

/-! ### Main definition and properties -/

section Main

/-- **The normalized restricted product of Haar measures** on `Πʳ i, [G i, B i]`.

Over a countable index type `ι`, when each `μ i` is a left Haar measure on `G i` and
`μ i (B i) = 1` for all but finitely many `i`, `restrictedHaar B μ` is the unique left Haar measure
assigning `∏ᶠ i, μ i (C i)` to every measurable box `restrictedProductBox C` with `C i = B i`
cofinitely. Like `Measure.infinitePi`, it is defined via classical `if ... then ... else 0` so that
expressions involving `restrictedHaar B μ` carry no proof arguments. -/
@[to_additive /-- **The normalized restricted product of additive Haar measures**
on `Πʳ i, [G i, B i]`.

Over a countable index type `ι`, when each `μ i` is a left additive Haar measure on `G i` and
`μ i (B i) = 1` for all but finitely many `i`, `restrictedAddHaar B μ` is the unique left additive
Haar measure assigning `∏ᶠ i, μ i (C i)` to every measurable box `restrictedProductBox C` with
`C i = B i` cofinitely. -/]
noncomputable def restrictedHaar (B : ∀ i, S' i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] (μ : ∀ i, Measure (G i)) :
    Measure (Πʳ i, [G i, B i]) :=
  open scoped Classical in
  if h : Countable ι ∧ (∀ᶠ i in Filter.cofinite, μ i (B i) = 1) ∧
      (∀ i, (μ i).IsHaarMeasure) then
    let S₀ : Set ι := {i | μ i (B i) ≠ 1}
    have hS₀ : S₀.Finite := eventually_cofinite.mp h.2.1
    have : ∀ i, (μ i).IsHaarMeasure := h.2.2
    have hS₀_comp : ∀ i ∉ S₀, IsCompact (B i : Set (G i)) := fun i hi ↦
      isCompact_subgroup_of_isOpen_of_measure_ne_top (hBopen.out i) (μ i)
        (by rw [Classical.not_not.mp hi]; exact ENNReal.one_ne_top)
    auxRestrictedHaar S₀ hS₀ B hS₀_comp μ
  else 0

variable {B : ∀ i, S' i} [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
  [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]

/-- Unfolding `restrictedHaar B μ` to `auxRestrictedHaar T` at any finite set `T` outside which
`μ i (B i) = 1`. -/
@[to_additive]
private theorem restrictedHaar_eq_auxRestrictedHaar [Countable ι]
    (μ : ∀ i, Measure (G i)) [hμ_haar : ∀ i, (μ i).IsHaarMeasure]
    {T : Set ι} (hT : T.Finite) (hT_one : ∀ i ∉ T, μ i (B i) = 1) :
    restrictedHaar B μ =
      auxRestrictedHaar T hT B
        (fun i hi ↦ isCompact_subgroup_of_isOpen_of_measure_ne_top (hBopen.out i) (μ i)
          (by rw [hT_one i hi]; exact ENNReal.one_ne_top)) μ := by
  classical
  have hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1 :=
    Filter.eventually_of_mem hT.compl_mem_cofinite fun i hi ↦ hT_one i hi
  have hcond : Countable ι ∧ (∀ᶠ i in Filter.cofinite, μ i (B i) = 1) ∧
      (∀ i, (μ i).IsHaarMeasure) := ⟨‹Countable ι›, hμ, hμ_haar⟩
  let S₀ : Set ι := {i | μ i (B i) ≠ 1}
  have hS₀ : S₀.Finite := eventually_cofinite.mp hμ
  have hS₀T : S₀ ⊆ T := fun i hi ↦ Classical.byContradiction fun hiT ↦ hi (hT_one i hiT)
  have hS₀_one : ∀ i ∉ S₀, μ i (B i) = 1 := fun _ hi ↦ Classical.not_not.mp hi
  have hS₀_comp : ∀ i ∉ S₀, IsCompact (B i : Set (G i)) := fun i hi ↦
    isCompact_subgroup_of_isOpen_of_measure_ne_top (hBopen.out i) (μ i)
      (by rw [hS₀_one i hi]; exact ENNReal.one_ne_top)
  rw [restrictedHaar, dite_eq_left hcond]
  exact (auxRestrictedHaar_eq_of_subset S₀ hS₀ B hT hS₀T hS₀_comp μ hS₀_one).symm

/-- **`restrictedHaar B μ` is a left Haar measure** over a countable index type whenever cofinitely
many `B i` have local Haar measure `1`. -/
@[to_additive /-- **`restrictedAddHaar B μ` is a left additive Haar measure** over a countable index
type whenever cofinitely many `B i` have local additive Haar measure `1`. -/]
theorem isHaarMeasure_restrictedHaar [Countable ι]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1) :
    (restrictedHaar B μ).IsHaarMeasure := by
  let T : Set ι := {i | μ i (B i) ≠ 1}
  have hT : T.Finite := eventually_cofinite.mp hμ
  have hT_one : ∀ i ∉ T, μ i (B i) = 1 := fun _ hi ↦ Classical.not_not.mp hi
  rw [restrictedHaar_eq_auxRestrictedHaar μ hT hT_one]
  exact isHaarMeasure_auxRestrictedHaar T hT B _ μ

/-- `restrictedHaar B μ` is always left-invariant (falling back to `0` outside its domain). -/
@[to_additive]
instance isMulLeftInvariant_restrictedHaar (μ : ∀ i, Measure (G i)) :
    (restrictedHaar B μ).IsMulLeftInvariant := by
  classical
  by_cases h : Countable ι ∧ (∀ᶠ i in Filter.cofinite, μ i (B i) = 1) ∧
      (∀ i, (μ i).IsHaarMeasure)
  · have : Countable ι := h.1
    have : ∀ i, (μ i).IsHaarMeasure := h.2.2
    exact (isHaarMeasure_restrictedHaar μ h.2.1).toIsMulLeftInvariant
  · have h0 : restrictedHaar B μ = 0 := dite_eq_right h
    rw [h0]
    exact ⟨fun _ ↦ Measure.map_zero _⟩

/-- `restrictedHaar B μ` is always σ-finite (falling back to `0` outside its domain). -/
@[to_additive]
instance sigmaFinite_restrictedHaar (μ : ∀ i, Measure (G i)) :
    SigmaFinite (restrictedHaar B μ) := by
  classical
  by_cases h : Countable ι ∧ (∀ᶠ i in Filter.cofinite, μ i (B i) = 1) ∧
      (∀ i, (μ i).IsHaarMeasure)
  · rcases h with ⟨_, hμ, _⟩
    have hB_cof : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)) :=
      hμ.mono fun i hi ↦ isCompact_subgroup_of_isOpen_of_measure_ne_top (hBopen.out i) (μ i)
        (by rw [hi]; exact ENNReal.one_ne_top)
    have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
      RestrictedProduct.locallyCompactSpace_of_group _ hB_cof
    have : (restrictedHaar B μ).IsHaarMeasure := isHaarMeasure_restrictedHaar μ hμ
    infer_instance
  · have h0 : restrictedHaar B μ = 0 := dite_eq_right h
    rw [h0]
    infer_instance

/-- **Coordinate-box formula for `restrictedHaar`.** Every coordinate box `restrictedProductBox C`
(not necessarily measurable) with `C i = B i` for all but finitely many `i` has measure
`∏ᶠ i, μ i (C i)`. -/
@[to_additive /-- **Coordinate-box formula for `restrictedAddHaar`.** Every coordinate box
`restrictedProductBox C` (not necessarily measurable) with `C i = B i` for all but finitely many `i`
has measure `∏ᶠ i, μ i (C i)`. -/]
theorem restrictedHaar_box [Countable ι]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCB : ∀ᶠ i in Filter.cofinite, C i = B i) :
    restrictedHaar B μ (restrictedProductBox C) = ∏ᶠ i, μ i (C i) := by
  classical
  let T : Set ι := {i | μ i (B i) ≠ 1 ∨ C i ≠ B i}
  have hT : T.Finite :=
    ((eventually_cofinite.mp hμ).union (eventually_cofinite.mp hCB)).subset fun _ hx ↦ hx
  have hT_one : ∀ i ∉ T, μ i (B i) = 1 :=
    fun _ hi ↦ Classical.not_not.mp fun hnm ↦ hi (Or.inl hnm)
  have hT_C : ∀ i ∉ T, C i = B i :=
    fun _ hi ↦ Classical.not_not.mp fun hncb ↦ hi (Or.inr hncb)
  rw [restrictedHaar_eq_auxRestrictedHaar μ hT hT_one,
    auxRestrictedHaar_box_eq_finprod_mem T hT B _ μ hT_C]
  have hsupp : Function.mulSupport (fun i ↦ μ i (C i)) ⊆ T := fun i hi ↦ by
    rw [Function.mem_mulSupport] at hi
    by_contra hiT
    exact hi (by rw [hT_C i hiT, hT_one i hiT])
  rw [finprod_mem_eq_finite_toFinset_prod _ hT,
    finprod_eq_prod_of_mulSupport_subset _ (s := hT.toFinset)
      fun i hi ↦ hT.mem_toFinset.mpr (hsupp hi)]

/-- The everywhere-integral open subgroup `Set.range (RestrictedProduct.structureMap ...)` has
`restrictedHaar`-measure `∏ᶠ i, μ i (B i)`. -/
@[to_additive]
theorem restrictedHaar_range_structureMap [Countable ι]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1) :
    restrictedHaar B μ
        (Set.range (RestrictedProduct.structureMap G (fun i ↦ (B i : Set (G i))) cofinite)) =
      ∏ᶠ i, μ i (B i) := by
  rw [← restrictedProductBox_self_eq_range_structureMap]
  exact restrictedHaar_box μ hμ (.of_forall fun _ ↦ rfl)

/-- **Level-subgroup pullback formula.** For any finite set `I : Finset ι` outside which every `B i`
has `μ i (B i) = 1`, pulling `restrictedHaar B μ` back along the open subgroup embedding
`restrictedProductLevelMap` yields
`(Measure.pi fun i : I ↦ μ i.1).prod (Measure.infinitePi fun j ↦ (μ j.1).comap (↑))`. -/
@[to_additive comap_restrictedProductAddLevelMap_restrictedAddHaar]
theorem comap_restrictedProductLevelMap_restrictedHaar [Countable ι]
    (I : Finset ι)
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hI_one : ∀ i ∉ (I : Set ι), μ i (B i) = 1) :
    (restrictedHaar B μ).comap (restrictedProductLevelMap (I : Set ι) I.finite_toSet B) =
      (Measure.pi fun i : I ↦ μ i.1).prod
        (Measure.infinitePi fun j : {i // i ∉ (I : Set ι)} ↦
          (μ j.1).comap ((↑) : B j.1 → G j.1)) := by
  let hI_comp : ∀ i ∉ (I : Set ι), IsCompact (B i : Set (G i)) := fun i hi ↦
    isCompact_subgroup_of_isOpen_of_measure_ne_top (hBopen.out i) (μ i)
      (by rw [hI_one i hi]; exact ENNReal.one_ne_top)
  let R_tail := Πʳ j : {i // i ∉ (I : Set ι)}, [G j.1, B j.1]
  let _ : Fact (∀ j : {i // i ∉ (I : Set ι)}, IsOpen (B j.1 : Set (G j.1))) :=
    ⟨fun j ↦ hBopen.out j.1⟩
  let _ : MeasurableSpace R_tail := borel R_tail
  have : BorelSpace R_tail := ⟨rfl⟩
  have : SecondCountableTopology R_tail := inferInstance
  let e := (awayContinuousMulEquiv (I : Set ι) I.finite_toSet B fun i _ ↦ hBopen.out i).symm
  let str := RestrictedProduct.structureMap (fun j : {i // i ∉ (I : Set ι)} ↦ G j.1)
    (fun j ↦ (B j.1 : Set (G j.1))) cofinite
  let f := Prod.map (id : (∀ i : I, G i.1) → ∀ i : I, G i.1) str
  have he : MeasurableEmbedding e := e.toHomeomorph.isOpenEmbedding.measurableEmbedding
  have hstr : MeasurableEmbedding str :=
    (RestrictedProduct.isOpenEmbedding_structureMap fun j ↦ hBopen.out j.1).measurableEmbedding
  have hf : MeasurableEmbedding f := MeasurableEmbedding.id.prodMap hstr
  rw [restrictedHaar_eq_auxRestrictedHaar μ I.finite_toSet hI_one]
  dsimp only [auxRestrictedHaar]
  have hpi : @Measure.pi (I : Set ι) _ I.finite_toSet.fintype _ (fun i ↦ μ i.1) =
      Measure.pi fun i : I ↦ μ i.1 := by
    congr 1
    exact Subsingleton.elim _ _
  have hlevel : (restrictedProductLevelMap (I : Set ι) I.finite_toSet B : _ → _) = e ∘ f :=
    coe_restrictedProductLevelMap (I : Set ι) I.finite_toSet B fun i _ ↦ hBopen.out i
  rw [hpi, hlevel, ← he.comap_comap f, he.comap_map,
    ← comap_structureMap_tailHaar (I : Set ι) B hI_comp μ hI_one]
  have : ∀ j : {i // i ∉ (I : Set ι)},
      IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    fun j ↦ isProbabilityMeasure_comap_subtype_of_eq_one
      (hBopen.out j.1).measurableSet (hI_one j.1 j.2)
  have : SigmaFinite
      ((Measure.haarMeasure (tailSubgroupPositiveCompacts (I : Set ι) B hI_comp)).comap str) := by
    rw [comap_structureMap_tailHaar (I : Set ι) B hI_comp μ hI_one]
    infer_instance
  refine (Measure.prod_eq fun s t _ _ ↦ ?_).symm
  rw [hf.comap_apply, prodMap_image_prod, image_id, Measure.prod_prod, hstr.comap_apply]

/-- When `μ i (B i) = 1` for *every* `i`, pulling `restrictedHaar B μ` back along
`RestrictedProduct.structureMap` recovers `Measure.infinitePi (fun i ↦ (μ i).comap (↑))`. -/
@[to_additive]
theorem comap_structureMap_restrictedHaar [Countable ι]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ_all : ∀ i, μ i (B i) = 1) :
    (restrictedHaar B μ).comap
        (RestrictedProduct.structureMap G (fun i ↦ (B i : Set (G i))) cofinite) =
      Measure.infinitePi fun i ↦ (μ i).comap ((↑) : B i → G i) := by
  classical
  have hstr : MeasurableEmbedding
      (RestrictedProduct.structureMap G (fun i ↦ (B i : Set (G i))) cofinite) :=
    (RestrictedProduct.isOpenEmbedding_structureMap hBopen.out).measurableEmbedding
  have : ∀ i : ι, IsProbabilityMeasure ((μ i).comap ((↑) : B i → G i)) :=
    fun i ↦ isProbabilityMeasure_comap_subtype_of_eq_one (hBopen.out i).measurableSet (hμ_all i)
  refine Measure.eq_infinitePi _ fun F t _ ↦ ?_
  let C : ∀ i, Set (G i) := fun i ↦
    if i ∈ F then ((↑) : B i → G i) '' t i else (B i : Set (G i))
  have hCB : ∀ᶠ i in Filter.cofinite, C i = B i :=
    Filter.eventually_of_mem F.finite_toSet.compl_mem_cofinite fun i hi ↦
      ite_eq_right (Finset.mem_coe.not.mp hi)
  rw [hstr.comap_apply, image_structureMap_pi B F t,
    restrictedHaar_box μ (.of_forall hμ_all) hCB]
  refine (finprod_eq_prod_of_mulSupport_subset _ (s := F) fun i hi ↦ ?_).trans ?_
  · rw [Function.mem_mulSupport] at hi
    by_contra hiF
    have hCi : C i = B i := ite_eq_right (Finset.mem_coe.not.mp hiF)
    exact hi (by rw [hCi, hμ_all i])
  · refine Finset.prod_congr rfl fun i hiF ↦ ?_
    simp only [C, hiF, ↓reduceIte]
    have hme : MeasurableEmbedding ((↑) : B i → G i) :=
      MeasurableEmbedding.subtype_coe (hBopen.out i).measurableSet
    exact (hme.comap_apply (μ i) (t i)).symm

@[to_additive]
private theorem exists_countable_open_box_cover_restrictedHaar [Countable ι]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1) :
    ∃ T : Set (Set (Πʳ i, [G i, B i])),
      (T ⊆ {s | ∃ C : ∀ i, Set (G i), (∀ i, IsOpen (C i)) ∧
        (∀ᶠ i in Filter.cofinite, C i = B i) ∧ s = restrictedProductBox C}) ∧
      T.Countable ∧ ⋃₀ T = Set.univ ∧ ∀ t ∈ T, restrictedHaar B μ t ≠ ∞ := by
  classical
  choose U hyU hUopen hUtop using fun i y ↦ (μ i).exists_isOpen_measure_lt_top y
  let F₀ : Set ι := {i | μ i (B i) ≠ 1}
  have hF₀ : F₀.Finite := eventually_cofinite.mp hμ
  let Fx (x : Πʳ i, [G i, B i]) : Set ι := F₀ ∪ {j | x j ∉ B j}
  have hFx (x : Πʳ i, [G i, B i]) : (Fx x).Finite := hF₀.union (mem_cofinite.mp x.2)
  let C_x (x : Πʳ i, [G i, B i]) : ∀ i, Set (G i) := fun i ↦
    if i ∈ Fx x then U i (x i) else (B i : Set (G i))
  let W (x : Πʳ i, [G i, B i]) : Set (Πʳ i, [G i, B i]) := restrictedProductBox (C_x x)
  have hC_open (x : Πʳ i, [G i, B i]) (i : ι) : IsOpen (C_x x i) := by
    dsimp only [C_x]
    split_ifs <;> [exact hUopen i (x i); exact hBopen.out i]
  have hC_cof (x : Πʳ i, [G i, B i]) : ∀ᶠ i in Filter.cofinite, C_x x i = B i :=
    Filter.eventually_of_mem (hFx x).compl_mem_cofinite fun i hi ↦ ite_eq_right hi
  have hxW (x : Πʳ i, [G i, B i]) : x ∈ W x := fun i ↦ by
    dsimp only [C_x]
    split_ifs with hi
    · exact hyU i (x i)
    · exact Classical.not_not.mp fun hxB ↦ hi (Or.inr hxB)
  have hW_lt_top (x : Πʳ i, [G i, B i]) : restrictedHaar B μ (W x) ≠ ∞ := by
    rw [restrictedHaar_box μ hμ (hC_cof x),
      finprod_eq_prod_of_mulSupport_subset _ (s := (hFx x).toFinset)]
    · refine (ENNReal.prod_lt_top fun i _ ↦ ?_).ne
      dsimp only [C_x]
      split_ifs with hi
      · exact hUtop i (x i)
      · simp [Classical.not_not.mp fun hnm ↦ hi (Or.inl hnm)]
    · intro i hi
      rw [Function.mem_mulSupport] at hi
      refine (hFx x).mem_toFinset.mpr (Classical.byContradiction fun hiFx ↦ hi ?_)
      rw [show C_x x i = B i from ite_eq_right hiFx,
        Classical.not_not.mp fun hnm ↦ hiFx (Or.inl hnm)]
  obtain ⟨t, ht_count, ht_cov⟩ := LindelofSpace.elim_nhds_subcover W
    fun x ↦ (isOpen_restrictedProductBox (hC_open x) (hC_cof x)).mem_nhds (hxW x)
  refine ⟨W '' t, ?_, ht_count.image W, by rwa [sUnion_image], ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨C_x x, hC_open x, hC_cof x, rfl⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hW_lt_top x

/-- **Uniqueness from open coordinate boxes.** Any Borel measure `ν` on `Πʳ i, [G i, B i]` (with no
left-invariance or finiteness assumption on `ν`) that gives every open box with `C i = B i`
cofinitely the mass `∏ᶠ i, μ i (C i)` equals `restrictedHaar B μ`. -/
@[to_additive /-- **Uniqueness from open coordinate boxes.** Any Borel measure `ν` on
`Πʳ i, [G i, B i]` (with no left-invariance or finiteness assumption on `ν`) that gives every open
box with `C i = B i` cofinitely the mass `∏ᶠ i, μ i (C i)` equals `restrictedAddHaar B μ`. -/]
theorem eq_restrictedHaar_of_open_box [Countable ι]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    {ν : Measure (Πʳ i, [G i, B i])}
    (hν : ∀ C : ∀ i, Set (G i), (∀ i, IsOpen (C i)) →
      (∀ᶠ i in Filter.cofinite, C i = B i) →
      ν (restrictedProductBox C) = ∏ᶠ i, μ i (C i)) :
    ν = restrictedHaar B μ := by
  symm
  obtain ⟨T, hT_sub, hT_count, hT_cov, hT_fin⟩ :=
    exists_countable_open_box_cover_restrictedHaar μ hμ
  refine Measure.ext_of_generateFrom_of_cover_subset
    (measurableSpace_restrictedProduct_eq_generateFrom_open_box (.of_forall hBopen.out))
    isPiSystem_open_restrictedProductBox hT_sub hT_count hT_cov hT_fin ?_
  rintro _ ⟨C, hC, hCB, rfl⟩
  rw [restrictedHaar_box μ hμ hCB, hν C hC hCB]

/-- Any Borel measure on `Πʳ i, [G i, B i]` assigning `∏ᶠ i, μ i (C i)` to every measurable box with
`C i = B i` cofinitely equals `restrictedHaar B μ`. -/
@[to_additive]
theorem eq_restrictedHaar_of_box [Countable ι]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    {ν : Measure (Πʳ i, [G i, B i])}
    (hν : ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
      (∀ᶠ i in Filter.cofinite, C i = B i) →
      ν (restrictedProductBox C) = ∏ᶠ i, μ i (C i)) :
    ν = restrictedHaar B μ :=
  eq_restrictedHaar_of_open_box μ hμ fun C hC ↦ hν C fun i ↦ (hC i).measurableSet

/-- **Existence and uniqueness of the restricted product of Haar measures.**
Over a countable index type `ι`, when `μ i (B i) = 1` for all but finitely many `i`, there exists a
unique left Haar measure on `Πʳ i, [G i, B i]` that gives every measurable box
`{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely the product `∏ᶠ i, μ i (C i)`. -/
@[to_additive /-- **Existence and uniqueness of the restricted product of additive Haar measures.**
Over a countable index type `ι`, when `μ i (B i) = 1` for all but finitely many `i`, there exists a
unique left additive Haar measure on `Πʳ i, [G i, B i]` that gives every measurable box
`{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely the product `∏ᶠ i, μ i (C i)`. -/]
theorem exists_unique_restrictedHaar [Countable ι]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1) :
    ∃! ν : Measure (Πʳ i, [G i, B i]), ν.IsHaarMeasure ∧
      ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
        (∀ᶠ i in Filter.cofinite, C i = B i) →
        ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) :=
  ⟨restrictedHaar B μ,
    ⟨isHaarMeasure_restrictedHaar μ hμ, fun _ _ hCB ↦ restrictedHaar_box μ hμ hCB⟩,
    fun _ ⟨_, hbox⟩ ↦ eq_restrictedHaar_of_box μ hμ hbox⟩

/-- **Splitting `restrictedHaar` along any finite set of indices.** For *every* finite set
`I : Finset ι`, pushing `restrictedHaar B μ` forward along `awayContinuousMulEquiv` yields the
product of `Measure.pi (fun i : I ↦ μ i.1)` with the restricted Haar product away from `I`. -/
@[to_additive map_addAwayContinuousAddEquiv_restrictedAddHaar]
theorem map_awayContinuousMulEquiv_restrictedHaar
    (I : Finset ι)
    [Fact (∀ j : {i // i ∉ (I : Set ι)}, IsOpen (B j.1 : Set (G j.1)))]
    [MeasurableSpace (Πʳ j : {i // i ∉ (I : Set ι)}, [G j.1, B j.1])]
    [BorelSpace (Πʳ j : {i // i ∉ (I : Set ι)}, [G j.1, B j.1])]
    (μ : ∀ i, Measure (G i)) [hμ_haar : ∀ i, (μ i).IsHaarMeasure] :
    (restrictedHaar B μ).map
        (awayContinuousMulEquiv (I : Set ι) I.finite_toSet B fun i _ ↦ hBopen.out i) =
      (Measure.pi fun i : I ↦ μ i.1).prod
        (restrictedHaar (fun j : {i // i ∉ (I : Set ι)} ↦ B j.1) (fun j ↦ μ j.1)) := by
  classical
  by_cases h : Countable ι ∧ ∀ᶠ i in Filter.cofinite, μ i (B i) = 1
  · rcases h with ⟨_, hμ⟩
    have hμ_tail : ∀ᶠ j : {i // i ∉ (I : Set ι)} in Filter.cofinite, μ j.1 (B j.1) = 1 :=
      (eventually_cofinite_notMem_iff I).mp hμ
    let c := awayContinuousMulEquiv (I : Set ι) I.finite_toSet B fun i _ ↦ hBopen.out i
    let e := c.toHomeomorph.toMeasurableEquiv
    suffices hsymm :
        ((Measure.pi fun i : I ↦ μ i.1).prod
          (restrictedHaar (fun j : {i // i ∉ (I : Set ι)} ↦ B j.1) (fun j ↦ μ j.1))).map e.symm =
        restrictedHaar B μ by
      rw [show (c : _ → _) = e from rfl, ← hsymm]
      exact e.symm.map_symm_map
    refine eq_restrictedHaar_of_open_box μ hμ fun C _ hCB ↦ ?_
    have hCB_tail : ∀ᶠ j : {i // i ∉ (I : Set ι)} in Filter.cofinite, C j.1 = B j.1 :=
      Subtype.coe_injective.tendsto_cofinite hCB
    rw [e.symm.map_apply, show (e.symm : _ → _) = c.symm from rfl,
      preimage_awayContinuousMulEquiv_symm_restrictedProductBox, Measure.prod_prod, Measure.pi_pi,
      restrictedHaar_box (B := fun j : {i // i ∉ (I : Set ι)} ↦ B j.1)
        (fun j ↦ μ j.1) hμ_tail hCB_tail]
    have hsupp : Function.HasFiniteMulSupport (fun i ↦ μ i (C i)) :=
      eventually_cofinite.mp ((hμ.and hCB).mono fun i ⟨h1, h2⟩ ↦ by dsimp only; rw [h2, h1])
    have hcompl : (∏ᶠ (i : ι) (_ : i ∉ (I : Set ι)), μ i (C i)) =
        ∏ᶠ i ∈ (I : Set ι)ᶜ, μ i (C i) := rfl
    rw [Finset.prod_coe_sort I (fun i ↦ μ i (C i)),
      ← finprod_mem_coe_finset (fun i ↦ μ i (C i)) I,
      finprod_subtype_eq_finprod_cond (f := fun i ↦ μ i (C i)) (· ∉ (I : Set ι)),
      hcompl, ← finprod_mem_union' disjoint_compl_right (I.finite_toSet.inter_of_left _)
        (hsupp.inter_of_right _),
      union_compl_self, finprod_mem_univ]
  · have h0 : restrictedHaar B μ = 0 :=
      dite_eq_right fun ⟨h1, h2, _⟩ ↦ h ⟨h1, h2⟩
    have h_tail : ¬ (Countable {i // i ∉ (I : Set ι)} ∧
        (∀ᶠ j : {i // i ∉ (I : Set ι)} in Filter.cofinite, μ j.1 (B j.1) = 1) ∧
        ∀ j : {i // i ∉ (I : Set ι)}, (μ j.1).IsHaarMeasure) := by
      rintro ⟨hc_tail, hμ_tail, _⟩
      exact h ⟨Countable.of_equiv _ (Equiv.sumCompl (· ∈ (I : Set ι))),
        (eventually_cofinite_notMem_iff I).mpr hμ_tail⟩
    have h0_tail : restrictedHaar (fun j : {i // i ∉ (I : Set ι)} ↦ B j.1) (fun j ↦ μ j.1) = 0 :=
      dite_eq_right h_tail
    simp [h0, h0_tail]

/-- When every local measure `μ i` is right-invariant, `restrictedHaar B μ` is right-invariant. -/
@[to_additive]
instance isMulRightInvariant_restrictedHaar
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsMulRightInvariant] :
    (restrictedHaar B μ).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    classical
    by_cases h : Countable ι ∧ (∀ᶠ i in Filter.cofinite, μ i (B i) = 1) ∧
        (∀ i, (μ i).IsHaarMeasure)
    · rcases h with ⟨_, hμ, _⟩
      refine eq_restrictedHaar_of_open_box μ hμ fun C hC hCB ↦ ?_
      have hmeas : MeasurableSet (restrictedProductBox C : Set (Πʳ i, [G i, B i])) :=
        measurableSet_restrictedProductBox fun i ↦ (hC i).measurableSet
      have hpre : (· * g) ⁻¹' restrictedProductBox C =
          restrictedProductBox (fun i ↦ (· * g i) ⁻¹' C i) := by
        ext x
        simp [RestrictedProduct.mul_apply]
      have hCg_cof : ∀ᶠ i in Filter.cofinite, (· * g i) ⁻¹' C i = B i :=
        (hCB.and g.2).mono fun i ⟨hCi, hgi⟩ ↦ by
          rw [hCi]
          ext x
          exact mul_mem_cancel_right hgi
      rw [Measure.map_apply (measurable_mul_const g) hmeas, hpre, restrictedHaar_box μ hμ hCg_cof]
      simp_rw [measure_preimage_mul_right]
    · have h0 : restrictedHaar B μ = 0 := dite_eq_right h
      simp [h0]

/-- When every local measure `μ i` is inversion-invariant, `restrictedHaar B μ` is
inversion-invariant. -/
@[to_additive]
instance isInvInvariant_restrictedHaar
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsInvInvariant] :
    (restrictedHaar B μ).IsInvInvariant where
  inv_eq_self := by
    classical
    by_cases h : Countable ι ∧ (∀ᶠ i in Filter.cofinite, μ i (B i) = 1) ∧
        (∀ i, (μ i).IsHaarMeasure)
    · rcases h with ⟨_, hμ, _⟩
      refine eq_restrictedHaar_of_open_box μ hμ fun C hC hCB ↦ ?_
      have hmeas : MeasurableSet (restrictedProductBox C : Set (Πʳ i, [G i, B i])) :=
        measurableSet_restrictedProductBox fun i ↦ (hC i).measurableSet
      have hpre : (Inv.inv : Πʳ i, [G i, B i] → Πʳ i, [G i, B i]) ⁻¹' restrictedProductBox C =
          restrictedProductBox (fun i ↦ Inv.inv ⁻¹' C i) := by
        ext x
        simp
      have hCinv_cof : ∀ᶠ i in Filter.cofinite, Inv.inv ⁻¹' C i = B i :=
        hCB.mono fun i hCi ↦ by
          rw [hCi]
          ext x
          exact inv_mem_iff
      rw [Measure.inv_def, Measure.map_apply measurable_inv hmeas, hpre,
        restrictedHaar_box μ hμ hCinv_cof]
      simp_rw [Measure.measure_preimage_inv]
    · have h0 : restrictedHaar B μ = 0 := dite_eq_right h
      simp [h0, Measure.inv_def]

end Main

section SubgroupSpecialization

variable {U : ∀ i, Subgroup (G i)} [Fact (∀ i, IsOpen (U i : Set (G i)))]
  [MeasurableSpace (RestrictedProductGroup U)] [BorelSpace (RestrictedProductGroup U)]

/-- The everywhere-integral subgroup `integralSubgroup U` has `restrictedHaar`-measure
`∏ᶠ i, μ i (U i)`. -/
@[to_additive]
theorem restrictedHaar_integralSubgroup [Countable ι]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (U i) = 1) :
    restrictedHaar U μ (integralSubgroup U : Set (RestrictedProductGroup U)) =
      ∏ᶠ i, μ i (U i) := by
  rw [coe_integralSubgroup_eq_restrictedProductBox]
  exact restrictedHaar_box μ hμ (.of_forall fun _ ↦ rfl)

/-- Specialization of `map_awayContinuousMulEquiv_restrictedHaar` directly to `awayDecomposition`
for a family of `Subgroup`s. -/
@[to_additive map_addAwayDecomposition_restrictedAddHaar]
theorem map_awayDecomposition_restrictedHaar
    (I : Finset ι)
    [Fact (∀ j : {i // i ∉ (I : Set ι)}, IsOpen (U j.1 : Set (G j.1)))]
    [MeasurableSpace (RestrictedProductGroup fun j : {i // i ∉ (I : Set ι)} ↦ U j.1)]
    [BorelSpace (RestrictedProductGroup fun j : {i // i ∉ (I : Set ι)} ↦ U j.1)]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] :
    (restrictedHaar U μ).map (awayDecomposition (I : Set ι) I.finite_toSet U) =
      (Measure.pi fun i : I ↦ μ i.1).prod
        (restrictedHaar (fun j : {i // i ∉ (I : Set ι)} ↦ U j.1) (fun j ↦ μ j.1)) := by
  have hcoe : (awayDecomposition (I : Set ι) I.finite_toSet U : _ → _) =
      awayContinuousMulEquiv (I : Set ι) I.finite_toSet U
        (fun i _ ↦ (Fact.out : ∀ i, IsOpen (U i : Set (G i))) i) := by
    funext x
    exact (awayContinuousMulEquiv_apply (I : Set ι) I.finite_toSet U _ x).symm
  rw [hcoe]
  exact map_awayContinuousMulEquiv_restrictedHaar I μ

end SubgroupSpecialization

end RestrictedHaar

end TauCeti
