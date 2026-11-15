/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.PullbackCup
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Homology
import TauCeti.Algebra.Module.Equiv.SpanSingleton

/-!
# Bijectivity of the Thom map: the Thom isomorphism

Let `E → B` be a real vector bundle with model fibre `F` of finite dimension `r = finrank ℝ F` and
Thom pair `(E, E₀)`, where `E₀` is the complement of the zero section, and let
`u ∈ Hʳ(E, E₀; K)` be a Thom class (`TauCeti.IsThomClass`) with coefficients in a commutative ring
`K`: a relative class whose restriction to the fibre pair `(E_b, E_b ∖ {0})` over every point `b`
generates `Hʳ(E_b, E_b ∖ {0}; K) ≅ K`. This file proves the **Thom isomorphism** for the cohomology
Thom map `Φ_u : Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(E, E₀; M)`, `a ↦ π^*a ⌣ u` (`TauCeti.thomMap`), and for the
homology Thom map `Hₘ(E, E₀; K) ⟶ Hₚ(B; K)`, `x ↦ π_*(x ⌢ u)` (`TauCeti.homologyThomMap`).

## The argument

1. **Over a trivializing set (`Bundle.Trivialization`).** If `W ⊆ B` lies in the base set of a
   linear trivialization `e`, `e.thomPairOverIso` identifies `(E|_W, E₀|_W)` with the product Thom
   pair `(W × F, W × (F ∖ {0}))`, carrying the fibre over `b ∈ W` to the fibre over `b` by the
   continuous linear equivalence of `e` at `b`. Transporting along this isomorphism reduces
   bijectivity over `W` (`Bundle.Trivialization.bijective_pullbackCup_thomPairOver` and
   `Bundle.Trivialization.bijective_pullbackCupRestrict_thomPairProj`) to the product-bundle Thom
   isomorphism `TauCeti.bijective_pullbackCup_prodThomPairProj`. For a globally trivializable bundle
   (`e.baseSet = Set.univ`), this gives `Bundle.Trivialization.bijective_thomMap` and
   `Bundle.Trivialization.thomEquiv` for any commutative ring `K` and any `K`-module `M`.
2. **Finite unions of trivializing open sets and compact bases.** Induction on a finite family of
   trivializing open sets `W i`, using the Mayer–Vietoris step
   `TopCat.bijective_pullbackCupRestrict_union` together with the below-rank cohomology vanishing
   `TauCeti.isZero_singularCohomology_thomPairOver_biUnion` on the intersections
   `W a ∩ ⋃ i ∈ s, W i = ⋃ i ∈ s, (W a ∩ W i)`, shows that `TopCat.pullbackCupRestrict` of `u` is
   bijective over every finite union of trivializing open sets
   (`TauCeti.bijective_pullbackCupRestrict_thomPairProj_biUnion`), hence that `TauCeti.thomMap` is
   bijective whenever finitely many trivializing open sets cover `B`
   (`TauCeti.bijective_thomMap_of_iUnion_eq_univ`). Over a compact base this gives the Thom
   isomorphism `TauCeti.thomEquivOfCompactSpace` for any commutative ring `K` and any `K`-module
   `M`.
3. **Arbitrary bases with field coefficients.** Over a field `K`, for any topological pair `P` and
   map `g : P.fst ⟶ Z`, the cap-and-push-forward morphism `x ↦ g_*(x ⌢ u)` in homology is up to sign
   dual to `TopPair.pullbackCup` under the universal coefficient equivalence, hence is an
   isomorphism on every finite union `W_s = ⋃ b ∈ s, (trivializationAt F E b).baseSet`. Since
   singular homology commutes with the filtered colimit of these open sets and their Thom pairs
   (`TauCeti.isColimitMapCoconeSingularHomology` and
   `TauCeti.isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion`), the global homology
   Thom map `TauCeti.homologyThomMap` is an isomorphism over an arbitrary base `B` without any
   compactness, paracompactness or separation assumption (`TauCeti.isIso_homologyThomMap_of_field`,
   `TauCeti.homologyThomIsoOfField`), and dualizing back via `TauCeti.bijective_homologyThomMap_iff`
   gives the cohomology Thom isomorphism `TauCeti.thomEquivOfField` over an arbitrary base `B` (both
   for oriented bundles over any field and, with `K = ZMod 2` or any field with `Subsingleton Kˣ`,
   for unoriented bundles via `TauCeti.existsUnique_isThomClass_of_subsingleton_units`).

## Main definitions and results

* `Bundle.Trivialization.bijective_pullbackCup_thomPairOver`,
  `Bundle.Trivialization.bijective_pullbackCupRestrict_thomPairProj`: bijectivity of the Thom map
  over a subset of the base set of a linear trivialization.
* `Bundle.Trivialization.bijective_thomMap`, `Bundle.Trivialization.thomEquiv`: the Thom isomorphism
  for a globally trivializable bundle.
* `TauCeti.bijective_pullbackCupRestrict_thomPairProj_biUnion`,
  `TauCeti.bijective_thomMap_of_iUnion_eq_univ`: bijectivity over finite unions and finite covers of
  trivializing open sets.
* `TauCeti.bijective_thomMap_of_compactSpace`, `TauCeti.thomEquivOfCompactSpace`: the Thom
  isomorphism over a compact base for any commutative ring `K` and `K`-module `M`.
* `TauCeti.isIso_homologyThomMap_of_field`, `TauCeti.bijective_homologyThomMap_of_field`,
  `TauCeti.homologyThomIsoOfField`: the homology Thom isomorphism over an arbitrary base with field
  coefficients.
* `TauCeti.bijective_thomMap_of_field`, `TauCeti.thomEquivOfField`: the cohomology Thom isomorphism
  over an arbitrary base with field coefficients.
* `TauCeti.VectorBundleOrientation.thomEquivOfCompactSpace`,
  `TauCeti.VectorBundleOrientation.thomEquivOfField`,
  `TauCeti.VectorBundleOrientation.homologyThomIsoOfField`: specializations to the Thom class
  `TauCeti.VectorBundleOrientation.thomClassOfModel` of an oriented bundle.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 4.D, Theorem 4D.10.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Limits Module MonoidalCategory Set Topology

universe w

/-! ### Over a trivializing set and for globally trivializable bundles -/

namespace TauCeti

/-- The bundle projection `π F E` as a `TopCat` morphism with syntactic domain
`TopCat.of (TotalSpace F E)`, used so `TopCat.pullbackCupRestrict` has the same syntactic ambient
space as `TauCeti.thomPairOver`. -/
private abbrev thomPairProjHom {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] : TopCat.of (TotalSpace F E) ⟶ TopCat.of B :=
  TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩

/-- Rewriting `thomPairProj F E` to `thomPairProjHom F E` inside `TopCat.pullbackCupRestrict` after
identifying `(thomPair F E).fst` with `TopCat.of (TotalSpace F E)`. -/
private theorem bijective_pullbackCupRestrict_thomPairProj_iff {B : Type w} [TopologicalSpace B]
    (F : Type*) [TopologicalSpace F] (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
    [∀ b, Zero (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    {K : Type w} [CommRing K] (M : ModuleCat.{w} K) (W : Set B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E) (zeroSectionCompl F E) M W
        n p m h u) ↔
      Function.Bijective (TopCat.pullbackCupRestrict (thomPairProjHom F E) (zeroSectionCompl F E)
        M W n p m h u) := by
  -- `(thomPair F E).fst` is `TopCat.of (TotalSpace F E)` through `TopPair.ofSubset`; align the
  -- implicit ambient-space parameter before rewriting `thomPairProj F E`.
  change Function.Bijective (TopCat.pullbackCupRestrict (X := TopCat.of (TotalSpace F E))
      (thomPairProj F E) (zeroSectionCompl F E) M W n p m h u) ↔ _
  have hproj : (thomPairProj F E : TopCat.of (TotalSpace F E) ⟶ TopCat.of B) =
      thomPairProjHom F E := thomPairProj_def F E
  rw [hproj]

end TauCeti

namespace Bundle.Trivialization

open TauCeti

section TrivializingSet

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet)
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

include hW in
/-- **The Thom isomorphism over a subset of a trivializing set.** If `W ⊆ e.baseSet` for a linear
trivialization `e`, and `u ∈ Hʳ(E|_W, E₀|_W; K)`, `r = finrank ℝ F`, restricts on the fibre pair
over every point `b ∈ W` to a generator of `Hʳ(E_b, E_b ∖ {0}; K)`, then `a ↦ π^*a ⌣ u` is bijective
from `Hᵖ(W; M)` to `Hᵐ(E|_W, E₀|_W; M)` whenever `p + r = m`. -/
theorem bijective_pullbackCup_thomPairOver
    {u : (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b (hb : b ∈ W), Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) (finrank ℝ F) u} = ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective ((thomPairOver F E W).pullbackCup M
      (TopCat.ofHom ((⟨π F E, FiberBundle.continuous_proj F E⟩ :
        C(TotalSpace F E, B)).restrictPreimage W)) (finrank ℝ F) p m h u) := by
  let φ := e.thomPairOverIso ℝ hW
  let u' := TopPair.singularCohomologyMap φ.inv (finrank ℝ F) u
  have hu_eq : TopPair.singularCohomologyMap φ.hom (finrank ℝ F) u' = u := by
    rw [← TopPair.singularCohomologyMap_comp_apply, Iso.hom_inv_id,
      TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
  have hg : TopPair.Hom.fst φ.hom ≫ prodThomPairProj W F =
      TopCat.ofHom ((⟨π F E, FiberBundle.continuous_proj F E⟩ :
        C(TotalSpace F E, B)).restrictPreimage W) ≫ 𝟙 (TopCat.of W) :=
    TopCat.ext fun v ↦ by
      rw [ConcreteCategory.comp_apply, Category.comp_id]
      exact (prodThomPairProj_apply F _).trans
        (congrArg Prod.fst (e.thomPairOverIso_hom_fst_apply ℝ hW v))
  rw [← hu_eq]
  refine (TopPair.bijective_pullbackCup_iff_of_isIso (M := M) φ.hom (𝟙 (TopCat.of W)) hg h u').2
    (bijective_pullbackCup_prodThomPairProj M (fun b ↦ ?_) h)
  have hfib : prodThomPairFiberMap F b ≫ φ.inv =
      (e.continuousLinearEquivAt ℝ b (hW b.2)).complZeroPairIso.inv ≫
        fiberThomPairOverMap F E b.2 := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
      e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW b.2]
  rw [← TopPair.singularCohomologyMap_comp_apply, hfib, TopPair.singularCohomologyMap_comp_apply]
  exact ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K (ModuleCat.of K K)
    (finrank ℝ F)).mapIso
      (e.continuousLinearEquivAt ℝ b (hW b.2)).complZeroPairIso.symm.op
    ).toLinearEquiv.span_singleton_apply_eq_top_iff.2 (hu b.1 b.2)

include hW in
/-- **Bijectivity of `TopCat.pullbackCupRestrict` over a subset of a trivializing set.** If
`W ⊆ e.baseSet` for a linear trivialization `e`, and `u ∈ Hʳ(E, E₀; K)` restricts to a generator on
every fibre over `W`, then `TopCat.pullbackCupRestrict` of `u` over `W` is bijective in every
degree. -/
theorem bijective_pullbackCupRestrict_thomPairProj
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ W, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E) (zeroSectionCompl F E) M W
      (finrank ℝ F) p m h u) := by
  rw [bijective_pullbackCupRestrict_thomPairProj_iff, TopCat.pullbackCupRestrict_apply]
  refine e.bijective_pullbackCup_thomPairOver hW M (fun b hb ↦ ?_) h
  have hfib : TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) (finrank ℝ F)
      (TopPair.singularCohomologyMap
        (TopCat.restrictPreimagePairMap (thomPairProjHom F E) (zeroSectionCompl F E) W)
        (finrank ℝ F) u) =
      TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u :=
    (TopPair.singularCohomologyMap_comp_apply (fiberThomPairOverMap F E hb)
      (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W) (finrank ℝ F) u).symm.trans
      (congrArg (fun φ ↦ TopPair.singularCohomologyMap φ (finrank ℝ F) u)
        (fiberThomPairOverMap_comp_restrictPreimagePairMap F E hb))
  rw [hfib]
  exact hu b hb

end TrivializingSet

section Global

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ] (he : e.baseSet = Set.univ)
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

include he in
/-- **The Thom isomorphism for a globally trivializable bundle**: if `e` is a linear trivialization
over the whole base and `u` is a Thom class of `E`, then `TauCeti.thomMap` is bijective in every
degree. -/
theorem bijective_thomMap
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨hF, hu'⟩ := isThomClass_iff.1 hu
  rw [thomMap_def]
  refine (TopCat.bijective_pullbackCupRestrict_univ_iff (thomPairProj F E)
    (zeroSectionCompl F E) M h u).1 ?_
  exact e.bijective_pullbackCupRestrict_thomPairProj (he ▸ Subset.rfl) M (fun b _ ↦ hu' b) h

/-- **The Thom isomorphism `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` for a globally trivializable bundle.** -/
def thomEquiv
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (p m : ℕ) (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u) (e.bijective_thomMap he M hu h)

@[simp]
theorem thomEquiv_apply
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (p m : ℕ) (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    e.thomEquiv he M hu p m h a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

end Global

end Bundle.Trivialization

/-! ### Finite unions of trivializing open sets and compact bases -/

namespace TauCeti

section FiniteUnion

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **Bijectivity of the Thom map over a finite union of trivializing open sets.** If each open set
`W i`, `i ∈ s`, lies in the base set of a linear trivialization, and `u ∈ Hʳ(E, E₀; K)` restricts
to a generator on every fibre over `⋃ i ∈ s, W i`, then `TopCat.pullbackCupRestrict` of `u` over
`⋃ i ∈ s, W i` is bijective in every degree. -/
theorem bijective_pullbackCupRestrict_thomPairProj_biUnion [FiniteDimensional ℝ F] {ι : Type*}
    (s : Finset ι) {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E) (zeroSectionCompl F E) M
      (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  classical
  rw [bijective_pullbackCupRestrict_thomPairProj_iff]
  induction s using Finset.induction_on generalizing W p m with
  | empty =>
    have hW_empty : (⋃ i ∈ (∅ : Finset ι), W i) = (∅ : Set B) := by simp
    rw [hW_empty]
    have : IsEmpty (TopCat.of ↥(∅ : Set B)) := Set.isEmpty_coe_sort.2 rfl
    have hdom : Subsingleton
        ((TopCat.of ↥(∅ : Set B)).singularCohomology (ModuleCat.of K K) K M p) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_singularCohomology_of_isEmpty (ModuleCat.of K K) K M _ p)
    have hcod : Subsingleton ((thomPairOver F E ∅).singularCohomology (ModuleCat.of K K) K M m) :=
      ModuleCat.subsingleton_of_isZero
        (TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of K K) M m
          fun j _ ↦ isZero_singularHomology_thomPairOver_empty (ModuleCat.of K K) j)
    exact ⟨fun x y _ ↦ hdom.elim x y, fun y ↦ ⟨0, hcod.elim _ y⟩⟩
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    refine TopCat.bijective_pullbackCupRestrict_union (thomPairProjHom F E) (zeroSectionCompl F E) M
      (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (hs i hi)) u
      (fun q _ ↦ ?_) (fun q _ ↦ ?_) (fun q _ ↦ ?_) (fun j hj ↦ ?_) h
    · rw [← bijective_pullbackCupRestrict_thomPairProj_iff]
      exact e.bijective_pullbackCupRestrict_thomPairProj he M
        (fun b hb ↦ hu b (mem_iUnion₂.2 ⟨a, Finset.mem_insert_self a s, hb⟩)) rfl
    · exact ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hWe i (hs i hi))
        (fun b hb ↦ hu b (by
          rw [Finset.set_biUnion_insert]
          exact Or.inr hb)) rfl
    · rw [inter_iUnion₂]
      refine ih (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter (hWo i (hs i hi)))
        (fun i hi ↦ ?_) (fun b hb ↦ hu b ?_) rfl
      · obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
        exact ⟨e', he', inter_subset_right.trans hi'⟩
      · obtain ⟨_, ⟨i, rfl⟩, _, ⟨hi, rfl⟩, hba, _⟩ := hb
        exact mem_iUnion₂.2 ⟨a, Finset.mem_insert_self a s, hba⟩
    · rw [inter_iUnion₂]
      refine isZero_singularCohomology_thomPairOver_biUnion (ModuleCat.of K K) M s
        (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter (hWo i (hs i hi)))
        (fun i hi ↦ ?_) (by omega)
      obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
      exact ⟨e', he', inter_subset_right.trans hi'⟩

/-- **The Thom isomorphism for a bundle covered by finitely many trivializing open sets**: if the
finitely many open sets `W i`, `i ∈ s`, each contained in the base set of a linear trivialization,
cover `B`, and `u` is a Thom class of `E`, then `TauCeti.thomMap` is bijective in every degree. -/
theorem bijective_thomMap_of_iUnion_eq_univ {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = Set.univ)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨hF, hu'⟩ := isThomClass_iff.1 hu
  rw [thomMap_def]
  refine (TopCat.bijective_pullbackCupRestrict_univ_iff (thomPairProj F E)
    (zeroSectionCompl F E) M h u).1 ?_
  rw [← hW]
  exact bijective_pullbackCupRestrict_thomPairProj_biUnion M s hWo hWe (fun b _ ↦ hu' b) h

/-- **The Thom isomorphism over a compact base**: for a real vector bundle `E → B` over a compact
space `B` and any Thom class `u ∈ Hʳ(E, E₀; K)`, the Thom map `Hᵖ(B; M) ⟶ Hᵐ(E, E₀; M)`,
`a ↦ π^*a ⌣ u`, is bijective whenever `p + finrank ℝ F = m`, for any commutative ring `K` and any
`K`-module `M`. -/
theorem bijective_thomMap_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet) (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
  exact bijective_thomMap_of_iUnion_eq_univ M t
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩)
    (univ_subset_iff.1 ht) hu h

/-- **The Thom isomorphism `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` over a compact base.** -/
def thomEquivOfCompactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (p m : ℕ) (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u)
    (bijective_thomMap_of_compactSpace M hu h)

@[simp]
theorem thomEquivOfCompactSpace_apply [CompactSpace B] [VectorBundle ℝ F E]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (p m : ℕ) (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfCompactSpace M hu p m h a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

end FiniteUnion

/-! ### Arbitrary bases with field coefficients -/

section FieldHelpers

namespace ThomBijectiveField

variable {K : Type w} [CommRing K]

/-- For a pair `P` and a map `g : P.fst ⟶ Z`, the relative cap product `Hₘ(P; K) ⟶ Hₚ(P.fst; K)`
with `u ∈ Hⁿ(P; K)` followed by push-forward along `g`. For `(thomPair F E, thomPairProj F E)` this
is `TauCeti.homologyThomMap`. -/
private def capPushforward (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) (n p m : ℕ)
    (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    P.singularHomology (ModuleCat.of K K) m ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj Z :=
  P.singularCap K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom n p m h u ≫
    ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map g

private lemma capPushforward_naturality {P P' : TopPair.{w}} (φ : P ⟶ P') {Z Z' : TopCat.{w}}
    (g : P.fst ⟶ Z) (g' : P'.fst ⟶ Z') (f : Z ⟶ Z') (hφ : TopPair.Hom.fst φ ≫ g' = g ≫ f)
    {n p m : ℕ} (h : n + p = m)
    (u : P'.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    capPushforward P g n p m h (TopPair.singularCohomologyMap φ n u) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map f =
      TopPair.singularHomologyMap φ (ModuleCat.of K K) m ≫ capPushforward P' g' n p m h u := by
  rw [capPushforward, capPushforward, Category.assoc, ← Functor.map_comp, ← hφ, Functor.map_comp,
    ← Category.assoc, TopPair.singularCap_naturality, Category.assoc]

/-- Under the Kronecker pairing, `capPushforward` is `(-1)^(n * p)` times the transpose of
`TopPair.pullbackCup`. -/
private lemma capPushforward_comp_singularKronecker (P : TopPair.{w}) {Z : TopCat.{w}}
    (g : P.fst ⟶ Z) {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Z.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) :
    capPushforward P g n p m h u ≫ Z.singularKronecker K p a =
      ((-1 : ℤ) ^ (n * p)) • P.singularKronecker K m
        (P.pullbackCup (ModuleCat.of K K) g n p m (by omega) u a) := by
  rw [capPushforward, Category.assoc, ← TopCat.singularKronecker_naturality,
    TopPair.singularCap_comp_singularKronecker, TopPair.pullbackCup_apply,
    TopPair.singularCup_gradedComm K P (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u' := (λ_ (ModuleCat.of K K)).inv) (μ' := (λ_ (ModuleCat.of K K)).hom)
      (μ := (ρ_ (ModuleCat.of K K)).hom) ?_ ?_ (by omega), map_zsmul, mul_comm]
  -- `pullbackCup` cups along `𝟙_ (ModuleCat K)`, which is definitionally `ModuleCat.of K K`.
  · rfl
  · rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, ← unitors_inv_equal]
    rfl
  · exact braiding_leftUnitor _

/-- Over a field, `capPushforward` is bijective if and only if `TopPair.pullbackCup` is. -/
private lemma bijective_capPushforward_iff {K : Type w} [Field K] (P : TopPair.{w})
    {Z : TopCat.{w}} (g : P.fst ⟶ Z) {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (capPushforward P g n p m h u).hom ↔
      Function.Bijective (P.pullbackCup (ModuleCat.of K K) g n p m (by omega) u) := by
  set T := (capPushforward P g n p m h u).hom
  have hc : ((-1 : K) ^ (n * p)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have key (a : Z.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) :
      P.singularCohomologyDualEquiv m
          (P.pullbackCup (ModuleCat.of K K) g n p m (by omega) u a) =
        LinearEquiv.smulOfNeZero K _ _ hc (T.dualMap (Z.singularCohomologyDualEquiv p a)) := by
    ext x
    have hx := congrArg (fun φ ↦ φ.hom x) (capPushforward_comp_singularKronecker P g h u a)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul,
      LinearMap.smul_apply] at hx
    rw [LinearEquiv.smulOfNeZero_apply, LinearMap.smul_apply, LinearMap.dualMap_apply,
      TopPair.singularCohomologyDualEquiv_apply, TopCat.singularCohomologyDualEquiv_apply, hx]
    simp [← Int.cast_smul_eq_zsmul K, ← mul_assoc, ← mul_pow]
  have e : ⇑(P.pullbackCup (ModuleCat.of K K) g n p m (by omega) u) =
      ⇑(P.singularCohomologyDualEquiv m).symm ∘ ⇑(LinearEquiv.smulOfNeZero K _ _ hc) ∘
        ⇑T.dualMap ∘ ⇑(Z.singularCohomologyDualEquiv p) := by
    funext a
    simp only [Function.comp_apply, ← key, LinearEquiv.symm_apply_apply]
  rw [e, EquivLike.comp_bijective, EquivLike.comp_bijective, EquivLike.bijective_comp,
    LinearMap.dualMap_bijective_iff]

section BundleColimit

variable {B : Type w} [TopologicalSpace B] (F : Type w) [NormedAddCommGroup F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- The diagram of finite unions of the chosen trivializing open sets in the base. -/
private abbrev baseDiagram : Finset B ⥤ TopCat.{w} where
  obj s := TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet)
  map f := TopCat.ofHom (ContinuousMap.inclusion
    (biUnion_subset_biUnion_left (Finset.coe_subset.2 f.le)))

/-- The cocone of inclusions of finite unions of the chosen trivializing open sets into `B`. -/
private abbrev baseCocone : Cocone (baseDiagram F E) where
  pt := TopCat.of B
  ι := { app _ := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ }

/-- In every degree `p`, `Hₚ(B; K)` is the filtered colimit of `Hₚ(W_s; K)` over `s : Finset B`. -/
private def isColimitBaseSingularHomology (K : Type w) [CommRing K] (p : ℕ) :
    IsColimit (((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).mapCocone
      (baseCocone F E)) :=
  isColimitMapCoconeSingularHomology (ModuleCat.of K K) p (baseCocone F E)
    (fun _ ↦ IsEmbedding.subtypeVal) fun L hL ↦ by
      obtain ⟨s, hs⟩ := hL.elim_finite_subcover _
        (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
          mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
      exact ⟨s, fun b hb ↦ ⟨⟨b, hs hb⟩, rfl⟩⟩

/-- The homology Thom map restricted to `(E|_W, E₀|_W) ⟶ W`. -/
private def homologyThomMapOver {K : Type w} [CommRing K] (W : Set B) (n p m : ℕ) (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    (thomPairOver F E W).singularHomology (ModuleCat.of K K) m ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj (TopCat.of W) :=
  capPushforward (thomPairOver F E W)
    (TopCat.ofHom ((⟨π F E, FiberBundle.continuous_proj F E⟩ :
      C(TotalSpace F E, B)).restrictPreimage W))
    n p m h
    (TopPair.singularCohomologyMap
      (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W) n u)

private lemma homologyThomMapOver_naturality {K : Type w} [CommRing K] {W W' : Set B}
    (hWW' : W ⊆ W') {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMapOver F E W n p m h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.inclusion hWW')) =
      TopPair.singularHomologyMap (thomPairOverMap F E hWW') (ModuleCat.of K K) m ≫
        homologyThomMapOver F E W' n p m h u := by
  have hu : TopPair.singularCohomologyMap (thomPairOverMap F E hWW') n
      (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W') n u) =
      TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n u := by
    rw [← TopPair.singularCohomologyMap_comp_apply, thomPairOverMap_comp_restrictPreimagePairMap]
  unfold homologyThomMapOver
  rw [← hu]
  exact capPushforward_naturality (thomPairOverMap F E hWW')
    (TopCat.ofHom ((⟨π F E, FiberBundle.continuous_proj F E⟩ :
      C(TotalSpace F E, B)).restrictPreimage W))
    (TopCat.ofHom ((⟨π F E, FiberBundle.continuous_proj F E⟩ :
      C(TotalSpace F E, B)).restrictPreimage W'))
    (TopCat.ofHom (ContinuousMap.inclusion hWW'))
    (TopCat.ext fun v ↦ congrArg
      ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).restrictPreimage W')
      (thomPairOverMap_fst_apply F E hWW' v)) h _

private lemma homologyThomMapOver_comp_ι {K : Type w} [CommRing K] (W : Set B) {n p m : ℕ}
    (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMapOver F E W n p m h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(W, B))) =
      TopPair.singularHomologyMap (thomPairOverMap F E (subset_univ W)) (ModuleCat.of K K) m ≫
        TopPair.singularHomologyMap (thomPairOverUnivIso F E).hom (ModuleCat.of K K) m ≫
          homologyThomMap F E (ModuleCat.of K K) n p m h u := by
  have hmap : thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom =
      TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W := by
    rw [thomPairOverUnivIso_hom, thomPairOverMap_comp_restrictPreimagePairMap]
  rw [← TopPair.singularHomologyMap_comp_assoc, hmap, homologyThomMap_apply]
  exact capPushforward_naturality
    (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
      (zeroSectionCompl F E) W)
    (TopCat.ofHom ((⟨π F E, FiberBundle.continuous_proj F E⟩ :
      C(TotalSpace F E, B)).restrictPreimage W))
    (thomPairProj F E)
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(W, B)))
    (TopCat.ext fun v ↦ (thomPairProj_apply F E _).trans
      (congrArg (π F E) (TopCat.restrictPreimagePairMap_fst_apply _ _ _ v)))
    h u

private lemma singularHomology_thomPairOver_obj_eq (K : Type w) [CommRing K] (s : Finset B)
    (m : ℕ) :
    (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology
        (ModuleCat.of K K) m =
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
        ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) := by
  rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]

private lemma singularHomology_thomPair_pt_eq (K : Type w) [CommRing K] (m : ℕ) :
    (thomPair F E).singularHomology (ModuleCat.of K K) m =
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
        (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt := by
  rw [thomPairFiniteTrivializingUnionCocone_pt, TopPair.singularHomologyFunctor_obj]

variable [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E]

private lemma isIso_homologyThomMapOver_finiteTrivializingUnion
    {K : Type w} [Field K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (s : Finset B) {p m : ℕ} (h : finrank ℝ F + p = m) :
    IsIso (homologyThomMapOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)
      (finrank ℝ F) p m h u) := by
  obtain ⟨hF, hu'⟩ := isThomClass_iff.1 hu
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  refine (bijective_capPushforward_iff (thomPairOver F E _) _ h _).2 ?_
  have hbij := (bijective_pullbackCupRestrict_thomPairProj_iff F E (ModuleCat.of K K)
    (⋃ b ∈ s, (trivializationAt F E b).baseSet) (p := p) (m := m) (by omega) u).1
    (bijective_pullbackCupRestrict_thomPairProj_biUnion (ModuleCat.of K K) s
      (fun b _ ↦ (trivializationAt F E b).open_baseSet)
      (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩)
      (fun b _ ↦ hu' b) (p := p) (m := m) (by omega))
  rwa [TopCat.pullbackCupRestrict_apply] at hbij

/-- The local homology Thom isomorphisms over `W_s`, assembled into a natural isomorphism over
`s : Finset B`. -/
private def finiteUnionHomologyThomNatIso {K : Type w} [Field K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor (ModuleCat.of K K) m ≅
      baseDiagram F E ⋙
        (singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K) :=
  NatIso.ofComponents
    (fun s ↦
      haveI := isIso_homologyThomMapOver_finiteTrivializingUnion F E hu s h
      eqToIso (singularHomology_thomPairOver_obj_eq F E K s m).symm ≪≫
        asIso (homologyThomMapOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)
          (finrank ℝ F) p m h u))
    fun {s t} f ↦ by
      have := isIso_homologyThomMapOver_finiteTrivializingUnion F E hu s h
      have := isIso_homologyThomMapOver_finiteTrivializingUnion F E hu t h
      dsimp only [Functor.comp_obj, Functor.comp_map, baseDiagram]
      simp only [thomPairFiniteTrivializingUnionDiagram_map, TopPair.singularHomologyFunctor_map,
        Iso.trans_hom, eqToIso.hom, asIso_hom, Category.assoc, TopPair.singularHomologyMap_comp,
        TopPair.singularHomologyMap_eqToHom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact congrArg (eqToHom _ ≫ ·) (homologyThomMapOver_naturality F E
        (biUnion_subset_biUnion_left (Finset.coe_subset.2 f.le)) h u).symm

end BundleColimit

end ThomBijectiveField

end FieldHelpers

section Field

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [Field K]

/-- **The homology Thom isomorphism over an arbitrary base with field coefficients**: for any real
vector bundle `E → B` (with no compactness, paracompactness or separation hypotheses on `B`), any
field `K`, and any Thom class `u ∈ Hʳ(E, E₀; K)`, the homology Thom map
`Hₘ(E, E₀; K) ⟶ Hₚ(B; K)`, `x ↦ π_*(x ⌢ u)`, is an isomorphism whenever `finrank ℝ F + p = m`. -/
theorem isIso_homologyThomMap_of_field
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    IsIso (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
  let P₁ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) m
  let P₂ := ThomBijectiveField.isColimitBaseSingularHomology F E K p
  let α := ThomBijectiveField.finiteUnionHomologyThomNatIso F E hu h
  let eqPt := ThomBijectiveField.singularHomology_thomPair_pt_eq F E K m
  have hcocone : eqToHom eqPt.symm ≫
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u =
      (P₁.coconePointsIsoOfNatIso P₂ α).hom := by
    refine P₁.hom_ext fun s ↦ ?_
    have := ThomBijectiveField.isIso_homologyThomMapOver_finiteTrivializingUnion F E hu s h
    refine (?_ : _ = α.hom.app s ≫ _).trans (P₁.comp_coconePointsIsoOfNatIso_hom P₂ α s).symm
    dsimp only [Functor.mapCocone_ι_app, ThomBijectiveField.baseCocone, α,
      ThomBijectiveField.finiteUnionHomologyThomNatIso, NatIso.ofComponents_hom_app,
      Iso.trans_hom, eqToIso.hom, asIso_hom]
    simp only [thomPairFiniteTrivializingUnionCocone_ι_app, TopPair.singularHomologyFunctor_map,
      Category.assoc, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact congrArg (eqToHom _ ≫ ·) (ThomBijectiveField.homologyThomMapOver_comp_ι F E _ h u).symm
  have : IsIso (eqToHom eqPt.symm ≫
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
    rw [hcocone]
    exact (P₁.coconePointsIsoOfNatIso P₂ α).isIso_hom
  exact IsIso.of_isIso_comp_left (eqToHom eqPt.symm) _

/-- **Bijectivity of the homology Thom map over an arbitrary base with field coefficients.** -/
theorem bijective_homologyThomMap_of_field
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom := by
  have := isIso_homologyThomMap_of_field hu h
  exact (asIso (homologyThomMap F E (ModuleCat.of K K)
    (finrank ℝ F) p m h u)).toLinearEquiv.bijective

/-- **The homology Thom isomorphism `Hₘ(E, E₀; K) ≅ Hₚ(B; K)` over an arbitrary base** with
coefficients in a field `K`. -/
def homologyThomIsoOfField
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (p m : ℕ) (h : finrank ℝ F + p = m := by lia) :
    (thomPair F E).singularHomology (ModuleCat.of K K) m ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  @asIso _ _ _ _ (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u)
    (isIso_homologyThomMap_of_field hu h)

@[simp]
theorem homologyThomIsoOfField_hom
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (p m : ℕ) (h : finrank ℝ F + p = m) :
    (homologyThomIsoOfField hu p m h).hom =
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u :=
  (rfl)

/-- **The cohomology Thom isomorphism over an arbitrary base with field coefficients**: for any real
vector bundle `E → B` (over an arbitrary topological space `B`), any field `K`, and any Thom class
`u ∈ Hʳ(E, E₀; K)`, the Thom map `Hᵖ(B; K) ⟶ Hᵐ(E, E₀; K)`, `a ↦ π^*a ⌣ u`, is bijective whenever
`p + finrank ℝ F = m`. With `K = ZMod 2` (or any field with `Subsingleton Kˣ`) this applies to
every real vector bundle without any orientation via
`TauCeti.existsUnique_isThomClass_of_subsingleton_units`. -/
theorem bijective_thomMap_of_field
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) :=
  (bijective_homologyThomMap_iff F E (p := p) (m := m) (by omega) u).1
    (bijective_homologyThomMap_of_field hu (by omega))

/-- **The cohomology Thom isomorphism `Hᵖ(B; K) ≃ₗ[K] Hᵐ(E, E₀; K)` over an arbitrary base** with
coefficients in a field `K`. -/
def thomEquivOfField
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (p m : ℕ) (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) m :=
  LinearEquiv.ofBijective (thomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u)
    (bijective_thomMap_of_field hu h)

@[simp]
theorem thomEquivOfField_apply
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (p m : ℕ) (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) :
    thomEquivOfField hu p m h a =
      thomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u a :=
  (rfl)

end Field

end TauCeti

/-! ### Oriented vector bundles -/

namespace TauCeti.VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type*} [Fintype ι]
  (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
  (ω : Orientation ℝ F ι)

/-- **The Thom isomorphism `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` for an oriented vector bundle over a
compact base**, induced by `o.thomClassOfModel hι ω g` for any generator `g ∈ Hʳ(F, F ∖ {0}; K)` and
any commutative ring `K` and `K`-module `M`. -/
def thomEquivOfCompactSpace [CompactSpace B] {K : Type w} [CommRing K] (M : ModuleCat.{w} K)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (p m : ℕ) (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  TauCeti.thomEquivOfCompactSpace M (o.isThomClass_thomClassOfModel hι ω hg) p m h

@[simp]
theorem thomEquivOfCompactSpace_apply [CompactSpace B] {K : Type w} [CommRing K]
    (M : ModuleCat.{w} K)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (p m : ℕ) (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    o.thomEquivOfCompactSpace hι ω M hg p m h a =
      thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g) a :=
  (rfl)

/-- **The cohomology Thom isomorphism `Hᵖ(B; K) ≃ₗ[K] Hᵐ(E, E₀; K)` for an oriented vector bundle
over an arbitrary base** with coefficients in a field `K`. -/
def thomEquivOfField {K : Type w} [Field K]
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (p m : ℕ) (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) m :=
  TauCeti.thomEquivOfField (o.isThomClass_thomClassOfModel hι ω hg) p m h

@[simp]
theorem thomEquivOfField_apply {K : Type w} [Field K]
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (p m : ℕ) (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) :
    o.thomEquivOfField hι ω hg p m h a =
      thomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h (o.thomClassOfModel hι ω g) a :=
  (rfl)

/-- **The homology Thom isomorphism `Hₘ(E, E₀; K) ≅ Hₚ(B; K)` for an oriented vector bundle over an
arbitrary base** with coefficients in a field `K`. -/
def homologyThomIsoOfField {K : Type w} [Field K]
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (p m : ℕ) (h : finrank ℝ F + p = m := by lia) :
    (thomPair F E).singularHomology (ModuleCat.of K K) m ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  TauCeti.homologyThomIsoOfField (o.isThomClass_thomClassOfModel hι ω hg) p m h

@[simp]
theorem homologyThomIsoOfField_hom {K : Type w} [Field K]
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (p m : ℕ) (h : finrank ℝ F + p = m) :
    (o.homologyThomIsoOfField hι ω hg p m h).hom =
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h (o.thomClassOfModel hι ω g) :=
  (rfl)

end TauCeti.VectorBundleOrientation
