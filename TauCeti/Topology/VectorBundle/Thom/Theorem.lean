/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Homology
import TauCeti.AlgebraicTopology.Cohomology.Cap.ChainMap
import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.PullbackCup

/-!
# The Thom isomorphism theorem in cohomology and homology

Let `E → B` be a real vector bundle of finite rank `r = dim F` over an arbitrary topological space
`B`, with Thom pair `(E, E₀)` (`E₀` the complement of the zero section) and projection
`π : E ⟶ B`. Let `K` be a commutative ring and let `u ∈ Hʳ(E, E₀; K)` be a Thom class
(`TauCeti.IsThomClass`), meaning `u` restricts to a generator of `Hʳ(E_b, E_b ∖ {0}; K) ≅ K` on
every fibre. This file proves the **Thom isomorphism theorem** in both cohomology and homology
for arbitrary `K`-module coefficients, with no compactness, paracompactness, or finite-type
assumptions on `B`:

* **Cohomology** (`TauCeti.bijective_thomMap`, `TauCeti.thomEquiv`): for every `K`-module `M` and
  all degrees `p + r = m`, the Thom map `TauCeti.thomMap`
  `Φ_u : Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`, `a ↦ π^*a ⌣ u`,
  is an isomorphism of `K`-modules.
* **Homology** (`TauCeti.isIso_homologyThomMap`, `TauCeti.homologyThomIso`): for every `K`-module
  `A` and all degrees `r + p = m`, the homology Thom map `TauCeti.homologyThomMap`
  `Ψ_u : Hₘ(E, E₀; A) ≅ Hₚ(B; A)`, `x ↦ π_*(x ⌢ u)`,
  is an isomorphism in `ModuleCat K`.

The proof follows Milnor–Stasheff (§10, Theorem 10.4), Hatcher (§4.D, Theorem 4D.10), and
Spanier (Ch. 5, §7), lifted to the chain level so that the passage from finite trivializing unions
to an arbitrary base works directly in homology without needing `lim¹` vanishing or
paracompactness:

1. **Trivializing open sets**: over an open set `W` contained in the base set of a linear
   trivialization `e`, `e.thomPairOverIso` identifies `(E|_W, E₀|_W)` with the product Thom pair
   `(W × F, W × (F ∖ {0}))`, where bijectivity of `a ↦ π^*a ⌣ u` holds for every coefficient
   module `M` by `TauCeti.bijective_pullbackCup_prodThomPair`.
2. **Finite trivializing unions**: induction on a finite family of trivializing open sets, using
   the Mayer–Vietoris step `TopCat.bijective_pullbackCupRestrict_union` and below-rank vanishing
   `TauCeti.isZero_singularCohomology_thomPairOver_biUnion`, gives bijectivity of
   `a ↦ π^*a ⌣ u` over every finite union `W_s` of trivializing open sets for every `K`-module `M`.
3. **Chain quasi-isomorphism over finite unions**: lifting `u` to a cocycle `ζ`, the dual
   detection theorem `TopPair.quasiIso_pullbackCapChainMap_of_bijective_pullbackCup` upgrades
   cohomology bijectivity over `W_s` (for all `M`) into a quasi-isomorphism of the cap-and-push
   chain map `TopPair.pullbackCapChainMap` over `W_s`, hence an isomorphism on homology
   `Hₘ(E|_{W_s}, E₀|_{W_s}; K) ≅ Hₚ(W_s; K)` for every `r + p = m`.
4. **Arbitrary bases via filtered colimits**: singular homology of both `B` and `(E, E₀)` is the
   filtered colimit over all finite unions `W_s` of the preferred trivializing open sets, so the
   homology Thom map `Hₘ(E, E₀; K) ⟶ Hₚ(B; K)` is an isomorphism for every `r + p = m`.
5. **Global chain quasi-isomorphism and arbitrary coefficients**: together with below-rank homology
   vanishing (`TauCeti.isZero_singularHomology_thomPair`), this makes the global chain map
   `TopPair.pullbackCapChainMap` a quasi-isomorphism of projective chain complexes over `K`.
   Applying `Hom(-, M)` (`TopPair.bijective_pullbackCup_of_quasiIso_pullbackCapChainMap`) yields
   the cohomology Thom isomorphism for all `M`, and tensoring with `A`
   (`TopPair.isIso_singularCap_comp_map_of_quasiIso_self`) yields the homology Thom isomorphism for
   all `A`.

Specializing to the canonical Thom class `TauCeti.VectorBundleOrientation.thomClassOfModel` of an
oriented bundle gives the oriented Thom isomorphisms in cohomology and homology
(`TauCeti.VectorBundleOrientation.thomEquivOfModel`,
`TauCeti.VectorBundleOrientation.homologyThomIsoOfModel`). Together with
`TauCeti.existsUnique_isThomClass_of_subsingleton_units`, the general theorem also yields the
mod-2 Thom isomorphism for arbitrary (not necessarily orientable) real vector bundles.

## Main definitions and results

* `TauCeti.bijective_thomMap`, `TauCeti.thomEquiv`: the Thom isomorphism in cohomology for
  arbitrary `K`-module coefficients and an arbitrary base space.
* `TauCeti.isIso_homologyThomMap`, `TauCeti.bijective_homologyThomMap`, `TauCeti.homologyThomIso`:
  the Thom isomorphism in homology for arbitrary `K`-module coefficients and an arbitrary base.
* `TauCeti.VectorBundleOrientation.thomEquivOfModel`,
  `TauCeti.VectorBundleOrientation.homologyThomIsoOfModel`: the cohomology and homology Thom
  isomorphisms of an oriented real vector bundle.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), §4.D, Theorem 4D.10.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Limits Module MonoidalCategory Set

universe w

namespace TauCeti

section Helpers

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K]

/-- The bundle projection `π : E ⟶ B` as an explicit `TopCat` morphism whose underlying function
is definitionally `π F E`, so `TopCat.pullbackCupRestrict` and `TopCat.restrictPreimagePairMap`
apply directly to `thomPairOver F E W`. -/
private abbrev projHom (F : Type w) [TopologicalSpace F] (E : B → Type w)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] :
    TopCat.of (TotalSpace F E) ⟶ TopCat.of B :=
  TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩

/-- **Trivializing open set step**: over a subset `W` contained in the base set of a linear
trivialization `e`, the pullback-cup map `a ↦ π^*a ⌣ u|_W` of a Thom class `u` is bijective for
every `K`-module `M` and every `p + finrank ℝ F = m`. -/
private theorem bijective_pullbackCupRestrict_of_subset_baseSet
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet)
    (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective
      (TopCat.pullbackCupRestrict (projHom F E) (zeroSectionCompl F E) M W
        (finrank ℝ F) p m h u) := by
  have := (isThomClass_iff.1 hu).1
  let φ := e.thomPairOverIso ℝ hW
  have hproj : TopPair.Hom.fst φ.inv ≫
        TopCat.ofHom ((projHom F E).hom.restrictPreimage W) =
      prodThomPairProj W F ≫ 𝟙 (TopCat.of W) := by
    rw [Category.comp_id]
    refine TopCat.ext fun x ↦ Subtype.ext ?_
    have hx : TopPair.Hom.fst (e.thomPairOverIso ℝ hW).hom (TopPair.Hom.fst φ.inv x) = x := by
      change (TopPair.Hom.fst φ.inv ≫ TopPair.Hom.fst φ.hom) x = x
      rw [← TopPair.Hom.fst_comp, φ.inv_hom_id]
      rfl
    let x' : ↥W × F := x
    let y : ↥(π F E ⁻¹' W) := TopPair.Hom.fst φ.inv x
    have hy : (⟨y.1.proj, y.2⟩, (e y.1).2) = x' :=
      (e.thomPairOverIso_hom_fst_apply ℝ hW y).symm.trans hx
    change y.1.proj = (prodThomPairProj (↥W) F x').1
    rw [prodThomPairProj_apply]
    exact congrArg (fun p : ↥W × F ↦ p.1.1) hy
  rw [TopCat.pullbackCupRestrict_apply]
  refine (TopPair.bijective_pullbackCup_iff_of_isIso φ.inv (𝟙 (TopCat.of W)) hproj h _).1 ?_
  refine bijective_pullbackCup_prodThomPair M _ (fun b ↦ ?_) p m h
  have hfib : prodThomPairFiberMap F b ≫ φ.inv =
      (e.continuousLinearEquivAt ℝ b (hW b.2)).complZeroPairIso.inv ≫
        fiberThomPairOverMap F E b.2 := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
      e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW b.2]
  have hcomp : fiberThomPairOverMap F E b.2 ≫
        TopCat.restrictPreimagePairMap (projHom F E) (zeroSectionCompl F E) W =
      fiberThomPairMap F E b.1 :=
    fiberThomPairOverMap_comp_restrictPreimagePairMap F E b.2
  rw [← TopPair.singularCohomologyMap_comp_apply, hfib,
    ← TopPair.singularCohomologyMap_comp_apply, Category.assoc, hcomp,
    TopPair.singularCohomologyMap_comp_apply]
  let fEquiv : (TopPair.ofSubset (X := TopCat.of (E b.1)) ({0}ᶜ : Set (E b.1))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F) ≃ₗ[K]
      (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F) :=
    ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)).mapIso
        (e.continuousLinearEquivAt ℝ b (hW b.2)).complZeroPairIso.symm.op).toLinearEquiv
  have hspan := (Submodule.map_eq_top_iff (e := fEquiv)).2 ((isThomClass_iff.1 hu).2 b.1)
  rw [← Submodule.span_image_linearEquiv fEquiv, Set.image_singleton] at hspan
  exact hspan

/-- **Finite trivializing union step**: over a finite union `W = ⋃ i ∈ s, W i` of trivializing
open sets, the pullback-cup map `a ↦ π^*a ⌣ u|_W` of a Thom class `u` is bijective for every
`K`-module `M` and every `p + finrank ℝ F = m`. -/
private theorem bijective_pullbackCupRestrict_biUnion {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective
      (TopCat.pullbackCupRestrict (projHom F E) (zeroSectionCompl F E) M
        (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  classical
  have := (isThomClass_iff.1 hu).1
  induction s using Finset.induction_on generalizing W p m with
  | empty =>
    have h0 : (⋃ i ∈ (∅ : Finset ι), W i) = ∅ := by simp
    have hSrc : Subsingleton ((TopCat.of ↥(⋃ i ∈ (∅ : Finset ι), W i)).singularCohomology
        (ModuleCat.of K K) K M p) := by
      have : IsEmpty (TopCat.of ↥(⋃ i ∈ (∅ : Finset ι), W i)) := by
        rw [h0]
        exact inferInstanceAs (IsEmpty ↥(∅ : Set B))
      exact ModuleCat.subsingleton_of_isZero
        (isZero_singularCohomology_of_isEmpty (ModuleCat.of K K) K M _ p)
    have hTgt : Subsingleton
        ((thomPairOver F E (⋃ i ∈ (∅ : Finset ι), W i)).singularCohomology
          (ModuleCat.of K K) K M m) := by
      refine ModuleCat.subsingleton_of_isZero
        (TopPair.isZero_singularCohomology_of_isZero_singularHomology _ _ _ _ fun j _ ↦ ?_)
      simpa [h0] using isZero_singularHomology_thomPairOver_empty (F := F) (E := E)
        (ModuleCat.of K K) j
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  | insert a s _ ih =>
    have hU : (⋃ i ∈ insert a s, W i) = W a ∪ ⋃ i ∈ s, W i := by
      ext x
      simp
    rw [hU]
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    have hWa : IsOpen (W a) := hWo a (Finset.mem_insert_self a s)
    have hWs : IsOpen (⋃ i ∈ s, W i) :=
      isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (hs i hi)
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    refine TopCat.bijective_pullbackCupRestrict_union (projHom F E) (zeroSectionCompl F E) M
      hWa hWs u
      (fun q _ ↦ bijective_pullbackCupRestrict_of_subset_baseSet e he M rfl hu)
      (fun q _ ↦ ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hWe i (hs i hi)) rfl)
      (fun q _ ↦ by
        rw [inter_iUnion₂]
        refine ih (fun i hi ↦ hWa.inter (hWo i (hs i hi))) (fun i hi ↦ ?_) rfl
        obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
        exact ⟨e', he', inter_subset_right.trans hi'⟩)
      (fun j hj ↦ by
        rw [inter_iUnion₂]
        refine isZero_singularCohomology_thomPairOver_biUnion (ModuleCat.of K K) M s
          (fun i hi ↦ hWa.inter (hWo i (hs i hi))) (fun i hi ↦ ?_) (by omega)
        obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
        exact ⟨e', he', inter_subset_right.trans hi'⟩)
      h

/-- **Homology cap-and-pushforward isomorphism over a finite trivializing union**: for a finite
union `W = ⋃ i ∈ s, W i` of trivializing open sets, the cap-and-pushforward map
`Hₘ(E|_W, E₀|_W; K) ⟶ Hₚ(W; K)` with the restriction of a Thom class `u` is an isomorphism in
every degree `finrank ℝ F + p = m`. -/
private theorem isIso_singularCap_comp_map_thomPairOver_biUnion {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    IsIso ((thomPairOver F E (⋃ i ∈ s, W i)).singularCap K
        (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom (finrank ℝ F) p m h
        (TopPair.singularCohomologyMap
          (TopCat.restrictPreimagePairMap (projHom F E) (zeroSectionCompl F E)
            (⋃ i ∈ s, W i)) _ u) ≫
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
        (TopCat.ofHom ((projHom F E).hom.restrictPreimage (⋃ i ∈ s, W i)) :
          (thomPairOver F E (⋃ i ∈ s, W i)).fst ⟶ TopCat.of ↥(⋃ i ∈ s, W i))) := by
  have := (isThomClass_iff.1 hu).1
  obtain ⟨ζ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ (finrank ℝ F) u
  let ιW := TopCat.restrictPreimagePairMap (projHom F E) (zeroSectionCompl F E) (⋃ i ∈ s, W i)
  let πW : (thomPairOver F E (⋃ i ∈ s, W i)).fst ⟶ TopCat.of ↥(⋃ i ∈ s, W i) :=
    TopCat.ofHom ((projHom F E).hom.restrictPreimage (⋃ i ∈ s, W i))
  let ζW : ((thomPairOver F E (⋃ i ∈ s, W i)).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).cycles (finrank ℝ F) :=
    HomologicalComplex.cyclesMap (TopPair.singularCochainComplexMap ιW) (finrank ℝ F) ζ
  have hζW : ((thomPairOver F E (⋃ i ∈ s, W i)).singularCochainComplex (ModuleCat.of K K) K
        (ModuleCat.of K K)).homologyπ (finrank ℝ F) ζW =
      TopPair.singularCohomologyMap ιW (finrank ℝ F)
        (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
          (ModuleCat.of K K)).homologyπ (finrank ℝ F) ζ) :=
    (ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality _ (finrank ℝ F)) ζ).symm
  have hq : QuasiIso ((thomPairOver F E (⋃ i ∈ s, W i)).pullbackCapChainMap K
      (𝟙_ (ModuleCat.{w} K)) πW ζW) := by
    refine TopPair.quasiIso_pullbackCapChainMap_of_bijective_pullbackCup _ πW ζW
      (fun M j hj ↦ isZero_singularCohomology_thomPairOver_biUnion (ModuleCat.of K K) M s hWo hWe
        hj)
      (fun M q n hq ↦ ?_)
    rw [hζW]
    have hbij := bijective_pullbackCupRestrict_biUnion s hWo hWe M hq hu
    rw [TopCat.pullbackCupRestrict_apply] at hbij
    exact hbij
  have hIso := (TopPair.isIso_homologyMap_pullbackCapChainMap_iff K
    (thomPairOver F E (⋃ i ∈ s, W i)) (𝟙_ (ModuleCat.{w} K)) πW h ζW).1 inferInstance
  exact Eq.mp (congrArg (fun x ↦ IsIso ((thomPairOver F E (⋃ i ∈ s, W i)).singularCap K
      (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom (finrank ℝ F) p m h x ≫
    ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map πW)) hζW) hIso

section Colimit

variable [VectorBundle ℝ F E]

/-- The finite unions of the preferred trivializing open sets, as subspaces of the base. -/
private def baseFiniteTrivializingUnionDiagram (F : Type w) [TopologicalSpace F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] : Finset B ⥤ TopCat.{w} where
  obj s := TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet)
  map f := TopCat.ofHom
    (ContinuousMap.inclusion (biUnion_subset_biUnion_left (Finset.coe_subset.2 f.le)))

/-- The inclusions of the finite unions of the preferred trivializing open sets into the base. -/
private abbrev baseFiniteTrivializingUnionCocone (F : Type w) [TopologicalSpace F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] :
    Cocone (baseFiniteTrivializingUnionDiagram F E) where
  pt := TopCat.of B
  ι := { app _ := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ }

/-- In every degree `p`, the singular homology of the base is the filtered colimit of the singular
homologies of the finite unions of the preferred trivializing open sets. -/
private def isColimitSingularHomologyBaseFiniteTrivializingUnion (K : Type w) [CommRing K]
    (p : ℕ) :
    IsColimit (((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).mapCocone
      (baseFiniteTrivializingUnionCocone (B := B) F E)) :=
  isColimitMapCoconeSingularHomology (ModuleCat.of K K) p
    (baseFiniteTrivializingUnionCocone F E) (fun _ ↦ Topology.IsEmbedding.subtypeVal)
    fun L hL ↦ by
      obtain ⟨s, hs⟩ := hL.elim_finite_subcover _
        (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
          mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
      exact ⟨s, fun b hb ↦ ⟨⟨b, hs hb⟩, rfl⟩⟩

/-- **The homology Thom map with `K` coefficients is an isomorphism over an arbitrary base**:
both `Hₘ(E, E₀; K)` and `Hₚ(B; K)` are the filtered colimits of their values over finite unions of
the preferred trivializing open sets, where the cap-and-pushforward map is an isomorphism. -/
private theorem isIso_homologyThomMap_self {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    IsIso (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
  have := (isThomClass_iff.1 hu).1
  let W (s : Finset B) : Set B := ⋃ b ∈ s, (trivializationAt F E b).baseSet
  let πW (s : Finset B) : (thomPairOver F E (W s)).fst ⟶ TopCat.of ↥(W s) :=
    TopCat.ofHom ((projHom F E).hom.restrictPreimage (W s))
  let Φ (s : Finset B) :
      (thomPairOver F E (W s)).singularHomology (ModuleCat.of K K) m ⟶
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj
          (TopCat.of ↥(W s)) :=
    (thomPairOver F E (W s)).singularCap K (λ_ (ModuleCat.of K K)).inv
        (λ_ (ModuleCat.of K K)).hom (finrank ℝ F) p m h
        (TopPair.singularCohomologyMap
          (TopCat.restrictPreimagePairMap (projHom F E) (zeroSectionCompl F E) (W s)) _ u) ≫
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map (πW s)
  have hΦiso (s : Finset B) : IsIso (Φ s) :=
    isIso_singularCap_comp_map_thomPairOver_biUnion s
      (fun b _ ↦ (trivializationAt F E b).open_baseSet)
      (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) h hu
  have hObjEq (s : Finset B) :
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
          ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) =
        (thomPairOver F E (W s)).singularHomology (ModuleCat.of K K) m := by
    rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]
  have hPtEq :
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
          (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt =
        (thomPair F E).singularHomology (ModuleCat.of K K) m := by
    rw [thomPairFiniteTrivializingUnionCocone_pt, TopPair.singularHomologyFunctor_obj]
  have hΦnat {s t : Finset B} (f : s ⟶ t) :
      TopPair.singularHomologyMap
          (thomPairOverMap F E (biUnion_subset_biUnion_left (Finset.coe_subset.2 f.le)))
          (ModuleCat.of K K) m ≫ Φ t =
        Φ s ≫ ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
          ((baseFiniteTrivializingUnionDiagram F E).map f) := by
    dsimp only [Φ, baseFiniteTrivializingUnionDiagram]
    have hst : W s ⊆ W t := biUnion_subset_biUnion_left (Finset.coe_subset.2 f.le)
    have hcomp : thomPairOverMap F E hst ≫
          TopCat.restrictPreimagePairMap (projHom F E) (zeroSectionCompl F E) (W t) =
        TopCat.restrictPreimagePairMap (projHom F E) (zeroSectionCompl F E) (W s) :=
      thomPairOverMap_comp_restrictPreimagePairMap F E hst
    have hproj : TopPair.Hom.fst (thomPairOverMap F E hst) ≫ πW t =
        πW s ≫ TopCat.ofHom (ContinuousMap.inclusion hst) :=
      TopCat.ext fun v ↦ Subtype.ext
        (congrArg TotalSpace.proj (congrArg Subtype.val (thomPairOverMap_fst_apply F E hst v)))
    rw [Category.assoc, ← Functor.map_comp, ← hproj, Functor.map_comp, ← Category.assoc,
      ← Category.assoc, ← hcomp, TopPair.singularCohomologyMap_comp_apply,
      TopPair.singularCap_naturality]
  let α : thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor (ModuleCat.of K K) m ≅
      baseFiniteTrivializingUnionDiagram F E ⋙
        (singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K) :=
    NatIso.ofComponents
      (fun s ↦ eqToIso (hObjEq s) ≪≫ @asIso _ _ _ _ (Φ s) (hΦiso s))
      fun {s t} f ↦ by
        dsimp only [Functor.comp_obj, Functor.comp_map]
        simp only [thomPairFiniteTrivializingUnionDiagram_map, TopPair.singularHomologyFunctor_map,
          Iso.trans_hom, eqToIso.hom, Category.assoc, TopPair.singularHomologyMap_comp,
          TopPair.singularHomologyMap_eqToHom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        exact congrArg (eqToHom (hObjEq s) ≫ ·) (hΦnat f)
  let P₁ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) m
  let P₂ := isColimitSingularHomologyBaseFiniteTrivializingUnion (B := B) (F := F) (E := E) K p
  have hcolim : eqToHom hPtEq ≫ homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u =
      (P₁.coconePointsIsoOfNatIso P₂ α).hom := by
    refine P₁.hom_ext fun s ↦ ?_
    rw [P₁.comp_coconePointsIsoOfNatIso_hom P₂ α s,
      singularHomologyFunctor_mapCocone_thomPairFiniteTrivializingUnionCocone_ι_app_assoc]
    dsimp only [α, NatIso.ofComponents_hom_app, Iso.trans_hom, eqToIso.hom,
      Functor.mapCocone_ι_app, baseFiniteTrivializingUnionCocone]
    change eqToHom (hObjEq s) ≫ TopPair.singularHomologyMap _ (ModuleCat.of K K) m ≫
        homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u =
      eqToHom (hObjEq s) ≫ Φ s ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    dsimp only [Φ]
    rw [homologyThomMap_apply, Category.assoc]
    congr 1
    have hproj : TopPair.Hom.fst (thomPairOverMap F E (subset_univ (W s)) ≫
            (thomPairOverUnivIso F E).hom) ≫ thomPairProj F E =
        πW s ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := by
      refine TopCat.ext fun v ↦ ?_
      let v' : ↥(π F E ⁻¹' W s) := v
      change (thomPairProj F E) (TopPair.Hom.fst (thomPairOverUnivIso F E).hom
          (TopPair.Hom.fst (thomPairOverMap F E (subset_univ (W s))) v')) = v'.1.proj
      rw [thomPairOverMap_fst_apply, thomPairOverUnivIso_hom_fst_apply, thomPairProj_apply]
    have hcomp : thomPairOverMap F E (subset_univ (W s)) ≫ (thomPairOverUnivIso F E).hom =
        TopCat.restrictPreimagePairMap (projHom F E) (zeroSectionCompl F E) (W s) := by
      rw [thomPairOverUnivIso_hom]
      exact thomPairOverMap_comp_restrictPreimagePairMap F E (subset_univ (W s))
    rw [← Functor.map_comp, ← hproj, Functor.map_comp, ← Category.assoc, ← Category.assoc,
      ← hcomp, TopPair.singularCap_naturality]
  have : IsIso
      (eqToHom hPtEq ≫ homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
    rw [hcolim]
    exact (P₁.coconePointsIsoOfNatIso P₂ α).isIso_hom
  exact IsIso.of_isIso_comp_left (eqToHom hPtEq) _

/-- **Global chain-level Thom quasi-isomorphism**: for any cocycle `ζ` representing a Thom class of
a real vector bundle `E → B`, the cap-and-pushforward chain map
`C_•(E, E₀; K) ⟶ C_{• - r}(B; K)` is a quasi-isomorphism. -/
private theorem quasiIso_pullbackCapChainMap_thomPair
    {ζ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).cycles (finrank ℝ F)}
    (hu : IsThomClass F E (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).homologyπ (finrank ℝ F) ζ)) :
    QuasiIso ((thomPair F E).pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K))
      (thomPairProj F E) ζ) := by
  have := (isThomClass_iff.1 hu).1
  rw [quasiIso_iff]
  intro m
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hm : finrank ℝ F ≤ m
  · let p := m - finrank ℝ F
    have h : finrank ℝ F + p = m := by omega
    have hIso := isIso_homologyThomMap_self h hu
    rw [homologyThomMap_apply] at hIso
    exact (TopPair.isIso_homologyMap_pullbackCapChainMap_iff K (thomPair F E)
      (𝟙_ (ModuleCat.{w} K)) (thomPairProj F E) h ζ).2 hIso
  · exact TopPair.isIso_homologyMap_pullbackCapChainMap_lt K (thomPair F E)
      (𝟙_ (ModuleCat.{w} K)) (thomPairProj F E) (by omega) ζ
      (isZero_singularHomology_thomPair (F := F) (E := E) (ModuleCat.of K K) (by omega))

end Colimit

end Helpers

/-! ### The Thom isomorphism theorem in cohomology and homology -/

section MainTheorems

variable {B : Type w} [TopologicalSpace B] (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K]

/-- **The Thom isomorphism theorem in cohomology.** For a real vector bundle `E → B` of finite
rank `r = finrank ℝ F` over an arbitrary base `B`, a commutative ring `K`, a Thom class
`u ∈ Hʳ(E, E₀; K)`, and any `K`-module `M`, the Thom map `a ↦ π^*a ⌣ u` is a bijection
from `Hᵖ(B; M)` to `Hᵐ(E, E₀; M)` for all `p + r = m`. -/
theorem bijective_thomMap (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  rw [thomMap_def]
  obtain ⟨ζ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ (finrank ℝ F) u
  have := quasiIso_pullbackCapChainMap_thomPair hu
  exact TopPair.bijective_pullbackCup_of_quasiIso_pullbackCapChainMap (thomPair F E)
    (thomPairProj F E) ζ M h

/-- **The cohomology Thom isomorphism**: for a Thom class `u ∈ Hʳ(E, E₀; K)` of a real vector
bundle `E → B` of rank `r = finrank ℝ F` and any `K`-module `M`, the `K`-linear isomorphism
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` given by `a ↦ π^*a ⌣ u`, for `p + r = m`. -/
def thomEquiv (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u) (bijective_thomMap F E M h hu)

@[simp]
theorem thomEquiv_apply (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquiv F E M h hu a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

@[simp]
theorem thomEquiv_symm_thomMap (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (thomEquiv F E M h hu).symm (thomMap F E M (finrank ℝ F) p m h u a) = a :=
  (thomEquiv F E M h hu).symm_apply_apply a

@[simp]
theorem thomMap_thomEquiv_symm (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (y : (thomPair F E).singularCohomology (ModuleCat.of K K) K M m) :
    thomMap F E M (finrank ℝ F) p m h u ((thomEquiv F E M h hu).symm y) = y :=
  (thomEquiv F E M h hu).apply_symm_apply y

/-- The cohomology Thom isomorphism sends `1 ∈ H⁰(B; K)` to the Thom class `u`. -/
theorem thomEquiv_one (h : 0 + finrank ℝ F = finrank ℝ F)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    thomEquiv F E (ModuleCat.of K K) h hu
        (((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K
          (ModuleCat.of K K)).homologyπ 0
          ((TopCat.of B).constSingularCocycle K (𝟙 (ModuleCat.of K K)))) = u :=
  thomMap_one F E h u

/-- **Naturality of the cohomology Thom isomorphism** under maps of Thom pairs covering maps of
bases. -/
theorem thomEquiv_naturality {B' : Type w} [TopologicalSpace B'] {E' : B' → Type w}
    [TopologicalSpace (TotalSpace F E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F E'] [VectorBundle ℝ F E']
    (M : ModuleCat.{w} K) (φ : thomPair F E' ⟶ thomPair F E) (g : TopCat.of B' ⟶ TopCat.of B)
    (hφ : TopPair.Hom.fst φ ≫ thomPairProj F E = thomPairProj F E' ≫ g)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (hu' : IsThomClass F E' (TopPair.singularCohomologyMap φ (finrank ℝ F) u))
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquiv F E' M h hu' (TopCat.singularCohomologyMap g p a) =
      TopPair.singularCohomologyMap φ m (thomEquiv F E M h hu a) :=
  thomMap_naturality F E φ g hφ h u a

/-- **Naturality of the cohomology Thom isomorphism under pullbacks** along continuous maps
`f : B' → B`. -/
theorem thomEquiv_pullback {B' : Type w} [TopologicalSpace B'] (f : C(B', B))
    (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquiv F ((⇑f) *ᵖ E) M h (hu.pullback f)
        (TopCat.singularCohomologyMap (TopCat.ofHom f) p a) =
      TopPair.singularCohomologyMap (pullbackThomPairMap F E f) m (thomEquiv F E M h hu a) :=
  thomMap_pullback F E f h u a

/-- **The cohomology Thom isomorphism is linear over the cohomology of the base**: for
`a ∈ H^q(B; K)` and `b ∈ Hᵖ(B; M)`, `Φ_u(a ⌣ b) = π^*a ⌣ Φ_u(b)`. -/
theorem thomEquiv_singularCup (M : ModuleCat.{w} K) {p q r m s : ℕ}
    (h : p + finrank ℝ F = m) (hqp : q + p = r) (hrn : r + finrank ℝ F = s) (hqm : q + m = s)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) q)
    (b : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquiv F E M hrn hu ((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv
        (λ_ M).hom q p r hqp a b) =
      (thomPair F E).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q m s hqm
        (TopCat.singularCohomologyMap (thomPairProj F E) q a) (thomEquiv F E M h hu b) :=
  thomMap_singularCup F E h hqp hrn hqm u a b

/-- **The Thom isomorphism theorem in homology.** For a real vector bundle `E → B` of finite rank
`r = finrank ℝ F` over an arbitrary base `B`, a commutative ring `K`, a Thom class
`u ∈ Hʳ(E, E₀; K)`, and any `K`-module `A`, the homology Thom map `x ↦ π_*(x ⌢ u)` is an
isomorphism `Hₘ(E, E₀; A) ⟶ Hₚ(B; A)` in `ModuleCat K` for all `r + p = m`. -/
theorem isIso_homologyThomMap (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    IsIso (homologyThomMap F E A (finrank ℝ F) p m h u) := by
  rw [homologyThomMap_apply]
  obtain ⟨ζ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ (finrank ℝ F) u
  have : Module.Projective K (𝟙_ (ModuleCat.{w} K)) := inferInstanceAs (Module.Projective K K)
  have : Projective (𝟙_ (ModuleCat.{w} K)) :=
    ModuleCat.projective_of_categoryTheory_projective (𝟙_ (ModuleCat.{w} K))
  have := quasiIso_pullbackCapChainMap_thomPair hu
  exact TopPair.isIso_singularCap_comp_map_of_quasiIso_self K (thomPair F E) A
    (thomPairProj F E) h ζ

/-- The underlying `K`-linear map of the homology Thom map of a Thom class is bijective for every
`K`-module `A` and every `finrank ℝ F + p = m`. -/
theorem bijective_homologyThomMap (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (homologyThomMap F E A (finrank ℝ F) p m h u).hom :=
  (ConcreteCategory.isIso_iff_bijective _).1 (isIso_homologyThomMap F E A h hu)

/-- **The homology Thom isomorphism**: for a Thom class `u ∈ Hʳ(E, E₀; K)` of a real vector
bundle `E → B` of rank `r = finrank ℝ F` and any `K`-module `A`, the isomorphism
`Hₘ(E, E₀; A) ≅ Hₚ(B; A)` in `ModuleCat K` given by `x ↦ π_*(x ⌢ u)` for `r + p = m`. -/
def homologyThomIso (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (thomPair F E).singularHomology A m ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj (TopCat.of B) :=
  @asIso _ _ _ _ (homologyThomMap F E A (finrank ℝ F) p m h u)
    (isIso_homologyThomMap F E A h hu)

@[simp]
theorem homologyThomIso_hom (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (homologyThomIso F E A h hu).hom = homologyThomMap F E A (finrank ℝ F) p m h u :=
  (rfl)

/-- **Naturality of the homology Thom isomorphism** under maps of Thom pairs covering maps of
bases. -/
theorem homologyThomIso_hom_naturality {B' : Type w} [TopologicalSpace B'] {E' : B' → Type w}
    [TopologicalSpace (TotalSpace F E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F E'] [VectorBundle ℝ F E']
    (A : ModuleCat.{w} K) (φ : thomPair F E' ⟶ thomPair F E) (g : TopCat.of B' ⟶ TopCat.of B)
    (hφ : TopPair.Hom.fst φ ≫ thomPairProj F E = thomPairProj F E' ≫ g)
    {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (hu' : IsThomClass F E' (TopPair.singularCohomologyMap φ (finrank ℝ F) u)) :
    (homologyThomIso F E' A h hu').hom ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map g =
      TopPair.singularHomologyMap φ A m ≫ (homologyThomIso F E A h hu).hom :=
  homologyThomMap_naturality F E φ g hφ h u

/-- **Naturality of the homology Thom isomorphism under pullbacks** along continuous maps
`f : B' → B`. -/
theorem homologyThomIso_hom_pullback {B' : Type w} [TopologicalSpace B'] (f : C(B', B))
    (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (homologyThomIso F ((⇑f) *ᵖ E) A h (hu.pullback f)).hom ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map (TopCat.ofHom f) =
      TopPair.singularHomologyMap (pullbackThomPairMap F E f) A m ≫
        (homologyThomIso F E A h hu).hom :=
  homologyThomMap_pullback F E f h u

end MainTheorems

/-! ### Oriented bundles -/

namespace VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type*} [Fintype ι]
  {K : Type w} [CommRing K]

/-- **Cohomology Thom isomorphism of an oriented vector bundle** normalized by a model orientation
`ω` and a generator `g` of `Hʳ(F, F ∖ {0}; K)`. -/
theorem bijective_thomMap_thomClassOfModel (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (M : ModuleCat.{w} K) {p m : ℕ}
    (h : p + finrank ℝ F = m) :
    Function.Bijective
      (thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g)) :=
  bijective_thomMap F E M h (o.isThomClass_thomClassOfModel hι ω hg)

/-- **The cohomology Thom isomorphism of an oriented vector bundle**, as a `K`-linear equivalence
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` for `p + finrank ℝ F = m`. -/
def thomEquivOfModel (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (M : ModuleCat.{w} K) {p m : ℕ}
    (h : p + finrank ℝ F = m) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  thomEquiv F E M h (o.isThomClass_thomClassOfModel hι ω hg)

@[simp]
theorem thomEquivOfModel_apply (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (M : ModuleCat.{w} K) {p m : ℕ}
    (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    o.thomEquivOfModel hι ω hg M h a =
      thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g) a :=
  (rfl)

/-- **Homology Thom isomorphism of an oriented vector bundle** normalized by a model orientation
`ω` and a generator `g` of `Hʳ(F, F ∖ {0}; K)`. -/
theorem isIso_homologyThomMap_thomClassOfModel (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (A : ModuleCat.{w} K) {p m : ℕ}
    (h : finrank ℝ F + p = m) :
    IsIso (homologyThomMap F E A (finrank ℝ F) p m h (o.thomClassOfModel hι ω g)) :=
  isIso_homologyThomMap F E A h (o.isThomClass_thomClassOfModel hι ω hg)

/-- **The homology Thom isomorphism of an oriented vector bundle**, as an isomorphism
`Hₘ(E, E₀; A) ≅ Hₚ(B; A)` in `ModuleCat K` for `finrank ℝ F + p = m`. -/
def homologyThomIsoOfModel (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (A : ModuleCat.{w} K) {p m : ℕ}
    (h : finrank ℝ F + p = m) :
    (thomPair F E).singularHomology A m ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj (TopCat.of B) :=
  homologyThomIso F E A h (o.isThomClass_thomClassOfModel hι ω hg)

@[simp]
theorem homologyThomIsoOfModel_hom (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (A : ModuleCat.{w} K) {p m : ℕ}
    (h : finrank ℝ F + p = m) :
    (o.homologyThomIsoOfModel hι ω hg A h).hom =
      homologyThomMap F E A (finrank ℝ F) p m h (o.thomClassOfModel hι ω g) :=
  (rfl)

end VectorBundleOrientation

end TauCeti
