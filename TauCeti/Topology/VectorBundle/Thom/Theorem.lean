/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Homology
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import TauCeti.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.Algebra.Homology.Embedding.LinearYoneda
import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.ThomMap
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing
import TauCeti.CategoryTheory.Injective.Basic

/-!
# The Thom isomorphism theorem

Let `E → B` be a real vector bundle of finite rank `r = finrank ℝ F` over an arbitrary topological
space `B`, with Thom pair `(E, E₀)` (`TauCeti.thomPair`) and projection `π : E ⟶ B`
(`TauCeti.thomPairProj`). Let `K` be a commutative ring and `u ∈ Hʳ(E, E₀; K)` a Thom class
(`TauCeti.IsThomClass F E u`), meaning that `u` restricts to a generator of
`Hʳ(E_b, E_b ∖ {0}; K) ≅ K` on every fibre.

This file proves the **Thom isomorphism theorem** in both singular cohomology and singular homology
over an arbitrary base `B`, for all finite ranks `r ≥ 0` and all coefficient `K`-modules `M` and
`A`:

* **Cohomology** (`TauCeti.IsThomClass.bijective_thomMap`, `TauCeti.IsThomClass.thomEquiv`):
  `Φ_u : Hᵖ(B; M) ≃ₗ[K] Hᵖ⁺ʳ(E, E₀; M)`, `a ↦ π^* a ⌣ u`.
* **Homology** (`TauCeti.IsThomClass.isIso_homologyThomMap`, `TauCeti.IsThomClass.homologyThomIso`):
  `Φ_u : Hᵣ₊ₚ(E, E₀; A) ≅ Hₚ(B; A)`, `x ↦ π_*(x ⌢ u)`.

In particular, combined with `TauCeti.VectorBundleOrientation.thomClassOfModel` and
`TauCeti.existsUnique_isThomClass_of_subsingleton_units`, every oriented real vector bundle admits
a Thom isomorphism over every commutative ring `K` (including integral coefficients), and every
real vector bundle admits a Thom isomorphism over any ring with a single unit such as `ZMod 2`.

## Proof strategy

1. **Finite unions of trivializing open sets (cohomology, all `M`).** Over an open subset `W` of a
   linear trivialization's base set, `Bundle.Trivialization.thomPairOverIso` reduces the claim to
   the product bundle `W × F`, where `TauCeti.bijective_pullbackCup_prodThomPair` gives bijectivity
   for every `K`-module `M` and every degree `p`. Finite induction with the Mayer–Vietoris step
   `TopCat.bijective_pullbackCupRestrict_union` extends this to finite unions of trivializing open
   sets.
2. **Finite unions of trivializing open sets (homology with `K` coefficients).** Under the
   Kronecker pairing into any injective `K`-module `M`, the homology Thom map over `W` transposes
   to `(-1)^(r p)` times the cohomology Thom map over `W` with coefficients in `M`. Since
   `ModuleCat K` has enough injectives and the Kronecker map is bijective for injective `M`,
   `TauCeti.isIso_of_bijective_precomp_injective` shows that the homology Thom map with `K`
   coefficients is an isomorphism over every finite union of trivializing open sets.
3. **Arbitrary base `B` (homology with `K` coefficients).** Passing to the filtered colimit over
   all finite unions of the preferred trivializing open sets
   (`TauCeti.isColimitMapCoconeSingularHomology` and
   `TauCeti.isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion`) gives the homology
   Thom isomorphism with `K` coefficients over an arbitrary base `B`.
4. **Chain-level Thom quasi-isomorphism (arbitrary `B`, all `M` and `A`).** Representing `u` by a
   relative cocycle `φ`, the signed cap-and-project chain map
   `C(E, E₀; K) ⟶ C(B; K).extend (n ↦ n + r)` is a quasi-isomorphism between `ℕ`-graded chain
   complexes of projective `K`-modules (vanishing below `r`, and agreeing with `(-1)^(r p)` times
   the homology Thom map in degrees `≥ r`). Applying `Hom(-, M)`
   (`ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective`) recovers the cohomology Thom map
   `TauCeti.thomMap` for every `K`-module `M`, proving bijectivity in full generality. Applying
   `A ⊗ -` to the resulting chain homotopy equivalence and comparing via
   `SSetPair.chainComplexPairing (ρ_ A).hom` proves the homology Thom isomorphism for every
   `K`-module `A`.

## Main definitions and results

* `TauCeti.IsThomClass.bijective_thomMap`: bijectivity of `TauCeti.thomMap` for any Thom class `u`,
  any base `B`, any coefficient module `M`, and any degree `p`.
* `TauCeti.IsThomClass.thomEquiv`: the cohomology Thom isomorphism `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`,
  with `thomEquiv_apply`, `thomEquiv_one`, `thomEquiv_symm_self`, `thomEquiv_singularCup`,
  `thomEquiv_naturality`, and `thomEquiv_symm_naturality`.
* `TauCeti.IsThomClass.isIso_homologyThomMap` and `TauCeti.IsThomClass.bijective_homologyThomMap`:
  the homology Thom map `TauCeti.homologyThomMap` is an isomorphism for any Thom class `u`, any
  base `B`, any coefficient module `A`, and any degree `p`.
* `TauCeti.IsThomClass.homologyThomIso`: the homology Thom isomorphism `Hₘ(E, E₀; A) ≅ Hₚ(B; A)`,
  with `homologyThomIso_hom` and `homologyThomIso_naturality`.
* `TauCeti.VectorBundleOrientation.bijective_thomMap_thomClassOfModel` and
  `TauCeti.VectorBundleOrientation.isIso_homologyThomMap_thomClassOfModel`: specializations to the
  Thom class of an oriented real vector bundle.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.D, Theorem 4D.10.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7, Theorem 10.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex Set Module

universe w

namespace TauCeti

/-! ### Auxiliary lemmas -/

section Helpers

variable {C : Type*} [Category* C] [Preadditive C]

/-- Scaling an isomorphism in a preadditive category by `(-1 : ℤ) ^ k` yields an isomorphism. -/
private theorem isIso_neg_one_pow_zsmul {X Y : C} (k : ℕ) (f : X ⟶ Y) [IsIso f] :
    IsIso (((-1 : ℤ) ^ k) • f) :=
  ⟨⟨((-1 : ℤ) ^ k) • inv f, by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← mul_pow,
      IsIso.hom_inv_id]
    simp, by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← mul_pow,
      IsIso.inv_hom_id]
    simp⟩⟩

/-- Scaling an additive group by `(-1 : ℤ) ^ k` is an involution, hence bijective. -/
private theorem bijective_neg_one_pow_zsmul {V : Type*} [AddCommGroup V] (k : ℕ) :
    Function.Bijective (fun v : V ↦ ((-1 : ℤ) ^ k) • v) := by
  have hinv : Function.LeftInverse (fun v : V ↦ ((-1 : ℤ) ^ k) • v)
      (fun v : V ↦ ((-1 : ℤ) ^ k) • v) := fun v ↦ by
    dsimp only
    rw [← mul_zsmul, ← mul_pow]
    simp
  exact ⟨hinv.injective, hinv.surjective⟩

/-- For a pair `P` and a map `g : P.fst ⟶ Z`, the cap-and-pushforward map on `K`-homology is
adjoint to `P.pullbackCup M g` under the Kronecker pairing into any `K`-module `M`, up to the
sign `(-1)^(n p)`. -/
private theorem singularCap_comp_map_comp_singularKronecker {K : Type w} [CommRing K]
    {P : TopPair.{w}} {Z : TopCat.{w}} (g : P.fst ⟶ Z) (M : ModuleCat.{w} K) {n p m : ℕ}
    (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Z.singularCohomology (ModuleCat.of K K) K M p) :
    (P.singularCap K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom n p m h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map g) ≫
      Z.singularKronecker K p a =
    ((-1 : ℤ) ^ (n * p)) • P.singularKronecker K m (P.pullbackCup M g n p m (by omega) u a) := by
  rw [Category.assoc, ← TopCat.singularKronecker_naturality,
    TopPair.singularCap_comp_singularKronecker, TopPair.pullbackCup_apply,
    TopPair.singularCup_gradedComm K P (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u' := (λ_ (ModuleCat.of K K)).inv) (μ' := (λ_ M).hom) (μ := (ρ_ M).hom) ?_ ?_ (by omega),
    map_zsmul, mul_comm]
  · rfl
  · rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, ← unitors_inv_equal]
    rfl
  · exact braiding_leftUnitor M

/-- If `a ↦ g^* a ⌣ u` is bijective for every coefficient `K`-module `M`, then `x ↦ g_*(x ⌢ u)` is
an isomorphism on `K`-homology. -/
private theorem isIso_singularCap_comp_map_of_bijective_pullbackCup {K : Type w} [CommRing K]
    {P : TopPair.{w}} {Z : TopCat.{w}} (g : P.fst ⟶ Z) {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hbij : ∀ M : ModuleCat.{w} K, Function.Bijective (P.pullbackCup M g n p m (by omega) u)) :
    IsIso (P.singularCap K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom n p m h u ≫
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map g) := by
  refine isIso_of_bijective_precomp_injective _ fun M _ ↦ ?_
  have hcomp :
      (fun ψ : ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj Z ⟶ M ↦
          (P.singularCap K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom n p m h u ≫
            ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map g) ≫ ψ) ∘
        ⇑(Z.singularKronecker (R := ModuleCat.of K K) (M := M) K p) =
      (fun φ : P.singularHomology (ModuleCat.of K K) m ⟶ M ↦ ((-1 : ℤ) ^ (n * p)) • φ) ∘
        ⇑(P.singularKronecker (R := ModuleCat.of K K) (M := M) K m) ∘
        ⇑(P.pullbackCup M g n p m (by omega) u) := by
    funext a
    exact singularCap_comp_map_comp_singularKronecker g M h u a
  have hZ : Function.Bijective (Z.singularKronecker (R := ModuleCat.of K K) (M := M) K p) := by
    rw [TopCat.singularKronecker_def]
    exact ChainComplex.kronecker_bijective p
  have hP : Function.Bijective (P.singularKronecker (R := ModuleCat.of K K) (M := M) K m) := by
    rw [TopPair.singularKronecker_def]
    exact ChainComplex.kronecker_bijective m
  have hrhs : Function.Bijective
      ((fun φ : P.singularHomology (ModuleCat.of K K) m ⟶ M ↦ ((-1 : ℤ) ^ (n * p)) • φ) ∘
        ⇑(P.singularKronecker (R := ModuleCat.of K K) (M := M) K m) ∘
        ⇑(P.pullbackCup M g n p m (by omega) u)) :=
    (bijective_neg_one_pow_zsmul (n * p)).comp (hP.comp (hbij M))
  exact (Function.Bijective.of_comp_iff _ hZ).1 (hcomp ▸ hrhs)

end Helpers

/-! ### Step 1: Cohomology over finite unions of trivializing open sets -/

section FiniteTrivializingUnion

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] {K : Type w} [CommRing K]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] in
/-- The restriction of the bundle projection `π : E ⟶ B` to the ambient space of `thomPairOver`. -/
private def thomPairOverProj (W : Set B) : (thomPairOver F E W).fst ⟶ TopCat.of W :=
  TopCat.ofHom ((TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩).hom.restrictPreimage W)

/-- Over a subset `W` of the base set of a linear trivialization, the restricted pullback-cup map
of a Thom class is bijective in every degree and for every coefficient module. -/
private theorem bijective_pullbackCupRestrict_of_subset_baseSet
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (TopCat.pullbackCupRestrict
      (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) M W
      (finrank ℝ F) p m h u) := by
  rw [TopCat.pullbackCupRestrict_apply]
  let φ := e.thomPairOverIso ℝ hW
  let uW : (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F) :=
    TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
      (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W)
      (finrank ℝ F) u
  let u' := TopPair.singularCohomologyMap φ.inv (finrank ℝ F) uW
  have huW : TopPair.singularCohomologyMap φ.hom (finrank ℝ F) u' = uW := by
    rw [← TopPair.singularCohomologyMap_comp_apply, Iso.hom_inv_id,
      TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
  have htri : TopPair.Hom.fst φ.hom ≫ prodThomPairProj W F =
      thomPairOverProj (F := F) (E := E) W ≫ 𝟙 (TopCat.of W) := by
    refine TopCat.ext fun v ↦ ?_
    rw [Category.comp_id, ConcreteCategory.comp_apply, e.thomPairOverIso_hom_fst_apply ℝ hW v,
      prodThomPairProj_apply]
    rfl
  change Function.Bijective ((thomPairOver F E W).pullbackCup M
    (thomPairOverProj (F := F) (E := E) W) (finrank ℝ F) p m h uW)
  rw [← huW]
  refine (TopPair.bijective_pullbackCup_iff_of_isIso φ.hom (𝟙 (TopCat.of W)) htri h u').2 ?_
  refine bijective_pullbackCup_prodThomPair M (fun b ↦ ?_) h
  have hfib : prodThomPairFiberMap F b ≫ φ.inv =
      (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.inv ≫
        fiberThomPairOverMap F E b.2 := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
      e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW b.2]
  have hcomp : prodThomPairFiberMap F b ≫ φ.inv ≫
      TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W =
      (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.inv ≫
        fiberThomPairMap F E b.1 := by
    rw [← Category.assoc, hfib, Category.assoc, fiberThomPairOverMap_comp_restrictPreimagePairMap]
  have hgen : TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u' =
      TopPair.singularCohomologyMap
        (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.inv (finrank ℝ F)
        (TopPair.singularCohomologyMap (fiberThomPairMap F E b.1) (finrank ℝ F) u) := by
    dsimp only [u', uW]
    rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
      Category.assoc, hcomp, TopPair.singularCohomologyMap_comp_apply]
  rw [hgen]
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  have hx : TopPair.singularCohomologyMap
      (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.hom (finrank ℝ F) x ∈
      Submodule.span K
        {TopPair.singularCohomologyMap (fiberThomPairMap F E b.1) (finrank ℝ F) u} := by
    rw [(isThomClass_iff.1 hu).2 b.1]
    trivial
  rw [Submodule.mem_span_singleton] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, ?_⟩
  have hinv := congrArg (TopPair.singularCohomologyMap
    (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.inv (finrank ℝ F)) hc
  have hinv' : TopPair.singularCohomologyMap
      (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.inv (finrank ℝ F)
      (TopPair.singularCohomologyMap
        (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.hom (finrank ℝ F) x) = x := by
    rw [← TopPair.singularCohomologyMap_comp_apply, Iso.inv_hom_id,
      TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
  rw [map_smul, hinv'] at hinv
  exact hinv

omit [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] in
/-- Over the empty subset of the base, the restricted pullback-cup map is bijective between zero
modules. -/
private theorem bijective_pullbackCupRestrict_empty
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (TopCat.pullbackCupRestrict
      (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) M (∅ : Set B)
      (finrank ℝ F) p m h u) := by
  have h1 : IsZero ((TopCat.of (∅ : Set B)).singularCohomology (ModuleCat.of K K) K M p) :=
    isZero_singularCohomology_of_isEmpty (ModuleCat.of K K) K M (TopCat.of (∅ : Set B)) p
  have h2 : IsZero ((thomPairOver F E ∅).singularCohomology (ModuleCat.of K K) K M m) :=
    TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of K K) M m
      fun j _ ↦ isZero_singularHomology_thomPairOver_empty (F := F) (E := E) (ModuleCat.of K K) j
  have : Subsingleton ((TopCat.of (∅ : Set B)).singularCohomology (ModuleCat.of K K) K M p) :=
    ModuleCat.isZero_iff_subsingleton.1 h1
  have : Subsingleton ((thomPairOver F E ∅).singularCohomology (ModuleCat.of K K) K M m) :=
    ModuleCat.isZero_iff_subsingleton.1 h2
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- Over any finite union of trivializing open sets, the restricted pullback-cup map of a Thom
class is bijective in every degree and for every coefficient module. -/
private theorem bijective_pullbackCupRestrict_biUnion {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) :
    ∀ (p m : ℕ) (h : p + finrank ℝ F = m),
      Function.Bijective (TopCat.pullbackCupRestrict
        (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) M
        (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro p m h
    rw [show (⋃ i ∈ (∅ : Finset ι), W i) = ∅ by simp]
    exact bijective_pullbackCupRestrict_empty u M h
  | insert a s _ ih =>
    intro p m h
    rw [Finset.set_biUnion_insert]
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    refine TopCat.bijective_pullbackCupRestrict_union
      (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) M
      (hWo a (Finset.mem_insert_self a s))
      (isOpen_biUnion fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi)) u
      (fun q _ ↦ bijective_pullbackCupRestrict_of_subset_baseSet e he hu M rfl)
      (fun q _ ↦ ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi)) q (q + finrank ℝ F) rfl)
      (fun q _ ↦ bijective_pullbackCupRestrict_of_subset_baseSet e
        (inter_subset_left.trans he) hu M rfl)
      (fun j hj ↦ TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of K K)
        M j fun k hk ↦ e.isZero_singularHomology_thomPairOver (inter_subset_left.trans he)
          (ModuleCat.of K K) (by omega))
      h

end FiniteTrivializingUnion

/-! ### Step 2 & 3: Homology Thom isomorphism with `K` coefficients over an arbitrary base -/

section HomologySelf

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {K : Type w} [CommRing K]

/-- The homology Thom map restricted over a subset `W` of the base, with `K` coefficients. -/
private def homologyThomMapOver (W : Set B) {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    (thomPairOver F E W).singularHomology (ModuleCat.of K K) m ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj (TopCat.of W) :=
  (thomPairOver F E W).singularCap K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom n p m h
      (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n u) ≫
    ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
      (thomPairOverProj (F := F) (E := E) W)

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- The restricted homology Thom map is natural with respect to inclusions `W ⊆ W'` of subsets of
the base. -/
private theorem homologyThomMapOver_naturality {W W' : Set B} (hWW' : W ⊆ W') {n p m : ℕ}
    (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    TopPair.singularHomologyMap (thomPairOverMap F E hWW') (ModuleCat.of K K) m ≫
        homologyThomMapOver W' h u =
      homologyThomMapOver W h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.inclusion hWW')) := by
  dsimp only [homologyThomMapOver]
  have hproj : thomPairOverProj (F := F) (E := E) W ≫ TopCat.ofHom (ContinuousMap.inclusion hWW') =
      TopPair.Hom.fst (thomPairOverMap F E hWW') ≫ thomPairOverProj (F := F) (E := E) W' := by
    rw [thomPairOverMap_fst]
    exact TopCat.ext fun _ ↦ rfl
  rw [Category.assoc, ← Functor.map_comp, hproj, Functor.map_comp, ← Category.assoc,
    ← TopPair.singularCap_naturality, ← TopPair.singularCohomologyMap_comp_apply,
    thomPairOverMap_comp_restrictPreimagePairMap, Category.assoc]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- The homology Thom map over the whole base restricts to `homologyThomMapOver` over any subset
`W` of the base. -/
private theorem homologyThomMap_restrict (W : Set B) {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    TopPair.singularHomologyMap (thomPairOverMap F E (subset_univ W) ≫
          (thomPairOverUnivIso F E).hom) (ModuleCat.of K K) m ≫
        homologyThomMap F E (ModuleCat.of K K) n p m h u =
      homologyThomMapOver W h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) := by
  have hmap : thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom =
      TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W := by
    rw [thomPairOverUnivIso_hom]
    exact thomPairOverMap_comp_restrictPreimagePairMap F E (subset_univ W)
  have hproj : thomPairOverProj (F := F) (E := E) W ≫
        TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ =
      TopPair.Hom.fst (TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) ≫
        thomPairProj F E := by
    refine TopCat.ext fun v ↦ ?_
    have hv : (TopPair.Hom.fst (TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W)) v = v.1 :=
      TopCat.restrictPreimagePairMap_fst_apply _ _ _ v
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hv, thomPairProj_apply]
    rfl
  rw [hmap, homologyThomMap_apply, homologyThomMapOver, Category.assoc, ← Functor.map_comp, hproj,
    Functor.map_comp, ← Category.assoc, ← TopPair.singularCap_naturality, Category.assoc]

/-- Over a finite union of the preferred trivializing open sets, `homologyThomMapOver` is an
isomorphism. -/
private theorem isIso_homologyThomMapOver_finiteTrivializingUnion (s : Finset B) {p m : ℕ}
    (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    IsIso (homologyThomMapOver (F := F) (E := E)
      (⋃ b ∈ s, (trivializationAt F E b).baseSet) h u) :=
  isIso_singularCap_comp_map_of_bijective_pullbackCup _ h _ fun M ↦ by
    have hbij := bijective_pullbackCupRestrict_biUnion s
      (fun b _ ↦ (trivializationAt F E b).open_baseSet)
      (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩)
      hu M p m (by omega)
    rw [TopCat.pullbackCupRestrict_apply] at hbij
    exact hbij

variable (F E) in
/-- The finite unions of the preferred trivializing open sets, as a diagram of subspaces of `B`. -/
private def baseFiniteTrivializingUnionDiagram : Finset B ⥤ TopCat.{w} where
  obj s := TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet)
  map f := TopCat.ofHom (ContinuousMap.inclusion (biUnion_subset_biUnion_left f.le))

variable (F E) in
/-- The inclusions of the finite unions of the preferred trivializing open sets into `B`. -/
private def baseFiniteTrivializingUnionCocone :
    Cocone (baseFiniteTrivializingUnionDiagram (B := B) F E) where
  pt := TopCat.of B
  ι := { app _ := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ }

variable (F E K) in
/-- The homology of the base in any degree `p` is the filtered colimit of the homologies of the
finite unions of the preferred trivializing open sets. -/
private def isColimitSingularHomologyBaseFiniteTrivializingUnion (p : ℕ) :
    IsColimit (((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).mapCocone
      (baseFiniteTrivializingUnionCocone (B := B) F E)) :=
  isColimitMapCoconeSingularHomology (ModuleCat.of K K) p
    (baseFiniteTrivializingUnionCocone F E) (fun _ ↦ Topology.IsEmbedding.subtypeVal)
    fun L hL ↦ by
      obtain ⟨s, hs⟩ := hL.elim_finite_subcover _
        (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
          mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
      exact ⟨s, fun b hb ↦ ⟨⟨b, hs hb⟩, rfl⟩⟩

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
private theorem singularHomology_thomPairOver_finiteTrivializingUnion_eq (m : ℕ) (s : Finset B) :
    (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology
        (ModuleCat.of K K) m =
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
        ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) := by
  rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
private theorem singularHomology_thomPair_eq (m : ℕ) :
    (thomPair F E).singularHomology (ModuleCat.of K K) m =
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
        (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt := by
  rw [thomPairFiniteTrivializingUnionCocone_pt, TopPair.singularHomologyFunctor_obj]

/-- The homology Thom maps over the finite unions of the preferred trivializing open sets form a
natural isomorphism of diagrams. -/
private def thomPairFiniteTrivializingUnionHomologyThomIso {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor (ModuleCat.of K K) m ≅
      baseFiniteTrivializingUnionDiagram F E ⋙
        (singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K) :=
  NatIso.ofComponents
    (fun s ↦
      (eqToIso (singularHomology_thomPairOver_finiteTrivializingUnion_eq (F := F) (E := E)
        (K := K) m s)).symm ≪≫
        @asIso _ _ _ _ (homologyThomMapOver (⋃ b ∈ s, (trivializationAt F E b).baseSet) h u)
          (isIso_homologyThomMapOver_finiteTrivializingUnion s h hu))
    fun {s t} f ↦ by
      have := isIso_homologyThomMapOver_finiteTrivializingUnion s h hu
      have := isIso_homologyThomMapOver_finiteTrivializingUnion t h hu
      have hst : (⋃ b ∈ s, (trivializationAt F E b).baseSet) ⊆
          ⋃ b ∈ t, (trivializationAt F E b).baseSet := fun x hx ↦ by
        simp only [mem_iUnion, exists_prop] at hx ⊢
        obtain ⟨b, hb, hxb⟩ := hx
        exact ⟨b, f.le hb, hxb⟩
      dsimp only [Functor.comp_obj, Functor.comp_map, baseFiniteTrivializingUnionDiagram]
      simp only [thomPairFiniteTrivializingUnionDiagram_map, TopPair.singularHomologyFunctor_map,
        Iso.trans_hom, Iso.symm_hom, eqToIso.inv, asIso_hom, Category.assoc,
        TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      rw [← homologyThomMapOver_naturality hst h u]

/-- **The homology Thom isomorphism with `K` coefficients over an arbitrary base**: passing to the
filtered colimit over finite unions of trivializing open sets shows `homologyThomMap` is an
isomorphism for `A = K`. -/
private theorem isIso_homologyThomMap_self {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    IsIso (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
  let P₁ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) m
  let P₂ := isColimitSingularHomologyBaseFiniteTrivializingUnion F E K p
  let α := thomPairFiniteTrivializingUnionHomologyThomIso h hu
  have hcolim :
      eqToHom (singularHomology_thomPair_eq (F := F) (E := E) (K := K) m).symm ≫
        homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u =
      (P₁.coconePointsIsoOfNatIso P₂ α).hom := by
    refine P₁.hom_ext fun s ↦ ?_
    refine Eq.trans ?_ (P₁.comp_coconePointsIsoOfNatIso_hom P₂ α s).symm
    have hleg := singularHomologyFunctor_mapCocone_thomPairFiniteTrivializingUnionCocone_ι_app_assoc
      (F := F) (E := E) (ModuleCat.of K K) m s
      (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u)
    rw [hleg, homologyThomMap_restrict]
    simp only [α, thomPairFiniteTrivializingUnionHomologyThomIso, NatIso.ofComponents_hom_app,
      Iso.trans_hom, Iso.symm_hom, eqToIso.inv, Functor.mapCocone_ι_app,
      baseFiniteTrivializingUnionCocone, Category.assoc]
    rfl
  have : IsIso (eqToHom (singularHomology_thomPair_eq (F := F) (E := E) (K := K) m).symm ≫
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
    rw [hcolim]
    exact (P₁.coconePointsIsoOfNatIso P₂ α).isIso_hom
  exact IsIso.of_isIso_comp_left
    (eqToHom (singularHomology_thomPair_eq (F := F) (E := E) (K := K) m).symm) _

end HomologySelf

/-! ### Step 4: Chain-level Thom quasi-isomorphism for all coefficient modules -/

section ChainThomMap

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K]

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
/-- View a degree-`r` relative cocycle `φ` directly as a morphism `C_r(E, E₀; K) ⟶ K`. -/
private def cochainCycleHom {r : ℕ}
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).cycles r) :
    ((thomPair F E).singularChainComplex (𝟙_ (ModuleCat.{w} K))).X r ⟶ 𝟙_ (ModuleCat.{w} K) :=
  ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).iCycles r φ

/-- The signed chain-level Thom map `C(E, E₀; A) ⟶ C(B; A).extend (n ↦ n + r)` associated to a
relative cocycle `φ` of degree `r`. In degree `n = p + r`, it is `(-1)^(r p)` times capping with
`φ` followed by pushing forward along `π : E ⟶ B`. -/
private def chainThomMap (A : ModuleCat.{w} K) {r : ℕ}
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).cycles r) :
    (thomPair F E).singularChainComplex A ⟶
      ((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extend
        (ComplexShape.embeddingDownNatAdd r) where
  f n :=
    if h : r ≤ n then
      ((-1 : ℤ) ^ (r * (n - r))) •
        (ChainComplex.capChain K
            ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
            r (n - r) n (by omega)
            (cochainCycleHom (F := F) (E := E) φ) ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) A).f (n - r) ≫
          (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendXIso
            (ComplexShape.embeddingDownNatAdd r)
            (show (ComplexShape.embeddingDownNatAdd r).f (n - r) = n by
              simp [ComplexShape.embeddingDownNatAdd_f]; omega)).inv)
    else 0
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    by_cases hj : r ≤ j
    · have hi : r ≤ i := by omega
      simp only [dite_eq_left_of_eq_true (eq_true hi), dite_eq_left_of_eq_true (eq_true hj)]
      have heq_i : j + 1 = i := hij
      subst heq_i
      set q := j - r
      have hiq : j + 1 - r = q + 1 := by omega
      have hjd : (ComplexShape.embeddingDownNatAdd r).f q = j := by
        simp [ComplexShape.embeddingDownNatAdd_f]; omega
      have hcomm_aux : ∀ (k : ℕ) (_ : k = q + 1) (hkr : r + k = j + 1)
          (hkd : (ComplexShape.embeddingDownNatAdd r).f k = j + 1),
          (((-1 : ℤ) ^ (r * k)) •
              (ChainComplex.capChain K
                  ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
                  ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
                  r k (j + 1) hkr (cochainCycleHom (F := F) (E := E) φ) ≫
                (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) A).f k ≫
                (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendXIso
                  (ComplexShape.embeddingDownNatAdd r) hkd).inv)) ≫
            (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extend
              (ComplexShape.embeddingDownNatAdd r)).d (j + 1) j =
          ((thomPair F E).singularChainComplex A).d (j + 1) j ≫
            (((-1 : ℤ) ^ (r * q)) •
              (ChainComplex.capChain K
                  ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
                  ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
                  r q j (by omega) (cochainCycleHom (F := F) (E := E) φ) ≫
                (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) A).f q ≫
                (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendXIso
                  (ComplexShape.embeddingDownNatAdd r) hjd).inv)) := by
        rintro _ rfl hkr hkd
        rw [← cancel_mono ((((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendXIso
          (ComplexShape.embeddingDownNatAdd r) hjd).hom)]
        simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
        rw [(((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extend_d_eq
          (ComplexShape.embeddingDownNatAdd r) hkd hjd)]
        simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
        rw [((SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) A).comm (q + 1) q)]
        have hcap : ChainComplex.capChain K
              ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
              ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
              r (q + 1) (j + 1) hkr (cochainCycleHom (F := F) (E := E) φ) ≫
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplex A).d (q + 1) q =
          ((-1 : ℤ) ^ r) • (((thomPair F E).singularChainComplex A).d (j + 1) j ≫
            ChainComplex.capChain K
              ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
              ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
              r q j (by omega) (cochainCycleHom (F := F) (E := E) φ)) :=
          ChainComplex.capChain_comp_d_of_cycles (k := K)
            ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
            r q j (by omega) φ
        rw [reassoc_of% hcap, Preadditive.zsmul_comp, smul_smul]
        have hsign : (-1 : ℤ) ^ (r * (q + 1)) * (-1 : ℤ) ^ r = (-1 : ℤ) ^ (r * q) := by
          rw [mul_add, mul_one, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
          simp
        rw [hsign, Category.assoc]
      exact hcomm_aux (j + 1 - r) hiq (by omega)
        (by simp [ComplexShape.embeddingDownNatAdd_f]; omega)
    · exact (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).isZero_extend_X
        (ComplexShape.embeddingDownNatAdd r) j fun p hp ↦ by
          simp only [ComplexShape.embeddingDownNatAdd_f] at hp
          omega).eq_of_tgt _ _

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
/-- Formula for `chainThomMap` in degree `m = r + p`. -/
private lemma chainThomMap_f_eq (A : ModuleCat.{w} K) {r p m : ℕ} (h : r + p = m)
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).cycles r) :
    (chainThomMap (F := F) (E := E) A φ).f m =
      ((-1 : ℤ) ^ (r * p)) •
        (ChainComplex.capChain K
            ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
            r p m h (cochainCycleHom (F := F) (E := E) φ) ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) A).f p ≫
          (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendXIso
            (ComplexShape.embeddingDownNatAdd r)
            (show (ComplexShape.embeddingDownNatAdd r).f p = m by
              simp [ComplexShape.embeddingDownNatAdd_f]; omega)).inv) := by
  have hle : r ≤ m := by omega
  have hsub : m - r = p := by omega
  dsimp only [chainThomMap]
  rw [dite_eq_left_of_eq_true (eq_true hle)]
  subst hsub
  rfl

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
/-- In degree `m = r + p`, `chainThomMap A φ` induces `(-1)^(r p)` times `homologyThomMap` on
homology. -/
private theorem homologyMap_chainThomMap_comp_extendHomologyIso_hom (A : ModuleCat.{w} K)
    {r p m : ℕ} (h : r + p = m)
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).cycles r) :
    homologyMap (chainThomMap (F := F) (E := E) A φ) m ≫
        (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendHomologyIso
          (ComplexShape.embeddingDownNatAdd r)
          (show (ComplexShape.embeddingDownNatAdd r).f p = m by
            simp [ComplexShape.embeddingDownNatAdd_f]; omega)).hom =
      ((-1 : ℤ) ^ (r * p)) •
        homologyThomMap F E A r p m h
          (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
            (ModuleCat.of K K)).homologyπ r φ) := by
  have hp : (ComplexShape.embeddingDownNatAdd r).f p = m := by
    simp [ComplexShape.embeddingDownNatAdd_f]; omega
  refine (cancel_epi (((thomPair F E).singularChainComplex A).homologyπ m)).1 ?_
  have hLHS : ((thomPair F E).singularChainComplex A).homologyπ m ≫
      (homologyMap (chainThomMap (F := F) (E := E) A φ) m ≫
        (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendHomologyIso
          (ComplexShape.embeddingDownNatAdd r) hp).hom) =
      (cyclesMap (chainThomMap (F := F) (E := E) A φ) m ≫
        (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendCyclesIso
          (ComplexShape.embeddingDownNatAdd r) hp).hom) ≫
        ((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).homologyπ p := by
    rw [homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom, Category.assoc]
  have hcap := TopPair.singularCap_homologyπ (thomPair F E) K (λ_ A).inv (λ_ A).hom r p m h φ
  have hRHS : ((thomPair F E).singularChainComplex A).homologyπ m ≫
      (((-1 : ℤ) ^ (r * p)) •
        homologyThomMap F E A r p m h
          (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
            (ModuleCat.of K K)).homologyπ r φ)) =
      (((-1 : ℤ) ^ (r * p)) •
        (ChainComplex.capCycles K ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
          ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom) r p m h φ ≫
        cyclesMap (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) A) p)) ≫
        ((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).homologyπ p := by
    have hstep := (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map (thomPairProj F E))
        hcap).trans (Category.assoc _ _ _)
    have hnat : ((TopCat.toSSet.obj (thomPair F E).fst).chainComplex A).homologyπ p ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map (thomPairProj F E) =
        cyclesMap (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) A) p ≫
          ((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).homologyπ p := by
      rw [TauCeti.singularHomologyFunctor_obj_map, SSet.homologyMap]
      exact homologyπ_naturality _ p
    rw [Preadditive.comp_zsmul, homologyThomMap_apply]
    refine (congrArg (((-1 : ℤ) ^ (r * p)) • ·)
      (hstep.trans (congrArg (_ ≫ ·) hnat))).trans ?_
    simp only [Preadditive.zsmul_comp, Category.assoc]
    rfl
  refine hLHS.trans (Eq.trans ?_ hRHS.symm)
  congr 1
  rw [← cancel_mono (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).iCycles p)]
  simp only [Category.assoc, extendCyclesIso_hom_iCycles, cyclesMap_i_assoc,
    Preadditive.zsmul_comp, cyclesMap_i, ChainComplex.capCycles_i_assoc,
    chainThomMap_f_eq A h φ, Preadditive.comp_zsmul, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Every term of `C(B; K).extend (n ↦ n + r)` is projective. -/
private theorem projective_extend_chainComplex_X (r n : ℕ) :
    Projective ((((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of K K)).extend
      (ComplexShape.embeddingDownNatAdd r)).X n) := by
  by_cases h : r ≤ n
  · have hp : (ComplexShape.embeddingDownNatAdd r).f (n - r) = n := by
      simp [ComplexShape.embeddingDownNatAdd_f]; omega
    exact Projective.of_iso
      ((((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of K K)).extendXIso
        (ComplexShape.embeddingDownNatAdd r) hp).symm) inferInstance
  · have hzero := ((TopCat.toSSet.obj (TopCat.of B)).chainComplex
      (ModuleCat.of K K)).isZero_extend_X (ComplexShape.embeddingDownNatAdd r) n fun p hp ↦ by
        simp only [ComplexShape.embeddingDownNatAdd_f] at hp
        omega
    exact ⟨fun f e _ ↦ ⟨0, hzero.eq_of_src _ _⟩⟩

/-- When `φ` represents a Thom class `u`, the chain-level Thom map with `K` coefficients is a
quasi-isomorphism. -/
private theorem quasiIso_chainThomMap_self [VectorBundle ℝ F E]
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).cycles (finrank ℝ F))
    (hu : IsThomClass F E
      (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
        (ModuleCat.of K K)).homologyπ (finrank ℝ F) φ)) :
    QuasiIso (chainThomMap (F := F) (E := E) (ModuleCat.of K K) φ) := by
  have := (isThomClass_iff.1 hu).1
  refine (quasiIso_iff _).2 fun n ↦ ?_
  by_cases h : finrank ℝ F ≤ n
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    have hp : (ComplexShape.embeddingDownNatAdd (finrank ℝ F)).f (n - finrank ℝ F) = n := by
      simp [ComplexShape.embeddingDownNatAdd_f]; omega
    have hmul := homologyMap_chainThomMap_comp_extendHomologyIso_hom (F := F) (E := E)
      (ModuleCat.of K K) (p := n - finrank ℝ F) (m := n) (by omega) φ
    have hIso : IsIso (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) (n - finrank ℝ F) n
        (by omega) (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
          (ModuleCat.of K K)).homologyπ (finrank ℝ F) φ)) :=
      isIso_homologyThomMap_self (by omega) hu
    have hsc := @isIso_neg_one_pow_zsmul (ModuleCat.{w} K) _ _ _ _
      (finrank ℝ F * (n - finrank ℝ F)) _ hIso
    have : IsIso (homologyMap (chainThomMap (F := F) (E := E) (ModuleCat.of K K) φ) n ≫
        (((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of K K)).extendHomologyIso
          (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) hp).hom) := by
      obtain ⟨⟨g, hg₁, hg₂⟩⟩ := hsc
      exact ⟨⟨g, by rw [hmul]; exact hg₁, by rw [hmul]; exact hg₂⟩⟩
    exact IsIso.of_isIso_comp_right _
      ((((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of K K)).extendHomologyIso
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) hp).hom)
  · rw [quasiIsoAt_iff_exactAt]
    · exact ((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of K K)).extend_exactAt
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) n fun p hp ↦ by
          simp only [ComplexShape.embeddingDownNatAdd_f] at hp
          omega
    · exact ((thomPair F E).singularChainComplex (ModuleCat.of K K)).exactAt_iff_isZero_homology n
        |>.2 (isZero_singularHomology_thomPair (F := F) (E := E) (ModuleCat.of K K) (by omega))

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
/-- On cohomology with coefficients in any `K`-module `M`, the map induced by
`chainThomMap (ModuleCat.of K K) φ` (composed with the shift isomorphisms) is the cohomology Thom
map `TauCeti.thomMap`. -/
private theorem homologyMap_chainThomMap_linearYoneda_eq_thomMap (M : ModuleCat.{w} K)
    {r p m : ℕ} (h : p + r = m)
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).cycles r)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    homologyMap ((ChainComplex.linearYonedaFunctor K M).map
        (chainThomMap (F := F) (E := E) (ModuleCat.of K K) φ).op) m
      (homologyMap (((TopCat.toSSet.obj (TopCat.of B)).chainComplex
          (ModuleCat.of K K)).linearYonedaObjExtendIso K M r).inv m
        ((((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
          (ComplexShape.embeddingUpNatAdd r)
          (show (ComplexShape.embeddingUpNatAdd r).f p = m by
            simp [ComplexShape.embeddingUpNatAdd_f]; omega)).inv a)) =
      thomMap F E M r p m h
        (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
          (ModuleCat.of K K)).homologyπ r φ) a := by
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  let CB := (TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of K K)
  let Φ := chainThomMap (F := F) (E := E) (ModuleCat.of K K) φ
  have hpu : (ComplexShape.embeddingUpNatAdd r).f p = m := by
    simp [ComplexShape.embeddingUpNatAdd_f]; omega
  have hpd : (ComplexShape.embeddingDownNatAdd r).f p = m := by
    simp [ComplexShape.embeddingDownNatAdd_f]; omega
  have hstep1 : (((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
      (ComplexShape.embeddingUpNatAdd r) hpu).inv
      (((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K M).homologyπ p ψ) =
      (((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K M).extend
        (ComplexShape.embeddingUpNatAdd r)).homologyπ m
        ((((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K M).extendCyclesIso
          (ComplexShape.embeddingUpNatAdd r) hpu).inv ψ) :=
    ConcreteCategory.congr_hom
      (((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K M).homologyπ_extendHomologyIso_inv
        (ComplexShape.embeddingUpNatAdd r) hpu) ψ
  have hstep2 : ∀ (X Y : CochainComplex (ModuleCat.{w} K) ℕ) (f : X ⟶ Y) (z : X.cycles m),
      homologyMap f m (X.homologyπ m z) = Y.homologyπ m (cyclesMap f m z) :=
    fun _ _ f z ↦ ConcreteCategory.congr_hom (homologyπ_naturality f m) z
  rw [hstep1, hstep2]
  have hstep3 : homologyMap ((ChainComplex.linearYonedaFunctor K M).map Φ.op) m
      (((ChainComplex.linearYonedaFunctor K M).obj
        (Opposite.op (CB.extend (ComplexShape.embeddingDownNatAdd r)))).homologyπ m
        (cyclesMap (CB.linearYonedaObjExtendIso K M r).inv m
          (((CB.linearYonedaObj K M).extendCyclesIso
            (ComplexShape.embeddingUpNatAdd r) hpu).inv ψ))) =
      ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K M).homologyπ m
        (cyclesMap ((ChainComplex.linearYonedaFunctor K M).map Φ.op) m
          (cyclesMap (CB.linearYonedaObjExtendIso K M r).inv m
            (((CB.linearYonedaObj K M).extendCyclesIso
              (ComplexShape.embeddingUpNatAdd r) hpu).inv ψ))) :=
    ConcreteCategory.congr_hom
      (homologyπ_naturality ((ChainComplex.linearYonedaFunctor K M).map Φ.op) m) _
  refine hstep3.trans ?_
  let ψ' : ((thomPair F E).fst.singularCochainComplex (ModuleCat.of K K) K M).cycles p :=
    cyclesMap ((ChainComplex.linearYonedaFunctor K M).map
      (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) (ModuleCat.of K K)).op) p ψ
  have hcyc : cyclesMap ((ChainComplex.linearYonedaFunctor K M).map Φ.op) m
      (cyclesMap (CB.linearYonedaObjExtendIso K M r).inv m
        (((CB.linearYonedaObj K M).extendCyclesIso (ComplexShape.embeddingUpNatAdd r) hpu).inv ψ)) =
      ((-1 : ℤ) ^ (r * p)) •
        ChainComplex.cupCycles K ((thomPair F E).alexanderWhitneyDiagonal (λ_ _).inv) (λ_ M).hom
          r p m (by omega) φ ψ' := by
    have hinj : Function.Injective (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
        M).iCycles m) :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    apply hinj
    rw [map_zsmul, ChainComplex.iCycles_cupCycles]
    have hL1 : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K M).iCycles m
        (cyclesMap ((ChainComplex.linearYonedaFunctor K M).map Φ.op) m
          (cyclesMap (CB.linearYonedaObjExtendIso K M r).inv m
            (((CB.linearYonedaObj K M).extendCyclesIso
              (ComplexShape.embeddingUpNatAdd r) hpu).inv ψ))) =
        Φ.f m ≫ (_root_.ChainComplex.linearYonedaObj (CB.extend
          (ComplexShape.embeddingDownNatAdd r)) K M).iCycles m
          (cyclesMap (CB.linearYonedaObjExtendIso K M r).inv m
            (((CB.linearYonedaObj K M).extendCyclesIso
              (ComplexShape.embeddingUpNatAdd r) hpu).inv ψ)) :=
      ConcreteCategory.congr_hom
        (cyclesMap_i ((ChainComplex.linearYonedaFunctor K M).map Φ.op) m) _
    let ψ₀ : ((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of K K)).X p ⟶ M :=
      (CB.linearYonedaObj K M).iCycles p ψ
    have hL2 : (_root_.ChainComplex.linearYonedaObj (CB.extend
          (ComplexShape.embeddingDownNatAdd r)) K M).iCycles m
          (cyclesMap (CB.linearYonedaObjExtendIso K M r).inv m
            (((CB.linearYonedaObj K M).extendCyclesIso
              (ComplexShape.embeddingUpNatAdd r) hpu).inv ψ)) =
        (((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of K K)).extendXIso
          (ComplexShape.embeddingDownNatAdd r) hpd).hom ≫ ψ₀ :=
      CB.iCycles_cyclesMap_linearYonedaObjExtendIso_inv_apply K M r (p := p) (n := m) h ψ
    have hψ' : ((thomPair F E).fst.singularCochainComplex (ModuleCat.of K K) K M).iCycles p ψ' =
        (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) (ModuleCat.of K K)).f p ≫
          ψ₀ :=
      ConcreteCategory.congr_hom
        (cyclesMap_i ((ChainComplex.linearYonedaFunctor K M).map
          (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) (ModuleCat.of K K)).op) p) ψ
    refine hL1.trans ?_
    rw [hL2, chainThomMap_f_eq (ModuleCat.of K K) (p := p) (m := m) (by omega) φ,
      Preadditive.zsmul_comp, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← Category.assoc]
    have hcap_cup := ChainComplex.capChain_comp (k := K)
      ((thomPair F E).alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
      ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
      (λ_ M).hom r p m (by omega)
      (cochainCycleHom (F := F) (E := E) φ)
      ((SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) (ModuleCat.of K K)).f p ≫ ψ₀)
      ((SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) (ModuleCat.of K K)).f p ≫ ψ₀)
      (by
        rw [SSet.chainComplexPairing_leftUnitor_hom_f]
        exact (leftUnitor_naturality _).symm)
    rw [hψ']
    exact hcap_cup
  rw [hcyc, map_zsmul, ← ChainComplex.cup_homologyπ]
  have hπψ' : ((thomPair F E).fst.singularCochainComplex (ModuleCat.of K K) K M).homologyπ p ψ' =
      TopCat.singularCohomologyMap (thomPairProj F E) p
        (((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K M).homologyπ p ψ) :=
    (ConcreteCategory.congr_hom
      (homologyπ_naturality ((ChainComplex.linearYonedaFunctor K M).map
        (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) (ModuleCat.of K K)).op) p)
      ψ).symm
  rw [hπψ', thomMap_apply,
    TopPair.singularCup_gradedComm K (thomPair F E) (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u' := (λ_ (ModuleCat.of K K)).inv) (μ' := (λ_ M).hom) (μ := (ρ_ M).hom) ?_ ?_ (by omega)]
  · rw [smul_smul, mul_comm p r, ← mul_pow]
    simp
    rfl
  · rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, ← unitors_inv_equal]
    rfl
  · exact braiding_leftUnitor M

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
/-- Tensoring on the left with `A` carries `chainThomMap (𝟙_ (ModuleCat K)) φ` to
`chainThomMap A φ`, up to the coefficient-pairing isomorphisms. -/
private theorem chainThomMap_tensorLeft_comm (A : ModuleCat.{w} K) {r : ℕ}
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).cycles r) :
    ((tensorLeft A).mapHomologicalComplex _).map
        (chainThomMap (F := F) (E := E) (𝟙_ (ModuleCat.{w} K)) φ) ≫
      (((TopCat.toSSet.obj (TopCat.of B)).chainComplex (𝟙_ (ModuleCat.{w} K))).mapExtendIso
        (tensorLeft A) (ComplexShape.embeddingDownNatAdd r)).hom ≫
      HomologicalComplex.extendMap
        ((TopCat.toSSet.obj (TopCat.of B)).chainComplexPairing (ρ_ A).hom)
        (ComplexShape.embeddingDownNatAdd r) =
    (TopPair.toSSetPair.obj (thomPair F E)).chainComplexPairing (ρ_ A).hom ≫
      chainThomMap (F := F) (E := E) A φ := by
  ext n : 1
  by_cases h : r ≤ n
  · set q := n - r
    have hqn : r + q = n := by omega
    have hqd : (ComplexShape.embeddingDownNatAdd r).f q = n := by
      simp [ComplexShape.embeddingDownNatAdd_f]; omega
    rw [← cancel_mono ((((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendXIso
      (ComplexShape.embeddingDownNatAdd r) hqd).hom)]
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc,
      extendMap_f _ _ hqd, Iso.inv_hom_id, Category.comp_id,
      mapExtendIso_hom_f_comp_extendXIso_hom_assoc,
      chainThomMap_f_eq (𝟙_ (ModuleCat.{w} K)) hqn φ, chainThomMap_f_eq A hqn φ,
      Preadditive.comp_zsmul, Preadditive.zsmul_comp, Functor.map_zsmul]
    congr 1
    have hcancel :
        A ◁ ((((TopCat.toSSet.obj (TopCat.of B)).chainComplex (𝟙_ (ModuleCat.{w} K))).extendXIso
            (ComplexShape.embeddingDownNatAdd r) hqd).inv) ≫
          A ◁ ((((TopCat.toSSet.obj (TopCat.of B)).chainComplex (𝟙_ (ModuleCat.{w} K))).extendXIso
            (ComplexShape.embeddingDownNatAdd r) hqd).hom) = 𝟙 _ := by
      rw [← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]
    simp only [curriedTensor_obj_map, whiskerLeft_comp, Category.assoc]
    rw [reassoc_of% hcancel]
    have hnatB := congrArg (fun f ↦ f.f q)
      (SSet.chainComplexPairing_naturality (TopCat.toSSet.map (thomPairProj F E)) (ρ_ A).hom)
    dsimp only [comp_f, Functor.mapHomologicalComplex_map_f, curriedTensor_obj_map] at hnatB
    rw [hnatB]
    -- Reduce to equality on the relative cap chains before pushing forward along `π`.
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_epi (A ◁ ((thomPair F E).singularChainComplexπ (𝟙_ (ModuleCat.{w} K))).f n)]
    rw [SSetPair.whiskerLeft_chainComplexπ_f_chainComplexPairing_f_assoc]
    -- Check on each singular `n`-simplex of the total space `E`.
    let SE := TopCat.toSSet.obj (thomPair F E).fst
    refine Cofan.IsColimit.hom_ext
      (isColimitCofanMkObjOfIsColimit (tensorLeft A) _ _
        (SE.isColimitChainComplexXCofan (𝟙_ (ModuleCat.{w} K)) n)) _ _ fun σ ↦ ?_
    let c : 𝟙_ (ModuleCat.{w} K) ⟶ 𝟙_ (ModuleCat.{w} K) :=
      SE.ιChainComplex (SE.map (SimplexCategory.subinterval 0 r (by omega)).op σ) ≫
        ((thomPair F E).singularChainComplexπ (𝟙_ (ModuleCat.{w} K))).f r ≫
        cochainCycleHom (F := F) (E := E) φ
    let ισ₁ : 𝟙_ (ModuleCat.{w} K) ⟶
        ((TopPair.toSSetPair.obj (thomPair F E)).right.chainComplex (𝟙_ (ModuleCat.{w} K))).X n :=
      SE.ιChainComplex σ
    have hL : A ◁ ισ₁ ≫
        A ◁ ((thomPair F E).singularChainComplexπ (𝟙_ (ModuleCat.{w} K))).f n ≫
        A ◁ ChainComplex.capChain K
          ((thomPair F E).alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
          (SE.chainComplexPairing (λ_ (𝟙_ (ModuleCat.{w} K))).hom) r q n hqn
          (cochainCycleHom (F := F) (E := E) φ) ≫
        (SE.chainComplexPairing (ρ_ A).hom).f q =
      (A ◁ (λ_ (𝟙_ (ModuleCat.{w} K))).inv ≫
        A ◁ (c ▷ 𝟙_ (ModuleCat.{w} K)) ≫
        A ◁ (λ_ (𝟙_ (ModuleCat.{w} K))).hom ≫
        (ρ_ A).hom) ≫
        SE.ιChainComplex (SE.map (SimplexCategory.subinterval r q (by omega)).op σ) := by
      have hcapL : A ◁ (ισ₁ ≫ ((thomPair F E).singularChainComplexπ (𝟙_ (ModuleCat.{w} K))).f n ≫
            ChainComplex.capChain K
              ((thomPair F E).alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
              (SE.chainComplexPairing (λ_ (𝟙_ (ModuleCat.{w} K))).hom) r q n hqn
              (cochainCycleHom (F := F) (E := E) φ)) =
          A ◁ ((λ_ (𝟙_ (ModuleCat.{w} K))).inv ≫
            (c ▷ 𝟙_ (ModuleCat.{w} K)) ≫
            (λ_ (𝟙_ (ModuleCat.{w} K))).hom ≫
            SE.ιChainComplex (SE.map (SimplexCategory.subinterval r q (by omega)).op σ)) :=
        congrArg (A ◁ ·)
          (TopPair.ιChainComplex_singularChainComplexπ_capChain_alexanderWhitneyDiagonal
            (thomPair F E) K (λ_ (𝟙_ (ModuleCat.{w} K))).inv
            (λ_ (𝟙_ (ModuleCat.{w} K))).hom r q n hqn
            (cochainCycleHom (F := F) (E := E) φ) σ)
      have hL1 : A ◁ ισ₁ ≫
          A ◁ ((thomPair F E).singularChainComplexπ (𝟙_ (ModuleCat.{w} K))).f n ≫
          A ◁ ChainComplex.capChain K
            ((thomPair F E).alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
            (SE.chainComplexPairing (λ_ (𝟙_ (ModuleCat.{w} K))).hom) r q n hqn
            (cochainCycleHom (F := F) (E := E) φ) =
          A ◁ (ισ₁ ≫ ((thomPair F E).singularChainComplexπ (𝟙_ (ModuleCat.{w} K))).f n ≫
            ChainComplex.capChain K
              ((thomPair F E).alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
              (SE.chainComplexPairing (λ_ (𝟙_ (ModuleCat.{w} K))).hom) r q n hqn
              (cochainCycleHom (F := F) (E := E) φ)) := by
        rw [← whiskerLeft_comp, ← whiskerLeft_comp]
      rw [← Category.assoc, ← Category.assoc, Category.assoc (A ◁ ισ₁), hL1, hcapL]
      simp only [whiskerLeft_comp, Category.assoc,
        SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f]
    have hR : A ◁ SE.ιChainComplex σ ≫
        (SE.chainComplexPairing (ρ_ A).hom).f n ≫
        ((thomPair F E).singularChainComplexπ A).f n ≫
        ChainComplex.capChain K ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
          (SE.chainComplexPairing (λ_ A).hom) r q n hqn
          (cochainCycleHom (F := F) (E := E) φ) =
      ((ρ_ A).hom ≫ (λ_ A).inv ≫ (c ▷ A) ≫ (λ_ A).hom) ≫
        SE.ιChainComplex (SE.map (SimplexCategory.subinterval r q (by omega)).op σ) := by
      rw [SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f_assoc]
      have hcapR := TopPair.ιChainComplex_singularChainComplexπ_capChain_alexanderWhitneyDiagonal
        (thomPair F E) K (λ_ A).inv (λ_ A).hom r q n hqn
        (cochainCycleHom (F := F) (E := E) φ) σ
      exact (congrArg ((ρ_ A).hom ≫ ·) hcapR).trans (by simp only [Category.assoc]; rfl)
    refine hL.trans (Eq.trans ?_ hR.symm)
    congr 1
    have hunit : (λ_ (𝟙_ (ModuleCat.{w} K))).inv ≫ (c ▷ 𝟙_ (ModuleCat.{w} K)) ≫
        (λ_ (𝟙_ (ModuleCat.{w} K))).hom = c := by
      rw [unitors_inv_equal, unitors_equal, rightUnitor_naturality, Iso.inv_hom_id_assoc]
    rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, Category.assoc (λ_ _).inv, hunit,
      ← Category.assoc (ρ_ A).hom, ← braiding_tensorUnit_right,
      ← BraidedCategory.braiding_naturality_right_assoc, braiding_tensorUnit_right,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · exact (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).isZero_extend_X
      (ComplexShape.embeddingDownNatAdd r) n fun p hp ↦ by
        simp only [ComplexShape.embeddingDownNatAdd_f] at hp
        omega).eq_of_tgt _ _

/-- When `φ` represents a Thom class, `chainThomMap A φ` is a quasi-isomorphism for every
coefficient module `A`. -/
private theorem quasiIso_chainThomMap [VectorBundle ℝ F E] (A : ModuleCat.{w} K)
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).cycles (finrank ℝ F))
    (hu : IsThomClass F E
      (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
        (ModuleCat.of K K)).homologyπ (finrank ℝ F) φ)) :
    QuasiIso (chainThomMap (F := F) (E := E) A φ) := by
  have : QuasiIso (chainThomMap (F := F) (E := E) (𝟙_ (ModuleCat.{w} K)) φ) :=
    quasiIso_chainThomMap_self φ hu
  have : ∀ n, Projective (((thomPair F E).singularChainComplex (𝟙_ (ModuleCat.{w} K))).X n) :=
    fun n ↦ SSetPair.projective_chainComplex_X (ModuleCat.of K K) _ n
  have : ∀ n, Projective
      ((((TopCat.toSSet.obj (TopCat.of B)).chainComplex (𝟙_ (ModuleCat.{w} K))).extend
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F))).X n) :=
    projective_extend_chainComplex_X (finrank ℝ F)
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective
    (chainThomMap (F := F) (E := E) (𝟙_ (ModuleCat.{w} K)) φ)).1 ‹_›
  have htop : QuasiIso (((tensorLeft A).mapHomologicalComplex _).map
      (chainThomMap (F := F) (E := E) (𝟙_ (ModuleCat.{w} K)) φ)) :=
    (HomologicalComplex.mem_quasiIso_iff _).1 <|
      homotopyEquivalences_le_quasiIso _ _ _
        ⟨(tensorLeft A).mapHomotopyEquiv e, by
          dsimp [Functor.mapHomotopyEquiv]
          rw [he]⟩
  have _ : IsIso
      ((((TopCat.toSSet.obj (TopCat.of B)).chainComplex (𝟙_ (ModuleCat.{w} K))).mapExtendIso
        (tensorLeft A) (ComplexShape.embeddingDownNatAdd (finrank ℝ F))).hom ≫
      HomologicalComplex.extendMap
        ((TopCat.toSSet.obj (TopCat.of B)).chainComplexPairing (ρ_ A).hom)
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F))) := by
    have : ∀ n, IsIso ((HomologicalComplex.extendMap
        ((TopCat.toSSet.obj (TopCat.of B)).chainComplexPairing (ρ_ A).hom)
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F))).f n) := fun n ↦ by
      by_cases h : finrank ℝ F ≤ n
      · have hp : (ComplexShape.embeddingDownNatAdd (finrank ℝ F)).f (n - finrank ℝ F) = n := by
          simp [ComplexShape.embeddingDownNatAdd_f]; omega
        rw [HomologicalComplex.extendMap_f _ _ hp]
        infer_instance
      · have hzero₁ := (((tensorLeft A).mapHomologicalComplex _).obj
          ((TopCat.toSSet.obj (TopCat.of B)).chainComplex (𝟙_ (ModuleCat.{w} K)))).isZero_extend_X
            (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) n fun p hp ↦ by
              simp only [ComplexShape.embeddingDownNatAdd_f] at hp
              omega
        have hzero₂ := ((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).isZero_extend_X
          (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) n fun p hp ↦ by
            simp only [ComplexShape.embeddingDownNatAdd_f] at hp
            omega
        exact ⟨⟨0, hzero₁.eq_of_src _ _, hzero₂.eq_of_src _ _⟩⟩
    have : IsIso (HomologicalComplex.extendMap
        ((TopCat.toSSet.obj (TopCat.of B)).chainComplexPairing (ρ_ A).hom)
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F))) :=
      HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  have hcomp : QuasiIso
      ((TopPair.toSSetPair.obj (thomPair F E)).chainComplexPairing (ρ_ A).hom ≫
        chainThomMap (F := F) (E := E) A φ) := by
    rw [← chainThomMap_tensorLeft_comm A φ]
    exact quasiIso_comp _ _
  exact quasiIso_of_comp_left
    ((TopPair.toSSetPair.obj (thomPair F E)).chainComplexPairing (ρ_ A).hom)
    (chainThomMap (F := F) (E := E) A φ)

end ChainThomMap

/-! ### The Thom isomorphism theorem in cohomology and homology -/

namespace IsThomClass

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K]

/-- **The Thom isomorphism theorem in singular cohomology.** Let `E → B` be a real vector bundle of
finite rank `r = finrank ℝ F` over an arbitrary base `B`, and let `u ∈ Hʳ(E, E₀; K)` be a Thom
class (`TauCeti.IsThomClass`). Then for every `K`-module `M` and every `p : ℕ`, the Thom map
`a ↦ π^* a ⌣ u : Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(E, E₀; M)` (`TauCeti.thomMap`) is bijective. -/
theorem bijective_thomMap
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ (finrank ℝ F) u
  have : QuasiIso (chainThomMap (F := F) (E := E) (ModuleCat.of K K) φ) :=
    quasiIso_chainThomMap_self φ hu
  have : ∀ n, Projective (((thomPair F E).singularChainComplex (ModuleCat.of K K)).X n) :=
    fun n ↦ SSetPair.projective_chainComplex_X _ _ n
  have : ∀ n, Projective
      ((((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of K K)).extend
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F))).X n) :=
    projective_extend_chainComplex_X (finrank ℝ F)
  have : QuasiIso ((ChainComplex.linearYonedaFunctor K M).map
      (chainThomMap (F := F) (E := E) (ModuleCat.of K K) φ).op) :=
    _root_.ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective _ K M
  have hIso : IsIso (homologyMap ((ChainComplex.linearYonedaFunctor K M).map
      (chainThomMap (F := F) (E := E) (ModuleCat.of K K) φ).op) m) :=
    (quasiIsoAt_iff_isIso_homologyMap _ m).1 ((quasiIso_iff _).1 ‹_› m)
  have hpu : (ComplexShape.embeddingUpNatAdd (finrank ℝ F)).f p = m := by
    simp [ComplexShape.embeddingUpNatAdd_f]; omega
  let e : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≅
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
    (((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
      (ComplexShape.embeddingUpNatAdd (finrank ℝ F)) hpu).symm ≪≫
    (homologyMapIso (((TopCat.toSSet.obj (TopCat.of B)).chainComplex
      (ModuleCat.of K K)).linearYonedaObjExtendIso K M (finrank ℝ F)).symm m) ≪≫
    @asIso _ _ _ _
      (homologyMap ((ChainComplex.linearYonedaFunctor K M).map
        (chainThomMap (F := F) (E := E) (ModuleCat.of K K) φ).op) m) hIso
  have heq : ⇑(thomMap F E M (finrank ℝ F) p m h
      (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
        (ModuleCat.of K K)).homologyπ (finrank ℝ F) φ)) = ⇑e.toLinearEquiv := by
    funext a
    change _ = e.hom a
    simp only [e, Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom, ConcreteCategory.comp_apply]
    exact (homologyMap_chainThomMap_linearYoneda_eq_thomMap M h φ a).symm
  rw [heq]
  exact e.toLinearEquiv.bijective

/-- **The Thom isomorphism in singular cohomology**, `Hᵖ(B; M) ≃ₗ[K] Hᵖ⁺ʳ(E, E₀; M)`: for a Thom
class `u ∈ Hʳ(E, E₀; K)` of a real vector bundle `E → B` over an arbitrary base `B`, the linear
equivalence given by `a ↦ π^* a ⌣ u`. -/
def thomEquiv
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u) (hu.bijective_thomMap M h)

/-- The cohomology Thom isomorphism is `TauCeti.thomMap`. -/
@[simp]
theorem thomEquiv_apply
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu.thomEquiv M h a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

/-- The cohomology Thom isomorphism sends `1 ∈ H⁰(B; K)` to the Thom class `u`. -/
theorem thomEquiv_one
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    hu.thomEquiv (ModuleCat.of K K) (zero_add _)
        (((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ 0
          ((TopCat.of B).constSingularCocycle K (𝟙 (ModuleCat.of K K)))) = u :=
  thomMap_one F E (zero_add _) u

/-- The inverse of the cohomology Thom isomorphism sends the Thom class `u` to `1 ∈ H⁰(B; K)`. -/
@[simp]
theorem thomEquiv_symm_self
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (hu.thomEquiv (ModuleCat.of K K) (zero_add _)).symm u =
      (((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ 0
        ((TopCat.of B).constSingularCocycle K (𝟙 (ModuleCat.of K K)))) :=
  (hu.thomEquiv (ModuleCat.of K K) (zero_add _)).symm_apply_eq.2 hu.thomEquiv_one.symm

/-- The cohomology Thom isomorphism is linear over the cohomology ring of the base:
`Φ_u(a ⌣ b) = π^* a ⌣ Φ_u(b)`. -/
theorem thomEquiv_singularCup
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) {p q r m s : ℕ}
    (h : p + finrank ℝ F = m) (hqp : q + p = r) (hrn : r + finrank ℝ F = s) (hqm : q + m = s)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) q)
    (b : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu.thomEquiv M hrn
        ((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q p r hqp a b) =
      (thomPair F E).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q m s hqm
        (TopCat.singularCohomologyMap (thomPairProj F E) q a) (hu.thomEquiv M h b) :=
  thomMap_singularCup F E h hqp hrn hqm u a b

/-- Naturality of the cohomology Thom isomorphism along maps of Thom pairs covering maps of
bases. -/
theorem thomEquiv_naturality {B' : Type w} [TopologicalSpace B'] {F' : Type w}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {E' : B' → Type w}
    [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (φ : thomPair F' E' ⟶ thomPair F E) (g : TopCat.of B' ⟶ TopCat.of B)
    (hφ : TopPair.Hom.fst φ ≫ thomPairProj F E = thomPairProj F' E' ≫ g)
    (hr : finrank ℝ F' = finrank ℝ F) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    (hu' : IsThomClass F' E' (hr.symm ▸ TopPair.singularCohomologyMap φ (finrank ℝ F) u))
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu'.thomEquiv M (hr.symm ▸ h) (TopCat.singularCohomologyMap g p a) =
      TopPair.singularCohomologyMap φ m (hu.thomEquiv M h a) := by
  simp only [thomEquiv_apply]
  have hgen : ∀ (n' : ℕ) (hn : n' = finrank ℝ F) (h' : p + n' = m)
      (u' : (thomPair F' E').singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n'),
      u' = hn.symm ▸ TopPair.singularCohomologyMap φ (finrank ℝ F) u →
      thomMap F' E' M n' p m h' u' (TopCat.singularCohomologyMap g p a) =
        TopPair.singularCohomologyMap φ m (thomMap F E M (finrank ℝ F) p m h u a) := by
    rintro _ rfl h' _ rfl
    exact thomMap_naturality F E φ g hφ h u a
  exact hgen (finrank ℝ F') hr (hr.symm ▸ h) _ rfl

/-- Naturality of the inverse cohomology Thom isomorphism along maps of Thom pairs covering maps
of bases: `Φ'⁻¹(φ^* y) = g^*(Φ⁻¹ y)`. -/
theorem thomEquiv_symm_naturality {B' : Type w} [TopologicalSpace B'] {F' : Type w}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {E' : B' → Type w}
    [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (φ : thomPair F' E' ⟶ thomPair F E) (g : TopCat.of B' ⟶ TopCat.of B)
    (hφ : TopPair.Hom.fst φ ≫ thomPairProj F E = thomPairProj F' E' ≫ g)
    (hr : finrank ℝ F' = finrank ℝ F) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    (hu' : IsThomClass F' E' (hr.symm ▸ TopPair.singularCohomologyMap φ (finrank ℝ F) u))
    (y : (thomPair F E).singularCohomology (ModuleCat.of K K) K M m) :
    (hu'.thomEquiv M (hr.symm ▸ h)).symm (TopPair.singularCohomologyMap φ m y) =
      TopCat.singularCohomologyMap g p ((hu.thomEquiv M h).symm y) := by
  rw [LinearEquiv.symm_apply_eq, hu.thomEquiv_naturality φ g hφ hr M h hu',
    LinearEquiv.apply_symm_apply]

/-- **The Thom isomorphism theorem in singular homology.** Let `E → B` be a real vector bundle of
finite rank `r = finrank ℝ F` over an arbitrary base `B`, and let `u ∈ Hʳ(E, E₀; K)` be a Thom
class (`TauCeti.IsThomClass`). Then for every `K`-module `A` and every `p : ℕ`, the homology Thom
map `x ↦ π_*(x ⌢ u) : Hᵣ₊ₚ(E, E₀; A) ⟶ Hₚ(B; A)` (`TauCeti.homologyThomMap`) is an isomorphism. -/
theorem isIso_homologyThomMap
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m) :
    IsIso (homologyThomMap F E A (finrank ℝ F) p m h u) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ (finrank ℝ F) u
  have : QuasiIso (chainThomMap (F := F) (E := E) A φ) := quasiIso_chainThomMap A φ hu
  have hIso : IsIso (homologyMap (chainThomMap (F := F) (E := E) A φ) m) :=
    (quasiIsoAt_iff_isIso_homologyMap _ m).1 ((quasiIso_iff _).1 ‹_› m)
  have hp : (ComplexShape.embeddingDownNatAdd (finrank ℝ F)).f p = m := by
    simp [ComplexShape.embeddingDownNatAdd_f]; omega
  have hmul := homologyMap_chainThomMap_comp_extendHomologyIso_hom (F := F) (E := E) A h φ
  have hscaled : IsIso (((-1 : ℤ) ^ (finrank ℝ F * p)) •
      homologyThomMap F E A (finrank ℝ F) p m h
        (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
          (ModuleCat.of K K)).homologyπ (finrank ℝ F) φ)) := by
    have hcomp : IsIso (homologyMap (chainThomMap (F := F) (E := E) A φ) m ≫
        (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendHomologyIso
          (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) hp).hom) :=
      inferInstance
    obtain ⟨⟨g, hg₁, hg₂⟩⟩ := hcomp
    rw [hmul] at hg₁ hg₂
    exact ⟨⟨g, hg₁, hg₂⟩⟩
  have hres := isIso_neg_one_pow_zsmul (finrank ℝ F * p)
    (((-1 : ℤ) ^ (finrank ℝ F * p)) •
      homologyThomMap F E A (finrank ℝ F) p m h
        (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
          (ModuleCat.of K K)).homologyπ (finrank ℝ F) φ))
  rw [smul_smul, ← mul_pow] at hres
  simpa using hres

/-- The homology Thom map of a Thom class is bijective on elements for every coefficient module `A`
and every degree `p`. -/
theorem bijective_homologyThomMap
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E A (finrank ℝ F) p m h u).hom :=
  (@asIso _ _ _ _ (homologyThomMap F E A (finrank ℝ F) p m h u)
    (hu.isIso_homologyThomMap A h)).toLinearEquiv.bijective

/-- **The Thom isomorphism in singular homology**, `Hᵣ₊ₚ(E, E₀; A) ≅ Hₚ(B; A)`: for a Thom class
`u ∈ Hʳ(E, E₀; K)` of a real vector bundle `E → B` over an arbitrary base `B`, the isomorphism of
`K`-modules given by `x ↦ π_*(x ⌢ u)`. -/
def homologyThomIso
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m) :
    (thomPair F E).singularHomology A m ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj (TopCat.of B) :=
  @asIso _ _ _ _ (homologyThomMap F E A (finrank ℝ F) p m h u) (hu.isIso_homologyThomMap A h)

/-- The forward morphism of `TauCeti.IsThomClass.homologyThomIso` is `TauCeti.homologyThomMap`. -/
@[simp]
theorem homologyThomIso_hom
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m) :
    (hu.homologyThomIso A h).hom = homologyThomMap F E A (finrank ℝ F) p m h u :=
  (rfl)

/-- Naturality of the homology Thom isomorphism along maps of Thom pairs covering maps of bases. -/
theorem homologyThomIso_naturality {B' : Type w} [TopologicalSpace B'] {F' : Type w}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {E' : B' → Type w}
    [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (φ : thomPair F' E' ⟶ thomPair F E) (g : TopCat.of B' ⟶ TopCat.of B)
    (hφ : TopPair.Hom.fst φ ≫ thomPairProj F E = thomPairProj F' E' ≫ g)
    (hr : finrank ℝ F' = finrank ℝ F) (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m)
    (hu' : IsThomClass F' E' (hr.symm ▸ TopPair.singularCohomologyMap φ (finrank ℝ F) u)) :
    (hu'.homologyThomIso A (hr.symm ▸ h)).hom ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map g =
      TopPair.singularHomologyMap φ A m ≫ (hu.homologyThomIso A h).hom := by
  simp only [homologyThomIso_hom]
  have hgen : ∀ (n' : ℕ) (hn : n' = finrank ℝ F) (h' : n' + p = m)
      (u' : (thomPair F' E').singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n'),
      u' = hn.symm ▸ TopPair.singularCohomologyMap φ (finrank ℝ F) u →
      homologyThomMap F' E' A n' p m h' u' ≫
          ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map g =
        TopPair.singularHomologyMap φ A m ≫ homologyThomMap F E A (finrank ℝ F) p m h u := by
    rintro _ rfl h' _ rfl
    exact homologyThomMap_naturality F E φ g hφ h u
  exact hgen (finrank ℝ F') hr (hr.symm ▸ h) _ rfl

end IsThomClass

/-! ### Specializations for oriented vector bundles -/

namespace VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type*} [Fintype ι] {K : Type w} [CommRing K]

/-- **The cohomology Thom isomorphism for an oriented vector bundle**: for any orientation `o` of
`E`, orientation `ω` of `F`, and generator `g` of `Hʳ(F, F ∖ {0}; K)`, the Thom map of
`o.thomClassOfModel hι ω g` is bijective in every degree and for every coefficient `K`-module
`M`. -/
theorem bijective_thomMap_thomClassOfModel (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g)) :=
  (o.isThomClass_thomClassOfModel hι ω hg).bijective_thomMap M h

/-- **The homology Thom isomorphism for an oriented vector bundle**: for any orientation `o` of
`E`, orientation `ω` of `F`, and generator `g` of `Hʳ(F, F ∖ {0}; K)`, the homology Thom map of
`o.thomClassOfModel hι ω g` is an isomorphism in every degree and for every coefficient `K`-module
`A`. -/
theorem isIso_homologyThomMap_thomClassOfModel (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m) :
    IsIso (homologyThomMap F E A (finrank ℝ F) p m h (o.thomClassOfModel hι ω g)) :=
  (o.isThomClass_thomClassOfModel hι ω hg).isIso_homologyThomMap A h

end VectorBundleOrientation

end TauCeti
