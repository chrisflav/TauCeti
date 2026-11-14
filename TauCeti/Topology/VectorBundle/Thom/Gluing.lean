/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Pullback
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Thom.Class
public import TauCeti.Topology.VectorBundle.Thom.Homology

/-!
# Gluing the Thom isomorphism over arbitrary bases

Let `E → B` be a real vector bundle with finite-dimensional model fibre `F` of rank `r`, let `K` be
a commutative ring, and let `u ∈ Hʳ(E, E₀; K)` be a Thom class (`TauCeti.IsThomClass`). Assuming the
product-bundle case for a generator `u₀ ∈ Hʳ(F, F ∖ {0}; K)` (bijectivity of
`a ↦ pr₁^* a ⌣ pr₂^* u₀` on `(W × F, W × (F ∖ {0}))`), this file carries out the global assembly of
the Thom isomorphism in both cohomology (`TauCeti.thomMap`) and homology (`TauCeti.homologyThomMap`)
over an arbitrary base `B` and for arbitrary `K`-module coefficients:

1. **Homology–cohomology equivalence**
   (`TauCeti.forall_bijective_thomMap_iff_forall_bijective_homologyThomMap`,
   `TauCeti.bijective_homologyThomMap_of_forall_bijective_thomMap`): since `Hₙ(E, E₀; K) = 0` for
   `n < r` (`TauCeti.isZero_singularHomology_thomPair`), bijectivity of `TauCeti.thomMap` for all
   `K`-modules `M` and all degrees is equivalent to bijectivity of `TauCeti.homologyThomMap` with
   coefficients in `K` across all degrees, which in turn implies bijectivity of
   `TauCeti.homologyThomMap` for every `K`-module `A`.
2. **Varying-unit reduction on disconnected trivializing sets**
   (`TauCeti.exists_pullbackCup_prodThomPairProj_eq`,
   `TauCeti.bijective_pullbackCup_prodThomPair_of_span_eq_top`,
   `Bundle.Trivialization.bijective_pullbackCupRestrict_totalSpaceProj`): over a possibly
   disconnected base `W`, any class `v ∈ Hʳ(W × F, W × (F ∖ {0}); K)` whose fibre restrictions
   generate `Hʳ(F, F ∖ {0}; K)` has the form `pr₁^* ε ⌣ pr₂^* u₀` for a degree-zero unit
   `ε ∈ H⁰(W; K)`. Cup product on `Hᵖ(W; M)` with `ε` is invertible, reducing the local
   trivializing-set case for `u` to the single-generator product case for `u₀`.
3. **Finite-union Mayer–Vietoris gluing and compact bases**
   (`TauCeti.bijective_pullbackCupRestrict_totalSpaceProj_biUnion`,
   `TauCeti.bijective_thomMap_of_compactSpace`): induction over finite unions of open subsets of
   linear trivializations via `TopCat.bijective_pullbackCupRestrict_union` and the vanishing of
   overlap cohomology below the rank (`TauCeti.isZero_singularCohomology_thomPairOver_biUnion`).
4. **Passage to an arbitrary base** (`TauCeti.bijective_homologyThomMap`,
   `TauCeti.bijective_thomMap`): over each finite union `U_s` of chosen trivializing open sets,
   cohomology bijectivity gives homology bijectivity with coefficients in `K`; since singular
   homology commutes with the directed union of the `U_s`
   (`TauCeti.isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion`), `homologyThomMap`
   with `K`-coefficients is bijective over `B`, and step 1 upgrades this to `thomMap` and
   `homologyThomMap` for every `K`-module of coefficients.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7, Theorem 10.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 4.D, Theorem 4D.10.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Limits Module MonoidalCategory Set Topology

universe w

namespace TauCeti

/-! ### Equivalence of the cohomology and homology Thom isomorphisms -/

section Equivalence

/-- `TauCeti.homologyThomMap` is `TopPair.capPushforward` of the Thom pair along its projection. -/
theorem homologyThomMap_eq_capPushforward {B : Type w} [TopologicalSpace B] (F : Type*)
    [TopologicalSpace F] (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] {K : Type w} [CommRing K]
    (A : ModuleCat.{w} K) (n p m : ℕ) (h : n + p = m) :
    homologyThomMap F E A n p m h =
      (thomPair F E).capPushforward A (thomPairProj F E) n p m h :=
  LinearMap.ext fun u ↦
    (homologyThomMap_apply F E (A := A) h u).trans (TopPair.capPushforward_apply _ _ h u).symm

variable {B : Type w} [TopologicalSpace B] (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {K : Type w} [CommRing K]

/-- **Equivalence of the cohomology and homology Thom isomorphisms.** Since `Hⱼ(E, E₀; K) = 0` for
`j < dim F`, `TauCeti.thomMap` of `u ∈ Hʳ(E, E₀; K)` is bijective in every degree and for every
`K`-module `M` if and only if `TauCeti.homologyThomMap` of `u` with coefficients in `K` is bijective
in every degree. -/
theorem forall_bijective_thomMap_iff_forall_bijective_homologyThomMap
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)) :
    (∀ (M : ModuleCat.{w} K) p m (h : p + finrank ℝ F = m),
        Function.Bijective (thomMap F E M (finrank ℝ F) p m h u)) ↔
      ∀ p m (h : finrank ℝ F + p = m),
        Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
  simp only [thomMap_def, homologyThomMap_eq_capPushforward]
  exact (thomPair F E).forall_bijective_pullbackCup_iff_forall_bijective_capPushforward
    (thomPairProj F E) (finrank ℝ F) (fun _ hj ↦ isZero_singularHomology_thomPair _ hj) u

/-- If `TauCeti.homologyThomMap` of `u ∈ Hʳ(E, E₀; K)` with coefficients in `K` is bijective in
every degree, then it is bijective in every degree for every `K`-module `A`. -/
theorem bijective_homologyThomMap_of_forall_bijective_homologyThomMap
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hbij : ∀ q k (hk : finrank ℝ F + q = k),
      Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) q k hk u))
    (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E A (finrank ℝ F) p m h u) := by
  rw [homologyThomMap_eq_capPushforward]
  exact (thomPair F E).bijective_capPushforward_of_forall_bijective_capPushforward
    (thomPairProj F E) A (finrank ℝ F) p m h
    (fun _ hj ↦ isZero_singularHomology_thomPair _ hj) u
    fun q k hk ↦ by simpa [homologyThomMap_eq_capPushforward] using hbij q k hk

/-- If `TauCeti.thomMap` of `u ∈ Hʳ(E, E₀; K)` is bijective in every degree for every `K`-module
`M`, then `TauCeti.homologyThomMap` of `u` is bijective in every degree for every `K`-module `A`. -/
theorem bijective_homologyThomMap_of_forall_bijective_thomMap
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hbij : ∀ (M : ModuleCat.{w} K) q k (hk : q + finrank ℝ F = k),
      Function.Bijective (thomMap F E M (finrank ℝ F) q k hk u))
    (A : ModuleCat.{w} K) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E A (finrank ℝ F) p m h u) :=
  bijective_homologyThomMap_of_forall_bijective_homologyThomMap F E u
    ((forall_bijective_thomMap_iff_forall_bijective_homologyThomMap F E u).1 hbij) A h

end Equivalence

/-! ### Varying-unit reduction over disconnected trivializing sets -/

section VaryingUnit

variable {K : Type w} [CommRing K]

/-- `TopPair.pullbackCup` of `g^* ε ⌣ u` is `TopPair.pullbackCup` of `u` after right-cupping on the
base with `ε ∈ H⁰(Z; K)`. -/
private theorem pullbackCup_pullbackCup_zero (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z)
    (M : ModuleCat.{w} K) {n p m : ℕ} (h : p + n = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (ε : Z.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0)
    (b : Z.singularCohomology (ModuleCat.of K K) K M p) :
    P.pullbackCup M g n p m h (P.pullbackCup (ModuleCat.of K K) g n 0 n (Nat.zero_add n) u ε) b =
      P.pullbackCup M g n p m h u
        (Z.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p)
          b ε) := by
  rw [TopPair.pullbackCup_apply, TopPair.pullbackCup_apply, TopPair.pullbackCup_apply,
    ← TopCat.singularCup_naturality]
  exact (TopPair.singularCup_assoc K P (by monoidal) (by monoidal)
    (Nat.add_zero p) h (Nat.zero_add n) h _ _ _).symm

/-- Right-cupping on `Hᵖ(Z; M)` with a degree-zero unit `ε ∈ H⁰(Z; K)` is bijective. -/
private theorem bijective_singularCup_zero_of_mul_eq_one {Z : TopCat.{w}} (M : ModuleCat.{w} K)
    (p : ℕ) {ε₀ η₀ : Z.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0}
    (hεη : Z.singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl ε₀ η₀ = Z.singularCohomologyZeroOne)
    (hηε : Z.singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl η₀ ε₀ = Z.singularCohomologyZeroOne) :
    Function.Bijective (fun b : Z.singularCohomology (ModuleCat.of K K) K M p ↦
      Z.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p) b
        (ε₀ : Z.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0)) := by
  have hone (b : Z.singularCohomology (ModuleCat.of K K) K M p) :
      Z.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p) b
        Z.singularCohomologyZeroOne = b := by
    rw [TopCat.singularCohomologyZeroOne_def]
    exact Z.singularCup_constSingularCocycle_right K (η := 𝟙 _)
      (by simp [unitors_inv_equal]; rfl) (by simp) (Nat.add_zero p) b
  refine Function.bijective_iff_has_inverse.2
    ⟨fun b ↦ Z.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p)
        b η₀,
      fun b ↦ ?_, fun b ↦ ?_⟩
  · refine (Z.singularCup_assoc K (u₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (μ₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).hom)
      (μ' := (ρ_ M).hom) (by monoidal) (by monoidal) (Nat.add_zero p) (Nat.add_zero p)
      rfl (Nat.add_zero p) b ε₀ η₀).trans ?_
    rw [hεη, hone]
  · refine (Z.singularCup_assoc K (u₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (μ₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).hom)
      (μ' := (ρ_ M).hom) (by monoidal) (by monoidal) (Nat.add_zero p) (Nat.add_zero p)
      rfl (Nat.add_zero p) b η₀ ε₀).trans ?_
    rw [hηε, hone]

/-- Points joined by a path in `W` have homotopic fibre inclusions into `prodThomPair W F`, so they
induce the same restriction map on relative singular cohomology. -/
private theorem singularCohomologyMap_prodThomPairFiberMap_eq_of_joined {W : Type w}
    [TopologicalSpace W] {F : Type w} [TopologicalSpace F] [Zero F] {w w' : W}
    (hw : Joined w w') (n : ℕ)
    (u : (prodThomPair W F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    TopPair.singularCohomologyMap (prodThomPairFiberMap F w) n u =
      TopPair.singularCohomologyMap (prodThomPairFiberMap F w') n u := by
  let γ := hw.somePath
  let g₀ : TopCat.of F ⟶ TopCat.of (W × F) := TopCat.ofHom ⟨fun x ↦ (w, x), by fun_prop⟩
  let g₁ : TopCat.of F ⟶ TopCat.of (W × F) := TopCat.ofHom ⟨fun x ↦ (w', x), by fun_prop⟩
  let H : g₀.hom.Homotopy g₁.hom :=
    { toContinuousMap := ⟨fun q : unitInterval × F ↦ (γ q.1, q.2), by fun_prop⟩
      map_zero_left _ := Prod.ext γ.source rfl
      map_one_left _ := Prod.ext γ.target rfl }
  have hH : TopPair.Homotopy (prodThomPairFiberMap F w) (prodThomPairFiberMap F w') := by
    convert TopPair.ofSubsetHomotopy H (B := ({0}ᶜ : Set F)) (B' := {p : W × F | p.2 ≠ 0})
      fun _ _ hx ↦ hx <;>
    exact TopPair.hom_ext_of_fst _ ((TopCat.ext fun (x : F) ↦
      prodThomPairFiberMap_fst_apply F _ x).trans (TopPair.ofSubsetMap_fst _ _).symm)
  exact ConcreteCategory.congr_hom
    (hH.congr_singularCohomologyMap (ModuleCat.of K K) K (ModuleCat.of K K) n) u

/-- Under a linear equivalence with `K`, a generator of a cyclic `K`-module maps to a unit. -/
private theorem isUnit_of_span_eq_top {V : Type*} [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] ModuleCat.of K K) {v : V} (hv : Submodule.span K {v} = ⊤) :
    IsUnit (e v : K) := by
  have hv' : e.symm (1 : K) ∈ Submodule.span K {v} := hv.symm ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hv'
  refine IsUnit.of_mul_eq_one_right c ?_
  simpa [smul_eq_mul] using congrArg e hc

variable {W : Type w} [TopologicalSpace W] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Factoring a fibrewise generator on a product bundle.** Let `u₀` generate `Hʳ(F, F ∖ {0}; K)`
and let `u ∈ Hʳ(W × F, W × (F ∖ {0}); K)` restrict to a generator on every fibre over `W`. Then
`u = pr₁^* ε ⌣ pr₂^* u₀` for a degree-zero class `ε ∈ H⁰(W; K)` invertible for the cup product. -/
theorem exists_pullbackCup_prodThomPairProj_eq
    {u₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu₀ : Submodule.span K {u₀} = ⊤)
    {u : (prodThomPair W F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ w : W, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F w) (finrank ℝ F) u} = ⊤) :
    ∃ ε₀ η₀ : (TopCat.of W).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0,
      (TopCat.of W).singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl ε₀ η₀ =
        (TopCat.of W).singularCohomologyZeroOne ∧
      (TopCat.of W).singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl η₀ ε₀ =
        (TopCat.of W).singularCohomologyZeroOne ∧
      u = (prodThomPair W F).pullbackCup (ModuleCat.of K K) (prodThomPairProj W F)
        (finrank ℝ F) 0 (finrank ℝ F) (Nat.zero_add _)
        (TopPair.singularCohomologyMap (prodThomPairSnd W F) (finrank ℝ F) u₀) ε₀ := by
  let e := singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of K K)
    (OpenPartialHomeomorph.refl F) (Set.mem_univ (0 : F))
  have hu₀_unit : IsUnit (e u₀ : K) := isUnit_of_span_eq_top e hu₀
  let f : W → K := fun w ↦
    (e (TopPair.singularCohomologyMap (prodThomPairFiberMap F w) (finrank ℝ F) u) : K) *
      ↑hu₀_unit.unit⁻¹
  have hf_joined : ∀ x y : TopCat.of W, Joined x y → f x = f y := fun x y hxy ↦ by
    dsimp only [f]
    rw [singularCohomologyMap_prodThomPairFiberMap_eq_of_joined hxy]
  obtain ⟨ε₀, hε₀⟩ := exists_singularCohomologyZeroEval_eq (X := TopCat.of W) f hf_joined
  have hε₀_unit : ∀ x : TopCat.of W, IsUnit (singularCohomologyZeroEval x ε₀) := fun w ↦ by
    rw [hε₀ w]
    exact (isUnit_of_span_eq_top e (hu w)).mul (Units.isUnit hu₀_unit.unit⁻¹)
  obtain ⟨η₀, hεη, hηε⟩ := exists_singularCup_eq_one ε₀ hε₀_unit
  refine ⟨ε₀, η₀, hεη, hηε, singularCohomology_prodThomPair_ext fun w ↦ ?_⟩
  let P₀ := TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)
  have hnat := TopPair.pullbackCup_naturality (M := ModuleCat.of K K) (prodThomPairFiberMap F w)
    (TopCat.const (X := P₀.fst) w) (prodThomPairProj W F) (𝟙 (TopCat.of W))
    (by
      rw [Category.comp_id]
      exact TopCat.ext fun (x : F) ↦ ((congrArg (prodThomPairProj W F)
        (prodThomPairFiberMap_fst_apply F w x)).trans (prodThomPairProj_apply F (w, x))).trans
        (TopCat.const_apply (X := P₀.fst) (Y := TopCat.of W) w x).symm)
    (Nat.zero_add (finrank ℝ F))
    (TopPair.singularCohomologyMap (prodThomPairSnd W F) (finrank ℝ F) u₀) ε₀
  rw [TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
    ← TopPair.singularCohomologyMap_comp_apply, prodThomPairFiberMap_comp_prodThomPairSnd,
    TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply] at hnat
  rw [← hnat, TopPair.pullbackCup_apply,
    singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul, hε₀ w, map_smul,
    LinearMap.smul_apply, TopCat.singularCohomologyZeroOne_def,
    P₀.singularCup_constSingularCocycle_left K (η := 𝟙 _) (by monoidal) (by monoidal)
      (Nat.zero_add _) u₀]
  refine e.injective ?_
  have hval : (e (f w • u₀) : K) = f w * (e u₀ : K) := by simp [smul_eq_mul]
  rw [hval]
  dsimp only [f]
  rw [mul_assoc, hu₀_unit.val_inv_mul, mul_one]

/-- **Bijectivity on a product bundle for an arbitrary fibrewise generator.** Over a possibly
disconnected space `W`, if `a ↦ pr₁^* a ⌣ pr₂^* u₀` is bijective for a generator `u₀` of
`Hʳ(F, F ∖ {0}; K)`, then `a ↦ pr₁^* a ⌣ u` is bijective for every `u ∈ Hʳ(W × F, W × (F ∖ {0}); K)`
whose restriction to every fibre generates `Hʳ(F, F ∖ {0}; K)`. -/
theorem bijective_pullbackCup_prodThomPair_of_span_eq_top (M : ModuleCat.{w} K)
    {u₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu₀ : Submodule.span K {u₀} = ⊤) {p m : ℕ} (h : p + finrank ℝ F = m)
    (hprod : Function.Bijective ((prodThomPair W F).pullbackCup M (prodThomPairProj W F)
      (finrank ℝ F) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd W F) (finrank ℝ F) u₀)))
    {u : (prodThomPair W F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ w : W, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F w) (finrank ℝ F) u} = ⊤) :
    Function.Bijective ((prodThomPair W F).pullbackCup M (prodThomPairProj W F)
      (finrank ℝ F) p m h u) := by
  obtain ⟨ε₀, η₀, hεη, hηε, rfl⟩ := exists_pullbackCup_prodThomPairProj_eq hu₀ hu
  have hcomp : ⇑((prodThomPair W F).pullbackCup M (prodThomPairProj W F) (finrank ℝ F) p m h
      ((prodThomPair W F).pullbackCup (ModuleCat.of K K) (prodThomPairProj W F)
        (finrank ℝ F) 0 (finrank ℝ F) (Nat.zero_add _)
        (TopPair.singularCohomologyMap (prodThomPairSnd W F) (finrank ℝ F) u₀) ε₀)) =
      ⇑((prodThomPair W F).pullbackCup M (prodThomPairProj W F) (finrank ℝ F) p m h
        (TopPair.singularCohomologyMap (prodThomPairSnd W F) (finrank ℝ F) u₀)) ∘
        fun b ↦ (TopCat.of W).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p
          (Nat.add_zero p) b ε₀ :=
    funext (pullbackCup_pullbackCup_zero (prodThomPair W F) (prodThomPairProj W F) M h _ _ )
  rw [hcomp]
  exact hprod.comp (bijective_singularCup_zero_of_mul_eq_one M p hεη hηε)

end VaryingUnit

/-! ### Trivializing open sets and finite-union Mayer–Vietoris gluing -/

section FiniteUnion

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K]

/-- The bundle projection `π : E → B` as a morphism `TopCat.of (TotalSpace F E) ⟶ TopCat.of B`,
matching the ambient space of `zeroSectionCompl F E` in `TopCat.pullbackCupRestrict` and
`TopCat.capPushforwardRestrict`. -/
abbrev totalSpaceProj (F : Type*) [TopologicalSpace F] (E : B → Type w)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] :
    TopCat.of (TotalSpace F E) ⟶ TopCat.of B :=
  TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩

/-- **The Thom map over a subset of a trivializing open set.** If `W ⊆ e.baseSet` for a linear
trivialization `e` and `u` is a Thom class of `E`, then the restricted Thom map over `W` is
bijective whenever the product-bundle Thom map for a fibre generator `u₀` is bijective over `W`. -/
theorem _root_.Bundle.Trivialization.bijective_pullbackCupRestrict_totalSpaceProj
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet)
    (M : ModuleCat.{w} K)
    {u₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu₀ : Submodule.span K {u₀} = ⊤) {p m : ℕ} (h : p + finrank ℝ F = m)
    (hprod : Function.Bijective ((prodThomPair ↥W F).pullbackCup M (prodThomPairProj ↥W F)
      (finrank ℝ F) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd ↥W F) (finrank ℝ F) u₀)))
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (TopCat.pullbackCupRestrict (totalSpaceProj F E) (zeroSectionCompl F E) M W
      (finrank ℝ F) p m h u) := by
  rw [TopCat.pullbackCupRestrict_apply]
  let uW := TopPair.singularCohomologyMap
    (TopCat.restrictPreimagePairMap (totalSpaceProj F E) (zeroSectionCompl F E) W) (finrank ℝ F) u
  have hg : TopPair.Hom.fst (e.thomPairOverIso ℝ hW).inv ≫
      TopCat.ofHom ((totalSpaceProj F E).hom.restrictPreimage W) =
      prodThomPairProj ↥W F ≫ 𝟙 (TopCat.of ↥W) := by
    rw [Category.comp_id]
    exact ((TopPair.proj₁.mapIso (e.thomPairOverIso ℝ hW)).inv_comp_eq).2
      (TopCat.ext fun (v : π F E ⁻¹' W) ↦
        (prodThomPairProj_apply F ((⟨v.1.proj, v.2⟩ : ↥W), (e v).2)).symm.trans
          (congrArg (prodThomPairProj ↥W F) (e.thomPairOverIso_hom_fst_apply ℝ hW v)).symm)
  refine (TopPair.bijective_pullbackCup_iff_of_isIso (e.thomPairOverIso ℝ hW).inv
    (𝟙 (TopCat.of ↥W)) (g := prodThomPairProj ↥W F)
    (g' := TopCat.ofHom ((totalSpaceProj F E).hom.restrictPreimage W)) hg h uW).1 ?_
  refine bijective_pullbackCup_prodThomPair_of_span_eq_top M hu₀ h hprod fun w ↦ ?_
  let φ := (e.continuousLinearEquivAt ℝ w.1 (hW w.2)).complZeroPairIso
  have hfib : prodThomPairFiberMap F w ≫ (e.thomPairOverIso ℝ hW).inv =
      φ.inv ≫ fiberThomPairOverMap F E w.2 := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
      e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW w.2]
  have hrestr : TopCat.restrictPreimagePairMap (totalSpaceProj F E) (zeroSectionCompl F E) W =
      TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W := rfl
  have huProd_w : TopPair.singularCohomologyMap (prodThomPairFiberMap F w) (finrank ℝ F)
      (TopPair.singularCohomologyMap (e.thomPairOverIso ℝ hW).inv (finrank ℝ F) uW) =
      TopPair.singularCohomologyMap φ.inv (finrank ℝ F)
        (TopPair.singularCohomologyMap (fiberThomPairMap F E w.1) (finrank ℝ F) u) := by
    simp only [uW, hrestr, ← TopPair.singularCohomologyMap_comp_apply]
    rw [reassoc_of% hfib, fiberThomPairOverMap_comp_restrictPreimagePairMap]
  rw [huProd_w, Submodule.span_singleton_eq_top_iff]
  intro v
  obtain ⟨r, hr⟩ := (Submodule.span_singleton_eq_top_iff K _).1 ((isThomClass_iff.1 hu).2 w.1)
    (TopPair.singularCohomologyMap φ.hom (finrank ℝ F) v)
  refine ⟨r, ?_⟩
  simpa [← TopPair.singularCohomologyMap_comp_apply] using
    congrArg (TopPair.singularCohomologyMap φ.inv (finrank ℝ F)) hr

/-- **Finite-union Mayer–Vietoris gluing of the Thom map.** Over a finite union of open sets `W i`,
each contained in the base set of a linear trivialization, the restricted Thom map of a Thom class
`u` is bijective in degree `p` whenever the product-bundle Thom map for a generator `u₀` is
bijective in degrees `q ≤ p` over open subsets of `B`. -/
theorem bijective_pullbackCupRestrict_totalSpaceProj_biUnion (M : ModuleCat.{w} K) {ι : Type*}
    (s : Finset ι) {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {u₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu₀ : Submodule.span K {u₀} = ⊤) {p m : ℕ} (h : p + finrank ℝ F = m)
    (hprod : ∀ (U : Set B), IsOpen U → ∀ q ≤ p,
      Function.Bijective ((prodThomPair ↥U F).pullbackCup M (prodThomPairProj ↥U F)
        (finrank ℝ F) q (q + finrank ℝ F) rfl
        (TopPair.singularCohomologyMap (prodThomPairSnd ↥U F) (finrank ℝ F) u₀)))
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (TopCat.pullbackCupRestrict (totalSpaceProj F E) (zeroSectionCompl F E) M
      (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  classical
  induction s using Finset.induction_on generalizing W p m with
  | empty =>
    have : IsEmpty ↥(⋃ i ∈ (∅ : Finset ι), W i) := by simp
    have hsrc : IsZero ((TopCat.of ↥(⋃ i ∈ (∅ : Finset ι), W i)).singularCohomology
        (ModuleCat.of K K) K M p) :=
      isZero_singularCohomology_of_isEmpty (ModuleCat.of K K) K M _ p
    have htgt : IsZero ((thomPairOver F E (⋃ i ∈ (∅ : Finset ι), W i)).singularCohomology
        (ModuleCat.of K K) K M m) :=
      TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of K K) M m
        fun j _ ↦ by simpa using isZero_singularHomology_thomPairOver_empty (ModuleCat.of K K) j
    exact (ConcreteCategory.isIso_iff_bijective (ModuleCat.ofHom _)).1 (hsrc.isIso htgt _)
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have ha : a ∈ insert a s := Finset.mem_insert_self a s
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    obtain ⟨e, _, he⟩ := hWe a ha
    refine TopCat.bijective_pullbackCupRestrict_union (totalSpaceProj F E) (zeroSectionCompl F E) M
      (hWo a ha) (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (hs i hi)) u
      (fun q hq ↦ ?_) (fun q hq ↦ ?_) (fun q hq ↦ ?_) (fun j hj ↦ ?_) h
    · exact e.bijective_pullbackCupRestrict_totalSpaceProj he M hu₀ rfl
        (hprod (W a) (hWo a ha) q hq) hu
    · exact ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hWe i (hs i hi)) rfl
        fun U hU q' hq' ↦ hprod U hU q' (hq'.trans hq)
    · rw [inter_iUnion₂]
      refine ih (fun i hi ↦ (hWo a ha).inter (hWo i (hs i hi))) (fun i hi ↦ ?_) rfl
        fun U hU q' hq' ↦ hprod U hU q' (hq'.trans hq)
      obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
      exact ⟨e', he', inter_subset_right.trans hi'⟩
    · change IsZero ((thomPairOver F E (W a ∩ ⋃ i ∈ s, W i)).singularCohomology
        (ModuleCat.of K K) K M j)
      rw [inter_iUnion₂]
      refine isZero_singularCohomology_thomPairOver_biUnion (ModuleCat.of K K) M s
        (fun i hi ↦ (hWo a ha).inter (hWo i (hs i hi))) (fun i hi ↦ ?_) (by omega)
      obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
      exact ⟨e', he', inter_subset_right.trans hi'⟩

/-- **The Thom isomorphism over a compact base.** Over a compact base `B`, if the product-bundle
Thom map for a fibre generator `u₀` is bijective in degrees `q ≤ p` over open subsets of `B` for a
`K`-module `M`, then `TauCeti.thomMap` of any Thom class `u` is bijective in degree `p` for `M`. -/
theorem bijective_thomMap_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    (M : ModuleCat.{w} K)
    {u₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu₀ : Submodule.span K {u₀} = ⊤) {p m : ℕ} (h : p + finrank ℝ F = m)
    (hprod : ∀ (U : Set B), IsOpen U → ∀ q ≤ p,
      Function.Bijective ((prodThomPair ↥U F).pullbackCup M (prodThomPairProj ↥U F)
        (finrank ℝ F) q (q + finrank ℝ F) rfl
        (TopPair.singularCohomologyMap (prodThomPairSnd ↥U F) (finrank ℝ F) u₀)))
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
  have hbij := bijective_pullbackCupRestrict_totalSpaceProj_biUnion M t
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) hu₀ h hprod hu
  rw [univ_subset_iff.1 ht, TopCat.bijective_pullbackCupRestrict_univ_iff] at hbij
  have heq : (thomPair F E).pullbackCup M (totalSpaceProj F E) (finrank ℝ F) p m h u =
      thomMap F E M (finrank ℝ F) p m h u := by
    rw [thomMap_def, thomPairProj_def]
  rwa [heq] at hbij

end FiniteUnion

/-! ### Directed-union passage to an arbitrary base -/

section ArbitraryBase

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {K : Type w} [CommRing K]

/-- The diagram of finite unions of the chosen trivializing open sets of `E → B`. -/
private def baseFiniteTrivializingUnionDiagram (F : Type w) [TopologicalSpace F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] : Finset B ⥤ TopCat.{w} where
  obj s := TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet)
  map f := TopCat.ofHom (ContinuousMap.inclusion (biUnion_subset_biUnion_left f.le))

/-- The cocone of inclusions of finite trivializing unions into `B`. -/
private def baseFiniteTrivializingUnionCocone (F : Type w) [TopologicalSpace F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] : Cocone (baseFiniteTrivializingUnionDiagram F E) where
  pt := TopCat.of B
  ι := { app _ := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ }

/-- Singular homology of `B` in any degree `p` is the filtered colimit over finite unions of the
chosen trivializing open sets. -/
private def isColimitSingularHomologyBaseFiniteTrivializingUnion (A : ModuleCat.{w} K) (p : ℕ) :
    IsColimit (((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).mapCocone
      (baseFiniteTrivializingUnionCocone F E)) :=
  isColimitMapCoconeSingularHomology A p (baseFiniteTrivializingUnionCocone F E)
    (fun _ ↦ IsEmbedding.subtypeVal) fun L hL ↦ by
      obtain ⟨s, hs⟩ := hL.elim_finite_subcover _
        (fun b ↦ (trivializationAt F E b).open_baseSet)
        fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
      exact ⟨s, fun b hb ↦ ⟨⟨b, hs hb⟩, rfl⟩⟩

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
private theorem singularHomology_thomPairOver_finiteTrivializingUnion_eq (A : ModuleCat.{w} K)
    (m : ℕ) (s : Finset B) :
    (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology A m =
      (TopPair.singularHomologyFunctor A m).obj
        ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) := by
  rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
private theorem singularHomology_thomPair_eq (A : ModuleCat.{w} K) (m : ℕ) :
    (thomPair F E).singularHomology A m =
      (TopPair.singularHomologyFunctor A m).obj
        (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt := by
  rw [thomPairFiniteTrivializingUnionCocone_pt, TopPair.singularHomologyFunctor_obj]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- Over an arbitrary base, if `TopCat.capPushforwardRestrict` of `u` is an isomorphism over every
finite union of the chosen trivializing open sets, then `TauCeti.homologyThomMap` of `u` is an
isomorphism over the whole base. -/
private theorem isIso_homologyThomMap_of_finiteTrivializingUnion (A : ModuleCat.{w} K)
    {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hiso : ∀ s : Finset B, IsIso (TopCat.capPushforwardRestrict (totalSpaceProj F E)
      (zeroSectionCompl F E) A (⋃ b ∈ s, (trivializationAt F E b).baseSet) n p m h u)) :
    IsIso (homologyThomMap F E A n p m h u) := by
  have heq : homologyThomMap F E A n p m h u =
      (thomPair F E).capPushforward A (totalSpaceProj F E) n p m h u := by
    rw [homologyThomMap_eq_capPushforward, thomPairProj_def]
  rw [heq]
  let P₁ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion
    (F := F) (E := E) A m
  let P₂ := isColimitSingularHomologyBaseFiniteTrivializingUnion (F := F) (E := E) A p
  let α : thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor A m ≅
      baseFiniteTrivializingUnionDiagram F E ⋙
        (singularHomologyFunctor (ModuleCat.{w} K) p).obj A :=
    NatIso.ofComponents
      (fun s ↦ eqToIso (singularHomology_thomPairOver_finiteTrivializingUnion_eq (F := F) (E := E)
        A m s).symm ≪≫ @asIso _ _ _ _ (TopCat.capPushforwardRestrict (totalSpaceProj F E)
          (zeroSectionCompl F E) A (⋃ b ∈ s, (trivializationAt F E b).baseSet) n p m h u)
          (hiso s))
      fun {s t} f ↦ by
        have := hiso s
        have := hiso t
        dsimp only [Functor.comp_obj, Functor.comp_map, baseFiniteTrivializingUnionDiagram]
        simp only [thomPairFiniteTrivializingUnionDiagram_map,
          TopPair.singularHomologyFunctor_map, Iso.trans_hom, eqToIso.hom, asIso_hom,
          Category.assoc, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        have hst : (⋃ b ∈ s, (trivializationAt F E b).baseSet) ⊆
            ⋃ b ∈ t, (trivializationAt F E b).baseSet :=
          biUnion_subset_biUnion_left f.le
        have hmap : thomPairOverMap F E hst =
            TopPair.ofInclusionMap
              (inter_subset_left : totalSpaceProj F E ⁻¹'
                (⋃ b ∈ s, (trivializationAt F E b).baseSet) ∩ zeroSectionCompl F E ⊆ _)
              inter_subset_left (ContinuousMap.inclusion (preimage_mono hst))
              fun _ hx ↦ ⟨hst hx.1, hx.2⟩ :=
          TopPair.hom_ext_of_fst _
            ((thomPairOverMap_fst F E hst).trans (TopPair.ofInclusionMap_fst _ _).symm)
        rw [hmap]
        exact congrArg (eqToHom _ ≫ ·)
          (TopCat.capPushforwardRestrict_naturality (totalSpaceProj F E) (zeroSectionCompl F E) A
            hst h u).symm
  have hleg (s : Finset B) :
      ((TopPair.singularHomologyFunctor A m).mapCocone
          (thomPairFiniteTrivializingUnionCocone (F := F) (E := E))).ι.app s ≫
        eqToHom (singularHomology_thomPair_eq (F := F) (E := E) A m).symm ≫
        (thomPair F E).capPushforward A (totalSpaceProj F E) n p m h u =
      (α.hom.app s) ≫
        (((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).mapCocone
          (baseFiniteTrivializingUnionCocone F E)).ι.app s := by
    have hα : α.hom.app s =
        eqToHom (singularHomology_thomPairOver_finiteTrivializingUnion_eq (F := F) (E := E)
          A m s).symm ≫
        TopCat.capPushforwardRestrict (totalSpaceProj F E) (zeroSectionCompl F E) A
          (⋃ b ∈ s, (trivializationAt F E b).baseSet) n p m h u := rfl
    rw [hα]
    dsimp only [Functor.mapCocone_ι_app, baseFiniteTrivializingUnionCocone,
      baseFiniteTrivializingUnionDiagram]
    simp only [thomPairFiniteTrivializingUnionCocone_ι_app, TopPair.singularHomologyFunctor_map,
      TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    refine congrArg (eqToHom _ ≫ ·) ?_
    rw [← TopPair.singularHomologyMap_comp_assoc, thomPairOverUnivIso_hom,
      thomPairOverMap_comp_restrictPreimagePairMap, TopCat.capPushforwardRestrict_apply]
    exact (TopPair.capPushforward_naturality
      (TopCat.restrictPreimagePairMap (totalSpaceProj F E) (zeroSectionCompl F E)
        (⋃ b ∈ s, (trivializationAt F E b).baseSet))
      _ (totalSpaceProj F E) (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
      (by rw [TopCat.restrictPreimagePairMap_fst]; exact TopCat.ext fun _ ↦ rfl) h u).symm
  have hpt : eqToHom (singularHomology_thomPair_eq (F := F) (E := E) A m).symm ≫
        (thomPair F E).capPushforward A (totalSpaceProj F E) n p m h u =
      (P₁.coconePointsIsoOfNatIso P₂ α).hom :=
    P₁.hom_ext fun s ↦ (hleg s).trans (P₁.comp_coconePointsIsoOfNatIso_hom P₂ α s).symm
  have hiso_comp : IsIso (eqToHom (singularHomology_thomPair_eq (F := F) (E := E) A m).symm ≫
      (thomPair F E).capPushforward A (totalSpaceProj F E) n p m h u) := by
    rw [hpt]
    exact (P₁.coconePointsIsoOfNatIso P₂ α).isIso_hom
  exact IsIso.of_isIso_comp_left
    (eqToHom (singularHomology_thomPair_eq (F := F) (E := E) A m).symm) _

/-- **The homology Thom isomorphism over an arbitrary base.** Let `E → B` be a real vector bundle
with finite-dimensional model fibre `F` of rank `r`, and `u ∈ Hʳ(E, E₀; K)` a Thom class. If the
product-bundle Thom map of a fibre generator `u₀` is bijective over open subsets of `B` for every
`K`-module and degree, then `TauCeti.homologyThomMap` of `u` is bijective in every degree for every
`K`-module `A`. -/
theorem bijective_homologyThomMap (A : ModuleCat.{w} K)
    {u₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu₀ : Submodule.span K {u₀} = ⊤)
    (hprod : ∀ (N : ModuleCat.{w} K) (U : Set B), IsOpen U → ∀ q,
      Function.Bijective ((prodThomPair ↥U F).pullbackCup N (prodThomPairProj ↥U F)
        (finrank ℝ F) q (q + finrank ℝ F) rfl
        (TopPair.singularCohomologyMap (prodThomPairSnd ↥U F) (finrank ℝ F) u₀)))
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E A (finrank ℝ F) p m h u) := by
  refine bijective_homologyThomMap_of_forall_bijective_homologyThomMap F E u (fun q k hk ↦ ?_) A h
  refine (ConcreteCategory.isIso_iff_bijective _).1
    (isIso_homologyThomMap_of_finiteTrivializingUnion (ModuleCat.of K K) hk u fun s ↦ ?_)
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  rw [TopCat.capPushforwardRestrict_apply]
  let P_s := thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)
  refine (P_s.forall_bijective_pullbackCup_iff_forall_bijective_capPushforward
    (TopCat.ofHom ((totalSpaceProj F E).hom.restrictPreimage _)) (finrank ℝ F)
    (fun _ hj ↦ isZero_singularHomology_thomPairOver_biUnion (ModuleCat.of K K) s
      (fun b _ ↦ (trivializationAt F E b).open_baseSet)
      (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) hj) _).1
    (fun N q' k' hk' ↦ ?_) q k hk
  have hbij := bijective_pullbackCupRestrict_totalSpaceProj_biUnion N s
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) hu₀ hk'
    (fun U hU r _ ↦ hprod N U hU r) hu
  rwa [TopCat.pullbackCupRestrict_apply] at hbij

/-- **The cohomology Thom isomorphism over an arbitrary base.** Let `E → B` be a real vector bundle
with finite-dimensional model fibre `F` of rank `r`, and `u ∈ Hʳ(E, E₀; K)` a Thom class. If the
product-bundle Thom map of a fibre generator `u₀` is bijective over open subsets of `B` for every
`K`-module and degree, then `TauCeti.thomMap` of `u` is bijective in every degree for every
`K`-module `M`. -/
theorem bijective_thomMap (M : ModuleCat.{w} K)
    {u₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu₀ : Submodule.span K {u₀} = ⊤)
    (hprod : ∀ (N : ModuleCat.{w} K) (U : Set B), IsOpen U → ∀ q,
      Function.Bijective ((prodThomPair ↥U F).pullbackCup N (prodThomPairProj ↥U F)
        (finrank ℝ F) q (q + finrank ℝ F) rfl
        (TopPair.singularCohomologyMap (prodThomPairSnd ↥U F) (finrank ℝ F) u₀)))
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) :=
  ((forall_bijective_thomMap_iff_forall_bijective_homologyThomMap F E u).2 fun _ _ hk ↦
    bijective_homologyThomMap (ModuleCat.of K K) hu₀ hprod hu hk) M p m h

end ArbitraryBase

end TauCeti
