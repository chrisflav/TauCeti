/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic
import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere

/-!
# The Thom isomorphism for a product bundle

Let `B` be a topological space, `F` a finite-dimensional real normed space of dimension `r`,
`K` a commutative ring, and `M` a `K`-module. This file proves the local (product-bundle) case of
the Thom isomorphism in singular cohomology: for any relative class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` whose restriction to each fibre pair `(F, F ∖ {0})`
generates `Hʳ(F, F ∖ {0}; K)`, the map

`Hᵖ(B; M) ⟶ Hᵐ(B × F, B × (F ∖ {0}); M)`,  `a ↦ π^* a ⌣ u`,  `p + r = m`,

(`TopPair.pullbackCup`) is bijective (`TauCeti.bijective_pullbackCup_prodThomPair`).

The proof proceeds in two steps. First, if *some* class `u₀` induces a bijection for all `M`, `p`,
and `m`, then any class `u` generating every fibre satisfies `u = π^* ε ⌣ u₀` for some
`ε ∈ H⁰(B; K)`. Restricting to the fibre over `b ∈ B` gives `u|_b = ε(b) • u₀|_b`; since
`Hʳ(F, F ∖ {0}; K) ≅ K` (`TauCeti.singularCohomologyComplSingletonFinrankEquivSelf`), the value
`ε(b)` is a unit in `K` at every point `b`. Hence `ε` is invertible for the cup product on
`H⁰(B; K)` (`TauCeti.exists_singularCup_eq_one`), so `a ↦ a ⌣ ε` is bijective and
`a ↦ π^* a ⌣ u = π^* (a ⌣ ε) ⌣ u₀` is bijective as well.

Second, we construct such a reference class `u₀` in all three rank regimes:
* `r = 0`: `F ∖ {0}` is empty, so `Hᵐ(B × F, ∅) ≅ Hᵐ(B × F) ≅ Hᵐ(B)` and the lift of
  `1 ∈ H⁰(B × F; K)` works.
* `r = 1`: fixing `e : F ≃L[ℝ] ℝ`, `B × (F ∖ {0})` is homotopy equivalent to `B ⊔ B`, so
  `Hⁿ(B × (F ∖ {0}); M)` decomposes via `π₀^* b + π₀^* c ⌣ σ` for the class `σ ∈ H⁰` equal to
  `1` on `e x > 0` and `0` on `e x < 0`; taking `u₀ = δ σ` reduces the cup product to the long
  exact sequence of the pair via `TopPair.singularCohomologyδ_singularCup`.
* `r = d + 2 ≥ 2`: fixing `e : F ≃L[ℝ] ℝᵈ⁺²`, taking
  `u₀ = δ (prodThomPairPuncturedClass K B e)` identifies `a ↦ π^* a ⌣ u₀` up to sign with
  `TauCeti.prodThomPairSingularCohomologySphereEquiv`, using
  `TopPair.singularCohomologyδ_singularCup` and graded commutativity
  (`TopCat.singularCup_gradedComm`).

## Main results

* `TauCeti.bijective_pullbackCup_prodThomPair`: for any relative class `u` on the Thom pair of a
  product bundle `B × F → B` whose restriction to every fibre generates `Hʳ(F, F ∖ {0}; K)`,
  the map `a ↦ π^* a ⌣ u` is bijective for every `K`-module `M` and every `p + r = m`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
-/

public section

noncomputable section

open CategoryTheory Limits Module MonoidalCategory

universe w

namespace TauCeti

variable {K : Type w} [CommRing K] {B : Type w} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-! ### Reduction from an arbitrary fibrewise generator to a single reference class -/

section Reduction

/-- Cup product on the right with `1 ∈ H⁰(X; K)` is the identity on `Hᵖ(X; M)`. -/
private theorem singularCup_singularCohomologyZeroOne_right_module (X : TopCat.{w})
    (M : ModuleCat.{w} K) {p : ℕ} (h : p + 0 = p)
    (a : X.singularCohomology (ModuleCat.of K K) K M p) :
    X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p h a
        (X.singularCohomologyZeroOne (k := K)) = a := by
  rw [TopCat.singularCohomologyZeroOne_def]
  exact X.singularCup_constSingularCocycle_right K (u := (λ_ _).inv) (μ := (ρ_ M).hom)
    (e := 𝟙 _) (η := 𝟙 _) (by simp [unitors_inv_equal]) (by simp) h a

/-- Cup product on the right with an invertible degree-zero class `ε ∈ H⁰(X; K)` is bijective
on `Hᵖ(X; M)`. -/
private theorem bijective_singularCup_right_of_exists_inv (X : TopCat.{w}) (M : ModuleCat.{w} K)
    (p : ℕ) (ε η : X.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0)
    (hεη : X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ (𝟙_ (ModuleCat.{w} K))).hom
      0 0 0 rfl ε η = X.singularCohomologyZeroOne)
    (hηε : X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ (𝟙_ (ModuleCat.{w} K))).hom
      0 0 0 rfl η ε = X.singularCohomologyZeroOne) :
    Function.Bijective fun a : X.singularCohomology (ModuleCat.of K K) K M p ↦
      X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (add_zero p) a ε := by
  let f : X.singularCohomology (ModuleCat.of K K) K M p →
      X.singularCohomology (ModuleCat.of K K) K M p := fun a ↦
    X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (add_zero p) a ε
  let g : X.singularCohomology (ModuleCat.of K K) K M p →
      X.singularCohomology (ModuleCat.of K K) K M p := fun a ↦
    X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (add_zero p) a η
  have hfg : ∀ a, f (g a) = a := fun a ↦ by
    dsimp only [f, g]
    rw [X.singularCup_assoc K (u₁₂ := (λ_ _).inv) (u := (λ_ _).inv) (u₂₃ := (λ_ _).inv)
      (u' := (λ_ _).inv) (μ₁₂ := (ρ_ M).hom) (μ := (ρ_ M).hom) (μ₂₃ := (λ_ _).hom)
      (μ' := (ρ_ M).hom) (m' := 0) (by monoidal) (by monoidal) (add_zero p) (add_zero p) rfl
      (add_zero p), hηε, singularCup_singularCohomologyZeroOne_right_module]
  have hgf : ∀ a, g (f a) = a := fun a ↦ by
    dsimp only [f, g]
    rw [X.singularCup_assoc K (u₁₂ := (λ_ _).inv) (u := (λ_ _).inv) (u₂₃ := (λ_ _).inv)
      (u' := (λ_ _).inv) (μ₁₂ := (ρ_ M).hom) (μ := (ρ_ M).hom) (μ₂₃ := (λ_ _).hom)
      (μ' := (ρ_ M).hom) (m' := 0) (by monoidal) (by monoidal) (add_zero p) (add_zero p) rfl
      (add_zero p), hεη, singularCup_singularCohomologyZeroOne_right_module]
  exact ⟨Function.LeftInverse.injective hgf, Function.RightInverse.surjective hfg⟩

/-- Replacing `u₀` by `π^* ε ⌣ u₀` factors `pullbackCup` through `a ↦ a ⌣ ε`. -/
private theorem pullbackCup_pullbackCup_zero (P : TopPair.{w}) {Z : TopCat.{w}} (π : P.fst ⟶ Z)
    (M : ModuleCat.{w} K) {r p m : ℕ} (h : p + r = m)
    (u₀ : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) r)
    (ε : Z.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0)
    (a : Z.singularCohomology (ModuleCat.of K K) K M p) :
    P.pullbackCup M π r p m h (P.pullbackCup (ModuleCat.of K K) π r 0 r (zero_add r) u₀ ε) a =
      P.pullbackCup M π r p m h u₀
        (Z.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (add_zero p)
          a ε) := by
  rw [TopPair.pullbackCup_apply, TopPair.pullbackCup_apply, TopPair.pullbackCup_apply,
    ← P.singularCup_assoc K (u₁₂ := (λ_ _).inv) (u := (λ_ _).inv) (u₂₃ := (λ_ _).inv)
      (u' := (λ_ _).inv) (μ₁₂ := (ρ_ M).hom) (μ := (ρ_ M).hom)
      (μ₂₃ := (ρ_ (ModuleCat.of K K)).hom) (μ' := (ρ_ M).hom)
      (by monoidal) (by monoidal) (add_zero p) h (zero_add r) h]
  exact congrArg
    (fun x ↦ P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p r m h x u₀)
    (TopCat.singularCup_naturality π K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p
      (add_zero p) a ε)

/-- If `a ↦ π^* a ⌣ u₀` is bijective for all coefficient modules and degrees, then the same
holds for every class `u` whose restriction to each fibre pair generates
`Hʳ(F, F ∖ {0}; K)`. -/
private theorem bijective_pullbackCup_prodThomPair_of_exists
    (u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu₀ : ∀ (N : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m),
      Function.Bijective ((prodThomPair B F).pullbackCup N (prodThomPairProj B F)
        (finrank ℝ F) p m h u₀))
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) := by
  obtain ⟨ε, hε⟩ := (hu₀ (ModuleCat.of K K) 0 (finrank ℝ F) (zero_add _)).2 u
  have hunit : ∀ b : B, IsUnit (singularCohomologyZeroEval b ε) := fun b ↦ by
    have hcomp : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
        TopCat.const b :=
      TopCat.ext fun (x : F) ↦ by
        change prodThomPairProj B F (TopPair.Hom.fst (prodThomPairFiberMap F b) x) = b
        rw [prodThomPairFiberMap_fst_apply, prodThomPairProj_apply]
    have hfib : TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u =
        singularCohomologyZeroEval b ε •
          TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u₀ := by
      rw [← hε, TopPair.pullbackCup_apply, ← TopPair.singularCup_naturality,
        ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hcomp,
        singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul,
        map_smul, LinearMap.smul_apply]
      congr 1
      rw [TopCat.singularCohomologyZeroOne_def]
      exact (TopPair.ofSubset (X := TopCat.of F)
          ({0}ᶜ : Set F)).singularCup_constSingularCocycle_left
        K (u := (λ_ _).inv) (μ := (ρ_ (𝟙_ (ModuleCat.{w} K))).hom) (e := 𝟙 _)
        (η := 𝟙 _) (by monoidal) (by monoidal) (zero_add _) _
    let eF := singularCohomologyComplSingletonFinrankEquivSelf (k := K) (ModuleCat.of K K)
      (OpenPartialHomeomorph.refl F) (Set.mem_univ (0 : F))
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1
      (Submodule.eq_top_iff'.1 (hu b) (eF.symm (1 : K)))
    have ha' : eF (TopPair.singularCohomologyMap
        (prodThomPairFiberMap F b) (finrank ℝ F) u) * a = 1 := by
      have := congrArg eF ha
      simpa [map_smul, smul_eq_mul, mul_comm] using this
    have hprod : IsUnit (eF (TopPair.singularCohomologyMap
        (prodThomPairFiberMap F b) (finrank ℝ F) u)) :=
      IsUnit.of_mul_eq_one a ha'
    rw [hfib, map_smul, smul_eq_mul] at hprod
    exact isUnit_of_mul_isUnit_left hprod
  obtain ⟨η, hεη, hηε⟩ := exists_singularCup_eq_one ε hunit
  have hfun : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) =
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u₀) ∘
        fun a ↦ (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
          p 0 p (add_zero p) a ε :=
    funext fun a ↦ by
      rw [← hε, Function.comp_apply, pullbackCup_pullbackCup_zero]
  rw [hfun]
  exact (hu₀ M p m h).comp
    (bijective_singularCup_right_of_exists_inv (TopCat.of B) M p ε η hεη hηε)

end Reduction

/-! ### Rank 0 -/

section RankZero

omit [FiniteDimensional ℝ F] in
/-- The map `π^* : Hᵖ(B; M) ⟶ Hᵖ(B × F; M)` is an isomorphism since `F` is contractible. -/
private theorem isIso_singularCohomologyMap_prodThomPairProj (M : ModuleCat.{w} K) (p : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := M)
      (prodThomPairProj B F) p) := by
  have hproj : TopCat.ofHom ContinuousMap.fst = prodThomPairProj B F :=
    TopCat.ext fun p ↦ (prodThomPairProj_apply F p).symm
  rw [← hproj]
  have := (ContinuousMap.HomotopyEquiv.prodContractible B F).isIso_singularCohomologyMap
    (ModuleCat.of K K) K M p
  rwa [ContinuousMap.HomotopyEquiv.prodContractible_toFun] at this

variable (B F) in
/-- When `dim F = 0`, the lift of `1 ∈ H⁰(B × F; K)` to `H⁰(B × F, ∅; K)` induces a
bijective `pullbackCup` in every degree and for every coefficient module. -/
private theorem exists_bijective_pullbackCup_prodThomPair_zero (hr : finrank ℝ F = 0) :
    ∃ u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0,
      ∀ (M : ModuleCat.{w} K) (p m : ℕ) (h : p + 0 = m),
        Function.Bijective
          ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h u₀) := by
  have : Subsingleton F := Module.finrank_zero_iff.1 hr
  have : IsEmpty (prodThomPair B F).snd := ⟨fun p ↦ p.2 (Subsingleton.elim p.1.2 0)⟩
  let u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0 :=
    inv ((prodThomPair B F).singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0)
      ((prodThomPair B F).fst.singularCohomologyZeroOne)
  refine ⟨u₀, fun M p m h ↦ ?_⟩
  have hm : p = m := by lia
  subst hm
  have hπ : IsIso ((prodThomPair B F).singularCohomologyπ (ModuleCat.of K K) K M p) :=
    inferInstance
  have hproj : IsIso (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := M)
      (prodThomPairProj B F) p) :=
    isIso_singularCohomologyMap_prodThomPairProj M p
  have hcomp : ((prodThomPair B F).singularCohomologyπ (ModuleCat.of K K) K M p) ∘
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p p h u₀) =
        TopCat.singularCohomologyMap (prodThomPairProj B F) p := funext fun a ↦ by
    simp only [Function.comp_apply, TopPair.pullbackCup_apply,
      TopPair.singularCohomologyπ_singularCup]
    have hu₀π : (prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K
        (𝟙_ (ModuleCat.{w} K)) 0 u₀ = (prodThomPair B F).fst.singularCohomologyZeroOne := by
      change ((prodThomPair B F).singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0)
          u₀ = _
      rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
    rw [hu₀π, singularCup_singularCohomologyZeroOne_right_module]
    rfl
  have hbijπ : Function.Bijective
      ((prodThomPair B F).singularCohomologyπ (ModuleCat.of K K) K M p) :=
    (asIso ((prodThomPair B F).singularCohomologyπ
      (ModuleCat.of K K) K M p)).toLinearEquiv.bijective
  have hbijproj : Function.Bijective
      (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := M)
        (prodThomPairProj B F) p) :=
    (asIso (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := M)
      (prodThomPairProj B F) p)).toLinearEquiv.bijective
  exact (Function.Bijective.of_comp_iff' hbijπ _).1 (hcomp.symm ▸ hbijproj)

end RankZero

/-! ### Rank 1 -/

section RankOne

/-- Forward map `B × (F ∖ {0}) ⟶ B ⊔ B` for a 1-dimensional fibre `e : F ≃L[ℝ] ℝ`. -/
private def prodThomPairPuncturedToFunOne (e : F ≃L[ℝ] ℝ) :
    C((prodThomPair B F).snd, TopCat.of (Σ _ : ULift.{w} Bool, TopCat.of B)) where
  toFun p := ⟨ULift.up (decide (0 < e p.1.2)), p.1.1⟩
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro p
    have hne : e p.1.2 ≠ 0 := fun h0 ↦ p.2 (e.injective (h0.trans e.map_zero.symm))
    have hcont_e : Continuous fun q : (prodThomPair B F).snd ↦ e q.1.2 :=
      e.continuous.comp (continuous_snd.comp continuous_subtype_val)
    have hcont_b : Continuous fun q : (prodThomPair B F).snd ↦ q.1.1 :=
      continuous_fst.comp continuous_subtype_val
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hopen : IsOpen {q : (prodThomPair B F).snd | e q.1.2 < 0} :=
        isOpen_lt hcont_e continuous_const
      refine (ContinuousAt.congr (f := fun q : (prodThomPair B F).snd ↦
          (⟨ULift.up false, q.1.1⟩ : Σ _ : ULift.{w} Bool, TopCat.of B)) ?_ ?_)
      · exact (continuous_sigmaMk.comp hcont_b).continuousAt
      · filter_upwards [hopen.mem_nhds hneg] with q hq
        have : ¬ (0 < e q.1.2) := not_lt.2 hq.le
        simp [this]
    · have hopen : IsOpen {q : (prodThomPair B F).snd | 0 < e q.1.2} :=
        isOpen_lt continuous_const hcont_e
      refine (ContinuousAt.congr (f := fun q : (prodThomPair B F).snd ↦
          (⟨ULift.up true, q.1.1⟩ : Σ _ : ULift.{w} Bool, TopCat.of B)) ?_ ?_)
      · exact (continuous_sigmaMk.comp hcont_b).continuousAt
      · filter_upwards [hopen.mem_nhds hpos] with q hq
        simp [hq]

/-- Inverse map `B ⊔ B ⟶ B × (F ∖ {0})` for a 1-dimensional fibre `e : F ≃L[ℝ] ℝ`. -/
private def prodThomPairPuncturedInvFunOne (e : F ≃L[ℝ] ℝ) :
    C(TopCat.of (Σ _ : ULift.{w} Bool, TopCat.of B), (prodThomPair B F).snd) where
  toFun s := ⟨(s.2, e.symm (if s.1.down then (1 : ℝ) else (-1 : ℝ))), by split_ifs <;> simp⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact continuous_sigma_iff.2 fun _ ↦ continuous_id
    · exact continuous_sigma_iff.2 fun i ↦
        continuous_const (y := e.symm (if i.down then (1 : ℝ) else (-1 : ℝ)))

/-- For `e : F ≃L[ℝ] ℝ`, `B × (F ∖ {0})` is homotopy equivalent to `B ⊔ B`, represented
as `Σ _ : ULift Bool, B`. -/
private def prodThomPairPuncturedHomotopyEquivOne (e : F ≃L[ℝ] ℝ) :
    ContinuousMap.HomotopyEquiv (prodThomPair B F).snd
      (TopCat.of (Σ _ : ULift.{w} Bool, TopCat.of B)) where
  toFun := prodThomPairPuncturedToFunOne e
  invFun := prodThomPairPuncturedInvFunOne e
  left_inv := Nonempty.intro
    { toFun := fun tp ↦
        ⟨(tp.2.1.1,
            (1 - (tp.1 : ℝ)) • e.symm (if 0 < e tp.2.1.2 then (1 : ℝ) else (-1 : ℝ)) +
              (tp.1 : ℝ) • tp.2.1.2), by
          intro hzero
          have he := congrArg e hzero
          rw [map_add, map_smul, map_smul, e.apply_symm_apply, map_zero,
            smul_eq_mul, smul_eq_mul] at he
          have ht0 : 0 ≤ (tp.1 : ℝ) := tp.1.2.1
          have ht1 : 0 ≤ 1 - (tp.1 : ℝ) := sub_nonneg.2 tp.1.2.2
          have hne : e tp.2.1.2 ≠ 0 := fun h0 ↦
            tp.2.2 (e.injective (h0.trans e.map_zero.symm))
          by_cases hpos : 0 < e tp.2.1.2
          · simp only [hpos, ↓reduceIte, mul_one] at he
            have : 0 < (1 - (tp.1 : ℝ)) + (tp.1 : ℝ) * e tp.2.1.2 := by
              rcases eq_or_lt_of_le ht0 with ht | ht
              · rw [← ht]; linarith
              · exact add_pos_of_nonneg_of_pos ht1 (mul_pos ht hpos)
            linarith
          · simp only [hpos, ↓reduceIte] at he
            have hneg : e tp.2.1.2 < 0 := lt_of_le_of_ne (not_lt.1 hpos) hne
            have : (1 - (tp.1 : ℝ)) * (-1) + (tp.1 : ℝ) * e tp.2.1.2 < 0 := by
              rcases eq_or_lt_of_le ht0 with ht | ht
              · rw [← ht]; linarith
              · exact add_neg_of_nonpos_of_neg (by linarith) (mul_neg_of_pos_of_neg ht hneg)
            linarith⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.prodMk
          (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)) ?_) _
        have hcont_t : Continuous fun tp : unitInterval × (prodThomPair B F).snd ↦
            (tp.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        have hcont_x : Continuous fun tp : unitInterval × (prodThomPair B F).snd ↦ tp.2.1.2 :=
          continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
        have hcont_sgn : Continuous fun tp : unitInterval × (prodThomPair B F).snd ↦
            e.symm (if 0 < e tp.2.1.2 then (1 : ℝ) else (-1 : ℝ)) := by
          rw [continuous_iff_continuousAt]
          intro tp
          have hne : e tp.2.1.2 ≠ 0 := fun h0 ↦
            tp.2.2 (e.injective (h0.trans e.map_zero.symm))
          have hcont_e : Continuous fun q : unitInterval × (prodThomPair B F).snd ↦
              e q.2.1.2 :=
            e.continuous.comp hcont_x
          rcases lt_or_gt_of_ne hne with hneg | hpos
          · refine ContinuousAt.congr (f := fun _ ↦ e.symm (-1)) continuousAt_const ?_
            filter_upwards [(isOpen_lt hcont_e continuous_const).mem_nhds hneg] with q hq
            simp [not_lt.2 hq.le]
          · refine ContinuousAt.congr (f := fun _ ↦ e.symm 1) continuousAt_const ?_
            filter_upwards [(isOpen_lt continuous_const hcont_e).mem_nhds hpos] with q hq
            simp [hq]
        exact ((continuous_const.sub hcont_t).smul hcont_sgn).add (hcont_t.smul hcont_x)
      map_zero_left := fun p ↦ by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · change (1 - (0 : ℝ)) • e.symm (if 0 < e p.1.2 then (1 : ℝ) else (-1 : ℝ)) +
              (0 : ℝ) • p.1.2 =
            e.symm (if decide (0 < e p.1.2) = true then (1 : ℝ) else (-1 : ℝ))
          by_cases h : 0 < e p.1.2 <;> simp [h]
      map_one_left := fun p ↦ by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · simp }
  right_inv := by
    have h : (prodThomPairPuncturedToFunOne (B := B) e).comp
        (prodThomPairPuncturedInvFunOne (B := B) e) = ContinuousMap.id _ :=
      ContinuousMap.ext fun ⟨⟨b⟩, x⟩ ↦ by
        change (⟨⟨decide (0 < e (e.symm (if b then (1 : ℝ) else (-1 : ℝ))))⟩, x⟩ :
            Σ _ : ULift.{w} Bool, TopCat.of B) = ⟨⟨b⟩, x⟩
        cases b <;> simp
    rw [h]

/-- For a limit fan over `ULift Bool` in `ModuleCat K`, pairing the two projections is bijective. -/
private lemma bijective_fan_uliftBool {P : ModuleCat.{w} K} {F : ULift.{w} Bool → ModuleCat.{w} K}
    {π : ∀ i, P ⟶ F i} (hc : IsLimit (Fan.mk P π)) :
    Function.Bijective fun z : P ↦ (π (ULift.up true) z, π (ULift.up false) z) := by
  refine ⟨fun z₁ z₂ hz ↦ ?_, fun ⟨a, b⟩ ↦ ?_⟩
  · have hhom : ModuleCat.ofHom (LinearMap.toSpanSingleton K P z₁) =
        ModuleCat.ofHom (LinearMap.toSpanSingleton K P z₂) := by
      refine Fan.IsLimit.hom_ext hc _ _ fun ⟨i⟩ ↦ ?_
      ext
      cases i
      · simpa using (Prod.ext_iff.1 hz).2
      · simpa using (Prod.ext_iff.1 hz).1
    simpa using ConcreteCategory.congr_hom hhom (1 : K)
  · let f : ∀ i : ULift.{w} Bool, ModuleCat.of K K ⟶ F i := fun i ↦
      match i with
      | ⟨true⟩ => ModuleCat.ofHom (LinearMap.toSpanSingleton K (F ⟨true⟩) a)
      | ⟨false⟩ => ModuleCat.ofHom (LinearMap.toSpanSingleton K (F ⟨false⟩) b)
    refine ⟨(Fan.IsLimit.lift hc f) (1 : K), Prod.ext ?_ ?_⟩
    · have h1 := ConcreteCategory.congr_hom (Fan.IsLimit.fac hc f (ULift.up true)) (1 : K)
      simpa [f] using h1
    · have h2 := ConcreteCategory.congr_hom (Fan.IsLimit.fac hc f (ULift.up false)) (1 : K)
      simpa [f] using h2

variable (B F) in
/-- When `dim F = 1`, there exists a class `u₀ ∈ H¹(B × F, B × (F ∖ {0}); K)` inducing a
bijective `pullbackCup` in every degree and for every coefficient module. -/
private theorem exists_bijective_pullbackCup_prodThomPair_one (hr : finrank ℝ F = 1) :
    ∃ u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 1,
      ∀ (M : ModuleCat.{w} K) (p m : ℕ) (h : p + 1 = m),
        Function.Bijective
          ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 1 p m h u₀) := by
  let e : F ≃L[ℝ] ℝ :=
    (LinearEquiv.ofFinrankEq F ℝ (by rw [hr, Module.finrank_self])).toContinuousLinearEquiv
  let P := prodThomPair B F
  let sPos : TopCat.of B ⟶ P.snd :=
    TopCat.ofHom ⟨fun b ↦ ⟨(b, e.symm 1), by simp⟩, by fun_prop⟩
  let sNeg : TopCat.of B ⟶ P.snd :=
    TopCat.ofHom ⟨fun b ↦ ⟨(b, e.symm (-1)), by simp⟩, by fun_prop⟩
  have hsPosProj : sPos ≫ prodThomPairPuncturedProj B F = 𝟙 (TopCat.of B) :=
    TopCat.ext fun b ↦ prodThomPairPuncturedProj_apply F (sPos b)
  have hsNegProj : sNeg ≫ prodThomPairPuncturedProj B F = 𝟙 (TopCat.of B) :=
    TopCat.ext fun b ↦ prodThomPairPuncturedProj_apply F (sNeg b)
  -- The locally constant class `σ ∈ H⁰(B × (F ∖ {0}); K)` equal to `1` on `e x > 0` and `0`
  -- on `e x < 0`.
  have hσ_loc : ∀ p q : P.snd, Joined p q →
      (if 0 < e p.1.2 then (1 : K) else 0) = (if 0 < e q.1.2 then (1 : K) else 0) := by
    intro p q ⟨γ⟩
    have hcont : Continuous (fun t : unitInterval ↦ e (γ t).1.2) :=
      e.continuous.comp (continuous_snd.comp (continuous_subtype_val.comp γ.continuous))
    have hne : ∀ t : unitInterval, e (γ t).1.2 ≠ 0 := fun t h0 ↦
      (γ t).2 (e.injective (h0.trans e.map_zero.symm))
    have hsign : (0 < e p.1.2) ↔ (0 < e q.1.2) := by
      have hconn : _root_.IsConnected (Set.range (fun t : unitInterval ↦ e (γ t).1.2)) :=
        isConnected_range hcont
      have hzero : (0 : ℝ) ∉ Set.range (fun t : unitInterval ↦ e (γ t).1.2) := by
        rintro ⟨t, ht⟩
        exact hne t ht
      have hmemp : e p.1.2 ∈ Set.range (fun t : unitInterval ↦ e (γ t).1.2) :=
        ⟨0, by simp⟩
      have hmemq : e q.1.2 ∈ Set.range (fun t : unitInterval ↦ e (γ t).1.2) :=
        ⟨1, by simp⟩
      constructor <;> intro hpos
      · by_contra hle
        have hlt : e q.1.2 < 0 := lt_of_le_of_ne (not_lt.1 hle)
          (fun h0 ↦ q.2 (e.injective (h0.trans e.map_zero.symm)))
        exact hzero (hconn.isPreconnected.Icc_subset hmemq hmemp ⟨hlt.le, hpos.le⟩)
      · by_contra hle
        have hlt : e p.1.2 < 0 := lt_of_le_of_ne (not_lt.1 hle)
          (fun h0 ↦ p.2 (e.injective (h0.trans e.map_zero.symm)))
        exact hzero (hconn.isPreconnected.Icc_subset hmemp hmemq ⟨hlt.le, hpos.le⟩)
    simp only [hsign]
  obtain ⟨σ, hσ⟩ := exists_singularCohomologyZeroEval_eq (k := K) (X := P.snd)
    (fun p ↦ if 0 < e p.1.2 then (1 : K) else 0) hσ_loc
  have hσPos : TopCat.singularCohomologyMap sPos 0 σ = (TopCat.of B).singularCohomologyZeroOne :=
    singularCohomologyZero_ext fun b ↦ by
      rw [singularCohomologyZeroEval_naturality, hσ,
        singularCohomologyZeroEval_singularCohomologyZeroOne]
      change (if 0 < e (e.symm 1) then (1 : K) else 0) = 1
      simp
  have hσNeg : TopCat.singularCohomologyMap sNeg 0 σ = 0 :=
    singularCohomologyZero_ext fun b ↦ by
      rw [singularCohomologyZeroEval_naturality, hσ, map_zero]
      change (if 0 < e (e.symm (-1)) then (1 : K) else 0) = 0
      simp
  -- For every `M` and `n`, `Hⁿ(B × (F ∖ {0}); M) ≃ Hⁿ(B; M) × Hⁿ(B; M)` via
  -- `(sPos^*, sNeg^*)`.
  have hbijective_eval (M : ModuleCat.{w} K) (n : ℕ) :
      Function.Bijective fun y : P.snd.singularCohomology (ModuleCat.of K K) K M n ↦
        (TopCat.singularCohomologyMap sPos n y, TopCat.singularCohomologyMap sNeg n y) := by
    let heq := prodThomPairPuncturedHomotopyEquivOne (B := B) e
    have hinvIso : IsIso (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := M)
        (TopCat.ofHom heq.invFun) n) :=
      heq.symm.isIso_singularCohomologyMap (ModuleCat.of K K) K M n
    let X₁ : ULift.{w} Bool → TopCat.{w} := fun _ ↦ TopCat.of B
    have hfanBij := bijective_fan_uliftBool
      (isLimitFanSingularCohomology X₁ (ModuleCat.{w} K) (ModuleCat.of K K) K M n)
    have hsPosEq : sPos = TopCat.sigmaι X₁ (ULift.up true) ≫ TopCat.ofHom heq.invFun :=
      TopCat.ext fun b ↦ Subtype.ext (Prod.ext rfl (by
        change e.symm 1 = e.symm (if true then (1 : ℝ) else (-1 : ℝ))
        simp))
    have hsNegEq : sNeg = TopCat.sigmaι X₁ (ULift.up false) ≫ TopCat.ofHom heq.invFun :=
      TopCat.ext fun b ↦ Subtype.ext (Prod.ext rfl (by
        change e.symm (-1) = e.symm (if false then (1 : ℝ) else (-1 : ℝ))
        simp))
    have hcomp : (fun y : P.snd.singularCohomology (ModuleCat.of K K) K M n ↦
          (TopCat.singularCohomologyMap sPos n y, TopCat.singularCohomologyMap sNeg n y)) =
        (fun z ↦ (TopCat.singularCohomologyMap (TopCat.sigmaι X₁ (ULift.up true)) n z,
            TopCat.singularCohomologyMap (TopCat.sigmaι X₁ (ULift.up false)) n z)) ∘
          TopCat.singularCohomologyMap (TopCat.ofHom heq.invFun) n := funext fun y ↦ by
      simp only [hsPosEq, hsNegEq, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
      rfl
    rw [hcomp]
    exact hfanBij.comp
      (asIso (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := M)
        (TopCat.ofHom heq.invFun) n)).toLinearEquiv.bijective
  -- Decomposition `(b, c) ↦ π_0^* b + π_0^* c ⌣ σ` is bijective on
  -- `Hⁿ(B × (F ∖ {0}); M)`.
  let D (M : ModuleCat.{w} K) (n : ℕ) :
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K M n ×
          (TopCat.of B).singularCohomology (ModuleCat.of K K) K M n →
        P.snd.singularCohomology (ModuleCat.of K K) K M n := fun bc ↦
    TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.1 +
      P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom n 0 n (add_zero n)
        (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) σ
  have hD_bij (M : ModuleCat.{w} K) (n : ℕ) : Function.Bijective (D M n) := by
    have hcomp : (fun y : P.snd.singularCohomology (ModuleCat.of K K) K M n ↦
          (TopCat.singularCohomologyMap sPos n y, TopCat.singularCohomologyMap sNeg n y)) ∘
          D M n = fun bc ↦ (bc.1 + bc.2, bc.1) := funext fun ⟨b, c⟩ ↦ by
      simp only [Function.comp_apply, D, map_add, ← TopCat.singularCup_naturality,
        ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
        hsPosProj, hsNegProj, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
        hσPos, hσNeg, map_zero, add_zero]
      rw [singularCup_singularCohomologyZeroOne_right_module]
    have hshear : Function.Bijective
        (fun bc : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M n ×
            (TopCat.of B).singularCohomology (ModuleCat.of K K) K M n ↦ (bc.1 + bc.2, bc.1)) :=
      ⟨fun ⟨b₁, c₁⟩ ⟨b₂, c₂⟩ h ↦ by
          have hb : b₁ = b₂ := congrArg Prod.snd h
          have hc : c₁ = c₂ := add_left_cancel (hb ▸ congrArg Prod.fst h)
          exact Prod.ext hb hc,
        fun ⟨u, v⟩ ↦ ⟨(v, u - v), Prod.ext (add_sub_cancel v u) rfl⟩⟩
    exact (Function.Bijective.of_comp_iff' (hbijective_eval M n) (D M n)).1
      (hcomp.symm ▸ hshear)
  -- Take `u₀ = δ σ ∈ H¹(B × F, B × (F ∖ {0}); K)`.
  let u₀ : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 1 :=
    P.singularCohomologyδ (ModuleCat.of K K) K (ModuleCat.of K K) 0 1 rfl σ
  refine ⟨u₀, fun M p m h ↦ ?_⟩
  subst h
  have hPmap : P.map ≫ prodThomPairProj B F = prodThomPairPuncturedProj B F :=
    map_comp_prodThomPairProj F
  have hproj_bij (n : ℕ) : Function.Bijective
      (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := M)
        (prodThomPairProj B F) n) := by
    have := isIso_singularCohomologyMap_prodThomPairProj (K := K) (B := B) (F := F) M n
    exact (asIso (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := M)
      (prodThomPairProj B F) n)).toLinearEquiv.bijective
  have hproj0_inj (n : ℕ) : Function.Injective
      (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := M)
        (prodThomPairPuncturedProj B F) n) :=
    Function.LeftInverse.injective (g := TopCat.singularCohomologyMap sPos n) fun b ↦ by
      rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hsPosProj,
        TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]
  -- Compare `a ↦ π^* a ⌣ δ σ` with `a ↦ δ (π_0^* a ⌣ σ)` up to `(-1)^p`.
  let g : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p →
      P.singularCohomology (ModuleCat.of K K) K M (p + 1) := fun a ↦
    P.singularCohomologyδ (ModuleCat.of K K) K M p (p + 1) rfl (D M p (0, a))
  have hformula (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
      g a = ((-1 : ℤ) ^ p) • P.pullbackCup M (prodThomPairProj B F) 1 p (p + 1) rfl u₀ a := by
    have hD0 : D M p (0, a) =
        P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (add_zero p)
          (TopCat.singularCohomologyMap P.map p
            (TopCat.singularCohomologyMap (prodThomPairProj B F) p a)) σ := by
      simp only [D, map_zero, zero_add, ← ConcreteCategory.comp_apply,
        ← TopCat.singularCohomologyMap_comp, hPmap]
    rw [show g a = P.singularCohomologyδ (ModuleCat.of K K) K M p (p + 1) rfl (D M p (0, a)) from
      rfl, hD0, TopPair.singularCohomologyδ_singularCup K P _ _ (h := add_zero p) (hq := rfl)
      (hm := rfl) (h' := rfl), TopPair.pullbackCup_apply]
  have hg_bij : Function.Bijective g := by
    refine ⟨fun a₁ a₂ ha ↦ ?_, fun z ↦ ?_⟩
    · have hsub : g (a₁ - a₂) = 0 := by
        rw [hformula, hformula] at ha
        rw [hformula, map_sub, smul_sub, sub_eq_zero]
        exact ha
      obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
        (P.singularCohomology_exact_subspace (ModuleCat.of K K) K M p (p + 1)) _ hsub
      obtain ⟨b, rfl⟩ := (hproj_bij p).2 y
      have hDb0 : D M p (b, 0) =
          TopCat.singularCohomologyMap P.map p
            (TopCat.singularCohomologyMap (prodThomPairProj B F) p b) := by
        simp only [D, map_zero, LinearMap.zero_apply, add_zero, ← ConcreteCategory.comp_apply,
          ← TopCat.singularCohomologyMap_comp, hPmap]
      rw [← hDb0] at hy
      have heq : a₁ - a₂ = 0 := congrArg Prod.snd ((hD_bij M p).1 hy).symm
      exact sub_eq_zero.1 heq
    · obtain ⟨b, hb⟩ :=
        (hproj_bij (p + 1)).2 (P.singularCohomologyπ (ModuleCat.of K K) K M _ z)
      have hπ : P.singularCohomologyπ (ModuleCat.of K K) K M (p + 1) z = 0 := by
        have h0 := ConcreteCategory.congr_hom
          (P.singularCohomologyπ_comp_singularCohomologyMap (ModuleCat.of K K) K M (p + 1)) z
        rw [ConcreteCategory.comp_apply, ← hb, ← ConcreteCategory.comp_apply,
          ← TopCat.singularCohomologyMap_comp, hPmap] at h0
        rw [← hb, hproj0_inj (p + 1) (h0.trans (map_zero _).symm), map_zero]
      obtain ⟨x, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
        (P.singularCohomology_exact_relative (ModuleCat.of K K) K M p (p + 1)) z hπ
      obtain ⟨⟨b', c⟩, rfl⟩ := (hD_bij M p).2 x
      refine ⟨c, ?_⟩
      have hδb :
          P.singularCohomologyδ (ModuleCat.of K K) K M p (p + 1) rfl (D M p (b', 0)) = 0 := by
        have hDb0 : D M p (b', 0) =
            TopCat.singularCohomologyMap P.map p
              (TopCat.singularCohomologyMap (prodThomPairProj B F) p b') := by
          simp only [D, map_zero, LinearMap.zero_apply, add_zero, ← ConcreteCategory.comp_apply,
            ← TopCat.singularCohomologyMap_comp, hPmap]
        rw [hDb0, ← ConcreteCategory.comp_apply,
          P.singularCohomologyMap_comp_singularCohomologyδ (ModuleCat.of K K) K M p (p + 1)]
        simp
      have hsum : D M p (b', c) = D M p (b', 0) + D M p (0, c) := by
        simp [D]
      rw [hsum, map_add, hδb, zero_add]
  have hsign : Function.Bijective (fun z : P.singularCohomology (ModuleCat.of K K) K M (p + 1) ↦
      ((-1 : ℤ) ^ p) • z) :=
    ⟨fun x y hxy ↦ by
        have := congrArg (((-1 : ℤ) ^ p) • ·) hxy
        simpa [smul_smul, ← mul_pow] using this,
      fun y ↦ ⟨((-1 : ℤ) ^ p) • y, by simp [smul_smul, ← mul_pow]⟩⟩
  have hcomp : (fun z ↦ ((-1 : ℤ) ^ p) • z) ∘
      (P.pullbackCup M (prodThomPairProj B F) 1 p (p + 1) rfl u₀) = g :=
    funext fun a ↦ (hformula a).symm
  exact (Function.Bijective.of_comp_iff' hsign _).1 (hcomp.symm ▸ hg_bij)

end RankOne

/-! ### Rank ≥ 2 -/

section RankAtLeastTwo

variable (B F) in
/-- When `dim F = d + 2`, `δ (prodThomPairPuncturedClass K B e)` induces a bijective `pullbackCup`
in every degree and for every coefficient module, matching
`TauCeti.prodThomPairSingularCohomologySphereEquiv` up to sign. -/
private theorem exists_bijective_pullbackCup_prodThomPair_succ_succ {d : ℕ}
    (hr : finrank ℝ F = d + 2) :
    ∃ u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
        (d + 2),
      ∀ (M : ModuleCat.{w} K) (p m : ℕ) (h : p + (d + 2) = m),
        Function.Bijective
          ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h u₀) := by
  let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    (LinearEquiv.ofFinrankEq F (EuclideanSpace ℝ (Fin (d + 2)))
      (by rw [hr, finrank_euclideanSpace_fin])).toContinuousLinearEquiv
  let σ := prodThomPairPuncturedClass K B e
  let u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (d + 2) :=
    (prodThomPair B F).singularCohomologyδ (ModuleCat.of K K) K (ModuleCat.of K K) (d + 1) (d + 2)
      rfl σ
  refine ⟨u₀, fun M p m h ↦ ?_⟩
  have hformula (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
      prodThomPairSingularCohomologySphereEquiv M B e p m h a =
        ((-1 : ℤ) ^ (p * (d + 1) + p)) •
          (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h u₀ a := by
    rw [prodThomPairSingularCohomologySphereEquiv_apply]
    have hcomm : (prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv
        (λ_ M).hom (d + 1) p (d + 1 + p) rfl σ
        (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a) =
      ((-1 : ℤ) ^ (p * (d + 1))) •
        (prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
          p (d + 1) (d + 1 + p) (add_comm p (d + 1))
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a) σ :=
      (prodThomPair B F).snd.singularCup_gradedComm K
        (by rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal])
        (by rw [braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id, Category.comp_id])
        (add_comm p (d + 1)) _ σ
    rw [hcomm, map_zsmul]
    have hproj : TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (prodThomPairPuncturedProj B F) p a =
        TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (prodThomPair B F).map p
          (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K))
            (prodThomPairProj B F) p a) := by
      rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
        map_comp_prodThomPairProj]
    rw [hproj, TopPair.singularCohomologyδ_singularCup K (prodThomPair B F) _ _
      (h := add_comm p (d + 1)) (hq := rfl) (hm := by lia) (h' := h), smul_smul, ← pow_add,
      TopPair.pullbackCup_apply]
  have hsign : Function.Bijective (fun z : (prodThomPair B F).singularCohomology
      (ModuleCat.of K K) K M m ↦ ((-1 : ℤ) ^ (p * (d + 1) + p)) • z) :=
    ⟨fun x y hxy ↦ by
        have := congrArg (((-1 : ℤ) ^ (p * (d + 1) + p)) • ·) hxy
        simpa [smul_smul, ← mul_pow] using this,
      fun y ↦ ⟨((-1 : ℤ) ^ (p * (d + 1) + p)) • y, by simp [smul_smul, ← mul_pow]⟩⟩
  have hcomp : (fun z ↦ ((-1 : ℤ) ^ (p * (d + 1) + p)) • z) ∘
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h u₀) =
      ⇑(prodThomPairSingularCohomologySphereEquiv M B e p m h) :=
    funext fun a ↦ (hformula a).symm
  exact (Function.Bijective.of_comp_iff' hsign _).1
    (hcomp.symm ▸ (prodThomPairSingularCohomologySphereEquiv M B e p m h).bijective)

end RankAtLeastTwo

/-! ### The product-bundle Thom isomorphism -/

/-- **The Thom isomorphism for a product bundle**: for a finite-dimensional real normed space `F`
of dimension `r` and any relative class `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` whose restriction
to every fibre generates `Hʳ(F, F ∖ {0}; K)`, the map `a ↦ π^* a ⌣ u` is bijective from
`Hᵖ(B; M)` to `Hᵐ(B × F, B × (F ∖ {0}); M)` for every `K`-module `M` and `p + r = m`. -/
theorem bijective_pullbackCup_prodThomPair (M : ModuleCat.{w} K)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    (p m : ℕ) (h : p + finrank ℝ F = m) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) := by
  have hex : ∀ r : ℕ, finrank ℝ F = r →
      ∃ u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) r,
        ∀ (N : ModuleCat.{w} K) (q n : ℕ) (hq : q + r = n),
          Function.Bijective
            ((prodThomPair B F).pullbackCup N (prodThomPairProj B F) r q n hq u₀) := by
    intro r hr
    cases r with
    | zero => exact exists_bijective_pullbackCup_prodThomPair_zero B F hr
    | succ r' =>
      cases r' with
      | zero => exact exists_bijective_pullbackCup_prodThomPair_one B F hr
      | succ d => exact exists_bijective_pullbackCup_prodThomPair_succ_succ B F hr
  obtain ⟨u₀, hu₀⟩ := hex (finrank ℝ F) rfl
  exact bijective_pullbackCup_prodThomPair_of_exists u₀ hu₀ u hu M p m h

end TauCeti
