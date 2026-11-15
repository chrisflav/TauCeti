/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Basic
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere

/-!
# The Thom isomorphism for a product bundle

Let `B` be a topological space, `F` a finite-dimensional real normed space of dimension `r`, `K` a
commutative ring, and `M` a `K`-module. For a relative class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` whose restriction to the fibre pair `(F, F ∖ {0})` over every
point of `B` generates `Hʳ(F, F ∖ {0}; K)`, pulling back along the projection
`π : B × F → B` (`TauCeti.prodThomPairProj`) and taking the cup product with `u` gives a `K`-linear
equivalence

`Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)`,  `a ↦ π^*a ⌣ u`,  `p + r = m`

(`TauCeti.bijective_pullbackCup_prodThomPairProj`, `TauCeti.prodThomPairPullbackCupEquiv`). This is
the local, product-bundle step in the Mayer–Vietoris proof of the Thom isomorphism
(Milnor and Stasheff, Theorem 10.4; Hatcher, Theorem 4D.10), covering all ranks `r ≥ 0` and any
fibrewise-generating class `u` rather than only a class pulled back from `F`.

The proof first constructs one model class `g₀ ∈ Hʳ(F, F ∖ {0}; K)` whose pullback `u₀` along the
second projection has bijective `TopPair.pullbackCup` for every `B` and `M`, splitting by rank:

* for `r = 0`, `F ∖ {0}` is empty, so relative cohomology is absolute cohomology and `u₀` is the
  unit class lifted across `TopPair.isIso_singularCohomologyπ_of_isEmpty`;
* for `r = 1`, `B × (F ∖ {0})` splits into two disjoint open half-products `B × F₊` and `B × F₋`,
  each homotopy equivalent to `B`, so Mayer–Vietoris decomposes `Hᵖ(B × (F ∖ {0}); M)` as
  `π₀^* Hᵖ(B; M) ⊕ (π₀^* Hᵖ(B; M) ⌣ σ)` for the indicator class `σ ∈ H⁰(B × (F ∖ {0}); K)` of the
  positive half, and the long exact sequence of the pair identifies `a ↦ δ (π₀^* a ⌣ σ)` with
  `(-1)ᵖ (π^* a ⌣ δ σ)` via `TopPair.singularCohomologyδ_singularCup`;
* for `r = d + 2 ≥ 2`, `TauCeti.prodThomPairSingularCohomologySphereEquiv` already shows that
  `a ↦ δ (σ ⌣ π₀^* a)` is bijective, and graded commutativity together with
  `TopPair.singularCohomologyδ_singularCup` identifies it up to sign with `a ↦ π^* a ⌣ δ σ`.

Any class `u` generating every fibre then has the form `u = π^* ε ⌣ u₀` for a degree-zero class
`ε ∈ H⁰(B; K)` whose point evaluations are units of `K`, so `ε` is invertible for the cup product
(`TauCeti.exists_singularCup_eq_one`) and `a ↦ π^* a ⌣ u = π^* (a ⌣ ε) ⌣ u₀` is bijective.

## Main definitions and results

* `TauCeti.bijective_pullbackCup_prodThomPairProj`: `a ↦ π^*a ⌣ u` is bijective in every degree
  whenever `u` generates every fibre.
* `TauCeti.bijective_pullbackCup_prodThomPairSnd`: special case for the pullback of a generator of
  `Hʳ(F, F ∖ {0}; K)` along the second projection.
* `TauCeti.prodThomPairPullbackCupEquiv`: the resulting `K`-linear equivalence
  `Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
-/

public section

noncomputable section

open CategoryTheory Limits Module MonoidalCategory

universe w

namespace TauCeti

section DisjointMayerVietoris

variable {C : Type*} [Category.{w} C] [HasCoproducts.{w} C] [Abelian C]
  (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)

/-- For a cover of `X` by two disjoint open sets `U` and `V`, the Mayer–Vietoris restriction map
`Hⁿ(X) ⟶ Hⁿ(U) ⊞ Hⁿ(V)` is an isomorphism in every degree. -/
private theorem isIso_singularCohomologyMayerVietorisToBiprod_of_isEmpty {X : TopCat.{w}}
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    [IsEmpty ↥(U ∩ V)] (n : ℕ) :
    IsIso (TopCat.singularCohomologyMayerVietorisToBiprod R k M U V n) := by
  have hzero := isZero_singularCohomology_of_isEmpty R k M (TopCat.of ↥(U ∩ V))
  have : Epi (TopCat.singularCohomologyMayerVietorisToBiprod R k M U V n) :=
    (TopCat.singularCohomologyMayerVietoris_exact₂ R k M hU hV hUV n).epi_f
      ((hzero n).eq_of_tgt _ _)
  have : Mono (TopCat.singularCohomologyMayerVietorisToBiprod R k M U V n) := by
    cases n with
    | zero => exact TopCat.mono_singularCohomologyMayerVietorisToBiprod_zero R k M hU hV hUV
    | succ m =>
      exact (TopCat.singularCohomologyMayerVietoris_exact₁ R k M hU hV hUV m (m + 1) rfl).mono_g
        ((hzero m).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

end DisjointMayerVietoris

namespace ProdThomPairPullbackCup

variable {K : Type w} [CommRing K]

/-! ### Rank zero -/

section RankZero

private theorem isIso_singularCohomologyMap_of_isIso {R M : ModuleCat.{w} K}
    {X Y : TopCat.{w}} (f : X ⟶ Y) [IsIso f] (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := K) (M := M) f n) := by
  refine ⟨TopCat.singularCohomologyMap (inv f) n, ?_, ?_⟩
  · rw [← TopCat.singularCohomologyMap_comp, IsIso.inv_hom_id, TopCat.singularCohomologyMap_id]
  · rw [← TopCat.singularCohomologyMap_comp, IsIso.hom_inv_id, TopCat.singularCohomologyMap_id]

/-- Tensor-unit version of `exists_model_bijective_of_subsingleton`. -/
private theorem exists_model_bijective_of_subsingleton_unit (F : Type w) [TopologicalSpace F]
    [Zero F] [Subsingleton F] :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0,
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ) (h : p + 0 = m),
        Function.Bijective (fun c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p ↦
          (prodThomPair B F).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
            p 0 m h (TopCat.singularCohomologyMap (prodThomPairProj B F) p c)
            (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g₀)) := by
  let Q := TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)
  have : IsEmpty Q.snd := ⟨fun x ↦ x.2 (Subsingleton.elim x.1 0)⟩
  let oneF : Q.fst.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 :=
    (Q.fst.singularCochainComplex (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))).homologyπ 0
      (Q.fst.constSingularCocycle K (𝟙 (𝟙_ (ModuleCat.{w} K))))
  obtain ⟨g₀, hπ_g₀⟩ :
      ∃ g₀ : Q.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0,
        Q.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 g₀ = oneF :=
    ⟨inv (Q.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0) oneF,
      IsIso.inv_hom_id_apply _ _⟩
  refine ⟨g₀, fun B _ M p m h ↦ ?_⟩
  obtain rfl : p = m := (Nat.add_zero p).symm.trans h
  let P := prodThomPair B F
  have : IsEmpty P.snd := ⟨fun x ↦ x.2 (Subsingleton.elim x.1.2 0)⟩
  have : Unique F := uniqueOfSubsingleton (0 : F)
  have hu₀ : P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g₀) =
      (P.fst.singularCochainComplex (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))).homologyπ 0
        (P.fst.constSingularCocycle K (𝟙 (𝟙_ (ModuleCat.{w} K)))) := by
    have hnat := ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality
      (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := 𝟙_ (ModuleCat.{w} K)) (prodThomPairSnd B F) 0) g₀
    simp only [ConcreteCategory.comp_apply] at hnat
    exact hnat.symm.trans ((congrArg _ hπ_g₀).trans
      (TopCat.singularCohomologyMap_homologyπ_constSingularCocycle _ K (𝟙 (𝟙_ (ModuleCat.{w} K)))))
  have hcomp : ⇑(P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p) ∘
      (fun a ↦ P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p h
        (TopCat.singularCohomologyMap (prodThomPairProj B F) p a)
        (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g₀)) =
      ⇑(TopCat.singularCohomologyMap (prodThomPairProj B F) p) := by
    funext a
    rw [Function.comp_apply, TopPair.singularCohomologyπ_singularCup, hu₀]
    exact P.fst.singularCup_constSingularCocycle_right K (η := 𝟙 (𝟙_ (ModuleCat.{w} K)))
      (by monoidal) (by monoidal) h _
  let isoB : P.fst ≅ TopCat.of B := TopCat.isoOfHomeo (Homeomorph.prodUnique B F)
  have hproj : prodThomPairProj B F = isoB.hom :=
    TopCat.ext fun x ↦ prodThomPairProj_apply F x
  have hbij_proj : Function.Bijective
      (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (prodThomPairProj B F) p) := by
    rw [hproj]
    have := isIso_singularCohomologyMap_of_isIso (R := 𝟙_ (ModuleCat.{w} K)) (M := M) isoB.hom p
    exact (asIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      isoB.hom p)).toLinearEquiv.bijective
  have hbij_π : Function.Bijective (P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p) :=
    (asIso (P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p)).toLinearEquiv.bijective
  rw [← Function.Bijective.of_comp_iff' hbij_π, hcomp]
  exact hbij_proj

/-- When `F` is a subsingleton, `F ∖ {0}` is empty and the inverse of
`TopPair.isIso_singularCohomologyπ_of_isEmpty` gives a class on `(F, F ∖ {0})` whose pullback to
`prodThomPair B F` has bijective `TopPair.pullbackCup` in every degree. -/
private theorem exists_model_bijective_of_subsingleton (F : Type w) [TopologicalSpace F] [Zero F]
    [Subsingleton F] :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) 0,
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ) (h : p + 0 = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g₀)) := by
  obtain ⟨g₀, hg₀⟩ := exists_model_bijective_of_subsingleton_unit (K := K) F
  refine ⟨g₀, fun B _ M p m h ↦ ?_⟩
  have hfun : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g₀)) = _ :=
    funext ((prodThomPair B F).pullbackCup_apply _ h _)
  rw [hfun]
  exact hg₀ B M p m h

end RankZero

/-! ### Rank one -/

section RankOne

private lemma prodThomPairSnd_snd_val {B F : Type w} [TopologicalSpace B] [TopologicalSpace F]
    [Zero F] (p : (prodThomPair B F).snd) :
    (TopPair.Hom.snd (prodThomPairSnd B F) p).1 = p.1.2 :=
  (ConcreteCategory.congr_hom (TopPair.Hom.w (prodThomPairSnd B F)) p).trans
    (prodThomPairSnd_fst_apply F p.1)

/-- Given a nonzero vector `v ∈ F`, `prodThomPairPuncturedProj B F` has a section and therefore
induces an injection in cohomology. -/
private theorem injective_singularCohomologyMap_prodThomPairPuncturedProj {B F : Type w}
    [TopologicalSpace B] [TopologicalSpace F] [Zero F] (M : ModuleCat.{w} K) {v : F} (hv : v ≠ 0)
    (q : ℕ) :
    Function.Injective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (prodThomPairPuncturedProj B F) q) := by
  let s : TopCat.of B ⟶ (prodThomPair B F).snd := TopCat.ofHom ⟨fun b ↦ ⟨(b, v), hv⟩, by fun_prop⟩
  have hs : s ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
    TopCat.ext fun b ↦ prodThomPairPuncturedProj_apply F (s b)
  refine Function.LeftInverse.injective (g := TopCat.singularCohomologyMap s q) fun b ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hs,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On `F ∖ {0}` for `e : F ≃L[ℝ] ℝ`, the indicator of `{x | 0 < e x}` is locally constant, hence
is the point-evaluation function of a degree-zero cohomology class. -/
private theorem exists_rankOnePuncturedClass (e : F ≃L[ℝ] ℝ) :
    ∃ σ₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).snd.singularCohomology
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0,
      ∀ x : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).snd,
        singularCohomologyZeroEval x σ₀ = if 0 < e x.1 then 1 else 0 := by
  let X := (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).snd
  let Upos : Set X := {x | 0 < e x.1}
  have hUpos_open : IsOpen Upos :=
    isOpen_lt continuous_const (e.continuous.comp continuous_subtype_val)
  have hUneg_open : IsOpen {x : X | e x.1 < 0} :=
    isOpen_lt (e.continuous.comp continuous_subtype_val) continuous_const
  have hcompl : {x : X | e x.1 < 0}ᶜ = Upos :=
    Set.ext fun x ↦ by
      -- Unfold set-builder membership in `{x | e x.1 < 0}ᶜ` and `Upos` to inequalities on `e x.1`.
      change ¬ e x.1 < 0 ↔ 0 < e x.1
      exact not_lt.trans ⟨fun h ↦ h.lt_of_ne' ((map_ne_zero_iff e e.injective).2 x.2), le_of_lt⟩
  have hclopen : IsClopen Upos := ⟨hcompl ▸ hUneg_open.isClosed_compl, hUpos_open⟩
  refine exists_singularCohomologyZeroEval_eq (fun x : X ↦ if x ∈ Upos then (1 : K) else 0)
    fun x y ⟨γ⟩ ↦ ?_
  have hmem : x ∈ Upos ↔ y ∈ Upos := by
    constructor <;> intro h
    · have huniv := (hclopen.preimage γ.continuous).eq_univ ⟨0, by simpa using h⟩
      have h1 : (1 : unitInterval) ∈ γ ⁻¹' Upos := huniv ▸ Set.mem_univ 1
      simpa using h1
    · have huniv := (hclopen.preimage γ.continuous).eq_univ ⟨1, by simpa using h⟩
      have h0 : (0 : unitInterval) ∈ γ ⁻¹' Upos := huniv ▸ Set.mem_univ 0
      simpa using h0
  simp only [hmem]

/-- For a nonempty convex open subset `S` of `F ∖ {0}`, the projection from
`{p : B × (F ∖ {0}) | p.2 ∈ S}` to `B` induces an isomorphism on singular cohomology. -/
private theorem isIso_singularCohomologyMap_halfProdProj {B : Type w} [TopologicalSpace B]
    {S : Set F} (hS₀ : ∀ x ∈ S, x ≠ 0) (hconv : Convex ℝ S) (hne : S.Nonempty)
    (M : ModuleCat.{w} K) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (TopCat.ofHom (ContinuousMap.subtypeVal {p : (prodThomPair B F).snd | p.1.2 ∈ S}) ≫
        prodThomPairPuncturedProj B F) n) := by
  let U : Set (prodThomPair B F).snd := {p | p.1.2 ∈ S}
  have : ContractibleSpace S := hconv.contractibleSpace hne
  let h : U ≃ₜ B × S :=
    { toFun p := (p.1.1.1, ⟨p.1.1.2, p.2⟩)
      invFun q := ⟨⟨(q.1, q.2.1), hS₀ q.2.1 q.2.2⟩, q.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let isoH : TopCat.of U ≅ TopCat.of (B × S) := TopCat.isoOfHomeo h
  have hj : TopCat.ofHom (ContinuousMap.subtypeVal U) ≫ prodThomPairPuncturedProj B F =
      isoH.hom ≫ TopCat.ofHom ContinuousMap.fst :=
    TopCat.ext fun p ↦ prodThomPairPuncturedProj_apply F p.1
  have hfst : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (TopCat.ofHom (ContinuousMap.fst : C(B × S, B))) n) := by
    have := (ContinuousMap.HomotopyEquiv.prodContractible B S).isIso_singularCohomologyMap
      (𝟙_ (ModuleCat.{w} K)) K M n
    rwa [ContinuousMap.HomotopyEquiv.prodContractible_toFun] at this
  have := isIso_singularCohomologyMap_of_isIso (R := 𝟙_ (ModuleCat.{w} K)) (M := M) isoH.hom n
  rw [hj, TopCat.singularCohomologyMap_comp]
  exact IsIso.comp_isIso

/-- The map `(b, c) ↦ π₀^* b + π₀^* c ⌣ σ` on `Hⁿ(B; M) × Hⁿ(B; M)` in rank one. -/
private def rankOnePuncturedMap {B : Type w} [TopologicalSpace B] (M : ModuleCat.{w} K)
    (σ₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).snd.singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0) (n : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) →ₗ[K]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n :=
  LinearMap.coprod (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n).hom
    (((prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom n 0 n
        (Nat.add_zero n)).flip
        (TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairSnd B F)) 0 σ₀) ∘ₗ
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n).hom)

/-- The shear `(b, c) ↦ (b + c, b)` on `V × V` used to diagonalize `rankOnePuncturedMap`. -/
private def rankOneShear (V : Type*) [AddCommGroup V] [Module K V] : (V × V) ≃ₗ[K] (V × V) where
  toFun bc := (bc.1 + bc.2, bc.1)
  invFun xy := (xy.2, xy.1 - xy.2)
  map_add' x y := Prod.ext (by simp only [Prod.fst_add, Prod.snd_add]; abel) rfl
  map_smul' r x := Prod.ext (smul_add r x.1 x.2).symm rfl
  left_inv x := Prod.ext rfl (add_sub_cancel_left x.1 x.2)
  right_inv x := Prod.ext (add_sub_cancel x.2 x.1) rfl

/-- Restriction of the rank-one indicator class to the positive and negative half-products. -/
private theorem rankOnePuncturedClass_restrict {B : Type w} [TopologicalSpace B] (e : F ≃L[ℝ] ℝ)
    (σ₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).snd.singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (hσ₀ : ∀ x, singularCohomologyZeroEval x σ₀ = if 0 < e x.1 then 1 else 0) :
    TopCat.singularCohomologyMap
        (TopCat.ofHom (ContinuousMap.subtypeVal {p : (prodThomPair B F).snd | 0 < e p.1.2})) 0
        (TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairSnd B F)) 0 σ₀) =
      (TopCat.of {p : (prodThomPair B F).snd | 0 < e p.1.2}).singularCohomologyZeroOne ∧
    TopCat.singularCohomologyMap
        (TopCat.ofHom (ContinuousMap.subtypeVal {p : (prodThomPair B F).snd | e p.1.2 < 0})) 0
        (TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairSnd B F)) 0 σ₀) = 0 := by
  refine ⟨singularCohomologyZero_ext fun q ↦ ?_, singularCohomologyZero_ext fun q ↦ ?_⟩
  · rw [singularCohomologyZeroEval_naturality, singularCohomologyZeroEval_naturality, hσ₀,
      prodThomPairSnd_snd_val, singularCohomologyZeroEval_singularCohomologyZeroOne]
    have hq : 0 < e q.1.1.2 := q.2
    simp [hq]
  · rw [singularCohomologyZeroEval_naturality, singularCohomologyZeroEval_naturality, hσ₀,
      prodThomPairSnd_snd_val, map_zero]
    have hq : ¬ 0 < e q.1.1.2 := not_lt.2 q.2.le
    simp [hq]

private theorem isIso_rankOneMayerVietorisToBiprod {B : Type w} [TopologicalSpace B]
    (M : ModuleCat.{w} K) (e : F ≃L[ℝ] ℝ) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMayerVietorisToBiprod (𝟙_ (ModuleCat.{w} K)) K M
      {p : (prodThomPair B F).snd | 0 < e p.1.2}
      {p : (prodThomPair B F).snd | e p.1.2 < 0} n) := by
  have hUpos : IsOpen {p : (prodThomPair B F).snd | 0 < e p.1.2} :=
    isOpen_lt continuous_const (e.continuous.comp (continuous_snd.comp continuous_subtype_val))
  have hUneg : IsOpen {p : (prodThomPair B F).snd | e p.1.2 < 0} :=
    isOpen_lt (e.continuous.comp (continuous_snd.comp continuous_subtype_val)) continuous_const
  have hUV : {p : (prodThomPair B F).snd | 0 < e p.1.2} ∪
      {p : (prodThomPair B F).snd | e p.1.2 < 0} = Set.univ :=
    Set.eq_univ_of_forall fun p ↦ (lt_or_gt_of_ne ((map_ne_zero_iff e e.injective).2 p.2)).symm
  have : IsEmpty ↥({p : (prodThomPair B F).snd | 0 < e p.1.2} ∩
      {p : (prodThomPair B F).snd | e p.1.2 < 0}) := ⟨fun p ↦ by
    have h1 : 0 < e p.1.1.2 := p.2.1
    have h2 : e p.1.1.2 < 0 := p.2.2
    exact lt_asymm h1 h2⟩
  exact isIso_singularCohomologyMayerVietorisToBiprod_of_isEmpty
    (𝟙_ (ModuleCat.{w} K)) K M hUpos hUneg hUV n

/-- In rank one, `(b, c) ↦ π₀^* b + π₀^* c ⌣ σ` is bijective in every degree. -/
private theorem bijective_rankOnePuncturedMap {B : Type w} [TopologicalSpace B]
    (M : ModuleCat.{w} K) (e : F ≃L[ℝ] ℝ)
    (σ₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).snd.singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (hσ₀ : ∀ x, singularCohomologyZeroEval x σ₀ = if 0 < e x.1 then 1 else 0) (n : ℕ) :
    Function.Bijective (rankOnePuncturedMap (B := B) M σ₀ n) := by
  let Upos : Set (prodThomPair B F).snd := {p | 0 < e p.1.2}
  let Uneg : Set (prodThomPair B F).snd := {p | e p.1.2 < 0}
  have hMV := isIso_rankOneMayerVietorisToBiprod (B := B) M e n
  obtain ⟨hσ_pos, hσ_neg⟩ := rankOnePuncturedClass_restrict (B := B) e σ₀ hσ₀
  have hj_pos := isIso_singularCohomologyMap_halfProdProj (B := B) (S := {x : F | 0 < e x})
    (fun x (hx : 0 < e x) h0 ↦ by simp [h0] at hx)
    ((convex_Ioi (0 : ℝ)).linear_preimage e.toLinearMap) ⟨e.symm 1, by simp⟩ M n
  have hj_neg := isIso_singularCohomologyMap_halfProdProj (B := B) (S := {x : F | e x < 0})
    (fun x (hx : e x < 0) h0 ↦ by simp [h0] at hx)
    ((convex_Iio (0 : ℝ)).linear_preimage e.toLinearMap) ⟨e.symm (-1), by simp⟩ M n
  let resPair := ((asIso (TopCat.singularCohomologyMayerVietorisToBiprod
      (𝟙_ (ModuleCat.{w} K)) K M Upos Uneg n)).trans (ModuleCat.biprodIsoProd _ _)).toLinearEquiv
  let prodEquiv := (rankOneShear (K := K) _).trans (LinearEquiv.prodCongr
      (asIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (TopCat.ofHom (ContinuousMap.subtypeVal Upos) ≫
          prodThomPairPuncturedProj B F) n)).toLinearEquiv
      (asIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (TopCat.ofHom (ContinuousMap.subtypeVal Uneg) ≫
          prodThomPairPuncturedProj B F) n)).toLinearEquiv)
  suffices hφ : ⇑resPair ∘ ⇑(rankOnePuncturedMap (B := B) M σ₀ n) = ⇑prodEquiv by
    exact (Function.Bijective.of_comp_iff' resPair.bijective _).1 (hφ ▸ prodEquiv.bijective)
  funext bc
  rw [Function.comp_apply]
  -- Unfold `resPair` into `(ModuleCat.biprodIsoProd _ _).hom` applied to `ToBiprod`.
  change (ModuleCat.biprodIsoProd _ _).hom
      (TopCat.singularCohomologyMayerVietorisToBiprod (𝟙_ (ModuleCat.{w} K)) K M Upos Uneg n
        (rankOnePuncturedMap (B := B) M σ₀ n bc)) = prodEquiv bc
  rw [ModuleCat.biprodIsoProd_hom_apply]
  refine Prod.ext ?_ ?_
  · dsimp only [prodEquiv, rankOneShear, rankOnePuncturedMap, LinearEquiv.trans_apply,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.prodCongr_apply,
      Iso.toLinearEquiv_apply, asIso_hom, LinearMap.coprod_apply, LinearMap.flip_apply,
      LinearMap.comp_apply]
    rw [← ConcreteCategory.comp_apply, TopCat.singularCohomologyMayerVietorisToBiprod_fst,
      map_add, ← TopCat.singularCup_naturality, hσ_pos, TopCat.singularCohomologyZeroOne_def,
      (TopCat.of Upos).singularCup_constSingularCocycle_right K
        (η := 𝟙 (𝟙_ (ModuleCat.{w} K))) (by monoidal) (by monoidal) (Nat.add_zero n),
      map_add, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
  · dsimp only [prodEquiv, rankOneShear, rankOnePuncturedMap, LinearEquiv.trans_apply,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.prodCongr_apply,
      Iso.toLinearEquiv_apply, asIso_hom, LinearMap.coprod_apply, LinearMap.flip_apply,
      LinearMap.comp_apply]
    rw [← ConcreteCategory.comp_apply, TopCat.singularCohomologyMayerVietorisToBiprod_snd,
      map_add, ← TopCat.singularCup_naturality, hσ_neg, map_zero, add_zero,
      TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]

/-- In rank one, `(b, c) ↦ π₀^* b + π₀^* c ⌣ σ` as a `K`-linear equivalence. -/
private def rankOnePuncturedEquiv {B : Type w} [TopologicalSpace B] (M : ModuleCat.{w} K)
    (e : F ≃L[ℝ] ℝ)
    (σ₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).snd.singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (hσ₀ : ∀ x, singularCohomologyZeroEval x σ₀ = if 0 < e x.1 then 1 else 0) (n : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) ≃ₗ[K]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n :=
  LinearEquiv.ofBijective (rankOnePuncturedMap M σ₀ n) (bijective_rankOnePuncturedMap M e σ₀ hσ₀ n)

private theorem rankOnePuncturedEquiv_apply {B : Type w} [TopologicalSpace B] (M : ModuleCat.{w} K)
    (e : F ≃L[ℝ] ℝ)
    (σ₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).snd.singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (hσ₀ : ∀ x, singularCohomologyZeroEval x σ₀ = if 0 < e x.1 then 1 else 0) (n : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) :
    rankOnePuncturedEquiv M e σ₀ hσ₀ n bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.1 +
        (prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
          n 0 n (Nat.add_zero n)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2)
          (TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairSnd B F)) 0 σ₀) :=
  (rfl)

/-- Since `F` is contractible, `prodThomPairProj B F` induces a surjection in cohomology. -/
private theorem surjective_singularCohomologyMap_prodThomPairProj {B : Type w} [TopologicalSpace B]
    (M : ModuleCat.{w} K) (q : ℕ) :
    Function.Surjective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (prodThomPairProj B F) q) := fun y ↦ by
  have hiso := (ContinuousMap.HomotopyEquiv.prodContractible B F).isIso_singularCohomologyMap
    (𝟙_ (ModuleCat.{w} K)) K M q
  rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun] at hiso
  have hproj : TopCat.ofHom ContinuousMap.fst = prodThomPairProj B F :=
    TopCat.ext fun p ↦ (prodThomPairProj_apply F p).symm
  have : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
    (prodThomPairProj B F) q) := hproj ▸ hiso
  exact ⟨inv (TopCat.singularCohomologyMap (prodThomPairProj B F) q) y, IsIso.inv_hom_id_apply _ _⟩

/-- Every class of `Hᵐ(B × F; M)` is pulled back from `B` when `F` is contractible, and `π₀^*` is
injective when `F ∖ {0}` has a point; consequently `c ↦ δ (π₀^* c ⌣ σ)` is bijective in rank one. -/
private theorem bijective_rankOneDeltaMap {B : Type w} [TopologicalSpace B] (M : ModuleCat.{w} K)
    (e : F ≃L[ℝ] ℝ)
    (σ₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).snd.singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (hσ₀ : ∀ x, singularCohomologyZeroEval x σ₀ = if 0 < e x.1 then 1 else 0)
    (n m : ℕ) (h : n + 1 = m) :
    let P := prodThomPair B F
    let D := rankOnePuncturedEquiv (B := B) M e σ₀ hσ₀ n
    Function.Bijective (fun c ↦
      P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m h (D (0, c))) := by
  intro P D
  have hv : (e.symm 1 : F) ≠ 0 := fun h0 ↦ by simpa using congrArg e h0
  have hD0 (b : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) :
      D (b, 0) = TopCat.singularCohomologyMap P.map n
        (TopCat.singularCohomologyMap (prodThomPairProj B F) n b) := by
    rw [rankOnePuncturedEquiv_apply, map_zero, LinearMap.map_zero₂, add_zero,
      ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
      map_comp_prodThomPairProj]
  let f : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n →ₗ[K]
      P.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M m :=
    (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m h).hom ∘ₗ
      D.toLinearMap ∘ₗ LinearMap.inr K _ _
  -- Rewrite `c ↦ δ (D (0, c))` as the `K`-linear map `f` so `injective_iff_map_eq_zero` applies.
  change Function.Bijective f
  refine ⟨(injective_iff_map_eq_zero f).2 fun c hc ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_subspace (𝟙_ (ModuleCat.{w} K)) K M n m h) (D (0, c)) hc
    obtain ⟨b, rfl⟩ := surjective_singularCohomologyMap_prodThomPairProj (F := F) M n y
    rw [← hD0 b] at hy
    exact congrArg Prod.snd (D.injective hy).symm
  · obtain ⟨b, hb⟩ := surjective_singularCohomologyMap_prodThomPairProj (F := F) M m
      (P.singularCohomologyπ _ K M m z)
    have hπ : P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M m z = 0 := by
      have h0 := ConcreteCategory.congr_hom
        (P.singularCohomologyπ_comp_singularCohomologyMap (𝟙_ (ModuleCat.{w} K)) K M m) z
      rw [ConcreteCategory.comp_apply, ← hb, ← ConcreteCategory.comp_apply,
        ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj] at h0
      rw [← hb, injective_singularCohomologyMap_prodThomPairPuncturedProj M hv m
        (h0.trans (map_zero _).symm), map_zero]
    obtain ⟨x, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_relative (𝟙_ (ModuleCat.{w} K)) K M n m h) z hπ
    obtain ⟨⟨b', c⟩, rfl⟩ := D.surjective x
    have hδ0 : P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m h (D (b', 0)) = 0 := by
      rw [hD0 b', ← ConcreteCategory.comp_apply,
        P.singularCohomologyMap_comp_singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m h]
      rfl
    refine ⟨c, ?_⟩
    have hbc : ((b', c) : _ × _) = (b', 0) + (0, c) := by simp
    -- Unfold `f c` back to `δ (D (0, c))`.
    change P.singularCohomologyδ _ K M n m h (D (0, c)) = _
    rw [hbc, map_add, map_add, hδ0, zero_add]

/-- When `e : F ≃L[ℝ] ℝ`, `δ σ₀ ∈ H¹(F, F ∖ {0}; K)` pulls back to a class on `prodThomPair B F`
with bijective `TopPair.pullbackCup` in every degree. -/
private theorem exists_model_bijective_of_equiv_real (e : F ≃L[ℝ] ℝ) :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) 1,
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ) (h : p + 1 = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 1 p m h
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) 1 g₀)) := by
  obtain ⟨σ₀, hσ₀⟩ := exists_rankOnePuncturedClass (K := K) e
  let Q := TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)
  let g₀ : Q.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 1 :=
    Q.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 1 rfl σ₀
  refine ⟨g₀, fun B _ M p m h ↦ ?_⟩
  let P := prodThomPair B F
  let σ : P.snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 :=
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairSnd B F)) 0 σ₀
  have hu₀ : TopPair.singularCohomologyMap (prodThomPairSnd B F) 1 g₀ =
      P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 1 rfl σ :=
    ConcreteCategory.congr_hom
      (TopPair.singularCohomologyδ_naturality (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
        (M := 𝟙_ (ModuleCat.{w} K)) (prodThomPairSnd B F) 0 1 rfl) σ₀
  have hbij := bijective_rankOneDeltaMap (B := B) M e σ₀ hσ₀ p m h
  have hsign : Function.Bijective
      (fun x : P.singularCohomology (ModuleCat.of K K) K M m ↦ ((-1 : ℤ) ^ p) • x) := by
    refine Function.Involutive.bijective fun x ↦ ?_
    rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  suffices heq : (fun c ↦ P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h
      (rankOnePuncturedEquiv (B := B) M e σ₀ hσ₀ p (0, c))) =
      (fun x ↦ ((-1 : ℤ) ^ p) • x) ∘
        ⇑(P.pullbackCup M (prodThomPairProj B F) 1 p m h
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) 1 g₀)) by
    exact (Function.Bijective.of_comp_iff' hsign _).1 (heq ▸ hbij)
  funext c
  rw [Function.comp_apply, TopPair.pullbackCup_apply, rankOnePuncturedEquiv_apply,
    map_zero, zero_add, ← map_comp_prodThomPairProj, TopCat.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply,
    P.singularCohomologyδ_singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
      (Nat.add_zero p) rfl h h, hu₀]

end RankOne

/-! ### Rank at least two -/

section RankGeTwo

private lemma prodThomPairSnd_comp_complZeroPairIsoProdThomPair_hom (B F : Type w)
    [TopologicalSpace B] [TopologicalSpace F] [Zero F] :
    prodThomPairSnd B F ≫ (complZeroPairIsoProdThomPair F).hom =
      prodThomPairMap F (ContinuousMap.const B PUnit.unit) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun p ↦ by
    rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply, complZeroPairIsoProdThomPair_hom]
    exact (prodThomPairFiberMap_fst_apply F PUnit.unit _).trans
      ((congrArg (Prod.mk PUnit.unit) (prodThomPairSnd_fst_apply F p)).trans
        (prodThomPairMap_fst_apply F (ContinuousMap.const B PUnit.unit) p).symm))

private lemma bijective_zsmul_neg_one_pow_mul {V : Type*} [AddCommGroup V] (a b : ℕ) :
    Function.Bijective (fun x : V ↦ ((-1 : ℤ) ^ a * (-1 : ℤ) ^ b) • x) := by
  refine Function.Involutive.bijective fun x ↦ ?_
  have hk2 : ((-1 : ℤ) ^ a * (-1 : ℤ) ^ b) * ((-1 : ℤ) ^ a * (-1 : ℤ) ^ b) = 1 := by
    rw [mul_mul_mul_comm, ← mul_pow, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_pow, mul_one]
  rw [smul_smul, hk2, one_smul]

/-- Tensor-unit version of `exists_model_bijective_of_equiv_euclidean`, proved before crossing from
`𝟙_ (ModuleCat.{w} K)` to `ModuleCat.of K K` so the explicit witness `g₀` is never unfolded during
type comparison. -/
private theorem exists_model_bijective_of_equiv_euclidean_unit {F : Type w} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {d : ℕ} (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) (d + 2),
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ) (h : p + (d + 2) = m),
        Function.Bijective (fun c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p ↦
          (prodThomPair B F).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
            p (d + 2) m h (TopCat.singularCohomologyMap (prodThomPairProj B F) p c)
            (TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 2) g₀)) := by
  obtain ⟨g₀, hg₀_def⟩ :
      ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) (d + 2),
        g₀ = TopPair.singularCohomologyMap (complZeroPairIsoProdThomPair F).hom (d + 2)
          ((prodThomPair PUnit.{w + 1} F).singularCohomologyδ
            (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) (d + 1) (d + 2) rfl
            (prodThomPairPuncturedClass K PUnit.{w + 1} e)) := ⟨_, rfl⟩
  refine ⟨g₀, fun B _ M p m h ↦ ?_⟩
  let P := prodThomPair B F
  have hu₀ : TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 2) g₀ =
      P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) (d + 1) (d + 2) rfl
        (prodThomPairPuncturedClass K B e) := by
    rw [hg₀_def, ← TopPair.singularCohomologyMap_comp_apply,
      prodThomPairSnd_comp_complZeroPairIsoProdThomPair_hom]
    have hnat := ConcreteCategory.congr_hom
      (TopPair.singularCohomologyδ_naturality (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
        (M := 𝟙_ (ModuleCat.{w} K)) (prodThomPairMap F (ContinuousMap.const B PUnit.unit))
        (d + 1) (d + 2) rfl) (prodThomPairPuncturedClass K PUnit.{w + 1} e)
    simp only [ConcreteCategory.comp_apply] at hnat
    rw [hnat, singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass]
  have hu_braid : (λ_ (𝟙_ (ModuleCat.{w} K))).inv ≫
      (β_ (𝟙_ (ModuleCat.{w} K)) (𝟙_ (ModuleCat.{w} K))).hom =
      (λ_ (𝟙_ (ModuleCat.{w} K))).inv := by
    rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal]
  have hμ_braid : (β_ M (𝟙_ (ModuleCat.{w} K))).hom ≫ (λ_ M).hom = (ρ_ M).hom := by
    rw [braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hsign := bijective_zsmul_neg_one_pow_mul
    (V := P.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M m) (p * (d + 1)) p
  suffices heq : ⇑(prodThomPairSingularCohomologySphereEquiv M B e p m h) =
      (fun x ↦ ((-1 : ℤ) ^ (p * (d + 1)) * (-1 : ℤ) ^ p) • x) ∘
        fun c ↦ P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
          p (d + 2) m h (TopCat.singularCohomologyMap (prodThomPairProj B F) p c)
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 2) g₀) by
    exact (Function.Bijective.of_comp_iff' hsign _).1
      (heq ▸ (prodThomPairSingularCohomologySphereEquiv M B e p m h).bijective)
  funext c
  rw [Function.comp_apply, prodThomPairSingularCohomologySphereEquiv_apply,
    P.snd.singularCup_gradedComm K hu_braid hμ_braid (add_comm p (d + 1))
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p c)
      (prodThomPairPuncturedClass K B e),
    map_zsmul, ← map_comp_prodThomPairProj, TopCat.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply,
    P.singularCohomologyδ_singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
      (add_comm p (d + 1)) rfl (by lia) h, ← hu₀, smul_smul]

/-- When `e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))`, the connecting image of
`TauCeti.prodThomPairPuncturedClass` over a point pulls back to a class on `prodThomPair B F` with
bijective `TopPair.pullbackCup` in every degree. -/
private theorem exists_model_bijective_of_equiv_euclidean {F : Type w} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {d : ℕ} (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (d + 2),
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ) (h : p + (d + 2) = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 2) g₀)) := by
  obtain ⟨g₀, hg₀⟩ := exists_model_bijective_of_equiv_euclidean_unit (K := K) e
  refine ⟨g₀, fun B _ M p m h ↦ ?_⟩
  have hfun : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 2) g₀)) = _ :=
    funext ((prodThomPair B F).pullbackCup_apply _ h _)
  rw [hfun]
  exact hg₀ B M p m h

end RankGeTwo

/-! ### Assembling all ranks -/

/-- Auxiliary form of `exists_model_bijective` parameterized by `r = finrank ℝ F` so pattern
matching on `r` avoids dependent degree casts. -/
private theorem exists_model_bijective_aux (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (r : ℕ) (hr : finrank ℝ F = r) :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) r,
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ) (h : p + r = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) r p m h
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) r g₀)) := by
  rcases r with _ | _ | d
  · have : Subsingleton F := (Module.finrank_eq_zero_iff_of_free ℝ F).1 hr
    exact exists_model_bijective_of_subsingleton (K := K) F
  · exact exists_model_bijective_of_equiv_real (K := K)
      (ContinuousLinearEquiv.ofFinrankEq (hr.trans (Module.finrank_self ℝ).symm))
  · exact exists_model_bijective_of_equiv_euclidean (K := K)
      (ContinuousLinearEquiv.ofFinrankEq (hr.trans (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm))

/-- For every finite-dimensional real normed space `F`, there exists a model class
`g₀ ∈ Hʳ(F, F ∖ {0}; K)` whose pullback to `prodThomPair B F` has bijective `TopPair.pullbackCup`
in every degree for every base `B` and coefficient module `M`. -/
private theorem exists_model_bijective (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F),
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ)
        (h : p + finrank ℝ F = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F)
          (finrank ℝ F) p m h (TopPair.singularCohomologyMap (prodThomPairSnd B F) _ g₀)) :=
  exists_model_bijective_aux F (finrank ℝ F) rfl

end ProdThomPairPullbackCup

/-! ### Arbitrary fibrewise-generating classes -/

section Main

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)
  {B : Type w} [TopologicalSpace B]

/-- Right cup multiplication on `Hᵖ(B; M)` by a degree-zero class `ε ∈ H⁰(B; K)` with a cup-product
inverse is bijective. -/
private theorem bijective_singularCup_degreeZero_right
    {ε ε' : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0}
    (h1 : (TopCat.of B).singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl ε ε' =
      (TopCat.of B).singularCohomologyZeroOne)
    (h2 : (TopCat.of B).singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl ε' ε =
      (TopCat.of B).singularCohomologyZeroOne)
    (p : ℕ) :
    Function.Bijective (fun a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ↦
      (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p)
        a ε) := by
  let mulR (η : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) 0) :
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p →
        (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p :=
    fun a ↦ (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
      p 0 p (Nat.add_zero p) a η
  have hcomp (η₁ η₂ : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) 0)
      (hη : (TopCat.of B).singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl η₁ η₂ =
        (TopCat.of B).singularCohomologyZeroOne)
      (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
      mulR η₂ (mulR η₁ a) = a := by
    dsimp only [mulR]
    rw [(TopCat.of B).singularCup_assoc K (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (μ' := (ρ_ M).hom)
      (μ₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).hom) (by monoidal) (by monoidal)
      (Nat.add_zero p) (Nat.add_zero p) rfl (Nat.add_zero p) a η₁ η₂, hη,
      TopCat.singularCohomologyZeroOne_def]
    exact (TopCat.of B).singularCup_constSingularCocycle_right K
      (η := 𝟙 (𝟙_ (ModuleCat.{w} K))) (by monoidal) (by monoidal) (Nat.add_zero p) a
  exact ⟨Function.LeftInverse.injective (hcomp ε ε' h1),
    Function.RightInverse.surjective (hcomp ε' ε h2)⟩

/-- Restricting `π^* ε₀ ⌣ pr₂^* g₀` to the fibre over `b` scales `g₀` by the point evaluation of
`ε₀` at `b`. -/
private theorem singularCohomologyMap_prodThomPairFiberMap_pullbackCup_zero
    {F : Type w} [TopologicalSpace F] [Zero F] {r : ℕ}
    (g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) r)
    (ε₀ : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0) (b : B) :
    let ε : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 :=
      ε₀
    TopPair.singularCohomologyMap (prodThomPairFiberMap F b) r
        ((prodThomPair B F).pullbackCup (ModuleCat.of K K) (prodThomPairProj B F) r 0 r
          (zero_add r) (TopPair.singularCohomologyMap (prodThomPairSnd B F) r g₀) ε₀) =
      singularCohomologyZeroEval (X := TopCat.of B) b ε • g₀ := by
  intro ε
  let Q := TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)
  have hconst : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
      TopCat.const (X := Q.fst) b :=
    TopCat.ext fun x ↦ by
      rw [ConcreteCategory.comp_apply]
      exact (prodThomPairProj_apply F _).trans
        ((congrArg Prod.fst (prodThomPairFiberMap_fst_apply F b x)).trans
          (TopCat.const_apply (X := Q.fst) (Y := TopCat.of B) b x).symm)
  have hconst_ε : TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
      (M := 𝟙_ (ModuleCat.{w} K)) (TopCat.const (X := Q.fst) b) 0 ε =
      singularCohomologyZeroEval (X := TopCat.of B) b ε • Q.fst.singularCohomologyZeroOne :=
    singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul (X := TopCat.of B) (Y := Q.fst)
      b ε
  have hpull : TopPair.singularCohomologyMap (prodThomPairFiberMap F b) r
      ((prodThomPair B F).pullbackCup (ModuleCat.of K K) (prodThomPairProj B F) r 0 r
        (zero_add r) (TopPair.singularCohomologyMap (prodThomPairSnd B F) r g₀) ε₀) =
      Q.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ (ModuleCat.of K K)).hom 0 r r
        (zero_add r) (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
          (M := 𝟙_ (ModuleCat.{w} K)) (TopCat.const (X := Q.fst) b) 0 ε) g₀ := by
    rw [TopPair.pullbackCup_apply, ← TopPair.singularCup_naturality,
      ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hconst,
      ← TopPair.singularCohomologyMap_comp_apply, prodThomPairFiberMap_comp_prodThomPairSnd,
      TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
    rfl
  rw [hpull, hconst_ε, map_smul, LinearMap.smul_apply, TopCat.singularCohomologyZeroOne_def]
  exact congrArg (singularCohomologyZeroEval (X := TopCat.of B) b ε • ·)
    (Q.singularCup_constSingularCocycle_left K (η := 𝟙 (𝟙_ (ModuleCat.{w} K)))
      (by monoidal) (by monoidal) (zero_add r) g₀)

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The Thom isomorphism for a product bundle**: if `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)`,
`r = finrank ℝ F`, restricts on the fibre over every point `b : B` to a generator of
`Hʳ(F, F ∖ {0}; K)`, then `a ↦ π^*a ⌣ u` is bijective from `Hᵖ(B; M)` to
`Hᵐ(B × F, B × (F ∖ {0}); M)` whenever `p + r = m`. -/
theorem bijective_pullbackCup_prodThomPairProj
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) := by
  obtain ⟨g₀, hg₀⟩ := ProdThomPairPullbackCup.exists_model_bijective (K := K) F
  let P := prodThomPair B F
  let u₀ := TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g₀
  obtain ⟨ε₀, hε⟩ := (hg₀ B (ModuleCat.of K K) 0 (finrank ℝ F) (zero_add _)).2 u
  let ε : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 := ε₀
  have hε_unit (b : B) : IsUnit (singularCohomologyZeroEval (X := TopCat.of B) b ε) := by
    let eloc := singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of K K)
      (OpenPartialHomeomorph.refl F) (Set.mem_univ (0 : F))
    have hunit := eloc.span_singleton_eq_top_iff_isUnit.1 (hu b)
    rw [← hε, singularCohomologyMap_prodThomPairFiberMap_pullbackCup_zero g₀ ε₀ b,
      map_smul, smul_eq_mul] at hunit
    exact isUnit_of_mul_isUnit_left hunit
  obtain ⟨ε', h1, h2⟩ := exists_singularCup_eq_one ε hε_unit
  have hfac : ⇑(P.pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) =
      ⇑(P.pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u₀) ∘
        fun a ↦ (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
          p 0 p (Nat.add_zero p) a ε := by
    funext a
    rw [Function.comp_apply, ← hε, TopPair.pullbackCup_apply, TopPair.pullbackCup_apply,
      TopPair.pullbackCup_apply, ← TopCat.singularCup_naturality]
    exact (P.singularCup_assoc K (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (μ' := (ρ_ M).hom)
      (μ₂₃ := (ρ_ (ModuleCat.of K K)).hom) (by monoidal) (by monoidal)
      (Nat.add_zero p) h (zero_add _) h _ _ u₀).symm
  rw [hfac]
  exact (hg₀ B M p m h).comp (bijective_singularCup_degreeZero_right M h1 h2 p)

variable (B) in
/-- Pulling back a generator `g ∈ Hʳ(F, F ∖ {0}; K)` along the second projection gives a class on
`prodThomPair B F` with bijective `TopPair.pullbackCup` in every degree. -/
theorem bijective_pullbackCup_prodThomPairSnd
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g)) :=
  bijective_pullbackCup_prodThomPairProj M
    (fun b ↦ by
      rw [← TopPair.singularCohomologyMap_comp_apply, prodThomPairFiberMap_comp_prodThomPairSnd,
        TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
      exact hg)
    h

/-- **The Thom isomorphism `Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)` for a product bundle**,
given by `a ↦ π^*a ⌣ u` for any class `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` whose fibre restrictions
generate `Hʳ(F, F ∖ {0}; K)`. -/
def prodThomPairPullbackCupEquiv
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    (p m : ℕ) (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (prodThomPair B F).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective
    ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u)
    (bijective_pullbackCup_prodThomPairProj M hu h)

@[simp]
theorem prodThomPairPullbackCupEquiv_apply
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    prodThomPairPullbackCupEquiv M hu p m h a =
      (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u a := by
  rfl

end Main

end TauCeti
