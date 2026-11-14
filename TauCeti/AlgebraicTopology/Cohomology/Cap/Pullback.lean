/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.HomEquiv
import TauCeti.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.Algebra.Homology.Embedding.DownNatAdd
import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing

/-!
# The cap product with a relative class followed by push-forward

Let `P = (X, B)` be a topological pair, `g : X ⟶ Z` a continuous map, and `u ∈ Hʳ(X, B; K)` a
relative cohomology class with coefficients in a commutative ring `K`. For any `K`-module `A`, this
file studies the homological counterpart of `TopPair.pullbackCup`:

`Hₘ(X, B; A) ⟶ Hₚ(Z; A)`,  `x ↦ g_*(x ⌢ u)`,  `r + p = m`,

(`TopPair.capPushforward`), the relative cap product with `u` (`TopPair.singularCap`) followed by
the push-forward along `g`. For the Thom pair `(E, E₀)` of a vector bundle and its projection
`E ⟶ B`, this is definitionally `TauCeti.homologyThomMap`.

Over a field `K`, the Kronecker pairing already shows that `x ↦ g_*(x ⌢ u)` is bijective in degree
`r + p` if and only if `a ↦ g^*a ⌣ u` is bijective in degree `p` (see
`TauCeti.bijective_homologyThomMap_iff`). Over an arbitrary commutative ring `K`, individual degrees
are coupled by `Ext` and `Tor`, so one works at the chain level instead. Choosing a relative
`r`-cocycle `φ` representing `u`, the signed cap-and-push-forward maps
`(-1)^(r p) g_*( - ⌢ φ) : C_{p + r}(X, B; K) ⟶ Cₚ(Z; K)` assemble into a chain map from
`C_*(X, B; K)` to the extension of `C_*(Z; K)` along `p ↦ p + r`
(`ComplexShape.embeddingDownNatAdd r`), which has zeros below degree `r`. Both chain complexes
consist of projective `K`-modules.

When `Hₘ(X, B; K) = 0` for all `m < r`, the induced map on homology in degree `r + p` is
`(-1)^(r p)` times `TopPair.capPushforward`, while applying `Hom(-, M)` recovers
`TopPair.pullbackCup` in degree `p + r` (the sign `(-1)^(r p)` cancelling the Koszul sign of
`TopPair.singularCup_gradedComm`). By
`ChainComplex.quasiIso_iff_forall_quasiIso_linearYonedaFunctor_map_of_projective`, `pullbackCup` is
bijective in all degrees and for all `K`-modules `M` if and only if `capPushforward` with
coefficients `K` is bijective in all degrees; moreover, the chain map is then a chain homotopy
equivalence, so tensoring on the left with any `K`-module `A` shows that `capPushforward` with
coefficients `A` is bijective in all degrees as well. This lets the Thom isomorphism pass between
cohomology (where Mayer–Vietoris gluing is carried out using the `H*(B)`-module structure) and
homology (which commutes with directed unions over arbitrary bases).

## Main definitions and results

* `TopPair.capPushforward`: the map `x ↦ g_*(x ⌢ u)`, `K`-linear in `u`.
* `TopPair.capPushforward_naturality`, `TopPair.bijective_capPushforward_iff_of_isIso`: naturality
  in maps of pairs and invariance of bijectivity under isomorphisms.
* `TopPair.forall_bijective_pullbackCup_iff_forall_bijective_capPushforward`: when
  `Hₘ(X, B; K) = 0` for `m < r`, `a ↦ g^*a ⌣ u` is bijective for all `M` and `p` if and only if
  `x ↦ g_*(x ⌢ u)` with coefficients `K` is bijective for all `p`.
* `TopPair.bijective_capPushforward_of_forall_bijective_capPushforward`: under the same below-`r`
  vanishing, bijectivity of `x ↦ g_*(x ⌢ u)` with coefficients `K` in all degrees implies its
  bijectivity with coefficients in any `K`-module `A`.
* `TopCat.capPushforwardRestrict`: the restricted map over a subset `S ⊆ Y` for `π : X ⟶ Y` and
  `Z ⊆ X`, with naturality and whole-base equivalence mirroring `TopCat.pullbackCupRestrict`.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Sections 6–7.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.3 and Section 4.D.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex Opposite AlgebraicTopology Simplicial

universe w

namespace TopPair

section Basic

variable {K : Type w} [CommRing K] (A : ModuleCat.{w} K)

/-- For a pair `P = (X, B)`, a map `g : X ⟶ Z`, and a class `u ∈ Hⁿ(X, B; K)`, the map
`Hₘ(X, B; A) ⟶ Hₚ(Z; A)`, `x ↦ g_*(x ⌢ u)`, `n + p = m`, as a `K`-linear map of `u`. Both the
chain-coefficient morphism and the value pairing are the left unitor `K ⊗ A ≅ A`. -/
def capPushforward (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) (n p m : ℕ)
    (h : n + p = m) :
    P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      (P.singularHomology A m ⟶
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj Z) :=
  Linear.rightComp K _
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map g) ∘ₗ
    P.singularCap K (λ_ A).inv (λ_ A).hom n p m h

variable {A}

/-- `TopPair.capPushforward` is the relative cap product with `u` followed by push-forward along
`g`. -/
theorem capPushforward_apply (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) {n p m : ℕ}
    (h : n + p = m) (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    P.capPushforward A g n p m h u =
      P.singularCap K (λ_ A).inv (λ_ A).hom n p m h u ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map g :=
  (rfl)

/-- **Naturality of `x ↦ g_*(x ⌢ u)`.** For a map of pairs `φ : P ⟶ P'` and maps `g : P.fst ⟶ Z`,
`g' : P'.fst ⟶ Z'`, and `f : Z ⟶ Z'` with `φ ≫ g' = g ≫ f` on ambient spaces,
`f_*(g_*(x ⌢ φ^*u)) = g'_*(φ_*x ⌢ u)`. -/
@[reassoc]
theorem capPushforward_naturality {P P' : TopPair.{w}} (φ : P ⟶ P') {Z Z' : TopCat.{w}}
    (g : P.fst ⟶ Z) (g' : P'.fst ⟶ Z') (f : Z ⟶ Z') (hg : Hom.fst φ ≫ g' = g ≫ f) {n p m : ℕ}
    (h : n + p = m) (u : P'.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    P.capPushforward A g n p m h (TopPair.singularCohomologyMap φ n u) ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map f =
      TopPair.singularHomologyMap φ A m ≫ P'.capPushforward A g' n p m h u := by
  rw [capPushforward_apply, capPushforward_apply, Category.assoc, ← Functor.map_comp, ← hg,
    Functor.map_comp, ← Category.assoc, TopPair.singularCap_naturality, Category.assoc]

/-- Bijectivity of `x ↦ g_*(x ⌢ u)` is invariant under isomorphisms `φ : P ⟶ P'` of pairs and
`f : Z ⟶ Z'` of targets satisfying `φ ≫ g' = g ≫ f` on ambient spaces. -/
theorem bijective_capPushforward_iff_of_isIso {P P' : TopPair.{w}} (φ : P ⟶ P') {Z Z' : TopCat.{w}}
    {g : P.fst ⟶ Z} {g' : P'.fst ⟶ Z'} (f : Z ⟶ Z') [IsIso φ] [IsIso f]
    (hg : Hom.fst φ ≫ g' = g ≫ f) {n p m : ℕ} (h : n + p = m)
    (u : P'.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (P.capPushforward A g n p m h (TopPair.singularCohomologyMap φ n u)) ↔
      Function.Bijective (P'.capPushforward A g' n p m h u) := by
  simp only [← ConcreteCategory.isIso_iff_bijective]
  have hφ : IsIso (TopPair.singularHomologyMap φ A m) :=
    ⟨⟨TopPair.singularHomologyMap (inv φ) A m,
      by rw [← TopPair.singularHomologyMap_comp, IsIso.hom_inv_id, TopPair.singularHomologyMap_id],
      by rw [← TopPair.singularHomologyMap_comp, IsIso.inv_hom_id,
        TopPair.singularHomologyMap_id]⟩⟩
  have hf : IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map f) :=
    inferInstance
  have hc := capPushforward_naturality (A := A) φ g g' f hg h u
  refine ⟨fun h1 ↦ ?_, fun h2 ↦ ?_⟩
  · have : IsIso (TopPair.singularHomologyMap φ A m ≫ P'.capPushforward A g' n p m h u) :=
      hc ▸ IsIso.comp_isIso' h1 hf
    exact IsIso.of_isIso_comp_left (TopPair.singularHomologyMap φ A m) _
  · have : IsIso (P.capPushforward A g n p m h (TopPair.singularCohomologyMap φ n u) ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map f) :=
      hc.symm ▸ IsIso.comp_isIso' hφ h2
    exact IsIso.of_isIso_comp_right _
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map f)

end Basic

/-! ### Chain-level realization of `capPushforward` and comparison with `pullbackCup` -/

section ChainEquivalence

variable {K : Type w} [CommRing K]

/-- On the restricted chain complex `C_{q + r}(X, B; K)`, capping with a relative `r`-cocycle `φ`
with the Koszul sign `(-1)^(r * q)` and pushing forward along `g` is a chain map into
`C_q(Z; K)`. -/
private def capRestrictionChainMap (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) (r : ℕ)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    (P.singularChainComplex (ModuleCat.of K K)).restriction (ComplexShape.embeddingDownNatAdd r) ⟶
      (TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K) where
  f q :=
    ((P.singularChainComplex (ModuleCat.of K K)).restrictionXIso
        (ComplexShape.embeddingDownNatAdd r) (ComplexShape.embeddingDownNatAdd_f r q)).hom ≫
      (((-1 : ℤ) ^ (r * q)) •
        (TauCeti.ChainComplex.capChain K
            (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
            ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
            r q (q + r) (Nat.add_comm r q)
            ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).iCycles r φ) ≫
          (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)).f q))
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst hij
    rw [(P.singularChainComplex (ModuleCat.of K K)).restriction_d_eq
        (ComplexShape.embeddingDownNatAdd r)
        (ComplexShape.embeddingDownNatAdd_f r (j + 1))
        (ComplexShape.embeddingDownNatAdd_f r j)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    let ψ : (P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).X r ⟶ 𝟙_ (ModuleCat.{w} K) :=
      (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).iCycles r φ
    have hcomm : ∀ (n' : ℕ) (hn' : r + (j + 1) = n') (_ : n' = (j + r) + 1),
        (((-1 : ℤ) ^ (r * (j + 1))) •
            (TauCeti.ChainComplex.capChain K
                (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
                ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
                r (j + 1) n' hn' ψ ≫
              (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)).f (j + 1))) ≫
            ((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K)).d (j + 1) j =
          (P.singularChainComplex (ModuleCat.of K K)).d n' (j + r) ≫
            (((-1 : ℤ) ^ (r * j)) •
              (TauCeti.ChainComplex.capChain K
                  (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
                  ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
                  r j (j + r) (Nat.add_comm r j) ψ ≫
                (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)).f j)) := by
      rintro _ hn' rfl
      have hcap : TauCeti.ChainComplex.capChain K
          (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
          r (j + 1) (j + r + 1) hn' ψ ≫
            ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of K K)).d (j + 1) j =
          ((-1 : ℤ) ^ r) • ((P.singularChainComplex (ModuleCat.of K K)).d (j + r + 1) (j + r) ≫
            TauCeti.ChainComplex.capChain K
              (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
              ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
              r j (j + r) (Nat.add_comm r j) ψ) :=
        TauCeti.ChainComplex.capChain_comp_d_of_cycles
          (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
          r j (j + r) (Nat.add_comm r j) φ
      rw [Preadditive.zsmul_comp, Category.assoc, HomologicalComplex.Hom.comm,
        ← Category.assoc, hcap, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
        smul_smul]
      have hsign : (-1 : ℤ) ^ (r * (j + 1)) * (-1 : ℤ) ^ r = (-1 : ℤ) ^ (r * j) := by
        rw [mul_add, mul_one, pow_add, mul_assoc, ← mul_pow]
        simp
      rw [hsign]
    exact hcomm (j + 1 + r) (Nat.add_comm r (j + 1)) (by omega)

/-- The chain map `C_*(X, B; K) ⟶ C_*(Z; K).extend (p ↦ p + r)` realizing signed
cap-and-push-forward with a relative `r`-cocycle `φ` in degrees `≥ r` and zero below degree `r`. -/
private def capExtendChainMap (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) (r : ℕ)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    P.singularChainComplex (ModuleCat.of K K) ⟶
      ((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K)).extend
        (ComplexShape.embeddingDownNatAdd r) :=
  (ComplexShape.embeddingDownNatAdd r).liftExtend (capRestrictionChainMap P g r φ)
    fun _ hj _ _ ↦ hj.false_of_isTruncLE.elim

private theorem capExtendChainMap_f (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z)
    (r q m : ℕ) (hq : (ComplexShape.embeddingDownNatAdd r).f q = m)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    (capExtendChainMap P g r φ).f m =
      ((P.singularChainComplex (ModuleCat.of K K)).restrictionXIso
          (ComplexShape.embeddingDownNatAdd r) hq).inv ≫
        (capRestrictionChainMap P g r φ).f q ≫
          (((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K)).extendXIso
            (ComplexShape.embeddingDownNatAdd r) hq).inv :=
  (ComplexShape.embeddingDownNatAdd r).liftExtend_f (capRestrictionChainMap P g r φ) _ hq

/-- In degree `q + r`, `capExtendChainMap` induces `(-1)^(r * q)` times `capPushforward` on
homology, under `extendHomologyIso`. -/
private theorem homologyMap_capExtendChainMap_comp_extendHomologyIso (P : TopPair.{w})
    {Z : TopCat.{w}} (g : P.fst ⟶ Z) (r q : ℕ)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    homologyMap (capExtendChainMap P g r φ) (q + r) ≫
        (((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K)).extendHomologyIso
          (ComplexShape.embeddingDownNatAdd r) (ComplexShape.embeddingDownNatAdd_f r q)).hom =
      ((-1 : ℤ) ^ (r * q)) • P.capPushforward (ModuleCat.of K K) g r q (q + r) (Nat.add_comm r q)
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ) := by
  let e := ComplexShape.embeddingDownNatAdd r
  have hq : e.f q = q + r := ComplexShape.embeddingDownNatAdd_f r q
  let L := (TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K)
  let φ' : ((P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K
      (𝟙_ (ModuleCat.{w} K))).cycles r := φ
  let mid : (P.singularChainComplex (ModuleCat.of K K)).cycles (q + r) ⟶ L.homology q :=
    ((-1 : ℤ) ^ (r * q)) •
      (TauCeti.ChainComplex.capCycles K
          (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
          r q (q + r) (Nat.add_comm r q) φ' ≫
        cyclesMap (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)) q ≫
        L.homologyπ q)
  refine (cancel_epi ((P.singularChainComplex (ModuleCat.of K K)).homologyπ (q + r))).1 ?_
  have lhs_eq :
      (P.singularChainComplex (ModuleCat.of K K)).homologyπ (q + r) ≫
        (homologyMap (capExtendChainMap P g r φ) (q + r) ≫ (L.extendHomologyIso e hq).hom) =
      mid := by
    rw [homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom]
    have hcyc : cyclesMap (capExtendChainMap P g r φ) (q + r) ≫ (L.extendCyclesIso e hq).hom =
        ((-1 : ℤ) ^ (r * q)) •
          (TauCeti.ChainComplex.capCycles K
              (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
              ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
              r q (q + r) (Nat.add_comm r q) φ' ≫
            cyclesMap (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)) q) := by
      rw [← cancel_mono (L.iCycles q), Category.assoc, extendCyclesIso_hom_iCycles,
        cyclesMap_i_assoc, Preadditive.zsmul_comp, Category.assoc, cyclesMap_i,
        TauCeti.ChainComplex.capCycles_i_assoc]
      have hcap_f : (capExtendChainMap P g r φ).f (q + r) ≫ (L.extendXIso e hq).hom =
          ((-1 : ℤ) ^ (r * q)) •
            (TauCeti.ChainComplex.capChain K
                (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
                ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
                r q (q + r) (Nat.add_comm r q)
                ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).iCycles r φ) ≫
              (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)).f q) := by
        rw [capExtendChainMap_f P g r q (q + r) hq φ]
        dsimp only [capRestrictionChainMap, e, L]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.zsmul_comp, Iso.inv_hom_id,
          Category.comp_id]
      rw [hcap_f, Preadditive.comp_zsmul]
      rfl
    rw [reassoc_of% hcyc, Preadditive.zsmul_comp, Category.assoc]
  have rhs_eq :
      (P.singularChainComplex (ModuleCat.of K K)).homologyπ (q + r) ≫
        (((-1 : ℤ) ^ (r * q)) • P.capPushforward (ModuleCat.of K K) g r q (q + r)
          (Nat.add_comm r q)
          ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ)) =
      mid := by
    rw [Preadditive.comp_zsmul]
    refine congrArg (((-1 : ℤ) ^ (r * q)) • ·) ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) q).obj
          (ModuleCat.of K K)).map g)
        (TopPair.singularCap_homologyπ P K (λ_ (ModuleCat.of K K)).inv
          (λ_ (ModuleCat.of K K)).hom r q (q + r) (Nat.add_comm r q) φ)).trans
        ((Category.assoc _ _ _).trans
          (congrArg _ (homologyπ_naturality
            (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)) q))))
  exact lhs_eq.trans rhs_eq.symm

private theorem isIso_neg_one_pow_zsmul_iff {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (n : ℕ) (f : X ⟶ Y) :
    IsIso (((-1 : ℤ) ^ n) • f) ↔ IsIso f := by
  have hinv : ∀ {g : X ⟶ Y}, IsIso g → IsIso (((-1 : ℤ) ^ n) • g) := fun ⟨⟨gi, h₁, h₂⟩⟩ ↦
    ⟨⟨((-1 : ℤ) ^ n) • gi,
      by rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← mul_pow]; simp [h₁],
      by rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← mul_pow]; simp [h₂]⟩⟩
  refine ⟨fun h ↦ ?_, hinv⟩
  have h' := hinv h
  rwa [smul_smul, ← mul_pow, show (-1 : ℤ) * -1 = 1 from rfl, one_pow, one_smul] at h'

/-- When `Hₘ(X, B; K) = 0` for `m < r`, `capExtendChainMap` is a quasi-isomorphism if and only if
`capPushforward` with coefficients `K` is bijective in every degree `r + q`. -/
private theorem quasiIso_capExtendChainMap_iff (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z)
    (r : ℕ) (hzero : ∀ m < r, IsZero (P.singularHomology (ModuleCat.of K K) m))
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    QuasiIso (capExtendChainMap P g r φ) ↔
      ∀ p m (h : r + p = m), Function.Bijective
        (P.capPushforward (ModuleCat.of K K) g r p m h
          ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ)) := by
  let e := ComplexShape.embeddingDownNatAdd r
  let L := (TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K)
  let u := (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ
  constructor
  · intro hq p m hm
    subst hm
    suffices ∀ (m' : ℕ) (hm₀ : r + p = m') (_ : m' = p + r),
        Function.Bijective (P.capPushforward (ModuleCat.of K K) g r p m' hm₀ u) from
      this (r + p) rfl (Nat.add_comm r p)
    rintro _ hm₀ rfl
    rw [← ConcreteCategory.isIso_iff_bijective, ← isIso_neg_one_pow_zsmul_iff (r * p),
      ← homologyMap_capExtendChainMap_comp_extendHomologyIso P g r p φ]
    exact IsIso.comp_isIso' ((quasiIsoAt_iff_isIso_homologyMap _ _).1 (hq.1 (p + r)))
      (L.extendHomologyIso e (ComplexShape.embeddingDownNatAdd_f r p)).isIso_hom
  · intro hbij
    rw [quasiIso_iff]
    intro m
    rw [quasiIsoAt_iff_isIso_homologyMap]
    by_cases hmr : m < r
    · exact (hzero m hmr).isIso
        ((L.extend_exactAt e m (fun p hp ↦ by simp [e] at hp; omega)).isZero_homology) _
    · obtain ⟨p, rfl⟩ : ∃ p, p + r = m := ⟨m - r, by omega⟩
      have hp : e.f p = p + r := ComplexShape.embeddingDownNatAdd_f r p
      have hsmul : IsIso (((-1 : ℤ) ^ (r * p)) •
          P.capPushforward (ModuleCat.of K K) g r p (p + r) (Nat.add_comm r p) u) :=
        (isIso_neg_one_pow_zsmul_iff (r * p) _).2
          ((ConcreteCategory.isIso_iff_bijective _).2 (hbij p (p + r) (Nat.add_comm r p)))
      have : IsIso (homologyMap (capExtendChainMap P g r φ) (p + r) ≫
          (L.extendHomologyIso e hp).hom) :=
        (homologyMap_capExtendChainMap_comp_extendHomologyIso P g r p φ).symm ▸ hsmul
      exact IsIso.of_isIso_comp_right _ (L.extendHomologyIso e hp).hom

/-- The embedding `n ↦ n + r` of `ComplexShape.up ℕ` into itself, with syntactic shape `up ℕ`. -/
private def embeddingUpNatAdd (r : ℕ) : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.embeddingUp'Add (1 : ℕ) r

@[simp]
private theorem embeddingUpNatAdd_f (r n : ℕ) : (embeddingUpNatAdd r).f n = n + r := (rfl)

private instance (r : ℕ) : (embeddingUpNatAdd r).IsRelIff :=
  inferInstanceAs (ComplexShape.embeddingUp'Add (1 : ℕ) r).IsRelIff

/-- Degreewise component of `linearYonedaObjExtendIso`. -/
private def linearYonedaObjExtendXIso (L : ChainComplex (ModuleCat.{w} K) ℕ)
    (M : ModuleCat.{w} K) (r m : ℕ) :
    ((L.linearYonedaObj K M).extend (embeddingUpNatAdd r)).X m ≅
      (ChainComplex.linearYonedaObj (L.extend (ComplexShape.embeddingDownNatAdd r)) K M).X m :=
  if hm : r ≤ m then
    have hq_up : (embeddingUpNatAdd r).f (m - r) = m := by simp; omega
    have hq_dn : (ComplexShape.embeddingDownNatAdd r).f (m - r) = m := by simp; omega
    ((L.linearYonedaObj K M).extendXIso (embeddingUpNatAdd r) hq_up) ≪≫
      ((linearYoneda K (ModuleCat.{w} K)).obj M).mapIso
        (L.extendXIso (ComplexShape.embeddingDownNatAdd r) hq_dn).op
  else
    have hno_up : ∀ q, (embeddingUpNatAdd r).f q ≠ m := by simp; omega
    have hno_dn : ∀ q, (ComplexShape.embeddingDownNatAdd r).f q ≠ m := by simp; omega
    IsZero.iso
      ((L.linearYonedaObj K M).isZero_extend_X (embeddingUpNatAdd r) m hno_up)
      (((linearYoneda K (ModuleCat.{w} K)).obj M).map_isZero
        (L.isZero_extend_X (ComplexShape.embeddingDownNatAdd r) m hno_dn).op)

private theorem linearYonedaObjExtendXIso_hom_apply (L : ChainComplex (ModuleCat.{w} K) ℕ)
    (M : ModuleCat.{w} K) {r q m : ℕ}
    (hq_up : (embeddingUpNatAdd r).f q = m)
    (hq_dn : (ComplexShape.embeddingDownNatAdd r).f q = m)
    (y : ((L.linearYonedaObj K M).extend (embeddingUpNatAdd r)).X m) :
    (linearYonedaObjExtendXIso L M r m).hom y =
      (L.extendXIso (ComplexShape.embeddingDownNatAdd r) hq_dn).hom ≫
        ((L.linearYonedaObj K M).extendXIso (embeddingUpNatAdd r) hq_up).hom y := by
  obtain rfl : q = m - r := by simp at hq_dn; omega
  dsimp only [linearYonedaObjExtendXIso]
  split_ifs with hm
  · rfl
  · simp at hq_dn; omega

/-- Applying `Hom(-, M)` to an extended chain complex `L.extend (embeddingDownNatAdd r)` is
isomorphic to extending `Hom(L, M)` along `embeddingUpNatAdd r`. -/
private def linearYonedaObjExtendIso (L : ChainComplex (ModuleCat.{w} K) ℕ)
    (M : ModuleCat.{w} K) (r : ℕ) :
    (L.linearYonedaObj K M).extend (embeddingUpNatAdd r) ≅
      ChainComplex.linearYonedaObj (L.extend (ComplexShape.embeddingDownNatAdd r)) K M :=
  HomologicalComplex.Hom.isoOfComponents (linearYonedaObjExtendXIso L M r) fun i j hij ↦ by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    by_cases hi : r ≤ i
    · have hq_up : (embeddingUpNatAdd r).f (i - r) = i := by simp; omega
      have hq1_up : (embeddingUpNatAdd r).f (i - r + 1) = i + 1 := by simp; omega
      have hq_dn : (ComplexShape.embeddingDownNatAdd r).f (i - r) = i := by simp; omega
      have hq1_dn : (ComplexShape.embeddingDownNatAdd r).f (i - r + 1) = i + 1 := by simp; omega
      refine ConcreteCategory.hom_ext _ _ fun y ↦ ?_
      simp only [ModuleCat.comp_apply]
      let g₀ : L.X (i - r) ⟶ M :=
        ((L.linearYonedaObj K M).extendXIso (embeddingUpNatAdd r) hq_up).hom y
      have hlhs : ((linearYonedaObjExtendXIso L M r (i + 1)).hom)
            ((((L.linearYonedaObj K M).extend (embeddingUpNatAdd r)).d i (i + 1)) y) =
          (L.extendXIso (ComplexShape.embeddingDownNatAdd r) hq1_dn).hom ≫
            L.d (i - r + 1) (i - r) ≫ g₀ := by
        have hy := ConcreteCategory.congr_hom
          ((L.linearYonedaObj K M).extend_d_eq (embeddingUpNatAdd r) hq_up hq1_up) y
        refine (congrArg ((linearYonedaObjExtendXIso L M r (i + 1)).hom) hy).trans
          ((linearYonedaObjExtendXIso_hom_apply L M hq1_up hq1_dn _).trans ?_)
        simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
        rfl
      have hrhs : (((ChainComplex.linearYonedaObj (L.extend (ComplexShape.embeddingDownNatAdd r))
              K M).d i (i + 1)) ((linearYonedaObjExtendXIso L M r i).hom y)) =
          (L.extendXIso (ComplexShape.embeddingDownNatAdd r) hq1_dn).hom ≫
            L.d (i - r + 1) (i - r) ≫ g₀ := by
        have hy : (((ChainComplex.linearYonedaObj (L.extend (ComplexShape.embeddingDownNatAdd r))
              K M).d i (i + 1)) ((linearYonedaObjExtendXIso L M r i).hom y)) =
            (L.extend (ComplexShape.embeddingDownNatAdd r)).d (i + 1) i ≫
              (L.extendXIso (ComplexShape.embeddingDownNatAdd r) hq_dn).hom ≫ g₀ :=
          congrArg ((L.extend (ComplexShape.embeddingDownNatAdd r)).d (i + 1) i ≫ ·)
            (linearYonedaObjExtendXIso_hom_apply L M hq_up hq_dn y)
        refine hy.trans ?_
        rw [L.extend_d_eq (ComplexShape.embeddingDownNatAdd r) hq1_dn hq_dn, Category.assoc,
          Category.assoc, Iso.inv_hom_id_assoc]
      exact hrhs.trans hlhs.symm
    · exact ((L.linearYonedaObj K M).isZero_extend_X
        (embeddingUpNatAdd r) i (by simp; omega)).eq_of_src _ _

/-- In degree `q + r`, applying `Hom(-, M)` to `capExtendChainMap` induces `pullbackCup` on
cohomology, under `linearYonedaObjExtendIso` and `extendHomologyIso`. -/
private theorem extendHomologyIso_inv_comp_homologyMap_linearYonedaFunctor_capExtendChainMap
    (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) (M : ModuleCat.{w} K) (r q : ℕ)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r)
    (a : Z.singularCohomology (ModuleCat.of K K) K M q) :
    homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
        (capExtendChainMap P g r φ).op) (q + r)
      (homologyMap (linearYonedaObjExtendIso
          ((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K)) M r).hom (q + r)
        (((Z.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
          (embeddingUpNatAdd r) (embeddingUpNatAdd_f r q)).inv a)) =
      P.pullbackCup M g r q (q + r) rfl
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ) a := by
  let e := ComplexShape.embeddingDownNatAdd r
  let e_up := embeddingUpNatAdd r
  have hq : e.f q = q + r := ComplexShape.embeddingDownNatAdd_f r q
  have hq_up : e_up.f q = q + r := embeddingUpNatAdd_f r q
  let L := (TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K)
  obtain ⟨α, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q a
  let β : (ChainComplex.linearYonedaObj (L.extend e) K M).cycles (q + r) :=
    cyclesMap (linearYonedaObjExtendIso L M r).hom (q + r)
      (((Z.singularCochainComplex (ModuleCat.of K K) K M).extendCyclesIso e_up hq_up).inv α)
  -- Express the inverse of `extendHomologyIso` on the cocycle `α`.
  have hα : ((Z.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso e_up hq_up).inv
        ((Z.singularCochainComplex (ModuleCat.of K K) K M).homologyπ q α) =
      ((Z.singularCochainComplex (ModuleCat.of K K) K M).extend e_up).homologyπ (q + r)
        (((Z.singularCochainComplex (ModuleCat.of K K) K M).extendCyclesIso e_up hq_up).inv α) := by
    have := ConcreteCategory.congr_hom
      (homologyπ_extendHomologyIso_hom (Z.singularCochainComplex (ModuleCat.of K K) K M)
        (e := e_up) (hj' := hq_up))
      (((Z.singularCochainComplex (ModuleCat.of K K) K M).extendCyclesIso e_up hq_up).inv α)
    simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply] at this
    rw [← this, Iso.hom_inv_id_apply]
  refine (congrArg _ (congrArg _ hα)).trans ?_
  refine (congrArg _ (ConcreteCategory.congr_hom
    (homologyπ_naturality (linearYonedaObjExtendIso L M r).hom (q + r))
    (((Z.singularCochainComplex (ModuleCat.of K K) K M).extendCyclesIso e_up hq_up).inv
      α))).trans ?_
  refine (TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_homologyπ_apply
    (capExtendChainMap P g r φ) (q + r) β).trans ?_
  -- Identify the pushed-forward cocycle on `C_{q + r}(X, B; K)` with `(-1)^(r * q) • (φ ⌣ g^*α)`.
  have hcocycle :
      HomologicalComplex.cyclesMap (K := ChainComplex.linearYonedaObj (L.extend e) K M)
          (L := (P.singularChainComplex (ModuleCat.of K K)).linearYonedaObj K M)
          ((TauCeti.ChainComplex.linearYonedaFunctor K M).map (capExtendChainMap P g r φ).op)
          (q + r) β =
      ((-1 : ℤ) ^ (r * q)) • TauCeti.ChainComplex.cupCycles K
        (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv) (λ_ M).hom
        r q (q + r) (Nat.add_comm r q) φ
        (cyclesMap (TopCat.singularCochainComplexMap g) q α) := by
    apply HomologicalComplex.moduleCat_iCycles_injective
    refine (TauCeti.ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply
      (capExtendChainMap P g r φ) (q + r) β).trans ?_
    rw [map_zsmul, TauCeti.ChainComplex.iCycles_cupCycles,
      TauCeti.ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply]
    let α₀ : L.X q ⟶ M := (Z.singularCochainComplex (ModuleCat.of K K) K M).iCycles q α
    have hβ : (ChainComplex.linearYonedaObj (L.extend e) K M).iCycles (q + r) β =
        (L.extendXIso e hq).hom ≫ α₀ := by
      have hc2 := ConcreteCategory.congr_hom
        (cyclesMap_i (linearYonedaObjExtendIso L M r).hom (q + r))
        (((Z.singularCochainComplex (ModuleCat.of K K) K M).extendCyclesIso e_up hq_up).inv α)
      have hc3 := ConcreteCategory.congr_hom
        (extendCyclesIso_inv_iCycles (Z.singularCochainComplex (ModuleCat.of K K) K M)
          (e := e_up) (hj' := hq_up)) α
      simp only [ModuleCat.comp_apply] at hc2 hc3
      refine hc2.trans ?_
      dsimp only [linearYonedaObjExtendIso, Hom.isoOfComponents_hom_f]
      exact (congrArg ((linearYonedaObjExtendXIso L M r (q + r)).hom) hc3).trans
        ((linearYonedaObjExtendXIso_hom_apply L M hq_up hq _).trans
          (congrArg ((L.extendXIso e hq).hom ≫ ·)
            (((L.linearYonedaObj K M).extendXIso (embeddingUpNatAdd r) hq_up).inv_hom_id_apply α₀)))
    rw [hβ, capExtendChainMap_f P g r q (q + r) hq φ]
    dsimp only [capRestrictionChainMap, e, L]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.zsmul_comp]
    congr 1
    refine TauCeti.ChainComplex.capChain_comp _ _ (λ_ M).hom r q (q + r) (Nat.add_comm r q) _ _ _ ?_
    rw [SSet.chainComplexPairing_leftUnitor_hom_f]
    exact (leftUnitor_naturality _).symm
  refine (congrArg ((P.singularCochainComplex (ModuleCat.of K K) K M).homologyπ (q + r))
    hcocycle).trans ?_
  rw [map_zsmul, ← TauCeti.ChainComplex.cup_homologyπ]
  -- `cyclesMap (singularCochainComplexMap g) q α` represents `singularCohomologyMap g q [α]`.
  have hgα : ((P.fst.singularCochainComplex (ModuleCat.of K K) K M).homologyπ q
        (cyclesMap (TopCat.singularCochainComplexMap g) q α)) =
      TopCat.singularCohomologyMap g q
        ((Z.singularCochainComplex (ModuleCat.of K K) K M).homologyπ q α) :=
    (ConcreteCategory.congr_hom (homologyπ_naturality (TopCat.singularCochainComplexMap g) q)
      α).symm
  rw [hgα, TopPair.singularCup_gradedComm (k := K) P
      (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u' := (λ_ (ModuleCat.of K K)).inv)
      (μ := (ρ_ M).hom) (μ' := (λ_ M).hom) ?_ ?_ (rfl : q + r = q + r),
    smul_smul, mul_comm r q, ← mul_pow]
  · simp only [show (-1 : ℤ) * -1 = 1 from rfl, one_pow, one_smul, pullbackCup_apply]
    rfl
  · rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, ← unitors_inv_equal]
    rfl
  · exact braiding_leftUnitor M

/-- When `Hₘ(X, B; K) = 0` for `m < r`, `Hom(capExtendChainMap, M)` is a quasi-isomorphism if and
only if `pullbackCup M` is bijective in every degree `p + r`. -/
private theorem quasiIso_linearYonedaFunctor_capExtendChainMap_iff (P : TopPair.{w})
    {Z : TopCat.{w}} (g : P.fst ⟶ Z) (M : ModuleCat.{w} K) (r : ℕ)
    (hzero : ∀ m < r, IsZero (P.singularHomology (ModuleCat.of K K) m))
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
        (capExtendChainMap P g r φ).op) ↔
      ∀ p m (h : p + r = m), Function.Bijective
        (P.pullbackCup M g r p m h
          ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ)) := by
  let e := ComplexShape.embeddingDownNatAdd r
  let e_up := embeddingUpNatAdd r
  let L := (TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K)
  let u := (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ
  let iso_ext := linearYonedaObjExtendIso L M r
  constructor
  · intro hq p m hm
    subst hm
    have hp_up : e_up.f p = p + r := embeddingUpNatAdd_f r p
    have h1 : Function.Bijective (homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
        (capExtendChainMap P g r φ).op) (p + r)) :=
      (ConcreteCategory.isIso_iff_bijective _).1
        ((quasiIsoAt_iff_isIso_homologyMap _ _).1 (hq.1 (p + r)))
    have h2 : Function.Bijective (homologyMap iso_ext.hom (p + r)) :=
      (ConcreteCategory.isIso_iff_bijective _).1 ((homologyMapIso iso_ext (p + r)).isIso_hom)
    have h3 : Function.Bijective
        (((Z.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso e_up hp_up).inv) :=
      (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
    have hcomp : ⇑(P.pullbackCup M g r p (p + r) rfl u) =
        ⇑(homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
            (capExtendChainMap P g r φ).op) (p + r)) ∘
          ⇑(homologyMap iso_ext.hom (p + r)) ∘
            ⇑(((Z.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
              e_up hp_up).inv) :=
      funext fun a ↦
        (extendHomologyIso_inv_comp_homologyMap_linearYonedaFunctor_capExtendChainMap
          P g M r p φ a).symm
    rw [hcomp]
    exact h1.comp (h2.comp h3)
  · intro hbij
    rw [quasiIso_iff]
    intro m
    rw [quasiIsoAt_iff_isIso_homologyMap]
    by_cases hmr : m < r
    · have hsrc : IsZero ((ChainComplex.linearYonedaObj (L.extend e) K M).homology m) :=
        (((Z.singularCochainComplex (ModuleCat.of K K) K M).extend_exactAt e_up m
          (fun p hp ↦ by simp [e_up] at hp; omega)).isZero_homology).of_iso
          (homologyMapIso iso_ext m).symm
      have htgt : IsZero (P.singularCohomology (ModuleCat.of K K) K M m) :=
        TopPair.isZero_singularCohomology_of_isZero_singularHomology P (ModuleCat.of K K) M m
          fun j hj ↦ hzero j (Nat.lt_of_le_of_lt hj hmr)
      exact hsrc.isIso htgt _
    · obtain ⟨p, rfl⟩ : ∃ p, p + r = m := ⟨m - r, by omega⟩
      have hp_up : e_up.f p = p + r := embeddingUpNatAdd_f r p
      rw [ConcreteCategory.isIso_iff_bijective]
      have h2 : Function.Bijective (homologyMap iso_ext.hom (p + r)) :=
        (ConcreteCategory.isIso_iff_bijective _).1 ((homologyMapIso iso_ext (p + r)).isIso_hom)
      have h3 : Function.Bijective
          (((Z.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso e_up hp_up).inv) :=
        (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
      have hcomp : ⇑(homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
            (capExtendChainMap P g r φ).op) (p + r)) ∘
          (⇑(homologyMap iso_ext.hom (p + r)) ∘
            ⇑(((Z.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
              e_up hp_up).inv)) =
          ⇑(P.pullbackCup M g r p (p + r) rfl u) :=
        funext fun a ↦
          extendHomologyIso_inv_comp_homologyMap_linearYonedaFunctor_capExtendChainMap
            P g M r p φ a
      exact (Function.Bijective.of_comp_iff _ (h2.comp h3)).1 (hcomp.symm ▸ hbij p (p + r) rfl)

/-- **Equivalence between `pullbackCup` and `capPushforward` across all degrees.** Let `P = (X, B)`
be a topological pair with `Hₘ(X, B; K) = 0` for all `m < r`, let `g : X ⟶ Z`, and let
`u ∈ Hʳ(X, B; K)`. Over any commutative ring `K`, `a ↦ g^*a ⌣ u` is bijective for every `K`-module
`M` and every degree `p` if and only if `x ↦ g_*(x ⌢ u)` with coefficients `K` is bijective for
every degree `p`. -/
theorem forall_bijective_pullbackCup_iff_forall_bijective_capPushforward (P : TopPair.{w})
    {Z : TopCat.{w}} (g : P.fst ⟶ Z) (r : ℕ)
    (hzero : ∀ m < r, IsZero (P.singularHomology (ModuleCat.of K K) m))
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) r) :
    (∀ (M : ModuleCat.{w} K) (p m : ℕ) (h : p + r = m),
        Function.Bijective (P.pullbackCup M g r p m h u)) ↔
      (∀ (p m : ℕ) (h : r + p = m),
        Function.Bijective (P.capPushforward (ModuleCat.of K K) g r p m h u)) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ r u
  have : ∀ n, Projective ((P.singularChainComplex (ModuleCat.of K K)).X n) :=
    fun n ↦ SSetPair.projective_chainComplex_X (ModuleCat.of K K) (toSSetPair.obj P) n
  have : ∀ n, Projective (((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K)).X n) :=
    inferInstance
  rw [← quasiIso_capExtendChainMap_iff P g r hzero φ,
    ChainComplex.quasiIso_iff_forall_quasiIso_linearYonedaFunctor_map_of_projective
      (capExtendChainMap P g r φ) K]
  exact forall_congr' fun M ↦
    (quasiIso_linearYonedaFunctor_capExtendChainMap_iff P g M r hzero φ).symm

/-! ### Passage from `K`-coefficients to arbitrary `K`-module coefficients `A` in homology -/

/-- For an invertible coefficient pairing, the induced chain map on relative simplicial chains
is an isomorphism. -/
private theorem isIso_ssetPair_chainComplexPairing (Q : SSetPair.{w}) (A : ModuleCat.{w} K) :
    IsIso (Q.chainComplexPairing (ρ_ A).hom) := by
  have hdeg : ∀ n, IsIso ((Q.chainComplexPairing (ρ_ A).hom).f n) := fun n ↦ by
    let S : ModuleCat.{w} K := 𝟙_ (ModuleCat.{w} K)
    let h₂ := (SSetPair.chainComplexXSplitting A Q n).gIsCokernel
    have : IsIso ((Q.left.chainComplexPairing (ρ_ A).hom).f n) :=
      ((eval _ _ n).mapIso (asIso (Q.left.chainComplexPairing (ρ_ A).hom))).isIso_hom
    have : IsIso ((Q.right.chainComplexPairing (ρ_ A).hom).f n) :=
      ((eval _ _ n).mapIso (asIso (Q.right.chainComplexPairing (ρ_ A).hom))).isIso_hom
    let α₁ : A ⊗ (Q.left.chainComplex S).X n ≅ (Q.left.chainComplex A).X n :=
      asIso ((Q.left.chainComplexPairing (ρ_ A).hom).f n)
    let α₂ : A ⊗ (Q.right.chainComplex S).X n ≅ (Q.right.chainComplex A).X n :=
      asIso ((Q.right.chainComplexPairing (ρ_ A).hom).f n)
    have hcomm : (A ◁ (SSet.chainComplexMap Q.hom S).f n) ≫ α₂.hom =
        α₁.hom ≫ (SSet.chainComplexMap Q.hom A).f n :=
      congrArg (fun ψ ↦ ψ.f n) (SSet.chainComplexPairing_naturality Q.hom (ρ_ A).hom)
    have hw : (SSet.chainComplexMap Q.hom A).f n ≫
        (α₂.inv ≫ (A ◁ (Q.chainComplexπ S).f n)) = 0 := by
      rw [← cancel_epi α₁.hom, ← Category.assoc, ← hcomm, Category.assoc, Iso.hom_inv_id_assoc,
        ← whiskerLeft_comp, Q.chainComplex_condition_f, MonoidalPreadditive.whiskerLeft_zero,
        comp_zero]
    obtain ⟨inv_n, hinv_n⟩ := CokernelCofork.IsColimit.desc' h₂
      (α₂.inv ≫ (A ◁ (Q.chainComplexπ S).f n)) hw
    have hinv_n' : (Q.chainComplexπ A).f n ≫ inv_n =
        α₂.inv ≫ (A ◁ (Q.chainComplexπ S).f n) := hinv_n
    refine ⟨⟨inv_n, ?_, ?_⟩⟩
    · rw [← cancel_epi (A ◁ (Q.chainComplexπ S).f n),
        SSetPair.whiskerLeft_chainComplexπ_f_chainComplexPairing_f_assoc]
      dsimp
      rw [Category.comp_id, hinv_n']
      exact Iso.hom_inv_id_assoc α₂ _
    · rw [← cancel_epi ((Q.chainComplexπ A).f n), Category.comp_id, reassoc_of% hinv_n',
        SSetPair.whiskerLeft_chainComplexπ_f_chainComplexPairing_f]
      exact Iso.inv_hom_id_assoc α₂ _
  exact (HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso ((Q.chainComplexPairing (ρ_ A).hom).f n))
    (fun i j _ ↦ by simp)).isIso_hom

/-- Degreewise component of `tensorLeftExtendIso`. -/
private def tensorLeftExtendXIso (A : ModuleCat.{w} K) (L : ChainComplex (ModuleCat.{w} K) ℕ)
    (r m : ℕ) :
    ((((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (L.extend (ComplexShape.embeddingDownNatAdd r))).X m) ≅
      ((((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj L).extend
        (ComplexShape.embeddingDownNatAdd r)).X m :=
  if hm : r ≤ m then
    have hq : (ComplexShape.embeddingDownNatAdd r).f (m - r) = m := by simp; omega
    (tensorLeft A).mapIso (L.extendXIso (ComplexShape.embeddingDownNatAdd r) hq) ≪≫
      ((((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj L).extendXIso
        (ComplexShape.embeddingDownNatAdd r) hq).symm
  else
    have hno : ∀ q, (ComplexShape.embeddingDownNatAdd r).f q ≠ m := by simp; omega
    IsZero.iso
      ((tensorLeft A).map_isZero (L.isZero_extend_X (ComplexShape.embeddingDownNatAdd r) m hno))
      ((((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj L).isZero_extend_X
        (ComplexShape.embeddingDownNatAdd r) m hno)

private theorem tensorLeftExtendXIso_hom_eq (A : ModuleCat.{w} K)
    (L : ChainComplex (ModuleCat.{w} K) ℕ) {r q m : ℕ}
    (hq : (ComplexShape.embeddingDownNatAdd r).f q = m) :
    (tensorLeftExtendXIso A L r m).hom =
      (A ◁ (L.extendXIso (ComplexShape.embeddingDownNatAdd r) hq).hom) ≫
        ((((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj L).extendXIso
          (ComplexShape.embeddingDownNatAdd r) hq).inv := by
  obtain rfl : q = m - r := by simp at hq; omega
  dsimp only [tensorLeftExtendXIso]
  split_ifs with hm
  · rfl
  · simp at hq; omega

/-- Tensoring an extended chain complex `L.extend e` on the left by `A` is isomorphic to extending
`A ⊗ L` along `e`. -/
private def tensorLeftExtendIso (A : ModuleCat.{w} K) (L : ChainComplex (ModuleCat.{w} K) ℕ)
    (r : ℕ) :
    (((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (L.extend (ComplexShape.embeddingDownNatAdd r))) ≅
      (((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj L).extend
        (ComplexShape.embeddingDownNatAdd r) :=
  HomologicalComplex.Hom.isoOfComponents (tensorLeftExtendXIso A L r) fun i j hij ↦ by
    simp only [ComplexShape.down_Rel] at hij
    subst hij
    by_cases hj : r ≤ j
    · have hq : (ComplexShape.embeddingDownNatAdd r).f (j - r) = j := by simp; omega
      have hq1 : (ComplexShape.embeddingDownNatAdd r).f (j - r + 1) = j + 1 := by simp; omega
      rw [tensorLeftExtendXIso_hom_eq A L hq, tensorLeftExtendXIso_hom_eq A L hq1]
      dsimp only [Functor.mapHomologicalComplex_obj_d]
      rw [L.extend_d_eq (ComplexShape.embeddingDownNatAdd r) hq1 hq,
        (((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj L).extend_d_eq
          (ComplexShape.embeddingDownNatAdd r) hq1 hq]
      simp
    · exact ((((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj L).isZero_extend_X
        (ComplexShape.embeddingDownNatAdd r) j (by simp; omega)).eq_of_tgt _ _

/-- Tensoring `capChain` with `K` coefficients on the left by `A` intertwines with `capChain` with
`A` coefficients under `chainComplexPairing (ρ_ A).hom`. -/
private theorem whiskerLeft_capChain_comp_chainComplexPairing (P : TopPair.{w})
    {Z : TopCat.{w}} (g : P.fst ⟶ Z) (A : ModuleCat.{w} K) (r q : ℕ)
    (φ : (P.singularChainComplex (ModuleCat.of K K)).X r ⟶ ModuleCat.of K K) :
    (A ◁ (TauCeti.ChainComplex.capChain K
          (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
          r q (q + r) (Nat.add_comm r q) φ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)).f q)) ≫
      ((TopCat.toSSet.obj Z).chainComplexPairing (ρ_ A).hom).f q =
    ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom).f (q + r) ≫
      TauCeti.ChainComplex.capChain K (P.alexanderWhitneyDiagonal (λ_ A).inv)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom)
          r q (q + r) (Nat.add_comm r q) φ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map g) A).f q := by
  rw [← cancel_epi (A ◁ ((toSSetPair.obj P).chainComplexπ (ModuleCat.of K K)).f (q + r)),
    SSetPair.whiskerLeft_chainComplexπ_f_chainComplexPairing_f_assoc]
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (tensorLeft A) _ _
    (((toSSetPair.obj P).right).isColimitChainComplexXCofan (ModuleCat.of K K) (q + r))) _ _
    fun σ ↦ ?_
  simp only [cofan_mk_inj, curriedTensor_obj_map]
  dsimp only [Cofan.mk_pt, curriedTensor_obj_obj]
  let c : ModuleCat.of K K ⟶ ModuleCat.of K K :=
    (TopCat.toSSet.obj P.fst).ιChainComplex
        ((TopCat.toSSet.obj P.fst).map (SimplexCategory.subinterval 0 r (by omega)).op σ) ≫
      (P.singularChainComplexπ (ModuleCat.of K K)).f r ≫ φ
  let τ : (TopCat.toSSet.obj Z) _⦋q⦌ :=
    (TopCat.toSSet.map g).app _
      ((TopCat.toSSet.obj P.fst).map (SimplexCategory.subinterval r q (by omega)).op σ)
  have hK : (toSSetPair.obj P).right.ιChainComplex σ ≫
        (((toSSetPair.obj P).chainComplexπ (ModuleCat.of K K)).f (q + r) ≫
          TauCeti.ChainComplex.capChain K
            (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
            ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
            r q (q + r) (Nat.add_comm r q) φ ≫
          (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)).f q) =
      (λ_ (ModuleCat.of K K)).inv ≫ (c ▷ ModuleCat.of K K) ≫ (λ_ (ModuleCat.of K K)).hom ≫
        (TopCat.toSSet.obj Z).ιChainComplex τ :=
    ((reassoc_of% (TopPair.ιChainComplex_singularChainComplexπ_capChain_alexanderWhitneyDiagonal
      P K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom r q (q + r)
      (Nat.add_comm r q) φ σ))
      ((SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)).f q)).trans
      (by simp only [SSet.ι_chainComplexMap_f]; rfl)
  have hA : (toSSetPair.obj P).right.ιChainComplex σ ≫
        (((toSSetPair.obj P).chainComplexπ A).f (q + r) ≫
          TauCeti.ChainComplex.capChain K
            (P.alexanderWhitneyDiagonal (λ_ A).inv)
            ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom)
            r q (q + r) (Nat.add_comm r q) φ ≫
          (SSet.chainComplexMap (TopCat.toSSet.map g) A).f q) =
      (λ_ A).inv ≫ (c ▷ A) ≫ (λ_ A).hom ≫ (TopCat.toSSet.obj Z).ιChainComplex τ :=
    ((reassoc_of% (TopPair.ιChainComplex_singularChainComplexπ_capChain_alexanderWhitneyDiagonal
      P K (λ_ A).inv (λ_ A).hom r q (q + r) (Nat.add_comm r q) φ σ))
      ((SSet.chainComplexMap (TopCat.toSSet.map g) A).f q)).trans
      (by simp only [SSet.ι_chainComplexMap_f]; rfl)
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [hK, whiskerLeft_comp_assoc, whiskerLeft_comp_assoc, whiskerLeft_comp_assoc,
    SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f,
    SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f_assoc, hA]
  suffices (A ◁ (λ_ (ModuleCat.of K K)).inv) ≫ (A ◁ (c ▷ ModuleCat.of K K)) ≫
        (A ◁ (λ_ (ModuleCat.of K K)).hom) ≫ (ρ_ A).hom =
      (ρ_ A).hom ≫ (λ_ A).inv ≫ (c ▷ A) ≫ (λ_ A).hom by
    simpa only [Category.assoc] using congrArg (· ≫ (TopCat.toSSet.obj Z).ιChainComplex τ) this
  let U : ModuleCat.{w} K := 𝟙_ (ModuleCat.{w} K)
  let c' : U ⟶ U := c
  change (A ◁ (λ_ U).inv) ≫ (A ◁ (c' ▷ U)) ≫ (A ◁ (λ_ U).hom) ≫ (ρ_ A).hom =
    (ρ_ A).hom ≫ (λ_ A).inv ≫ (c' ▷ A) ≫ (λ_ A).hom
  refine ModuleCat.MonoidalCategory.tensor_ext fun a (k : K) ↦ ?_
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.hom_hom_leftUnitor, ModuleCat.hom_hom_rightUnitor, LinearEquiv.coe_coe]
  let r₀ : K := c.hom 1
  change (TensorProduct.rid K A) (a ⊗ₜ[K] (TensorProduct.lid K K) (r₀ ⊗ₜ[K] k)) =
    (TensorProduct.lid K A) (r₀ ⊗ₜ[K] (TensorProduct.rid K A) (a ⊗ₜ[K] k))
  simp only [TensorProduct.lid_tmul, TensorProduct.rid_tmul, smul_eq_mul, mul_smul]

/-- **Passage from `K`-coefficients to arbitrary `K`-module coefficients `A` in `capPushforward`.**
If `Hₘ(X, B; K) = 0` for all `m < r` and `x ↦ g_*(x ⌢ u)` with coefficients `K` is bijective in
every degree `r + q`, then `x ↦ g_*(x ⌢ u)` with coefficients in **any** `K`-module `A` is bijective
in every degree `r + p`. -/
theorem bijective_capPushforward_of_forall_bijective_capPushforward (P : TopPair.{w})
    {Z : TopCat.{w}} (g : P.fst ⟶ Z) (A : ModuleCat.{w} K) (r p m : ℕ) (h : r + p = m)
    (hzero : ∀ j < r, IsZero (P.singularHomology (ModuleCat.of K K) j))
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) r)
    (hbij : ∀ (q m' : ℕ) (hq : r + q = m'),
      Function.Bijective (P.capPushforward (ModuleCat.of K K) g r q m' hq u)) :
    Function.Bijective (P.capPushforward A g r p m h u) := by
  subst h
  suffices ∀ (m' : ℕ) (hm₀ : r + p = m') (_ : m' = p + r),
      Function.Bijective (P.capPushforward A g r p m' hm₀ u) from
    this (r + p) rfl (Nat.add_comm r p)
  rintro _ hm₀ rfl
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ r u
  let e := ComplexShape.embeddingDownNatAdd r
  have hp : e.f p = p + r := ComplexShape.embeddingDownNatAdd_f r p
  let L_K := (TopCat.toSSet.obj Z).chainComplex (ModuleCat.of K K)
  let L_A := (TopCat.toSSet.obj Z).chainComplex A
  let F_A := (tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)
  have : ∀ n, Projective ((P.singularChainComplex (ModuleCat.of K K)).X n) :=
    fun n ↦ SSetPair.projective_chainComplex_X (ModuleCat.of K K) (toSSetPair.obj P) n
  have : ∀ n, Projective (L_K.X n) := inferInstance
  have hqK : QuasiIso (capExtendChainMap P g r φ) :=
    (quasiIso_capExtendChainMap_iff P g r hzero φ).2 hbij
  obtain ⟨he, hhe⟩ := (ChainComplex.quasiIso_iff_of_projective (capExtendChainMap P g r φ)).1 hqK
  have hqFA : QuasiIso (F_A.map (capExtendChainMap P g r φ)) :=
    homotopyEquivalences_le_quasiIso _ _ _
      ⟨(tensorLeft A).mapHomotopyEquiv he, show F_A.map he.hom = F_A.map _ by rw [hhe]⟩
  have hF : IsIso (homologyMap (F_A.map (capExtendChainMap P g r φ)) (p + r)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 (hqFA.1 (p + r))
  have hpairP : IsIso ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) :=
    isIso_ssetPair_chainComplexPairing (toSSetPair.obj P) A
  let pairZ : F_A.obj L_K ≅ L_A := asIso ((TopCat.toSSet.obj Z).chainComplexPairing (ρ_ A).hom)
  let rhsIso : F_A.obj (L_K.extend e) ≅ L_A.extend e :=
    tensorLeftExtendIso A L_K r ≪≫ (e.extendFunctor _).mapIso pairZ
  let φ' : ((P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K
      (𝟙_ (ModuleCat.{w} K))).cycles r := φ
  let pairCyc : (F_A.obj (P.singularChainComplex (ModuleCat.of K K))).cycles (p + r) ⟶
      (P.singularChainComplex A).cycles (p + r) :=
    cyclesMap ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) (p + r)
  let mid : (F_A.obj (P.singularChainComplex (ModuleCat.of K K))).cycles (p + r) ⟶
      L_A.homology p :=
    pairCyc ≫
      (((-1 : ℤ) ^ (r * p)) •
        (TauCeti.ChainComplex.capCycles K (P.alexanderWhitneyDiagonal (λ_ A).inv)
            ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom)
            r p (p + r) hm₀ φ' ≫
          cyclesMap (SSet.chainComplexMap (TopCat.toSSet.map g) A) p ≫
          L_A.homologyπ p))
  -- Identify the degree-`(p + r)` homology map of `F_A.map (capExtendChainMap ...)` with
  -- `(-1)^(r * p)` times `capPushforward A`.
  have hcomm_hom :
      homologyMap ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) (p + r) ≫
        (((-1 : ℤ) ^ (r * p)) • P.capPushforward A g r p (p + r) hm₀
          ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ)) =
      homologyMap (F_A.map (capExtendChainMap P g r φ)) (p + r) ≫
        homologyMap rhsIso.hom (p + r) ≫ (L_A.extendHomologyIso e hp).hom := by
    refine (cancel_epi
      ((F_A.obj (P.singularChainComplex (ModuleCat.of K K))).homologyπ (p + r))).1 ?_
    have lhs_eq :
        (F_A.obj (P.singularChainComplex (ModuleCat.of K K))).homologyπ (p + r) ≫
          (homologyMap ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) (p + r) ≫
            (((-1 : ℤ) ^ (r * p)) • P.capPushforward A g r p (p + r) hm₀
              ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ))) =
        mid := by
      have h1 : (F_A.obj (P.singularChainComplex (ModuleCat.of K K))).homologyπ (p + r) ≫
            (homologyMap ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) (p + r) ≫
              (((-1 : ℤ) ^ (r * p)) • P.capPushforward A g r p (p + r) hm₀
                ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r
                  φ))) =
          pairCyc ≫ ((P.singularChainComplex A).homologyπ (p + r) ≫
            (((-1 : ℤ) ^ (r * p)) • P.capPushforward A g r p (p + r) hm₀
              ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r
                φ))) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) (homologyπ_naturality
            ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) (p + r))).trans
            (Category.assoc _ _ _))
      refine h1.trans (congrArg (pairCyc ≫ ·) ?_)
      rw [Preadditive.comp_zsmul]
      refine congrArg (((-1 : ℤ) ^ (r * p)) • ·) ?_
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj
            A).map g)
          (TopPair.singularCap_homologyπ P K (λ_ A).inv (λ_ A).hom r p (p + r) hm₀ φ)).trans
          ((Category.assoc _ _ _).trans
            (congrArg _ (homologyπ_naturality
              (SSet.chainComplexMap (TopCat.toSSet.map g) A) p))))
    have rhs_eq :
        (F_A.obj (P.singularChainComplex (ModuleCat.of K K))).homologyπ (p + r) ≫
          (homologyMap (F_A.map (capExtendChainMap P g r φ)) (p + r) ≫
            homologyMap rhsIso.hom (p + r) ≫ (L_A.extendHomologyIso e hp).hom) =
        mid := by
      rw [homologyπ_naturality_assoc, homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom]
      have hcyc :
          pairCyc ≫
              (((-1 : ℤ) ^ (r * p)) •
                (TauCeti.ChainComplex.capCycles K (P.alexanderWhitneyDiagonal (λ_ A).inv)
                    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom)
                    r p (p + r) hm₀ φ' ≫
                  cyclesMap (SSet.chainComplexMap (TopCat.toSSet.map g) A) p)) =
            cyclesMap (F_A.map (capExtendChainMap P g r φ)) (p + r) ≫
              cyclesMap rhsIso.hom (p + r) ≫ (L_A.extendCyclesIso e hp).hom := by
        let ψ : (P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).X r ⟶ 𝟙_ (ModuleCat.{w} K) :=
          ((P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K
            (𝟙_ (ModuleCat.{w} K))).iCycles r φ'
        let ψ' : (P.singularChainComplex (ModuleCat.of K K)).X r ⟶ ModuleCat.of K K := ψ
        rw [← cancel_mono (L_A.iCycles p), Category.assoc, Preadditive.zsmul_comp,
          Preadditive.comp_zsmul, Category.assoc, cyclesMap_i,
          TauCeti.ChainComplex.capCycles_i_assoc]
        change (-1 : ℤ) ^ (r * p) • (pairCyc ≫ (P.singularChainComplex A).iCycles (p + r) ≫
            TauCeti.ChainComplex.capChain K (P.alexanderWhitneyDiagonal (λ_ A).inv)
              ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r p (p + r) hm₀ ψ' ≫
            (SSet.chainComplexMap (TopCat.toSSet.map g) A).f p) = _
        rw [reassoc_of% (show pairCyc ≫ (P.singularChainComplex A).iCycles (p + r) =
            (F_A.obj (P.singularChainComplex (ModuleCat.of K K))).iCycles (p + r) ≫
              ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom).f (p + r) from
            cyclesMap_i ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) (p + r))]
        simp only [Category.assoc]
        rw [extendCyclesIso_hom_iCycles, cyclesMap_i_assoc, cyclesMap_i_assoc]
        have hcap : (capExtendChainMap P g r φ).f (p + r) =
            (((-1 : ℤ) ^ (r * p)) •
              (TauCeti.ChainComplex.capChain K
                  (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
                  ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
                  r p (p + r) (Nat.add_comm r p) ψ' ≫
                (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)).f p)) ≫
              (L_K.extendXIso e hp).inv := by
          rw [capExtendChainMap_f P g r p (p + r) hp φ]
          dsimp only [capRestrictionChainMap, e]
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
          rfl
        have hrhs_f : rhsIso.hom.f (p + r) ≫ (L_A.extendXIso e hp).hom =
            (A ◁ (L_K.extendXIso e hp).hom) ≫
              ((TopCat.toSSet.obj Z).chainComplexPairing (ρ_ A).hom).f p := by
          let f_pair : F_A.obj L_K ⟶ L_A := (TopCat.toSSet.obj Z).chainComplexPairing (ρ_ A).hom
          have h1 : rhsIso.hom.f (p + r) =
              (tensorLeftExtendXIso A L_K r (p + r)).hom ≫ (extendMap f_pair e).f (p + r) := rfl
          rw [h1, Category.assoc, tensorLeftExtendXIso_hom_eq A L_K hp, extendMap_f f_pair e hp]
          dsimp only [F_A, e]
          simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
          rfl
        have hFcap : (F_A.map (capExtendChainMap P g r φ)).f (p + r) =
            A ◁ (capExtendChainMap P g r φ).f (p + r) := rfl
        have hinv : (A ◁ (L_K.extendXIso e hp).inv) ≫ (A ◁ (L_K.extendXIso e hp).hom) = 𝟙 _ := by
          rw [← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]
        have hzsmul {X Y : ModuleCat.{w} K} (n : ℤ) (f : X ⟶ Y) : A ◁ (n • f) = n • (A ◁ f) :=
          (tensorLeft A).map_zsmul
        rw [hrhs_f, hFcap, hcap, whiskerLeft_comp_assoc, reassoc_of% hinv,
          hzsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
        congr 2
        exact (whiskerLeft_capChain_comp_chainComplexPairing P g A r p ψ').symm
      rw [reassoc_of% hcyc.symm, Preadditive.zsmul_comp, Category.assoc]
    exact lhs_eq.trans rhs_eq.symm
  rw [← ConcreteCategory.isIso_iff_bijective, ← isIso_neg_one_pow_zsmul_iff (r * p)]
  have hrhs : IsIso (homologyMap rhsIso.hom (p + r)) := (homologyMapIso rhsIso (p + r)).isIso_hom
  have hpair_iso :
      IsIso (homologyMap ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) (p + r)) :=
    (homologyMapIso (@asIso _ _ _ _ ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) hpairP)
      (p + r)).isIso_hom
  have hrhs_all : IsIso (homologyMap (F_A.map (capExtendChainMap P g r φ)) (p + r) ≫
      homologyMap rhsIso.hom (p + r) ≫ (L_A.extendHomologyIso e hp).hom) :=
    IsIso.comp_isIso' hF (IsIso.comp_isIso' hrhs (L_A.extendHomologyIso e hp).isIso_hom)
  have hcomp_iso : IsIso (homologyMap ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) (p + r) ≫
      (((-1 : ℤ) ^ (r * p)) • P.capPushforward A g r p (p + r) hm₀
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ))) :=
    hcomm_hom.symm ▸ hrhs_all
  exact IsIso.of_isIso_comp_left
    (homologyMap ((toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) (p + r)) _

end ChainEquivalence

end TopPair

namespace TopCat

variable {K : Type w} [CommRing K] {X Y : TopCat.{w}} (π : X ⟶ Y) (Z : Set X)
  (A : ModuleCat.{w} K)

/-- The map `x ↦ π_*(x ⌢ u)` over a subset `S` of the base: `TopPair.capPushforward` of the
restriction of `u ∈ Hⁿ(X, Z; K)` to `(π⁻¹ S, π⁻¹ S ∩ Z)` along the restricted map `π⁻¹ S ⟶ S`,
from `Hₘ(π⁻¹ S, π⁻¹ S ∩ Z; A)` to `Hₚ(S; A)`. -/
def capPushforwardRestrict (S : Set Y) (n p m : ℕ) (h : n + p = m) :
    (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      ((TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).singularHomology A m ⟶
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj (of S)) :=
  (TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).capPushforward A
      (ofHom (π.hom.restrictPreimage S)) n p m h ∘ₗ
    (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) n).hom

/-- `TopCat.capPushforwardRestrict` is `TopPair.capPushforward` composed with restriction of `u` to
the pair over `S`. -/
theorem capPushforwardRestrict_def (S : Set Y) (n p m : ℕ) (h : n + p = m) :
    capPushforwardRestrict π Z A S n p m h =
      (TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).capPushforward A
          (ofHom (π.hom.restrictPreimage S)) n p m h ∘ₗ
        (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) n).hom :=
  (rfl)

/-- `TopCat.capPushforwardRestrict` at `u` is `TopPair.capPushforward` of the restriction of `u` to
the pair over `S`. -/
theorem capPushforwardRestrict_apply (S : Set Y) {n p m : ℕ} (h : n + p = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    capPushforwardRestrict π Z A S n p m h u =
      (TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).capPushforward A
        (ofHom (π.hom.restrictPreimage S)) n p m h
        (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) n u) :=
  (rfl)

/-- **Naturality of `capPushforwardRestrict` in the subset `S ⊆ T`.** -/
@[reassoc]
theorem capPushforwardRestrict_naturality {S T : Set Y} (hST : S ⊆ T) {n p m : ℕ} (h : n + p = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    capPushforwardRestrict π Z A S n p m h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
          (ofHom (ContinuousMap.inclusion hST)) =
      TopPair.singularHomologyMap (TopPair.ofInclusionMap
          (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S) Set.inter_subset_left
          (ContinuousMap.inclusion (Set.preimage_mono hST)) fun _ hx ↦ ⟨hST hx.1, hx.2⟩) A m ≫
        capPushforwardRestrict π Z A T n p m h u := by
  have hg : TopPair.Hom.fst (TopPair.ofInclusionMap
      (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S) Set.inter_subset_left
      (ContinuousMap.inclusion (Set.preimage_mono hST)) fun _ hx ↦ ⟨hST hx.1, hx.2⟩) ≫
        ofHom (π.hom.restrictPreimage T) =
      ofHom (π.hom.restrictPreimage S) ≫ ofHom (ContinuousMap.inclusion hST) :=
    TopCat.ext fun x ↦ Subtype.ext (congrArg (fun y : ↥(π ⁻¹' T) ↦ π y.1)
      (TopPair.ofInclusionMap_fst_apply _ _ x))
  rw [capPushforwardRestrict_apply, capPushforwardRestrict_apply,
    ← ofInclusionMap_inclusion_comp_restrictPreimagePairMap π Z hST,
    TopPair.singularCohomologyMap_comp_apply, TopPair.capPushforward_naturality _ _ _ _ hg]

/-- Over `Set.univ`, `capPushforwardRestrict` is bijective if and only if `capPushforward` is. -/
theorem bijective_capPushforwardRestrict_univ_iff {n p m : ℕ} (h : n + p = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (capPushforwardRestrict π Z A Set.univ n p m h u) ↔
      Function.Bijective ((TopPair.ofSubset Z).capPushforward A π n p m h u) := by
  have := isIso_restrictPreimagePairMap π Z (S := Set.univ) fun _ ↦ Set.mem_univ _
  rw [capPushforwardRestrict_apply]
  exact TopPair.bijective_capPushforward_iff_of_isIso (restrictPreimagePairMap π Z Set.univ)
    (isoOfHomeo (Homeomorph.Set.univ Y)).hom
    (TopCat.ext fun x ↦ congrArg π (restrictPreimagePairMap_fst_apply π Z Set.univ x)) h u

end TopCat
