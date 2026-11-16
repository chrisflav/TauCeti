/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import TauCeti.Algebra.Homology.HomologicalComplex.Projective.QuasiIso
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.Homotopy
import TauCeti.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.Algebra.Homology.Monoidal.Cap.Kronecker
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing

/-!
# The pullback-cap chain map and universal coefficient transfer

Let `P = (X, Y)` be a topological pair, `π : X ⟶ Z` a continuous map, and `ζ` a relative
`r`-cocycle of `P` with coefficients in the tensor unit `𝟙_ C` representing a cohomology class
`u ∈ Hʳ(X, Y; 𝟙_ C)`. For any coefficient object `A : C`, capping a relative `m`-chain of `P`
with `ζ` (with sign `(-1)^(r * (m - r))`) and pushing forward along `π` defines a chain map

`P.pullbackCapChainMap k A π ζ : C(X, Y; A) ⟶ C(Z; A).extend (+r)`

from the relative singular chain complex of `P` to the singular chain complex of `Z` shifted
upward by `r` degrees via zero extension (`ComplexShape.embeddingDownNatAdd r`).

On homology in degree `m = r + p`, this chain map induces (up to the sign `(-1)^(r * p)`) the
homology cap-and-pushforward morphism `x ↦ π_*(x ⌢ u) : Hₘ(X, Y; A) ⟶ Hₚ(Z; A)`
(`TopPair.homologyMap_pullbackCapChainMap_comp_extendHomologyIso_hom`).

With coefficients in `ModuleCat K` for a commutative ring `K` and `A = K`, applying
`Hom(-, M)` for any `K`-module `M` turns `P.pullbackCapChainMap` into the cohomology
pullback-cup map `a ↦ π^*a ⌣ u : Hᵖ(Z; M) ⟶ Hᵐ(X, Y; M)` (`TopPair.pullbackCup`), with no
sign (`TopPair.homologyMap_linearYonedaFunctor_pullbackCapChainMap`): the sign `(-1)^(r * p)`
in the chain map cancels the Koszul sign `(-1)^(p * r)` from graded commutativity of the cup
product (`TopPair.singularCup_gradedComm`).

Because singular chain complexes with projective unit coefficients are degreewise projective, this
gives a two-way transfer between cohomology and homology with arbitrary coefficients:
* If `Hʲ(X, Y; M) = 0` for `j < r` and `a ↦ π^*a ⌣ u` is bijective for every `K`-module `M`,
  then `P.pullbackCapChainMap K K π ζ` is a quasi-isomorphism
  (`TopPair.quasiIso_pullbackCapChainMap_of_bijective_pullbackCup`), using
  `ChainComplex.quasiIso_of_forall_quasiIso_linearYonedaFunctor_map`.
* Conversely, if `P.pullbackCapChainMap K K π ζ` is a quasi-isomorphism, then
  `a ↦ π^*a ⌣ u` is bijective for every `K`-module `M`
  (`TopPair.bijective_pullbackCup_of_quasiIso_pullbackCapChainMap`), and tensoring with any
  coefficient object `A` shows that `P.pullbackCapChainMap k A π ζ` is also a quasi-isomorphism
  (`TopPair.quasiIso_pullbackCapChainMap_of_quasiIso_self`), so `x ↦ π_*(x ⌢ u)` is an
  isomorphism on homology with arbitrary coefficients `A`
  (`TopPair.isIso_singularCap_comp_map_of_quasiIso_self`).

This mechanism drives the passage from finite trivializing unions to arbitrary bases and arbitrary
coefficient modules in the proof of the Thom isomorphism theorem.

## Main definitions and results

* `TopPair.pullbackCapChainMap`: the signed cap-and-pushforward chain map
  `C(X, Y; A) ⟶ C(Z; A).extend (+r)`.
* `TopPair.homologyMap_pullbackCapChainMap_comp_extendHomologyIso_hom`: on homology in degree
  `m = r + p`, it computes `(-1)^(r * p) • (x ↦ π_*(x ⌢ u))`.
* `TopPair.homologyMap_linearYonedaFunctor_pullbackCapChainMap`: on cohomology with values in `M`,
  it computes `TopPair.pullbackCup`.
* `TopPair.quasiIso_pullbackCapChainMap_of_bijective_pullbackCup`: bijectivity of `pullbackCup`
  for all `M` (with vanishing below `r`) implies `pullbackCapChainMap` is a quasi-isomorphism.
* `TopPair.bijective_pullbackCup_of_quasiIso_pullbackCapChainMap`: conversely, a quasi-isomorphism
  on chains with `K`-coefficients yields bijectivity of `pullbackCup` for all `K`-modules `M`.
* `TopPair.quasiIso_pullbackCapChainMap_of_quasiIso_self` and
  `TopPair.isIso_singularCap_comp_map_of_quasiIso_self`: a quasi-isomorphism on chains with
  `𝟙_ C`-coefficients transfers by tensoring to arbitrary coefficients `A`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

universe w v u

namespace TopPair

/-! ### The signed cap-and-pushforward chain map -/

section ChainMap

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft (𝟙_ C))]
  (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C]

/-- The degree-`m` component of `TopPair.pullbackCapChainMap`: for `r ≤ m`, cap with `ζ` with
sign `(-1)^(r * (m - r))`, push forward along `π`, and enter the shifted complex; for `m < r`,
zero. -/
private def pullbackCapChainMapF (P : TopPair.{w}) {Z : TopCat.{w}} (A : C) (π : P.fst ⟶ Z)
    {r : ℕ} (ζ : (P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).cycles r) (m : ℕ) :
    (P.singularChainComplex A).X m ⟶
      (((TopCat.toSSet.obj Z).chainComplex A).extend (ComplexShape.embeddingDownNatAdd r)).X m :=
  if hm : r ≤ m then
    ((-1 : ℤ) ^ (r * (m - r))) •
      (TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal (λ_ A).inv)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r (m - r) m (by omega)
          ((P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).iCycles r ζ) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map π) A).f (m - r) ≫
        (((TopCat.toSSet.obj Z).chainComplex A).extendXIso (ComplexShape.embeddingDownNatAdd r)
          (show (ComplexShape.embeddingDownNatAdd r).f (m - r) = m by
            simp only [ComplexShape.embeddingDownNatAdd_f]; omega)).inv)
  else
    0

/-- **The pullback-cap chain map** `C(X, Y; A) ⟶ C(Z; A).extend (+r)`: for a topological pair
`P = (X, Y)`, a continuous map `π : X ⟶ Z`, and a relative `r`-cocycle `ζ` of `P`, capping with
`ζ` with sign `(-1)^(r * (m - r))` and pushing forward along `π` defines a chain map into the
singular chain complex of `Z` shifted upward by `r` degrees. -/
def pullbackCapChainMap (P : TopPair.{w}) {Z : TopCat.{w}} (A : C) (π : P.fst ⟶ Z)
    {r : ℕ} (ζ : (P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).cycles r) :
    P.singularChainComplex A ⟶
      ((TopCat.toSSet.obj Z).chainComplex A).extend (ComplexShape.embeddingDownNatAdd r) where
  f := pullbackCapChainMapF k P A π ζ
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    by_cases hj : r ≤ j
    · obtain rfl : i = j + 1 := hij'.symm
      have hi : r ≤ j + 1 := by omega
      have hq : j + 1 - r = j - r + 1 := by omega
      obtain ⟨φ, hφ⟩ : ∃ φ : (P.singularChainComplex (𝟙_ C)).X r ⟶ 𝟙_ C,
          φ = (P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).iCycles r ζ := ⟨_, rfl⟩
      simp only [pullbackCapChainMapF, hi, hj, ↓reduceDIte, Preadditive.zsmul_comp,
        Preadditive.comp_zsmul]
      rw [← hφ]
      have hdZ := ((TopCat.toSSet.obj Z).chainComplex A).extend_d_eq
        (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f (j + 1 - r) = j + 1 by
          simp only [ComplexShape.embeddingDownNatAdd_f]; omega)
        (show (ComplexShape.embeddingDownNatAdd r).f (j - r) = j by
          simp only [ComplexShape.embeddingDownNatAdd_f]; omega)
      rw [Category.assoc, Category.assoc, hdZ, Iso.inv_hom_id_assoc]
      have hπ : (SSet.chainComplexMap (TopCat.toSSet.map π) A).f (j + 1 - r) ≫
            ((TopCat.toSSet.obj Z).chainComplex A).d (j + 1 - r) (j - r) =
          ((TopCat.toSSet.obj P.fst).chainComplex A).d (j + 1 - r) (j - r) ≫
            (SSet.chainComplexMap (TopCat.toSSet.map π) A).f (j - r) :=
        (SSet.chainComplexMap (TopCat.toSSet.map π) A).comm (j + 1 - r) (j - r)
      rw [reassoc_of% hπ]
      have hcap : TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal (λ_ A).inv)
            ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r (j + 1 - r) (j + 1)
            (by omega) φ ≫
            ((TopCat.toSSet.obj P.fst).chainComplex A).d (j + 1 - r) (j - r) =
          ((-1 : ℤ) ^ r) • ((P.singularChainComplex A).d (j + 1) j ≫
            TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal (λ_ A).inv)
              ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r (j - r) j (by omega)
              φ) := by
        have hstep : ∀ {q' : ℕ} (hq' : q' = j - r + 1),
            TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal (λ_ A).inv)
              ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r q' (j + 1)
              (by omega) φ ≫
              ((TopCat.toSSet.obj P.fst).chainComplex A).d q' (j - r) =
            ((-1 : ℤ) ^ r) • ((P.singularChainComplex A).d (j + 1) j ≫
              TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal (λ_ A).inv)
                ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r (j - r) j (by omega)
                φ) := by
          rintro _ rfl
          rw [hφ]
          exact TauCeti.ChainComplex.capChain_comp_d_of_cycles
            (P.alexanderWhitneyDiagonal (λ_ A).inv)
            ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r (j - r) j (by omega) ζ
        exact hstep hq
      rw [reassoc_of% hcap, Preadditive.zsmul_comp, smul_smul, Category.assoc]
      have hsign :
          (-1 : ℤ) ^ (r * (j + 1 - r)) * (-1 : ℤ) ^ r = (-1 : ℤ) ^ (r * (j - r)) := by
        rw [hq, ← pow_add, mul_add, mul_one, add_assoc, pow_add, ← two_mul, pow_mul]
        norm_num
      rw [hsign]
    · exact (((TopCat.toSSet.obj Z).chainComplex A).isZero_extend_X
        (ComplexShape.embeddingDownNatAdd r) j fun _ hm ↦ by
          simp only [ComplexShape.embeddingDownNatAdd_f] at hm; omega).eq_of_tgt _ _

/-- In degree `m = r + p`, composing `pullbackCapChainMap` with `extendXIso.hom` recovers the
signed cap-and-pushforward map on chains. -/
@[reassoc]
lemma pullbackCapChainMap_f_comp_extendXIso_hom (P : TopPair.{w}) {Z : TopCat.{w}} (A : C)
    (π : P.fst ⟶ Z) {r p m : ℕ} (h : r + p = m)
    (ζ : (P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).cycles r) :
    (P.pullbackCapChainMap k A π ζ).f m ≫
        (((TopCat.toSSet.obj Z).chainComplex A).extendXIso (ComplexShape.embeddingDownNatAdd r)
          (show (ComplexShape.embeddingDownNatAdd r).f p = m by
            simp only [ComplexShape.embeddingDownNatAdd_f]; omega)).hom =
      ((-1 : ℤ) ^ (r * p)) •
        (TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal (λ_ A).inv)
            ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r p m h
            ((P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).iCycles r ζ) ≫
          (SSet.chainComplexMap (TopCat.toSSet.map π) A).f p) := by
  have hm : r ≤ m := by omega
  obtain rfl : p = m - r := by omega
  change pullbackCapChainMapF k P A π ζ m ≫ _ = _
  simp only [pullbackCapChainMapF, hm, ↓reduceDIte, Preadditive.zsmul_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- **Action of `pullbackCapChainMap` on homology**: in degree `m = r + p`, composing
`homologyMap (P.pullbackCapChainMap k A π ζ) m` with `extendHomologyIso.hom` gives `(-1)^(r * p)`
times the relative cap product with `[ζ]` followed by pushforward along `π`. -/
lemma homologyMap_pullbackCapChainMap_comp_extendHomologyIso_hom (P : TopPair.{w})
    {Z : TopCat.{w}} (A : C) (π : P.fst ⟶ Z) {r p m : ℕ} (h : r + p = m)
    (ζ : (P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).cycles r) :
    HomologicalComplex.homologyMap (P.pullbackCapChainMap k A π ζ) m ≫
        (((TopCat.toSSet.obj Z).chainComplex A).extendHomologyIso
          (ComplexShape.embeddingDownNatAdd r)
          (show (ComplexShape.embeddingDownNatAdd r).f p = m by
            simp only [ComplexShape.embeddingDownNatAdd_f]; omega)).hom =
      ((-1 : ℤ) ^ (r * p)) •
        (P.singularCap k (λ_ A).inv (λ_ A).hom r p m h
            ((P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).homologyπ r ζ) ≫
          ((AlgebraicTopology.singularHomologyFunctor C p).obj A).map π) := by
  rw [TauCeti.singularHomologyFunctor_obj_map]
  let c : (P.singularChainComplex A).homology m ⟶
      ((TopCat.toSSet.obj P.fst).chainComplex A).homology p :=
    P.singularCap k (λ_ A).inv (λ_ A).hom r p m h
      ((P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).homologyπ r ζ)
  let πH : ((TopCat.toSSet.obj P.fst).chainComplex A).homology p ⟶
      ((TopCat.toSSet.obj Z).chainComplex A).homology p :=
    SSet.homologyMap (TopCat.toSSet.map π) A p
  have hcap : (P.singularChainComplex A).homologyπ m ≫ c =
      TauCeti.ChainComplex.capCycles k (P.alexanderWhitneyDiagonal (λ_ A).inv)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r p m h ζ ≫
        ((TopCat.toSSet.obj P.fst).chainComplex A).homologyπ p :=
    TopPair.singularCap_homologyπ _ _ _ _ _ _ _ _ _
  change HomologicalComplex.homologyMap (P.pullbackCapChainMap k A π ζ) m ≫ _ =
    ((-1 : ℤ) ^ (r * p)) • (c ≫ πH)
  apply (cancel_epi ((P.singularChainComplex A).homologyπ m)).1
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom, Preadditive.comp_zsmul,
    ← Category.assoc ((P.singularChainComplex A).homologyπ m), hcap, Category.assoc]
  have hπ : ((TopCat.toSSet.obj P.fst).chainComplex A).homologyπ p ≫ πH =
      HomologicalComplex.cyclesMap (SSet.chainComplexMap (TopCat.toSSet.map π) A) p ≫
        ((TopCat.toSSet.obj Z).chainComplex A).homologyπ p :=
    HomologicalComplex.homologyπ_naturality _ p
  rw [hπ, ← Category.assoc (TauCeti.ChainComplex.capCycles _ _ _ _ _ _ _ _),
    ← Preadditive.zsmul_comp, ← Category.assoc (HomologicalComplex.cyclesMap _ _)]
  refine congrArg (· ≫ ((TopCat.toSSet.obj Z).chainComplex A).homologyπ p) ?_
  rw [← cancel_mono (((TopCat.toSSet.obj Z).chainComplex A).iCycles p)]
  simp only [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
    HomologicalComplex.cyclesMap_i_assoc, HomologicalComplex.cyclesMap_i,
    Preadditive.zsmul_comp, TauCeti.ChainComplex.capCycles_i_assoc,
    pullbackCapChainMap_f_comp_extendXIso_hom k P A π h ζ, Preadditive.comp_zsmul]

/-- In shifted degree `m = r + p`, `homologyMap (P.pullbackCapChainMap k A π ζ) m` is an
isomorphism iff the cap-and-pushforward map `x ↦ π_*(x ⌢ [ζ])` is an isomorphism. -/
lemma isIso_homologyMap_pullbackCapChainMap_iff (P : TopPair.{w}) {Z : TopCat.{w}} (A : C)
    (π : P.fst ⟶ Z) {r p m : ℕ} (h : r + p = m)
    (ζ : (P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).cycles r) :
    IsIso (HomologicalComplex.homologyMap (P.pullbackCapChainMap k A π ζ) m) ↔
      IsIso (P.singularCap k (λ_ A).inv (λ_ A).hom r p m h
          ((P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).homologyπ r ζ) ≫
        ((AlgebraicTopology.singularHomologyFunctor C p).obj A).map π) := by
  let e := ((TopCat.toSSet.obj Z).chainComplex A).extendHomologyIso
    (ComplexShape.embeddingDownNatAdd r)
    (show (ComplexShape.embeddingDownNatAdd r).f p = m by
      simp only [ComplexShape.embeddingDownNatAdd_f]; omega)
  let g : (P.singularChainComplex A).homology m ⟶
      ((TopCat.toSSet.obj Z).chainComplex A).homology p :=
    P.singularCap k (λ_ A).inv (λ_ A).hom r p m h
        ((P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).homologyπ r ζ) ≫
      ((AlgebraicTopology.singularHomologyFunctor C p).obj A).map π
  have hcomm : HomologicalComplex.homologyMap (P.pullbackCapChainMap k A π ζ) m ≫ e.hom =
      ((-1 : ℤ) ^ (r * p)) • g :=
    homologyMap_pullbackCapChainMap_comp_extendHomologyIso_hom k P A π h ζ
  have hsign : IsIso (((-1 : ℤ) ^ (r * p)) • g) ↔ IsIso g := by
    constructor
    · intro hg
      refine ⟨⟨((-1 : ℤ) ^ (r * p)) • inv (((-1 : ℤ) ^ (r * p)) • g), ?_, ?_⟩⟩
      · rw [Preadditive.comp_zsmul, ← Preadditive.zsmul_comp, IsIso.hom_inv_id]
      · rw [Preadditive.zsmul_comp, ← Preadditive.comp_zsmul, IsIso.inv_hom_id]
    · intro hg
      refine ⟨⟨((-1 : ℤ) ^ (r * p)) • inv g, ?_, ?_⟩⟩
      · rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← mul_pow,
          IsIso.hom_inv_id]
        simp
      · rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← mul_pow,
          IsIso.inv_hom_id]
        simp
  change IsIso _ ↔ IsIso g
  rw [← hsign, ← hcomm]
  constructor
  · intro (_ : IsIso (HomologicalComplex.homologyMap (P.pullbackCapChainMap k A π ζ) m))
    refine ⟨⟨e.inv ≫ inv (HomologicalComplex.homologyMap (P.pullbackCapChainMap k A π ζ) m),
      by simp, by simp⟩⟩
  · intro (_ :
        IsIso (HomologicalComplex.homologyMap (P.pullbackCapChainMap k A π ζ) m ≫ e.hom))
    refine ⟨⟨e.hom ≫
        inv (HomologicalComplex.homologyMap (P.pullbackCapChainMap k A π ζ) m ≫ e.hom),
        ?_, ?_⟩⟩
    · rw [← Category.assoc, IsIso.hom_inv_id]
    · rw [← cancel_mono e.hom, Category.assoc, Category.assoc,
        IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- Below degree `r`, `homologyMap (P.pullbackCapChainMap k A π ζ) m` is an isomorphism whenever
`Hₘ(X, Y; A)` vanishes. -/
lemma isIso_homologyMap_pullbackCapChainMap_lt (P : TopPair.{w}) {Z : TopCat.{w}} (A : C)
    (π : P.fst ⟶ Z) {r m : ℕ} (hm : m < r)
    (ζ : (P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).cycles r)
    (hP : IsZero (P.singularHomology A m)) :
    IsIso (HomologicalComplex.homologyMap (P.pullbackCapChainMap k A π ζ) m) := by
  have hZ : IsZero ((((TopCat.toSSet.obj Z).chainComplex A).extend
      (ComplexShape.embeddingDownNatAdd r)).homology m) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _
      (((TopCat.toSSet.obj Z).chainComplex A).isZero_extend_X
        (ComplexShape.embeddingDownNatAdd r) m fun _ hi ↦ by
          simp only [ComplexShape.embeddingDownNatAdd_f] at hi; omega)
  refine ⟨⟨0, hP.eq_of_src _ _, hZ.eq_of_src _ _⟩⟩

end ChainMap

/-! ### Coefficient transfer via tensoring -/

section TensorTransfer

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]

/-- An invertible coefficient pairing induces an isomorphism on relative simplicial chains. -/
private lemma isIso_ssetPair_chainComplexPairing {M S N : C}
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]
    (P : SSetPair.{w}) (μ : M ⊗ S ⟶ N) [IsIso μ] :
    IsIso (P.chainComplexPairing μ) := by
  have : ∀ n, IsIso ((P.chainComplexPairing μ).f n) := fun n ↦ by
    have hnat := congrArg (fun φ ↦ φ.f n) (SSet.chainComplexPairing_naturality P.hom μ)
    dsimp at hnat
    have hzero : (SSet.chainComplexMap P.hom N).f n ≫
          inv ((P.right.chainComplexPairing μ).f n) ≫ (M ◁ (P.chainComplexπ S).f n) = 0 := by
      have hcomm : (SSet.chainComplexMap P.hom N).f n ≫
            inv ((P.right.chainComplexPairing μ).f n) =
          inv ((P.left.chainComplexPairing μ).f n) ≫
            (M ◁ (SSet.chainComplexMap P.hom S).f n) := by
        rw [IsIso.comp_inv_eq, Category.assoc, hnat, IsIso.inv_hom_id_assoc]
      rw [reassoc_of% hcomm, ← MonoidalCategory.whiskerLeft_comp,
        SSetPair.chainComplex_condition_f, MonoidalPreadditive.whiskerLeft_zero, comp_zero]
    let g := CokernelCofork.IsColimit.desc'
      (SSetPair.chainComplexXSplitting N P n).gIsCokernel
      (inv ((P.right.chainComplexPairing μ).f n) ≫ (M ◁ (P.chainComplexπ S).f n)) hzero
    have hg : (P.chainComplexπ N).f n ≫ g.1 =
        inv ((P.right.chainComplexPairing μ).f n) ≫ (M ◁ (P.chainComplexπ S).f n) := g.2
    refine ⟨⟨g.1, ?_, ?_⟩⟩
    · apply (cancel_epi (M ◁ (P.chainComplexπ S).f n)).1
      dsimp only [Functor.mapHomologicalComplex_obj_X, curriedTensor_obj_obj]
      rw [Category.comp_id, SSetPair.whiskerLeft_chainComplexπ_f_chainComplexPairing_f_assoc, hg,
        IsIso.hom_inv_id_assoc]
    · apply (cancel_epi ((P.chainComplexπ N).f n)).1
      rw [Category.comp_id, reassoc_of% hg,
        SSetPair.whiskerLeft_chainComplexπ_f_chainComplexPairing_f, IsIso.inv_hom_id_assoc]
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The degree-`m` isomorphism `A ⊗ (C(Z; 𝟙_ C).extend (+r))_m ≅ (C(Z; A).extend (+r))_m`. -/
private def tensorLeftExtendPairingIsoX (Z : TopCat.{w}) (A : C)
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft A)] (r m : ℕ) :
    (((tensorLeft A).mapHomologicalComplex _).obj
        (((TopCat.toSSet.obj Z).chainComplex (𝟙_ C)).extend
          (ComplexShape.embeddingDownNatAdd r))).X m ≅
      (((TopCat.toSSet.obj Z).chainComplex A).extend (ComplexShape.embeddingDownNatAdd r)).X m := by
  by_cases hm : r ≤ m
  · let eK := ((TopCat.toSSet.obj Z).chainComplex (𝟙_ C)).extendXIso
      (ComplexShape.embeddingDownNatAdd r) (i := m - r) (i' := m)
      (by simp only [ComplexShape.embeddingDownNatAdd_f]; omega)
    let eA := ((TopCat.toSSet.obj Z).chainComplex A).extendXIso
      (ComplexShape.embeddingDownNatAdd r) (i := m - r) (i' := m)
      (by simp only [ComplexShape.embeddingDownNatAdd_f]; omega)
    exact (tensorLeft A).mapIso eK ≪≫
      asIso (((TopCat.toSSet.obj Z).chainComplexPairing (ρ_ A).hom).f (m - r)) ≪≫ eA.symm
  · have hK : IsZero ((((TopCat.toSSet.obj Z).chainComplex (𝟙_ C)).extend
        (ComplexShape.embeddingDownNatAdd r)).X m) :=
      ((TopCat.toSSet.obj Z).chainComplex (𝟙_ C)).isZero_extend_X
        (ComplexShape.embeddingDownNatAdd r) m fun _ hi ↦ by
          simp only [ComplexShape.embeddingDownNatAdd_f] at hi; omega
    have hA : IsZero ((((TopCat.toSSet.obj Z).chainComplex A).extend
        (ComplexShape.embeddingDownNatAdd r)).X m) :=
      ((TopCat.toSSet.obj Z).chainComplex A).isZero_extend_X
        (ComplexShape.embeddingDownNatAdd r) m fun _ hi ↦ by
          simp only [ComplexShape.embeddingDownNatAdd_f] at hi; omega
    exact (Functor.map_isZero (tensorLeft A) hK).iso hA

/-- The isomorphism `A ⊗ (C(Z; 𝟙_ C).extend (+r)) ≅ C(Z; A).extend (+r)` induced by the right
unitor `A ⊗ 𝟙_ C ≅ A`. -/
private def tensorLeftExtendPairingIso (Z : TopCat.{w}) (A : C)
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft A)] (r : ℕ) :
    ((tensorLeft A).mapHomologicalComplex _).obj
        (((TopCat.toSSet.obj Z).chainComplex (𝟙_ C)).extend
          (ComplexShape.embeddingDownNatAdd r)) ≅
      ((TopCat.toSSet.obj Z).chainComplex A).extend (ComplexShape.embeddingDownNatAdd r) :=
  HomologicalComplex.Hom.isoOfComponents (tensorLeftExtendPairingIsoX Z A r) fun i j hij ↦ by
    have hij' : j + 1 = i := hij
    by_cases hj : r ≤ j
    · have hi : r ≤ i := by omega
      have hdK := ((TopCat.toSSet.obj Z).chainComplex (𝟙_ C)).extend_d_eq
        (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f (i - r) = i by
          simp only [ComplexShape.embeddingDownNatAdd_f]; omega)
        (show (ComplexShape.embeddingDownNatAdd r).f (j - r) = j by
          simp only [ComplexShape.embeddingDownNatAdd_f]; omega)
      have hdA := ((TopCat.toSSet.obj Z).chainComplex A).extend_d_eq
        (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f (i - r) = i by
          simp only [ComplexShape.embeddingDownNatAdd_f]; omega)
        (show (ComplexShape.embeddingDownNatAdd r).f (j - r) = j by
          simp only [ComplexShape.embeddingDownNatAdd_f]; omega)
      have hpair := ((TopCat.toSSet.obj Z).chainComplexPairing (ρ_ A).hom).comm (i - r) (j - r)
      have hcancel : (A ◁ (((TopCat.toSSet.obj Z).chainComplex (𝟙_ C)).extendXIso
            (ComplexShape.embeddingDownNatAdd r)
            (show (ComplexShape.embeddingDownNatAdd r).f (j - r) = j by
              simp only [ComplexShape.embeddingDownNatAdd_f]; omega)).inv) ≫
          (A ◁ (((TopCat.toSSet.obj Z).chainComplex (𝟙_ C)).extendXIso
            (ComplexShape.embeddingDownNatAdd r)
            (show (ComplexShape.embeddingDownNatAdd r).f (j - r) = j by
              simp only [ComplexShape.embeddingDownNatAdd_f]; omega)).hom) = 𝟙 _ := by
        rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id]
      dsimp at hpair ⊢
      simp only [tensorLeftExtendPairingIsoX, hi, hj, ↓reduceDIte, Iso.trans_hom,
        Functor.mapIso_hom, curriedTensor_obj_map, asIso_hom, Iso.symm_hom, Category.assoc]
      rw [hdK, hdA, Iso.inv_hom_id_assoc]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [reassoc_of% hcancel, reassoc_of% hpair]
    · exact (((TopCat.toSSet.obj Z).chainComplex A).isZero_extend_X
        (ComplexShape.embeddingDownNatAdd r) j fun _ hm ↦ by
          simp only [ComplexShape.embeddingDownNatAdd_f] at hm; omega).eq_of_tgt _ _

private lemma tensorLeftExtendPairingIso_hom_f_comp_extendXIso_hom (Z : TopCat.{w}) (A : C)
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft A)] {r p m : ℕ}
    (h : r + p = m) :
    (tensorLeftExtendPairingIso Z A r).hom.f m ≫
        (((TopCat.toSSet.obj Z).chainComplex A).extendXIso (ComplexShape.embeddingDownNatAdd r)
          (show (ComplexShape.embeddingDownNatAdd r).f p = m by
            simp only [ComplexShape.embeddingDownNatAdd_f]; omega)).hom =
      (A ◁ (((TopCat.toSSet.obj Z).chainComplex (𝟙_ C)).extendXIso
          (ComplexShape.embeddingDownNatAdd r)
          (show (ComplexShape.embeddingDownNatAdd r).f p = m by
            simp only [ComplexShape.embeddingDownNatAdd_f]; omega)).hom) ≫
        ((TopCat.toSSet.obj Z).chainComplexPairing (ρ_ A).hom).f p := by
  have hm : r ≤ m := by omega
  obtain rfl : p = m - r := by omega
  change (tensorLeftExtendPairingIsoX Z A r m).hom ≫ _ = _
  simp only [tensorLeftExtendPairingIsoX, hm, ↓reduceDIte, Iso.trans_hom, Functor.mapIso_hom,
    curriedTensor_obj_map, asIso_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

variable [BraidedCategory C]

omit [Abelian C] [HasCoproducts.{w} C] [MonoidalPreadditive C] in
/-- In a braided monoidal category, an endomorphism `c : 𝟙_ C ⟶ 𝟙_ C` acts the same on the
right and on the left of any object `A`. -/
private lemma whiskerLeft_comp_rightUnitor_hom (A : C) (c : 𝟙_ C ⟶ 𝟙_ C) :
    (A ◁ c) ≫ (ρ_ A).hom = (ρ_ A).hom ≫ (λ_ A).inv ≫ (c ▷ A) ≫ (λ_ A).hom := by
  calc (A ◁ c) ≫ (ρ_ A).hom
      = (A ◁ c) ≫ (β_ A (𝟙_ C)).hom ≫ (λ_ A).hom := by rw [braiding_leftUnitor]
    _ = (β_ A (𝟙_ C)).hom ≫ (c ▷ A) ≫ (λ_ A).hom := by
          rw [BraidedCategory.braiding_naturality_right_assoc]
    _ = (ρ_ A).hom ≫ (λ_ A).inv ≫ (c ▷ A) ≫ (λ_ A).hom := by
          rw [← braiding_leftUnitor, Category.assoc, Iso.hom_inv_id_assoc]

variable [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft (𝟙_ C))]
  (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C]

/-- Tensoring `P.pullbackCapChainMap k (𝟙_ C) π ζ` on the left with `A` is isomorphic to
`P.pullbackCapChainMap k A π ζ` via the right-unitor pairings on relative and absolute chains. -/
private lemma tensorLeft_pullbackCapChainMap_comm (P : TopPair.{w}) {Z : TopCat.{w}} (A : C)
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft A)]
    (π : P.fst ⟶ Z) {r : ℕ} (ζ : (P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).cycles r) :
    ((tensorLeft A).mapHomologicalComplex _).map (P.pullbackCapChainMap k (𝟙_ C) π ζ) ≫
        (tensorLeftExtendPairingIso Z A r).hom =
      (TopPair.toSSetPair.obj P).chainComplexPairing (ρ_ A).hom ≫
        P.pullbackCapChainMap k A π ζ := by
  ext m : 1
  by_cases hm : r ≤ m
  · let p := m - r
    have h : r + p = m := by omega
    obtain ⟨φ, hφ⟩ : ∃ φ : (P.singularChainComplex (𝟙_ C)).X r ⟶ 𝟙_ C,
        φ = (P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).iCycles r ζ := ⟨_, rfl⟩
    rw [← cancel_mono ((((TopCat.toSSet.obj Z).chainComplex A).extendXIso
      (ComplexShape.embeddingDownNatAdd r)
      (show (ComplexShape.embeddingDownNatAdd r).f p = m by
        simp only [ComplexShape.embeddingDownNatAdd_f]; omega)).hom)]
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      curriedTensor_obj_map, Category.assoc]
    rw [tensorLeftExtendPairingIso_hom_f_comp_extendXIso_hom Z A h,
      pullbackCapChainMap_f_comp_extendXIso_hom k P A π h ζ,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      pullbackCapChainMap_f_comp_extendXIso_hom k P (𝟙_ C) π h ζ]
    rw [← hφ]
    have hzsmul : ∀ {X Y : C} (n : ℤ) (f : X ⟶ Y), A ◁ (n • f) = n • (A ◁ f) :=
      fun n f ↦ (tensorLeft A).map_zsmul (f := f) (r := n)
    rw [hzsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    congr 1
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    have hnat := congrArg (fun ψ ↦ ψ.f p)
      (SSet.chainComplexPairing_naturality (TopCat.toSSet.map π) (ρ_ A).hom)
    dsimp at hnat
    rw [hnat, ← Category.assoc, ← Category.assoc]
    congr 1
    -- Both sides map `A ⊗ Cₘ(X, Y; 𝟙_ C) ⟶ Cₚ(X; A)`; check on singular `m`-simplices.
    let πP : ((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ C)).X m ⟶
        (P.singularChainComplex (𝟙_ C)).X m :=
      (P.singularChainComplexπ (𝟙_ C)).f m
    have hπPEpi : Epi (A ◁ πP) :=
      inferInstanceAs (Epi (A ◁ (P.singularChainComplexπ (𝟙_ C)).f m))
    apply (cancel_epi (A ◁ πP)).1
    let j : ((TopCat.toSSet.obj P.fst).chainComplex (A ⊗ 𝟙_ C)).X m ⟶
        A ⊗ ((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ C)).X m :=
      ((SSet.chainComplexFunctorObjCompMapIso (tensorLeft A) (𝟙_ C)).inv.app
        (TopCat.toSSet.obj P.fst)).f m
    have hjEpi : Epi j := inferInstanceAs (Epi (((SSet.chainComplexFunctorObjCompMapIso
      (tensorLeft A) (𝟙_ C)).inv.app (TopCat.toSSet.obj P.fst)).f m))
    apply (cancel_epi j).1
    ext σ
    have hι : (TopCat.toSSet.obj P.fst).ιChainComplex σ ≫ j =
        A ◁ (TopCat.toSSet.obj P.fst).ιChainComplex σ :=
      SSet.ιChainComplex_chainComplexFunctorObjCompMapIso_inv_app_f _ (tensorLeft A) (𝟙_ C) σ
    rw [reassoc_of% hι, reassoc_of% hι, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
    let c : 𝟙_ C ⟶ 𝟙_ C :=
      (TopCat.toSSet.obj P.fst).ιChainComplex
          ((TopCat.toSSet.obj P.fst).map (SimplexCategory.subinterval 0 r (by omega)).op σ) ≫
        (P.singularChainComplexπ (𝟙_ C)).f r ≫ φ
    let σr := (TopCat.toSSet.obj P.fst).map (SimplexCategory.subinterval r p (by omega)).op σ
    have hL : (A ◁ ((TopCat.toSSet.obj P.fst).ιChainComplex σ ≫ πP ≫
            TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal (λ_ (𝟙_ C)).inv)
              ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (𝟙_ C)).hom) r p m h φ)) ≫
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (ρ_ A).hom).f p =
        (A ◁ ((λ_ (𝟙_ C)).inv ≫ (c ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom ≫
            (TopCat.toSSet.obj P.fst).ιChainComplex σr)) ≫
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (ρ_ A).hom).f p :=
      congrArg
        (fun f ↦ (A ◁ f) ≫ ((TopCat.toSSet.obj P.fst).chainComplexPairing (ρ_ A).hom).f p)
        (TopPair.ιChainComplex_singularChainComplexπ_capChain_alexanderWhitneyDiagonal P k
          (λ_ (𝟙_ C)).inv (λ_ (𝟙_ C)).hom r p m h φ σ)
    let πPA : ((TopCat.toSSet.obj P.fst).chainComplex A).X m ⟶ (P.singularChainComplex A).X m :=
      (P.singularChainComplexπ A).f m
    have hpairP : (A ◁ πP) ≫
          ((TopPair.toSSetPair.obj P).chainComplexPairing (ρ_ A).hom).f m =
        ((TopCat.toSSet.obj P.fst).chainComplexPairing (ρ_ A).hom).f m ≫ πPA :=
      SSetPair.whiskerLeft_chainComplexπ_f_chainComplexPairing_f (TopPair.toSSetPair.obj P)
        (ρ_ A).hom m
    have hR : (A ◁ (TopCat.toSSet.obj P.fst).ιChainComplex σ) ≫
          (A ◁ πP) ≫
          ((TopPair.toSSetPair.obj P).chainComplexPairing (ρ_ A).hom).f m ≫
          TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal (λ_ A).inv)
            ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r p m h φ =
        (ρ_ A).hom ≫ (λ_ A).inv ≫ (c ▷ A) ≫ (λ_ A).hom ≫
          (TopCat.toSSet.obj P.fst).ιChainComplex σr := by
      rw [reassoc_of% hpairP, SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f_assoc]
      exact congrArg ((ρ_ A).hom ≫ ·)
        (TopPair.ιChainComplex_singularChainComplexπ_capChain_alexanderWhitneyDiagonal P k
          (λ_ A).inv (λ_ A).hom r p m h φ σ)
    refine hL.trans (Eq.trans ?_ hR.symm)
    have hc : (λ_ (𝟙_ C)).inv ≫ (c ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom = c := by
      rw [MonoidalCategory.unitors_inv_equal, MonoidalCategory.unitors_equal,
        MonoidalCategory.rightUnitor_naturality, Iso.inv_hom_id_assoc]
    rw [reassoc_of% hc, MonoidalCategory.whiskerLeft_comp_assoc,
      SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f, ← Category.assoc,
      whiskerLeft_comp_rightUnitor_hom A c, Category.assoc, Category.assoc, Category.assoc]
  · exact (((TopCat.toSSet.obj Z).chainComplex A).isZero_extend_X
      (ComplexShape.embeddingDownNatAdd r) m fun _ hi ↦ by
        simp only [ComplexShape.embeddingDownNatAdd_f] at hi; omega).eq_of_tgt _ _

/-- **Universal coefficient transfer for `pullbackCapChainMap`**: if `P.pullbackCapChainMap` with
tensor-unit coefficients is a quasi-isomorphism (with `𝟙_ C` projective), then
`P.pullbackCapChainMap` is a quasi-isomorphism for every coefficient object `A` whose left tensor
preserves `w`-small coproducts. -/
theorem quasiIso_pullbackCapChainMap_of_quasiIso_self (P : TopPair.{w}) {Z : TopCat.{w}} (A : C)
    [Projective (𝟙_ C)]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft A)]
    (π : P.fst ⟶ Z) {r : ℕ} (ζ : (P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).cycles r)
    [QuasiIso (P.pullbackCapChainMap k (𝟙_ C) π ζ)] :
    QuasiIso (P.pullbackCapChainMap k A π ζ) := by
  have hhe : homotopyEquivalences _ _ (P.pullbackCapChainMap k (𝟙_ C) π ζ) :=
    (ChainComplex.quasiIso_iff_of_projective _).1 ‹_›
  have hheA : homotopyEquivalences _ _
      (((tensorLeft A).mapHomologicalComplex _).map (P.pullbackCapChainMap k (𝟙_ C) π ζ)) :=
    Functor.homotopyEquivalences_mapHomologicalComplex_map (tensorLeft A) _ hhe
  have : QuasiIso
      (((tensorLeft A).mapHomologicalComplex _).map (P.pullbackCapChainMap k (𝟙_ C) π ζ)) :=
    homotopyEquivalences_le_quasiIso _ _ _ hheA
  have : IsIso ((TopPair.toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) :=
    isIso_ssetPair_chainComplexPairing (TopPair.toSSetPair.obj P) (ρ_ A).hom
  have heq : P.pullbackCapChainMap k A π ζ =
      inv ((TopPair.toSSetPair.obj P).chainComplexPairing (ρ_ A).hom) ≫
        ((tensorLeft A).mapHomologicalComplex _).map (P.pullbackCapChainMap k (𝟙_ C) π ζ) ≫
        (tensorLeftExtendPairingIso Z A r).hom := by
    rw [tensorLeft_pullbackCapChainMap_comm k P A π ζ, IsIso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

/-- **Homology isomorphism for arbitrary coefficients**: under the hypotheses of
`quasiIso_pullbackCapChainMap_of_quasiIso_self`, the cap-and-pushforward map
`x ↦ π_*(x ⌢ [ζ]) : Hₘ(X, Y; A) ⟶ Hₚ(Z; A)` is an isomorphism for every `A`, `r + p = m`. -/
theorem isIso_singularCap_comp_map_of_quasiIso_self (P : TopPair.{w}) {Z : TopCat.{w}} (A : C)
    [Projective (𝟙_ C)]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft A)]
    (π : P.fst ⟶ Z) {r p m : ℕ} (h : r + p = m)
    (ζ : (P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).cycles r)
    [QuasiIso (P.pullbackCapChainMap k (𝟙_ C) π ζ)] :
    IsIso (P.singularCap k (λ_ A).inv (λ_ A).hom r p m h
        ((P.singularCochainComplex (𝟙_ C) k (𝟙_ C)).homologyπ r ζ) ≫
      ((AlgebraicTopology.singularHomologyFunctor C p).obj A).map π) := by
  have := quasiIso_pullbackCapChainMap_of_quasiIso_self k P A π ζ
  exact (isIso_homologyMap_pullbackCapChainMap_iff k P A π h ζ).1 inferInstance

end TensorTransfer

/-! ### Cohomology pullback-cup as the dual of `pullbackCapChainMap` -/

section ModuleCat

variable {K : Type w} [CommRing K]

/-- **Cohomology action of `pullbackCapChainMap`**: applying `Hom(-, M)` to
`P.pullbackCapChainMap K K π ζ` and identifying the source with `Hᵖ(Z; M)` via
`ChainComplex.homologyLinearYonedaObjExtendIso` recovers `TopPair.pullbackCup`
(`a ↦ π^*a ⌣ [ζ]`) with no sign. -/
theorem homologyMap_linearYonedaFunctor_pullbackCapChainMap (P : TopPair.{w}) {Z : TopCat.{w}}
    (π : P.fst ⟶ Z) {r : ℕ}
    (ζ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r)
    (M : ModuleCat.{w} K) {p m : ℕ} (h : p + r = m)
    (a : Z.singularCohomology (ModuleCat.of K K) K M p) :
    HomologicalComplex.homologyMap
        ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
          (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ).op) m
        ((ChainComplex.homologyLinearYonedaObjExtendIso
          ((TopCat.toSSet.obj Z).chainComplex (𝟙_ (ModuleCat.{w} K))) K M h).inv a) =
      P.pullbackCup M π r p m h
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r ζ) a := by
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  let KZ := (TopCat.toSSet.obj Z).chainComplex (𝟙_ (ModuleCat.{w} K))
  let fY : ChainComplex.linearYonedaObj (KZ.extend (ComplexShape.embeddingDownNatAdd r)) K M ⟶
      (P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K M :=
    (TauCeti.ChainComplex.linearYonedaFunctor K M).map
      (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ).op
  let eUp := (KZ.linearYonedaObj K M).extendCyclesIso (ComplexShape.embeddingUpNatAdd r)
    (show (ComplexShape.embeddingUpNatAdd r).f p = m by
      simp only [ComplexShape.embeddingUpNatAdd_f]; omega)
  let φ : (ChainComplex.linearYonedaObj
      (KZ.extend (ComplexShape.embeddingDownNatAdd r)) K M).cycles m :=
    HomologicalComplex.cyclesMap (KZ.linearYonedaObjExtendIso K M r).inv m (eUp.inv ψ)
  have hφ : ((ChainComplex.linearYonedaObj
        (KZ.extend (ComplexShape.embeddingDownNatAdd r)) K M).iCycles m φ :
          (KZ.extend (ComplexShape.embeddingDownNatAdd r)).X m ⟶ M) =
      (KZ.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = m by
          simp only [ComplexShape.embeddingDownNatAdd_f]; omega)).hom ≫
        ((KZ.linearYonedaObj K M).iCycles p ψ : KZ.X p ⟶ M) := by
    have h₁ := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (KZ.linearYonedaObjExtendIso K M r).inv m) (eUp.inv ψ)
    have h₂ := ConcreteCategory.congr_hom
      ((KZ.linearYonedaObj K M).extendCyclesIso_inv_iCycles (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f p = m by
          simp only [ComplexShape.embeddingUpNatAdd_f]; omega)) ψ
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    exact (h₁.trans (congrArg _ h₂)).trans
      (ChainComplex.extendXIso_inv_comp_linearYonedaObjExtendIso_inv_f KZ K M h _)
  have hinv := ChainComplex.homologyLinearYonedaObjExtendIso_inv_homologyπ KZ K M h ψ φ hφ
  have hnat : HomologicalComplex.homologyMap fY m
        ((ChainComplex.linearYonedaObj
          (KZ.extend (ComplexShape.embeddingDownNatAdd r)) K M).homologyπ m φ) =
      ((P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K M).homologyπ m
        (HomologicalComplex.cyclesMap fY m φ) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality fY m) φ
  change HomologicalComplex.homologyMap fY m
      ((KZ.homologyLinearYonedaObjExtendIso K M h).inv
        ((KZ.linearYonedaObj K M).homologyπ p ψ)) = _
  rw [hinv, hnat]
  -- Evaluate the resulting cocycle on `P` via `capChain_comp`.
  let gπ : KZ.linearYonedaObj K M ⟶
      ((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K M :=
    (TauCeti.ChainComplex.linearYonedaFunctor K M).map
      (SSet.chainComplexMap (TopCat.toSSet.map π) (𝟙_ (ModuleCat.{w} K))).op
  let ψπ : (((TopCat.toSSet.obj P.fst).chainComplex
      (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K M).cycles p :=
    HomologicalComplex.cyclesMap gπ p ψ
  have hψπ : ((((TopCat.toSSet.obj P.fst).chainComplex
        (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K M).iCycles p ψπ :
          ((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{w} K))).X p ⟶ M) =
      (SSet.chainComplexMap (TopCat.toSSet.map π) (𝟙_ (ModuleCat.{w} K))).f p ≫
        ((KZ.linearYonedaObj K M).iCycles p ψ : KZ.X p ⟶ M) :=
    TauCeti.ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply _ p ψ
  have hcyc : HomologicalComplex.cyclesMap fY m φ =
      ((-1 : ℤ) ^ (r * p)) •
        TauCeti.ChainComplex.cupCycles K
          (P.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (λ_ M).hom r p m
          (by omega) ζ ψπ := by
    apply HomologicalComplex.moduleCat_iCycles_injective
    have h1 : (((P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K M).iCycles m
          (HomologicalComplex.cyclesMap fY m φ) :
            (P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).X m ⟶ M) =
        ((-1 : ℤ) ^ (r * p)) •
          (((P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K M).iCycles m
            (TauCeti.ChainComplex.cupCycles K
              (P.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (λ_ M).hom r p m
              (by omega) ζ ψπ) :
                (P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).X m ⟶ M) := by
      obtain ⟨α, hα⟩ : ∃ α : (P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).X r ⟶
            𝟙_ (ModuleCat.{w} K),
          α = (P.singularCochainComplex (𝟙_ (ModuleCat.{w} K)) K
            (𝟙_ (ModuleCat.{w} K))).iCycles r ζ := ⟨_, rfl⟩
      obtain ⟨β, hβ⟩ : ∃ β : KZ.X p ⟶ M,
          β = (KZ.linearYonedaObj K M).iCycles p ψ := ⟨_, rfl⟩
      have hi : (((P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K M).iCycles m
            (HomologicalComplex.cyclesMap fY m φ) :
              (P.singularChainComplex (𝟙_ (ModuleCat.{w} K))).X m ⟶ M) =
          (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ).f m ≫
            ((ChainComplex.linearYonedaObj
              (KZ.extend (ComplexShape.embeddingDownNatAdd r)) K M).iCycles m φ :
                (KZ.extend (ComplexShape.embeddingDownNatAdd r)).X m ⟶ M) :=
        TauCeti.ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply _ m φ
      have hcap := pullbackCapChainMap_f_comp_extendXIso_hom_assoc K P (𝟙_ (ModuleCat.{w} K)) π
        (p := p) (by omega : r + p = m) ζ β
      rw [← hα] at hcap
      rw [hi, hφ, ← hβ, hcap, Preadditive.zsmul_comp, Category.assoc, hβ, ← hψπ,
        TauCeti.ChainComplex.iCycles_cupCycles]
      congr 1
      rw [hα]
      exact TauCeti.ChainComplex.capChain_comp
        (P.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (𝟙_ (ModuleCat.{w} K))).hom)
        (λ_ M).hom r p m (by omega) _ _ _ (by
          rw [SSet.chainComplexPairing_leftUnitor_hom_f]
          exact (MonoidalCategory.leftUnitor_naturality
            ((((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K
              M).iCycles p ψπ :
                ((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{w} K))).X p ⟶ M)).symm)
    simpa only [map_zsmul] using h1
  rw [hcyc, map_zsmul, ← TauCeti.ChainComplex.cup_homologyπ]
  have hπψ : (((TopCat.toSSet.obj P.fst).chainComplex
        (𝟙_ (ModuleCat.{w} K))).linearYonedaObj K M).homologyπ p ψπ =
      TopCat.singularCohomologyMap π p
        ((Z.singularCochainComplex (ModuleCat.of K K) K M).homologyπ p ψ) :=
    (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality gπ p) ψ).symm
  rw [hπψ, TopPair.singularCup_gradedComm K P
    (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
    (μ := (ρ_ M).hom) (μ' := (λ_ M).hom)
    (by rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, ← unitors_inv_equal])
    (braiding_leftUnitor M) h]
  rw [smul_smul, mul_comm p r, ← mul_pow]
  simp only [mul_neg, mul_one, neg_neg, one_pow, one_smul, TopPair.pullbackCup_apply]
  rfl

/-- **Detecting quasi-isomorphisms from `pullbackCup` on arbitrary coefficients**: if
`Hʲ(X, Y; M) = 0` for all `j < r` and `a ↦ π^*a ⌣ [ζ]` is bijective for every `K`-module `M`
and all degrees `p + r = m`, then `P.pullbackCapChainMap K K π ζ` is a quasi-isomorphism. -/
theorem quasiIso_pullbackCapChainMap_of_bijective_pullbackCup (P : TopPair.{w}) {Z : TopCat.{w}}
    (π : P.fst ⟶ Z) {r : ℕ}
    (ζ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r)
    (hvan : ∀ (M : ModuleCat.{w} K) (j : ℕ), j < r →
      IsZero (P.singularCohomology (ModuleCat.of K K) K M j))
    (hbij : ∀ (M : ModuleCat.{w} K) (p m : ℕ) (h : p + r = m),
      Function.Bijective (P.pullbackCup M π r p m h
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r ζ))) :
    QuasiIso (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ) := by
  have : Module.Projective K (𝟙_ (ModuleCat.{w} K)) := inferInstanceAs (Module.Projective K K)
  apply ChainComplex.quasiIso_of_forall_quasiIso_linearYonedaFunctor_map _ K
  intro M
  rw [quasiIso_iff]
  intro m
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hm : r ≤ m
  · let p := m - r
    have h : p + r = m := by omega
    let KZ := (TopCat.toSSet.obj Z).chainComplex (𝟙_ (ModuleCat.{w} K))
    let e := KZ.homologyLinearYonedaObjExtendIso K M h
    have hcomp : e.inv ≫ HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
            (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ).op) m =
        ModuleCat.ofHom (P.pullbackCup M π r p m h
          ((P.singularCochainComplex (ModuleCat.of K K) K
            (ModuleCat.of K K)).homologyπ r ζ)) := by
      ext a
      exact homologyMap_linearYonedaFunctor_pullbackCapChainMap P π ζ M h a
    have hIsoComp : IsIso (e.inv ≫ HomologicalComplex.homologyMap
        ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
          (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ).op) m) := by
      rw [hcomp]
      exact (ConcreteCategory.isIso_iff_bijective _).2 (hbij M p m h)
    exact IsIso.of_isIso_comp_left e.inv _
  · have hZ : IsZero ((ChainComplex.linearYonedaObj
        (((TopCat.toSSet.obj Z).chainComplex (𝟙_ (ModuleCat.{w} K))).extend
          (ComplexShape.embeddingDownNatAdd r)) K M).homology m) :=
      ChainComplex.isZero_homology_linearYonedaObj_extend _ K M r m (by omega)
    have hP : IsZero (P.singularCohomology (ModuleCat.of K K) K M m) := hvan M m (by omega)
    exact ⟨⟨0, hZ.eq_of_src _ _, hP.eq_of_src _ _⟩⟩

/-- **Cohomology bijectivity from chain quasi-isomorphism**: if `P.pullbackCapChainMap K K π ζ`
is a quasi-isomorphism, then `a ↦ π^*a ⌣ [ζ]` is bijective for every `K`-module `M` and all
degrees `p + r = m`. -/
theorem bijective_pullbackCup_of_quasiIso_pullbackCapChainMap (P : TopPair.{w}) {Z : TopCat.{w}}
    (π : P.fst ⟶ Z) {r : ℕ}
    (ζ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r)
    [QuasiIso (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ)]
    (M : ModuleCat.{w} K) {p m : ℕ} (h : p + r = m) :
    Function.Bijective (P.pullbackCup M π r p m h
      ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r ζ)) := by
  have : Module.Projective K (𝟙_ (ModuleCat.{w} K)) := inferInstanceAs (Module.Projective K K)
  have hq : QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
      (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ).op) :=
    ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective _ K M
  have : IsIso (HomologicalComplex.homologyMap
      ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
        (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ).op) m) :=
    (quasiIsoAt_iff_isIso_homologyMap _ m).1 ((quasiIso_iff _).1 hq m)
  let KZ := (TopCat.toSSet.obj Z).chainComplex (𝟙_ (ModuleCat.{w} K))
  let e := KZ.homologyLinearYonedaObjExtendIso K M h
  have hcomp : ModuleCat.ofHom (P.pullbackCup M π r p m h
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r ζ)) =
      e.inv ≫ HomologicalComplex.homologyMap
        ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
          (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ).op) m := by
    ext a
    exact (homologyMap_linearYonedaFunctor_pullbackCapChainMap P π ζ M h a).symm
  have hIso : IsIso (ModuleCat.ofHom (P.pullbackCup M π r p m h
      ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r ζ))) := by
    rw [hcomp]
    change IsIso (e.inv ≫ HomologicalComplex.homologyMap
      ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
        (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ).op) m)
    refine ⟨⟨inv (HomologicalComplex.homologyMap
        ((TauCeti.ChainComplex.linearYonedaFunctor K M).map
          (P.pullbackCapChainMap K (𝟙_ (ModuleCat.{w} K)) π ζ).op) m) ≫ e.hom,
      by simp, by simp⟩⟩
  exact (ConcreteCategory.isIso_iff_bijective _).1 hIso

end ModuleCat

end TopPair
