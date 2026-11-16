/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.MappingCone
public import TauCeti.KnotTheory.Khovanov.AdjoinCircle
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Resolution.Reindex
public import TauCeti.KnotTheory.Khovanov.Resolution.Skein
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Circle.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.One.Basic
public import TauCeti.KnotTheory.PDCode.Reidemeister.One.ResolveCrossing

/-!
# First Reidemeister invariance of Khovanov homology

Inserting a kink into a planar link diagram leaves its Khovanov complex invariant up to an explicit
direct-sum splitting into a contractible mapping cone and the original complex, hence up to a
strong deformation retraction (`TauCeti.SpecialContraction`), a chain homotopy equivalence
(`HomotopyEquiv`), and a bigraded isomorphism on Khovanov homology over every commutative ring `R`.

Resolving the new crossing `Fin.last n` of a kink splits the unnormalized Khovanov bracket into the
mapping cone of the saddle map between its `A`- and `B`-smoothings
(`TauCeti.PDCode.khovanovBracketMappingConeIso`). One resolution recovers the original diagram and
the other detaches a crossing-free circle (`TauCeti.PDCode.ResolutionEquiv`), whose bracket splits
as the direct sum of two shifted copies (`TauCeti.PDCode.adjoinCircleKhovanovBracketIso`):

* For a positive kink (`b = true`), the saddle map merges the detached circle into the circle
  carrying the kink, matching `TauCeti.PDCode.adjoinCircleCollapseMerge`. Its `1`-summand component
  is the identity, so split-epimorphism cancellation (`CochainComplex.mappingCone.isoOfInlCompEqId`)
  splits off a contractible cone `mappingCone (𝟙 _)` and leaves `⟦D⟧` shifted in quantum degree by
  `+1`.
* For a negative kink (`b = false`), the saddle map splits the circle carrying the kink into itself
  and the detached circle, matching `TauCeti.PDCode.adjoinCircleCollapseSplit`. Its `X`-summand
  component is the identity, so split-monomorphism cancellation
  (`CochainComplex.mappingCone.isoOfCompSndEqId`) splits off a contractible cone `mappingCone (𝟙 _)`
  and leaves `⟦D⟧` shifted in quantum degree by `-2` and in cochain degree by `-1`.

Passing to the writhe-normalized Khovanov complex `TauCeti.OrientedPDCode.khovanovComplex` cancels
both shifts exactly, yielding bigraded invariance for both first Reidemeister generators: inserting
a kink on an arc (`TauCeti.OrientedPDCode.reidemeisterOne`) and inserting an isolated kink on a
crossing-free circle (`TauCeti.OrientedPDCode.adjoinKink`).

## Main definitions

In `TauCeti.PDCode`:

* `reidemeisterOneKhovanovBracketTrueIso`, `reidemeisterOneKhovanovBracketFalseIso`: direct-sum
  cancellation isomorphisms for the unnormalized bracket under `PDCode.reidemeisterOne`.
* `reidemeisterOneKhovanovBracketTrueContraction`,
  `reidemeisterOneKhovanovBracketFalseContraction`: the induced special contractions of brackets.
* `adjoinKinkKhovanovBracketTrueIso`, `adjoinKinkKhovanovBracketFalseIso`,
  `adjoinKinkKhovanovBracketTrueContraction`, `adjoinKinkKhovanovBracketFalseContraction`: the
  corresponding decompositions and special contractions for `PDCode.adjoinKink`.

In `TauCeti.OrientedPDCode`:

* `reidemeisterOneKhovanovComplexTrueIso`, `reidemeisterOneKhovanovComplexFalseIso`: direct-sum
  cancellation isomorphisms for the normalized Khovanov complex under
  `OrientedPDCode.reidemeisterOne`.
* `reidemeisterOneKhovanovComplexContraction`, `reidemeisterOneKhovanovComplexHomotopyEquiv`,
  `reidemeisterOneKhovanovHomologyIso`: strong deformation retraction, chain homotopy equivalence,
  and bigraded homology isomorphism for `OrientedPDCode.reidemeisterOne` of either crossing sign.
* `adjoinKinkKhovanovComplexTrueIso`, `adjoinKinkKhovanovComplexFalseIso`,
  `adjoinKinkKhovanovComplexContraction`, `adjoinKinkKhovanovComplexHomotopyEquiv`,
  `adjoinKinkKhovanovHomologyIso`: the corresponding results comparing `OrientedPDCode.adjoinKink`
  with `OrientedPDCode.adjoinCircle`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §5.2.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.5.1.
* D. Bar-Natan, *Fast Khovanov homology computations*, J. Knot Theory Ramifications 16 (2007),
  Lemma 4.2.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex Finset PiTensorProduct DualNumber

universe u

/-! ### Auxiliary shift isomorphism on mapping cones -/

section ShiftHelpers

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- Shifting the mapping cone of an identity morphism gives the mapping cone of the shifted
identity morphism. -/
private def shiftMappingConeIdIso (K : CochainComplex C ℤ) (a : ℤ) :
    (mappingCone (𝟙 K))⟦a⟧ ≅ mappingCone (𝟙 (K⟦a⟧)) :=
  mappingCone.shiftIso (𝟙 K) a ≪≫
    mappingCone.mapIso (Iso.refl _) (Iso.refl _) (by simp)

end ShiftHelpers

/-! ### Cube natural isomorphisms and general bracket cancellation -/

namespace TauCeti.PDCode

section GeneralCancellation

variable {n : ℕ} {D₁ D₂ : PDCode n}

/-- Two `Fin.insertNth` states agree away from the inserted index. -/
private theorem insertNth_eq_of_ne (c : Fin (n + 1)) (t₁ t₂ : Bool) (s : Fin n → Bool)
    {i : Fin (n + 1)} (hi : i ≠ c) :
    (c.insertNth t₁ s : Fin (n + 1) → Bool) i = (c.insertNth t₂ s : Fin (n + 1) → Bool) i := by
  obtain rfl | ⟨j, rfl⟩ := c.eq_self_or_eq_succAbove i
  · exact absurd rfl hi
  · simp

/-- The isomorphism of cube complexes induced by an isomorphism of cubes, typed directly with
`Functor.cubeComplex` endpoints. -/
private def cubeComplexMapIso {R : Type u} [CommRing R]
    {F G : Finset (Fin n) ⥤ ModuleCat.{u} R} (e : F ≅ G) : F.cubeComplex ≅ G.cubeComplex :=
  (cubeComplexFunctor (ModuleCat.{u} R) (Fin n)).mapIso e

@[simp]
private theorem cubeComplexMapIso_hom {R : Type u} [CommRing R]
    {F G : Finset (Fin n) ⥤ ModuleCat.{u} R} (e : F ≅ G) :
    (cubeComplexMapIso e).hom = NatTrans.cubeComplexMap e.hom := rfl

@[simp]
private theorem cubeComplexMapIso_inv {R : Type u} [CommRing R]
    {F G : Finset (Fin n) ⥤ ModuleCat.{u} R} (e : F ≅ G) :
    (cubeComplexMapIso e).inv = NatTrans.cubeComplexMap e.inv := rfl

private theorem cubeComplexMap_eqToHom {R : Type u} [CommRing R]
    {F G : Finset (Fin n) ⥤ ModuleCat.{u} R} (h : F = G) :
    NatTrans.cubeComplexMap (eqToHom h) = eqToHom (congrArg Functor.cubeComplex h) := by
  subst h
  simp

/-- `resolveCrossingCubeCircleEquiv` agrees with `resolveCrossingResolvedCircleEquiv` composed with
the cast along `cubeState_resolveCrossingVertex`. -/
private theorem resolveCrossingCubeCircleEquiv_eq {D : PDCode (n + 1)} (c : Fin (n + 1))
    (t : Bool) (S : Finset (Fin n)) :
    D.resolveCrossingCubeCircleEquiv c t S =
      (D.resolveCrossingResolvedCircleEquiv c t (cubeState S)).trans
        (Equiv.cast (congrArg D.ResolvedCircle (cubeState_resolveCrossingVertex c t S).symm)) := by
  have hcast_inl : ∀ {u v : Fin (n + 1) → Bool} (h : u = v) (x : Fin (4 * (n + 1))),
      Equiv.cast (congrArg D.ResolvedCircle h) (.inl ⟦x⟧) = .inl ⟦x⟧ := by
    rintro u _ rfl x
    rfl
  have hcast_inr : ∀ {u v : Fin (n + 1) → Bool} (h : u = v)
      (i : Fin D.crossinglessComponentCount),
      Equiv.cast (congrArg D.ResolvedCircle h) (.inr i) = .inr i := by
    rintro u _ rfl i
    rfl
  ext C
  rcases C with C | i
  · obtain ⟨x, rfl⟩ := Quotient.exists_rep C
    obtain ⟨⟨i, k⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
    rw [Equiv.trans_apply, resolveCrossingCubeCircleEquiv_inl_mk,
      resolveCrossingResolvedCircleEquiv_inl_mk,
      hcast_inl (cubeState_resolveCrossingVertex c t S).symm]
  · by_cases hi : (i : ℕ) < D.crossinglessComponentCount
    · have hi_eq : i = (Fin.castAdd (D.detachedCircleCount c t) ⟨i, hi⟩).cast
          (D.resolveCrossing_crossinglessComponentCount c t).symm := by
        ext
        rfl
      rw [hi_eq, Equiv.trans_apply, resolveCrossingCubeCircleEquiv_inr_castAdd,
        resolveCrossingResolvedCircleEquiv_inr_castAdd,
        hcast_inr (cubeState_resolveCrossingVertex c t S).symm]
    · have hlt : (i : ℕ) < D.crossinglessComponentCount + D.detachedCircleCount c t := by
        simpa [D.resolveCrossing_crossinglessComponentCount c t] using i.isLt
      have hj : (i : ℕ) - D.crossinglessComponentCount < D.detachedCircleCount c t := by omega
      have hi_eq : i = (Fin.natAdd D.crossinglessComponentCount
            ⟨(i : ℕ) - D.crossinglessComponentCount, hj⟩).cast
          (D.resolveCrossing_crossinglessComponentCount c t).symm := by
        ext
        simp
        omega
      rw [hi_eq, Equiv.trans_apply, resolveCrossingCubeCircleEquiv_inr_natAdd,
        resolveCrossingResolvedCircleEquiv_inr_natAdd,
        hcast_inl (cubeState_resolveCrossingVertex c t S).symm]

/-- A `ResolutionEquiv` fixing the crossing index induces a natural isomorphism of resolution
cubes. -/
private def resolutionCubeNatIso (E : D₁.ResolutionEquiv D₂) (hE : E.crossingEquiv = Equiv.refl _)
    (hD₁ : D₁.IsPlanar) (hD₂ : D₂.IsPlanar) (R : Type u) [CommRing R] (j : ℤ) :
    D₁.resolutionCube hD₁ R j ≅ D₂.resolutionCube hD₂ R j :=
  let α : ∀ S : Finset (Fin n),
      (D₁.resolutionCube hD₁ R j).obj S ≅ (D₂.resolutionCube hD₂ R j).obj S :=
    fun S ↦ E.resolutionCubeIso hD₁ hD₂ R j S ≪≫
      eqToIso (congrArg (D₂.resolutionCube hD₂ R j).obj (by simp [hE]))
  NatIso.ofComponents α fun {S T} f ↦ by
    have hnat := (NatTrans.ofCubeEdges (F := D₁.resolutionCube hD₁ R j)
      (G := D₂.resolutionCube hD₂ R j) (fun U ↦ (α U).hom) fun U V hUV ↦ by
        obtain ⟨a, ha, rfl⟩ := hUV.exists_finset_insert
        have hcomp := (Functor.isCubeReindexCompatible_iff.1
          (E.isCubeReindexCompatible hD₁ hD₂ R j)) U a ha
        have hU : U.map E.crossingEquiv.toEmbedding = U := by simp [hE]
        have hIU : (insert a U).map E.crossingEquiv.toEmbedding = insert a U := by simp [hE]
        have hle : homOfLE (hUV.le) = homOfLE (U.subset_insert a) := Subsingleton.elim _ _
        have hsq : ∀ {A B A' B' : Finset (Fin n)} (hA : A = A') (hB : B = B')
            (hab : A ⊆ B) (hab' : A' ⊆ B'),
            (D₂.resolutionCube hD₂ R j).map (homOfLE hab) ≫
                eqToHom (congrArg (D₂.resolutionCube hD₂ R j).obj hB) =
              eqToHom (congrArg (D₂.resolutionCube hD₂ R j).obj hA) ≫
                (D₂.resolutionCube hD₂ R j).map (homOfLE hab') := by
          rintro A B _ _ rfl rfl hab hab'
          simp
        dsimp only [α]
        rw [hle, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom,
          ← Category.assoc, hcomp, Category.assoc,
          hsq hU hIU (map_subset_map.2 (U.subset_insert a)) (U.subset_insert a),
          ← Category.assoc]).naturality f
    simpa only [NatTrans.ofCubeEdges_app] using hnat

@[reassoc]
private theorem resolutionCubeNatIso_hom_app_comp_resolutionCubeι
    (E : D₁.ResolutionEquiv D₂) (hE : E.crossingEquiv = Equiv.refl _)
    (hD₁ : D₁.IsPlanar) (hD₂ : D₂.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)
    (S : Finset (Fin n)) :
    (resolutionCubeNatIso E hE hD₁ hD₂ R j).hom.app S ≫ D₂.resolutionCubeι hD₂ R j S =
      D₁.resolutionCubeι hD₁ R j S ≫
        ModuleCat.ofHom (reindex R (fun _ ↦ R[ε])
          (E.smoothingEquiv (s := cubeState S) (t := cubeState S)
            (fun i ↦ by simp [hE])).resolvedCircleCongr).toLinearMap := by
  have haux : ∀ {T : Finset (Fin n)} (hT : S.map E.crossingEquiv.toEmbedding = T)
      (h : ∀ i, cubeState T (E.crossingEquiv i) = cubeState S i),
      (E.resolutionCubeIso hD₁ hD₂ R j S).hom ≫
          eqToHom (congrArg (D₂.resolutionCube hD₂ R j).obj hT) ≫ D₂.resolutionCubeι hD₂ R j T =
        D₁.resolutionCubeι hD₁ R j S ≫
          ModuleCat.ofHom (reindex R (fun _ ↦ R[ε])
            (E.smoothingEquiv h).resolvedCircleCongr).toLinearMap := by
    intro T hT h
    subst hT
    rw [eqToHom_refl, Category.id_comp, E.resolutionCubeIso_hom_comp_resolutionCubeι]
  simpa only [resolutionCubeNatIso, NatIso.ofComponents_hom_app, Iso.trans_hom, eqToIso.hom,
    Category.assoc] using haux (by simp [hE]) (fun i ↦ by simp [hE])

/-- Reindexing transport for a saddle merge with states equal to `c.insertNth`. -/
private theorem reindex_cast_resolutionMergeMap_collapse {D : PDCode n} {D' : PDCode (n + 1)}
    (c : Fin (n + 1)) (p : D.Mark) (s : Fin n → Bool) {u v : Fin (n + 1) → Bool}
    (hu : c.insertNth true s = u) (hv : c.insertNth false s = v)
    (huv : ∀ i, i ≠ c → u i = v i) (hc : u c ≠ v c)
    (hcard : #(D'.circlesAt u c) = 2)
    (eA : D.adjoinCircle.ResolvedCircle s ≃ (D'.resolveCrossing c true).ResolvedCircle s)
    (eB : D.ResolvedCircle s ≃ (D'.resolveCrossing c false).ResolvedCircle s)
    (hmap : ∀ (hB : #(D'.circlesAt (c.insertNth false s) c) = 1)
      (C : D.adjoinCircle.ResolvedCircle s),
      D'.saddleResolvedCircleMap (fun _ hi ↦ insertNth_eq_of_ne c true false s hi) hB
          (D'.resolveCrossingResolvedCircleEquiv c true s (eA C)) =
        D'.resolveCrossingResolvedCircleEquiv c false s (eB (D.adjoinCircleCollapse p s C)))
    (R : Type u) [CommRing R] (x : Khovanov.CircleTensor R (D.adjoinCircle.ResolvedCircle s)) :
    D'.resolutionMergeMap huv hc hcard R
        (reindex R (fun _ ↦ R[ε])
          ((eA.trans (D'.resolveCrossingResolvedCircleEquiv c true s)).trans
            (Equiv.cast (congrArg D'.ResolvedCircle hu))) x) =
      reindex R (fun _ ↦ R[ε])
        ((eB.trans (D'.resolveCrossingResolvedCircleEquiv c false s)).trans
          (Equiv.cast (congrArg D'.ResolvedCircle hv)))
        (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) (D.adjoinCircleCollapse p s) x) := by
  subst hu hv
  simp only [Equiv.cast_refl, Equiv.trans_refl, resolutionMergeMap_def]
  exact (reindex_fiberwiseMul
    (eA.trans (D'.resolveCrossingResolvedCircleEquiv c true s))
    (eB.trans (D'.resolveCrossingResolvedCircleEquiv c false s))
    (funext fun C ↦ (hmap (D'.card_circlesAt_eq_one_of_card_circlesAt_eq_two huv hc hcard) C).symm)
    x).symm

/-- Reindexing transport for a saddle split with states equal to `c.insertNth`. -/
private theorem reindex_cast_resolutionSplitMap_collapse {D : PDCode n} {D' : PDCode (n + 1)}
    (c : Fin (n + 1)) (p : D.Mark) (s : Fin n → Bool) {u v : Fin (n + 1) → Bool}
    (hu : c.insertNth true s = u) (hv : c.insertNth false s = v)
    (huv : ∀ i, i ≠ c → u i = v i) (hc : u c ≠ v c)
    (hcard : #(D'.circlesAt v c) = 2)
    (eA : D.ResolvedCircle s ≃ (D'.resolveCrossing c true).ResolvedCircle s)
    (eB : D.adjoinCircle.ResolvedCircle s ≃ (D'.resolveCrossing c false).ResolvedCircle s)
    (hmap : ∀ (hA : #(D'.circlesAt (c.insertNth true s) c) = 1)
      (C : D.adjoinCircle.ResolvedCircle s),
      D'.saddleResolvedCircleMap (fun _ hi ↦ insertNth_eq_of_ne c false true s hi) hA
          (D'.resolveCrossingResolvedCircleEquiv c false s (eB C)) =
        D'.resolveCrossingResolvedCircleEquiv c true s (eA (D.adjoinCircleCollapse p s C)))
    (R : Type u) [CommRing R] (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D'.resolutionSplitMap huv hc hcard R
        (reindex R (fun _ ↦ R[ε])
          ((eA.trans (D'.resolveCrossingResolvedCircleEquiv c true s)).trans
            (Equiv.cast (congrArg D'.ResolvedCircle hu))) x) =
      reindex R (fun _ ↦ R[ε])
        ((eB.trans (D'.resolveCrossingResolvedCircleEquiv c false s)).trans
          (Equiv.cast (congrArg D'.ResolvedCircle hv)))
        (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleCollapse p s) x) := by
  subst hu hv
  simp only [Equiv.cast_refl, Equiv.trans_refl, resolutionSplitMap_def]
  exact (Khovanov.reindex_fiberwiseSplit
    (eB.trans (D'.resolveCrossingResolvedCircleEquiv c false s))
    (eA.trans (D'.resolveCrossingResolvedCircleEquiv c true s))
    (funext fun C ↦
      (hmap (D'.card_circlesAt_eq_one_of_card_circlesAt_eq_two
        (fun i hi ↦ (huv i hi).symm) hc.symm hcard) C).symm) x).symm

/-- When the `A`- and `B`-resolutions at `c` match `D.adjoinCircle` and `D` and the saddle at `c`
matches `adjoinCircleCollapseMerge` on circles, the saddle map of cubes coincides with
`D.adjoinCircleCollapseMerge` through the cube identifications. -/
private theorem resolveCrossingSaddle_eq_adjoinCircleCollapseMerge
    {D : PDCode n} {D' : PDCode (n + 1)} (c : Fin (n + 1)) (p : D.Mark)
    (hD : D.IsPlanar) (hD₀ : D.adjoinCircle.IsPlanar) (hD' : D'.IsPlanar)
    (E_A : D.adjoinCircle.ResolutionEquiv (D'.resolveCrossing c true))
    (hEA : E_A.crossingEquiv = Equiv.refl _)
    (E_B : D.ResolutionEquiv (D'.resolveCrossing c false))
    (hEB : E_B.crossingEquiv = Equiv.refl _)
    (hcard : ∀ s : Fin n → Bool, #(D'.circlesAt (c.insertNth true s) c) = 2)
    (hmap : ∀ (s : Fin n → Bool) (hB : #(D'.circlesAt (c.insertNth false s) c) = 1)
      (C : D.adjoinCircle.ResolvedCircle s),
      D'.saddleResolvedCircleMap (fun _ hi ↦ insertNth_eq_of_ne c true false s hi) hB
          (D'.resolveCrossingResolvedCircleEquiv c true s
            ((E_A.smoothingEquiv (s := s) (t := s) (fun i ↦ by simp [hEA])).resolvedCircleCongr
              C)) =
        D'.resolveCrossingResolvedCircleEquiv c false s
          ((E_B.smoothingEquiv (s := s) (t := s) (fun i ↦ by simp [hEB])).resolvedCircleCongr
            (D.adjoinCircleCollapse p s C)))
    (R : Type u) [CommRing R] (j : ℤ) :
    (resolutionCubeNatIso E_A hEA hD₀ (hD'.resolveCrossing _ c true) R j).hom ≫
        D'.resolveCrossingSaddle c hD' R j =
      D.adjoinCircleCollapseMerge hD hD₀ R p j ≫
        (resolutionCubeNatIso E_B hEB hD (hD'.resolveCrossing _ c false) R (j - 1)).hom := by
  ext S : 2
  have hst : ∀ i, i ≠ c → cubeState (resolveCrossingVertex c true S) i =
      cubeState (resolveCrossingVertex c false S) i := fun i hi ↦ by
    rw [cubeState_resolveCrossingVertex, cubeState_resolveCrossingVertex]
    exact insertNth_eq_of_ne c true false (cubeState S) hi
  have hc : cubeState (resolveCrossingVertex c true S) c ≠
      cubeState (resolveCrossingVertex c false S) c := by
    rw [cubeState_resolveCrossingVertex, cubeState_resolveCrossingVertex]
    simp
  have hcardS : #(D'.circlesAt (cubeState (resolveCrossingVertex c true S)) c) = 2 := by
    rw [cubeState_resolveCrossingVertex]
    exact hcard (cubeState S)
  rw [← cancel_mono ((D'.resolveCrossing c false).resolutionCubeι
      (hD'.resolveCrossing _ c false) R (j - 1) S ≫
    (reindex R (fun _ ↦ R[ε]) (D'.resolveCrossingCubeCircleEquiv c false S)).toModuleIso.hom)]
  simp only [NatTrans.comp_app, Category.assoc, LinearEquiv.toModuleIso_hom]
  rw [D'.resolveCrossingSaddle_app_comp_resolutionCubeι c hD' R j S hst hc (.inl hcardS),
    resolutionCubeNatIso_hom_app_comp_resolutionCubeι_assoc E_A hEA,
    resolutionCubeNatIso_hom_app_comp_resolutionCubeι_assoc E_B hEB,
    D.adjoinCircleCollapseMerge_app_comp_resolutionCubeι_assoc hD hD₀ R p j S]
  ext x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AlgHom.toLinearMap_apply]
  rw [D'.resolutionEdgeMap_eq_resolutionMergeMap hst hc (.inl hcardS) R hcardS,
    AlgHom.toLinearMap_apply]
  have hreA : reindex R (fun _ ↦ R[ε]) (D'.resolveCrossingCubeCircleEquiv c true S)
      (reindex R (fun _ ↦ R[ε]) ((E_A.smoothingEquiv (s := cubeState S) (t := cubeState S)
        (fun i ↦ by simp [hEA])).resolvedCircleCongr)
        ((D.adjoinCircle.resolutionCubeι hD₀ R j S).hom x)) =
      reindex R (fun _ ↦ R[ε])
        ((((E_A.smoothingEquiv (s := cubeState S) (t := cubeState S)
            (fun i ↦ by simp [hEA])).resolvedCircleCongr).trans
          (D'.resolveCrossingResolvedCircleEquiv c true (cubeState S))).trans
          (Equiv.cast (congrArg D'.ResolvedCircle
            (cubeState_resolveCrossingVertex c true S).symm)))
        ((D.adjoinCircle.resolutionCubeι hD₀ R j S).hom x) := by
    simp [resolveCrossingCubeCircleEquiv_eq, ← reindex_trans, Equiv.trans_assoc]
  have hreB : reindex R (fun _ ↦ R[ε]) (D'.resolveCrossingCubeCircleEquiv c false S)
      (reindex R (fun _ ↦ R[ε]) ((E_B.smoothingEquiv (s := cubeState S) (t := cubeState S)
        (fun i ↦ by simp [hEB])).resolvedCircleCongr)
        (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) (D.adjoinCircleCollapse p (cubeState S))
          ((D.adjoinCircle.resolutionCubeι hD₀ R j S).hom x))) =
      reindex R (fun _ ↦ R[ε])
        ((((E_B.smoothingEquiv (s := cubeState S) (t := cubeState S)
            (fun i ↦ by simp [hEB])).resolvedCircleCongr).trans
          (D'.resolveCrossingResolvedCircleEquiv c false (cubeState S))).trans
          (Equiv.cast (congrArg D'.ResolvedCircle
            (cubeState_resolveCrossingVertex c false S).symm)))
        (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) (D.adjoinCircleCollapse p (cubeState S))
          ((D.adjoinCircle.resolutionCubeι hD₀ R j S).hom x)) := by
    simp [resolveCrossingCubeCircleEquiv_eq, ← reindex_trans, Equiv.trans_assoc]
  rw [hreA, hreB]
  exact reindex_cast_resolutionMergeMap_collapse c p (cubeState S)
    (cubeState_resolveCrossingVertex c true S).symm
    (cubeState_resolveCrossingVertex c false S).symm hst hc hcardS _ _
    (hmap (cubeState S)) R _

/-- When the `A`- and `B`-resolutions at `c` match `D` and `D.adjoinCircle` and the saddle at `c`
matches `adjoinCircleCollapseSplit` on circles, the saddle map of cubes coincides with
`D.adjoinCircleCollapseSplit` through the cube identifications. -/
private theorem resolveCrossingSaddle_eq_adjoinCircleCollapseSplit
    {D : PDCode n} {D' : PDCode (n + 1)} (c : Fin (n + 1)) (p : D.Mark)
    (hD : D.IsPlanar) (hD₀ : D.adjoinCircle.IsPlanar) (hD' : D'.IsPlanar)
    (E_A : D.ResolutionEquiv (D'.resolveCrossing c true))
    (hEA : E_A.crossingEquiv = Equiv.refl _)
    (E_B : D.adjoinCircle.ResolutionEquiv (D'.resolveCrossing c false))
    (hEB : E_B.crossingEquiv = Equiv.refl _)
    (hcard : ∀ s : Fin n → Bool, #(D'.circlesAt (c.insertNth false s) c) = 2)
    (hmap : ∀ (s : Fin n → Bool) (hA : #(D'.circlesAt (c.insertNth true s) c) = 1)
      (C : D.adjoinCircle.ResolvedCircle s),
      D'.saddleResolvedCircleMap (fun _ hi ↦ insertNth_eq_of_ne c false true s hi) hA
          (D'.resolveCrossingResolvedCircleEquiv c false s
            ((E_B.smoothingEquiv (s := s) (t := s) (fun i ↦ by simp [hEB])).resolvedCircleCongr
              C)) =
        D'.resolveCrossingResolvedCircleEquiv c true s
          ((E_A.smoothingEquiv (s := s) (t := s) (fun i ↦ by simp [hEA])).resolvedCircleCongr
            (D.adjoinCircleCollapse p s C)))
    (R : Type u) [CommRing R] (j : ℤ) :
    (resolutionCubeNatIso E_A hEA hD (hD'.resolveCrossing _ c true) R j).hom ≫
        D'.resolveCrossingSaddle c hD' R j =
      D.adjoinCircleCollapseSplit hD hD₀ R p j ≫
        (resolutionCubeNatIso E_B hEB hD₀ (hD'.resolveCrossing _ c false) R (j - 1)).hom := by
  ext S : 2
  have hst : ∀ i, i ≠ c → cubeState (resolveCrossingVertex c true S) i =
      cubeState (resolveCrossingVertex c false S) i := fun i hi ↦ by
    rw [cubeState_resolveCrossingVertex, cubeState_resolveCrossingVertex]
    exact insertNth_eq_of_ne c true false (cubeState S) hi
  have hc : cubeState (resolveCrossingVertex c true S) c ≠
      cubeState (resolveCrossingVertex c false S) c := by
    rw [cubeState_resolveCrossingVertex, cubeState_resolveCrossingVertex]
    simp
  have hcardS : #(D'.circlesAt (cubeState (resolveCrossingVertex c false S)) c) = 2 := by
    rw [cubeState_resolveCrossingVertex]
    exact hcard (cubeState S)
  rw [← cancel_mono ((D'.resolveCrossing c false).resolutionCubeι
      (hD'.resolveCrossing _ c false) R (j - 1) S ≫
    (reindex R (fun _ ↦ R[ε]) (D'.resolveCrossingCubeCircleEquiv c false S)).toModuleIso.hom)]
  simp only [NatTrans.comp_app, Category.assoc, LinearEquiv.toModuleIso_hom]
  rw [D'.resolveCrossingSaddle_app_comp_resolutionCubeι c hD' R j S hst hc (.inr hcardS),
    resolutionCubeNatIso_hom_app_comp_resolutionCubeι_assoc E_A hEA,
    resolutionCubeNatIso_hom_app_comp_resolutionCubeι_assoc E_B hEB,
    D.adjoinCircleCollapseSplit_app_comp_resolutionCubeι_assoc hD hD₀ R p j S]
  ext x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [D'.resolutionEdgeMap_eq_resolutionSplitMap hst hc (.inr hcardS) R hcardS]
  have hreA : reindex R (fun _ ↦ R[ε]) (D'.resolveCrossingCubeCircleEquiv c true S)
      (reindex R (fun _ ↦ R[ε]) ((E_A.smoothingEquiv (s := cubeState S) (t := cubeState S)
        (fun i ↦ by simp [hEA])).resolvedCircleCongr)
        ((D.resolutionCubeι hD R j S).hom x)) =
      reindex R (fun _ ↦ R[ε])
        ((((E_A.smoothingEquiv (s := cubeState S) (t := cubeState S)
            (fun i ↦ by simp [hEA])).resolvedCircleCongr).trans
          (D'.resolveCrossingResolvedCircleEquiv c true (cubeState S))).trans
          (Equiv.cast (congrArg D'.ResolvedCircle
            (cubeState_resolveCrossingVertex c true S).symm)))
        ((D.resolutionCubeι hD R j S).hom x) := by
    simp [resolveCrossingCubeCircleEquiv_eq, ← reindex_trans, Equiv.trans_assoc]
  have hreB : reindex R (fun _ ↦ R[ε]) (D'.resolveCrossingCubeCircleEquiv c false S)
      (reindex R (fun _ ↦ R[ε]) ((E_B.smoothingEquiv (s := cubeState S) (t := cubeState S)
        (fun i ↦ by simp [hEB])).resolvedCircleCongr)
        (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleCollapse p (cubeState S))
          ((D.resolutionCubeι hD R j S).hom x))) =
      reindex R (fun _ ↦ R[ε])
        ((((E_B.smoothingEquiv (s := cubeState S) (t := cubeState S)
            (fun i ↦ by simp [hEB])).resolvedCircleCongr).trans
          (D'.resolveCrossingResolvedCircleEquiv c false (cubeState S))).trans
          (Equiv.cast (congrArg D'.ResolvedCircle
            (cubeState_resolveCrossingVertex c false S).symm)))
        (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleCollapse p (cubeState S))
          ((D.resolutionCubeι hD R j S).hom x)) := by
    simp [resolveCrossingCubeCircleEquiv_eq, ← reindex_trans, Equiv.trans_assoc]
  rw [hreA, hreB]
  exact reindex_cast_resolutionSplitMap_collapse c p (cubeState S)
    (cubeState_resolveCrossingVertex c true S).symm
    (cubeState_resolveCrossingVertex c false S).symm hst hc hcardS _ _
    (hmap (cubeState S)) R _

/-- **General bracket cancellation (merge case).** If the saddle map at `c` agrees with
`adjoinCircleCollapseMerge` through crossing-preserving `ResolutionEquiv`s, then
`⟦D'⟧ʲ ≅ mappingCone (𝟙 (⟦D⟧ʲ⁻¹⟦-1⟧)) ⊞ ⟦D⟧ʲ⁺¹`. -/
private def khovanovBracketMergeCancelIso
    {D : PDCode n} {D' : PDCode (n + 1)} (c : Fin (n + 1)) (p : D.Mark)
    (hD : D.IsPlanar) (hD₀ : D.adjoinCircle.IsPlanar) (hD' : D'.IsPlanar)
    (E_A : D.adjoinCircle.ResolutionEquiv (D'.resolveCrossing c true))
    (hEA : E_A.crossingEquiv = Equiv.refl _)
    (E_B : D.ResolutionEquiv (D'.resolveCrossing c false))
    (hEB : E_B.crossingEquiv = Equiv.refl _)
    (hcard : ∀ s : Fin n → Bool, #(D'.circlesAt (c.insertNth true s) c) = 2)
    (hmap : ∀ (s : Fin n → Bool) (hB : #(D'.circlesAt (c.insertNth false s) c) = 1)
      (C : D.adjoinCircle.ResolvedCircle s),
      D'.saddleResolvedCircleMap (fun _ hi ↦ insertNth_eq_of_ne c true false s hi) hB
          (D'.resolveCrossingResolvedCircleEquiv c true s
            ((E_A.smoothingEquiv (s := s) (t := s) (fun i ↦ by simp [hEA])).resolvedCircleCongr
              C)) =
        D'.resolveCrossingResolvedCircleEquiv c false s
          ((E_B.smoothingEquiv (s := s) (t := s) (fun i ↦ by simp [hEB])).resolvedCircleCongr
            (D.adjoinCircleCollapse p s C)))
    (R : Type u) [CommRing R] (j : ℤ) :
    D'.khovanovBracket hD' R j ≅
      mappingCone (𝟙 ((D.khovanovBracket hD R (j - 1))⟦(-1 : ℤ)⟧)) ⊞
        D.khovanovBracket hD R (j + 1) :=
  let isoA := resolutionCubeNatIso E_A hEA hD₀ (hD'.resolveCrossing _ c true) R j
  let isoB := resolutionCubeNatIso E_B hEB hD (hD'.resolveCrossing _ c false) R (j - 1)
  let eA : D.khovanovBracket hD R (j - 1) ⊞ D.khovanovBracket hD R (j + 1) ≅
      ((D'.resolveCrossing c true).resolutionCube (hD'.resolveCrossing _ c true) R j).cubeComplex :=
    (D.adjoinCircleKhovanovBracketIso hD hD₀ R j).symm ≪≫
      eqToIso (D.adjoinCircle.khovanovBracket_apply hD₀ R j) ≪≫
      cubeComplexMapIso isoA
  let eB : D.khovanovBracket hD R (j - 1) ≅
      ((D'.resolveCrossing c false).resolutionCube (hD'.resolveCrossing _ c false) R
        (j - 1)).cubeComplex :=
    eqToIso (D.khovanovBracket_apply hD R (j - 1)) ≪≫
      cubeComplexMapIso isoB
  let φ : D.khovanovBracket hD R (j - 1) ⊞ D.khovanovBracket hD R (j + 1) ⟶
      D.khovanovBracket hD R (j - 1) :=
    eA.hom ≫ NatTrans.cubeComplexMap (D'.resolveCrossingSaddle c hD' R j) ≫ eB.inv
  have hcube : isoA.hom ≫ D'.resolveCrossingSaddle c hD' R j ≫ isoB.inv =
      D.adjoinCircleCollapseMerge hD hD₀ R p j := by
    rw [← Category.assoc, resolveCrossingSaddle_eq_adjoinCircleCollapseMerge c p hD hD₀ hD' E_A hEA
      E_B hEB hcard hmap R j, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hφ : biprod.inl ≫ φ = 𝟙 (D.khovanovBracket hD R (j - 1)) := by
    dsimp only [φ, eA, eB]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      cubeComplexMapIso_hom, cubeComplexMapIso_inv, Category.assoc,
      inl_adjoinCircleKhovanovBracketIso_inv_assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
      ← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
      ← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
      Category.assoc, Category.assoc, hcube, D.adjoinCircleCubeInl_comp_collapseMerge hD hD₀ R p j,
      NatTrans.cubeComplexMap_id]
    simp
  have hcone : (D'.khovanovBracket hD' R j)⟦(1 : ℤ)⟧ ≅
      mappingCone (𝟙 (D.khovanovBracket hD R (j - 1))) ⊞
        (D.khovanovBracket hD R (j + 1))⟦(1 : ℤ)⟧ :=
    (D'.khovanovBracketMappingConeIso c hD' R j).symm ≪≫
      (mappingCone.mapIso eA eB (by simp [φ])).symm ≪≫
      mappingCone.isoOfInlCompEqId hφ
  let S := CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (-1 : ℤ)
  letI := preservesBinaryBiproducts_of_preservesBiproducts S
  let cancel := CategoryTheory.shiftFunctorCompIsoId
    (CochainComplex (ModuleCat.{u} R) ℤ) (1 : ℤ) (-1 : ℤ) (by omega)
  (cancel.app (D'.khovanovBracket hD' R j)).symm ≪≫
    S.mapIso hcone ≪≫
    S.mapBiprod _ _ ≪≫
    biprod.mapIso (shiftMappingConeIdIso _ (-1)) (cancel.app _)

/-- **General bracket cancellation (split case).** If the saddle map at `c` agrees with
`adjoinCircleCollapseSplit` through crossing-preserving `ResolutionEquiv`s, then
`⟦D'⟧ʲ ≅ mappingCone (𝟙 (⟦D⟧ʲ⟦-1⟧)) ⊞ ⟦D⟧ʲ⁻²⟦-1⟧`. -/
private def khovanovBracketSplitCancelIso
    {D : PDCode n} {D' : PDCode (n + 1)} (c : Fin (n + 1)) (p : D.Mark)
    (hD : D.IsPlanar) (hD₀ : D.adjoinCircle.IsPlanar) (hD' : D'.IsPlanar)
    (E_A : D.ResolutionEquiv (D'.resolveCrossing c true))
    (hEA : E_A.crossingEquiv = Equiv.refl _)
    (E_B : D.adjoinCircle.ResolutionEquiv (D'.resolveCrossing c false))
    (hEB : E_B.crossingEquiv = Equiv.refl _)
    (hcard : ∀ s : Fin n → Bool, #(D'.circlesAt (c.insertNth false s) c) = 2)
    (hmap : ∀ (s : Fin n → Bool) (hA : #(D'.circlesAt (c.insertNth true s) c) = 1)
      (C : D.adjoinCircle.ResolvedCircle s),
      D'.saddleResolvedCircleMap (fun _ hi ↦ insertNth_eq_of_ne c false true s hi) hA
          (D'.resolveCrossingResolvedCircleEquiv c false s
            ((E_B.smoothingEquiv (s := s) (t := s) (fun i ↦ by simp [hEB])).resolvedCircleCongr
              C)) =
        D'.resolveCrossingResolvedCircleEquiv c true s
          ((E_A.smoothingEquiv (s := s) (t := s) (fun i ↦ by simp [hEA])).resolvedCircleCongr
            (D.adjoinCircleCollapse p s C)))
    (R : Type u) [CommRing R] (j : ℤ) :
    D'.khovanovBracket hD' R j ≅
      mappingCone (𝟙 ((D.khovanovBracket hD R j)⟦(-1 : ℤ)⟧)) ⊞
        (D.khovanovBracket hD R (j - 2))⟦(-1 : ℤ)⟧ :=
  let isoA := resolutionCubeNatIso E_A hEA hD (hD'.resolveCrossing _ c true) R j
  let isoB := resolutionCubeNatIso E_B hEB hD₀ (hD'.resolveCrossing _ c false) R (j - 1)
  let eA : D.khovanovBracket hD R j ≅
      ((D'.resolveCrossing c true).resolutionCube (hD'.resolveCrossing _ c true) R j).cubeComplex :=
    eqToIso (D.khovanovBracket_apply hD R j) ≪≫
      cubeComplexMapIso isoA
  let eB : D.khovanovBracket hD R (j - 2) ⊞ D.khovanovBracket hD R j ≅
      ((D'.resolveCrossing c false).resolutionCube (hD'.resolveCrossing _ c false) R
        (j - 1)).cubeComplex :=
    biprod.mapIso (eqToIso (by congr 1; omega)) (eqToIso (by congr 1; omega)) ≪≫
      (D.adjoinCircleKhovanovBracketIso hD hD₀ R (j - 1)).symm ≪≫
      eqToIso (D.adjoinCircle.khovanovBracket_apply hD₀ R (j - 1)) ≪≫
      cubeComplexMapIso isoB
  let φ : D.khovanovBracket hD R j ⟶
      D.khovanovBracket hD R (j - 2) ⊞ D.khovanovBracket hD R j :=
    eA.hom ≫ NatTrans.cubeComplexMap (D'.resolveCrossingSaddle c hD' R j) ≫ eB.inv
  have hcube : isoA.hom ≫ D'.resolveCrossingSaddle c hD' R j ≫ isoB.inv =
      D.adjoinCircleCollapseSplit hD hD₀ R p j := by
    rw [← Category.assoc, resolveCrossingSaddle_eq_adjoinCircleCollapseSplit c p hD hD₀ hD' E_A hEA
      E_B hEB hcard hmap R j, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hφ : φ ≫ biprod.snd = 𝟙 (D.khovanovBracket hD R j) := by
    dsimp only [φ, eA, eB]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, eqToIso.hom, eqToIso.inv,
      cubeComplexMapIso_hom, cubeComplexMapIso_inv, biprod.mapIso_inv, Category.assoc,
      biprod.map_snd, adjoinCircleKhovanovBracketIso_hom_snd_assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
      ← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
      ← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
      Category.assoc (isoA.hom), hcube, D.collapseSplit_comp_adjoinCircleCubeSnd hD hD₀ R p j,
      cubeComplexMap_eqToHom]
    simp
  have hcone : (D'.khovanovBracket hD' R j)⟦(1 : ℤ)⟧ ≅
      mappingCone (𝟙 (D.khovanovBracket hD R j)) ⊞ D.khovanovBracket hD R (j - 2) :=
    (D'.khovanovBracketMappingConeIso c hD' R j).symm ≪≫
      (mappingCone.mapIso eA eB (by simp [φ])).symm ≪≫
      mappingCone.isoOfCompSndEqId hφ
  let S := CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (-1 : ℤ)
  letI := preservesBinaryBiproducts_of_preservesBiproducts S
  let cancel := CategoryTheory.shiftFunctorCompIsoId
    (CochainComplex (ModuleCat.{u} R) ℤ) (1 : ℤ) (-1 : ℤ) (by omega)
  (cancel.app (D'.khovanovBracket hD' R j)).symm ≪≫
    S.mapIso hcone ≪≫
    S.mapBiprod _ _ ≪≫
    biprod.mapIso (shiftMappingConeIdIso _ (-1)) (Iso.refl _)

end GeneralCancellation

/-! ### Unnormalized Khovanov bracket under `PDCode.reidemeisterOne` -/

section ReidemeisterOneBracket

variable {n : ℕ} (D : PDCode n) (h : Fin (4 * n))

/-- In the `b`-smoothing of the kink `D.reidemeisterOne h b`, the new crossing meets two circles:
the circle through the cut arc `h` and the detached loop `{2, 3}`. -/
private theorem card_circlesAt_reidemeisterOne_self (b : Bool) (s : Fin n → Bool) :
    #((D.reidemeisterOne h b).circlesAt ((Fin.last n).insertNth b s) (Fin.last n)) = 2 := by
  set D' := D.reidemeisterOne h b
  have hdet : D'.detachedCircleCount (Fin.last n) b = 1 := by
    simp [D', detachedCircleCount_reidemeisterOne_last]
  obtain ⟨⟨i₀, k₀⟩, hik₀⟩ := (crossingSlotEquiv n).surjective (D.halfEdge.symm h)
  have hh : D.crossing i₀ k₀ = h := by
    rw [crossing_apply, hik₀, Equiv.apply_symm_apply]
  have he0 : D'.edgePair.val (D'.crossing (Fin.last n) 0) =
      D'.crossing ((Fin.last n).succAbove i₀) k₀ := by
    rw [Fin.succAbove_last, crossing_apply, crossing_apply, crossingSlotEquiv_succ_last,
      crossingSlotEquiv_succ_castSucc, reidemeisterOne_crossing_last,
      reidemeisterOne_crossing_castSucc, reidemeisterOne_edgePair_inr_zero, hh]
  have h0_eq : D'.resolveCrossingResolvedCircleEquiv (Fin.last n) b s
      (.inl ⟦crossingSlotEquiv n (i₀, k₀)⟧) = .inl ⟦D'.crossing (Fin.last n) 0⟧ := by
    rw [resolveCrossingResolvedCircleEquiv_inl_mk, ← he0, CrossingCircle.mk_edgePair]
  have h2_eq : D'.resolveCrossingResolvedCircleEquiv (Fin.last n) b s
      (.inr ((Fin.natAdd D'.crossinglessComponentCount ⟨0, by omega⟩).cast
        (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) b).symm)) =
      .inl ⟦D'.crossing (Fin.last n) 2⟧ := by
    rw [resolveCrossingResolvedCircleEquiv_inr_natAdd]
    have hne : D'.edgePair.val (D'.crossing (Fin.last n) 0) ≠
        D'.crossing (Fin.last n)
          (slotSmoothing (bif b then D'.overPair (Fin.last n) else !D'.overPair (Fin.last n))
            0) := by
      rw [he0, Fin.succAbove_last]
      simp [D']
    rw [ite_eq_right (fun h ↦ hne h.2)]
  have hne02 : (⟦D'.crossing (Fin.last n) 0⟧ : D'.CrossingCircle ((Fin.last n).insertNth b s)) ≠
      ⟦D'.crossing (Fin.last n) 2⟧ := by
    intro heq
    have hcongr : D'.resolveCrossingResolvedCircleEquiv (Fin.last n) b s
        (.inl ⟦crossingSlotEquiv n (i₀, k₀)⟧) =
        D'.resolveCrossingResolvedCircleEquiv (Fin.last n) b s
          (.inr ((Fin.natAdd D'.crossinglessComponentCount ⟨0, by omega⟩).cast
            (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) b).symm)) := by
      rw [h0_eq, h2_eq, heq]
    exact Sum.inl_ne_inr ((D'.resolveCrossingResolvedCircleEquiv (Fin.last n) b s).injective hcongr)
  have hsub : {⟦D'.crossing (Fin.last n) 0⟧, ⟦D'.crossing (Fin.last n) 2⟧} ⊆
      D'.circlesAt ((Fin.last n).insertNth b s) (Fin.last n) := by
    intro C hC
    simp only [mem_insert, mem_singleton] at hC
    rcases hC with rfl | rfl <;> exact D'.mk_crossing_mem_circlesAt _ _ _
  have hge : 2 ≤ #(D'.circlesAt ((Fin.last n).insertNth b s) (Fin.last n)) := by
    calc
      2 = #({⟦D'.crossing (Fin.last n) 0⟧, ⟦D'.crossing (Fin.last n) 2⟧} :
            Finset (D'.CrossingCircle ((Fin.last n).insertNth b s))) :=
        (card_pair hne02).symm
      _ ≤ #(D'.circlesAt ((Fin.last n).insertNth b s) (Fin.last n)) := card_le_card hsub
  exact le_antisymm (D'.card_circlesAt_le_two _ _) hge

/-- The saddle correspondence from the `b`-smoothing to the `!b`-smoothing of
`D.reidemeisterOne h b` matches `D.adjoinCircleCollapse (Mark.onArc D h)`. -/
private theorem saddleResolvedCircleMap_reidemeisterOne (b : Bool) (s : Fin n → Bool)
    (hnot : #((D.reidemeisterOne h b).circlesAt ((Fin.last n).insertNth (!b) s) (Fin.last n)) = 1)
    (C : D.adjoinCircle.ResolvedCircle s) :
    (D.reidemeisterOne h b).saddleResolvedCircleMap
        (fun _ hi ↦ insertNth_eq_of_ne (Fin.last n) b (!b) s hi) hnot
        ((D.reidemeisterOne h b).resolveCrossingResolvedCircleEquiv (Fin.last n) b s
          (((ResolutionEquiv.resolveCrossingReidemeisterOneSelf D h b).smoothingEquiv
            (s := s) (t := s) (fun _ ↦ by simp)).resolvedCircleCongr C)) =
      (D.reidemeisterOne h b).resolveCrossingResolvedCircleEquiv (Fin.last n) (!b) s
        (((ResolutionEquiv.resolveCrossingReidemeisterOneNot D h b).smoothingEquiv
          (s := s) (t := s) (fun _ ↦ by simp)).resolvedCircleCongr
            (D.adjoinCircleCollapse (Mark.onArc D h) s C)) := by
  set D' := D.reidemeisterOne h b
  set Eself := ResolutionEquiv.resolveCrossingReidemeisterOneSelf D h b
  set Enot := ResolutionEquiv.resolveCrossingReidemeisterOneNot D h b
  rcases D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl s C with rfl | ⟨C | i, rfl⟩
  · rw [D.adjoinCircleCollapse_adjoinCircleNew, Mark.resolvedCircle_onArc, D.adjoinCircleNew_eq]
    have hdet : D'.detachedCircleCount (Fin.last n) b = 1 := by
      simp [D', detachedCircleCount_reidemeisterOne_last]
    have hself_new : Eself.crossinglessEquiv
        (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm
          (Fin.last D.crossinglessComponentCount)) =
        (Fin.natAdd D'.crossinglessComponentCount ⟨0, by omega⟩).cast
          (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) b).symm := by
      ext
      simp [Eself, D']
    obtain ⟨⟨i₀, k₀⟩, hik₀⟩ := (crossingSlotEquiv n).surjective (D.halfEdge.symm h)
    have hh : D.crossing i₀ k₀ = h := by
      rw [crossing_apply, hik₀, Equiv.apply_symm_apply]
    have hne0 : (D.reidemeisterOne h b).edgePair.val
          ((D.reidemeisterOne h b).crossing (Fin.last n) 0) ≠
        (D.reidemeisterOne h b).crossing (Fin.last n)
          (slotSmoothing (bif b then (D.reidemeisterOne h b).overPair (Fin.last n)
            else !(D.reidemeisterOne h b).overPair (Fin.last n)) 0) := by
      simp
    have h20 :
        (⟦(D.reidemeisterOne h b).crossing (Fin.last n) 2⟧ :
          (D.reidemeisterOne h b).CrossingCircle ((Fin.last n).insertNth (!b) s)) =
            ⟦(D.reidemeisterOne h b).crossing (Fin.last n) 0⟧ := by
      obtain ⟨C₀, hC₀⟩ := Finset.card_eq_one.1 hnot
      have h2mem : (⟦(D.reidemeisterOne h b).crossing (Fin.last n) 2⟧ :
          (D.reidemeisterOne h b).CrossingCircle ((Fin.last n).insertNth (!b) s)) ∈ {C₀} :=
        hC₀ ▸ (D.reidemeisterOne h b).mk_crossing_mem_circlesAt _ _ 2
      have h0mem : (⟦(D.reidemeisterOne h b).crossing (Fin.last n) 0⟧ :
          (D.reidemeisterOne h b).CrossingCircle ((Fin.last n).insertNth (!b) s)) ∈ {C₀} :=
        hC₀ ▸ (D.reidemeisterOne h b).mk_crossing_mem_circlesAt _ _ 0
      exact (Finset.mem_singleton.1 h2mem).trans (Finset.mem_singleton.1 h0mem).symm
    rw [SmoothingEquiv.resolvedCircleCongr_inr, SmoothingEquiv.resolvedCircleCongr_inl,
      SmoothingEquiv.crossingCircleCongr_mk,
      ResolutionEquiv.smoothingEquiv_crossinglessEquiv,
      ResolutionEquiv.smoothingEquiv_halfEdgeEquiv,
      show (ResolutionEquiv.resolveCrossingReidemeisterOneSelf D h b) = Eself from rfl,
      ResolutionEquiv.resolveCrossingReidemeisterOneNot_halfEdgeEquiv,
      hself_new, resolveCrossingResolvedCircleEquiv_inr_natAdd,
      saddleResolvedCircleMap_inl, saddleCircleMap_mk, ite_eq_right (fun h ↦ hne0 h.2),
      ← hik₀, resolveCrossingResolvedCircleEquiv_inl_mk]
    congr 1
    rw [h20, ← CrossingCircle.mk_edgePair, Fin.succAbove_last, crossing_apply, crossing_apply,
      crossingSlotEquiv_succ_last, crossingSlotEquiv_succ_castSucc, reidemeisterOne_crossing_last,
      reidemeisterOne_crossing_castSucc, reidemeisterOne_edgePair_inr_zero, hh]
  · obtain ⟨x, rfl⟩ := Quotient.exists_rep C
    obtain ⟨⟨i, k⟩, hik⟩ := (crossingSlotEquiv n).surjective (D.halfEdge.symm x)
    rw [D.adjoinCircleCollapse_adjoinCircleIncl, D.adjoinCircleIncl_inl,
      D.adjoinCircleCrossingCircleEquiv_mk]
    simp only [SmoothingEquiv.resolvedCircleCongr_inl, SmoothingEquiv.crossingCircleCongr_mk,
      ResolutionEquiv.smoothingEquiv_halfEdgeEquiv,
      ResolutionEquiv.resolveCrossingReidemeisterOneSelf_halfEdgeEquiv,
      ResolutionEquiv.resolveCrossingReidemeisterOneNot_halfEdgeEquiv, ← hik,
      resolveCrossingResolvedCircleEquiv_inl_mk, saddleResolvedCircleMap_inl, saddleCircleMap_mk]
  · rw [D.adjoinCircleCollapse_adjoinCircleIncl, D.adjoinCircleIncl_inr]
    have hself_i : Eself.crossinglessEquiv
        (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm i.castSucc) =
        (Fin.castAdd (D'.detachedCircleCount (Fin.last n) b)
          (i.cast (reidemeisterOne_crossinglessComponentCount D h b).symm)).cast
          (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) b).symm := by
      ext
      simp [Eself]
    have hnot_i : Enot.crossinglessEquiv i =
        (Fin.castAdd (D'.detachedCircleCount (Fin.last n) (!b))
          (i.cast (reidemeisterOne_crossinglessComponentCount D h b).symm)).cast
          (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) (!b)).symm := by
      ext
      simp [Enot]
    rw [SmoothingEquiv.resolvedCircleCongr_inr, SmoothingEquiv.resolvedCircleCongr_inr,
      ResolutionEquiv.smoothingEquiv_crossinglessEquiv,
      ResolutionEquiv.smoothingEquiv_crossinglessEquiv,
      show (ResolutionEquiv.resolveCrossingReidemeisterOneSelf D h b) = Eself from rfl,
      show (ResolutionEquiv.resolveCrossingReidemeisterOneNot D h b) = Enot from rfl,
      hself_i, hnot_i, resolveCrossingResolvedCircleEquiv_inr_castAdd,
      resolveCrossingResolvedCircleEquiv_inr_castAdd, saddleResolvedCircleMap_inr]

/-- **First Reidemeister cancellation on the unnormalized bracket (positive kink).**
`⟦D.reidemeisterOne h true⟧ʲ ≅ mappingCone (𝟙 (⟦D⟧ʲ⁻¹⟦-1⟧)) ⊞ ⟦D⟧ʲ⁺¹`. -/
def reidemeisterOneKhovanovBracketTrueIso (hD : D.IsPlanar)
    (hD' : (D.reidemeisterOne h true).IsPlanar) (R : Type u) [CommRing R] (j : ℤ) :
    (D.reidemeisterOne h true).khovanovBracket hD' R j ≅
      mappingCone (𝟙 ((D.khovanovBracket hD R (j - 1))⟦(-1 : ℤ)⟧)) ⊞
        D.khovanovBracket hD R (j + 1) :=
  khovanovBracketMergeCancelIso (Fin.last n) (Mark.onArc D h) hD
    ((isPlanar_adjoinCircle_iff D).2 hD) hD'
    (ResolutionEquiv.resolveCrossingReidemeisterOneSelf D h true) (by simp)
    (ResolutionEquiv.resolveCrossingReidemeisterOneNot D h true) (by simp)
    (D.card_circlesAt_reidemeisterOne_self h true)
    (fun s hB C ↦ D.saddleResolvedCircleMap_reidemeisterOne h true s hB C) R j

/-- **First Reidemeister cancellation on the unnormalized bracket (negative kink).**
`⟦D.reidemeisterOne h false⟧ʲ ≅ mappingCone (𝟙 (⟦D⟧ʲ⟦-1⟧)) ⊞ ⟦D⟧ʲ⁻²⟦-1⟧`. -/
def reidemeisterOneKhovanovBracketFalseIso (hD : D.IsPlanar)
    (hD' : (D.reidemeisterOne h false).IsPlanar) (R : Type u) [CommRing R] (j : ℤ) :
    (D.reidemeisterOne h false).khovanovBracket hD' R j ≅
      mappingCone (𝟙 ((D.khovanovBracket hD R j)⟦(-1 : ℤ)⟧)) ⊞
        (D.khovanovBracket hD R (j - 2))⟦(-1 : ℤ)⟧ :=
  khovanovBracketSplitCancelIso (Fin.last n) (Mark.onArc D h) hD
    ((isPlanar_adjoinCircle_iff D).2 hD) hD'
    (ResolutionEquiv.resolveCrossingReidemeisterOneNot D h false) (by simp)
    (ResolutionEquiv.resolveCrossingReidemeisterOneSelf D h false) (by simp)
    (D.card_circlesAt_reidemeisterOne_self h false)
    (fun s hA C ↦ D.saddleResolvedCircleMap_reidemeisterOne h false s hA C) R j

/-- Strong deformation retraction of `⟦D.reidemeisterOne h true⟧ʲ` onto `⟦D⟧ʲ⁺¹`. -/
def reidemeisterOneKhovanovBracketTrueContraction (hD : D.IsPlanar)
    (hD' : (D.reidemeisterOne h true).IsPlanar) (R : Type u) [CommRing R] (j : ℤ) :
    SpecialContraction ((D.reidemeisterOne h true).khovanovBracket hD' R j)
      (D.khovanovBracket hD R (j + 1)) :=
  (SpecialContraction.biprodMappingConeIdLeft _ _).ofIso
    (D.reidemeisterOneKhovanovBracketTrueIso h hD hD' R j) (Iso.refl _)

/-- Strong deformation retraction of `⟦D.reidemeisterOne h false⟧ʲ` onto `⟦D⟧ʲ⁻²⟦-1⟧`. -/
def reidemeisterOneKhovanovBracketFalseContraction (hD : D.IsPlanar)
    (hD' : (D.reidemeisterOne h false).IsPlanar) (R : Type u) [CommRing R] (j : ℤ) :
    SpecialContraction ((D.reidemeisterOne h false).khovanovBracket hD' R j)
      ((D.khovanovBracket hD R (j - 2))⟦(-1 : ℤ)⟧) :=
  (SpecialContraction.biprodMappingConeIdLeft _ _).ofIso
    (D.reidemeisterOneKhovanovBracketFalseIso h hD hD' R j) (Iso.refl _)

end ReidemeisterOneBracket

/-! ### Unnormalized Khovanov bracket under `PDCode.adjoinKink` -/

section AdjoinKinkBracket

variable {n : ℕ} (D : PDCode n)

/-- The mark placed on the newly adjoined circle of `D.adjoinCircle`. -/
private def adjoinCircleLastMark : D.adjoinCircle.Mark :=
  Mark.onCircle D.adjoinCircle
    ((Fin.last D.crossinglessComponentCount).cast (adjoinCircle_crossinglessComponentCount D).symm)

/-- In the `b`-smoothing of `D.adjoinKink b`, the isolated kink splits into two detached circles,
so its crossing meets two distinct circles. -/
private theorem card_circlesAt_adjoinKink_self (b : Bool) (s : Fin n → Bool) :
    #((D.adjoinKink b).circlesAt ((Fin.last n).insertNth b s) (Fin.last n)) = 2 := by
  set D' := D.adjoinKink b
  have hdet : D'.detachedCircleCount (Fin.last n) b = 2 := by
    simp [D', detachedCircleCount_adjoinKink_last]
  have heq0 : D'.edgePair.val (D'.crossing (Fin.last n) 0) =
      D'.crossing (Fin.last n)
        (slotSmoothing (bif b then D'.overPair (Fin.last n) else !D'.overPair (Fin.last n)) 0) := by
    cases b <;> simp [D']
  have h0_eq : D'.resolveCrossingResolvedCircleEquiv (Fin.last n) b s
      (.inr ((Fin.natAdd D'.crossinglessComponentCount ⟨0, by omega⟩).cast
        (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) b).symm)) =
      .inl ⟦D'.crossing (Fin.last n) 0⟧ := by
    rw [resolveCrossingResolvedCircleEquiv_inr_natAdd, ite_eq_left ⟨rfl, heq0⟩]
  have h2_eq : D'.resolveCrossingResolvedCircleEquiv (Fin.last n) b s
      (.inr ((Fin.natAdd D'.crossinglessComponentCount ⟨1, by omega⟩).cast
        (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) b).symm)) =
      .inl ⟦D'.crossing (Fin.last n) 2⟧ := by
    rw [resolveCrossingResolvedCircleEquiv_inr_natAdd]
    simp
  have hne02 : (⟦D'.crossing (Fin.last n) 0⟧ : D'.CrossingCircle ((Fin.last n).insertNth b s)) ≠
      ⟦D'.crossing (Fin.last n) 2⟧ := by
    intro heq
    have hcongr : D'.resolveCrossingResolvedCircleEquiv (Fin.last n) b s
        (.inr ((Fin.natAdd D'.crossinglessComponentCount ⟨0, by omega⟩).cast
          (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) b).symm)) =
        D'.resolveCrossingResolvedCircleEquiv (Fin.last n) b s
          (.inr ((Fin.natAdd D'.crossinglessComponentCount ⟨1, by omega⟩).cast
            (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) b).symm)) := by
      rw [h0_eq, h2_eq, heq]
    have hinj := (D'.resolveCrossingResolvedCircleEquiv (Fin.last n) b s).injective hcongr
    have hval := congrArg Fin.val (Sum.inr.inj hinj)
    simp at hval
  have hsub : {⟦D'.crossing (Fin.last n) 0⟧, ⟦D'.crossing (Fin.last n) 2⟧} ⊆
      D'.circlesAt ((Fin.last n).insertNth b s) (Fin.last n) := by
    intro C hC
    simp only [mem_insert, mem_singleton] at hC
    rcases hC with rfl | rfl <;> exact D'.mk_crossing_mem_circlesAt _ _ _
  have hge : 2 ≤ #(D'.circlesAt ((Fin.last n).insertNth b s) (Fin.last n)) := by
    calc
      2 = #({⟦D'.crossing (Fin.last n) 0⟧, ⟦D'.crossing (Fin.last n) 2⟧} :
            Finset (D'.CrossingCircle ((Fin.last n).insertNth b s))) :=
        (card_pair hne02).symm
      _ ≤ #(D'.circlesAt ((Fin.last n).insertNth b s) (Fin.last n)) := card_le_card hsub
  exact le_antisymm (D'.card_circlesAt_le_two _ _) hge

/-- The saddle correspondence from the `b`-smoothing to the `!b`-smoothing of `D.adjoinKink b`
matches `D.adjoinCircle.adjoinCircleCollapse D.adjoinCircleLastMark`. -/
private theorem saddleResolvedCircleMap_adjoinKink (b : Bool) (s : Fin n → Bool)
    (hnot : #((D.adjoinKink b).circlesAt ((Fin.last n).insertNth (!b) s) (Fin.last n)) = 1)
    (C : D.adjoinCircle.adjoinCircle.ResolvedCircle s) :
    (D.adjoinKink b).saddleResolvedCircleMap
        (fun _ hi ↦ insertNth_eq_of_ne (Fin.last n) b (!b) s hi) hnot
        ((D.adjoinKink b).resolveCrossingResolvedCircleEquiv (Fin.last n) b s
          (((ResolutionEquiv.resolveCrossingAdjoinKinkSelf D b).smoothingEquiv
            (s := s) (t := s) (fun _ ↦ by simp)).resolvedCircleCongr C)) =
      (D.adjoinKink b).resolveCrossingResolvedCircleEquiv (Fin.last n) (!b) s
        (((ResolutionEquiv.resolveCrossingAdjoinKinkNot D b).smoothingEquiv
          (s := s) (t := s) (fun _ ↦ by simp)).resolvedCircleCongr
            (D.adjoinCircle.adjoinCircleCollapse D.adjoinCircleLastMark s C)) := by
  set D' := D.adjoinKink b
  set Eself := ResolutionEquiv.resolveCrossingAdjoinKinkSelf D b
  set Enot := ResolutionEquiv.resolveCrossingAdjoinKinkNot D b
  have hdetSelf : D'.detachedCircleCount (Fin.last n) b = 2 := by
    simp [D', detachedCircleCount_adjoinKink_last]
  have hdetNot : D'.detachedCircleCount (Fin.last n) (!b) = 1 := by
    simp [D', detachedCircleCount_adjoinKink_last]
  have heqSelf : (D.adjoinKink b).edgePair.val ((D.adjoinKink b).crossing (Fin.last n) 0) =
      (D.adjoinKink b).crossing (Fin.last n)
        (slotSmoothing (bif b then (D.adjoinKink b).overPair (Fin.last n)
          else !(D.adjoinKink b).overPair (Fin.last n)) 0) := by
    cases b <;> simp
  have hneNot : (D.adjoinKink b).edgePair.val ((D.adjoinKink b).crossing (Fin.last n) 0) ≠
      (D.adjoinKink b).crossing (Fin.last n)
        (slotSmoothing (bif !b then (D.adjoinKink b).overPair (Fin.last n)
          else !(D.adjoinKink b).overPair (Fin.last n)) 0) := by
    cases b <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have h02 : (⟦(D.adjoinKink b).crossing (Fin.last n) 0⟧ :
      (D.adjoinKink b).CrossingCircle ((Fin.last n).insertNth (!b) s)) =
      ⟦(D.adjoinKink b).crossing (Fin.last n) 2⟧ := by
    obtain ⟨C₀, hC₀⟩ := Finset.card_eq_one.1 hnot
    have h0mem : (⟦(D.adjoinKink b).crossing (Fin.last n) 0⟧ :
        (D.adjoinKink b).CrossingCircle ((Fin.last n).insertNth (!b) s)) ∈ {C₀} :=
      hC₀ ▸ (D.adjoinKink b).mk_crossing_mem_circlesAt _ _ 0
    have h2mem : (⟦(D.adjoinKink b).crossing (Fin.last n) 2⟧ :
        (D.adjoinKink b).CrossingCircle ((Fin.last n).insertNth (!b) s)) ∈ {C₀} :=
      hC₀ ▸ (D.adjoinKink b).mk_crossing_mem_circlesAt _ _ 2
    exact (Finset.mem_singleton.1 h0mem).trans (Finset.mem_singleton.1 h2mem).symm
  rcases D.adjoinCircle.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl s C with
    rfl | ⟨C, rfl⟩
  · rw [D.adjoinCircle.adjoinCircleCollapse_adjoinCircleNew, adjoinCircleLastMark,
      Mark.resolvedCircle_onCircle, D.adjoinCircle.adjoinCircleNew_eq]
    have hself_new : Eself.crossinglessEquiv
        ((Fin.last D.adjoinCircle.crossinglessComponentCount).cast
          (adjoinCircle_crossinglessComponentCount D.adjoinCircle).symm) =
        (Fin.natAdd D'.crossinglessComponentCount ⟨1, by omega⟩).cast
          (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) b).symm := by
      ext
      simp [Eself, D']
    have hnot_last : Enot.crossinglessEquiv
        ((Fin.last D.crossinglessComponentCount).cast
          (adjoinCircle_crossinglessComponentCount D).symm) =
        (Fin.natAdd D'.crossinglessComponentCount ⟨0, by omega⟩).cast
          (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) (!b)).symm := by
      ext
      simp [Enot, D']
    rw [SmoothingEquiv.resolvedCircleCongr_inr, SmoothingEquiv.resolvedCircleCongr_inr,
      ResolutionEquiv.smoothingEquiv_crossinglessEquiv,
      ResolutionEquiv.smoothingEquiv_crossinglessEquiv,
      show (ResolutionEquiv.resolveCrossingAdjoinKinkSelf D b) = Eself from rfl,
      show (ResolutionEquiv.resolveCrossingAdjoinKinkNot D b) = Enot from rfl,
      hself_new, hnot_last, resolveCrossingResolvedCircleEquiv_inr_natAdd,
      resolveCrossingResolvedCircleEquiv_inr_natAdd,
      saddleResolvedCircleMap_inl, saddleCircleMap_mk,
      ite_eq_right (fun h ↦ by simp at h), ite_eq_right (fun h ↦ hneNot h.2)]
  · rw [D.adjoinCircle.adjoinCircleCollapse_adjoinCircleIncl]
    rcases D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl s C with rfl | ⟨C | i, rfl⟩
    · rw [D.adjoinCircleNew_eq, D.adjoinCircle.adjoinCircleIncl_inr]
      have hself_i : Eself.crossinglessEquiv
          (Fin.cast (adjoinCircle_crossinglessComponentCount D.adjoinCircle).symm
            (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm
              (Fin.last D.crossinglessComponentCount)).castSucc) =
          (Fin.natAdd D'.crossinglessComponentCount ⟨0, by omega⟩).cast
            (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) b).symm := by
        ext
        simp [Eself, D']
      have hnot_i : Enot.crossinglessEquiv
          (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm
            (Fin.last D.crossinglessComponentCount)) =
          (Fin.natAdd D'.crossinglessComponentCount ⟨0, by omega⟩).cast
            (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) (!b)).symm := by
        ext
        simp [Enot, D']
      rw [SmoothingEquiv.resolvedCircleCongr_inr, SmoothingEquiv.resolvedCircleCongr_inr,
        ResolutionEquiv.smoothingEquiv_crossinglessEquiv,
        ResolutionEquiv.smoothingEquiv_crossinglessEquiv,
        show (ResolutionEquiv.resolveCrossingAdjoinKinkSelf D b) = Eself from rfl,
        show (ResolutionEquiv.resolveCrossingAdjoinKinkNot D b) = Enot from rfl,
        hself_i, hnot_i, resolveCrossingResolvedCircleEquiv_inr_natAdd,
        resolveCrossingResolvedCircleEquiv_inr_natAdd,
        saddleResolvedCircleMap_inl, saddleCircleMap_mk,
        ite_eq_left ⟨rfl, heqSelf⟩, ite_eq_right (fun h ↦ hneNot h.2), h02]
    · obtain ⟨x, rfl⟩ := Quotient.exists_rep C
      obtain ⟨⟨i, k⟩, hik⟩ := (crossingSlotEquiv n).surjective (D.halfEdge.symm x)
      simp only [adjoinCircleIncl_inl, adjoinCircleCrossingCircleEquiv_mk,
        SmoothingEquiv.resolvedCircleCongr_inl, SmoothingEquiv.crossingCircleCongr_mk,
        ResolutionEquiv.smoothingEquiv_halfEdgeEquiv,
        ResolutionEquiv.resolveCrossingAdjoinKinkSelf_halfEdgeEquiv,
        ResolutionEquiv.resolveCrossingAdjoinKinkNot_halfEdgeEquiv, ← hik,
        resolveCrossingResolvedCircleEquiv_inl_mk, saddleResolvedCircleMap_inl, saddleCircleMap_mk]
    · rw [D.adjoinCircleIncl_inr, D.adjoinCircle.adjoinCircleIncl_inr]
      have hself_i : Eself.crossinglessEquiv
          (Fin.cast (adjoinCircle_crossinglessComponentCount D.adjoinCircle).symm
            (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm i.castSucc).castSucc) =
          (Fin.castAdd (D'.detachedCircleCount (Fin.last n) b)
            (i.cast (adjoinKink_crossinglessComponentCount D b).symm)).cast
            (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) b).symm := by
        ext
        simp [Eself]
      have hnot_i : Enot.crossinglessEquiv
          (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm i.castSucc) =
          (Fin.castAdd (D'.detachedCircleCount (Fin.last n) (!b))
            (i.cast (adjoinKink_crossinglessComponentCount D b).symm)).cast
            (D'.resolveCrossing_crossinglessComponentCount (Fin.last n) (!b)).symm := by
        ext
        simp [Enot]
      rw [SmoothingEquiv.resolvedCircleCongr_inr, SmoothingEquiv.resolvedCircleCongr_inr,
        ResolutionEquiv.smoothingEquiv_crossinglessEquiv,
        ResolutionEquiv.smoothingEquiv_crossinglessEquiv,
        show (ResolutionEquiv.resolveCrossingAdjoinKinkSelf D b) = Eself from rfl,
        show (ResolutionEquiv.resolveCrossingAdjoinKinkNot D b) = Enot from rfl,
        hself_i, hnot_i, resolveCrossingResolvedCircleEquiv_inr_castAdd,
        resolveCrossingResolvedCircleEquiv_inr_castAdd, saddleResolvedCircleMap_inr]

/-- **Isolated-kink cancellation on the unnormalized bracket (positive kink).**
`⟦D.adjoinKink true⟧ʲ ≅ mappingCone (𝟙 (⟦D.adjoinCircle⟧ʲ⁻¹⟦-1⟧)) ⊞ ⟦D.adjoinCircle⟧ʲ⁺¹`. -/
def adjoinKinkKhovanovBracketTrueIso (hD₀ : D.adjoinCircle.IsPlanar)
    (hD' : (D.adjoinKink true).IsPlanar) (R : Type u) [CommRing R] (j : ℤ) :
    (D.adjoinKink true).khovanovBracket hD' R j ≅
      mappingCone (𝟙 ((D.adjoinCircle.khovanovBracket hD₀ R (j - 1))⟦(-1 : ℤ)⟧)) ⊞
        D.adjoinCircle.khovanovBracket hD₀ R (j + 1) :=
  khovanovBracketMergeCancelIso (Fin.last n) D.adjoinCircleLastMark hD₀
    ((isPlanar_adjoinCircle_iff D.adjoinCircle).2 hD₀) hD'
    (ResolutionEquiv.resolveCrossingAdjoinKinkSelf D true) (by simp)
    (ResolutionEquiv.resolveCrossingAdjoinKinkNot D true) (by simp)
    (D.card_circlesAt_adjoinKink_self true)
    (fun s hB C ↦ D.saddleResolvedCircleMap_adjoinKink true s hB C) R j

/-- **Isolated-kink cancellation on the unnormalized bracket (negative kink).**
`⟦D.adjoinKink false⟧ʲ ≅ mappingCone (𝟙 (⟦D.adjoinCircle⟧ʲ⟦-1⟧)) ⊞ ⟦D.adjoinCircle⟧ʲ⁻²⟦-1⟧`. -/
def adjoinKinkKhovanovBracketFalseIso (hD₀ : D.adjoinCircle.IsPlanar)
    (hD' : (D.adjoinKink false).IsPlanar) (R : Type u) [CommRing R] (j : ℤ) :
    (D.adjoinKink false).khovanovBracket hD' R j ≅
      mappingCone (𝟙 ((D.adjoinCircle.khovanovBracket hD₀ R j)⟦(-1 : ℤ)⟧)) ⊞
        (D.adjoinCircle.khovanovBracket hD₀ R (j - 2))⟦(-1 : ℤ)⟧ :=
  khovanovBracketSplitCancelIso (Fin.last n) D.adjoinCircleLastMark hD₀
    ((isPlanar_adjoinCircle_iff D.adjoinCircle).2 hD₀) hD'
    (ResolutionEquiv.resolveCrossingAdjoinKinkNot D false) (by simp)
    (ResolutionEquiv.resolveCrossingAdjoinKinkSelf D false) (by simp)
    (D.card_circlesAt_adjoinKink_self false)
    (fun s hA C ↦ D.saddleResolvedCircleMap_adjoinKink false s hA C) R j

/-- Strong deformation retraction of `⟦D.adjoinKink true⟧ʲ` onto `⟦D.adjoinCircle⟧ʲ⁺¹`. -/
def adjoinKinkKhovanovBracketTrueContraction (hD₀ : D.adjoinCircle.IsPlanar)
    (hD' : (D.adjoinKink true).IsPlanar) (R : Type u) [CommRing R] (j : ℤ) :
    SpecialContraction ((D.adjoinKink true).khovanovBracket hD' R j)
      (D.adjoinCircle.khovanovBracket hD₀ R (j + 1)) :=
  (SpecialContraction.biprodMappingConeIdLeft _ _).ofIso
    (D.adjoinKinkKhovanovBracketTrueIso hD₀ hD' R j) (Iso.refl _)

/-- Strong deformation retraction of `⟦D.adjoinKink false⟧ʲ` onto `⟦D.adjoinCircle⟧ʲ⁻²⟦-1⟧`. -/
def adjoinKinkKhovanovBracketFalseContraction (hD₀ : D.adjoinCircle.IsPlanar)
    (hD' : (D.adjoinKink false).IsPlanar) (R : Type u) [CommRing R] (j : ℤ) :
    SpecialContraction ((D.adjoinKink false).khovanovBracket hD' R j)
      ((D.adjoinCircle.khovanovBracket hD₀ R (j - 2))⟦(-1 : ℤ)⟧) :=
  (SpecialContraction.biprodMappingConeIdLeft _ _).ofIso
    (D.adjoinKinkKhovanovBracketFalseIso hD₀ hD' R j) (Iso.refl _)

end AdjoinKinkBracket

end TauCeti.PDCode

/-! ### Normalized Khovanov complex and homology under the first Reidemeister moves -/

namespace TauCeti.OrientedPDCode

section NormalizationHelpers

/-- Transport the unnormalized Khovanov bracket along an equality of PD-codes. -/
private def khovanovBracketEqIso {n : ℕ} {P₁ P₂ : PDCode n} (h : P₁ = P₂)
    (hP₁ : P₁.IsPlanar) (hP₂ : P₂.IsPlanar) (R : Type u) [CommRing R] (k : ℤ) :
    P₁.khovanovBracket hP₁ R k ≅ P₂.khovanovBracket hP₂ R k := by
  subst h
  exact Iso.refl _

/-- Lift a positive-kink bracket cancellation isomorphism to the normalized Khovanov complex. -/
private def khovanovComplexTrueIsoOfBracketIso {n m : ℕ}
    {D₁ : OrientedPDCode n} {D₂ : OrientedPDCode m}
    {P₁ : PDCode n} {P₂ : PDCode m} (hP₁ : D₁.toPDCode = P₁) (hP₂ : D₂.toPDCode = P₂)
    (hD₁ : D₁.toPDCode.IsPlanar) (hD₂ : D₂.toPDCode.IsPlanar) (R : Type u) [CommRing R]
    (hpos : D₂.positiveCrossingCount = D₁.positiveCrossingCount + 1)
    (hneg : D₂.negativeCrossingCount = D₁.negativeCrossingCount)
    (e : ∀ k : ℤ, P₂.khovanovBracket (hP₂ ▸ hD₂) R k ≅
      mappingCone (𝟙 ((P₁.khovanovBracket (hP₁ ▸ hD₁) R (k - 1))⟦(-1 : ℤ)⟧)) ⊞
        P₁.khovanovBracket (hP₁ ▸ hD₁) R (k + 1))
    (j : ℤ) :
    D₂.khovanovComplex hD₂ R j ≅
      mappingCone (𝟙 ((D₁.khovanovComplex hD₁ R (j - 2))⟦(-1 : ℤ)⟧)) ⊞
        D₁.khovanovComplex hD₁ R j :=
  let a : ℤ := D₁.negativeCrossingCount
  let k : ℤ := j - D₂.positiveCrossingCount + 2 * D₂.negativeCrossingCount
  let S := CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) a
  letI := preservesBinaryBiproducts_of_preservesBiproducts S
  let shiftComm : ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
      (K⟦(-1 : ℤ)⟧)⟦a⟧ ≅ (K⟦a⟧)⟦(-1 : ℤ)⟧ := fun K ↦
    ((CategoryTheory.shiftFunctorAdd' _ (-1 : ℤ) a (a + (-1)) (by omega)).symm.app K) ≪≫
      (CategoryTheory.shiftFunctorAdd' _ a (-1 : ℤ) (a + (-1)) rfl).app K
  let eK := shiftComm _ ≪≫
    (CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso
      (S.mapIso (khovanovBracketEqIso hP₁.symm (hP₁ ▸ hD₁) hD₁ R (k - 1)) ≪≫
        eqToIso (by congr 2; omega) ≪≫ (D₁.khovanovComplexShiftIso hD₁ R (j - 2)).symm)
  D₂.khovanovComplexShiftIso hD₂ R j ≪≫
    eqToIso (by dsimp only [a, k]; rw [hneg]) ≪≫
    S.mapIso (khovanovBracketEqIso hP₂ hD₂ (hP₂ ▸ hD₂) R k ≪≫ e k) ≪≫
    S.mapBiprod _ _ ≪≫
    biprod.mapIso
      (shiftMappingConeIdIso _ a ≪≫ mappingCone.mapIso eK eK (by simp))
      (S.mapIso (khovanovBracketEqIso hP₁.symm (hP₁ ▸ hD₁) hD₁ R (k + 1)) ≪≫
        eqToIso (by congr 2; omega) ≪≫ (D₁.khovanovComplexShiftIso hD₁ R j).symm)

/-- Lift a negative-kink bracket cancellation isomorphism to the normalized Khovanov complex. -/
private def khovanovComplexFalseIsoOfBracketIso {n m : ℕ}
    {D₁ : OrientedPDCode n} {D₂ : OrientedPDCode m}
    {P₁ : PDCode n} {P₂ : PDCode m} (hP₁ : D₁.toPDCode = P₁) (hP₂ : D₂.toPDCode = P₂)
    (hD₁ : D₁.toPDCode.IsPlanar) (hD₂ : D₂.toPDCode.IsPlanar) (R : Type u) [CommRing R]
    (hpos : D₂.positiveCrossingCount = D₁.positiveCrossingCount)
    (hneg : D₂.negativeCrossingCount = D₁.negativeCrossingCount + 1)
    (e : ∀ k : ℤ, P₂.khovanovBracket (hP₂ ▸ hD₂) R k ≅
      mappingCone (𝟙 ((P₁.khovanovBracket (hP₁ ▸ hD₁) R k)⟦(-1 : ℤ)⟧)) ⊞
        (P₁.khovanovBracket (hP₁ ▸ hD₁) R (k - 2))⟦(-1 : ℤ)⟧)
    (j : ℤ) :
    D₂.khovanovComplex hD₂ R j ≅
      mappingCone (𝟙 (D₁.khovanovComplex hD₁ R (j + 2))) ⊞ D₁.khovanovComplex hD₁ R j :=
  let a : ℤ := D₁.negativeCrossingCount
  let k : ℤ := j - D₂.positiveCrossingCount + 2 * D₂.negativeCrossingCount
  let S := CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (a + 1)
  letI := preservesBinaryBiproducts_of_preservesBiproducts S
  let shiftCancel : ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
      (K⟦(-1 : ℤ)⟧)⟦a + 1⟧ ≅ K⟦a⟧ := fun K ↦
    (CategoryTheory.shiftFunctorAdd' _ (-1 : ℤ) (a + 1) a (by omega)).symm.app K
  let eK := shiftCancel _ ≪≫
    (CategoryTheory.shiftFunctor _ a).mapIso
      (khovanovBracketEqIso hP₁.symm (hP₁ ▸ hD₁) hD₁ R k) ≪≫
    eqToIso (by congr 2; omega) ≪≫ (D₁.khovanovComplexShiftIso hD₁ R (j + 2)).symm
  D₂.khovanovComplexShiftIso hD₂ R j ≪≫
    eqToIso (by dsimp only [a, k]; rw [hneg]; push_cast; rfl) ≪≫
    S.mapIso (khovanovBracketEqIso hP₂ hD₂ (hP₂ ▸ hD₂) R k ≪≫ e k) ≪≫
    S.mapBiprod _ _ ≪≫
    biprod.mapIso
      (shiftMappingConeIdIso _ (a + 1) ≪≫ mappingCone.mapIso eK eK (by simp))
      (shiftCancel _ ≪≫
        (CategoryTheory.shiftFunctor _ a).mapIso
          (khovanovBracketEqIso hP₁.symm (hP₁ ▸ hD₁) hD₁ R (k - 2)) ≪≫
        eqToIso (by congr 2; omega) ≪≫ (D₁.khovanovComplexShiftIso hD₁ R j).symm)

end NormalizationHelpers

/-! ### Kink inserted into an arc (`OrientedPDCode.reidemeisterOne`) -/

section ReidemeisterOne

variable {n : ℕ} (D : OrientedPDCode n) (h : Fin (4 * n))
  (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- **First Reidemeister direct-sum cancellation (positive kink on an arc).**
`C(D.reidemeisterOne h true)ʲ ≅ mappingCone (𝟙 (C(D)ʲ⁻²⟦-1⟧)) ⊞ C(D)ʲ`. -/
def reidemeisterOneKhovanovComplexTrueIso
    (hD' : (D.reidemeisterOne h true).toPDCode.IsPlanar) (j : ℤ) :
    (D.reidemeisterOne h true).khovanovComplex hD' R j ≅
      mappingCone (𝟙 ((D.khovanovComplex hD R (j - 2))⟦(-1 : ℤ)⟧)) ⊞
        D.khovanovComplex hD R j :=
  khovanovComplexTrueIsoOfBracketIso rfl (D.toPDCode_reidemeisterOne h true) hD hD' R
    (by simp) (by simp)
    (fun k ↦ D.toPDCode.reidemeisterOneKhovanovBracketTrueIso h hD _ R k) j

/-- **First Reidemeister direct-sum cancellation (negative kink on an arc).**
`C(D.reidemeisterOne h false)ʲ ≅ mappingCone (𝟙 (C(D)ʲ⁺²)) ⊞ C(D)ʲ`. -/
def reidemeisterOneKhovanovComplexFalseIso
    (hD' : (D.reidemeisterOne h false).toPDCode.IsPlanar) (j : ℤ) :
    (D.reidemeisterOne h false).khovanovComplex hD' R j ≅
      mappingCone (𝟙 (D.khovanovComplex hD R (j + 2))) ⊞ D.khovanovComplex hD R j :=
  khovanovComplexFalseIsoOfBracketIso rfl (D.toPDCode_reidemeisterOne h false) hD hD' R
    (by simp) (by simp)
    (fun k ↦ D.toPDCode.reidemeisterOneKhovanovBracketFalseIso h hD _ R k) j

/-- **First Reidemeister strong deformation retraction (kink on an arc).** For either crossing sign
`b`, the normalized Khovanov complex of `D.reidemeisterOne h b` admits a special contraction onto
that of `D` in every quantum degree `j`. -/
def reidemeisterOneKhovanovComplexContraction (b : Bool)
    (hD' : (D.reidemeisterOne h b).toPDCode.IsPlanar) (j : ℤ) :
    SpecialContraction ((D.reidemeisterOne h b).khovanovComplex hD' R j)
      (D.khovanovComplex hD R j) :=
  match b with
  | true =>
    (SpecialContraction.biprodMappingConeIdLeft _ _).ofIso
      (D.reidemeisterOneKhovanovComplexTrueIso h hD R hD' j) (Iso.refl _)
  | false =>
    (SpecialContraction.biprodMappingConeIdLeft _ _).ofIso
      (D.reidemeisterOneKhovanovComplexFalseIso h hD R hD' j) (Iso.refl _)

/-- **First Reidemeister homotopy equivalence (kink on an arc).** For either crossing sign `b`, the
normalized Khovanov complex of `D.reidemeisterOne h b` is chain homotopy equivalent to that of `D`
in every quantum degree `j`. -/
def reidemeisterOneKhovanovComplexHomotopyEquiv (b : Bool)
    (hD' : (D.reidemeisterOne h b).toPDCode.IsPlanar) (j : ℤ) :
    HomotopyEquiv ((D.reidemeisterOne h b).khovanovComplex hD' R j)
      (D.khovanovComplex hD R j) :=
  (D.reidemeisterOneKhovanovComplexContraction h hD R b hD' j).toContraction.homotopyEquiv.symm

/-- **First Reidemeister invariance of Khovanov homology (kink on an arc).** For every planar
oriented code `D`, half-edge `h`, crossing sign `b`, commutative ring `R`, and bidegree `(i, j)`,
`Khⁱʲ(D.reidemeisterOne h b; R) ≅ Khⁱʲ(D; R)`. -/
def reidemeisterOneKhovanovHomologyIso (b : Bool)
    (hD' : (D.reidemeisterOne h b).toPDCode.IsPlanar) (i j : ℤ) :
    (D.reidemeisterOne h b).khovanovHomology hD' R i j ≅ D.khovanovHomology hD R i j :=
  (D.reidemeisterOneKhovanovComplexHomotopyEquiv h hD R b hD' j).toHomologyIso i

end ReidemeisterOne

/-! ### Isolated kink on a crossing-free circle (`OrientedPDCode.adjoinKink`) -/

section AdjoinKink

variable {n : ℕ} (D : OrientedPDCode n) (o : Bool)
  (hD₀ : (D.adjoinCircle o).toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- **First Reidemeister direct-sum cancellation (positive isolated kink).**
`C(D.adjoinKink o true)ʲ ≅ mappingCone (𝟙 (C(D.adjoinCircle o)ʲ⁻²⟦-1⟧)) ⊞ C(D.adjoinCircle o)ʲ`. -/
def adjoinKinkKhovanovComplexTrueIso
    (hD' : (D.adjoinKink o true).toPDCode.IsPlanar) (j : ℤ) :
    (D.adjoinKink o true).khovanovComplex hD' R j ≅
      mappingCone (𝟙 (((D.adjoinCircle o).khovanovComplex hD₀ R (j - 2))⟦(-1 : ℤ)⟧)) ⊞
        (D.adjoinCircle o).khovanovComplex hD₀ R j :=
  khovanovComplexTrueIsoOfBracketIso (D.toPDCode_adjoinCircle o) (D.toPDCode_adjoinKink o true)
    hD₀ hD' R (by simp) (by simp)
    (fun k ↦ D.toPDCode.adjoinKinkKhovanovBracketTrueIso _ _ R k) j

/-- **First Reidemeister direct-sum cancellation (negative isolated kink).**
`C(D.adjoinKink o false)ʲ ≅ mappingCone (𝟙 (C(D.adjoinCircle o)ʲ⁺²)) ⊞ C(D.adjoinCircle o)ʲ`. -/
def adjoinKinkKhovanovComplexFalseIso
    (hD' : (D.adjoinKink o false).toPDCode.IsPlanar) (j : ℤ) :
    (D.adjoinKink o false).khovanovComplex hD' R j ≅
      mappingCone (𝟙 ((D.adjoinCircle o).khovanovComplex hD₀ R (j + 2))) ⊞
        (D.adjoinCircle o).khovanovComplex hD₀ R j :=
  khovanovComplexFalseIsoOfBracketIso (D.toPDCode_adjoinCircle o) (D.toPDCode_adjoinKink o false)
    hD₀ hD' R (by simp) (by simp)
    (fun k ↦ D.toPDCode.adjoinKinkKhovanovBracketFalseIso _ _ R k) j

/-- **First Reidemeister strong deformation retraction (isolated kink).** For either orientation
`o` and crossing sign `b`, the normalized Khovanov complex of `D.adjoinKink o b` admits a special
contraction onto that of `D.adjoinCircle o` in every quantum degree `j`. -/
def adjoinKinkKhovanovComplexContraction (b : Bool)
    (hD' : (D.adjoinKink o b).toPDCode.IsPlanar) (j : ℤ) :
    SpecialContraction ((D.adjoinKink o b).khovanovComplex hD' R j)
      ((D.adjoinCircle o).khovanovComplex hD₀ R j) :=
  match b with
  | true =>
    (SpecialContraction.biprodMappingConeIdLeft _ _).ofIso
      (D.adjoinKinkKhovanovComplexTrueIso o hD₀ R hD' j) (Iso.refl _)
  | false =>
    (SpecialContraction.biprodMappingConeIdLeft _ _).ofIso
      (D.adjoinKinkKhovanovComplexFalseIso o hD₀ R hD' j) (Iso.refl _)

/-- **First Reidemeister homotopy equivalence (isolated kink).** For either orientation `o` and
crossing sign `b`, the normalized Khovanov complex of `D.adjoinKink o b` is chain homotopy
equivalent to that of `D.adjoinCircle o` in every quantum degree `j`. -/
def adjoinKinkKhovanovComplexHomotopyEquiv (b : Bool)
    (hD' : (D.adjoinKink o b).toPDCode.IsPlanar) (j : ℤ) :
    HomotopyEquiv ((D.adjoinKink o b).khovanovComplex hD' R j)
      ((D.adjoinCircle o).khovanovComplex hD₀ R j) :=
  (D.adjoinKinkKhovanovComplexContraction o hD₀ R b hD' j).toContraction.homotopyEquiv.symm

/-- **First Reidemeister invariance of Khovanov homology (isolated kink).** For every planar
oriented code `D`, circle orientation `o`, crossing sign `b`, commutative ring `R`, and bidegree
`(i, j)`, `Khⁱʲ(D.adjoinKink o b; R) ≅ Khⁱʲ(D.adjoinCircle o; R)`. -/
def adjoinKinkKhovanovHomologyIso (b : Bool)
    (hD' : (D.adjoinKink o b).toPDCode.IsPlanar) (i j : ℤ) :
    (D.adjoinKink o b).khovanovHomology hD' R i j ≅
      (D.adjoinCircle o).khovanovHomology hD₀ R i j :=
  (D.adjoinKinkKhovanovComplexHomotopyEquiv o hD₀ R b hD' j).toHomologyIso i

end AdjoinKink

end TauCeti.OrientedPDCode
