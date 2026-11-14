/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.Algebra.Homology.DerivedCategory.Plus
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.Acyclic
public import TauCeti.Algebra.Homology.HomologySequenceLemmas

/-!
# Computing bounded-below right derived functors from adapted resolutions

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough injectives.
Mathlib constructs the total right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D` as a triangulated
functor equipped with the complex-level unit
`F.rightDerivedFunctorPlusUnit : F.mapCochainComplexPlus ⋙ Q ⟶ Q ⋙ F.rightDerivedFunctorPlus`.

This file develops the computational interface for `F.rightDerivedFunctorPlus`:

* **Degreewise injective complexes, `t`-bounds, and truncations**:
  `F.rightDerivedFunctorPlusUnit.app K` is an isomorphism whenever `K` consists of injective
  objects (`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_injective`);
  `F.rightDerivedFunctorPlus` preserves `IsGE b` (`isGE_rightDerivedFunctorPlus_obj`), so its
  cohomology vanishes below degree `b`; and for any `K : CochainComplex.Plus C` and `m : ℤ`, the
  canonical truncation `K.ιTruncLE m : K.truncLE m ⟶ K` induces an isomorphism on
  `Hⁱ(RF(Q -))` for `i ≤ m` and a monomorphism for `i ≤ m + 1`.
* **Adapted classes (Stacks Lemma 13.16.7, tag 015E)**: if `P : ObjectProperty C` contains all
  injective objects, is closed under isomorphisms and cokernels of monomorphisms, and `F` is exact
  on short exact sequences in `P`, then `F.rightDerivedFunctorPlusUnit.app K` is an isomorphism for
  every `K : CochainComplex.Plus C` with terms in `P`
  (`isIso_rightDerivedFunctorPlusUnit_app_of_adapted`), `F` preserves quasi-isomorphisms between
  bounded-below complexes in `P` (`quasiIso_map_of_adapted`), and any bounded-below `P`-resolution
  `ι : X ⟶ K` computes `F.rightDerivedFunctorPlus.obj (Q.obj X)` and its cohomology, naturally up
  to homotopy (`rightDerivedFunctorPlusObjIsoOfResolution`,
  `rightDerivedFunctorPlusHomologyIsoOfResolution`, `rightDerivedFunctorPlusIsoOfResolution`).
* **Compatibility with classical right derived functors**: composing with
  `DerivedCategory.Plus.singleFunctor C 0` and taking `n`-th cohomology recovers `F.rightDerived n`
  naturally (`singleFunctorCompRightDerivedFunctorPlusHomologyIso`), and vanishes in negative
  degrees (`isZero_singleFunctor_comp_rightDerivedFunctorPlus_homology_of_neg`).

## References

* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque 239 (1996), II.2.
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006, §13.3.
* The Stacks Project, Derived Categories, §13.16, Lemma 13.16.7 (tag 015E).
-/

public section

noncomputable section

open CategoryTheory Category Limits Pretriangulated Triangulated

universe w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

section General

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

/-- Naturality of `F.rightDerivedFunctorPlusUnit` with unfolded functor compositions. -/
@[reassoc]
lemma rightDerivedFunctorPlusUnit_naturality {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f) ≫
        F.rightDerivedFunctorPlusUnit.app L =
      F.rightDerivedFunctorPlusUnit.app K ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) :=
  F.rightDerivedFunctorPlusUnit.naturality f

/-- The unit `F.rightDerivedFunctorPlusUnit.app K` is an isomorphism on any bounded-below cochain
complex `K` whose terms are injective. -/
instance isIso_rightDerivedFunctorPlusUnit_app_of_injective (K : CochainComplex.Plus C)
    [∀ n : ℤ, Injective (K.obj.X n)] :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨b, _⟩ := K.property
  let K₀ : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty _ K.obj inferInstance
  have hK₀ : K₀.IsStrictlyGE b := by
    rwa [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff K₀ (InjectiveObject.ι C)]
  let K' : CochainComplex.Plus (InjectiveObject C) := ⟨K₀, b, hK₀⟩
  let e : (InjectiveObject.ι C).mapCochainComplexPlus.obj K' ≅ K :=
    (CochainComplex.Plus.fullyFaithfulι C).preimageIso
      (HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
        intro i j _
        dsimp [K', K₀, InjectiveObject.ι, HomologicalComplex.liftObjectProperty]
        rw [id_comp, comp_id]))
  exact (NatTrans.isIso_app_iff_of_iso F.rightDerivedFunctorPlusUnit e).1 inferInstance

/-- Homotopic morphisms in `CochainComplex.Plus C` induce equal morphisms under
`DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus`. -/
lemma rightDerivedFunctorPlus_Q_map_eq_of_homotopy {K L : CochainComplex.Plus C} {f g : K ⟶ L}
    (h : Homotopy f.hom g.hom) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) =
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g) :=
  congr_arg F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q_map_eq_of_homotopy h)

/-- `DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus` sends mapping-cone triangles in
`CochainComplex.Plus C` to distinguished triangles in `DerivedCategory.Plus D`. -/
lemma rightDerivedFunctorPlus_mappingConeTriangle_distinguished {K L : CochainComplex.Plus C}
    (f : K ⟶ L) :
    (DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus).mapTriangle.obj
        (CochainComplex.Plus.mappingConeTriangle f) ∈
      distTriang (DerivedCategory.Plus D) :=
  isomorphic_distinguished _
    (F.rightDerivedFunctorPlus.map_distinguished _
      (DerivedCategory.Plus.mappingConeTriangle_distinguished f)) _
    ((Functor.mapTriangleCompIso DerivedCategory.Plus.Q F.rightDerivedFunctorPlus).app _)

/-- `F.rightDerivedFunctorPlus` is left `t`-exact: it preserves `IsGE b` for every `b : ℤ`. -/
instance isGE_rightDerivedFunctorPlus_obj (X : DerivedCategory.Plus C) (b : ℤ) [X.IsGE b] :
    (F.rightDerivedFunctorPlus.obj X).IsGE b := by
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso X b
  let L' : CochainComplex.Plus C := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  have : L'.obj.IsStrictlyGE b := by
    dsimp only [L', mapCochainComplexPlus_obj_obj]
    infer_instance
  have : (F.mapCochainComplexPlus.obj L').obj.IsStrictlyGE b := by
    dsimp only [mapCochainComplexPlus_obj_obj]
    infer_instance
  let eIso : DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj L') ≅
      F.rightDerivedFunctorPlus.obj X :=
    asIso (F.rightDerivedFunctorPlusUnit.app L') ≪≫ F.rightDerivedFunctorPlus.mapIso e
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso eIso b

/-- If `X : DerivedCategory.Plus C` is `≥ b`, then the cohomology of
`F.rightDerivedFunctorPlus.obj X` vanishes in every degree `i < b`. -/
lemma isZero_homology_rightDerivedFunctorPlus_of_isGE (X : DerivedCategory.Plus C) (b i : ℤ)
    (hi : i < b) [X.IsGE b] :
    IsZero ((DerivedCategory.Plus.homologyFunctor D i).obj (F.rightDerivedFunctorPlus.obj X)) :=
  DerivedCategory.Plus.isZero_of_isGE (F.rightDerivedFunctorPlus.obj X) b i hi

/-- If `K : CochainComplex.Plus C` has vanishing cohomology below degree `b`, the quotient map to
its canonical truncation `K.truncGE b` becomes an isomorphism under `F.rightDerivedFunctorPlus`. -/
instance isIso_rightDerivedFunctorPlus_πTruncGE (K : CochainComplex.Plus C) (b : ℤ)
    [K.obj.IsGE b] :
    IsIso (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (K.πTruncGE b))) := by
  have : QuasiIso (K.πTruncGE b).hom := by
    dsimp only [CochainComplex.Plus.πTruncGE_hom]
    infer_instance
  infer_instance

/-- For any bounded-below cochain complex `K` and integer `m`, the canonical truncation inclusion
`K.ιTruncLE m : K.truncLE m ⟶ K` induces a monomorphism on `Hⁱ(RF(Q -))` in every degree
`i ≤ m + 1`. -/
lemma mono_homologyMap_rightDerivedFunctorPlus_ιTruncLE (K : CochainComplex.Plus C) (m i : ℤ)
    (hi : i ≤ m + 1) :
    Mono ((DerivedCategory.Plus.homologyFunctor D i).map
      (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (K.ιTruncLE m)))) := by
  let T := F.rightDerivedFunctorPlus.mapTriangle.obj
    (DerivedCategory.Plus.truncLEGETriangle K m (m + 1) rfl)
  have hT : T ∈ distTriang (DerivedCategory.Plus D) :=
    F.rightDerivedFunctorPlus.map_distinguished _
      (DerivedCategory.Plus.truncLEGETriangle_distinguished K m (m + 1) rfl)
  let T' := DerivedCategory.Plus.ι.mapTriangle.obj T
  have hT' : T' ∈ distTriang (DerivedCategory D) :=
    (DerivedCategory.Plus.mem_distTriang_iff T).1 hT
  have : (K.truncGE (m + 1)).obj.IsGE (m + 1) := by
    dsimp only [CochainComplex.Plus.truncGE_obj]
    infer_instance
  have hobj₃ : T.obj₃.IsGE (m + 1) := by
    dsimp only [T, Functor.mapTriangle_obj, DerivedCategory.Plus.truncLEGETriangle,
      Triangle.mk_obj₃]
    infer_instance
  have hzero : IsZero ((DerivedCategory.homologyFunctor D (i - 1)).obj T'.obj₃) := by
    have : T'.obj₃.IsGE (m + 1) := by
      dsimp only [T', Functor.mapTriangle_obj, Triangle.mk_obj₃]
      infer_instance
    exact DerivedCategory.isZero_of_isGE T'.obj₃ (m + 1) (i - 1) (by lia)
  exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T' hT' (i - 1) i (by lia)).2
    (hzero.eq_of_src _ _)

/-- For any bounded-below cochain complex `K` and integer `m`, the canonical truncation inclusion
`K.ιTruncLE m : K.truncLE m ⟶ K` induces an epimorphism on `Hⁱ(RF(Q -))` in every degree
`i ≤ m`. -/
lemma epi_homologyMap_rightDerivedFunctorPlus_ιTruncLE (K : CochainComplex.Plus C) (m i : ℤ)
    (hi : i ≤ m) :
    Epi ((DerivedCategory.Plus.homologyFunctor D i).map
      (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (K.ιTruncLE m)))) := by
  let T := F.rightDerivedFunctorPlus.mapTriangle.obj
    (DerivedCategory.Plus.truncLEGETriangle K m (m + 1) rfl)
  have hT : T ∈ distTriang (DerivedCategory.Plus D) :=
    F.rightDerivedFunctorPlus.map_distinguished _
      (DerivedCategory.Plus.truncLEGETriangle_distinguished K m (m + 1) rfl)
  let T' := DerivedCategory.Plus.ι.mapTriangle.obj T
  have hT' : T' ∈ distTriang (DerivedCategory D) :=
    (DerivedCategory.Plus.mem_distTriang_iff T).1 hT
  have : (K.truncGE (m + 1)).obj.IsGE (m + 1) := by
    dsimp only [CochainComplex.Plus.truncGE_obj]
    infer_instance
  have hobj₃ : T.obj₃.IsGE (m + 1) := by
    dsimp only [T, Functor.mapTriangle_obj, DerivedCategory.Plus.truncLEGETriangle,
      Triangle.mk_obj₃]
    infer_instance
  have hzero : IsZero ((DerivedCategory.homologyFunctor D i).obj T'.obj₃) := by
    have : T'.obj₃.IsGE (m + 1) := by
      dsimp only [T', Functor.mapTriangle_obj, Triangle.mk_obj₃]
      infer_instance
    exact DerivedCategory.isZero_of_isGE T'.obj₃ (m + 1) i (by lia)
  exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T' hT' i).2
    (hzero.eq_of_tgt _ _)

/-- For any bounded-below cochain complex `K` and integer `m`, the canonical truncation inclusion
`K.ιTruncLE m : K.truncLE m ⟶ K` induces an isomorphism on `Hⁱ(RF(Q -))` in every degree
`i ≤ m`. -/
lemma isIso_homologyMap_rightDerivedFunctorPlus_ιTruncLE (K : CochainComplex.Plus C) (m i : ℤ)
    (hi : i ≤ m) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D i).map
      (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (K.ιTruncLE m)))) := by
  have := F.mono_homologyMap_rightDerivedFunctorPlus_ιTruncLE K m i (by lia)
  have := F.epi_homologyMap_rightDerivedFunctorPlus_ιTruncLE K m i hi
  exact isIso_of_mono_of_epi _

/-- Component isomorphism identifying the cohomology of `Q.obj (F.mapCochainComplexPlus.obj K)`
with the cohomology of `(F.mapHomologicalComplex (.up ℤ)).obj K.obj`. -/
private def mapCochainComplexPlusHomologyIso (K : CochainComplex.Plus C) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj
        (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)) ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).homology n :=
  (DerivedCategory.Plus.homologyFunctorFactors D n).app (F.mapCochainComplexPlus.obj K)

omit [EnoughInjectives C] [HasDerivedCategory C] in
@[reassoc]
private lemma mapCochainComplexPlusHomologyIso_hom_naturality {K L : CochainComplex.Plus C}
    (φ : K ⟶ L) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).map
        (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ)) ≫
        (F.mapCochainComplexPlusHomologyIso L n).hom =
      (F.mapCochainComplexPlusHomologyIso K n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom) n :=
  DerivedCategory.Plus.homologyFunctorFactors_hom_naturality (F.mapCochainComplexPlus.map φ) n

end General

section Adapted

variable (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hinj : ∀ Y : C, Injective Y → P Y)
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)

include hinj hP hF in
/-- **Adapted complexes compute `rightDerivedFunctorPlus` (Stacks Lemma 13.16.7, tag 015E).**
Let `P` contain the injective objects, be closed under isomorphisms and cokernels of monomorphisms,
and assume `F` is exact on short exact sequences in `P`. Then `F.rightDerivedFunctorPlusUnit.app K`
is an isomorphism for every bounded-below complex `K` whose terms belong to `P`. -/
theorem isIso_rightDerivedFunctorPlusUnit_app_of_adapted
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (K : CochainComplex.Plus C) (hK : ∀ n : ℤ, P (K.obj.X n)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨b, _⟩ := K.property
  obtain ⟨L₀, i₀, _, _, hL₀inj, hL₀ge⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective K.obj (b - 1) b (by lia)
  -- The cokernel of `i₀ : K.obj ⟶ L₀` is bounded below, acyclic, and degreewise in `P`.
  let S := ShortComplex.mk i₀ (cokernel.π i₀) (cokernel.condition i₀)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i₀)) inferInstance inferInstance
  have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  have hX₃ge : S.X₃.IsStrictlyGE (b - 1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    have hL₀n : IsZero (S.X₂.X n) := CochainComplex.isZero_of_isStrictlyGE L₀ (b - 1) n hn
    have hepi : Epi (S.g.f n) := (hSn n).epi_g
    rw [IsZero.iff_id_eq_zero, ← cancel_epi (S.g.f n), comp_id, comp_zero]
    exact hL₀n.eq_of_src _ _
  have hFS : (S.map (F.mapHomologicalComplex (.up ℤ))).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
      hF _ (hSn n) (hK n) (hinj _ (hL₀inj n))
  have hFi₀ : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map i₀) :=
    hFS.quasiIso_f_iff.2 (HomologicalComplex.Acyclic.map_of_shortExact_of_isStrictlyGE F P hP hF
      (b - 1) (hS.quasiIso_f_iff.1 inferInstance) fun n _ ↦
        hP _ (hSn n) (hK n) (hinj _ (hL₀inj n)))
  -- Compare `K` with the injective complex `L = ⟨L₀, _⟩` via `rightDerivedFunctorPlusUnit`.
  let L : CochainComplex.Plus C := ⟨L₀, b - 1, hL₀ge⟩
  let i : K ⟶ L := ObjectProperty.homMk i₀
  have : ∀ n : ℤ, Injective (L.obj.X n) := hL₀inj
  have : QuasiIso i.hom := by
    dsimp only [i, ObjectProperty.homMk_hom]
    infer_instance
  have : QuasiIso (F.mapCochainComplexPlus.map i).hom := by
    dsimp only [i, mapCochainComplexPlus_map_hom, ObjectProperty.homMk_hom]
    exact hFi₀
  have : IsIso (F.rightDerivedFunctorPlusUnit.app K ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i)) := by
    rw [← F.rightDerivedFunctorPlusUnit_naturality i]
    exact IsIso.comp_isIso
  exact IsIso.of_isIso_comp_right (F.rightDerivedFunctorPlusUnit.app K)
    (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i))

include hinj hP hF in
/-- `F` preserves quasi-isomorphisms between bounded-below `ℤ`-indexed cochain complexes whose
terms lie in an `F`-adapted class `P`. -/
theorem quasiIso_map_of_adapted {K L : CochainComplex C ℤ} (b₁ b₂ : ℤ)
    [K.IsStrictlyGE b₁] [L.IsStrictlyGE b₂] (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n : ℤ, P (K.X n)) (hL : ∀ n : ℤ, P (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map φ) := by
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  let K' : CochainComplex.Plus C := ⟨K, b₁, inferInstance⟩
  let L' : CochainComplex.Plus C := ⟨L, b₂, inferInstance⟩
  let φ' : K' ⟶ L' := ObjectProperty.homMk φ
  have : QuasiIso φ'.hom := by
    dsimp only [φ', ObjectProperty.homMk_hom]
    infer_instance
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_adapted P hinj hP hF K' hK
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_adapted P hinj hP hF L' hL
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ') ≫
      F.rightDerivedFunctorPlusUnit.app L') := by
    rw [F.rightDerivedFunctorPlusUnit_naturality φ']
    exact IsIso.comp_isIso
  have hQ : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ')) :=
    IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlusUnit.app L')
  exact (DerivedCategory.Plus.isIso_Q_map_iff_quasiIso (F.mapCochainComplexPlus.map φ')).1 hQ

section Resolution

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

/-- For a bounded-below `P`-resolution `ι : X ⟶ K` in `CochainComplex.Plus C`, `RF(Q X)` is
canonically isomorphic to `Q(F K)` in `DerivedCategory.Plus D`. -/
def rightDerivedFunctorPlusObjIsoOfResolution {X K : CochainComplex.Plus C} (ι : X ⟶ K)
    [QuasiIso ι.hom] (hK : ∀ n : ℤ, P (K.obj.X n)) :
    F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj X) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K) :=
  let eUnit : DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K) ≅
      F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) :=
    @asIso _ _ _ _ (F.rightDerivedFunctorPlusUnit.app K)
      (F.isIso_rightDerivedFunctorPlusUnit_app_of_adapted P hinj hP hF K hK)
  F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map ι)) ≪≫ eUnit.symm

@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_comp_unit {X K : CochainComplex.Plus C}
    (ι : X ⟶ K) [QuasiIso ι.hom] (hK : ∀ n : ℤ, P (K.obj.X n)) :
    (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hK).hom ≫
        F.rightDerivedFunctorPlusUnit.app K =
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ι) := by
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_adapted P hinj hP hF K hK
  simp [rightDerivedFunctorPlusObjIsoOfResolution]

/-- `rightDerivedFunctorPlusObjIsoOfResolution` is natural with respect to morphisms of resolutions
that commute up to homotopy. -/
@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality_of_homotopy
    {X K Y L : CochainComplex.Plus C} (ι : X ⟶ K) [QuasiIso ι.hom] (hK : ∀ n : ℤ, P (K.obj.X n))
    (κ : Y ⟶ L) [QuasiIso κ.hom] (hL : ∀ n : ℤ, P (L.obj.X n))
    (f : X ⟶ Y) (φ : K ⟶ L) (H : Homotopy (ι.hom ≫ φ.hom) (f.hom ≫ κ.hom)) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF κ hL).hom =
      (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hK).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) := by
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_adapted P hinj hP hF L hL
  rw [← cancel_mono (F.rightDerivedFunctorPlusUnit.app L), assoc, assoc,
    F.rightDerivedFunctorPlusObjIsoOfResolution_hom_comp_unit,
    F.rightDerivedFunctorPlusUnit_naturality φ,
    F.rightDerivedFunctorPlusObjIsoOfResolution_hom_comp_unit_assoc,
    ← F.rightDerivedFunctorPlus.map_comp, ← F.rightDerivedFunctorPlus.map_comp,
    ← DerivedCategory.Plus.Q.map_comp, ← DerivedCategory.Plus.Q.map_comp]
  exact F.rightDerivedFunctorPlus_Q_map_eq_of_homotopy H.symm

/-- Strict naturality of `rightDerivedFunctorPlusObjIsoOfResolution` for commuting morphisms of
bounded-below `P`-resolutions. -/
@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality
    {X K Y L : CochainComplex.Plus C} (ι : X ⟶ K) [QuasiIso ι.hom] (hK : ∀ n : ℤ, P (K.obj.X n))
    (κ : Y ⟶ L) [QuasiIso κ.hom] (hL : ∀ n : ℤ, P (L.obj.X n))
    (f : X ⟶ Y) (φ : K ⟶ L) (hφ : ι ≫ φ = f ≫ κ) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF κ hL).hom =
      (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hK).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) :=
  F.rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality_of_homotopy P hinj hP hF ι hK κ hL f φ
    (Homotopy.ofEq (congr_arg (CochainComplex.Plus.ι C).map hφ))

/-- For a bounded-below `P`-resolution `ι : X ⟶ K` in `CochainComplex.Plus C`, the `n`-th
cohomology of `RF(Q X)` is canonically isomorphic to `Hⁿ(F K)`. -/
def rightDerivedFunctorPlusHomologyIsoOfResolution {X K : CochainComplex.Plus C} (ι : X ⟶ K)
    [QuasiIso ι.hom] (hK : ∀ n : ℤ, P (K.obj.X n)) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj X)) ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).homology n :=
  (DerivedCategory.Plus.homologyFunctor D n).mapIso
    (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hK) ≪≫
    F.mapCochainComplexPlusHomologyIso K n

/-- `rightDerivedFunctorPlusHomologyIsoOfResolution` is natural with respect to morphisms of
bounded-below `P`-resolutions commuting up to homotopy. -/
@[reassoc]
lemma rightDerivedFunctorPlusHomologyIsoOfResolution_hom_naturality_of_homotopy
    {X K Y L : CochainComplex.Plus C} (ι : X ⟶ K) [QuasiIso ι.hom] (hK : ∀ n : ℤ, P (K.obj.X n))
    (κ : Y ⟶ L) [QuasiIso κ.hom] (hL : ∀ n : ℤ, P (L.obj.X n))
    (f : X ⟶ Y) (φ : K ⟶ L) (H : Homotopy (ι.hom ≫ φ.hom) (f.hom ≫ κ.hom)) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) ≫
        (F.rightDerivedFunctorPlusHomologyIsoOfResolution P hinj hP hF κ hL n).hom =
      (F.rightDerivedFunctorPlusHomologyIsoOfResolution P hinj hP hF ι hK n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom) n := by
  dsimp only [rightDerivedFunctorPlusHomologyIsoOfResolution, Iso.trans_hom, mapIso_hom]
  rw [← map_comp_assoc,
    F.rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality_of_homotopy P hinj hP hF ι hK κ hL
      f φ H,
    map_comp_assoc, F.mapCochainComplexPlusHomologyIso_hom_naturality, assoc]

/-- A functorial bounded-below `P`-resolution `ι : G ⟶ R` indexed by any category `E` computes
`G ⋙ Q ⋙ F.rightDerivedFunctorPlus` naturally as `R ⋙ F.mapCochainComplexPlus ⋙ Q`. -/
def rightDerivedFunctorPlusIsoOfResolution {E : Type u₃} [Category.{v₃} E]
    (G R : E ⥤ CochainComplex.Plus C) (ι : G ⟶ R) [∀ A, QuasiIso (ι.app A).hom]
    (hR : ∀ (A : E) (n : ℤ), P ((R.obj A).obj.X n)) :
    G ⋙ DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus ≅
      R ⋙ F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  NatIso.ofComponents
    (fun A ↦ F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF (ι.app A) (hR A))
    (fun f ↦ F.rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality P hinj hP hF
      (ι.app _) (hR _) (ι.app _) (hR _) (G.map f) (R.map f) (ι.naturality f).symm)

@[simp]
lemma rightDerivedFunctorPlusIsoOfResolution_app {E : Type u₃} [Category.{v₃} E]
    (G R : E ⥤ CochainComplex.Plus C) (ι : G ⟶ R) [∀ A, QuasiIso (ι.app A).hom]
    (hR : ∀ (A : E) (n : ℤ), P ((R.obj A).obj.X n)) (A : E) :
    (F.rightDerivedFunctorPlusIsoOfResolution P hinj hP hF G R ι hR).app A =
      F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF (ι.app A) (hR A) :=
  (rfl)

end Resolution

end Adapted

section SingleDegreeZero

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

/-- In negative degrees, `F.rightDerivedFunctorPlus` applied to a single object in degree `0` has
vanishing cohomology. -/
lemma isZero_singleFunctor_comp_rightDerivedFunctorPlus_homology_of_neg (X : C) (m : ℤ)
    (hm : m < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D m).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X))) :=
  F.isZero_homology_rightDerivedFunctorPlus_of_isGE
    ((DerivedCategory.Plus.singleFunctor C 0).obj X) 0 m hm

/-- The chosen injective resolution of `X : C` extended by zero to `CochainComplex.Plus C`. -/
@[implicit_reducible]
private def injectiveResolutionPlus (X : C) : CochainComplex.Plus C :=
  ⟨(injectiveResolution X).cochainComplex, 0, inferInstance⟩

/-- The quasi-isomorphism from `(CochainComplex.Plus.singleFunctor C 0).obj X` to
`injectiveResolutionPlus X` induced by `(injectiveResolution X).ι'`. -/
private def injectiveResolutionPlusι (X : C) :
    (CochainComplex.Plus.singleFunctor C 0).obj X ⟶ injectiveResolutionPlus X :=
  ObjectProperty.homMk (injectiveResolution X).ι'

private instance (X : C) (m : ℤ) : Injective ((injectiveResolutionPlus X).obj.X m) := by
  dsimp only [injectiveResolutionPlus]
  infer_instance

private instance (X : C) : QuasiIso (injectiveResolutionPlusι X).hom :=
  let u : (CochainComplex.singleFunctor C 0).obj X ⟶
      ((CochainComplex.single₀ C).obj X).extend ComplexShape.embeddingUpNat :=
    (HomologicalComplex.extendSingleIso _ _ _ _ (by simp)).inv
  let v : ((CochainComplex.single₀ C).obj X).extend ComplexShape.embeddingUpNat ⟶
      (injectiveResolution X).cocomplex.extend ComplexShape.embeddingUpNat :=
    HomologicalComplex.extendMap (injectiveResolution X).ι ComplexShape.embeddingUpNat
  quasiIso_comp u v

private def singleQObjIso (X : C) :
    (DerivedCategory.Plus.singleFunctor C 0).obj X ≅
      DerivedCategory.Plus.Q.obj ((CochainComplex.Plus.singleFunctor C 0).obj X) :=
  (DerivedCategory.Plus.singleFunctorIsoCompQ C 0).app X

omit [EnoughInjectives C] in
@[reassoc]
private lemma singleQObjIso_hom_naturality {X Y : C} (f : X ⟶ Y) :
    (DerivedCategory.Plus.singleFunctor C 0).map f ≫ (singleQObjIso Y).hom =
      (singleQObjIso X).hom ≫
        DerivedCategory.Plus.Q.map ((CochainComplex.Plus.singleFunctor C 0).map f) :=
  (DerivedCategory.Plus.singleFunctorIsoCompQ C 0).hom.naturality f

private def rightDerivedFunctorPlusUnitIso (K : CochainComplex.Plus C)
    [∀ m : ℤ, Injective (K.obj.X m)] :
    DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K) ≅
      F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) :=
  asIso (F.rightDerivedFunctorPlusUnit.app K)

@[reassoc]
private lemma rightDerivedFunctorPlusUnitIso_hom_naturality {K L : CochainComplex.Plus C}
    [∀ m : ℤ, Injective (K.obj.X m)] [∀ m : ℤ, Injective (L.obj.X m)] (f : K ⟶ L) :
    DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f) ≫
        (F.rightDerivedFunctorPlusUnitIso L).hom =
      (F.rightDerivedFunctorPlusUnitIso K).hom ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) :=
  F.rightDerivedFunctorPlusUnit.naturality f

private def singleObjIsoInjectiveResolution (X : C) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj (injectiveResolutionPlus X)) :=
  F.rightDerivedFunctorPlus.mapIso
    (singleQObjIso X ≪≫ asIso (DerivedCategory.Plus.Q.map (injectiveResolutionPlusι X))) ≪≫
    (F.rightDerivedFunctorPlusUnitIso (injectiveResolutionPlus X)).symm

private def injectiveResolutionExtendHomologyIso (X : C) (n : ℕ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (injectiveResolutionPlus X).obj).homology (n : ℤ) ≅
      (HomologicalComplex.homologyFunctor D (.up ℕ) n).obj
        ((F.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution X).cocomplex) :=
  (ComplexShape.embeddingUpNat.extendFunctorCompMapHomologicalComplexHomologyIso F
    (j := n) (j' := (n : ℤ)) (by simp)).app (injectiveResolution X).cocomplex

omit [HasDerivedCategory C] [HasDerivedCategory D] in
@[reassoc]
private lemma injectiveResolutionExtendHomologyIso_hom_naturality {X Y : C} {f : X ⟶ Y}
    (φ : InjectiveResolution.Hom (injectiveResolution X) (injectiveResolution Y) f) (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) ≫
        (F.injectiveResolutionExtendHomologyIso Y n).hom =
      (F.injectiveResolutionExtendHomologyIso X n).hom ≫
        (F.mapHomologicalComplex (.up ℕ) ⋙
          HomologicalComplex.homologyFunctor D (.up ℕ) n).map φ.hom :=
  (ComplexShape.embeddingUpNat.extendFunctorCompMapHomologicalComplexHomologyIso F
    (j := n) (j' := (n : ℤ)) (by simp)).hom.naturality φ.hom

/-- On single complexes concentrated in degree `0`, the `n`-th cohomology of
`F.rightDerivedFunctorPlus` is naturally isomorphic to the classical right derived functor
`F.rightDerived n`. -/
def singleFunctorCompRightDerivedFunctorPlusHomologyIso (n : ℕ) :
    DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor D (n : ℤ) ≅
      F.rightDerived n := by
  refine NatIso.ofComponents (fun X ↦ ?_) (fun {X Y} f ↦ ?_)
  · exact (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).mapIso
        (F.singleObjIsoInjectiveResolution X) ≪≫
      F.mapCochainComplexPlusHomologyIso (injectiveResolutionPlus X) (n : ℤ) ≪≫
      F.injectiveResolutionExtendHomologyIso X n ≪≫
      ((injectiveResolution X).isoRightDerivedObj F n).symm
  · let φ : InjectiveResolution.Hom (injectiveResolution X) (injectiveResolution Y) f :=
      ⟨InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X), by
        rw [InjectiveResolution.desc_commutes_zero, CochainComplex.single₀_map_f_zero]
        rfl⟩
    let φPlus : injectiveResolutionPlus X ⟶ injectiveResolutionPlus Y :=
      ObjectProperty.homMk φ.hom'
    have hcomm : injectiveResolutionPlusι X ≫ φPlus =
        (CochainComplex.Plus.singleFunctor C 0).map f ≫ injectiveResolutionPlusι Y := by
      apply (CochainComplex.Plus.ι C).map_injective
      exact φ.ι'_comp_hom'
    have hD : F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫
        (F.singleObjIsoInjectiveResolution Y).hom =
        (F.singleObjIsoInjectiveResolution X).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φPlus) := by
      dsimp only [singleObjIsoInjectiveResolution]
      rw [← cancel_mono (F.rightDerivedFunctorPlusUnitIso (injectiveResolutionPlus Y)).hom]
      simp only [Iso.trans_hom, mapIso_hom, asIso_hom, Iso.symm_hom, assoc, Iso.inv_hom_id,
        comp_id, F.rightDerivedFunctorPlusUnitIso_hom_naturality, Iso.inv_hom_id_assoc]
      rw [← F.rightDerivedFunctorPlus.map_comp, ← F.rightDerivedFunctorPlus.map_comp,
        reassoc_of% (singleQObjIso_hom_naturality f), ← DerivedCategory.Plus.Q.map_comp,
        assoc, ← DerivedCategory.Plus.Q.map_comp, hcomm]
    dsimp only [Functor.comp_obj, comp_map, Iso.trans_hom, mapIso_hom, Iso.symm_hom]
    rw [← (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map_comp_assoc, hD,
      (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map_comp_assoc,
      reassoc_of% (F.mapCochainComplexPlusHomologyIso_hom_naturality φPlus (n : ℤ))]
    dsimp only [φPlus, ObjectProperty.homMk]
    rw [F.injectiveResolutionExtendHomologyIso_hom_naturality_assoc φ n, assoc, assoc, assoc]
    exact _ ≫= (_ ≫= (_ ≫= (InjectiveResolution.isoRightDerivedObj_inv_naturality f
      (injectiveResolution X) (injectiveResolution Y) φ.hom
      (InjectiveResolution.desc_commutes_zero f _ _) F n).symm))

end SingleDegreeZero

end CategoryTheory.Functor
