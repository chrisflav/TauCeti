/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import TauCeti.Topology.Sheaves.Cohomology.Forget
public import TauCeti.Topology.Sheaves.Cohomology.Instances

/-!
# Bounded-below derived global sections of sheaves of modules

Let `R` be a commutative ring and `X` be an arbitrary topological space (with no separation,
compactness, or nonemptiness hypotheses). Applying Mathlib's bounded-below total right derived
functor construction `CategoryTheory.Functor.rightDerivedFunctorPlus` to the global sections functor
`Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)` produces the triangulated functor
`RΓ : D⁺(Mod(X_R)) ⥤ D⁺(Mod_R)`.

Because injective sheaves of `R`-modules are flasque, cokernels of monomorphisms between flasque
sheaves are flasque, and `Γ` is exact on short exact sequences of flasque sheaves, flasque sheaves
form an adapted class for `Γ` in the sense of
`TauCeti/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean`. Specializing that general
interface yields:

* **Computation by bounded-below flasque resolutions**: `rightDerivedFunctorPlusUnit.app K` is an
  isomorphism for every bounded-below complex `K` of flasque sheaves
  (`CategoryTheory.Sheaf.isIso_rightDerivedFunctorPlusUnit_app_Γ_of_isFlasque`); `Γ` preserves
  quasi-isomorphisms between bounded-below `ℤ`-indexed complexes of flasque sheaves
  (`quasiIso_map_Γ_of_isFlasque_int`); and any bounded-below flasque resolution `ι : F ⟶ K` computes
  both `RΓ(Q F)` (`rightDerivedFunctorPlusΓObjIsoOfIsFlasque`) and its cohomology
  (`rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque`), naturally up to homotopy, as well as
  functorially (`rightDerivedFunctorPlusΓIsoOfIsFlasque`).
* **Cone triangles, lower bounds, and canonical truncations**: mapping-cone triangles map to
  distinguished triangles (`rightDerivedFunctorPlusΓ_mappingConeTriangle_distinguished`), `IsGE b`
  forces cohomology of `RΓ` to vanish below degree `b`
  (`isZero_homology_rightDerivedFunctorPlusΓ_of_isGE`), and the canonical truncation inclusion
  `K.ιTruncLE m : K.truncLE m ⟶ K` induces an isomorphism on `Hⁱ(RΓ(Q -))` for `i ≤ m` and a
  monomorphism for `i ≤ m + 1`.
* **Recovery of degree-zero sheaf cohomology**: on single sheaves concentrated in degree `0`,
  `Hⁿ(RΓ(F[0]))` vanishes for `n < 0` and for `n : ℕ` is naturally isomorphic to
  `(Sheaf.Γ _ _).rightDerived n`
  (`TauCeti.Topology.singleFunctorCompRightDerivedFunctorPlusΓHomologyIso`), to the cohomology of
  global sections of the Godement resolution
  (`singleFunctorCompRightDerivedFunctorPlusΓIsoGodement`), and—after forgetting `R`-module
  structures—to Mathlib's `Ext`-based sheaf cohomology `Sheaf.functorH`
  (`singleFunctorCompRightDerivedFunctorPlusΓForgetIsoFunctorH`).

## References

* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006, §13.3.
* The Stacks Project, Cohomology of Sheaves, §20.3, Lemma 20.12.3 (tag 09SY), and Lemma 20.30.2
  (tag 0FKT); Derived Categories, Lemma 13.16.7 (tag 015E).
-/

public section

noncomputable section

open CategoryTheory Category Limits Pretriangulated Triangulated TopologicalSpace

universe w₁ w₂ v u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  [(Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]

omit [(Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive] in
private lemma isFlasque_X₃_of_shortExact
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))) (hS : S.ShortExact)
    (h₁ : isFlasque X _ S.X₁) (h₂ : isFlasque X _ S.X₂) : isFlasque X _ S.X₃ :=
  have : TopCat.Presheaf.IsFlasque S.X₁.obj := isFlasque_iff.mp h₁
  have : TopCat.Presheaf.IsFlasque S.X₂.obj := isFlasque_iff.mp h₂
  isFlasque_iff.mpr hS.isFlasque_X₃_of_isFlasque

private lemma shortExact_map_Γ_of_shortExact_isFlasque
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))) (hS : S.ShortExact)
    (h₁ : isFlasque X _ S.X₁) (_ : isFlasque X _ S.X₂) :
    (S.map (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))).ShortExact :=
  have : TopCat.Presheaf.IsFlasque S.X₁.obj := isFlasque_iff.mp h₁
  hS.map_Γ_of_isFlasque

/-- Global sections preserve quasi-isomorphisms between bounded-below `ℤ`-indexed cochain complexes
of flasque sheaves of `R`-modules on an arbitrary topological space `X`. -/
theorem quasiIso_map_Γ_of_isFlasque_int
    {K L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℤ}
    (b₁ b₂ : ℤ) [K.IsStrictlyGE b₁] [L.IsStrictlyGE b₂] (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (K.X n).obj)
    (hL : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (L.X n).obj) :
    QuasiIso (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex
      (.up ℤ)).map φ) :=
  (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).quasiIso_map_of_adapted
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _))
    isFlasque_X₃_of_shortExact shortExact_map_Γ_of_shortExact_isFlasque b₁ b₂ φ
    (fun n ↦ isFlasque_iff.mpr (hK n)) (fun n ↦ isFlasque_iff.mpr (hL n))

section DerivedPlus

variable [HasDerivedCategory.{w₁} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]

/-- The unit of `(Γ _ _).rightDerivedFunctorPlus` is an isomorphism on any bounded-below complex of
flasque sheaves of `R`-modules. -/
theorem isIso_rightDerivedFunctorPlusUnit_app_Γ_of_isFlasque
    (K : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (hK : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (K.obj.X n).obj) :
    IsIso ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit.app
      K) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).isIso_rightDerivedFunctorPlusUnit_app_of_adapted
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _))
    isFlasque_X₃_of_shortExact shortExact_map_Γ_of_shortExact_isFlasque K
    (fun n ↦ isFlasque_iff.mpr (hK n))

/-- For a bounded-below flasque resolution `ι : F ⟶ K` in `CochainComplex.Plus`, `RΓ(Q F)` is
canonically isomorphic to `Q(Γ K)` in `DerivedCategory.Plus (ModuleCat.{u} R)`. -/
def rightDerivedFunctorPlusΓObjIsoOfIsFlasque
    {F K : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : F ⟶ K) [QuasiIso ι.hom] (hK : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (K.obj.X n).obj) :
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj F) ≅
      DerivedCategory.Plus.Q.obj
        ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapCochainComplexPlus.obj K) :=
  (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlusObjIsoOfResolution
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _))
    isFlasque_X₃_of_shortExact shortExact_map_Γ_of_shortExact_isFlasque ι
    (fun n ↦ isFlasque_iff.mpr (hK n))

@[reassoc]
lemma rightDerivedFunctorPlusΓObjIsoOfIsFlasque_hom_comp_unit
    {F K : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : F ⟶ K) [QuasiIso ι.hom] (hK : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (K.obj.X n).obj) :
    (rightDerivedFunctorPlusΓObjIsoOfIsFlasque ι hK).hom ≫
        (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit.app K =
      (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map ι) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).rightDerivedFunctorPlusObjIsoOfResolution_hom_comp_unit
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _))
    isFlasque_X₃_of_shortExact shortExact_map_Γ_of_shortExact_isFlasque ι
    (fun n ↦ isFlasque_iff.mpr (hK n))

/-- `rightDerivedFunctorPlusΓObjIsoOfIsFlasque` is natural with respect to morphisms of
bounded-below flasque resolutions commuting up to homotopy. -/
@[reassoc]
lemma rightDerivedFunctorPlusΓObjIsoOfIsFlasque_hom_naturality_of_homotopy
    {F K G L : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : F ⟶ K) [QuasiIso ι.hom] (hK : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (K.obj.X n).obj)
    (κ : G ⟶ L) [QuasiIso κ.hom] (hL : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (L.obj.X n).obj)
    (f : F ⟶ G) (φ : K ⟶ L) (H : Homotopy (ι.hom ≫ φ.hom) (f.hom ≫ κ.hom)) :
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map f) ≫
        (rightDerivedFunctorPlusΓObjIsoOfIsFlasque κ hL).hom =
      (rightDerivedFunctorPlusΓObjIsoOfIsFlasque ι hK).hom ≫
        DerivedCategory.Plus.Q.map
          ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapCochainComplexPlus.map φ) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality_of_homotopy
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _))
    isFlasque_X₃_of_shortExact shortExact_map_Γ_of_shortExact_isFlasque ι
    (fun n ↦ isFlasque_iff.mpr (hK n)) κ (fun n ↦ isFlasque_iff.mpr (hL n)) f φ H

/-- Strict naturality of `rightDerivedFunctorPlusΓObjIsoOfIsFlasque` for commuting morphisms of
bounded-below flasque resolutions. -/
@[reassoc]
lemma rightDerivedFunctorPlusΓObjIsoOfIsFlasque_hom_naturality
    {F K G L : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : F ⟶ K) [QuasiIso ι.hom] (hK : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (K.obj.X n).obj)
    (κ : G ⟶ L) [QuasiIso κ.hom] (hL : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (L.obj.X n).obj)
    (f : F ⟶ G) (φ : K ⟶ L) (hφ : ι ≫ φ = f ≫ κ) :
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map f) ≫
        (rightDerivedFunctorPlusΓObjIsoOfIsFlasque κ hL).hom =
      (rightDerivedFunctorPlusΓObjIsoOfIsFlasque ι hK).hom ≫
        DerivedCategory.Plus.Q.map
          ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapCochainComplexPlus.map φ) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _))
    isFlasque_X₃_of_shortExact shortExact_map_Γ_of_shortExact_isFlasque ι
    (fun n ↦ isFlasque_iff.mpr (hK n)) κ (fun n ↦ isFlasque_iff.mpr (hL n)) f φ hφ

/-- For a bounded-below flasque resolution `ι : F ⟶ K`, the `n`-th cohomology of `RΓ(Q F)` is
canonically isomorphic to `Hⁿ(Γ K)`. -/
def rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque
    {F K : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : F ⟶ K) [QuasiIso ι.hom] (hK : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (K.obj.X n).obj)
    (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).obj
        ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj F)) ≅
      (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex
        (.up ℤ)).obj K.obj).homology n :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).rightDerivedFunctorPlusHomologyIsoOfResolution
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _))
    isFlasque_X₃_of_shortExact shortExact_map_Γ_of_shortExact_isFlasque ι
    (fun m ↦ isFlasque_iff.mpr (hK m)) n

/-- `rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque` is natural with respect to morphisms of
bounded-below flasque resolutions commuting up to homotopy. -/
@[reassoc]
lemma rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque_hom_naturality_of_homotopy
    {F K G L : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : F ⟶ K) [QuasiIso ι.hom] (hK : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (K.obj.X n).obj)
    (κ : G ⟶ L) [QuasiIso κ.hom] (hL : ∀ n : ℤ, TopCat.Presheaf.IsFlasque (L.obj.X n).obj)
    (f : F ⟶ G) (φ : K ⟶ L) (H : Homotopy (ι.hom ≫ φ.hom) (f.hom ≫ κ.hom)) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
        ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map f)) ≫
        (rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque κ hL n).hom =
      (rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque ι hK n).hom ≫
        HomologicalComplex.homologyMap
          (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex
            (.up ℤ)).map φ.hom) n :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).rightDerivedFunctorPlusHomologyIsoOfResolution_hom_naturality_of_homotopy
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _))
    isFlasque_X₃_of_shortExact shortExact_map_Γ_of_shortExact_isFlasque ι
    (fun m ↦ isFlasque_iff.mpr (hK m)) κ (fun m ↦ isFlasque_iff.mpr (hL m)) f φ H n

/-- A functorial bounded-below flasque resolution `ι : G ⟶ K` computes `G ⋙ Q ⋙ RΓ` naturally as
`K ⋙ Γ.mapCochainComplexPlus ⋙ Q`. -/
def rightDerivedFunctorPlusΓIsoOfIsFlasque {E : Type*} [Category.{v} E]
    (G K : E ⥤ CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (ι : G ⟶ K) [∀ A, QuasiIso (ι.app A).hom]
    (hK : ∀ (A : E) (n : ℤ), TopCat.Presheaf.IsFlasque ((K.obj A).obj.X n).obj) :
    G ⋙ DerivedCategory.Plus.Q ⋙
        (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus ≅
      K ⋙ (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q :=
  (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlusIsoOfResolution
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _))
    isFlasque_X₃_of_shortExact shortExact_map_Γ_of_shortExact_isFlasque G K ι
    (fun A n ↦ isFlasque_iff.mpr (hK A n))

@[simp]
lemma rightDerivedFunctorPlusΓIsoOfIsFlasque_app {E : Type*} [Category.{v} E]
    (G K : E ⥤ CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (ι : G ⟶ K) [∀ A, QuasiIso (ι.app A).hom]
    (hK : ∀ (A : E) (n : ℤ), TopCat.Presheaf.IsFlasque ((K.obj A).obj.X n).obj) (A : E) :
    (rightDerivedFunctorPlusΓIsoOfIsFlasque G K ι hK).app A =
      rightDerivedFunctorPlusΓObjIsoOfIsFlasque (ι.app A) (hK A) := by
  simp [rightDerivedFunctorPlusΓIsoOfIsFlasque, rightDerivedFunctorPlusΓObjIsoOfIsFlasque]

/-- Mapping-cone triangles of bounded-below complexes of module sheaves map to distinguished
triangles in `DerivedCategory.Plus (ModuleCat.{u} R)` under `Q ⋙ RΓ`. -/
lemma rightDerivedFunctorPlusΓ_mappingConeTriangle_distinguished
    {K L : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (f : K ⟶ L) :
    (DerivedCategory.Plus.Q ⋙
        (Γ (Opens.grothendieckTopology X)
          (ModuleCat.{u} R)).rightDerivedFunctorPlus).mapTriangle.obj
        (CochainComplex.Plus.mappingConeTriangle f) ∈
      distTriang (DerivedCategory.Plus (ModuleCat.{u} R)) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).rightDerivedFunctorPlus_mappingConeTriangle_distinguished f

/-- If `F : DerivedCategory.Plus (Sheaf _ (ModuleCat R))` is `≥ b`, then `Hⁱ(RΓ(F))` vanishes for
every `i < b`. -/
lemma isZero_homology_rightDerivedFunctorPlusΓ_of_isGE
    (F : DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (b i : ℤ) (hi : i < b) [F.IsGE b] :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) i).obj
      ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.obj F)) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).isZero_homology_rightDerivedFunctorPlus_of_isGE F b i hi

/-- For any bounded-below complex `K` of module sheaves and `m : ℤ`, the canonical truncation
inclusion `K.ιTruncLE m : K.truncLE m ⟶ K` induces a monomorphism on `Hⁱ(RΓ(Q -))` for
`i ≤ m + 1`. -/
lemma mono_homologyMap_rightDerivedFunctorPlusΓ_ιTruncLE
    (K : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (m i : ℤ) (hi : i ≤ m + 1) :
    Mono ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) i).map
      ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (K.ιTruncLE m)))) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).mono_homologyMap_rightDerivedFunctorPlus_ιTruncLE K m i hi

/-- For any bounded-below complex `K` of module sheaves and `m : ℤ`, the canonical truncation
inclusion `K.ιTruncLE m : K.truncLE m ⟶ K` induces an epimorphism on `Hⁱ(RΓ(Q -))` for `i ≤ m`. -/
lemma epi_homologyMap_rightDerivedFunctorPlusΓ_ιTruncLE
    (K : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (m i : ℤ) (hi : i ≤ m) :
    Epi ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) i).map
      ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (K.ιTruncLE m)))) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).epi_homologyMap_rightDerivedFunctorPlus_ιTruncLE K m i hi

/-- For any bounded-below complex `K` of module sheaves and `m : ℤ`, the canonical truncation
inclusion `K.ιTruncLE m : K.truncLE m ⟶ K` induces an isomorphism on `Hⁱ(RΓ(Q -))` for `i ≤ m`. -/
lemma isIso_homologyMap_rightDerivedFunctorPlusΓ_ιTruncLE
    (K : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (m i : ℤ) (hi : i ≤ m) :
    IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) i).map
      ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (K.ιTruncLE m)))) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).isIso_homologyMap_rightDerivedFunctorPlus_ιTruncLE K m i hi

end DerivedPlus

end CategoryTheory.Sheaf

namespace TauCeti.Topology

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  [(Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]
  [HasDerivedCategory.{w₁} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]

/-- On a single sheaf of `R`-modules placed in degree `0`, `RΓ` has vanishing cohomology in
negative degrees. -/
lemma isZero_singleFunctor_comp_rightDerivedFunctorPlusΓ_homology_of_neg
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (m : ℤ) (hm : m < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) m).obj
      ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
  (Sheaf.Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).isZero_singleFunctor_comp_rightDerivedFunctorPlus_homology_of_neg F m hm

/-- On single sheaves of `R`-modules placed in degree `0`, the `n`-th cohomology of `RΓ` recovers
the classical right derived global sections functor `(Sheaf.Γ _ _).rightDerived n`. -/
def singleFunctorCompRightDerivedFunctorPlusΓHomologyIso (n : ℕ) :
    DerivedCategory.Plus.singleFunctor
        (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) 0 ⋙
        (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ) ≅
      (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n :=
  (Sheaf.Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).singleFunctorCompRightDerivedFunctorPlusHomologyIso n

/-- On single sheaves of `R`-modules placed in degree `0`, the `n`-th cohomology of `RΓ` is
naturally isomorphic to the `n`-th cohomology of global sections of the Godement resolution. -/
def singleFunctorCompRightDerivedFunctorPlusΓIsoGodement (n : ℕ) :
    DerivedCategory.Plus.singleFunctor
        (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) 0 ⋙
        (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ) ≅
      godementResolution (ModuleCat.{u} R) X ⋙
        (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _ ⋙
        HomologicalComplex.homologyFunctor _ _ n :=
  singleFunctorCompRightDerivedFunctorPlusΓHomologyIso n ≪≫ rightDerivedΓIsoGodement n

/-- On single sheaves of `R`-modules placed in degree `0`, the abelian group underlying the `n`-th
cohomology of `RΓ` is naturally isomorphic to Mathlib's `Ext`-based sheaf cohomology
`Sheaf.functorH (Opens.grothendieckTopology X) n` of the underlying abelian sheaf. -/
def singleFunctorCompRightDerivedFunctorPlusΓForgetIsoFunctorH (n : ℕ) :
    (DerivedCategory.Plus.singleFunctor
        (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) 0 ⋙
        (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)) ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ⋙
        Sheaf.functorH (Opens.grothendieckTopology X) n :=
  Functor.isoWhiskerRight (singleFunctorCompRightDerivedFunctorPlusΓHomologyIso n)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ≪≫
    moduleCohomologyForgetComparison X R n

end TauCeti.Topology
