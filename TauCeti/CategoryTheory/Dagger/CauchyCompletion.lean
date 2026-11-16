/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Dagger.Mat
public import TauCeti.CategoryTheory.Dagger.Karoubi

/-!
# Finite dagger Cauchy completion

A preadditive dagger category is *finitely dagger Cauchy complete*
(`IsFinitelyDaggerCauchyComplete`) when it admits all finite dagger biproducts
(`HasFiniteDaggerBiproducts`) and every dagger projection splits via a dagger isometry
(`IsDaggerIdempotentComplete`).

Given any preadditive dagger category `C` with additive dagger (`DaggerPreadditive C`), its finite
dagger Cauchy completion is `DaggerCauchyCompletion C := DaggerKaroubi (Mat_ C)`. It is finitely
dagger Cauchy complete, receives a fully faithful additive dagger-preserving embedding
`DaggerCauchyCompletion.toDaggerCauchyCompletion C : C ⥤ DaggerCauchyCompletion C`, and satisfies
the universal property that every additive dagger-preserving functor `F : C ⥤ D` into a finitely
dagger Cauchy complete category extends along `toDaggerCauchyCompletion C` to an additive
dagger-preserving functor `DaggerCauchyCompletion.lift F : DaggerCauchyCompletion C ⥤ D`, strictly
unique up to a unique comparison isomorphism (which is pointwise unitary whenever the witness on
`C` is).

When `C` is already finitely dagger Cauchy complete, `toDaggerCauchyCompletion C` is part of an
equivalence `DaggerCauchyCompletion.equivSelf C : C ≌ DaggerCauchyCompletion C` with
dagger-preserving functors and pointwise unitary unit and counit isomorphisms.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ w

namespace TauCeti

/-- A preadditive dagger category is *finitely dagger Cauchy complete* if it has all finite dagger
biproducts and every dagger projection admits a dagger splitting. -/
class IsFinitelyDaggerCauchyComplete (C : Type u₁) [Category.{v₁} C] [Preadditive C]
    [DaggerCategory C] : Prop extends
  HasFiniteDaggerBiproducts C, IsDaggerIdempotentComplete C where

instance (C : Type u₁) [Category.{v₁} C] [Preadditive C] [DaggerCategory C]
    [HasFiniteDaggerBiproducts C] [IsDaggerIdempotentComplete C] :
    IsFinitelyDaggerCauchyComplete C where

/-- Dagger idempotent completeness transfers back along a dagger-preserving equivalence whose unit
is pointwise unitary. -/
theorem isDaggerIdempotentComplete_of_equivalence {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
    {D : Type u₂} [Category.{v₂} D] [DaggerCategory D] [IsDaggerIdempotentComplete D]
    (e : C ≌ D) [e.functor.PreservesDagger] [e.inverse.PreservesDagger]
    (hη : ∀ X : C, IsUnitary (e.unitIso.app X).hom) :
    IsDaggerIdempotentComplete C where
  daggerProjections_split X p hp := by
    have hsplit := IsDaggerIdempotentComplete.daggerProjections_split _ _
      (e.functor.map_isDaggerProjection hp)
    rcases (isDaggerSplit_iff _).mp hsplit with ⟨Y, v, hv, hrange⟩
    let s : DaggerSplitting (e.functor.map p) := ⟨Y, v, hv, hrange⟩
    let u := (e.unitIso.app X).hom
    have hu : IsUnitary u := hη X
    have hconj : dagger (dagger u) ≫ e.inverse.map (e.functor.map p) ≫ dagger u = p := by
      rw [dagger_dagger]
      have hnat : p ≫ u = u ≫ e.inverse.map (e.functor.map p) := e.unitIso.hom.naturality p
      rw [← Category.assoc, ← hnat, Category.assoc, hu.hom_dagger_id]
      exact Category.comp_id p
    have hs := (s.map e.inverse).ofUnitaryConj (dagger u) hu.dagger
    rw [hconj] at hs
    exact hs.isDaggerSplit

/-- The finite dagger Cauchy completion of a preadditive dagger category `C`, constructed as the
dagger Karoubi completion of the matrix category `Mat_ C`. -/
abbrev DaggerCauchyCompletion (C : Type u₁) [Category.{v₁} C] [Preadditive C]
    [DaggerCategory C] [DaggerPreadditive C] :=
  DaggerKaroubi (Mat_ C)

namespace DaggerCauchyCompletion

section Basic

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] [DaggerCategory C] [DaggerPreadditive C]

/-- The canonical embedding `C ⥤ DaggerCauchyCompletion C`, obtained by composing
`Mat_.embedding C` with `DaggerKaroubi.toDaggerKaroubi (Mat_ C)`. -/
noncomputable abbrev toDaggerCauchyCompletion : C ⥤ DaggerCauchyCompletion C :=
  Mat_.embedding C ⋙ DaggerKaroubi.toDaggerKaroubi (Mat_ C)

/-- When `C` is finitely dagger Cauchy complete, `Mat_ C` is already dagger idempotent complete. -/
instance instIsDaggerIdempotentCompleteMat [IsFinitelyDaggerCauchyComplete C] :
    IsDaggerIdempotentComplete (Mat_ C) :=
  isDaggerIdempotentComplete_of_equivalence (Mat_.daggerEquivalenceSelf C)
    (Mat_.isUnitary_daggerEquivalenceSelf_unitIso C)

end Basic

section UniversalProperty

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [DaggerCategory C] [DaggerPreadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [DaggerCategory D]
  [IsFinitelyDaggerCauchyComplete D]

/-- Extension of an additive dagger-preserving functor `F : C ⥤ D` into a finitely dagger Cauchy
complete category `D` along `toDaggerCauchyCompletion C`. -/
noncomputable abbrev lift (F : C ⥤ D) [F.Additive] [F.PreservesDagger] :
    DaggerCauchyCompletion C ⥤ D :=
  DaggerKaroubi.lift (Mat_.daggerLift F)

/-- Canonical unitary natural isomorphism `toDaggerCauchyCompletion C ⋙ lift F ≅ F`. -/
noncomputable def toDaggerCauchyCompletionCompLiftIso (F : C ⥤ D) [F.Additive] [F.PreservesDagger] :
    toDaggerCauchyCompletion C ⋙ lift F ≅ F :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Mat_.embedding C)
      (DaggerKaroubi.toDaggerKaroubiCompLiftIso (Mat_.daggerLift F)) ≪≫
      Mat_.embeddingDaggerLiftIso F

/-- Forward component of `toDaggerCauchyCompletionCompLiftIso F`. -/
@[simp] theorem toDaggerCauchyCompletionCompLiftIso_hom_app (F : C ⥤ D) [F.Additive]
    [F.PreservesDagger] (X : C) :
    (toDaggerCauchyCompletionCompLiftIso F).hom.app X =
      (DaggerKaroubi.toDaggerKaroubiCompLiftIso (Mat_.daggerLift F)).hom.app
          ((Mat_.embedding C).obj X) ≫
        (Mat_.embeddingDaggerLiftIso F).hom.app X := by
  dsimp [toDaggerCauchyCompletionCompLiftIso]
  exact Category.id_comp _

/-- Every component of `toDaggerCauchyCompletionCompLiftIso F` is unitary. -/
theorem isUnitary_toDaggerCauchyCompletionCompLiftIso (F : C ⥤ D) [F.Additive]
    [F.PreservesDagger] (X : C) :
    IsUnitary ((toDaggerCauchyCompletionCompLiftIso F).app X).hom := by
  have h1 := DaggerKaroubi.isUnitary_toDaggerKaroubiCompLiftIso (Mat_.daggerLift F)
    ((Mat_.embedding C).obj X)
  have h2 := Mat_.isUnitary_embeddingDaggerLiftIso F X
  change IsUnitary ((toDaggerCauchyCompletionCompLiftIso F).hom.app X)
  rw [toDaggerCauchyCompletionCompLiftIso_hom_app]
  exact h1.comp h2

/-- Any additive functor `L : DaggerCauchyCompletion C ⥤ D` equipped with
`α : toDaggerCauchyCompletion C ⋙ L ≅ F` is canonically isomorphic to `lift F`. -/
noncomputable def liftUnique (F : C ⥤ D) [F.Additive] [F.PreservesDagger]
    (L : DaggerCauchyCompletion C ⥤ D) [L.Additive]
    (α : toDaggerCauchyCompletion C ⋙ L ≅ F) : L ≅ lift F :=
  DaggerKaroubi.liftUnique (Mat_.daggerLift F) L
    (Mat_.daggerLiftUnique F (DaggerKaroubi.toDaggerKaroubi (Mat_ C) ⋙ L)
      ((Functor.associator _ _ _).symm ≪≫ α))

/-- Restricting `liftUnique F L α` along `toDaggerCauchyCompletion C` recovers `α`. -/
theorem liftUnique_hom_app_toDaggerCauchyCompletion (F : C ⥤ D) [F.Additive]
    [F.PreservesDagger] (L : DaggerCauchyCompletion C ⥤ D) [L.Additive]
    (α : toDaggerCauchyCompletion C ⋙ L ≅ F) (X : C) :
    (liftUnique F L α).hom.app ((toDaggerCauchyCompletion C).obj X) ≫
      (toDaggerCauchyCompletionCompLiftIso F).hom.app X = α.hom.app X := by
  rw [toDaggerCauchyCompletionCompLiftIso_hom_app, ← Category.assoc]
  dsimp only [liftUnique, toDaggerCauchyCompletion, Functor.comp_obj]
  rw [DaggerKaroubi.liftUnique_hom_app_toDaggerKaroubi (Mat_.daggerLift F) L _
      ((Mat_.embedding C).obj X),
    Mat_.daggerLiftUnique_hom_app_embedding]
  dsimp
  exact Category.id_comp _

/-- `liftUnique F L α` is pointwise unitary whenever `L` preserves daggers and `α` is pointwise
unitary. -/
theorem isUnitary_liftUnique (F : C ⥤ D) [F.Additive] [F.PreservesDagger]
    (L : DaggerCauchyCompletion C ⥤ D) [L.Additive] [L.PreservesDagger]
    (α : toDaggerCauchyCompletion C ⋙ L ≅ F)
    (hα : ∀ X, IsUnitary (α.app X).hom) (P : DaggerCauchyCompletion C) :
    IsUnitary ((liftUnique F L α).app P).hom := by
  refine DaggerKaroubi.isUnitary_liftUnique (Mat_.daggerLift F) L _ ?_ P
  intro M
  refine Mat_.isUnitary_daggerLiftUnique F (DaggerKaroubi.toDaggerKaroubi (Mat_ C) ⋙ L) _ ?_ M
  intro X
  change IsUnitary (𝟙 _ ≫ α.hom.app X)
  rw [Category.id_comp]
  exact hα X

/-- Strict uniqueness of the comparison transformation `L ⟶ lift F`: any natural transformation
matching `α` on `toDaggerCauchyCompletion C` equals `(liftUnique F L α).hom`. -/
theorem eq_liftUnique_hom (F : C ⥤ D) [F.Additive] [F.PreservesDagger]
    (L : DaggerCauchyCompletion C ⥤ D) [L.Additive]
    (α : toDaggerCauchyCompletion C ⋙ L ≅ F) (β : L ⟶ lift F)
    (hβ : ∀ X, β.app ((toDaggerCauchyCompletion C).obj X) ≫
      (toDaggerCauchyCompletionCompLiftIso F).hom.app X = α.hom.app X) :
    β = (liftUnique F L α).hom := by
  let αMat : Mat_.embedding C ⋙ (DaggerKaroubi.toDaggerKaroubi (Mat_ C) ⋙ L) ≅ F :=
    (Functor.associator _ _ _).symm ≪≫ α
  let βMat : DaggerKaroubi.toDaggerKaroubi (Mat_ C) ⋙ L ⟶ Mat_.daggerLift F :=
    Functor.whiskerLeft (DaggerKaroubi.toDaggerKaroubi (Mat_ C)) β ≫
      (DaggerKaroubi.toDaggerKaroubiCompLiftIso (Mat_.daggerLift F)).hom
  have hβMat : βMat = (Mat_.daggerLiftUnique F (DaggerKaroubi.toDaggerKaroubi (Mat_ C) ⋙ L)
      αMat).hom := by
    apply Mat_.eq_daggerLiftUnique_hom
    intro X
    have hX := hβ X
    rw [toDaggerCauchyCompletionCompLiftIso_hom_app] at hX
    change (β.app ((toDaggerCauchyCompletion C).obj X) ≫
        (DaggerKaroubi.toDaggerKaroubiCompLiftIso (Mat_.daggerLift F)).hom.app
          ((Mat_.embedding C).obj X)) ≫
        (Mat_.embeddingDaggerLiftIso F).hom.app X = 𝟙 _ ≫ α.hom.app X
    rw [Category.assoc, hX, Category.id_comp]
  apply DaggerKaroubi.eq_liftUnique_hom (Mat_.daggerLift F) L
    (Mat_.daggerLiftUnique F (DaggerKaroubi.toDaggerKaroubi (Mat_ C) ⋙ L) αMat) β
  intro M
  exact congrArg (fun τ => τ.app M) hβMat

/-- Two additive functors `DaggerCauchyCompletion C ⥤ D` (with `G` dagger-preserving) are naturally
isomorphic whenever their restrictions along `toDaggerCauchyCompletion C` are naturally
isomorphic; the resulting isomorphism is pointwise unitary if both functors preserve daggers and
the given isomorphism on `C` is unitary. -/
noncomputable def daggerExt {F G : DaggerCauchyCompletion C ⥤ D} [F.Additive] [G.Additive]
    [G.PreservesDagger]
    (α : toDaggerCauchyCompletion C ⋙ F ≅ toDaggerCauchyCompletion C ⋙ G) : F ≅ G :=
  liftUnique (toDaggerCauchyCompletion C ⋙ G) F α ≪≫
    (liftUnique (toDaggerCauchyCompletion C ⋙ G) G (Iso.refl _)).symm

/-- `DaggerCauchyCompletion.daggerExt` preserves pointwise unitarity. -/
theorem isUnitary_daggerExt {F G : DaggerCauchyCompletion C ⥤ D} [F.Additive] [G.Additive]
    [F.PreservesDagger] [G.PreservesDagger]
    (α : toDaggerCauchyCompletion C ⋙ F ≅ toDaggerCauchyCompletion C ⋙ G)
    (hα : ∀ X, IsUnitary (α.app X).hom) (P : DaggerCauchyCompletion C) :
    IsUnitary ((daggerExt α).app P).hom := by
  let e := (liftUnique (toDaggerCauchyCompletion C ⋙ G) G (Iso.refl _)).app P
  have h1 := isUnitary_liftUnique (toDaggerCauchyCompletion C ⋙ G) F α hα P
  have h2 : IsUnitary e.hom :=
    isUnitary_liftUnique (toDaggerCauchyCompletion C ⋙ G) G (Iso.refl _)
      (fun _ => IsUnitary.id _) P
  refine h1.comp ?_
  change IsUnitary e.inv
  rw [← e.dagger_hom_eq_inv_of_isUnitary h2]
  exact h2.dagger

end UniversalProperty

section SelfEquivalence

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] [DaggerCategory C] [DaggerPreadditive C]
  [IsFinitelyDaggerCauchyComplete C]

private noncomputable def equivSelfAux :
    toDaggerCauchyCompletion C ⋙ lift (𝟭 C) ⋙ toDaggerCauchyCompletion C ≅
      toDaggerCauchyCompletion C ⋙ 𝟭 (DaggerCauchyCompletion C) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (toDaggerCauchyCompletionCompLiftIso (𝟭 C))
      (toDaggerCauchyCompletion C) ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm

private theorem isUnitary_equivSelfAux (X : C) :
    IsUnitary ((equivSelfAux C).app X).hom := by
  have hu := isUnitary_toDaggerCauchyCompletionCompLiftIso (𝟭 C) X
  simpa [equivSelfAux] using (toDaggerCauchyCompletion C).map_isUnitary hu

/-- A finitely dagger Cauchy complete category is equivalent to its own finite dagger Cauchy
completion, via dagger-preserving functors with pointwise unitary unit and counit isomorphisms. -/
noncomputable def equivSelf : C ≌ DaggerCauchyCompletion C :=
  CategoryTheory.Equivalence.mk (toDaggerCauchyCompletion C) (lift (𝟭 C))
    (toDaggerCauchyCompletionCompLiftIso (𝟭 C)).symm
    (daggerExt (equivSelfAux C))

/-- The forward functor of `equivSelf C` is `toDaggerCauchyCompletion C`. -/
@[simp] theorem equivSelf_functor :
    (equivSelf C).functor = toDaggerCauchyCompletion C := (rfl)

/-- The inverse functor of `equivSelf C` is `lift (𝟭 C)`. -/
@[simp] theorem equivSelf_inverse :
    (equivSelf C).inverse = lift (𝟭 C) := (rfl)

/-- The forward functor of `equivSelf C` preserves daggers. -/
instance instPreservesDaggerEquivSelfFunctor : (equivSelf C).functor.PreservesDagger := by
  rw [equivSelf_functor]
  infer_instance

/-- The inverse functor of `equivSelf C` preserves daggers. -/
instance instPreservesDaggerEquivSelfInverse : (equivSelf C).inverse.PreservesDagger := by
  rw [equivSelf_inverse]
  infer_instance

/-- The unit of `equivSelf C` is pointwise unitary. -/
theorem isUnitary_equivSelf_unitIso (X : C) :
    IsUnitary ((equivSelf C).unitIso.app X).hom := by
  let η := (toDaggerCauchyCompletionCompLiftIso (𝟭 C)).symm
  let ε := daggerExt (equivSelfAux C)
  have hη : ∀ Y : C, IsUnitary (η.app Y).hom := fun Y => by
    have hu := isUnitary_toDaggerCauchyCompletionCompLiftIso (𝟭 C) Y
    change IsUnitary ((toDaggerCauchyCompletionCompLiftIso (𝟭 C)).app Y).inv
    rw [← ((toDaggerCauchyCompletionCompLiftIso (𝟭 C)).app Y).dagger_hom_eq_inv_of_isUnitary hu]
    exact hu.dagger
  have hη_inv : ∀ Y : C, IsUnitary (η.app Y).inv := fun Y => by
    rw [← (η.app Y).dagger_hom_eq_inv_of_isUnitary (hη Y)]
    exact (hη Y).dagger
  have hε : ∀ P : DaggerCauchyCompletion C, IsUnitary (ε.app P).hom :=
    isUnitary_daggerExt (equivSelfAux C) (isUnitary_equivSelfAux C)
  have hε_inv : ∀ P : DaggerCauchyCompletion C, IsUnitary (ε.app P).inv := fun P => by
    rw [← (ε.app P).dagger_hom_eq_inv_of_isUnitary (hε P)]
    exact (hε P).dagger
  change IsUnitary ((CategoryTheory.Equivalence.adjointifyη η ε).app X).hom
  dsimp [CategoryTheory.Equivalence.adjointifyη, Trans.trans]
  simp only [Category.comp_id]
  exact ((hη X).comp ((lift (𝟭 C)).map_isUnitary
      (hε_inv ((toDaggerCauchyCompletion C).obj X)))).comp
    ((lift (𝟭 C)).map_isUnitary ((toDaggerCauchyCompletion C).map_isUnitary (hη_inv X)))

/-- The counit of `equivSelf C` is pointwise unitary. -/
theorem isUnitary_equivSelf_counitIso (P : DaggerCauchyCompletion C) :
    IsUnitary ((equivSelf C).counitIso.app P).hom :=
  isUnitary_daggerExt (equivSelfAux C) (isUnitary_equivSelfAux C) P

end SelfEquivalence

end DaggerCauchyCompletion

end TauCeti
