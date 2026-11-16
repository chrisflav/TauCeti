/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Dagger.Idempotents
public import TauCeti.CategoryTheory.Linear.FullSubcategory
public import TauCeti.CategoryTheory.Linear.Karoubi

/-!
# Dagger Karoubi completion

This file constructs the dagger Karoubi completion `TauCeti.DaggerKaroubi C` of a dagger category
`C` as the full subcategory of Mathlib's `CategoryTheory.Idempotents.Karoubi C` spanned by
self-adjoint idempotents (dagger projections).

## Main definitions

* `TauCeti.isDaggerProjectionProperty C`: the `ObjectProperty` on `Idempotents.Karoubi C`
  selecting objects whose idempotent satisfies `dagger P.p = P.p`.
* `TauCeti.DaggerKaroubi C`: the dagger Karoubi completion of `C`, carrying induced
  `DaggerCategory`, `DaggerPreadditive`, `DaggerLinear R`, `IsDaggerIdempotentComplete`, and
  (when `C` has finite orthogonal biproducts) `HasFiniteDaggerBiproducts` structures.
* `TauCeti.DaggerKaroubi.toDaggerKaroubi C`: the fully faithful dagger-preserving embedding
  `C ⥤ DaggerKaroubi C`.
* `TauCeti.DaggerKaroubi.complement P` and `TauCeti.DaggerKaroubi.decomposition P`: in a
  preadditive dagger category, every `P : DaggerKaroubi C` has an orthogonal complement with
  unitary decomposition `daggerBiprod P P.complement ≅ (toDaggerKaroubi C).obj P.X`.
* `TauCeti.DaggerKaroubi.liftWithSplittings`, `TauCeti.DaggerKaroubi.liftWithSplittingsIso`,
  `TauCeti.DaggerKaroubi.liftWithSplittingsUnique`, and `TauCeti.DaggerKaroubi.lift`: the
  universal property of `DaggerKaroubi C` for dagger-preserving (additive / `R`-linear) functors,
  with explicit splittings, unitary independence of chosen splittings, unitary comparison
  isomorphisms, and strict uniqueness.
* `TauCeti.DaggerKaroubi.toDaggerKaroubiEquivalence C`: unitary equivalence `C ≌ DaggerKaroubi C`
  when `C` is already dagger idempotent complete.
* `TauCeti.DaggerKaroubi.equivKaroubiOfExistsSimilarProjection`: comparison equivalence
  `DaggerKaroubi C ≌ Idempotents.Karoubi C` whenever every idempotent in `C` is similar to a
  dagger projection.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe w v₁ v₂ u₁ u₂

/-- The object property on `Idempotents.Karoubi C` selecting objects whose idempotent is
self-adjoint (a dagger projection). -/
@[expose] def isDaggerProjectionProperty (C : Type u₁) [Category.{v₁} C] [DaggerCategory C] :
    ObjectProperty (Idempotents.Karoubi C) :=
  fun P => dagger P.p = P.p

/-- The dagger Karoubi completion (dagger idempotent completion) of a dagger category `C`,
realized as the full subcategory of `CategoryTheory.Idempotents.Karoubi C` spanned by dagger
projections `dagger P.p = P.p`. -/
abbrev DaggerKaroubi (C : Type u₁) [Category.{v₁} C] [DaggerCategory C] :=
  (isDaggerProjectionProperty C).FullSubcategory

namespace DaggerKaroubi

section Basic

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]

/-- Construct an object of `DaggerKaroubi C` from an object and a dagger projection on it. -/
@[expose] def mk (X : C) (p : X ⟶ X) (hp : IsDaggerProjection p) : DaggerKaroubi C :=
  ⟨⟨X, p, hp.idem⟩, hp.dagger_eq⟩

/-- The underlying object of `P : DaggerKaroubi C`. -/
abbrev X (P : DaggerKaroubi C) : C := P.obj.X

/-- The underlying dagger projection of `P : DaggerKaroubi C`. -/
abbrev p (P : DaggerKaroubi C) : P.X ⟶ P.X := P.obj.p

/-- Underlying object of `mk X p hp`. -/
@[simp] theorem mk_X (X : C) (p : X ⟶ X) (hp : IsDaggerProjection p) : (mk X p hp).X = X := (rfl)

/-- Underlying projection of `mk X p hp`. -/
@[simp] theorem mk_p (X : C) (p : X ⟶ X) (hp : IsDaggerProjection p) : (mk X p hp).p = p := (rfl)

/-- The projection of an object in `DaggerKaroubi C` is idempotent. -/
@[reassoc] theorem idem (P : DaggerKaroubi C) : P.p ≫ P.p = P.p :=
  P.obj.idem

/-- The projection of an object in `DaggerKaroubi C` is self-adjoint. -/
@[simp] theorem dagger_p (P : DaggerKaroubi C) : dagger P.p = P.p :=
  P.property

/-- The projection of an object in `DaggerKaroubi C` satisfies `IsDaggerProjection`. -/
theorem isDaggerProjection (P : DaggerKaroubi C) : IsDaggerProjection P.p :=
  (isDaggerProjection_iff _).mpr ⟨P.idem, P.dagger_p⟩

/-- Construct a morphism in `DaggerKaroubi C` from a compatible underlying morphism in `C`. -/
@[expose] def homMk {P Q : DaggerKaroubi C} (f : P.X ⟶ Q.X)
    (comm : P.p ≫ f ≫ Q.p = f := by simp) : P ⟶ Q :=
  ObjectProperty.homMk ⟨f, comm⟩

/-- Underlying morphism of `homMk f comm`. -/
@[simp] theorem homMk_hom_f {P Q : DaggerKaroubi C} (f : P.X ⟶ Q.X)
    (comm : P.p ≫ f ≫ Q.p = f) : (homMk f comm).hom.f = f := (rfl)

/-- Two morphisms in `DaggerKaroubi C` are equal if their underlying morphisms in `C` are equal. -/
theorem hom_ext {P Q : DaggerKaroubi C} {f g : P ⟶ Q} (h : f.hom.f = g.hom.f) : f = g :=
  ObjectProperty.hom_ext _ (Idempotents.Karoubi.hom_ext _ _ h)

/-- Underlying morphism of the identity in `DaggerKaroubi C`. -/
theorem id_hom_f (P : DaggerKaroubi C) : (𝟙 P : P ⟶ P).hom.f = P.p := (rfl)

/-- Underlying morphism of a composition in `DaggerKaroubi C`. -/
@[simp] theorem comp_hom_f {P Q R : DaggerKaroubi C} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).hom.f = f.hom.f ≫ g.hom.f := (rfl)

/-- Precomposing an underlying morphism in `DaggerKaroubi C` with the source projection leaves it
unchanged. -/
@[reassoc] theorem p_comp {P Q : DaggerKaroubi C} (f : P ⟶ Q) :
    P.p ≫ f.hom.f = f.hom.f :=
  Idempotents.Karoubi.p_comp f.hom

/-- Postcomposing an underlying morphism in `DaggerKaroubi C` with the target projection leaves it
unchanged. -/
@[reassoc] theorem comp_p {P Q : DaggerKaroubi C} (f : P ⟶ Q) :
    f.hom.f ≫ Q.p = f.hom.f :=
  Idempotents.Karoubi.comp_p f.hom

/-- The dagger structure on `DaggerKaroubi C`, acting on underlying morphisms via the dagger
of `C`. -/
instance instDaggerCategory : DaggerCategory (DaggerKaroubi C) where
  dagger {P Q} f :=
    homMk (dagger f.hom.f) (by
      calc Q.p ≫ dagger f.hom.f ≫ P.p
          = dagger Q.p ≫ dagger f.hom.f ≫ dagger P.p := by rw [P.dagger_p, Q.dagger_p]
        _ = dagger (P.p ≫ f.hom.f ≫ Q.p) := by rw [dagger_comp, dagger_comp, Category.assoc]
        _ = dagger f.hom.f := by rw [f.hom.comm])
  dagger_id P := hom_ext P.dagger_p
  dagger_comp f g := hom_ext (dagger_comp f.hom.f g.hom.f)
  dagger_dagger f := hom_ext (dagger_dagger f.hom.f)

/-- Underlying morphism of a dagger in `DaggerKaroubi C`. -/
@[simp] theorem dagger_hom_f {P Q : DaggerKaroubi C} (f : P ⟶ Q) :
    (dagger f).hom.f = dagger f.hom.f := (rfl)

/-- Underlying morphism of a sum in `DaggerKaroubi C`. -/
@[simp] theorem add_hom_f [Preadditive C] {P Q : DaggerKaroubi C} (f g : P ⟶ Q) :
    (f + g).hom.f = f.hom.f + g.hom.f := (rfl)

/-- Underlying morphism of zero in `DaggerKaroubi C`. -/
@[simp] theorem zero_hom_f [Preadditive C] {P Q : DaggerKaroubi C} :
    (0 : P ⟶ Q).hom.f = 0 := (rfl)

/-- Underlying morphism of negation in `DaggerKaroubi C`. -/
@[simp] theorem neg_hom_f [Preadditive C] {P Q : DaggerKaroubi C} (f : P ⟶ Q) :
    (-f).hom.f = -f.hom.f := (rfl)

/-- Underlying morphism of subtraction in `DaggerKaroubi C`. -/
theorem sub_hom_f [Preadditive C] {P Q : DaggerKaroubi C} (f g : P ⟶ Q) :
    (f - g).hom.f = f.hom.f - g.hom.f := by
  rw [sub_eq_add_neg, add_hom_f, neg_hom_f, sub_eq_add_neg]

/-- Underlying morphism of a finite sum in `DaggerKaroubi C`. -/
@[simp] theorem sum_hom_f [Preadditive C] {P Q : DaggerKaroubi C} {α : Type*} (s : Finset α)
    (f : α → (P ⟶ Q)) :
    (∑ a ∈ s, f a).hom.f = ∑ a ∈ s, (f a).hom.f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- Underlying morphism of a scalar multiple in `DaggerKaroubi C`. -/
theorem smul_hom_f [Preadditive C] {R : Type w} [Semiring R] [Linear R C]
    {P Q : DaggerKaroubi C} (r : R) (f : P ⟶ Q) :
    (r • f).hom.f = r • f.hom.f := (rfl)

/-- The dagger Karoubi completion of a preadditive dagger category is a preadditive dagger
category. -/
instance instDaggerPreadditive [Preadditive C] [DaggerPreadditive C] :
    DaggerPreadditive (DaggerKaroubi C) where
  dagger_add f g := hom_ext (dagger_add f.hom.f g.hom.f)

/-- The dagger Karoubi completion of a star-linear dagger category is a star-linear dagger
category. -/
instance instDaggerLinear [Preadditive C] {R : Type w} [Semiring R]
    [StarRing R] [Linear R C] [DaggerLinear R C] : DaggerLinear R (DaggerKaroubi C) where
  dagger_smul r f := hom_ext (dagger_smul r f.hom.f)

variable (C)

/-- The full inclusion `DaggerKaroubi C ⥤ Idempotents.Karoubi C` forgetting self-adjointness. -/
abbrev forget : DaggerKaroubi C ⥤ Idempotents.Karoubi C :=
  (isDaggerProjectionProperty C).ι

/-- The canonical fully faithful dagger-preserving embedding `C ⥤ DaggerKaroubi C`. -/
@[expose] def toDaggerKaroubi : C ⥤ DaggerKaroubi C :=
  (isDaggerProjectionProperty C).lift (Idempotents.toKaroubi C) (fun X => dagger_id X)

variable {C}

/-- Object action of `toDaggerKaroubi C` on underlying objects. -/
@[simp] theorem toDaggerKaroubi_obj_X (X : C) : ((toDaggerKaroubi C).obj X).X = X := (rfl)

/-- Object action of `toDaggerKaroubi C` on underlying projections. -/
@[simp] theorem toDaggerKaroubi_obj_p (X : C) : ((toDaggerKaroubi C).obj X).p = 𝟙 X := (rfl)

/-- Morphism action of `toDaggerKaroubi C` on underlying morphisms. -/
@[simp] theorem toDaggerKaroubi_map_hom_f {X Y : C} (f : X ⟶ Y) :
    ((toDaggerKaroubi C).map f).hom.f = f := (rfl)

variable (C)

/-- `toDaggerKaroubi C` is full. -/
instance instFullToDaggerKaroubi : (toDaggerKaroubi C).Full where
  map_surjective f := ⟨f.hom.f, hom_ext rfl⟩

/-- `toDaggerKaroubi C` is faithful. -/
instance instFaithfulToDaggerKaroubi : (toDaggerKaroubi C).Faithful where
  map_injective h := congrArg (fun g => g.hom.f) h

/-- `toDaggerKaroubi C` is additive when `C` is preadditive. -/
instance instAdditiveToDaggerKaroubi [Preadditive C] : (toDaggerKaroubi C).Additive where
  map_add := hom_ext rfl

/-- `toDaggerKaroubi C` preserves daggers. -/
instance instPreservesDaggerToDaggerKaroubi : (toDaggerKaroubi C).PreservesDagger where
  map_dagger _ := hom_ext rfl

/-- `toDaggerKaroubi C` is `R`-linear when `C` is `R`-linear. -/
instance instLinearToDaggerKaroubi [Preadditive C] {R : Type w} [Semiring R] [Linear R C] :
    (toDaggerKaroubi C).Linear R where
  map_smul _ _ := hom_ext rfl

/-- Composing `toDaggerKaroubi C` with `forget C` recovers Mathlib's `Idempotents.toKaroubi C`. -/
def toDaggerKaroubiCompForgetIso : toDaggerKaroubi C ⋙ forget C ≅ Idempotents.toKaroubi C :=
  Iso.refl _

variable {C}

/-- The canonical isometric inclusion `P ⟶ (toDaggerKaroubi C).obj P.X`. -/
def decompIdIncl (P : DaggerKaroubi C) : P ⟶ (toDaggerKaroubi C).obj P.X :=
  homMk P.p (by change P.p ≫ P.p ≫ 𝟙 P.X = P.p; simp)

/-- The canonical projection `(toDaggerKaroubi C).obj P.X ⟶ P`, adjoint to `decompIdIncl P`. -/
def decompIdProj (P : DaggerKaroubi C) : (toDaggerKaroubi C).obj P.X ⟶ P :=
  homMk P.p (by change 𝟙 P.X ≫ P.p ≫ P.p = P.p; simp)

/-- Underlying morphism of `decompIdIncl P`. -/
@[simp] theorem decompIdIncl_hom_f (P : DaggerKaroubi C) : (decompIdIncl P).hom.f = P.p := (rfl)

/-- Underlying morphism of `decompIdProj P`. -/
@[simp] theorem decompIdProj_hom_f (P : DaggerKaroubi C) : (decompIdProj P).hom.f = P.p := (rfl)

/-- The dagger of `decompIdIncl P` is `decompIdProj P`. -/
@[simp] theorem dagger_decompIdIncl (P : DaggerKaroubi C) :
    dagger (decompIdIncl P) = decompIdProj P :=
  hom_ext P.dagger_p

/-- The dagger of `decompIdProj P` is `decompIdIncl P`. -/
@[simp] theorem dagger_decompIdProj (P : DaggerKaroubi C) :
    dagger (decompIdProj P) = decompIdIncl P :=
  hom_ext P.dagger_p

/-- `decompIdIncl P ≫ decompIdProj P = 𝟙 P`. -/
@[reassoc (attr := simp)] theorem decompId (P : DaggerKaroubi C) :
    decompIdIncl P ≫ decompIdProj P = 𝟙 P :=
  hom_ext P.idem

/-- `decompIdIncl P` is a dagger isometry. -/
theorem isDaggerIsometry_decompIdIncl (P : DaggerKaroubi C) :
    IsDaggerIsometry (decompIdIncl P) := by
  rw [isDaggerIsometry_iff, dagger_decompIdIncl, decompId]

/-- `decompIdProj P ≫ decompIdIncl P = (toDaggerKaroubi C).map P.p`. -/
@[reassoc (attr := simp)] theorem decomp_p (P : DaggerKaroubi C) :
    decompIdProj P ≫ decompIdIncl P = (toDaggerKaroubi C).map P.p :=
  hom_ext P.idem

/-- For every `f : P ⟶ Q`, composing with `decompIdIncl Q` factors through `decompIdIncl P`. -/
@[reassoc] theorem comp_decompIdIncl {P Q : DaggerKaroubi C} (f : P ⟶ Q) :
    f ≫ decompIdIncl Q = decompIdIncl P ≫ (toDaggerKaroubi C).map f.hom.f :=
  hom_ext (by
    change f.hom.f ≫ Q.p = P.p ≫ f.hom.f
    rw [comp_p, p_comp])

/-- The canonical dagger splitting of `(toDaggerKaroubi C).map P.p` by `P`. -/
@[expose] def canonicalSplitting (P : DaggerKaroubi C) :
    DaggerSplitting ((toDaggerKaroubi C).map P.p) where
  obj := P
  hom := decompIdIncl P
  isometry := by rw [dagger_decompIdIncl, decompId]
  range := by rw [dagger_decompIdIncl, decomp_p]

/-- Every dagger projection in `DaggerKaroubi C` admits an explicit dagger splitting. -/
@[expose] def splittingOfProjection {P : DaggerKaroubi C} {q : P ⟶ P}
    (hq : IsDaggerProjection q) : DaggerSplitting q :=
  let hq' : IsDaggerProjection q.hom.f :=
    (isDaggerProjection_iff _).mpr
      ⟨congrArg (fun f => f.hom.f) hq.idem, congrArg (fun f => f.hom.f) hq.dagger_eq⟩
  { obj := mk P.X q.hom.f hq'
    hom := homMk q.hom.f (by
      change q.hom.f ≫ q.hom.f ≫ P.p = q.hom.f
      rw [comp_p, hq'.idem])
    isometry := hom_ext (by
      change q.hom.f ≫ dagger q.hom.f = q.hom.f
      rw [hq'.dagger_eq, hq'.idem])
    range := hom_ext (by
      change dagger q.hom.f ≫ q.hom.f = q.hom.f
      rw [hq'.dagger_eq, hq'.idem]) }

/-- The dagger Karoubi completion is always dagger idempotent complete. -/
instance instIsDaggerIdempotentComplete : IsDaggerIdempotentComplete (DaggerKaroubi C) where
  daggerProjections_split _ _ hq := (splittingOfProjection hq).isDaggerSplit

end Basic

section Preadditive

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [DaggerCategory C]

section Complement

variable [DaggerPreadditive C]

/-- The orthogonal complement of `P : DaggerKaroubi C`, given by the dagger projection
`𝟙 P.X - P.p`. -/
@[expose] def complement (P : DaggerKaroubi C) : DaggerKaroubi C :=
  mk P.X (𝟙 P.X - P.p) P.isDaggerProjection.one_sub

/-- Underlying object of `P.complement`. -/
@[simp] theorem complement_X (P : DaggerKaroubi C) : P.complement.X = P.X := (rfl)

/-- Underlying projection of `P.complement`. -/
@[simp] theorem complement_p (P : DaggerKaroubi C) : P.complement.p = 𝟙 P.X - P.p := (rfl)

private def complementIncl (P : DaggerKaroubi C) :
    P.complement ⟶ (toDaggerKaroubi C).obj P.X :=
  homMk (𝟙 P.X - P.p) (by
    change (𝟙 P.X - P.p) ≫ (𝟙 P.X - P.p) ≫ 𝟙 P.X = 𝟙 P.X - P.p
    rw [Category.comp_id, P.isDaggerProjection.one_sub.idem])

private def complementProj (P : DaggerKaroubi C) :
    (toDaggerKaroubi C).obj P.X ⟶ P.complement :=
  homMk (𝟙 P.X - P.p) (by
    change 𝟙 P.X ≫ (𝟙 P.X - P.p) ≫ (𝟙 P.X - P.p) = 𝟙 P.X - P.p
    rw [Category.id_comp, P.isDaggerProjection.one_sub.idem])

private def complementBicone (P : DaggerKaroubi C) :
    BinaryBicone P P.complement where
  pt := (toDaggerKaroubi C).obj P.X
  fst := decompIdProj P
  snd := complementProj P
  inl := decompIdIncl P
  inr := complementIncl P
  inl_fst := decompId P
  inl_snd := hom_ext (by
    change P.p ≫ (𝟙 P.X - P.p) = 0
    simp [Preadditive.comp_sub])
  inr_fst := hom_ext (by
    change (𝟙 P.X - P.p) ≫ P.p = 0
    simp [Preadditive.sub_comp])
  inr_snd := hom_ext P.isDaggerProjection.one_sub.idem

private theorem complementBicone_isOrthogonal (P : DaggerKaroubi C) :
    (complementBicone P).IsOrthogonal :=
  (BinaryBicone.isOrthogonal_iff _).mpr
    ⟨dagger_decompIdIncl P, hom_ext P.isDaggerProjection.one_sub.dagger_eq⟩

private theorem complementBicone_total (P : DaggerKaroubi C) :
    (complementBicone P).fst ≫ (complementBicone P).inl +
      (complementBicone P).snd ≫ (complementBicone P).inr =
      𝟙 (complementBicone P).pt := by
  refine hom_ext ?_
  change P.p ≫ P.p + (𝟙 P.X - P.p) ≫ (𝟙 P.X - P.p) = 𝟙 P.X
  rw [P.idem, P.isDaggerProjection.one_sub.idem, add_sub_cancel]

/-- Every `P : DaggerKaroubi C` has a binary orthogonal biproduct with its orthogonal complement. -/
instance hasBinaryDaggerBiproduct_complement (P : DaggerKaroubi C) :
    HasBinaryDaggerBiproduct P P.complement :=
  hasBinaryDaggerBiproduct_of_total (complementBicone P) (complementBicone_isOrthogonal P)
    (complementBicone_total P)

/-- Canonical unitary isomorphism `daggerBiprod P P.complement ≅ (toDaggerKaroubi C).obj P.X`. -/
noncomputable def decomposition (P : DaggerKaroubi C) :
    daggerBiprod P P.complement ≅ (toDaggerKaroubi C).obj P.X where
  hom := daggerBiprod.desc (decompIdIncl P) (complementIncl P)
  inv := daggerBiprod.lift (decompIdProj P) (complementProj P)
  hom_inv_id := by
    apply daggerBiprod.hom_ext'
    · apply daggerBiprod.hom_ext
      · simp only [Category.assoc, Category.comp_id, daggerBiprod.inl_desc_assoc,
          daggerBiprod.lift_fst, decompId, BinaryBicone.inl_fst]
      · simp only [Category.assoc, Category.comp_id, daggerBiprod.inl_desc_assoc,
          daggerBiprod.lift_snd, BinaryBicone.inl_snd]
        exact hom_ext (by change P.p ≫ (𝟙 P.X - P.p) = 0; simp [Preadditive.comp_sub])
    · apply daggerBiprod.hom_ext
      · simp only [Category.assoc, Category.comp_id, daggerBiprod.inr_desc_assoc,
          daggerBiprod.lift_fst, BinaryBicone.inr_fst]
        exact hom_ext (by change (𝟙 P.X - P.p) ≫ P.p = 0; simp [Preadditive.sub_comp])
      · simp only [Category.assoc, Category.comp_id, daggerBiprod.inr_desc_assoc,
          daggerBiprod.lift_snd, BinaryBicone.inr_snd]
        exact hom_ext P.isDaggerProjection.one_sub.idem
  inv_hom_id := by
    rw [daggerBiprod.lift_desc]
    exact complementBicone_total P

/-- The orthogonal decomposition isomorphism `decomposition P` is unitary. -/
theorem isUnitary_decomposition (P : DaggerKaroubi C) : IsUnitary (decomposition P).hom :=
  (decomposition P).isUnitary_hom_iff.mpr (by
    change dagger (daggerBiprod.desc (decompIdIncl P) (complementIncl P)) =
      daggerBiprod.lift (decompIdProj P) (complementProj P)
    rw [daggerBiprod.dagger_desc, dagger_decompIdIncl]
    congr 1
    exact hom_ext P.isDaggerProjection.one_sub.dagger_eq)

end Complement

section Biproducts

variable [HasFiniteDaggerBiproducts C]

private theorem isDaggerProjection_map {J : Type} [Finite J] (F : J → DaggerKaroubi C) :
    IsDaggerProjection (daggerBiproduct.map fun j => (F j).p) :=
  (isDaggerProjection_iff _).mpr
    ⟨by
        apply daggerBiproduct.hom_ext
        intro j
        simp only [Category.assoc, daggerBiproduct.map_π, daggerBiproduct.map_π_assoc, idem],
      by
        rw [daggerBiproduct.dagger_map]
        congr 1
        funext j
        exact (F j).dagger_p⟩

private noncomputable def bicone {J : Type} [Finite J] (F : J → DaggerKaroubi C) : Bicone F where
  pt := mk (daggerBiproduct fun j => (F j).X) (daggerBiproduct.map fun j => (F j).p)
    (isDaggerProjection_map F)
  π j := homMk
    ((daggerBiproduct.map fun k => (F k).p) ≫ daggerBiproduct.π (fun k => (F k).X) j)
    (by
      change (daggerBiproduct.map fun k => (F k).p) ≫
          ((daggerBiproduct.map fun k => (F k).p) ≫ daggerBiproduct.π (fun k => (F k).X) j) ≫
            (F j).p =
        (daggerBiproduct.map fun k => (F k).p) ≫ daggerBiproduct.π (fun k => (F k).X) j
      simp only [Category.assoc, daggerBiproduct.map_π, daggerBiproduct.map_π_assoc, idem])
  ι j := homMk
    (daggerBiproduct.ι (fun k => (F k).X) j ≫ daggerBiproduct.map fun k => (F k).p)
    (by
      change (F j).p ≫ (daggerBiproduct.ι (fun k => (F k).X) j ≫
          daggerBiproduct.map fun k => (F k).p) ≫
          (daggerBiproduct.map fun k => (F k).p) =
        daggerBiproduct.ι (fun k => (F k).X) j ≫ daggerBiproduct.map fun k => (F k).p
      simp only [Category.assoc, daggerBiproduct.ι_map, idem_assoc])
  ι_π j j' := by
    classical
    refine hom_ext ?_
    change (daggerBiproduct.ι (fun k => (F k).X) j ≫ daggerBiproduct.map fun k => (F k).p) ≫
        (daggerBiproduct.map fun k => (F k).p) ≫ daggerBiproduct.π (fun k => (F k).X) j' = _
    by_cases h : j = j'
    · subst h
      simp [daggerBiproduct.map_π]
    · simp [h, daggerBiproduct.map_π, daggerBiproduct.ι_π_ne_assoc _ h]

private theorem bicone_isOrthogonal {J : Type} [Finite J] (F : J → DaggerKaroubi C) :
    (bicone F).IsOrthogonal :=
  (Bicone.isOrthogonal_iff _).mpr fun j => hom_ext (by
    change dagger (daggerBiproduct.ι (fun k => (F k).X) j ≫ daggerBiproduct.map fun k => (F k).p) =
      (daggerBiproduct.map fun k => (F k).p) ≫ daggerBiproduct.π (fun k => (F k).X) j
    rw [dagger_comp, (isDaggerProjection_map F).dagger_eq, daggerBiproduct.dagger_ι])

private theorem bicone_total {J : Type} [Fintype J] (F : J → DaggerKaroubi C) :
    ∑ j : J, (bicone F).π j ≫ (bicone F).ι j = 𝟙 (bicone F).pt := by
  refine hom_ext ?_
  rw [sum_hom_f]
  change (∑ j : J, ((daggerBiproduct.map fun k => (F k).p) ≫
        daggerBiproduct.π (fun k => (F k).X) j) ≫
      daggerBiproduct.ι (fun k => (F k).X) j ≫ (daggerBiproduct.map fun k => (F k).p)) =
    (daggerBiproduct.map fun k => (F k).p)
  have hsum :
      (∑ j : J, ((daggerBiproduct.map fun k => (F k).p) ≫
          daggerBiproduct.π (fun k => (F k).X) j) ≫
        daggerBiproduct.ι (fun k => (F k).X) j ≫ (daggerBiproduct.map fun k => (F k).p)) =
      (daggerBiproduct.map fun k => (F k).p) ≫
        (∑ j : J, daggerBiproduct.π (fun k => (F k).X) j ≫
          daggerBiproduct.ι (fun k => (F k).X) j) ≫
        (daggerBiproduct.map fun k => (F k).p) := by
    simp only [Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
  rw [hsum, daggerBiproduct.total, Category.id_comp, (isDaggerProjection_map F).idem]

/-- If `C` is preadditive with finite orthogonal biproducts, then `DaggerKaroubi C` also has
finite orthogonal biproducts. -/
instance instHasFiniteDaggerBiproducts : HasFiniteDaggerBiproducts (DaggerKaroubi C) where
  out _ :=
    { has_daggerBiproduct := fun F =>
        hasDaggerBiproduct_of_total (bicone F) (bicone_isOrthogonal F) (bicone_total F) }

/-- If `C` is preadditive with finite orthogonal biproducts, then `DaggerKaroubi C` also has
binary orthogonal biproducts. -/
instance instHasBinaryDaggerBiproducts : HasBinaryDaggerBiproducts (DaggerKaroubi C) :=
  hasBinaryDaggerBiproducts_of_finite_daggerBiproducts (DaggerKaroubi C)

end Biproducts

end Preadditive

section UniversalProperty

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]

/-- Extension of a functor `F : C ⥤ D` to `DaggerKaroubi C ⥤ D` using an explicit choice of
dagger splittings `s P` for every `F.map P.p`. -/
@[expose] def liftWithSplittings (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) :
    DaggerKaroubi C ⥤ D where
  obj P := (s P).obj
  map {P Q} f := (s P).hom ≫ F.map f.hom.f ≫ dagger (s Q).hom
  map_id P := by
    change (s P).hom ≫ F.map P.p ≫ dagger (s P).hom = 𝟙 (s P).obj
    calc (s P).hom ≫ F.map P.p ≫ dagger (s P).hom
        = (s P).hom ≫ (dagger (s P).hom ≫ (s P).hom) ≫ dagger (s P).hom :=
          (congrArg (fun m => (s P).hom ≫ m ≫ dagger (s P).hom) (s P).range).symm
      _ = ((s P).hom ≫ dagger (s P).hom) ≫ ((s P).hom ≫ dagger (s P).hom) := by
          simp only [Category.assoc]
      _ = 𝟙 (s P).obj := by rw [(s P).isometry, Category.id_comp]
  map_comp {P Q R} f g := by
    change (s P).hom ≫ F.map (f.hom.f ≫ g.hom.f) ≫ dagger (s R).hom =
      ((s P).hom ≫ F.map f.hom.f ≫ dagger (s Q).hom) ≫
        (s Q).hom ≫ F.map g.hom.f ≫ dagger (s R).hom
    symm
    calc ((s P).hom ≫ F.map f.hom.f ≫ dagger (s Q).hom) ≫
          (s Q).hom ≫ F.map g.hom.f ≫ dagger (s R).hom
        = (s P).hom ≫ F.map f.hom.f ≫ (dagger (s Q).hom ≫ (s Q).hom) ≫
            F.map g.hom.f ≫ dagger (s R).hom := by simp only [Category.assoc]
      _ = (s P).hom ≫ F.map (f.hom.f ≫ Q.p ≫ g.hom.f) ≫ dagger (s R).hom := by
          rw [(s Q).range, F.map_comp, F.map_comp]
          simp only [Category.assoc]
      _ = (s P).hom ≫ F.map (f.hom.f ≫ g.hom.f) ≫ dagger (s R).hom := by simp

/-- Object action of `liftWithSplittings F s`. -/
@[simp] theorem liftWithSplittings_obj (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) (P : DaggerKaroubi C) :
    (liftWithSplittings F s).obj P = (s P).obj := (rfl)

/-- Morphism action of `liftWithSplittings F s`. -/
@[simp] theorem liftWithSplittings_map (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) {P Q : DaggerKaroubi C} (f : P ⟶ Q) :
    (liftWithSplittings F s).map f = (s P).hom ≫ F.map f.hom.f ≫ dagger (s Q).hom := (rfl)

/-- `liftWithSplittings F s` preserves daggers when `F` does. -/
instance instPreservesDaggerLiftWithSplittings (F : C ⥤ D) [F.PreservesDagger]
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) :
    (liftWithSplittings F s).PreservesDagger where
  map_dagger {P Q} f := by
    change (s Q).hom ≫ F.map (dagger f.hom.f) ≫ dagger (s P).hom =
      dagger ((s P).hom ≫ F.map f.hom.f ≫ dagger (s Q).hom)
    simp only [F.map_dagger, dagger_comp, dagger_dagger, Category.assoc]

/-- `liftWithSplittings F s` is additive when `F` is additive. -/
instance instAdditiveLiftWithSplittings [Preadditive C] [Preadditive D] (F : C ⥤ D)
    [F.Additive] (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) :
    (liftWithSplittings F s).Additive where
  map_add := by
    intro P Q f g
    change (s P).hom ≫ F.map (f.hom.f + g.hom.f) ≫ dagger (s Q).hom =
      (s P).hom ≫ F.map f.hom.f ≫ dagger (s Q).hom + (s P).hom ≫ F.map g.hom.f ≫ dagger (s Q).hom
    simp only [F.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- `liftWithSplittings F s` is `R`-linear when `F` is `R`-linear. -/
instance instLinearLiftWithSplittings [Preadditive C] [Preadditive D] {R : Type w} [Semiring R]
    [Linear R C] [Linear R D] (F : C ⥤ D) [F.Linear R]
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) :
    (liftWithSplittings F s).Linear R where
  map_smul {P Q} f r := by
    change (s P).hom ≫ F.map (r • f.hom.f) ≫ dagger (s Q).hom =
      r • ((s P).hom ≫ F.map f.hom.f ≫ dagger (s Q).hom)
    simp only [F.map_smul, Linear.smul_comp, Linear.comp_smul]

/-- Canonical unitary natural isomorphism `toDaggerKaroubi C ⋙ liftWithSplittings F s ≅ F`. -/
def toDaggerKaroubiCompLiftWithSplittingsIso (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) :
    toDaggerKaroubi C ⋙ liftWithSplittings F s ≅ F :=
  NatIso.ofComponents
    (fun X =>
      { hom := (s ((toDaggerKaroubi C).obj X)).hom
        inv := dagger (s ((toDaggerKaroubi C).obj X)).hom
        hom_inv_id := (s _).isometry
        inv_hom_id := (s _).range.trans (F.map_id X) })
    fun {X Y} f => by
      have hY :
          dagger (s ((toDaggerKaroubi C).obj Y)).hom ≫ (s ((toDaggerKaroubi C).obj Y)).hom =
            𝟙 (F.obj ((toDaggerKaroubi C).obj Y).X) :=
        (s ((toDaggerKaroubi C).obj Y)).range.trans (F.map_id Y)
      change ((s ((toDaggerKaroubi C).obj X)).hom ≫ F.map ((toDaggerKaroubi C).map f).hom.f ≫
          dagger (s ((toDaggerKaroubi C).obj Y)).hom) ≫
        (s ((toDaggerKaroubi C).obj Y)).hom =
        (s ((toDaggerKaroubi C).obj X)).hom ≫ F.map ((toDaggerKaroubi C).map f).hom.f
      rw [Category.assoc, Category.assoc, hY, Category.comp_id]

/-- Forward component of `toDaggerKaroubiCompLiftWithSplittingsIso F s`. -/
@[simp] theorem toDaggerKaroubiCompLiftWithSplittingsIso_hom_app (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) (X : C) :
    (toDaggerKaroubiCompLiftWithSplittingsIso F s).hom.app X =
      (s ((toDaggerKaroubi C).obj X)).hom := (rfl)

/-- Inverse component of `toDaggerKaroubiCompLiftWithSplittingsIso F s`. -/
@[simp] theorem toDaggerKaroubiCompLiftWithSplittingsIso_inv_app (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) (X : C) :
    (toDaggerKaroubiCompLiftWithSplittingsIso F s).inv.app X =
      dagger (s ((toDaggerKaroubi C).obj X)).hom := (rfl)

/-- Every component of `toDaggerKaroubiCompLiftWithSplittingsIso F s` is unitary. -/
theorem isUnitary_toDaggerKaroubiCompLiftWithSplittingsIso (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) (X : C) :
    IsUnitary ((toDaggerKaroubiCompLiftWithSplittingsIso F s).app X).hom :=
  ((toDaggerKaroubiCompLiftWithSplittingsIso F s).app X).isUnitary_hom_iff.mpr rfl

/-- Independence of chosen splittings: two families of splittings of `F.map P.p` produce
canonically unitarily naturally isomorphic extensions `DaggerKaroubi C ⥤ D`. -/
def liftWithSplittingsIso (F : C ⥤ D)
    (s₁ s₂ : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) :
    liftWithSplittings F s₁ ≅ liftWithSplittings F s₂ :=
  NatIso.ofComponents (fun P => (s₁ P).iso (s₂ P)) fun {P Q} f => by
    change ((s₁ P).hom ≫ F.map f.hom.f ≫ dagger (s₁ Q).hom) ≫ ((s₁ Q).iso (s₂ Q)).hom =
      ((s₁ P).iso (s₂ P)).hom ≫ (s₂ P).hom ≫ F.map f.hom.f ≫ dagger (s₂ Q).hom
    rw [DaggerSplitting.iso_hom, DaggerSplitting.iso_hom]
    have hL :
        ((s₁ P).hom ≫ F.map f.hom.f ≫ dagger (s₁ Q).hom) ≫ (s₁ Q).hom ≫ dagger (s₂ Q).hom =
          (s₁ P).hom ≫ F.map f.hom.f ≫ dagger (s₂ Q).hom := by
      rw [Category.assoc, Category.assoc, (s₁ Q).range_assoc, ← F.map_comp_assoc, comp_p]
    have hR :
        ((s₁ P).hom ≫ dagger (s₂ P).hom) ≫ (s₂ P).hom ≫ F.map f.hom.f ≫ dagger (s₂ Q).hom =
          (s₁ P).hom ≫ F.map f.hom.f ≫ dagger (s₂ Q).hom := by
      rw [Category.assoc, (s₂ P).range_assoc, ← F.map_comp_assoc, p_comp]
    exact hL.trans hR.symm

/-- Every component of `liftWithSplittingsIso F s₁ s₂` is unitary. -/
theorem isUnitary_liftWithSplittingsIso (F : C ⥤ D)
    (s₁ s₂ : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) (P : DaggerKaroubi C) :
    IsUnitary ((liftWithSplittingsIso F s₁ s₂).app P).hom :=
  (s₁ P).isUnitary_iso (s₂ P)

/-- `liftWithSplittingsIso` intertwines the canonical restriction isomorphisms on
`toDaggerKaroubi C`. -/
theorem liftWithSplittingsIso_hom_app_toDaggerKaroubi (F : C ⥤ D)
    (s₁ s₂ : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p)) (X : C) :
    (liftWithSplittingsIso F s₁ s₂).hom.app ((toDaggerKaroubi C).obj X) ≫
      (toDaggerKaroubiCompLiftWithSplittingsIso F s₂).hom.app X =
      (toDaggerKaroubiCompLiftWithSplittingsIso F s₁).hom.app X := by
  have hX :
      dagger (s₂ ((toDaggerKaroubi C).obj X)).hom ≫ (s₂ ((toDaggerKaroubi C).obj X)).hom =
        𝟙 (F.obj ((toDaggerKaroubi C).obj X).X) :=
    (s₂ ((toDaggerKaroubi C).obj X)).range.trans (F.map_id X)
  change ((s₁ ((toDaggerKaroubi C).obj X)).iso (s₂ ((toDaggerKaroubi C).obj X))).hom ≫
      (s₂ ((toDaggerKaroubi C).obj X)).hom =
    (s₁ ((toDaggerKaroubi C).obj X)).hom
  rw [DaggerSplitting.iso_hom, Category.assoc, hX, Category.comp_id]

/-- Any functor `L : DaggerKaroubi C ⥤ D` equipped with `α : toDaggerKaroubi C ⋙ L ≅ F` is
canonically isomorphic to `liftWithSplittings F s`. -/
def liftWithSplittingsUnique (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p))
    (L : DaggerKaroubi C ⥤ D) (α : toDaggerKaroubi C ⋙ L ≅ F) :
    L ≅ liftWithSplittings F s :=
  NatIso.ofComponents
    (fun P =>
      { hom := L.map (decompIdIncl P) ≫ α.hom.app P.X ≫ dagger (s P).hom
        inv := (s P).hom ≫ α.inv.app P.X ≫ L.map (decompIdProj P)
        hom_inv_id := by
          have hnat :
              L.map ((toDaggerKaroubi C).map P.p) ≫ α.hom.app P.X = α.hom.app P.X ≫ F.map P.p :=
            α.hom.naturality P.p
          calc (L.map (decompIdIncl P) ≫ α.hom.app P.X ≫ dagger (s P).hom) ≫
                (s P).hom ≫ α.inv.app P.X ≫ L.map (decompIdProj P)
              = L.map (decompIdIncl P) ≫ (α.hom.app P.X ≫ F.map P.p) ≫
                  α.inv.app P.X ≫ L.map (decompIdProj P) := by
                simp only [Category.assoc, (s P).range_assoc]
            _ = L.map (decompIdIncl P) ≫ (L.map ((toDaggerKaroubi C).map P.p) ≫ α.hom.app P.X) ≫
                  α.inv.app P.X ≫ L.map (decompIdProj P) := by rw [← hnat]
            _ = L.map (decompIdIncl P ≫ (toDaggerKaroubi C).map P.p ≫ decompIdProj P) := by
                simp only [Category.assoc, Iso.hom_inv_id_app_assoc, L.map_comp]
            _ = L.map (𝟙 P) := by
                congr 1; exact hom_ext (by change P.p ≫ P.p ≫ P.p = P.p; simp)
            _ = 𝟙 (L.obj P) := L.map_id P
        inv_hom_id := by
          have hnat :
              L.map ((toDaggerKaroubi C).map P.p) ≫ α.hom.app P.X = α.hom.app P.X ≫ F.map P.p :=
            α.hom.naturality P.p
          calc ((s P).hom ≫ α.inv.app P.X ≫ L.map (decompIdProj P)) ≫
                L.map (decompIdIncl P) ≫ α.hom.app P.X ≫ dagger (s P).hom
              = (s P).hom ≫ α.inv.app P.X ≫ (L.map ((toDaggerKaroubi C).map P.p) ≫
                  α.hom.app P.X) ≫ dagger (s P).hom := by
                simp only [Category.assoc, ← L.map_comp_assoc, decomp_p]
            _ = (s P).hom ≫ α.inv.app P.X ≫ α.hom.app P.X ≫ F.map P.p ≫ dagger (s P).hom := by
                rw [hnat, Category.assoc]
            _ = (s P).hom ≫ F.map P.p ≫ dagger (s P).hom := by rw [Iso.inv_hom_id_app_assoc]
            _ = 𝟙 (s P).obj := (liftWithSplittings F s).map_id P })
    fun {P Q} f => by
      have hnat :
          L.map ((toDaggerKaroubi C).map f.hom.f) ≫ α.hom.app Q.X =
            α.hom.app P.X ≫ F.map f.hom.f :=
        α.hom.naturality f.hom.f
      change L.map f ≫ L.map (decompIdIncl Q) ≫ α.hom.app Q.X ≫ dagger (s Q).hom =
        (L.map (decompIdIncl P) ≫ α.hom.app P.X ≫ dagger (s P).hom) ≫
          (s P).hom ≫ F.map f.hom.f ≫ dagger (s Q).hom
      have hL :
          L.map f ≫ L.map (decompIdIncl Q) ≫ α.hom.app Q.X ≫ dagger (s Q).hom =
            L.map (decompIdIncl P) ≫ α.hom.app P.X ≫ F.map f.hom.f ≫ dagger (s Q).hom := by
        rw [← L.map_comp_assoc, comp_decompIdIncl, L.map_comp, Category.assoc, reassoc_of% hnat]
      have hR :
          (L.map (decompIdIncl P) ≫ α.hom.app P.X ≫ dagger (s P).hom) ≫
              (s P).hom ≫ F.map f.hom.f ≫ dagger (s Q).hom =
            L.map (decompIdIncl P) ≫ α.hom.app P.X ≫ F.map f.hom.f ≫ dagger (s Q).hom := by
        rw [Category.assoc, Category.assoc, (s P).range_assoc, ← F.map_comp_assoc, p_comp]
      exact hL.trans hR.symm

/-- Forward component of `liftWithSplittingsUnique F s L α`. -/
@[simp] theorem liftWithSplittingsUnique_hom_app (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p))
    (L : DaggerKaroubi C ⥤ D) (α : toDaggerKaroubi C ⋙ L ≅ F)
    (P : DaggerKaroubi C) :
    (liftWithSplittingsUnique F s L α).hom.app P =
      L.map (decompIdIncl P) ≫ α.hom.app P.X ≫ dagger (s P).hom := (rfl)

/-- Restricting `liftWithSplittingsUnique F s L α` along `toDaggerKaroubi C` recovers `α`. -/
theorem liftWithSplittingsUnique_hom_app_toDaggerKaroubi (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p))
    (L : DaggerKaroubi C ⥤ D) (α : toDaggerKaroubi C ⋙ L ≅ F) (X : C) :
    (liftWithSplittingsUnique F s L α).hom.app ((toDaggerKaroubi C).obj X) ≫
      (toDaggerKaroubiCompLiftWithSplittingsIso F s).hom.app X = α.hom.app X := by
  have hid : decompIdIncl ((toDaggerKaroubi C).obj X) = 𝟙 ((toDaggerKaroubi C).obj X) :=
    hom_ext rfl
  have hL :
      L.map (decompIdIncl ((toDaggerKaroubi C).obj X)) = 𝟙 (L.obj ((toDaggerKaroubi C).obj X)) :=
    (congrArg L.map hid).trans (L.map_id _)
  have hX :
      dagger (s ((toDaggerKaroubi C).obj X)).hom ≫ (s ((toDaggerKaroubi C).obj X)).hom =
        𝟙 (F.obj ((toDaggerKaroubi C).obj X).X) :=
    (s ((toDaggerKaroubi C).obj X)).range.trans (F.map_id X)
  change (L.map (decompIdIncl ((toDaggerKaroubi C).obj X)) ≫
      α.hom.app ((toDaggerKaroubi C).obj X).X ≫
      dagger (s ((toDaggerKaroubi C).obj X)).hom) ≫ (s ((toDaggerKaroubi C).obj X)).hom =
    α.hom.app X
  rw [Category.assoc, Category.assoc, hX, Category.comp_id]
  exact (congrArg (· ≫ α.hom.app X) hL).trans (Category.id_comp _)

/-- `liftWithSplittingsUnique F s L α` is pointwise unitary whenever `L` preserves daggers and `α`
is pointwise unitary. -/
theorem isUnitary_liftWithSplittingsUnique (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p))
    (L : DaggerKaroubi C ⥤ D) [L.PreservesDagger] (α : toDaggerKaroubi C ⋙ L ≅ F)
    (hα : ∀ X, IsUnitary (α.app X).hom) (P : DaggerKaroubi C) :
    IsUnitary ((liftWithSplittingsUnique F s L α).app P).hom :=
  ((liftWithSplittingsUnique F s L α).app P).isUnitary_hom_iff.mpr (by
    have hαP : dagger (α.hom.app P.X) = α.inv.app P.X :=
      (α.app P.X).dagger_hom_eq_inv_of_isUnitary (hα P.X)
    change dagger (L.map (decompIdIncl P) ≫ α.hom.app P.X ≫ dagger (s P).hom) =
      (s P).hom ≫ α.inv.app P.X ≫ L.map (decompIdProj P)
    rw [dagger_comp, dagger_comp, dagger_dagger, hαP, ← L.map_dagger, dagger_decompIdIncl,
      Category.assoc])

/-- Strict uniqueness of the comparison transformation `L ⟶ liftWithSplittings F s`: any natural
transformation matching `α` on `toDaggerKaroubi C` equals
`(liftWithSplittingsUnique F s L α).hom`. -/
theorem eq_liftWithSplittingsUnique_hom (F : C ⥤ D)
    (s : ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p))
    (L : DaggerKaroubi C ⥤ D) (α : toDaggerKaroubi C ⋙ L ≅ F)
    (β : L ⟶ liftWithSplittings F s)
    (hβ : ∀ X, β.app ((toDaggerKaroubi C).obj X) ≫
      (toDaggerKaroubiCompLiftWithSplittingsIso F s).hom.app X = α.hom.app X) :
    β = (liftWithSplittingsUnique F s L α).hom := by
  ext P
  have hnat := β.naturality (decompIdIncl P)
  let u := (toDaggerKaroubiCompLiftWithSplittingsIso F s).hom.app P.X
  let d : F.obj P.X ⟶ (liftWithSplittings F s).obj P := dagger (s P).hom
  have hu : dagger u ≫ u = 𝟙 (F.obj P.X) :=
    (isUnitary_toDaggerKaroubiCompLiftWithSplittingsIso F s P.X).dagger_hom_id
  have hstep :
      (liftWithSplittings F s).map (decompIdIncl P) ≫ u ≫ d =
        𝟙 ((liftWithSplittings F s).obj P) := by
    change ((s P).hom ≫ F.map P.p ≫ dagger u) ≫ u ≫ dagger (s P).hom = 𝟙 (s P).obj
    rw [Category.assoc, Category.assoc, reassoc_of% hu]
    exact (liftWithSplittings F s).map_id P
  rw [← Category.comp_id (β.app P), ← hstep, ← Category.assoc, ← hnat, Category.assoc,
    ← Category.assoc (β.app _), hβ P.X]
  rfl

section CompleteTarget

variable [IsDaggerIdempotentComplete D]

private noncomputable def chosenSplittings (F : C ⥤ D) [F.PreservesDagger] :
    ∀ P : DaggerKaroubi C, DaggerSplitting (F.map P.p) := fun P =>
  have h := (isDaggerSplit_iff _).mp
    (IsDaggerIdempotentComplete.daggerProjections_split _ _
      (F.map_isDaggerProjection P.isDaggerProjection))
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1, h.choose_spec.choose_spec.2⟩

/-- Extension of a dagger-preserving functor `F : C ⥤ D` into a dagger idempotent complete
category `D` along `toDaggerKaroubi C`. -/
noncomputable def lift (F : C ⥤ D) [F.PreservesDagger] : DaggerKaroubi C ⥤ D :=
  liftWithSplittings F (chosenSplittings F)

/-- `DaggerKaroubi.lift F` preserves daggers. -/
instance instPreservesDaggerLift (F : C ⥤ D) [F.PreservesDagger] : (lift F).PreservesDagger :=
  inferInstanceAs (liftWithSplittings F (chosenSplittings F)).PreservesDagger

/-- `DaggerKaroubi.lift F` is additive when `F` is additive. -/
instance instAdditiveLift [Preadditive C] [Preadditive D] (F : C ⥤ D)
    [F.Additive] [F.PreservesDagger] : (lift F).Additive :=
  inferInstanceAs (liftWithSplittings F (chosenSplittings F)).Additive

/-- `DaggerKaroubi.lift F` is `R`-linear when `F` is `R`-linear. -/
instance instLinearLift [Preadditive C] [Preadditive D] {R : Type w} [Semiring R]
    [Linear R C] [Linear R D] (F : C ⥤ D) [F.Linear R] [F.PreservesDagger] :
    (lift F).Linear R :=
  inferInstanceAs ((liftWithSplittings F (chosenSplittings F)).Linear R)

/-- Canonical unitary natural isomorphism `toDaggerKaroubi C ⋙ lift F ≅ F`. -/
noncomputable def toDaggerKaroubiCompLiftIso (F : C ⥤ D) [F.PreservesDagger] :
    toDaggerKaroubi C ⋙ lift F ≅ F :=
  toDaggerKaroubiCompLiftWithSplittingsIso F (chosenSplittings F)

/-- Every component of `toDaggerKaroubiCompLiftIso F` is unitary. -/
theorem isUnitary_toDaggerKaroubiCompLiftIso (F : C ⥤ D) [F.PreservesDagger] (X : C) :
    IsUnitary ((toDaggerKaroubiCompLiftIso F).app X).hom :=
  isUnitary_toDaggerKaroubiCompLiftWithSplittingsIso F (chosenSplittings F) X

/-- Canonical comparison isomorphism `L ≅ lift F` for any functor `L` extending `F`. -/
noncomputable def liftUnique (F : C ⥤ D) [F.PreservesDagger]
    (L : DaggerKaroubi C ⥤ D) (α : toDaggerKaroubi C ⋙ L ≅ F) :
    L ≅ lift F :=
  liftWithSplittingsUnique F (chosenSplittings F) L α

/-- Restricting `liftUnique F L α` along `toDaggerKaroubi C` recovers `α`. -/
@[simp] theorem liftUnique_hom_app_toDaggerKaroubi (F : C ⥤ D) [F.PreservesDagger]
    (L : DaggerKaroubi C ⥤ D) (α : toDaggerKaroubi C ⋙ L ≅ F) (X : C) :
    (liftUnique F L α).hom.app ((toDaggerKaroubi C).obj X) ≫
      (toDaggerKaroubiCompLiftIso F).hom.app X = α.hom.app X :=
  liftWithSplittingsUnique_hom_app_toDaggerKaroubi F (chosenSplittings F) L α X

/-- `liftUnique F L α` is pointwise unitary whenever `L` preserves daggers and `α` is pointwise
unitary. -/
theorem isUnitary_liftUnique (F : C ⥤ D) [F.PreservesDagger]
    (L : DaggerKaroubi C ⥤ D) [L.PreservesDagger] (α : toDaggerKaroubi C ⋙ L ≅ F)
    (hα : ∀ X, IsUnitary (α.app X).hom) (P : DaggerKaroubi C) :
    IsUnitary ((liftUnique F L α).app P).hom :=
  isUnitary_liftWithSplittingsUnique F (chosenSplittings F) L α hα P

/-- Strict uniqueness of the comparison transformation `L ⟶ lift F`. -/
theorem eq_liftUnique_hom (F : C ⥤ D) [F.PreservesDagger]
    (L : DaggerKaroubi C ⥤ D) (α : toDaggerKaroubi C ⋙ L ≅ F)
    (β : L ⟶ lift F)
    (hβ : ∀ X, β.app ((toDaggerKaroubi C).obj X) ≫
      (toDaggerKaroubiCompLiftIso F).hom.app X = α.hom.app X) :
    β = (liftUnique F L α).hom :=
  eq_liftWithSplittingsUnique_hom F (chosenSplittings F) L α β hβ

end CompleteTarget

end UniversalProperty

section SelfEquivalence

variable (C : Type u₁) [Category.{v₁} C] [DaggerCategory C] [IsDaggerIdempotentComplete C]

/-- Equivalence `C ≌ DaggerKaroubi C` when `C` is already dagger idempotent complete, with
dagger-preserving functors and pointwise unitary unit and counit isomorphisms. -/
noncomputable def toDaggerKaroubiEquivalence : C ≌ DaggerKaroubi C where
  functor := toDaggerKaroubi C
  inverse := lift (𝟭 C)
  unitIso := (toDaggerKaroubiCompLiftIso (𝟭 C)).symm
  counitIso :=
    NatIso.ofComponents
      (fun P =>
        { hom := homMk (chosenSplittings (𝟭 C) P).hom (by
            change 𝟙 _ ≫ (chosenSplittings (𝟭 C) P).hom ≫ P.p = (chosenSplittings (𝟭 C) P).hom
            rw [Category.id_comp]
            exact (chosenSplittings (𝟭 C) P).hom_comp_p)
          inv := homMk (dagger (chosenSplittings (𝟭 C) P).hom) (by
            change P.p ≫ dagger (chosenSplittings (𝟭 C) P).hom ≫ 𝟙 _ =
              dagger (chosenSplittings (𝟭 C) P).hom
            rw [Category.comp_id]
            exact (chosenSplittings (𝟭 C) P).p_comp_dagger_hom)
          hom_inv_id := hom_ext (chosenSplittings (𝟭 C) P).isometry
          inv_hom_id := hom_ext (chosenSplittings (𝟭 C) P).range })
      fun {P Q} f => hom_ext (by
        change ((chosenSplittings (𝟭 C) P).hom ≫ f.hom.f ≫
            dagger (chosenSplittings (𝟭 C) Q).hom) ≫ (chosenSplittings (𝟭 C) Q).hom =
          (chosenSplittings (𝟭 C) P).hom ≫ f.hom.f
        rw [Category.assoc, Category.assoc]
        have hQ : dagger (chosenSplittings (𝟭 C) Q).hom ≫ (chosenSplittings (𝟭 C) Q).hom = Q.p :=
          (chosenSplittings (𝟭 C) Q).range
        rw [hQ, comp_p])
  functor_unitIso_comp X := hom_ext (chosenSplittings (𝟭 C) ((toDaggerKaroubi C).obj X)).range

/-- The forward functor of `toDaggerKaroubiEquivalence C` is `toDaggerKaroubi C`. -/
@[simp] theorem toDaggerKaroubiEquivalence_functor :
    (toDaggerKaroubiEquivalence C).functor = toDaggerKaroubi C := (rfl)

/-- The inverse functor of `toDaggerKaroubiEquivalence C` is `lift (𝟭 C)`. -/
@[simp] theorem toDaggerKaroubiEquivalence_inverse :
    (toDaggerKaroubiEquivalence C).inverse = lift (𝟭 C) := (rfl)

/-- The forward functor of `toDaggerKaroubiEquivalence C` preserves daggers. -/
instance instPreservesDaggerToDaggerKaroubiEquivalenceFunctor :
    (toDaggerKaroubiEquivalence C).functor.PreservesDagger := by
  rw [toDaggerKaroubiEquivalence_functor]
  infer_instance

/-- The inverse functor of `toDaggerKaroubiEquivalence C` preserves daggers. -/
instance instPreservesDaggerToDaggerKaroubiEquivalenceInverse :
    (toDaggerKaroubiEquivalence C).inverse.PreservesDagger := by
  rw [toDaggerKaroubiEquivalence_inverse]
  infer_instance

/-- The unit of `toDaggerKaroubiEquivalence C` is pointwise unitary. -/
theorem isUnitary_toDaggerKaroubiEquivalence_unitIso (X : C) :
    IsUnitary ((toDaggerKaroubiEquivalence C).unitIso.app X).hom := by
  have hu := isUnitary_toDaggerKaroubiCompLiftIso (𝟭 C) X
  change IsUnitary ((toDaggerKaroubiCompLiftIso (𝟭 C)).app X).inv
  rw [← ((toDaggerKaroubiCompLiftIso (𝟭 C)).app X).dagger_hom_eq_inv_of_isUnitary hu]
  exact hu.dagger

/-- The counit of `toDaggerKaroubiEquivalence C` is pointwise unitary. -/
theorem isUnitary_toDaggerKaroubiEquivalence_counitIso (P : DaggerKaroubi C) :
    IsUnitary ((toDaggerKaroubiEquivalence C).counitIso.app P).hom :=
  ((toDaggerKaroubiEquivalence C).counitIso.app P).isUnitary_hom_iff.mpr (hom_ext rfl)

end SelfEquivalence

section ComparisonWithKaroubi

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]

/-- If every idempotent in `C` is similar via an isomorphism to a dagger projection, then
`DaggerKaroubi.forget C : DaggerKaroubi C ⥤ Idempotents.Karoubi C` is an equivalence of
categories. -/
theorem forget_isEquivalence_of_exists_similar_projection
    (h : ∀ {X : C} (e : X ⟶ X), e ≫ e = e →
      ∃ (p : X ⟶ X) (u : X ≅ X), IsDaggerProjection p ∧ u.inv ≫ e ≫ u.hom = p) :
    (forget C).IsEquivalence := by
  have : (forget C).EssSurj :=
    ⟨fun Q => by
      rcases h Q.p Q.idem with ⟨p, u, hp, hu⟩
      have hpu : p ≫ u.inv = u.inv ≫ Q.p := by
        rw [← hu, Category.assoc, Category.assoc, u.hom_inv_id, Category.comp_id]
      have hup : u.hom ≫ p = Q.p ≫ u.hom := by
        rw [← hu, ← Category.assoc, ← Category.assoc, u.hom_inv_id, Category.id_comp]
      refine ⟨mk Q.X p hp, ⟨{
        hom := ⟨p ≫ u.inv, by
          change p ≫ (p ≫ u.inv) ≫ Q.p = p ≫ u.inv
          rw [Category.assoc, ← hpu, hp.idem_assoc, hp.idem_assoc]⟩
        inv := ⟨Q.p ≫ u.hom, by
          change Q.p ≫ (Q.p ≫ u.hom) ≫ p = Q.p ≫ u.hom
          rw [Category.assoc, hup, ← Category.assoc Q.p Q.p, Q.idem,
            ← Category.assoc Q.p Q.p, Q.idem]⟩
        hom_inv_id := Idempotents.Karoubi.hom_ext _ _ (by
          change (p ≫ u.inv) ≫ (Q.p ≫ u.hom) = p
          rw [Category.assoc, hu, hp.idem])
        inv_hom_id := Idempotents.Karoubi.hom_ext _ _ (by
          change (Q.p ≫ u.hom) ≫ (p ≫ u.inv) = Q.p
          rw [Category.assoc, hpu, ← Category.assoc u.hom, u.hom_inv_id, Category.id_comp,
            Q.idem]) }⟩⟩⟩
  exact {}

/-- Equivalence `DaggerKaroubi C ≌ Idempotents.Karoubi C` when every idempotent in `C` is similar
to a dagger projection. -/
noncomputable def equivKaroubiOfExistsSimilarProjection
    (h : ∀ {X : C} (e : X ⟶ X), e ≫ e = e →
      ∃ (p : X ⟶ X) (u : X ≅ X), IsDaggerProjection p ∧ u.inv ≫ e ≫ u.hom = p) :
    DaggerKaroubi C ≌ Idempotents.Karoubi C :=
  have := forget_isEquivalence_of_exists_similar_projection h
  (forget C).asEquivalence

end ComparisonWithKaroubi

end DaggerKaroubi

end TauCeti
