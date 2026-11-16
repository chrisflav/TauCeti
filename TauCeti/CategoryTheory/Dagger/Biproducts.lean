/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.CategoryTheory.Dagger.Functor

/-!
# Orthogonal biproducts in dagger categories

An orthogonal bicone (or dagger bicone) for a family `f : J → C` in a dagger category with zero
morphisms is a bicone whose projections are the daggers of its inclusions: `dagger (b.ι j) = b.π j`.
A dagger biproduct is a bilimit bicone that is orthogonal.

Because Mathlib's `HasBiproduct` is proposition-valued and chooses an arbitrary bilimit bicone via
`Classical.choice`, `HasDaggerBiproduct` packages the existence of an orthogonal bilimit bicone
directly, supplying chosen orthogonal biproducts `daggerBiproduct f`. Every dagger biproduct is a
native biproduct, and any two orthogonal bilimit bicones over the same family are canonically
isomorphic by a unique unitary isomorphism. Taking daggers swaps `lift` with `desc`, acts
componentwise on `map`, and takes the conjugate transpose on biproduct matrices.

## Main definitions and results

* `CategoryTheory.Limits.Bicone.IsOrthogonal`: orthogonality predicate on native bicones.
* `CategoryTheory.Limits.Bicone.IsOrthogonal.isUnitary_coconePointUniqueUpToIso`: any two
  orthogonal bilimit bicones are related by a unique unitary isomorphism.
* `TauCeti.HasDaggerBiproduct`, `TauCeti.HasDaggerBiproductsOfShape`,
  `TauCeti.HasFiniteDaggerBiproducts`: existence of dagger biproducts, implying the corresponding
  native Mathlib biproduct classes.
* `TauCeti.daggerBiproduct`: chosen orthogonal biproducts with their universal properties, dagger
  formulas (`dagger_lift`, `dagger_desc`, `dagger_map`, `dagger_matrix`), and comparison with
  native biproducts (`isoBiproduct`, `isUnitary_isoBiproduct_iff`).
* `CategoryTheory.Functor.mapDaggerBiproduct`: canonical unitary preservation isomorphism for
  dagger-preserving functors that preserve biproducts.

## References

* P. Selinger, *Dagger compact closed categories and completely positive maps*,
  Electronic Notes in Theoretical Computer Science 170 (2007), 139–163.
* C. Heunen and J. Vicary, *Categories for Quantum Theory: An Introduction*,
  Oxford University Press (2019).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TauCeti

universe w w' v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

namespace Bicone

variable {J : Type w} {K : Type w'} {F : J → C}

/-- The canonical isomorphism between two bilimit bicones over the same family commutes with
projections as well as inclusions. -/
theorem IsBilimit.coconePointUniqueUpToIso_hom_π {b₁ b₂ : Bicone F}
    (hb₁ : b₁.IsBilimit) (hb₂ : b₂.IsBilimit) (j : J) :
    (hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit).hom ≫ b₂.π j = b₁.π j := by
  refine hb₁.isColimit.hom_ext fun ⟨i⟩ => ?_
  have hcomp : b₁.ι i ≫ (hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit).hom = b₂.ι i :=
    hb₁.isColimit.comp_coconePointUniqueUpToIso_hom hb₂.isColimit ⟨i⟩
  simp only [Bicone.toCocone_ι_app, reassoc_of% hcomp, b₂.ι_π, b₁.ι_π]

section Dagger

variable [DaggerCategory C] [DaggerCategory D]

/-- A bicone in a dagger category is orthogonal when every projection is the dagger of the
corresponding inclusion. -/
def IsOrthogonal (b : Bicone F) : Prop :=
  ∀ j, dagger (b.ι j) = b.π j

/-- Characterization of an orthogonal bicone. -/
theorem isOrthogonal_iff (b : Bicone F) :
    b.IsOrthogonal ↔ ∀ j, dagger (b.ι j) = b.π j := Iff.rfl

namespace IsOrthogonal

/-- The dagger of an inclusion in an orthogonal bicone is the matching projection. -/
theorem dagger_ι {b : Bicone F} (hb : b.IsOrthogonal) (j : J) :
    dagger (b.ι j) = b.π j := hb j

/-- The dagger of a projection in an orthogonal bicone is the matching inclusion. -/
theorem dagger_π {b : Bicone F} (hb : b.IsOrthogonal) (j : J) :
    dagger (b.π j) = b.ι j := by
  rw [← hb j, dagger_dagger]

/-- Orthogonality of a bicone may equivalently be verified on projections. -/
theorem of_dagger_π {b : Bicone F} (h : ∀ j, dagger (b.π j) = b.ι j) :
    b.IsOrthogonal := fun j => by
  rw [← h j, dagger_dagger]

/-- Whiskering an orthogonal bicone along an equivalence of index types preserves orthogonality. -/
theorem whisker {b : Bicone F} (hb : b.IsOrthogonal) (g : K ≃ J) :
    (b.whisker g).IsOrthogonal := fun k => hb (g k)

/-- A dagger-preserving functor preserving zero morphisms maps orthogonal bicones to orthogonal
bicones. -/
theorem map {b : Bicone F} (hb : b.IsOrthogonal) (G : C ⥤ D) [G.PreservesZeroMorphisms]
    [G.PreservesDagger] : (G.mapBicone b).IsOrthogonal := fun j => by
  simp [Functor.mapBicone, ← G.map_dagger, hb j]

/-- The canonical isomorphism between two orthogonal bilimit bicones over the same family is
unitary. -/
theorem isUnitary_coconePointUniqueUpToIso {b₁ b₂ : Bicone F}
    (hb₁ : b₁.IsBilimit) (hb₂ : b₂.IsBilimit)
    (ho₁ : b₁.IsOrthogonal) (ho₂ : b₂.IsOrthogonal) :
    IsUnitary (hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit).hom := by
  let e := hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit
  rw [e.isUnitary_hom_iff]
  refine hb₁.isLimit.hom_ext fun ⟨j⟩ => ?_
  have hι : b₁.ι j ≫ e.hom = b₂.ι j :=
    hb₁.isColimit.comp_coconePointUniqueUpToIso_hom hb₂.isColimit ⟨j⟩
  have hπ : e.inv ≫ b₁.π j = b₂.π j :=
    e.inv_comp_eq.mpr (hb₁.coconePointUniqueUpToIso_hom_π hb₂ j).symm
  simp only [Bicone.toCone_π_app]
  calc
    dagger e.hom ≫ b₁.π j = dagger e.hom ≫ dagger (b₁.ι j) := by rw [ho₁.dagger_ι]
    _ = dagger (b₁.ι j ≫ e.hom) := (dagger_comp _ _).symm
    _ = dagger (b₂.ι j) := by rw [hι]
    _ = b₂.π j := ho₂.dagger_ι j
    _ = e.inv ≫ b₁.π j := hπ.symm

/-- A morphism between two orthogonal bilimit bicones commuting with the inclusions is unique and
unitary. -/
theorem eq_and_isUnitary_of_wι {b₁ b₂ : Bicone F}
    (hb₁ : b₁.IsBilimit) (hb₂ : b₂.IsBilimit)
    (ho₁ : b₁.IsOrthogonal) (ho₂ : b₂.IsOrthogonal)
    {f : b₁.pt ⟶ b₂.pt} (hf : ∀ j, b₁.ι j ≫ f = b₂.ι j) :
    f = (hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit).hom ∧ IsUnitary f := by
  have heq : f = (hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit).hom :=
    hb₁.isColimit.hom_ext fun ⟨j⟩ => by
      simpa using (hf j).trans
        (hb₁.isColimit.comp_coconePointUniqueUpToIso_hom hb₂.isColimit ⟨j⟩).symm
  exact ⟨heq, heq ▸ isUnitary_coconePointUniqueUpToIso hb₁ hb₂ ho₁ ho₂⟩

/-- A morphism between two orthogonal bilimit bicones commuting with the projections is unique and
unitary. -/
theorem eq_and_isUnitary_of_wπ {b₁ b₂ : Bicone F}
    (hb₁ : b₁.IsBilimit) (hb₂ : b₂.IsBilimit)
    (ho₁ : b₁.IsOrthogonal) (ho₂ : b₂.IsOrthogonal)
    {f : b₁.pt ⟶ b₂.pt} (hf : ∀ j, f ≫ b₂.π j = b₁.π j) :
    f = (hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit).hom ∧ IsUnitary f := by
  have heq : f = (hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit).hom :=
    hb₂.isLimit.hom_ext fun ⟨j⟩ => by
      simpa using (hf j).trans (hb₁.coconePointUniqueUpToIso_hom_π hb₂ j).symm
  exact ⟨heq, heq ▸ isUnitary_coconePointUniqueUpToIso hb₁ hb₂ ho₁ ho₂⟩

end IsOrthogonal

end Dagger

end Bicone

namespace IsZero

omit [HasZeroMorphisms C] in
/-- The unique isomorphism between two zero objects in a dagger category is unitary. -/
theorem isUnitary_iso [DaggerCategory C] {X Y : C} (hX : IsZero X) (hY : IsZero Y) :
    IsUnitary (hX.iso hY).hom :=
  (isUnitary_iff _).mpr ⟨hX.eq_of_src _ _, hY.eq_of_src _ _⟩

end IsZero

end CategoryTheory.Limits

namespace TauCeti

section Classes

variable (J : Type w) (C : Type u₁) [Category.{v₁} C] [HasZeroMorphisms C] [DaggerCategory C]

/-- An orthogonal bilimit bicone over a family `F : J → C`. -/
structure LimitDaggerBicone {J : Type w} {C : Type u₁} [Category.{v₁} C]
    [HasZeroMorphisms C] [DaggerCategory C] (F : J → C) extends LimitBicone F where
  /-- The projections are the daggers of the inclusions. -/
  isOrthogonal : bicone.IsOrthogonal

/-- `HasDaggerBiproduct F` expresses the existence of an orthogonal bilimit bicone over `F`. -/
class HasDaggerBiproduct {J : Type w} {C : Type u₁} [Category.{v₁} C]
    [HasZeroMorphisms C] [DaggerCategory C] (F : J → C) : Prop where mk' ::
  /-- There exists an orthogonal bilimit bicone over `F`. -/
  exists_daggerBiproduct : Nonempty (LimitDaggerBicone F)

/-- `C` has dagger biproducts of shape `J` if every family `F : J → C` has a dagger biproduct. -/
class HasDaggerBiproductsOfShape : Prop where
  /-- Every family indexed by `J` admits a dagger biproduct. -/
  has_daggerBiproduct : ∀ F : J → C, HasDaggerBiproduct F

attribute [instance 100] HasDaggerBiproductsOfShape.has_daggerBiproduct

/-- `C` has finite dagger biproducts if it has dagger biproducts indexed by `Fin n` for every
`n`. -/
class HasFiniteDaggerBiproducts (C : Type u₁) [Category.{v₁} C]
    [HasZeroMorphisms C] [DaggerCategory C] : Prop where
  /-- `C` has dagger biproducts of shape `Fin n` for every `n`. -/
  out : ∀ n, HasDaggerBiproductsOfShape (Fin n) C

end Classes

section Indexed

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [DaggerCategory C]
variable {J : Type w} {K : Type w'}

/-- Construct `HasDaggerBiproduct F` from an explicit `LimitDaggerBicone F`. -/
theorem HasDaggerBiproduct.mk {F : J → C} (d : LimitDaggerBicone F) : HasDaggerBiproduct F :=
  ⟨Nonempty.intro d⟩

/-- Extract a chosen orthogonal bilimit bicone from `HasDaggerBiproduct F`. -/
def getDaggerBiproductData (F : J → C) [HasDaggerBiproduct F] : LimitDaggerBicone F :=
  Classical.choice HasDaggerBiproduct.exists_daggerBiproduct

/-- The chosen orthogonal bilimit bicone for `F`. -/
def daggerBiproduct.bicone (F : J → C) [HasDaggerBiproduct F] : Bicone F :=
  (getDaggerBiproductData F).bicone

/-- The chosen dagger biproduct bicone is orthogonal. -/
theorem daggerBiproduct.bicone_isOrthogonal (F : J → C) [HasDaggerBiproduct F] :
    (daggerBiproduct.bicone F).IsOrthogonal :=
  (getDaggerBiproductData F).isOrthogonal

/-- The chosen dagger biproduct bicone is a bilimit bicone. -/
def daggerBiproduct.isBilimit (F : J → C) [HasDaggerBiproduct F] :
    (daggerBiproduct.bicone F).IsBilimit :=
  (getDaggerBiproductData F).isBilimit

/-- The chosen dagger biproduct bicone is a limit cone. -/
def daggerBiproduct.isLimit (F : J → C) [HasDaggerBiproduct F] :
    IsLimit (daggerBiproduct.bicone F).toCone :=
  (daggerBiproduct.isBilimit F).isLimit

/-- The chosen dagger biproduct bicone is a colimit cocone. -/
def daggerBiproduct.isColimit (F : J → C) [HasDaggerBiproduct F] :
    IsColimit (daggerBiproduct.bicone F).toCocone :=
  (daggerBiproduct.isBilimit F).isColimit

/-- Every dagger biproduct yields a native biproduct. -/
instance (priority := 100) hasBiproduct_of_hasDaggerBiproduct (F : J → C)
    [HasDaggerBiproduct F] : HasBiproduct F :=
  HasBiproduct.mk (getDaggerBiproductData F).toLimitBicone

/-- Transport `HasDaggerBiproductsOfShape` across an equivalence of index types. -/
theorem hasDaggerBiproductsOfShape_of_equiv (C : Type u₁) [Category.{v₁} C]
    [HasZeroMorphisms C] [DaggerCategory C] {K : Type w'} [HasDaggerBiproductsOfShape K C]
    (e : J ≃ K) : HasDaggerBiproductsOfShape J C :=
  ⟨fun F =>
    let ⟨⟨⟨c, hc⟩, ho⟩⟩ := HasDaggerBiproductsOfShape.has_daggerBiproduct (F ∘ e.symm)
    HasDaggerBiproduct.mk <| by
      simpa only [Function.comp_def, e.symm_apply_apply] using
        LimitDaggerBicone.mk
          (LimitBicone.mk (c.whisker e) ((c.whiskerIsBilimitIff e).2 hc))
          (ho.whisker e)⟩

/-- A category with finite dagger biproducts has dagger biproducts indexed by any finite type. -/
instance (priority := 100) hasDaggerBiproductsOfShape_finite [HasFiniteDaggerBiproducts C]
    [Finite J] : HasDaggerBiproductsOfShape J C := by
  rcases Finite.exists_equiv_fin J with ⟨n, ⟨e⟩⟩
  have : HasDaggerBiproductsOfShape (Fin n) C := HasFiniteDaggerBiproducts.out n
  exact hasDaggerBiproductsOfShape_of_equiv C e

/-- A category with dagger biproducts of shape `J` has native biproducts of shape `J`. -/
instance (priority := 100) hasBiproductsOfShape_of_hasDaggerBiproductsOfShape
    [HasDaggerBiproductsOfShape J C] : HasBiproductsOfShape J C :=
  ⟨fun F => hasBiproduct_of_hasDaggerBiproduct F⟩

/-- A category with finite dagger biproducts has native finite biproducts. -/
instance (priority := 100) hasFiniteBiproducts_of_hasFiniteDaggerBiproducts
    [HasFiniteDaggerBiproducts C] : HasFiniteBiproducts C :=
  ⟨fun n =>
    have : HasDaggerBiproductsOfShape (Fin n) C := HasFiniteDaggerBiproducts.out n
    inferInstance⟩

/-- The chosen orthogonal biproduct object of a family `f : J → C`. -/
abbrev daggerBiproduct (f : J → C) [HasDaggerBiproduct f] : C :=
  (daggerBiproduct.bicone f).pt

namespace daggerBiproduct

/-- The projection from the orthogonal biproduct onto summand `j`. -/
abbrev π (f : J → C) [HasDaggerBiproduct f] (j : J) : daggerBiproduct f ⟶ f j :=
  (daggerBiproduct.bicone f).π j

/-- The inclusion of summand `j` into the orthogonal biproduct. -/
abbrev ι (f : J → C) [HasDaggerBiproduct f] (j : J) : f j ⟶ daggerBiproduct f :=
  (daggerBiproduct.bicone f).ι j

/-- The dagger of the `j`-th inclusion is the `j`-th projection. -/
@[simp, grind =] theorem dagger_ι (f : J → C) [HasDaggerBiproduct f] (j : J) :
    dagger (ι f j) = π f j :=
  (bicone_isOrthogonal f).dagger_ι j

/-- The dagger of the `j`-th projection is the `j`-th inclusion. -/
@[simp, grind =] theorem dagger_π (f : J → C) [HasDaggerBiproduct f] (j : J) :
    dagger (π f j) = ι f j :=
  (bicone_isOrthogonal f).dagger_π j

/-- Inclusion followed by projection on the orthogonal biproduct gives the Kronecker delta. -/
@[reassoc] theorem ι_π [DecidableEq J] (f : J → C) [HasDaggerBiproduct f] (j j' : J) :
    ι f j ≫ π f j' = if h : j = j' then eqToHom (congrArg f h) else 0 := by
  convert (bicone f).ι_π j j'

/-- Inclusion followed by matching projection is the identity. -/
@[reassoc] theorem ι_π_self (f : J → C) [HasDaggerBiproduct f] (j : J) :
    ι f j ≫ π f j = 𝟙 (f j) :=
  bicone_ι_π_self _ j

/-- Inclusion followed by a distinct projection is zero. -/
@[reassoc] theorem ι_π_ne (f : J → C) [HasDaggerBiproduct f] {j j' : J}
    (h : j ≠ j') : ι f j ≫ π f j' = 0 :=
  bicone_ι_π_ne _ h

/-- Assemble a family of morphisms into the summands into a morphism into the orthogonal
biproduct. -/
abbrev lift {f : J → C} [HasDaggerBiproduct f] {P : C} (p : ∀ j, P ⟶ f j) :
    P ⟶ daggerBiproduct f :=
  (isLimit f).lift (Fan.mk P p)

/-- Assemble a family of morphisms out of the summands into a morphism out of the orthogonal
biproduct. -/
abbrev desc {f : J → C} [HasDaggerBiproduct f] {P : C} (p : ∀ j, f j ⟶ P) :
    daggerBiproduct f ⟶ P :=
  (isColimit f).desc (Cofan.mk P p)

/-- Projecting a lift recovers its `j`-th component. -/
@[reassoc (attr := simp)] theorem lift_π {f : J → C} [HasDaggerBiproduct f] {P : C}
    (p : ∀ j, P ⟶ f j) (j : J) : lift p ≫ π f j = p j :=
  (isLimit f).fac _ ⟨j⟩

/-- Restricting a desc along an inclusion recovers its `j`-th component. -/
@[reassoc (attr := simp)] theorem ι_desc {f : J → C} [HasDaggerBiproduct f] {P : C}
    (p : ∀ j, f j ⟶ P) (j : J) : ι f j ≫ desc p = p j :=
  (isColimit f).fac _ ⟨j⟩

/-- Two morphisms into an orthogonal biproduct are equal if their projections agree. -/
@[ext 1001] theorem hom_ext {f : J → C} [HasDaggerBiproduct f] {P : C}
    (g h : P ⟶ daggerBiproduct f) (w : ∀ j, g ≫ π f j = h ≫ π f j) : g = h :=
  (isLimit f).hom_ext fun j => w j.as

/-- Two morphisms out of an orthogonal biproduct are equal if their restrictions to summands
agree. -/
@[ext] theorem hom_ext' {f : J → C} [HasDaggerBiproduct f] {P : C}
    (g h : daggerBiproduct f ⟶ P) (w : ∀ j, ι f j ≫ g = ι f j ≫ h) : g = h :=
  (isColimit f).hom_ext fun j => w j.as

/-- Taking the dagger turns `lift` into `desc` of the daggers. -/
@[simp] theorem dagger_lift {f : J → C} [HasDaggerBiproduct f] {P : C}
    (p : ∀ j, P ⟶ f j) : dagger (lift p) = desc fun j => dagger (p j) := by
  refine hom_ext' _ _ fun j => ?_
  rw [ι_desc, ← dagger_π, ← dagger_comp, lift_π]

/-- Taking the dagger turns `desc` into `lift` of the daggers. -/
@[simp] theorem dagger_desc {f : J → C} [HasDaggerBiproduct f] {P : C}
    (p : ∀ j, f j ⟶ P) : dagger (desc p) = lift fun j => dagger (p j) := by
  refine hom_ext _ _ fun j => ?_
  rw [lift_π, ← dagger_ι, ← dagger_comp, ι_desc]

/-- The diagonal morphism between orthogonal biproducts induced by a family of morphisms. -/
def map {f g : J → C} [HasDaggerBiproduct f] [HasDaggerBiproduct g]
    (p : ∀ j, f j ⟶ g j) : daggerBiproduct f ⟶ daggerBiproduct g :=
  lift fun j => π f j ≫ p j

/-- Projecting a diagonal map gives the corresponding summand map. -/
@[reassoc (attr := simp)] theorem map_π {f g : J → C} [HasDaggerBiproduct f]
    [HasDaggerBiproduct g] (p : ∀ j, f j ⟶ g j) (j : J) :
    map p ≫ π g j = π f j ≫ p j :=
  lift_π _ j

/-- Restricting a diagonal map along an inclusion gives the corresponding summand map. -/
@[reassoc (attr := simp)] theorem ι_map {f g : J → C} [HasDaggerBiproduct f]
    [HasDaggerBiproduct g] (p : ∀ j, f j ⟶ g j) (j : J) :
    ι f j ≫ map p = p j ≫ ι g j := by
  classical
  refine hom_ext _ _ fun j' => ?_
  by_cases h : j = j'
  · subst h; simp
  · simp [h]

/-- Taking the dagger acts componentwise on diagonal maps between orthogonal biproducts. -/
@[simp] theorem dagger_map {f g : J → C} [HasDaggerBiproduct f] [HasDaggerBiproduct g]
    (p : ∀ j, f j ⟶ g j) : dagger (map p) = map fun j => dagger (p j) := by
  refine hom_ext _ _ fun j => ?_
  rw [map_π, ← dagger_ι, ← dagger_comp, ι_map, dagger_comp, dagger_ι]

/-- Diagonal isomorphism between orthogonal biproducts induced by a family of isomorphisms. -/
def mapIso {f g : J → C} [HasDaggerBiproduct f] [HasDaggerBiproduct g]
    (p : ∀ j, f j ≅ g j) : daggerBiproduct f ≅ daggerBiproduct g where
  hom := map fun j => (p j).hom
  inv := map fun j => (p j).inv
  hom_inv_id := by
    refine hom_ext _ _ fun j => ?_
    simp
  inv_hom_id := by
    refine hom_ext _ _ fun j => ?_
    simp

/-- Forward morphism of `mapIso`. -/
@[simp] theorem mapIso_hom {f g : J → C} [HasDaggerBiproduct f] [HasDaggerBiproduct g]
    (p : ∀ j, f j ≅ g j) : (mapIso p).hom = map fun j => (p j).hom := (rfl)

/-- Inverse morphism of `mapIso`. -/
@[simp] theorem mapIso_inv {f g : J → C} [HasDaggerBiproduct f] [HasDaggerBiproduct g]
    (p : ∀ j, f j ≅ g j) : (mapIso p).inv = map fun j => (p j).inv := (rfl)

/-- A diagonal isomorphism with unitary components is unitary. -/
theorem isUnitary_mapIso {f g : J → C} [HasDaggerBiproduct f] [HasDaggerBiproduct g]
    (p : ∀ j, f j ≅ g j) (hp : ∀ j, IsUnitary (p j).hom) : IsUnitary (mapIso p).hom := by
  rw [(mapIso p).isUnitary_hom_iff]
  refine hom_ext _ _ fun j => ?_
  simp [dagger_map, (p j).dagger_hom_eq_inv_of_isUnitary (hp j)]

/-- Assemble a matrix of morphisms into a morphism between orthogonal biproducts. -/
def matrix {f : J → C} {g : K → C} [HasDaggerBiproduct f] [HasDaggerBiproduct g]
    (m : ∀ j k, f j ⟶ g k) : daggerBiproduct f ⟶ daggerBiproduct g :=
  desc fun j => lift fun k => m j k

/-- Restricting a biproduct matrix along an inclusion gives the row lift. -/
@[reassoc (attr := simp)] theorem ι_matrix {f : J → C} {g : K → C}
    [HasDaggerBiproduct f] [HasDaggerBiproduct g] (m : ∀ j k, f j ⟶ g k) (j : J) :
    ι f j ≫ matrix m = lift fun k => m j k :=
  ι_desc _ j

/-- Projecting a biproduct matrix onto a summand gives the column desc. -/
@[reassoc (attr := simp)] theorem matrix_π {f : J → C} {g : K → C}
    [HasDaggerBiproduct f] [HasDaggerBiproduct g] (m : ∀ j k, f j ⟶ g k) (k : K) :
    matrix m ≫ π g k = desc fun j => m j k := by
  refine hom_ext' _ _ fun j => ?_
  simp

/-- Taking the dagger of a biproduct matrix gives its conjugate transpose. -/
@[simp] theorem dagger_matrix {f : J → C} {g : K → C}
    [HasDaggerBiproduct f] [HasDaggerBiproduct g] (m : ∀ j k, f j ⟶ g k) :
    dagger (matrix m) = matrix fun k j => dagger (m j k) := by
  refine hom_ext _ _ fun j => ?_
  rw [matrix_π]
  refine hom_ext' _ _ fun k => ?_
  rw [ι_desc, ← dagger_π g k, ← dagger_ι f j, ← dagger_comp, ← dagger_comp,
    Category.assoc, ι_matrix_assoc, lift_π]

/-- Composing a biproduct matrix on the right with a diagonal map multiplies each column. -/
@[reassoc] theorem matrix_map {f : J → C} {g h : K → C}
    [HasDaggerBiproduct f] [HasDaggerBiproduct g] [HasDaggerBiproduct h]
    (m : ∀ j k, f j ⟶ g k) (n : ∀ k, g k ⟶ h k) :
    matrix m ≫ map n = matrix fun j k => m j k ≫ n k := by
  refine hom_ext _ _ fun k => hom_ext' _ _ fun j => ?_
  simp

/-- Composing a diagonal map on the right with a biproduct matrix multiplies each row. -/
@[reassoc] theorem map_matrix {f g : J → C} {h : K → C}
    [HasDaggerBiproduct f] [HasDaggerBiproduct g] [HasDaggerBiproduct h]
    (n : ∀ j, f j ⟶ g j) (m : ∀ j k, g j ⟶ h k) :
    map n ≫ matrix m = matrix fun j k => n j ≫ m j k := by
  refine hom_ext _ _ fun k => hom_ext' _ _ fun j => ?_
  simp

/-- Canonical comparison isomorphism between the chosen orthogonal biproduct and Mathlib's chosen
biproduct. -/
def isoBiproduct (f : J → C) [HasDaggerBiproduct f] [HasBiproduct f] :
    daggerBiproduct f ≅ ⨁ f :=
  (isColimit f).coconePointUniqueUpToIso (biproduct.isColimit f)

/-- The comparison isomorphism with Mathlib's biproduct intertwines inclusions. -/
@[reassoc (attr := simp)] theorem ι_isoBiproduct_hom (f : J → C)
    [HasDaggerBiproduct f] [HasBiproduct f] (j : J) :
    ι f j ≫ (isoBiproduct f).hom = biproduct.ι f j :=
  (isColimit f).comp_coconePointUniqueUpToIso_hom (biproduct.isColimit f) ⟨j⟩

/-- The comparison isomorphism with Mathlib's biproduct intertwines projections. -/
@[reassoc (attr := simp)] theorem isoBiproduct_hom_π (f : J → C)
    [HasDaggerBiproduct f] [HasBiproduct f] (j : J) :
    (isoBiproduct f).hom ≫ biproduct.π f j = π f j :=
  (isBilimit f).coconePointUniqueUpToIso_hom_π (biproduct.isBilimit f) j

/-- The canonical comparison `daggerBiproduct f ≅ ⨁ f` is unitary if and only if Mathlib's chosen
biproduct bicone is orthogonal. -/
theorem isUnitary_isoBiproduct_iff (f : J → C) [HasDaggerBiproduct f] [HasBiproduct f] :
    IsUnitary (isoBiproduct f).hom ↔ (biproduct.bicone f).IsOrthogonal := by
  constructor
  · intro hu j
    have hinv : dagger (isoBiproduct f).hom = (isoBiproduct f).inv :=
      (isoBiproduct f).dagger_hom_eq_inv_of_isUnitary hu
    calc
      dagger (biproduct.ι f j) = dagger (ι f j ≫ (isoBiproduct f).hom) := by rw [ι_isoBiproduct_hom]
      _ = dagger (isoBiproduct f).hom ≫ dagger (ι f j) := dagger_comp _ _
      _ = (isoBiproduct f).inv ≫ π f j := by rw [hinv, dagger_ι]
      _ = biproduct.π f j := by rw [Iso.inv_comp_eq, isoBiproduct_hom_π]
  · intro ho
    exact Bicone.IsOrthogonal.isUnitary_coconePointUniqueUpToIso
      (isBilimit f) (biproduct.isBilimit f) (bicone_isOrthogonal f) ho

end daggerBiproduct

section Preadditive

variable {C' : Type u₁} [Category.{v₁} C'] [Preadditive C'] [DaggerCategory C']

/-- In a preadditive dagger category, an orthogonal finite bicone whose projections and inclusions
sum to the identity yields a dagger biproduct. -/
theorem hasDaggerBiproduct_of_total [Fintype J] {f : J → C'} (b : Bicone f)
    (ho : b.IsOrthogonal) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt) :
    HasDaggerBiproduct f :=
  HasDaggerBiproduct.mk
    { bicone := b
      isBilimit := isBilimitOfTotal b total
      isOrthogonal := ho }

namespace daggerBiproduct

section Finite

variable [Fintype J] {f : J → C'} [HasDaggerBiproduct f]

/-- The projections and inclusions of a finite orthogonal biproduct sum to the identity. -/
@[simp] theorem total : ∑ j : J, π f j ≫ ι f j = 𝟙 (daggerBiproduct f) :=
  IsBilimit.total (isBilimit f)

/-- A lift into a finite orthogonal biproduct expands as a sum over summands. -/
theorem lift_eq {P : C'} (p : ∀ j, P ⟶ f j) :
    lift p = ∑ j, p j ≫ ι f j := by
  classical
  refine hom_ext _ _ fun j => ?_
  simp [Preadditive.sum_comp, ι_π, comp_dite]

/-- A desc out of a finite orthogonal biproduct expands as a sum over summands. -/
theorem desc_eq {P : C'} (p : ∀ j, f j ⟶ P) :
    desc p = ∑ j, π f j ≫ p j := by
  classical
  refine hom_ext' _ _ fun j => ?_
  simp [Preadditive.comp_sum, ι_π_assoc, dite_comp]

/-- Composing a lift and a desc over a finite orthogonal biproduct yields the inner sum. -/
@[reassoc] theorem lift_desc {P Q : C'} (p : ∀ j, P ⟶ f j) (q : ∀ j, f j ⟶ Q) :
    lift p ≫ desc q = ∑ j, p j ≫ q j := by
  classical
  simp [lift_eq, desc_eq, Preadditive.comp_sum, Preadditive.sum_comp, ι_π_assoc,
    comp_dite, dite_comp]

end Finite

/-- Matrix multiplication for morphisms between finite orthogonal biproducts. -/
@[reassoc] theorem matrix_comp_matrix {L : Type*} [Fintype K] {f : J → C'} {g : K → C'}
    {h : L → C'} [HasDaggerBiproduct f] [HasDaggerBiproduct g] [HasDaggerBiproduct h]
    (m : ∀ j k, f j ⟶ g k) (n : ∀ k l, g k ⟶ h l) :
    matrix m ≫ matrix n = matrix fun j l => ∑ k, m j k ≫ n k l := by
  refine hom_ext _ _ fun l => hom_ext' _ _ fun j => ?_
  simp [lift_desc]

/-- Addition of matrices between orthogonal biproducts is entrywise. -/
theorem matrix_add {f : J → C'} {g : K → C'} [HasDaggerBiproduct f] [HasDaggerBiproduct g]
    (m n : ∀ j k, f j ⟶ g k) :
    matrix (fun j k => m j k + n j k) = matrix m + matrix n := by
  refine hom_ext _ _ fun k => hom_ext' _ _ fun j => ?_
  simp

/-- Scalar multiplication on matrices between orthogonal biproducts is entrywise. -/
@[simp] theorem matrix_smul {R : Type*} [Semiring R] [Linear R C'] {f : J → C'} {g : K → C'}
    [HasDaggerBiproduct f] [HasDaggerBiproduct g] (r : R) (m : ∀ j k, f j ⟶ g k) :
    matrix (fun j k => r • m j k) = r • matrix m := by
  refine hom_ext _ _ fun k => hom_ext' _ _ fun j => ?_
  simp

end daggerBiproduct

end Preadditive

end Indexed

end TauCeti

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [DaggerCategory D]
variable {J : Type w}

/-- A dagger-preserving functor that preserves a biproduct carries a dagger biproduct to a dagger
biproduct. -/
theorem hasDaggerBiproduct_of_preserves (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.PreservesDagger] (f : J → C) [HasDaggerBiproduct f] [PreservesBiproduct f F] :
    HasDaggerBiproduct (fun j => F.obj (f j)) :=
  HasDaggerBiproduct.mk
    { bicone := F.mapBicone (daggerBiproduct.bicone f)
      isBilimit := isBilimitOfPreserves F (daggerBiproduct.isBilimit f)
      isOrthogonal := (daggerBiproduct.bicone_isOrthogonal f).map F }

/-- The canonical isomorphism `F.obj (daggerBiproduct f) ≅ daggerBiproduct (fun j => F.obj (f j))`
for a zero-morphism-preserving functor preserving the biproduct of `f`. -/
def mapDaggerBiproduct (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (f : J → C) [HasDaggerBiproduct f] [PreservesBiproduct f F]
    [HasDaggerBiproduct (fun j => F.obj (f j))] :
    F.obj (daggerBiproduct f) ≅ daggerBiproduct (fun j => F.obj (f j)) :=
  (isBilimitOfPreserves F (daggerBiproduct.isBilimit f)).isColimit.coconePointUniqueUpToIso
    (daggerBiproduct.isColimit (fun j => F.obj (f j)))

/-- The preservation isomorphism intertwines inclusions. -/
@[reassoc (attr := simp)] theorem map_ι_mapDaggerBiproduct_hom (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (f : J → C)
    [HasDaggerBiproduct f] [PreservesBiproduct f F]
    [HasDaggerBiproduct (fun j => F.obj (f j))] (j : J) :
    F.map (daggerBiproduct.ι f j) ≫ (F.mapDaggerBiproduct f).hom =
      daggerBiproduct.ι (fun j => F.obj (f j)) j :=
  (isBilimitOfPreserves F (daggerBiproduct.isBilimit f)).isColimit.comp_coconePointUniqueUpToIso_hom
    (daggerBiproduct.isColimit (fun j => F.obj (f j))) ⟨j⟩

/-- The preservation isomorphism intertwines projections. -/
@[reassoc (attr := simp)] theorem mapDaggerBiproduct_hom_π (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (f : J → C)
    [HasDaggerBiproduct f] [PreservesBiproduct f F]
    [HasDaggerBiproduct (fun j => F.obj (f j))] (j : J) :
    (F.mapDaggerBiproduct f).hom ≫ daggerBiproduct.π (fun j => F.obj (f j)) j =
      F.map (daggerBiproduct.π f j) :=
  (isBilimitOfPreserves F (daggerBiproduct.isBilimit f)).coconePointUniqueUpToIso_hom_π
    (daggerBiproduct.isBilimit (fun j => F.obj (f j))) j

/-- The inverse preservation isomorphism intertwines inclusions. -/
@[reassoc (attr := simp)] theorem ι_mapDaggerBiproduct_inv (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (f : J → C)
    [HasDaggerBiproduct f] [PreservesBiproduct f F]
    [HasDaggerBiproduct (fun j => F.obj (f j))] (j : J) :
    daggerBiproduct.ι (fun j => F.obj (f j)) j ≫ (F.mapDaggerBiproduct f).inv =
      F.map (daggerBiproduct.ι f j) := by
  rw [Iso.comp_inv_eq, map_ι_mapDaggerBiproduct_hom]

/-- The canonical preservation isomorphism `F.mapDaggerBiproduct f` is unitary. -/
theorem isUnitary_mapDaggerBiproduct (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.PreservesDagger] (f : J → C) [HasDaggerBiproduct f] [PreservesBiproduct f F]
    [HasDaggerBiproduct (fun j => F.obj (f j))] : IsUnitary (F.mapDaggerBiproduct f).hom :=
  Bicone.IsOrthogonal.isUnitary_coconePointUniqueUpToIso
    (isBilimitOfPreserves F (daggerBiproduct.isBilimit f))
    (daggerBiproduct.isBilimit (fun j => F.obj (f j)))
    ((daggerBiproduct.bicone_isOrthogonal f).map F)
    (daggerBiproduct.bicone_isOrthogonal (fun j => F.obj (f j)))

end CategoryTheory.Functor
