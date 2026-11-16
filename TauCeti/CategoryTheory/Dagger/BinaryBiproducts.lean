/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Dagger.Biproducts

/-!
# Binary orthogonal biproducts in dagger categories

An orthogonal binary bicone for a pair `P, Q` in a dagger category with zero morphisms is a
`BinaryBicone P Q` whose projections are the daggers of its inclusions:
`dagger b.inl = b.fst` and `dagger b.inr = b.snd`.

This module develops `BinaryBicone.IsOrthogonal`, uniqueness of orthogonal binary bilimit bicones
up to unique unitary isomorphism, the classes `HasBinaryDaggerBiproduct` and
`HasBinaryDaggerBiproducts`, and the chosen binary orthogonal biproduct `daggerBiprod P Q` together
with its dagger identities and comparison with Mathlib's `P ⊞ Q`.

## Main definitions and results

* `CategoryTheory.Limits.BinaryBicone.IsOrthogonal`: orthogonality predicate on native binary
  bicones, together with unitary uniqueness (`isUnitary_coconePointUniqueUpToIso`).
* `TauCeti.HasBinaryDaggerBiproduct`, `TauCeti.HasBinaryDaggerBiproducts`: existence of binary
  dagger biproducts, implied by `HasFiniteDaggerBiproducts` and implying Mathlib's
  `HasBinaryBiproducts`.
* `TauCeti.daggerBiprod`: chosen binary orthogonal biproducts, dagger formulas (`dagger_lift`,
  `dagger_desc`, `dagger_map`), and comparison with native `biprod` (`isoBiprod`,
  `isUnitary_isoBiprod_iff`).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TauCeti

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

namespace BinaryBicone

variable {P Q : C}

/-- The canonical isomorphism between two binary bilimit bicones commutes with the first
projection. -/
theorem IsBilimit.coconePointUniqueUpToIso_hom_fst {b₁ b₂ : BinaryBicone P Q}
    (hb₁ : b₁.IsBilimit) (hb₂ : b₂.IsBilimit) :
    (hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit).hom ≫ b₂.fst = b₁.fst := by
  let e : b₁.pt ≅ b₂.pt := hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit
  refine hb₁.isColimit.hom_ext fun ⟨j⟩ => ?_
  cases j
  · have h : b₁.inl ≫ e.hom = b₂.inl :=
      hb₁.isColimit.comp_coconePointUniqueUpToIso_hom hb₂.isColimit ⟨WalkingPair.left⟩
    exact (Category.assoc b₁.inl e.hom b₂.fst).symm.trans (by simp [h])
  · have h : b₁.inr ≫ e.hom = b₂.inr :=
      hb₁.isColimit.comp_coconePointUniqueUpToIso_hom hb₂.isColimit ⟨WalkingPair.right⟩
    exact (Category.assoc b₁.inr e.hom b₂.fst).symm.trans (by simp [h])

/-- The canonical isomorphism between two binary bilimit bicones commutes with the second
projection. -/
theorem IsBilimit.coconePointUniqueUpToIso_hom_snd {b₁ b₂ : BinaryBicone P Q}
    (hb₁ : b₁.IsBilimit) (hb₂ : b₂.IsBilimit) :
    (hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit).hom ≫ b₂.snd = b₁.snd := by
  let e : b₁.pt ≅ b₂.pt := hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit
  refine hb₁.isColimit.hom_ext fun ⟨j⟩ => ?_
  cases j
  · have h : b₁.inl ≫ e.hom = b₂.inl :=
      hb₁.isColimit.comp_coconePointUniqueUpToIso_hom hb₂.isColimit ⟨WalkingPair.left⟩
    exact (Category.assoc b₁.inl e.hom b₂.snd).symm.trans (by simp [h])
  · have h : b₁.inr ≫ e.hom = b₂.inr :=
      hb₁.isColimit.comp_coconePointUniqueUpToIso_hom hb₂.isColimit ⟨WalkingPair.right⟩
    exact (Category.assoc b₁.inr e.hom b₂.snd).symm.trans (by simp [h])

section Dagger

variable [DaggerCategory C] [DaggerCategory D]

/-- A binary bicone in a dagger category is orthogonal when its projections are the daggers of its
inclusions. -/
def IsOrthogonal (b : BinaryBicone P Q) : Prop :=
  dagger b.inl = b.fst ∧ dagger b.inr = b.snd

/-- Characterization of an orthogonal binary bicone. -/
theorem isOrthogonal_iff (b : BinaryBicone P Q) :
    b.IsOrthogonal ↔ dagger b.inl = b.fst ∧ dagger b.inr = b.snd := Iff.rfl

namespace IsOrthogonal

/-- The dagger of the left inclusion of an orthogonal binary bicone is the first projection. -/
theorem dagger_inl {b : BinaryBicone P Q} (hb : b.IsOrthogonal) : dagger b.inl = b.fst := hb.1

/-- The dagger of the right inclusion of an orthogonal binary bicone is the second projection. -/
theorem dagger_inr {b : BinaryBicone P Q} (hb : b.IsOrthogonal) : dagger b.inr = b.snd := hb.2

/-- The dagger of the first projection of an orthogonal binary bicone is the left inclusion. -/
theorem dagger_fst {b : BinaryBicone P Q} (hb : b.IsOrthogonal) : dagger b.fst = b.inl := by
  rw [← hb.1, dagger_dagger]

/-- The dagger of the second projection of an orthogonal binary bicone is the right inclusion. -/
theorem dagger_snd {b : BinaryBicone P Q} (hb : b.IsOrthogonal) : dagger b.snd = b.inr := by
  rw [← hb.2, dagger_dagger]

/-- Orthogonality of a binary bicone may equivalently be verified on projections. -/
theorem of_dagger_fst_snd {b : BinaryBicone P Q}
    (hfst : dagger b.fst = b.inl) (hsnd : dagger b.snd = b.inr) : b.IsOrthogonal :=
  ⟨by rw [← hfst, dagger_dagger], by rw [← hsnd, dagger_dagger]⟩

/-- Converting an orthogonal binary bicone to a `Bicone` over `WalkingPair` preserves
orthogonality. -/
theorem toBicone {b : BinaryBicone P Q} (hb : b.IsOrthogonal) :
    b.toBicone.IsOrthogonal :=
  (Bicone.isOrthogonal_iff _).mpr fun j => by
    cases j
    · exact hb.1
    · exact hb.2

/-- A dagger-preserving functor preserving zero morphisms maps orthogonal binary bicones to
orthogonal binary bicones. -/
theorem map {b : BinaryBicone P Q} (hb : b.IsOrthogonal) (G : C ⥤ D) [G.PreservesZeroMorphisms]
    [G.PreservesDagger] : (G.mapBinaryBicone b).IsOrthogonal :=
  ⟨(G.map_dagger b.inl).symm.trans (congrArg G.map hb.1),
   (G.map_dagger b.inr).symm.trans (congrArg G.map hb.2)⟩

/-- The canonical isomorphism between two orthogonal binary bilimit bicones is unitary. -/
theorem isUnitary_coconePointUniqueUpToIso {b₁ b₂ : BinaryBicone P Q}
    (hb₁ : b₁.IsBilimit) (hb₂ : b₂.IsBilimit)
    (ho₁ : b₁.IsOrthogonal) (ho₂ : b₂.IsOrthogonal) :
    IsUnitary (hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit).hom := by
  let e : b₁.pt ≅ b₂.pt := hb₁.isColimit.coconePointUniqueUpToIso hb₂.isColimit
  refine e.isUnitary_hom_iff.mpr ?_
  refine hb₁.isLimit.hom_ext fun ⟨j⟩ => ?_
  cases j
  · have hι : b₁.inl ≫ e.hom = b₂.inl :=
      hb₁.isColimit.comp_coconePointUniqueUpToIso_hom hb₂.isColimit ⟨WalkingPair.left⟩
    have hπ : e.inv ≫ b₁.fst = b₂.fst :=
      e.inv_comp_eq.mpr (hb₁.coconePointUniqueUpToIso_hom_fst hb₂).symm
    simp only [BinaryBicone.toCone_π_app_left]
    calc
      dagger e.hom ≫ b₁.fst = dagger e.hom ≫ dagger b₁.inl := by rw [ho₁.dagger_inl]
      _ = dagger (b₁.inl ≫ e.hom) := (dagger_comp _ _).symm
      _ = dagger b₂.inl := by rw [hι]
      _ = b₂.fst := ho₂.dagger_inl
      _ = e.inv ≫ b₁.fst := hπ.symm
  · have hι : b₁.inr ≫ e.hom = b₂.inr :=
      hb₁.isColimit.comp_coconePointUniqueUpToIso_hom hb₂.isColimit ⟨WalkingPair.right⟩
    have hπ : e.inv ≫ b₁.snd = b₂.snd :=
      e.inv_comp_eq.mpr (hb₁.coconePointUniqueUpToIso_hom_snd hb₂).symm
    simp only [BinaryBicone.toCone_π_app_right]
    calc
      dagger e.hom ≫ b₁.snd = dagger e.hom ≫ dagger b₁.inr := by rw [ho₁.dagger_inr]
      _ = dagger (b₁.inr ≫ e.hom) := (dagger_comp _ _).symm
      _ = dagger b₂.inr := by rw [hι]
      _ = b₂.snd := ho₂.dagger_inr
      _ = e.inv ≫ b₁.snd := hπ.symm

end IsOrthogonal

end Dagger

end BinaryBicone

/-- Converting an orthogonal `Bicone` over `WalkingPair` to a `BinaryBicone` preserves
orthogonality. -/
theorem Bicone.IsOrthogonal.toBinaryBicone [DaggerCategory C] {P Q : C}
    {b : Bicone (pairFunction P Q)} (hb : b.IsOrthogonal) : b.toBinaryBicone.IsOrthogonal :=
  ⟨hb.dagger_ι WalkingPair.left, hb.dagger_ι WalkingPair.right⟩

end CategoryTheory.Limits

namespace TauCeti

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [DaggerCategory C]

/-- An orthogonal binary bilimit bicone over `P` and `Q`. -/
structure BinaryDaggerBiproductData (P Q : C) extends BinaryBiproductData P Q where
  /-- The projections are the daggers of the inclusions. -/
  isOrthogonal : bicone.IsOrthogonal

/-- `HasBinaryDaggerBiproduct P Q` expresses the existence of an orthogonal binary bilimit bicone
over `P` and `Q`. -/
class HasBinaryDaggerBiproduct (P Q : C) : Prop where mk' ::
  /-- There exists an orthogonal binary bilimit bicone over `P` and `Q`. -/
  exists_binary_daggerBiproduct : Nonempty (BinaryDaggerBiproductData P Q)

/-- Construct `HasBinaryDaggerBiproduct P Q` from explicit orthogonal binary biproduct data. -/
theorem HasBinaryDaggerBiproduct.mk {P Q : C} (d : BinaryDaggerBiproductData P Q) :
    HasBinaryDaggerBiproduct P Q :=
  ⟨Nonempty.intro d⟩

/-- Extract a chosen orthogonal binary bilimit bicone from `HasBinaryDaggerBiproduct P Q`. -/
def getBinaryDaggerBiproductData (P Q : C) [HasBinaryDaggerBiproduct P Q] :
    BinaryDaggerBiproductData P Q :=
  Classical.choice HasBinaryDaggerBiproduct.exists_binary_daggerBiproduct

/-- The chosen orthogonal binary bicone for `P` and `Q`. -/
def daggerBiprod.bicone (P Q : C) [HasBinaryDaggerBiproduct P Q] : BinaryBicone P Q :=
  (getBinaryDaggerBiproductData P Q).bicone

/-- The chosen binary dagger biproduct bicone is orthogonal. -/
theorem daggerBiprod.bicone_isOrthogonal (P Q : C) [HasBinaryDaggerBiproduct P Q] :
    (daggerBiprod.bicone P Q).IsOrthogonal :=
  (getBinaryDaggerBiproductData P Q).isOrthogonal

/-- The chosen binary dagger biproduct bicone is a bilimit bicone. -/
def daggerBiprod.isBilimit (P Q : C) [HasBinaryDaggerBiproduct P Q] :
    (daggerBiprod.bicone P Q).IsBilimit :=
  (getBinaryDaggerBiproductData P Q).isBilimit

/-- Every binary dagger biproduct yields a native binary biproduct. -/
instance (priority := 100) hasBinaryBiproduct_of_hasBinaryDaggerBiproduct (P Q : C)
    [HasBinaryDaggerBiproduct P Q] : HasBinaryBiproduct P Q :=
  HasBinaryBiproduct.mk (getBinaryDaggerBiproductData P Q).toBinaryBiproductData

/-- `C` has binary dagger biproducts if every pair of objects admits a binary dagger biproduct. -/
class HasBinaryDaggerBiproducts (C : Type u₁) [Category.{v₁} C]
    [HasZeroMorphisms C] [DaggerCategory C] : Prop where
  /-- Every pair of objects admits a binary dagger biproduct. -/
  has_binary_daggerBiproduct : ∀ P Q : C, HasBinaryDaggerBiproduct P Q

attribute [instance 100] HasBinaryDaggerBiproducts.has_binary_daggerBiproduct

/-- A category with binary dagger biproducts has native binary biproducts. -/
instance (priority := 100) hasBinaryBiproducts_of_hasBinaryDaggerBiproducts
    [HasBinaryDaggerBiproducts C] : HasBinaryBiproducts C :=
  ⟨fun P Q => hasBinaryBiproduct_of_hasBinaryDaggerBiproduct P Q⟩

/-- A category with finite dagger biproducts has binary dagger biproducts. -/
theorem hasBinaryDaggerBiproducts_of_finite_daggerBiproducts (C : Type u₁) [Category.{v₁} C]
    [HasZeroMorphisms C] [DaggerCategory C] [HasFiniteDaggerBiproducts C] :
    HasBinaryDaggerBiproducts C :=
  ⟨fun P Q =>
    HasBinaryDaggerBiproduct.mk
      { bicone := (daggerBiproduct.bicone (pairFunction P Q)).toBinaryBicone
        isBilimit :=
          (Bicone.toBinaryBiconeIsBilimit _).symm (daggerBiproduct.isBilimit _)
        isOrthogonal := (daggerBiproduct.bicone_isOrthogonal _).toBinaryBicone }⟩

/-- The chosen binary orthogonal biproduct object of `P` and `Q`. -/
abbrev daggerBiprod (P Q : C) [HasBinaryDaggerBiproduct P Q] : C :=
  (daggerBiprod.bicone P Q).pt

namespace daggerBiprod

variable {P Q R S : C}

/-- First projection of a binary orthogonal biproduct. -/
abbrev fst [HasBinaryDaggerBiproduct P Q] : daggerBiprod P Q ⟶ P := (bicone P Q).fst

/-- Second projection of a binary orthogonal biproduct. -/
abbrev snd [HasBinaryDaggerBiproduct P Q] : daggerBiprod P Q ⟶ Q := (bicone P Q).snd

/-- Left inclusion of a binary orthogonal biproduct. -/
abbrev inl [HasBinaryDaggerBiproduct P Q] : P ⟶ daggerBiprod P Q := (bicone P Q).inl

/-- Right inclusion of a binary orthogonal biproduct. -/
abbrev inr [HasBinaryDaggerBiproduct P Q] : Q ⟶ daggerBiprod P Q := (bicone P Q).inr

/-- The dagger of the left inclusion is the first projection. -/
@[simp, grind =] theorem dagger_inl [HasBinaryDaggerBiproduct P Q] :
    dagger (inl (P := P) (Q := Q)) = fst :=
  (bicone_isOrthogonal P Q).dagger_inl

/-- The dagger of the right inclusion is the second projection. -/
@[simp, grind =] theorem dagger_inr [HasBinaryDaggerBiproduct P Q] :
    dagger (inr (P := P) (Q := Q)) = snd :=
  (bicone_isOrthogonal P Q).dagger_inr

/-- The dagger of the first projection is the left inclusion. -/
@[simp, grind =] theorem dagger_fst [HasBinaryDaggerBiproduct P Q] :
    dagger (fst (P := P) (Q := Q)) = inl :=
  (bicone_isOrthogonal P Q).dagger_fst

/-- The dagger of the second projection is the right inclusion. -/
@[simp, grind =] theorem dagger_snd [HasBinaryDaggerBiproduct P Q] :
    dagger (snd (P := P) (Q := Q)) = inr :=
  (bicone_isOrthogonal P Q).dagger_snd

/-- Lift a pair of morphisms into a binary orthogonal biproduct. -/
abbrev lift [HasBinaryDaggerBiproduct P Q] (f : R ⟶ P) (g : R ⟶ Q) :
    R ⟶ daggerBiprod P Q :=
  (isBilimit P Q).isLimit.lift (BinaryFan.mk f g)

/-- Descend a pair of morphisms out of a binary orthogonal biproduct. -/
abbrev desc [HasBinaryDaggerBiproduct P Q] (f : P ⟶ R) (g : Q ⟶ R) :
    daggerBiprod P Q ⟶ R :=
  (isBilimit P Q).isColimit.desc (BinaryCofan.mk f g)

/-- First projection of a binary lift. -/
@[reassoc (attr := simp)] theorem lift_fst [HasBinaryDaggerBiproduct P Q]
    (f : R ⟶ P) (g : R ⟶ Q) : lift f g ≫ fst = f :=
  (isBilimit P Q).isLimit.fac _ ⟨WalkingPair.left⟩

/-- Second projection of a binary lift. -/
@[reassoc (attr := simp)] theorem lift_snd [HasBinaryDaggerBiproduct P Q]
    (f : R ⟶ P) (g : R ⟶ Q) : lift f g ≫ snd = g :=
  (isBilimit P Q).isLimit.fac _ ⟨WalkingPair.right⟩

/-- Left restriction of a binary desc. -/
@[reassoc (attr := simp)] theorem inl_desc [HasBinaryDaggerBiproduct P Q]
    (f : P ⟶ R) (g : Q ⟶ R) : inl ≫ desc f g = f :=
  (isBilimit P Q).isColimit.fac _ ⟨WalkingPair.left⟩

/-- Right restriction of a binary desc. -/
@[reassoc (attr := simp)] theorem inr_desc [HasBinaryDaggerBiproduct P Q]
    (f : P ⟶ R) (g : Q ⟶ R) : inr ≫ desc f g = g :=
  (isBilimit P Q).isColimit.fac _ ⟨WalkingPair.right⟩

/-- Two morphisms into a binary orthogonal biproduct are equal when both projections agree. -/
@[ext 1001] theorem hom_ext [HasBinaryDaggerBiproduct P Q] {f g : R ⟶ daggerBiprod P Q}
    (h₁ : f ≫ fst = g ≫ fst) (h₂ : f ≫ snd = g ≫ snd) : f = g :=
  (isBilimit P Q).isLimit.hom_ext fun ⟨j⟩ => by cases j <;> assumption

/-- Two morphisms out of a binary orthogonal biproduct are equal when both restrictions agree. -/
@[ext] theorem hom_ext' [HasBinaryDaggerBiproduct P Q] {f g : daggerBiprod P Q ⟶ R}
    (h₁ : inl ≫ f = inl ≫ g) (h₂ : inr ≫ f = inr ≫ g) : f = g :=
  (isBilimit P Q).isColimit.hom_ext fun ⟨j⟩ => by cases j <;> assumption

/-- Taking the dagger turns a binary lift into a binary desc of the daggers. -/
@[simp] theorem dagger_lift [HasBinaryDaggerBiproduct P Q] (f : R ⟶ P) (g : R ⟶ Q) :
    dagger (lift f g) = desc (dagger f) (dagger g) := by
  refine hom_ext' ?_ ?_
  · rw [inl_desc, ← dagger_fst, ← dagger_comp, lift_fst]
  · rw [inr_desc, ← dagger_snd, ← dagger_comp, lift_snd]

/-- Taking the dagger turns a binary desc into a binary lift of the daggers. -/
@[simp] theorem dagger_desc [HasBinaryDaggerBiproduct P Q] (f : P ⟶ R) (g : Q ⟶ R) :
    dagger (desc f g) = lift (dagger f) (dagger g) := by
  refine hom_ext ?_ ?_
  · rw [lift_fst, ← dagger_inl, ← dagger_comp, inl_desc]
  · rw [lift_snd, ← dagger_inr, ← dagger_comp, inr_desc]

/-- Diagonal morphism between binary orthogonal biproducts. -/
def map [HasBinaryDaggerBiproduct P Q] [HasBinaryDaggerBiproduct R S]
    (f : P ⟶ R) (g : Q ⟶ S) : daggerBiprod P Q ⟶ daggerBiprod R S :=
  lift (fst ≫ f) (snd ≫ g)

/-- First projection of a diagonal binary map. -/
@[reassoc (attr := simp)] theorem map_fst [HasBinaryDaggerBiproduct P Q]
    [HasBinaryDaggerBiproduct R S] (f : P ⟶ R) (g : Q ⟶ S) :
    map f g ≫ fst = fst ≫ f :=
  lift_fst _ _

/-- Second projection of a diagonal binary map. -/
@[reassoc (attr := simp)] theorem map_snd [HasBinaryDaggerBiproduct P Q]
    [HasBinaryDaggerBiproduct R S] (f : P ⟶ R) (g : Q ⟶ S) :
    map f g ≫ snd = snd ≫ g :=
  lift_snd _ _

/-- Left inclusion into a diagonal binary map. -/
@[reassoc (attr := simp)] theorem inl_map [HasBinaryDaggerBiproduct P Q]
    [HasBinaryDaggerBiproduct R S] (f : P ⟶ R) (g : Q ⟶ S) :
    inl ≫ map f g = f ≫ inl := by
  refine hom_ext ?_ ?_ <;> simp

/-- Right inclusion into a diagonal binary map. -/
@[reassoc (attr := simp)] theorem inr_map [HasBinaryDaggerBiproduct P Q]
    [HasBinaryDaggerBiproduct R S] (f : P ⟶ R) (g : Q ⟶ S) :
    inr ≫ map f g = g ≫ inr := by
  refine hom_ext ?_ ?_ <;> simp

/-- Taking the dagger acts componentwise on binary diagonal maps. -/
@[simp] theorem dagger_map [HasBinaryDaggerBiproduct P Q] [HasBinaryDaggerBiproduct R S]
    (f : P ⟶ R) (g : Q ⟶ S) : dagger (map f g) = map (dagger f) (dagger g) := by
  refine hom_ext ?_ ?_
  · rw [map_fst, ← dagger_inl, ← dagger_comp, inl_map, dagger_comp, dagger_inl]
  · rw [map_snd, ← dagger_inr, ← dagger_comp, inr_map, dagger_comp, dagger_inr]

/-- Canonical comparison isomorphism with Mathlib's chosen binary biproduct. -/
def isoBiprod (P Q : C) [HasBinaryDaggerBiproduct P Q] [HasBinaryBiproduct P Q] :
    daggerBiprod P Q ≅ P ⊞ Q :=
  (isBilimit P Q).isColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit P Q)

/-- The comparison `daggerBiprod P Q ≅ P ⊞ Q` is unitary if and only if Mathlib's chosen binary
biproduct bicone is orthogonal. -/
theorem isUnitary_isoBiprod_iff (P Q : C) [HasBinaryDaggerBiproduct P Q]
    [HasBinaryBiproduct P Q] :
    IsUnitary (isoBiprod P Q).hom ↔ (BinaryBiproduct.bicone P Q).IsOrthogonal := by
  constructor
  · intro hu
    have hinv : dagger (isoBiprod P Q).hom = (isoBiprod P Q).inv :=
      (isoBiprod P Q).dagger_hom_eq_inv_of_isUnitary hu
    have hinl : inl ≫ (isoBiprod P Q).hom = biprod.inl :=
      (isBilimit P Q).isColimit.comp_coconePointUniqueUpToIso_hom
        (BinaryBiproduct.isColimit P Q) ⟨WalkingPair.left⟩
    have hinr : inr ≫ (isoBiprod P Q).hom = biprod.inr :=
      (isBilimit P Q).isColimit.comp_coconePointUniqueUpToIso_hom
        (BinaryBiproduct.isColimit P Q) ⟨WalkingPair.right⟩
    have hfst : (isoBiprod P Q).hom ≫ biprod.fst = fst :=
      (isBilimit P Q).coconePointUniqueUpToIso_hom_fst (BinaryBiproduct.isBilimit P Q)
    have hsnd : (isoBiprod P Q).hom ≫ biprod.snd = snd :=
      (isBilimit P Q).coconePointUniqueUpToIso_hom_snd (BinaryBiproduct.isBilimit P Q)
    constructor
    · calc
        dagger (BinaryBiproduct.bicone P Q).inl = dagger (inl ≫ (isoBiprod P Q).hom) := by
          rw [hinl]
        _ = (isoBiprod P Q).inv ≫ fst := by rw [dagger_comp, hinv, dagger_inl]
        _ = (BinaryBiproduct.bicone P Q).fst := by rw [Iso.inv_comp_eq, hfst]
    · calc
        dagger (BinaryBiproduct.bicone P Q).inr = dagger (inr ≫ (isoBiprod P Q).hom) := by
          rw [hinr]
        _ = (isoBiprod P Q).inv ≫ snd := by rw [dagger_comp, hinv, dagger_inr]
        _ = (BinaryBiproduct.bicone P Q).snd := by rw [Iso.inv_comp_eq, hsnd]
  · intro ho
    exact BinaryBicone.IsOrthogonal.isUnitary_coconePointUniqueUpToIso
      (isBilimit P Q) (BinaryBiproduct.isBilimit P Q) (bicone_isOrthogonal P Q) ho

end daggerBiprod

section Preadditive

variable {C' : Type u₁} [Category.{v₁} C'] [Preadditive C'] [DaggerCategory C'] {P Q : C'}

/-- The binary orthogonal biproduct decomposition of the identity. -/
@[simp] theorem daggerBiprod.total [HasBinaryDaggerBiproduct P Q] :
    daggerBiprod.fst ≫ daggerBiprod.inl + daggerBiprod.snd ≫ daggerBiprod.inr =
      𝟙 (daggerBiprod P Q) := by
  refine daggerBiprod.hom_ext ?_ ?_ <;> simp

/-- In a preadditive category, `daggerBiprod.lift f g` is `f ≫ inl + g ≫ inr`. -/
theorem daggerBiprod.lift_eq [HasBinaryDaggerBiproduct P Q] {W : C'} (f : W ⟶ P) (g : W ⟶ Q) :
    daggerBiprod.lift f g = f ≫ daggerBiprod.inl + g ≫ daggerBiprod.inr := by
  refine daggerBiprod.hom_ext ?_ ?_ <;> simp

/-- In a preadditive category, `daggerBiprod.desc f g` is `fst ≫ f + snd ≫ g`. -/
theorem daggerBiprod.desc_eq [HasBinaryDaggerBiproduct P Q] {W : C'} (f : P ⟶ W) (g : Q ⟶ W) :
    daggerBiprod.desc f g = daggerBiprod.fst ≫ f + daggerBiprod.snd ≫ g := by
  refine daggerBiprod.hom_ext' ?_ ?_ <;> simp

/-- The composition `lift f g ≫ desc h k` expands as `f ≫ h + g ≫ k`. -/
@[simp] theorem daggerBiprod.lift_desc [HasBinaryDaggerBiproduct P Q] {W Z : C'}
    (f : W ⟶ P) (g : W ⟶ Q) (h : P ⟶ Z) (k : Q ⟶ Z) :
    daggerBiprod.lift f g ≫ daggerBiprod.desc h k = f ≫ h + g ≫ k := by
  rw [daggerBiprod.desc_eq, Preadditive.comp_add, daggerBiprod.lift_fst_assoc,
    daggerBiprod.lift_snd_assoc]

/-- In a preadditive dagger category, an orthogonal binary bicone whose projections and inclusions
sum to the identity yields a binary dagger biproduct. -/
theorem hasBinaryDaggerBiproduct_of_total (b : BinaryBicone P Q) (ho : b.IsOrthogonal)
    (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) :
    HasBinaryDaggerBiproduct P Q :=
  HasBinaryDaggerBiproduct.mk
    { bicone := b
      isBilimit := isBinaryBilimitOfTotal b total
      isOrthogonal := ho }

end Preadditive

end TauCeti
