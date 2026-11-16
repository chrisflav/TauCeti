/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Retract
public import TauCeti.CategoryTheory.Dagger.BinaryBiproducts

/-!
# Dagger isometries, projections, and unitary splittings

In a dagger category, a *dagger isometry* is an arrow `v : Y ⟶ X` satisfying `v ≫ dagger v = 𝟙 Y`,
and a *dagger projection* is a self-adjoint idempotent `p : X ⟶ X`, i.e. `p ≫ p = p` and
`dagger p = p`. A *dagger splitting* (or *unitary splitting*) of an endomorphism `p : X ⟶ X` is an
object `Y` together with a dagger isometry `v : Y ⟶ X` whose range projection `dagger v ≫ v` equals
`p`.

Any endomorphism admitting a dagger splitting is automatically a dagger projection; in particular,
non-self-adjoint idempotents cannot be dagger-split. Two dagger splittings of the same projection
are related by a unique unitary isomorphism compatible with their isometric inclusions, and
unitary conjugacy of projections transports dagger splittings along unitary isomorphisms.

In a preadditive category, an idempotent `e` sharing the same range equations (`e ≫ p = e` and
`p ≫ e = p`) with another idempotent `p` is similar to `p` via the explicit isomorphism
`𝟙 X + e - p`. When `p` is dagger-split, any algebraic retract splitting `e` is isomorphic to the
dagger splitting of `p`, and this comparison is compatible with the retraction if and only if
`e = p`.

## Main definitions and results

* `TauCeti.IsDaggerIsometry`: arrows `v` with `v ≫ dagger v = 𝟙 _`.
* `TauCeti.IsDaggerProjection`: self-adjoint idempotents, identified with `IsStarProjection` on
  `CategoryTheory.End`.
* `TauCeti.DaggerSplitting` and `TauCeti.IsDaggerSplit`: unitary splittings of projections, with
  unitary uniqueness (`DaggerSplitting.iso`, `DaggerSplitting.isUnitary_iso`,
  `DaggerSplitting.eq_iso_hom_of_comp_eq`) and unitary conjugacy transport
  (`DaggerSplitting.ofUnitaryConj`).
* `TauCeti.sameRangeSimilarityIso`: explicit similarity `𝟙 X + e - p` between idempotents with the
  same range equations.
* `TauCeti.retractIsoDaggerSplitting`: comparison between an algebraic retract of `e` and a dagger
  splitting of `p`, characterizing when the comparison is unitary and when the retraction agrees
  with the dagger of the isometric inclusion.
* `TauCeti.IsDaggerIdempotentComplete`: class expressing that every dagger projection splits,
  together with `isIdempotentComplete_of_exists_similar_projection`.

## References

* P. Selinger, *Idempotents in dagger categories*, Electronic Notes in Theoretical Computer
  Science 210 (2008), 107–122.
* C. Heunen and J. Vicary, *Categories for Quantum Theory: An Introduction*,
  Oxford University Press (2019).
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti

universe v₁ v₂ u₁ u₂

namespace TauCeti

variable {C : Type u₁} [Category.{v₁} C]

section Similarity

variable [Preadditive C] {X : C}

/-- Two idempotents `e, p : X ⟶ X` satisfying the same-range equations `e ≫ p = e` and `p ≫ e = p`
are similar via `𝟙 X + e - p`, with inverse `𝟙 X + p - e`. -/
def sameRangeSimilarityIso {e p : X ⟶ X} (he : e ≫ e = e) (hp : p ≫ p = p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) : X ≅ X where
  hom := 𝟙 X + e - p
  inv := 𝟙 X + p - e
  hom_inv_id := by
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.comp_add,
      Preadditive.add_comp, Category.id_comp, Category.comp_id, he, hp, hep, hpe]
    abel
  inv_hom_id := by
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.comp_add,
      Preadditive.add_comp, Category.id_comp, Category.comp_id, he, hp, hep, hpe]
    abel

/-- The forward arrow of `sameRangeSimilarityIso` is `𝟙 X + e - p`. -/
@[simp] theorem sameRangeSimilarityIso_hom {e p : X ⟶ X} (he : e ≫ e = e) (hp : p ≫ p = p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) :
    (sameRangeSimilarityIso he hp hep hpe).hom = 𝟙 X + e - p := (rfl)

/-- The inverse arrow of `sameRangeSimilarityIso` is `𝟙 X + p - e`. -/
@[simp] theorem sameRangeSimilarityIso_inv {e p : X ⟶ X} (he : e ≫ e = e) (hp : p ≫ p = p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) :
    (sameRangeSimilarityIso he hp hep hpe).inv = 𝟙 X + p - e := (rfl)

/-- Conjugating `e` by `sameRangeSimilarityIso` yields `p`. -/
theorem sameRangeSimilarityIso_inv_comp_comp_hom {e p : X ⟶ X} (he : e ≫ e = e) (hp : p ≫ p = p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) :
    (sameRangeSimilarityIso he hp hep hpe).inv ≫ e ≫
      (sameRangeSimilarityIso he hp hep hpe).hom = p := by
  simp only [sameRangeSimilarityIso_hom, sameRangeSimilarityIso_inv, Preadditive.comp_sub,
    Preadditive.sub_comp, Preadditive.comp_add, Preadditive.add_comp, Category.id_comp,
    Category.comp_id, he, hep, hpe]
  abel

/-- Conjugating `p` by the inverse of `sameRangeSimilarityIso` recovers `e`. -/
theorem sameRangeSimilarityIso_hom_comp_comp_inv {e p : X ⟶ X} (he : e ≫ e = e) (hp : p ≫ p = p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) :
    (sameRangeSimilarityIso he hp hep hpe).hom ≫ p ≫
      (sameRangeSimilarityIso he hp hep hpe).inv = e := by
  simp only [sameRangeSimilarityIso_hom, sameRangeSimilarityIso_inv, Preadditive.comp_sub,
    Preadditive.sub_comp, Preadditive.comp_add, Preadditive.add_comp, Category.id_comp,
    Category.comp_id, hp, hep, hpe]
  abel

end Similarity

variable [DaggerCategory C]
variable {W X Y Z : C}

/-- An arrow `v : Y ⟶ X` in a dagger category is a dagger isometry when `v ≫ dagger v = 𝟙 Y`. -/
def IsDaggerIsometry (v : Y ⟶ X) : Prop :=
  v ≫ dagger v = 𝟙 Y

/-- Characterization of a dagger isometry. -/
theorem isDaggerIsometry_iff (v : Y ⟶ X) :
    IsDaggerIsometry v ↔ v ≫ dagger v = 𝟙 Y := Iff.rfl

namespace IsDaggerIsometry

/-- A dagger isometry composed with its dagger is the identity on its domain. -/
@[reassoc (attr := simp), grind =] theorem hom_dagger_id {v : Y ⟶ X} (hv : IsDaggerIsometry v) :
    v ≫ dagger v = 𝟙 Y := hv

/-- Identity arrows are dagger isometries. -/
@[simp] theorem id (X : C) : IsDaggerIsometry (𝟙 X) := by
  simp [isDaggerIsometry_iff]

/-- Equality arrows are dagger isometries. -/
@[simp] theorem eqToHom (h : X = Y) : IsDaggerIsometry (CategoryTheory.eqToHom h) := by
  cases h
  simp

/-- Composites of dagger isometries are dagger isometries. -/
theorem comp {v : X ⟶ Y} {w : Y ⟶ Z} (hv : IsDaggerIsometry v) (hw : IsDaggerIsometry w) :
    IsDaggerIsometry (v ≫ w) := by
  rw [isDaggerIsometry_iff, dagger_comp, Category.assoc, hw.hom_dagger_id_assoc, hv.hom_dagger_id]

/-- Every unitary arrow is a dagger isometry. -/
theorem of_isUnitary {u : X ⟶ Y} (hu : IsUnitary u) : IsDaggerIsometry u :=
  hu.hom_dagger_id

/-- An invertible dagger isometry is unitary. -/
theorem isUnitary_of_isIso {v : X ⟶ Y} (hv : IsDaggerIsometry v) [IsIso v] : IsUnitary v := by
  have hd : dagger v = inv v :=
    (cancel_epi v).mp (hv.hom_dagger_id.trans (IsIso.hom_inv_id v).symm)
  exact (isUnitary_iff v).mpr ⟨hv.hom_dagger_id, by rw [hd, IsIso.inv_hom_id]⟩

/-- A dagger isometry is a split monomorphism with retraction `dagger v`. -/
def splitMono {v : Y ⟶ X} (hv : IsDaggerIsometry v) : SplitMono v where
  retraction := dagger v
  id := hv

/-- A dagger isometry is a monomorphism. -/
theorem mono {v : Y ⟶ X} (hv : IsDaggerIsometry v) : Mono v :=
  let _ : IsSplitMono v := ⟨⟨hv.splitMono⟩⟩
  inferInstance

/-- The range endomorphism `dagger v ≫ v` of a dagger isometry is idempotent. -/
@[reassoc] theorem dagger_comp_self_idem {v : Y ⟶ X} (hv : IsDaggerIsometry v) :
    (dagger v ≫ v) ≫ (dagger v ≫ v) = dagger v ≫ v := by
  rw [Category.assoc, hv.hom_dagger_id_assoc]

/-- The range endomorphism `dagger v ≫ v` of a dagger isometry is self-adjoint. -/
theorem dagger_comp_self_selfAdjoint (v : Y ⟶ X) :
    dagger (dagger v ≫ v) = dagger v ≫ v := by
  simp

end IsDaggerIsometry

/-- An arrow is unitary if and only if both it and its dagger are dagger isometries. -/
theorem isUnitary_iff_isDaggerIsometry (f : X ⟶ Y) :
    IsUnitary f ↔ IsDaggerIsometry f ∧ IsDaggerIsometry (dagger f) := by
  simp [isUnitary_iff, isDaggerIsometry_iff]

/-- An invertible arrow is unitary if and only if it is a dagger isometry. -/
theorem isUnitary_iff_isDaggerIsometry_of_isIso (f : X ⟶ Y) [IsIso f] :
    IsUnitary f ↔ IsDaggerIsometry f :=
  ⟨IsDaggerIsometry.of_isUnitary, fun hf => hf.isUnitary_of_isIso⟩

/-- An endomorphism `p : X ⟶ X` in a dagger category is a dagger projection when it is both
idempotent and self-adjoint. -/
def IsDaggerProjection (p : X ⟶ X) : Prop :=
  p ≫ p = p ∧ dagger p = p

/-- Characterization of a dagger projection. -/
theorem isDaggerProjection_iff (p : X ⟶ X) :
    IsDaggerProjection p ↔ p ≫ p = p ∧ dagger p = p := Iff.rfl

/-- Dagger projections on `X` are precisely the star projections in `CategoryTheory.End X`. -/
theorem isDaggerProjection_iff_isStarProjection_end (p : X ⟶ X) :
    IsDaggerProjection p ↔ IsStarProjection (End.of p) := by
  rw [isDaggerProjection_iff, isStarProjection_iff']
  constructor
  · rintro ⟨hidem, hdag⟩
    exact ⟨End.ext hidem, End.ext hdag⟩
  · rintro ⟨hidem, hdag⟩
    exact ⟨congrArg End.asHom hidem, congrArg End.asHom hdag⟩

namespace IsDaggerProjection

/-- A dagger projection is idempotent. -/
@[reassoc (attr := simp), grind =] theorem idem {p : X ⟶ X} (hp : IsDaggerProjection p) :
    p ≫ p = p := hp.1

/-- A dagger projection is self-adjoint. -/
@[simp, grind =] theorem dagger_eq {p : X ⟶ X} (hp : IsDaggerProjection p) :
    dagger p = p := hp.2

/-- The identity endomorphism is a dagger projection. -/
@[simp] theorem id (X : C) : IsDaggerProjection (𝟙 X) := by
  simp [isDaggerProjection_iff]

/-- The zero endomorphism is a dagger projection in a preadditive dagger category. -/
@[simp] theorem zero [Preadditive C] [DaggerPreadditive C] (X : C) :
    IsDaggerProjection (0 : X ⟶ X) := by
  simp [isDaggerProjection_iff]

/-- The range endomorphism `dagger v ≫ v` of a dagger isometry is a dagger projection. -/
theorem of_isDaggerIsometry {v : Y ⟶ X} (hv : IsDaggerIsometry v) :
    IsDaggerProjection (dagger v ≫ v) :=
  ⟨hv.dagger_comp_self_idem, by simp⟩

/-- The orthogonal complement `𝟙 X - p` of a dagger projection is a dagger projection. -/
theorem one_sub [Preadditive C] [DaggerPreadditive C] {p : X ⟶ X} (hp : IsDaggerProjection p) :
    IsDaggerProjection (𝟙 X - p) := by
  refine ⟨Idempotents.idem_of_id_sub_idem p hp.idem, ?_⟩
  simp [hp.dagger_eq]

/-- The sum of two orthogonal dagger projections is a dagger projection. -/
theorem add_of_comp_eq_zero [Preadditive C] [DaggerPreadditive C] {p q : X ⟶ X}
    (hp : IsDaggerProjection p) (hq : IsDaggerProjection q) (hpq : p ≫ q = 0) :
    IsDaggerProjection (p + q) := by
  have hqp : q ≫ p = 0 := by
    simpa [hp.dagger_eq, hq.dagger_eq] using congrArg dagger hpq
  refine ⟨?_, by simp [hp.dagger_eq, hq.dagger_eq]⟩
  simp [Preadditive.comp_add, Preadditive.add_comp, hp.idem, hq.idem, hpq, hqp]

/-- Conjugating a dagger projection by a unitary arrow produces a dagger projection. -/
theorem unitaryConj {p : X ⟶ X} (hp : IsDaggerProjection p) {u : X ⟶ Y} (hu : IsUnitary u) :
    IsDaggerProjection (dagger u ≫ p ≫ u) := by
  refine ⟨?_, ?_⟩
  · simp [Category.assoc, hu.hom_dagger_id_assoc, hp.idem_assoc]
  · simp [Category.assoc, hp.dagger_eq]

/-- Each summand projection `π f j ≫ ι f j` of a dagger biproduct is a dagger projection. -/
theorem daggerBiproduct_proj {J : Type*} [HasZeroMorphisms C] (f : J → C)
    [HasDaggerBiproduct f] (j : J) :
    IsDaggerProjection (daggerBiproduct.π f j ≫ daggerBiproduct.ι f j) := by
  have hv : IsDaggerIsometry (daggerBiproduct.ι f j) := by
    rw [isDaggerIsometry_iff, daggerBiproduct.dagger_ι, daggerBiproduct.ι_π_self]
  simpa only [daggerBiproduct.dagger_ι] using of_isDaggerIsometry hv

end IsDaggerProjection

/-- A dagger splitting (unitary splitting) of an endomorphism `p : X ⟶ X` consists of an object
`obj` and a dagger isometry `hom : obj ⟶ X` with `dagger hom ≫ hom = p`. -/
structure DaggerSplitting {X : C} (p : X ⟶ X) where
  /-- The split subobject. -/
  obj : C
  /-- The isometric inclusion into `X`. -/
  hom : obj ⟶ X
  /-- The inclusion is a dagger isometry. -/
  isometry : hom ≫ dagger hom = 𝟙 obj
  /-- The range projection of the inclusion is `p`. -/
  range : dagger hom ≫ hom = p

attribute [reassoc (attr := simp)] DaggerSplitting.isometry DaggerSplitting.range

namespace DaggerSplitting

/-- The inclusion of a dagger splitting is a dagger isometry. -/
theorem isDaggerIsometry {p : X ⟶ X} (s : DaggerSplitting p) :
    IsDaggerIsometry s.hom := s.isometry

/-- Any endomorphism with a dagger splitting is a dagger projection. -/
theorem isDaggerProjection {p : X ⟶ X} (s : DaggerSplitting p) :
    IsDaggerProjection p := by
  simpa only [s.range] using IsDaggerProjection.of_isDaggerIsometry s.isDaggerIsometry

/-- The isometric inclusion absorbs `p` on the right. -/
@[reassoc (attr := simp)] theorem hom_comp_p {p : X ⟶ X} (s : DaggerSplitting p) :
    s.hom ≫ p = s.hom := by
  calc
    s.hom ≫ p = s.hom ≫ (dagger s.hom ≫ s.hom) := by rw [s.range]
    _ = s.hom := by rw [s.isometry_assoc]

/-- The dagger of the isometric inclusion absorbs `p` on the left. -/
@[reassoc (attr := simp)] theorem p_comp_dagger_hom {p : X ⟶ X} (s : DaggerSplitting p) :
    p ≫ dagger s.hom = dagger s.hom := by
  calc
    p ≫ dagger s.hom = (dagger s.hom ≫ s.hom) ≫ dagger s.hom := by rw [s.range]
    _ = dagger s.hom := by rw [Category.assoc, s.isometry, Category.comp_id]

/-- A dagger splitting gives a native retract `Retract s.obj X`. -/
def toRetract {p : X ⟶ X} (s : DaggerSplitting p) : Retract s.obj X where
  i := s.hom
  r := dagger s.hom
  retract := s.isometry

/-- The inclusion of the retract induced by a dagger splitting is `s.hom`. -/
@[simp] theorem toRetract_i {p : X ⟶ X} (s : DaggerSplitting p) : s.toRetract.i = s.hom := (rfl)

/-- The retraction induced by a dagger splitting is `dagger s.hom`. -/
@[simp] theorem toRetract_r {p : X ⟶ X} (s : DaggerSplitting p) :
    s.toRetract.r = dagger s.hom := (rfl)

/-- A dagger splitting makes `s.hom` a split monomorphism. -/
def toSplitMono {p : X ⟶ X} (s : DaggerSplitting p) : SplitMono s.hom :=
  s.isDaggerIsometry.splitMono

/-- The canonical identity splitting of `𝟙 X`. -/
@[expose] def id (X : C) : DaggerSplitting (𝟙 X) where
  obj := X
  hom := 𝟙 X
  isometry := by simp
  range := by simp

/-- The object of the identity splitting is `X`. -/
@[simp] theorem id_obj (X : C) : (DaggerSplitting.id X).obj = X := (rfl)

/-- The inclusion of the identity splitting is `𝟙 X`. -/
@[simp] theorem id_hom (X : C) : (DaggerSplitting.id X).hom = 𝟙 X := (rfl)

/-- The canonical isomorphism between two dagger splittings of the same projection. -/
def iso {p : X ⟶ X} (s₁ s₂ : DaggerSplitting p) : s₁.obj ≅ s₂.obj where
  hom := s₁.hom ≫ dagger s₂.hom
  inv := s₂.hom ≫ dagger s₁.hom
  hom_inv_id := by
    rw [Category.assoc, s₂.range_assoc, s₁.hom_comp_p_assoc, s₁.isometry]
  inv_hom_id := by
    rw [Category.assoc, s₁.range_assoc, s₂.hom_comp_p_assoc, s₂.isometry]

/-- The forward arrow of `DaggerSplitting.iso` is `s₁.hom ≫ dagger s₂.hom`. -/
@[simp] theorem iso_hom {p : X ⟶ X} (s₁ s₂ : DaggerSplitting p) :
    (s₁.iso s₂).hom = s₁.hom ≫ dagger s₂.hom := (rfl)

/-- The inverse arrow of `DaggerSplitting.iso` is `s₂.hom ≫ dagger s₁.hom`. -/
@[simp] theorem iso_inv {p : X ⟶ X} (s₁ s₂ : DaggerSplitting p) :
    (s₁.iso s₂).inv = s₂.hom ≫ dagger s₁.hom := (rfl)

/-- The canonical isomorphism between two dagger splittings commutes with their inclusions. -/
@[reassoc] theorem iso_hom_comp {p : X ⟶ X} (s₁ s₂ : DaggerSplitting p) :
    (s₁.iso s₂).hom ≫ s₂.hom = s₁.hom := by
  rw [iso_hom, Category.assoc, s₂.range, s₁.hom_comp_p]

/-- The inverse of the canonical isomorphism between two dagger splittings commutes with their
inclusions. -/
@[reassoc] theorem iso_inv_comp {p : X ⟶ X} (s₁ s₂ : DaggerSplitting p) :
    (s₁.iso s₂).inv ≫ s₁.hom = s₂.hom := by
  rw [iso_inv, Category.assoc, s₁.range, s₂.hom_comp_p]

/-- The canonical isomorphism between two dagger splittings of the same projection is unitary. -/
theorem isUnitary_iso {p : X ⟶ X} (s₁ s₂ : DaggerSplitting p) :
    IsUnitary (s₁.iso s₂).hom :=
  (s₁.iso s₂).isUnitary_hom_iff.mpr (by simp [iso_hom, iso_inv])

/-- Any arrow between the objects of two dagger splittings of `p` that intertwines their inclusions
equals the canonical unitary isomorphism. -/
theorem eq_iso_hom_of_comp_eq {p : X ⟶ X} (s₁ s₂ : DaggerSplitting p)
    {f : s₁.obj ⟶ s₂.obj} (hf : f ≫ s₂.hom = s₁.hom) :
    f = (s₁.iso s₂).hom := by
  calc
    f = f ≫ (s₂.hom ≫ dagger s₂.hom) := by rw [s₂.isometry, Category.comp_id]
    _ = (f ≫ s₂.hom) ≫ dagger s₂.hom := (Category.assoc _ _ _).symm
    _ = (s₁.iso s₂).hom := by rw [hf, iso_hom]

/-- A dagger-preserving functor maps dagger splittings to dagger splittings. -/
@[expose] def map {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]
    (F : C ⥤ D) [F.PreservesDagger] {p : X ⟶ X} (s : DaggerSplitting p) :
    DaggerSplitting (F.map p) where
  obj := F.obj s.obj
  hom := F.map s.hom
  isometry := by rw [← F.map_dagger, ← F.map_comp, s.isometry, F.map_id]
  range := by rw [← F.map_dagger, ← F.map_comp, s.range]

/-- The object of a mapped dagger splitting is `F.obj s.obj`. -/
@[simp] theorem map_obj {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]
    (F : C ⥤ D) [F.PreservesDagger] {p : X ⟶ X} (s : DaggerSplitting p) :
    (s.map F).obj = F.obj s.obj := (rfl)

/-- The inclusion of a mapped dagger splitting is `F.map s.hom`. -/
@[simp] theorem map_hom {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]
    (F : C ⥤ D) [F.PreservesDagger] {p : X ⟶ X} (s : DaggerSplitting p) :
    (s.map F).hom = F.map s.hom := (rfl)

/-- Transport a dagger splitting of `p` along a unitary arrow `u : X ⟶ Y` to obtain a dagger
splitting of the unitarily conjugate projection `dagger u ≫ p ≫ u`. -/
@[expose] def ofUnitaryConj {p : X ⟶ X} (s : DaggerSplitting p) (u : X ⟶ Y) (hu : IsUnitary u) :
    DaggerSplitting (dagger u ≫ p ≫ u) where
  obj := s.obj
  hom := s.hom ≫ u
  isometry := by rw [dagger_comp, Category.assoc, hu.hom_dagger_id_assoc, s.isometry]
  range := by rw [dagger_comp, Category.assoc, s.range_assoc]

/-- The object of a transported dagger splitting is unchanged. -/
@[simp] theorem ofUnitaryConj_obj {p : X ⟶ X} (s : DaggerSplitting p) (u : X ⟶ Y)
    (hu : IsUnitary u) : (s.ofUnitaryConj u hu).obj = s.obj := (rfl)

/-- The inclusion of a transported dagger splitting is `s.hom ≫ u`. -/
@[simp] theorem ofUnitaryConj_hom {p : X ⟶ X} (s : DaggerSplitting p) (u : X ⟶ Y)
    (hu : IsUnitary u) : (s.ofUnitaryConj u hu).hom = s.hom ≫ u := (rfl)

/-- If `q = dagger u ≫ p ≫ u` for a unitary `u`, any dagger splittings of `p` and `q` have
unitarily isomorphic split objects. -/
def isoOfUnitaryConj {p : X ⟶ X} {q : Y ⟶ Y} (s₁ : DaggerSplitting p) (s₂ : DaggerSplitting q)
    (u : X ⟶ Y) (hu : IsUnitary u) (h : dagger u ≫ p ≫ u = q) :
    s₁.obj ≅ s₂.obj where
  hom := s₁.hom ≫ u ≫ dagger s₂.hom
  inv := s₂.hom ≫ dagger u ≫ dagger s₁.hom
  hom_inv_id := by
    rw [Category.assoc, Category.assoc, s₂.range_assoc, ← h, Category.assoc,
      hu.hom_dagger_id_assoc, Category.assoc, hu.hom_dagger_id_assoc, s₁.hom_comp_p_assoc,
      s₁.isometry]
  inv_hom_id := by
    rw [Category.assoc, Category.assoc, s₁.range_assoc, reassoc_of% h, s₂.hom_comp_p_assoc,
      s₂.isometry]

/-- The forward arrow of `isoOfUnitaryConj` is `s₁.hom ≫ u ≫ dagger s₂.hom`. -/
@[simp] theorem isoOfUnitaryConj_hom {p : X ⟶ X} {q : Y ⟶ Y}
    (s₁ : DaggerSplitting p) (s₂ : DaggerSplitting q)
    (u : X ⟶ Y) (hu : IsUnitary u) (h : dagger u ≫ p ≫ u = q) :
    (s₁.isoOfUnitaryConj s₂ u hu h).hom = s₁.hom ≫ u ≫ dagger s₂.hom := (rfl)

/-- The inverse arrow of `isoOfUnitaryConj` is `s₂.hom ≫ dagger u ≫ dagger s₁.hom`. -/
@[simp] theorem isoOfUnitaryConj_inv {p : X ⟶ X} {q : Y ⟶ Y}
    (s₁ : DaggerSplitting p) (s₂ : DaggerSplitting q)
    (u : X ⟶ Y) (hu : IsUnitary u) (h : dagger u ≫ p ≫ u = q) :
    (s₁.isoOfUnitaryConj s₂ u hu h).inv = s₂.hom ≫ dagger u ≫ dagger s₁.hom := (rfl)

/-- The comparison isomorphism induced by unitary conjugacy of projections is unitary. -/
theorem isUnitary_isoOfUnitaryConj {p : X ⟶ X} {q : Y ⟶ Y}
    (s₁ : DaggerSplitting p) (s₂ : DaggerSplitting q)
    (u : X ⟶ Y) (hu : IsUnitary u) (h : dagger u ≫ p ≫ u = q) :
    IsUnitary (isoOfUnitaryConj s₁ s₂ u hu h).hom :=
  (s₁.isoOfUnitaryConj s₂ u hu h).isUnitary_hom_iff.mpr (by
    simp [isoOfUnitaryConj_hom, isoOfUnitaryConj_inv, Category.assoc])

/-- An orthogonal sum of two dagger splittings of orthogonal projections (`p ≫ q = 0`) yields a
dagger splitting of `p + q` via their binary dagger biproduct. -/
@[expose] noncomputable def addOfCompEqZero [Preadditive C] [DaggerPreadditive C]
    {p q : X ⟶ X} (s₁ : DaggerSplitting p) (s₂ : DaggerSplitting q)
    [HasBinaryDaggerBiproduct s₁.obj s₂.obj] (hpq : p ≫ q = 0) :
    DaggerSplitting (p + q) where
  obj := daggerBiprod s₁.obj s₂.obj
  hom := daggerBiprod.desc s₁.hom s₂.hom
  isometry := by
    have hqp : q ≫ p = 0 := by
      simpa [s₁.isDaggerProjection.dagger_eq, s₂.isDaggerProjection.dagger_eq] using
        congrArg dagger hpq
    have h12 : s₁.hom ≫ dagger s₂.hom = 0 := by
      calc
        s₁.hom ≫ dagger s₂.hom = (s₁.hom ≫ p) ≫ (q ≫ dagger s₂.hom) := by
          rw [s₁.hom_comp_p, s₂.p_comp_dagger_hom]
        _ = s₁.hom ≫ (p ≫ q) ≫ dagger s₂.hom := by simp [Category.assoc]
        _ = 0 := by rw [hpq, Limits.zero_comp, Limits.comp_zero]
    have h21 : s₂.hom ≫ dagger s₁.hom = 0 := by
      calc
        s₂.hom ≫ dagger s₁.hom = (s₂.hom ≫ q) ≫ (p ≫ dagger s₁.hom) := by
          rw [s₂.hom_comp_p, s₁.p_comp_dagger_hom]
        _ = s₂.hom ≫ (q ≫ p) ≫ dagger s₁.hom := by simp [Category.assoc]
        _ = 0 := by rw [hqp, Limits.zero_comp, Limits.comp_zero]
    rw [daggerBiprod.dagger_desc]
    refine daggerBiprod.hom_ext' ?_ ?_ <;> refine daggerBiprod.hom_ext ?_ ?_ <;>
      simp [Category.assoc, h12, h21]
  range := by
    rw [daggerBiprod.dagger_desc, daggerBiprod.lift_desc, s₁.range, s₂.range]

end DaggerSplitting

/-- An endomorphism `p : X ⟶ X` is dagger-split if it admits a dagger splitting. -/
def IsDaggerSplit (p : X ⟶ X) : Prop :=
  Nonempty (DaggerSplitting p)

/-- Characterization of a dagger-split endomorphism. -/
theorem isDaggerSplit_iff (p : X ⟶ X) :
    IsDaggerSplit p ↔ ∃ (Y : C) (v : Y ⟶ X), v ≫ dagger v = 𝟙 Y ∧ dagger v ≫ v = p := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.obj, s.hom, s.isometry, s.range⟩
  · rintro ⟨Y, v, hv, hr⟩
    exact ⟨⟨Y, v, hv, hr⟩⟩

/-- Any dagger splitting witnesses `IsDaggerSplit`. -/
theorem DaggerSplitting.isDaggerSplit {p : X ⟶ X} (s : DaggerSplitting p) :
    IsDaggerSplit p := ⟨s⟩

/-- Any dagger-split endomorphism is a dagger projection. In particular, non-self-adjoint
idempotents do not admit dagger splittings. -/
theorem IsDaggerSplit.isDaggerProjection {p : X ⟶ X} (hp : IsDaggerSplit p) :
    IsDaggerProjection p :=
  hp.elim DaggerSplitting.isDaggerProjection

/-- The identity endomorphism is dagger-split. -/
@[simp] theorem isDaggerSplit_id (X : C) : IsDaggerSplit (𝟙 X) :=
  (DaggerSplitting.id X).isDaggerSplit

/-- Unitary conjugacy preserves dagger-splittability. -/
theorem IsDaggerSplit.unitaryConj {p : X ⟶ X} (hp : IsDaggerSplit p)
    {u : X ⟶ Y} (hu : IsUnitary u) : IsDaggerSplit (dagger u ≫ p ≫ u) :=
  hp.elim fun s => (s.ofUnitaryConj u hu).isDaggerSplit

/-- Unitary conjugacy preserves and reflects dagger-splittability. -/
theorem isDaggerSplit_unitaryConj_iff {p : X ⟶ X} {u : X ⟶ Y} (hu : IsUnitary u) :
    IsDaggerSplit (dagger u ≫ p ≫ u) ↔ IsDaggerSplit p := by
  constructor
  · intro h
    have h' := h.unitaryConj hu.dagger
    simpa [Category.assoc, hu.hom_dagger_id, hu.hom_dagger_id_assoc] using h'
  · exact fun h => h.unitaryConj hu

/-- In a preadditive dagger category with binary dagger biproducts, the sum of two orthogonal
dagger-split projections is dagger-split. -/
theorem IsDaggerSplit.add_of_comp_eq_zero [Preadditive C] [DaggerPreadditive C]
    [HasBinaryDaggerBiproducts C] {p q : X ⟶ X} (hp : IsDaggerSplit p) (hq : IsDaggerSplit q)
    (hpq : p ≫ q = 0) : IsDaggerSplit (p + q) :=
  hp.elim fun s₁ => hq.elim fun s₂ => (s₁.addOfCompEqZero s₂ hpq).isDaggerSplit

section RetractComparison

/-- Given an algebraic splitting `(i, r)` of an idempotent `e = r ≫ i` and a dagger splitting `s` of
a projection `p` with the same range equations (`e ≫ p = e`, `p ≫ e = p`), the retract object `Y`
is canonically isomorphic to `s.obj` via `i ≫ dagger s.hom`. -/
def retractIsoDaggerSplitting {e p : X ⟶ X} (i : Y ⟶ X) (r : X ⟶ Y)
    (hir : i ≫ r = 𝟙 Y) (hri : r ≫ i = e) (s : DaggerSplitting p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) : Y ≅ s.obj where
  hom := i ≫ dagger s.hom
  inv := s.hom ≫ r
  hom_inv_id := by
    have hip : i ≫ p = i := by
      calc
        i ≫ p = (i ≫ r ≫ i) ≫ p := by rw [← Category.assoc, hir, Category.id_comp]
        _ = i ≫ (e ≫ p) := by rw [hri, Category.assoc]
        _ = i ≫ r ≫ i := by rw [hep, hri]
        _ = i := by rw [← Category.assoc, hir, Category.id_comp]
    rw [Category.assoc, s.range_assoc, reassoc_of% hip, hir]
  inv_hom_id := by
    have hse : s.hom ≫ e = s.hom := by
      calc
        s.hom ≫ e = (s.hom ≫ p) ≫ e := by rw [s.hom_comp_p]
        _ = s.hom ≫ (p ≫ e) := Category.assoc _ _ _
        _ = s.hom := by rw [hpe, s.hom_comp_p]
    rw [Category.assoc, reassoc_of% hri, reassoc_of% hse, s.isometry]

/-- The forward arrow of `retractIsoDaggerSplitting` is `i ≫ dagger s.hom`. -/
@[simp] theorem retractIsoDaggerSplitting_hom {e p : X ⟶ X} (i : Y ⟶ X) (r : X ⟶ Y)
    (hir : i ≫ r = 𝟙 Y) (hri : r ≫ i = e) (s : DaggerSplitting p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) :
    (retractIsoDaggerSplitting i r hir hri s hep hpe).hom = i ≫ dagger s.hom := (rfl)

/-- The inverse arrow of `retractIsoDaggerSplitting` is `s.hom ≫ r`. -/
@[simp] theorem retractIsoDaggerSplitting_inv {e p : X ⟶ X} (i : Y ⟶ X) (r : X ⟶ Y)
    (hir : i ≫ r = 𝟙 Y) (hri : r ≫ i = e) (s : DaggerSplitting p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) :
    (retractIsoDaggerSplitting i r hir hri s hep hpe).inv = s.hom ≫ r := (rfl)

/-- The comparison isomorphism always intertwines the inclusion `i` with `s.hom`. -/
@[reassoc] theorem retractIsoDaggerSplitting_hom_comp {e p : X ⟶ X}
    (i : Y ⟶ X) (r : X ⟶ Y) (hir : i ≫ r = 𝟙 Y) (hri : r ≫ i = e) (s : DaggerSplitting p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) :
    (retractIsoDaggerSplitting i r hir hri s hep hpe).hom ≫ s.hom = i := by
  have hip : i ≫ p = i := by
    calc
      i ≫ p = (i ≫ r ≫ i) ≫ p := by rw [← Category.assoc, hir, Category.id_comp]
      _ = i ≫ (e ≫ p) := by rw [hri, Category.assoc]
      _ = i ≫ r ≫ i := by rw [hep, hri]
      _ = i := by rw [← Category.assoc, hir, Category.id_comp]
  rw [retractIsoDaggerSplitting_hom, Category.assoc, s.range, hip]

/-- The comparison isomorphism intertwines the algebraic retraction `r` with the orthogonal
retraction `dagger s.hom` if and only if `e = p`. -/
theorem retractIsoDaggerSplitting_comp_hom_iff {e p : X ⟶ X}
    (i : Y ⟶ X) (r : X ⟶ Y) (hir : i ≫ r = 𝟙 Y) (hri : r ≫ i = e) (s : DaggerSplitting p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) :
    r ≫ (retractIsoDaggerSplitting i r hir hri s hep hpe).hom = dagger s.hom ↔ e = p := by
  constructor
  · intro h
    have he : e ≫ dagger s.hom = dagger s.hom := by
      simpa [retractIsoDaggerSplitting_hom, ← Category.assoc, hri] using h
    have := congrArg (· ≫ s.hom) he
    simpa [Category.assoc, s.range, hep] using this
  · intro h
    subst h
    rw [retractIsoDaggerSplitting_hom, ← Category.assoc, hri, s.p_comp_dagger_hom]

/-- The comparison isomorphism `Y ≅ s.obj` is unitary if and only if the inclusion `i` is a dagger
isometry. -/
theorem isUnitary_retractIsoDaggerSplitting_iff {e p : X ⟶ X}
    (i : Y ⟶ X) (r : X ⟶ Y) (hir : i ≫ r = 𝟙 Y) (hri : r ≫ i = e) (s : DaggerSplitting p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) :
    IsUnitary (retractIsoDaggerSplitting i r hir hri s hep hpe).hom ↔ IsDaggerIsometry i := by
  have hip : i ≫ p = i := by
    calc
      i ≫ p = (i ≫ r ≫ i) ≫ p := by rw [← Category.assoc, hir, Category.id_comp]
      _ = i ≫ (e ≫ p) := by rw [hri, Category.assoc]
      _ = i ≫ r ≫ i := by rw [hep, hri]
      _ = i := by rw [← Category.assoc, hir, Category.id_comp]
  rw [isUnitary_iff_isDaggerIsometry_of_isIso, isDaggerIsometry_iff, isDaggerIsometry_iff]
  change (i ≫ dagger s.hom) ≫ dagger (i ≫ dagger s.hom) = 𝟙 Y ↔ i ≫ dagger i = 𝟙 Y
  rw [dagger_comp, dagger_dagger, Category.assoc, s.range_assoc, reassoc_of% hip]

/-- For an algebraic splitting `(i, r)` of `e` with the same range as a dagger projection `p`,
the retraction `r` equals `dagger i` if and only if `i` is a dagger isometry and `e = p`. -/
theorem retract_eq_dagger_iff {e p : X ⟶ X} (i : Y ⟶ X) (r : X ⟶ Y)
    (hir : i ≫ r = 𝟙 Y) (hri : r ≫ i = e) (hp : IsDaggerProjection p)
    (hep : e ≫ p = e) (hpe : p ≫ e = p) :
    r = dagger i ↔ IsDaggerIsometry i ∧ e = p := by
  constructor
  · intro hr
    refine ⟨?_, ?_⟩
    · rw [isDaggerIsometry_iff, ← hr, hir]
    · have he_dag : dagger e = e := by rw [← hri, hr, dagger_comp, dagger_dagger]
      have hpe' : p ≫ e = e := by
        simpa [hp.dagger_eq, he_dag] using congrArg dagger hep
      exact hpe'.symm.trans hpe
  · rintro ⟨hi, rfl⟩
    have h1 : i ≫ dagger i = 𝟙 Y := hi
    have h2 : dagger e = e := hp.dagger_eq
    have h3 : r ≫ (i ≫ dagger i) = dagger i := by
      have : dagger (i ≫ r) = 𝟙 Y := by rw [hir, dagger_id]
      rw [← Category.assoc, hri, ← h2, ← hri, dagger_comp, Category.assoc]
      simpa [Category.assoc] using congrArg (dagger i ≫ ·) this
    simpa [h1, Category.comp_id] using h3

end RetractComparison

/-- A dagger category is *dagger idempotent complete* (or *dagger Karoubian*) if every dagger
projection admits a dagger splitting. -/
class IsDaggerIdempotentComplete (C : Type u₁) [Category.{v₁} C] [DaggerCategory C] : Prop where
  /-- Every dagger projection splits via a dagger isometry. -/
  daggerProjections_split :
    ∀ (X : C) (p : X ⟶ X), IsDaggerProjection p → IsDaggerSplit p

/-- If `C` is dagger idempotent complete and every idempotent in `C` is similar to a dagger
projection, then `C` is idempotent complete in the native sense. -/
theorem isIdempotentComplete_of_exists_similar_projection [IsDaggerIdempotentComplete C]
    (h : ∀ (X : C) (e : X ⟶ X), e ≫ e = e →
      ∃ (p : X ⟶ X) (u : X ≅ X), IsDaggerProjection p ∧ u.inv ≫ e ≫ u.hom = p) :
    IsIdempotentComplete C where
  idempotents_split X e he := by
    rcases h X e he with ⟨p, u, hp, hu⟩
    rcases (IsDaggerIdempotentComplete.daggerProjections_split X p hp) with ⟨s⟩
    refine ⟨s.obj, s.hom ≫ u.inv, u.hom ≫ dagger s.hom, ?_, ?_⟩
    · rw [Category.assoc, u.inv_hom_id_assoc, s.isometry]
    · rw [Category.assoc, s.range_assoc, ← hu, Category.assoc, Category.assoc,
        u.hom_inv_id, Category.comp_id, u.hom_inv_id_assoc]

end TauCeti

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]
variable {X Y : C}

/-- Dagger-preserving functors preserve dagger isometries. -/
theorem map_isDaggerIsometry (F : C ⥤ D) [F.PreservesDagger] {v : Y ⟶ X}
    (hv : IsDaggerIsometry v) : IsDaggerIsometry (F.map v) := by
  rw [isDaggerIsometry_iff, ← F.map_dagger, ← F.map_comp, hv.hom_dagger_id, F.map_id]

/-- Faithful dagger-preserving functors reflect dagger isometries. -/
@[simp] theorem isDaggerIsometry_map_iff (F : C ⥤ D) [F.PreservesDagger] [F.Faithful]
    (v : Y ⟶ X) : IsDaggerIsometry (F.map v) ↔ IsDaggerIsometry v := by
  simp only [isDaggerIsometry_iff, ← F.map_dagger, ← F.map_comp, ← F.map_id,
    F.map_injective.eq_iff]

/-- Dagger-preserving functors preserve dagger projections. -/
theorem map_isDaggerProjection (F : C ⥤ D) [F.PreservesDagger] {p : X ⟶ X}
    (hp : IsDaggerProjection p) : IsDaggerProjection (F.map p) := by
  refine ⟨?_, ?_⟩
  · rw [← F.map_comp, hp.idem]
  · rw [← F.map_dagger, hp.dagger_eq]

/-- Faithful dagger-preserving functors reflect dagger projections. -/
@[simp] theorem isDaggerProjection_map_iff (F : C ⥤ D) [F.PreservesDagger] [F.Faithful]
    (p : X ⟶ X) : IsDaggerProjection (F.map p) ↔ IsDaggerProjection p := by
  simp only [isDaggerProjection_iff, ← F.map_comp, ← F.map_dagger, F.map_injective.eq_iff]

/-- Dagger-preserving functors preserve dagger-splittability. -/
theorem map_isDaggerSplit (F : C ⥤ D) [F.PreservesDagger] {p : X ⟶ X}
    (hp : IsDaggerSplit p) : IsDaggerSplit (F.map p) :=
  hp.elim fun s => (s.map F).isDaggerSplit

end CategoryTheory.Functor
