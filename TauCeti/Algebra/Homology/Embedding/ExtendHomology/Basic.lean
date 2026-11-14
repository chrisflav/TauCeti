/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Opcycles, functoriality, and extension by zero

The opcycles isomorphism of an extended complex is natural in chain maps and compatible with
`HomologicalComplex.opcyclesToCycles`. These identities require homology only in the degrees
involved, in a category with zero morphisms and a zero object. An extended chain map is an
epimorphism in homology in a degree of the image exactly when the original map is, the counterpart
for epimorphisms of Mathlib's `HomologicalComplex.quasiIsoAt_extendMap_iff`. Outside the image,
an extended complex has zero homology, so every extended chain map is an isomorphism in homology
there.

Moreover, extending by zero along `e : c.Embedding c'` commutes up to canonical natural isomorphism
with `Functor.mapHomologicalComplex` for any zero-morphism-preserving functor `F : C ⥤ D`
(`ComplexShape.Embedding.extendFunctorCompMapHomologicalComplexIso`), and `e.extendFunctor`
intertwines the homology functors on `c'` and `c` at matching degrees
(`ComplexShape.Embedding.extendFunctorCompHomologyFunctorIso`).

Adapted from [TauCetiProject/TauCeti#10141](https://github.com/TauCetiProject/TauCeti/pull/10141).
-/

public section

open CategoryTheory Category Limits ZeroObject

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K L : HomologicalComplex C c} (φ : K ⟶ L) (e : c.Embedding c')

/-- The identification of the opcycles of an extended complex is natural. -/
@[reassoc (attr := simp)]
lemma extendOpcyclesIso_hom_naturality {j : ι} {j' : ι'} (hj' : e.f j = j')
    [K.HasHomology j] [L.HasHomology j] [(K.extend e).HasHomology j']
    [(L.extend e).HasHomology j'] :
    opcyclesMap (extendMap φ e) j' ≫ (L.extendOpcyclesIso e hj').hom =
      (K.extendOpcyclesIso e hj').hom ≫ opcyclesMap φ j := by
  simp [← cancel_epi ((K.extend e).pOpcycles j'), extendMap_f φ e hj']

variable (K) in
/-- The identifications of the opcycles and cycles of an extended complex are compatible with the
maps `opcyclesToCycles`. -/
-- The left-hand side does not determine the source index `i` for the simplifier.
@[reassoc]
lemma opcyclesToCycles_extendCyclesIso_hom {i j : ι} {i' j' : ι'} (hi' : e.f i = i')
    (hj' : e.f j = j') [K.HasHomology i] [K.HasHomology j] [(K.extend e).HasHomology i']
    [(K.extend e).HasHomology j'] :
    (K.extend e).opcyclesToCycles i' j' ≫ (K.extendCyclesIso e hj').hom =
      (K.extendOpcyclesIso e hi').hom ≫ K.opcyclesToCycles i j := by
  simp [← cancel_epi ((K.extend e).pOpcycles i'), ← cancel_mono (K.iCycles j),
    K.extend_d_eq e hi' hj']

variable {e} in
/-- In a degree `j'` in the image of `e`, the map induced in homology by the extension of `φ` is an
epimorphism exactly when the map induced by `φ` is in the corresponding degree `j`. -/
lemma epi_homologyMap_extendMap_iff {j : ι} {j' : ι'} (hj' : e.f j = j')
    [K.HasHomology j] [L.HasHomology j] [(K.extend e).HasHomology j']
    [(L.extend e).HasHomology j'] :
    Epi (homologyMap (extendMap φ e) j') ↔ Epi (homologyMap φ j) :=
  (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.extendHomologyIso e hj') (L.extendHomologyIso e hj'))

variable {e} in
/-- In a degree `j'` outside the image of `e`, the map induced in homology by the extension of `φ`
is an isomorphism, between zero objects. -/
lemma isIso_homologyMap_extendMap_of_forall_ne {j' : ι'} (hj' : ∀ j, e.f j ≠ j')
    [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j'] :
    IsIso (homologyMap (extendMap φ e) j') :=
  ⟨0, (K.extend_exactAt e j' hj').isZero_homology.eq_of_src _ _,
    (L.extend_exactAt e j' hj').isZero_homology.eq_of_src _ _⟩

section MapHomologicalComplex

variable {D : Type*} [Category* D] [HasZeroMorphisms D] [HasZeroObject D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- Degreewise comparison `F.obj (extend.X K o) ≅ extend.X (F.mapHomologicalComplex.obj K) o`. -/
private noncomputable def extend.mapXObjIso (K : HomologicalComplex C c) :
    ∀ (o : Option ι), F.obj (extend.X K o) ≅ extend.X ((F.mapHomologicalComplex c).obj K) o
  | some _ =>
    F.mapIso (extend.XIso K rfl) ≪≫ (extend.XIso ((F.mapHomologicalComplex c).obj K) rfl).symm
  | none => IsZero.iso (F.map_isZero (Limits.isZero_zero C)) (Limits.isZero_zero D)

private lemma extend.mapXObjIso_comm (K : HomologicalComplex C c) (o₁ o₂ : Option ι) :
    (extend.mapXObjIso F K o₁).hom ≫ extend.d ((F.mapHomologicalComplex c).obj K) o₁ o₂ =
      F.map (extend.d K o₁ o₂) ≫ (extend.mapXObjIso F K o₂).hom :=
  match o₁, o₂ with
  | none, _ => (F.map_isZero (Limits.isZero_zero C)).eq_of_src _ _
  | some _, none => (Limits.isZero_zero D).eq_of_tgt _ _
  | some i, some j => by
    rw [extend.d_eq _ rfl rfl, extend.d_eq _ rfl rfl]
    dsimp [extend.mapXObjIso]
    rw [assoc, Iso.inv_hom_id_assoc, F.map_comp, F.map_comp, assoc, assoc,
      ← F.map_comp_assoc (extend.XIso K rfl).inv, Iso.inv_hom_id, F.map_id, id_comp]

private lemma extend.mapXObjIso_hom_some (K : HomologicalComplex C c) {o : Option ι} {i : ι}
    (ho : o = some i) :
    (extend.mapXObjIso F K o).hom =
      F.map (extend.XIso K ho).hom ≫ (extend.XIso ((F.mapHomologicalComplex c).obj K) ho).inv := by
  subst ho
  rfl

variable (K) in
/-- Extending `K` by zero along `e` and then applying `F` is canonically isomorphic to applying `F`
and then extending by zero along `e`. -/
noncomputable def mapHomologicalComplexExtendIso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅ ((F.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents (fun i' ↦ extend.mapXObjIso F K (e.r i'))
    (fun i' j' _ ↦ extend.mapXObjIso_comm F K (e.r i') (e.r j'))

variable (K) in
-- Not `@[simp]` because the left-hand side does not determine the preimage index `i : ι`.
@[reassoc]
lemma mapHomologicalComplexExtendIso_hom_f {i : ι} {i' : ι'} (hi : e.f i = i') :
    (K.mapHomologicalComplexExtendIso e F).hom.f i' =
      F.map (K.extendXIso e hi).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e hi).inv :=
  extend.mapXObjIso_hom_some F K (e.r_eq_some hi)

variable (K) in
-- Not `@[simp]` because the left-hand side does not determine the preimage index `i : ι`.
@[reassoc]
lemma mapHomologicalComplexExtendIso_inv_f {i : ι} {i' : ι'} (hi : e.f i = i') :
    (K.mapHomologicalComplexExtendIso e F).inv.f i' =
      (((F.mapHomologicalComplex c).obj K).extendXIso e hi).hom ≫
        F.map (K.extendXIso e hi).inv := by
  rw [← cancel_epi ((K.mapHomologicalComplexExtendIso e F).hom.f i'), ← comp_f,
    Iso.hom_inv_id, id_f, mapHomologicalComplexExtendIso_hom_f K e F hi, assoc,
    Iso.inv_hom_id_assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id]
  rfl

@[reassoc (attr := simp)]
lemma mapHomologicalComplexExtendIso_hom_naturality :
    (F.mapHomologicalComplex c').map (extendMap φ e) ≫
        (L.mapHomologicalComplexExtendIso e F).hom =
      (K.mapHomologicalComplexExtendIso e F).hom ≫
        extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    rw [comp_f, comp_f, mapHomologicalComplexExtendIso_hom_f L e F hi,
      mapHomologicalComplexExtendIso_hom_f K e F hi, Functor.mapHomologicalComplex_map_f,
      extendMap_f φ e hi, extendMap_f ((F.mapHomologicalComplex c).map φ) e hi]
    simp only [Functor.map_comp, Functor.mapHomologicalComplex_map_f, assoc, Iso.inv_hom_id_assoc]
    rw [← F.map_comp_assoc (L.extendXIso e hi).inv, Iso.inv_hom_id, F.map_id, id_comp]
  · have hnone := e.r_eq_none i' (fun i hi ↦ hi' ⟨i, hi⟩)
    exact (F.map_isZero (K.isZero_extend_X' e i' hnone)).eq_of_src _ _

end MapHomologicalComplex

end HomologicalComplex

namespace ComplexShape.Embedding

open HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  {C D : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  [Category* D] [HasZeroMorphisms D] [HasZeroObject D]

/-- Extending complexes by zero along `e` commutes with `Functor.mapHomologicalComplex`. -/
noncomputable def extendFunctorCompMapHomologicalComplexIso
    (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor D :=
  NatIso.ofComponents (fun K ↦ K.mapHomologicalComplexExtendIso e F)
    (fun φ ↦ mapHomologicalComplexExtendIso_hom_naturality φ e F)

@[simp]
lemma extendFunctorCompMapHomologicalComplexIso_hom_app
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : HomologicalComplex C c) :
    (e.extendFunctorCompMapHomologicalComplexIso F).hom.app K =
      (K.mapHomologicalComplexExtendIso e F).hom :=
  (rfl)

@[simp]
lemma extendFunctorCompMapHomologicalComplexIso_inv_app
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : HomologicalComplex C c) :
    (e.extendFunctorCompMapHomologicalComplexIso F).inv.app K =
      (K.mapHomologicalComplexExtendIso e F).inv :=
  (rfl)

variable (C) in
/-- Given `e : c.Embedding c'` and `e.f j = j'`, extending along `e` and taking homology in degree
`j'` is naturally isomorphic to taking homology in degree `j`. -/
noncomputable def extendFunctorCompHomologyFunctorIso [CategoryWithHomology C]
    {j : ι} {j' : ι'} (hj' : e.f j = j') :
    e.extendFunctor C ⋙ HomologicalComplex.homologyFunctor C c' j' ≅
      HomologicalComplex.homologyFunctor C c j :=
  NatIso.ofComponents (fun K ↦ K.extendHomologyIso e hj')
    (fun φ ↦ extendHomologyIso_hom_naturality φ e hj')

@[simp]
lemma extendFunctorCompHomologyFunctorIso_hom_app [CategoryWithHomology C]
    {j : ι} {j' : ι'} (hj' : e.f j = j') (K : HomologicalComplex C c) :
    (e.extendFunctorCompHomologyFunctorIso C hj').hom.app K =
      (K.extendHomologyIso e hj').hom :=
  (rfl)

@[simp]
lemma extendFunctorCompHomologyFunctorIso_inv_app [CategoryWithHomology C]
    {j : ι} {j' : ι'} (hj' : e.f j = j') (K : HomologicalComplex C c) :
    (e.extendFunctorCompHomologyFunctorIso C hj').inv.app K =
      (K.extendHomologyIso e hj').inv :=
  (rfl)

/-- Extending along `e`, applying `F`, and taking homology in degree `j' = e.f j` is naturally
isomorphic to applying `F` and taking homology in degree `j`. -/
noncomputable def extendFunctorCompMapHomologicalComplexHomologyIso [CategoryWithHomology D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {j : ι} {j' : ι'} (hj' : e.f j = j') :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ⋙ HomologicalComplex.homologyFunctor D c' j' ≅
      F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c j :=
  Functor.isoWhiskerRight (e.extendFunctorCompMapHomologicalComplexIso F)
      (HomologicalComplex.homologyFunctor D c' j') ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex c)
      (e.extendFunctorCompHomologyFunctorIso D hj')

end ComplexShape.Embedding
