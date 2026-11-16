/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.Ext
public import TauCeti.Algebra.Homology.Embedding.DownNatAdd
public import TauCeti.Algebra.Homology.Embedding.UpNatAdd

/-!
# Commutation of extension by zero with functors and `Hom(-, Y)`

Extending a homological complex `K` along an embedding `e : c.Embedding c'` of complex shapes
places its terms at the indices in the image of `e` and zero objects elsewhere. Any functor
`F : C ⥤ D` preserving zero morphisms sends zero objects to zero objects, so applying `F`
degreewise commutes with extension by zero:
`F(K.extend e) ≅ (F K).extend e` (`HomologicalComplex.mapExtendIso`).

For a `ℕ`-indexed chain complex `X` in a `k`-linear abelian category `C` and an object `Y : C`,
extending `X` along the degree shift `n ↦ n + r` (`ComplexShape.embeddingDownNatAdd r`) and then
taking the cochain complex `Hom(-, Y)` (`ChainComplex.linearYonedaObj`) is naturally isomorphic to
extending `Hom(X, Y)` along `n ↦ n + r` (`ComplexShape.embeddingUpNatAdd r`):
`Hom(X.extend (n ↦ n + r), Y) ≅ Hom(X, Y).extend (n ↦ n + r)`
(`ChainComplex.linearYonedaObjExtendIso`).

## Main definitions and results

* `HomologicalComplex.mapExtendIso`: for a functor preserving zero morphisms,
  `(F.mapHomologicalComplex c').obj (K.extend e) ≅ ((F.mapHomologicalComplex c).obj K).extend e`,
  with component formulas `mapExtendIso_hom_f_comp_extendXIso_hom`,
  `mapExtendIso_inv_f_comp_map_extendXIso_hom`, and naturality `mapExtendIso_hom_naturality`.
* `ChainComplex.linearYonedaObjExtendIso`: the isomorphism of cochain complexes
  `(X.extend (ComplexShape.embeddingDownNatAdd r)).linearYonedaObj k Y ≅
    (X.linearYonedaObj k Y).extend (ComplexShape.embeddingUpNatAdd r)`,
  with component formulas `linearYonedaObjExtendIso_hom_f_apply`,
  `linearYonedaObjExtendIso_inv_f_apply`, and cocycle formula
  `iCycles_cyclesMap_linearYonedaObjExtendIso_inv_apply`.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace HomologicalComplex

section MapExtend

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroObject C] [HasZeroMorphisms D] [HasZeroObject D]
  (K : HomologicalComplex C c) (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c')

/-- The degree-`i'` component of `HomologicalComplex.mapExtendIso`. -/
private def mapExtendIsoX (i' : ι') :
    F.obj ((K.extend e).X i') ≅ (((F.mapHomologicalComplex c).obj K).extend e).X i' :=
  match h : e.r i' with
  | none =>
      IsZero.iso (F.map_isZero (K.isZero_extend_X' e i' h))
        (((F.mapHomologicalComplex c).obj K).isZero_extend_X' e i' h)
  | some _ =>
      F.mapIso (K.extendXIso e (e.f_eq_of_r_eq_some h)) ≪≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e (e.f_eq_of_r_eq_some h)).symm

private lemma mapExtendIsoX_hom_eq {i : ι} {i' : ι'} (hi : e.f i = i') :
    (mapExtendIsoX K F e i').hom =
      F.map (K.extendXIso e hi).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e hi).inv := by
  have hr : e.r i' = some i := e.r_eq_some hi
  unfold mapExtendIsoX
  split
  · rename_i hnone
    simp [hr] at hnone
  · rename_i j hj
    obtain rfl : j = i := Option.some.inj (hj.symm.trans hr)
    rfl

private lemma mapExtendIsoX_inv_eq {i : ι} {i' : ι'} (hi : e.f i = i') :
    (mapExtendIsoX K F e i').inv =
      (((F.mapHomologicalComplex c).obj K).extendXIso e hi).hom ≫
        F.map (K.extendXIso e hi).inv := by
  have hr : e.r i' = some i := e.r_eq_some hi
  unfold mapExtendIsoX
  split
  · rename_i hnone
    simp [hr] at hnone
  · rename_i j hj
    obtain rfl : j = i := Option.some.inj (hj.symm.trans hr)
    rfl

/-- **A zero-preserving functor commutes with extension by zero**:
`F(K.extend e) ≅ (F K).extend e`. -/
def mapExtendIso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents (mapExtendIsoX K F e) fun i' j' _ ↦ by
    obtain hi | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · exact (F.map_isZero (K.isZero_extend_X' e i' hi)).eq_of_src _ _
    · obtain hj | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · exact (((F.mapHomologicalComplex c).obj K).isZero_extend_X' e j' hj).eq_of_tgt _ _
      · have hi' : e.f i = i' := e.f_eq_of_r_eq_some hi
        have hj' : e.f j = j' := e.f_eq_of_r_eq_some hj
        dsimp only [Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_obj_d]
        rw [mapExtendIsoX_hom_eq K F e hi', mapExtendIsoX_hom_eq K F e hj',
          K.extend_d_eq e hi' hj', ((F.mapHomologicalComplex c).obj K).extend_d_eq e hi' hj']
        simp only [F.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
        rw [← F.map_comp_assoc (K.extendXIso e hj').inv, Iso.inv_hom_id, F.map_id, Category.id_comp]
        rfl

/-- In a degree `i' = e.f i`, the forward map of `mapExtendIso` intertwines the identifications
with `F.obj (K.X i)`. -/
@[reassoc (attr := simp)]
lemma mapExtendIso_hom_f_comp_extendXIso_hom {i : ι} {i' : ι'} (hi : e.f i = i') :
    (K.mapExtendIso F e).hom.f i' ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e hi).hom =
      F.map (K.extendXIso e hi).hom := by
  change (mapExtendIsoX K F e i').hom ≫ _ = _
  rw [mapExtendIsoX_hom_eq K F e hi, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In a degree `i' = e.f i`, the inverse map of `mapExtendIso` intertwines the identifications
with `F.obj (K.X i)`. -/
@[reassoc (attr := simp)]
lemma mapExtendIso_inv_f_comp_map_extendXIso_hom {i : ι} {i' : ι'} (hi : e.f i = i') :
    (K.mapExtendIso F e).inv.f i' ≫ F.map (K.extendXIso e hi).hom =
      (((F.mapHomologicalComplex c).obj K).extendXIso e hi).hom := by
  change (mapExtendIsoX K F e i').inv ≫ _ = _
  rw [mapExtendIsoX_inv_eq K F e hi, Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id]
  exact Category.comp_id _

/-- `HomologicalComplex.mapExtendIso` is natural in the complex `K`. -/
@[reassoc]
lemma mapExtendIso_hom_naturality {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c') :
    (F.mapHomologicalComplex c').map (extendMap φ e) ≫ (L.mapExtendIso F e).hom =
      (K.mapExtendIso F e).hom ≫ extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext i' : 1
  obtain hi | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
  · exact (F.map_isZero (K.isZero_extend_X' e i' hi)).eq_of_src _ _
  · have hi' : e.f i = i' := e.f_eq_of_r_eq_some hi
    rw [← cancel_mono (((F.mapHomologicalComplex c).obj L).extendXIso e hi').hom]
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc,
      mapExtendIso_hom_f_comp_extendXIso_hom, extendMap_f _ e hi',
      mapExtendIso_hom_f_comp_extendXIso_hom_assoc, Iso.inv_hom_id, Category.comp_id,
      F.map_comp]
    rw [← F.map_comp (L.extendXIso e hi').inv, Iso.inv_hom_id, F.map_id, Category.comp_id]

end MapExtend

end HomologicalComplex

namespace ChainComplex

section LinearYonedaExtend

variable {C : Type*} [Category* C] [Abelian C] (X : ChainComplex C ℕ)
  (k : Type*) [Ring k] [Linear k C] (Y : C) (r : ℕ)

/-- The degree-`n` component of `ChainComplex.linearYonedaObjExtendIso`. -/
private def linearYonedaObjExtendIsoX (n : ℕ) :
    (linearYonedaObj (X.extend (ComplexShape.embeddingDownNatAdd r)) k Y).X n ≅
      ((X.linearYonedaObj k Y).extend (ComplexShape.embeddingUpNatAdd r)).X n :=
  if h : r ≤ n then
    have hpd : (ComplexShape.embeddingDownNatAdd r).f (n - r) = n := by
      rw [ComplexShape.embeddingDownNatAdd_f]; exact Nat.sub_add_cancel h
    have hpu : (ComplexShape.embeddingUpNatAdd r).f (n - r) = n := by
      rw [ComplexShape.embeddingUpNatAdd_f]; exact Nat.sub_add_cancel h
    ((linearYoneda k C).obj Y).mapIso
        (X.extendXIso (ComplexShape.embeddingDownNatAdd r) hpd).symm.op ≪≫
      ((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r) hpu).symm
  else
    IsZero.iso
      (((linearYoneda k C).obj Y).map_isZero
        (X.isZero_extend_X (ComplexShape.embeddingDownNatAdd r) n fun p hp ↦ by
          simp only [ComplexShape.embeddingDownNatAdd_f] at hp
          omega).op)
      ((X.linearYonedaObj k Y).isZero_extend_X (ComplexShape.embeddingUpNatAdd r) n fun p hp ↦ by
        simp only [ComplexShape.embeddingUpNatAdd_f] at hp
        omega)

private lemma linearYonedaObjExtendIsoX_hom_apply {p n : ℕ} (hp : p + r = n)
    (g : (linearYonedaObj (X.extend (ComplexShape.embeddingDownNatAdd r)) k Y).X n) :
    ((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f p = n by simpa using hp)).hom
        ((linearYonedaObjExtendIsoX X k Y r n).hom g) =
      (X.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = n by simpa using hp)).inv ≫ g := by
  have hle : r ≤ n := by omega
  have hsub : n - r = p := by omega
  subst hsub
  simp only [linearYonedaObjExtendIsoX, dite_eq_left_of_eq_true (eq_true hle)]
  let eU := (X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
    (show (ComplexShape.embeddingUpNatAdd r).f (n - r) = n by simpa using hp)
  let x : (X.linearYonedaObj k Y).X (n - r) :=
    (X.extendXIso (ComplexShape.embeddingDownNatAdd r)
      (show (ComplexShape.embeddingDownNatAdd r).f (n - r) = n by simpa using hp)).inv ≫ g
  exact congrArg (fun φ ↦ φ.hom x) eU.inv_hom_id

private lemma linearYonedaObjExtendIsoX_inv_apply {p n : ℕ} (hp : p + r = n)
    (f : (X.linearYonedaObj k Y).X p) :
    (linearYonedaObjExtendIsoX X k Y r n).inv
        (((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
          (show (ComplexShape.embeddingUpNatAdd r).f p = n by simpa using hp)).inv f) =
      (X.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = n by simpa using hp)).hom ≫ f := by
  have hle : r ≤ n := by omega
  have hsub : n - r = p := by omega
  subst hsub
  simp only [linearYonedaObjExtendIsoX, dite_eq_left_of_eq_true (eq_true hle)]
  let eU := (X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
    (show (ComplexShape.embeddingUpNatAdd r).f (n - r) = n by simpa using hp)
  exact congrArg
    ((X.extendXIso (ComplexShape.embeddingDownNatAdd r)
      (show (ComplexShape.embeddingDownNatAdd r).f (n - r) = n by simpa using hp)).hom ≫ ·)
    (congrArg (fun φ ↦ φ.hom f) eU.inv_hom_id)

/-- **`Hom(-, Y)` commutes with shifting a `ℕ`-indexed chain complex up by `r` degrees**:
`Hom(X.extend (n ↦ n + r), Y) ≅ Hom(X, Y).extend (n ↦ n + r)`. -/
def linearYonedaObjExtendIso :
    linearYonedaObj (X.extend (ComplexShape.embeddingDownNatAdd r)) k Y ≅
      (X.linearYonedaObj k Y).extend (ComplexShape.embeddingUpNatAdd r) :=
  Hom.isoOfComponents (linearYonedaObjExtendIsoX X k Y r) fun i j hij ↦ by
    simp only [ComplexShape.up_Rel] at hij
    by_cases hi : r ≤ i
    · have hj : r ≤ j := by omega
      have hip : i - r + r = i := Nat.sub_add_cancel hi
      have hjp : j - r + r = j := Nat.sub_add_cancel hj
      have hipd : (ComplexShape.embeddingDownNatAdd r).f (i - r) = i := by simpa using hip
      have hjpd : (ComplexShape.embeddingDownNatAdd r).f (j - r) = j := by simpa using hjp
      have hipu : (ComplexShape.embeddingUpNatAdd r).f (i - r) = i := by simpa using hip
      have hjpu : (ComplexShape.embeddingUpNatAdd r).f (j - r) = j := by simpa using hjp
      rw [← cancel_mono ((X.linearYonedaObj k Y).extendXIso
        (ComplexShape.embeddingUpNatAdd r) hjpu).hom]
      ext (g : (X.extend (ComplexShape.embeddingDownNatAdd r)).X i ⟶ Y)
      have hL : ((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r) hjpu).hom
          ((linearYonedaObjExtendIsoX X k Y r j).hom
            ((linearYonedaObj (X.extend (ComplexShape.embeddingDownNatAdd r)) k Y).d i j g)) =
          (X.extendXIso (ComplexShape.embeddingDownNatAdd r) hjpd).inv ≫
            (X.extend (ComplexShape.embeddingDownNatAdd r)).d j i ≫ g :=
        linearYonedaObjExtendIsoX_hom_apply X k Y r hjp _
      have hR1 : ((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r) hjpu).hom
          (((X.linearYonedaObj k Y).extend (ComplexShape.embeddingUpNatAdd r)).d i j
            ((linearYonedaObjExtendIsoX X k Y r i).hom g)) =
          (X.linearYonedaObj k Y).d (i - r) (j - r)
            (((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r) hipu).hom
              ((linearYonedaObjExtendIsoX X k Y r i).hom g)) := by
        have hd := (X.linearYonedaObj k Y).extend_d_eq (ComplexShape.embeddingUpNatAdd r) hipu hjpu
        have hc : ((X.linearYonedaObj k Y).extend (ComplexShape.embeddingUpNatAdd r)).d i j ≫
            ((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r) hjpu).hom =
            ((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r) hipu).hom ≫
              (X.linearYonedaObj k Y).d (i - r) (j - r) := by
          rw [hd, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
        exact ConcreteCategory.congr_hom hc ((linearYonedaObjExtendIsoX X k Y r i).hom g)
      have hR2 : ((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r) hipu).hom
          ((linearYonedaObjExtendIsoX X k Y r i).hom g) =
          (X.extendXIso (ComplexShape.embeddingDownNatAdd r) hipd).inv ≫ g :=
        linearYonedaObjExtendIsoX_hom_apply X k Y r hip g
      change ((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r) hjpu).hom
          (((X.linearYonedaObj k Y).extend (ComplexShape.embeddingUpNatAdd r)).d i j
            ((linearYonedaObjExtendIsoX X k Y r i).hom g)) =
        ((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r) hjpu).hom
          ((linearYonedaObjExtendIsoX X k Y r j).hom
            ((linearYonedaObj (X.extend (ComplexShape.embeddingDownNatAdd r)) k Y).d i j g))
      rw [hR1, hR2, hL]
      change X.d (j - r) (i - r) ≫
          (X.extendXIso (ComplexShape.embeddingDownNatAdd r) hipd).inv ≫ g =
        (X.extendXIso (ComplexShape.embeddingDownNatAdd r) hjpd).inv ≫
          (X.extend (ComplexShape.embeddingDownNatAdd r)).d j i ≫ g
      rw [X.extend_d_eq (ComplexShape.embeddingDownNatAdd r) hjpd hipd]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · exact (((linearYoneda k C).obj Y).map_isZero
        (X.isZero_extend_X (ComplexShape.embeddingDownNatAdd r) i fun p hp ↦ by
          simp only [ComplexShape.embeddingDownNatAdd_f] at hp
          omega).op).eq_of_src _ _

/-- In degree `n = p + r`, the forward map of `linearYonedaObjExtendIso` sends a cochain
`g : (X.extend _).X n ⟶ Y` to `(X.extendXIso _ _).inv ≫ g` (after `extendXIso.hom`). -/
@[simp]
lemma linearYonedaObjExtendIso_hom_f_apply {p n : ℕ} (hp : p + r = n)
    (g : (linearYonedaObj (X.extend (ComplexShape.embeddingDownNatAdd r)) k Y).X n) :
    ((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f p = n by simpa using hp)).hom
        ((X.linearYonedaObjExtendIso k Y r).hom.f n g) =
      (X.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = n by simpa using hp)).inv ≫ g :=
  linearYonedaObjExtendIsoX_hom_apply X k Y r hp g

/-- In degree `n = p + r`, the inverse map of `linearYonedaObjExtendIso` sends a cochain
`f : X.X p ⟶ Y` (placed in the extended cochain complex via `extendXIso.inv`) to
`(X.extendXIso _ _).hom ≫ f`. -/
@[simp]
lemma linearYonedaObjExtendIso_inv_f_apply {p n : ℕ} (hp : p + r = n)
    (f : (X.linearYonedaObj k Y).X p) :
    (X.linearYonedaObjExtendIso k Y r).inv.f n
        (((X.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
          (show (ComplexShape.embeddingUpNatAdd r).f p = n by simpa using hp)).inv f) =
      (X.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = n by simpa using hp)).hom ≫ f :=
  linearYonedaObjExtendIsoX_inv_apply X k Y r hp f

/-- In degree `n = p + r`, transporting a cocycle `ψ` of `Hom(X, Y)` to
`Hom(X.extend (n ↦ n + r), Y)` via `extendCyclesIso.inv` and `linearYonedaObjExtendIso.inv`
gives the underlying cochain `(X.extendXIso _ _).hom ≫ iCycles p ψ`. -/
lemma iCycles_cyclesMap_linearYonedaObjExtendIso_inv_apply {p n : ℕ} (hp : p + r = n)
    (ψ : (X.linearYonedaObj k Y).cycles p) :
    (linearYonedaObj (X.extend (ComplexShape.embeddingDownNatAdd r)) k Y).iCycles n
        (cyclesMap (X.linearYonedaObjExtendIso k Y r).inv n
          (((X.linearYonedaObj k Y).extendCyclesIso (ComplexShape.embeddingUpNatAdd r)
            (show (ComplexShape.embeddingUpNatAdd r).f p = n by simpa using hp)).inv ψ)) =
      (X.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = n by simpa using hp)).hom ≫
        (X.linearYonedaObj k Y).iCycles p ψ := by
  have h₁ := ConcreteCategory.congr_hom
    (cyclesMap_i (X.linearYonedaObjExtendIso k Y r).inv n)
    (((X.linearYonedaObj k Y).extendCyclesIso (ComplexShape.embeddingUpNatAdd r)
      (show (ComplexShape.embeddingUpNatAdd r).f p = n by simpa using hp)).inv ψ)
  have h₂ := ConcreteCategory.congr_hom
    ((X.linearYonedaObj k Y).extendCyclesIso_inv_iCycles (ComplexShape.embeddingUpNatAdd r)
      (show (ComplexShape.embeddingUpNatAdd r).f p = n by simpa using hp)) ψ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
  rw [h₁, h₂]
  exact linearYonedaObjExtendIso_inv_f_apply X k Y r hp _

end LinearYonedaExtend

end ChainComplex
