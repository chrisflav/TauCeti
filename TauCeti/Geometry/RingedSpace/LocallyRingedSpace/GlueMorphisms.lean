/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Restrict
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.GlueMorphisms

/-!
# Gluing morphisms of locally ringed spaces along open covers

Let `X` and `Y` be locally ringed spaces and `(U i)_{i : ι}` an open cover of `X` (`⨆ i, U i = ⊤`).
A family of morphisms `f i : X|_{U i} ⟶ Y` agreeing on the pairwise intersections `U i ⊓ U j`
glues to a unique morphism `X ⟶ Y` restricting to each `f i` (EGA I, Ch. I, proof of 2.2.4, and
10.4.6).

On underlying presheafed spaces the glued morphism is constructed by
`AlgebraicGeometry.PresheafedSpace.glueMorphisms`, using preservation of pullbacks of open
immersions along the forgetful functor to `PresheafedSpace`. Locality on stalks follows because
every `x : X` lies in some `U i`, where the stalk map of the glued morphism composed with the
invertible stalk map of `X|_{U i} ⟶ X` agrees with the local stalk map of `f i`.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.glueMorphisms`: the morphism `X ⟶ Y` glued from compatible
  morphisms `f i : X|_{U i} ⟶ Y` on an open cover.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.pullback_fst_comp_eq_iff_restrictHomOfLE_inf`: overlap
  compatibility on the categorical pullback equals compatibility on `U i ⊓ U j`.
* `AlgebraicGeometry.LocallyRingedSpace.ofRestrict_glueMorphisms`: the glued morphism restricts to
  `f i` on each `U i`.
* `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_ofRestrict`: morphisms out of `X` are determined
  by their restrictions to an open cover.
* `AlgebraicGeometry.LocallyRingedSpace.existsUnique_of_ofRestrict`: unique existence of the glued
  morphism.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 2.2.4 and 10.4.6.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace

universe w u

variable {X Y : LocallyRingedSpace.{u}} {ι : Type w} (U : ι → Opens X)

/-- Two morphisms `f i : X|_{U i} ⟶ Y` and `f j : X|_{U j} ⟶ Y` agree on the categorical pullback
`X|_{U i} ×_X X|_{U j}` if and only if they agree after restricting to `X|_{U i ⊓ U j}`. -/
theorem pullback_fst_comp_eq_iff_restrictHomOfLE_inf
    (f : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ Y) (i j : ι) :
    pullback.fst (X.ofRestrict (U i).isOpenEmbedding) (X.ofRestrict (U j).isOpenEmbedding) ≫ f i =
        pullback.snd _ _ ≫ f j ↔
      X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
        X.restrictHomOfLE inf_le_right ≫ f j := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have w : X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫
        X.ofRestrict (U i).isOpenEmbedding =
      X.restrictHomOfLE inf_le_right ≫ X.ofRestrict (U j).isOpenEmbedding := by
      rw [restrictHomOfLE_ofRestrict, restrictHomOfLE_ofRestrict]
    rw [← pullback.lift_fst _ _ w, Category.assoc, h, pullback.lift_snd_assoc]
  · let ji := X.ofRestrict (U i).isOpenEmbedding
    let jj := X.ofRestrict (U j).isOpenEmbedding
    let jij := X.ofRestrict (U i ⊓ U j).isOpenEmbedding
    let p := pullback.fst ji jj ≫ ji
    have hrange : Set.range p.base ⊆ Set.range jij.base := by
      rintro _ ⟨z, rfl⟩
      have hcond := congrArg (fun g ↦ g.base z) (pullback.condition (f := ji) (g := jj))
      have hxi : p.base z ∈ U i := (pullback.fst ji jj).base z |>.2
      have hxj : p.base z ∈ U j := by
        have hz : p.base z = (pullback.snd ji jj ≫ jj).base z := hcond
        rw [hz]
        exact ((pullback.snd ji jj).base z).2
      exact ⟨⟨p.base z, hxi, hxj⟩, rfl⟩
    let l := IsOpenImmersion.lift jij p hrange
    have hfst : pullback.fst ji jj = l ≫ X.restrictHomOfLE inf_le_left := by
      rw [← cancel_mono ji, Category.assoc, restrictHomOfLE_ofRestrict, IsOpenImmersion.lift_fac]
    have hsnd : pullback.snd ji jj = l ≫ X.restrictHomOfLE inf_le_right := by
      rw [← cancel_mono jj, Category.assoc, restrictHomOfLE_ofRestrict, IsOpenImmersion.lift_fac]
      exact (pullback.condition (f := ji) (g := jj)).symm
    rw [hfst, hsnd, Category.assoc, h, Category.assoc]

private theorem toPresheafedSpace_pullback_cond
    (f : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ Y)
    (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.restrictHomOfLE inf_le_right ≫ f j)
    (i j : ι) :
    pullback.fst (X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding)
        (X.toPresheafedSpace.ofRestrict (U j).isOpenEmbedding) ≫ (f i).toHom =
      pullback.snd _ _ ≫ (f j).toHom := by
  let F := LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace
  have hpull := (pullback_fst_comp_eq_iff_restrictHomOfLE_inf U f i j).mpr (hf i j)
  have hmap := congrArg (fun k ↦ (PreservesPullback.iso F
    (X.ofRestrict (U i).isOpenEmbedding) (X.ofRestrict (U j).isOpenEmbedding)).inv ≫ F.map k) hpull
  rw [Functor.map_comp, Functor.map_comp, PreservesPullback.iso_inv_fst_assoc,
    PreservesPullback.iso_inv_snd_assoc] at hmap
  exact hmap

section Glue

variable (hU : ⨆ i, U i = ⊤) (f : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ Y)
  (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
    X.restrictHomOfLE inf_le_right ≫ f j)

private noncomputable def gluePsh : X.toPresheafedSpace ⟶ Y.toPresheafedSpace :=
  PresheafedSpace.glueMorphisms X.IsSheaf U hU (fun i ↦ (f i).toHom)
    (toPresheafedSpace_pullback_cond U f hf)

private theorem isLocalHom_stalkMap_gluePsh (x : X) :
    IsLocalHom ((gluePsh U hU f hf).stalkMap x).hom := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.symm ▸ trivial : x ∈ ⨆ i, U i)
  let y : X.toPresheafedSpace.restrict (U i).isOpenEmbedding := ⟨x, hi⟩
  have hcomp : X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding ≫ gluePsh U hU f hf =
      (f i).toHom :=
    PresheafedSpace.ofRestrict_glueMorphisms X.IsSheaf U hU (fun i ↦ (f i).toHom)
      (toPresheafedSpace_pullback_cond U f hf) i
  have hlocal : IsLocalHom
      (((X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding ≫
        gluePsh U hU f hf).stalkMap y).hom) := by
    rw [hcomp]
    exact (f i).prop y
  rw [PresheafedSpace.stalkMap.comp] at hlocal
  have : IsLocalHom (((X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding).stalkMap y).hom.comp
      ((gluePsh U hU f hf).stalkMap x).hom) := hlocal
  exact isLocalHom_of_comp _
    ((X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding).stalkMap y).hom

/-- **Gluing morphisms of locally ringed spaces.** Given an open cover `U i` of `X` (`⨆ i, U i = ⊤`)
and morphisms `f i : X|_{U i} ⟶ Y` agreeing on each overlap `U i ⊓ U j`, they glue to a morphism
`X ⟶ Y` restricting to each `f i` (`ofRestrict_glueMorphisms`), which is unique
(`hom_ext_of_ofRestrict`). -/
noncomputable def glueMorphisms : X ⟶ Y where
  toHom := gluePsh U hU f hf
  prop := isLocalHom_stalkMap_gluePsh U hU f hf

/-- The glued morphism restricts to `f i` on each open `U i` of the cover. -/
@[reassoc (attr := simp)]
theorem ofRestrict_glueMorphisms (i : ι) :
    X.ofRestrict (U i).isOpenEmbedding ≫ glueMorphisms U hU f hf = f i :=
  Hom.ext' (PresheafedSpace.ofRestrict_glueMorphisms X.IsSheaf U hU (fun i ↦ (f i).toHom)
    (toPresheafedSpace_pullback_cond U f hf) i)

include hU in
/-- **Morphisms of locally ringed spaces are determined locally.** Two morphisms `X ⟶ Y` agreeing
on every member of an open cover of `X` are equal. -/
theorem hom_ext_of_ofRestrict {g g' : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g = X.ofRestrict (U i).isOpenEmbedding ≫ g') :
    g = g' :=
  Hom.ext' (PresheafedSpace.hom_ext_of_ofRestrict X.IsSheaf U hU fun i ↦ congrArg Hom.toHom (h i))

include hU hf in
/-- **Unique existence of glued morphisms of locally ringed spaces** along an open cover. -/
theorem existsUnique_of_ofRestrict :
    ∃! g : X ⟶ Y, ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g = f i :=
  ⟨glueMorphisms U hU f hf, ofRestrict_glueMorphisms U hU f hf,
    fun _ hg ↦ hom_ext_of_ofRestrict U hU fun i ↦
      (hg i).trans (ofRestrict_glueMorphisms U hU f hf i).symm⟩

end Glue

end AlgebraicGeometry.LocallyRingedSpace
