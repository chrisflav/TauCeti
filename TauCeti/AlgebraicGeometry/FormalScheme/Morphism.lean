/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.SectionsTopology
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.GlueMorphisms

import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The global morphism correspondence and automatic continuity for formal schemes

Let `X` be a formal scheme of finite ideal type and `A` a complete adic ring of finite ideal type.
Every morphism of formal schemes `f : X ⟶ ofSpf A` induces a ring homomorphism
`sectionsHom f : A →+* Γ(X, O_X)` on global sections, obtained by precomposing `f.c.app (op ⊤)` with
`Spf.globalSectionsIso`.

On every affine formal open `U` of `X`, the composite of `sectionsHom f` with restriction to `U`
equals `Spf.sectionsRingHom (hU.fromSpf ≫ f).hom` and is therefore continuous for the intrinsic
adic topology `hU.sectionsTopology` (`continuousOnAffines_sectionsHom`). Conversely, any ring
homomorphism `φ : A →+* Γ(X, O_X)` whose restrictions to affine formal opens are continuous
(`ContinuousOnAffines X A φ`) induces local morphisms `X.restrict U ⟶ ofSpf A` via `Spf.map` that
agree on overlaps and glue via `FormalScheme.glueMorphisms` to a unique morphism
`homSpf φ hφ : X ⟶ ofSpf A` (`homSpfEquiv`, EGA I, Ch. I, 10.4.6).

In addition, continuity on affine formal opens admits an open-cover-free residue-field criterion
(`continuousOnAffines_iff_Γevaluation_eq_zero`), and the section map `Γ(V, O_Y) →+* Γ(U, O_X)`
induced by *any* morphism of formal schemes `f : X ⟶ Y` between affine formal opens with
`U ≤ f ⁻¹' V` is automatically continuous (`sectionMap_continuous`).

## Main definitions

* `TauCeti.FormalScheme.restrictHomOfLE` and `TauCeti.FormalScheme.glueMorphisms`: open-immersion
  inclusions `X.restrict U ⟶ X.restrict V` for `U ≤ V` and gluing of morphisms along open covers.
* `TauCeti.FormalScheme.ContinuousOnAffines`: the predicate that `φ : A →+* Γ(X, O_X)` restricts to
  a continuous homomorphism into `(Γ(U, O_X), hU.sectionsTopology)` on every affine formal open `U`.
* `TauCeti.FormalScheme.sectionsHom`: the ring homomorphism `A →+* Γ(X, O_X)` induced by a morphism
  `X ⟶ ofSpf A`.
* `TauCeti.FormalScheme.homSpf` and `TauCeti.FormalScheme.homSpfEquiv`: the inverse construction
  and the bijection `(X ⟶ ofSpf A) ≃ { φ : A →+* Γ(X, O_X) // ContinuousOnAffines X A φ }`.

## Main results

* `TauCeti.FormalScheme.continuousOnAffines_iff_Γevaluation_eq_zero`: `φ` satisfies
  `ContinuousOnAffines X A φ` if and only if every element of an ideal of definition of `A` maps to
  a global section vanishing in the residue field at every point of `X`.
* `TauCeti.FormalScheme.continuousOnAffines_sectionsHom`,
  `TauCeti.FormalScheme.sectionsHom_injective`, `TauCeti.FormalScheme.sectionsHom_homSpf`,
  `TauCeti.FormalScheme.homSpf_sectionsHom`: the two directions of the global formal-spectrum
  adjunction (EGA I, Ch. I, 10.4.6; Stacks Tag 0AN0).
* `TauCeti.FormalScheme.sectionMap_continuous` and
  `TauCeti.FormalScheme.IsAffineOpen.continuous_restrict`: automatic continuity of section maps
  between affine formal opens along arbitrary morphisms and open inclusions of formal schemes.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §§10.2.2, 10.4.6.
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0).
-/

public section

open CategoryTheory Limits TopologicalSpace Topology Opposite AlgebraicGeometry

universe w u

namespace TauCeti.FormalScheme

section Gluing

/-- For opens `U ≤ V` of a formal scheme `X`, the open-immersion inclusion
`X.restrict U ⟶ X.restrict V`. -/
noncomputable def restrictHomOfLE (X : FormalScheme.{u}) {U V : Opens X} (h : U ≤ V) :
    X.restrict U ⟶ X.restrict V :=
  InducedCategory.homMk (X.toLocallyRingedSpace.restrictHomOfLE h)

theorem forgetToLocallyRingedSpace_map_restrictHomOfLE (X : FormalScheme.{u}) {U V : Opens X}
    (h : U ≤ V) :
    forgetToLocallyRingedSpace.map (X.restrictHomOfLE h) =
      X.toLocallyRingedSpace.restrictHomOfLE h :=
  (rfl)

/-- The inclusion `X.restrict U ⟶ X.restrict V` is an open immersion of locally ringed spaces. -/
instance isOpenImmersion_restrictHomOfLE (X : FormalScheme.{u}) {U V : Opens X} (h : U ≤ V) :
    LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map (X.restrictHomOfLE h)) :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (X.toLocallyRingedSpace.restrictHomOfLE h))

/-- Composing `X.restrict U ⟶ X.restrict V` with `X.ofRestrict V` gives `X.ofRestrict U`. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_ofRestrict (X : FormalScheme.{u}) {U V : Opens X} (h : U ≤ V) :
    X.restrictHomOfLE h ≫ X.ofRestrict V = X.ofRestrict U := by
  have hV : (X.ofRestrict V).hom = X.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding :=
    forgetToLocallyRingedSpace_map_ofRestrict X V
  have hU : (X.ofRestrict U).hom = X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding :=
    forgetToLocallyRingedSpace_map_ofRestrict X U
  exact InducedCategory.hom_ext
    ((congrArg (X.toLocallyRingedSpace.restrictHomOfLE h ≫ ·) hV).trans
      ((X.toLocallyRingedSpace.restrictHomOfLE_ofRestrict h).trans hU.symm))

/-- The inclusion of `X.restrict U` into itself is the identity. -/
@[simp]
theorem restrictHomOfLE_refl (X : FormalScheme.{u}) (U : Opens X) :
    X.restrictHomOfLE (le_refl U) = 𝟙 (X.restrict U) :=
  InducedCategory.hom_ext (X.toLocallyRingedSpace.restrictHomOfLE_refl U)

/-- Inclusions between restrictions of `X` to nested opens compose. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_comp (X : FormalScheme.{u}) {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    X.restrictHomOfLE h ≫ X.restrictHomOfLE k = X.restrictHomOfLE (h.trans k) :=
  InducedCategory.hom_ext (X.toLocallyRingedSpace.restrictHomOfLE_comp h k)

/-- **Gluing morphisms of formal schemes** along an open cover `⨆ i, U i = ⊤` from compatible local
morphisms `f i : X.restrict (U i) ⟶ Y` (EGA I, Ch. I, 10.4.6). -/
noncomputable def glueMorphisms {X Y : FormalScheme.{u}} {ι : Type w} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) (f : ∀ i, X.restrict (U i) ⟶ Y)
    (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.restrictHomOfLE inf_le_right ≫ f j) : X ⟶ Y :=
  InducedCategory.homMk (LocallyRingedSpace.glueMorphisms U hU (fun i ↦ (f i).hom)
    fun i j ↦ congrArg InducedCategory.Hom.hom (hf i j))

/-- The glued morphism of formal schemes restricts to `f i` on each open `U i` of the cover. -/
@[reassoc (attr := simp)]
theorem ofRestrict_glueMorphisms {X Y : FormalScheme.{u}} {ι : Type w} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) (f : ∀ i, X.restrict (U i) ⟶ Y)
    (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.restrictHomOfLE inf_le_right ≫ f j)
    (i : ι) :
    X.ofRestrict (U i) ≫ glueMorphisms U hU f hf = f i := by
  have hof : (X.ofRestrict (U i)).hom = X.toLocallyRingedSpace.ofRestrict (U i).isOpenEmbedding :=
    forgetToLocallyRingedSpace_map_ofRestrict X (U i)
  exact InducedCategory.hom_ext ((congrArg (· ≫ _) hof).trans
    (LocallyRingedSpace.ofRestrict_glueMorphisms U hU (fun j ↦ (f j).hom)
      (fun j k ↦ congrArg InducedCategory.Hom.hom (hf j k)) i))

/-- Morphisms of formal schemes out of `X` are uniquely determined by their restrictions to an open
cover of `X`. -/
theorem hom_ext_of_ofRestrict {X Y : FormalScheme.{u}} {ι : Type w} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) {g g' : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i) ≫ g = X.ofRestrict (U i) ≫ g') : g = g' := by
  refine InducedCategory.hom_ext (LocallyRingedSpace.hom_ext_of_ofRestrict U hU fun i ↦ ?_)
  have hof : (X.ofRestrict (U i)).hom = X.toLocallyRingedSpace.ofRestrict (U i).isOpenEmbedding :=
    forgetToLocallyRingedSpace_map_ofRestrict X (U i)
  exact (congrArg (· ≫ g.hom) hof.symm).trans
    ((congrArg InducedCategory.Hom.hom (h i)).trans (congrArg (· ≫ g'.hom) hof))

/-- Unique existence of a morphism of formal schemes glued from compatible morphisms on an open
cover. -/
theorem existsUnique_of_ofRestrict {X Y : FormalScheme.{u}} {ι : Type w} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) (f : ∀ i, X.restrict (U i) ⟶ Y)
    (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.restrictHomOfLE inf_le_right ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, X.ofRestrict (U i) ≫ g = f i :=
  ⟨glueMorphisms U hU f hf, ofRestrict_glueMorphisms U hU f hf,
    fun _ hg ↦ hom_ext_of_ofRestrict U hU fun i ↦
      (hg i).trans (ofRestrict_glueMorphisms U hU f hf i).symm⟩

end Gluing

section ContinuityAndCorrespondence

private theorem iSup_affineOpens_eq_top (X : FormalScheme.{u}) :
    (⨆ i : { U : Opens X // X.IsAffineOpen U }, i.1) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨U, hU, hxU, _⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ (⊤ : Opens X) from trivial)
  exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩

private theorem evaluation_map_homOfLE {Y : LocallyRingedSpace.{u}} {U W : Opens Y} (hUW : U ≤ W)
    (x : U) (s : Y.presheaf.obj (op W)) :
    Y.evaluation x (Y.presheaf.map (homOfLE hUW).op s) = Y.evaluation ⟨x.1, hUW x.2⟩ s :=
  congrArg (Y.residue x.1) (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hUW) x.1 x.2 s)

private theorem c_app_top_eq_of_eq {Y Z : FormalScheme.{u}} {g₁ g₂ : Y ⟶ Z} (h : g₁ = g₂)
    (s : Z.presheaf.obj (op ⊤)) :
    (forgetToLocallyRingedSpace.map g₁).c.app (op ⊤) s =
      (forgetToLocallyRingedSpace.map g₂).c.app (op ⊤) s := by
  have heq : g₁.hom.toHom = g₂.hom.toHom := congrArg (fun k : Y ⟶ Z ↦ k.hom.toHom) h
  have hcongr := ConcreteCategory.congr_hom (PresheafedSpace.congr_app heq (op ⊤)) s
  have hid : Y.presheaf.map (eqToHom rfl) = 𝟙 (Y.presheaf.obj (op ⊤)) :=
    (congrArg Y.presheaf.map (Subsingleton.elim _ _)).trans (Y.presheaf.map_id _)
  exact hcongr.trans (ConcreteCategory.congr_hom hid _)

/-- A ring homomorphism `φ : A →+* Γ(X, O_X)` is *continuous on affine opens* if, for every affine
formal open `U` of `X`, its composite with restriction `Γ(X, O_X) →+* Γ(U, O_X)` is continuous into
`(Γ(U, O_X), hU.sectionsTopology)` (EGA I, Ch. I, 10.4.6). -/
@[expose]
def ContinuousOnAffines (X : FormalScheme.{u}) (A : Type u) [CommRing A] [TopologicalSpace A]
    (φ : A →+* X.presheaf.obj (op ⊤)) : Prop :=
  ∀ ⦃U : Opens X⦄ (hU : X.IsAffineOpen U),
    @Continuous A (X.presheaf.obj (op U)) _ hU.sectionsTopology
      ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ)

/-- **Residue-field criterion for `ContinuousOnAffines`**: when some finitely generated ideal `K`
defines the topology of `A`, a ring homomorphism `φ : A →+* Γ(X, O_X)` is continuous on affine
formal opens of `X` if and only if, for any ideal of definition `I` of `A`, `φ a` vanishes in the
residue field at every point of `X` for all `a ∈ I`. Neither completeness of `A` nor finite
generation of `I` is needed. -/
theorem continuousOnAffines_iff_Γevaluation_eq_zero {X : FormalScheme.{u}} {A : Type u}
    [CommRing A] [TopologicalSpace A] {I K : Ideal A} (hI : IsAdic I) (hK : IsAdic K)
    (hKfg : K.FG) (φ : A →+* X.presheaf.obj (op ⊤)) :
    ContinuousOnAffines X A φ ↔
      ∀ a ∈ I, ∀ x : X, X.toLocallyRingedSpace.Γevaluation x (φ a) = 0 := by
  refine ⟨fun hφ a ha x ↦ ?_, fun h U hU ↦ ?_⟩
  · obtain ⟨U, hU, hxU, _⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ (⊤ : Opens X) from trivial)
    let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
    have := hU.isTopologicalRing
    have := hU.isAdicRing
    have hnilp : IsTopologicallyNilpotent (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ a)) :=
      (hI.isTopologicallyNilpotent_of_mem ha).map (hφ hU)
    have hev := (hU.isTopologicallyNilpotent_iff_evaluation_eq_zero _).mp hnilp ⟨x, hxU⟩
    exact (evaluation_map_homOfLE (le_top : U ≤ ⊤) ⟨x, hxU⟩ (φ a)).symm.trans hev
  · let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
    have := hU.isTopologicalRing
    have := hU.isAdicRing
    rw [hI.continuous_iff_forall_isTopologicallyNilpotent
      (IsAdicRing.ideal_spec (X.presheaf.obj (op U))).2.1 hK hKfg]
    intro a ha
    rw [hU.isTopologicallyNilpotent_iff_evaluation_eq_zero]
    intro x
    exact (evaluation_map_homOfLE (le_top : U ≤ ⊤) x (φ a)).trans (h a ha x.1)

/-- When `A` carries the discrete topology, every ring homomorphism `A →+* Γ(X, O_X)` satisfies
`ContinuousOnAffines`. -/
theorem continuousOnAffines_of_discreteTopology {X : FormalScheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [DiscreteTopology A] (φ : A →+* X.presheaf.obj (op ⊤)) :
    ContinuousOnAffines X A φ := by
  intro U hU
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  exact continuous_of_discreteTopology

/-- The ring homomorphism `A →+* Γ(X, O_X)` induced on global sections by a morphism of formal
schemes `f : X ⟶ ofSpf A`, read through `Spf.globalSectionsIso` (EGA I, Ch. I, 10.4.6). -/
noncomputable def sectionsHom {X : FormalScheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : X ⟶ ofSpf A) :
    A →+* X.presheaf.obj (op ⊤) :=
  have := (IsAdicRing.ideal_spec A).2.2
  ((Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫
    (forgetToLocallyRingedSpace.map f).c.app (op ⊤)).hom

/-- Applying `sectionsHom f` evaluates `f.c.app (op ⊤)` on `(Spf.globalSectionsIso _).inv a`. -/
theorem sectionsHom_apply {X : FormalScheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : X ⟶ ofSpf A) (a : A) :
    sectionsHom f a =
      (forgetToLocallyRingedSpace.map f).c.app (op ⊤)
        ((@Spf.globalSectionsIso A _ _ _ (IsAdicRing.ideal A) (IsAdicRing.ideal_spec A).2.2
          (IsAdicRing.ideal_spec A).2.1).inv a) :=
  (rfl)

/-- The identity morphism of `ofSpf A` induces `(Spf.globalSectionsIso _).inv` on global
sections. -/
@[simp]
theorem sectionsHom_id (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] :
    sectionsHom (𝟙 (ofSpf A)) =
      (@Spf.globalSectionsIso A _ _ _ (IsAdicRing.ideal A) (IsAdicRing.ideal_spec A).2.2
        (IsAdicRing.ideal_spec A).2.1).inv.hom := by
  ext a
  exact (rfl)

/-- Precomposing `f : X ⟶ ofSpf A` with `g : Y ⟶ X` composes `sectionsHom f` with the global-section
map of `g`. -/
@[simp]
theorem sectionsHom_comp {X Y : FormalScheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (g : Y ⟶ X) (f : X ⟶ ofSpf A) :
    sectionsHom (g ≫ f) =
      ((forgetToLocallyRingedSpace.map g).c.app (op ⊤)).hom.comp (sectionsHom f) := by
  ext a
  exact (rfl)

/-- For a morphism between affine formal schemes `f : ofSpf A ⟶ ofSpf B`, `sectionsHom f` is
`Spf.sectionsRingHom f.hom` followed by `(Spf.globalSectionsIso _).inv`. -/
theorem sectionsHom_ofSpf {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (f : ofSpf A ⟶ ofSpf B) :
    sectionsHom f =
      ((@Spf.globalSectionsIso A _ _ _ (IsAdicRing.ideal A) (IsAdicRing.ideal_spec A).2.2
        (IsAdicRing.ideal_spec A).2.1).inv.hom).comp (Spf.sectionsRingHom f.hom) := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  ext b
  exact ConcreteCategory.congr_hom (Spf.globalSectionsIso_inv_comp_c_app_top f.hom) b

/-- Along `f : X ⟶ ofSpf A`, `sectionsHom f a` vanishes in the residue field of `X` at `x` if and
only if `a` belongs to the open prime `f x` of `A` (EGA I, Ch. I, 10.2.2, 10.4.6). -/
theorem Γevaluation_sectionsHom_eq_zero_iff {X : FormalScheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : X ⟶ ofSpf A) (x : X) (a : A) :
    X.toLocallyRingedSpace.Γevaluation x (sectionsHom f a) = 0 ↔
      a ∈ (f.hom.base x : Spf.carrier A).1.asIdeal :=
  Spf.Γevaluation_c_app_top_eq_zero_iff f.hom x a

/-- On an affine formal open `U` of `X`, restricting `sectionsHom f` to `U` recovers
`Spf.sectionsRingHom` of the composite `hU.fromSpf ≫ f : ofSpf Γ(U, O_X) ⟶ ofSpf A`. -/
theorem IsAffineOpen.sectionsRingHom_fromSpf_comp {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] (f : X ⟶ ofSpf A) :
    @Spf.sectionsRingHom (X.presheaf.obj (op U)) A _ hU.sectionsTopology hU.isTopologicalRing
        hU.isAdicRing _ _ _ _ (hU.fromSpf ≫ f).hom =
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp (sectionsHom f) := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  have := (IsAdicRing.ideal_spec (X.presheaf.obj (op U))).2.2
  have := (IsAdicRing.ideal_spec A).2.2
  ext a
  apply (ConcreteCategory.bijective_of_isIso hU.sectionsGlobalIso.inv).injective
  have hc := (ConcreteCategory.congr_hom
    (Spf.globalSectionsIso_inv_comp_c_app_top (hU.fromSpf ≫ f).hom) a).symm
  exact hc.trans (hU.fromSpf_c_app_top (sectionsHom f a))

/-- Every morphism `f : X ⟶ ofSpf A` induces a global-section homomorphism satisfying
`ContinuousOnAffines`. -/
theorem continuousOnAffines_sectionsHom {X : FormalScheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : X ⟶ ofSpf A) :
    ContinuousOnAffines X A (sectionsHom f) := by
  intro U hU
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  rw [← IsAffineOpen.sectionsRingHom_fromSpf_comp hU f]
  exact Spf.continuous_sectionsRingHom (hU.fromSpf ≫ f).hom

/-- A morphism `X ⟶ ofSpf A` is uniquely determined by the ring homomorphism it induces on global
sections (EGA I, Ch. I, 10.4.6). -/
theorem sectionsHom_injective {X : FormalScheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    Function.Injective (sectionsHom (X := X) (A := A)) := by
  intro f₁ f₂ hφ
  refine hom_ext_of_ofRestrict (fun i : { U : Opens X // X.IsAffineOpen U } ↦ i.1)
    (iSup_affineOpens_eq_top X) fun ⟨U, hU⟩ ↦ ?_
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  apply (cancel_epi hU.isoSpf.inv).mp
  rw [hU.isoSpf_inv_ofRestrict_assoc, hU.isoSpf_inv_ofRestrict_assoc]
  apply InducedCategory.hom_ext
  apply Spf.sectionsRingHom_injective
  rw [IsAffineOpen.sectionsRingHom_fromSpf_comp hU f₁,
    IsAffineOpen.sectionsRingHom_fromSpf_comp hU f₂, hφ]

private noncomputable def homSpfLoc {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U)
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (φ : A →+* X.presheaf.obj (op ⊤)) (hφ : ContinuousOnAffines X A φ) :
    X.restrict U ⟶ ofSpf A :=
  hU.isoSpf.hom ≫ InducedCategory.homMk
    (@Spf.map (X.presheaf.obj (op U)) A _ hU.sectionsTopology hU.isTopologicalRing hU.isAdicRing
      _ _ _ _ ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ) (hφ hU))

private theorem sectionsHom_homSpfLoc {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U)
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (φ : A →+* X.presheaf.obj (op ⊤)) (hφ : ContinuousOnAffines X A φ) :
    sectionsHom (homSpfLoc hU φ hφ) =
      ((forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (op ⊤)).hom.comp φ := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  have := (IsAdicRing.ideal_spec (X.presheaf.obj (op U))).2.2
  have := (IsAdicRing.ideal_spec A).2.2
  let φU := (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ
  let m : Spf (X.presheaf.obj (op U)) ⟶ Spf A := Spf.map φU (hφ hU)
  ext a
  have hm : m.c.app (op ⊤) ((Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv a) =
      hU.sectionsGlobalIso.inv (φU a) := by
    have hc := ConcreteCategory.congr_hom (Spf.globalSectionsIso_inv_comp_c_app_top m) a
    exact hc.trans (congrArg hU.sectionsGlobalIso.inv
      (congrArg (fun ψ : A →+* _ ↦ ψ a) (Spf.sectionsRingHom_map φU (hφ hU))))
  exact (congrArg ((forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤)) hm).trans
    (hU.isoSpf_hom_c_app_top (φ a))

/-- The morphism of formal schemes `X ⟶ ofSpf A` glued from a ring homomorphism
`φ : A →+* Γ(X, O_X)` satisfying `ContinuousOnAffines X A φ` (EGA I, Ch. I, 10.4.6). -/
noncomputable def homSpf {X : FormalScheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (φ : A →+* X.presheaf.obj (op ⊤))
    (hφ : ContinuousOnAffines X A φ) : X ⟶ ofSpf A :=
  glueMorphisms (fun i : { U : Opens X // X.IsAffineOpen U } ↦ i.1) (iSup_affineOpens_eq_top X)
    (fun i ↦ homSpfLoc i.2 φ hφ) fun ⟨U, hU⟩ ⟨V, hV⟩ ↦ by
      apply sectionsHom_injective
      ext a
      rw [sectionsHom_comp, sectionsHom_comp, sectionsHom_homSpfLoc, sectionsHom_homSpfLoc]
      change ((X.restrictHomOfLE (inf_le_left : U ⊓ V ≤ U) ≫ X.ofRestrict U).hom.c.app (op ⊤))
          (φ a) =
        ((X.restrictHomOfLE (inf_le_right : U ⊓ V ≤ V) ≫ X.ofRestrict V).hom.c.app (op ⊤)) (φ a)
      exact (c_app_top_eq_of_eq (X.restrictHomOfLE_ofRestrict (inf_le_left : U ⊓ V ≤ U))
        (φ a)).trans
        (c_app_top_eq_of_eq (X.restrictHomOfLE_ofRestrict (inf_le_right : U ⊓ V ≤ V)) (φ a)).symm

/-- `homSpf φ hφ` induces `φ` on global sections. -/
@[simp]
theorem sectionsHom_homSpf {X : FormalScheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (φ : A →+* X.presheaf.obj (op ⊤))
    (hφ : ContinuousOnAffines X A φ) :
    sectionsHom (homSpf φ hφ) = φ := by
  ext a
  refine X.toLocallyRingedSpace.sheaf.eq_of_locally_eq'
    (fun i : { U : Opens X // X.IsAffineOpen U } ↦ i.1) ⊤ (fun _ ↦ homOfLE le_top)
    (iSup_affineOpens_eq_top X).ge (sectionsHom (homSpf φ hφ) a) (φ a) fun ⟨U, hU⟩ ↦ ?_
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  have hof : X.ofRestrict U ≫ homSpf φ hφ = homSpfLoc hU φ hφ :=
    ofRestrict_glueMorphisms (fun i : { U : Opens X // X.IsAffineOpen U } ↦ i.1) _ _ _ ⟨U, hU⟩
  have hcomp : hU.fromSpf ≫ homSpf φ hφ =
      InducedCategory.homMk (Spf.map
        ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ) (hφ hU)) :=
    (congrArg (· ≫ homSpf φ hφ) hU.isoSpf_inv_ofRestrict.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (hU.isoSpf.inv ≫ ·) hof).trans (hU.isoSpf.inv_hom_id_assoc _)))
  have hsec := congrArg (fun g : @ofSpf (X.presheaf.obj (op U)) _ hU.sectionsTopology
      hU.isTopologicalRing hU.isAdicRing ⟶ ofSpf A ↦ Spf.sectionsRingHom g.hom a) hcomp
  exact (congrArg (fun ψ : A →+* _ ↦ ψ a)
    (IsAffineOpen.sectionsRingHom_fromSpf_comp hU (homSpf φ hφ))).symm.trans
    (hsec.trans (congrArg (fun ψ : A →+* _ ↦ ψ a)
      (Spf.sectionsRingHom_map ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ)
        (hφ hU))))

/-- Gluing from `sectionsHom f` recovers `f`. -/
@[simp]
theorem homSpf_sectionsHom {X : FormalScheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : X ⟶ ofSpf A) :
    homSpf (sectionsHom f) (continuousOnAffines_sectionsHom f) = f :=
  sectionsHom_injective (sectionsHom_homSpf _ _)

/-- **Global formal-spectrum morphism correspondence** (EGA I, Ch. I, 10.4.6; Stacks Tag 0AN0):
morphisms `X ⟶ ofSpf A` correspond bijectively to ring homomorphisms `A →+* Γ(X, O_X)` that are
continuous on affine formal opens. -/
noncomputable def homSpfEquiv (X : FormalScheme.{u}) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (X ⟶ ofSpf A) ≃ { φ : A →+* X.presheaf.obj (op ⊤) // ContinuousOnAffines X A φ } where
  toFun f := ⟨sectionsHom f, continuousOnAffines_sectionsHom f⟩
  invFun φ := homSpf φ.1 φ.2
  left_inv := homSpf_sectionsHom
  right_inv φ := Subtype.ext (sectionsHom_homSpf φ.1 φ.2)

@[simp]
theorem homSpfEquiv_apply_coe {X : FormalScheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : X ⟶ ofSpf A) :
    (homSpfEquiv X A f : A →+* X.presheaf.obj (op ⊤)) = sectionsHom f :=
  (rfl)

@[simp]
theorem homSpfEquiv_symm_apply {X : FormalScheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (φ : { φ : A →+* X.presheaf.obj (op ⊤) // ContinuousOnAffines X A φ }) :
    (homSpfEquiv X A).symm φ = homSpf φ.1 φ.2 :=
  (rfl)

/-- `homSpf` is bijective on `{ φ : A →+* Γ(X, O_X) // ContinuousOnAffines X A φ }`. -/
theorem homSpf_bijective (X : FormalScheme.{u}) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    Function.Bijective
      (fun φ : { φ : A →+* X.presheaf.obj (op ⊤) // ContinuousOnAffines X A φ } ↦
        homSpf φ.1 φ.2) :=
  (homSpfEquiv X A).symm.bijective

/-- **Automatic continuity of section maps between affine formal opens**: for any morphism of formal
schemes `f : X ⟶ Y` and affine formal opens `U` of `X` and `V` of `Y` with `f(U) ⊆ V`
(`U ≤ (Opens.map f.hom.base).obj V`), the induced ring homomorphism `Γ(V, O_Y) →+* Γ(U, O_X)` is
continuous from `hV.sectionsTopology` to `hU.sectionsTopology`. -/
theorem sectionMap_continuous {X Y : FormalScheme.{u}} (f : X ⟶ Y) {V : Opens Y} {U : Opens X}
    (hV : Y.IsAffineOpen V) (hU : X.IsAffineOpen U)
    (hUV : U ≤ (Opens.map f.hom.base).obj V) :
    @Continuous (Y.presheaf.obj (op V)) (X.presheaf.obj (op U))
      hV.sectionsTopology hU.sectionsTopology
      ((forgetToLocallyRingedSpace.map f).c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op).hom := by
  let : TopologicalSpace (Y.presheaf.obj (op V)) := hV.sectionsTopology
  have := hV.isTopologicalRing
  have := hV.isAdicRing
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  have hIV := (IsAdicRing.ideal_spec (Y.presheaf.obj (op V))).2.1
  have hIVfg := (IsAdicRing.ideal_spec (Y.presheaf.obj (op V))).1
  have hIU := (IsAdicRing.ideal_spec (X.presheaf.obj (op U))).2.1
  refine (hIV.continuous_iff_forall_isTopologicallyNilpotent hIU hIV hIVfg).mpr fun s hs ↦ ?_
  rw [hU.isTopologicallyNilpotent_iff_evaluation_eq_zero]
  intro x
  have hsV : ∀ y : V, Y.toLocallyRingedSpace.evaluation y s = 0 :=
    (hV.isTopologicallyNilpotent_iff_evaluation_eq_zero s).mp
      (hIV.isTopologicallyNilpotent_of_mem hs)
  have hres := evaluation_map_homOfLE (Y := X.toLocallyRingedSpace) hUV x
    ((forgetToLocallyRingedSpace.map f).c.app (op V) s)
  have hnat := LocallyRingedSpace.evaluation_naturality_apply f.hom ⟨x.1, hUV x.2⟩ s
  exact hres.trans (hnat.symm.trans
    ((congrArg (LocallyRingedSpace.residueFieldMap f.hom x.1)
      (hsV ⟨f.hom.base x.1, hUV x.2⟩)).trans (map_zero _)))

/-- Restriction `Γ(U, O_X) →+* Γ(V, O_X)` between nested affine formal opens `V ≤ U` of `X` is
continuous for their intrinsic section topologies. -/
theorem IsAffineOpen.continuous_restrict {X : FormalScheme.{u}} {U V : Opens X}
    (hU : X.IsAffineOpen U) (hV : X.IsAffineOpen V) (hVU : V ≤ U) :
    @Continuous (X.presheaf.obj (op U)) (X.presheaf.obj (op V))
      hU.sectionsTopology hV.sectionsTopology (X.presheaf.map (homOfLE hVU).op).hom := by
  have heq : ((forgetToLocallyRingedSpace.map (𝟙 X)).c.app (op U) ≫
      X.presheaf.map (homOfLE hVU).op).hom = (X.presheaf.map (homOfLE hVU).op).hom := by
    ext s
    exact (rfl)
  exact (congrArg (fun φ : _ →+* _ ↦ @Continuous _ _ hU.sectionsTopology hV.sectionsTopology φ)
    heq).mp (sectionMap_continuous (𝟙 X) hU hV hVU)

end ContinuityAndCorrespondence

end TauCeti.FormalScheme
