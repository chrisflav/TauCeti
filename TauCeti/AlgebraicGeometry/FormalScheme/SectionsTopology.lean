/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Morphism
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.SectionsTopology

import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import TauCeti.Topology.Algebra.Ring.Basic

/-!
# The intrinsic topology on affine formal section rings

Every affine formal open `U` of a formal scheme `X` is the image of an open immersion
`f : Spf A ⟶ X.toLocallyRingedSpace` for some complete adic ring `A` of finite ideal type. Pulling
back the topology of `A` along the induced ring isomorphism `Γ(U, O_X) ≅ A` endows `Γ(U, O_X)` with
a canonical topology `IsAffineOpen.sectionsTopology`.

Automatic continuity of morphisms between formal spectra
(`TauCeti.FormalScheme.Spf.continuous_sectionsRingHom`) implies that any two formal-spectrum charts
of `U` differ by a homeomorphic ring equivalence on global sections, so `sectionsTopology` is
independent of the chosen chart. Equipped with this topology, `Γ(U, O_X)` is itself a complete adic
ring of finite ideal type (`isAdicRing`), its topologically nilpotent elements are precisely the
sections vanishing in the residue field at every point of `U`
(`isTopologicallyNilpotent_iff_evaluation_eq_zero`), and any finitely generated ideal with that
radical defines the topology (`sectionsTopology_eq_adic`). Consequently `X.restrict U` is
canonically isomorphic to `ofSpf Γ(U, O_X)` (`isoSpf`).

## Main definitions

* `TauCeti.FormalScheme.chartSectionsIso`: the ring isomorphism `Γ(U, O_X) ≅ A` induced by an open
  immersion `f : Spf A ⟶ X.toLocallyRingedSpace` with range `U`.
* `TauCeti.FormalScheme.IsAffineOpen.sectionsTopology`: the chart-independent intrinsic adic
  topology on `Γ(U, O_X)` for an affine formal open `U`.
* `TauCeti.FormalScheme.IsAffineOpen.chartSectionsHomeomorph`: the homeomorphism
  `(Γ(U, O_X), hU.sectionsTopology) ≃ₜ A` induced by any formal-spectrum chart of `U`.
* `TauCeti.FormalScheme.IsAffineOpen.fromSpf` and `TauCeti.FormalScheme.IsAffineOpen.isoSpf`: the
  canonical open immersion `ofSpf Γ(U, O_X) ⟶ X` with image `U` and the resulting isomorphism
  `X.restrict U ≅ ofSpf Γ(U, O_X)`.

## Main results

* `TauCeti.FormalScheme.IsAffineOpen.sectionsTopology_eq_induced` and
  `TauCeti.FormalScheme.IsAffineOpen.isHomeomorph_chartSectionsIso`: `sectionsTopology` agrees with
  the topology pulled back from every formal-spectrum chart of `U`.
* `TauCeti.FormalScheme.IsAffineOpen.isTopologicalRing`,
  `TauCeti.FormalScheme.IsAffineOpen.isAdicRing`, and `TauCeti.FormalScheme.IsAffineOpen.t2Space`:
  `(Γ(U, O_X), hU.sectionsTopology)` is a Hausdorff complete adic ring of finite ideal type.
* `TauCeti.FormalScheme.IsAffineOpen.isTopologicallyNilpotent_iff_evaluation_eq_zero` and
  `TauCeti.FormalScheme.IsAffineOpen.sectionsTopology_eq_adic`: intrinsic residue-field
  characterisation of topologically nilpotent sections and of ideals of definition on `Γ(U, O_X)`.
* `TauCeti.FormalScheme.sectionsTopology_top_ofSpf`: on `ofSpf A`, the intrinsic topology on global
  sections coincides with `Spf.quotientSectionsTopology`.
* `AlgebraicGeometry.Scheme.isAffineOpen_discreteTopology_sectionsTopology`: on an ordinary
  scheme viewed as a formal scheme, every affine formal open has the discrete section topology.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §§10.1.3, 10.2.2,
  10.4.2.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Topology Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme

section Chart

variable {X : LocallyRingedSpace.{u}} {U : Opens X}

/-- If the topological image of `f : Y ⟶ X` is contained in `U`, then the preimage of `U` under `f`
is `⊤`. -/
theorem map_eq_top_of_range_subset {Y : LocallyRingedSpace.{u}}
    (f : Y ⟶ X) (hU : Set.range f.base ⊆ (U : Set X)) :
    (Opens.map f.base).obj U = ⊤ := by
  ext y
  exact iff_of_true (hU ⟨y, rfl⟩) trivial

private theorem evaluation_eq_Γevaluation_of_eq_top {Y : LocallyRingedSpace.{u}} {V : Opens Y}
    (hV : V = ⊤) (q : V) (t : Y.presheaf.obj (op V)) :
    Y.evaluation q t = Y.Γevaluation q.1 (Y.presheaf.map (eqToHom (congrArg op hV)) t) := by
  subst hV
  simp [LocallyRingedSpace.Γevaluation]

/-- The ring isomorphism `Γ(U, O_X) ≅ A` induced by an open immersion `f : Spf A ⟶ X` with
topological image `U`. -/
noncomputable def chartSectionsIso {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : Spf A ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion f] (hrange : Set.range f.base = (U : Set X)) :
    X.presheaf.obj (op U) ≅ CommRingCat.of A := by
  have := (IsAdicRing.ideal_spec A).2.2
  have : IsIso (f.c.app (op U)) :=
    PresheafedSpace.IsOpenImmersion.isIso_of_subset f.toHom U hrange.ge
  exact asIso (f.c.app (op U)) ≪≫
    (Spf A).presheaf.mapIso (eqToIso (congrArg op (map_eq_top_of_range_subset f hrange.le))) ≪≫
    Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1

/-- `chartSectionsIso f hrange` sends `s ∈ Γ(U, O_X)` to the element of `A` corresponding on `⊤`
to `f.c.app (op U) s`. -/
theorem globalSectionsIso_inv_chartSectionsIso_hom {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : Spf A ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion f] (hrange : Set.range f.base = (U : Set X))
    (s : X.presheaf.obj (op U)) :
    (@Spf.globalSectionsIso A _ _ _ (IsAdicRing.ideal A) (IsAdicRing.ideal_spec A).2.2
      (IsAdicRing.ideal_spec A).2.1).inv ((chartSectionsIso f hrange).hom s) =
      (Spf A).presheaf.map (eqToHom (congrArg op (map_eq_top_of_range_subset f hrange.le)))
        (f.c.app (op U) s) := by
  have := (IsAdicRing.ideal_spec A).2.2
  let eA := Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1
  change eA.inv (eA.hom ((Spf A).presheaf.map _ (f.c.app (op U) s))) = _
  exact ConcreteCategory.congr_hom eA.hom_inv_id _

/-- Transition between two formal-spectrum charts of the same open `U` on `Γ(U, O_X)` is given by
`Spf.sectionsRingHom` of the lifted open-immersion comparison, and is therefore continuous. -/
private theorem chartSectionsIso_inv_comp_hom {A₁ A₂ : Type u}
    [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsAdicRing A₁]
    [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂] [IsAdicRing A₂]
    (f₁ : Spf A₁ ⟶ X) [LocallyRingedSpace.IsOpenImmersion f₁]
    (hrange₁ : Set.range f₁.base = (U : Set X))
    (f₂ : Spf A₂ ⟶ X) [LocallyRingedSpace.IsOpenImmersion f₂]
    (hrange₂ : Set.range f₂.base = (U : Set X)) :
    ((chartSectionsIso f₂ hrange₂).inv ≫ (chartSectionsIso f₁ hrange₁).hom).hom =
      Spf.sectionsRingHom (LocallyRingedSpace.IsOpenImmersion.lift f₂ f₁
        (hrange₁.trans hrange₂.symm).le) := by
  have := (IsAdicRing.ideal_spec A₁).2.2
  have := (IsAdicRing.ideal_spec A₂).2.2
  let g := LocallyRingedSpace.IsOpenImmersion.lift f₂ f₁ (hrange₁.trans hrange₂.symm).le
  have hg : g ≫ f₂ = f₁ := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  let e₁ := chartSectionsIso f₁ hrange₁
  let e₂ := chartSectionsIso f₂ hrange₂
  let g₁ := Spf.globalSectionsIso (IsAdicRing.ideal_spec A₁).2.1
  let htop₁ := map_eq_top_of_range_subset f₁ hrange₁.le
  let htop₂ := map_eq_top_of_range_subset f₂ hrange₂.le
  suffices hsuff : ∀ s : X.presheaf.obj (op U), e₁.hom s = Spf.sectionsRingHom g (e₂.hom s) by
    ext a
    exact (hsuff (e₂.inv a)).trans (congrArg (Spf.sectionsRingHom g)
      (ConcreteCategory.congr_hom e₂.inv_hom_id a))
  intro s
  apply (ConcreteCategory.bijective_of_isIso g₁.inv).injective
  have hlhs := globalSectionsIso_inv_chartSectionsIso_hom f₁ hrange₁ s
  let v₂ : op ((Opens.map f₂.base).obj U) ⟶ op ⊤ := eqToHom (congrArg op htop₂)
  have hrhs₁ : g₁.inv (Spf.sectionsRingHom g (e₂.hom s)) =
      g.c.app (op ⊤) ((Spf A₂).presheaf.map v₂ (f₂.c.app (op U) s)) :=
    ((ConcreteCategory.congr_hom (Spf.globalSectionsIso_inv_comp_c_app_top g)
      (e₂.hom s)).symm).trans (congrArg (g.c.app (op ⊤))
        (globalSectionsIso_inv_chartSectionsIso_hom f₂ hrange₂ s))
  have hnat := ConcreteCategory.congr_hom (g.c.naturality v₂) (f₂.c.app (op U) s)
  have hcongr := ConcreteCategory.congr_hom
    (PresheafedSpace.congr_app (congrArg LocallyRingedSpace.Hom.toHom hg.symm) (op U)) s
  let u₁ : op ((Opens.map (g ≫ f₂).base).obj U) ⟶ op ((Opens.map f₁.base).obj U) :=
    eqToHom (congrArg (fun k : Spf A₁ ⟶ X ↦ op ((Opens.map k.base).obj U)) hg)
  have hmap₁ : (Spf A₁).presheaf.map u₁ ≫
      (Spf A₁).presheaf.map (eqToHom (congrArg op htop₁)) =
      (Spf A₁).presheaf.map (((Opens.map g.base).op).map v₂) :=
    ((Spf A₁).presheaf.map_comp _ _).symm.trans
      (congrArg (Spf A₁).presheaf.map (Subsingleton.elim _ _))
  have hstep := ConcreteCategory.congr_hom hmap₁
    (g.c.app (op ((Opens.map f₂.base).obj U)) (f₂.c.app (op U) s))
  exact hlhs.trans ((congrArg ((Spf A₁).presheaf.map (eqToHom (congrArg op htop₁))) hcongr).trans
    (hstep.trans (hnat.symm.trans hrhs₁.symm)))

end Chart

namespace IsAffineOpen

variable {X : FormalScheme.{u}} {U : Opens X}

private structure ChartData (hU : X.IsAffineOpen U) where
  Ring : Type u
  [commRing : CommRing Ring]
  [topologicalSpace : TopologicalSpace Ring]
  [isTopologicalRing : IsTopologicalRing Ring]
  [isAdicRing : IsAdicRing Ring]
  hom : Spf Ring ⟶ X.toLocallyRingedSpace
  [isOpenImmersion : LocallyRingedSpace.IsOpenImmersion hom]
  range_eq : Set.range hom.base = (U : Set X)

attribute [instance] ChartData.commRing ChartData.topologicalSpace
  ChartData.isTopologicalRing ChartData.isAdicRing ChartData.isOpenImmersion

private noncomputable def chartData (hU : X.IsAffineOpen U) : ChartData hU :=
  let A := Classical.choose hU
  let h1 := Classical.choose_spec hU
  let cA := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let tA := Classical.choose h2
  let h3 := Classical.choose_spec h2
  let trA := Classical.choose h3
  let h4 := Classical.choose_spec h3
  let adA := Classical.choose h4
  let h5 := Classical.choose_spec h4
  let f := Classical.choose h5
  let hf := Classical.choose_spec h5
  @ChartData.mk X U hU A cA tA trA adA f hf.1 hf.2

/-- The intrinsic adic topology on `Γ(U, O_X)` for an affine formal open `U`, obtained by pulling
back the topology of a formal-spectrum chart along `chartSectionsIso`. By
`sectionsTopology_eq_induced`, it does not depend on the choice of chart. -/
@[instance_reducible]
noncomputable def sectionsTopology (hU : X.IsAffineOpen U) :
    TopologicalSpace (X.presheaf.obj (op U)) :=
  let c := chartData hU
  TopologicalSpace.induced (chartSectionsIso c.hom c.range_eq).hom inferInstance

/-- **Chart independence of `sectionsTopology`**: for *every* open immersion
`f : Spf A ⟶ X.toLocallyRingedSpace` with image `U`, `hU.sectionsTopology` is the pullback of the
topology of `A` along `chartSectionsIso f hrange`. -/
theorem sectionsTopology_eq_induced (hU : X.IsAffineOpen U) {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : Spf A ⟶ X.toLocallyRingedSpace)
    [LocallyRingedSpace.IsOpenImmersion f] (hrange : Set.range f.base = (U : Set X)) :
    hU.sectionsTopology =
      TopologicalSpace.induced (chartSectionsIso f hrange).hom ‹TopologicalSpace A› := by
  let c := chartData hU
  let t₀ : TopologicalSpace (X.presheaf.obj (op U)) :=
    TopologicalSpace.induced (chartSectionsIso c.hom c.range_eq).hom c.topologicalSpace
  let t₁ : TopologicalSpace (X.presheaf.obj (op U)) :=
    TopologicalSpace.induced (chartSectionsIso f hrange).hom ‹TopologicalSpace A›
  change t₀ = t₁
  apply le_antisymm
  · refine (@continuous_iff_le_induced _ _ _ t₀ ‹TopologicalSpace A›).mp ?_
    have hcomp : ((chartSectionsIso f hrange).hom : X.presheaf.obj (op U) → A) =
        ((chartSectionsIso c.hom c.range_eq).inv ≫ (chartSectionsIso f hrange).hom) ∘
          (chartSectionsIso c.hom c.range_eq).hom := by
      ext s
      exact (ConcreteCategory.congr_hom
        ((chartSectionsIso c.hom c.range_eq).hom_inv_id_assoc (chartSectionsIso f hrange).hom)
          s).symm
    rw [hcomp]
    have hcont : Continuous (((chartSectionsIso c.hom c.range_eq).inv ≫
        (chartSectionsIso f hrange).hom).hom) := by
      rw [chartSectionsIso_inv_comp_hom f hrange c.hom c.range_eq]
      exact Spf.continuous_sectionsRingHom _
    exact @Continuous.comp _ _ _ t₀ c.topologicalSpace _ _ _ hcont continuous_induced_dom
  · refine (@continuous_iff_le_induced _ _ _ t₁ c.topologicalSpace).mp ?_
    have hcomp : ((chartSectionsIso c.hom c.range_eq).hom : X.presheaf.obj (op U) → c.Ring) =
        ((chartSectionsIso f hrange).inv ≫ (chartSectionsIso c.hom c.range_eq).hom) ∘
          (chartSectionsIso f hrange).hom := by
      ext s
      exact (ConcreteCategory.congr_hom
        ((chartSectionsIso f hrange).hom_inv_id_assoc (chartSectionsIso c.hom c.range_eq).hom)
          s).symm
    rw [hcomp]
    have hcont : Continuous (((chartSectionsIso f hrange).inv ≫
        (chartSectionsIso c.hom c.range_eq).hom).hom) := by
      rw [chartSectionsIso_inv_comp_hom c.hom c.range_eq f hrange]
      exact Spf.continuous_sectionsRingHom _
    exact @Continuous.comp _ _ _ t₁ ‹TopologicalSpace A› _ _ _ hcont continuous_induced_dom

/-- The homeomorphism `(Γ(U, O_X), hU.sectionsTopology) ≃ₜ A` induced by an open immersion
`f : Spf A ⟶ X.toLocallyRingedSpace` with image `U`. Its forward and inverse maps are the
underlying functions of `(chartSectionsIso f hrange).hom` and `(chartSectionsIso f hrange).inv`. -/
@[expose] noncomputable def chartSectionsHomeomorph (hU : X.IsAffineOpen U) {A : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (f : Spf A ⟶ X.toLocallyRingedSpace) [LocallyRingedSpace.IsOpenImmersion f]
    (hrange : Set.range f.base = (U : Set X)) :
    @Homeomorph (X.presheaf.obj (op U)) A hU.sectionsTopology ‹TopologicalSpace A› :=
  letI : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  (chartSectionsIso f hrange).commRingCatIsoToRingEquiv.toEquiv.toHomeomorphOfIsInducing
    ⟨hU.sectionsTopology_eq_induced f hrange⟩

@[simp]
theorem chartSectionsHomeomorph_apply (hU : X.IsAffineOpen U) {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : Spf A ⟶ X.toLocallyRingedSpace)
    [LocallyRingedSpace.IsOpenImmersion f] (hrange : Set.range f.base = (U : Set X))
    (s : X.presheaf.obj (op U)) :
    hU.chartSectionsHomeomorph f hrange s = (chartSectionsIso f hrange).hom s := rfl

@[simp]
theorem chartSectionsHomeomorph_symm_apply (hU : X.IsAffineOpen U) {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : Spf A ⟶ X.toLocallyRingedSpace)
    [LocallyRingedSpace.IsOpenImmersion f] (hrange : Set.range f.base = (U : Set X)) (a : A) :
    (@Homeomorph.symm _ _ hU.sectionsTopology ‹TopologicalSpace A›
      (hU.chartSectionsHomeomorph f hrange)) a = (chartSectionsIso f hrange).inv a := rfl

/-- Every formal-spectrum chart `f : Spf A ⟶ X.toLocallyRingedSpace` with image `U` induces a
homeomorphism `(Γ(U, O_X), hU.sectionsTopology) → A` via `chartSectionsIso`. -/
theorem isHomeomorph_chartSectionsIso (hU : X.IsAffineOpen U) {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : Spf A ⟶ X.toLocallyRingedSpace)
    [LocallyRingedSpace.IsOpenImmersion f] (hrange : Set.range f.base = (U : Set X)) :
    @IsHomeomorph _ _ hU.sectionsTopology ‹TopologicalSpace A› (chartSectionsIso f hrange).hom := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  exact ((chartSectionsIso f hrange).commRingCatIsoToRingEquiv.toEquiv.toHomeomorphOfIsInducing
    ⟨hU.sectionsTopology_eq_induced f hrange⟩).isHomeomorph

/-- With `hU.sectionsTopology`, `Γ(U, O_X)` is a topological ring. -/
theorem isTopologicalRing (hU : X.IsAffineOpen U) :
    @IsTopologicalRing (X.presheaf.obj (op U)) hU.sectionsTopology _ := by
  obtain ⟨A, _, _, _, _, f, hf, hrange⟩ := id hU
  have := hf
  rw [hU.sectionsTopology_eq_induced f hrange]
  exact TauCeti.isTopologicalRing_induced (chartSectionsIso f hrange).hom.hom

/-- With `hU.sectionsTopology`, `Γ(U, O_X)` is a complete adic ring of finite ideal type. -/
theorem isAdicRing (hU : X.IsAffineOpen U) :
    @IsAdicRing (X.presheaf.obj (op U)) _ hU.sectionsTopology hU.isTopologicalRing := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  obtain ⟨A, _, _, _, _, f, hf, hrange⟩ := id hU
  have := hf
  exact IsAdicRing.of_ringEquiv (chartSectionsIso f hrange).commRingCatIsoToRingEquiv
    ⟨hU.sectionsTopology_eq_induced f hrange⟩

/-- With `hU.sectionsTopology`, `Γ(U, O_X)` is Hausdorff. -/
theorem t2Space (hU : X.IsAffineOpen U) :
    @T2Space (X.presheaf.obj (op U)) hU.sectionsTopology := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  infer_instance

/-- **Residue-field characterisation of topologically nilpotent sections**: a section
`s ∈ Γ(U, O_X)` over an affine formal open `U` is topologically nilpotent for `hU.sectionsTopology`
if and only if it vanishes in the residue field of `X` at every point of `U`. -/
theorem isTopologicallyNilpotent_iff_evaluation_eq_zero (hU : X.IsAffineOpen U)
    (s : X.presheaf.obj (op U)) :
    @IsTopologicallyNilpotent (X.presheaf.obj (op U)) _ hU.sectionsTopology s ↔
      ∀ x : U, X.toLocallyRingedSpace.evaluation x s = 0 := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  obtain ⟨A, _, _, _, _, f, hf, hrange⟩ := id hU
  have := hf
  have := (IsAdicRing.ideal_spec A).2.2
  let e := chartSectionsIso f hrange
  let he := hU.chartSectionsHomeomorph f hrange
  have htop := map_eq_top_of_range_subset f hrange.le
  have hnilp : IsTopologicallyNilpotent s ↔ IsTopologicallyNilpotent (e.hom s) := by
    refine ⟨fun hs ↦ hs.map (φ := e.hom.hom) he.continuous, fun ha ↦ ?_⟩
    have hinv : e.inv (e.hom s) = s := ConcreteCategory.congr_hom e.hom_inv_id s
    exact hinv ▸ ha.map (φ := e.inv.hom) he.continuous_symm
  rw [hnilp, (IsAdicRing.ideal_spec A).2.1.isTopologicallyNilpotent_iff_mem_radical,
    ← Spf.basicOpen_eq_bot_iff (IsAdicRing.ideal_spec A).2.1, eq_bot_iff]
  have hp_iff (p : Spf.carrier A) :
      e.hom s ∈ (p : PrimeSpectrum A).asIdeal ↔
        X.toLocallyRingedSpace.evaluation ⟨f.base p, hrange.le ⟨p, rfl⟩⟩ s = 0 := by
    have h1 := (Spf.Γevaluation_globalSectionsIso_inv_eq_zero_iff p (e.hom s)).symm
    have h2 : (Spf A).Γevaluation p
        ((Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv (e.hom s)) =
        (LocallyRingedSpace.residueFieldMap f p)
          (X.toLocallyRingedSpace.evaluation ⟨f.base p, hrange.le ⟨p, rfl⟩⟩ s) := by
      have ha := congrArg ((Spf A).Γevaluation p)
        (globalSectionsIso_inv_chartSectionsIso_hom f hrange s)
      have hb := (evaluation_eq_Γevaluation_of_eq_top htop ⟨p, htop ▸ trivial⟩
        (f.c.app (op U) s)).symm
      have hc := (LocallyRingedSpace.evaluation_naturality_apply f
        ⟨p, htop ▸ trivial⟩ s).symm
      exact ha.trans (hb.trans hc)
    exact h1.trans ((congrArg (· = 0) h2).to_iff.trans
      (let p' : Spf A := p
      map_eq_zero_iff (LocallyRingedSpace.residueFieldMap f p').hom (RingHom.injective _)))
  refine ⟨fun h x ↦ ?_, fun h p hp ↦ ?_⟩
  · obtain ⟨p, hp⟩ := hrange.ge x.2
    have hx : x = ⟨f.base p, hrange.le ⟨p, rfl⟩⟩ := Subtype.ext hp.symm
    rw [hx, ← hp_iff p]
    by_contra hnot
    exact h (Spf.mem_basicOpen.mpr hnot)
  · exact (Spf.mem_basicOpen.mp hp) ((hp_iff p).mpr (h ⟨f.base p, hrange.le ⟨p, rfl⟩⟩))

/-- **Intrinsic characterisation of `sectionsTopology`**: any finitely generated ideal `I` of
`Γ(U, O_X)` whose radical consists of the sections vanishing in every residue field on `U` defines
`hU.sectionsTopology` (`hU.sectionsTopology = I.adicTopology`). -/
theorem sectionsTopology_eq_adic (hU : X.IsAffineOpen U) {I : Ideal (X.presheaf.obj (op U))}
    (hIfg : I.FG)
    (hrad : ∀ s : X.presheaf.obj (op U),
      s ∈ I.radical ↔ ∀ x : U, X.toLocallyRingedSpace.evaluation x s = 0) :
    hU.sectionsTopology = I.adicTopology := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  have hJ := (IsAdicRing.ideal_spec (X.presheaf.obj (op U))).2.1
  have hJfg := (IsAdicRing.ideal_spec (X.presheaf.obj (op U))).1
  have heq : (IsAdicRing.ideal (X.presheaf.obj (op U))).radical = I.radical := by
    ext s
    rw [← hJ.isTopologicallyNilpotent_iff_mem_radical,
      hU.isTopologicallyNilpotent_iff_evaluation_eq_zero, hrad]
  exact IsAdic.of_radical_eq hJ hJfg hIfg heq

private theorem spf_map_eq_id {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (φ : A →+* A) (hφ : Continuous φ) (h : φ = RingHom.id A) :
    Spf.map φ hφ = 𝟙 (Spf A) := by
  subst h
  exact Spf.map_id

private noncomputable def chartSpfIso (hU : X.IsAffineOpen U) :
    @Spf (X.presheaf.obj (op U)) _ hU.sectionsTopology hU.isTopologicalRing hU.isAdicRing ≅
      Spf (chartData hU).Ring := by
  letI : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  let c := chartData hU
  let e := chartSectionsIso c.hom c.range_eq
  let he := hU.chartSectionsHomeomorph c.hom c.range_eq
  have hcont_inv : Continuous e.inv.hom := he.continuous_symm
  have hcont_hom : Continuous e.hom.hom := he.continuous
  refine
    { hom := Spf.map e.inv.hom hcont_inv
      inv := Spf.map e.hom.hom hcont_hom
      hom_inv_id := (Spf.map_comp e.inv.hom hcont_inv e.hom.hom hcont_hom).symm.trans
        (spf_map_eq_id _ _ (RingHom.ext fun x ↦ ConcreteCategory.congr_hom e.hom_inv_id x))
      inv_hom_id := (Spf.map_comp e.hom.hom hcont_hom e.inv.hom hcont_inv).symm.trans
        (spf_map_eq_id _ _ (RingHom.ext fun x ↦ ConcreteCategory.congr_hom e.inv_hom_id x)) }

/-- Auxiliary open immersion `Spf Γ(U, O_X) ⟶ X.toLocallyRingedSpace` obtained by transporting the
chosen chart along `chartSectionsIso`. -/
private noncomputable def fromSpfLRS (hU : X.IsAffineOpen U) :
    @Spf (X.presheaf.obj (op U)) _ hU.sectionsTopology hU.isTopologicalRing hU.isAdicRing ⟶
      X.toLocallyRingedSpace :=
  hU.chartSpfIso.hom ≫ (chartData hU).hom

/-- The canonical isomorphism between global sections of `Spf Γ(U, O_X)` and `Γ(U, O_X)`. -/
@[expose]
noncomputable def sectionsGlobalIso (hU : X.IsAffineOpen U) :
    (@Spf (X.presheaf.obj (op U)) _ hU.sectionsTopology hU.isTopologicalRing
      hU.isAdicRing).presheaf.obj (op ⊤) ≅ X.presheaf.obj (op U) := by
  letI : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  have := (IsAdicRing.ideal_spec (X.presheaf.obj (op U))).2.2
  exact Spf.globalSectionsIso (IsAdicRing.ideal_spec (X.presheaf.obj (op U))).2.1

/-- The canonical open immersion `ofSpf Γ(U, O_X) ⟶ X` with image `U`, where `Γ(U, O_X)` carries
`hU.sectionsTopology`. -/
noncomputable def fromSpf (hU : X.IsAffineOpen U) :
    @ofSpf (X.presheaf.obj (op U)) _ hU.sectionsTopology hU.isTopologicalRing hU.isAdicRing ⟶ X :=
  InducedCategory.homMk hU.fromSpfLRS

/-- `hU.fromSpf` is an open immersion of locally ringed spaces. -/
instance isOpenImmersion_fromSpf (hU : X.IsAffineOpen U) :
    LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map hU.fromSpf) := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  change LocallyRingedSpace.IsOpenImmersion (hU.chartSpfIso.hom ≫ (chartData hU).hom)
  infer_instance

/-- The topological image of `hU.fromSpf` is `U`. -/
@[simp]
theorem range_fromSpf (hU : X.IsAffineOpen U) :
    Set.range (forgetToLocallyRingedSpace.map hU.fromSpf).base = (U : Set X) :=
  (LocallyRingedSpace.range_iso_inv_comp hU.chartSpfIso.symm (chartData hU).hom).trans
    (chartData hU).range_eq

/-- On `op U`, `hU.fromSpf` acts via `hU.sectionsGlobalIso.inv`. -/
theorem fromSpf_c_app_self (hU : X.IsAffineOpen U) (s : X.presheaf.obj (op U)) :
    (@Spf (X.presheaf.obj (op U)) _ hU.sectionsTopology hU.isTopologicalRing
        hU.isAdicRing).presheaf.map
      (eqToHom (congrArg op (map_eq_top_of_range_subset hU.fromSpf.hom hU.range_fromSpf.le)))
      ((forgetToLocallyRingedSpace.map hU.fromSpf).c.app (op U) s) =
      hU.sectionsGlobalIso.inv s := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  have := (IsAdicRing.ideal_spec (X.presheaf.obj (op U))).2.2
  let c := chartData hU
  have := (IsAdicRing.ideal_spec c.Ring).2.2
  let e := chartSectionsIso c.hom c.range_eq
  let g := hU.chartSpfIso.hom
  have htopA := map_eq_top_of_range_subset c.hom c.range_eq.le
  have htopR := map_eq_top_of_range_subset hU.fromSpf.hom hU.range_fromSpf.le
  let vA : op ((Opens.map c.hom.base).obj U) ⟶ op ⊤ := eqToHom (congrArg op htopA)
  have hnat := ConcreteCategory.congr_hom (g.c.naturality vA) (c.hom.c.app (op U) s)
  have hmapR : (Spf (X.presheaf.obj (op U))).presheaf.map (((Opens.map g.base).op).map vA) =
      (Spf (X.presheaf.obj (op U))).presheaf.map (eqToHom (congrArg op htopR)) :=
    congrArg (Spf (X.presheaf.obj (op U))).presheaf.map (Subsingleton.elim _ _)
  have hstep := ConcreteCategory.congr_hom hmapR.symm
    (g.c.app (op ((Opens.map c.hom.base).obj U)) (c.hom.c.app (op U) s))
  have hg_top : g.c.app (op ⊤) ((Spf c.Ring).presheaf.map vA (c.hom.c.app (op U) s)) =
      hU.sectionsGlobalIso.inv s := by
    have hc := ConcreteCategory.congr_hom (Spf.globalSectionsIso_inv_comp_c_app_top g) (e.hom s)
    have hmap_inv : Spf.sectionsRingHom g (e.hom s) = s :=
      (congrArg (fun φ : c.Ring →+* _ ↦ φ (e.hom s)) (Spf.sectionsRingHom_map _ _)).trans
        (ConcreteCategory.congr_hom e.hom_inv_id s)
    exact (congrArg (g.c.app (op ⊤))
      (globalSectionsIso_inv_chartSectionsIso_hom c.hom c.range_eq s).symm).trans
      (hc.trans (congrArg hU.sectionsGlobalIso.inv hmap_inv))
  change (Spf (X.presheaf.obj (op U))).presheaf.map (eqToHom (congrArg op htopR))
    (g.c.app (op ((Opens.map c.hom.base).obj U)) (c.hom.c.app (op U) s)) = _
  exact hstep.trans (hnat.symm.trans hg_top)

/-- On global sections `op ⊤`, `hU.fromSpf` restricts `s ∈ Γ(X, O_X)` to `U` and maps it via
`hU.sectionsGlobalIso.inv`. -/
theorem fromSpf_c_app_top (hU : X.IsAffineOpen U) (s : X.presheaf.obj (op ⊤)) :
    (forgetToLocallyRingedSpace.map hU.fromSpf).c.app (op ⊤) s =
      hU.sectionsGlobalIso.inv (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  let i : Spf (X.presheaf.obj (op U)) ⟶ X.toLocallyRingedSpace := hU.fromSpf.hom
  have htopR := map_eq_top_of_range_subset i hU.range_fromSpf.le
  have hnat := ConcreteCategory.congr_hom (i.c.naturality (homOfLE (le_top : U ≤ ⊤)).op) s
  have hmap : (Spf (X.presheaf.obj (op U))).presheaf.map
        (((Opens.map i.base).map (homOfLE (le_top : U ≤ ⊤))).op) ≫
      (Spf (X.presheaf.obj (op U))).presheaf.map (eqToHom (congrArg op htopR)) = 𝟙 _ :=
    ((Spf (X.presheaf.obj (op U))).presheaf.map_comp _ _).symm.trans
      ((congrArg (Spf (X.presheaf.obj (op U))).presheaf.map (Subsingleton.elim _ _)).trans
        ((Spf (X.presheaf.obj (op U))).presheaf.map_id _))
  have hstep := (ConcreteCategory.congr_hom hmap (i.c.app (op ⊤) s)).symm
  exact hstep.trans ((congrArg ((Spf (X.presheaf.obj (op U))).presheaf.map
    (eqToHom (congrArg op htopR))) hnat.symm).trans
    (hU.fromSpf_c_app_self (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)))

private noncomputable def isoSpfLRS (hU : X.IsAffineOpen U) :
    X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅
      @Spf (X.presheaf.obj (op U)) _ hU.sectionsTopology hU.isTopologicalRing hU.isAdicRing := by
  letI : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  have hi : LocallyRingedSpace.IsOpenImmersion hU.fromSpfLRS := hU.isOpenImmersion_fromSpf
  have hj : LocallyRingedSpace.IsOpenImmersion
      (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) := inferInstance
  have hrange_i : Set.range hU.fromSpfLRS.base = (U : Set X) := hU.range_fromSpf
  have hji : Set.range (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).base ⊆
      Set.range hU.fromSpfLRS.base := Subtype.range_coe.trans_le hrange_i.ge
  have hij : Set.range hU.fromSpfLRS.base ⊆
      Set.range (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).base :=
    hrange_i.trans_le Subtype.range_coe.ge
  exact
    { hom := LocallyRingedSpace.IsOpenImmersion.lift hU.fromSpfLRS
        (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) hji
      inv := LocallyRingedSpace.IsOpenImmersion.lift
        (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) hU.fromSpfLRS hij
      hom_inv_id := (cancel_mono (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding)).mp
        (by simp)
      inv_hom_id := (cancel_mono hU.fromSpfLRS).mp (by simp) }

/-- For an affine formal open `U` of `X`, `X.restrict U` is canonically isomorphic to
`ofSpf Γ(U, O_X)`, where `Γ(U, O_X)` carries `hU.sectionsTopology`. -/
noncomputable def isoSpf (hU : X.IsAffineOpen U) :
    X.restrict U ≅
      @ofSpf (X.presheaf.obj (op U)) _ hU.sectionsTopology hU.isTopologicalRing hU.isAdicRing :=
  InducedCategory.isoMk hU.isoSpfLRS

/-- `hU.isoSpf.hom` followed by `hU.fromSpf` is the open inclusion `X.ofRestrict U`. -/
@[reassoc (attr := simp)]
theorem isoSpf_hom_fromSpf (hU : X.IsAffineOpen U) :
    hU.isoSpf.hom ≫ hU.fromSpf = X.ofRestrict U := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  have : LocallyRingedSpace.IsOpenImmersion hU.fromSpfLRS := hU.isOpenImmersion_fromSpf
  have hrange_i : Set.range hU.fromSpfLRS.base = (U : Set X) := hU.range_fromSpf
  have hof : (X.ofRestrict U).hom = X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding :=
    forgetToLocallyRingedSpace_map_ofRestrict X U
  exact InducedCategory.hom_ext
    ((LocallyRingedSpace.IsOpenImmersion.lift_fac hU.fromSpfLRS
      (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding)
      (Subtype.range_coe.trans_le hrange_i.ge)).trans hof.symm)

/-- `hU.isoSpf.inv` followed by `X.ofRestrict U` is `hU.fromSpf`. -/
@[reassoc (attr := simp)]
theorem isoSpf_inv_ofRestrict (hU : X.IsAffineOpen U) :
    hU.isoSpf.inv ≫ X.ofRestrict U = hU.fromSpf := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  have := hU.isAdicRing
  have hrange_i : Set.range hU.fromSpfLRS.base = (U : Set X) := hU.range_fromSpf
  have hof : (X.ofRestrict U).hom = X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding :=
    forgetToLocallyRingedSpace_map_ofRestrict X U
  exact InducedCategory.hom_ext
    ((congrArg (hU.isoSpfLRS.inv ≫ ·) hof).trans
      (LocallyRingedSpace.IsOpenImmersion.lift_fac
        (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) hU.fromSpfLRS
        (hrange_i.trans_le Subtype.range_coe.ge)))

/-- On global sections `op ⊤`, `hU.isoSpf.hom` sends `hU.sectionsGlobalIso.inv (s|_U)` to the
restriction `(X.ofRestrict U).c.app (op ⊤) s`. -/
theorem isoSpf_hom_c_app_top (hU : X.IsAffineOpen U) (s : X.presheaf.obj (op ⊤)) :
    (forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤)
        (hU.sectionsGlobalIso.inv (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)) =
      (forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (op ⊤) s := by
  have heq : (hU.isoSpf.hom ≫ hU.fromSpf).hom.toHom = (X.ofRestrict U).hom.toHom :=
    congrArg (fun k : X.restrict U ⟶ X ↦ k.hom.toHom) hU.isoSpf_hom_fromSpf
  have hcongr := ConcreteCategory.congr_hom (PresheafedSpace.congr_app heq (op ⊤)) s
  have hid : (X.restrict U).presheaf.map (eqToHom rfl) =
      𝟙 ((X.restrict U).presheaf.obj (op ⊤)) :=
    (congrArg (X.restrict U).presheaf.map (Subsingleton.elim _ _)).trans
      ((X.restrict U).presheaf.map_id _)
  have hcomp : (forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤)
      ((forgetToLocallyRingedSpace.map hU.fromSpf).c.app (op ⊤) s) =
      (forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (op ⊤) s :=
    hcongr.trans (ConcreteCategory.congr_hom hid _)
  exact (congrArg ((forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤))
    (hU.fromSpf_c_app_top s).symm).trans hcomp

end IsAffineOpen

/-- On the affine formal scheme `ofSpf A`, the intrinsic topology
`(isAffineOpen_top_ofSpf A).sectionsTopology` on global sections coincides with
`Spf.quotientSectionsTopology`. -/
theorem sectionsTopology_top_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (isAffineOpen_top_ofSpf A).sectionsTopology =
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 ⊤ := by
  have := (IsAdicRing.ideal_spec A).2.2
  have hi : LocallyRingedSpace.IsOpenImmersion (𝟙 (Spf A)) := inferInstance
  rw [@IsAffineOpen.sectionsTopology_eq_induced (ofSpf A) ⊤ (isAffineOpen_top_ofSpf A)
    A _ _ _ _ (𝟙 (Spf A)) hi Set.range_id]
  have hchart : ((@chartSectionsIso (Spf A) ⊤ A _ _ _ _ (𝟙 (Spf A)) hi Set.range_id).hom :
      (Spf A).presheaf.obj (op ⊤) → A) =
      (Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom := by
    have heq : (Spf A).presheaf.map
        (eqToHom (congrArg op (map_eq_top_of_range_subset (X := Spf A) (U := ⊤)
          (𝟙 (Spf A)) Set.range_id.le))) = 𝟙 _ :=
      (congrArg (Spf A).presheaf.map (Subsingleton.elim _ _)).trans ((Spf A).presheaf.map_id _)
    ext s
    dsimp [chartSectionsIso]
    exact congrArg (Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom
      (ConcreteCategory.congr_hom heq s)
  let : TopologicalSpace ((Spf.structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.obj (op ⊤)) :=
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 ⊤
  exact (congrArg (TopologicalSpace.induced · _) hchart).trans
    (Spf.isHomeomorph_globalSectionsIso (IsAdicRing.ideal_spec A).2.1).isInducing.eq_induced.symm

/-- Every affine formal open is quasi-compact. -/
theorem IsAffineOpen.isCompact {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsCompact (U : Set X) := by
  obtain ⟨A, _, _, _, _, f, _, hrange⟩ := hU
  have : CompactSpace ↑↑(Spf A).toPresheafedSpace :=
    Spf.compactSpace_carrier (IsAdicRing.ideal_spec A).2.1
  exact hrange ▸ isCompact_range f.base.hom.continuous

end TauCeti.FormalScheme

namespace AlgebraicGeometry.Scheme

open TauCeti TauCeti.FormalScheme

/-- On an ordinary scheme viewed as a formal scheme (`X.toFormalScheme`), every affine formal open
has the discrete intrinsic section topology. -/
theorem isAffineOpen_discreteTopology_sectionsTopology (X : Scheme.{u})
    {U : X.Opens} (hU : X.toFormalScheme.IsAffineOpen U) :
    @DiscreteTopology (X.toFormalScheme.presheaf.obj (op U)) hU.sectionsTopology := by
  let : TopologicalSpace (X.toFormalScheme.presheaf.obj (op U)) := hU.sectionsTopology
  have := hU.isTopologicalRing
  refine is_bot_adic_iff.mp (hU.sectionsTopology_eq_adic Submodule.fg_bot fun s ↦ ?_)
  have hrad : s ∈ (⊥ : Ideal (X.toFormalScheme.presheaf.obj (op U))).radical ↔ IsNilpotent s := by
    simp [Ideal.mem_radical_iff, IsNilpotent]
  have hnilp : IsNilpotent (s : X.presheaf.obj (op U)) ↔ X.basicOpen s = ⊥ :=
    Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU.isCompact s
  exact hrad.trans (hnilp.trans
    (X.toLocallyRingedSpace.basicOpen_eq_bot_iff_forall_evaluation_eq_zero s))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.IsAffineOpen

open TauCeti TauCeti.FormalScheme

/-- Every affine open subscheme of an ordinary scheme `X` is an affine formal open of
`X.toFormalScheme` (using the discrete topology on its coordinate ring). -/
theorem toFormalScheme {X : Scheme.{u}} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    X.toFormalScheme.IsAffineOpen U := by
  let R : Type u := Γ(X, U)
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have h1 : LocallyRingedSpace.IsOpenImmersion (Spf.discreteIsoSpec R).hom :=
    LocallyRingedSpace.IsOpenImmersion.of_isIso _
  have h2 : LocallyRingedSpace.IsOpenImmersion hU.fromSpec.toLRSHom :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (Scheme.forgetToLocallyRingedSpace.map hU.fromSpec))
  have hg : LocallyRingedSpace.IsOpenImmersion
      ((Spf.discreteIsoSpec R).hom ≫ hU.fromSpec.toLRSHom) :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (Spf.discreteIsoSpec R).hom h1
      hU.fromSpec.toLRSHom h2
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
    (Spf.discreteIsoSpec R).hom ≫ hU.fromSpec.toLRSHom, hg, ?_⟩
  exact (LocallyRingedSpace.range_iso_inv_comp (Spf.discreteIsoSpec R).symm
    hU.fromSpec.toLRSHom).trans hU.range_fromSpec

end AlgebraicGeometry.IsAffineOpen
