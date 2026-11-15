/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Functoriality
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Quotient

import TauCeti.Topology.Sheaves.Functors

/-!
# Morphisms of formal spectra

A continuous homomorphism of adic rings induces a morphism of locally ringed spaces
in the opposite direction. The underlying continuous map pulls back open primes and the
structure-sheaf map is obtained from the maps of quotient thickenings.

This file proves that the resulting stalk maps are local: after composing with an
ideal-of-definition quotient, they agree with the stalk maps of morphisms of ordinary
schemes. It also records the compatibility with every quotient thickening and the induced
map on global sections. The identities `map_id` and `map_comp` make this construction
contravariantly functorial.

Conversely, every morphism of locally ringed spaces `f : Spf A ⟶ Spf B` between formal spectra of
adic rings of finite ideal type induces a ring homomorphism `sectionsRingHom f : B →+* A` on global
sections that is automatically continuous (`continuous_sectionsRingHom`) and uniquely determines `f`
(`sectionsRingHom_injective`, `map_sectionsRingHom`). Together these establish the bijection
`homEquiv : (Spf A ⟶ Spf B) ≃ { φ : B →+* A // Continuous φ }` and the ideal-power continuity
criterion `homEquiv_pow` (EGA I, Ch. I, 10.2.2). No noetherian hypothesis is needed.

## Main definitions

* `TauCeti.FormalScheme.Spf.map`: the morphism `Spf A ⟶ Spf B` induced by a continuous ring
  homomorphism `B →+* A`.
* `TauCeti.FormalScheme.Spf.sectionsRingHom`: the ring homomorphism `B →+* A` induced on global
  sections by a morphism `Spf A ⟶ Spf B`.
* `TauCeti.FormalScheme.Spf.homEquiv`: the bijection between `Spf A ⟶ Spf B` and continuous ring
  homomorphisms `B →+* A`.

## Main results

* `TauCeti.FormalScheme.Spf.continuous_sectionsRingHom`: automatic continuity of the global-section
  homomorphism of any morphism `Spf A ⟶ Spf B`.
* `TauCeti.FormalScheme.Spf.sectionsRingHom_injective` and
  `TauCeti.FormalScheme.Spf.map_sectionsRingHom`: every morphism `Spf A ⟶ Spf B` is uniquely
  recovered as `Spf.map` of its global-section homomorphism.
* `TauCeti.FormalScheme.Spf.homEquiv_pow`: equivalence of existence of a lift `Spf A ⟶ Spf B`,
  continuity, the radical condition, and the ideal-power condition.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*,
  Ch. 0, 7.1.3–7.1.4, and Ch. I, 10.2.1–10.2.2.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme.Spf

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsAdicRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
  (φ : B →+* A) (hφ : Continuous φ) {K : Ideal B} {L : Ideal A}

/-- The continuous map and the inverse-limit sheaf map, before checking locality. -/
private noncomputable def mapPresheafedSpace :
    (Spf A).toPresheafedSpace ⟶ (Spf B).toPresheafedSpace where
  base := TopCat.ofHom (comap φ hφ)
  c := (structureSheafMap φ hφ (IsAdicRing.ideal_spec B).2.1
    (IsAdicRing.ideal_spec A).2.1).hom

-- The extra restriction `i` accounts for the equality, rather than definitional equality,
-- of the base maps in the square of quotient thickenings.
omit [IsTopologicalRing A] [IsAdicRing A] [IsTopologicalRing B] [IsAdicRing B] in
private theorem specQuotientMap_c_app (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L.comap φ) (U : Opens (carrier B))
    (i : (Opens.map (quotientInclusion hL)).obj
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U) ⟶
      (Opens.map (Spec.topMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL)))).obj
        ((Opens.map (quotientInclusion hK)).obj U)) :
    (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL))).c.app
        (op ((Opens.map (quotientInclusion hK)).obj U)) ≫
      (Spec.locallyRingedSpaceObj (CommRingCat.of (A ⧸ L))).presheaf.map i.op =
        (quotientMap φ hφ hK hL hKL).hom.app (op U) := by
  refine CommRingCat.hom_ext ?_
  rw [CommRingCat.hom_comp]
  have hc : ((Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL))).c.app
      (op ((Opens.map (quotientInclusion hK)).obj U))).hom =
      StructureSheaf.comap (Ideal.quotientMap L φ hKL)
        ((Opens.map (quotientInclusion hK)).obj U) _ fun _ ↦ id :=
    rfl
  have hmap := congrArg CommRingCat.Hom.hom
    (Spec.locallyRingedSpaceObj_presheaf_map (CommRingCat.of (A ⧸ L)) i.op)
  have hquot := congrArg CommRingCat.Hom.hom (quotientMap_hom_app φ hφ hK hL hKL (op U))
  exact (congrArg₂ RingHom.comp hmap hc).trans
    ((StructureSheaf.map_comp_comap (Ideal.quotientMap L φ hKL)
      ((Opens.map (quotientInclusion hK)).obj U) _ i).trans hquot.symm)

/-- On every compatible pair of thickenings the constructed map is the ordinary spectrum map. -/
private theorem fromSpecQuotient_comp_mapPresheafedSpace (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L.comap φ) :
    (fromSpecQuotient hL).toHom ≫ mapPresheafedSpace φ hφ =
      (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL)) ≫
        fromSpecQuotient hK).toHom := by
  let f₁ := (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL))).toHom
  let g₁ : (Spec.locallyRingedSpaceObj (CommRingCat.of (B ⧸ K))).toPresheafedSpace ⟶
      (Spf B).toPresheafedSpace :=
    { base := quotientInclusion hK
      c := (toQuotientSheaf (IsAdicRing.ideal_spec B).2.1 hK).hom }
  let f₂ : (Spec.locallyRingedSpaceObj (CommRingCat.of (A ⧸ L))).toPresheafedSpace ⟶
      (Spf A).toPresheafedSpace :=
    { base := quotientInclusion hL
      c := (toQuotientSheaf (IsAdicRing.ideal_spec A).2.1 hL).hom }
  have hbase : (f₁ ≫ g₁).base = (f₂ ≫ mapPresheafedSpace φ hφ).base := by
    apply ConcreteCategory.hom_ext
    intro q
    exact (comap_quotientInclusion φ hφ hK hL hKL q).symm
  rw [LocallyRingedSpace.comp_toHom, fromSpecQuotient_toHom hK, fromSpecQuotient_toHom hL]
  symm
  refine PresheafedSpace.Hom.ext _ _ hbase ?_
  ext U : 1
  refine CommRingCat.hom_ext ?_
  rw [NatTrans.comp_app, Functor.whiskerRight_app, CommRingCat.hom_comp]
  have hcomp₁ := (congrArg CommRingCat.Hom.hom
    (PresheafedSpace.comp_c_app f₁ g₁ (op U))).trans (CommRingCat.hom_comp _ _)
  have hcomp₂ := (congrArg CommRingCat.Hom.hom
    (PresheafedSpace.comp_c_app f₂ (mapPresheafedSpace φ hφ) (op U))).trans
      (CommRingCat.hom_comp _ _)
  have hspec := congrArg CommRingCat.Hom.hom (specQuotientMap_c_app φ hφ hK hL hKL U
    (eqToHom (congrArg (fun f ↦ (Opens.map f).obj U) hbase.symm)))
  have hsheaf := congrArg (fun η ↦ (η.hom.app (op U)).hom)
    (structureSheafMap_comp_toQuotientSheaf φ hφ (IsAdicRing.ideal_spec B).2.1
      (IsAdicRing.ideal_spec A).2.1 hK hL hKL).symm
  exact (congrArg (RingHom.comp _) hcomp₁).trans <| (RingHom.comp_assoc _ _ _).symm.trans <|
    (congrArg₂ RingHom.comp ((CommRingCat.hom_comp _ _).symm.trans hspec) rfl).trans <|
      hsheaf.trans hcomp₂.symm

/-- Locality can be checked after passing to a quotient thickening through every point. -/
private theorem mapPresheafedSpace_isLocalHom (p : carrier A) :
    IsLocalHom ((mapPresheafedSpace φ hφ).stalkMap p).hom := by
  let L := IsAdicRing.ideal A
  have hL : IsAdic L := (IsAdicRing.ideal_spec A).2.1
  obtain ⟨n, hn⟩ := IsAdic.exists_pow_succ_le_comap (IsAdicRing.ideal_spec B).2.1
    (by simpa using hL.isOpen_pow 1) hφ
  let K := IsAdicRing.ideal B ^ (n + 1)
  have hK : IsAdic K := is_ideal_adic_pow (IsAdicRing.ideal_spec B).2.1 n.succ_pos
  let q := homeomorphSpecQuotient hL p
  have hp : (fromSpecQuotient hL).base q = p := by
    rw [fromSpecQuotient_points]
    exact (homeomorphSpecQuotient hL).symm_apply_apply p
  have hlocal : IsLocalHom
      (((fromSpecQuotient hL).toHom ≫ mapPresheafedSpace φ hφ).stalkMap q).hom := by
    rw [fromSpecQuotient_comp_mapPresheafedSpace φ hφ hK hL hn]
    exact LocallyRingedSpace.isLocalHomStalkMap'
      (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hn)) ≫
        fromSpecQuotient hK) q
  have hcomp : (((fromSpecQuotient hL).toHom ≫ mapPresheafedSpace φ hφ).stalkMap q).hom =
      ((fromSpecQuotient hL).stalkMap q).hom.comp
        ((mapPresheafedSpace φ hφ).stalkMap ((fromSpecQuotient hL).base q)).hom :=
    (congrArg CommRingCat.Hom.hom
      (PresheafedSpace.stalkMap.comp (fromSpecQuotient hL).toHom (mapPresheafedSpace φ hφ) q)).trans
      (CommRingCat.hom_comp _ _)
  have : IsLocalHom (((fromSpecQuotient hL).stalkMap q).hom.comp
      ((mapPresheafedSpace φ hφ).stalkMap ((fromSpecQuotient hL).base q)).hom) :=
    hcomp ▸ hlocal
  have := isLocalHom_of_comp
    ((mapPresheafedSpace φ hφ).stalkMap ((fromSpecQuotient hL).base q)).hom
    ((fromSpecQuotient hL).stalkMap q).hom
  rwa [hp] at this

/-- The morphism of locally ringed spaces induced contravariantly by a continuous ring
homomorphism. On points it pulls back open primes, and on quotient thickenings it is induced
by the corresponding quotient ring homomorphisms (EGA I, Ch. I, 10.2.1). -/
noncomputable def map : Spf A ⟶ Spf B where
  toHom := mapPresheafedSpace φ hφ
  prop := mapPresheafedSpace_isLocalHom φ hφ

/-- The underlying map of `Spf.map` pulls back open prime ideals. -/
@[simp]
theorem map_base : (map φ hφ).base = TopCat.ofHom (comap φ hφ) :=
  (rfl)

/-- The underlying presheafed-space morphism of `Spf.map`, including its sheaf component. -/
theorem map_toHom : (map φ hφ).toHom =
    { base := TopCat.ofHom (comap φ hφ)
      c := (structureSheafMap φ hφ (IsAdicRing.ideal_spec B).2.1
        (IsAdicRing.ideal_spec A).2.1).hom } :=
  (rfl)

/-- `Spf.map` commutes with every compatible pair of ideal-of-definition quotient inclusions. -/
@[reassoc]
theorem fromSpecQuotient_comp_map (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L.comap φ) :
    fromSpecQuotient hL ≫ map φ hφ =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL)) ≫
        fromSpecQuotient hK := by
  apply LocallyRingedSpace.Hom.ext'
  exact fromSpecQuotient_comp_mapPresheafedSpace φ hφ hK hL hKL

/-- Under the global-section comparisons, the map induced by `Spf.map φ` is `φ`
(EGA I, Ch. I, 10.2.2). -/
@[reassoc]
theorem map_globalSections :
    have := (IsAdicRing.ideal_spec A).2.2
    have := (IsAdicRing.ideal_spec B).2.2
    (map φ hφ).c.app (op ⊤) ≫ (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom =
      (globalSectionsIso (IsAdicRing.ideal_spec B).2.1).hom ≫ CommRingCat.ofHom φ := by
  intro _ _
  exact structureSheafMap_hom_app_top_comp_globalSectionsIso_hom φ hφ
    (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec A).2.1

/-- A morphism of formal spectra determines the continuous ring homomorphism that induces it. -/
theorem map_injective {φ ψ : B →+* A} {hφ : Continuous φ} {hψ : Continuous ψ}
    (h : map φ hφ = map ψ hψ) : φ = ψ := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  have hglobal :
      (globalSectionsIso (IsAdicRing.ideal_spec B).2.1).hom ≫ CommRingCat.ofHom φ =
        (globalSectionsIso (IsAdicRing.ideal_spec B).2.1).hom ≫ CommRingCat.ofHom ψ := by
    rw [← map_globalSections φ hφ, h, map_globalSections ψ hψ]
  have hmaps := (cancel_epi (globalSectionsIso (IsAdicRing.ideal_spec B).2.1).hom).mp hglobal
  exact congrArg CommRingCat.Hom.hom hmaps

/-- The identity homomorphism induces the identity morphism of formal spectra. -/
@[simp]
theorem map_id : map (RingHom.id A) continuous_id = 𝟙 (Spf A) := by
  have hid : TopCat.ofHom (comap (RingHom.id A) continuous_id) = 𝟙 (TopCat.of (carrier A)) := by
    simp
  apply LocallyRingedSpace.Hom.ext'
  rw [map_toHom, LocallyRingedSpace.id_toHom]
  refine PresheafedSpace.Hom.ext _ _ hid ?_
  rw [structureSheafMap_id]
  exact TopCat.Sheaf.eqToHom_hom_comp_whiskerRight_of_eq_id hid _ _

variable {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsAdicRing C] (ψ : C →+* B) (hψ : Continuous ψ)

/-- Composition of continuous homomorphisms induces composition in the opposite order. -/
@[reassoc]
theorem map_comp : map (φ.comp ψ) (hφ.comp hψ) = map φ hφ ≫ map ψ hψ := by
  have hfg : TopCat.ofHom (comap (φ.comp ψ) (hφ.comp hψ)) =
      TopCat.ofHom (comap φ hφ) ≫ TopCat.ofHom (comap ψ hψ) := by
    rw [comap_comp, TopCat.ofHom_comp]
  apply LocallyRingedSpace.Hom.ext'
  rw [LocallyRingedSpace.comp_toHom, map_toHom, map_toHom, map_toHom]
  refine PresheafedSpace.Hom.ext _ _ hfg ?_
  have h := congrArg InducedCategory.Hom.hom (structureSheafMap_comp φ hφ ψ hψ
    (IsAdicRing.ideal_spec C).2.1 (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec A).2.1).symm
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    TopCat.Sheaf.pushforward_map, TopCat.Sheaf.eqToHom_hom_eq_whiskerRight_of_eq_comp hfg _ _] at h
  exact h

section Correspondence

/-- The ring homomorphism `B →+* A` induced on global sections by a morphism of locally ringed
spaces `f : Spf A ⟶ Spf B`, read through `globalSectionsIso` (EGA I, Ch. I, 10.2.2). -/
noncomputable def sectionsRingHom (f : Spf A ⟶ Spf B) : B →+* A :=
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  ((globalSectionsIso (IsAdicRing.ideal_spec B).2.1).inv ≫
    f.c.app (op ⊤) ≫
    (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom).hom

/-- `sectionsRingHom f` intertwines the global-section identifications with `f.c.app (op ⊤)`. -/
@[reassoc]
theorem globalSectionsIso_inv_comp_c_app_top (f : Spf A ⟶ Spf B) :
    have := (IsAdicRing.ideal_spec A).2.2
    have := (IsAdicRing.ideal_spec B).2.2
    (globalSectionsIso (IsAdicRing.ideal_spec B).2.1).inv ≫ f.c.app (op ⊤) =
      CommRingCat.ofHom (sectionsRingHom f) ≫
        (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv := by
  intro _ _
  exact ((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).eq_comp_inv).mpr (Category.assoc _ _ _)

/-- The ring homomorphism induced on global sections by `Spf.map φ hφ` is `φ`. -/
@[simp]
theorem sectionsRingHom_map : sectionsRingHom (map φ hφ) = φ := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  exact congrArg CommRingCat.Hom.hom
    (((globalSectionsIso (IsAdicRing.ideal_spec B).2.1).inv_comp_eq).mpr (map_globalSections φ hφ))

/-- For any morphism `f : Spf A ⟶ Spf B`, an element `b ∈ B` lies in the open prime `f p` if and
only if `sectionsRingHom f b` lies in `p` (EGA I, Ch. I, 10.2.2). -/
theorem mem_asIdeal_base_iff (f : Spf A ⟶ Spf B) (p : carrier A) (b : B) :
    b ∈ (f.base p : carrier B).1.asIdeal ↔
      sectionsRingHom f b ∈ (p : PrimeSpectrum A).asIdeal := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  have h : f.c.app (op ⊤) ((globalSectionsIso (IsAdicRing.ideal_spec B).2.1).inv b) =
      (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv (sectionsRingHom f b) :=
    ConcreteCategory.congr_hom (globalSectionsIso_inv_comp_c_app_top f) b
  exact (Γevaluation_c_app_top_eq_zero_iff f p b).symm.trans
    ((congrArg (fun s ↦ (Spf A).Γevaluation p s = 0) h).to_iff.trans
      (Γevaluation_globalSectionsIso_inv_eq_zero_iff p (sectionsRingHom f b)))

/-- **Automatic continuity on formal spectra** (EGA I, Ch. I, 10.2.2): the ring homomorphism
`B →+* A` induced on global sections by any morphism of locally ringed spaces `Spf A ⟶ Spf B` is
continuous. -/
theorem continuous_sectionsRingHom (f : Spf A ⟶ Spf B) : Continuous (sectionsRingHom f) := by
  refine IsAdic.continuous_of_map_le_radical (IsAdicRing.ideal_spec B).2.1
    (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec B).1 ?_
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, ← basicOpen_eq_bot_iff (IsAdicRing.ideal_spec A).2.1, eq_bot_iff]
  intro p hp
  exact (mem_basicOpen.mp hp) ((mem_asIdeal_base_iff f p b).mp
    (((mem_carrier_iff_le (IsAdicRing.ideal_spec B).2.1).mp (f.base p : carrier B).2) hb))

/-- On underlying topological spaces, every morphism `f : Spf A ⟶ Spf B` pulls back open primes
along `sectionsRingHom f`. -/
theorem base_eq_comap_sectionsRingHom (f : Spf A ⟶ Spf B) :
    f.base = TopCat.ofHom (comap (sectionsRingHom f) (continuous_sectionsRingHom f)) := by
  apply ConcreteCategory.hom_ext
  intro (p : carrier A)
  apply Subtype.ext
  refine (?_ : (f.base p : carrier B).1 = PrimeSpectrum.comap (sectionsRingHom f) p).trans
    (coe_comap_apply (sectionsRingHom f) (continuous_sectionsRingHom f) p).symm
  ext b
  exact mem_asIdeal_base_iff f p b

/-- On `D(b)`, the section map of `f : Spf A ⟶ Spf B` restricts on algebraic elements from `B` to
`algebraMap A (CompletedAway A (θ b)) ∘ θ`. -/
private theorem c_app_basicOpen_comp_algebraMap (f : Spf A ⟶ Spf B) {θ : B →+* A}
    (hθ : sectionsRingHom f = θ) (b : B)
    (hb : (Opens.map f.base).obj (basicOpen b) = basicOpen (θ b)) :
    ((basicOpenSectionsIso (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec B).1 b).inv ≫
        f.c.app (op (basicOpen b)) ≫
        (Spf A).presheaf.map (eqToHom (congrArg op hb)) ≫
        (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1
          (θ b)).hom).hom.comp (algebraMap B (AdicRing.CompletedAway B b)) =
      (algebraMap A (AdicRing.CompletedAway A (θ b))).comp θ := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  let eB_top := globalSectionsIso (IsAdicRing.ideal_spec B).2.1
  let eB_b := basicOpenSectionsIso (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec B).1 b
  let eA_top := globalSectionsIso (IsAdicRing.ideal_spec A).2.1
  let eA_b := basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 (θ b)
  let rA := (Spf A).presheaf.map (eqToHom (congrArg op hb))
  ext x
  have h0 : eB_b.hom ((Spf B).presheaf.map (homOfLE (le_top : basicOpen b ≤ ⊤)).op
        (eB_top.inv x)) = algebraMap B (AdicRing.CompletedAway B b) x :=
    ConcreteCategory.congr_hom (globalSectionsIso_inv_comp_basicOpenSectionsIso_hom
      (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec B).1 b) x
  have h1 : eB_b.inv (algebraMap B (AdicRing.CompletedAway B b) x) =
      (Spf B).presheaf.map (homOfLE (le_top : basicOpen b ≤ ⊤)).op (eB_top.inv x) :=
    (congrArg eB_b.inv h0.symm).trans (ConcreteCategory.congr_hom eB_b.hom_inv_id _)
  have h2 : f.c.app (op (basicOpen b))
        ((Spf B).presheaf.map (homOfLE (le_top : basicOpen b ≤ ⊤)).op (eB_top.inv x)) =
      (Spf A).presheaf.map ((Opens.map f.base).map (homOfLE (le_top : basicOpen b ≤ ⊤))).op
        (f.c.app (op ⊤) (eB_top.inv x)) :=
    ConcreteCategory.congr_hom (f.c.naturality (homOfLE (le_top : basicOpen b ≤ ⊤)).op)
      (eB_top.inv x)
  have h3 : f.c.app (op ⊤) (eB_top.inv x) = eA_top.inv (θ x) :=
    hθ ▸ ConcreteCategory.congr_hom (globalSectionsIso_inv_comp_c_app_top f) x
  have hmap : (Spf A).presheaf.map
        ((Opens.map f.base).map (homOfLE (le_top : basicOpen b ≤ ⊤))).op ≫ rA =
      (Spf A).presheaf.map (homOfLE (le_top : basicOpen (θ b) ≤ ⊤)).op :=
    ((Spf A).presheaf.map_comp _ _).symm.trans
      (congrArg (Spf A).presheaf.map (Subsingleton.elim _ _))
  have h4 : rA ((Spf A).presheaf.map
        ((Opens.map f.base).map (homOfLE (le_top : basicOpen b ≤ ⊤))).op (eA_top.inv (θ x))) =
      (Spf A).presheaf.map (homOfLE (le_top : basicOpen (θ b) ≤ ⊤)).op (eA_top.inv (θ x)) :=
    ConcreteCategory.congr_hom hmap (eA_top.inv (θ x))
  have h5 : eA_b.hom ((Spf A).presheaf.map (homOfLE (le_top : basicOpen (θ b) ≤ ⊤)).op
        (eA_top.inv (θ x))) = algebraMap A (AdicRing.CompletedAway A (θ b)) (θ x) :=
    ConcreteCategory.congr_hom (globalSectionsIso_inv_comp_basicOpenSectionsIso_hom
      (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 (θ b)) (θ x)
  change eA_b.hom (rA (f.c.app (op (basicOpen b))
    (eB_b.inv (algebraMap B (AdicRing.CompletedAway B b) x)))) =
    algebraMap A (AdicRing.CompletedAway A (θ b)) (θ x)
  exact (congrArg (fun z ↦ eA_b.hom (rA (f.c.app (op (basicOpen b)) z))) h1).trans
    ((congrArg (fun z ↦ eA_b.hom (rA z)) h2).trans
      ((congrArg (fun z ↦ eA_b.hom (rA ((Spf A).presheaf.map _ z))) h3).trans
        ((congrArg eA_b.hom h4).trans h5)))

/-- On every basic open `D(b)`, the section map of `f : Spf A ⟶ Spf B` is uniquely determined as
the continuous extension of `sectionsRingHom f` to `CompletedAway B b`. -/
private theorem c_app_basicOpen_eq_of_sectionsRingHom_eq (f : Spf A ⟶ Spf B) {θ : B →+* A}
    (hθ : sectionsRingHom f = θ) (hθc : Continuous θ) (b : B)
    (hb : (Opens.map f.base).obj (basicOpen b) = basicOpen (θ b)) :
    (basicOpenSectionsIso (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec B).1 b).inv ≫
        f.c.app (op (basicOpen b)) ≫
        (Spf A).presheaf.map (eqToHom (congrArg op hb)) ≫
        (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1
          (θ b)).hom =
      CommRingCat.ofHom (AdicRing.CompletedAway.lift
        ((algebraMap A (AdicRing.CompletedAway A (θ b))).comp θ)
        ((AdicRing.CompletedAway.continuous_algebraMap A (θ b)).comp hθc)
        (by simpa using AdicRing.CompletedAway.isUnit_algebraMap_self A (θ b))) := by
  let eB_b := basicOpenSectionsIso (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec B).1 b
  let eA_b := basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 (θ b)
  let rA := (Spf A).presheaf.map (eqToHom (congrArg op hb))
  let lhs := eB_b.inv ≫ f.c.app (op (basicOpen b)) ≫ rA ≫ eA_b.hom
  have hB := c_app_basicOpen_comp_algebraMap f hθ b hb
  have hcont : Continuous lhs.hom := by
    refine IsAdic.continuous_of_map_le_radical (AdicRing.CompletedAway.isAdic B b)
      (AdicRing.CompletedAway.isAdic A (θ b)) ((IsAdicRing.ideal_spec B).1.map _) ?_
    rw [Ideal.map_map, hB, ← Ideal.map_map]
    exact (Ideal.map_mono ((IsAdicRing.ideal_spec B).2.1.map_le_radical_of_continuous
      (IsAdicRing.ideal_spec A).2.1 hθc)).trans (Ideal.map_radical_le _)
  apply CommRingCat.hom_ext
  rw [CommRingCat.hom_ofHom]
  exact AdicRing.CompletedAway.ringHom_ext B b hcont
    (AdicRing.CompletedAway.continuous_lift _ _ _)
    (hB.trans (AdicRing.CompletedAway.lift_comp_algebraMap _ _ _).symm)

/-- A morphism `Spf A ⟶ Spf B` is uniquely determined by the ring homomorphism it induces on global
sections (EGA I, Ch. I, 10.2.2). -/
theorem sectionsRingHom_injective : Function.Injective (sectionsRingHom (A := A) (B := B)) := by
  intro f₁ f₂ hφ
  let θ := sectionsRingHom f₂
  have hθc : Continuous θ := continuous_sectionsRingHom f₂
  have hbase : f₁.toHom.base = f₂.toHom.base := by
    rw [base_eq_comap_sectionsRingHom f₁, base_eq_comap_sectionsRingHom f₂]
    congr 1
    ext p : 1
    apply Subtype.ext
    apply PrimeSpectrum.ext
    ext b
    simp [hφ]
  have hw : (Opens.map f₁.toHom.base).op = (Opens.map f₂.toHom.base).op := by rw [hbase]
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ hbase ?_
  refine TopCat.Sheaf.hom_ext (Spf B).presheaf
    ((TopCat.Sheaf.pushforward CommRingCat f₂.base).obj (Spf A).sheaf)
    isBasis_basicOpen fun b ↦ ?_
  have hb₂ : (Opens.map f₂.base).obj (basicOpen b) = basicOpen (θ b) := by
    rw [base_eq_comap_sectionsRingHom f₂]
    exact comap_basicOpen θ hθc b
  have hb₁ : (Opens.map f₁.base).obj (basicOpen b) = basicOpen (θ b) := by
    rw [hbase]
    exact hb₂
  let eB_b := basicOpenSectionsIso (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec B).1 b
  let eA_b := basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 (θ b)
  let r₁ := (Spf A).presheaf.map (eqToHom (congrArg op hb₁))
  let r₂ := (Spf A).presheaf.map (eqToHom (congrArg op hb₂))
  have hwhisk : (Functor.whiskerRight (eqToHom hw) (Spf A).presheaf).app (op (basicOpen b)) ≫ r₂ =
      r₁ :=
    ((Spf A).presheaf.map_comp _ _).symm.trans
      (congrArg (Spf A).presheaf.map (Subsingleton.elim _ _))
  have hc₁ := c_app_basicOpen_eq_of_sectionsRingHom_eq f₁ hφ hθc b hb₁
  have hc₂ := c_app_basicOpen_eq_of_sectionsRingHom_eq f₂ rfl hθc b hb₂
  have hlhs : (f₁.toHom.c ≫ Functor.whiskerRight (eqToHom hw) (Spf A).presheaf).app
      (op (basicOpen b)) ≫ r₂ = f₁.c.app (op (basicOpen b)) ≫ r₁ :=
    (Category.assoc (f₁.c.app (op (basicOpen b))) _ r₂).trans
      (congrArg (f₁.c.app (op (basicOpen b)) ≫ ·) hwhisk)
  apply (cancel_mono r₂).mp
  apply (cancel_mono eA_b.hom).mp
  apply (cancel_epi eB_b.inv).mp
  exact (congrArg (fun g ↦ eB_b.inv ≫ (g ≫ eA_b.hom)) hlhs).trans
    ((congrArg (eB_b.inv ≫ ·) (Category.assoc _ _ _)).trans
      (hc₁.trans (hc₂.symm.trans (congrArg (eB_b.inv ≫ ·) (Category.assoc _ _ _).symm))))

/-- Every morphism of locally ringed spaces `f : Spf A ⟶ Spf B` is `Spf.map` of its global-section
ring homomorphism (EGA I, Ch. I, 10.2.2). -/
@[simp]
theorem map_sectionsRingHom (f : Spf A ⟶ Spf B) :
    map (sectionsRingHom f) (continuous_sectionsRingHom f) = f :=
  sectionsRingHom_injective (sectionsRingHom_map _ _)

/-- The identity morphism of `Spf A` induces the identity ring homomorphism on `A`. -/
@[simp]
theorem sectionsRingHom_id : sectionsRingHom (𝟙 (Spf A)) = RingHom.id A := by
  rw [← map_id (A := A), sectionsRingHom_map]

/-- Composition of morphisms of formal spectra induces composition of ring homomorphisms in the
opposite order. -/
@[simp]
theorem sectionsRingHom_comp (f : Spf A ⟶ Spf B) (g : Spf B ⟶ Spf C) :
    sectionsRingHom (f ≫ g) = (sectionsRingHom f).comp (sectionsRingHom g) := by
  conv_lhs => rw [← map_sectionsRingHom f, ← map_sectionsRingHom g, ← map_comp]
  exact sectionsRingHom_map _ _

/-- **Full faithfulness of `Spf`** (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY): morphisms of locally
ringed spaces `Spf A ⟶ Spf B` between formal spectra of adic rings of finite ideal type correspond
bijectively to continuous ring homomorphisms `B →+* A`. -/
noncomputable def homEquiv : (Spf A ⟶ Spf B) ≃ { φ : B →+* A // Continuous φ } where
  toFun f := ⟨sectionsRingHom f, continuous_sectionsRingHom f⟩
  invFun φ := map φ.1 φ.2
  left_inv := map_sectionsRingHom
  right_inv φ := Subtype.ext (sectionsRingHom_map φ.1 φ.2)

/-- Applying `homEquiv` to `f` yields `sectionsRingHom f` as the underlying ring homomorphism. -/
@[simp]
theorem homEquiv_apply_coe (f : Spf A ⟶ Spf B) : (homEquiv f : B →+* A) = sectionsRingHom f :=
  (rfl)

/-- The inverse of `homEquiv` is `Spf.map`. -/
@[simp]
theorem homEquiv_symm_apply (φ : { φ : B →+* A // Continuous φ }) :
    homEquiv.symm φ = map φ.1 φ.2 :=
  (rfl)

/-- **Ideal-power criterion for morphisms of formal spectra** (EGA I, Ch. I, 10.2.2; EGA 0,
7.1.3–7.1.4): for any ideals of definition `K` of `B` and `L` of `A` (neither assumed finitely
generated), a ring homomorphism `θ : B →+* A` arises on global sections from a morphism
`Spf A ⟶ Spf B` if and only if `θ` is continuous, if and only if `K.map θ ≤ L.radical`, and if and
only if `(K ^ k).map θ ≤ L` for some positive integer `k`. -/
theorem homEquiv_pow (hK : IsAdic K) (hL : IsAdic L) (θ : B →+* A) :
    ((∃ f : Spf A ⟶ Spf B, sectionsRingHom f = θ) ↔ Continuous θ) ∧
      (Continuous θ ↔ K.map θ ≤ L.radical) ∧
      (K.map θ ≤ L.radical ↔ ∃ k > 0, (K ^ k).map θ ≤ L) := by
  have hB := (IsAdicRing.ideal_spec B).2.1
  have hBfg := (IsAdicRing.ideal_spec B).1
  refine ⟨⟨?_, fun hθ ↦ ⟨map θ hθ, sectionsRingHom_map θ hθ⟩⟩,
    hK.continuous_iff_map_le_radical hL hB hBfg,
    (hK.continuous_iff_map_le_radical hL hB hBfg).symm.trans
      (hK.continuous_iff_exists_pow_map_le hL hB hBfg)⟩
  rintro ⟨f, rfl⟩
  exact continuous_sectionsRingHom f

end Correspondence

end TauCeti.FormalScheme.Spf
