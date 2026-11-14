/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Prod
public import TauCeti.Topology.Homotopy.Proper
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Topology.Maps.Proper.Basic

/-!
# The proper homotopy extension property and proper strong deformation retractions

A subset `A` of a topological space `X` has the *proper homotopy extension property*
(`TauCeti.HasProperHomotopyExtensionProperty`) when every jointly proper homotopy `H : I × A → Y`
whose initial map extends to a proper map `f : X → Y` extends to a jointly proper homotopy
`K : I × X → Y`. Unlike the ordinary homotopy extension property, properness is required jointly on
the whole cylinder `I × X`, not slice by slice.

For a closed subset `A ⊆ X`, this property has a geometric characterization matching the ordinary
one (`TauCeti.hasProperHomotopyExtensionProperty_iff_exists_proper_retraction`): `A` has the proper
homotopy extension property if and only if the bottom-and-sides subspace `{0} × X ∪ I × A`
(`TauCeti.cylinderExtensionDomain A`) is a *proper* retract of the cylinder `I × X`. No separation
or local-compactness hypothesis on `X` or `Y` is needed. Passing through this proper cylinder
retraction frees the property from the universe of the target space
(`TauCeti.HasProperHomotopyExtensionProperty.exists_extension_of_isClosed`), shows that closed
subsets with the proper homotopy extension property also have the ordinary homotopy extension
property (`TauCeti.HasProperHomotopyExtensionProperty.hasHomotopyExtensionProperty`), and identifies
the two notions on compact Hausdorff ambient spaces
(`TauCeti.hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty`).

Passing to NDR data (`TauCeti.NDRPair`) preserves properness of the ambient deformation: Strøm's
construction `TauCeti.NDRPair.ofRetraction` from a proper cylinder retraction has a proper
deformation, and both the cylinder deformation and the product of two NDR pairs preserve properness
(`TauCeti.NDRPair.isProperMap_cylinderDeformation`,
`TauCeti.NDRPair.isProperMap_prod_deformation`). This yields Strøm's product theorem for closed
proper cofibrations (`TauCeti.HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod`) and in
particular the proper homotopy extension property of the cylinder-boundary pair
`({0, 1} × X) ∪ (I × A) ⊆ I × X`
(`TauCeti.HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod`).

Applying proper extension on the cylinder-boundary pair makes any jointly proper homotopy followed
by a jointly proper homotopy that retraces it on `A` stationary on `A` while retaining joint
properness (`TauCeti.HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retracing`).
Consequently, if `A ⊆ X` has the proper homotopy extension property and its inclusion `A → X` is a
proper homotopy equivalence (`ContinuousMap.HasProperHomotopyInverse`), then `A` is a *proper
strong deformation retract* of `X`: the proper homotopy inverse rectifies to a proper retraction
`r : X → A` fixing `A` together with a jointly proper homotopy from `id_X` to `incl ∘ r` relative
to `A` (`TauCeti.properStrongDeformationRetract_of_inverse`,
`TauCeti.HasProperHomotopyExtensionProperty.exists_proper_strong_deformation_retraction_iff`).

## Main declarations

* `TauCeti.HasProperHomotopyExtensionProperty`: the proper homotopy extension property of `A ⊆ X`.
* `TauCeti.hasProperHomotopyExtensionProperty_iff_exists_proper_retraction`: **a closed subset has
  the proper homotopy extension property iff `{0} × X ∪ I × A` is a proper retract of `I × X`.**
* `TauCeti.hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty`: on a compact
  Hausdorff space, the proper and ordinary homotopy extension properties coincide for closed
  subsets.
* `TauCeti.hasProperHomotopyExtensionProperty_singleton_zero` and
  `TauCeti.not_hasProperHomotopyExtensionProperty_harmonicSeqSet`: `{0} ⊆ I` has the proper homotopy
  extension property, whereas the closed harmonic subspace `{0} ∪ {1 / (n + 1) | n : ℕ} ⊆ I` fails
  both the ordinary and proper properties.
* `TauCeti.HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod` and
  `TauCeti.HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod`: **Strøm's
  product theorem** and the **cylinder-boundary pair** for closed proper cofibrations.
* `TauCeti.HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retracing`: jointly
  proper retracing homotopies rectify to jointly proper homotopies stationary on `A`.
* `TauCeti.properStrongDeformationRetract_of_inverse` and
  `TauCeti.HasProperHomotopyExtensionProperty.exists_proper_strong_deformation_retraction_iff`:
  **a proper cofibration whose inclusion has a proper homotopy inverse is a proper strong
  deformation retract.**

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, §1 (proper homotopy extension and proper mapping-cylinder
  deformations).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, p. 14 (harmonic-sequence counterexample) and Proposition 0.19 (strong deformation
  retractions from homotopy equivalences).
* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142 (NDR pairs and products of
  closed cofibrations).
* Formal structure adapted from `TauCeti.Topology.Homotopy.Extension.Basic`,
  `TauCeti.Topology.Homotopy.Extension.NDRPair`, `TauCeti.Topology.Homotopy.Extension.Prod`, and
  `TauCeti.Topology.Homotopy.Extension.DeformationRetract`.
-/

public section

namespace TauCeti

open ContinuousMap Filter Metric Set Topology unitInterval

universe u u' v

section Basic

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- A subset `A` of `X` has the **proper homotopy extension property** when every jointly proper
homotopy `H : I × A → Y` whose initial slice agrees on `A` with a proper map `f : X → Y` extends to
a jointly proper homotopy `K : I × X → Y` starting at `f`.

Targets `Y` in the universe of `X` are quantified over in the definition; for closed `A`,
`TauCeti.HasProperHomotopyExtensionProperty.exists_extension_of_isClosed` extends proper homotopies
with values in any universe. -/
def HasProperHomotopyExtensionProperty {X : Type u} [TopologicalSpace X]
    (A : Set X) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y],
    ∀ (f : C(X, Y)), IsProperMap f →
    ∀ (H : C(unitInterval × A, Y)), IsProperMap H →
      (∀ a : A, H (0, a) = f (a : X)) →
      ∃ K : C(unitInterval × X, Y), IsProperMap K ∧
        (∀ x : X, K (0, x) = f x) ∧
        (∀ (t : unitInterval) (a : A), K (t, (a : X)) = H (t, a))

/-- Unfolding of `TauCeti.HasProperHomotopyExtensionProperty`. -/
theorem hasProperHomotopyExtensionProperty_iff :
    HasProperHomotopyExtensionProperty A ↔
      ∀ (Y : Type u) [TopologicalSpace Y] (f : C(X, Y)), IsProperMap f →
        ∀ (H : C(I × A, Y)), IsProperMap H → (∀ a : A, H (0, a) = f (a : X)) →
          ∃ K : C(I × X, Y), IsProperMap K ∧
            (∀ x : X, K (0, x) = f x) ∧ ∀ (t : I) (a : A), K (t, (a : X)) = H (t, a) :=
  (Iff.rfl)

/-- The defining extension property of `TauCeti.HasProperHomotopyExtensionProperty`. -/
theorem HasProperHomotopyExtensionProperty.exists_extension
    (h : HasProperHomotopyExtensionProperty A) {Y : Type u} [TopologicalSpace Y]
    {f : C(X, Y)} (hf : IsProperMap f) {H : C(I × A, Y)} (hH : IsProperMap H)
    (hH₀ : ∀ a : A, H (0, a) = f (a : X)) :
    ∃ K : C(I × X, Y), IsProperMap K ∧
      (∀ x : X, K (0, x) = f x) ∧ ∀ (t : I) (a : A), K (t, (a : X)) = H (t, a) :=
  h Y f hf H hH hH₀

/-- The empty subset has the proper homotopy extension property: the constant homotopy
`f ∘ Prod.snd` is proper because `I` is compact. -/
theorem hasProperHomotopyExtensionProperty_empty :
    HasProperHomotopyExtensionProperty (∅ : Set X) :=
  fun _ _ f hf _ _ _ ↦
    ⟨f.comp ContinuousMap.snd, hf.comp isProperMap_snd_of_compactSpace,
      fun _ ↦ rfl, fun _ a ↦ a.2.elim⟩

/-- The whole space `univ` has the proper homotopy extension property: `I × X` and `I × univ` are
homeomorphic. -/
theorem hasProperHomotopyExtensionProperty_univ :
    HasProperHomotopyExtensionProperty (univ : Set X) := by
  intro Y _ f _ H hH hH₀
  let e : I × X ≃ₜ I × (univ : Set X) :=
    (Homeomorph.refl I).prodCongr (Homeomorph.Set.univ X).symm
  refine ⟨H.comp (e : C(I × X, I × (univ : Set X))), hH.comp e.isProperMap, fun x ↦ ?_,
    fun t a ↦ ?_⟩
  · exact hH₀ ⟨x, trivial⟩
  · exact congrArg H (Prod.ext rfl (Subtype.ext rfl))

/-- **A proper retraction of `I × X` onto `{0} × X ∪ I × A` solves every proper homotopy extension
problem** for a closed subset `A ⊆ X`, with values in a space in any universe. -/
theorem exists_proper_homotopy_extension_of_retraction {Y : Type v} [TopologicalSpace Y]
    (hA : IsClosed A) {r : C(I × X, I × X)} (hr_prop : IsProperMap r)
    (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p)
    {f : C(X, Y)} (hf : IsProperMap f) {H : C(I × A, Y)} (hH : IsProperMap H)
    (hH₀ : ∀ a : A, H (0, a) = f (a : X)) :
    ∃ K : C(I × X, Y), IsProperMap K ∧
      (∀ x : X, K (0, x) = f x) ∧ ∀ (t : I) (a : A), K (t, (a : X)) = H (t, a) := by
  classical
  -- Glue `f` and `H` on `{0} × X ∪ I × A`, which is covered by its two closed pieces `{t = 0}`
  -- (homeomorphic to `X`) and `{x ∈ A}` (homeomorphic to `I × A`).
  let J := cylinderExtensionDomain A
  let Φ : J → Y := fun q ↦ if h : q.1.2 ∈ A then H (q.1.1, ⟨q.1.2, h⟩) else f q.1.2
  let S₀ : Set J := {q | q.1.1 = 0}
  let S₁ : Set J := {q | q.1.2 ∈ A}
  have hS₀ : IsClosed S₀ :=
    (isClosed_singleton (x := (0 : I))).preimage (continuous_fst.comp continuous_subtype_val)
  have hS₁ : IsClosed S₁ := hA.preimage (continuous_snd.comp continuous_subtype_val)
  have hcover : S₀ ∪ S₁ = univ := eq_univ_of_forall fun q ↦ mem_cylinderExtensionDomain_iff.1 q.2
  have hΦ : IsProperMap Φ := by
    refine IsProperMap.of_domRestrict_of_isClosed_union hS₀ hS₁ hcover ?_ ?_
    · let e₀ : S₀ ≃ₜ X :=
        { toFun := fun q ↦ q.1.1.2
          invFun := fun x ↦ ⟨⟨(0, x), zero_mem_cylinderExtensionDomain x⟩, rfl⟩
          left_inv := fun q ↦ Subtype.ext (Subtype.ext (Prod.ext q.2.symm rfl))
          right_inv := fun _ ↦ rfl }
      have heq : S₀.domRestrict Φ = f ∘ e₀ := funext fun q ↦ by
        dsimp only [domRestrict_apply, Φ, Function.comp_apply, e₀]
        split_ifs with h
        · exact (congrArg (fun t ↦ H (t, ⟨q.1.1.2, h⟩)) q.2).trans (hH₀ ⟨q.1.1.2, h⟩)
        · rfl
      rw [heq]
      exact hf.comp e₀.isProperMap
    · let e₁ : S₁ ≃ₜ I × A :=
        { toFun := fun q ↦ (q.1.1.1, ⟨q.1.1.2, q.2⟩)
          invFun := fun p ↦ ⟨⟨(p.1, p.2), mem_cylinderExtensionDomain_of_mem p.2.2⟩, p.2.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      have heq : S₁.domRestrict Φ = H ∘ e₁ := funext fun q ↦ by
        have hq : q.1.1.2 ∈ A := q.2
        simp only [domRestrict_apply, Φ, hq, ↓reduceDIte, Function.comp_apply]
        rfl
      rw [heq]
      exact hH.comp e₁.isProperMap
  let R : C(I × X, J) := ⟨fun p ↦ ⟨r p, hr p⟩, r.continuous.subtype_mk hr⟩
  have hR : IsProperMap R :=
    isProperMap_of_comp_of_inj R.continuous continuous_subtype_val hr_prop Subtype.val_injective
  refine ⟨⟨Φ ∘ R, hΦ.continuous.comp R.continuous⟩, hΦ.comp hR, fun x ↦ ?_, fun t a ↦ ?_⟩
  · have h0 : R (0, x) = ⟨(0, x), zero_mem_cylinderExtensionDomain x⟩ :=
      Subtype.ext (hr' _ (zero_mem_cylinderExtensionDomain x))
    simp only [ContinuousMap.coe_mk, Function.comp_apply, h0, Φ]
    split_ifs with h
    · exact hH₀ ⟨x, h⟩
    · rfl
  · have ha : R (t, a) = ⟨(t, a), mem_cylinderExtensionDomain_of_mem a.2⟩ :=
      Subtype.ext (hr' _ (mem_cylinderExtensionDomain_of_mem a.2))
    simp only [ContinuousMap.coe_mk, Function.comp_apply, ha, Φ, a.2, ↓reduceDIte]

/-- A closed subset whose cylinder extension domain is a proper retract of `I × X` has the proper
homotopy extension property. -/
theorem hasProperHomotopyExtensionProperty_of_proper_retraction (hA : IsClosed A)
    {r : C(I × X, I × X)} (hr_prop : IsProperMap r)
    (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p) :
    HasProperHomotopyExtensionProperty A :=
  fun _ _ _ hf _ hH hH₀ ↦
    exists_proper_homotopy_extension_of_retraction hA hr_prop hr hr' hf hH hH₀

/-- A clopen subset has the proper homotopy extension property: collapsing the cylinder over `Aᶜ`
to height `0` while fixing the cylinder over `A` is proper on both pieces of the clopen partition
`I × A` and `I × Aᶜ`. -/
theorem _root_.IsClopen.hasProperHomotopyExtensionProperty (hA : IsClopen A) :
    HasProperHomotopyExtensionProperty A := by
  classical
  have hfr : frontier {p : I × X | p.2 ∈ A} = ∅ :=
    (hA.preimage (f := (Prod.snd : I × X → X)) continuous_snd).frontier_eq
  let r : C(I × X, I × X) :=
    ⟨fun p ↦ if p.2 ∈ A then p else ((0 : I), p.2),
      Continuous.if (by simp [hfr]) continuous_id (by fun_prop)⟩
  have hr_prop : IsProperMap r := by
    let S : Set (I × X) := Prod.snd ⁻¹' A
    let T : Set (I × X) := Prod.snd ⁻¹' Aᶜ
    have hST : S ∪ T = univ := by rw [← preimage_union, union_compl_self, preimage_univ]
    refine IsProperMap.of_domRestrict_of_isClosed_union
      (hA.isClosed.preimage continuous_snd) (hA.compl.isClosed.preimage continuous_snd) hST ?_ ?_
    · have heq : S.domRestrict r = Subtype.val := funext fun p ↦ by
        have hp : p.1.2 ∈ A := p.2
        simp only [domRestrict_apply, r, ContinuousMap.coe_mk, hp, ↓reduceIte]
      rw [heq]
      exact (hA.isClosed.preimage continuous_snd).isProperMap_subtypeVal
    · have heq : T.domRestrict r =
          (fun x : X ↦ ((0 : I), x)) ∘ Prod.snd ∘ (Subtype.val : T → I × X) := funext fun p ↦ by
        have hp : p.1.2 ∉ A := p.2
        simp only [domRestrict_apply, r, ContinuousMap.coe_mk, hp, ↓reduceIte, Function.comp_apply]
      rw [heq]
      exact (isProperMap_prodMk_left (0 : I)).comp
        (isProperMap_snd_of_compactSpace.comp
          (hA.compl.isClosed.preimage continuous_snd).isProperMap_subtypeVal)
  refine hasProperHomotopyExtensionProperty_of_proper_retraction hA.isClosed hr_prop
    (fun p ↦ ?_) (fun p hp ↦ ?_)
  · by_cases h : p.2 ∈ A <;> simp [r, h, mem_cylinderExtensionDomain_iff]
  · obtain ⟨t, x⟩ := p
    rcases mem_cylinderExtensionDomain_iff.1 hp with rfl | hx
    · by_cases h : x ∈ A <;> simp [r, h]
    · simp [r, hx]

/-- Solving the universal proper homotopy extension problem with target
`{0} × X ∪ I × A` produces a proper retraction of `I × X` onto `{0} × X ∪ I × A` whenever `A` is
closed. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_retraction
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    ∃ r : C(I × X, I × X), IsProperMap r ∧ (∀ p, r p ∈ cylinderExtensionDomain A) ∧
      ∀ p ∈ cylinderExtensionDomain A, r p = p := by
  let f₀ : C(X, cylinderExtensionDomain A) :=
    ⟨fun x ↦ ⟨((0 : I), x), zero_mem_cylinderExtensionDomain x⟩, by fun_prop⟩
  let H₀ : C(I × A, cylinderExtensionDomain A) :=
    ⟨fun q ↦ ⟨(q.1, (q.2 : X)), mem_cylinderExtensionDomain_of_mem q.2.2⟩, by fun_prop⟩
  have hf₀ : IsProperMap f₀ :=
    isProperMap_of_comp_of_inj f₀.continuous continuous_subtype_val
      (isProperMap_prodMk_left (0 : I)) Subtype.val_injective
  have hH₀ : IsProperMap H₀ :=
    isProperMap_of_comp_of_inj H₀.continuous continuous_subtype_val
      (isProperMap_id.prodMap hA.isProperMap_subtypeVal) Subtype.val_injective
  obtain ⟨K, hK, hK₀, hK₁⟩ := h.exists_extension hf₀ hH₀ (fun _ ↦ rfl)
  refine ⟨(subtypeVal _).comp K,
    (isClosed_cylinderExtensionDomain hA).isProperMap_subtypeVal.comp hK,
    fun p ↦ (K p).2, ?_⟩
  rintro ⟨t, x⟩ hp
  rcases mem_cylinderExtensionDomain_iff.1 hp with rfl | hx
  · exact congrArg Subtype.val (hK₀ x)
  · exact congrArg Subtype.val (hK₁ t ⟨x, hx⟩)

/-- **A closed subset has the proper homotopy extension property if and only if `{0} × X ∪ I × A`
is a proper retract of `I × X`.** -/
theorem hasProperHomotopyExtensionProperty_iff_exists_proper_retraction (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty A ↔
      ∃ r : C(I × X, I × X), IsProperMap r ∧ (∀ p, r p ∈ cylinderExtensionDomain A) ∧
        ∀ p ∈ cylinderExtensionDomain A, r p = p :=
  ⟨fun h ↦ h.exists_proper_retraction hA,
    fun ⟨_, hr_prop, hr, hr'⟩ ↦
      hasProperHomotopyExtensionProperty_of_proper_retraction hA hr_prop hr hr'⟩

/-- For a closed subset, the proper homotopy extension property extends proper homotopies with
values in a space in an arbitrary universe. -/
theorem HasProperHomotopyExtensionProperty.exists_extension_of_isClosed (hA : IsClosed A)
    (h : HasProperHomotopyExtensionProperty A) {Y : Type v} [TopologicalSpace Y]
    {f : C(X, Y)} (hf : IsProperMap f) {H : C(I × A, Y)} (hH : IsProperMap H)
    (hH₀ : ∀ a : A, H (0, a) = f (a : X)) :
    ∃ K : C(I × X, Y), IsProperMap K ∧
      (∀ x : X, K (0, x) = f x) ∧ ∀ (t : I) (a : A), K (t, (a : X)) = H (t, a) := by
  obtain ⟨_, hr_prop, hr, hr'⟩ := h.exists_proper_retraction hA
  exact exists_proper_homotopy_extension_of_retraction hA hr_prop hr hr' hf hH hH₀

/-- A closed subset with the proper homotopy extension property also has the ordinary homotopy
extension property, by forgetting properness of the cylinder retraction. -/
theorem HasProperHomotopyExtensionProperty.hasHomotopyExtensionProperty (hA : IsClosed A)
    (h : HasProperHomotopyExtensionProperty A) : HasHomotopyExtensionProperty A := by
  obtain ⟨_, -, hr, hr'⟩ := h.exists_proper_retraction hA
  exact hasHomotopyExtensionProperty_of_retraction hA hr hr'

/-- On a compact Hausdorff ambient space, a closed subset has the proper homotopy extension
property if and only if it has the ordinary homotopy extension property: every continuous
self-map of the compact Hausdorff cylinder `I × X` is proper. -/
theorem hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty
    [CompactSpace X] [T2Space X] (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty A ↔ HasHomotopyExtensionProperty A :=
  ⟨fun h ↦ h.hasHomotopyExtensionProperty hA, fun h ↦ by
    obtain ⟨r, hr, hr'⟩ := h.exists_retraction
    exact hasProperHomotopyExtensionProperty_of_proper_retraction hA r.continuous.isProperMap
      hr hr'⟩

/-- The proper homotopy extension property transports along a homeomorphism inside one universe,
with no closedness assumption on `A`. -/
theorem HasProperHomotopyExtensionProperty.image {X' : Type u} [TopologicalSpace X']
    (h : HasProperHomotopyExtensionProperty A) (e : X ≃ₜ X') :
    HasProperHomotopyExtensionProperty (e '' A) := by
  intro Y _ f hf H hH hH₀
  let eA : I × A ≃ₜ I × (e '' A) := (Homeomorph.refl I).prodCongr (e.image A)
  obtain ⟨K, hK, hK₀, hK₁⟩ := h.exists_extension
    (f := f.comp (e : C(X, X'))) (hf.comp e.isProperMap)
    (H := H.comp (eA : C(I × A, I × (e '' A)))) (hH.comp eA.isProperMap)
    fun a ↦ hH₀ ⟨e a, mem_image_of_mem e a.2⟩
  let eCyl : I × X' ≃ₜ I × X := (Homeomorph.refl I).prodCongr e.symm
  refine ⟨K.comp (eCyl : C(I × X', I × X)), hK.comp eCyl.isProperMap, fun x' ↦ ?_, fun t b ↦ ?_⟩
  · simpa [eCyl] using hK₀ (e.symm x')
  · rcases b with ⟨_, a, ha, rfl⟩
    have hc : eCyl (t, e a) = (t, a) := Prod.ext rfl (e.symm_apply_apply a)
    exact (congrArg K hc).trans (hK₁ t ⟨a, ha⟩)

/-- For a closed subset, the proper homotopy extension property transports along a homeomorphism
across universes. -/
theorem HasProperHomotopyExtensionProperty.image_of_isClosed {X' : Type u'} [TopologicalSpace X']
    (h : HasProperHomotopyExtensionProperty A) (e : X ≃ₜ X') (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty (e '' A) := by
  obtain ⟨r, hr_prop, hr, hr'⟩ := h.exists_proper_retraction hA
  let eCyl : I × X ≃ₜ I × X' := (Homeomorph.refl I).prodCongr e
  let r' : C(I × X', I × X') := (eCyl : C(I × X, I × X')).comp (r.comp eCyl.symm)
  have hr'_prop : IsProperMap r' := eCyl.isProperMap.comp (hr_prop.comp eCyl.symm.isProperMap)
  refine hasProperHomotopyExtensionProperty_of_proper_retraction (e.isClosedMap A hA) hr'_prop
    (fun q ↦ ?_) (fun q hq ↦ ?_)
  · rcases mem_cylinderExtensionDomain_iff.1 (hr (eCyl.symm q)) with h0 | hmem
    · exact mem_cylinderExtensionDomain_iff.2 (Or.inl h0)
    · exact mem_cylinderExtensionDomain_iff.2 (Or.inr (mem_image_of_mem e hmem))
  · have hq' : eCyl.symm q ∈ cylinderExtensionDomain A := by
      rcases mem_cylinderExtensionDomain_iff.1 hq with h0 | ⟨a, ha, hae⟩
      · exact mem_cylinderExtensionDomain_iff.2 (Or.inl h0)
      · exact mem_cylinderExtensionDomain_iff.2 (Or.inr (by simpa [eCyl, ← hae] using ha))
    simp [r', hr' _ hq']

/-- **Proper cofibrations compose along closed embeddings.** If `j : X → X'` is a closed embedding
whose range has the proper homotopy extension property in `X'`, and `A` has the proper homotopy
extension property in `X`, then `j '' A` has the proper homotopy extension property in `X'`. -/
theorem HasProperHomotopyExtensionProperty.image_of_isClosedEmbedding {X' : Type u}
    [TopologicalSpace X'] (h : HasProperHomotopyExtensionProperty A) {j : X → X'}
    (hj : IsClosedEmbedding j) (hj' : HasProperHomotopyExtensionProperty (range j)) :
    HasProperHomotopyExtensionProperty (j '' A) := by
  intro Y _ f hf H hH hH₀
  let ejA : A ≃ₜ j '' A :=
    { toFun := fun a ↦ ⟨j a, mem_image_of_mem j a.2⟩
      invFun := fun b ↦ ⟨hj.isEmbedding.toHomeomorph.symm ⟨b.1, image_subset_range j A b.2⟩, by
        rcases b with ⟨_, a, ha, rfl⟩
        simpa using ha⟩
      left_inv := fun a ↦ Subtype.ext (hj.isEmbedding.toHomeomorph.symm_apply_apply a)
      right_inv := fun ⟨_, a, _, rfl⟩ ↦ Subtype.ext (by simp) }
  let eId : I × A ≃ₜ I × (j '' A) := (Homeomorph.refl I).prodCongr ejA
  obtain ⟨G, hG, hG₀, hG₁⟩ := h.exists_extension
    (f := f.comp ⟨j, hj.continuous⟩) (hf.comp hj.isProperMap)
    (H := H.comp (eId : C(I × A, I × (j '' A)))) (hH.comp eId.isProperMap)
    fun a ↦ hH₀ ⟨j a, mem_image_of_mem j a.2⟩
  let eRange : I × range j ≃ₜ I × X :=
    (Homeomorph.refl I).prodCongr hj.isEmbedding.toHomeomorph.symm
  obtain ⟨K, hK, hK₀, hK₁⟩ := hj'.exists_extension hf
    (H := G.comp (eRange : C(I × range j, I × X))) (hG.comp eRange.isProperMap)
    fun y ↦ by
      rcases y with ⟨_, x, rfl⟩
      simpa [eRange] using hG₀ x
  refine ⟨K, hK, hK₀, fun t b ↦ ?_⟩
  rcases b with ⟨_, a, ha, rfl⟩
  rw [hK₁ t ⟨j a, mem_range_self a⟩]
  have heR : eRange (t, ⟨j a, mem_range_self a⟩) = (t, a) :=
    Prod.ext rfl (hj.isEmbedding.toHomeomorph.symm_apply_apply a)
  exact (congrArg G heR).trans (hG₁ t ⟨a, ha⟩)

end Basic

section Examples

/-- The singleton `{0}` has the proper homotopy extension property in the unit interval `I`,
witnessed by the explicit proper piecewise-linear retraction
`(t, x) ↦ (projIcc 0 1 (t - x), projIcc 0 1 (x - t))` of `I × I` onto `{0} × I ∪ I × {0}`. -/
theorem hasProperHomotopyExtensionProperty_singleton_zero :
    HasProperHomotopyExtensionProperty ({0} : Set I) := by
  let r : C(I × I, I × I) :=
    ⟨fun p ↦ (projIcc 0 1 zero_le_one ((p.1 : ℝ) - p.2),
      projIcc 0 1 zero_le_one ((p.2 : ℝ) - p.1)), by fun_prop⟩
  refine hasProperHomotopyExtensionProperty_of_proper_retraction isClosed_singleton
    r.continuous.isProperMap (fun p ↦ ?_) (fun p hp ↦ ?_)
  · rw [mem_cylinderExtensionDomain_iff]
    rcases le_total (p.1 : ℝ) p.2 with h | h
    · exact Or.inl (projIcc_eq_zero.2 (sub_nonpos.2 h))
    · exact Or.inr (mem_singleton_iff.2 (projIcc_eq_zero.2 (sub_nonpos.2 h)))
  · obtain ⟨t, x⟩ := p
    rcases mem_cylinderExtensionDomain_iff.1 hp with rfl | hx
    · refine Prod.ext ?_ ?_
      · exact projIcc_eq_zero.2 (by simp only [Icc.coe_zero, zero_sub]; linarith [x.2.1])
      · simpa only [r, ContinuousMap.coe_mk, Icc.coe_zero, sub_zero] using projIcc_of_mem _ x.2
    · obtain rfl : x = 0 := mem_singleton_iff.1 hx
      refine Prod.ext ?_ ?_
      · simpa only [r, ContinuousMap.coe_mk, Icc.coe_zero, sub_zero] using projIcc_of_mem _ t.2
      · exact projIcc_eq_zero.2 (by simp only [Icc.coe_zero, zero_sub]; linarith [t.2.1])

/-- The endpoints `{0, 1}` have the proper homotopy extension property in `I`. -/
theorem hasProperHomotopyExtensionProperty_zero_one :
    HasProperHomotopyExtensionProperty ({0, 1} : Set I) :=
  (hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty
    (Set.toFinite _).isClosed).2 hasHomotopyExtensionProperty_zero_one

private noncomputable def ballRadialRetraction (E : Type u)
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] :
    C(I × closedBall (0 : E) 1, I × closedBall (0 : E) 1) :=
  ⟨fun p ↦ (⟨(ballRadialProjection p).1, (ballRadialProjection_spec p).1⟩,
      ⟨(ballRadialProjection p).2, (ballRadialProjection_spec p).2.1⟩),
    (continuous_ballRadialProjection.fst.subtype_mk _).prodMk
      (continuous_ballRadialProjection.snd.subtype_mk _)⟩

private theorem isProperMap_ballRadialRetraction {E : Type u}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] :
    IsProperMap (ballRadialRetraction E) := by
  let r := ballRadialRetraction E
  rw [isProperMap_iff_ultrafilter]
  refine ⟨r.continuous, fun 𝒰 ⟨t₀, y₀⟩ hy ↦ ?_⟩
  obtain ⟨t₁, -, ht₁⟩ := isCompact_univ.ultrafilter_le_nhds (𝒰.map fun p ↦ p.1) (by simp)
  have ht₁' : Tendsto (fun p : I × closedBall (0 : E) 1 ↦ p.1) 𝒰 (𝓝 t₁) := by
    rwa [Ultrafilter.coe_map] at ht₁
  let nrm : I × closedBall (0 : E) 1 → I :=
    fun p ↦ ⟨‖(p.2 : E)‖, norm_nonneg _, mem_closedBall_zero_iff.1 p.2.2⟩
  obtain ⟨s₁, -, hs₁⟩ := isCompact_univ.ultrafilter_le_nhds (𝒰.map nrm) (by simp)
  have hs₁' : Tendsto (fun p : I × closedBall (0 : E) 1 ↦ ‖(p.2 : E)‖) 𝒰 (𝓝 (s₁ : ℝ)) :=
    (continuous_subtype_val.tendsto s₁).comp (by rwa [Ultrafilter.coe_map] at hs₁)
  let d₁ : ℝ := max (2 - (t₁ : ℝ)) (2 * s₁)
  have hd₁_pos : 0 < d₁ := lt_of_lt_of_le (by linarith [t₁.2.2]) (le_max_left _ _)
  have hd : Tendsto (ballRadialDen (E := E)) 𝒰 (𝓝 d₁) :=
    ((tendsto_const_nhds.sub ((continuous_subtype_val.tendsto t₁).comp ht₁')).max
      (tendsto_const_nhds.mul hs₁')).congr fun p ↦ (ballRadialDen_def p).symm
  have hy₂ : Tendsto (fun p ↦ ((r p).2 : E)) 𝒰 (𝓝 (y₀ : E)) :=
    ((continuous_subtype_val.comp continuous_snd).tendsto (t₀, y₀)).comp hy
  have hpx : Tendsto (fun p : I × closedBall (0 : E) 1 ↦ (p.2 : E)) 𝒰
      (𝓝 ((d₁ / 2) • (y₀ : E))) := by
    refine ((hd.div_const 2).smul hy₂).congr fun p ↦ ?_
    have hdp : ballRadialDen p ≠ 0 := by
      rw [ballRadialDen_def]
      exact (lt_of_lt_of_le (by linarith [p.1.2.2]) (le_max_left _ _)).ne'
    simp only [r, ballRadialRetraction, ContinuousMap.coe_mk, ballRadialProjection_def, smul_smul]
    rw [div_mul_div_cancel₀ two_ne_zero, div_self hdp, one_smul]
  let x₁ : closedBall (0 : E) 1 :=
    ⟨(d₁ / 2) • (y₀ : E), isClosed_closedBall.mem_of_tendsto hpx (.of_forall fun p ↦ p.2.2)⟩
  have hw : (𝒰 : Filter _) ≤ 𝓝 (t₁, x₁) := ht₁'.prodMk_nhds (tendsto_subtype_rng.2 hpx)
  have hs_eq : (s₁ : ℝ) = ‖(x₁ : E)‖ :=
    tendsto_nhds_unique hs₁' ((continuous_norm.tendsto (x₁ : E)).comp hpx)
  have hd_eq : ballRadialDen (t₁, x₁) = d₁ := by rw [ballRadialDen_def, ← hs_eq]
  have ht_eq : (r (t₁, x₁)).1 = t₀ :=
    tendsto_nhds_unique (((continuous_fst.comp r.continuous).tendsto _).mono_left hw)
      ((continuous_fst.tendsto (t₀, y₀)).comp hy)
  have hy_eq : (r (t₁, x₁)).2 = y₀ := Subtype.ext <| by
    simp only [r, ballRadialRetraction, ContinuousMap.coe_mk, ballRadialProjection_def, hd_eq, x₁,
      smul_smul]
    rw [div_mul_div_cancel₀ hd₁_pos.ne', div_self two_ne_zero, one_smul]
  exact ⟨(t₁, x₁), Prod.ext ht_eq hy_eq, hw⟩

/-- **The unit sphere of a real seminormed space has the proper homotopy extension property inside
the closed unit ball.** No finite-dimensionality (`ProperSpace`) or separation (`T2Space`)
hypothesis is needed: the radial denominator `max (2 - t) (2 ‖x‖)` is bounded below by `1`, so
along any ultrafilter on `I × closedBall 0 1` where the radial projection converges, compactness of
`I` for `(t, ‖x‖)` recovers a limit of `x = (d / 2) • y`. -/
theorem hasProperHomotopyExtensionProperty_sphere_closedBall {E : Type u}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] :
    HasProperHomotopyExtensionProperty
      (Subtype.val ⁻¹' (sphere (0 : E) 1) : Set (closedBall (0 : E) 1)) := by
  refine hasProperHomotopyExtensionProperty_of_proper_retraction
    (isClosed_sphere.preimage continuous_subtype_val) isProperMap_ballRadialRetraction
    (fun p ↦ ?_) (fun p hp ↦ ?_)
  · rw [mem_cylinderExtensionDomain_iff]
    exact (ballRadialProjection_spec p).2.2.imp Subtype.ext id
  · have h := ballRadialProjection_eq_self p hp
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-- The harmonic sequence `n ↦ 1 / (n + 1)` in the unit interval `I`. -/
noncomputable def harmonicSeq (n : ℕ) : I :=
  ⟨1 / ((n : ℝ) + 1), by positivity,
    div_le_one_of_le₀ (by linarith [n.cast_nonneg (α := ℝ)]) (by positivity)⟩

@[simp]
theorem coe_harmonicSeq (n : ℕ) : (harmonicSeq n : ℝ) = 1 / ((n : ℝ) + 1) := (rfl)

/-- The closed harmonic subspace `{0} ∪ {1 / (n + 1) | n : ℕ}` of the unit interval `I` (Hatcher,
Chapter 0, p. 14). -/
noncomputable def harmonicSeqSet : Set I := insert 0 (range harmonicSeq)

theorem tendsto_harmonicSeq : Tendsto harmonicSeq atTop (𝓝 0) :=
  tendsto_subtype_rng.2 tendsto_one_div_add_atTop_nhds_zero_nat

theorem isClosed_harmonicSeqSet : IsClosed harmonicSeqSet :=
  tendsto_harmonicSeq.isCompact_insert_range.isClosed

private theorem mid_harmonicSeq_notMem (n : ℕ) {y : I} (hy : y ∈ harmonicSeqSet) :
    (y : ℝ) ≠ ((harmonicSeq (n + 1) : ℝ) + harmonicSeq n) / 2 := by
  intro hmid
  have hn1 : (harmonicSeq (n + 1) : ℝ) = 1 / ((n : ℝ) + 2) := by
    push_cast [coe_harmonicSeq]
    ring
  have hn0 : (harmonicSeq n : ℝ) = 1 / ((n : ℝ) + 1) := rfl
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  have hlt : 1 / ((n : ℝ) + 2) < 1 / ((n : ℝ) + 1) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  rcases hy with rfl | ⟨m, rfl⟩
  · rw [Icc.coe_zero, hn1, hn0] at hmid
    linarith
  · rw [hn1, hn0, coe_harmonicSeq] at hmid
    have hm1 : (m : ℝ) + 1 < (n : ℝ) + 2 :=
      (one_div_lt_one_div (by positivity) (by positivity)).1 (by linarith)
    have hm2 : (n : ℝ) + 1 < (m : ℝ) + 1 :=
      (one_div_lt_one_div (by positivity) (by positivity)).1 (by linarith)
    have h1 : m < n + 1 := by exact_mod_cast (by linarith : (m : ℝ) < (n : ℝ) + 1)
    have h2 : n < m := by exact_mod_cast (by linarith : (n : ℝ) < m)
    omega

/-- **Negative control (Hatcher, Chapter 0, p. 14).** Although `harmonicSeqSet` is closed in `I`,
it fails the homotopy extension property: NDR data for `harmonicSeqSet` would map a sufficiently
small interval `[1 / (n + 2), 1 / (n + 1)]` into `harmonicSeqSet` while fixing its endpoints,
violating the intermediate value theorem. -/
theorem not_hasHomotopyExtensionProperty_harmonicSeqSet :
    ¬ HasHomotopyExtensionProperty harmonicSeqSet := by
  intro h
  obtain ⟨N⟩ := nonempty_ndrPair_iff.2 ⟨isClosed_harmonicSeqSet, h⟩
  have h0 : N.control 0 < 1 := by
    rw [(N.control_eq_zero_iff 0).2 (mem_insert 0 _)]
    exact zero_lt_one
  have hnhds : {x : I | N.control x < 1} ∈ 𝓝 (0 : I) :=
    (isOpen_lt N.control.continuous continuous_const).mem_nhds h0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  obtain ⟨n, hn⟩ := (tendsto_harmonicSeq.eventually (Metric.ball_mem_nhds 0 hδ)).exists
  have hdist : (harmonicSeq n : ℝ) < δ := by
    rwa [Subtype.dist_eq, Real.dist_eq, Icc.coe_zero, sub_zero,
      abs_of_nonneg (harmonicSeq n).2.1] at hn
  have hlt : (harmonicSeq (n + 1) : ℝ) < harmonicSeq n := by
    simp only [coe_harmonicSeq]
    exact one_div_lt_one_div_of_lt (by positivity) (by push_cast; linarith)
  let g : ℝ → ℝ := fun r ↦ (N.deformation (1, projIcc 0 1 zero_le_one r) : ℝ)
  have hg_cont : Continuous g := by fun_prop
  have hg_left : g (harmonicSeq (n + 1)) = harmonicSeq (n + 1) := by
    simp only [g, projIcc_val]
    exact congrArg Subtype.val (N.deformation_of_mem 1 (Or.inr ⟨n + 1, rfl⟩))
  have hg_right : g (harmonicSeq n) = harmonicSeq n := by
    simp only [g, projIcc_val]
    exact congrArg Subtype.val (N.deformation_of_mem 1 (Or.inr ⟨n, rfl⟩))
  have hmid_mem : ((harmonicSeq (n + 1) : ℝ) + harmonicSeq n) / 2 ∈
      Icc (g (harmonicSeq (n + 1))) (g (harmonicSeq n)) := by
    rw [hg_left, hg_right]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨r, hrIcc, hgr⟩ := intermediate_value_Icc hlt.le hg_cont.continuousOn hmid_mem
  have hr01 : r ∈ Icc (0 : ℝ) 1 :=
    ⟨(harmonicSeq (n + 1)).2.1.trans hrIcc.1, hrIcc.2.trans (harmonicSeq n).2.2⟩
  let x : I := ⟨r, hr01⟩
  have hx_proj : projIcc 0 1 zero_le_one r = x := projIcc_of_mem zero_le_one hr01
  have hx_lt : N.control x < 1 := by
    apply hball
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, Icc.coe_zero, sub_zero,
      abs_of_nonneg hr01.1]
    exact hrIcc.2.trans_lt hdist
  exact mid_harmonicSeq_notMem n (N.deformation_one_mem hx_lt)
    (by simpa only [g, hx_proj] using hgr)

/-- **Negative control for proper homotopy extension.** The closed subset `harmonicSeqSet` of `I`
does not have the proper homotopy extension property. -/
theorem not_hasProperHomotopyExtensionProperty_harmonicSeqSet :
    ¬ HasProperHomotopyExtensionProperty harmonicSeqSet := fun h ↦
  not_hasHomotopyExtensionProperty_harmonicSeqSet
    (h.hasHomotopyExtensionProperty isClosed_harmonicSeqSet)

end Examples

section NDRAndProd

namespace NDRPair

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : Set X} {B : Set Y}

/-- Ultrafilter convergence step shared by `NDRPair.cylinderDeformation` and `NDRPair.prod`: if
`N.deformation` is proper, `t` and `v` converge in `I` along an ultrafilter `𝒰`, and
`z ↦ N.deformation (t z * projIcc 0 1 (v z / N.control (q z)), q z)` converges to `x₀`, then `q`
converges along `𝒰` to a point `x₁` realizing the value `x₀`. -/
private theorem exists_tendsto_of_ultrafilter {Z : Type*} (N : NDRPair A)
    (hN : IsProperMap N.deformation) {t v : Z → I} {q : Z → X}
    {𝒰 : Ultrafilter Z} {t₁ v₁ : I} {x₀ : X} (ht : Tendsto t 𝒰 (𝓝 t₁))
    (hv : Tendsto v 𝒰 (𝓝 v₁))
    (hdef : Tendsto (fun z ↦
      N.deformation (t z * projIcc 0 1 zero_le_one ((v z : ℝ) / N.control (q z)), q z)) 𝒰 (𝓝 x₀)) :
    ∃ x₁ : X, Tendsto q 𝒰 (𝓝 x₁) ∧
      N.deformation (t₁ * projIcc 0 1 zero_le_one ((v₁ : ℝ) / N.control x₁), x₁) = x₀ := by
  let τ : Z → I := fun z ↦ t z * projIcc 0 1 zero_le_one ((v z : ℝ) / N.control (q z))
  have hmap : Tendsto N.deformation (𝒰.map fun z ↦ (τ z, q z)) (𝓝 x₀) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    exact hdef
  obtain ⟨⟨r₁, x₁⟩, hr₁x₁, hle⟩ := hN.ultrafilter_le_nhds_of_tendsto hmap
  have hpair : Tendsto (fun z ↦ (τ z, q z)) 𝒰 (𝓝 (r₁, x₁)) := by
    rwa [Ultrafilter.coe_map] at hle
  have hqx₁ : Tendsto q 𝒰 (𝓝 x₁) := (continuous_snd.tendsto (r₁, x₁)).comp hpair
  refine ⟨x₁, hqx₁, ?_⟩
  by_cases hx₁ : x₁ ∈ A
  · rw [N.deformation_of_mem _ hx₁]
    exact (N.deformation_of_mem r₁ hx₁).symm.trans hr₁x₁
  · have hu : (N.control x₁ : ℝ) ≠ 0 := by
      intro h0
      exact hx₁ ((N.control_eq_zero_iff x₁).1 (Subtype.ext h0))
    have hctrl : Tendsto (fun z ↦ (N.control (q z) : ℝ)) 𝒰 (𝓝 (N.control x₁ : ℝ)) :=
      ((continuous_subtype_val.comp N.control.continuous).tendsto x₁).comp hqx₁
    have hv' : Tendsto (fun z ↦ (v z : ℝ)) 𝒰 (𝓝 (v₁ : ℝ)) :=
      (continuous_subtype_val.tendsto v₁).comp hv
    have hdiv : Tendsto (fun z ↦ (v z : ℝ) / N.control (q z)) 𝒰
        (𝓝 ((v₁ : ℝ) / N.control x₁)) := hv'.div hctrl hu
    have hτ : Tendsto τ 𝒰 (𝓝 (t₁ * projIcc 0 1 zero_le_one ((v₁ : ℝ) / N.control x₁))) :=
      ht.mul ((continuous_projIcc.tendsto _).comp hdiv)
    have hτ' : Tendsto τ 𝒰 (𝓝 r₁) := (continuous_fst.tendsto (r₁, x₁)).comp hpair
    rw [tendsto_nhds_unique hτ hτ']
    exact hr₁x₁

/-- The deformation of `NDRPair.ofRetraction` is proper whenever the cylinder retraction is proper,
since `I` is compact. -/
theorem isProperMap_ofRetraction_deformation {r : C(I × X, I × X)} (hr_prop : IsProperMap r)
    (hr : ∀ p, r p ∈ cylinderExtensionDomain A) (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p)
    (hA : IsClosed A) : IsProperMap (ofRetraction hr hr' hA).deformation := by
  have heq : ((ofRetraction hr hr' hA).deformation : I × X → X) = Prod.snd ∘ r :=
    funext (ofRetraction_deformation hr hr' hA)
  rw [heq]
  exact isProperMap_snd_of_compactSpace.comp hr_prop

/-- If the deformation of an NDR pair is proper, then so is its cylinder deformation
`I × (I × X) → I × X`. -/
theorem isProperMap_cylinderDeformation (N : NDRPair A) (hN : IsProperMap N.deformation) :
    IsProperMap N.cylinderDeformation := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨N.cylinderDeformation.continuous, fun 𝒰 ⟨t₀, x₀⟩ hy ↦ ?_⟩
  obtain ⟨s₁, -, hs₁⟩ := isCompact_univ.ultrafilter_le_nhds (𝒰.map fun w ↦ w.1) (by simp)
  obtain ⟨t₁, -, ht₁⟩ := isCompact_univ.ultrafilter_le_nhds (𝒰.map fun w ↦ w.2.1) (by simp)
  have hs₁' : Tendsto (fun w : I × I × X ↦ w.1) 𝒰 (𝓝 s₁) := by rwa [Ultrafilter.coe_map] at hs₁
  have ht₁' : Tendsto (fun w : I × I × X ↦ w.2.1) 𝒰 (𝓝 t₁) := by
    rwa [Ultrafilter.coe_map] at ht₁
  have hy₂ : Tendsto (fun w : I × I × X ↦
      N.deformation (w.1 * projIcc 0 1 zero_le_one ((w.2.1 : ℝ) / N.control w.2.2), w.2.2)) 𝒰
      (𝓝 x₀) :=
    ((continuous_snd.tendsto (t₀, x₀)).comp hy).congr fun w ↦
      N.cylinderDeformation_snd w.1 w.2.1 w.2.2
  obtain ⟨x₁, hx₁, hx_eq⟩ := N.exists_tendsto_of_ultrafilter hN hs₁' ht₁' hy₂
  have hw : (𝒰 : Filter (I × I × X)) ≤ 𝓝 (s₁, t₁, x₁) :=
    hs₁'.prodMk_nhds (ht₁'.prodMk_nhds hx₁)
  have ht_eq : (N.cylinderDeformation (s₁, t₁, x₁)).1 = t₀ :=
    tendsto_nhds_unique
      (((continuous_fst.comp N.cylinderDeformation.continuous).tendsto _).mono_left hw)
      ((continuous_fst.tendsto (t₀, x₀)).comp hy)
  exact ⟨(s₁, t₁, x₁), Prod.ext ht_eq (by simpa only [cylinderDeformation_snd] using hx_eq), hw⟩

/-- If the deformations of two NDR pairs are proper, then so is the deformation of their product
`NDRPair.prod`. -/
theorem isProperMap_prod_deformation (N : NDRPair A) (M : NDRPair B)
    (hN : IsProperMap N.deformation) (hM : IsProperMap M.deformation) :
    IsProperMap (N.prod M).deformation := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨(N.prod M).deformation.continuous, fun 𝒰 ⟨x₀, y₀⟩ hxy ↦ ?_⟩
  obtain ⟨t₁, -, ht₁⟩ := isCompact_univ.ultrafilter_le_nhds (𝒰.map fun w ↦ w.1) (by simp)
  have ht₁' : Tendsto (fun w : I × X × Y ↦ w.1) 𝒰 (𝓝 t₁) := by rwa [Ultrafilter.coe_map] at ht₁
  obtain ⟨u₁, -, hu₁⟩ := isCompact_univ.ultrafilter_le_nhds
    (𝒰.map fun w : I × X × Y ↦ N.control w.2.1) (by simp)
  obtain ⟨v₁, -, hv₁⟩ := isCompact_univ.ultrafilter_le_nhds
    (𝒰.map fun w : I × X × Y ↦ M.control w.2.2) (by simp)
  have hu₁' : Tendsto (fun w : I × X × Y ↦ N.control w.2.1) 𝒰 (𝓝 u₁) := by
    rwa [Ultrafilter.coe_map] at hu₁
  have hv₁' : Tendsto (fun w : I × X × Y ↦ M.control w.2.2) 𝒰 (𝓝 v₁) := by
    rwa [Ultrafilter.coe_map] at hv₁
  have hxy₁ : Tendsto (fun w : I × X × Y ↦
      N.deformation (w.1 * projIcc 0 1 zero_le_one ((M.control w.2.2 : ℝ) / N.control w.2.1),
        w.2.1)) 𝒰 (𝓝 x₀) :=
    ((continuous_fst.tendsto (x₀, y₀)).comp hxy).congr fun w ↦
      congrArg Prod.fst (N.prod_deformation_apply M w.1 w.2.1 w.2.2)
  have hxy₂ : Tendsto (fun w : I × X × Y ↦
      M.deformation (w.1 * projIcc 0 1 zero_le_one ((N.control w.2.1 : ℝ) / M.control w.2.2),
        w.2.2)) 𝒰 (𝓝 y₀) :=
    ((continuous_snd.tendsto (x₀, y₀)).comp hxy).congr fun w ↦
      congrArg Prod.snd (N.prod_deformation_apply M w.1 w.2.1 w.2.2)
  obtain ⟨x₁, hx₁, hx_eq⟩ := N.exists_tendsto_of_ultrafilter hN ht₁' hv₁' hxy₁
  obtain ⟨y₁, hy₁, hy_eq⟩ := M.exists_tendsto_of_ultrafilter hM ht₁' hu₁' hxy₂
  have hu_eq : u₁ = N.control x₁ :=
    tendsto_nhds_unique hu₁' ((N.control.continuous.tendsto x₁).comp hx₁)
  have hv_eq : v₁ = M.control y₁ :=
    tendsto_nhds_unique hv₁' ((M.control.continuous.tendsto y₁).comp hy₁)
  subst hu_eq hv_eq
  refine ⟨(t₁, x₁, y₁), ?_, ht₁'.prodMk_nhds (hx₁.prodMk_nhds hy₁)⟩
  rw [prod_deformation_apply, hx_eq, hy_eq]

/-- An NDR pair with proper deformation has the proper homotopy extension property: the time-`1`
slice of `cylinderDeformation` is a proper retraction of `I × X` onto `{0} × X ∪ I × A`. -/
theorem hasProperHomotopyExtensionProperty (N : NDRPair A) (hN : IsProperMap N.deformation) :
    HasProperHomotopyExtensionProperty A := by
  let r : C(I × X, I × X) := (subtypeVal _).comp N.cylinderRetraction
  have hr_eq : (r : I × X → I × X) = fun z ↦ N.cylinderDeformation (1, z) :=
    funext N.coe_cylinderRetraction_apply
  have hr_prop : IsProperMap r := by
    rw [hr_eq]
    exact (N.isProperMap_cylinderDeformation hN).comp (isProperMap_prodMk_left (1 : I))
  exact hasProperHomotopyExtensionProperty_of_proper_retraction N.isClosed hr_prop
    (fun z ↦ (N.cylinderRetraction z).2)
    fun z hz ↦ congrArg Subtype.val (N.cylinderRetraction_apply_coe ⟨z, hz⟩)

end NDRPair

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : Set X} {B : Set Y}

/-- **Strøm's product theorem for proper homotopy extension.** If closed subsets `A ⊆ X` and
`B ⊆ Y` have the proper homotopy extension property, then so does `A × Y ∪ X × B ⊆ X × Y`. -/
theorem HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod
    (hA : HasProperHomotopyExtensionProperty A) (hA' : IsClosed A)
    (hB : HasProperHomotopyExtensionProperty B) (hB' : IsClosed B) :
    HasProperHomotopyExtensionProperty (A ×ˢ (univ : Set Y) ∪ (univ : Set X) ×ˢ B) := by
  obtain ⟨rA, hrA_prop, hrA, hrA'⟩ := hA.exists_proper_retraction hA'
  obtain ⟨rB, hrB_prop, hrB, hrB'⟩ := hB.exists_proper_retraction hB'
  let N := NDRPair.ofRetraction hrA hrA' hA'
  let M := NDRPair.ofRetraction hrB hrB' hB'
  exact (N.prod M).hasProperHomotopyExtensionProperty
    (N.isProperMap_prod_deformation M
      (NDRPair.isProperMap_ofRetraction_deformation hrA_prop hrA hrA' hA')
      (NDRPair.isProperMap_ofRetraction_deformation hrB_prop hrB hrB' hB'))

/-- A closed subset with the proper homotopy extension property retains it after taking the product
with any space. -/
theorem HasProperHomotopyExtensionProperty.univ_prod
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty ((univ : Set Y) ×ˢ A) := by
  simpa using
    hasProperHomotopyExtensionProperty_empty.prod_univ_union_univ_prod isClosed_empty h hA

/-- **Proper homotopy extension for the cylinder-boundary pair.** If a closed subset `A ⊆ X` has
the proper homotopy extension property, then so does `{0, 1} × X ∪ I × A ⊆ I × X`. -/
theorem HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty (({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A) :=
  hasProperHomotopyExtensionProperty_zero_one.prod_univ_union_univ_prod
    (Set.toFinite _).isClosed h hA

end NDRAndProd

section RetracingAndSDR

private theorem isProperMap_of_isClosed_cover₃ {Z W : Type*} [TopologicalSpace Z]
    [TopologicalSpace W] {f : Z → W} {C₀ C₁ C₂ : Set Z}
    (h₀ : IsClosed C₀) (h₁ : IsClosed C₁) (h₂ : IsClosed C₂) (hcover : C₀ ∪ (C₁ ∪ C₂) = univ)
    (hf₀ : IsProperMap (C₀.domRestrict f)) (hf₁ : IsProperMap (C₁.domRestrict f))
    (hf₂ : IsProperMap (C₂.domRestrict f)) : IsProperMap f := by
  refine IsProperMap.of_domRestrict_of_isClosed_union h₀ (h₁.union h₂) hcover hf₀ ?_
  let U₁ : Set ↥(C₁ ∪ C₂) := Subtype.val ⁻¹' C₁
  let U₂ : Set ↥(C₁ ∪ C₂) := Subtype.val ⁻¹' C₂
  have hUcover : U₁ ∪ U₂ = univ := eq_univ_of_forall fun q ↦ q.2
  refine IsProperMap.of_domRestrict_of_isClosed_union (h₁.preimage continuous_subtype_val)
    (h₂.preimage continuous_subtype_val) hUcover ?_ ?_
  · let i₁ : U₁ ≃ₜ C₁ :=
      { toFun := fun q ↦ ⟨q.1.1, q.2⟩
        invFun := fun p ↦ ⟨⟨p.1, Or.inl p.2⟩, p.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact hf₁.comp i₁.isProperMap
  · let i₂ : U₂ ≃ₜ C₂ :=
      { toFun := fun q ↦ ⟨q.1.1, q.2⟩
        invFun := fun p ↦ ⟨⟨p.1, Or.inr p.2⟩, p.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact hf₂.comp i₂.isProperMap

/-- The tent map `t ↦ min (2 t) (2 - 2 t)` on `I`, rising from `0` to `1` on `[0, 1 / 2]` and
returning to `0` on `[1 / 2, 1]`. -/
private noncomputable def tent (t : I) : I :=
  ⟨min (2 * t) (2 - 2 * t), le_min (by linarith [t.2.1]) (by linarith [t.2.2]),
    min_le_iff.2 <| (le_total (t : ℝ) (1 / 2)).imp (fun h ↦ by linarith) fun h ↦ by linarith⟩

private theorem continuous_tent : Continuous tent := by
  unfold tent
  fun_prop

private theorem tent_zero : tent 0 = 0 := by
  ext
  simp [tent]

private theorem tent_one : tent 1 = 0 := by
  ext
  norm_num [tent]

private noncomputable def retracingTime (ut : I × I) : I :=
  projIcc 0 1 zero_le_one ((tent ut.2 : ℝ) - ut.1)

private theorem continuous_retracingTime : Continuous retracingTime := by
  unfold retracingTime
  have := continuous_tent
  fun_prop

private theorem retracingTime_zero_right (u : I) : retracingTime (u, 0) = 0 :=
  projIcc_eq_zero.2 (by simp [tent_zero, u.2.1])

private theorem retracingTime_one_right (u : I) : retracingTime (u, 1) = 0 :=
  projIcc_eq_zero.2 (by simp [tent_one, u.2.1])

private theorem retracingTime_zero_left (t : I) : retracingTime (0, t) = tent t := by
  simp [retracingTime]

private theorem retracingTime_one_left (t : I) : retracingTime (1, t) = 0 := by
  rw [retracingTime]
  exact projIcc_eq_zero.2 (by dsimp only [Icc.coe_one]; linarith [unitInterval.le_one (tent t)])

private theorem trans_apply_of_retracing {X : Type*} {Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f₀ f₁ f₂ : C(X, Y)} (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) {x : X}
    (hG : ∀ t, G (t, x) = F (σ t, x)) (t : I) :
    F.trans G (t, x) = F (tent t, x) := by
  rw [Homotopy.trans_apply]
  split_ifs with ht
  · congr 2
    ext
    simp [tent, min_eq_left (by linarith : (2 : ℝ) * t ≤ 2 - 2 * t)]
  · rw [hG]
    congr 2
    ext
    simp only [tent, coe_symm_eq]
    rw [min_eq_right (by linarith)]
    ring

variable {X : Type u} [TopologicalSpace X] {A : Set X}

private abbrev cylinderBoundary (A : Set X) : Set (I × X) :=
  ({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A

open scoped Classical in
/-- Boundary homotopy on `I × ({0, 1} × X ∪ I × A)` used in
`HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retracing`: constant `f₀` on
`{0} × X`, constant `f₂` on `{1} × X`, and `F (projIcc 0 1 (tent t - u), x)` over `A`. -/
private noncomputable def retracingBoundaryMap {Y : Type v} [TopologicalSpace Y]
    {f₀ f₁ : C(X, Y)} (F : f₀.Homotopy f₁) (f₂ : C(X, Y))
    (p : I × cylinderBoundary A) : Y :=
  if p.2.1.2 ∈ A then F (retracingTime (p.1, p.2.1.1), p.2.1.2)
  else if p.2.1.1 = 0 then f₀ p.2.1.2
  else f₂ p.2.1.2

private theorem isProperMap_retracingBoundaryMap {Y : Type v} [TopologicalSpace Y]
    {f₀ f₁ f₂ : C(X, Y)} (hA_closed : IsClosed A) {F : f₀.Homotopy f₁} (hF : IsProperMap F)
    {G : f₁.Homotopy f₂} (hG : IsProperMap G)
    (hretr : ∀ t, ∀ x ∈ A, G (t, x) = F (σ t, x)) :
    IsProperMap (retracingBoundaryMap (A := A) F f₂) := by
  have hf₀₂ (x : X) (hx : x ∈ A) : f₀ x = f₂ x := by
    rw [← F.apply_zero, ← symm_one, ← hretr 1 x hx, G.apply_one]
  let B := cylinderBoundary A
  let m := retracingBoundaryMap (A := A) F f₂
  let C₀ : Set (I × B) := {p | p.2.1.1 = 0}
  let C₁ : Set (I × B) := {p | p.2.1.1 = 1}
  let C₂ : Set (I × B) := {p | p.2.1.2 ∈ A}
  have hcover : C₀ ∪ (C₁ ∪ C₂) = univ := eq_univ_of_forall fun p ↦ by
    rcases p.2.2 with ⟨ht, -⟩ | ⟨-, hx⟩
    · exact (mem_insert_iff.1 ht).imp id (fun h1 ↦ Or.inl (mem_singleton_iff.1 h1))
    · exact Or.inr (Or.inr hx)
  refine isProperMap_of_isClosed_cover₃ (C₀ := C₀) (C₁ := C₁) (C₂ := C₂)
    ((isClosed_singleton (x := (0 : I))).preimage (by fun_prop))
    ((isClosed_singleton (x := (1 : I))).preimage (by fun_prop))
    (hA_closed.preimage (by fun_prop)) hcover ?_ ?_ ?_
  · let e₀ : C₀ ≃ₜ I × X :=
      { toFun := fun p ↦ (p.1.1, p.1.2.1.2)
        invFun := fun q ↦ ⟨(q.1, ⟨(0, q.2), Or.inl ⟨Or.inl rfl, trivial⟩⟩), rfl⟩
        left_inv := fun p ↦ Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext p.2.symm rfl)))
        right_inv := fun _ ↦ rfl }
    have heq : C₀.domRestrict m = f₀ ∘ Prod.snd ∘ e₀ := funext fun p ↦ by
      have hp : p.1.2.1.1 = 0 := p.2
      simp only [domRestrict_apply, m, retracingBoundaryMap, hp, ↓reduceIte, Function.comp_apply]
      split_ifs with hx
      · rw [retracingTime_zero_right, F.apply_zero]
        rfl
      · rfl
    rw [heq]
    exact (Homotopy.isProperMap_left hF).comp (isProperMap_snd_of_compactSpace.comp e₀.isProperMap)
  · let e₁ : C₁ ≃ₜ I × X :=
      { toFun := fun p ↦ (p.1.1, p.1.2.1.2)
        invFun := fun q ↦ ⟨(q.1, ⟨(1, q.2), Or.inl ⟨Or.inr rfl, trivial⟩⟩), rfl⟩
        left_inv := fun p ↦ Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext p.2.symm rfl)))
        right_inv := fun _ ↦ rfl }
    have heq : C₁.domRestrict m = f₂ ∘ Prod.snd ∘ e₁ := funext fun p ↦ by
      have hp : p.1.2.1.1 = 1 := p.2
      simp only [domRestrict_apply, m, retracingBoundaryMap, hp, one_ne_zero, ↓reduceIte,
        Function.comp_apply]
      split_ifs with hx
      · rw [retracingTime_one_right, F.apply_zero, hf₀₂ _ hx]
        rfl
      · rfl
    rw [heq]
    exact (Homotopy.isProperMap_right hG).comp (isProperMap_snd_of_compactSpace.comp e₁.isProperMap)
  · let e₂ : C₂ ≃ₜ (I × I) × A :=
      { toFun := fun p ↦ ((p.1.1, p.1.2.1.1), ⟨p.1.2.1.2, p.2⟩)
        invFun := fun q ↦ ⟨(q.1.1, ⟨(q.1.2, q.2), Or.inr ⟨trivial, q.2.2⟩⟩), q.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have heq : C₂.domRestrict m = F ∘ Prod.map retracingTime Subtype.val ∘ e₂ := funext fun p ↦ by
      have hp : p.1.2.1.2 ∈ A := p.2
      simp only [domRestrict_apply, m, retracingBoundaryMap, hp, ↓reduceIte, Function.comp_apply]
      rfl
    rw [heq]
    exact hF.comp
      ((continuous_retracingTime.isProperMap.prodMap hA_closed.isProperMap_subtypeVal).comp
        e₂.isProperMap)

/-- **A jointly proper homotopy that retraces itself on `A` rectifies to a jointly proper homotopy
relative to `A`.** Let `A ⊆ X` be closed with the proper homotopy extension property, let
`F : f₀ ≃ f₁` and `G : f₁ ≃ f₂` be jointly proper homotopies into `Y`, and suppose `G` runs
backwards along `F` at every point of `A`. Extending the tent contraction from the cylinder
boundary `{0, 1} × X ∪ I × A` to `I × (I × X)` and taking the terminal slice yields a jointly
proper homotopy `f₀ ≃ f₂` relative to `A`. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retracing
    {Y : Type v} [TopologicalSpace Y] {f₀ f₁ f₂ : C(X, Y)}
    (hA : HasProperHomotopyExtensionProperty A) (hA_closed : IsClosed A)
    {F : f₀.Homotopy f₁} (hF : IsProperMap F) {G : f₁.Homotopy f₂} (hG : IsProperMap G)
    (hretr : ∀ t, ∀ x ∈ A, G (t, x) = F (σ t, x)) :
    ∃ H : f₀.HomotopyRel f₂ A, IsProperMap H := by
  have hf₀₂ (x : X) (hx : x ∈ A) : f₀ x = f₂ x := by
    rw [← F.apply_zero, ← symm_one, ← hretr 1 x hx, G.apply_one]
  have hB_closed : IsClosed (cylinderBoundary A) :=
    (((Set.toFinite ({0, 1} : Set I)).isClosed).prod isClosed_univ).union
      (isClosed_univ.prod hA_closed)
  have hm_prop : IsProperMap (retracingBoundaryMap (A := A) F f₂) :=
    isProperMap_retracingBoundaryMap hA_closed hF hG hretr
  obtain ⟨E, hE_prop, _, hE_B⟩ := (hA.zero_one_prod_univ_union_univ_prod hA_closed
    |>.exists_extension_of_isClosed hB_closed (Homotopy.isProperMap_trans hF hG)
    (H := ⟨retracingBoundaryMap F f₂, hm_prop.continuous⟩) hm_prop) fun q ↦ by
      rcases q with ⟨⟨t, x⟩, hq⟩
      dsimp only [ContinuousMap.coe_mk, retracingBoundaryMap]
      split_ifs with hx ht0
      · rw [retracingTime_zero_left]
        exact (trans_apply_of_retracing F G (fun s ↦ hretr s x hx) t).symm
      · subst ht0
        exact ((F.trans G).apply_zero x).symm
      · rcases hq with ⟨ht01, -⟩ | ⟨-, hx'⟩
        · obtain rfl : t = 1 := (mem_insert_iff.1 ht01).resolve_left ht0 |> mem_singleton_iff.1
          exact ((F.trans G).apply_one x).symm
        · exact absurd hx' hx
  refine ⟨{ toFun := fun p ↦ E (1, p)
            continuous_toFun := E.continuous.comp (continuous_const.prodMk continuous_id)
            map_zero_left := fun x ↦ by
              rw [hE_B 1 ⟨(0, x), Or.inl ⟨Or.inl rfl, trivial⟩⟩]
              simp only [ContinuousMap.coe_mk, retracingBoundaryMap, ↓reduceIte]
              split_ifs with hx
              · rw [retracingTime_zero_right, F.apply_zero]
              · rfl
            map_one_left := fun x ↦ by
              rw [hE_B 1 ⟨(1, x), Or.inl ⟨Or.inr rfl, trivial⟩⟩]
              simp only [ContinuousMap.coe_mk, retracingBoundaryMap, one_ne_zero, ↓reduceIte]
              split_ifs with hx
              · rw [retracingTime_one_right, F.apply_zero, hf₀₂ x hx]
              · rfl
            prop' := fun t x hx ↦ by
              dsimp only [ContinuousMap.coe_mk]
              rw [hE_B 1 ⟨(t, x), Or.inr ⟨trivial, hx⟩⟩]
              simp only [ContinuousMap.coe_mk, retracingBoundaryMap, hx, ↓reduceIte,
                retracingTime_one_left, F.apply_zero] },
    hE_prop.comp (isProperMap_prodMk_left (1 : I))⟩

/-- **Rectifying a proper homotopy left inverse to a proper retraction.** If `A ⊆ X` has the
proper homotopy extension property and `g : X → A` is a proper map with a jointly proper homotopy
`H : g ∘ incl ≃ id_A`, then `g` is linked by a jointly proper homotopy to a proper retraction
`r : X → A` fixing `A` pointwise. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_retraction_homotopic
    (hA : HasProperHomotopyExtensionProperty A) {g : C(X, A)} (hg : IsProperMap g)
    (H : Homotopy (g.comp (subtypeVal A)) (ContinuousMap.id A)) (hH : IsProperMap H) :
    ∃ (r : C(X, A)) (G : r.Homotopy g), IsProperMap r ∧ (∀ a : A, r a = a) ∧ IsProperMap G := by
  obtain ⟨K, hK, hK₀, hK₁⟩ := hA.exists_extension hg hH fun a ↦ H.apply_zero a
  let G₀ : g.Homotopy ⟨fun x ↦ K (1, x), by fun_prop⟩ :=
    { toContinuousMap := K
      map_zero_left := hK₀
      map_one_left := fun _ ↦ rfl }
  have hG₀ : IsProperMap G₀ := hK
  refine ⟨⟨fun x ↦ K (1, x), by fun_prop⟩, G₀.symm, Homotopy.isProperMap_right hG₀,
    fun a ↦ (hK₁ 1 a).trans (H.apply_one a), Homotopy.isProperMap_symm hG₀⟩

/-- **Upgrading a proper retraction to a proper strong deformation retraction.** If `A ⊆ X` is
closed with the proper homotopy extension property, `r : X → A` is a proper retraction fixing `A`,
and `incl ∘ r` is linked to `id_X` by a jointly proper homotopy, then `id_X` is linked to
`incl ∘ r` by a jointly proper homotopy relative to `A`. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retraction
    (hA : HasProperHomotopyExtensionProperty A) (hA_closed : IsClosed A)
    {r : C(X, A)} (hr_prop : IsProperMap r) (hr : ∀ a : A, r a = a)
    (K : Homotopy ((subtypeVal A).comp r) (ContinuousMap.id X)) (hK : IsProperMap K) :
    ∃ H : (ContinuousMap.id X).HomotopyRel ((subtypeVal A).comp r) A, IsProperMap H := by
  let F := K.symm
  have hF : IsProperMap F := Homotopy.isProperMap_symm hK
  let G : Homotopy ((subtypeVal A).comp r) ((subtypeVal A).comp r) :=
    (F.symm.compContinuousMap ((subtypeVal A).comp r)).cast
      (ContinuousMap.ext fun x ↦ by simp [hr]) (ContinuousMap.id_comp _)
  have hG : IsProperMap G :=
    Homotopy.isProperMap_compContinuousMap (Homotopy.isProperMap_symm hF)
      (hA_closed.isProperMap_subtypeVal.comp hr_prop)
  refine hA.exists_proper_homotopyRel_of_retracing hA_closed hF hG fun t x hx ↦ ?_
  have hrx : (r x : X) = x := congrArg Subtype.val (hr ⟨x, hx⟩)
  simp [G, F, hrx]

/-- **A proper cofibration whose inclusion has a proper homotopy inverse is a proper strong
deformation retract.** Given `A ⊆ X` with the proper homotopy extension property, proper inclusion
`incl : A → X`, a proper homotopy inverse `g : X → A`, and jointly proper homotopies
`H : g ∘ incl ≃ id_A` and `K : incl ∘ g ≃ id_X`, there exist a proper retraction `r : X → A` fixing
`A` pointwise and a jointly proper homotopy `id_X ≃ incl ∘ r` relative to `A`.

Working directly with `IsProperMap` via closed maps and ultrafilters avoids any `T2Space` or
`LocallyCompactSpace` assumption on `X`; closedness of `A` follows from properness of the
inclusion. -/
theorem properStrongDeformationRetract_of_inverse
    {X : Type u} [TopologicalSpace X]
    (A : Set X) (hA : HasProperHomotopyExtensionProperty A)
    (hincl : IsProperMap (Subtype.val : A → X)) (g : C(X, A)) (hg : IsProperMap g)
    (H : ContinuousMap.Homotopy (g.comp ⟨Subtype.val, continuous_subtype_val⟩)
      (ContinuousMap.id A))
    (K : ContinuousMap.Homotopy
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp g) (ContinuousMap.id X))
    (hH : IsProperMap H) (hK : IsProperMap K) :
    ∃ r : C(X, A), IsProperMap r ∧ (∀ a : A, r (a : X) = a) ∧
      ∃ H : (ContinuousMap.id X).HomotopyRel
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp r) A,
        IsProperMap H := by
  have hA_closed : IsClosed A := isProperMap_subtypeVal_iff.1 hincl
  obtain ⟨r, G, hr_prop, hr_fix, hG⟩ := hA.exists_proper_retraction_homotopic hg H hH
  let K' : Homotopy ((subtypeVal A).comp r) (ContinuousMap.id X) :=
    ((Homotopy.refl (subtypeVal A)).comp G).trans K
  have hK' : IsProperMap K' :=
    Homotopy.isProperMap_trans (Homotopy.isProperMap_comp (Homotopy.isProperMap_refl hincl) hG) hK
  exact ⟨r, hr_prop, hr_fix,
    hA.exists_proper_homotopyRel_of_retraction hA_closed hr_prop hr_fix K' hK'⟩

/-- **Characterization of proper strong deformation retracts among proper cofibrations.** A subset
`A ⊆ X` with the proper homotopy extension property is closed and admits a proper strong
deformation retraction if and only if its inclusion `A → X` is a proper homotopy equivalence. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_strong_deformation_retraction_iff
    (hA : HasProperHomotopyExtensionProperty A) :
    (IsClosed A ∧ ∃ r : C(X, A), IsProperMap r ∧ (∀ a : A, r (a : X) = a) ∧
      ∃ H : (ContinuousMap.id X).HomotopyRel ((subtypeVal A).comp r) A, IsProperMap H) ↔
      (subtypeVal A).HasProperHomotopyInverse := by
  constructor
  · rintro ⟨hA_closed, r, hr_prop, hr_fix, H, hH⟩
    have hri : r.comp (subtypeVal A) = ContinuousMap.id A := ContinuousMap.ext hr_fix
    exact .intro hA_closed.isProperMap_subtypeVal r hr_prop
      ((Homotopy.refl (ContinuousMap.id A)).cast hri.symm rfl) H.toHomotopy.symm
      ((Homotopy.isProperMap_cast_iff _ _ _).2 (Homotopy.isProperMap_refl isProperMap_id))
      (Homotopy.isProperMap_symm hH)
  · intro hincl_equiv
    have hincl : IsProperMap (Subtype.val : A → X) := hincl_equiv.isProperMap
    obtain ⟨g, hg, H, K, hH, hK⟩ := hincl_equiv.exists_inverse
    exact ⟨isProperMap_subtypeVal_iff.1 hincl,
      properStrongDeformationRetract_of_inverse A hA hincl g hg H K hH hK⟩

end RetracingAndSDR

end TauCeti
