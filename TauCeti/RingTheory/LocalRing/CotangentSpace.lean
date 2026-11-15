/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Functoriality of the cotangent space of a local ring

A local homomorphism `f : R →+* S` between local rings carries `𝔪_R` into `𝔪_S` and `𝔪_R²` into
`𝔪_S²`, so it induces a map `IsLocalRing.CotangentSpace.map f : 𝔪_R / 𝔪_R² → 𝔪_S / 𝔪_S²` that is
semilinear over `IsLocalRing.ResidueField.map f : κ(R) →+* κ(S)`.

When `S` is Noetherian, Nakayama's lemma (`IsLocalRing.CotangentSpace.span_image_eq_top_iff`) shows
that surjectivity of `CotangentSpace.map f` forces `𝔪_R S = 𝔪_S`, and the converse holds whenever
`κ(R) → κ(S)` is surjective. Together with `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`,
this characterizes formal unramifiedness of an essentially finite-type local homomorphism with
surjective residue-field map by surjectivity on cotangent spaces.

## Main definitions and results

* `IsLocalRing.CotangentSpace.map`: the semilinear map `CotangentSpace R →ₛₗ[ResidueField.map f]
  CotangentSpace S` induced by a local ring homomorphism `f : R →+* S`.
* `IsLocalRing.CotangentSpace.mapEquiv`: the semilinear equivalence on cotangent spaces induced by
  a ring isomorphism of local rings.
* `IsLocalRing.CotangentSpace.map_maximalIdeal_eq_of_map_surjective`: if `S` is Noetherian and
  `CotangentSpace.map f` is surjective, then `(maximalIdeal R).map f = maximalIdeal S`.
* `IsLocalRing.CotangentSpace.map_surjective_of_map_maximalIdeal_eq`: conversely, if
  `ResidueField.map f` is surjective and `(maximalIdeal R).map f = maximalIdeal S`, then
  `CotangentSpace.map f` is surjective.
* `IsLocalRing.CotangentSpace.formallyUnramified_iff_map_surjective`: for an essentially
  finite-type local homomorphism into a Noetherian local ring with surjective residue-field map,
  formal unramifiedness is equivalent to surjectivity of `CotangentSpace.map f`.

## References

* [The Stacks Project, Tag 00UW](https://stacks.math.columbia.edu/tag/00UW)
* [The Stacks Project, Tag 02FM](https://stacks.math.columbia.edu/tag/02FM)
-/

public section

namespace IsLocalRing.CotangentSpace

variable {R S T : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [CommRing T] [IsLocalRing T]

/-- A local ring homomorphism `f : R →+* S` induces a map `𝔪_R / 𝔪_R² → 𝔪_S / 𝔪_S²` on cotangent
spaces, semilinear over `IsLocalRing.ResidueField.map f`. -/
noncomputable def map (f : R →+* S) [IsLocalHom f] :
    CotangentSpace R →ₛₗ[ResidueField.map f] CotangentSpace S where
  __ :=
    QuotientAddGroup.lift _
      ((toCotangentSpace S).toAddMonoidHom.comp
        { toFun := fun x ↦ ⟨f x.1, map_nonunit f x.1 x.2⟩
          map_zero' := Subtype.ext (map_zero f)
          map_add' := fun x y ↦ Subtype.ext (map_add f x.1 y.1) })
      fun x hx ↦ by
        simp only [Submodule.mem_toAddSubgroup] at hx
        rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
          toCotangentSpace_apply, Ideal.toCotangent_eq_zero, pow_two]
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        refine Submodule.smul_induction_on hx
          (fun r hr y _ ↦ ?_) (fun a b ha hb ↦ ?_)
        · rw [Submodule.coe_smul_of_tower, smul_eq_mul, map_mul]
          exact Ideal.mul_mem_mul (map_nonunit f r hr) (map_nonunit f y.1 y.2)
        · rw [Submodule.coe_add, map_add]
          exact add_mem ha hb
  map_smul' c x := by
    obtain ⟨r, rfl⟩ := residue_surjective c
    obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective x
    -- On representatives in `𝔪_R`, `QuotientAddGroup.lift` evaluates to `toCotangentSpace S`.
    change toCotangentSpace S ⟨f (r * x.1), _⟩ =
      ResidueField.map f (residue R r) • toCotangentSpace S ⟨f x.1, _⟩
    rw [ResidueField.map_residue, ← (toCotangentSpace S).map_smulₛₗ]
    exact congrArg (toCotangentSpace S) (Subtype.ext (map_mul f r x.1))

/-- On the class of `x ∈ 𝔪_R`, `CotangentSpace.map f` sends `x mod 𝔪_R²` to `f x mod 𝔪_S²`. -/
@[simp]
theorem map_toCotangent (f : R →+* S) [IsLocalHom f] (x : maximalIdeal R) :
    map f ((maximalIdeal R).toCotangent x) =
      (maximalIdeal S).toCotangent ⟨f x.1, map_nonunit f x.1 x.2⟩ :=
  (rfl)

/-- On `toCotangentSpace`, `CotangentSpace.map f` sends `x` to the class of `f x`. -/
@[simp]
theorem map_toCotangentSpace (f : R →+* S) [IsLocalHom f] (x : maximalIdeal R) :
    map f (toCotangentSpace R x) =
      toCotangentSpace S ⟨f x.1, map_nonunit f x.1 x.2⟩ :=
  (rfl)

/-- `CotangentSpace.map` of the identity ring homomorphism acts as the identity. -/
@[simp]
theorem map_id_apply (x : CotangentSpace R) : map (RingHom.id R) x = x := by
  obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective x
  rfl

/-- `CotangentSpace.map` is functorial under composition of local ring homomorphisms. -/
@[simp]
theorem map_comp_apply (f : R →+* S) (g : S →+* T) [IsLocalHom f] [IsLocalHom g]
    (x : CotangentSpace R) :
    map (g.comp f) x = map g (map f x) := by
  obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective x
  rfl

/-- The maps on residue fields induced by a ring isomorphism and its inverse form an inverse pair
of ring homomorphisms. -/
noncomputable instance ringHomInvPair_residueField_map (e : R ≃+* S) :
    RingHomInvPair (ResidueField.map (e : R →+* S)) (ResidueField.map (e.symm : S →+* R)) :=
  RingHomInvPair.of_ringEquiv (ResidueField.mapEquiv e)

/-- A ring isomorphism of local rings induces a semilinear equivalence of cotangent spaces. -/
noncomputable def mapEquiv (e : R ≃+* S) :
    CotangentSpace R ≃ₛₗ[ResidueField.map (e : R →+* S)] CotangentSpace S where
  __ := map (e : R →+* S)
  invFun := map (e.symm : S →+* R)
  left_inv x := by
    obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective x
    simp
  right_inv x := by
    obtain ⟨x, rfl⟩ := (maximalIdeal S).toCotangent_surjective x
    simp

/-- `CotangentSpace.mapEquiv e` acts as `CotangentSpace.map e`. -/
@[simp]
theorem mapEquiv_apply (e : R ≃+* S) (x : CotangentSpace R) :
    mapEquiv e x = map (e : R →+* S) x :=
  (rfl)

/-- The inverse of `CotangentSpace.mapEquiv e` is `CotangentSpace.mapEquiv e.symm`. -/
@[simp]
theorem mapEquiv_symm (e : R ≃+* S) :
    (mapEquiv e).symm = mapEquiv e.symm :=
  (rfl)

/-- If `S` is Noetherian and `CotangentSpace.map f` is surjective, then `𝔪_R` generates `𝔪_S`. -/
theorem map_maximalIdeal_eq_of_map_surjective [IsNoetherianRing S] (f : R →+* S) [IsLocalHom f]
    (hsurj : Function.Surjective (map f)) :
    (maximalIdeal R).map f = maximalIdeal S := by
  refine le_antisymm (((local_hom_tfae f).out 1 3).mp ‹_›) ?_
  let M : Submodule S (maximalIdeal S) :=
    Submodule.comap (maximalIdeal S).subtype ((maximalIdeal R).map f)
  have htop :
      Submodule.span (ResidueField S) ((maximalIdeal S).toCotangent '' (M : Set _)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨w, rfl⟩ := hsurj z
    obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective w
    exact Submodule.subset_span
      ⟨⟨f x.1, map_nonunit f x.1 x.2⟩, Ideal.mem_map_of_mem f x.2, rfl⟩
  have hM : M = ⊤ := by
    simpa only [M.span_eq] using
      (span_image_eq_top_iff (R := S) (s := (M : Set _))).mp htop
  intro y hy
  exact Submodule.mem_comap.mp (hM ▸ Submodule.mem_top : (⟨y, hy⟩ : maximalIdeal S) ∈ M)

/-- If `ResidueField.map f` is surjective and `𝔪_R` generates `𝔪_S`, then `CotangentSpace.map f` is
surjective. -/
theorem map_surjective_of_map_maximalIdeal_eq (f : R →+* S) [IsLocalHom f]
    (hres : Function.Surjective (ResidueField.map f))
    (hmax : (maximalIdeal R).map f = maximalIdeal S) :
    Function.Surjective (map f) := by
  intro z
  obtain ⟨⟨y, hy⟩, rfl⟩ := (maximalIdeal S).toCotangent_surjective z
  have hle : (maximalIdeal R).map f ≤ maximalIdeal S := hmax.le
  have hy' : y ∈ (maximalIdeal R).map f := hmax.symm ▸ hy
  refine Submodule.span_induction
    (p := fun y (h : y ∈ (maximalIdeal R).map f) ↦
      (maximalIdeal S).toCotangent ⟨y, hle h⟩ ∈ Set.range (map f))
    (fun _ hx ↦ ?_) ⟨0, by rw [map_zero]; exact ((maximalIdeal S).toCotangent.map_zero).symm⟩
    (fun a b ha hb ⟨u, hu⟩ ⟨v, hv⟩ ↦ ?_) (fun s a ha ⟨u, hu⟩ ↦ ?_) hy'
  · obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨(maximalIdeal R).toCotangent ⟨r, hr⟩, rfl⟩
  · refine ⟨u + v, ?_⟩
    rw [map_add, hu, hv, ← map_add]
    rfl
  · obtain ⟨c, hc⟩ := hres (residue S s)
    refine ⟨c • u, ?_⟩
    rw [LinearMap.map_smulₛₗ, hc, hu, ← toCotangentSpace_apply, ← (toCotangentSpace S).map_smulₛₗ,
      toCotangentSpace_apply]
    rfl

/-- Over a Noetherian target local ring, when `ResidueField.map f` is surjective,
`CotangentSpace.map f` is surjective if and only if `𝔪_R` generates `𝔪_S`. -/
theorem map_surjective_iff [IsNoetherianRing S] (f : R →+* S) [IsLocalHom f]
    (hres : Function.Surjective (ResidueField.map f)) :
    Function.Surjective (map f) ↔ (maximalIdeal R).map f = maximalIdeal S :=
  ⟨map_maximalIdeal_eq_of_map_surjective f, map_surjective_of_map_maximalIdeal_eq f hres⟩

/-- An essentially finite-type local homomorphism `f : R →+* S` into a Noetherian local ring with
surjective residue-field map is formally unramified if and only if the induced map on cotangent
spaces `CotangentSpace.map f` is surjective. -/
theorem formallyUnramified_iff_map_surjective [IsNoetherianRing S] (f : R →+* S) [IsLocalHom f]
    (hft : f.EssFiniteType) (hres : Function.Surjective (ResidueField.map f)) :
    f.FormallyUnramified ↔ Function.Surjective (map f) := by
  algebraize [f]
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have hmap : algebraMap (ResidueField R) (ResidueField S) = ResidueField.map f := by
    ext x
    obtain ⟨r, rfl⟩ := residue_surjective x
    rfl
  have hsurj : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)) :=
    hmap.symm ▸ hres
  have : Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
    ⟨fun y ↦ by obtain ⟨x, rfl⟩ := hsurj y; exact isSeparable_algebraMap x⟩
  have hfu : f.FormallyUnramified ↔ Algebra.FormallyUnramified R S := by
    rw [← RingHom.algebraMap_toAlgebra f, RingHom.formallyUnramified_algebraMap]
  rw [hfu, Algebra.FormallyUnramified.iff_map_maximalIdeal_eq, and_iff_right ‹_›,
    RingHom.algebraMap_toAlgebra, map_surjective_iff f hres]

end IsLocalRing.CotangentSpace
