/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic
public import TauCeti.AlgebraicGeometry.TangentSpace.Basic
public import TauCeti.RingTheory.LocalRing.CotangentSpace
public import TauCeti.RingTheory.TrivSqZeroExt
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-!
# Zariski cotangent functoriality, dual numbers, and group-scheme tangent additivity

A morphism of schemes `f : X ⟶ Y` induces at each point `x : X` a map on Zariski cotangent spaces
`f.zariskiCotangentMap x : ZariskiCotangentSpace Y (f x) → ZariskiCotangentSpace X x`, semilinear
over `f.residueFieldMap x`. When `f` is locally of finite type, the stalk at `x` is Noetherian, and
`f.residueFieldMap x` is surjective, formal unramifiedness of `f.stalkMap x` is equivalent to
surjectivity of `f.zariskiCotangentMap x`.

Over a field `K`, for any `K`-scheme `X : Over (Spec (.of K))` equipped with a `K`-rational section
`s : 𝟙_ (Over (Spec (.of K))) ⟶ X` and any symmetric `K`-bimodule `M`, morphisms from
`Spec (TrivSqZeroExt K M)` to `X` over `Spec K` extending `s` correspond canonically to functionals
`ZariskiCotangentSpace X.left (overSectionHom s (IsLocalRing.closedPoint K)) → M` semilinear along
`residueFieldRingEquivOfSection`, compatibly with morphisms of pointed `K`-schemes and `K`-linear
maps in `M`.

Applying this functoriality to `M`, `M × M`, the two coordinate inclusions, the projections, and
addition on `M × M` shows that for any group scheme `G` over `Spec K`, the group law on
`Spec (TrivSqZeroExt K M)`-points lying over the identity `η[G]` corresponds to pointwise addition
of cotangent functionals (Stacks Project, Tag 0BFG). Neither commutativity nor smoothness of `G` is
needed. When `M = K`, `trivSqZeroOver K K` and `trivSqZeroSection K K` package in `Over (Spec K)`
the projection and section of `TauCeti.AlgebraicGeometry.dualNumberSplitEpi K`, generalized here to
an arbitrary module `M` so that `M × M` is handled uniformly.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.zariskiCotangentMap`: functorial pullback on Zariski cotangent
  spaces.
* `AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_iff_zariskiCotangentMap_surjective`:
  cotangent-surjectivity criterion for formal unramifiedness of a stalk map.
* `TauCeti.AlgebraicGeometry.trivSqZeroOver`, `TauCeti.AlgebraicGeometry.trivSqZeroSection`,
  `TauCeti.AlgebraicGeometry.trivSqZeroOverMap`: `Spec (TrivSqZeroExt K M)` as a pointed scheme
  over `Spec K`, contravariantly functorial in `M`.
* `TauCeti.AlgebraicGeometry.trivSqZeroPointEquiv`: canonical equivalence between pointed
  `TrivSqZeroExt K M`-points and Zariski cotangent functionals at a `K`-rational section.
* `TauCeti.AlgebraicGeometry.trivSqZeroPointEquiv_mul`: group multiplication of infinitesimal
  identity points adds their cotangent functionals (Stacks Project, Tag 0BFG).

## References

* [The Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* J. S. Milne, *Algebraic Groups* (2017), §10.b.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry IsLocalRing TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ Y` induces a pullback map on Zariski cotangent spaces at `x : X`,
semilinear over `IsLocalRing.ResidueField.map (f.stalkMap x).hom`. -/
noncomputable def zariskiCotangentMap (f : X ⟶ Y) (x : X) :
    ZariskiCotangentSpace Y (f x) →ₛₗ[ResidueField.map (f.stalkMap x).hom]
      ZariskiCotangentSpace X x :=
  CotangentSpace.map (f.stalkMap x).hom

/-- `zariskiCotangentMap` acts on classes of maximal-ideal germs via `f.stalkMap x`. -/
@[simp]
theorem zariskiCotangentMap_toCotangentSpace (f : X ⟶ Y) (x : X)
    (m : maximalIdeal (Y.presheaf.stalk (f x))) :
    f.zariskiCotangentMap x (toCotangentSpace _ m) =
      toCotangentSpace _ ⟨f.stalkMap x m.1, map_nonunit (f.stalkMap x).hom m.1 m.2⟩ :=
  CotangentSpace.map_toCotangentSpace (f.stalkMap x).hom m

/-- The identity morphism induces the identity on Zariski cotangent spaces. -/
theorem zariskiCotangentMap_id_apply (X : Scheme.{u}) (x : X) (v : ZariskiCotangentSpace X x) :
    Scheme.Hom.zariskiCotangentMap (𝟙 X) x v = v := by
  obtain ⟨m, rfl⟩ := (maximalIdeal (X.presheaf.stalk ((𝟙 X) x))).toCotangent_surjective v
  exact (CotangentSpace.map_toCotangent (Scheme.Hom.stalkMap (𝟙 X) x).hom m).trans
    (congrArg _ (Subtype.ext (by simp; rfl)))

/-- `zariskiCotangentMap` is contravariantly functorial under composition of scheme morphisms. -/
theorem zariskiCotangentMap_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (v : ZariskiCotangentSpace Z (g (f x))) :
    (f ≫ g).zariskiCotangentMap x v =
      f.zariskiCotangentMap x (g.zariskiCotangentMap (f x) v) := by
  obtain ⟨m, rfl⟩ := (maximalIdeal (Z.presheaf.stalk ((f ≫ g) x))).toCotangent_surjective v
  let mg : maximalIdeal (Y.presheaf.stalk (f x)) :=
    ⟨g.stalkMap (f x) m.1, map_nonunit (g.stalkMap (f x)).hom m.1 m.2⟩
  let mfg : maximalIdeal (X.presheaf.stalk x) :=
    ⟨f.stalkMap x mg.1, map_nonunit (f.stalkMap x).hom mg.1 mg.2⟩
  have h1 := CotangentSpace.map_toCotangent ((f ≫ g).stalkMap x).hom m
  have h2 : (⟨(f ≫ g).stalkMap x m.1, map_nonunit ((f ≫ g).stalkMap x).hom m.1 m.2⟩ :
      maximalIdeal (X.presheaf.stalk x)) = mfg :=
    Subtype.ext (by simp [mg, mfg, Scheme.Hom.stalkMap_comp]; rfl)
  have h3 := (CotangentSpace.map_toCotangent (f.stalkMap x).hom mg).symm
  have h4 := congrArg (f.zariskiCotangentMap x)
    (CotangentSpace.map_toCotangent (g.stalkMap (f x)).hom m).symm
  exact (h1.trans (congrArg _ h2)).trans (h3.trans h4)

/-- When `f` is locally of finite type, `𝒪_{X, x}` is Noetherian, and `f.residueFieldMap x` is
surjective, `f.stalkMap x` is formally unramified if and only if `f.zariskiCotangentMap x` is
surjective. -/
theorem formallyUnramified_stalkMap_iff_zariskiCotangentMap_surjective (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (hres : Function.Surjective (f.residueFieldMap x)) :
    (f.stalkMap x).hom.FormallyUnramified ↔ Function.Surjective (f.zariskiCotangentMap x) :=
  CotangentSpace.formallyUnramified_iff_map_surjective (f.stalkMap x).hom
    (LocallyOfFiniteType.stalkMap f x) hres

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

section LocalRingLift

variable {K R M : Type u} [Field K] [CommRing R] [IsLocalRing R] [AddCommGroup M]
  [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]

/-- For a local ring `R` with a local retraction `ε : R →+* K` of `baseMap : K →+* R`, an element
lies in `maximalIdeal R` iff `ε` sends it to `0`. -/
private lemma mem_maximalIdeal_iff_eq_zero_of_isLocalHom (ε : R →+* K) [IsLocalHom ε] (r : R) :
    r ∈ maximalIdeal R ↔ ε r = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  exact ⟨fun hr ↦ by_contra fun h0 ↦ hr (IsLocalHom.map_nonunit r (IsUnit.mk0 (ε r) h0)),
    fun h0 hr ↦ not_isUnit_zero (h0 ▸ ε.isUnit_map hr)⟩

/-- For any local retraction `ε` of `baseMap`, `a - baseMap (ε a)` lies in `maximalIdeal R`. -/
private lemma sub_baseMap_mem_maximalIdeal (baseMap : K →+* R) (ε : R →+* K) [IsLocalHom ε]
    (hε : ∀ c, ε (baseMap c) = c) (a : R) :
    a - baseMap (ε a) ∈ maximalIdeal R :=
  (mem_maximalIdeal_iff_eq_zero_of_isLocalHom ε _).mpr <| by rw [map_sub, hε, sub_self]

/-- Construct a `K`-compatible ring homomorphism `R →+* TrivSqZeroExt K M` lifting `ε` from a
semilinear functional on `CotangentSpace R`. -/
private noncomputable def ringHomOfCotangentLinear (baseMap : K →+* R) (ε : R →+* K)
    [IsLocalHom ε] (hε : ∀ c, ε (baseMap c) = c) (e : ResidueField R ≃+* K)
    (he : ∀ r, e (residue R r) = ε r) (ℓ : CotangentSpace R →ₛₗ[e.toRingHom] M) :
    R →+* TrivSqZeroExt K M where
  toFun a :=
    TrivSqZeroExt.inl (ε a) +
      TrivSqZeroExt.inr (ℓ (toCotangentSpace R ⟨a - baseMap (ε a),
        sub_baseMap_mem_maximalIdeal baseMap ε hε a⟩))
  map_one' := by
    have h1 : (⟨1 - baseMap (ε 1), sub_baseMap_mem_maximalIdeal baseMap ε hε 1⟩ :
        maximalIdeal R) = 0 := by ext; simp
    rw [h1, map_zero, map_zero, map_one, TrivSqZeroExt.inr_zero, add_zero,
      TrivSqZeroExt.inl_one]
  map_mul' a b := by
    have hδ := sub_baseMap_mem_maximalIdeal baseMap ε hε
    have he' (r : R) : e.toRingHom (residue R r) = ε r := he r
    have hmem : (a * b - baseMap (ε (a * b))) -
        (baseMap (ε b) * (a - baseMap (ε a)) + baseMap (ε a) * (b - baseMap (ε b))) ∈
          maximalIdeal R ^ 2 := by
      have hid : (a * b - baseMap (ε (a * b))) -
          (baseMap (ε b) * (a - baseMap (ε a)) + baseMap (ε a) * (b - baseMap (ε b))) =
          (a - baseMap (ε a)) * (b - baseMap (ε b)) := by
        simp only [map_mul]
        ring
      rw [hid, pow_two]
      exact Ideal.mul_mem_mul (hδ a) (hδ b)
    have hcot : toCotangentSpace R ⟨a * b - baseMap (ε (a * b)), hδ (a * b)⟩ =
        residue R (baseMap (ε b)) • toCotangentSpace R ⟨a - baseMap (ε a), hδ a⟩ +
          residue R (baseMap (ε a)) • toCotangentSpace R ⟨b - baseMap (ε b), hδ b⟩ := by
      rw [← (toCotangentSpace R).map_smulₛₗ, ← (toCotangentSpace R).map_smulₛₗ, ← map_add,
        ← sub_eq_zero, ← map_sub, toCotangentSpace_apply, Ideal.toCotangent_eq_zero]
      exact hmem
    have hd : ℓ (toCotangentSpace R ⟨a * b - baseMap (ε (a * b)), hδ (a * b)⟩) =
        ε a • ℓ (toCotangentSpace R ⟨b - baseMap (ε b), hδ b⟩) +
          ε b • ℓ (toCotangentSpace R ⟨a - baseMap (ε a), hδ a⟩) := by
      rw [hcot, map_add, ℓ.map_smulₛₗ, ℓ.map_smulₛₗ, he', hε, he', hε, add_comm]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        add_zero, zero_add, op_smul_eq_smul]
      rw [hd, add_comm]
  map_zero' := by
    have h0 : (⟨0 - baseMap (ε 0), sub_baseMap_mem_maximalIdeal baseMap ε hε 0⟩ :
        maximalIdeal R) = 0 := by ext; simp
    rw [h0, map_zero, map_zero, map_zero, TrivSqZeroExt.inl_zero, TrivSqZeroExt.inr_zero, add_zero]
  map_add' a b := by
    have hδ := sub_baseMap_mem_maximalIdeal baseMap ε hε
    have hab : (⟨a + b - baseMap (ε (a + b)), hδ (a + b)⟩ : maximalIdeal R) =
        ⟨a - baseMap (ε a), hδ a⟩ + ⟨b - baseMap (ε b), hδ b⟩ := by
      ext
      simp only [Submodule.coe_add, map_add]
      ring
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      rw [hab, map_add, map_add]

private lemma ringHomOfCotangentLinear_snd (baseMap : K →+* R) (ε : R →+* K)
    [IsLocalHom ε] (hε : ∀ c, ε (baseMap c) = c) (e : ResidueField R ≃+* K)
    (he : ∀ r, e (residue R r) = ε r) (ℓ : CotangentSpace R →ₛₗ[e.toRingHom] M) (a : R) :
    (ringHomOfCotangentLinear baseMap ε hε e he ℓ a).snd =
      ℓ (toCotangentSpace R ⟨a - baseMap (ε a), sub_baseMap_mem_maximalIdeal baseMap ε hε a⟩) := by
  simp [ringHomOfCotangentLinear]

private lemma ringHomOfCotangentLinear_comp_baseMap (baseMap : K →+* R) (ε : R →+* K)
    [IsLocalHom ε] (hε : ∀ c, ε (baseMap c) = c) (e : ResidueField R ≃+* K)
    (he : ∀ r, e (residue R r) = ε r) (ℓ : CotangentSpace R →ₛₗ[e.toRingHom] M) :
    (ringHomOfCotangentLinear baseMap ε hε e he ℓ).comp baseMap =
      algebraMap K (TrivSqZeroExt K M) := by
  refine RingHom.ext fun c ↦ ?_
  have hc : (⟨baseMap c - baseMap (ε (baseMap c)),
      sub_baseMap_mem_maximalIdeal baseMap ε hε (baseMap c)⟩ : maximalIdeal R) = 0 := by
    ext
    simp [hε]
  ext
  · simp [ringHomOfCotangentLinear, hε, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [RingHom.comp_apply, ringHomOfCotangentLinear_snd, hc, map_zero, map_zero,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]

private lemma fstHom_comp_ringHomOfCotangentLinear (baseMap : K →+* R) (ε : R →+* K)
    [IsLocalHom ε] (hε : ∀ c, ε (baseMap c) = c) (e : ResidueField R ≃+* K)
    (he : ∀ r, e (residue R r) = ε r) (ℓ : CotangentSpace R →ₛₗ[e.toRingHom] M) :
    (TrivSqZeroExt.fstHom K K M).toRingHom.comp
        (ringHomOfCotangentLinear baseMap ε hε e he ℓ) = ε := by
  ext a
  simp [ringHomOfCotangentLinear]

/-- Extract a semilinear functional on `CotangentSpace R` from a ring lift
`R →+* TrivSqZeroExt K M` of `ε`. -/
private noncomputable def cotangentLinearOfRingHom (ε : R →+* K) [IsLocalHom ε]
    (e : ResidueField R ≃+* K) (he : ∀ r, e (residue R r) = ε r)
    (ψ : R →+* TrivSqZeroExt K M)
    (hfst : (TrivSqZeroExt.fstHom K K M).toRingHom.comp ψ = ε) :
    CotangentSpace R →ₛₗ[e.toRingHom] M where
  __ :=
    QuotientAddGroup.lift _
      { toFun := fun m : maximalIdeal R ↦ (ψ m.1).snd
        map_zero' := by simp
        map_add' := fun a b ↦ by simp }
      fun x hx ↦ by
        have hfst_apply (r : R) : (ψ r).fst = ε r := congr($hfst r)
        simp only [Submodule.mem_toAddSubgroup] at hx
        rw [AddMonoidHom.mem_ker]
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        refine Submodule.smul_induction_on hx (fun r hr y _ ↦ ?_) (fun a b ha hb ↦ ?_)
        · have hr0 : (ψ r).fst = 0 :=
            (hfst_apply r).trans ((mem_maximalIdeal_iff_eq_zero_of_isLocalHom ε r).mp hr)
          have hy0 : (ψ y.1).fst = 0 :=
            (hfst_apply y.1).trans ((mem_maximalIdeal_iff_eq_zero_of_isLocalHom ε y.1).mp y.2)
          rw [Submodule.coe_smul_of_tower, smul_eq_mul, map_mul, TrivSqZeroExt.snd_mul,
            op_smul_eq_smul, hr0, hy0, zero_smul, zero_smul, add_zero]
        · rw [Submodule.coe_add, map_add, TrivSqZeroExt.snd_add, ha, hb, add_zero]
  map_smul' c v := by
    have hfst_apply (r : R) : (ψ r).fst = ε r := congr($hfst r)
    obtain ⟨r, rfl⟩ := residue_surjective c
    obtain ⟨m, rfl⟩ := (maximalIdeal R).toCotangent_surjective v
    have hm0 : (ψ m.1).fst = 0 :=
      (hfst_apply m.1).trans ((mem_maximalIdeal_iff_eq_zero_of_isLocalHom ε m.1).mp m.2)
    -- Evaluate `QuotientAddGroup.lift` on representatives in `𝔪_R`.
    change (ψ (r * m.1)).snd = e (residue R r) • (ψ m.1).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, hm0, zero_smul, add_zero, hfst_apply, he]

private lemma cotangentLinearOfRingHom_toCotangent (ε : R →+* K) [IsLocalHom ε]
    (e : ResidueField R ≃+* K) (he : ∀ r, e (residue R r) = ε r)
    (ψ : R →+* TrivSqZeroExt K M)
    (hfst : (TrivSqZeroExt.fstHom K K M).toRingHom.comp ψ = ε)
    (m : maximalIdeal R) :
    cotangentLinearOfRingHom ε e he ψ hfst ((maximalIdeal R).toCotangent m) = (ψ m.1).snd :=
  rfl

private lemma cotangentLinearOfRingHom_toCotangentSpace (ε : R →+* K) [IsLocalHom ε]
    (e : ResidueField R ≃+* K) (he : ∀ r, e (residue R r) = ε r)
    (ψ : R →+* TrivSqZeroExt K M)
    (hfst : (TrivSqZeroExt.fstHom K K M).toRingHom.comp ψ = ε)
    (m : maximalIdeal R) :
    cotangentLinearOfRingHom ε e he ψ hfst (toCotangentSpace R m) = (ψ m.1).snd :=
  rfl

/-- Equivalence between `K`-compatible ring lifts `R →+* TrivSqZeroExt K M` of `ε` and semilinear
functionals on `CotangentSpace R`. -/
private noncomputable def ringHomEquivCotangentLinear (baseMap : K →+* R) (ε : R →+* K)
    [IsLocalHom ε] (hε : ∀ c, ε (baseMap c) = c) (e : ResidueField R ≃+* K)
    (he : ∀ r, e (residue R r) = ε r) :
    {ψ : R →+* TrivSqZeroExt K M //
      ψ.comp baseMap = algebraMap K (TrivSqZeroExt K M) ∧
        (TrivSqZeroExt.fstHom K K M).toRingHom.comp ψ = ε} ≃
      (CotangentSpace R →ₛₗ[e.toRingHom] M) where
  toFun := fun ⟨ψ, _, hfst⟩ ↦ cotangentLinearOfRingHom ε e he ψ hfst
  invFun ℓ := ⟨ringHomOfCotangentLinear baseMap ε hε e he ℓ,
    ⟨ringHomOfCotangentLinear_comp_baseMap baseMap ε hε e he ℓ,
      fstHom_comp_ringHomOfCotangentLinear baseMap ε hε e he ℓ⟩⟩
  left_inv := fun ⟨ψ, hK, hfst⟩ ↦ by
    apply Subtype.ext
    refine RingHom.ext fun a ↦ ?_
    have hfst_a : (ψ a).fst = ε a := congr($hfst a)
    have hK_c (c : K) : ψ (baseMap c) = TrivSqZeroExt.inl c := by
      simpa [TrivSqZeroExt.algebraMap_eq_inl] using congr($hK c)
    ext
    · simpa [ringHomOfCotangentLinear] using hfst_a.symm
    · dsimp only
      rw [ringHomOfCotangentLinear_snd, cotangentLinearOfRingHom_toCotangentSpace, map_sub, hK_c,
        TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inl, sub_zero]
  right_inv ℓ := by
    ext v
    obtain ⟨m, rfl⟩ := (maximalIdeal R).toCotangent_surjective v
    have hm0 : ε m.1 = 0 := (mem_maximalIdeal_iff_eq_zero_of_isLocalHom ε m.1).mp m.2
    dsimp only
    rw [cotangentLinearOfRingHom_toCotangent, ringHomOfCotangentLinear_snd]
    congr 1
    rw [toCotangentSpace_apply]
    congr 1
    ext
    simp [hm0]

/-- Evaluation of `ringHomEquivCotangentLinear` on `toCotangent m` extracts the `M`-component. -/
private lemma ringHomEquivCotangentLinear_toCotangent (baseMap : K →+* R) (ε : R →+* K)
    [IsLocalHom ε] (hε : ∀ c, ε (baseMap c) = c) (e : ResidueField R ≃+* K)
    (he : ∀ r, e (residue R r) = ε r)
    (ψ : {ψ : R →+* TrivSqZeroExt K M //
      ψ.comp baseMap = algebraMap K (TrivSqZeroExt K M) ∧
        (TrivSqZeroExt.fstHom K K M).toRingHom.comp ψ = ε})
    (m : maximalIdeal R) :
    ringHomEquivCotangentLinear baseMap ε hε e he ψ ((maximalIdeal R).toCotangent m) =
      (ψ.1 m.1).snd :=
  rfl

/-- Functoriality of `ringHomEquivCotangentLinear` in the module `M`, stated for an abstract local
ring `R`. -/
private lemma ringHomEquivCotangentLinear_overMap
    {N : Type u} [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N] [IsCentralScalar K N]
    (baseMap : K →+* R) (ε : R →+* K) [IsLocalHom ε] (hε : ∀ c, ε (baseMap c) = c)
    (e : ResidueField R ≃+* K) (he : ∀ r, e (residue R r) = ε r)
    (α : M →ₗ[K] N)
    (ψM : {ψ : R →+* TrivSqZeroExt K M //
      ψ.comp baseMap = algebraMap K (TrivSqZeroExt K M) ∧
        (TrivSqZeroExt.fstHom K K M).toRingHom.comp ψ = ε})
    (ψN : {ψ : R →+* TrivSqZeroExt K N //
      ψ.comp baseMap = algebraMap K (TrivSqZeroExt K N) ∧
        (TrivSqZeroExt.fstHom K K N).toRingHom.comp ψ = ε})
    (hψ : ψN.1 = (TrivSqZeroExt.map α).toRingHom.comp ψM.1) (w : CotangentSpace R) :
    ringHomEquivCotangentLinear baseMap ε hε e he ψN w =
      α (ringHomEquivCotangentLinear baseMap ε hε e he ψM w) := by
  obtain ⟨m, rfl⟩ := (maximalIdeal R).toCotangent_surjective w
  rw [ringHomEquivCotangentLinear_toCotangent, ringHomEquivCotangentLinear_toCotangent, hψ,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.snd_map]

/-- Functoriality of `ringHomEquivCotangentLinear` along a local ring homomorphism composed with a
ring isomorphism, stated for abstract local rings so `rw` never inspects scheme stalks. -/
private lemma ringHomEquivCotangentLinear_comp_zariski
    {R₂ R₃ : Type u} [CommRing R₂] [IsLocalRing R₂] [CommRing R₃] [IsLocalRing R₃]
    (ι₁ : K →+* R) (ε₁ : R →+* K) [IsLocalHom ε₁] (hε₁ : ∀ c, ε₁ (ι₁ c) = c)
    (e₁ : ResidueField R ≃+* K) (he₁ : ∀ r, e₁ (residue R r) = ε₁ r)
    (ι₃ : K →+* R₃) (ε₃ : R₃ →+* K) [IsLocalHom ε₃] (hε₃ : ∀ c, ε₃ (ι₃ c) = c)
    (e₃ : ResidueField R₃ ≃+* K) (he₃ : ∀ r, e₃ (residue R₃ r) = ε₃ r)
    (g : R₂ →+* R) [IsLocalHom g] (iso : R₃ ≃+* R₂)
    (ψ₁ : {ψ : R →+* TrivSqZeroExt K M //
      ψ.comp ι₁ = algebraMap K (TrivSqZeroExt K M) ∧
        (TrivSqZeroExt.fstHom K K M).toRingHom.comp ψ = ε₁})
    (ψ₃ : {ψ : R₃ →+* TrivSqZeroExt K M //
      ψ.comp ι₃ = algebraMap K (TrivSqZeroExt K M) ∧
        (TrivSqZeroExt.fstHom K K M).toRingHom.comp ψ = ε₃})
    (hψ : ψ₃.1 = ψ₁.1.comp (g.comp iso.toRingHom)) (w : CotangentSpace R₃) :
    ringHomEquivCotangentLinear ι₃ ε₃ hε₃ e₃ he₃ ψ₃ w =
      ringHomEquivCotangentLinear ι₁ ε₁ hε₁ e₁ he₁ ψ₁
        (CotangentSpace.map g (CotangentSpace.mapEquiv iso w)) := by
  obtain ⟨m, rfl⟩ := (maximalIdeal R₃).toCotangent_surjective w
  rw [CotangentSpace.mapEquiv_apply, CotangentSpace.map_toCotangent,
    CotangentSpace.map_toCotangent, ringHomEquivCotangentLinear_toCotangent,
    ringHomEquivCotangentLinear_toCotangent, hψ]
  rfl

end LocalRingLift

section TrivSqZero

variable (K M : Type u) [Field K] [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M]
  [IsCentralScalar K M]

/-- `Spec (TrivSqZeroExt K M)` viewed as a scheme over `Spec K`. -/
noncomputable abbrev trivSqZeroOver : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K M))))

/-- The canonical `K`-rational section `Spec K ⟶ Spec (TrivSqZeroExt K M)` over `Spec K` induced
by the projection `TrivSqZeroExt.fstHom K K M`. -/
noncomputable def trivSqZeroSection : 𝟙_ (Over (Spec (.of K))) ⟶ trivSqZeroOver K M :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom)) <| by
    have h : CommRingCat.ofHom
        ((TrivSqZeroExt.fstHom K K M).toRingHom.comp (algebraMap K (TrivSqZeroExt K M))) =
        𝟙 (CommRingCat.of K) := by
      ext c
      exact (TrivSqZeroExt.fstHom K K M).commutes c
    -- Unfold `(trivSqZeroOver K M).hom` to `Spec.map` of `algebraMap` without unfolding `fstHom`.
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h, Spec.map_id, Over.tensorUnit_hom]

/-- Underlying scheme morphism of `trivSqZeroSection K M`. -/
@[simp]
theorem trivSqZeroSection_left :
    (trivSqZeroSection K M).left =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom) :=
  (rfl)

variable {K M}

/-- Contravariant functoriality of `trivSqZeroOver K M` in the `K`-module `M`. -/
noncomputable def trivSqZeroOverMap {N : Type u} [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N]
    [IsCentralScalar K N] (α : M →ₗ[K] N) :
    trivSqZeroOver K N ⟶ trivSqZeroOver K M :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map α).toRingHom)) <| by
    -- Unfold `.hom` of `trivSqZeroOver` to `Spec.map` of `algebraMap`.
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ (TrivSqZeroExt.map α).commutes c

/-- Underlying scheme morphism of `trivSqZeroOverMap α`. -/
@[simp]
theorem trivSqZeroOverMap_left {N : Type u} [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N]
    [IsCentralScalar K N] (α : M →ₗ[K] N) :
    (trivSqZeroOverMap α).left =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map α).toRingHom) :=
  (rfl)

/-- `trivSqZeroOverMap` sends the identity linear map to the identity morphism. -/
@[simp]
theorem trivSqZeroOverMap_id :
    trivSqZeroOverMap (LinearMap.id : M →ₗ[K] M) = 𝟙 (trivSqZeroOver K M) := by
  apply Over.OverMorphism.ext
  rw [trivSqZeroOverMap_left, Over.id_left]
  simp

/-- `trivSqZeroOverMap` reverses composition of `K`-linear maps. -/
@[simp, reassoc]
theorem trivSqZeroOverMap_comp {L N : Type u} [AddCommGroup L] [Module K L] [Module Kᵐᵒᵖ L]
    [IsCentralScalar K L] [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N] [IsCentralScalar K N]
    (α : L →ₗ[K] M) (β : M →ₗ[K] N) :
    trivSqZeroOverMap (β.comp α) = trivSqZeroOverMap β ≫ trivSqZeroOverMap α := by
  apply Over.OverMorphism.ext
  rw [trivSqZeroOverMap_left, Over.comp_left, trivSqZeroOverMap_left, trivSqZeroOverMap_left,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext z <;> simp

/-- `trivSqZeroOverMap` commutes with the canonical sections `trivSqZeroSection`. -/
@[simp, reassoc]
theorem trivSqZeroSection_overMap {N : Type u} [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N]
    [IsCentralScalar K N] (α : M →ₗ[K] N) :
    trivSqZeroSection K N ≫ trivSqZeroOverMap α = trivSqZeroSection K M := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, trivSqZeroSection_left, trivSqZeroOverMap_left, trivSqZeroSection_left,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext z
  simp

/-- The zero linear map induces the morphism factoring through the base `Spec K` and the canonical
section. -/
theorem trivSqZeroOverMap_zero {N : Type u} [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N]
    [IsCentralScalar K N] :
    trivSqZeroOverMap (0 : M →ₗ[K] N) =
      toUnit (trivSqZeroOver K N) ≫ trivSqZeroSection K M := by
  apply Over.OverMorphism.ext
  rw [trivSqZeroOverMap_left, Over.comp_left, Over.toUnit_left, trivSqZeroSection_left]
  -- Unfold `(trivSqZeroOver K N).hom` to `Spec.map` of `algebraMap`.
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext z <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

end TrivSqZero

section PointedEquiv

variable {K : Type u} [Field K]

/-- The underlying scheme morphism `Spec K ⟶ X.left` of a `K`-rational section
`s : 𝟙_ (Over (Spec (.of K))) ⟶ X`. Typing the domain as `Spec (.of K)` rather than
`(𝟙_ (Over (Spec (.of K)))).left` keeps applications to `closedPoint K` type-correct at `implicit`
transparency. -/
noncomputable abbrev overSectionHom {X : Over (Spec (.of K))}
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ X) : Spec (.of K) ⟶ X.left :=
  s.left

/-- Every morphism `s : 𝟙_ (Over (Spec (.of K))) ⟶ X` is a section of `X.hom`. -/
theorem overSection_comp_hom {X : Over (Spec (.of K))} (s : 𝟙_ (Over (Spec (.of K))) ⟶ X) :
    overSectionHom s ≫ X.hom = 𝟙 (Spec (.of K)) :=
  (Over.w s).trans Over.tensorUnit_hom

/-- `fromSpecStalk` composed with `X.hom` is `Spec.map` of `Scheme.baseRingToStalk`. -/
private lemma fromSpecStalk_comp_hom (X : Over (Spec (.of K))) (x : X.left) :
    X.left.fromSpecStalk x ≫ X.hom =
      Spec.map (CommRingCat.ofHom (Scheme.baseRingToStalk K X.left x)) :=
  X.left.fromSpecStalk_comp_over (k := K) x

/-- Composing `Spec.map` of `stalkCongr` with `fromSpecStalk` shifts the base point. Written with
`Eq.trans` so `nhds ≤ nhds` inside `stalkCongr_hom` is never inspected by `rw`. -/
private lemma specMap_stalkCongr_fromSpecStalk {X : Scheme.{u}} {x y : X} (h : x = y) :
    Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ X.fromSpecStalk x =
      X.fromSpecStalk y :=
  (congrArg (Spec.map · ≫ X.fromSpecStalk x)
    (TopCat.Presheaf.stalkCongr_hom X.presheaf (Inseparable.of_eq h))).trans
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk _)

/-- Composing `Spec.map` of a stalk isomorphism and `stalkClosedPointTo f` with `fromSpecStalk`
recovers `f`. Written with `Eq.trans` so `closedPoint` is never inspected by `rw`. -/
private lemma specMap_stalkCongr_stalkClosedPointTo {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : Spec (.of R) ⟶ X) {x : X} (hx : x = f (closedPoint R)) :
    Spec.map ((X.presheaf.stalkCongr (Inseparable.of_eq hx)).hom ≫
        Scheme.stalkClosedPointTo f) ≫ X.fromSpecStalk x = f :=
  (congrArg (· ≫ X.fromSpecStalk x) (Spec.map_comp _ _)).trans <|
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (specMap_stalkCongr_fromSpecStalk hx)).trans
        (Scheme.Spec_stalkClosedPointTo_fromSpecStalk f)

/-- Compatibility of stalk morphisms in `CommRingCat` from compatibility with `fromSpecStalk` along
a morphism `f : X ⟶ Y`, stated for general scheme points `x : X` and `y : Y` with `y = f x`. -/
private lemma stalkMap_comp_of_fromSpecStalk {X Y : Scheme.{u}} {f : X ⟶ Y}
    {x : X} {y : Y} (e : y = f x) {S : Type u} [CommRing S]
    {ψX : X.presheaf.stalk x ⟶ CommRingCat.of S}
    {ψY : Y.presheaf.stalk y ⟶ CommRingCat.of S}
    (h : Spec.map ψY ≫ Y.fromSpecStalk y = (Spec.map ψX ≫ X.fromSpecStalk x) ≫ f) :
    ψY = (Y.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ f.stalkMap x ≫ ψX := by
  rw [← Spec.map_inj, ← cancel_mono (Y.fromSpecStalk y), h, Category.assoc,
    Spec.map_comp_assoc, Spec.map_comp_assoc, specMap_stalkCongr_fromSpecStalk e,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The projection `TrivSqZeroExt K M →+* K` is a local ring homomorphism. -/
private instance isLocalHom_fstHom (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M]
    [IsCentralScalar K M] : IsLocalHom (TrivSqZeroExt.fstHom K K M).toRingHom :=
  ⟨fun _ hz ↦ TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hz⟩

/-- At a `K`-rational section `s`, the stalk evaluation `Scheme.stalkClosedPointTo`
acts as the identity on `K` via `Scheme.baseRingToStalk`. -/
private lemma stalkClosedPointTo_baseRingToStalk {X : Over (Spec (.of K))}
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ X) (c : K) :
    Scheme.stalkClosedPointTo (overSectionHom s)
        (Scheme.baseRingToStalk K X.left (overSectionHom s (closedPoint K)) c) = c := by
  have h : Spec.map (CommRingCat.ofHom
      (Scheme.baseRingToStalk K X.left (overSectionHom s (closedPoint K))) ≫
        Scheme.stalkClosedPointTo (overSectionHom s)) = Spec.map (𝟙 (CommRingCat.of K)) :=
    (Spec.map_comp _ _).trans <|
      (congrArg (_ ≫ ·) (fromSpecStalk_comp_hom X _).symm).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ X.hom) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)).trans <|
            (overSection_comp_hom s).trans (Spec.map_id _).symm
  exact congr($(Spec.map_injective h) c)

/-- At a `K`-rational section `s`, `residueFieldRingEquivOfSection` on `residue _ r` agrees with
`Scheme.stalkClosedPointTo`. -/
private lemma residueFieldRingEquivOfSection_residue {X : Over (Spec (.of K))}
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ X)
    (r : X.left.presheaf.stalk (overSectionHom s (closedPoint K))) :
    residueFieldRingEquivOfSection (overSection_comp_hom s) (residue _ r) =
      Scheme.stalkClosedPointTo (overSectionHom s) r :=
  (residueFieldRingEquivOfSection_apply (overSection_comp_hom s) _).trans
    congr($(X.left.residue_descResidueField (Scheme.stalkClosedPointTo (overSectionHom s))) r)

/-- Any morphism `t : trivSqZeroOver K M ⟶ X` extending `s` sends the closed point of
`TrivSqZeroExt K M` to the base point of `s`. -/
private lemma pointedOver_closedPoint_eq {X : Over (Spec (.of K))}
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ X) {M : Type u} [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M] {t : trivSqZeroOver K M ⟶ X}
    (ht : trivSqZeroSection K M ≫ t = s) :
    t.left (closedPoint (TrivSqZeroExt K M)) = overSectionHom s (closedPoint K) :=
  let fstCatHom : CommRingCat.of (TrivSqZeroExt K M) ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom
  have : IsLocalHom fstCatHom.hom := isLocalHom_fstHom M
  let secHom : Spec (.of K) ⟶ Spec (.of (TrivSqZeroExt K M)) := (trivSqZeroSection K M).left
  (congrArg t.left (Spec_closedPoint (f := fstCatHom)).symm).trans <|
    (Scheme.Hom.comp_apply secHom t.left (closedPoint K)).symm.trans
      congr($(congrArg overSectionHom ht) (closedPoint K))

/-- Build a pointed morphism `trivSqZeroOver K M ⟶ X` extending `s` from a `K`-compatible stalk
morphism in `CommRingCat`. -/
private noncomputable def pointedOverOfStalkHom (X : Over (Spec (.of K)))
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ X) (M : Type u) [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    (ψ : {ψ : X.left.presheaf.stalk (overSectionHom s (closedPoint K)) ⟶
        CommRingCat.of (TrivSqZeroExt K M) //
      CommRingCat.ofHom (Scheme.baseRingToStalk K X.left (overSectionHom s (closedPoint K))) ≫
          ψ = CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K M)) ∧
        ψ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom =
          Scheme.stalkClosedPointTo (overSectionHom s)}) :
    {t : trivSqZeroOver K M ⟶ X // trivSqZeroSection K M ≫ t = s} :=
  ⟨Over.homMk (Spec.map ψ.1 ≫ X.left.fromSpecStalk (overSectionHom s (closedPoint K)))
      (((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (fromSpecStalk_comp_hom X _))).trans <|
        (Spec.map_comp _ _).symm.trans (congrArg Spec.map ψ.2.1)),
    Over.OverMorphism.ext <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _) (Spec.map_comp _ _).symm).trans <|
          (congrArg (fun u ↦ Spec.map u ≫ _) ψ.2.2).trans
            (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)⟩

/-- First half of `trivSqZeroPointEquiv`: pointed morphisms `trivSqZeroOver K M ⟶ X` over `s`
correspond to `K`-compatible stalk morphisms in `CommRingCat` lifting
`Scheme.stalkClosedPointTo`. -/
private noncomputable def pointedOverEquivStalkHom (X : Over (Spec (.of K)))
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ X) (M : Type u) [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    {t : trivSqZeroOver K M ⟶ X // trivSqZeroSection K M ≫ t = s} ≃
      {ψ : X.left.presheaf.stalk (overSectionHom s (closedPoint K)) ⟶
          CommRingCat.of (TrivSqZeroExt K M) //
        CommRingCat.ofHom (Scheme.baseRingToStalk K X.left (overSectionHom s (closedPoint K))) ≫
            ψ = CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K M)) ∧
          ψ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom =
            Scheme.stalkClosedPointTo (overSectionHom s)} where
  toFun := fun ⟨t, ht⟩ ↦
    let hpt := pointedOver_closedPoint_eq s ht
    let ψc := (X.left.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom ≫
      Scheme.stalkClosedPointTo t.left
    have hSpec : Spec.map ψc ≫ X.left.fromSpecStalk (overSectionHom s (closedPoint K)) = t.left :=
      specMap_stalkCongr_stalkClosedPointTo t.left hpt.symm
    ⟨ψc,
      ⟨Spec.map_injective <|
          (Spec.map_comp _ _).trans <|
            (congrArg (_ ≫ ·) (fromSpecStalk_comp_hom X _).symm).trans <|
              (Category.assoc _ _ _).symm.trans <|
                (congrArg (· ≫ X.hom) hSpec).trans (Over.w t),
        Spec.map_injective <| (cancel_mono (X.left.fromSpecStalk _)).mp <|
          ((congrArg (· ≫ _) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans <|
            (congrArg (_ ≫ ·) hSpec).trans <|
              (congrArg overSectionHom ht).trans
                (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).symm⟩⟩
  invFun := pointedOverOfStalkHom X s M
  left_inv := fun ⟨t, ht⟩ ↦
    Subtype.ext <| Over.OverMorphism.ext <|
      specMap_stalkCongr_stalkClosedPointTo t.left (pointedOver_closedPoint_eq s ht).symm
  right_inv ψ := Subtype.ext <|
    Spec.map_injective <| (cancel_mono (X.left.fromSpecStalk _)).mp <|
      specMap_stalkCongr_stalkClosedPointTo (pointedOverOfStalkHom X s M ψ).1.left
        (pointedOver_closedPoint_eq s (pointedOverOfStalkHom X s M ψ).2).symm

private lemma pointedOverEquivStalkHom_specMap (X : Over (Spec (.of K)))
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ X) (M : Type u) [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    (t : {t : trivSqZeroOver K M ⟶ X // trivSqZeroSection K M ≫ t = s}) :
    Spec.map (pointedOverEquivStalkHom X s M t).1 ≫
      X.left.fromSpecStalk (overSectionHom s (closedPoint K)) = t.1.left :=
  specMap_stalkCongr_stalkClosedPointTo t.1.left (pointedOver_closedPoint_eq s t.2).symm

/-- Equivalence between compatible `CommRingCat` morphisms `R ⟶ .of S` and `RingHom`s `R →+* S`. -/
private def commRingCatLiftEquiv {R : CommRingCat.{u}} {S : Type u} [CommRing S]
    (baseMap : K →+* R) (g : K →+* S) {T : Type u} [CommRing T] (f : S →+* T)
    (ε : R ⟶ CommRingCat.of T) :
    {ψ : R ⟶ CommRingCat.of S //
      CommRingCat.ofHom baseMap ≫ ψ = CommRingCat.ofHom g ∧ ψ ≫ CommRingCat.ofHom f = ε} ≃
      {ψ : (R : Type u) →+* S // ψ.comp baseMap = g ∧ f.comp ψ = ε.hom} where
  toFun := fun ⟨ψ, h1, h2⟩ ↦
    ⟨ψ.hom, ⟨congrArg CommRingCat.Hom.hom h1, congrArg CommRingCat.Hom.hom h2⟩⟩
  invFun := fun ⟨ψ, h1, h2⟩ ↦
    ⟨CommRingCat.ofHom ψ, ⟨CommRingCat.hom_ext h1, CommRingCat.hom_ext h2⟩⟩
  left_inv := fun ⟨_, _, _⟩ ↦ Subtype.ext (CommRingCat.hom_ext rfl)
  right_inv := fun ⟨_, _, _⟩ ↦ Subtype.ext rfl

/-- Pointed morphisms `trivSqZeroOver K M ⟶ X` extending `s` correspond to `K`-compatible ring
homomorphisms out of the stalk at `s`. -/
private noncomputable def pointedOverEquivRingHom (X : Over (Spec (.of K)))
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ X) (M : Type u) [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    {t : trivSqZeroOver K M ⟶ X // trivSqZeroSection K M ≫ t = s} ≃
      {ψ : (X.left.presheaf.stalk (overSectionHom s (closedPoint K)) : Type u) →+*
          TrivSqZeroExt K M //
        ψ.comp (Scheme.baseRingToStalk K X.left (overSectionHom s (closedPoint K))) =
            algebraMap K (TrivSqZeroExt K M) ∧
          (TrivSqZeroExt.fstHom K K M).toRingHom.comp ψ =
            (Scheme.stalkClosedPointTo (overSectionHom s)).hom} :=
  (pointedOverEquivStalkHom X s M).trans
    (commRingCatLiftEquiv (R := X.left.presheaf.stalk (overSectionHom s (closedPoint K)))
      (Scheme.baseRingToStalk K X.left (overSectionHom s (closedPoint K)))
      (algebraMap K (TrivSqZeroExt K M))
      (TrivSqZeroExt.fstHom K K M).toRingHom
      (Scheme.stalkClosedPointTo (overSectionHom s)))

/-- **Infinitesimal points and Zariski cotangent functionals.** For any scheme `X` over `Spec K`,
any `K`-rational section `s : 𝟙_ (Over (Spec (.of K))) ⟶ X`, and any symmetric `K`-bimodule `M`,
morphisms `trivSqZeroOver K M ⟶ X` over `Spec K` extending `s` correspond canonically to
semilinear functionals `ZariskiCotangentSpace X.left (overSectionHom s (closedPoint K)) → M`. -/
noncomputable def trivSqZeroPointEquiv (X : Over (Spec (.of K)))
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ X) (M : Type u) [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    {t : trivSqZeroOver K M ⟶ X // trivSqZeroSection K M ≫ t = s} ≃
      (ZariskiCotangentSpace X.left (overSectionHom s (closedPoint K)) →ₛₗ[
        (residueFieldRingEquivOfSection (overSection_comp_hom s)).toRingHom] M) :=
  (pointedOverEquivRingHom X s M).trans <|
    ringHomEquivCotangentLinear
      (Scheme.baseRingToStalk K X.left (overSectionHom s (closedPoint K)))
      (Scheme.stalkClosedPointTo (overSectionHom s)).hom
      (stalkClosedPointTo_baseRingToStalk s)
      (residueFieldRingEquivOfSection (overSection_comp_hom s))
      (residueFieldRingEquivOfSection_residue s)

/-- Functoriality of `trivSqZeroPointEquiv` in the `K`-module `M`: precomposing an infinitesimal
point with `trivSqZeroOverMap α` postcomposes its cotangent functional with `α`. -/
theorem trivSqZeroPointEquiv_overMap {X : Over (Spec (.of K))}
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ X) {M N : Type u} [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M] [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N]
    [IsCentralScalar K N] (α : M →ₗ[K] N)
    (t : {t : trivSqZeroOver K M ⟶ X // trivSqZeroSection K M ≫ t = s})
    (w : ZariskiCotangentSpace X.left (overSectionHom s (closedPoint K))) :
    trivSqZeroPointEquiv X s N
        ⟨trivSqZeroOverMap α ≫ t.1, by rw [trivSqZeroSection_overMap_assoc, t.2]⟩ w =
      α (trivSqZeroPointEquiv X s M t w) := by
  let tN : {t : trivSqZeroOver K N ⟶ X // trivSqZeroSection K N ≫ t = s} :=
    ⟨trivSqZeroOverMap α ≫ t.1, by rw [trivSqZeroSection_overMap_assoc, t.2]⟩
  have hM := pointedOverEquivStalkHom_specMap X s M t
  have hN := pointedOverEquivStalkHom_specMap X s N tN
  have hψc : (pointedOverEquivStalkHom X s N tN).1 =
      (pointedOverEquivStalkHom X s M t).1 ≫
        CommRingCat.ofHom (TrivSqZeroExt.map α).toRingHom :=
    Spec.map_injective <| (cancel_mono (X.left.fromSpecStalk _)).mp <|
      hN.trans <| (congrArg ((trivSqZeroOverMap α).left ≫ ·) hM.symm).trans <|
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ X.left.fromSpecStalk _) (Spec.map_comp _ _).symm)
  exact ringHomEquivCotangentLinear_overMap
    (Scheme.baseRingToStalk K X.left (overSectionHom s (closedPoint K)))
    (Scheme.stalkClosedPointTo (overSectionHom s)).hom
    (stalkClosedPointTo_baseRingToStalk s)
    (residueFieldRingEquivOfSection (overSection_comp_hom s))
    (residueFieldRingEquivOfSection_residue s) α
    (pointedOverEquivRingHom X s M t) (pointedOverEquivRingHom X s N tN)
    ((congrArg CommRingCat.Hom.hom hψc).trans (CommRingCat.hom_comp _ _)) w

/-- Functoriality of `trivSqZeroPointEquiv` in `(X, s)`: postcomposing an infinitesimal point with
`φ : X ⟶ Y` precomposes its cotangent functional with `φ.left.zariskiCotangentMap`. -/
theorem trivSqZeroPointEquiv_comp {X Y : Over (Spec (.of K))}
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ X) (φ : X ⟶ Y) {M : Type u} [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    (t : {t : trivSqZeroOver K M ⟶ X // trivSqZeroSection K M ≫ t = s})
    (w : ZariskiCotangentSpace Y.left (overSectionHom (s ≫ φ) (closedPoint K))) :
    trivSqZeroPointEquiv Y (s ≫ φ) M ⟨t.1 ≫ φ, by rw [← Category.assoc, t.2]⟩ w =
      trivSqZeroPointEquiv X s M t
        (φ.left.zariskiCotangentMap (overSectionHom s (closedPoint K))
          (CotangentSpace.mapEquiv (Y.left.presheaf.stalkCongr
            (Inseparable.of_eq (Scheme.Hom.comp_apply (overSectionHom s) φ.left
              (closedPoint K)))).commRingCatIsoToRingEquiv w)) := by
  let e : overSectionHom (s ≫ φ) (closedPoint K) =
      φ.left (overSectionHom s (closedPoint K)) :=
    Scheme.Hom.comp_apply (overSectionHom s) φ.left (closedPoint K)
  let tY : {t : trivSqZeroOver K M ⟶ Y // trivSqZeroSection K M ≫ t = s ≫ φ} :=
    ⟨t.1 ≫ φ, by rw [← Category.assoc, t.2]⟩
  have hX := pointedOverEquivStalkHom_specMap X s M t
  have hY := pointedOverEquivStalkHom_specMap Y (s ≫ φ) M tY
  have hψc := stalkMap_comp_of_fromSpecStalk e (hY.trans (congrArg (· ≫ φ.left) hX.symm))
  exact ringHomEquivCotangentLinear_comp_zariski
    (Scheme.baseRingToStalk K X.left (overSectionHom s (closedPoint K)))
    (Scheme.stalkClosedPointTo (overSectionHom s)).hom
    (stalkClosedPointTo_baseRingToStalk s)
    (residueFieldRingEquivOfSection (overSection_comp_hom s))
    (residueFieldRingEquivOfSection_residue s)
    (Scheme.baseRingToStalk K Y.left (overSectionHom (s ≫ φ) (closedPoint K)))
    (Scheme.stalkClosedPointTo (overSectionHom (s ≫ φ))).hom
    (stalkClosedPointTo_baseRingToStalk (s ≫ φ))
    (residueFieldRingEquivOfSection (overSection_comp_hom (s ≫ φ)))
    (residueFieldRingEquivOfSection_residue (s ≫ φ))
    (φ.left.stalkMap (overSectionHom s (closedPoint K))).hom
    (Y.left.presheaf.stalkCongr (Inseparable.of_eq e)).commRingCatIsoToRingEquiv
    (pointedOverEquivRingHom X s M t) (pointedOverEquivRingHom Y (s ≫ φ) M tY)
    (RingHom.ext fun r ↦ congr($(congrArg CommRingCat.Hom.hom hψc) r)) w

/-- Variant of `trivSqZeroPointEquiv_comp` for an explicit target section `sY` satisfying
`sX ≫ φ = sY`. -/
theorem trivSqZeroPointEquiv_comp_of_eq {X Y : Over (Spec (.of K))}
    (sX : 𝟙_ (Over (Spec (.of K))) ⟶ X) (sY : 𝟙_ (Over (Spec (.of K))) ⟶ Y)
    (φ : X ⟶ Y) (hs : sX ≫ φ = sY) {M : Type u} [AddCommGroup M] [Module K M]
    [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    (t : {t : trivSqZeroOver K M ⟶ X // trivSqZeroSection K M ≫ t = sX})
    (w : ZariskiCotangentSpace Y.left (overSectionHom sY (closedPoint K))) :
    trivSqZeroPointEquiv Y sY M ⟨t.1 ≫ φ, by rw [← Category.assoc, t.2, hs]⟩ w =
      trivSqZeroPointEquiv X sX M t
        (φ.left.zariskiCotangentMap (overSectionHom sX (closedPoint K))
          (CotangentSpace.mapEquiv (Y.left.presheaf.stalkCongr
            (Inseparable.of_eq (congr($(congrArg overSectionHom hs.symm) (closedPoint K)).trans
              (Scheme.Hom.comp_apply (overSectionHom sX) φ.left
                (closedPoint K))))).commRingCatIsoToRingEquiv w)) := by
  subst hs
  exact trivSqZeroPointEquiv_comp sX φ t w

/-- The unit section `η[G]` is the multiplicative identity of `𝟙_ (Over (Spec (.of K))) ⟶ G`. -/
private lemma unit_eq_one (G : Over (Spec (.of K))) [GrpObj G] :
    η[G] = (1 : 𝟙_ (Over (Spec (.of K))) ⟶ G) := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

/-- The constant infinitesimal point `toUnit (trivSqZeroOver K M) ≫ η[G]` at the identity of a
group scheme corresponds to the zero cotangent functional. -/
theorem trivSqZeroPointEquiv_one (G : Over (Spec (.of K))) [GrpObj G] (M : Type u)
    [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    trivSqZeroPointEquiv G η[G] M
      ⟨(1 : trivSqZeroOver K M ⟶ G), by
        rw [Hom.one_def, ← Category.assoc,
          toUnit_unique (trivSqZeroSection K M ≫ toUnit _) (𝟙 _), Category.id_comp]⟩ = 0 := by
  let onePt : {t : trivSqZeroOver K M ⟶ G // trivSqZeroSection K M ≫ t = η[G]} :=
    ⟨1, by
      rw [Hom.one_def, ← Category.assoc,
        toUnit_unique (trivSqZeroSection K M ≫ toUnit _) (𝟙 _), Category.id_comp]⟩
  ext w
  have hone : onePt.1 = trivSqZeroOverMap (0 : M →ₗ[K] M) ≫ onePt.1 := by
    dsimp [onePt]
    rw [trivSqZeroOverMap_zero, Hom.one_def, ← Category.assoc,
      toUnit_unique ((toUnit (trivSqZeroOver K M) ≫ trivSqZeroSection K M) ≫ toUnit _) (toUnit _)]
  let zeroMapPt : {t : trivSqZeroOver K M ⟶ G // trivSqZeroSection K M ≫ t = η[G]} :=
    ⟨trivSqZeroOverMap (0 : M →ₗ[K] M) ≫ onePt.1, by rw [trivSqZeroSection_overMap_assoc, onePt.2]⟩
  exact (congrArg (fun u ↦ trivSqZeroPointEquiv G η[G] M u w)
    (Subtype.ext hone : onePt = zeroMapPt)).trans
      ((trivSqZeroPointEquiv_overMap η[G] (0 : M →ₗ[K] M) onePt w).trans (LinearMap.zero_apply _))

/-- **Stacks Project, Tag 0BFG.** For any group scheme `G` over `Spec K` and any symmetric
`K`-bimodule `M`, multiplying two `Spec (TrivSqZeroExt K M)`-points of `G` lying over `η[G]`
adds their induced Zariski cotangent functionals. -/
@[stacks 0BFG]
theorem trivSqZeroPointEquiv_mul (G : Over (Spec (.of K))) [GrpObj G] {M : Type u}
    [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    (t₁ t₂ : {t : trivSqZeroOver K M ⟶ G // trivSqZeroSection K M ≫ t = η[G]}) :
    trivSqZeroPointEquiv G η[G] M
      ⟨t₁.1 * t₂.1, by
        rw [MonObj.comp_mul, t₁.2, t₂.2, unit_eq_one G, _root_.mul_one]⟩ =
      trivSqZeroPointEquiv G η[G] M t₁ + trivSqZeroPointEquiv G η[G] M t₂ := by
  let inlL : M →ₗ[K] M × M := LinearMap.inl K M M
  let inrL : M →ₗ[K] M × M := LinearMap.inr K M M
  let fstL : M × M →ₗ[K] M := LinearMap.fst K M M
  let sndL : M × M →ₗ[K] M := LinearMap.snd K M M
  let addL : M × M →ₗ[K] M := LinearMap.coprod LinearMap.id LinearMap.id
  have hunit (u : {t : trivSqZeroOver K M ⟶ G // trivSqZeroSection K M ≫ t = η[G]}) :
      trivSqZeroOverMap (0 : M →ₗ[K] M) ≫ u.1 = 1 := by
    rw [trivSqZeroOverMap_zero, Category.assoc, u.2, ← Hom.one_def]
  let T : {t : trivSqZeroOver K (M × M) ⟶ G // trivSqZeroSection K (M × M) ≫ t = η[G]} :=
    ⟨(trivSqZeroOverMap inlL ≫ t₁.1) * (trivSqZeroOverMap inrL ≫ t₂.1), by
      rw [MonObj.comp_mul, trivSqZeroSection_overMap_assoc, t₁.2,
        trivSqZeroSection_overMap_assoc, t₂.2, unit_eq_one G, _root_.mul_one]⟩
  have hfst : trivSqZeroOverMap fstL ≫ T.1 = t₁.1 := by
    dsimp [T]
    rw [MonObj.comp_mul, ← trivSqZeroOverMap_comp_assoc, ← trivSqZeroOverMap_comp_assoc,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, trivSqZeroOverMap_id, Category.id_comp,
      hunit t₂, _root_.mul_one]
  have hsnd : trivSqZeroOverMap sndL ≫ T.1 = t₂.1 := by
    dsimp [T]
    rw [MonObj.comp_mul, ← trivSqZeroOverMap_comp_assoc, ← trivSqZeroOverMap_comp_assoc,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, trivSqZeroOverMap_id, Category.id_comp,
      hunit t₁, _root_.one_mul]
  have hadd : trivSqZeroOverMap addL ≫ T.1 = t₁.1 * t₂.1 := by
    dsimp [T, addL]
    rw [MonObj.comp_mul, ← trivSqZeroOverMap_comp_assoc, ← trivSqZeroOverMap_comp_assoc,
      LinearMap.coprod_inl, LinearMap.coprod_inr, trivSqZeroOverMap_id, Category.id_comp,
      Category.id_comp]
  let prodPt : {t : trivSqZeroOver K M ⟶ G // trivSqZeroSection K M ≫ t = η[G]} :=
    ⟨t₁.1 * t₂.1, by rw [MonObj.comp_mul, t₁.2, t₂.2, unit_eq_one G, _root_.mul_one]⟩
  let addPt : {t : trivSqZeroOver K M ⟶ G // trivSqZeroSection K M ≫ t = η[G]} :=
    ⟨trivSqZeroOverMap addL ≫ T.1, by rw [trivSqZeroSection_overMap_assoc, T.2]⟩
  let fstPt : {t : trivSqZeroOver K M ⟶ G // trivSqZeroSection K M ≫ t = η[G]} :=
    ⟨trivSqZeroOverMap fstL ≫ T.1, by rw [trivSqZeroSection_overMap_assoc, T.2]⟩
  let sndPt : {t : trivSqZeroOver K M ⟶ G // trivSqZeroSection K M ≫ t = η[G]} :=
    ⟨trivSqZeroOverMap sndL ≫ T.1, by rw [trivSqZeroSection_overMap_assoc, T.2]⟩
  ext w
  have hw_add := (congrArg (fun u ↦ trivSqZeroPointEquiv G η[G] M u w)
    (Subtype.ext hadd.symm : prodPt = addPt)).trans (trivSqZeroPointEquiv_overMap η[G] addL T w)
  have hw_fst := (congrArg (fun u ↦ trivSqZeroPointEquiv G η[G] M u w)
    (Subtype.ext hfst.symm : t₁ = fstPt)).trans (trivSqZeroPointEquiv_overMap η[G] fstL T w)
  have hw_snd := (congrArg (fun u ↦ trivSqZeroPointEquiv G η[G] M u w)
    (Subtype.ext hsnd.symm : t₂ = sndPt)).trans (trivSqZeroPointEquiv_overMap η[G] sndL T w)
  exact (hw_add.trans ((LinearMap.coprod_apply _ _ _).trans
    (congrArg₂ (· + ·) hw_fst.symm hw_snd.symm))).trans (LinearMap.add_apply _ _ _).symm

end PointedEquiv

end TauCeti.AlgebraicGeometry
