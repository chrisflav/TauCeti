/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import TauCeti.Algebra.Category.ModuleCat.Topology.RestrictScalars
public import TauCeti.RepresentationTheory.Continuous.RestrictScalars.Basic

/-!
# Forgetting the scalars of a topological representation

A continuous representation of a monoid `G` on a topological `R`-module `V` is in particular a
continuous representation on the underlying topological abelian group, that is on `V` as a
topological `ℤ`-module for the canonical action of `ℤ`, because every operator is additive and
continuous. Using `ContRepresentation.restrictScalars ℤ` and
`ContIntertwiningMap.restrictScalars ℤ`, this file packages that observation as the functor
`TopRep.restrictScalarsInt : TopRep k G ⥤ TopRep ℤ G` on the category of topological
representations. It then records that the two functors from which Mathlib builds continuous
cohomology, the coinduction `TopRep.coind₁Functor` and the invariants `TopRep.invariantsFunctor`,
commute with forgetting the scalars: the coinduced representation of the underlying additive
representation is the underlying additive representation of the coinduced one, on the nose on the
function space `C(G, V)`, and the invariants of the underlying additive representation are the
underlying topological abelian group of the invariants.

The reason for stopping at `ℤ` is explained in
`TauCeti.Algebra.Category.ModuleCat.Topology.RestrictScalars`: only the canonical `ℤ`-module
structure exists on every topological module without a choice.

## Main definitions

* `TopRep.restrictScalarsInt`: the functor `TopRep k G ⥤ TopRep ℤ G` forgetting the scalars.
* `TopRep.coind₁RestrictScalarsIntIso`: coinduction commutes with forgetting the scalars.
* `TopRep.invariantsRestrictScalarsIntIso`: taking invariants commutes with forgetting the
  scalars.

## Main results

* `TopRep.coind₁ι_comp_coind₁RestrictScalarsIntIso_hom` and
  `TopRep.coind₁Functor_map_comp_coind₁RestrictScalarsIntIso_hom`: the identification of the
  coinduced representations is compatible with the unit `TopRep.coind₁ι` and with the maps
  induced by `TopRep.coind₁Functor`.
* `TopRep.invariantsRestrictScalarsIntIso_hom_comp_map`: the identification of the invariants is
  compatible with the maps induced by `TopRep.invariantsFunctor`.
-/

public section

open CategoryTheory ContRepresentation

namespace TopRep

/-! ### The functor on topological representations -/

section Monoid

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Monoid G]

/-- Forgetting the scalars of a topological representation: the functor `TopRep k G ⥤ TopRep ℤ G`
sending a representation on a topological `k`-module to the same representation on the underlying
topological abelian group. The body is exposed because a consumer must see that the underlying
type of `restrictScalarsInt.obj X` is that of `X` before it can name its elements. -/
@[expose] def restrictScalarsInt : TopRep k G ⥤ TopRep ℤ G where
  obj X := of (X.ρ.restrictScalars ℤ)
  map f := ofHom (f.hom.restrictScalars ℤ)
  map_id X := by ext x; simp
  map_comp f g := by ext x; simp

/-- The underlying type of a representation is unchanged by forgetting the scalars. -/
@[simp]
theorem restrictScalarsInt_obj_V (X : TopRep k G) : (restrictScalarsInt.obj X).V = X.V :=
  (rfl)

/-- The operators of a representation are unchanged by forgetting the scalars. -/
@[simp]
theorem restrictScalarsInt_obj_ρ_apply (X : TopRep k G) (g : G) (x : X.V) :
    (restrictScalarsInt.obj X).ρ g x = X.ρ g x :=
  ContRepresentation.restrictScalars_apply_apply ℤ X.ρ g x

/-- The underlying function of a morphism is unchanged by forgetting the scalars. -/
-- The argument is typed by the domain of `restrictScalarsInt.map f`, so that `simp` can use the
-- lemma: `(restrictScalarsInt.obj X).V` is `X.V` only after unfolding `restrictScalarsInt`.
@[simp]
theorem restrictScalarsInt_map_hom_apply {X Y : TopRep k G} (f : X ⟶ Y)
    (x : (restrictScalarsInt.obj X).V) :
    (restrictScalarsInt.map f).hom x = f.hom x :=
  ContIntertwiningMap.restrictScalars_apply ℤ f.hom x

instance : (restrictScalarsInt (k := k) (G := G)).Additive where
  map_add := by
    intro X Y f g
    ext x
    exact (restrictScalarsInt_map_hom_apply (f + g) x).trans <|
      (DFunLike.congr_fun (hom_add X Y f g) x).trans <|
      congrArg₂ (· + ·) (restrictScalarsInt_map_hom_apply f x).symm
        (restrictScalarsInt_map_hom_apply g x).symm

/-- Forgetting the scalars preserves discreteness of the underlying type. This is
`TopRep.restrictScalarsInt_obj_V` read as an instance: the equality holds by definition but not
at reducible transparency, so instance search cannot see through the functor on its own. -/
instance (X : TopRep k G) [DiscreteTopology X.V] : DiscreteTopology (restrictScalarsInt.obj X).V :=
  ‹DiscreteTopology X.V›

end Monoid

section Restriction

universe u v

variable {k : Type v} [Ring k] [TopologicalSpace k]
  {G H : Type u} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- The scalar-restricted coefficient map used when the acting group changes. -/
noncomputable def resRestrictScalarsIntMap (phi : H →* G) {X : TopRep.{u} k G}
    {Y : TopRep.{u} k H} (f : res phi X ⟶ Y) :
    res phi (restrictScalarsInt.obj X) ⟶ restrictScalarsInt.obj Y :=
  ConcreteCategory.ofHom
    { toContinuousLinearMap := f.hom.toContinuousLinearMap.restrictScalars ℤ
      isIntertwining' h := by
        ext x
        -- Scalar restriction and `res phi` leave the operators unchanged: `ρ h` acts on the
        -- restricted objects as `X.ρ (phi h)` and `Y.ρ h`.
        exact (congrArg f.hom
          (ContRepresentation.restrictScalars_apply_apply ℤ X.ρ (phi h) x)).trans
          ((f.hom.isIntertwining h x).trans
            (ContRepresentation.restrictScalars_apply_apply ℤ Y.ρ h (f.hom x)).symm) }

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]
  [IsTopologicalGroup H] in
/-- `resRestrictScalarsIntMap` has the same underlying function as the original coefficient map. -/
@[simp]
theorem resRestrictScalarsIntMap_hom_apply (phi : H →* G) {X : TopRep.{u} k G}
    {Y : TopRep.{u} k H} (f : res phi X ⟶ Y)
    (x : (res phi (restrictScalarsInt.obj X)).V) :
    (resRestrictScalarsIntMap phi f).hom x = f.hom x := by
  rfl

end Restriction

/-! ### Compatibility with coinduction and invariants -/

section Coinduction

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Coinduction commutes with forgetting the scalars: both sides are the representation of `G` on
`C(G, X.V)` by `g • f = x ↦ ρ(g) (f (g⁻¹ x))`, read over `ℤ`. -/
-- Both structure maps are the identity of `C(G, X.V)`:
-- `ContRepresentation.coind₁` builds the same operators from `X.ρ.restrictScalars ℤ` as from
-- `X.ρ`, because forgetting the scalars keeps the underlying functions
-- (`ContRepresentation.restrictScalars_apply_apply`).
def coind₁RestrictScalarsIntIso (X : TopRep k G) :
    (restrictScalarsInt.obj X).coind₁ ≅ restrictScalarsInt.obj X.coind₁ where
  hom := ofHom
    { toFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      cont := continuous_id
      isIntertwining' g := by
        ext f x
        exact (ContRepresentation.restrictScalars_apply_apply ℤ X.ρ g (f (g⁻¹ * x))).trans
          (congrArg (fun h : C(G, X.V) ↦ h x)
            (ContRepresentation.restrictScalars_apply_apply ℤ X.ρ.coind₁ g f).symm) }
  inv := ofHom
    { toFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      cont := continuous_id
      isIntertwining' g := by
        ext f x
        exact (congrArg (fun h : C(G, X.V) ↦ h x)
          (ContRepresentation.restrictScalars_apply_apply ℤ X.ρ.coind₁ g f)).trans
          (ContRepresentation.restrictScalars_apply_apply ℤ X.ρ g (f (g⁻¹ * x))).symm }
  hom_inv_id := by ext f; rfl
  inv_hom_id := by ext f; rfl

/-- `coind₁RestrictScalarsIntIso` is the identity on the function space `C(G, X.V)`. -/
-- The argument is typed by the domain of the map, as in `restrictScalarsInt_map_hom_apply`.
@[simp]
theorem coind₁RestrictScalarsIntIso_hom_apply (X : TopRep k G)
    (f : C(G, (restrictScalarsInt.obj X).V)) :
    (coind₁RestrictScalarsIntIso X).hom.hom f = f :=
  (rfl)

/-- The inverse of `coind₁RestrictScalarsIntIso` is the identity on the function space
`C(G, X.V)`. -/
@[simp]
theorem coind₁RestrictScalarsIntIso_inv_apply (X : TopRep k G) (f : C(G, X.V)) :
    (coind₁RestrictScalarsIntIso X).inv.hom f = f :=
  (rfl)

/-- The identification of the coinduced representations is compatible with the unit
`TopRep.coind₁ι`, the inclusion of a representation as the constant functions. -/
-- Not a simp lemma: the unit lives in `TopRep.{max v w}`, so the carrier universe of `X` occurs
-- in every constant of the left-hand side only as `max v w`, which `simp` cannot instantiate.
@[reassoc]
theorem coind₁ι_comp_coind₁RestrictScalarsIntIso_hom (X : TopRep k G) :
    ofHom (restrictScalarsInt.obj X).ρ.coind₁ι ≫ (coind₁RestrictScalarsIntIso X).hom =
      restrictScalarsInt.map (ofHom X.ρ.coind₁ι) := by
  ext v
  exact (ContIntertwiningMap.restrictScalars_apply ℤ X.ρ.coind₁ι v).symm

/-- The identification of the coinduced representations is compatible with the maps induced by
`TopRep.coind₁Functor`. -/
@[reassoc (attr := simp)]
theorem coind₁Functor_map_comp_coind₁RestrictScalarsIntIso_hom {X Y : TopRep k G}
    (f : X ⟶ Y) :
    (coind₁Functor ℤ G).map (restrictScalarsInt.map f) ≫
        (coind₁RestrictScalarsIntIso Y).hom =
      (coind₁RestrictScalarsIntIso X).hom ≫
        restrictScalarsInt.map ((coind₁Functor k G).map f) := by
  ext F
  refine ContinuousMap.ext fun g ↦ ?_
  exact (ContIntertwiningMap.restrictScalars_apply ℤ f.hom (F g)).trans
    (congrArg (fun h : C(G, Y.V) ↦ h g)
      (ContIntertwiningMap.restrictScalars_apply ℤ (coind₁Map f.hom) F).symm)

end Coinduction

section Invariants

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Group G]

/-- Taking invariants commutes with forgetting the scalars, as topological `ℤ`-modules: the
invariants of the underlying additive representation are the underlying topological abelian group
of the invariants. -/
def invariantsRestrictScalarsIntEquiv (X : TopRep k G) :
    (restrictScalarsInt.obj X).invariants ≃L[ℤ]
      TopModuleCat.restrictScalarsInt.obj X.invariants where
  toFun x := ⟨x.1, (ContRepresentation.mem_invariants_restrictScalars_iff ℤ X.ρ).mp x.2⟩
  invFun x := ⟨x.1, (ContRepresentation.mem_invariants_restrictScalars_iff ℤ X.ρ).mpr x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val
  continuous_invFun := continuous_induced_rng.2 continuous_subtype_val

/-- `invariantsRestrictScalarsIntEquiv` is the identity on the underlying elements. -/
@[simp]
theorem coe_invariantsRestrictScalarsIntEquiv_apply (X : TopRep k G)
    (x : (restrictScalarsInt.obj X).invariants) :
    (invariantsRestrictScalarsIntEquiv X x).1 = x.1 :=
  (rfl)

/-- Taking invariants commutes with forgetting the scalars, as an isomorphism in
`TopModuleCat ℤ`. -/
noncomputable def invariantsRestrictScalarsIntIso (X : TopRep k G) :
    (invariantsFunctor ℤ G).obj (restrictScalarsInt.obj X) ≅
      TopModuleCat.restrictScalarsInt.obj ((invariantsFunctor k G).obj X) :=
  TopModuleCat.ofIso (invariantsRestrictScalarsIntEquiv X)

/-- `invariantsRestrictScalarsIntIso` is the identity on the underlying invariant elements. -/
@[simp]
theorem coe_invariantsRestrictScalarsIntIso_hom_apply (X : TopRep k G)
    (x : (restrictScalarsInt.obj X).invariants) :
    ((invariantsRestrictScalarsIntIso X).hom x).1 = x.1 :=
  (rfl)

/-- The inverse of `invariantsRestrictScalarsIntIso` is the identity on the underlying invariant
elements. -/
@[simp]
theorem coe_invariantsRestrictScalarsIntIso_inv_apply (X : TopRep k G) (x : X.invariants) :
    ((invariantsRestrictScalarsIntIso X).inv x).1 = x.1 :=
  (rfl)

/-- The identification of the invariants is compatible with the maps induced by
`TopRep.invariantsFunctor`. -/
@[reassoc (attr := simp)]
theorem invariantsRestrictScalarsIntIso_hom_comp_map {X Y : TopRep k G} (f : X ⟶ Y) :
    (invariantsRestrictScalarsIntIso X).hom ≫
        TopModuleCat.restrictScalarsInt.map ((invariantsFunctor k G).map f) =
      (invariantsFunctor ℤ G).map (restrictScalarsInt.map f) ≫
        (invariantsRestrictScalarsIntIso Y).hom := by
  ext x
  exact Subtype.ext (ContIntertwiningMap.restrictScalars_apply ℤ f.hom x.1).symm

end Invariants

end TopRep
