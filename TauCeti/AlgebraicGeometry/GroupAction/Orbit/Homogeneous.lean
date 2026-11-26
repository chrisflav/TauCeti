/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Stabilizer
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.GroupAction.Orbit.BaseChange
import TauCeti.Topology.JacobsonSpace

/-!
# Homogeneous scheme actions

When a group scheme `G` over a field `k` acts on a scheme `X` over `k` and the geometric orbit
`orbit G x` of a rational point `x` covers all of `X`, the locally closed orbit immersion
`orbitInclusion G x : orbitOver G x ⟶ X` becomes a surjective closed immersion. If in addition
`X` is reduced, it is an equivariant isomorphism of schemes over `Spec k`, identifying `X` with
the locally closed orbit scheme `orbitOver G x`.

Consequently, when `G` is geometrically reduced and finite type over `k` and `X` is reduced and
finite type over `k` with `orbit G x = Set.univ`, the orbit morphism `orbitMap G x : G ⟶ X` is
faithfully flat and locally of finite presentation (an fppf cover), and is smooth if and only if
the scheme-theoretic stabilizer `stabilizer G x` is smooth over `k`.

Two criteria for `orbit G x = Set.univ` are supplied: over an algebraically closed field,
transitivity of rational group points on rational points of `X` implies every closed point lies
in the locally closed orbit, which forces the orbit to be all of `X` by Jacobsonness; over a
general field `k`, geometric transitivity after base change to `AlgebraicClosure k` descends
along `Spec (AlgebraicClosure k) ⟶ Spec k`.

## Main declarations

* `TauCeti.SchemeAction.orbit_eq_univ_iff_surjective_orbitMap`: the geometric orbit is all of
  `X` iff `(orbitMap G x).left` is surjective.
* `TauCeti.SchemeAction.closedPoints_subset_orbit_of_forall_exists_smul_eq`: over an algebraically
  closed field, rational-point transitivity covers all closed points.
* `TauCeti.SchemeAction.orbit_eq_univ_of_forall_exists_smul_eq`,
  `TauCeti.SchemeAction.orbit_eq_univ_of_geom_transitive`: criteria for `orbit G x = Set.univ`.
* `TauCeti.SchemeAction.isIso_orbitInclusion_of_orbit_eq_univ` and
  `TauCeti.SchemeAction.orbitInclusionIsoOfOrbitEqUniv`: when `X` is reduced and `orbit G x =
  Set.univ`, the orbit immersion is an equivariant `k`-scheme isomorphism.
* `TauCeti.SchemeAction.flat_orbitMap_of_orbit_eq_univ`,
  `TauCeti.SchemeAction.locallyOfFinitePresentation_orbitMap_of_orbit_eq_univ`, and
  `TauCeti.SchemeAction.smooth_orbitMap_iff_smooth_stabilizer`: fppf-cover and smoothness
  properties of the orbit morphism on homogeneous reduced targets.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace TauCeti.SchemeAction

universe u

section Monoid

variable {S : Scheme.{u}} (G : Over S) {X : Over S} [MonObj G] [ModObj G X]

/-- The geometric orbit of a section covers all of `X` if and only if the underlying scheme map
of the orbit morphism is surjective. -/
theorem orbit_eq_univ_iff_surjective_orbitMap (x : 𝟙_ (Over S) ⟶ X) :
    orbit G x = Set.univ ↔ Surjective (orbitMap G x).left := by
  rw [orbit_def, Set.range_eq_univ]
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.surj⟩

/-- When the geometric orbit equals all of `X`, the orbit morphism is surjective. -/
theorem surjective_orbitMap_of_orbit_eq_univ (x : 𝟙_ (Over S) ⟶ X)
    (hx : orbit G x = Set.univ) :
    Surjective (orbitMap G x).left :=
  (orbit_eq_univ_iff_surjective_orbitMap G x).mp hx

/-- A geometric orbit pulls back to `Set.univ` under a faithfully flat field extension only if it
already equals `Set.univ` over the base field. -/
theorem orbit_eq_univ_of_pullback {k L : Type u} [Field k] [Field L] [Algebra k L]
    (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [MonObj G] [ModObj G X]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (hx : letI := (Over.pullback (Spec.algebraMap k L)).modObjObj G X
      orbit ((Over.pullback (Spec.algebraMap k L)).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback (Spec.algebraMap k L)) ≫
          (Over.pullback (Spec.algebraMap k L)).map x) = Set.univ) :
    orbit G x = Set.univ := by
  let f := Spec.algebraMap k L
  have hff : (CommRingCat.ofHom (algebraMap k L)).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    ((flat_and_surjective_SpecMap_iff _).2 hff).2
  have : Surjective (pullback.fst X.hom f) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback X.hom f).flip inferInstance
  rw [orbit_pullback] at hx
  exact Set.eq_univ_of_forall fun p ↦ by
    obtain ⟨q, rfl⟩ := (pullback.fst X.hom f).surjective p
    change q ∈ pullback.fst X.hom f ⁻¹' orbit G x
    rw [hx]
    trivial

end Monoid

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] (G : Over (Spec (.of k)))
  {X : Over (Spec (.of k))} [MonObj G] [ModObj G X] [LocallyOfFiniteType X.hom]

/-- Over an algebraically closed field, if every rational point of a locally-of-finite-type scheme
`X` is a rational translate of `x`, then every closed point of `X` lies in the geometric orbit
`orbit G x`. -/
theorem closedPoints_subset_orbit_of_forall_exists_smul_eq
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (h : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
      ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y) :
    closedPoints X.left ⊆ orbit G x := by
  intro p hp
  let y : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
    Over.homMk (AlgebraicGeometry.pointOfClosedPoint X.hom p (mem_closedPoints_iff.mp hp))
      (AlgebraicGeometry.pointOfClosedPoint_comp X.hom p (mem_closedPoints_iff.mp hp))
  obtain ⟨g, hg⟩ := h y
  have hy : y.left (IsLocalRing.closedPoint k) = p :=
    AlgebraicGeometry.pointOfClosedPoint_apply X.hom p (mem_closedPoints_iff.mp hp)
      (IsLocalRing.closedPoint k)
  rw [← hy, ← hg]
  exact smul_left_apply_mem_orbit G x g (IsLocalRing.closedPoint k)

end AlgClosed

section Field

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) {X : Over (Spec (.of k))}
  [GrpObj G] [ModObj G X] [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

/-- Over any field, if the geometric orbit of a rational point contains every closed point of `X`,
then it equals all of `X`. -/
theorem orbit_eq_univ_of_closedPoints_subset (h : closedPoints X.left ⊆ orbit G x) :
    orbit G x = Set.univ := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  exact (isLocallyClosed_orbit G x).eq_univ_of_closedPoints_subset h

/-- Over an algebraically closed field, if rational points of `G` carry `x` to every rational point
of `X`, then the geometric orbit `orbit G x` equals all of `X`. -/
theorem orbit_eq_univ_of_forall_exists_smul_eq [IsAlgClosed k]
    (h : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
      ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y) :
    orbit G x = Set.univ :=
  orbit_eq_univ_of_closedPoints_subset G x
    (closedPoints_subset_orbit_of_forall_exists_smul_eq G x h)

/-- Over an arbitrary field `k`, if after base change to `AlgebraicClosure k` rational points of
the group carry `x` to every rational point of `X`, then `orbit G x = Set.univ`. -/
theorem orbit_eq_univ_of_geom_transitive
    (h : letI := (Over.pullback (Spec.algebraMap k (AlgebraicClosure k))).modObjObj G X
      ∀ y : 𝟙_ (Over (Spec (.of (AlgebraicClosure k)))) ⟶
          (Over.pullback (Spec.algebraMap k (AlgebraicClosure k))).obj X,
        ∃ g : 𝟙_ (Over (Spec (.of (AlgebraicClosure k)))) ⟶
            (Over.pullback (Spec.algebraMap k (AlgebraicClosure k))).obj G,
          g • (Functor.LaxMonoidal.ε (Over.pullback (Spec.algebraMap k (AlgebraicClosure k))) ≫
            (Over.pullback (Spec.algebraMap k (AlgebraicClosure k))).map x) = y) :
    orbit G x = Set.univ := by
  let f := Spec.algebraMap k (AlgebraicClosure k)
  let := (Over.pullback f).modObjObj G X
  exact orbit_eq_univ_of_pullback G x
    (orbit_eq_univ_of_forall_exists_smul_eq ((Over.pullback f).obj G) _ h)

/-- When the geometric orbit equals all of `X`, the locally closed orbit immersion `orbitι G x` is
a closed immersion. -/
theorem isClosedImmersion_orbitι_of_orbit_eq_univ (hx : orbit G x = Set.univ) :
    IsClosedImmersion (orbitι G x) :=
  IsClosedImmersion.of_isPreimmersion (orbitι G x) (by rw [range_orbitι, hx]; exact isClosed_univ)

/-- When the geometric orbit equals all of `X`, the orbit immersion `orbitι G x` is surjective. -/
theorem surjective_orbitι_of_orbit_eq_univ (hx : orbit G x = Set.univ) :
    Surjective (orbitι G x) :=
  ⟨fun p ↦ by rw [← Set.mem_range, range_orbitι, hx]; trivial⟩

/-- When `X` is reduced and the geometric orbit equals all of `X`, the orbit immersion `orbitι G x`
is an isomorphism of schemes. -/
theorem isIso_orbitι_of_orbit_eq_univ [IsReduced X.left] (hx : orbit G x = Set.univ) :
    IsIso (orbitι G x) := by
  have := isClosedImmersion_orbitι_of_orbit_eq_univ G x hx
  have := surjective_orbitι_of_orbit_eq_univ G x hx
  exact isIso_of_isClosedImmersion_of_surjective (orbitι G x)

/-- When `X` is reduced and the geometric orbit equals all of `X`, the orbit inclusion
`orbitInclusion G x : orbitOver G x ⟶ X` is an isomorphism in `Over (Spec k)`. -/
theorem isIso_orbitInclusion_of_orbit_eq_univ [IsReduced X.left] (hx : orbit G x = Set.univ) :
    IsIso (orbitInclusion G x) := by
  have : IsIso ((Over.forget _).map (orbitInclusion G x)) := by
    simpa only [Over.forget_map, orbitInclusion_left] using isIso_orbitι_of_orbit_eq_univ G x hx
  exact isIso_of_reflects_iso (orbitInclusion G x) (Over.forget _)

/-- The equivariant `k`-scheme isomorphism `orbitOver G x ≅ X` when `X` is reduced and
`orbit G x = Set.univ`. -/
def orbitInclusionIsoOfOrbitEqUniv [IsReduced X.left] (hx : orbit G x = Set.univ) :
    orbitOver G x ≅ X :=
  @asIso _ _ _ _ (orbitInclusion G x) (isIso_orbitInclusion_of_orbit_eq_univ G x hx)

/-- The forward morphism of `orbitInclusionIsoOfOrbitEqUniv` is `orbitInclusion G x`. -/
@[simp]
theorem orbitInclusionIsoOfOrbitEqUniv_hom [IsReduced X.left] (hx : orbit G x = Set.univ) :
    (orbitInclusionIsoOfOrbitEqUniv G x hx).hom = orbitInclusion G x :=
  (rfl)

/-- The forward morphism of `orbitInclusionIsoOfOrbitEqUniv` is `G`-equivariant. -/
instance isModHom_orbitInclusionIsoOfOrbitEqUniv_hom [IsReduced X.left]
    (hx : orbit G x = Set.univ) :
    IsModHom G (orbitInclusionIsoOfOrbitEqUniv G x hx).hom := by
  rw [orbitInclusionIsoOfOrbitEqUniv_hom]
  infer_instance

/-- When `G` is geometrically reduced, `X` is reduced, and `orbit G x = Set.univ`, the orbit
morphism `(orbitMap G x).left` is flat. -/
theorem flat_orbitMap_of_orbit_eq_univ [GeometricallyReduced G.hom] [IsReduced X.left]
    (hx : orbit G x = Set.univ) :
    Flat (orbitMap G x).left := by
  have := isIso_orbitι_of_orbit_eq_univ G x hx
  rw [← orbitProjection_inclusion, Over.comp_left, orbitProjection_left, orbitInclusion_left]
  exact MorphismProperty.comp_mem _ (toOrbit G x) (orbitι G x) inferInstance inferInstance

/-- When `X` is reduced and `orbit G x = Set.univ`, the orbit morphism `(orbitMap G x).left` is
locally of finite presentation. -/
theorem locallyOfFinitePresentation_orbitMap_of_orbit_eq_univ [IsReduced X.left]
    (hx : orbit G x = Set.univ) :
    LocallyOfFinitePresentation (orbitMap G x).left := by
  have := isIso_orbitι_of_orbit_eq_univ G x hx
  rw [← orbitProjection_inclusion, Over.comp_left, orbitProjection_left, orbitInclusion_left]
  exact MorphismProperty.comp_mem _ (toOrbit G x) (orbitι G x) inferInstance inferInstance

/-- When `G` is geometrically reduced, `X` is reduced, and `orbit G x = Set.univ`, the orbit
morphism `(orbitMap G x).left` is smooth if and only if the scheme-theoretic stabilizer
`stabilizer G x` is smooth over `Spec k`. -/
theorem smooth_orbitMap_iff_smooth_stabilizer [GeometricallyReduced G.hom] [IsReduced X.left]
    (hx : orbit G x = Set.univ) :
    Smooth (orbitMap G x).left ↔ Smooth (stabilizer G x).hom := by
  have := isIso_orbitι_of_orbit_eq_univ G x hx
  rw [← smooth_toOrbit_iff G x, ← orbitProjection_inclusion, Over.comp_left,
    orbitProjection_left, orbitInclusion_left]
  refine ⟨fun h ↦ ?_, fun h ↦ smooth_comp _ _⟩
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using
    (smooth_comp (toOrbit G x ≫ orbitι G x) (inv (orbitι G x)))

end Field

end TauCeti.SchemeAction
