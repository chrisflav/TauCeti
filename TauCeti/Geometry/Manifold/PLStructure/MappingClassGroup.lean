/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PLStructure.Basic
public import TauCeti.Topology.Homotopy.Isotopy.MappingClassGroup
public import TauCeti.Topology.PL.Map
public import Mathlib.GroupTheory.QuotientGroup.Defs
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
import TauCeti.Analysis.Convex.SimplicialComplex.Map
import TauCeti.Topology.PL.Compact
import TauCeti.Topology.PL.Inverse
import TauCeti.Topology.PL.Product
import TauCeti.Topology.PL.Simplicial

/-!
# The piecewise-linear mapping class group

For a piecewise-linear structure `s : TauCeti.PLStructure d M`, a self-homeomorphism `f : M ≃ₜ M`
is **piecewise linear** (`TauCeti.PLStructure.IsPLHomeomorph s f`) when in the barycentric
coordinates of `s` it is the restriction of a map `TauCeti.IsPLOn` on the coordinate image of
the realization `|s.K|`. Because `|s.K|` is a finite simplicial complex in `s.ι → ℝ`, any such map
is affine on each simplex of a finite subdivision, injective on each simplex, and therefore has a
piecewise-linear inverse (`IsPLHomeomorph.symm`). Hence PL self-homeomorphisms form a subgroup
`PLStructure.plHomeomorphSubgroup s` of `M ≃ₜ M`.

Two self-homeomorphisms are **PL isotopic** (`TauCeti.PLStructure.IsPLIsotopic s f g`) when they
are joined by an isotopy through surjective maps (hence homeomorphisms) whose total
level-preserving map on `[0, 1] × |s.K|` is piecewise linear in barycentric coordinates. PL isotopy
is an equivalence relation closed under multiplication, inversion, and conjugation by PL
homeomorphisms; in particular, the normal subgroup `PLStructure.plIsotopicToIdSubgroup s` generated
by elements PL isotopic to `1` consists precisely of the PL homeomorphisms PL isotopic to `1`.

The quotient `TauCeti.MappingClassGroupPL s` is the PL mapping class group of `s`, with a
canonical forgetful homomorphism `TauCeti.MappingClassGroupPL.toTop s` into
`TauCeti.MappingClassGroupFull M`.

## Main definitions

* `TauCeti.PLStructure.coordRange`: the coordinate image of `Realization s.K` in `s.ι → ℝ`.
* `TauCeti.PLStructure.IsPLHomeomorph`: PL regularity of a self-homeomorphism in barycentric
  coordinates.
* `TauCeti.PLStructure.plHomeomorphSubgroup`: the subgroup of PL self-homeomorphisms.
* `TauCeti.PLStructure.IsPLIsotopic`: PL isotopy between self-homeomorphisms.
* `TauCeti.PLStructure.plIsotopicToIdSubgroup`: the normal subgroup of PL homeomorphisms PL
  isotopic to the identity.
* `TauCeti.MappingClassGroupPL`: the PL mapping class group.
* `TauCeti.MappingClassGroupPL.toTop`: the forgetful homomorphism to `MappingClassGroupFull M`.

## Main results

* `TauCeti.PLStructure.IsPLHomeomorph.symm`: a PL self-homeomorphism has a PL inverse.
* `TauCeti.PLStructure.mem_plHomeomorphSubgroup_iff`: membership in `plHomeomorphSubgroup s` is
  equivalent to `s.IsPLHomeomorph f`.
* `TauCeti.PLStructure.IsPLIsotopic.equivalence`: PL isotopy is an equivalence relation on PL
  self-homeomorphisms.
* `TauCeti.PLStructure.mem_plIsotopicToIdSubgroup_iff`: an element belongs to
  `plIsotopicToIdSubgroup s` if and only if it is PL isotopic to the identity.
-/

public section

open Set AbstractSimplicialComplex ContinuousMap
open scoped unitInterval

namespace TauCeti

section PLHomeomorph

variable {d : ℕ} {M : Type*} [TopologicalSpace M]

namespace PLStructure

/-- The image of the realization `Realization s.K` in coordinate space `s.ι → ℝ`. -/
abbrev coordRange (s : PLStructure d M) : Set (s.ι → ℝ) :=
  Set.range fun y : Realization s.K => ⇑(y : s.ι →₀ ℝ)

private theorem isCompact_coordRange (s : PLStructure d M) : IsCompact s.coordRange := by
  have : CompactSpace (Realization s.K) := inferInstance
  exact isCompact_range (continuous_realization_coe s.K)

private theorem standardGeometricComplex_faces_finite (s : PLStructure d M) :
    (standardGeometricComplex s.K).faces.Finite := by
  classical
  have := Fintype.ofFinite s.ι
  let toGeom : Finset s.ι → Finset (s.ι →₀ ℝ) := fun c => c.image fun i => Finsupp.single i (1 : ℝ)
  have hsub : (standardGeometricComplex s.K).faces ⊆ toGeom '' s.K.faces := by
    rintro τ hτ
    obtain ⟨c, hc, rfl⟩ := (mem_standardGeometricComplex_faces_iff s.K τ).mp hτ
    exact ⟨c, hc, rfl⟩
  exact ((Set.toFinite s.K.faces).image toGeom).subset hsub

private theorem injOn_linearEquivFunOnFinite (s : PLStructure d M) :
    InjOn (⇑(Finsupp.linearEquivFunOnFinite ℝ ℝ s.ι).toAffineMap)
      (standardGeometricComplex s.K).space := by
  intro x _ y _ hxy
  exact (Finsupp.linearEquivFunOnFinite ℝ ℝ s.ι).injective hxy

private noncomputable def coordComplex (s : PLStructure d M) :
    Geometry.SimplicialComplex ℝ (s.ι → ℝ) :=
  (standardGeometricComplex s.K).map (⇑(Finsupp.linearEquivFunOnFinite ℝ ℝ s.ι).toAffineMap)
    (injOn_linearEquivFunOnFinite s)
    fun _ _ => ⟨(Finsupp.linearEquivFunOnFinite ℝ ℝ s.ι).toAffineMap, fun _ _ => rfl⟩

private theorem coordComplex_space (s : PLStructure d M) :
    (coordComplex s).space = s.coordRange := by
  rw [coordComplex, Geometry.SimplicialComplex.space_map]
  ext z
  simp only [mem_image, Set.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

private theorem coordComplex_faces_finite (s : PLStructure d M) :
    (coordComplex s).faces.Finite :=
  Geometry.SimplicialComplex.finite_faces_map (standardGeometricComplex_faces_finite s)

/-- A self-homeomorphism `f : M ≃ₜ M` is **piecewise linear** for `s` when, in the barycentric
coordinates of `s`, it is the restriction of a map that is `TauCeti.IsPLOn` on `s.coordRange`. -/
def IsPLHomeomorph (s : PLStructure d M) (f : M ≃ₜ M) : Prop :=
  ∃ F : (s.ι → ℝ) → (s.ι → ℝ),
    IsPLOn F s.coordRange ∧
    ∀ y : Realization s.K, F ⇑(y : s.ι →₀ ℝ) = ⇑(s.e.symm (f (s.e y)) : s.ι →₀ ℝ)

/-- The identity homeomorphism is piecewise linear for every PL structure. -/
theorem IsPLHomeomorph.refl (s : PLStructure d M) : s.IsPLHomeomorph (Homeomorph.refl M) :=
  ⟨id, isPLOn_id _, fun y => by simp⟩

/-- A composition of PL self-homeomorphisms is a PL self-homeomorphism. -/
theorem IsPLHomeomorph.trans {s : PLStructure d M} {f g : M ≃ₜ M}
    (hf : s.IsPLHomeomorph f) (hg : s.IsPLHomeomorph g) : s.IsPLHomeomorph (f.trans g) := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  refine ⟨G ∘ F, hG.comp hF ?_, fun y => ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨s.e.symm (f (s.e y)), (hFf y).symm⟩
  · simp [Function.comp_apply, hFf, hGg]

/-- The inverse of a PL self-homeomorphism is piecewise linear: on each simplex of a finite
subdivision on which the forward map is affine and injective, its inverse is affine. -/
theorem IsPLHomeomorph.symm {s : PLStructure d M} {f : M ≃ₜ M}
    (hf : s.IsPLHomeomorph f) : s.IsPLHomeomorph f.symm := by
  classical
  have := Fintype.ofFinite s.ι
  obtain ⟨F, hF_pl, hF_eq⟩ := hf
  have hF_space : IsPLOn F (coordComplex s).space := by
    rwa [coordComplex_space]
  obtain ⟨K', hK'sub, hK'fin, hK'aff⟩ :=
    hF_space.exists_isSubdivision_eqOn (coordComplex_faces_finite s)
  have hK'space : K'.space = s.coordRange := hK'sub.space_eq.trans (coordComplex_space s)
  let G : (s.ι → ℝ) → (s.ι → ℝ) := fun z =>
    if hz : z ∈ s.coordRange then ⇑(s.e.symm (f.symm (s.e hz.choose)) : s.ι →₀ ℝ) else 0
  have hG_eq (y : Realization s.K) :
      G ⇑(y : s.ι →₀ ℝ) = ⇑(s.e.symm (f.symm (s.e y)) : s.ι →₀ ℝ) := by
    have hy : ⇑(y : s.ι →₀ ℝ) ∈ s.coordRange := ⟨y, rfl⟩
    have hchoose : hy.choose = y := injective_realization_coe s.K hy.choose_spec
    simp only [G, hy, ↓reduceDIte, hchoose]
  have hFinj : InjOn F K'.space := by
    intro x₁ hx₁ x₂ hx₂ hFx
    rw [hK'space] at hx₁ hx₂
    obtain ⟨y₁, rfl⟩ := hx₁
    obtain ⟨y₂, rfl⟩ := hx₂
    rw [hF_eq y₁, hF_eq y₂] at hFx
    have hy12 : y₁ = y₂ := s.e.injective (f.injective (s.e.symm.injective
      (injective_realization_coe s.K hFx)))
    subst hy12
    rfl
  choose A hA using fun c : K'.faces => hK'aff c.val c.property
  have hfinite : Finite K'.faces := hK'fin.to_subtype
  have hind (c : K'.faces) :
      AffineIndependent ℝ (Subtype.val : ↥((A c) '' (c.val : Set (s.ι → ℝ))) → (s.ι → ℝ)) := by
    have hinjA : InjOn (A c) (convexHull ℝ (c.val : Set (s.ι → ℝ))) :=
      (hFinj.mono (Geometry.SimplicialComplex.convexHull_subset_space c.property)).congr (hA c)
    have him := ((K'.indep c.property).map_of_injOn_convexHull (A c).toAffineMap
      (by simpa [Subtype.range_coe] using hinjA)).range
    have hrange : Set.range (⇑(A c).toAffineMap ∘ (Subtype.val : ↥(c.val : Set (s.ι → ℝ)) → _)) =
        ((A c) '' (c.val : Set (s.ι → ℝ))) := by
      rw [Set.range_comp, Subtype.range_coe]
      rfl
    exact hrange ▸ him
  have hleft : ∀ x ∈ (⋃ c : K'.faces, convexHull ℝ (c.val : Set (s.ι → ℝ))), G (F x) = x := by
    intro x hx
    have hx' : x ∈ K'.space := by
      rw [Geometry.SimplicialComplex.space, Set.biUnion_eq_iUnion]
      exact hx
    rw [hK'space] at hx'
    obtain ⟨y, rfl⟩ := hx'
    rw [hF_eq y, hG_eq (s.e.symm (f (s.e y)))]
    simp
  have hPA := isPiecewiseAffineOn_inverse_of_finite_simplex_cover (f := F) (g := G)
    (s := fun c : K'.faces => (c.val : Set (s.ι → ℝ))) A hA hind hleft
  have him_eq : F '' (⋃ c : K'.faces, convexHull ℝ (c.val : Set (s.ι → ℝ))) = s.coordRange := by
    have hU : (⋃ c : K'.faces, convexHull ℝ (c.val : Set (s.ι → ℝ))) = s.coordRange := by
      rw [← hK'space, Geometry.SimplicialComplex.space, Set.biUnion_eq_iUnion]
    rw [hU]
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      rw [hF_eq y]
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨⇑(s.e.symm (f.symm (s.e y)) : s.ι →₀ ℝ), ⟨_, rfl⟩, ?_⟩
      rw [hF_eq]
      simp
  refine ⟨G, ?_, hG_eq⟩
  rw [← him_eq]
  exact hPA.isPLOn

/-- The subgroup of piecewise-linear self-homeomorphisms of `M` relative to `s`. -/
def plHomeomorphSubgroup (s : PLStructure d M) : Subgroup (M ≃ₜ M) where
  carrier := {f | s.IsPLHomeomorph f ∧ s.IsPLHomeomorph f.symm}
  one_mem' := ⟨IsPLHomeomorph.refl s, IsPLHomeomorph.refl s⟩
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    exact ⟨hg.trans hf, hf'.trans hg'⟩
  inv_mem' := fun h => ⟨h.2, h.1⟩

/-- A self-homeomorphism belongs to `plHomeomorphSubgroup s` if and only if it is piecewise linear
for `s`. -/
@[simp]
theorem mem_plHomeomorphSubgroup_iff {s : PLStructure d M} {f : M ≃ₜ M} :
    f ∈ s.plHomeomorphSubgroup ↔ s.IsPLHomeomorph f :=
  ⟨fun hf => hf.1, fun hf => ⟨hf, hf.symm⟩⟩

end PLStructure

end PLHomeomorph

section PLIsotopy

variable {d : ℕ} {M : Type*} [TopologicalSpace M]

namespace PLStructure

/-- Two self-homeomorphisms are **PL isotopic** relative to `s` when an isotopy through
surjective maps (hence homeomorphisms) joins them whose level-preserving total map on
`[0, 1] × |s.K|` is piecewise linear in barycentric coordinates. -/
def IsPLIsotopic (s : PLStructure d M) (f g : M ≃ₜ M) : Prop :=
  ∃ F : Isotopy (f : C(M, M)) (g : C(M, M)),
    (∀ t, Function.Surjective fun x => F (t, x)) ∧
      ∃ G : ℝ × (s.ι → ℝ) → (s.ι → ℝ),
        IsPLOn G (Icc (0 : ℝ) 1 ×ˢ s.coordRange) ∧
        ∀ (t : I) (y : Realization s.K),
          G ((t : ℝ), ⇑(y : s.ι →₀ ℝ)) = ⇑(s.e.symm (F (t, s.e y)) : s.ι →₀ ℝ)

/-- The left endpoint of a PL isotopy is a PL homeomorphism. -/
theorem IsPLIsotopic.isPLHomeomorph_left {s : PLStructure d M} {f g : M ≃ₜ M}
    (h : s.IsPLIsotopic f g) : s.IsPLHomeomorph f := by
  obtain ⟨F, -, G, hG, hGF⟩ := h
  let inc : (s.ι → ℝ) →ᴬ[ℝ] ℝ × (s.ι → ℝ) :=
    (ContinuousAffineMap.const ℝ (s.ι → ℝ) (0 : ℝ)).prod (ContinuousAffineMap.id ℝ (s.ι → ℝ))
  refine ⟨G ∘ inc, hG.comp (isPLOn_continuousAffineMap inc _) ?_, fun y => ?_⟩
  · intro z hz
    exact ⟨⟨le_rfl, zero_le_one⟩, hz⟩
  · simpa [inc] using hGF 0 y

/-- The right endpoint of a PL isotopy is a PL homeomorphism. -/
theorem IsPLIsotopic.isPLHomeomorph_right {s : PLStructure d M} {f g : M ≃ₜ M}
    (h : s.IsPLIsotopic f g) : s.IsPLHomeomorph g := by
  obtain ⟨F, -, G, hG, hGF⟩ := h
  let inc : (s.ι → ℝ) →ᴬ[ℝ] ℝ × (s.ι → ℝ) :=
    (ContinuousAffineMap.const ℝ (s.ι → ℝ) (1 : ℝ)).prod (ContinuousAffineMap.id ℝ (s.ι → ℝ))
  refine ⟨G ∘ inc, hG.comp (isPLOn_continuousAffineMap inc _) ?_, fun y => ?_⟩
  · intro z hz
    exact ⟨⟨zero_le_one, le_rfl⟩, hz⟩
  · simpa [inc] using hGF 1 y

/-- Any PL self-homeomorphism is PL isotopic to itself. -/
theorem IsPLIsotopic.refl {s : PLStructure d M} {f : M ≃ₜ M} (hf : s.IsPLHomeomorph f) :
    s.IsPLIsotopic f f := by
  obtain ⟨F₀, hF₀, hF₀eq⟩ := hf
  let proj : (ℝ × (s.ι → ℝ)) →ᴬ[ℝ] (s.ι → ℝ) :=
    (ContinuousLinearMap.snd ℝ ℝ (s.ι → ℝ)).toContinuousAffineMap
  refine ⟨HomotopyWith.refl (f : C(M, M)) f.isEmbedding, fun _ => f.surjective, F₀ ∘ proj,
    hF₀.comp (isPLOn_continuousAffineMap proj _) (fun _ hx => hx.2), fun t y => ?_⟩
  simpa [proj] using hF₀eq y

/-- Time reversal preserves PL isotopy. -/
@[symm]
theorem IsPLIsotopic.symm {s : PLStructure d M} {f g : M ≃ₜ M} (h : s.IsPLIsotopic f g) :
    s.IsPLIsotopic g f := by
  obtain ⟨F, hsurj, G, hG, hGF⟩ := h
  let rev : (ℝ × (s.ι → ℝ)) →ᴬ[ℝ] ℝ × (s.ι → ℝ) :=
    ((ContinuousAffineMap.const ℝ (ℝ × (s.ι → ℝ)) (1 : ℝ)) -
      (ContinuousLinearMap.fst ℝ ℝ (s.ι → ℝ)).toContinuousAffineMap).prod
      (ContinuousLinearMap.snd ℝ ℝ (s.ι → ℝ)).toContinuousAffineMap
  have hrev (p : ℝ × (s.ι → ℝ)) : rev p = (1 - p.1, p.2) := rfl
  refine ⟨F.symm, fun t => hsurj (unitInterval.symm t), G ∘ rev,
    hG.comp (isPLOn_continuousAffineMap rev _) ?_, fun t y => ?_⟩
  · rintro ⟨t, z⟩ ⟨ht, hz⟩
    dsimp only [mem_Icc, Prod.fst, Prod.snd] at ht hz
    rw [mem_preimage, hrev]
    exact ⟨⟨by linarith [ht.2], by linarith [ht.1]⟩, hz⟩
  · simpa [hrev, Function.comp_apply, unitInterval.coe_symm_eq] using hGF (unitInterval.symm t) y

private theorem isConvexPolyhedron_fst_le (c : ℝ) (E : Type*)
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] :
    IsConvexPolyhedron {p : ℝ × E | p.1 ≤ c} := by
  let L : (ℝ × E) →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ E).toContinuousAffineMap - ContinuousAffineMap.const ℝ (ℝ × E) c
  convert isConvexPolyhedron_setOf_le L using 1
  ext p
  simp [L]

private theorem isConvexPolyhedron_le_fst (c : ℝ) (E : Type*)
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] :
    IsConvexPolyhedron {p : ℝ × E | c ≤ p.1} := by
  let L : (ℝ × E) →ᴬ[ℝ] ℝ :=
    ContinuousAffineMap.const ℝ (ℝ × E) c - (ContinuousLinearMap.fst ℝ ℝ E).toContinuousAffineMap
  convert isConvexPolyhedron_setOf_le L using 1
  ext p
  simp [L]

/-- PL isotopy is transitive by time concatenation at `1 / 2`. -/
@[trans]
theorem IsPLIsotopic.trans {s : PLStructure d M} {f g h : M ≃ₜ M}
    (hfg : s.IsPLIsotopic f g) (hgh : s.IsPLIsotopic g h) : s.IsPLIsotopic f h := by
  classical
  have := Fintype.ofFinite s.ι
  obtain ⟨F₁, hsurj₁, G₁, hG₁, hG₁eq⟩ := hfg
  obtain ⟨F₂, hsurj₂, G₂, hG₂, hG₂eq⟩ := hgh
  have hcpt : IsCompact (Icc (0 : ℝ) 1 ×ˢ s.coordRange) :=
    isCompact_Icc.prod s.isCompact_coordRange
  have hPA₁ : IsPiecewiseAffineOn G₁ (Icc (0 : ℝ) 1 ×ˢ s.coordRange) :=
    hG₁.isPiecewiseAffineOn_of_isCompact_of_finiteDimensional hcpt
  have hPA₂ : IsPiecewiseAffineOn G₂ (Icc (0 : ℝ) 1 ×ˢ s.coordRange) :=
    hG₂.isPiecewiseAffineOn_of_isCompact_of_finiteDimensional hcpt
  let scale₁ : (ℝ × (s.ι → ℝ)) →ᴬ[ℝ] ℝ × (s.ι → ℝ) :=
    ((2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ (s.ι → ℝ)).toContinuousAffineMap).prod
      (ContinuousLinearMap.snd ℝ ℝ (s.ι → ℝ)).toContinuousAffineMap
  let scale₂ : (ℝ × (s.ι → ℝ)) →ᴬ[ℝ] ℝ × (s.ι → ℝ) :=
    ((2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ (s.ι → ℝ)).toContinuousAffineMap -
      ContinuousAffineMap.const ℝ (ℝ × (s.ι → ℝ)) 1).prod
      (ContinuousLinearMap.snd ℝ ℝ (s.ι → ℝ)).toContinuousAffineMap
  have hscale₁ (p : ℝ × (s.ι → ℝ)) : scale₁ p = (2 * p.1, p.2) :=
    Prod.ext (smul_eq_mul 2 p.1) rfl
  have hscale₂ (p : ℝ × (s.ι → ℝ)) : scale₂ p = (2 * p.1 - 1, p.2) :=
    Prod.ext (congrArg (· - 1) (smul_eq_mul 2 p.1)) rfl
  have hPA₁' : IsPiecewiseAffineOn (G₁ ∘ scale₁)
      ((Icc (0 : ℝ) 1 ×ˢ s.coordRange) ∩ {p : ℝ × (s.ι → ℝ) | p.1 ≤ 1 / 2}) := by
    refine hPA₁.comp (isPiecewiseAffineOn_continuousAffineMap scale₁ _) ?_
    rintro ⟨t, z⟩ ⟨⟨ht, hz⟩, ht_half⟩
    have ht' : 0 ≤ t ∧ t ≤ 1 := ht
    have hth : t ≤ 1 / 2 := ht_half
    rw [hscale₁]
    exact ⟨⟨by linarith [ht'.1], by linarith⟩, hz⟩
  have hPA₂' : IsPiecewiseAffineOn (G₂ ∘ scale₂)
      ((Icc (0 : ℝ) 1 ×ˢ s.coordRange) ∩ {p : ℝ × (s.ι → ℝ) | 1 / 2 ≤ p.1}) := by
    refine hPA₂.comp (isPiecewiseAffineOn_continuousAffineMap scale₂ _) ?_
    rintro ⟨t, z⟩ ⟨⟨ht, hz⟩, ht_half⟩
    have ht' : 0 ≤ t ∧ t ≤ 1 := ht
    have hth : 1 / 2 ≤ t := ht_half
    rw [hscale₂]
    exact ⟨⟨by linarith, by linarith [ht'.2]⟩, hz⟩
  obtain ⟨n₁, C₁, A₁, hC₁, hcov₁, heq₁⟩ := isPiecewiseAffineOn_iff.mp hPA₁'
  obtain ⟨n₂, C₂, A₂, hC₂, hcov₂, heq₂⟩ := isPiecewiseAffineOn_iff.mp hPA₂'
  let G : ℝ × (s.ι → ℝ) → (s.ι → ℝ) := fun p =>
    if p.1 ≤ 1 / 2 then G₁ (scale₁ p) else G₂ (scale₂ p)
  have hG_eq (t : I) (y : Realization s.K) :
      G ((t : ℝ), ⇑(y : s.ι →₀ ℝ)) = ⇑(s.e.symm ((F₁.trans F₂) (t, s.e y)) : s.ι →₀ ℝ) := by
    simp only [G]
    rw [HomotopyWith.trans_apply]
    split_ifs with ht
    · have hsc : scale₁ ((t : ℝ), ⇑(y : s.ι →₀ ℝ)) =
          (((⟨2 * (t : ℝ),
            (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1, ht⟩⟩ : I) : ℝ),
            ⇑(y : s.ι →₀ ℝ)) :=
        hscale₁ _
      rw [hsc, hG₁eq]
    · have hsc : scale₂ ((t : ℝ), ⇑(y : s.ι →₀ ℝ)) =
          (((⟨2 * (t : ℝ) - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.property.2⟩⟩ : I) : ℝ),
            ⇑(y : s.ι →₀ ℝ)) :=
        hscale₂ _
      rw [hsc, hG₂eq]
  let C : Fin n₁ ⊕ Fin n₂ → Set (ℝ × (s.ι → ℝ)) := Sum.elim
    (fun i => C₁ i ∩ {p | p.1 ≤ 1 / 2})
    (fun j => C₂ j ∩ {p | 1 / 2 ≤ p.1})
  let A : Fin n₁ ⊕ Fin n₂ → ((ℝ × (s.ι → ℝ)) →ᴬ[ℝ] (s.ι → ℝ)) := Sum.elim A₁ A₂
  have hPA_G : IsPiecewiseAffineOn G (Icc (0 : ℝ) 1 ×ˢ s.coordRange) := by
    refine isPiecewiseAffineOn_of_finite (C := C) (A := A) ?_ ?_ ?_
    · rintro (i | j)
      · exact (hC₁ i).inter (isConvexPolyhedron_fst_le (1 / 2) (s.ι → ℝ))
      · exact (hC₂ j).inter (isConvexPolyhedron_le_fst (1 / 2) (s.ι → ℝ))
    · intro p hp
      by_cases hph : p.1 ≤ 1 / 2
      · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov₁ ⟨hp, hph⟩)
        exact mem_iUnion.mpr ⟨Sum.inl i, hi, hph⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov₂ ⟨hp, le_of_not_ge hph⟩)
        exact mem_iUnion.mpr ⟨Sum.inr j, hj, le_of_not_ge hph⟩
    · rintro (i | j) ⟨t, z⟩ ⟨⟨ht, hz⟩, hCmem, hhalf⟩
      · dsimp [G, A]
        split_ifs
        · exact heq₁ i ⟨⟨⟨ht, hz⟩, hhalf⟩, hCmem⟩
        · exact absurd (show t ≤ 1 / 2 from hhalf) ‹_›
      · change G (t, z) = A₂ j (t, z)
        have hhalf' : 1 / 2 ≤ t := hhalf
        by_cases hlt : t ≤ 1 / 2
        · have hteq : t = 1 / 2 := le_antisymm hlt hhalf'
          have hzr : z ∈ s.coordRange := hz
          obtain ⟨y, hy⟩ := hzr
          have hagree : G₁ (scale₁ (t, z)) = G₂ (scale₂ (t, z)) := by
            have h1 : scale₁ (t, z) = (((1 : I) : ℝ), ⇑(y : s.ι →₀ ℝ)) := by
              rw [hscale₁]
              refine Prod.ext ?_ hy.symm
              simp [hteq]
            have h2 : scale₂ (t, z) = (((0 : I) : ℝ), ⇑(y : s.ι →₀ ℝ)) := by
              rw [hscale₂]
              refine Prod.ext ?_ hy.symm
              simp [hteq]
            rw [h1, h2, hG₁eq, hG₂eq]
            simp
          rw [show G (t, z) = G₂ (scale₂ (t, z)) from by
            dsimp [G]
            split_ifs
            exact hagree]
          exact heq₂ j ⟨⟨⟨ht, hz⟩, hhalf'⟩, hCmem⟩
        · dsimp [G, A]
          split_ifs
          exact heq₂ j ⟨⟨⟨ht, hz⟩, hhalf'⟩, hCmem⟩
  refine ⟨F₁.trans F₂, fun t y => ?_, G, hPA_G.isPLOn, hG_eq⟩
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · simp only [HomotopyWith.trans_apply, ht, ↓reduceDIte]
    exact hsurj₁
      ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1, ht⟩⟩ y
  · simp only [HomotopyWith.trans_apply, ht, ↓reduceDIte]
    exact hsurj₂
      ⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.property.2⟩⟩ y

/-- PL isotopy is an equivalence relation on PL self-homeomorphisms. -/
theorem IsPLIsotopic.equivalence (s : PLStructure d M) :
    Equivalence (fun f g : s.plHomeomorphSubgroup => s.IsPLIsotopic (f : M ≃ₜ M) (g : M ≃ₜ M)) where
  refl f := IsPLIsotopic.refl (s.mem_plHomeomorphSubgroup_iff.mp f.property)
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

/-- A PL isotopy gives an ordinary topological isotopy. -/
theorem IsPLIsotopic.isotopic {s : PLStructure d M} {f g : M ≃ₜ M}
    (h : s.IsPLIsotopic f g) : Isotopic (f : C(M, M)) (g : C(M, M)) :=
  Isotopic.of_isotopy h.choose

/-- Precomposing a PL isotopy with a PL self-homeomorphism gives a PL isotopy. -/
theorem IsPLIsotopic.precomp {s : PLStructure d M} {f g h : M ≃ₜ M}
    (hfg : s.IsPLIsotopic f g) (hh : s.IsPLHomeomorph h) :
    s.IsPLIsotopic (h.trans f) (h.trans g) := by
  obtain ⟨F, hsurj, G, hG, hGF⟩ := hfg
  obtain ⟨H, hH, hHeq⟩ := hh
  let idH : ℝ × (s.ι → ℝ) → ℝ × (s.ι → ℝ) := Prod.map id H
  have hidH : IsPLOn idH (Icc (0 : ℝ) 1 ×ˢ s.coordRange) :=
    (isPLOn_id (Icc (0 : ℝ) 1)).prodMap hH
  let F' : Isotopy ((h.trans f : M ≃ₜ M) : C(M, M)) ((h.trans g : M ≃ₜ M) : C(M, M)) :=
    (F.precomp (h : C(M, M)) h.isEmbedding).cast rfl rfl
  have hF' (t : I) (x : M) : F' (t, x) = F (t, h x) :=
    F.precomp_apply (h : C(M, M)) h.isEmbedding (t, x)
  refine ⟨F', fun t y => ?_, G ∘ idH, hG.comp hidH ?_, fun t y => ?_⟩
  · obtain ⟨x, hx⟩ := hsurj t y
    refine ⟨h.symm x, ?_⟩
    dsimp only
    rw [hF']
    simpa using hx
  · rintro ⟨t, z⟩ ⟨ht, ⟨y, rfl⟩⟩
    exact ⟨ht, ⟨s.e.symm (h (s.e y)), (hHeq y).symm⟩⟩
  · rw [hF']
    simpa [idH, Function.comp_apply, hHeq] using hGF t (s.e.symm (h (s.e y)))

/-- Postcomposing a PL isotopy with a PL self-homeomorphism gives a PL isotopy. -/
theorem IsPLIsotopic.postcomp {s : PLStructure d M} {f g h : M ≃ₜ M}
    (hfg : s.IsPLIsotopic f g) (hh : s.IsPLHomeomorph h) :
    s.IsPLIsotopic (f.trans h) (g.trans h) := by
  obtain ⟨F, hsurj, G, hG, hGF⟩ := hfg
  obtain ⟨H, hH, hHeq⟩ := hh
  let F' : Isotopy ((f.trans h : M ≃ₜ M) : C(M, M)) ((g.trans h : M ≃ₜ M) : C(M, M)) :=
    (F.postcomp (h : C(M, M)) h.isEmbedding).cast rfl rfl
  have hF' (t : I) (x : M) : F' (t, x) = h (F (t, x)) :=
    F.postcomp_apply (h : C(M, M)) h.isEmbedding (t, x)
  refine ⟨F', fun t y => ?_, H ∘ G, hH.comp hG ?_, fun t y => ?_⟩
  · obtain ⟨x, hx⟩ := hsurj t (h.symm y)
    refine ⟨x, ?_⟩
    dsimp only
    rw [hF']
    simpa using congrArg h hx
  · rintro ⟨t, z⟩ ⟨ht, ⟨y, rfl⟩⟩
    let t' : I := ⟨t, ht⟩
    change G ((t' : ℝ), ⇑(y : s.ι →₀ ℝ)) ∈ s.coordRange
    rw [hGF t' y]
    exact ⟨_, rfl⟩
  · rw [hF']
    simp [Function.comp_apply, hGF t y, hHeq]

/-- Multiplying two homeomorphisms PL isotopic to `1` stays PL isotopic to `1`. -/
theorem IsPLIsotopic.mul_one {s : PLStructure d M} {f g : M ≃ₜ M}
    (hf : s.IsPLIsotopic f 1) (hg : s.IsPLIsotopic g 1) :
    s.IsPLIsotopic (f * g) 1 := by
  have h := (hf.precomp hg.isPLHomeomorph_left).trans hg
  convert h using 1

/-- Inverting a homeomorphism PL isotopic to `1` stays PL isotopic to `1`. -/
theorem IsPLIsotopic.inv_one {s : PLStructure d M} {f : M ≃ₜ M}
    (hf : s.IsPLIsotopic f 1) : s.IsPLIsotopic f⁻¹ 1 := by
  have h := (hf.postcomp hf.isPLHomeomorph_left.symm).symm
  convert h using 1 <;> (ext x; simp)

/-- Conjugating a homeomorphism PL isotopic to `1` by any PL self-homeomorphism stays PL
isotopic to `1`. -/
theorem IsPLIsotopic.conj_one {s : PLStructure d M} {f h : M ≃ₜ M}
    (hf : s.IsPLIsotopic f 1) (hh : s.IsPLHomeomorph h) :
    s.IsPLIsotopic (h * f * h⁻¹) 1 := by
  have hconj := (hf.postcomp hh).precomp hh.symm
  convert hconj using 1; ext x; simp

/-- The normal subgroup of `plHomeomorphSubgroup s` generated by the PL homeomorphisms PL
isotopic to the identity. By `mem_plIsotopicToIdSubgroup_iff`, its elements are precisely the PL
homeomorphisms PL isotopic to the identity. -/
def plIsotopicToIdSubgroup (s : PLStructure d M) : Subgroup s.plHomeomorphSubgroup :=
  Subgroup.normalClosure {f | s.IsPLIsotopic (f : M ≃ₜ M) 1}

/-- The subgroup of homeomorphisms PL isotopic to the identity is normal. -/
instance plIsotopicToIdSubgroup.normal (s : PLStructure d M) :
    s.plIsotopicToIdSubgroup.Normal :=
  Subgroup.normalClosure_normal

/-- A PL self-homeomorphism belongs to `plIsotopicToIdSubgroup s` if and only if it is PL isotopic
to the identity. -/
@[simp]
theorem mem_plIsotopicToIdSubgroup_iff {s : PLStructure d M}
    {f : s.plHomeomorphSubgroup} :
    f ∈ s.plIsotopicToIdSubgroup ↔ s.IsPLIsotopic (f : M ≃ₜ M) 1 := by
  let N : Subgroup s.plHomeomorphSubgroup :=
    { carrier := {g | s.IsPLIsotopic (g : M ≃ₜ M) 1}
      one_mem' := IsPLIsotopic.refl (IsPLHomeomorph.refl s)
      mul_mem' := fun ha hb => ha.mul_one hb
      inv_mem' := fun ha => ha.inv_one }
  have hN_normal : N.Normal :=
    ⟨fun n hn g => hn.conj_one (s.mem_plHomeomorphSubgroup_iff.mp g.property)⟩
  refine ⟨fun hf => ?_, fun hf => Subgroup.subset_normalClosure hf⟩
  exact (Subgroup.normalClosure_le_normal (N := N) fun _ hg => hg) hf

end PLStructure

end PLIsotopy

section PLMappingClassGroup

variable {d : ℕ} {M : Type*} [TopologicalSpace M]

/-- The **PL mapping class group** of a PL structure `s`: PL self-homeomorphisms modulo those PL
isotopic to the identity. -/
abbrev MappingClassGroupPL (s : PLStructure d M) : Type _ :=
  s.plHomeomorphSubgroup ⧸ s.plIsotopicToIdSubgroup

namespace MappingClassGroupPL

/-- The quotient homomorphism sending a PL self-homeomorphism to its PL mapping class. -/
@[expose]
def mk (s : PLStructure d M) : s.plHomeomorphSubgroup →* MappingClassGroupPL s :=
  QuotientGroup.mk' _

/-- Every PL mapping class is represented by a PL self-homeomorphism. -/
theorem mk_surjective (s : PLStructure d M) : Function.Surjective (mk s) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of `MappingClassGroupPL.mk` is `plIsotopicToIdSubgroup s`. -/
@[simp]
theorem ker_mk (s : PLStructure d M) : (mk s).ker = s.plIsotopicToIdSubgroup :=
  QuotientGroup.ker_mk' _

/-- A PL self-homeomorphism represents the identity PL mapping class if and only if it is PL
isotopic to the identity. -/
theorem mk_eq_one_iff {s : PLStructure d M} {f : s.plHomeomorphSubgroup} :
    mk s f = 1 ↔ s.IsPLIsotopic (f : M ≃ₜ M) 1 := by
  rw [← MonoidHom.mem_ker, ker_mk, PLStructure.mem_plIsotopicToIdSubgroup_iff]

/-- Two PL self-homeomorphisms represent the same PL mapping class if and only if they are PL
isotopic. -/
theorem mk_eq_mk_iff {s : PLStructure d M} {f g : s.plHomeomorphSubgroup} :
    mk s f = mk s g ↔ s.IsPLIsotopic (f : M ≃ₜ M) (g : M ≃ₜ M) := by
  rw [← div_eq_one, ← map_div, mk_eq_one_iff, div_eq_mul_inv]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hg := h.precomp (s.mem_plHomeomorphSubgroup_iff.mp g.property)
    convert hg using 1 <;> (ext x; simp)
  · have hg := h.precomp (s.mem_plHomeomorphSubgroup_iff.mp g.property).symm
    convert hg using 1; ext x; simp

section Lift

variable {G : Type*} [Group G]

/-- A homomorphism out of `plHomeomorphSubgroup s` trivial on homeomorphisms PL isotopic to the
identity descends to `MappingClassGroupPL s`. -/
def lift (s : PLStructure d M) (φ : s.plHomeomorphSubgroup →* G)
    (hφ : ∀ f : s.plHomeomorphSubgroup, s.IsPLIsotopic (f : M ≃ₜ M) 1 → φ f = 1) :
    MappingClassGroupPL s →* G :=
  QuotientGroup.lift _ φ fun f hf =>
    hφ f (PLStructure.mem_plIsotopicToIdSubgroup_iff.mp hf)

/-- The descended homomorphism sends the class of `f` to `φ f`. -/
@[simp]
theorem lift_mk {s : PLStructure d M} (φ : s.plHomeomorphSubgroup →* G)
    (hφ : ∀ f : s.plHomeomorphSubgroup, s.IsPLIsotopic (f : M ≃ₜ M) 1 → φ f = 1)
    (f : s.plHomeomorphSubgroup) :
    lift s φ hφ (mk s f) = φ f :=
  QuotientGroup.lift_mk' _ _ f

/-- The descended homomorphism composed with `mk` equals `φ`. -/
@[simp]
theorem lift_comp_mk {s : PLStructure d M} (φ : s.plHomeomorphSubgroup →* G)
    (hφ : ∀ f : s.plHomeomorphSubgroup, s.IsPLIsotopic (f : M ≃ₜ M) 1 → φ f = 1) :
    (lift s φ hφ).comp (mk s) = φ :=
  MonoidHom.ext (lift_mk φ hφ)

/-- Two homomorphisms out of `MappingClassGroupPL s` agreeing on every class `mk s f` are equal. -/
@[ext]
theorem hom_ext {s : PLStructure d M} {ψ ψ' : MappingClassGroupPL s →* G}
    (h : ψ.comp (mk s) = ψ'.comp (mk s)) : ψ = ψ' :=
  QuotientGroup.monoidHom_ext _ h

/-- The descended homomorphism is unique among homomorphisms whose composite with `mk` is `φ`. -/
theorem eq_lift_iff {s : PLStructure d M} {φ : s.plHomeomorphSubgroup →* G}
    {hφ : ∀ f : s.plHomeomorphSubgroup, s.IsPLIsotopic (f : M ≃ₜ M) 1 → φ f = 1}
    {ψ : MappingClassGroupPL s →* G} :
    ψ = lift s φ hφ ↔ ψ.comp (mk s) = φ :=
  ⟨fun h => h ▸ lift_comp_mk φ hφ, fun h => hom_ext (h.trans (lift_comp_mk φ hφ).symm)⟩

end Lift

/-- The forgetful homomorphism from the PL mapping class group to the full topological mapping
class group, descending because every PL isotopy is an isotopy. -/
@[expose]
def toTop (s : PLStructure d M) :
    MappingClassGroupPL s →* MappingClassGroupFull M :=
  QuotientGroup.map _ _ s.plHomeomorphSubgroup.subtype <| by
    refine Subgroup.normalClosure_le_normal ?_
    rintro f hf
    change (f : M ≃ₜ M) ∈ isotopicToIdSubgroup M
    rw [mem_isotopicToIdSubgroup_iff]
    have h1 : ((1 : M ≃ₜ M) : C(M, M)) = ContinuousMap.id M := by ext x; simp
    rw [← h1]
    exact hf.isotopic

/-- The forgetful homomorphism sends a PL mapping class to its topological mapping class. -/
@[simp]
theorem toTop_mk (s : PLStructure d M) (f : s.plHomeomorphSubgroup) :
    toTop s (mk s f) = MappingClassGroupFull.mk M f :=
  rfl

end MappingClassGroupPL

end PLMappingClassGroup

end TauCeti
