/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# The compact-open topology: discreteness, and pairing maps into a product

A continuous map `f` from a compact space to a discrete space has finite image, and each of its
fibres is closed, hence compact. Prescribing the value of a map on each of those finitely many
fibres is therefore a finite intersection of compact-open subbasic sets, so it is an open
condition, and it pins the map down to `f` itself. Consequently `C(X, Y)` is discrete.

Compactness of `X` is used and not merely convenient: for `X = ℕ` discrete and `Y = Bool` the
compact subsets of `X` are the finite ones, so the compact-open topology on `C(ℕ, Bool)` is the
product topology, which is not discrete.

The file also records when pairing two maps into a product, `(f, g) ↦ (x ↦ (f x, g x))`, is
continuous for the compact-open topologies. Mathlib's `ContinuousMap.continuous_prodMk_const` is
the case where the first map is constant. The case where the second map is constant follows by
swapping the factors. The general case, for every R₁ source and in particular for every regular
or Hausdorff one, is Mathlib's `ContinuousMap.continuous_prodMk'`. Topological groups are regular,
so these are the continuity statements behind the pointwise operations on the iterated function
spaces `C(G, C(G, …))` of the coinduced resolution of a topological representation.

Finally, the constant maps embed `Y` in `C(X, Y)` whenever `X` is nonempty
(`ContinuousMap.isEmbedding_const`): evaluation at any point is a continuous left inverse.
Postcomposition with a closed embedding `g` is a closed embedding
(`ContinuousMap.isClosedEmbedding_postcomp`): its range consists of the maps with values in the
closed range of `g`, a condition closed under pointwise limits.

## Currying for R₁ and locally compact sources

Mathlib's `Homeomorph.curry` and `ContinuousMap.continuous_uncurry` require both source factors
`X` and `Y` to be locally compact. Uncurrying `C(X, C(Y, Z)) → C(X × Y, Z)` is in fact continuous
for every space `X` as soon as `Y` is locally compact
(`ContinuousMap.continuous_uncurry_of_locallyCompact`), while currying `C(X × Y, Z) → C(X, C(Y, Z))`
is continuous whenever `X` is R₁ (for instance Hausdorff, such as a CW complex) with no local
compactness assumptions on `X` or `Y` (`ContinuousMap.continuous_curry_of_r1`). Together these yield
the exponential homeomorphism `Homeomorph.curryOfR1 : C(X × Y, Z) ≃ₜ C(X, C(Y, Z))`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Propositions A.14–A.16, for the compact-open exponential law on Hausdorff sources.
-/

public section

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The compact-open topology on the continuous maps from a compact space to a discrete space is
discrete. -/
instance discreteTopology [CompactSpace X] [DiscreteTopology Y] :
    DiscreteTopology C(X, Y) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro f
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have hset : ({f} : Set C(X, Y)) =
      ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨?_, fun h ↦ ext fun x ↦ h (f x) ⟨x, rfl⟩ rfl⟩
    rintro rfl _ _ _ hx
    exact hx
  rw [hset]
  exact hfin.isOpen_biInter fun y _ ↦ isOpen_setOfPred_mapsTo
    (isClosed_singleton.preimage f.continuous).isCompact (isOpen_discrete _)

/-- Pairing a map with a constant in the right component of a product is continuous, the mirror
image of Mathlib's `ContinuousMap.continuous_prodMk_const`, whose constant is the left component. -/
theorem continuous_prodMk_const_right {Z : Type*} [TopologicalSpace Z] :
    Continuous fun p : C(X, Y) × Z ↦ p.1.prodMk (const X p.2) := by
  have : (fun p : C(X, Y) × Z ↦ p.1.prodMk (const X p.2)) =
      fun p ↦ ContinuousMap.prodSwap.comp ((const X p.2).prodMk p.1) := by
    ext p x <;> rfl
  rw [this]
  exact (continuous_postcomp _).comp (continuous_prodMk_const.comp continuous_swap)

/-- Constant maps embed the target in the compact-open mapping space whenever the source is
nonempty. Evaluation at any point is a continuous left inverse. -/
theorem isEmbedding_const [Nonempty X] : Topology.IsEmbedding (const X : Y → C(X, Y)) :=
  Function.LeftInverse.isEmbedding (f := fun f : C(X, Y) ↦ f (Classical.arbitrary X))
    (fun _ ↦ rfl) (continuous_eval_const _) continuous_const'

variable {Z : Type*} [TopologicalSpace Z]

/-- The maps obtained by postcomposition with a topology inducing map `g` are exactly the maps
with values in the range of `g`. -/
theorem range_postcomp (g : C(Y, Z)) (hg : Topology.IsInducing g) :
    Set.range (g.comp : C(X, Y) → C(X, Z)) = {f | ∀ x, f x ∈ Set.range g} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun f x ↦ ⟨f x, rfl⟩) fun f hf ↦ ?_
  choose k hk using hf
  refine ⟨⟨k, hg.continuous_iff.2 ?_⟩, ext hk⟩
  simpa [Function.comp_def, hk] using f.continuous

/-- If `g : C(Y, Z)` is a closed embedding, then the composition
`ContinuousMap.comp g : C(X, Y) → C(X, Z)` is a closed embedding too. -/
theorem isClosedEmbedding_postcomp (g : C(Y, Z)) (hg : Topology.IsClosedEmbedding g) :
    Topology.IsClosedEmbedding (g.comp : C(X, Y) → C(X, Z)) := by
  refine ⟨isEmbedding_postcomp g hg.isEmbedding, ?_⟩
  simp only [range_postcomp g hg.isInducing, Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ hg.isClosed_range.preimage (continuous_eval_const x)

/-- Currying `C(X × Y, Z) → C(X, C(Y, Z))` is continuous whenever `X` is R₁ (for instance
Hausdorff), with no local compactness assumptions on `X` or `Y`. -/
theorem continuous_curry_of_r1 [R1Space X] :
    Continuous (curry : C(X × Y, Z) → C(X, C(Y, Z))) := by
  refine continuous_iff_continuousAt.2 fun f₀ ↦
    tendsto_nhds_compactOpen.2 fun K hK V hV hf₀ ↦ ?_
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  -- At each point of `K`, choose a basic compact-open neighborhood of `f₀.curry x` inside `V`
  -- and a compact neighborhood of `x` in `K` mapped into it.
  have hloc (x : K) : ∃ N : Set K, N ∈ nhds x ∧ IsCompact N ∧
      ∃ S : Set (Set Y × Set Z), S.Finite ∧
        (∀ L U, (L, U) ∈ S → IsCompact L ∧ IsOpen U ∧ Set.MapsTo f₀ ((Subtype.val '' N) ×ˢ L) U) ∧
        {g : C(Y, Z) | ∀ L U, (L, U) ∈ S → Set.MapsTo g L U} ⊆ V := by
    obtain ⟨S, hSf, hS, hSV⟩ := ContinuousMap.mem_nhds_iff.1 (hV.mem_nhds (hf₀ x.2))
    let B : Set C(Y, Z) := {g | ∀ L U, (L, U) ∈ S → Set.MapsTo g L U}
    have hB_open : IsOpen B := by
      have hBeq : B = ⋂ p ∈ S, {g : C(Y, Z) | Set.MapsTo g p.1 p.2} := by
        ext g
        simp [B]
      rw [hBeq]
      exact hSf.isOpen_biInter fun p hp ↦
        isOpen_setOfPred_mapsTo (hS p.1 p.2 hp).1 (hS p.1 p.2 hp).2.1
    have hpre : (f₀.curry ∘ Subtype.val) ⁻¹' B ∈ nhds x :=
      (hB_open.preimage (f₀.curry.continuous.comp continuous_subtype_val)).mem_nhds
        fun L U hp ↦ (hS L U hp).2.2
    obtain ⟨N, hNx, hNB, hNc⟩ := LocallyCompactSpace.local_compact_nhds x _ hpre
    refine ⟨N, hNx, hNc, S, hSf, fun L U hp ↦
      ⟨(hS L U hp).1, (hS L U hp).2.1, ?_⟩, hSV⟩
    rintro ⟨_, y⟩ ⟨⟨a, haN, rfl⟩, hyL⟩
    exact hNB haN L U hp hyL
  choose N hNx hNc S hSf hS hSV using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x : K ↦ N x) (fun x _ ↦ hNx x)
  have hev : ∀ᶠ f : C(X × Y, Z) in nhds f₀,
      ∀ x ∈ t, ∀ p ∈ S x, Set.MapsTo f ((Subtype.val '' N x) ×ˢ p.1) p.2 := by
    rw [Filter.eventually_all_finset]
    intro x _
    rw [(hSf x).eventually_all]
    intro p hp
    have hp' := hS x p.1 p.2 hp
    exact eventually_mapsTo (((hNc x).image continuous_subtype_val).prod hp'.1) hp'.2.1 hp'.2.2
  filter_upwards [hev] with f hf a haK
  obtain ⟨x, hxt, hax⟩ := Set.mem_iUnion₂.1 (ht.2 (Set.mem_univ (⟨a, haK⟩ : K)))
  exact hSV x fun L U hp y hyL ↦ hf x hxt (L, U) hp ⟨⟨⟨a, haK⟩, hax, rfl⟩, hyL⟩

/-- Uncurrying `C(X, C(Y, Z)) → C(X × Y, Z)` is continuous whenever `Y` is locally compact, with
no assumptions on `X` or `Z`. -/
theorem continuous_uncurry_of_locallyCompact [LocallyCompactSpace Y] :
    Continuous (uncurry : C(X, C(Y, Z)) → C(X × Y, Z)) := by
  classical
  refine continuous_iff_continuousAt.2 fun g₀ ↦
    tendsto_nhds_compactOpen.2 fun M hM U hU hg₀ ↦ ?_
  -- Cover `M` by finitely many boxes `W p ×ˢ interior (L p)` with `L p` compact and
  -- `g₀.uncurry (W p ×ˢ L p) ⊆ U`.
  have hloc (p : X × Y) (hp : p ∈ M) : ∃ W : Set X, IsOpen W ∧ p.1 ∈ W ∧
      ∃ L : Set Y, IsCompact L ∧ p.2 ∈ interior L ∧ Set.MapsTo g₀.uncurry (W ×ˢ L) U := by
    obtain ⟨W, V, hW, hV, hpW, hpV, hWV⟩ :=
      isOpen_prod_iff.1 (hU.preimage g₀.uncurry.continuous) p.1 p.2 (hg₀ hp)
    obtain ⟨L, hLnhds, hLV, hLc⟩ := LocallyCompactSpace.local_compact_nhds p.2 V (hV.mem_nhds hpV)
    exact ⟨W, hW, hpW, L, hLc, mem_interior_iff_mem_nhds.2 hLnhds,
      fun q hq ↦ hWV ⟨hq.1, hLV hq.2⟩⟩
  choose W hW hpW L hLc hpL hWL using fun p : M ↦ hloc p.1 p.2
  obtain ⟨t, ht⟩ := hM.elim_finite_subcover (fun p : M ↦ W p ×ˢ interior (L p))
    (fun p ↦ (hW p).prod isOpen_interior) fun p hp ↦
      Set.mem_iUnion.2 ⟨⟨p, hp⟩, ⟨hpW ⟨p, hp⟩, hpL ⟨p, hp⟩⟩⟩
  let B (p : M) : Set C(Y, Z) := {h | Set.MapsTo h (L p) U}
  have hB_open (p : M) : IsOpen (B p) := isOpen_setOfPred_mapsTo (hLc p) hU
  -- For each subset `S ⊆ t`, `K S` collects first coordinates of points in `M` avoiding
  -- `⋃ p ∈ S, interior (L p)`; `g₀` maps `K S` into `⋃ p ∈ t \ S, B p`.
  let N (S : Finset M) : Set (X × Y) := M \ ⋃ p ∈ S, Set.univ ×ˢ interior (L p)
  let K (S : Finset M) : Set X := Prod.fst '' N S
  let O (S : Finset M) : Set C(Y, Z) := ⋃ p ∈ t \ S, B p
  have hev : ∀ᶠ g : C(X, C(Y, Z)) in nhds g₀, ∀ S ∈ t.powerset, Set.MapsTo g (K S) (O S) := by
    rw [Filter.eventually_all_finset]
    intro S _
    refine eventually_mapsTo ?_ (isOpen_biUnion fun p _ ↦ hB_open p) ?_
    · exact (hM.diff (isOpen_biUnion fun _ _ ↦ isOpen_univ.prod isOpen_interior)).image
        continuous_fst
    · rintro x ⟨⟨x, y⟩, ⟨hxyM, hxyS⟩, rfl⟩
      obtain ⟨p, hpt, hxW, hyL⟩ := Set.mem_iUnion₂.1 (ht hxyM)
      refine Set.mem_iUnion₂.2 ⟨p, Finset.mem_sdiff.2 ⟨hpt, fun hpS ↦
        hxyS (Set.mem_iUnion₂.2 ⟨p, hpS, ⟨trivial, hyL⟩⟩)⟩,
        fun y' hy' ↦ hWL p (Set.mk_mem_prod hxW hy')⟩
  filter_upwards [hev] with g hg p hpM
  by_contra hgp
  let S : Finset M := t.filter fun q ↦ g p.1 ∈ B q
  have hpN : p ∈ N S := ⟨hpM, fun h ↦ by
    obtain ⟨q, hqS, _, hpq⟩ := Set.mem_iUnion₂.1 h
    exact hgp ((Finset.mem_filter.1 hqS).2 (interior_subset hpq))⟩
  obtain ⟨q, hqdiff, hqg⟩ := Set.mem_iUnion₂.1
    (hg S (Finset.mem_powerset.2 (Finset.filter_subset _ _)) ⟨p, hpN, rfl⟩)
  exact (Finset.mem_sdiff.1 hqdiff).2 (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hqdiff).1, hqg⟩)

end ContinuousMap

namespace Homeomorph

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Currying as a homeomorphism `C(X × Y, Z) ≃ₜ C(X, C(Y, Z))` when `X` is R₁ (for instance
Hausdorff) and `Y` is locally compact. -/
def curryOfR1 [R1Space X] [LocallyCompactSpace Y] : C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) where
  toFun := ContinuousMap.curry
  invFun := ContinuousMap.uncurry
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ContinuousMap.continuous_curry_of_r1
  continuous_invFun := ContinuousMap.continuous_uncurry_of_locallyCompact

@[simp]
theorem curryOfR1_apply [R1Space X] [LocallyCompactSpace Y] (f : C(X × Y, Z)) :
    curryOfR1 f = ContinuousMap.curry f := by
  rfl

@[simp]
theorem curryOfR1_symm_apply [R1Space X] [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) :
    curryOfR1.symm f = ContinuousMap.uncurry f := by
  rfl

end Homeomorph
