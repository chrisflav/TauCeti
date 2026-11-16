/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function

/-!
# Exact monotone-composition lifts

For an arbitrary domain `D : Set X`, a preordered codomain `Y` with outer domain `E : Set Y`,
an inner map `g : X → Y`, an outer map `h : Y → Z` into a preordered codomain `Z`, and a budget
`b : Z`, the composed sublevel set

    originalSet D g h b = {x ∈ D | h (g x) ≤ b}

admits the lifted reformulation

    liftedSet D E g h b = {(x, y) | x ∈ D ∧ y ∈ E ∧ g x ≤ y ∧ h y ≤ b}.

Whenever `g` maps `D` into `E` and `h` is monotone on `E`, the first projection maps the lifted
set onto the original set (`TauCeti.ConvexLifting.projection_eq`), with the canonical graph map
`x ↦ (x, g x)` providing the reverse witness. Convexity, differentiability, and compactness are
not required for this exact order identity.

Because the projection is exact, any objective pulled back along `Prod.fst` preserves feasible
minima (`TauCeti.ConvexLifting.feasible_minimum_iff`), attainment of feasible minima
(`TauCeti.ConvexLifting.attainment_iff`), lower bounds, and feasible objective values. When `g`
and `h` are convex on `D` and `E`, the lifted set is convex
(`TauCeti.ConvexLifting.convex_liftedSet`), and when in addition `g` maps `D` into `E` and `h`
is monotone on `E`, `originalSet` is convex (`TauCeti.ConvexLifting.convex_originalSet`).

## Main definitions

* `TauCeti.ConvexLifting.originalSet`: points in `D` satisfying `h (g x) ≤ b`.
* `TauCeti.ConvexLifting.liftedSet`: pairs `(x, y)` in `D ×ˢ E` satisfying `g x ≤ y` and
  `h y ≤ b`.

## Main statements

* `TauCeti.ConvexLifting.projection_eq`: exact projection `Prod.fst '' liftedSet = originalSet`
  under `Set.MapsTo g D E` and `MonotoneOn h E`.
* `TauCeti.ConvexLifting.mem_epigraph_comp_iff`: epigraph specialization of the lifted
  reformulation.
* `TauCeti.ConvexLifting.convex_liftedSet` and `TauCeti.ConvexLifting.convex_originalSet`:
  convexity of the lifted and original sets for convex inner and outer maps.
* `TauCeti.ConvexLifting.feasible_minimum_iff` and `TauCeti.ConvexLifting.attainment_iff`:
  equivalence of feasible minima and attainment for objectives pulled back along `Prod.fst`.

## References

* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global
  optimization*, Mathematical Programming 103 (2005), 225–249, §2, Proposition 1, pp. 226–227.
* M. Lubin, E. Yamangil, R. Bent, and J. P. Vielma, *Extended Formulations in Mixed-integer
  Convex Programming*, IPCO 2016, arXiv:1511.06710v3, §4, p. 9.
-/

public section

open Set

namespace TauCeti.ConvexLifting

/-! ### Sets and basic membership -/

section Defs

variable {X Y Z : Type*}

/-- Points in `D` satisfying the composed inequality `h (g x) ≤ b`. -/
def originalSet [LE Z] (D : Set X) (g : X → Y) (h : Y → Z) (b : Z) : Set X :=
  {x | x ∈ D ∧ h (g x) ≤ b}

/-- Admissible pairs `(x, y)` in `D ×ˢ E` with upper height `g x ≤ y` satisfying `h y ≤ b`. -/
def liftedSet [LE Y] [LE Z] (D : Set X) (E : Set Y) (g : X → Y) (h : Y → Z) (b : Z) :
    Set (X × Y) :=
  {p | p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b}

/-- Definitional unfolding of `originalSet`. -/
theorem originalSet_def [LE Z] (D : Set X) (g : X → Y) (h : Y → Z) (b : Z) :
    originalSet D g h b = {x | x ∈ D ∧ h (g x) ≤ b} :=
  (rfl)

/-- Definitional unfolding of `liftedSet`. -/
theorem liftedSet_def [LE Y] [LE Z] (D : Set X) (E : Set Y) (g : X → Y) (h : Y → Z) (b : Z) :
    liftedSet D E g h b = {p | p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b} :=
  (rfl)

/-- Membership in `originalSet` keeps the domain and composed inequality explicit. -/
@[simp]
theorem mem_originalSet_iff [LE Z] {D : Set X} {g : X → Y} {h : Y → Z} {b : Z} {x : X} :
    x ∈ originalSet D g h b ↔ x ∈ D ∧ h (g x) ≤ b :=
  Iff.rfl

/-- Membership in `liftedSet` retains both domains together with the lifting and budget
inequalities. -/
@[simp]
theorem mem_liftedSet_iff [LE Y] [LE Z] {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}
    {p : X × Y} :
    p ∈ liftedSet D E g h b ↔ p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b :=
  Iff.rfl

/-- `originalSet` is contained in its domain `D`. -/
theorem originalSet_subset [LE Z] {D : Set X} {g : X → Y} {h : Y → Z} {b : Z} :
    originalSet D g h b ⊆ D :=
  fun _ hx => hx.1

/-- `liftedSet` is contained in the product of its domains `D ×ˢ E`. -/
theorem liftedSet_subset_prod [LE Y] [LE Z] {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z}
    {b : Z} :
    liftedSet D E g h b ⊆ D ×ˢ E :=
  fun _ hp => ⟨hp.1, hp.2.1⟩

/-- Enlarging the domain enlarges `originalSet`. -/
theorem originalSet_mono_domain [LE Z] {D₁ D₂ : Set X} {g : X → Y} {h : Y → Z} {b : Z}
    (hD : D₁ ⊆ D₂) :
    originalSet D₁ g h b ⊆ originalSet D₂ g h b :=
  fun _ hx => ⟨hD hx.1, hx.2⟩

/-- Enlarging the budget enlarges `originalSet`. -/
theorem originalSet_mono_budget [Preorder Z] {D : Set X} {g : X → Y} {h : Y → Z} {b₁ b₂ : Z}
    (hb : b₁ ≤ b₂) :
    originalSet D g h b₁ ⊆ originalSet D g h b₂ :=
  fun _ hx => ⟨hx.1, hx.2.trans hb⟩

/-- Enlarging either domain enlarges `liftedSet`. -/
theorem liftedSet_mono_domain [LE Y] [LE Z] {D₁ D₂ : Set X} {E₁ E₂ : Set Y} {g : X → Y}
    {h : Y → Z} {b : Z} (hD : D₁ ⊆ D₂) (hE : E₁ ⊆ E₂) :
    liftedSet D₁ E₁ g h b ⊆ liftedSet D₂ E₂ g h b :=
  fun _ hp => ⟨hD hp.1, hE hp.2.1, hp.2.2⟩

/-- Enlarging the budget enlarges `liftedSet`. -/
theorem liftedSet_mono_budget [LE Y] [Preorder Z] {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z}
    {b₁ b₂ : Z} (hb : b₁ ≤ b₂) :
    liftedSet D E g h b₁ ⊆ liftedSet D E g h b₂ :=
  fun _ hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.trans hb⟩

end Defs

/-! ### Graph insertion and exact projection -/

section Projection

variable {X Y Z : Type*} [Preorder Y]

/-- Every point `x ∈ originalSet D g h b` whose image `g x` lies in `E` lifts via its graph
point `(x, g x)` into `liftedSet D E g h b`. -/
theorem graph_mem_liftedSet [LE Z] {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}
    {x : X} (hx : x ∈ originalSet D g h b) (hgx : g x ∈ E) :
    (x, g x) ∈ liftedSet D E g h b :=
  ⟨hx.1, hgx, le_rfl, hx.2⟩

/-- The canonical graph map sends `originalSet D g h b` into `liftedSet D E g h b` whenever `g`
maps `originalSet D g h b` into `E`. -/
theorem mapsTo_graph_liftedSet [LE Z] {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}
    (hg : MapsTo g (originalSet D g h b) E) :
    MapsTo (fun x => (x, g x)) (originalSet D g h b) (liftedSet D E g h b) :=
  fun _ hx => graph_mem_liftedSet hx (hg hx)

variable [Preorder Z]

/-- Forward projection of a point in `liftedSet`: monotonicity of `h` on `E` transfers the outer
budget from `p.2` back to `g p.1`. -/
theorem fst_mem_originalSet {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}
    {p : X × Y} (hp : p ∈ liftedSet D E g h b) (hg : g p.1 ∈ E) (hm : MonotoneOn h E) :
    p.1 ∈ originalSet D g h b :=
  ⟨hp.1, (hm hg hp.2.1 hp.2.2.1).trans hp.2.2.2⟩

/-- Under `MapsTo g D E` and `MonotoneOn h E`, the first projection maps `liftedSet` into
`originalSet`. -/
theorem mapsTo_fst_liftedSet {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}
    (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    MapsTo Prod.fst (liftedSet D E g h b) (originalSet D g h b) :=
  fun _ hp => fst_mem_originalSet hp (hg hp.1) hm

/-- **Exact projection of monotone-composition lifts.** Under `MapsTo g D E` and `MonotoneOn h E`,
the first projection of `liftedSet D E g h b` equals `originalSet D g h b`. -/
theorem projection_eq {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}
    (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    Prod.fst '' liftedSet D E g h b = originalSet D g h b := by
  refine Subset.antisymm (mapsTo_fst_liftedSet hg hm).image_subset ?_
  intro x hx
  exact ⟨(x, g x), graph_mem_liftedSet hx (hg hx.1), rfl⟩

/-- Pointwise existential criterion for membership in `originalSet`. -/
theorem exists_mem_liftedSet_iff {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}
    {x : X} (hg : x ∈ D → g x ∈ E) (hm : MonotoneOn h E) :
    (∃ y, (x, y) ∈ liftedSet D E g h b) ↔ x ∈ originalSet D g h b := by
  constructor
  · rintro ⟨y, hy⟩
    exact fst_mem_originalSet hy (hg hy.1) hm
  · intro hx
    exact ⟨g x, graph_mem_liftedSet hx (hg hx.1)⟩

/-- `liftedSet` is nonempty if and only if `originalSet` is nonempty. -/
theorem liftedSet_nonempty_iff {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}
    (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    (liftedSet D E g h b).Nonempty ↔ (originalSet D g h b).Nonempty := by
  rw [← projection_eq hg hm, image_nonempty]

/-- `liftedSet` is empty if and only if `originalSet` is empty. -/
theorem liftedSet_eq_empty_iff {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}
    (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    liftedSet D E g h b = ∅ ↔ originalSet D g h b = ∅ := by
  rw [← projection_eq hg hm, image_eq_empty]

/-- Epigraph specialization of the exact lifting criterion: `(x, t)` lies in the epigraph of
`h ∘ g` on `D` if and only if there is an admissible intermediate height `y ∈ E` with `g x ≤ y`
and `h y ≤ t`. -/
theorem mem_epigraph_comp_iff {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z}
    {x : X} {t : Z} (hg : x ∈ D → g x ∈ E) (hm : MonotoneOn h E) :
    (x, t) ∈ {p : X × Z | p.1 ∈ D ∧ h (g p.1) ≤ p.2} ↔
      ∃ y ∈ E, x ∈ D ∧ g x ≤ y ∧ h y ≤ t := by
  rw [mem_ofPred_eq, ← mem_originalSet_iff, ← exists_mem_liftedSet_iff hg hm]
  simp only [mem_liftedSet_iff]
  grind

end Projection

/-! ### Convexity of lifted and original sets -/

section Convex

variable {𝕜 X Y Z : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid X] [SMul 𝕜 X]
  [AddCommMonoid Y] [PartialOrder Y] [SMul 𝕜 Y]
  [AddCommMonoid Z] [PartialOrder Z] [IsOrderedAddMonoid Z] [Module 𝕜 Z] [PosSMulMono 𝕜 Z]

/-- When `g` is convex on `D` and `h` is convex on `E`, `liftedSet D E g h b` is convex.
Neither `MapsTo g D E` nor monotonicity of `h` is required for convexity of the lifted set. -/
theorem convex_liftedSet [IsOrderedAddMonoid Y] [PosSMulMono 𝕜 Y]
    {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}
    (hg : ConvexOn 𝕜 D g) (hh : ConvexOn 𝕜 E h) :
    Convex 𝕜 (liftedSet D E g h b) := by
  rintro ⟨x₁, y₁⟩ ⟨hx₁, hy₁, hgx₁, hhy₁⟩ ⟨x₂, y₂⟩ ⟨hx₂, hy₂, hgx₂, hhy₂⟩ a c ha hc hac
  have hsub := hh.convex_le b ⟨hy₁, hhy₁⟩ ⟨hy₂, hhy₂⟩ ha hc hac
  refine ⟨hg.1 hx₁ hx₂ ha hc hac, hsub.1, ?_, hsub.2⟩
  calc
    g (a • x₁ + c • x₂) ≤ a • g x₁ + c • g x₂ := hg.2 hx₁ hx₂ ha hc hac
    _ ≤ a • y₁ + c • y₂ := by gcongr

/-- When `g` is convex on `D`, `h` is convex and monotone on `E`, and `g` maps `D` into `E`,
the original set `originalSet D g h b` is convex. -/
theorem convex_originalSet {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}
    (hgE : MapsTo g D E) (hm : MonotoneOn h E)
    (hg : ConvexOn 𝕜 D g) (hh : ConvexOn 𝕜 E h) :
    Convex 𝕜 (originalSet D g h b) := by
  intro x₁ hx₁ x₂ hx₂ a c ha hc hac
  have hxD : a • x₁ + c • x₂ ∈ D := hg.1 hx₁.1 hx₂.1 ha hc hac
  have hsub := hh.convex_le b ⟨hgE hx₁.1, hx₁.2⟩ ⟨hgE hx₂.1, hx₂.2⟩ ha hc hac
  exact ⟨hxD, (hm (hgE hxD) hsub.1 (hg.2 hx₁.1 hx₂.1 ha hc hac)).trans hsub.2⟩

end Convex

/-! ### Feasible minima, attainment, and objective bounds -/

section Minima

variable {X Y Z β : Type*} [Preorder Y] [Preorder Z]
  {D : Set X} {E : Set Y} {g : X → Y} {h : Y → Z} {b : Z}

/-- An objective pulled back along `Prod.fst` has the same image on `liftedSet` as the original
objective has on `originalSet`. -/
theorem image_comp_fst_liftedSet (hg : MapsTo g D E) (hm : MonotoneOn h E) (f : X → β) :
    (f ∘ Prod.fst) '' liftedSet D E g h b = f '' originalSet D g h b := by
  rw [image_comp, projection_eq hg hm]

/-- Lower bounds on `f ∘ Prod.fst` over `liftedSet` coincide with lower bounds on `f` over
`originalSet`. -/
theorem forall_le_comp_fst_liftedSet_iff [LE β] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → β) (c : β) :
    (∀ p ∈ liftedSet D E g h b, c ≤ f p.1) ↔ ∀ x ∈ originalSet D g h b, c ≤ f x := by
  constructor
  · intro hc x hx
    exact hc (x, g x) (graph_mem_liftedSet hx (hg hx.1))
  · intro hc p hp
    exact hc p.1 (fst_mem_originalSet hp (hg hp.1) hm)

/-- Existence of a feasible point with objective value at most `c` transfers between `liftedSet`
and `originalSet`. -/
theorem exists_comp_fst_le_liftedSet_iff [LE β] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → β) (c : β) :
    (∃ p ∈ liftedSet D E g h b, f p.1 ≤ c) ↔ ∃ x ∈ originalSet D g h b, f x ≤ c := by
  constructor
  · rintro ⟨p, hp, hpc⟩
    exact ⟨p.1, fst_mem_originalSet hp (hg hp.1) hm, hpc⟩
  · rintro ⟨x, hx, hxc⟩
    exact ⟨(x, g x), graph_mem_liftedSet hx (hg hx.1), hxc⟩

/-- `IsMinOn` for a pulled-back objective on `liftedSet` is equivalent to `IsMinOn` at the first
coordinate on `originalSet`. -/
theorem isMinOn_liftedSet_iff [Preorder β] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → β) (p : X × Y) :
    IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p ↔ IsMinOn f (originalSet D g h b) p.1 := by
  constructor
  · intro hmin
    have hgraph : MapsTo (fun x => (x, g x)) (originalSet D g h b) (liftedSet D E g h b) :=
      mapsTo_graph_liftedSet (hg.mono_left originalSet_subset)
    exact fun x hx => hmin (hgraph hx)
  · intro hmin
    exact hmin.comp_of_mapsTo (mapsTo_fst_liftedSet hg hm) rfl

/-- A pair `p` is a feasible minimum of `f ∘ Prod.fst` on `liftedSet` if and only if `p` is
feasible in `liftedSet` and `p.1` is a feasible minimum of `f` on `originalSet`. Feasibility is
retained explicitly because `IsMinOn` alone does not assert membership. -/
theorem feasible_minimum_iff [Preorder β] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → β) (p : X × Y) :
    (p ∈ liftedSet D E g h b ∧ IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p) ↔
      p ∈ liftedSet D E g h b ∧ p.1 ∈ originalSet D g h b ∧
        IsMinOn f (originalSet D g h b) p.1 := by
  constructor
  · rintro ⟨hp, hmin⟩
    exact ⟨hp, fst_mem_originalSet hp (hg hp.1) hm, (isMinOn_liftedSet_iff hg hm f p).1 hmin⟩
  · rintro ⟨hp, _, hmin⟩
    exact ⟨hp, (isMinOn_liftedSet_iff hg hm f p).2 hmin⟩

/-- Existence of an attained feasible minimum transfers in both directions between `liftedSet`
and `originalSet`, without assuming attainment holds. -/
theorem attainment_iff [Preorder β] (hg : MapsTo g D E) (hm : MonotoneOn h E) (f : X → β) :
    (∃ p ∈ liftedSet D E g h b, IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p) ↔
      ∃ x ∈ originalSet D g h b, IsMinOn f (originalSet D g h b) x := by
  constructor
  · rintro ⟨p, hp, hmin⟩
    have h := (feasible_minimum_iff hg hm f p).1 ⟨hp, hmin⟩
    exact ⟨p.1, h.2.1, h.2.2⟩
  · rintro ⟨x, hx, hmin⟩
    exact ⟨(x, g x), graph_mem_liftedSet hx (hg hx.1),
      (isMinOn_liftedSet_iff hg hm f (x, g x)).2 hmin⟩

end Minima

end TauCeti.ConvexLifting
