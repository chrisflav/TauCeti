/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing
import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Basic
import TauCeti.KnotTheory.Grid.Rectangle.Count

/-!
# Uniqueness of two-step grid rectangle decompositions of a domain

In the grid differential `∂⁻`, every two-step term pairs with a partner that covers the same
multiset of squares: commuting the two moves when their side columns are disjoint, or recutting the
L-shaped union when they share one side column. The square rule for a grid sign assignment states
the converse direction as a universal quantifier over all distinct decompositions `E ≠ D` sharing
the same covered-square multiset as `D`.

This file classifies all two-step decompositions `E` with the same endpoints and covered-square
multiset as `D`:

* when `z = x` (annular domain), `E = D` is forced — there is no other decomposition of the same
  vertical or horizontal annulus;
* when `D` has disjoint side columns, `E = D` or `E = D.commute h`;
* when `D` has one common side column and the relevant rectangles are empty, `E = D` or
  `D.IsRecut E`.

Thus no third decomposition can ever share the covered-square multiset of two empty rectangles, and
checking the square rule for a candidate sign assignment reduces to checking the disjoint-commute
and one-common-side recut pairs.

## Main results

* `TauCeti.GridRectangleDecomposition.eq_of_middle_eq_of_coveredSquares_add_eq`: two nondiagonal
  decompositions with the same intermediate state and covered-square multiset are equal.
* `TauCeti.GridRectangleDecomposition.eq_of_coveredSquares_add_eq_self`: two diagonal
  decompositions with the same covered-square multiset are equal.
* `TauCeti.GridRectangleDecomposition.IsRecut.symm_sameSide_of_hasMixedSideOverlap`: reversing a
  recut of a mixed-side overlap produces a same-side overlap recut.
* `TauCeti.GridRectangleDecomposition.eq_or_eq_commute_of_hasDisjointSides_of_coveredSquares_add_eq`
  and `eq_or_isRecut_of_hasOneCommonSide_of_coveredSquares_add_eq`: a decomposition with the same
  covered-square multiset as a disjoint-side or empty one-common-side decomposition is either the
  same decomposition or its paired partner.
* `TauCeti.GridRectangleDecomposition.eq_commute_or_isRecut_of_coveredSquares_add_eq`: combined
  classification of all empty decompositions sharing a covered-square multiset.

## References

* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Section 4.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 4.6 and Section 15.2.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-! ### Auxiliary geometric lemmas -/

private theorem disjoint_coveredSquares_swapSides {u v : GridState n}
    (R : GridRectangleBetween u v) :
    Disjoint R.toGridRectangle.coveredSquares R.swapSides.toGridRectangle.coveredSquares := by
  rw [GridRectangle.disjoint_coveredSquares_iff]
  left
  simpa [GridRectangle.coveredColumns_def] using Grid.disjoint_cIco_swap R.left R.right

private theorem left_bottom_mem_coveredSquares {u v : GridState n}
    (R : GridRectangleBetween u v) :
    (R.left, R.bottom) ∈ R.toGridRectangle.coveredSquares :=
  (R.toGridRectangle.mem_coveredSquares _).mpr
    ⟨(R.toGridRectangle.mem_coveredColumns _).mpr (Grid.left_mem_cIco R.left_ne_right),
      (R.toGridRectangle.mem_coveredRows _).mpr (Grid.left_mem_cIco R.bottom_ne_top)⟩

private theorem coveredSquares_swapSides_ne {u v : GridState n}
    (R : GridRectangleBetween u v) :
    R.swapSides.toGridRectangle.coveredSquares ≠ R.toGridRectangle.coveredSquares := fun h =>
  Finset.disjoint_left.mp (disjoint_coveredSquares_swapSides R) (left_bottom_mem_coveredSquares R)
    (h.symm ▸ left_bottom_mem_coveredSquares R)

private theorem mem_coveredSquares_or_of_add_eq {D E : GridRectangleDecomposition x z}
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val)
    {p : Fin n × Fin n} (hp : p ∈ E.first.toGridRectangle.coveredSquares) :
    p ∈ D.first.toGridRectangle.coveredSquares ∨
      p ∈ D.second.toGridRectangle.coveredSquares := by
  have hmem : p ∈ D.first.toGridRectangle.coveredSquares.val +
      D.second.toGridRectangle.coveredSquares.val := by
    rw [← hdomain]
    exact Multiset.mem_add.mpr (Or.inl hp)
  exact Multiset.mem_add.mp hmem

/-! ### Same intermediate state and diagonal domains -/

private theorem coveredColumns_eq_of_coveredSquares_eq {u₁ v₁ u₂ v₂ : GridState n}
    (R₁ : GridRectangleBetween u₁ v₁) (R₂ : GridRectangleBetween u₂ v₂)
    (h : R₁.toGridRectangle.coveredSquares = R₂.toGridRectangle.coveredSquares) :
    Grid.cIco R₁.left R₁.right = Grid.cIco R₂.left R₂.right := by
  ext c
  constructor
  · intro hc
    have hmem : (c, R₁.bottom) ∈ R₂.toGridRectangle.coveredSquares :=
      h ▸ (R₁.toGridRectangle.mem_coveredSquares _).mpr
        ⟨(R₁.toGridRectangle.mem_coveredColumns _).mpr hc,
          (R₁.toGridRectangle.mem_coveredRows _).mpr (Grid.left_mem_cIco R₁.bottom_ne_top)⟩
    exact (R₂.toGridRectangle.mem_coveredColumns _).mp
      ((R₂.toGridRectangle.mem_coveredSquares _).mp hmem).1
  · intro hc
    have hmem : (c, R₂.bottom) ∈ R₁.toGridRectangle.coveredSquares :=
      h.symm ▸ (R₂.toGridRectangle.mem_coveredSquares _).mpr
        ⟨(R₂.toGridRectangle.mem_coveredColumns _).mpr hc,
          (R₂.toGridRectangle.mem_coveredRows _).mpr (Grid.left_mem_cIco R₂.bottom_ne_top)⟩
    exact (R₁.toGridRectangle.mem_coveredColumns _).mp
      ((R₁.toGridRectangle.mem_coveredSquares _).mp hmem).1

/-- Two nondiagonal two-step rectangle decompositions with the same intermediate state and the
same covered-square multiset are equal. -/
theorem eq_of_middle_eq_of_coveredSquares_add_eq {D E : GridRectangleDecomposition x z}
    (hzx : z ≠ x) (hmiddle : E.middle = D.middle)
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    E = D := by
  cases D with
  | mk Dm D₁ D₂ =>
    cases E with
    | mk Em E₁ E₂ =>
      dsimp only at hmiddle hdomain
      subst Em
      rcases D₁.eq_or_eq_swapSides E₁ with rfl | rfl <;>
        rcases D₂.eq_or_eq_swapSides E₂ with rfl | rfl
      · rfl
      · exfalso
        exact coveredSquares_swapSides_ne D₂ (Finset.val_inj.mp (add_left_cancel hdomain))
      · exfalso
        exact coveredSquares_swapSides_ne D₁ (Finset.val_inj.mp (add_right_cancel hdomain))
      · exfalso
        have hsq : D₁.toGridRectangle.coveredSquares =
            D₂.swapSides.toGridRectangle.coveredSquares := by
          refine Finset.Subset.antisymm (fun p hp => ?_) (fun p hp => ?_)
          · have hmem : p ∈ D₁.swapSides.toGridRectangle.coveredSquares.val +
                D₂.swapSides.toGridRectangle.coveredSquares.val := by
              rw [hdomain]; exact Multiset.mem_add.mpr (Or.inl hp)
            exact (Multiset.mem_add.mp hmem).resolve_left
              (Finset.disjoint_left.mp (disjoint_coveredSquares_swapSides D₁) hp)
          · have hmem : p ∈ D₁.toGridRectangle.coveredSquares.val +
                D₂.toGridRectangle.coveredSquares.val := by
              rw [← hdomain]; exact Multiset.mem_add.mpr (Or.inr hp)
            exact (Multiset.mem_add.mp hmem).resolve_right
              (Finset.disjoint_right.mp (disjoint_coveredSquares_swapSides D₂) hp)
        have hcol := coveredColumns_eq_of_coveredSquares_eq D₁ D₂.swapSides hsq
        rw [D₂.swapSides_left, D₂.swapSides_right] at hcol
        obtain ⟨hl, hr⟩ :=
          (Grid.cIco_eq_cIco_iff D₁.left_ne_right D₂.left_ne_right.symm).mp hcol
        exact hzx ((target_eq_source_iff_sideColumns_eq ⟨Dm, D₁, D₂⟩).mpr <| by
          simp [GridRectangleBetween.sideColumns, hl, hr, Finset.pair_comm])

/-- Two diagonal two-step rectangle decompositions covering the same multiset of squares are
equal. -/
theorem eq_of_coveredSquares_add_eq_self {D E : GridRectangleDecomposition x x}
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    E = D := by
  have hunion :
      E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares =
        D.first.toGridRectangle.coveredSquares ∪ D.second.toGridRectangle.coveredSquares := by
    rw [← Finset.val_inj, Finset.union_val, Finset.union_val,
      ← Multiset.add_eq_union_iff_disjoint.mpr
        (Finset.disjoint_val.mpr (E.first.disjoint_coveredSquares E.second)),
      ← Multiset.add_eq_union_iff_disjoint.mpr
        (Finset.disjoint_val.mpr (D.first.disjoint_coveredSquares D.second)), hdomain]
  rcases D.first.left_right_eq_cases D.second with ⟨hDl, _⟩ | ⟨hDl, _⟩ <;>
    rcases E.first.left_right_eq_cases E.second with ⟨hEl, _⟩ | ⟨hEl, _⟩
  · rw [E.first.coveredSquares_union_coveredSquares_of_left_eq_left E.second hEl,
      D.first.coveredSquares_union_coveredSquares_of_left_eq_left D.second hDl] at hunion
    have hcol : Grid.cIco E.first.left E.first.right = Grid.cIco D.first.left D.first.right := by
      ext c
      have hiff := Finset.ext_iff.mp hunion (c, D.first.bottom)
      simpa [Finset.mem_product, GridRectangle.mem_coveredColumns] using hiff
    obtain ⟨hl, hr⟩ :=
      (Grid.cIco_eq_cIco_iff E.first.left_ne_right D.first.left_ne_right).mp hcol
    exact GridRectangleDecomposition.ext hl hr (hEl.trans (hl.trans hDl.symm))
  · exfalso
    rw [E.first.coveredSquares_union_coveredSquares_of_left_eq_right E.second hEl,
      D.first.coveredSquares_union_coveredSquares_of_left_eq_left D.second hDl] at hunion
    have hmem : (D.first.right, E.first.bottom) ∈
        D.first.toGridRectangle.coveredColumns ×ˢ (Finset.univ : Finset (Fin n)) := by
      rw [← hunion]
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
        (E.first.toGridRectangle.mem_coveredRows _).mpr
          (Grid.left_mem_cIco E.first.bottom_ne_top)⟩
    exact Grid.right_notMem_cIco D.first.left D.first.right
      ((D.first.toGridRectangle.mem_coveredColumns _).mp (Finset.mem_product.mp hmem).1)
  · exfalso
    rw [E.first.coveredSquares_union_coveredSquares_of_left_eq_left E.second hEl,
      D.first.coveredSquares_union_coveredSquares_of_left_eq_right D.second hDl] at hunion
    have hmem : (E.first.right, D.first.bottom) ∈
        E.first.toGridRectangle.coveredColumns ×ˢ (Finset.univ : Finset (Fin n)) := by
      rw [hunion]
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
        (D.first.toGridRectangle.mem_coveredRows _).mpr
          (Grid.left_mem_cIco D.first.bottom_ne_top)⟩
    exact Grid.right_notMem_cIco E.first.left E.first.right
      ((E.first.toGridRectangle.mem_coveredColumns _).mp (Finset.mem_product.mp hmem).1)
  · rw [E.first.coveredSquares_union_coveredSquares_of_left_eq_right E.second hEl,
      D.first.coveredSquares_union_coveredSquares_of_left_eq_right D.second hDl] at hunion
    have hrow : Grid.cIco E.first.bottom E.first.top = Grid.cIco D.first.bottom D.first.top := by
      ext r
      have hiff := Finset.ext_iff.mp hunion (D.first.left, r)
      simpa [Finset.mem_product, GridRectangle.mem_coveredRows] using hiff
    obtain ⟨hb, ht⟩ :=
      (Grid.cIco_eq_cIco_iff E.first.bottom_ne_top D.first.bottom_ne_top).mp hrow
    have hl : E.first.left = D.first.left := x.toPerm.injective hb
    have hr : E.first.right = D.first.right := x.toPerm.injective ht
    exact GridRectangleDecomposition.ext hl hr (hEl.trans (hr.trans hDl.symm))

/-! ### Disjoint-side domains -/

private theorem middle_eq_or_eq_commute_middle_of_hasDisjointSides
    {D E : GridRectangleDecomposition x z} (h : D.HasDisjointSides) :
    E.middle = D.middle ∨ E.middle = (D.commute h).middle := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp h
  have hdisj : Disjoint ({D.first.left, D.first.right} : Finset (Fin n))
      {D.second.left, D.second.right} := by
    simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨⟨hll, hlr⟩, hrl, hrr⟩
  have hz : z = (x.swapColumns D.first.left D.first.right).swapColumns
      D.second.left D.second.right :=
    D.second.target_eq_swapColumns.trans
      (congrArg (·.swapColumns D.second.left D.second.right) D.first.target_eq_swapColumns)
  have hEdisj : E.HasDisjointSides := by
    have key : ∀ (z' : GridState n) (E' : GridRectangleDecomposition x z'),
        z' = (x.swapColumns D.first.left D.first.right).swapColumns
          D.second.left D.second.right → E'.HasDisjointSides := by
      rintro z' E' rfl
      exact hasDisjointSides_of_disjoint x D.first.left_ne_right D.second.left_ne_right hdisj E'
    exact key z E hz
  obtain ⟨hEll, hElr, _, _⟩ := E.hasDisjointSides_iff.mp hEdisj
  have hzE : z E.first.left = x E.first.right := by
    rw [E.second.map_of_ne E.first.left hEll hElr, E.first.map_left]
  have hmem : E.first.left ∈ D.first.sideColumns ∨ E.first.left ∈ D.second.sideColumns := by
    by_contra hnot
    rw [not_or] at hnot
    have hfix := D.target_apply_of_notMem_sideColumns hnot.1 hnot.2
    exact E.first.left_ne_right (x.toPerm.injective (hfix.symm.trans hzE))
  have hswap : ∀ {u v : Fin n}, z u = x v → E.first.left = u → E.first.right = v := by
    intro u v huv hu
    exact x.toPerm.injective (hzE.symm.trans (hu ▸ huv))
  simp only [GridRectangleBetween.mem_sideColumns] at hmem
  rcases hmem with (h1 | h1) | (h1 | h1)
  · left
    have h2 : E.first.right = D.first.right := hswap (by
      rw [D.second.map_of_ne D.first.left hll hlr, D.first.map_left]) h1
    rw [E.first.target_eq_swapColumns, D.first.target_eq_swapColumns, h1, h2]
  · left
    have h2 : E.first.right = D.first.left := hswap (by
      rw [D.second.map_of_ne D.first.right hrl hrr, D.first.map_right]) h1
    rw [E.first.target_eq_swapColumns, D.first.target_eq_swapColumns, h1, h2,
      GridState.swapColumns_comm]
  · right
    have h2 : E.first.right = D.second.right := hswap (by
      rw [D.second.map_left, D.first.map_of_ne D.second.right hlr.symm hrr.symm]) h1
    rw [E.first.target_eq_swapColumns, D.commute_middle h, h1, h2]
  · right
    have h2 : E.first.right = D.second.left := hswap (by
      rw [D.second.map_right, D.first.map_of_ne D.second.left hll.symm hrl.symm]) h1
    rw [E.first.target_eq_swapColumns, D.commute_middle h, h1, h2, GridState.swapColumns_comm]

/-- If `D` has disjoint side columns, then any two-step decomposition with the same endpoints and
covered-square multiset is either `D` or `D.commute h`. -/
theorem eq_or_eq_commute_of_hasDisjointSides_of_coveredSquares_add_eq
    {D E : GridRectangleDecomposition x z} (h : D.HasDisjointSides)
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    E = D ∨ E = D.commute h := by
  have hzx := D.target_ne_source_of_hasDisjointSides h
  rcases middle_eq_or_eq_commute_middle_of_hasDisjointSides h (E := E) with hmid | hmid
  · exact Or.inl (eq_of_middle_eq_of_coveredSquares_add_eq hzx hmid hdomain)
  · right
    refine eq_of_middle_eq_of_coveredSquares_add_eq hzx hmid ?_
    rw [D.commute_first_toGridRectangle h, D.commute_second_toGridRectangle h]
    exact hdomain.trans (add_comm _ _)

/-! ### One-common-side domains -/

/-- If `E`'s first side columns lie in `{p, q, r}` and its intermediate state avoids both swaps
involving `r`, then its ordered side columns are `(p, q)` or `(q, p)`. -/
private theorem first_sides_eq_of_mem_triple_of_ne_swaps {E : GridRectangleDecomposition x z}
    {p q r : Fin n} (hsub : E.first.sideColumns ⊆ {p, q, r})
    (h1 : E.middle ≠ x.swapColumns p r) (h2 : E.middle ≠ x.swapColumns q r) :
    (E.first.left = p ∧ E.first.right = q) ∨ (E.first.left = q ∧ E.first.right = p) := by
  have hEl : E.first.left ∈ ({p, q, r} : Finset (Fin n)) := hsub (by simp)
  have hEr : E.first.right ∈ ({p, q, r} : Finset (Fin n)) := hsub (by simp)
  have hne := E.first.left_ne_right
  have hmid := E.first.target_eq_swapColumns
  have hcomm := fun u v => GridState.swapColumns_comm (x := x) u v
  simp only [Finset.mem_insert, Finset.mem_singleton] at hEl hEr
  grind

private theorem not_middle_third_of_left_eq_left {D E : GridRectangleDecomposition x z}
    (hcommon : D.first.left = D.second.left) (hother : D.first.right ≠ D.second.right)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val)
    (hmidD : E.middle ≠ D.middle)
    (hmidR : E.middle ≠
      (D.recut (D.hasOneCommonSide_of_left_eq_left hcommon hother) hD₁ hD₂).middle) :
    False := by
  set a := D.first.left; set b := D.first.right; set c := D.second.right
  have hac : a ≠ c := hcommon ▸ D.second.left_ne_right
  have hD₂top : D.second.top = x c := by
    rw [GridRectangleBetween.top_def, D.first.map_of_ne c hac.symm hother.symm]
  have hrow : x b ∈ Grid.cIoo (x a) (x c) := by
    have hord := (D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon hother hD₁ hD₂).2
    rw [hD₂top] at hord
    exact hord
  have hone := D.hasOneCommonSide_of_left_eq_left hcommon hother
  have hEsub : E.first.sideColumns ⊆ {a, b, c} := by
    intro u hu
    have hmem : u ∈ D.first.sideColumns ∪ D.second.sideColumns := by
      rw [D.sideColumns_union_eq_of_hasOneCommonSide E hone]
      exact Finset.mem_union_left _ hu
    simp only [Finset.mem_union, GridRectangleBetween.mem_sideColumns, ← hcommon,
      Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    tauto
  have hmidD' : E.middle ≠ x.swapColumns a b := D.first.target_eq_swapColumns ▸ hmidD
  rcases (D.isRecutOfLeftEqLeft_recut hcommon hone hD₁ hD₂).recut_branch with
    ⟨hcol, hRmid, -, -⟩ | ⟨hcol, hRmid, -, -⟩
  · have hcases := first_sides_eq_of_mem_triple_of_ne_swaps (p := a) (q := c) (r := b)
      (fun u hu => by
        have := hEsub hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
        tauto)
      hmidD' (by rw [GridState.swapColumns_comm]; exact hRmid ▸ hmidR)
    rcases hcases with ⟨hl, hr⟩ | ⟨hl, -⟩
    · exact (E.first.isEmpty_iff_forall_notMem_cIoo).mp hE₁ b (hl ▸ hr ▸ hcol)
        (by simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hl, hr]
          using hrow)
    · have hp : (c, x c) ∈ E.first.toGridRectangle.coveredSquares := by
        simpa only [hl, GridRectangleBetween.bottom_def] using
          left_bottom_mem_coveredSquares E.first
      rcases mem_coveredSquares_or_of_add_eq hdomain hp with h1 | h2
      · exact Grid.notMem_cIco_of_mem_cIoo hcol
          ((D.first.toGridRectangle.mem_coveredColumns _).mp
            ((D.first.toGridRectangle.mem_coveredSquares _).mp h1).1)
      · exact Grid.right_notMem_cIco a c (by
          simpa only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
            GridRectangleBetween.toGridRectangle_right, ← hcommon] using
            ((D.second.toGridRectangle.mem_coveredSquares _).mp h2).1)
  · have hcases := first_sides_eq_of_mem_triple_of_ne_swaps (p := b) (q := c) (r := a)
      (fun u hu => by
        have := hEsub hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
        tauto)
      (by rw [GridState.swapColumns_comm]; exact hmidD')
      (by rw [GridState.swapColumns_comm]; exact hRmid ▸ hmidR)
    rcases hcases with ⟨hl, -⟩ | ⟨hl, -⟩
    · have hp : (b, x b) ∈ E.first.toGridRectangle.coveredSquares := by
        simpa only [hl, GridRectangleBetween.bottom_def] using
          left_bottom_mem_coveredSquares E.first
      rcases mem_coveredSquares_or_of_add_eq hdomain hp with h1 | h2
      · exact Grid.right_notMem_cIco a b
          ((D.first.toGridRectangle.mem_coveredColumns _).mp
            ((D.first.toGridRectangle.mem_coveredSquares _).mp h1).1)
      · exact Grid.notMem_cIco_of_mem_cIoo hcol (by
          simpa only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
            GridRectangleBetween.toGridRectangle_right, ← hcommon] using
            ((D.second.toGridRectangle.mem_coveredSquares _).mp h2).1)
    · have hp : (c, x c) ∈ E.first.toGridRectangle.coveredSquares := by
        simpa only [hl, GridRectangleBetween.bottom_def] using
          left_bottom_mem_coveredSquares E.first
      rcases mem_coveredSquares_or_of_add_eq hdomain hp with h1 | h2
      · exact Grid.notMem_cIco_of_mem_cIoo hrow
          ((D.first.toGridRectangle.mem_coveredRows _).mp
            ((D.first.toGridRectangle.mem_coveredSquares _).mp h1).2)
      · exact Grid.right_notMem_cIco a c (by
          simpa only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
            GridRectangleBetween.toGridRectangle_right, ← hcommon] using
            ((D.second.toGridRectangle.mem_coveredSquares _).mp h2).1)

private theorem not_middle_third_of_right_eq_right {D E : GridRectangleDecomposition x z}
    (hcommon : D.first.right = D.second.right) (hother : D.first.left ≠ D.second.left)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val)
    (hmidD : E.middle ≠ D.middle)
    (hmidR : E.middle ≠
      (D.recut (D.hasOneCommonSide_of_right_eq_right hcommon hother) hD₁ hD₂).middle) :
    False := by
  set a := D.first.left; set b := D.first.right; set c := D.second.left
  have hcb : c ≠ b := hcommon ▸ D.second.left_ne_right
  have hD₂bot : D.second.bottom = x c := by
    rw [GridRectangleBetween.bottom_def, D.first.map_of_ne c hother.symm hcb]
  have hD₂top : D.second.top = x a := by
    rw [GridRectangleBetween.top_def, ← hcommon, D.first.map_right]
  have hrow : x a ∈ Grid.cIoo (x c) (x b) := by
    have hord := (D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon hother hD₁ hD₂).2
    rw [hD₂bot] at hord
    exact hord
  have hone := D.hasOneCommonSide_of_right_eq_right hcommon hother
  have hEsub : E.first.sideColumns ⊆ {a, b, c} := by
    intro u hu
    have hmem : u ∈ D.first.sideColumns ∪ D.second.sideColumns := by
      rw [D.sideColumns_union_eq_of_hasOneCommonSide E hone]
      exact Finset.mem_union_left _ hu
    simp only [Finset.mem_union, GridRectangleBetween.mem_sideColumns, ← hcommon,
      Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    tauto
  have hmidD' : E.middle ≠ x.swapColumns a b := D.first.target_eq_swapColumns ▸ hmidD
  rcases (D.isRecutOfRightEqRight_recut hcommon hone hD₁ hD₂).recut_branch with
    ⟨hcol, hRmid, -, -⟩ | ⟨hcol, hRmid, -, -⟩
  · have hcases := first_sides_eq_of_mem_triple_of_ne_swaps (p := c) (q := b) (r := a)
      (fun u hu => by
        have := hEsub hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
        tauto)
      (hRmid ▸ hmidR) (by rw [GridState.swapColumns_comm]; exact hmidD')
    rcases hcases with ⟨hl, hr⟩ | ⟨hl, -⟩
    · exact (E.first.isEmpty_iff_forall_notMem_cIoo).mp hE₁ a (hl ▸ hr ▸ hcol)
        (by simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hl, hr]
          using hrow)
    · have hp : (b, x b) ∈ E.first.toGridRectangle.coveredSquares := by
        simpa only [hl, GridRectangleBetween.bottom_def] using
          left_bottom_mem_coveredSquares E.first
      rcases mem_coveredSquares_or_of_add_eq hdomain hp with h1 | h2
      · exact Grid.right_notMem_cIco a b
          ((D.first.toGridRectangle.mem_coveredColumns _).mp
            ((D.first.toGridRectangle.mem_coveredSquares _).mp h1).1)
      · exact Grid.right_notMem_cIco c b (by
          simpa only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
            GridRectangleBetween.toGridRectangle_right, ← hcommon] using
            ((D.second.toGridRectangle.mem_coveredSquares _).mp h2).1)
  · have hcases := first_sides_eq_of_mem_triple_of_ne_swaps (p := a) (q := c) (r := b)
      (fun u hu => by
        have := hEsub hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
        tauto)
      hmidD' (hRmid ▸ hmidR)
    rcases hcases with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · have hp : (a, x b) ∈ E.first.toGridRectangle.coveredSquares := by
        refine (E.first.toGridRectangle.mem_coveredSquares _).mpr ⟨?_, ?_⟩
        · simpa only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
            GridRectangleBetween.toGridRectangle_right, hl, hr] using Grid.left_mem_cIco hother
        · simpa only [GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_bottom,
            GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.bottom_def,
            GridRectangleBetween.top_def, hl, hr] using
            Grid.cIoo_subset_cIco (x a) (x c) (Grid.mem_cIoo_cyclic_left hrow)
      rcases mem_coveredSquares_or_of_add_eq hdomain hp with h1 | h2
      · exact Grid.right_notMem_cIco (x a) (x b)
          ((D.first.toGridRectangle.mem_coveredRows _).mp
            ((D.first.toGridRectangle.mem_coveredSquares _).mp h1).2)
      · exact Grid.notMem_cIco_of_mem_cIoo hrow (by
          simpa only [GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_bottom,
            GridRectangleBetween.toGridRectangle_top, hD₂bot, hD₂top] using
            ((D.second.toGridRectangle.mem_coveredSquares _).mp h2).2)
    · have hp : (b, x c) ∈ E.first.toGridRectangle.coveredSquares := by
        refine (E.first.toGridRectangle.mem_coveredSquares _).mpr ⟨?_, ?_⟩
        · simpa only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
            GridRectangleBetween.toGridRectangle_right, hl, hr] using
            Grid.cIoo_subset_cIco c a (Grid.mem_cIoo_cyclic_left hcol)
        · simpa only [GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_bottom,
            GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.bottom_def,
            GridRectangleBetween.top_def, hl, hr] using
            Grid.left_mem_cIco (x.toPerm.injective.ne hother.symm)
      rcases mem_coveredSquares_or_of_add_eq hdomain hp with h1 | h2
      · exact Grid.right_notMem_cIco a b
          ((D.first.toGridRectangle.mem_coveredColumns _).mp
            ((D.first.toGridRectangle.mem_coveredSquares _).mp h1).1)
      · exact Grid.right_notMem_cIco c b (by
          simpa only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
            GridRectangleBetween.toGridRectangle_right, ← hcommon] using
            ((D.second.toGridRectangle.mem_coveredSquares _).mp h2).1)

private theorem eq_or_isRecut_of_hasSameSideOverlap {D E : GridRectangleDecomposition x z}
    (hsame : D.HasSameSideOverlap)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    E = D ∨ D.IsRecut E := by
  obtain ⟨hone, hside⟩ := D.hasSameSideOverlap_iff.mp hsame
  have hzx := D.target_ne_source_of_hasOneCommonSide hone
  set R := D.recut hone hD₁ hD₂
  have hDR : D.IsRecut R := D.isRecut_recut hone hD₁ hD₂
  by_cases hmidD : E.middle = D.middle
  · exact Or.inl (eq_of_middle_eq_of_coveredSquares_add_eq hzx hmidD hdomain)
  by_cases hmidR : E.middle = R.middle
  · right
    have hER : E = R := eq_of_middle_eq_of_coveredSquares_add_eq hzx hmidR
      (hdomain.trans hDR.isRepartition.val_add_val_eq.symm)
    exact hER ▸ hDR
  · exfalso
    rcases hside with hcommon | hcommon
    · have hother : D.first.right ≠ D.second.right := fun hr =>
        D.sideColumns_ne_of_hasOneCommonSide hone
          (by rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon, hr])
      exact not_middle_third_of_left_eq_left hcommon hother hD₁ hD₂ hE₁ hdomain hmidD hmidR
    · have hother : D.first.left ≠ D.second.left := fun hl =>
        D.sideColumns_ne_of_hasOneCommonSide hone
          (by rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon, hl])
      exact not_middle_third_of_right_eq_right hcommon hother hD₁ hD₂ hE₁ hdomain hmidD hmidR

/-- If `D` has a mixed-side overlap and `E` is its recut, then `D` is a same-side recut of `E`. -/
theorem IsRecut.symm_sameSide_of_hasMixedSideOverlap {D E : GridRectangleDecomposition x z}
    (h : D.IsRecut E) (hmixed : D.HasMixedSideOverlap)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) :
    E.IsRecutOfLeftEqLeft D ∨ E.IsRecutOfRightEqRight D := by
  obtain ⟨-, hside⟩ := D.hasMixedSideOverlap_iff.mp hmixed
  have hED : E.IsRecut D := h.symm hD₁ hD₂
  rcases hED.orientation with ho | ho | ho | ho
  · exact Or.inl ho
  · exact Or.inr ho
  · exfalso
    obtain ⟨h1, h2⟩ := ho.recut_sides
    rcases hside with hc | hc
    · have htop := D.second_top_eq_first_top_of_left_eq_right hc
      rcases ho.recut_branch with ⟨-, -, h3, -⟩ | ⟨-, -, -, h3⟩
      · exact D.second.bottom_ne_top (h2.trans (h3.symm.trans htop.symm))
      · exact D.first.bottom_ne_top (h1.trans (h3.symm.trans htop))
    · have hbot := D.second_bottom_eq_first_bottom_of_right_eq_left hc
      rcases ho.recut_branch with ⟨-, -, h3, -⟩ | ⟨-, -, -, h3⟩
      · exact D.first.bottom_ne_top (hbot.symm.trans (h2.trans h3.symm))
      · exact D.second.bottom_ne_top (hbot.trans (h1.trans h3.symm))
  · exfalso
    obtain ⟨h1, h2⟩ := ho.recut_sides
    rcases hside with hc | hc
    · have htop := D.second_top_eq_first_top_of_left_eq_right hc
      rcases ho.recut_branch with ⟨-, -, h3, -⟩ | ⟨-, -, -, h3⟩
      · exact D.first.bottom_ne_top (h3.trans (h2.symm.trans htop))
      · exact D.second.bottom_ne_top (h3.trans (h1.symm.trans htop.symm))
    · have hbot := D.second_bottom_eq_first_bottom_of_right_eq_left hc
      rcases ho.recut_branch with ⟨-, -, h3, -⟩ | ⟨-, -, -, h3⟩
      · exact D.second.bottom_ne_top (hbot.trans (h3.trans h2.symm))
      · exact D.first.bottom_ne_top (hbot.symm.trans (h3.trans h1.symm))

private theorem hasSameSideOverlap_recut_of_hasMixedSideOverlap
    {D : GridRectangleDecomposition x z} (hmixed : D.HasMixedSideOverlap)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) :
    (D.recut (D.hasMixedSideOverlap_iff.mp hmixed).1 hD₁ hD₂).HasSameSideOverlap := by
  obtain ⟨hone, -⟩ := D.hasMixedSideOverlap_iff.mp hmixed
  have hRone := D.hasOneCommonSide_recut hone hD₁ hD₂
  have hsymm :=
    (D.isRecut_recut hone hD₁ hD₂).symm_sameSide_of_hasMixedSideOverlap hmixed hD₁ hD₂
  rcases hsymm with h | h
  · exact (D.recut hone hD₁ hD₂).hasSameSideOverlap_iff.mpr ⟨hRone, Or.inl h.side_eq⟩
  · exact (D.recut hone hD₁ hD₂).hasSameSideOverlap_iff.mpr ⟨hRone, Or.inr h.side_eq⟩

/-- If `D` shares exactly one side column and the relevant rectangles are empty with the same
covered-square multiset, then `E = D` or `D.IsRecut E`. -/
theorem eq_or_isRecut_of_hasOneCommonSide_of_coveredSquares_add_eq
    {D E : GridRectangleDecomposition x z} (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    E = D ∨ D.IsRecut E := by
  rcases D.hasSameSideOverlap_or_hasMixedSideOverlap hone with hsame | hmixed
  · exact eq_or_isRecut_of_hasSameSideOverlap hsame hD₁ hD₂ hE₁ hdomain
  · set R := D.recut hone hD₁ hD₂
    have hDR : D.IsRecut R := D.isRecut_recut hone hD₁ hD₂
    have hRsame : R.HasSameSideOverlap :=
      hasSameSideOverlap_recut_of_hasMixedSideOverlap hmixed hD₁ hD₂
    rcases eq_or_isRecut_of_hasSameSideOverlap hRsame hDR.isEmpty_first hDR.isEmpty_second hE₁
        (hdomain.trans hDR.isRepartition.val_add_val_eq.symm) with rfl | hRE
    · exact Or.inr hDR
    · left
      exact (R.existsUnique_isRecut (D.hasOneCommonSide_recut hone hD₁ hD₂)
        hDR.isEmpty_first hDR.isEmpty_second).unique hRE (hDR.symm hD₁ hD₂)

/-! ### Full classification -/

/-- Any two-step decomposition by empty rectangles covering the same multiset of squares as an
empty decomposition `D` is either `D` itself, `D.commute h` when `D` has disjoint sides, or the
recut of `D` when `D` shares one side column. -/
theorem eq_commute_or_isRecut_of_coveredSquares_add_eq
    {D E : GridRectangleDecomposition x z}
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    E = D ∨ (∃ h : D.HasDisjointSides, E = D.commute h) ∨ D.IsRecut E := by
  rcases D.hasDisjointSides_or_hasOneCommonSide_or_eq with hdisj | hone | rfl
  · rcases eq_or_eq_commute_of_hasDisjointSides_of_coveredSquares_add_eq hdisj hdomain with
      rfl | hE
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨hdisj, hE⟩)
  · have hres :=
      eq_or_isRecut_of_hasOneCommonSide_of_coveredSquares_add_eq hone hD₁ hD₂ hE₁ hdomain
    rcases hres with rfl | hrecut
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hrecut)
  · exact Or.inl (eq_of_coveredSquares_add_eq_self hdomain)

end GridRectangleDecomposition

end TauCeti
