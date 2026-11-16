/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Geometry
import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Empty

/-!
# Classification of two-step empty rectangle decompositions with the same domain

The square rule for a grid sign assignment constrains any two distinct two-step decompositions
`D, E : GridRectangleDecomposition x z` made of empty rectangles whose covered-square multisets
coincide:

`E.first.toGridRectangle.coveredSquares.val + E.second.toGridRectangle.coveredSquares.val =`
`  D.first.toGridRectangle.coveredSquares.val + D.second.toGridRectangle.coveredSquares.val`.

This file proves the uniqueness half of the rectangle-juxtaposition classification: no third
empty decomposition shares the same domain. Specifically:

* on the diagonal (`z = x`), an empty returning pair covers a thin vertical or thin horizontal
  annulus, which uniquely determines the decomposition (`E = D`);
* for two disjoint side pairs, the only other decomposition with the same domain is `D.commute`;
* for two side pairs sharing one column, the only other empty decomposition with the same domain
  is `D.recut`.

## Main results

* `TauCeti.GridRectangleDecomposition.eq_of_middle_eq_of_val_add_val_eq`: two nondiagonal
  decompositions through the same intermediate state covering the same multiset of squares agree.
* `TauCeti.GridRectangleDecomposition.eq_of_val_add_val_eq_self`: on the diagonal, two empty
  decompositions covering the same multiset of squares agree.
* `TauCeti.GridRectangleDecomposition.eq_or_eq_commute_of_val_add_val_eq`: when `D` has disjoint
  sides, any decomposition covering the same multiset of squares is `D` or `D.commute`.
* `TauCeti.GridRectangleDecomposition.eq_or_eq_recut_of_val_add_val_eq`: when `D` has one common
  side, any empty decomposition covering the same multiset of squares is `D` or `D.recut`.
* `TauCeti.GridRectangleDecomposition.eq_commute_or_eq_recut_of_ne_of_val_add_val_eq`: any
  distinct empty decomposition covering the same multiset of squares is `D.commute` or `D.recut`.

## References

* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Section 4.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208, 2015, Section 4.6 and Section 15.2.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-! ### Helper lemmas on side columns, covered squares, and multiset counts -/

private theorem count_finset_val {α : Type*} [DecidableEq α] (s : Finset α) (a : α) :
    Multiset.count a s.val = if a ∈ s then 1 else 0 := by
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem s.nodup (Finset.mem_val.mpr h)
  · exact Multiset.count_eq_zero_of_notMem (by simpa using h)

private theorem sideColumns_eq_of_endpoints {u v : GridState n}
    (R S : GridRectangleBetween u v) : R.sideColumns = S.sideColumns := by
  have hpairs : s(R.left, R.right) = s(S.left, S.right) :=
    GridState.sym2_mk_eq_of_swapColumns_eq R.left_ne_right
      (R.target_eq_swapColumns.symm.trans S.target_eq_swapColumns)
  simpa only [GridRectangleBetween.sideColumns, Sym2.toFinset_mk_eq] using
    congrArg Sym2.toFinset hpairs

private theorem sides_eq_swap_of_ne_left {u v : GridState n}
    {R S : GridRectangleBetween u v} (hne : S.left ≠ R.left) :
    S.left = R.right ∧ S.right = R.left := by
  have hsides : S.sideColumns = R.sideColumns := sideColumns_eq_of_endpoints S R
  have hleft_mem : S.left ∈ R.sideColumns := hsides ▸ by simp
  have hright_mem : S.right ∈ R.sideColumns := hsides ▸ by simp
  rw [R.mem_sideColumns] at hleft_mem hright_mem
  have hleft : S.left = R.right := hleft_mem.resolve_left hne
  exact ⟨hleft, hright_mem.resolve_right fun h => S.left_ne_right (hleft.trans h.symm)⟩

private theorem mem_coveredSquares_finRotate_symm_iff {u v : GridState n}
    (R : GridRectangleBetween u v) {c : Fin n} (hc : c ∉ R.sideColumns) (r : Fin n) :
    (c, r) ∈ R.toGridRectangle.coveredSquares ↔
      ((finRotate n).symm c, r) ∈ R.toGridRectangle.coveredSquares := by
  rw [R.mem_sideColumns, not_or] at hc
  have hrot : finRotate n ((finRotate n).symm c) = c := (finRotate n).apply_symm_apply c
  have hcol := Grid.mem_cIco_finRotate_iff_of_ne (a := R.left) (b := R.right)
    (c := (finRotate n).symm c) (by rw [hrot]; exact Ne.symm hc.1)
    (by rw [hrot]; exact Ne.symm hc.2)
  rw [hrot] at hcol
  simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares]
  exact and_congr_left' hcol

private theorem false_of_mem_first_notMem_of_val_add_val_eq
    {D E : GridRectangleDecomposition x z}
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val)
    {p : Fin n × Fin n}
    (hE : p ∈ E.first.toGridRectangle.coveredSquares)
    (hD₁ : p ∉ D.first.toGridRectangle.coveredSquares)
    (hD₂ : p ∉ D.second.toGridRectangle.coveredSquares) : False := by
  have hcount := congrArg (Multiset.count p) hsum
  simp only [Multiset.count_add, count_finset_val, hE, hD₁, hD₂, ↓reduceIte] at hcount
  omega

private theorem finRotate_symm_notMem_cIco_left {a b : Fin n} (hab : a ≠ b) :
    (finRotate n).symm a ∉ Grid.cIco a b := by
  have hrot : finRotate n ((finRotate n).symm a) = a := (finRotate n).apply_symm_apply a
  have hmem : (finRotate n).symm a ∈ Grid.cIco b a := by
    simpa only [hrot] using Grid.self_mem_cIco_finRotate (a := (finRotate n).symm a) (c := b)
      (by simpa only [hrot] using hab.symm)
  exact Finset.disjoint_right.mp (Grid.disjoint_cIco_swap a b) hmem

private theorem finRotate_symm_mem_cIco_right {a b : Fin n} (hab : a ≠ b) :
    (finRotate n).symm b ∈ Grid.cIco a b := by
  have hrot : finRotate n ((finRotate n).symm b) = b := (finRotate n).apply_symm_apply b
  simpa only [hrot] using Grid.self_mem_cIco_finRotate (a := (finRotate n).symm b) (c := a)
    (by simpa only [hrot] using hab)

private theorem first_sides_of_mem_triple_of_ne {E : GridRectangleDecomposition x z}
    {p q r : Fin n}
    (hfl : E.first.left ∈ ({p, q, r} : Finset (Fin n)))
    (hfr : E.first.right ∈ ({p, q, r} : Finset (Fin n)))
    (h₁ : E.middle ≠ x.swapColumns p r)
    (h₂ : E.middle ≠ x.swapColumns q r) :
    (E.first.left = p ∧ E.first.right = q) ∨ (E.first.left = q ∧ E.first.right = p) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfl hfr
  have hmid := E.first.target_eq_swapColumns
  rcases hfl with hl | hl | hl <;> rcases hfr with hr | hr | hr
  · exact (E.first.left_ne_right (hl.trans hr.symm)).elim
  · exact Or.inl ⟨hl, hr⟩
  · exact (h₁ (by rw [hmid, hl, hr])).elim
  · exact Or.inr ⟨hl, hr⟩
  · exact (E.first.left_ne_right (hl.trans hr.symm)).elim
  · exact (h₂ (by rw [hmid, hl, hr])).elim
  · exact (h₁ (by rw [hmid, hl, hr, GridState.swapColumns_comm])).elim
  · exact (h₂ (by rw [hmid, hl, hr, GridState.swapColumns_comm])).elim
  · exact (E.first.left_ne_right (hl.trans hr.symm)).elim

/-! ### Same intermediate state -/

private theorem eq_of_coveredSquares_val_eq {u v : GridState n}
    {R S : GridRectangleBetween u v}
    (hsq : S.toGridRectangle.coveredSquares.val = R.toGridRectangle.coveredSquares.val) :
    S = R := by
  refine GridRectangleBetween.left_injective ?_
  by_contra hne
  obtain ⟨_, hSr⟩ := sides_eq_swap_of_ne_left hne
  have hcorner : (R.left, R.bottom) ∈ S.toGridRectangle.coveredSquares :=
    Finset.mem_def.mpr (hsq ▸ Finset.mem_def.mp R.left_bottom_mem_coveredSquares)
  have hcol := (S.mem_toGridRectangle_coveredSquares.mp hcorner).1
  rw [hSr] at hcol
  exact Grid.right_notMem_cIco _ _ hcol

private theorem first_left_eq_of_same_middle {y : GridState n}
    {D₁ E₁ : GridRectangleBetween x y} {D₂ E₂ : GridRectangleBetween y z}
    (hzx : z ≠ x)
    (hsum : E₁.toGridRectangle.coveredSquares.val + E₂.toGridRectangle.coveredSquares.val =
      D₁.toGridRectangle.coveredSquares.val + D₂.toGridRectangle.coveredSquares.val) :
    E₁.left = D₁.left := by
  have hne_sides : D₁.sideColumns ≠ D₂.sideColumns := fun h =>
    hzx ((target_eq_source_iff_sideColumns_eq ⟨y, D₁, D₂⟩).mpr h)
  have hnsub : ¬D₁.sideColumns ⊆ D₂.sideColumns := fun hsub =>
    hne_sides (Finset.eq_of_subset_of_card_le hsub
      (by rw [D₁.card_sideColumns, D₂.card_sideColumns]))
  obtain ⟨v, hv₁, hv₂⟩ := Finset.not_subset.mp hnsub
  have hvE₂ : v ∉ E₂.sideColumns := (sideColumns_eq_of_endpoints E₂ D₂) ▸ hv₂
  by_contra hne
  obtain ⟨hE₁_left, hE₁_right⟩ := sides_eq_swap_of_ne_left hne
  set r := D₁.bottom
  have hE₁_not : ∀ c : Fin n, (c, r) ∉ E₁.toGridRectangle.coveredSquares := fun c hc => by
    have hrow := (E₁.mem_toGridRectangle_coveredSquares.mp hc).2
    rw [hE₁_left, hE₁_right] at hrow
    exact Grid.right_notMem_cIco _ _ hrow
  have hcount_v := congrArg (Multiset.count (v, r)) hsum
  have hcount_v' := congrArg (Multiset.count ((finRotate n).symm v, r)) hsum
  simp only [Multiset.count_add, count_finset_val, hE₁_not, ↓reduceIte,
    zero_add] at hcount_v hcount_v'
  have hD₂_eq : (if (v, r) ∈ D₂.toGridRectangle.coveredSquares then 1 else 0) =
      if ((finRotate n).symm v, r) ∈ D₂.toGridRectangle.coveredSquares then 1 else 0 := by
    simp [mem_coveredSquares_finRotate_symm_iff D₂ hv₂ r]
  have hE₂_eq : (if (v, r) ∈ E₂.toGridRectangle.coveredSquares then 1 else 0) =
      if ((finRotate n).symm v, r) ∈ E₂.toGridRectangle.coveredSquares then 1 else 0 := by
    simp [mem_coveredSquares_finRotate_symm_iff E₂ hvE₂ r]
  have hD₁_iff : (v, r) ∈ D₁.toGridRectangle.coveredSquares ↔
      ((finRotate n).symm v, r) ∈ D₁.toGridRectangle.coveredSquares := by
    by_cases hA : (v, r) ∈ D₁.toGridRectangle.coveredSquares <;>
      by_cases hB : ((finRotate n).symm v, r) ∈ D₁.toGridRectangle.coveredSquares <;>
      simp only [hA, hB, ↓reduceIte, hD₂_eq, hE₂_eq] at hcount_v hcount_v' ⊢ <;> omega
  simp only [D₁.mem_toGridRectangle_coveredSquares, r, GridRectangleBetween.bottom_def,
    Grid.left_mem_cIco (x.toPerm.injective.ne D₁.left_ne_right), and_true] at hD₁_iff
  rw [D₁.mem_sideColumns] at hv₁
  rcases hv₁ with rfl | rfl
  · exact finRotate_symm_notMem_cIco_left D₁.left_ne_right
      (hD₁_iff.mp (Grid.left_mem_cIco D₁.left_ne_right))
  · exact Grid.right_notMem_cIco D₁.left D₁.right
      (hD₁_iff.mpr (finRotate_symm_mem_cIco_right D₁.left_ne_right))

/-- Two nondiagonal two-step decompositions through the same intermediate state that cover the
same multiset of squares are equal. -/
theorem eq_of_middle_eq_of_val_add_val_eq {D E : GridRectangleDecomposition x z}
    (hzx : z ≠ x) (hmid : E.middle = D.middle)
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) : E = D := by
  cases D with
  | mk y D₁ D₂ =>
    cases E with
    | mk y' E₁ E₂ =>
      dsimp only at hmid hsum
      subst y'
      have hE₁ : E₁ = D₁ :=
        GridRectangleBetween.left_injective (first_left_eq_of_same_middle hzx hsum)
      subst hE₁
      have hE₂ : E₂ = D₂ := eq_of_coveredSquares_val_eq (add_left_cancel hsum)
      subst hE₂
      rfl

/-! ### Diagonal case (`z = x`) -/

private theorem product_singleton_univ_ne_univ_singleton {c r : Fin n} (hn : 1 < n) :
    ({c} : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)) ≠
      (Finset.univ : Finset (Fin n)) ×ˢ ({r} : Finset (Fin n)) := by
  intro heq
  have hmem : (finRotate n c, r) ∈
      ({c} : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)) := by
    rw [heq]; simp
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true] at hmem
  exact Grid.finRotate_ne_self hn c hmem

private theorem coveredColumns_eq_singleton_of_right_eq_finRotate {u v : GridState n}
    (R : GridRectangleBetween u v) (hrot : R.right = finRotate n R.left) :
    R.toGridRectangle.coveredColumns = {R.left} := by
  simp only [GridRectangle.coveredColumns_def, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right]
  exact Grid.cIco_eq_singleton_iff.mpr ⟨rfl, hrot, R.left_ne_right⟩

private theorem coveredRows_eq_singleton_of_top_eq_finRotate {u v : GridState n}
    (R : GridRectangleBetween u v) (hrot : R.top = finRotate n R.bottom) :
    R.toGridRectangle.coveredRows = {R.bottom} := by
  simp only [GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top]
  exact Grid.cIco_eq_singleton_iff.mpr ⟨rfl, hrot, R.bottom_ne_top⟩

/-- On the diagonal (`z = x`), two empty two-step decompositions covering the same multiset of
squares are equal: an empty returning pair covers either a thin vertical or a thin horizontal
annulus, and that annulus uniquely determines both rectangles. -/
theorem eq_of_val_add_val_eq_self {D E : GridRectangleDecomposition x x}
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hE₁ : E.first.IsEmpty) (hE₂ : E.second.IsEmpty)
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) : E = D := by
  have hunion : E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares =
      D.first.toGridRectangle.coveredSquares ∪ D.second.toGridRectangle.coveredSquares := by
    apply Finset.val_injective
    rw [← Finset.disjUnion_eq_union _ _ (E.first.disjoint_coveredSquares E.second),
      ← Finset.disjUnion_eq_union _ _ (D.first.disjoint_coveredSquares D.second),
      Finset.disjUnion_val, Finset.disjUnion_val]
    exact hsum
  have hn : 1 < n := by
    simpa only [Fintype.card_fin] using
      Fintype.one_lt_card_iff.mpr ⟨D.first.left, D.first.right, D.first.left_ne_right⟩
  rcases (D.first.isEmpty_and_isEmpty_iff D.second).mp ⟨hD₁, hD₂⟩ with
      ⟨hDleft, hDrot⟩ | ⟨hDleft, hDrot⟩ <;>
    rcases (E.first.isEmpty_and_isEmpty_iff E.second).mp ⟨hE₁, hE₂⟩ with
      ⟨hEleft, hErot⟩ | ⟨hEleft, hErot⟩
  · rw [E.first.coveredSquares_union_coveredSquares_of_left_eq_left E.second hEleft,
      D.first.coveredSquares_union_coveredSquares_of_left_eq_left D.second hDleft,
      coveredColumns_eq_singleton_of_right_eq_finRotate E.first hErot,
      coveredColumns_eq_singleton_of_right_eq_finRotate D.first hDrot] at hunion
    have hfl : E.first.left = D.first.left := by
      have hmem : (E.first.left, D.first.bottom) ∈
          ({D.first.left} : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)) := by
        rw [← hunion]; simp
      simpa only [Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true] using hmem
    exact ext hfl (by rw [hErot, hDrot, hfl]) (by rw [hEleft, hDleft, hfl])
  · rw [E.first.coveredSquares_union_coveredSquares_of_left_eq_right E.second hEleft,
      D.first.coveredSquares_union_coveredSquares_of_left_eq_left D.second hDleft,
      coveredRows_eq_singleton_of_top_eq_finRotate E.first hErot,
      coveredColumns_eq_singleton_of_right_eq_finRotate D.first hDrot] at hunion
    exact (product_singleton_univ_ne_univ_singleton hn hunion.symm).elim
  · rw [E.first.coveredSquares_union_coveredSquares_of_left_eq_left E.second hEleft,
      D.first.coveredSquares_union_coveredSquares_of_left_eq_right D.second hDleft,
      coveredColumns_eq_singleton_of_right_eq_finRotate E.first hErot,
      coveredRows_eq_singleton_of_top_eq_finRotate D.first hDrot] at hunion
    exact (product_singleton_univ_ne_univ_singleton hn hunion).elim
  · rw [E.first.coveredSquares_union_coveredSquares_of_left_eq_right E.second hEleft,
      D.first.coveredSquares_union_coveredSquares_of_left_eq_right D.second hDleft,
      coveredRows_eq_singleton_of_top_eq_finRotate E.first hErot,
      coveredRows_eq_singleton_of_top_eq_finRotate D.first hDrot] at hunion
    have hbot : E.first.bottom = D.first.bottom := by
      have hmem : (D.first.left, E.first.bottom) ∈
          (Finset.univ : Finset (Fin n)) ×ˢ ({D.first.bottom} : Finset (Fin n)) := by
        rw [← hunion]; simp
      simpa only [Finset.mem_product, Finset.mem_univ, Finset.mem_singleton, true_and] using hmem
    have hfl : E.first.left = D.first.left :=
      x.toPerm.injective (by simpa only [GridRectangleBetween.bottom_def] using hbot)
    have hfr : E.first.right = D.first.right :=
      x.toPerm.injective (by
        have htop : E.first.top = D.first.top := by rw [hErot, hbot, hDrot]
        simpa only [GridRectangleBetween.top_def] using htop)
    exact ext hfl hfr (by rw [hEleft, hDleft, hfr])

/-! ### Disjoint sides -/

private theorem hasDisjointSides_of_endpoints {D E : GridRectangleDecomposition x z}
    (h : D.HasDisjointSides) : E.HasDisjointSides := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp h
  have hz_eq : z = (x.swapColumns D.first.left D.first.right).swapColumns
      D.second.left D.second.right :=
    D.second.target_eq_swapColumns.trans
      (congrArg (·.swapColumns D.second.left D.second.right) D.first.target_eq_swapColumns)
  have hdisj : Disjoint ({D.first.left, D.first.right} : Finset (Fin n))
      {D.second.left, D.second.right} := by
    simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨⟨hll, hlr⟩, hrl, hrr⟩
  have aux : ∀ (z' : GridState n) (E' : GridRectangleDecomposition x z'),
      z' = (x.swapColumns D.first.left D.first.right).swapColumns D.second.left D.second.right →
      E'.HasDisjointSides := by
    rintro z' E' rfl
    exact hasDisjointSides_of_disjoint x D.first.left_ne_right D.second.left_ne_right hdisj E'
  exact aux z E hz_eq

private theorem middle_eq_or_eq_commute_middle {D E : GridRectangleDecomposition x z}
    (h : D.HasDisjointSides) : E.middle = D.middle ∨ E.middle = (D.commute h).middle := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp h
  obtain ⟨hEll, hElr, -, -⟩ := E.hasDisjointSides_iff.mp (hasDisjointSides_of_endpoints h)
  have hEz_left : z E.first.left = x E.first.right := by
    rw [E.second.map_of_ne E.first.left hEll hElr, E.first.map_left]
  have hmem : E.first.left ∈ D.first.sideColumns ∨ E.first.left ∈ D.second.sideColumns := by
    by_contra hnot
    rw [not_or] at hnot
    have hfix := D.target_apply_of_notMem_sideColumns hnot.1 hnot.2
    exact E.first.left_ne_right (x.toPerm.injective (hfix.symm.trans hEz_left))
  rcases hmem with hmem | hmem
  · left
    rw [D.first.mem_sideColumns] at hmem
    rcases hmem with hfl | hfl
    · have hfr : E.first.right = D.first.right := x.toPerm.injective <| by
        rw [← hEz_left, hfl, D.second.map_of_ne D.first.left hll hlr, D.first.map_left]
      rw [E.first.target_eq_swapColumns, D.first.target_eq_swapColumns, hfl, hfr]
    · have hfr : E.first.right = D.first.left := x.toPerm.injective <| by
        rw [← hEz_left, hfl, D.second.map_of_ne D.first.right hrl hrr, D.first.map_right]
      rw [E.first.target_eq_swapColumns, D.first.target_eq_swapColumns, hfl, hfr,
        GridState.swapColumns_comm]
  · right
    rw [D.second.mem_sideColumns] at hmem
    rcases hmem with hfl | hfl
    · have hfr : E.first.right = D.second.right := x.toPerm.injective <| by
        rw [← hEz_left, hfl, D.second.map_left,
          D.first.map_of_ne D.second.right hlr.symm hrr.symm]
      rw [E.first.target_eq_swapColumns, D.commute_middle h, hfl, hfr]
    · have hfr : E.first.right = D.second.left := x.toPerm.injective <| by
        rw [← hEz_left, hfl, D.second.map_right,
          D.first.map_of_ne D.second.left hll.symm hrl.symm]
      rw [E.first.target_eq_swapColumns, D.commute_middle h, hfl, hfr, GridState.swapColumns_comm]

/-- When `D` has disjoint side pairs, any two-step decomposition covering the same multiset of
squares is either `D` or `D.commute h`. -/
theorem eq_or_eq_commute_of_val_add_val_eq {D E : GridRectangleDecomposition x z}
    (h : D.HasDisjointSides)
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    E = D ∨ E = D.commute h := by
  have hzx := D.target_ne_source_of_hasDisjointSides h
  rcases middle_eq_or_eq_commute_middle h (E := E) with hmid | hmid
  · exact Or.inl (eq_of_middle_eq_of_val_add_val_eq hzx hmid hsum)
  · refine Or.inr (eq_of_middle_eq_of_val_add_val_eq hzx hmid ?_)
    rw [D.commute_first_toGridRectangle h, D.commute_second_toGridRectangle h,
      add_comm D.second.toGridRectangle.coveredSquares.val]
    exact hsum

/-! ### One common side -/

private theorem hasSameSideOverlap_recut_of_hasMixedSideOverlap
    (D : GridRectangleDecomposition x z) (hmix : D.HasMixedSideOverlap)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) :
    (D.recut (D.hasMixedSideOverlap_iff.mp hmix).1 hD₁ hD₂).HasSameSideOverlap := by
  obtain ⟨hone, hside⟩ := D.hasMixedSideOverlap_iff.mp hmix
  refine (D.recut hone hD₁ hD₂).hasSameSideOverlap_iff.mpr
    ⟨D.hasOneCommonSide_recut hone hD₁ hD₂, ?_⟩
  rcases hside with hcommon | hcommon
  · rcases D.recut_geometry_of_left_eq_right hcommon hone hD₁ hD₂ with
      ⟨-, hfl, -, hsl, -⟩ | ⟨-, -, hfr, -, hsr, -⟩
    · exact Or.inl (hfl.trans hsl.symm)
    · exact Or.inr (hfr.trans hsr.symm)
  · rcases D.recut_geometry_of_right_eq_left hcommon hone hD₁ hD₂ with
      ⟨-, -, hfr, -, hsr, -⟩ | ⟨-, hfl, -, hsl, -⟩
    · exact Or.inr (hfr.trans hsr.symm)
    · exact Or.inl (hfl.trans hsl.symm)

private theorem first_sides_mem_of_union_eq {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) {s : Finset (Fin n)}
    (hD_union : D.first.sideColumns ∪ D.second.sideColumns = s) :
    E.first.left ∈ s ∧ E.first.right ∈ s := by
  have hunion := (sideColumns_union_eq_of_hasOneCommonSide D E hone).symm.trans hD_union
  exact ⟨hunion ▸ Finset.mem_union_left _ (by simp),
    hunion ▸ Finset.mem_union_left _ (by simp)⟩

private theorem false_of_left_eq_left_branch_one {D E : GridRectangleDecomposition x z}
    (hcommon : D.first.left = D.second.left) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val)
    (hb_mem : D.first.right ∈ Grid.cIoo D.first.left D.second.right)
    (hEsides : (E.first.left = D.first.left ∧ E.first.right = D.second.right) ∨
      (E.first.left = D.second.right ∧ E.first.right = D.first.left)) : False := by
  set a := D.first.left
  set b := D.first.right
  set c := D.second.right
  have hab : a ≠ b := D.first.left_ne_right
  have hac : a ≠ c := by simpa only [a, c, hcommon] using D.second.left_ne_right
  have hbc : b ≠ c := Grid.ne_right_of_mem_cIoo hb_mem
  have hD₂_bot : D.second.bottom = x b := by
    rw [GridRectangleBetween.bottom_def, ← hcommon, D.first.map_left]
  have hD₂_top : D.second.top = x c := by
    rw [GridRectangleBetween.top_def, D.first.map_of_ne c hac.symm hbc.symm]
  rcases hEsides with ⟨hfl, hfr⟩ | ⟨hfl, _⟩
  · have hxa_notMem : x a ∉ Grid.cIoo (x b) (x c) := by
      have hmid_b : D.middle b = x a := D.first.map_right
      have h := D.second.isEmpty_iff_forall_notMem_cIoo.mp hD₂ b
        (by simpa [← hcommon] using hb_mem)
      simpa only [hmid_b, hD₂_bot, hD₂_top] using h
    have hxb_row : x b ∈ Grid.cIoo (x a) (x c) :=
      Grid.mem_cIoo_cyclic_left
        (((Grid.mem_cIoo_or_mem_cIoo_swap_iff (x.toPerm.injective.ne hbc)).mpr
          ⟨x.toPerm.injective.ne hab, x.toPerm.injective.ne hac⟩).resolve_left hxa_notMem)
    exact E.first.isEmpty_iff_forall_notMem_cIoo.mp hE₁ b (by simpa [hfl, hfr] using hb_mem)
      (by simpa [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hfl, hfr] using
        hxb_row)
  · refine false_of_mem_first_notMem_of_val_add_val_eq hsum (p := (c, x c))
      (by simpa only [hfl, GridRectangleBetween.bottom_def] using
        E.first.left_bottom_mem_coveredSquares) ?_ ?_
    · intro hc
      exact Grid.right_notMem_cIco a c
        (Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hb_mem ▸
          Finset.mem_union_left _ (D.first.mem_toGridRectangle_coveredSquares.mp hc).1)
    · intro hc
      have hcol := (D.second.mem_toGridRectangle_coveredSquares.mp hc).1
      rw [← hcommon] at hcol
      exact Grid.right_notMem_cIco a c hcol

private theorem false_of_left_eq_left_branch_two {D E : GridRectangleDecomposition x z}
    (hcommon : D.first.left = D.second.left) (hD₁ : D.first.IsEmpty)
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val)
    (hc_mem : D.second.right ∈ Grid.cIoo D.first.left D.first.right)
    (hEsides : (E.first.left = D.first.right ∧ E.first.right = D.second.right) ∨
      (E.first.left = D.second.right ∧ E.first.right = D.first.right)) : False := by
  set a := D.first.left
  set b := D.first.right
  set c := D.second.right
  have hac : a ≠ c := by simpa only [a, c, hcommon] using D.second.left_ne_right
  have hxc_notMem : x c ∉ Grid.cIoo (x a) (x b) := by
    simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def] using
      D.first.isEmpty_iff_forall_notMem_cIoo.mp hD₁ c hc_mem
  rcases hEsides with ⟨hfl, _⟩ | ⟨hfl, _⟩
  · refine false_of_mem_first_notMem_of_val_add_val_eq hsum (p := (b, x b))
      (by simpa only [hfl, GridRectangleBetween.bottom_def] using
        E.first.left_bottom_mem_coveredSquares) ?_ ?_
    · intro hb
      exact Grid.right_notMem_cIco a b (D.first.mem_toGridRectangle_coveredSquares.mp hb).1
    · intro hb
      have hcol := (D.second.mem_toGridRectangle_coveredSquares.mp hb).1
      rw [← hcommon] at hcol
      exact Grid.right_notMem_cIco a b
        (Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hc_mem ▸ Finset.mem_union_left _ hcol)
  · refine false_of_mem_first_notMem_of_val_add_val_eq hsum (p := (c, x c))
      (by simpa only [hfl, GridRectangleBetween.bottom_def] using
        E.first.left_bottom_mem_coveredSquares) ?_ ?_
    · intro hc
      exact hxc_notMem (Grid.mem_cIoo_of_mem_cIco
        (D.first.mem_toGridRectangle_coveredSquares.mp hc).2 (x.toPerm.injective.ne hac).symm)
    · intro hc
      have hcol := (D.second.mem_toGridRectangle_coveredSquares.mp hc).1
      rw [← hcommon] at hcol
      exact Grid.right_notMem_cIco a c hcol

private theorem eq_or_eq_recut_of_left_eq_left {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) (hcommon : D.first.left = D.second.left)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    E = D ∨ E = D.recut hone hD₁ hD₂ := by
  have hzx := D.target_ne_source_of_hasOneCommonSide hone
  by_cases hmidD : E.middle = D.middle
  · exact Or.inl (eq_of_middle_eq_of_val_add_val_eq hzx hmidD hsum)
  by_cases hmidR : E.middle = (D.recut hone hD₁ hD₂).middle
  · exact Or.inr (eq_of_middle_eq_of_val_add_val_eq hzx hmidR
      (hsum.trans (D.isRecut_recut hone hD₁ hD₂).isRepartition.val_add_val_eq.symm))
  exfalso
  set a := D.first.left
  set b := D.first.right
  set c := D.second.right
  have hE_sub : E.first.left ∈ ({a, b, c} : Finset (Fin n)) ∧
      E.first.right ∈ ({a, b, c} : Finset (Fin n)) :=
    first_sides_mem_of_union_eq hone <| by
      ext u
      simp only [Finset.mem_union, GridRectangleBetween.mem_sideColumns, Finset.mem_insert,
        Finset.mem_singleton, ← hcommon, a, b, c]
      tauto
  rcases (D.isRecutOfLeftEqLeft_recut hcommon hone hD₁ hD₂).recut_branch with
      ⟨hb_mem, hRmid, -, -⟩ | ⟨hc_mem, hRmid, -, -⟩
  · refine false_of_left_eq_left_branch_one hcommon hD₂ hE₁ hsum hb_mem
      (first_sides_of_mem_triple_of_ne (p := a) (q := c) (r := b)
        (by have h := hE_sub.1; simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto)
        (by have h := hE_sub.2; simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto)
        (by simpa only [D.first.target_eq_swapColumns] using hmidD)
        (by simpa only [hRmid, x.swapColumns_comm] using hmidR))
  · refine false_of_left_eq_left_branch_two hcommon hD₁ hsum hc_mem
      (first_sides_of_mem_triple_of_ne (p := b) (q := c) (r := a)
        (by have h := hE_sub.1; simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto)
        (by have h := hE_sub.2; simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto)
        (by simpa only [D.first.target_eq_swapColumns, x.swapColumns_comm b a] using hmidD)
        (by simpa only [hRmid, x.swapColumns_comm c a] using hmidR))

private theorem false_of_right_eq_right_branch_one {D E : GridRectangleDecomposition x z}
    (hcommon : D.first.right = D.second.right) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val)
    (ha_mem : D.first.left ∈ Grid.cIoo D.second.left D.first.right)
    (hEsides : (E.first.left = D.second.left ∧ E.first.right = D.first.right) ∨
      (E.first.left = D.first.right ∧ E.first.right = D.second.left)) : False := by
  set a := D.first.left
  set b := D.second.left
  set c := D.first.right
  have hab : a ≠ b := Grid.ne_left_of_mem_cIoo ha_mem
  have hac : a ≠ c := D.first.left_ne_right
  have hbc : b ≠ c := by simpa only [b, c, hcommon] using D.second.left_ne_right
  have hD₂_bot : D.second.bottom = x b := by
    rw [GridRectangleBetween.bottom_def, D.first.map_of_ne b hab.symm hbc]
  have hD₂_top : D.second.top = x a := by
    rw [GridRectangleBetween.top_def, ← hcommon, D.first.map_right]
  rcases hEsides with ⟨hfl, hfr⟩ | ⟨hfl, _⟩
  · have hxc_notMem : x c ∉ Grid.cIoo (x b) (x a) := by
      have hmid_a : D.middle a = x c := D.first.map_left
      have h := D.second.isEmpty_iff_forall_notMem_cIoo.mp hD₂ a
        (by simpa [← hcommon] using ha_mem)
      simpa only [hmid_a, hD₂_bot, hD₂_top] using h
    have hxa_row : x a ∈ Grid.cIoo (x b) (x c) :=
      Grid.mem_cIoo_cyclic_right
        (((Grid.mem_cIoo_or_mem_cIoo_swap_iff (x.toPerm.injective.ne hab).symm).mpr
          ⟨(x.toPerm.injective.ne hbc).symm, (x.toPerm.injective.ne hac).symm⟩).resolve_left
          hxc_notMem)
    exact E.first.isEmpty_iff_forall_notMem_cIoo.mp hE₁ a (by simpa [hfl, hfr] using ha_mem)
      (by simpa [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hfl, hfr] using
        hxa_row)
  · refine false_of_mem_first_notMem_of_val_add_val_eq hsum (p := (c, x c))
      (by simpa only [hfl, GridRectangleBetween.bottom_def] using
        E.first.left_bottom_mem_coveredSquares) ?_ ?_
    · intro hc
      exact Grid.right_notMem_cIco a c (D.first.mem_toGridRectangle_coveredSquares.mp hc).1
    · intro hc
      have hcol := (D.second.mem_toGridRectangle_coveredSquares.mp hc).1
      rw [← hcommon] at hcol
      exact Grid.right_notMem_cIco b c hcol

private theorem false_of_right_eq_right_branch_two {D E : GridRectangleDecomposition x z}
    (hcommon : D.first.right = D.second.right) (hD₁ : D.first.IsEmpty)
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val)
    (hb_mem : D.second.left ∈ Grid.cIoo D.first.left D.first.right)
    (hEsides : (E.first.left = D.first.left ∧ E.first.right = D.second.left) ∨
      (E.first.left = D.second.left ∧ E.first.right = D.first.left)) : False := by
  set a := D.first.left
  set b := D.second.left
  set c := D.first.right
  have hab : a ≠ b := (Grid.ne_left_of_mem_cIoo hb_mem).symm
  have hac : a ≠ c := D.first.left_ne_right
  have hbc : b ≠ c := by simpa only [b, c, hcommon] using D.second.left_ne_right
  have hxb_notMem : x b ∉ Grid.cIoo (x a) (x c) := by
    simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def] using
      D.first.isEmpty_iff_forall_notMem_cIoo.mp hD₁ b hb_mem
  have hxc_row : x c ∈ Grid.cIoo (x a) (x b) :=
    Grid.mem_cIoo_cyclic_right
      (((Grid.mem_cIoo_or_mem_cIoo_swap_iff (x.toPerm.injective.ne hac)).mpr
        ⟨(x.toPerm.injective.ne hab).symm, x.toPerm.injective.ne hbc⟩).resolve_left hxb_notMem)
  rcases hEsides with ⟨hfl, hfr⟩ | ⟨hfl, hfr⟩
  · refine false_of_mem_first_notMem_of_val_add_val_eq hsum (p := (a, x c)) ?_ ?_ ?_
    · rw [E.first.mem_toGridRectangle_coveredSquares, hfl, hfr]
      exact ⟨Grid.left_mem_cIco hab, Grid.cIoo_subset_cIco _ _ hxc_row⟩
    · intro ha
      exact Grid.right_notMem_cIco (x a) (x c)
        (D.first.mem_toGridRectangle_coveredSquares.mp ha).2
    · intro ha
      have hcol := (D.second.mem_toGridRectangle_coveredSquares.mp ha).1
      rw [← hcommon] at hcol
      exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hb_mem)
        (Grid.left_mem_cIco hab) hcol
  · refine false_of_mem_first_notMem_of_val_add_val_eq hsum (p := (c, x b)) ?_ ?_ ?_
    · rw [E.first.mem_toGridRectangle_coveredSquares, hfl, hfr]
      exact ⟨Grid.cIoo_subset_cIco _ _ (Grid.mem_cIoo_cyclic_left hb_mem),
        Grid.left_mem_cIco (x.toPerm.injective.ne hab).symm⟩
    · intro hc
      exact Grid.right_notMem_cIco a c (D.first.mem_toGridRectangle_coveredSquares.mp hc).1
    · intro hc
      have hcol := (D.second.mem_toGridRectangle_coveredSquares.mp hc).1
      rw [← hcommon] at hcol
      exact Grid.right_notMem_cIco b c hcol

private theorem eq_or_eq_recut_of_right_eq_right {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) (hcommon : D.first.right = D.second.right)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    E = D ∨ E = D.recut hone hD₁ hD₂ := by
  have hzx := D.target_ne_source_of_hasOneCommonSide hone
  by_cases hmidD : E.middle = D.middle
  · exact Or.inl (eq_of_middle_eq_of_val_add_val_eq hzx hmidD hsum)
  by_cases hmidR : E.middle = (D.recut hone hD₁ hD₂).middle
  · exact Or.inr (eq_of_middle_eq_of_val_add_val_eq hzx hmidR
      (hsum.trans (D.isRecut_recut hone hD₁ hD₂).isRepartition.val_add_val_eq.symm))
  exfalso
  set a := D.first.left
  set b := D.second.left
  set c := D.first.right
  have hE_sub : E.first.left ∈ ({a, b, c} : Finset (Fin n)) ∧
      E.first.right ∈ ({a, b, c} : Finset (Fin n)) :=
    first_sides_mem_of_union_eq hone <| by
      ext u
      simp only [Finset.mem_union, GridRectangleBetween.mem_sideColumns, Finset.mem_insert,
        Finset.mem_singleton, ← hcommon, a, b, c]
      tauto
  rcases (D.isRecutOfRightEqRight_recut hcommon hone hD₁ hD₂).recut_branch with
      ⟨ha_mem, hRmid, -, -⟩ | ⟨hb_mem, hRmid, -, -⟩
  · refine false_of_right_eq_right_branch_one hcommon hD₂ hE₁ hsum ha_mem
      (first_sides_of_mem_triple_of_ne (p := b) (q := c) (r := a)
        (by have h := hE_sub.1; simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto)
        (by have h := hE_sub.2; simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto)
        (by simpa only [hRmid] using hmidR)
        (by simpa only [D.first.target_eq_swapColumns, x.swapColumns_comm c a] using hmidD))
  · refine false_of_right_eq_right_branch_two hcommon hD₁ hsum hb_mem
      (first_sides_of_mem_triple_of_ne hE_sub.1 hE_sub.2
        (by simpa only [D.first.target_eq_swapColumns] using hmidD)
        (by simpa only [hRmid] using hmidR))

/-- When `D` has one common side column, any empty two-step decomposition covering the same
multiset of squares is either `D` or `D.recut hone hD₁ hD₂`. -/
theorem eq_or_eq_recut_of_val_add_val_eq {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hE₁ : E.first.IsEmpty)
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    E = D ∨ E = D.recut hone hD₁ hD₂ := by
  rcases D.hasSameSideOverlap_or_hasMixedSideOverlap hone with hsame | hmix
  · rcases (D.hasSameSideOverlap_iff.mp hsame).2 with hleft | hright
    · exact eq_or_eq_recut_of_left_eq_left hone hleft hD₁ hD₂ hE₁ hsum
    · exact eq_or_eq_recut_of_right_eq_right hone hright hD₁ hD₂ hE₁ hsum
  · -- Replace `D` by `D.recut`, which has same-side overlap and recuts back to `D`.
    have hrecut := D.isRecut_recut hone hD₁ hD₂
    have hsame := hasSameSideOverlap_recut_of_hasMixedSideOverlap D hmix hD₁ hD₂
    obtain ⟨hone', hside'⟩ := (D.recut hone hD₁ hD₂).hasSameSideOverlap_iff.mp hsame
    have hsum' : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
        (D.recut hone hD₁ hD₂).first.toGridRectangle.coveredSquares.val +
        (D.recut hone hD₁ hD₂).second.toGridRectangle.coveredSquares.val :=
      hsum.trans hrecut.isRepartition.val_add_val_eq.symm
    rcases hside' with hleft | hright
    · rcases eq_or_eq_recut_of_left_eq_left hone' hleft hrecut.isEmpty_first
          hrecut.isEmpty_second hE₁ hsum' with hE | hE
      · exact Or.inr hE
      · exact Or.inl (hE.trans (D.recut_recut hone hD₁ hD₂))
    · rcases eq_or_eq_recut_of_right_eq_right hone' hright hrecut.isEmpty_first
          hrecut.isEmpty_second hE₁ hsum' with hE | hE
      · exact Or.inr hE
      · exact Or.inl (hE.trans (D.recut_recut hone hD₁ hD₂))

/-! ### Combined classification -/

/-- Two distinct empty two-step decompositions covering the same multiset of squares are related
either by commuting two disjoint side pairs or by recutting along a single common side. -/
theorem eq_commute_or_eq_recut_of_ne_of_val_add_val_eq
    {D E : GridRectangleDecomposition x z}
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hE₁ : E.first.IsEmpty) (hE₂ : E.second.IsEmpty)
    (hne : E ≠ D)
    (hsum : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    (∃ h : D.HasDisjointSides, E = D.commute h) ∨
      (∃ h : D.HasOneCommonSide, E = D.recut h hD₁ hD₂) := by
  rcases D.hasDisjointSides_or_hasOneCommonSide_or_eq with hdisj | hone | rfl
  · exact Or.inl ⟨hdisj, (eq_or_eq_commute_of_val_add_val_eq hdisj hsum).resolve_left hne⟩
  · exact Or.inr
      ⟨hone, (eq_or_eq_recut_of_val_add_val_eq hone hD₁ hD₂ hE₁ hsum).resolve_left hne⟩
  · exact (hne (eq_of_val_add_val_eq_self hD₁ hD₂ hE₁ hE₂ hsum)).elim

end GridRectangleDecomposition

end TauCeti
