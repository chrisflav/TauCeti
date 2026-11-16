/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SignAssignment.Differential
import TauCeti.GroupTheory.Coxeter.Coboundary
import TauCeti.GroupTheory.Perm.Coxeter
import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing
import TauCeti.KnotTheory.Grid.Rectangle.Count

/-!
# Uniqueness of grid sign assignments up to gauge

Any two sign assignments `S, T : GridSignAssignment n` differ by a gauge transform
`T = S.gauge f` (`TauCeti.GridSignAssignment.exists_gauge_eq`), and the gauge
`f : GridState n → ℤˣ` is unique up to a global sign
(`TauCeti.GridSignAssignment.gauge_eq_gauge_iff`), hence unique once normalized at a chosen base
grid state (`TauCeti.GridSignAssignment.existsUnique_gauge_eq`). As a consequence, the signed
unblocked grid complexes attached to any two sign assignments are isomorphic by a diagonal sign
change (`TauCeti.GridDiagram.exists_signEquiv_signedUnblockedDifferential`).

The proof follows Manolescu–Ozsváth–Szabó–Thurston (Theorem 4.2) and
Ozsváth–Stipsicz–Szabó (Theorem 15.2.3). Writing `ρ(r) = S(r) · T(r) ∈ {±1}` for the ratio of
two sign assignments on an empty rectangle `r`, the square and annulus rules say that `ρ`
satisfies the same relations with all minus signs replaced by `+1`. The argument proceeds in
three stages:

1. **Adjacent columns (width `1`)**: restricting `ρ` to the width-`1` empty rectangles between
   `⟨σ⟩` and `⟨σ · sᵢ⟩` yields a `{±1}`-valued `1`-cocycle on the right Cayley graph of the
   type-`A` Coxeter system `TauCeti.permCoxeterSystem n`. The vertical annulus rule gives
   involution, the disjoint square rule gives commutation for `|i - j| ≥ 2`, and two recuts of
   an empty width-`2` rectangle give the length-`3` braid relation for `|i - j| = 1`. The
   Coxeter coboundary theorem (`CoxeterSystem.exists_coboundary`) therefore produces a gauge
   adjusting `S` so that `ρ = 1` on all adjacent-column rectangles.
2. **Non-wrapping rectangles (`r.left < r.right`)**: induction on the width `r.right - r.left`
   using `left = left` recuts against a width-`1` rectangle shows `ρ = 1` on every non-wrapping
   empty rectangle.
3. **All empty rectangles**: strong induction on the cardinality of the row interior
   `cIoo r.bottom r.top` handles wrapping rectangles (`r.right < r.left`). If the row interior is
   empty, the horizontal-annulus return rectangle is empty and non-wrapping; otherwise, taking the
   rightmost grid point whose row lies in `cIoo r.bottom r.top` produces a non-wrapping empty
   rectangle `s` whose `left = right` recut with `r` splits `cIoo r.bottom r.top` into two strictly
   smaller row interiors.

## Main results

* `TauCeti.GridSignAssignment.exists_gauge_eq`: any two sign assignments differ by a gauge.
* `TauCeti.GridSignAssignment.gauge_eq_gauge_iff`: two gauges produce the same sign assignment
  iff they differ by a global sign.
* `TauCeti.GridSignAssignment.existsUnique_gauge_eq`: unique gauge normalized at a base grid state.
* `TauCeti.GridDiagram.exists_signEquiv_signedUnblockedDifferential`: any two sign assignments
  induce isomorphic signed unblocked grid complexes.

## References

* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Section 4, Theorem 4.2.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 15.2, Theorem 15.2.3.
-/

public section

namespace TauCeti

namespace GridSignAssignment

open TauCeti.BraidGroup

/-! ### Ratio of two sign assignments -/

/-- The pointwise product `S(r) * T(r) ∈ ℤˣ` on empty rectangles, equal to `1` iff `S` and `T`
agree on `r`. -/
private def ratio {n : ℕ} (S T : GridSignAssignment n) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) : ℤˣ :=
  S.sign r hr * T.sign r hr

private theorem ratio_eq_one_iff {n : ℕ} {S T : GridSignAssignment n} {x y : GridState n}
    {r : GridRectangleBetween x y} (hr : r.IsEmpty) :
    ratio S T r hr = 1 ↔ S.sign r hr = T.sign r hr := by
  rw [ratio, mul_eq_one_iff_eq_inv, Int.units_inv_eq_self]

private theorem ratio_eq_of_eq {n : ℕ} (S T : GridSignAssignment n)
    {x₁ y₁ x₂ y₂ : GridState n}
    {r₁ : GridRectangleBetween x₁ y₁} {r₂ : GridRectangleBetween x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (hl : r₁.left = r₂.left)
    (hr₁ : r₁.IsEmpty) (hr₂ : r₂.IsEmpty) :
    ratio S T r₁ hr₁ = ratio S T r₂ hr₂ := by
  subst hx; subst hy
  rcases r₁.eq_or_eq_swapSides r₂ with rfl | hswap
  · rfl
  · exfalso
    rw [hswap, GridRectangleBetween.swapSides_left] at hl
    exact r₁.left_ne_right hl

private theorem ratio_mul_ratio_eq {n : ℕ} (S T : GridSignAssignment n) {x z : GridState n}
    {D E : GridRectangleDecomposition x z}
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hE₁ : E.first.IsEmpty) (hE₂ : E.second.IsEmpty) (hne : E ≠ D)
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    ratio S T E.first hE₁ * ratio S T E.second hE₂ =
      ratio S T D.first hD₁ * ratio S T D.second hD₂ := by
  unfold ratio
  calc (S.sign E.first hE₁ * T.sign E.first hE₁) *
          (S.sign E.second hE₂ * T.sign E.second hE₂)
      = (S.sign E.first hE₁ * S.sign E.second hE₂) *
          (T.sign E.first hE₁ * T.sign E.second hE₂) := by ac_rfl
    _ = (-(S.sign D.first hD₁ * S.sign D.second hD₂)) *
          (-(T.sign D.first hD₁ * T.sign D.second hD₂)) := by
        rw [S.sign_mul_sign_eq_neg D E hD₁ hD₂ hE₁ hE₂ hne hdomain,
          T.sign_mul_sign_eq_neg D E hD₁ hD₂ hE₁ hE₂ hne hdomain]
    _ = (S.sign D.first hD₁ * T.sign D.first hD₁) *
          (S.sign D.second hD₂ * T.sign D.second hD₂) := by
        rw [neg_mul_neg]
        ac_rfl

private theorem ratio_commute {n : ℕ} (S T : GridSignAssignment n) {x z : GridState n}
    (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) :
    ratio S T (D.commute h).first (D.isEmpty_commute_first h hD₁ hD₂) *
        ratio S T (D.commute h).second (D.isEmpty_commute_second h hD₁ hD₂) =
      ratio S T D.first hD₁ * ratio S T D.second hD₂ := by
  refine ratio_mul_ratio_eq S T hD₁ hD₂ _ _ (D.commute_ne h) ?_
  rw [D.commute_first_toGridRectangle h, D.commute_second_toGridRectangle h, add_comm]

private theorem ratio_recut {n : ℕ} (S T : GridSignAssignment n) {x z : GridState n}
    (D : GridRectangleDecomposition x z) (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) :
    ratio S T (D.recut hone hD₁ hD₂).first (D.isRecut_recut hone hD₁ hD₂).isEmpty_first *
        ratio S T (D.recut hone hD₁ hD₂).second
          (D.isRecut_recut hone hD₁ hD₂).isEmpty_second =
      ratio S T D.first hD₁ * ratio S T D.second hD₂ :=
  ratio_mul_ratio_eq S T hD₁ hD₂ _ _ (D.recut_ne hone hD₁ hD₂)
    (D.isRecut_recut hone hD₁ hD₂).isRepartition.val_add_val_eq

private theorem ratio_mul_ratio_eq_one_of_left_eq_left {n : ℕ} (S T : GridSignAssignment n)
    {x y : GridState n} (r : GridRectangleBetween x y) (s : GridRectangleBetween y x)
    (hr : r.IsEmpty) (hs : s.IsEmpty) (hleft : s.left = r.left) :
    ratio S T r hr * ratio S T s hs = 1 := by
  unfold ratio
  calc (S.sign r hr * T.sign r hr) * (S.sign s hs * T.sign s hs)
      = (S.sign r hr * S.sign s hs) * (T.sign r hr * T.sign s hs) := by ac_rfl
    _ = (-1) * (-1) := by
        rw [S.sign_mul_sign_eq_neg_one_of_left_eq_left r s hr hs hleft,
          T.sign_mul_sign_eq_neg_one_of_left_eq_left r s hr hs hleft]
    _ = 1 := by norm_num

private theorem ratio_mul_ratio_eq_one_of_left_eq_right {n : ℕ} (S T : GridSignAssignment n)
    {x y : GridState n} (r : GridRectangleBetween x y) (s : GridRectangleBetween y x)
    (hr : r.IsEmpty) (hs : s.IsEmpty) (hleft : s.left = r.right) :
    ratio S T r hr * ratio S T s hs = 1 := by
  unfold ratio
  calc (S.sign r hr * T.sign r hr) * (S.sign s hs * T.sign s hs)
      = (S.sign r hr * S.sign s hs) * (T.sign r hr * T.sign s hs) := by ac_rfl
    _ = 1 * 1 := by
        rw [S.sign_mul_sign_eq_one_of_left_eq_right r s hr hs hleft,
          T.sign_mul_sign_eq_one_of_left_eq_right r s hr hs hleft]
    _ = 1 := one_mul 1

/-! ### Step 1: Cocycle on adjacent transpositions -/

private theorem strandSucc_eq_finRotate {n : ℕ} (i : Fin (n - 1)) :
    strandSucc i = finRotate n (strand i) := by
  cases n with
  | zero => exact (strand i).elim0
  | succ m =>
    refine Fin.ext ?_
    rw [coe_finRotate_of_ne_last (fun h => by
      have := congrArg Fin.val h
      simp [val_strand, Fin.val_last] at this
      omega)]
    simp [val_strand, val_strandSucc]

private theorem mk_mul_simple_eq_swapColumns {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (⟨σ * (permCoxeterSystem n).simple i⟩ : GridState n) =
      (⟨σ⟩ : GridState n).swapColumns (strand i) (strandSucc i) := by
  refine GridState.ext fun c => ?_
  rw [GridState.swapColumns_apply]
  change (σ * (permCoxeterSystem n).simple i) c = σ (Equiv.swap (strand i) (strandSucc i) c)
  rw [Equiv.Perm.mul_apply, permCoxeterSystem_simple, transposition_eq_swap]

/-- The width-`1` empty rectangle from `⟨σ⟩` to `⟨σ * sᵢ⟩` along columns `i` and `i + 1`. -/
private noncomputable def adjRect {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    GridRectangleBetween (⟨σ⟩ : GridState n) ⟨σ * (permCoxeterSystem n).simple i⟩ :=
  GridRectangleBetween.ofSwapColumns ⟨σ⟩ ⟨σ * (permCoxeterSystem n).simple i⟩
    (strand i) (strandSucc i) (strand_ne_strandSucc i) (mk_mul_simple_eq_swapColumns σ i)

private theorem adjRect_left {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (adjRect σ i).left = strand i :=
  GridRectangleBetween.ofSwapColumns_left _ _ _ _ _ _

private theorem adjRect_right {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (adjRect σ i).right = strandSucc i :=
  GridRectangleBetween.ofSwapColumns_right _ _ _ _ _ _

private theorem adjRect_isEmpty {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (adjRect σ i).IsEmpty :=
  (adjRect σ i).isEmpty_of_right_eq_finRotate <| by
    rw [adjRect_left, adjRect_right, strandSucc_eq_finRotate]

/-- The `{±1}`-valued `1`-cocycle on the type-`A` Cayley graph obtained by evaluating `ratio S T`
on width-`1` rectangles. -/
private noncomputable def adjCocycle {n : ℕ} (S T : GridSignAssignment n)
    (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) : ℤˣ :=
  ratio S T (adjRect σ i) (adjRect_isEmpty σ i)

private theorem adjCocycle_inv {n : ℕ} (S T : GridSignAssignment n) (σ : Equiv.Perm (Fin n))
    (i : Fin (n - 1)) :
    adjCocycle S T σ i * adjCocycle S T (σ * (permCoxeterSystem n).simple i) i = 1 := by
  have hsq : σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple i = σ := by
    rw [mul_assoc, (permCoxeterSystem n).simple_mul_simple_self, mul_one]
  let s : GridRectangleBetween ⟨σ * (permCoxeterSystem n).simple i⟩ (⟨σ⟩ : GridState n) :=
    GridRectangleBetween.ofSwapColumns _ _ (strand i) (strandSucc i) (strand_ne_strandSucc i) <| by
      rw [← mk_mul_simple_eq_swapColumns, hsq]
  have hs : s.IsEmpty := s.isEmpty_of_right_eq_finRotate <| by
    simp [s, GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      strandSucc_eq_finRotate]
  have hreq : adjCocycle S T (σ * (permCoxeterSystem n).simple i) i = ratio S T s hs :=
    ratio_eq_of_eq S T rfl (congrArg GridState.mk hsq)
      (by simp [s, adjRect_left, GridRectangleBetween.ofSwapColumns_left]) _ hs
  rw [adjCocycle, hreq]
  exact ratio_mul_ratio_eq_one_of_left_eq_left S T (adjRect σ i) s (adjRect_isEmpty σ i) hs
    (by simp [s, adjRect_left, GridRectangleBetween.ofSwapColumns_left])

private theorem adjCocycle_mul_simple_self {n : ℕ} (S T : GridSignAssignment n)
    (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    adjCocycle S T (σ * (permCoxeterSystem n).simple i) i = adjCocycle S T σ i := by
  have h := (mul_eq_one_iff_eq_inv.mp (adjCocycle_inv S T σ i))
  simpa [Int.units_inv_eq_self] using h.symm

private theorem adjCocycle_braid_two {n : ℕ} (S T : GridSignAssignment n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)}
    (hfar : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    adjCocycle S T σ i * adjCocycle S T (σ * (permCoxeterSystem n).simple i) j =
      adjCocycle S T σ j * adjCocycle S T (σ * (permCoxeterSystem n).simple j) i := by
  let D : GridRectangleDecomposition (⟨σ⟩ : GridState n)
      ⟨σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j⟩ :=
    ⟨⟨σ * (permCoxeterSystem n).simple i⟩, adjRect σ i, adjRect _ j⟩
  have hdisj : D.HasDisjointSides := by
    rw [D.hasDisjointSides_iff]
    simp only [D, adjRect_left, adjRect_right, ne_eq, Fin.ext_iff, val_strand, val_strandSucc]
    omega
  have hcomm := ratio_commute S T D hdisj (adjRect_isEmpty σ i) (adjRect_isEmpty _ j)
  have hcommPerm : σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j =
      σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i := by
    simp only [mul_assoc, permCoxeterSystem_simple]
    rw [transposition_mul_transposition_comm hfar]
  have hmid : (D.commute hdisj).middle = ⟨σ * (permCoxeterSystem n).simple j⟩ := by
    rw [D.commute_middle hdisj]
    simpa [D, adjRect_left, adjRect_right] using (mk_mul_simple_eq_swapColumns σ j).symm
  have h1 : ratio S T (D.commute hdisj).first
      (D.isEmpty_commute_first hdisj (adjRect_isEmpty σ i) (adjRect_isEmpty _ j)) =
      adjCocycle S T σ j :=
    ratio_eq_of_eq S T rfl hmid (by rw [D.commute_first_left hdisj]; simp [D, adjRect_left]) _ _
  have h2 : ratio S T (D.commute hdisj).second
      (D.isEmpty_commute_second hdisj (adjRect_isEmpty σ i) (adjRect_isEmpty _ j)) =
      adjCocycle S T (σ * (permCoxeterSystem n).simple j) i :=
    ratio_eq_of_eq S T hmid (congrArg GridState.mk hcommPerm)
      (by rw [D.commute_second_left hdisj]; simp [D, adjRect_left]) _ _
  rw [h1, h2] at hcomm
  exact hcomm.symm

private theorem swap_strand_strandSucc_eq {n : ℕ} {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j) :
    Equiv.swap (strand i) (strandSucc j) =
      (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j *
        (permCoxeterSystem n).simple i := by
  have hbc : strandSucc i = strand j := Fin.ext (by simp [val_strandSucc, val_strand, hij])
  have hab : strand i ≠ strand j := by rw [← hbc]; exact strand_ne_strandSucc i
  have hbc' : strand j ≠ strandSucc j := strand_ne_strandSucc j
  have hac : strand i ≠ strandSucc j := strand_ne_strandSucc_of_succ hij
  ext x
  simp only [permCoxeterSystem_simple, transposition_eq_swap, Equiv.Perm.mul_apply, hbc,
    Equiv.swap_apply_def]
  grind

private theorem mem_cIoo_strand_strandSucc_iff {n : ℕ} {i j : Fin (n - 1)}
    (hij : (i : ℕ) + 1 = j) (x : Fin n) :
    x ∈ Grid.cIoo (strand i) (strandSucc j) ↔ x = strand j := by
  rw [Grid.mem_cIoo_of_val_lt (by simp only [val_strand, val_strandSucc]; omega)]
  simp only [Fin.ext_iff, val_strand, val_strandSucc]
  omega

private theorem adjCocycle_braid_three_of_notMem {n : ℕ} (S T : GridSignAssignment n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j)
    (hnot : σ (strand j) ∉ Grid.cIoo (σ (strand i)) (σ (strandSucc j))) :
    adjCocycle S T σ j * adjCocycle S T (σ * (permCoxeterSystem n).simple j) i *
        adjCocycle S T (σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i) j =
      adjCocycle S T σ i * adjCocycle S T (σ * (permCoxeterSystem n).simple i) j *
        adjCocycle S T
          (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i := by
  let a : Fin n := strand i
  let b : Fin n := strand j
  let c : Fin n := strandSucc j
  have hbi : strandSucc i = b := Fin.ext (by simp [b, val_strandSucc, val_strand, hij])
  have hac : a ≠ c := strand_ne_strandSucc_of_succ hij
  have hbraid : (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j *
      (permCoxeterSystem n).simple i =
      (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i *
        (permCoxeterSystem n).simple j := by
    simp only [permCoxeterSystem_simple]
    exact transposition_braid (Or.inl hij)
  have hswap : Equiv.swap a c =
      (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j *
        (permCoxeterSystem n).simple i := swap_strand_strandSucc_eq hij
  let τ : Equiv.Perm (Fin n) := σ * Equiv.swap a c
  have hτ_eq : (⟨τ⟩ : GridState n) = (⟨σ⟩ : GridState n).swapColumns a c := by
    refine GridState.ext fun k => ?_
    rw [GridState.swapColumns_apply]
    exact Equiv.Perm.mul_apply σ (Equiv.swap a c) k
  let w : GridRectangleBetween (⟨σ⟩ : GridState n) ⟨τ⟩ :=
    GridRectangleBetween.ofSwapColumns ⟨σ⟩ ⟨τ⟩ a c hac hτ_eq
  have hw_left : w.left = a := GridRectangleBetween.ofSwapColumns_left _ _ _ _ _ _
  have hw_right : w.right = c := GridRectangleBetween.ofSwapColumns_right _ _ _ _ _ _
  have hw_empty : w.IsEmpty := by
    rw [w.isEmpty_iff_forall_notMem_cIoo]
    intro k hk
    rw [hw_left, hw_right, mem_cIoo_strand_strandSucc_iff hij] at hk
    subst hk
    simpa [w, GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top]
      using hnot
  have hτi : τ * (permCoxeterSystem n).simple i =
      σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j := by
    simp only [τ, hswap, mul_assoc, (permCoxeterSystem n).simple_mul_simple_self, mul_one]
  have hτj : τ * (permCoxeterSystem n).simple j =
      σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i := by
    simp only [τ, hswap, hbraid, mul_assoc, (permCoxeterSystem n).simple_mul_simple_self, mul_one]
  have hbmem : b ∈ Grid.cIoo a c := (mem_cIoo_strand_strandSucc_iff hij b).mpr rfl
  -- Recut 1: `w` followed by `adjRect τ i` (sharing `left = a`).
  let D₁ : GridRectangleDecomposition (⟨σ⟩ : GridState n)
      ⟨τ * (permCoxeterSystem n).simple i⟩ :=
    ⟨⟨τ⟩, w, adjRect τ i⟩
  have hcom₁ : D₁.first.left = D₁.second.left := by simp [D₁, hw_left, adjRect_left, a]
  have hcol₁ : D₁.second.right ∈ Grid.cIoo D₁.first.left D₁.first.right := by
    simpa [D₁, hw_left, hw_right, adjRect_right, hbi] using hbmem
  let hone₁ := D₁.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcom₁ hcol₁
  obtain ⟨hE₁fl, hE₁fr, hE₁sl, _⟩ :=
    D₁.recut_sides_of_left_eq_left_of_mem_cIoo hcom₁ hcol₁ hw_empty (adjRect_isEmpty τ i)
  have hE₁mid : (D₁.recut hone₁ hw_empty (adjRect_isEmpty τ i)).middle =
      ⟨σ * (permCoxeterSystem n).simple i⟩ := by
    have htar := (D₁.recut hone₁ hw_empty (adjRect_isEmpty τ i)).first.target_toPerm_eq
    rw [hE₁fl, hE₁fr] at htar
    simp only [D₁, hw_left, adjRect_right, hbi] at htar
    refine GridState.ext fun k => ?_
    change (D₁.recut hone₁ hw_empty (adjRect_isEmpty τ i)).middle.toPerm k =
      (σ * (permCoxeterSystem n).simple i) k
    rw [htar, Equiv.trans_apply, Equiv.Perm.mul_apply, permCoxeterSystem_simple,
      transposition_eq_swap, hbi]
  have hrec₁ := ratio_recut S T D₁ hone₁ hw_empty (adjRect_isEmpty τ i)
  have hE₁f : ratio S T (D₁.recut hone₁ hw_empty (adjRect_isEmpty τ i)).first
      (D₁.isRecut_recut hone₁ hw_empty (adjRect_isEmpty τ i)).isEmpty_first =
      adjCocycle S T σ i :=
    ratio_eq_of_eq S T rfl hE₁mid (by rw [hE₁fl]; simp [D₁, hw_left, adjRect_left, a]) _ _
  have hE₁s : ratio S T (D₁.recut hone₁ hw_empty (adjRect_isEmpty τ i)).second
      (D₁.isRecut_recut hone₁ hw_empty (adjRect_isEmpty τ i)).isEmpty_second =
      adjCocycle S T (σ * (permCoxeterSystem n).simple i) j :=
    ratio_eq_of_eq S T hE₁mid (congrArg GridState.mk hτi)
      (by rw [hE₁sl]; simp [D₁, adjRect_right, adjRect_left, hbi, b]) _ _
  rw [hE₁f, hE₁s] at hrec₁
  have hτi_coc : adjCocycle S T τ i =
      adjCocycle S T (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i := by
    rw [← hτi, adjCocycle_mul_simple_self]
  have heq₁ : ratio S T w hw_empty =
      adjCocycle S T σ i * adjCocycle S T (σ * (permCoxeterSystem n).simple i) j *
        adjCocycle S T
          (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i := by
    have hmul := congrArg (· * adjCocycle S T τ i) hrec₁.symm
    dsimp only [D₁] at hmul
    rw [mul_assoc, ← adjCocycle, Int.units_mul_self, mul_one, hτi_coc] at hmul
    exact hmul
  -- Recut 2: `w` followed by `adjRect τ j` (sharing `right = c`).
  let D₂ : GridRectangleDecomposition (⟨σ⟩ : GridState n)
      ⟨τ * (permCoxeterSystem n).simple j⟩ :=
    ⟨⟨τ⟩, w, adjRect τ j⟩
  have hcom₂ : D₂.first.right = D₂.second.right := by simp [D₂, hw_right, adjRect_right, c]
  have hcol₂ : D₂.second.left ∈ Grid.cIoo D₂.first.left D₂.first.right := by
    simpa [D₂, hw_left, hw_right, adjRect_left, b] using hbmem
  let hone₂ := D₂.hasOneCommonSide_of_right_eq_right hcom₂
    (Grid.ne_left_of_mem_cIoo hcol₂).symm
  have hdata₂ := D₂.isRecutOfRightEqRight_recut hcom₂ hone₂ hw_empty (adjRect_isEmpty τ j)
  obtain ⟨hE₂fl, hE₂sl⟩ := hdata₂.recut_sides
  obtain ⟨hE₂fr, -, -, -, -, -⟩ :=
    D₂.recut_geometry_of_right_eq_right_of_second_left_mem_cIoo hcom₂ hcol₂ hw_empty
      (adjRect_isEmpty τ j)
  have hE₂mid : (D₂.recut hone₂ hw_empty (adjRect_isEmpty τ j)).middle =
      ⟨σ * (permCoxeterSystem n).simple j⟩ := by
    have htar := (D₂.recut hone₂ hw_empty (adjRect_isEmpty τ j)).first.target_toPerm_eq
    rw [hE₂fl, hE₂fr] at htar
    simp only [D₂, adjRect_left, hw_right, c] at htar
    refine GridState.ext fun k => ?_
    change (D₂.recut hone₂ hw_empty (adjRect_isEmpty τ j)).middle.toPerm k =
      (σ * (permCoxeterSystem n).simple j) k
    rw [htar, Equiv.trans_apply, Equiv.Perm.mul_apply, permCoxeterSystem_simple,
      transposition_eq_swap]
  have hrec₂ := ratio_recut S T D₂ hone₂ hw_empty (adjRect_isEmpty τ j)
  have hE₂f : ratio S T (D₂.recut hone₂ hw_empty (adjRect_isEmpty τ j)).first
      (D₂.isRecut_recut hone₂ hw_empty (adjRect_isEmpty τ j)).isEmpty_first =
      adjCocycle S T σ j :=
    ratio_eq_of_eq S T rfl hE₂mid (by rw [hE₂fl]; simp [D₂, adjRect_left]) _ _
  have hE₂s : ratio S T (D₂.recut hone₂ hw_empty (adjRect_isEmpty τ j)).second
      (D₂.isRecut_recut hone₂ hw_empty (adjRect_isEmpty τ j)).isEmpty_second =
      adjCocycle S T (σ * (permCoxeterSystem n).simple j) i :=
    ratio_eq_of_eq S T hE₂mid (congrArg GridState.mk hτj)
      (by rw [hE₂sl]; simp [D₂, hw_left, adjRect_left, a]) _ _
  rw [hE₂f, hE₂s] at hrec₂
  have hτj_coc : adjCocycle S T τ j =
      adjCocycle S T (σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i) j := by
    rw [← hτj, adjCocycle_mul_simple_self]
  have heq₂ : ratio S T w hw_empty =
      adjCocycle S T σ j * adjCocycle S T (σ * (permCoxeterSystem n).simple j) i *
        adjCocycle S T
          (σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i) j := by
    have hmul := congrArg (· * adjCocycle S T τ j) hrec₂.symm
    dsimp only [D₂] at hmul
    rw [mul_assoc, ← adjCocycle, Int.units_mul_self, mul_one, hτj_coc] at hmul
    exact hmul
  exact heq₂.symm.trans heq₁

private theorem adjCocycle_braid_three {n : ℕ} (S T : GridSignAssignment n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j) :
    adjCocycle S T σ j * adjCocycle S T (σ * (permCoxeterSystem n).simple j) i *
        adjCocycle S T (σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i) j =
      adjCocycle S T σ i * adjCocycle S T (σ * (permCoxeterSystem n).simple i) j *
        adjCocycle S T
          (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i := by
  by_cases hmem : σ (strand j) ∈ Grid.cIoo (σ (strand i)) (σ (strandSucc j))
  · -- Flip `σ` by `sᵢ` so the middle row moves outside the open interval.
    let σ' := σ * (permCoxeterSystem n).simple i
    have hbi : strandSucc i = strand j := Fin.ext (by simp [val_strandSucc, val_strand, hij])
    have hcne₁ : strandSucc j ≠ strand i := (strand_ne_strandSucc_of_succ hij).symm
    have hcne₂ : strandSucc j ≠ strand j := (strand_ne_strandSucc j).symm
    have hσ'a : σ' (strand i) = σ (strand j) := by
      simp [σ', permCoxeterSystem_simple, transposition_eq_swap, hbi]
    have hσ'b : σ' (strand j) = σ (strand i) := by
      simp [σ', permCoxeterSystem_simple, transposition_eq_swap, hbi]
    have hσ'c : σ' (strandSucc j) = σ (strandSucc j) := by
      simp [σ', permCoxeterSystem_simple, transposition_eq_swap, hbi,
        Equiv.swap_apply_of_ne_of_ne hcne₁ hcne₂]
    have hnot : σ' (strand j) ∉ Grid.cIoo (σ' (strand i)) (σ' (strandSucc j)) := by
      rw [hσ'a, hσ'b, hσ'c]
      exact Grid.notMem_cIoo_of_mem_cIoo hmem
    have h' := adjCocycle_braid_three_of_notMem S T σ' hij hnot
    have hbraid : σ' * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i =
        σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i *
          (permCoxeterSystem n).simple j := by
      simp only [σ', permCoxeterSystem_simple]
      calc σ * transposition i * transposition j * transposition i
          = σ * (transposition i * transposition j * transposition i) := by simp only [mul_assoc]
        _ = σ * (transposition j * transposition i * transposition j) := by
            rw [transposition_braid (Or.inl hij)]
        _ = σ * transposition j * transposition i * transposition j := by simp only [mul_assoc]
    have hσ'i : σ' * (permCoxeterSystem n).simple i = σ := by
      simp [σ', mul_assoc]
    have hlast : adjCocycle S T (σ' * (permCoxeterSystem n).simple j *
        (permCoxeterSystem n).simple i) j =
        adjCocycle S T
          (σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i) j := by
      rw [hbraid, adjCocycle_mul_simple_self]
    have hfirst : adjCocycle S T σ' i = adjCocycle S T σ i :=
      adjCocycle_mul_simple_self S T σ i
    rw [hσ'i, hlast, hfirst] at h'
    have hmul := congrArg (fun u =>
      (adjCocycle S T σ j * adjCocycle S T (σ * (permCoxeterSystem n).simple j) i) *
      (adjCocycle S T σ' j * adjCocycle S T (σ' * (permCoxeterSystem n).simple j) i) * u) h'
    have hcancel : ∀ x y z : ℤˣ, x * y * (y * z) = x * z := fun x y z => by
      calc x * y * (y * z) = (y * y) * (x * z) := by ac_rfl
        _ = x * z := by rw [Int.units_mul_self, one_mul]
    have hcancel' : ∀ x y w : ℤˣ, x * y * (w * x) = w * y := fun x y w => by
      calc x * y * (w * x) = (x * x) * (w * y) := by ac_rfl
        _ = w * y := by rw [Int.units_mul_self, one_mul]
    rw [hcancel, mul_assoc (adjCocycle S T σ i), hcancel'] at hmul
    simpa [mul_assoc, σ'] using hmul
  · exact adjCocycle_braid_three_of_notMem S T σ hij hmem

private theorem adjCocycle_braid {n : ℕ} (S T : GridSignAssignment n) (σ : Equiv.Perm (Fin n))
    (i j : Fin (n - 1)) (_ : CoxeterMatrix.A (n - 1) i j ≠ 0) :
    (permCoxeterSystem n).wordCocycleProd (adjCocycle S T) σ
        (CoxeterSystem.braidWord (CoxeterMatrix.A (n - 1)) i j) =
      (permCoxeterSystem n).wordCocycleProd (adjCocycle S T) σ
        (CoxeterSystem.braidWord (CoxeterMatrix.A (n - 1)) j i) := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have hval : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  by_cases hadj : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
  · rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, coxeterMatrixA_eq_three hadj,
      coxeterMatrixA_eq_three hadj.symm, CoxeterSystem.wordCocycleProd_alternatingWord_three,
      CoxeterSystem.wordCocycleProd_alternatingWord_three]
    rcases hadj with h | h
    · exact adjCocycle_braid_three S T σ h
    · exact (adjCocycle_braid_three S T σ h).symm
  · have hfar : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i := by omega
    rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, coxeterMatrixA_eq_two hfar,
      coxeterMatrixA_eq_two hfar.symm, CoxeterSystem.wordCocycleProd_alternatingWord_two,
      CoxeterSystem.wordCocycleProd_alternatingWord_two]
    exact adjCocycle_braid_two S T σ hfar

/-! ### Step 2: Non-wrapping rectangles (`r.left < r.right`) -/

private theorem ratio_eq_one_of_left_lt_right {n : ℕ} {S T : GridSignAssignment n}
    (hadj : ∀ σ i, adjCocycle S T σ i = 1) :
    ∀ (d : ℕ) {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      (r.left : ℕ) < r.right → (r.right : ℕ) - r.left = d + 1 → ratio S T r hr = 1
  | 0, x, y, r, hr, hlt, hdiff => by
    let i : Fin (n - 1) := ⟨r.left, by have := r.right.isLt; omega⟩
    have hl : strand i = r.left := Fin.ext (by simp [val_strand, i])
    have hr' : strandSucc i = r.right := Fin.ext (by simp [val_strandSucc, i]; omega)
    have hy : y = ⟨x.toPerm * (permCoxeterSystem n).simple i⟩ := by
      refine GridState.ext fun c => ?_
      change y.toPerm c = (x.toPerm * (permCoxeterSystem n).simple i) c
      rw [r.target_toPerm_eq, Equiv.trans_apply, Equiv.Perm.mul_apply, permCoxeterSystem_simple,
        transposition_eq_swap, hl, hr']
    have hreq : ratio S T r hr = adjCocycle S T x.toPerm i :=
      ratio_eq_of_eq S T rfl hy (by rw [adjRect_left, hl]) hr (adjRect_isEmpty x.toPerm i)
    rw [hreq, hadj]
  | d + 1, x, y, r, hr, hlt, hdiff => by
    let a := r.left
    let b := r.right
    let a' : Fin n := finRotate n a
    have ha'val : (a' : ℕ) = (a : ℕ) + 1 := by
      cases n with
      | zero => exact a.elim0
      | succ m =>
        rw [coe_finRotate_of_ne_last (fun h => by
          have hval := congrArg Fin.val h
          simp [Fin.val_last] at hval
          have := b.isLt
          omega)]
    have haa' : a ≠ a' := fun h => by
      have := congrArg Fin.val h
      omega
    have ha'mem : a' ∈ Grid.cIoo a b := by
      rw [Grid.mem_cIoo_of_val_lt hlt]
      omega
    let s : GridRectangleBetween y (y.swapColumns a a') :=
      GridRectangleBetween.ofSwapColumns y (y.swapColumns a a') a a' haa' rfl
    have hs_left : s.left = a := GridRectangleBetween.ofSwapColumns_left _ _ _ _ _ _
    have hs_right : s.right = a' := GridRectangleBetween.ofSwapColumns_right _ _ _ _ _ _
    have hs_empty : s.IsEmpty := s.isEmpty_of_right_eq_finRotate (by rw [hs_left, hs_right])
    have hs_ratio : ratio S T s hs_empty = 1 :=
      ratio_eq_one_of_left_lt_right hadj 0 s hs_empty
        (by rw [hs_left, hs_right, ha'val]; omega)
        (by rw [hs_left, hs_right, ha'val]; omega)
    let D : GridRectangleDecomposition x (y.swapColumns a a') := ⟨y, r, s⟩
    have hcom : D.first.left = D.second.left := hs_left.symm
    have hcol : D.second.right ∈ Grid.cIoo D.first.left D.first.right := by
      simpa [D, hs_right] using ha'mem
    let hone := D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcom hcol
    obtain ⟨hEfl, hEfr, hEsl, hEsr⟩ :=
      D.recut_sides_of_left_eq_left_of_mem_cIoo hcom hcol hr hs_empty
    have hrec := ratio_recut S T D hone hr hs_empty
    have hE₁ : ratio S T (D.recut hone hr hs_empty).first
        (D.isRecut_recut hone hr hs_empty).isEmpty_first = 1 :=
      ratio_eq_one_of_left_lt_right hadj 0 _ _
        (by rw [hEfl, hEfr]; dsimp only [D]; rw [hs_right, ha'val]; omega)
        (by rw [hEfl, hEfr]; dsimp only [D]; rw [hs_right, ha'val]; omega)
    have hE₂ : ratio S T (D.recut hone hr hs_empty).second
        (D.isRecut_recut hone hr hs_empty).isEmpty_second = 1 :=
      ratio_eq_one_of_left_lt_right hadj d _ _
        (by rw [hEsl, hEsr]; dsimp only [D]; rw [hs_right, ha'val]; omega)
        (by rw [hEsl, hEsr]; dsimp only [D]; rw [hs_right, ha'val]; omega)
    rw [hE₁, hE₂, one_mul] at hrec
    dsimp only [D] at hrec
    rw [hs_ratio, mul_one] at hrec
    exact hrec.symm

/-! ### Step 3: Wrapping rectangles by induction on the row interior -/

private theorem ratio_eq_one_of_nonwrapping {n : ℕ} {S T : GridSignAssignment n}
    (hnonwrap : ∀ {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      (r.left : ℕ) < r.right → ratio S T r hr = 1) :
    ∀ (m : ℕ) {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      (Grid.cIoo r.bottom r.top).card = m → ratio S T r hr = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro x y r hr hm
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne r.left_ne_right) with hlt | hgt
    · exact hnonwrap r hr hlt
    · by_cases hempty : Grid.cIoo r.bottom r.top = ∅
      · -- No grid point lies in the row interior, so the horizontal return rectangle is empty
        -- and non-wrapping.
        have hswap : x = y.swapColumns r.right r.left :=
          r.source_eq_swapColumns.trans (GridState.swapColumns_comm r.left r.right y)
        let s : GridRectangleBetween y x :=
          GridRectangleBetween.ofSwapColumns y x r.right r.left r.left_ne_right.symm hswap
        have hs_left : s.left = r.right := GridRectangleBetween.ofSwapColumns_left _ _ _ _ _ _
        have hs_right : s.right = r.left := GridRectangleBetween.ofSwapColumns_right _ _ _ _ _ _
        have hs_bot : s.bottom = r.bottom := by
          rw [GridRectangleBetween.ofSwapColumns_bottom, r.map_right, r.bottom_def]
        have hs_top : s.top = r.top := by
          rw [GridRectangleBetween.ofSwapColumns_top, r.map_left, r.top_def]
        have hs_empty : s.IsEmpty := by
          rw [s.isEmpty_iff_forall_notMem_cIoo]
          intro k _
          rw [hs_bot, hs_top, hempty]
          exact Finset.notMem_empty _
        have hs_ratio : ratio S T s hs_empty = 1 :=
          hnonwrap s hs_empty (by rw [hs_left, hs_right]; exact hgt)
        have hann := ratio_mul_ratio_eq_one_of_left_eq_right S T r s hr hs_empty hs_left
        rw [hs_ratio, mul_one] at hann
        exact hann
      · -- Choose the rightmost column `c` whose row lies in `cIoo r.bottom r.top`.
        obtain ⟨row₀, hrow₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        let cols : Finset (Fin n) :=
          Finset.univ.filter fun c => x c ∈ Grid.cIoo r.bottom r.top
        have hcols : cols.Nonempty := by
          refine ⟨x.toPerm.symm row₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          simpa using hrow₀
        obtain ⟨c, hc_mem, hc_max⟩ := Finset.exists_max_image cols (fun c => (c : ℕ)) hcols
        have hcrow : x c ∈ Grid.cIoo r.bottom r.top := (Finset.mem_filter.mp hc_mem).2
        have hcl : c ≠ r.left := fun h => by
          simp [h, r.bottom_def] at hcrow
        have hcr : c ≠ r.right := fun h => by
          simp [h, r.top_def] at hcrow
        have hc_not_in : c ∉ Grid.cIoo r.left r.right := fun hc =>
          (r.isEmpty_iff_forall_notMem_cIoo.mp hr c hc) hcrow
        have hc_in_swap : c ∈ Grid.cIoo r.right r.left := by
          rcases (Grid.mem_cIoo_or_mem_cIoo_swap_iff r.left_ne_right).mpr ⟨hcl, hcr⟩ with h | h
          · exact absurd h hc_not_in
          · exact h
        have hrc : (r.right : ℕ) < c ∧ (c : ℕ) < r.left :=
          (Grid.mem_cIoo_of_val_lt hgt).mp hc_in_swap
        let s : GridRectangleBetween y (y.swapColumns c r.left) :=
          GridRectangleBetween.ofSwapColumns y (y.swapColumns c r.left) c r.left hcl rfl
        have hs_left : s.left = c := GridRectangleBetween.ofSwapColumns_left _ _ _ _ _ _
        have hs_right : s.right = r.left := GridRectangleBetween.ofSwapColumns_right _ _ _ _ _ _
        have hs_bot : s.bottom = x c := by
          rw [GridRectangleBetween.ofSwapColumns_bottom, r.map_of_ne c hcl hcr]
        have hs_top : s.top = r.top := by
          rw [GridRectangleBetween.ofSwapColumns_top, r.map_left, r.top_def]
        have hs_empty : s.IsEmpty := by
          rw [s.isEmpty_iff_forall_notMem_cIoo]
          intro k hk hrowk
          rw [hs_left, hs_right, Grid.mem_cIoo_of_val_lt hrc.2] at hk
          have hkl : k ≠ r.left := fun h => by subst h; omega
          have hkr : k ≠ r.right := fun h => by subst h; omega
          rw [r.map_of_ne k hkl hkr, hs_bot, hs_top] at hrowk
          have hkcols : k ∈ cols := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, Grid.cIoo_subset_cIoo_left_of_mem_cIoo hcrow hrowk⟩
          have hle := hc_max k hkcols
          omega
        have hs_ratio : ratio S T s hs_empty = 1 :=
          hnonwrap s hs_empty (by rw [hs_left, hs_right]; exact hrc.2)
        let D : GridRectangleDecomposition x (y.swapColumns c r.left) := ⟨y, r, s⟩
        have hcom : D.first.left = D.second.right := hs_right.symm
        have hone := D.hasOneCommonSide_of_left_eq_right hcom
          (by dsimp only [D]; rw [hs_left]; exact hcr.symm)
        have hdata := D.isRecutOfLeftEqRight_recut hcom hone hr hs_empty
        obtain ⟨hEfb, hEsb⟩ := hdata.recut_sides
        have hsb_mem : D.second.bottom ∈ Grid.cIoo D.first.bottom D.first.top := by
          simpa [D, hs_bot] using hcrow
        have hbranch : (D.recut hone hr hs_empty).first.top = r.top ∧
            (D.recut hone hr hs_empty).second.top = x c := by
          rcases hdata.recut_branch with ⟨hbad, -⟩ | ⟨-, -, hft, hst⟩
          · exact absurd hbad (Grid.notMem_cIoo_of_mem_cIoo hsb_mem)
          · exact ⟨hft, hst.trans hs_bot⟩
        have hE₁lt : (Grid.cIoo (D.recut hone hr hs_empty).first.bottom
            (D.recut hone hr hs_empty).first.top).card < m := by
          rw [← hm, hEfb, hbranch.1]
          dsimp only [D]
          rw [hs_bot]
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨Grid.cIoo_subset_cIoo_left_of_mem_cIoo hcrow, fun heq =>
              Grid.left_notMem_cIoo (x c) r.top (heq ▸ hcrow)⟩)
        have hE₂lt : (Grid.cIoo (D.recut hone hr hs_empty).second.bottom
            (D.recut hone hr hs_empty).second.top).card < m := by
          rw [← hm, hEsb, hbranch.2]
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨Grid.cIoo_subset_cIoo_right_of_mem_cIoo hcrow, fun heq =>
              Grid.right_notMem_cIoo r.bottom (x c) (heq ▸ hcrow)⟩)
        have hrec := ratio_recut S T D hone hr hs_empty
        rw [ih _ hE₁lt _ _ rfl, ih _ hE₂lt _ _ rfl, one_mul] at hrec
        dsimp only [D] at hrec
        rw [hs_ratio, mul_one] at hrec
        exact hrec.symm

/-! ### Uniqueness up to gauge -/

/-- **Uniqueness of grid sign assignments up to gauge.** Any two sign assignments for grid states
of size `n` are related by a gauge transform. -/
theorem exists_gauge_eq {n : ℕ} (S T : GridSignAssignment n) :
    ∃ f : GridState n → ℤˣ, T = S.gauge f := by
  obtain ⟨f, hf⟩ := (permCoxeterSystem n).exists_coboundary
    (adjCocycle_inv S T) (adjCocycle_braid S T)
  refine ⟨fun x => f x.toPerm, ?_⟩
  have hadj : ∀ σ i, adjCocycle (S.gauge fun x => f x.toPerm) T σ i = 1 := fun σ i => by
    unfold adjCocycle ratio
    rw [gauge_sign]
    have hstep := hf σ i
    rw [Int.units_inv_eq_self] at hstep
    unfold adjCocycle ratio at hstep
    calc f σ * f (σ * (permCoxeterSystem n).simple i) *
            S.sign (adjRect σ i) (adjRect_isEmpty σ i) *
            T.sign (adjRect σ i) (adjRect_isEmpty σ i)
        = (f σ * f (σ * (permCoxeterSystem n).simple i)) *
            (S.sign (adjRect σ i) (adjRect_isEmpty σ i) *
              T.sign (adjRect σ i) (adjRect_isEmpty σ i)) := by ac_rfl
      _ = (f σ * f (σ * (permCoxeterSystem n).simple i)) *
            (f σ * f (σ * (permCoxeterSystem n).simple i)) := by rw [← hstep]
      _ = 1 := Int.units_mul_self _
  have hnonwrap : ∀ {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      (r.left : ℕ) < r.right → ratio (S.gauge fun x => f x.toPerm) T r hr = 1 :=
    fun r hr hlt =>
      ratio_eq_one_of_left_lt_right hadj ((r.right : ℕ) - r.left - 1) r hr hlt (by omega)
  refine GridSignAssignment.ext fun x y r hr => ?_
  exact ((ratio_eq_one_iff hr).mp (ratio_eq_one_of_nonwrapping hnonwrap _ r hr rfl)).symm

/-- Two gauges produce the same sign assignment if and only if they differ by a global sign. -/
theorem gauge_eq_gauge_iff {n : ℕ} (S : GridSignAssignment n) (f g : GridState n → ℤˣ) :
    S.gauge f = S.gauge g ↔ ∃ c : ℤˣ, ∀ x, g x = c * f x := by
  constructor
  · intro h
    have hstep : ∀ σ i, (f ⟨σ⟩)⁻¹ * f ⟨σ * (permCoxeterSystem n).simple i⟩ =
        (g ⟨σ⟩)⁻¹ * g ⟨σ * (permCoxeterSystem n).simple i⟩ := fun σ i => by
      have heq : (S.gauge f).sign (adjRect σ i) (adjRect_isEmpty σ i) =
          (S.gauge g).sign (adjRect σ i) (adjRect_isEmpty σ i) := by rw [h]
      simp only [gauge_sign] at heq
      rw [Int.units_inv_eq_self, Int.units_inv_eq_self]
      exact mul_right_cancel heq
    refine ⟨g ⟨1⟩ * (f ⟨1⟩)⁻¹, fun x => ?_⟩
    exact (permCoxeterSystem n).eq_mul_of_inv_mul_eq
      (f := fun σ => f ⟨σ⟩) (g := fun σ => g ⟨σ⟩) hstep x.toPerm
  · rintro ⟨c, hc⟩
    refine GridSignAssignment.ext fun x y r hr => ?_
    simp only [gauge_sign, hc]
    calc f x * f y * S.sign r hr
        = (c * c) * (f x * f y * S.sign r hr) := by rw [Int.units_mul_self, one_mul]
      _ = c * f x * (c * f y) * S.sign r hr := by ac_rfl

/-- Between any two sign assignments there is a unique gauge transform normalized to `1` at a
chosen base grid state `x₀`. -/
theorem existsUnique_gauge_eq {n : ℕ} (S T : GridSignAssignment n) (x₀ : GridState n) :
    ∃! f : GridState n → ℤˣ, f x₀ = 1 ∧ T = S.gauge f := by
  obtain ⟨f, rfl⟩ := S.exists_gauge_eq T
  refine ⟨fun x => f x₀ * f x, ⟨Int.units_mul_self (f x₀), ?_⟩, ?_⟩
  · exact (S.gauge_eq_gauge_iff f _).mpr ⟨f x₀, fun _ => rfl⟩
  · rintro g ⟨hg0, hge⟩
    obtain ⟨c, hc⟩ := (S.gauge_eq_gauge_iff f g).mp hge
    have hc0 : c = f x₀ := by
      have h0 := hc x₀
      rw [hg0] at h0
      have hmul := congrArg (· * f x₀) h0.symm
      simpa [mul_assoc, Int.units_mul_self] using hmul
    funext x
    rw [hc x, hc0]

end GridSignAssignment

namespace GridDiagram

/-- Any two sign assignments induce isomorphic signed unblocked grid complexes, conjugated by a
diagonal sign change `Finsupp.signEquiv` on grid states. -/
theorem exists_signEquiv_signedUnblockedDifferential {n : ℕ} (G : GridDiagram n)
    (S T : GridSignAssignment n) (R : Type*) [CommRing R] :
    ∃ f : GridState n → ℤˣ,
      G.signedUnblockedDifferential T R =
        (Finsupp.signEquiv (MvPolynomial (Fin n) R) f).toLinearMap ∘ₗ
          G.signedUnblockedDifferential S R ∘ₗ
            (Finsupp.signEquiv (MvPolynomial (Fin n) R) f).toLinearMap := by
  obtain ⟨f, rfl⟩ := S.exists_gauge_eq T
  exact ⟨f, G.signedUnblockedDifferential_gauge S R f⟩

end GridDiagram

end TauCeti
