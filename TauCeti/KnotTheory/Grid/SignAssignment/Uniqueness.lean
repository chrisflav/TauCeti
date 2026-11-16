/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SignAssignment.Differential
import TauCeti.GroupTheory.Coxeter.Cocycle
import TauCeti.GroupTheory.Perm.Coxeter
import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Geometry
import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Empty

/-!
# Uniqueness of grid sign assignments up to gauge

Any two grid sign assignments `S, T : TauCeti.GridSignAssignment n` are related by a gauge
transform `S.gauge f = T`, where `f : GridState n → ℤˣ` is unique up to multiplying by a global
sign `c : ℤˣ`. Consequently, the signed unblocked grid complexes of any two sign assignments on
the same grid diagram are canonically isomorphic via the diagonal sign change `Finsupp.signEquiv`.

The proof follows Manolescu--Ozsváth--Szabó--Thurston and Ozsváth--Stipsicz--Szabó:

1. **Width reduction.** Whenever `S` and `T` agree on all empty width-1 rectangles whose initial
   column lies in a set `C : Finset (Fin n)`, strong induction on the width `(Grid.cIco r.left
   r.right).card` using same-initial-side recuts shows that `S` and `T` agree on every empty
   rectangle whose covered columns lie in `C`.
2. **Wrap-around elimination.** Applying width reduction to all non-wrapping columns `C = univ \
   {last}` covers every empty rectangle whose column interval avoids the last column. Strong
   induction on the height `(Grid.cIco r.bottom r.top).card` using mixed-side recuts and the
   horizontal annulus rule then forces `S` and `T` to agree on the wrap-around width-1 rectangles
   from `last` to `0` as well, hence on all empty rectangles.
3. **Coxeter `1`-cocycle trivialization.** On the adjacent-transposition edges of the type-`A`
   Coxeter system `TauCeti.permCoxeterSystem n`, the ratio `S(r) * T(r)` defines a `1`-cocycle:
   backtracking cancels by the vertical annulus rule, commuting edges commute by the square rule on
   disjoint sides, and length-3 braid paths agree by combining mixed-side recuts with the vertical
   annulus rule. Applying `CoxeterSystem.existsUnique_mul_eq_of_cocycle` produces a gauge `f` so
   that `S.gauge f` and `T` agree on every non-wrapping width-1 rectangle, hence coincide.

## Main results

* `TauCeti.GridSignAssignment.exists_gauge_eq`: any two sign assignments are gauge equivalent.
* `TauCeti.GridSignAssignment.gauge_eq_self_iff`: a gauge fixes a sign assignment if and only if
  it is constant.
* `TauCeti.GridSignAssignment.gauge_eq_gauge_iff`: two gauges produce the same transform if and
  only if they differ by a global sign.
* `TauCeti.GridDiagram.exists_signEquiv_signedUnblockedDifferential`: the signed unblocked
  differentials for any two sign assignments are conjugate by a diagonal sign automorphism of
  `GC⁻`.

## References

* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Theorem 4.2 (arXiv:math/0610559).
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 15.2.
-/

public section

namespace TauCeti

open TauCeti.BraidGroup

namespace GridSignAssignment

variable {n : ℕ}

/-! ### Elementary helpers on `ℤˣ`, rectangles, and sign ratios -/

private theorem units_mul_eq_one_iff_eq {a b : ℤˣ} : a * b = 1 ↔ a = b :=
  mul_eq_one_iff_eq_inv.trans (by rw [Int.units_inv_eq_self])

private theorem isEmpty_of_top_eq_finRotate {x y : GridState n} (r : GridRectangleBetween x y)
    (h : r.top = finRotate n r.bottom) : r.IsEmpty :=
  r.isEmpty_transpose.mp (r.transpose.isEmpty_of_right_eq_finRotate h)

private theorem card_cIco_finRotate_lt {a b : Fin n} (hab : a ≠ b) (hrot : b ≠ finRotate n a) :
    (Grid.cIco (finRotate n a) b).card < (Grid.cIco a b).card := by
  have hmem : finRotate n a ∈ Grid.cIoo a b :=
    Grid.mem_cIoo_cyclic_right (Grid.mem_cIoo_finRotate_left_iff.mpr ⟨hab.symm, hrot⟩)
  have hcard := congrArg Finset.card (Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hmem)
  rw [Finset.card_union_of_disjoint (Grid.disjoint_cIco_cIco_of_mem_cIoo hmem)] at hcard
  have hpos : 0 < (Grid.cIco a (finRotate n a)).card :=
    Finset.card_pos.mpr ⟨a, Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hmem).symm⟩
  omega

/-- The pointwise ratio `S(r) * T(r) ∈ ℤˣ` of two sign assignments on an empty rectangle. -/
private def signRatio (S T : GridSignAssignment n) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) : ℤˣ :=
  S.sign r hr * T.sign r hr

private theorem signRatio_eq_one_iff (S T : GridSignAssignment n) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) :
    signRatio S T r hr = 1 ↔ S.sign r hr = T.sign r hr :=
  units_mul_eq_one_iff_eq

private theorem signRatio_mul_eq_signRatio_mul (S T : GridSignAssignment n)
    {x z : GridState n} (D E : GridRectangleDecomposition x z)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hE₁ : E.first.IsEmpty) (hE₂ : E.second.IsEmpty)
    (hne : E ≠ D)
    (hdom : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val) :
    signRatio S T E.first hE₁ * signRatio S T E.second hE₂ =
      signRatio S T D.first hD₁ * signRatio S T D.second hD₂ := by
  have hS := S.sign_mul_sign_eq_neg D E hD₁ hD₂ hE₁ hE₂ hne hdom
  have hT := T.sign_mul_sign_eq_neg D E hD₁ hD₂ hE₁ hE₂ hne hdom
  calc signRatio S T E.first hE₁ * signRatio S T E.second hE₂
      = (S.sign E.first hE₁ * S.sign E.second hE₂) *
          (T.sign E.first hE₁ * T.sign E.second hE₂) := by
          simp only [signRatio]; ac_rfl
    _ = (-(S.sign D.first hD₁ * S.sign D.second hD₂)) *
          (-(T.sign D.first hD₁ * T.sign D.second hD₂)) := by rw [hS, hT]
    _ = (S.sign D.first hD₁ * S.sign D.second hD₂) *
          (T.sign D.first hD₁ * T.sign D.second hD₂) := neg_mul_neg _ _
    _ = signRatio S T D.first hD₁ * signRatio S T D.second hD₂ := by
          simp only [signRatio]; ac_rfl

private theorem signRatio_recut (S T : GridSignAssignment n) {x z : GridState n}
    (D : GridRectangleDecomposition x z) (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) :
    signRatio S T (D.recut hone hD₁ hD₂).first
          (D.isRecut_recut hone hD₁ hD₂).isEmpty_first *
        signRatio S T (D.recut hone hD₁ hD₂).second
          (D.isRecut_recut hone hD₁ hD₂).isEmpty_second =
      signRatio S T D.first hD₁ * signRatio S T D.second hD₂ :=
  signRatio_mul_eq_signRatio_mul S T D (D.recut hone hD₁ hD₂) hD₁ hD₂
    (D.isRecut_recut hone hD₁ hD₂).isEmpty_first
    (D.isRecut_recut hone hD₁ hD₂).isEmpty_second
    (D.recut_ne hone hD₁ hD₂) (D.isRecut_recut hone hD₁ hD₂).isRepartition.val_add_val_eq

private theorem signRatio_commute (S T : GridSignAssignment n) {x z : GridState n}
    (D : GridRectangleDecomposition x z) (hdisj : D.HasDisjointSides)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) :
    signRatio S T (D.commute hdisj).first (D.isEmpty_commute_first hdisj hD₁ hD₂) *
        signRatio S T (D.commute hdisj).second (D.isEmpty_commute_second hdisj hD₁ hD₂) =
      signRatio S T D.first hD₁ * signRatio S T D.second hD₂ := by
  refine signRatio_mul_eq_signRatio_mul S T D (D.commute hdisj) hD₁ hD₂
    (D.isEmpty_commute_first hdisj hD₁ hD₂) (D.isEmpty_commute_second hdisj hD₁ hD₂)
    (D.commute_ne hdisj) ?_
  rw [D.commute_first_toGridRectangle hdisj, D.commute_second_toGridRectangle hdisj, add_comm]

private theorem signRatio_mul_eq_one_of_left_eq_left (S T : GridSignAssignment n)
    {x y : GridState n} (r : GridRectangleBetween x y) (s : GridRectangleBetween y x)
    (hr : r.IsEmpty) (hs : s.IsEmpty) (hleft : s.left = r.left) :
    signRatio S T r hr * signRatio S T s hs = 1 := by
  calc signRatio S T r hr * signRatio S T s hs
      = (S.sign r hr * S.sign s hs) * (T.sign r hr * T.sign s hs) := by
          simp only [signRatio]; ac_rfl
    _ = (-1) * (-1) := by
          rw [S.sign_mul_sign_eq_neg_one_of_left_eq_left r s hr hs hleft,
            T.sign_mul_sign_eq_neg_one_of_left_eq_left r s hr hs hleft]
    _ = 1 := (neg_mul_neg 1 1).trans (one_mul 1)

private theorem signRatio_mul_eq_one_of_left_eq_right (S T : GridSignAssignment n)
    {x y : GridState n} (r : GridRectangleBetween x y) (s : GridRectangleBetween y x)
    (hr : r.IsEmpty) (hs : s.IsEmpty) (hleft : s.left = r.right) :
    signRatio S T r hr * signRatio S T s hs = 1 := by
  calc signRatio S T r hr * signRatio S T s hs
      = (S.sign r hr * S.sign s hs) * (T.sign r hr * T.sign s hs) := by
          simp only [signRatio]; ac_rfl
    _ = 1 * 1 := by
          rw [S.sign_mul_sign_eq_one_of_left_eq_right r s hr hs hleft,
            T.sign_mul_sign_eq_one_of_left_eq_right r s hr hs hleft]
    _ = 1 := one_mul 1

private theorem signRatio_congr {S T : GridSignAssignment n} {x y x' y' : GridState n}
    (hx : x = x') (hy : y = y') {r : GridRectangleBetween x y} {r' : GridRectangleBetween x' y'}
    (hr : r.IsEmpty) (hr' : r'.IsEmpty) (hleft : r.left = r'.left) :
    signRatio S T r hr = signRatio S T r' hr' := by
  subst hx hy
  have hEq : r = r' := GridRectangleBetween.left_injective hleft
  subst hEq
  rfl

/-! ### Width reduction and wrap-around elimination -/

/-- If two sign assignments agree on all empty width-1 rectangles starting in `C`, then they agree
on every empty rectangle whose covered columns lie in `C`. -/
private theorem sign_eq_of_cIco_subset (S T : GridSignAssignment n) (C : Finset (Fin n))
    (hwidth : ∀ ⦃x y : GridState n⦄ (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      r.right = finRotate n r.left → r.left ∈ C → S.sign r hr = T.sign r hr) :
    ∀ ⦃x y : GridState n⦄ (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      Grid.cIco r.left r.right ⊆ C → S.sign r hr = T.sign r hr := by
  intro x y r hr hsub
  suffices ∀ k : ℕ, ∀ ⦃x y : GridState n⦄ (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      (Grid.cIco r.left r.right).card = k → Grid.cIco r.left r.right ⊆ C →
      S.sign r hr = T.sign r hr from this _ r hr rfl hsub
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro x y r hr hk hsub
    have hleft_mem : r.left ∈ C := hsub (Grid.left_mem_cIco r.left_ne_right)
    by_cases hrot : r.right = finRotate n r.left
    · exact hwidth r hr hrot hleft_mem
    · set c := finRotate n r.left
      have hc_mem : c ∈ Grid.cIoo r.left r.right :=
        Grid.mem_cIoo_cyclic_right
          (Grid.mem_cIoo_finRotate_left_iff.mpr ⟨r.left_ne_right.symm, hrot⟩)
      have hlc : r.left ≠ c := (Grid.ne_left_of_mem_cIoo hc_mem).symm
      let r₂ := GridRectangleBetween.ofSwapColumns y (y.swapColumns r.left c) r.left c hlc rfl
      have hr₂ : r₂.IsEmpty := r₂.isEmpty_of_right_eq_finRotate (by simp [r₂, c])
      let D : GridRectangleDecomposition x (y.swapColumns r.left c) := ⟨y, r, r₂⟩
      have hcommon : D.first.left = D.second.left := by simp [D, r₂]
      have hcol : D.second.right ∈ Grid.cIoo D.first.left D.first.right := by
        simpa [D, r₂] using hc_mem
      let hone := D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hcol
      let E := D.recut hone hr hr₂
      have hrec := D.isRecut_recut hone hr hr₂
      obtain ⟨hEfl, hEfr, hEsl, hEsr⟩ :=
        D.recut_sides_of_left_eq_left_of_mem_cIoo hcommon hcol hr hr₂
      have hD₂ : signRatio S T D.second hr₂ = 1 :=
        (signRatio_eq_one_iff S T _ _).mpr
          (hwidth r₂ hr₂ (by simp [r₂, c]) (by simpa [r₂] using hleft_mem))
      have hE₁ : signRatio S T E.first hrec.isEmpty_first = 1 :=
        (signRatio_eq_one_iff S T _ _).mpr
          (hwidth E.first hrec.isEmpty_first (by simp [E, hEfl, hEfr, D, r₂, c])
            (hEfl.symm ▸ hleft_mem))
      have hE₂_sub : Grid.cIco E.second.left E.second.right ⊆ C := by
        rw [hEsl, hEsr]
        simpa only [D, r₂, GridRectangleBetween.ofSwapColumns_right] using
          (Finset.subset_union_right.trans
            (Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hc_mem).subset).trans hsub
      have hE₂_lt : (Grid.cIco E.second.left E.second.right).card < k := by
        rw [hEsl, hEsr, ← hk]
        simpa only [D, r₂, GridRectangleBetween.ofSwapColumns_right] using
          card_cIco_finRotate_lt r.left_ne_right hrot
      have hE₂ : signRatio S T E.second hrec.isEmpty_second = 1 :=
        (signRatio_eq_one_iff S T _ _).mpr
          (ih _ hE₂_lt E.second hrec.isEmpty_second rfl hE₂_sub)
      have hsq := signRatio_recut S T D hone hr hr₂
      rw [hE₁, hE₂, hD₂, mul_one, mul_one] at hsq
      exact (signRatio_eq_one_iff S T r hr).mp hsq.symm

/-- If `S` and `T` agree on all empty rectangles avoiding column `lastCol`, then they also agree on
every empty height-1 rectangle starting at `lastCol` (by the horizontal annulus rule). -/
private theorem sign_eq_of_top_eq_finRotate_of_nonwrap (S T : GridSignAssignment n)
    (lastCol : Fin n)
    (hnonwrap : ∀ ⦃x y : GridState n⦄ (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      lastCol ∉ Grid.cIco r.left r.right → S.sign r hr = T.sign r hr)
    {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty)
    (hleft : r.left = lastCol) (htop : r.top = finRotate n r.bottom) :
    S.sign r hr = T.sign r hr := by
  let s := GridRectangleBetween.ofSwapColumns y x r.right r.left r.left_ne_right.symm
    (r.source_eq_swapColumns.trans (y.swapColumns_comm _ _))
  have hs_left : s.left = r.right := GridRectangleBetween.ofSwapColumns_left _ _ _ _ _ _
  have hs : s.IsEmpty :=
    ((r.isEmpty_and_isEmpty_iff_top_eq_finRotate_of_left_eq_right s hs_left).mpr htop).2
  have hs_not : lastCol ∉ Grid.cIco s.left s.right := by
    simp only [s, GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      hleft]
    exact Grid.right_notMem_cIco _ _
  have hs_eq : signRatio S T s hs = 1 :=
    (signRatio_eq_one_iff S T s hs).mpr (hnonwrap s hs hs_not)
  have hann := signRatio_mul_eq_one_of_left_eq_right S T r s hr hs hs_left
  rw [hs_eq, mul_one] at hann
  exact (signRatio_eq_one_iff S T r hr).mp hann

/-- Height induction step for width-1 rectangles starting at an omitted column `lastCol`. -/
private theorem sign_eq_wrap_of_nonwrap (S T : GridSignAssignment n) (lastCol : Fin n)
    (hnonwrap : ∀ ⦃x y : GridState n⦄ (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      lastCol ∉ Grid.cIco r.left r.right → S.sign r hr = T.sign r hr) :
    ∀ ⦃x y : GridState n⦄ (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      r.left = lastCol → r.right = finRotate n lastCol →
      S.sign r hr = T.sign r hr := by
  suffices ∀ h : ℕ, ∀ ⦃x y : GridState n⦄ (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      r.left = lastCol → r.right = finRotate n lastCol →
      (Grid.cIco r.bottom r.top).card = h → S.sign r hr = T.sign r hr from
    fun _ _ r hr hl hr' => this _ r hr hl hr' rfl
  intro h
  induction h using Nat.strong_induction_on with
  | ind h ih =>
    intro x y r hr hleft hright hcard
    by_cases htop : r.top = finRotate n r.bottom
    · exact sign_eq_of_top_eq_finRotate_of_nonwrap S T lastCol hnonwrap r hr hleft htop
    · set row := finRotate n r.bottom
      have hrow_mem : row ∈ Grid.cIoo r.bottom r.top :=
        Grid.mem_cIoo_cyclic_right
          (Grid.mem_cIoo_finRotate_left_iff.mpr ⟨r.bottom_ne_top.symm, htop⟩)
      let c : Fin n := x.toPerm.symm row
      have hxc : x c = row := Equiv.apply_symm_apply x.toPerm row
      have hcl : c ≠ r.left := fun heq =>
        Grid.ne_left_of_mem_cIoo hrow_mem (hxc.symm.trans (by rw [heq]; rfl))
      have hcr : c ≠ r.right := fun heq =>
        Grid.ne_right_of_mem_cIoo hrow_mem (hxc.symm.trans (by rw [heq]; rfl))
      let r₂ := GridRectangleBetween.ofSwapColumns y (y.swapColumns r.right c) r.right c hcr.symm
        rfl
      have hr₂_bot : r₂.bottom = r.bottom := by
        rw [GridRectangleBetween.ofSwapColumns_bottom]
        exact r.map_right
      have hr₂_top : r₂.top = row := by
        rw [GridRectangleBetween.ofSwapColumns_top]
        exact (r.map_of_ne c hcl hcr).trans hxc
      have hr₂ : r₂.IsEmpty := isEmpty_of_top_eq_finRotate r₂ (by rw [hr₂_top, hr₂_bot])
      let D : GridRectangleDecomposition x (y.swapColumns r.right c) := ⟨y, r, r₂⟩
      have hrl : D.first.right = D.second.left := by simp [D, r₂]
      have hone : D.HasOneCommonSide :=
        D.hasOneCommonSide_of_right_eq_left hrl (by simpa [D, r₂] using hcl.symm)
      let E := D.recut hone hr hr₂
      have hrec := D.isRecut_recut hone hr hr₂
      rcases D.recut_geometry_of_right_eq_left hrl hone hr hr₂ with ⟨hcontra, -⟩ |
          ⟨-, hEfl, -, hEsl, hEsr, hEfb, hEft, hEsb, hEst⟩
      · exfalso
        have hcontra' : r.top ∈ Grid.cIoo r.bottom (finRotate n r.bottom) := by
          simpa only [D, hr₂_top] using hcontra
        rw [Grid.cIoo_finRotate_eq_empty] at hcontra'
        exact Finset.notMem_empty _ hcontra'
      · have hD₂_not : lastCol ∉ Grid.cIco r₂.left r₂.right := by
          simp [r₂, hright]
        have hD₂ : signRatio S T D.second hr₂ = 1 :=
          (signRatio_eq_one_iff S T r₂ hr₂).mpr (hnonwrap r₂ hr₂ hD₂_not)
        have hE₁ : signRatio S T E.first hrec.isEmpty_first = 1 :=
          (signRatio_eq_one_iff S T E.first hrec.isEmpty_first).mpr
            (sign_eq_of_top_eq_finRotate_of_nonwrap S T lastCol hnonwrap E.first
              hrec.isEmpty_first (hEfl.trans hleft) (by rw [hEft, hEfb, hr₂_top]))
        have hE₂_lt : (Grid.cIco E.second.bottom E.second.top).card < h := by
          rw [hEsb, hEst, hr₂_top, ← hcard]
          exact card_cIco_finRotate_lt r.bottom_ne_top htop
        have hE₂ : signRatio S T E.second hrec.isEmpty_second = 1 :=
          (signRatio_eq_one_iff S T E.second hrec.isEmpty_second).mpr
            (ih _ hE₂_lt E.second hrec.isEmpty_second (hEsl.trans hleft) (hEsr.trans hright) rfl)
        have hsq := signRatio_recut S T D hone hr hr₂
        rw [hE₁, hE₂, hD₂, mul_one, mul_one] at hsq
        exact (signRatio_eq_one_iff S T r hr).mp hsq.symm

/-- If two sign assignments agree on all empty width-1 rectangles whose initial column is not a
fixed column `lastCol`, then they are equal. -/
private theorem eq_of_width_one_ne (S T : GridSignAssignment n) (lastCol : Fin n)
    (hwidth : ∀ ⦃x y : GridState n⦄ (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      r.right = finRotate n r.left → r.left ≠ lastCol → S.sign r hr = T.sign r hr) :
    S = T := by
  have hnonwrap : ∀ ⦃x y : GridState n⦄ (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      lastCol ∉ Grid.cIco r.left r.right → S.sign r hr = T.sign r hr := by
    intro x y r hr hnot
    refine sign_eq_of_cIco_subset S T (Finset.univ.erase lastCol)
      (fun _ _ r' hr' hrot hmem => hwidth r' hr' hrot (Finset.mem_erase.mp hmem).1) r hr ?_
    intro c hc
    exact Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hc), Finset.mem_univ c⟩
  refine GridSignAssignment.ext fun x y r hr => ?_
  refine sign_eq_of_cIco_subset S T Finset.univ (fun _ _ r' hr' hrot _ => ?_) r hr
    (Finset.subset_univ _)
  by_cases hlast : r'.left = lastCol
  · exact sign_eq_wrap_of_nonwrap S T lastCol hnonwrap r' hr' hlast
      (hrot.trans (congrArg (finRotate n) hlast))
  · exact hwidth r' hr' hrot hlast

/-! ### The Coxeter `1`-cocycle on adjacent transpositions -/

private theorem finRotate_strand (i : Fin (n - 1)) :
    finRotate n (strand i) = strandSucc i := by
  have hi := i.isLt
  cases n with
  | zero => omega
  | succ m =>
    apply Fin.ext
    rw [coe_finRotate]
    have hne : strand (n := m + 1) i ≠ Fin.last m := fun h => by
      have hval := congrArg Fin.val h
      simp only [val_strand, Fin.val_last] at hval
      omega
    simp only [val_strandSucc, val_strand, hne, ↓reduceIte]

private theorem mk_mul_transposition_eq_swapColumns (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (⟨σ * transposition i⟩ : GridState n) =
      (⟨σ⟩ : GridState n).swapColumns (strand i) (strandSucc i) :=
  GridState.ext fun c => by
    rw [GridState.swapColumns_apply, transposition_eq_swap]
    rfl

/-- The canonical empty width-1 rectangle from `⟨σ⟩` to `⟨σ * transposition i⟩`. -/
private def adjRect (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    GridRectangleBetween ⟨σ⟩ ⟨σ * transposition i⟩ :=
  GridRectangleBetween.ofSwapColumns ⟨σ⟩ ⟨σ * transposition i⟩ (strand i) (strandSucc i)
    (strand_ne_strandSucc i) (mk_mul_transposition_eq_swapColumns σ i)

private theorem adjRect_left (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (adjRect σ i).left = strand i :=
  GridRectangleBetween.ofSwapColumns_left _ _ _ _ _ _

private theorem adjRect_right (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (adjRect σ i).right = strandSucc i :=
  GridRectangleBetween.ofSwapColumns_right _ _ _ _ _ _

private theorem adjRect_bottom (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (adjRect σ i).bottom = σ (strand i) :=
  GridRectangleBetween.ofSwapColumns_bottom _ _ _ _ _ _

private theorem adjRect_top (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (adjRect σ i).top = σ (strandSucc i) :=
  GridRectangleBetween.ofSwapColumns_top _ _ _ _ _ _

private theorem isEmpty_adjRect (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (adjRect σ i).IsEmpty :=
  (adjRect σ i).isEmpty_of_right_eq_finRotate <| by
    rw [adjRect_left, adjRect_right, finRotate_strand]

/-- The `1`-cocycle on `permCoxeterSystem n` assigning to the edge `σ ↦ σ * sᵢ` the sign ratio
of `S` and `T` on the corresponding width-1 rectangle. -/
private def adjCocycle (S T : GridSignAssignment n) (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    ℤˣ :=
  signRatio S T (adjRect σ i) (isEmpty_adjRect σ i)

private theorem signRatio_mul_adjCocycle_eq_one (S T : GridSignAssignment n)
    {x y : GridState n} {r : GridRectangleBetween x y} (hr : r.IsEmpty)
    {σ : Equiv.Perm (Fin n)} (i : Fin (n - 1))
    (hy : y = ⟨σ⟩) (hx : x = ⟨σ * transposition i⟩) (hleft : r.left = strand i) :
    signRatio S T r hr * adjCocycle S T σ i = 1 := by
  subst hx hy
  exact signRatio_mul_eq_one_of_left_eq_left S T r (adjRect σ i) hr (isEmpty_adjRect σ i)
    ((adjRect_left σ i).trans hleft.symm)

private theorem adjCocycle_mul_self (S T : GridSignAssignment n) (σ : Equiv.Perm (Fin n))
    (i : Fin (n - 1)) :
    adjCocycle S T σ i * adjCocycle S T (σ * transposition i) i = 1 :=
  signRatio_mul_adjCocycle_eq_one S T (isEmpty_adjRect σ i) i rfl
    (GridState.ext fun c => by simp [mul_transposition_mul_self]) (adjRect_left σ i)

private theorem adjCocycle_eq_of_mul_transposition (S T : GridSignAssignment n)
    (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    adjCocycle S T (σ * transposition i) i = adjCocycle S T σ i :=
  (units_mul_eq_one_iff_eq.mp (adjCocycle_mul_self S T σ i)).symm

private theorem adjCocycle_braid_two (S T : GridSignAssignment n) (σ : Equiv.Perm (Fin n))
    {i j : Fin (n - 1)} (hfar : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    adjCocycle S T σ i * adjCocycle S T (σ * transposition i) j =
      adjCocycle S T σ j * adjCocycle S T (σ * transposition j) i := by
  let D : GridRectangleDecomposition ⟨σ⟩ ⟨σ * transposition i * transposition j⟩ :=
    ⟨⟨σ * transposition i⟩, adjRect σ i, adjRect (σ * transposition i) j⟩
  have hnodup := nodup_strand_strandSucc_strand_strandSucc hfar
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnodup
  have hdisj : D.HasDisjointSides := D.hasDisjointSides_iff.mpr <| by
    simp only [D, adjRect_left, adjRect_right]
    exact ⟨hnodup.1.2.1, hnodup.1.2.2, hnodup.2.1.1, hnodup.2.1.2⟩
  have h₁ := isEmpty_adjRect σ i
  have h₂ := isEmpty_adjRect (σ * transposition i) j
  have hsq := signRatio_commute S T D hdisj h₁ h₂
  let E := D.commute hdisj
  have hE_mid : E.middle = ⟨σ * transposition j⟩ := by
    rw [D.commute_middle hdisj]
    exact GridState.ext fun c => by
      simp [D, adjRect_left, adjRect_right, GridState.swapColumns_apply, transposition_eq_swap]
  have hE₁ : signRatio S T E.first (D.isEmpty_commute_first hdisj h₁ h₂) =
      adjCocycle S T σ j :=
    signRatio_congr rfl hE_mid _ _
      (((D.commute_first_left hdisj).trans (adjRect_left _ j)).trans (adjRect_left σ j).symm)
  have hE₂ : signRatio S T E.second (D.isEmpty_commute_second hdisj h₁ h₂) =
      adjCocycle S T (σ * transposition j) i :=
    signRatio_congr hE_mid
      (GridState.ext fun c => by
        simp [mul_assoc, transposition_mul_transposition_comm hfar])
      _ _ (((D.commute_second_left hdisj).trans (adjRect_left _ i)).trans
        (adjRect_left _ i).symm)
  rw [hE₁, hE₂] at hsq
  exact hsq.symm

private theorem transposition_braid_eq_swap {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j) :
    transposition i * transposition j * transposition i =
      Equiv.swap (strand i) (strandSucc j) := by
  have hji := strand_eq_strandSucc_of_succ hij
  have hac := strand_ne_strandSucc_of_succ hij
  have hbc : strandSucc i ≠ strandSucc j := by rw [← hji]; exact strand_ne_strandSucc j
  rw [transposition_eq_swap, transposition_eq_swap, hji,
    Equiv.swap_comm (strand i) (strandSucc i), Equiv.swap_comm (strandSucc i) (strandSucc j)]
  exact Equiv.swap_mul_swap_mul_swap hbc.symm hac.symm

private theorem adjCocycle_braid_right_of_notMem (S T : GridSignAssignment n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j)
    (hnot : σ (strandSucc i) ∉ Grid.cIoo (σ (strand i)) (σ (strandSucc j))) :
    ∃ (y : GridState n) (r : GridRectangleBetween ⟨σ⟩ y) (hr : r.IsEmpty),
      y = ⟨σ * Equiv.swap (strand i) (strandSucc j)⟩ ∧ r.left = strand i ∧
        adjCocycle S T σ i * adjCocycle S T (σ * transposition i) j *
          adjCocycle S T (σ * transposition i * transposition j) i = signRatio S T r hr := by
  set a := strand i
  set b := strandSucc i
  set c := strandSucc j
  have hji : strand j = b := strand_eq_strandSucc_of_succ hij
  have hac : a ≠ c := strand_ne_strandSucc_of_succ hij
  have hbc : b ≠ c := by rw [← hji]; exact strand_ne_strandSucc j
  have hw_eq : σ * transposition i * transposition j * transposition i = σ * Equiv.swap a c := by
    rw [mul_assoc σ, mul_assoc σ, transposition_braid_eq_swap hij]
  let D : GridRectangleDecomposition ⟨σ⟩ ⟨σ * transposition i * transposition j⟩ :=
    ⟨⟨σ * transposition i⟩, adjRect σ i, adjRect (σ * transposition i) j⟩
  have hrl : D.first.right = D.second.left := by rw [adjRect_right, adjRect_left, hji]
  have hone : D.HasOneCommonSide :=
    D.hasOneCommonSide_of_right_eq_left hrl (by rw [adjRect_left, adjRect_right]; exact hac)
  let E := D.recut hone (isEmpty_adjRect σ i) (isEmpty_adjRect (σ * transposition i) j)
  have hrec :=
    D.isRecut_recut hone (isEmpty_adjRect σ i) (isEmpty_adjRect (σ * transposition i) j)
  have htop : D.second.top = σ c := by
    rw [adjRect_top, Equiv.Perm.mul_apply, transposition_eq_swap,
      Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  have hgeom : E.first.left = a ∧ E.first.right = c ∧ E.second.left = a := by
    rcases D.recut_geometry_of_right_eq_left hrl hone (isEmpty_adjRect σ i)
        (isEmpty_adjRect (σ * transposition i) j) with ⟨hbad, -⟩ | ⟨-, h1, h2, h3, -⟩
    · exfalso
      rw [htop, adjRect_bottom, adjRect_top] at hbad
      exact hnot hbad
    · exact ⟨h1.trans (adjRect_left σ i), h2.trans (adjRect_right _ j),
        h3.trans (adjRect_left σ i)⟩
  have hmid : E.middle = ⟨σ * Equiv.swap a c⟩ := by
    rw [E.first.target_eq_swapColumns, hgeom.1, hgeom.2.1]
    exact GridState.ext fun u => by simp [GridState.swapColumns_apply]
  have hsq := signRatio_recut S T D hone (isEmpty_adjRect σ i)
    (isEmpty_adjRect (σ * transposition i) j)
  have hann := signRatio_mul_adjCocycle_eq_one S T hrec.isEmpty_second i rfl
    (by rw [hmid, hw_eq]) hgeom.2.2
  have hpath : adjCocycle S T σ i * adjCocycle S T (σ * transposition i) j *
      adjCocycle S T (σ * transposition i * transposition j) i =
      signRatio S T E.first hrec.isEmpty_first := by
    rw [adjCocycle, adjCocycle, ← hsq, mul_assoc, hann, mul_one]
  exact ⟨E.middle, E.first, hrec.isEmpty_first, hmid, hgeom.1, hpath⟩

private theorem adjCocycle_braid_left_of_notMem (S T : GridSignAssignment n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j)
    (hnot : σ (strandSucc i) ∉ Grid.cIoo (σ (strand i)) (σ (strandSucc j))) :
    ∃ (y : GridState n) (r : GridRectangleBetween ⟨σ⟩ y) (hr : r.IsEmpty),
      y = ⟨σ * Equiv.swap (strand i) (strandSucc j)⟩ ∧ r.left = strand i ∧
        adjCocycle S T σ j * adjCocycle S T (σ * transposition j) i *
          adjCocycle S T (σ * transposition j * transposition i) j = signRatio S T r hr := by
  set a := strand i
  set b := strandSucc i
  set c := strandSucc j
  have hji : strand j = b := strand_eq_strandSucc_of_succ hij
  have hac : a ≠ c := strand_ne_strandSucc_of_succ hij
  have hw_eq : σ * transposition j * transposition i * transposition j = σ * Equiv.swap a c := by
    rw [mul_assoc σ, mul_assoc σ, ← transposition_braid (Or.inl hij),
      transposition_braid_eq_swap hij]
  let D : GridRectangleDecomposition ⟨σ⟩ ⟨σ * transposition j * transposition i⟩ :=
    ⟨⟨σ * transposition j⟩, adjRect σ j, adjRect (σ * transposition j) i⟩
  have hlr : D.first.left = D.second.right := by rw [adjRect_left, adjRect_right, hji]
  have hone : D.HasOneCommonSide :=
    D.hasOneCommonSide_of_left_eq_right hlr (by rw [adjRect_right, adjRect_left]; exact hac.symm)
  let E := D.recut hone (isEmpty_adjRect σ j) (isEmpty_adjRect (σ * transposition j) i)
  have hrec :=
    D.isRecut_recut hone (isEmpty_adjRect σ j) (isEmpty_adjRect (σ * transposition j) i)
  have hbot : D.second.bottom = σ a := by
    rw [adjRect_bottom, Equiv.Perm.mul_apply, transposition_eq_swap, hji,
      Equiv.swap_apply_of_ne_of_ne (strand_ne_strandSucc i) hac]
  have hgeom : E.first.left = a ∧ E.first.right = c ∧ E.second.left = strand j := by
    rcases D.recut_geometry_of_left_eq_right hlr hone (isEmpty_adjRect σ j)
        (isEmpty_adjRect (σ * transposition j) i) with ⟨hbad, -⟩ | ⟨-, h1, h2, h3, -⟩
    · exfalso
      rw [hbot, adjRect_bottom, adjRect_top, hji] at hbad
      exact hnot hbad
    · exact ⟨h1.trans (adjRect_left _ i), h2.trans (adjRect_right σ j),
        h3.trans (adjRect_left σ j)⟩
  have hmid : E.middle = ⟨σ * Equiv.swap a c⟩ := by
    rw [E.first.target_eq_swapColumns, hgeom.1, hgeom.2.1]
    exact GridState.ext fun u => by simp [GridState.swapColumns_apply]
  have hsq := signRatio_recut S T D hone (isEmpty_adjRect σ j)
    (isEmpty_adjRect (σ * transposition j) i)
  have hann := signRatio_mul_adjCocycle_eq_one S T hrec.isEmpty_second j rfl
    (by rw [hmid, hw_eq]) hgeom.2.2
  have hpath : adjCocycle S T σ j * adjCocycle S T (σ * transposition j) i *
      adjCocycle S T (σ * transposition j * transposition i) j =
      signRatio S T E.first hrec.isEmpty_first := by
    rw [adjCocycle, adjCocycle, ← hsq, mul_assoc, hann, mul_one]
  exact ⟨E.middle, E.first, hrec.isEmpty_first, hmid, hgeom.1, hpath⟩

private theorem adjCocycle_braid_three_of_notMem (S T : GridSignAssignment n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j)
    (hnot : σ (strandSucc i) ∉ Grid.cIoo (σ (strand i)) (σ (strandSucc j))) :
    adjCocycle S T σ j * adjCocycle S T (σ * transposition j) i *
        adjCocycle S T (σ * transposition j * transposition i) j =
      adjCocycle S T σ i * adjCocycle S T (σ * transposition i) j *
        adjCocycle S T (σ * transposition i * transposition j) i := by
  obtain ⟨yL, rL, hrL, hL_mid, hL_left, hL_eq⟩ :=
    adjCocycle_braid_left_of_notMem S T σ hij hnot
  obtain ⟨yR, rR, hrR, hR_mid, hR_left, hR_eq⟩ :=
    adjCocycle_braid_right_of_notMem S T σ hij hnot
  rw [hL_eq, hR_eq]
  exact signRatio_congr rfl (hL_mid.trans hR_mid.symm) hrL hrR (hL_left.trans hR_left.symm)

private theorem adjCocycle_braid_three (S T : GridSignAssignment n) (σ : Equiv.Perm (Fin n))
    {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j) :
    adjCocycle S T σ j * adjCocycle S T (σ * transposition j) i *
        adjCocycle S T (σ * transposition j * transposition i) j =
      adjCocycle S T σ i * adjCocycle S T (σ * transposition i) j *
        adjCocycle S T (σ * transposition i * transposition j) i := by
  by_cases hmem : σ (strandSucc i) ∈ Grid.cIoo (σ (strand i)) (σ (strandSucc j))
  · set τ := σ * Equiv.swap (strand i) (strandSucc j)
    have hτ_eq₁ : τ = σ * transposition i * transposition j * transposition i := by
      simp only [τ, ← transposition_braid_eq_swap hij, mul_assoc]
    have hτ_eq₂ : τ = σ * transposition j * transposition i * transposition j := by
      rw [hτ_eq₁, mul_assoc σ, mul_assoc σ, transposition_braid (Or.inl hij),
        ← mul_assoc, ← mul_assoc]
    have hτ_not : τ (strandSucc i) ∉ Grid.cIoo (τ (strand i)) (τ (strandSucc j)) := by
      have hji := strand_eq_strandSucc_of_succ hij
      have hab := strand_ne_strandSucc i
      have hbc : strandSucc i ≠ strandSucc j := by rw [← hji]; exact strand_ne_strandSucc j
      have ha : τ (strand i) = σ (strandSucc j) := by simp [τ]
      have hb : τ (strandSucc i) = σ (strandSucc i) := by
        simp [τ, Equiv.swap_apply_of_ne_of_ne hab.symm hbc]
      have hc : τ (strandSucc j) = σ (strand i) := by simp [τ]
      rw [ha, hb, hc]
      exact fun h => Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hmem h
    have hτ := adjCocycle_braid_three_of_notMem S T τ hij hτ_not
    have h1 : adjCocycle S T τ j = adjCocycle S T (σ * transposition j * transposition i) j := by
      rw [hτ_eq₂, adjCocycle_eq_of_mul_transposition]
    have h2 : adjCocycle S T (τ * transposition j) i =
        adjCocycle S T (σ * transposition j) i := by
      rw [hτ_eq₂, mul_transposition_mul_self, adjCocycle_eq_of_mul_transposition]
    have h3 : adjCocycle S T (τ * transposition j * transposition i) j = adjCocycle S T σ j := by
      rw [hτ_eq₂, mul_transposition_mul_self, mul_transposition_mul_self,
        adjCocycle_eq_of_mul_transposition]
    have h4 : adjCocycle S T τ i = adjCocycle S T (σ * transposition i * transposition j) i := by
      rw [hτ_eq₁, adjCocycle_eq_of_mul_transposition]
    have h5 : adjCocycle S T (τ * transposition i) j =
        adjCocycle S T (σ * transposition i) j := by
      rw [hτ_eq₁, mul_transposition_mul_self, adjCocycle_eq_of_mul_transposition]
    have h6 : adjCocycle S T (τ * transposition i * transposition j) i = adjCocycle S T σ i := by
      rw [hτ_eq₁, mul_transposition_mul_self, mul_transposition_mul_self,
        adjCocycle_eq_of_mul_transposition]
    rw [h1, h2, h3, h4, h5, h6] at hτ
    calc adjCocycle S T σ j * adjCocycle S T (σ * transposition j) i *
          adjCocycle S T (σ * transposition j * transposition i) j
        = adjCocycle S T (σ * transposition j * transposition i) j *
            adjCocycle S T (σ * transposition j) i * adjCocycle S T σ j := by ac_rfl
      _ = adjCocycle S T (σ * transposition i * transposition j) i *
            adjCocycle S T (σ * transposition i) j * adjCocycle S T σ i := hτ
      _ = adjCocycle S T σ i * adjCocycle S T (σ * transposition i) j *
            adjCocycle S T (σ * transposition i * transposition j) i := by ac_rfl
  · exact adjCocycle_braid_three_of_notMem S T σ hij hmem

private theorem adjCocycle_braid (S T : GridSignAssignment n) (σ : Equiv.Perm (Fin n))
    (i j : Fin (n - 1)) :
    (permCoxeterSystem n).cocycleProd (adjCocycle S T) σ
        (CoxeterSystem.braidWord (CoxeterMatrix.A (n - 1)) i j) =
      (permCoxeterSystem n).cocycleProd (adjCocycle S T) σ
        (CoxeterSystem.braidWord (CoxeterMatrix.A (n - 1)) j i) := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have hval : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  by_cases hadj : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
  · rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord,
      coxeterMatrixA_eq_three hadj, coxeterMatrixA_eq_three hadj.symm,
      CoxeterSystem.cocycleProd_alternatingWord_three,
      CoxeterSystem.cocycleProd_alternatingWord_three]
    simp only [permCoxeterSystem_simple]
    rcases hadj with h | h
    · exact adjCocycle_braid_three S T σ h
    · exact (adjCocycle_braid_three S T σ h).symm
  · have hfar : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i := by omega
    rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord,
      coxeterMatrixA_eq_two hfar, coxeterMatrixA_eq_two hfar.symm,
      CoxeterSystem.cocycleProd_alternatingWord_two,
      CoxeterSystem.cocycleProd_alternatingWord_two]
    simp only [permCoxeterSystem_simple]
    exact adjCocycle_braid_two S T σ hfar

/-! ### Uniqueness up to gauge -/

/-- Any two grid sign assignments of the same size are related by a gauge transform. -/
theorem exists_gauge_eq (S T : GridSignAssignment n) :
    ∃ f : GridState n → ℤˣ, S.gauge f = T := by
  by_cases hn : 2 ≤ n
  · obtain ⟨g, ⟨_, hg⟩, _⟩ :=
      (permCoxeterSystem n).existsUnique_mul_eq_of_cocycle (adjCocycle S T)
        (fun σ i => by simp only [permCoxeterSystem_simple]; exact adjCocycle_mul_self S T σ i)
        (adjCocycle_braid S T)
    refine ⟨fun x => g x.toPerm,
      eq_of_width_one_ne (S.gauge fun x => g x.toPerm) T ⟨n - 1, by omega⟩ ?_⟩
    intro x y r hr hrot hnotlast
    have hlt : (r.left : ℕ) < n - 1 := by
      have := r.left.isLt
      have hne : (r.left : ℕ) ≠ n - 1 := fun h => hnotlast (Fin.ext h)
      omega
    let i : Fin (n - 1) := ⟨r.left, hlt⟩
    have hi_left : strand i = r.left := Fin.ext (by simp [i])
    have hi_right : strandSucc i = r.right := by
      rw [hrot, ← hi_left, finRotate_strand]
    have hy : y = ⟨x.toPerm * transposition i⟩ := by
      rw [r.target_eq_swapColumns]
      exact GridState.ext fun c => by
        simp [GridState.swapColumns_apply, transposition_eq_swap, hi_left, hi_right]
    have hy_perm : y.toPerm = x.toPerm * transposition i := congrArg GridState.toPerm hy
    have hratio : signRatio S T r hr = adjCocycle S T x.toPerm i :=
      signRatio_congr rfl hy hr (isEmpty_adjRect x.toPerm i)
        (hi_left.symm.trans (adjRect_left _ i).symm)
    have hstep := hg x.toPerm i
    simp only [permCoxeterSystem_simple] at hstep
    rw [gauge_sign, hy_perm, ← hstep, ← hratio, signRatio]
    calc g x.toPerm * (g x.toPerm * (S.sign r hr * T.sign r hr)) * S.sign r hr
        = (g x.toPerm * g x.toPerm) * (S.sign r hr * S.sign r hr) * T.sign r hr := by ac_rfl
      _ = T.sign r hr := by rw [Int.units_mul_self, Int.units_mul_self, one_mul, one_mul]
  · refine ⟨1, ?_⟩
    have : Subsingleton (Fin n) := ⟨fun a b => Fin.ext (by omega)⟩
    refine GridSignAssignment.ext fun x y r _ => ?_
    exact absurd (Subsingleton.elim r.left r.right) r.left_ne_right

/-- A gauge transform fixes a sign assignment if and only if the gauge is constant. -/
theorem gauge_eq_self_iff (S : GridSignAssignment n) (f : GridState n → ℤˣ) :
    S.gauge f = S ↔ ∃ c : ℤˣ, ∀ x, f x = c := by
  constructor
  · intro h
    refine ⟨f ⟨1⟩, fun x => ?_⟩
    let g : Equiv.Perm (Fin n) → ℤˣ := fun σ => f ⟨σ⟩
    have hinv : ∀ σ i, g (σ * (permCoxeterSystem n).simple i) = g σ := by
      intro σ i
      have hsign := congrArg (fun A : GridSignAssignment n =>
        A.sign (adjRect σ i) (isEmpty_adjRect σ i)) h
      simp only [gauge_sign] at hsign
      have hmul : f ⟨σ⟩ * f ⟨σ * transposition i⟩ = 1 :=
        mul_right_cancel (b := S.sign (adjRect σ i) (isEmpty_adjRect σ i))
          (by simpa only [one_mul] using hsign)
      rw [permCoxeterSystem_simple]
      exact (units_mul_eq_one_iff_eq.mp hmul).symm
    exact (permCoxeterSystem n).eq_const_of_forall_mul_simple hinv x.toPerm
  · rintro ⟨c, hc⟩
    refine GridSignAssignment.ext fun x y r hr => ?_
    simp only [gauge_sign, hc, Int.units_mul_self, one_mul]

/-- Two gauges produce the same gauge transform of a sign assignment if and only if they differ by
a global sign. -/
theorem gauge_eq_gauge_iff (S : GridSignAssignment n) (f g : GridState n → ℤˣ) :
    S.gauge f = S.gauge g ↔ ∃ c : ℤˣ, ∀ x, g x = c * f x := by
  have hiff : S.gauge f = S.gauge g ↔ S.gauge (f * g) = S := by
    constructor
    · intro h
      have h' := congrArg (fun A : GridSignAssignment n => A.gauge f) h
      simpa only [gauge_gauge_self, gauge_gauge] using h'.symm
    · intro h
      have h' := congrArg (fun A : GridSignAssignment n => A.gauge f) h
      have hff : f * (f * g) = g := funext fun x => by
        simp only [Pi.mul_apply, ← mul_assoc, Int.units_mul_self, one_mul]
      simpa only [gauge_gauge, hff] using h'.symm
  rw [hiff, gauge_eq_self_iff]
  refine exists_congr fun c => forall_congr' fun x => ?_
  simp only [Pi.mul_apply]
  constructor
  · intro h
    calc g x = (f x * f x) * g x := by rw [Int.units_mul_self, one_mul]
      _ = (f x * g x) * f x := by ac_rfl
      _ = c * f x := by rw [h]
  · intro h
    calc f x * g x = f x * (c * f x) := by rw [h]
      _ = c * (f x * f x) := by ac_rfl
      _ = c := by rw [Int.units_mul_self, mul_one]

end GridSignAssignment

namespace GridDiagram

/-- Any two grid sign assignments induce conjugate signed unblocked differentials on `GC⁻` via the
diagonal sign-change automorphism `Finsupp.signEquiv`. -/
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
