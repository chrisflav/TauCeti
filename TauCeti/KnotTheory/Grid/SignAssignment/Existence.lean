/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SignAssignment.Basic
import Mathlib.Analysis.Real.Sqrt
import TauCeti.KnotTheory.Grid.Differential.Square.SameDomain
import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Kernel
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Real
import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic

/-!
# Existence of grid sign assignments

This file constructs a grid sign assignment `TauCeti.GridSignAssignment n` for every grid size `n`,
following É. Gallais's Pin-group double-cover construction.

For `n < 2` there are no rectangles between size-`n` grid states, so the sign assignment is
vacuous. For `n ≥ 2`, endow `ℝⁿ` with the negative-definite quadratic form `Q(x) = -∑ i, xᵢ²`. The
symmetric group `Sₙ` embeds in `O(Q)` by permuting coordinates, and the twisted-conjugation
homomorphism `Pin(Q) → O(Q)` is surjective with kernel `{±1}`. Each ordered pair of distinct
columns `(a, b)` corresponds to the unit reflection vector `v(a, b) = (eₐ - e_b) / √2` with
`Q(v(a, b)) = -1`, whose Clifford image `u(a, b) ∈ Pin(Q)` lifts the transposition
`swap a b ∈ O(Q)`.

Choosing an arbitrary section `s : GridState n → Pin(Q)` lifting each grid state's permutation, a
rectangle `r` from `x` to `y` determines the kernel element
`s(x) * u(r.left, r.right) * s(y)⁻¹ ∈ ker(Pin(Q) → O(Q)) ≅ ℤˣ`. Its sign satisfies:

* the vertical annulus rule because `u(a, b)² = -1`;
* the horizontal annulus rule because `u(a, b) * u(b, a) = 1`;
* the square rule because `u(a, b)` and `u(c, d)` anticommute when `{a, b}` and `{c, d}` are
  disjoint, and `u(a, b) * u(b, c)` is cyclically invariant in `(a, b, c)`, which reverses the sign
  across every recut of a one-common-side decomposition.

## Main results

* `TauCeti.GridSignAssignment.instNonempty`: a grid sign assignment exists for every grid size `n`.

## References

* É. Gallais, *Sign assignments on link grid diagrams*, arXiv:0706.0089 (2007).
* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Section 4 (arXiv:math/0610559).
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 15.2.
-/

public section

namespace TauCeti

namespace GridSignAssignment

open _root_.CliffordAlgebra

/-! ### Negative-definite form and permutation representation -/

/-- The negative-definite standard quadratic form on `Fin n → ℝ`, for which every reflection
lies in the image of the Pin group. -/
private def negStdForm (n : ℕ) : QuadraticForm ℝ (Fin n → ℝ) :=
  -(realCliffordForm n 0)

private theorem neg_negStdForm_posDef (n : ℕ) : (-(negStdForm n)).PosDef := by
  simpa only [negStdForm, neg_neg] using posDef_realCliffordForm_zero n

private theorem negStdForm_nondegenerate (n : ℕ) : (negStdForm n).Nondegenerate :=
  (QuadraticMap.nondegenerate_neg (negStdForm n)).mp
    (neg_negStdForm_posDef n).anisotropic.nondegenerate

private theorem negStdForm_apply (n : ℕ) (v : Fin n → ℝ) :
    negStdForm n v = -∑ i, v i * v i := by
  rw [negStdForm, neg_apply, realCliffordForm_apply n 0 v]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [realCliffordWeight_of_lt i.isLt, one_mul]

private theorem negStdForm_single (n : ℕ) (i : Fin n) (x : ℝ) :
    negStdForm n (Pi.single i x) = -(x ^ 2) := by
  rw [negStdForm, neg_apply, realCliffordForm_apply_single n 0 i x,
    realCliffordWeight_of_lt i.isLt, one_mul]

private theorem polar_negStdForm_single (n : ℕ) (v : Fin n → ℝ) (i : Fin n) (a : ℝ) :
    QuadraticMap.polar (negStdForm n) v (Pi.single i a) = -(2 * a * v i) := by
  have hpol : QuadraticMap.polar (negStdForm n) v (Pi.single i a) =
      -QuadraticMap.polar (realCliffordForm n 0) v (Pi.single i a) := by
    simp only [negStdForm, QuadraticMap.polar, neg_apply]
    ring
  rw [hpol, polar_realCliffordForm_single n 0 v i a, realCliffordWeight_of_lt i.isLt]
  ring

/-- The orthogonal representation of `Equiv.Perm (Fin n)` permuting coordinates on `Fin n → ℝ`.
-/
private def permOrthogonal (n : ℕ) :
    Equiv.Perm (Fin n) →* TauCeti.QuadraticMap.orthogonalGroup (negStdForm n) where
  toFun σ :=
    ⟨LinearEquiv.funCongrLeft ℝ ℝ σ.symm,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun m => by
        simp only [negStdForm_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
        congr 1
        exact Equiv.sum_comp σ.symm (fun i => m i * m i)⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun _ => funext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (LinearEquiv.ext fun _ => funext fun _ => rfl)

private theorem permOrthogonal_apply (n : ℕ) (σ : Equiv.Perm (Fin n)) (m : Fin n → ℝ)
    (i : Fin n) :
    ((permOrthogonal n σ : TauCeti.QuadraticMap.orthogonalGroup (negStdForm n)) :
        (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) m i = m (σ⁻¹ i) :=
  rfl

/-! ### Reflection vectors and Pin generators for column swaps -/

/-- The unit reflection vector `(eₐ - e_b) / √2` associated to an ordered pair `(a, b)`. -/
private noncomputable def swapVec {n : ℕ} (a b : Fin n) : Fin n → ℝ :=
  (1 / Real.sqrt 2) • (Pi.single a (1 : ℝ) - Pi.single b 1)

private theorem polar_negStdForm_swapVec {n : ℕ} (a b : Fin n) (m : Fin n → ℝ) :
    QuadraticMap.polar (negStdForm n) (swapVec a b) m =
      -(Real.sqrt 2 * (m a - m b)) := by
  have hsymm : QuadraticMap.polar (negStdForm n) (swapVec a b) m =
      QuadraticMap.polar (negStdForm n) m (swapVec a b) := QuadraticMap.polar_comm _ _ _
  rw [hsymm, swapVec, QuadraticMap.polar_smul_right, QuadraticMap.polar_sub_right,
    polar_negStdForm_single, polar_negStdForm_single, smul_eq_mul]
  have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp [hne]
  rw [Real.sq_sqrt (by norm_num)]
  ring

private theorem negStdForm_swapVec {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    negStdForm n (swapVec a b) = -1 := by
  have hsub : negStdForm n (Pi.single a (1 : ℝ) - Pi.single b 1) = -2 := by
    rw [sub_eq_add_neg, QuadraticMap.map_add (negStdForm n), QuadraticMap.map_neg,
      negStdForm_single, negStdForm_single, ← Pi.single_neg, polar_negStdForm_single,
      Pi.single_eq_of_ne hab.symm]
    norm_num
  rw [swapVec, QuadraticMap.map_smul, hsub, smul_eq_mul, one_div, ← mul_inv,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The Pin-group lift `ι(v(a, b))` of the transposition `swap a b`. -/
private noncomputable def swapPin {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    pinGroup (negStdForm n) :=
  ⟨ι (negStdForm n) (swapVec a b), ι_mem_pinGroup (negStdForm_swapVec hab)⟩

private theorem coe_swapPin {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    (swapPin hab : CliffordAlgebra (negStdForm n)) = ι (negStdForm n) (swapVec a b) :=
  rfl

private theorem pinToOrthogonal_swapPin {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    pinToOrthogonal (negStdForm n) (swapPin hab) = permOrthogonal n (Equiv.swap a b) := by
  refine Subtype.ext (LinearEquiv.ext fun m => funext fun i => ?_)
  rw [swapPin, pinToOrthogonal_ι_apply (negStdForm_swapVec hab), permOrthogonal_apply,
    Equiv.swap_inv, polar_negStdForm_swapVec]
  simp only [Pi.add_apply, Pi.smul_apply, swapVec, Pi.sub_apply, smul_eq_mul]
  have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  by_cases hia : i = a
  · subst hia
    rw [Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_of_ne hab]
    field_simp [hne]
    ring
  · by_cases hib : i = b
    · subst hib
      rw [Equiv.swap_apply_right, Pi.single_eq_of_ne hab.symm, Pi.single_eq_same]
      field_simp [hne]
      ring
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib]
      ring

/-! ### Clifford algebra relations among swap generators -/

private theorem ι_single_mul_self {n : ℕ} (i : Fin n) :
    ι (negStdForm n) (Pi.single i (1 : ℝ)) * ι (negStdForm n) (Pi.single i 1) = -1 := by
  rw [ι_sq_scalar, negStdForm_single]
  simp

private theorem ι_single_mul_swap {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ι (negStdForm n) (Pi.single j (1 : ℝ)) * ι (negStdForm n) (Pi.single i 1) =
      -(ι (negStdForm n) (Pi.single i 1) * ι (negStdForm n) (Pi.single j 1)) := by
  have hpol : QuadraticMap.polar (negStdForm n) (Pi.single i (1 : ℝ)) (Pi.single j 1) = 0 := by
    rw [polar_negStdForm_single, Pi.single_eq_of_ne hij.symm]
    ring
  have hsum := ι_mul_ι_add_swap (Q := negStdForm n) (Pi.single i (1 : ℝ)) (Pi.single j 1)
  rw [hpol, map_zero] at hsum
  exact eq_neg_of_add_eq_zero_right hsum

private theorem swapVec_swap {n : ℕ} (a b : Fin n) : swapVec b a = -swapVec a b := by
  simp only [swapVec, ← smul_neg, neg_sub]

private theorem ι_swapVec_swap {n : ℕ} (a b : Fin n) :
    ι (negStdForm n) (swapVec b a) = -ι (negStdForm n) (swapVec a b) := by
  rw [swapVec_swap, map_neg]

private theorem ι_swapVec_mul_self {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    ι (negStdForm n) (swapVec a b) * ι (negStdForm n) (swapVec a b) = -1 := by
  rw [ι_sq_scalar, negStdForm_swapVec hab]
  simp

private theorem ι_swapVec_mul_swap {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    ι (negStdForm n) (swapVec a b) * ι (negStdForm n) (swapVec b a) = 1 := by
  rw [ι_swapVec_swap b a, neg_mul, ι_swapVec_mul_self hab.symm, neg_neg]

private theorem ι_swapVec_mul_comm_neg {n : ℕ} {a b c d : Fin n}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ι (negStdForm n) (swapVec c d) * ι (negStdForm n) (swapVec a b) =
      -(ι (negStdForm n) (swapVec a b) * ι (negStdForm n) (swapVec c d)) := by
  have hpol : QuadraticMap.polar (negStdForm n) (swapVec a b) (swapVec c d) = 0 := by
    rw [polar_negStdForm_swapVec]
    simp only [swapVec, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_of_ne hac,
      Pi.single_eq_of_ne had, Pi.single_eq_of_ne hbc, Pi.single_eq_of_ne hbd, sub_self,
      smul_zero, mul_zero, neg_zero]
  have hsum := ι_mul_ι_add_swap (Q := negStdForm n) (swapVec a b) (swapVec c d)
  rw [hpol, map_zero] at hsum
  exact eq_neg_of_add_eq_zero_right hsum

private theorem ι_swapVec_mul_triple_eq {n : ℕ} {a b c : Fin n} (hac : a ≠ c) :
    ι (negStdForm n) (swapVec a b) * ι (negStdForm n) (swapVec b c) =
      (1 / 2 : ℝ) • (1 +
        ι (negStdForm n) (Pi.single a 1) * ι (negStdForm n) (Pi.single b 1) +
        ι (negStdForm n) (Pi.single b 1) * ι (negStdForm n) (Pi.single c 1) +
        ι (negStdForm n) (Pi.single c 1) * ι (negStdForm n) (Pi.single a 1)) := by
  have hscale : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    rw [one_div_mul_one_div, Real.mul_self_sqrt (by norm_num)]
  simp only [swapVec, map_smul, map_sub, smul_mul_smul_comm, hscale]
  congr 1
  have h1 : ι (negStdForm n) (Pi.single b 1) * ι (negStdForm n) (Pi.single b 1) = -1 :=
    ι_single_mul_self b
  have h2 : ι (negStdForm n) (Pi.single a 1) * ι (negStdForm n) (Pi.single c 1) =
      -(ι (negStdForm n) (Pi.single c 1) * ι (negStdForm n) (Pi.single a 1)) :=
    ι_single_mul_swap hac.symm
  calc (ι (negStdForm n) (Pi.single a 1) - ι (negStdForm n) (Pi.single b 1)) *
        (ι (negStdForm n) (Pi.single b 1) - ι (negStdForm n) (Pi.single c 1))
      = ι (negStdForm n) (Pi.single a 1) * ι (negStdForm n) (Pi.single b 1) -
        ι (negStdForm n) (Pi.single a 1) * ι (negStdForm n) (Pi.single c 1) -
        ι (negStdForm n) (Pi.single b 1) * ι (negStdForm n) (Pi.single b 1) +
        ι (negStdForm n) (Pi.single b 1) * ι (negStdForm n) (Pi.single c 1) := by
          noncomm_ring
    _ = 1 +
        ι (negStdForm n) (Pi.single a 1) * ι (negStdForm n) (Pi.single b 1) +
        ι (negStdForm n) (Pi.single b 1) * ι (negStdForm n) (Pi.single c 1) +
        ι (negStdForm n) (Pi.single c 1) * ι (negStdForm n) (Pi.single a 1) := by
          rw [h1, h2]
          abel

private theorem ι_swapVec_mul_triple_cycle {n : ℕ} {a b c : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) :
    ι (negStdForm n) (swapVec a b) * ι (negStdForm n) (swapVec b c) =
      ι (negStdForm n) (swapVec b c) * ι (negStdForm n) (swapVec c a) := by
  rw [ι_swapVec_mul_triple_eq hac, ι_swapVec_mul_triple_eq hab.symm]
  congr 1
  abel

/-! ### Recut sign reversal in the Clifford algebra -/

private theorem ι_swapVec_recut_of_left_eq_left {n : ℕ} {x z : GridState n}
    {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) (hdata : D.IsRecutOfLeftEqLeft E) :
    ι (negStdForm n) (swapVec E.first.left E.first.right) *
        ι (negStdForm n) (swapVec E.second.left E.second.right) =
      -(ι (negStdForm n) (swapVec D.first.left D.first.right) *
        ι (negStdForm n) (swapVec D.second.left D.second.right)) := by
  have hcommon := hdata.side_eq
  obtain ⟨hEfr, hEsr⟩ := hdata.recut_sides
  set a := D.first.left
  set b := D.first.right
  set c := D.second.right
  have hab : a ≠ b := D.first.left_ne_right
  have hac : a ≠ c := by simpa only [a, c, hcommon] using D.second.left_ne_right
  have hbc : b ≠ c := fun h => D.sideColumns_ne_of_hasOneCommonSide hone (by
    simp only [GridRectangleBetween.sideColumns, ← hcommon, a, b, c] at h ⊢; rw [h])
  rw [← hcommon]
  rcases hdata.recut_branch with ⟨-, -, hEfl, hEsl⟩ | ⟨-, -, hEfl, hEsl⟩
  · rw [hEfl, hEfr, hEsl, hEsr]
    calc ι (negStdForm n) (swapVec b c) * ι (negStdForm n) (swapVec a b)
        = (-ι (negStdForm n) (swapVec c b)) * (-ι (negStdForm n) (swapVec b a)) := by
            rw [ι_swapVec_swap c b, ι_swapVec_swap b a]
      _ = ι (negStdForm n) (swapVec c b) * ι (negStdForm n) (swapVec b a) := neg_mul_neg _ _
      _ = ι (negStdForm n) (swapVec b a) * ι (negStdForm n) (swapVec a c) :=
            ι_swapVec_mul_triple_cycle hbc.symm hac.symm
      _ = -(ι (negStdForm n) (swapVec a b) * ι (negStdForm n) (swapVec a c)) := by
            rw [ι_swapVec_swap a b, neg_mul]
  · rw [hEfl, hEfr, hEsl, hEsr]
    calc ι (negStdForm n) (swapVec a c) * ι (negStdForm n) (swapVec c b)
        = ι (negStdForm n) (swapVec b a) * ι (negStdForm n) (swapVec a c) :=
            (ι_swapVec_mul_triple_cycle hab.symm hbc).symm
      _ = -(ι (negStdForm n) (swapVec a b) * ι (negStdForm n) (swapVec a c)) := by
            rw [ι_swapVec_swap a b, neg_mul]

private theorem ι_swapVec_recut_of_right_eq_right {n : ℕ} {x z : GridState n}
    {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) (hdata : D.IsRecutOfRightEqRight E) :
    ι (negStdForm n) (swapVec E.first.left E.first.right) *
        ι (negStdForm n) (swapVec E.second.left E.second.right) =
      -(ι (negStdForm n) (swapVec D.first.left D.first.right) *
        ι (negStdForm n) (swapVec D.second.left D.second.right)) := by
  have hcommon := hdata.side_eq
  obtain ⟨hEfl, hEsl⟩ := hdata.recut_sides
  set a := D.first.left
  set b := D.second.left
  set c := D.first.right
  have hac : a ≠ c := D.first.left_ne_right
  have hbc : b ≠ c := by simpa only [b, c, hcommon] using D.second.left_ne_right
  have hab : a ≠ b := fun h => D.sideColumns_ne_of_hasOneCommonSide hone (by
    simp only [GridRectangleBetween.sideColumns, ← hcommon, a, b, c] at h ⊢; rw [h])
  rw [← hcommon]
  rcases hdata.recut_branch with ⟨-, -, hEfr, hEsr⟩ | ⟨-, -, hEfr, hEsr⟩
  · rw [hEfl, hEfr, hEsl, hEsr]
    calc ι (negStdForm n) (swapVec b a) * ι (negStdForm n) (swapVec a c)
        = ι (negStdForm n) (swapVec a c) * ι (negStdForm n) (swapVec c b) :=
            ι_swapVec_mul_triple_cycle hab.symm hbc
      _ = -(ι (negStdForm n) (swapVec a c) * ι (negStdForm n) (swapVec b c)) := by
            rw [ι_swapVec_swap b c, mul_neg]
  · rw [hEfl, hEfr, hEsl, hEsr]
    calc ι (negStdForm n) (swapVec b c) * ι (negStdForm n) (swapVec a b)
        = (-ι (negStdForm n) (swapVec c b)) * (-ι (negStdForm n) (swapVec b a)) := by
            rw [ι_swapVec_swap c b, ι_swapVec_swap b a]
      _ = ι (negStdForm n) (swapVec c b) * ι (negStdForm n) (swapVec b a) := neg_mul_neg _ _
      _ = ι (negStdForm n) (swapVec b a) * ι (negStdForm n) (swapVec a c) :=
            ι_swapVec_mul_triple_cycle hbc.symm hac.symm
      _ = ι (negStdForm n) (swapVec a c) * ι (negStdForm n) (swapVec c b) :=
            ι_swapVec_mul_triple_cycle hab.symm hbc
      _ = -(ι (negStdForm n) (swapVec a c) * ι (negStdForm n) (swapVec b c)) := by
            rw [ι_swapVec_swap b c, mul_neg]

private theorem ι_swapVec_recut {n : ℕ} {x z : GridState n}
    (D : GridRectangleDecomposition x z) (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) :
    let E := D.recut hone hD₁ hD₂
    ι (negStdForm n) (swapVec E.first.left E.first.right) *
        ι (negStdForm n) (swapVec E.second.left E.second.right) =
      -(ι (negStdForm n) (swapVec D.first.left D.first.right) *
        ι (negStdForm n) (swapVec D.second.left D.second.right)) := by
  intro E
  rcases D.hasSameSideOverlap_or_hasMixedSideOverlap hone with hsame | hmix
  · rcases (D.hasSameSideOverlap_iff.mp hsame).2 with hleft | hright
    · exact ι_swapVec_recut_of_left_eq_left hone
        (D.isRecutOfLeftEqLeft_recut hleft hone hD₁ hD₂)
    · exact ι_swapVec_recut_of_right_eq_right hone
        (D.isRecutOfRightEqRight_recut hright hone hD₁ hD₂)
  · have hEone : E.HasOneCommonSide := D.hasOneCommonSide_recut hone hD₁ hD₂
    have hErecut : E.IsRecut D := (D.isRecut_recut hone hD₁ hD₂).symm hD₁ hD₂
    have hback : ι (negStdForm n) (swapVec D.first.left D.first.right) *
        ι (negStdForm n) (swapVec D.second.left D.second.right) =
        -(ι (negStdForm n) (swapVec E.first.left E.first.right) *
          ι (negStdForm n) (swapVec E.second.left E.second.right)) := by
      rcases (D.hasMixedSideOverlap_iff.mp hmix).2 with hleft | hright
      · rcases D.recut_geometry_of_left_eq_right hleft hone hD₁ hD₂ with
            ⟨-, hfl, -, hsl, -⟩ | ⟨-, -, hfr, -, hsr, -⟩
        · exact ι_swapVec_recut_of_left_eq_left hEone
            (hErecut.isRecutOfLeftEqLeft (hfl.trans hsl.symm))
        · exact ι_swapVec_recut_of_right_eq_right hEone
            (hErecut.isRecutOfRightEqRight (hfr.trans hsr.symm))
      · rcases D.recut_geometry_of_right_eq_left hright hone hD₁ hD₂ with
            ⟨-, -, hfr, -, hsr, -⟩ | ⟨-, hfl, -, hsl, -⟩
        · exact ι_swapVec_recut_of_right_eq_right hEone
            (hErecut.isRecutOfRightEqRight (hfr.trans hsr.symm))
        · exact ι_swapVec_recut_of_left_eq_left hEone
            (hErecut.isRecutOfLeftEqLeft (hfl.trans hsl.symm))
    rw [hback, neg_neg]

/-! ### Kernel character and construction of the sign assignment -/

private def zmodTwoToIntUnits : Multiplicative (ZMod 2) →* ℤˣ where
  toFun x := if Multiplicative.toAdd x = 0 then 1 else -1
  map_one' := rfl
  map_mul' x y := by
    have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := fun z => by
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hcases (Multiplicative.toAdd x) with hx | hx <;>
      rcases hcases (Multiplicative.toAdd y) with hy | hy <;>
      simp [hx, hy, (by decide : (1 + 1 : ZMod 2) = 0)]

private theorem zmodTwoToIntUnits_ofAdd_one :
    zmodTwoToIntUnits (Multiplicative.ofAdd 1) = -1 := by
  simp [zmodTwoToIntUnits]

/-- The isomorphism `ker(Pin(Q) → O(Q)) →* ℤˣ` sending `-1` to `-1`. -/
private noncomputable def kerPinToIntUnits (n : ℕ) [Nontrivial (Fin n → ℝ)] :
    MonoidHom.ker (pinToOrthogonal (negStdForm n)) →* ℤˣ :=
  zmodTwoToIntUnits.comp
    (zmodTwoMulEquivKerPinToOrthogonal (negStdForm n) (negStdForm_nondegenerate n)).symm.toMonoidHom

private noncomputable def negOneKer (n : ℕ) [Nontrivial (Fin n → ℝ)] :
    MonoidHom.ker (pinToOrthogonal (negStdForm n)) :=
  ⟨spinToPin (negStdForm n)
      (spinGroup.negOne (negStdForm n) (negStdForm_nondegenerate n).ne_zero),
    by rw [MonoidHom.mem_ker, pinToOrthogonal_spinToPin, spinGroup.spinToOrthogonal_negOne]⟩

private theorem coe_negOneKer (n : ℕ) [Nontrivial (Fin n → ℝ)] :
    ((negOneKer n : pinGroup (negStdForm n)) : CliffordAlgebra (negStdForm n)) = -1 := by
  simp only [negOneKer, coe_spinToPin_apply, spinGroup.coe_negOne]

private theorem kerPinToIntUnits_neg_one (n : ℕ) [Nontrivial (Fin n → ℝ)]
    (k : MonoidHom.ker (pinToOrthogonal (negStdForm n)))
    (hk : ((k : pinGroup (negStdForm n)) : CliffordAlgebra (negStdForm n)) = -1) :
    kerPinToIntUnits n k = -1 := by
  have hEq : k = negOneKer n :=
    Subtype.ext (Subtype.ext (hk.trans (coe_negOneKer n).symm))
  rw [hEq, kerPinToIntUnits, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, negOneKer,
    zmodTwoMulEquivKerPinToOrthogonal_symm_apply_negOne (negStdForm n) (negStdForm_nondegenerate n),
    zmodTwoToIntUnits_ofAdd_one]

private theorem kerPinToIntUnits_eq_neg_of_coe_eq_neg (n : ℕ) [Nontrivial (Fin n → ℝ)]
    (k₁ k₂ : MonoidHom.ker (pinToOrthogonal (negStdForm n)))
    (h : ((k₁ : pinGroup (negStdForm n)) : CliffordAlgebra (negStdForm n)) =
      -((k₂ : pinGroup (negStdForm n)) : CliffordAlgebra (negStdForm n))) :
    kerPinToIntUnits n k₁ = -kerPinToIntUnits n k₂ := by
  have hmul : k₁ = negOneKer n * k₂ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [h, Subgroup.coe_mul, Submonoid.coe_mul, coe_negOneKer, neg_one_mul]
  rw [hmul, map_mul, kerPinToIntUnits_neg_one n (negOneKer n) (coe_negOneKer n), neg_one_mul]

/-- The Pin-kernel element associated to a rectangle `r : GridRectangleBetween x y` using a chosen
section `s : GridState n → Pin(Q)`. -/
private noncomputable def rectKerElem {n : ℕ}
    (s : GridState n → pinGroup (negStdForm n))
    (hs : ∀ x, pinToOrthogonal (negStdForm n) (s x) = permOrthogonal n x.toPerm)
    {x y : GridState n} (r : GridRectangleBetween x y) :
    MonoidHom.ker (pinToOrthogonal (negStdForm n)) :=
  ⟨s x * swapPin r.left_ne_right * (s y)⁻¹, by
    have htoPerm : y.toPerm = x.toPerm * Equiv.swap r.left r.right :=
      (congrArg GridState.toPerm r.target_eq_swapColumns).trans (GridState.swapColumns_toPerm _ _ _)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hs x, hs y, pinToOrthogonal_swapPin,
      ← map_mul, ← map_inv, ← map_mul, htoPerm, mul_inv_cancel, map_one]⟩

private theorem coe_rectKerElem_mul {n : ℕ}
    (s : GridState n → pinGroup (negStdForm n))
    (hs : ∀ x, pinToOrthogonal (negStdForm n) (s x) = permOrthogonal n x.toPerm)
    {x y z : GridState n} (r₁ : GridRectangleBetween x y) (r₂ : GridRectangleBetween y z) :
    (((rectKerElem s hs r₁ * rectKerElem s hs r₂ :
        MonoidHom.ker (pinToOrthogonal (negStdForm n))) : pinGroup (negStdForm n)) :
        CliffordAlgebra (negStdForm n)) =
      (s x : CliffordAlgebra (negStdForm n)) *
        (ι (negStdForm n) (swapVec r₁.left r₁.right) *
          ι (negStdForm n) (swapVec r₂.left r₂.right)) *
        (((s z)⁻¹ : pinGroup (negStdForm n)) : CliffordAlgebra (negStdForm n)) := by
  have hprod : s x * swapPin r₁.left_ne_right * (s y)⁻¹ *
      (s y * swapPin r₂.left_ne_right * (s z)⁻¹) =
      s x * (swapPin r₁.left_ne_right * swapPin r₂.left_ne_right) * (s z)⁻¹ := by
    group
  rw [Subgroup.coe_mul, rectKerElem, rectKerElem, hprod]
  simp only [Submonoid.coe_mul, coe_swapPin]

/-- The Pin-group construction of a grid sign assignment for grid sizes `n ≥ 2`. -/
private noncomputable def ofPinGroup {n : ℕ} (hn : 2 ≤ n) : GridSignAssignment n := by
  haveI : Nontrivial (Fin n → ℝ) :=
    ⟨Pi.single ⟨0, by omega⟩ 1, 0, fun h => by simpa using congrFun h ⟨0, by omega⟩⟩
  have hsurj := pinToOrthogonal_surjective_of_negDef (negStdForm n) (neg_negStdForm_posDef n)
  choose s hs using fun x : GridState n => hsurj (permOrthogonal n x.toPerm)
  refine
    { sign := fun r _ => kerPinToIntUnits n (rectKerElem s hs r)
      sign_mul_sign_eq_neg := fun D E hD₁ hD₂ hE₁ hE₂ hne hdom => ?_
      sign_mul_sign_eq_neg_one_of_left_eq_left := fun {x _} r₁ r₂ _ _ hleft => ?_
      sign_mul_sign_eq_one_of_left_eq_right := fun r₁ r₂ _ _ hleft => ?_ }
  · rw [← map_mul, ← map_mul]
    refine kerPinToIntUnits_eq_neg_of_coe_eq_neg n _ _ ?_
    rw [coe_rectKerElem_mul, coe_rectKerElem_mul]
    have hneg : ι (negStdForm n) (swapVec E.first.left E.first.right) *
          ι (negStdForm n) (swapVec E.second.left E.second.right) =
        -(ι (negStdForm n) (swapVec D.first.left D.first.right) *
          ι (negStdForm n) (swapVec D.second.left D.second.right)) := by
      rcases D.eq_commute_or_eq_recut_of_ne_of_val_add_val_eq hD₁ hD₂ hE₁ hE₂ hne hdom with
          ⟨hdisj, rfl⟩ | ⟨hone, rfl⟩
      · obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp hdisj
        rw [D.commute_first_left hdisj, D.commute_first_right hdisj,
          D.commute_second_left hdisj, D.commute_second_right hdisj]
        exact ι_swapVec_mul_comm_neg hll hlr hrl hrr
      · exact ι_swapVec_recut D hone hD₁ hD₂
    rw [hneg, mul_neg, neg_mul]
  · rw [← map_mul]
    refine kerPinToIntUnits_neg_one n _ ?_
    rw [coe_rectKerElem_mul, hleft, r₁.right_eq_right_of_left_eq_left r₂ hleft,
      ι_swapVec_mul_self r₁.left_ne_right, mul_neg, mul_one, neg_mul]
    have hmul : (s x : CliffordAlgebra (negStdForm n)) *
        (((s x)⁻¹ : pinGroup (negStdForm n)) : CliffordAlgebra (negStdForm n)) = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
    rw [hmul]
  · rw [← map_mul]
    have hEq : rectKerElem s hs r₁ * rectKerElem s hs r₂ = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [coe_rectKerElem_mul, hleft, r₁.right_eq_left_of_left_eq_right r₂ hleft,
        ι_swapVec_mul_swap r₁.left_ne_right, mul_one, ← Submonoid.coe_mul, mul_inv_cancel]
      rfl
    rw [hEq, map_one]

/-- Every grid size `n` admits a grid sign assignment. -/
instance instNonempty (n : ℕ) : Nonempty (GridSignAssignment n) := by
  by_cases hn : 2 ≤ n
  · exact ⟨ofPinGroup hn⟩
  · have : Subsingleton (Fin n) := ⟨fun a b => Fin.ext (by omega)⟩
    exact ⟨⟨fun r _ => absurd (Subsingleton.elim r.left r.right) r.left_ne_right,
      fun D _ _ _ _ _ _ =>
        absurd (Subsingleton.elim D.first.left D.first.right) D.first.left_ne_right,
      fun r _ _ _ _ => absurd (Subsingleton.elim r.left r.right) r.left_ne_right,
      fun r _ _ _ _ => absurd (Subsingleton.elim r.left r.right) r.left_ne_right⟩⟩

end GridSignAssignment

end TauCeti
