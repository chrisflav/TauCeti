/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SignAssignment.Basic
import Mathlib.Analysis.Real.Sqrt
import TauCeti.KnotTheory.Grid.Differential.Square.UniqueDomain
import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Kernel
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Real
import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic

/-!
# Existence of sign assignments for grid rectangles

Every grid size `n` admits a sign assignment (`TauCeti.GridSignAssignment n`). We follow Gallais's
construction via the real Pin group `Pin⁻(n)` attached to the negative-definite quadratic form
`Q(v) = -∑ i, (v i)²` on `ℝⁿ`.

The symmetric group `Sₙ` embeds in `O(Q)` by permuting coordinates. For `n ≥ 1`, the twisted
conjugation homomorphism `Pin⁻(n) → O(Q)` is surjective with kernel `{±1}`. Each transposition
`(a b)` is the reflection in the unit vector `v_{a,b} = (e_a - e_b) / √2`, which satisfies
`Q(v_{a,b}) = -1` and therefore lifts to `ι(v_{a,b}) ∈ Pin⁻(n)`. Choosing an arbitrary lift
`L(x) ∈ Pin⁻(n)` of the permutation of each grid state `x`, every rectangle `r` from `x` to `y`
defines a central element
`L(x) · ι(v_{r.left, r.right}) · L(y)⁻¹ ∈ ker(Pin⁻(n) → O(Q)) = {±1}`,
which is the assigned sign `S(r)`.

In any two-step product `S(r₁) · S(r₂)`, the lifts of the intermediate state cancel, leaving
`L(x) · (ι(v_{a,b}) · ι(v_{c,d})) · L(z)⁻¹`. The three sign-assignment axioms then reduce to
identities in the Clifford algebra `Cl(Q)`:

* *vertical annulus*: `ι(v_{a,b}) · ι(v_{a,b}) = -1`;
* *horizontal annulus*: `ι(v_{a,b}) · ι(v_{b,a}) = 1`;
* *square rule*: disjoint root vectors are orthogonal so their Clifford products anticommute, and
  for three distinct indices `a, b, c`, the additive relation `v_{a,c} = v_{a,b} + v_{b,c}` yields
  the anticommutation identities matching all recut orientations.

## Main results

* `TauCeti.GridSignAssignment.instNonempty`: every grid size `n` admits a sign assignment.

## References

* É. Gallais, *Sign refinement for combinatorial link Floer homology*, Algebr. Geom. Topol. 8
  (2008), 1581–1592.
* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Section 4.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 15.2.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

namespace GridSignAssignment

/-! ### The negative-definite form and permutation action -/

/-- The negative-definite real quadratic form `v ↦ -∑ i, (v i)²` on `Fin n → ℝ`. -/
private abbrev negForm (n : ℕ) : QuadraticForm ℝ (Fin n → ℝ) :=
  -realCliffordForm n 0

private theorem posDef_neg_negForm (n : ℕ) : (-negForm n).PosDef := by
  simpa [negForm] using posDef_realCliffordForm_zero n

private theorem nondegenerate_negForm (n : ℕ) : (negForm n).Nondegenerate :=
  (QuadraticMap.nondegenerate_neg (negForm n)).mp (posDef_neg_negForm n).anisotropic.nondegenerate

/-- Coordinate permutations act orthogonally on `Fin n → ℝ` for `negForm n`. -/
private def permOrthogonal (n : ℕ) :
    Equiv.Perm (Fin n) →* TauCeti.QuadraticMap.orthogonalGroup (negForm n) where
  toFun σ :=
    ⟨(realCliffordFormZeroReindex σ.symm).toLinearEquiv,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
        simp [negForm]⟩
  map_one' := Subtype.ext <| LinearEquiv.ext fun v => funext fun i => by
    simp [realCliffordFormZeroReindex_apply, Equiv.Perm.one_def]
  map_mul' σ τ := Subtype.ext <| LinearEquiv.ext fun v => funext fun i => by
    simp [realCliffordFormZeroReindex_apply, Equiv.Perm.mul_def]

private theorem permOrthogonal_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ℝ)
    (i : Fin n) :
    ((permOrthogonal n σ : TauCeti.QuadraticMap.orthogonalGroup (negForm n)) :
        (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v i = v (σ⁻¹ i) :=
  realCliffordFormZeroReindex_apply σ.symm v i

/-! ### Root vectors and Clifford relations -/

/-- The normalized type-`A` root vector `(e_a - e_b) / √2` in `Fin n → ℝ`. -/
private noncomputable def swapVec {n : ℕ} (a b : Fin n) : Fin n → ℝ :=
  (Real.sqrt 2)⁻¹ • (Pi.single a 1 - Pi.single b 1)

private theorem swapVec_swap {n : ℕ} (a b : Fin n) : swapVec b a = -swapVec a b := by
  rw [swapVec, swapVec, ← smul_neg, neg_sub]

private theorem swapVec_add {n : ℕ} (a b c : Fin n) :
    swapVec a b + swapVec b c = swapVec a c := by
  simp only [swapVec, ← smul_add, sub_add_sub_cancel]

private theorem swapVec_apply {n : ℕ} (a b i : Fin n) :
    swapVec a b i =
      (Real.sqrt 2)⁻¹ * ((Pi.single a (1 : ℝ) : Fin n → ℝ) i -
        (Pi.single b (1 : ℝ) : Fin n → ℝ) i) := by
  simp [swapVec]

private theorem polar_negForm_swapVec {n : ℕ} (a b : Fin n) (m : Fin n → ℝ) :
    QuadraticMap.polar (negForm n) (swapVec a b) m =
      -(2 * (Real.sqrt 2)⁻¹) * (m a - m b) := by
  have h1 : QuadraticMap.polar (realCliffordForm n 0) m (Pi.single a 1) = 2 * m a := by
    rw [polar_realCliffordForm_single, realCliffordWeight_of_lt a.isLt]
    ring
  have h2 : QuadraticMap.polar (realCliffordForm n 0) m (Pi.single b 1) = 2 * m b := by
    rw [polar_realCliffordForm_single, realCliffordWeight_of_lt b.isLt]
    ring
  have hneg : QuadraticMap.polar (negForm n) (swapVec a b) m =
      -QuadraticMap.polar (realCliffordForm n 0) (swapVec a b) m := by
    simp only [QuadraticMap.polar, negForm, neg_apply]
    ring
  rw [hneg, QuadraticMap.polar_comm, swapVec, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_sub_right, h1, h2]
  simp only [smul_eq_mul]
  ring

private theorem negForm_swapVec {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    negForm n (swapVec a b) = -1 := by
  have hpol := polar_negForm_swapVec a b (swapVec a b)
  rw [QuadraticMap.polar_self, two_smul] at hpol
  simp only [swapVec_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, Pi.single_eq_of_ne hab.symm,
    sub_zero, zero_sub, mul_one, mul_neg, sub_neg_eq_add] at hpol
  have hval : -(2 * (Real.sqrt 2)⁻¹) * ((Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹) = -2 := by
    calc -(2 * (Real.sqrt 2)⁻¹) * ((Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹)
        = -4 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) := by ring
      _ = -4 * (2 : ℝ)⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
      _ = -2 := by norm_num
  linarith

/-- The Pin-group lift `ι(v_{a,b}) ∈ Pin⁻(n)` of the transposition `(a b)`. -/
private noncomputable def swapPin {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    pinGroup (negForm n) :=
  ⟨ι (negForm n) (swapVec a b), ι_mem_pinGroup (negForm_swapVec hab)⟩

private theorem pinToOrthogonal_swapPin {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    pinToOrthogonal (negForm n) (swapPin hab) = permOrthogonal n (Equiv.swap a b) := by
  refine Subtype.ext (LinearEquiv.ext fun m => funext fun i => ?_)
  rw [swapPin, pinToOrthogonal_ι_apply (negForm_swapVec hab), permOrthogonal_apply,
    Equiv.Perm.inv_def, Equiv.symm_swap, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    polar_negForm_swapVec, swapVec_apply]
  let d : ℝ :=
    (Pi.single a (1 : ℝ) : Fin n → ℝ) i - (Pi.single b (1 : ℝ) : Fin n → ℝ) i
  have hcoeff : -(2 * (Real.sqrt 2)⁻¹) * (m a - m b) * ((Real.sqrt 2)⁻¹ * d) =
      -(m a - m b) * d := by
    calc -(2 * (Real.sqrt 2)⁻¹) * (m a - m b) * ((Real.sqrt 2)⁻¹ * d)
        = -2 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * (m a - m b) * d := by ring
      _ = -2 * (2 : ℝ)⁻¹ * (m a - m b) * d := by
          rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
      _ = -(m a - m b) * d := by ring
  change m i + -(2 * (Real.sqrt 2)⁻¹) * (m a - m b) * ((Real.sqrt 2)⁻¹ * d) =
    m (Equiv.swap a b i)
  rw [hcoeff]
  by_cases hia : i = a
  · subst hia
    simp [d, Pi.single_eq_of_ne hab]
  · by_cases hib : i = b
    · subst hib
      simp [d, Pi.single_eq_of_ne hab.symm]
    · simp [d, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib,
        Equiv.swap_apply_of_ne_of_ne hia hib]

private theorem ι_swapVec_swap {n : ℕ} (a b : Fin n) :
    ι (negForm n) (swapVec b a) = -ι (negForm n) (swapVec a b) := by
  rw [swapVec_swap, map_neg]

private theorem ι_swapVec_mul_self {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    ι (negForm n) (swapVec a b) * ι (negForm n) (swapVec a b) = -1 := by
  rw [CliffordAlgebra.ι_sq_scalar, negForm_swapVec hab, map_neg, map_one]

private theorem ι_swapVec_mul_swap {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    ι (negForm n) (swapVec a b) * ι (negForm n) (swapVec b a) = 1 := by
  rw [ι_swapVec_swap a b, mul_neg, ι_swapVec_mul_self hab, neg_neg]

private theorem ι_swapVec_mul_anticomm {n : ℕ} {a b c d : Fin n}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ι (negForm n) (swapVec c d) * ι (negForm n) (swapVec a b) =
      -(ι (negForm n) (swapVec a b) * ι (negForm n) (swapVec c d)) := by
  have hpol : QuadraticMap.polar (negForm n) (swapVec a b) (swapVec c d) = 0 := by
    rw [polar_negForm_swapVec, swapVec_apply, swapVec_apply,
      Pi.single_eq_of_ne hac, Pi.single_eq_of_ne had,
      Pi.single_eq_of_ne hbc, Pi.single_eq_of_ne hbd]
    ring
  have hadd := CliffordAlgebra.ι_mul_ι_add_swap (Q := negForm n) (swapVec a b) (swapVec c d)
  rw [hpol, map_zero] at hadd
  exact eq_neg_of_add_eq_zero_right hadd

private theorem ι_swapVec_mul_add_swap {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ι (negForm n) (swapVec a b) * ι (negForm n) (swapVec b c) +
      ι (negForm n) (swapVec b c) * ι (negForm n) (swapVec a b) = 1 := by
  have hpol : QuadraticMap.polar (negForm n) (swapVec a b) (swapVec b c) = 1 := by
    rw [polar_negForm_swapVec, swapVec_apply, swapVec_apply,
      Pi.single_eq_of_ne hab, Pi.single_eq_of_ne hac,
      Pi.single_eq_same, Pi.single_eq_of_ne hbc]
    calc -(2 * (Real.sqrt 2)⁻¹) *
          ((Real.sqrt 2)⁻¹ * (0 - 0) - (Real.sqrt 2)⁻¹ * (1 - 0))
        = 2 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) := by ring
      _ = 2 * (2 : ℝ)⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
      _ = 1 := by norm_num
  have hadd := CliffordAlgebra.ι_mul_ι_add_swap (Q := negForm n) (swapVec a b) (swapVec b c)
  rw [hpol, map_one] at hadd
  exact hadd

private theorem ι_swapVec_recut_left_left_a {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ι (negForm n) (swapVec b c) * ι (negForm n) (swapVec a b) =
      -(ι (negForm n) (swapVec a b) * ι (negForm n) (swapVec a c)) := by
  rw [← swapVec_add a b c, map_add, mul_add, ι_swapVec_mul_self hab]
  have h := ι_swapVec_mul_add_swap hab hbc hac
  have h1 : ι (negForm n) (swapVec b c) * ι (negForm n) (swapVec a b) =
      1 - ι (negForm n) (swapVec a b) * ι (negForm n) (swapVec b c) := eq_sub_of_add_eq' h
  rw [h1]
  abel

private theorem ι_swapVec_recut_left_left_b {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) :
    ι (negForm n) (swapVec a c) * ι (negForm n) (swapVec c b) =
      -(ι (negForm n) (swapVec a b) * ι (negForm n) (swapVec a c)) := by
  rw [ι_swapVec_swap b c, mul_neg, ← swapVec_add a b c, map_add, add_mul, mul_add,
    ι_swapVec_mul_self hab, ι_swapVec_mul_self hbc]
  abel

private theorem ι_swapVec_recut_right_right_a {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ι (negForm n) (swapVec c a) * ι (negForm n) (swapVec a b) =
      -(ι (negForm n) (swapVec a b) * ι (negForm n) (swapVec c b)) := by
  rw [ι_swapVec_swap a c, ι_swapVec_swap b c, neg_mul, mul_neg, neg_neg,
    ← swapVec_add a b c, map_add, add_mul, ι_swapVec_mul_self hab]
  have h := ι_swapVec_mul_add_swap hab hbc hac
  have h1 : ι (negForm n) (swapVec b c) * ι (negForm n) (swapVec a b) =
      1 - ι (negForm n) (swapVec a b) * ι (negForm n) (swapVec b c) := eq_sub_of_add_eq' h
  rw [h1]
  abel

private theorem ι_swapVec_recut_right_right_b {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ι (negForm n) (swapVec c b) * ι (negForm n) (swapVec a c) =
      -(ι (negForm n) (swapVec a b) * ι (negForm n) (swapVec c b)) := by
  rw [ι_swapVec_swap b c, neg_mul, mul_neg, neg_neg, ← swapVec_add a b c, map_add, mul_add,
    ι_swapVec_mul_self hbc]
  have h := ι_swapVec_mul_add_swap hab hbc hac
  have h1 : ι (negForm n) (swapVec b c) * ι (negForm n) (swapVec a b) =
      1 - ι (negForm n) (swapVec a b) * ι (negForm n) (swapVec b c) := eq_sub_of_add_eq' h
  rw [h1]
  abel

private theorem ι_swapVec_of_isRecutOfLeftEqLeft {n : ℕ} {x z : GridState n}
    {D E : GridRectangleDecomposition x z} (h : D.IsRecutOfLeftEqLeft E) :
    ι (negForm n) (swapVec E.first.left E.first.right) *
        ι (negForm n) (swapVec E.second.left E.second.right) =
      -(ι (negForm n) (swapVec D.first.left D.first.right) *
        ι (negForm n) (swapVec D.second.left D.second.right)) := by
  have hc := h.side_eq
  obtain ⟨hr₁, hr₂⟩ := h.recut_sides
  rcases h.recut_branch with ⟨hmem, -, hl₁, hl₂⟩ | ⟨hmem, -, hl₁, hl₂⟩
  · have hbc : D.first.right ≠ D.second.right := Grid.ne_right_of_mem_cIoo hmem
    rw [hl₁, hr₁, hl₂, hr₂, ← hc]
    exact ι_swapVec_recut_left_left_a D.first.left_ne_right hbc (hc ▸ D.second.left_ne_right)
  · have hcb : D.second.right ≠ D.first.right := Grid.ne_right_of_mem_cIoo hmem
    rw [hl₁, hr₁, hl₂, hr₂, ← hc]
    exact ι_swapVec_recut_left_left_b D.first.left_ne_right hcb.symm

private theorem ι_swapVec_of_isRecutOfRightEqRight {n : ℕ} {x z : GridState n}
    {D E : GridRectangleDecomposition x z} (h : D.IsRecutOfRightEqRight E) :
    ι (negForm n) (swapVec E.first.left E.first.right) *
        ι (negForm n) (swapVec E.second.left E.second.right) =
      -(ι (negForm n) (swapVec D.first.left D.first.right) *
        ι (negForm n) (swapVec D.second.left D.second.right)) := by
  have hc := h.side_eq
  obtain ⟨hl₁, hl₂⟩ := h.recut_sides
  rcases h.recut_branch with ⟨hmem, -, hr₁, hr₂⟩ | ⟨hmem, -, hr₁, hr₂⟩
  · have hac : D.first.left ≠ D.second.left := Grid.ne_left_of_mem_cIoo hmem
    rw [hl₁, hr₁, hl₂, hr₂, ← hc]
    exact ι_swapVec_recut_right_right_a D.first.left_ne_right
      (hc ▸ D.second.left_ne_right.symm) hac
  · have hca : D.second.left ≠ D.first.left := Grid.ne_left_of_mem_cIoo hmem
    rw [hl₁, hr₁, hl₂, hr₂, ← hc]
    exact ι_swapVec_recut_right_right_b D.first.left_ne_right
      (hc ▸ D.second.left_ne_right.symm) hca.symm

/-! ### Reading signs out of the Pin kernel -/

private theorem coe_eq_one_or_neg_one_of_mem_ker {n : ℕ} [NeZero n]
    (k : MonoidHom.ker (pinToOrthogonal (negForm n))) :
    (k.1 : CliffordAlgebra (negForm n)) = 1 ∨ (k.1 : CliffordAlgebra (negForm n)) = -1 := by
  let e := zmodTwoMulEquivKerPinToOrthogonal (negForm n) (nondegenerate_negForm n)
  have hk : e (e.symm k) = k := e.apply_symm_apply k
  generalize hz : Multiplicative.toAdd (e.symm k) = z
  have hz' : e.symm k = Multiplicative.ofAdd z := by rw [← hz]; rfl
  rw [hz'] at hk
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with rfl | rfl
  · left
    have h1 : k = 1 := by rw [← hk, ofAdd_zero, map_one]
    simp [h1]
  · right
    have hneg : k = e (Multiplicative.ofAdd (1 : ZMod 2)) := hk.symm
    rw [hneg, zmodTwoMulEquivKerPinToOrthogonal_apply_ofAdd_one]
    simp [coe_spinToPin_apply, spinGroup.coe_negOne]

private theorem neg_one_ne_one_clifford {n : ℕ} [NeZero n] :
    (-1 : CliffordAlgebra (negForm n)) ≠ 1 := fun h =>
  spinGroup.negOne_ne_one (negForm n) (nondegenerate_negForm n).ne_zero <|
    Subtype.ext <| by rw [spinGroup.coe_negOne, OneMemClass.coe_one, h]

private theorem units_int_cast_injective {n : ℕ} [NeZero n] {s t : ℤˣ}
    (h : ((s : ℤ) : CliffordAlgebra (negForm n)) = ((t : ℤ) : CliffordAlgebra (negForm n))) :
    s = t := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · rfl
  · exfalso; exact neg_one_ne_one_clifford (by simpa using h.symm)
  · exfalso; exact neg_one_ne_one_clifford (by simpa using h)
  · rfl

private noncomputable def kerToSign {n : ℕ}
    (k : MonoidHom.ker (pinToOrthogonal (negForm n))) : ℤˣ :=
  open Classical in
  if (k.1 : CliffordAlgebra (negForm n)) = 1 then 1 else -1

private theorem int_cast_kerToSign {n : ℕ} [NeZero n]
    (k : MonoidHom.ker (pinToOrthogonal (negForm n))) :
    ((kerToSign k : ℤ) : CliffordAlgebra (negForm n)) = (k.1 : CliffordAlgebra (negForm n)) := by
  classical
  rcases coe_eq_one_or_neg_one_of_mem_ker k with h | h
  · simp [kerToSign, h]
  · simp [kerToSign, h, neg_one_ne_one_clifford]

/-! ### Construction of a grid sign assignment -/

/-- The Pin-group construction of a sign assignment for grid size `n ≥ 1`. -/
private noncomputable def ofNeZero (n : ℕ) [NeZero n] : GridSignAssignment n :=
  let lift : GridState n → pinGroup (negForm n) := fun x =>
    Classical.choose (pinToOrthogonal_surjective_of_negDef (negForm n) (posDef_neg_negForm n)
      (permOrthogonal n x.toPerm))
  have hlift : ∀ x : GridState n,
      pinToOrthogonal (negForm n) (lift x) = permOrthogonal n x.toPerm := fun x =>
    Classical.choose_spec (pinToOrthogonal_surjective_of_negDef (negForm n) (posDef_neg_negForm n)
      (permOrthogonal n x.toPerm))
  let rectKer : ∀ {x y : GridState n}, GridRectangleBetween x y →
      MonoidHom.ker (pinToOrthogonal (negForm n)) := fun {x y} r =>
    ⟨lift x * swapPin r.left_ne_right * (lift y)⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hlift x, hlift y,
        pinToOrthogonal_swapPin, ← map_mul]
      have hy : y.toPerm = x.toPerm * Equiv.swap r.left r.right := by
        ext c
        rw [r.target_toPerm_eq, Equiv.trans_apply, Equiv.Perm.mul_apply]
      rw [hy, mul_inv_cancel]⟩
  have hsign : ∀ {x y : GridState n} (r : GridRectangleBetween x y),
      ((kerToSign (rectKer r) : ℤ) : CliffordAlgebra (negForm n)) =
        (lift x : CliffordAlgebra (negForm n)) *
          ι (negForm n) (swapVec r.left r.right) *
          ((lift y)⁻¹ : pinGroup (negForm n)) := fun r => by
    rw [int_cast_kerToSign]
    simp [rectKer, swapPin]
  have hprod : ∀ {x y z : GridState n}
      (r₁ : GridRectangleBetween x y) (r₂ : GridRectangleBetween y z),
      (((kerToSign (rectKer r₁) * kerToSign (rectKer r₂) : ℤˣ) : ℤ) :
          CliffordAlgebra (negForm n)) =
        (lift x : CliffordAlgebra (negForm n)) *
          (ι (negForm n) (swapVec r₁.left r₁.right) *
            ι (negForm n) (swapVec r₂.left r₂.right)) *
          ((lift z)⁻¹ : pinGroup (negForm n)) := fun {x y z} r₁ r₂ => by
    rw [Units.val_mul, Int.cast_mul, hsign r₁, hsign r₂]
    have hinv : (((lift y)⁻¹ : pinGroup (negForm n)) : CliffordAlgebra (negForm n)) *
        (lift y : CliffordAlgebra (negForm n)) = 1 := by
      rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
    calc (lift x : CliffordAlgebra (negForm n)) * ι (negForm n) (swapVec r₁.left r₁.right) *
            ((lift y)⁻¹ : pinGroup (negForm n)) *
          ((lift y : CliffordAlgebra (negForm n)) * ι (negForm n) (swapVec r₂.left r₂.right) *
            ((lift z)⁻¹ : pinGroup (negForm n)))
        = (lift x : CliffordAlgebra (negForm n)) * ι (negForm n) (swapVec r₁.left r₁.right) *
            ((((lift y)⁻¹ : pinGroup (negForm n)) : CliffordAlgebra (negForm n)) *
              (lift y : CliffordAlgebra (negForm n))) *
            ι (negForm n) (swapVec r₂.left r₂.right) *
            ((lift z)⁻¹ : pinGroup (negForm n)) := by simp only [mul_assoc]
      _ = (lift x : CliffordAlgebra (negForm n)) *
            (ι (negForm n) (swapVec r₁.left r₁.right) *
              ι (negForm n) (swapVec r₂.left r₂.right)) *
            ((lift z)⁻¹ : pinGroup (negForm n)) := by
          rw [hinv, mul_one]
          simp only [mul_assoc]
  have hself : ∀ (x : GridState n),
      (lift x : CliffordAlgebra (negForm n)) * ((lift x)⁻¹ : pinGroup (negForm n)) = 1 :=
    fun x => by rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
  { sign := fun r _ => kerToSign (rectKer r)
    sign_mul_sign_eq_neg := fun {x z} D E hD₁ hD₂ hE₁ _ hne hdomain => by
      refine units_int_cast_injective (n := n) ?_
      rw [Units.val_neg, Int.cast_neg, hprod E.first E.second, hprod D.first D.second]
      suffices hcl :
          ι (negForm n) (swapVec E.first.left E.first.right) *
            ι (negForm n) (swapVec E.second.left E.second.right) =
          -(ι (negForm n) (swapVec D.first.left D.first.right) *
            ι (negForm n) (swapVec D.second.left D.second.right)) by
        rw [hcl, mul_neg, neg_mul]
      rcases D.hasDisjointSides_or_hasOneCommonSide_or_eq with hdisj | hone | rfl
      · rcases D.eq_or_eq_commute_of_hasDisjointSides_of_coveredSquares_add_eq hdisj hdomain with
            rfl | rfl
        · exact absurd rfl hne
        · obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp hdisj
          rw [D.commute_first_left hdisj, D.commute_first_right hdisj,
            D.commute_second_left hdisj, D.commute_second_right hdisj]
          exact ι_swapVec_mul_anticomm hll hlr hrl hrr
      · rcases D.eq_or_isRecut_of_hasOneCommonSide_of_coveredSquares_add_eq hone hD₁ hD₂ hE₁
            hdomain with rfl | hrecut
        · exact absurd rfl hne
        · rcases hrecut.orientation with ho | ho | ho | ho
          · exact ι_swapVec_of_isRecutOfLeftEqLeft ho
          · exact ι_swapVec_of_isRecutOfRightEqRight ho
          · have hmixed := D.hasMixedSideOverlap_iff.mpr ⟨hone, Or.inl ho.side_eq⟩
            rcases hrecut.symm_sameSide_of_hasMixedSideOverlap hmixed hD₁ hD₂ with hE | hE
            · rw [ι_swapVec_of_isRecutOfLeftEqLeft hE, neg_neg]
            · rw [ι_swapVec_of_isRecutOfRightEqRight hE, neg_neg]
          · have hmixed := D.hasMixedSideOverlap_iff.mpr ⟨hone, Or.inr ho.side_eq⟩
            rcases hrecut.symm_sameSide_of_hasMixedSideOverlap hmixed hD₁ hD₂ with hE | hE
            · rw [ι_swapVec_of_isRecutOfLeftEqLeft hE, neg_neg]
            · rw [ι_swapVec_of_isRecutOfRightEqRight hE, neg_neg]
      · exact absurd (D.eq_of_coveredSquares_add_eq_self hdomain) hne
    sign_mul_sign_eq_neg_one_of_left_eq_left := fun {x y} r s _ _ hleft => by
      have hright : s.right = r.right := r.right_eq_right_of_left_eq_left s hleft
      refine units_int_cast_injective (n := n) ?_
      rw [hprod r s, hleft, hright, ι_swapVec_mul_self r.left_ne_right, mul_neg, mul_one, neg_mul,
        hself x, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    sign_mul_sign_eq_one_of_left_eq_right := fun {x y} r s _ _ hleft => by
      have hright : s.right = r.left := r.right_eq_left_of_left_eq_right s hleft
      refine units_int_cast_injective (n := n) ?_
      rw [hprod r s, hleft, hright, ι_swapVec_mul_swap r.left_ne_right, mul_one, hself x,
        Units.val_one, Int.cast_one] }

/-- Every grid size admits a sign assignment. -/
instance instNonempty (n : ℕ) : Nonempty (GridSignAssignment n) := by
  cases n with
  | zero =>
    exact ⟨{
      sign := fun r _ => Fin.elim0 r.left
      sign_mul_sign_eq_neg := fun D _ _ _ _ _ _ _ => Fin.elim0 D.first.left
      sign_mul_sign_eq_neg_one_of_left_eq_left := fun r _ _ _ _ => Fin.elim0 r.left
      sign_mul_sign_eq_one_of_left_eq_right := fun r _ _ _ _ => Fin.elim0 r.left }⟩
  | succ k =>
    exact ⟨ofNeZero (k + 1)⟩

end GridSignAssignment

end TauCeti
