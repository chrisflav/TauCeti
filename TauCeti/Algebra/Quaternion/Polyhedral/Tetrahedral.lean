/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.Algebra.Quaternion.NormForm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import TauCeti.Algebra.Group.Subgroup.Closure

/-!
# The binary tetrahedral group in unit-quaternion coordinates

The **Hurwitz units** in Hamilton's real quaternions `ℍ[ℝ]` are the `24` unit quaternions consisting
of:

* the `8` signed basis units `(±1, 0, 0, 0)` and their coordinate permutations (`±1, ±i, ±j, ±k`),
  cut out by `Quaternion.IsSignedBasisUnit`;
* the `16` half-integer points `(±1 ± i ± j ± k) / 2`, cut out by `Quaternion.IsHalfUnit`.

Together they satisfy `Quaternion.IsTetrahedralUnit` and form the **binary tetrahedral subgroup**
`TauCeti.binaryTetrahedralUnitSubgroup` of `unitary ℍ[ℝ]` of exact order `24`.

We record both the coordinate generators `i`, `j`, `ω = (1 + i + j + k) / 2` and the `<2, 3, 3>`
presentation generators `ω = (1 + i + j + k) / 2` and `τ = (1 + i + j - k) / 2`, which satisfy
`ω ^ 3 = τ ^ 3 = (ω * τ) ^ 2 = -1` and are related to the coordinate units by `ω * τ = j` and
`τ * ω = i`.

## Main definitions

* `Quaternion.IsSignedBasisUnit`: coordinate permutations of `(±1, 0, 0, 0)` in `ℍ[ℝ]`.
* `Quaternion.IsHalfUnit`: the `16` quaternions `(±1 ± i ± j ± k) / 2` in `ℍ[ℝ]`.
* `Quaternion.IsTetrahedralUnit`: their union, the `24` Hurwitz unit quaternions.
* `TauCeti.quaternionUnitI`, `TauCeti.quaternionUnitJ`, `TauCeti.quaternionUnitK`: the imaginary
  basis units in `unitary ℍ[ℝ]`.
* `TauCeti.tetrahedralOmega`, `TauCeti.tetrahedralTau`: the `<2, 3, 3>` generators
  `(1 + i + j + k) / 2` and `(1 + i + j - k) / 2` in `unitary ℍ[ℝ]`.
* `TauCeti.binaryTetrahedralUnitSubgroup`: the binary tetrahedral subgroup of `unitary ℍ[ℝ]`.

## References

* J. H. Conway and D. A. Smith, *On Quaternions and Octonions*, A K Peters, 2003, §6.5.
-/

public section

open scoped Quaternion

namespace Quaternion

/-! ### Signed basis units and half-integer units -/

/-- A quaternion in `ℍ[ℝ]` is a **signed basis unit** if one of its four coordinates is `±1` and
the other three vanish; equivalently, its coordinate tuple is a permutation of `(±1, 0, 0, 0)`. -/
def IsSignedBasisUnit (q : ℍ[ℝ]) : Prop :=
  ∃ r : Fin 4, (equivTuple ℝ q r = 1 ∨ equivTuple ℝ q r = -1) ∧
    ∀ s : Fin 4, s ≠ r → equivTuple ℝ q s = 0

theorem isSignedBasisUnit_def (q : ℍ[ℝ]) :
    q.IsSignedBasisUnit ↔ ∃ r : Fin 4, (equivTuple ℝ q r = 1 ∨ equivTuple ℝ q r = -1) ∧
      ∀ s : Fin 4, s ≠ r → equivTuple ℝ q s = 0 := Iff.rfl

theorem isSignedBasisUnit_iff_coordinates {q : ℍ[ℝ]} :
    q.IsSignedBasisUnit ↔
      ((q.re = 1 ∨ q.re = -1) ∧ q.imI = 0 ∧ q.imJ = 0 ∧ q.imK = 0) ∨
      (q.re = 0 ∧ (q.imI = 1 ∨ q.imI = -1) ∧ q.imJ = 0 ∧ q.imK = 0) ∨
      (q.re = 0 ∧ q.imI = 0 ∧ (q.imJ = 1 ∨ q.imJ = -1) ∧ q.imK = 0) ∨
      (q.re = 0 ∧ q.imI = 0 ∧ q.imJ = 0 ∧ (q.imK = 1 ∨ q.imK = -1)) := by
  constructor
  · rintro ⟨r, hr, h0⟩
    fin_cases r
    · exact .inl ⟨by simpa using hr, by simpa using h0 1 (by decide),
        by simpa using h0 2 (by decide), by simpa using h0 3 (by decide)⟩
    · exact .inr (.inl ⟨by simpa using h0 0 (by decide), by simpa using hr,
        by simpa using h0 2 (by decide), by simpa using h0 3 (by decide)⟩)
    · exact .inr (.inr (.inl ⟨by simpa using h0 0 (by decide),
        by simpa using h0 1 (by decide), by simpa using hr,
        by simpa using h0 3 (by decide)⟩))
    · exact .inr (.inr (.inr ⟨by simpa using h0 0 (by decide),
        by simpa using h0 1 (by decide), by simpa using h0 2 (by decide),
        by simpa using hr⟩))
  · rintro (⟨hr, h1, h2, h3⟩ | ⟨h0, hr, h2, h3⟩ | ⟨h0, h1, hr, h3⟩ | ⟨h0, h1, h2, hr⟩)
    · exact ⟨0, by simpa using hr, fun s hs => by fin_cases s <;> simp_all⟩
    · exact ⟨1, by simpa using hr, fun s hs => by fin_cases s <;> simp_all⟩
    · exact ⟨2, by simpa using hr, fun s hs => by fin_cases s <;> simp_all⟩
    · exact ⟨3, by simpa using hr, fun s hs => by fin_cases s <;> simp_all⟩

private theorem comp_swap_eq_vec4_of_single {v : Fin 4 → ℝ} {r : Fin 4} {c : ℝ}
    (hr : v r = c) (h0 : ∀ s : Fin 4, s ≠ r → v s = 0) :
    v ∘ Equiv.swap 0 r = ![c, 0, 0, 0] := by
  ext s
  fin_cases s
  · simpa using hr
  · by_cases h : r = 1
    · subst h; simpa using h0 0 (by decide)
    · simpa [Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 4) ≠ 0) (Ne.symm h)] using
        h0 1 (Ne.symm h)
  · by_cases h : r = 2
    · subst h; simpa using h0 0 (by decide)
    · simpa [Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 4) ≠ 0) (Ne.symm h)] using
        h0 2 (Ne.symm h)
  · by_cases h : r = 3
    · subst h; simpa using h0 0 (by decide)
    · simpa [Equiv.swap_apply_of_ne_of_ne (by decide : (3 : Fin 4) ≠ 0) (Ne.symm h)] using
        h0 3 (Ne.symm h)

private theorem eq_zero_of_comp_perm_eq_vec4 {v : Fin 4 → ℝ} {σ : Equiv.Perm (Fin 4)} {c : ℝ}
    (hσ : v ∘ σ = ![c, 0, 0, 0]) {s : Fin 4} (hs : s ≠ σ 0) : v s = 0 := by
  have hne : σ.symm s ≠ 0 := fun h => hs (by simpa using congrArg σ h)
  have hval := congrFun hσ (σ.symm s)
  rw [Function.comp_apply, σ.apply_symm_apply] at hval
  rcases hidx : σ.symm s with ⟨_ | _ | _ | _, hlt⟩
  · exact absurd hidx hne
  · simpa [hidx] using hval
  · simpa [hidx] using hval
  · simpa [hidx] using hval

/-- A quaternion is a signed basis unit if and only if its coordinate tuple is a coordinate
permutation of `(1, 0, 0, 0)` or `(-1, 0, 0, 0)`. -/
theorem isSignedBasisUnit_iff_exists_perm {q : ℍ[ℝ]} :
    q.IsSignedBasisUnit ↔ ∃ σ : Equiv.Perm (Fin 4),
      equivTuple ℝ q ∘ σ = ![1, 0, 0, 0] ∨ equivTuple ℝ q ∘ σ = ![-1, 0, 0, 0] := by
  constructor
  · rintro ⟨r, hr | hr, h0⟩
    · exact ⟨Equiv.swap 0 r, .inl (comp_swap_eq_vec4_of_single hr h0)⟩
    · exact ⟨Equiv.swap 0 r, .inr (comp_swap_eq_vec4_of_single hr h0)⟩
  · rintro ⟨σ, hσ | hσ⟩
    · exact ⟨σ 0, .inl (by simpa using congrFun hσ 0), fun s hs =>
        eq_zero_of_comp_perm_eq_vec4 hσ hs⟩
    · exact ⟨σ 0, .inr (by simpa using congrFun hσ 0), fun s hs =>
        eq_zero_of_comp_perm_eq_vec4 hσ hs⟩

/-- Explicit parametrization of the `8` signed basis units by coordinate index and sign. -/
noncomputable def signedBasisUnit (p : Fin 4 × Bool) : ℍ[ℝ] :=
  (equivTuple ℝ).symm (Pi.single p.1 (if p.2 then (-1 : ℝ) else 1))

theorem equivTuple_signedBasisUnit (p : Fin 4 × Bool) :
    equivTuple ℝ (signedBasisUnit p) = Pi.single p.1 (if p.2 then (-1 : ℝ) else 1) :=
  (equivTuple ℝ).apply_symm_apply _

theorem injective_signedBasisUnit : Function.Injective signedBasisUnit := by
  rintro ⟨r₁, b₁⟩ ⟨r₂, b₂⟩ h
  have ht := congrArg (equivTuple ℝ) h
  rw [equivTuple_signedBasisUnit, equivTuple_signedBasisUnit] at ht
  have hr : r₁ = r₂ := by
    by_contra hne
    have hval := congrFun ht r₁
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hval
    cases b₁ <;> norm_num at hval
  subst hr
  have hb := congrFun ht r₁
  rw [Pi.single_eq_same, Pi.single_eq_same] at hb
  cases b₁ <;> cases b₂ <;> first | rfl | norm_num at hb

@[simp]
theorem isSignedBasisUnit_signedBasisUnit (p : Fin 4 × Bool) :
    (signedBasisUnit p).IsSignedBasisUnit := by
  refine ⟨p.1, ?_, fun s hs => ?_⟩
  · rw [equivTuple_signedBasisUnit, Pi.single_eq_same]
    cases p.2 <;> simp
  · rw [equivTuple_signedBasisUnit, Pi.single_eq_of_ne hs]

theorem range_signedBasisUnit :
    Set.range signedBasisUnit = {q : ℍ[ℝ] | q.IsSignedBasisUnit} := by
  ext q
  refine ⟨?_, fun ⟨r, hr, h0⟩ => ?_⟩
  · rintro ⟨p, rfl⟩
    exact isSignedBasisUnit_signedBasisUnit p
  · rcases hr with hr | hr
    · refine ⟨(r, false), (equivTuple ℝ).injective ?_⟩
      rw [equivTuple_signedBasisUnit]
      ext s
      by_cases hs : s = r
      · subst hs; simp [hr]
      · rw [Pi.single_eq_of_ne hs, h0 s hs]
    · refine ⟨(r, true), (equivTuple ℝ).injective ?_⟩
      rw [equivTuple_signedBasisUnit]
      ext s
      by_cases hs : s = r
      · subst hs; simp [hr]
      · rw [Pi.single_eq_of_ne hs, h0 s hs]

theorem exists_signedBasisUnit_of_isSignedBasisUnit {q : ℍ[ℝ]} (hq : q.IsSignedBasisUnit) :
    ∃ p : Fin 4 × Bool, signedBasisUnit p = q :=
  Set.ext_iff.mp range_signedBasisUnit q |>.mpr hq

theorem finite_isSignedBasisUnit : {q : ℍ[ℝ] | q.IsSignedBasisUnit}.Finite := by
  rw [← range_signedBasisUnit]
  exact Set.finite_range _

/-- There are `8` distinct signed basis units in `ℍ[ℝ]`. -/
@[simp]
theorem ncard_isSignedBasisUnit : {q : ℍ[ℝ] | q.IsSignedBasisUnit}.ncard = 8 := by
  rw [← range_signedBasisUnit, Set.ncard_range_of_injective injective_signedBasisUnit]
  simp

/-- A quaternion in `ℍ[ℝ]` is a **half-integer unit** if each of its four coordinates is `±1/2`,
that is, `q = (±1 ± i ± j ± k) / 2`. -/
def IsHalfUnit (q : ℍ[ℝ]) : Prop :=
  ∀ r : Fin 4, equivTuple ℝ q r = 1 / 2 ∨ equivTuple ℝ q r = -(1 / 2)

theorem isHalfUnit_def (q : ℍ[ℝ]) :
    q.IsHalfUnit ↔ ∀ r : Fin 4, equivTuple ℝ q r = 1 / 2 ∨ equivTuple ℝ q r = -(1 / 2) := Iff.rfl

theorem isHalfUnit_iff_coordinates {q : ℍ[ℝ]} :
    q.IsHalfUnit ↔
      (q.re = 1 / 2 ∨ q.re = -(1 / 2)) ∧
      (q.imI = 1 / 2 ∨ q.imI = -(1 / 2)) ∧
      (q.imJ = 1 / 2 ∨ q.imJ = -(1 / 2)) ∧
      (q.imK = 1 / 2 ∨ q.imK = -(1 / 2)) := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2, by simpa using h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ r
    fin_cases r
    · exact h0
    · exact h1
    · exact h2
    · exact h3

/-- Explicit parametrization of the `16` half-integer units `(±1 ± i ± j ± k) / 2`. -/
noncomputable def halfUnit (s : Fin 4 → Bool) : ℍ[ℝ] :=
  (equivTuple ℝ).symm fun r => if s r then -(1 / 2 : ℝ) else 1 / 2

theorem equivTuple_halfUnit (s : Fin 4 → Bool) :
    equivTuple ℝ (halfUnit s) = fun r => if s r then -(1 / 2 : ℝ) else 1 / 2 :=
  (equivTuple ℝ).apply_symm_apply _

theorem injective_halfUnit : Function.Injective halfUnit := by
  intro s₁ s₂ h
  have ht := congrArg (equivTuple ℝ) h
  rw [equivTuple_halfUnit, equivTuple_halfUnit] at ht
  ext r
  have hr : (if s₁ r then -(1 / 2 : ℝ) else 1 / 2) = if s₂ r then -(1 / 2) else 1 / 2 :=
    congrFun ht r
  cases h1 : s₁ r <;> cases h2 : s₂ r
  · rfl
  · rw [h1, h2] at hr; norm_num at hr
  · rw [h1, h2] at hr; norm_num at hr
  · rfl

@[simp]
theorem isHalfUnit_halfUnit (s : Fin 4 → Bool) : (halfUnit s).IsHalfUnit := fun r => by
  rw [equivTuple_halfUnit]
  cases h : s r
  · exact .inl (by simp [h])
  · exact .inr (by simp [h])

theorem range_halfUnit : Set.range halfUnit = {q : ℍ[ℝ] | q.IsHalfUnit} := by
  ext q
  refine ⟨?_, fun hq => ?_⟩
  · rintro ⟨s, rfl⟩
    exact isHalfUnit_halfUnit s
  · classical
    refine ⟨fun r => decide (equivTuple ℝ q r = -(1 / 2)), (equivTuple ℝ).injective ?_⟩
    rw [equivTuple_halfUnit]
    ext r
    rcases hq r with hr | hr <;> norm_num [hr]

theorem finite_isHalfUnit : {q : ℍ[ℝ] | q.IsHalfUnit}.Finite := by
  rw [← range_halfUnit]
  exact Set.finite_range _

/-- There are `16` distinct half-integer units `(±1 ± i ± j ± k) / 2` in `ℍ[ℝ]`. -/
@[simp]
theorem ncard_isHalfUnit : {q : ℍ[ℝ] | q.IsHalfUnit}.ncard = 16 := by
  rw [← range_halfUnit, Set.ncard_range_of_injective injective_halfUnit]
  simp

theorem disjoint_isSignedBasisUnit_isHalfUnit :
    Disjoint {q : ℍ[ℝ] | q.IsSignedBasisUnit} {q : ℍ[ℝ] | q.IsHalfUnit} := by
  rw [Set.disjoint_left]
  rintro q ⟨r, hr | hr, -⟩ hhalf <;> rcases hhalf r with hh | hh <;> linarith

/-! ### The 24 Hurwitz tetrahedral units -/

/-- A quaternion in `ℍ[ℝ]` is a **tetrahedral unit** (Hurwitz unit) if it is either one of the `8`
signed basis units or one of the `16` half-integer units `(±1 ± i ± j ± k) / 2`. -/
def IsTetrahedralUnit (q : ℍ[ℝ]) : Prop :=
  q.IsSignedBasisUnit ∨ q.IsHalfUnit

theorem isTetrahedralUnit_def (q : ℍ[ℝ]) :
    q.IsTetrahedralUnit ↔ q.IsSignedBasisUnit ∨ q.IsHalfUnit := Iff.rfl

theorem finite_isTetrahedralUnit : {q : ℍ[ℝ] | q.IsTetrahedralUnit}.Finite :=
  finite_isSignedBasisUnit.union finite_isHalfUnit

/-- **The 24 Hurwitz tetrahedral units are pairwise distinct.** -/
@[simp]
theorem ncard_isTetrahedralUnit : {q : ℍ[ℝ] | q.IsTetrahedralUnit}.ncard = 24 := by
  have heq : {q : ℍ[ℝ] | q.IsTetrahedralUnit} =
      {q : ℍ[ℝ] | q.IsSignedBasisUnit} ∪ {q : ℍ[ℝ] | q.IsHalfUnit} := rfl
  rw [heq, Set.ncard_union_eq disjoint_isSignedBasisUnit_isHalfUnit
    finite_isSignedBasisUnit finite_isHalfUnit, ncard_isSignedBasisUnit, ncard_isHalfUnit]

/-- Every coordinate square of a tetrahedral unit lies in `{0, 1/4, 1}`. -/
theorem IsTetrahedralUnit.coord_sq_mem {q : ℍ[ℝ]} (hq : q.IsTetrahedralUnit) (r : Fin 4) :
    (equivTuple ℝ q r) ^ 2 = 0 ∨ (equivTuple ℝ q r) ^ 2 = 1 / 4 ∨ (equivTuple ℝ q r) ^ 2 = 1 := by
  rcases hq with ⟨s, hs, h0⟩ | hhalf
  · by_cases hrs : r = s
    · subst hrs
      rcases hs with h | h <;> right <;> right <;> rw [h] <;> norm_num
    · left
      rw [h0 r hrs]
      norm_num
  · rcases hhalf r with h | h <;> right <;> left <;> rw [h] <;> norm_num

/-- Every tetrahedral unit has reduced norm one. -/
theorem IsTetrahedralUnit.normSq_eq_one {q : ℍ[ℝ]} (hq : q.IsTetrahedralUnit) : q.normSq = 1 := by
  rcases hq with hbasis | hhalf
  · obtain ⟨⟨r, b⟩, rfl⟩ := exists_signedBasisUnit_of_isSignedBasisUnit hbasis
    rw [normSq_def']
    fin_cases r <;> cases b <;> norm_num [signedBasisUnit]
  · rcases q with ⟨a, b, c, d⟩
    obtain ⟨rfl | rfl, rfl | rfl, rfl | rfl, rfl | rfl⟩ :=
      isHalfUnit_iff_coordinates.mp hhalf <;>
      · rw [normSq_def']; norm_num

/-- Every tetrahedral unit belongs to `unitary ℍ[ℝ]`. -/
theorem IsTetrahedralUnit.mem_unitary {q : ℍ[ℝ]} (hq : q.IsTetrahedralUnit) :
    q ∈ unitary ℍ[ℝ] :=
  (mem_unitary_iff_normSq_eq_one q).mpr hq.normSq_eq_one

theorem IsTetrahedralUnit.one : (1 : ℍ[ℝ]).IsTetrahedralUnit :=
  .inl (isSignedBasisUnit_iff_coordinates.mpr (by simp))

theorem IsTetrahedralUnit.neg {q : ℍ[ℝ]} (hq : q.IsTetrahedralUnit) : (-q).IsTetrahedralUnit := by
  rcases q with ⟨a, b, c, d⟩
  rcases hq with hbasis | hhalf
  · left
    rw [isSignedBasisUnit_iff_coordinates] at hbasis ⊢
    rcases hbasis with ⟨rfl | rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl | rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩ <;> norm_num
  · right
    obtain ⟨rfl | rfl, rfl | rfl, rfl | rfl, rfl | rfl⟩ :=
      isHalfUnit_iff_coordinates.mp hhalf <;>
      · rw [isHalfUnit_iff_coordinates]; norm_num

theorem IsTetrahedralUnit.star {q : ℍ[ℝ]} (hq : q.IsTetrahedralUnit) :
    (Star.star q).IsTetrahedralUnit := by
  rcases q with ⟨a, b, c, d⟩
  rcases hq with hbasis | hhalf
  · left
    rw [isSignedBasisUnit_iff_coordinates] at hbasis ⊢
    rcases hbasis with ⟨rfl | rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl | rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩ <;> norm_num
  · right
    obtain ⟨rfl | rfl, rfl | rfl, rfl | rfl, rfl | rfl⟩ :=
      isHalfUnit_iff_coordinates.mp hhalf <;>
      · rw [isHalfUnit_iff_coordinates]; norm_num

end Quaternion

namespace TauCeti

/-! ### Coordinate and `<2, 3, 3>` presentation generators -/

/-- The quaternion unit `i` as an element of `unitary ℍ[ℝ]`. -/
noncomputable def quaternionUnitI : unitary ℍ[ℝ] :=
  ⟨⟨0, 1, 0, 0⟩, (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr
    (by rw [Quaternion.normSq_def']; norm_num)⟩

/-- The quaternion unit `j` as an element of `unitary ℍ[ℝ]`. -/
noncomputable def quaternionUnitJ : unitary ℍ[ℝ] :=
  ⟨⟨0, 0, 1, 0⟩, (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr
    (by rw [Quaternion.normSq_def']; norm_num)⟩

/-- The quaternion unit `k` as an element of `unitary ℍ[ℝ]`. -/
noncomputable def quaternionUnitK : unitary ℍ[ℝ] :=
  ⟨⟨0, 0, 0, 1⟩, (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr
    (by rw [Quaternion.normSq_def']; norm_num)⟩

/-- The Hurwitz generator `ω = (1 + i + j + k) / 2` in `unitary ℍ[ℝ]`. -/
noncomputable def tetrahedralOmega : unitary ℍ[ℝ] :=
  ⟨⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩, (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr
    (by rw [Quaternion.normSq_def']; norm_num)⟩

/-- The second `<2, 3, 3>` generator `τ = (1 + i + j - k) / 2` in `unitary ℍ[ℝ]`. -/
noncomputable def tetrahedralTau : unitary ℍ[ℝ] :=
  ⟨⟨1 / 2, 1 / 2, 1 / 2, -(1 / 2)⟩, (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr
    (by rw [Quaternion.normSq_def']; norm_num)⟩

@[simp]
theorem coe_quaternionUnitI : (quaternionUnitI : ℍ[ℝ]) = ⟨0, 1, 0, 0⟩ := (rfl)

@[simp]
theorem coe_quaternionUnitJ : (quaternionUnitJ : ℍ[ℝ]) = ⟨0, 0, 1, 0⟩ := (rfl)

@[simp]
theorem coe_quaternionUnitK : (quaternionUnitK : ℍ[ℝ]) = ⟨0, 0, 0, 1⟩ := (rfl)

@[simp]
theorem coe_tetrahedralOmega :
    (tetrahedralOmega : ℍ[ℝ]) = ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ := (rfl)

@[simp]
theorem coe_tetrahedralTau :
    (tetrahedralTau : ℍ[ℝ]) = ⟨1 / 2, 1 / 2, 1 / 2, -(1 / 2)⟩ := (rfl)

@[simp]
theorem quaternionUnitI_mul_quaternionUnitJ :
    quaternionUnitI * quaternionUnitJ = quaternionUnitK := by
  ext <;> norm_num [coe_quaternionUnitI, coe_quaternionUnitJ, coe_quaternionUnitK]

@[simp]
theorem quaternionUnitI_sq : quaternionUnitI ^ 2 = -1 := by
  refine Subtype.ext ?_
  ext <;> norm_num [sq, Unitary.coe_neg, coe_quaternionUnitI]

@[simp]
theorem quaternionUnitJ_sq : quaternionUnitJ ^ 2 = -1 := by
  refine Subtype.ext ?_
  ext <;> norm_num [sq, Unitary.coe_neg, coe_quaternionUnitJ]

/-- The `<2, 3, 3>` generators recover `j` via `ω * τ = j`. -/
@[simp]
theorem tetrahedralOmega_mul_tetrahedralTau :
    tetrahedralOmega * tetrahedralTau = quaternionUnitJ := by
  ext <;> norm_num [coe_tetrahedralOmega, coe_tetrahedralTau, coe_quaternionUnitJ]

/-- Reversing the `<2, 3, 3>` generators recovers `i` via `τ * ω = i`. -/
@[simp]
theorem tetrahedralTau_mul_tetrahedralOmega :
    tetrahedralTau * tetrahedralOmega = quaternionUnitI := by
  ext <;> norm_num [coe_tetrahedralOmega, coe_tetrahedralTau, coe_quaternionUnitI]

/-- Conjugation by `ω` sends `i` to `j`: `ω * i * ω⁻¹ = j`. -/
theorem tetrahedralOmega_conj_quaternionUnitI :
    tetrahedralOmega * quaternionUnitI * tetrahedralOmega⁻¹ = quaternionUnitJ := by
  rw [← tetrahedralTau_mul_tetrahedralOmega, mul_assoc, mul_assoc tetrahedralTau,
    mul_inv_cancel, mul_one, tetrahedralOmega_mul_tetrahedralTau]

theorem tetrahedralOmega_sq :
    (tetrahedralOmega ^ 2 : unitary ℍ[ℝ]).val = ⟨-(1 / 2), 1 / 2, 1 / 2, 1 / 2⟩ := by
  ext <;> norm_num [sq, coe_tetrahedralOmega]

/-- The `<2, 3, 3>` relation `ω ^ 3 = -1`. -/
@[simp]
theorem tetrahedralOmega_pow_three : tetrahedralOmega ^ 3 = -1 := by
  refine Subtype.ext ?_
  ext <;> norm_num [pow_succ, Unitary.coe_neg, coe_tetrahedralOmega]

/-- The `<2, 3, 3>` relation `τ ^ 3 = -1`. -/
@[simp]
theorem tetrahedralTau_pow_three : tetrahedralTau ^ 3 = -1 := by
  refine Subtype.ext ?_
  ext <;> norm_num [pow_succ, Unitary.coe_neg, coe_tetrahedralTau]

/-- The `<2, 3, 3>` relation `(ω * τ) ^ 2 = -1`. -/
theorem tetrahedralOmega_mul_tetrahedralTau_sq :
    (tetrahedralOmega * tetrahedralTau) ^ 2 = -1 := by
  rw [tetrahedralOmega_mul_tetrahedralTau, quaternionUnitJ_sq]

@[simp]
theorem orderOf_quaternionUnitJ : orderOf quaternionUnitJ = 4 := by
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ fun p hp hdiv => ?_
  · rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, quaternionUnitJ_sq]
    norm_num
  · have hle := Nat.le_of_dvd (by norm_num) hdiv
    have hpge := hp.two_le
    interval_cases p
    · intro h
      have hre := congrArg (fun u : unitary ℍ[ℝ] => (u : ℍ[ℝ]).re) h
      rw [show (4 / 2 : ℕ) = 2 by norm_num, quaternionUnitJ_sq] at hre
      norm_num [Unitary.coe_neg] at hre
    · norm_num at hdiv
    · exact absurd hp (by decide)

/-- The generator `ω` has exact order `6`. -/
@[simp]
theorem orderOf_tetrahedralOmega : orderOf tetrahedralOmega = 6 := by
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ fun p hp hdiv => ?_
  · rw [show (6 : ℕ) = 3 * 2 by rfl, pow_mul, tetrahedralOmega_pow_three]
    norm_num
  · have hle := Nat.le_of_dvd (by norm_num) hdiv
    have hpge := hp.two_le
    interval_cases p
    · intro h
      have hre := congrArg (fun u : unitary ℍ[ℝ] => (u : ℍ[ℝ]).re) h
      rw [show (6 / 2 : ℕ) = 3 by norm_num, tetrahedralOmega_pow_three] at hre
      norm_num [Unitary.coe_neg] at hre
    · intro h
      have hre := congrArg (fun u : unitary ℍ[ℝ] => (u : ℍ[ℝ]).re) h
      rw [show (6 / 3 : ℕ) = 2 by norm_num, tetrahedralOmega_sq] at hre
      norm_num at hre
    · exact absurd hp (by decide)
    · norm_num at hdiv
    · exact absurd hp (by decide)

/-- The generator `τ` has exact order `6`. -/
@[simp]
theorem orderOf_tetrahedralTau : orderOf tetrahedralTau = 6 := by
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ fun p hp hdiv => ?_
  · rw [show (6 : ℕ) = 3 * 2 by rfl, pow_mul, tetrahedralTau_pow_three]
    norm_num
  · have hle := Nat.le_of_dvd (by norm_num) hdiv
    have hpge := hp.two_le
    interval_cases p
    · intro h
      have hre := congrArg (fun u : unitary ℍ[ℝ] => (u : ℍ[ℝ]).re) h
      rw [show (6 / 2 : ℕ) = 3 by norm_num, tetrahedralTau_pow_three] at hre
      norm_num [Unitary.coe_neg] at hre
    · intro h
      have hre := congrArg (fun u : unitary ℍ[ℝ] => (u : ℍ[ℝ]).re) h
      norm_num [sq, coe_tetrahedralTau] at hre
    · exact absurd hp (by decide)
    · norm_num at hdiv
    · exact absurd hp (by decide)

/-! ### Closure and the binary tetrahedral subgroup -/

private theorem isTetrahedralUnit_tetrahedralOmega_mul {q : ℍ[ℝ]} (hq : q.IsTetrahedralUnit) :
    ((tetrahedralOmega : ℍ[ℝ]) * q).IsTetrahedralUnit := by
  rcases q with ⟨a, b, c, d⟩
  rw [Quaternion.isTetrahedralUnit_def, Quaternion.isSignedBasisUnit_iff_coordinates,
    Quaternion.isHalfUnit_iff_coordinates] at hq ⊢
  rcases hq with (⟨rfl | rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl | rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl | rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩) |
    ⟨rfl | rfl, rfl | rfl, rfl | rfl, rfl | rfl⟩ <;>
    norm_num [coe_tetrahedralOmega]

private theorem isTetrahedralUnit_tetrahedralTau_mul {q : ℍ[ℝ]} (hq : q.IsTetrahedralUnit) :
    ((tetrahedralTau : ℍ[ℝ]) * q).IsTetrahedralUnit := by
  rcases q with ⟨a, b, c, d⟩
  rw [Quaternion.isTetrahedralUnit_def, Quaternion.isSignedBasisUnit_iff_coordinates,
    Quaternion.isHalfUnit_iff_coordinates] at hq ⊢
  rcases hq with (⟨rfl | rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl | rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl | rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩) |
    ⟨rfl | rfl, rfl | rfl, rfl | rfl, rfl | rfl⟩ <;>
    norm_num [coe_tetrahedralTau]

private theorem signedBasis_mem_closure_omega_tau {u : unitary ℍ[ℝ]}
    (hu : (u : ℍ[ℝ]).IsSignedBasisUnit) :
    u ∈ Subgroup.closure ({tetrahedralOmega, tetrahedralTau} : Set (unitary ℍ[ℝ])) := by
  have hω : tetrahedralOmega ∈ Subgroup.closure {tetrahedralOmega, tetrahedralTau} :=
    Subgroup.subset_closure (by simp)
  have hτ : tetrahedralTau ∈ Subgroup.closure {tetrahedralOmega, tetrahedralTau} :=
    Subgroup.subset_closure (by simp)
  have hj : quaternionUnitJ ∈ Subgroup.closure {tetrahedralOmega, tetrahedralTau} :=
    tetrahedralOmega_mul_tetrahedralTau ▸ mul_mem hω hτ
  have hi : quaternionUnitI ∈ Subgroup.closure {tetrahedralOmega, tetrahedralTau} :=
    tetrahedralTau_mul_tetrahedralOmega ▸ mul_mem hτ hω
  have hk : quaternionUnitK ∈ Subgroup.closure {tetrahedralOmega, tetrahedralTau} :=
    quaternionUnitI_mul_quaternionUnitJ ▸ mul_mem hi hj
  have hneg1 : (-1 : unitary ℍ[ℝ]) ∈ Subgroup.closure {tetrahedralOmega, tetrahedralTau} :=
    tetrahedralOmega_pow_three ▸ pow_mem hω 3
  obtain ⟨⟨r, b⟩, hval⟩ := Quaternion.exists_signedBasisUnit_of_isSignedBasisUnit hu
  fin_cases r <;> cases b
  · convert one_mem (Subgroup.closure {tetrahedralOmega, tetrahedralTau})
    exact Subtype.ext (hval.symm.trans (by ext <;> norm_num [Quaternion.signedBasisUnit]))
  · convert hneg1
    exact Subtype.ext (hval.symm.trans
      (by ext <;> norm_num [Quaternion.signedBasisUnit, Unitary.coe_neg]))
  · convert hi
    exact Subtype.ext (hval.symm.trans (by ext <;> norm_num [Quaternion.signedBasisUnit]))
  · convert mul_mem hneg1 hi
    exact Subtype.ext (hval.symm.trans
      (by ext <;> norm_num [Quaternion.signedBasisUnit, Unitary.coe_neg]))
  · convert hj
    exact Subtype.ext (hval.symm.trans (by ext <;> norm_num [Quaternion.signedBasisUnit]))
  · convert mul_mem hneg1 hj
    exact Subtype.ext (hval.symm.trans
      (by ext <;> norm_num [Quaternion.signedBasisUnit, Unitary.coe_neg]))
  · convert hk
    exact Subtype.ext (hval.symm.trans (by ext <;> norm_num [Quaternion.signedBasisUnit]))
  · convert mul_mem hneg1 hk
    exact Subtype.ext (hval.symm.trans
      (by ext <;> norm_num [Quaternion.signedBasisUnit, Unitary.coe_neg]))

private theorem coe_closure_tetrahedralOmega_tetrahedralTau :
    (Subgroup.closure ({tetrahedralOmega, tetrahedralTau} : Set (unitary ℍ[ℝ])) :
      Set (unitary ℍ[ℝ])) = {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsTetrahedralUnit} := by
  have hfin : {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsTetrahedralUnit}.Finite :=
    Quaternion.finite_isTetrahedralUnit.preimage Subtype.val_injective.injOn
  refine Subgroup.coe_closure_eq_of_forall_mul_mem hfin Quaternion.IsTetrahedralUnit.one
    (fun u hu => ?_) (fun s hs t ht => ?_)
  · have hω : tetrahedralOmega ∈ Subgroup.closure {tetrahedralOmega, tetrahedralTau} :=
      Subgroup.subset_closure (by simp)
    rcases hu with hbasis | hhalf
    · exact signedBasis_mem_closure_omega_tau hbasis
    · rcases isTetrahedralUnit_tetrahedralOmega_mul (.inr hhalf) with h1 | h1
      · have hmem := signedBasis_mem_closure_omega_tau (u := tetrahedralOmega * u) h1
        simpa using mul_mem (inv_mem hω) hmem
      · rcases isTetrahedralUnit_tetrahedralOmega_mul (.inr h1) with h2 | h2
        · have hmem := signedBasis_mem_closure_omega_tau
            (u := tetrahedralOmega * (tetrahedralOmega * u)) h2
          simpa [mul_assoc] using mul_mem (inv_mem hω) (mul_mem (inv_mem hω) hmem)
        · exfalso
          have h12 : ((tetrahedralOmega : ℍ[ℝ]) * u).IsHalfUnit ∧
              ((tetrahedralOmega : ℍ[ℝ]) * ((tetrahedralOmega : ℍ[ℝ]) * u)).IsHalfUnit := ⟨h1, h2⟩
          rcases u with ⟨⟨a, b, c, d⟩, hu_unit⟩
          obtain ⟨rfl | rfl, rfl | rfl, rfl | rfl, rfl | rfl⟩ :=
            Quaternion.isHalfUnit_iff_coordinates.mp hhalf <;>
            · rw [Quaternion.isHalfUnit_iff_coordinates,
                Quaternion.isHalfUnit_iff_coordinates] at h12
              norm_num [coe_tetrahedralOmega] at h12
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact isTetrahedralUnit_tetrahedralOmega_mul ht
    · exact isTetrahedralUnit_tetrahedralTau_mul ht

/-- **The Hurwitz units are closed under multiplication.** -/
theorem _root_.Quaternion.IsTetrahedralUnit.mul {p q : ℍ[ℝ]}
    (hp : p.IsTetrahedralUnit) (hq : q.IsTetrahedralUnit) : (p * q).IsTetrahedralUnit := by
  let up : unitary ℍ[ℝ] := ⟨p, hp.mem_unitary⟩
  let uq : unitary ℍ[ℝ] := ⟨q, hq.mem_unitary⟩
  have hup : up ∈ Subgroup.closure {tetrahedralOmega, tetrahedralTau} := by
    rw [← SetLike.mem_coe, coe_closure_tetrahedralOmega_tetrahedralTau]
    exact hp
  have huq : uq ∈ Subgroup.closure {tetrahedralOmega, tetrahedralTau} := by
    rw [← SetLike.mem_coe, coe_closure_tetrahedralOmega_tetrahedralTau]
    exact hq
  have hmul : up * uq ∈ (Subgroup.closure {tetrahedralOmega, tetrahedralTau} :
      Set (unitary ℍ[ℝ])) := mul_mem hup huq
  rwa [coe_closure_tetrahedralOmega_tetrahedralTau] at hmul

/-- **The Hurwitz units are closed under inversion.** -/
theorem _root_.Quaternion.IsTetrahedralUnit.inv {q : ℍ[ℝ]} (hq : q.IsTetrahedralUnit) :
    q⁻¹.IsTetrahedralUnit := by
  have hunit : q * Star.star q = 1 := (Unitary.mem_iff.mp hq.mem_unitary).2
  rw [inv_eq_of_mul_eq_one_right hunit]
  exact hq.star

/-- **The binary tetrahedral subgroup of `unitary ℍ[ℝ]`**, whose `24` elements are the `8` signed
basis units `±1, ±i, ±j, ±k` together with the `16` half-integer units `(±1 ± i ± j ± k) / 2`. -/
noncomputable def binaryTetrahedralUnitSubgroup : Subgroup (unitary ℍ[ℝ]) where
  carrier := {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsTetrahedralUnit}
  one_mem' := Quaternion.IsTetrahedralUnit.one
  mul_mem' hp hq := hp.mul hq
  inv_mem' hq := hq.star

theorem mem_binaryTetrahedralUnitSubgroup_iff {u : unitary ℍ[ℝ]} :
    u ∈ binaryTetrahedralUnitSubgroup ↔ (u : ℍ[ℝ]).IsTetrahedralUnit := Iff.rfl

@[simp]
theorem quaternionUnitI_mem_binaryTetrahedralUnitSubgroup :
    quaternionUnitI ∈ binaryTetrahedralUnitSubgroup :=
  .inl (Quaternion.isSignedBasisUnit_iff_coordinates.mpr (by simp [coe_quaternionUnitI]))

@[simp]
theorem quaternionUnitJ_mem_binaryTetrahedralUnitSubgroup :
    quaternionUnitJ ∈ binaryTetrahedralUnitSubgroup :=
  .inl (Quaternion.isSignedBasisUnit_iff_coordinates.mpr (by simp [coe_quaternionUnitJ]))

@[simp]
theorem quaternionUnitK_mem_binaryTetrahedralUnitSubgroup :
    quaternionUnitK ∈ binaryTetrahedralUnitSubgroup :=
  .inl (Quaternion.isSignedBasisUnit_iff_coordinates.mpr (by simp [coe_quaternionUnitK]))

@[simp]
theorem neg_one_mem_binaryTetrahedralUnitSubgroup :
    (-1 : unitary ℍ[ℝ]) ∈ binaryTetrahedralUnitSubgroup :=
  Quaternion.IsTetrahedralUnit.one.neg

@[simp]
theorem tetrahedralOmega_mem_binaryTetrahedralUnitSubgroup :
    tetrahedralOmega ∈ binaryTetrahedralUnitSubgroup :=
  .inr (Quaternion.isHalfUnit_iff_coordinates.mpr (by simp [coe_tetrahedralOmega]))

@[simp]
theorem tetrahedralTau_mem_binaryTetrahedralUnitSubgroup :
    tetrahedralTau ∈ binaryTetrahedralUnitSubgroup :=
  .inr (Quaternion.isHalfUnit_iff_coordinates.mpr (by simp [coe_tetrahedralTau]))

/-- **The binary tetrahedral subgroup is generated by the `<2, 3, 3>` pair `{ω, τ}`.** -/
theorem binaryTetrahedralUnitSubgroup_eq_closure :
    binaryTetrahedralUnitSubgroup = Subgroup.closure {tetrahedralOmega, tetrahedralTau} :=
  SetLike.ext' coe_closure_tetrahedralOmega_tetrahedralTau.symm

/-- **The binary tetrahedral subgroup is generated by the coordinate generators `{i, j, ω}`.** -/
theorem binaryTetrahedralUnitSubgroup_eq_closure_coordinates :
    binaryTetrahedralUnitSubgroup =
      Subgroup.closure {quaternionUnitI, quaternionUnitJ, tetrahedralOmega} := by
  refine le_antisymm ?_ ?_
  · rw [binaryTetrahedralUnitSubgroup_eq_closure, Subgroup.closure_le]
    rintro u (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · have hj : quaternionUnitJ ∈
          Subgroup.closure {quaternionUnitI, quaternionUnitJ, tetrahedralOmega} :=
        Subgroup.subset_closure (by simp)
      have hω : tetrahedralOmega ∈
          Subgroup.closure {quaternionUnitI, quaternionUnitJ, tetrahedralOmega} :=
        Subgroup.subset_closure (by simp)
      have hτ : tetrahedralTau = tetrahedralOmega⁻¹ * quaternionUnitJ := by
        rw [← tetrahedralOmega_mul_tetrahedralTau, inv_mul_cancel_left]
      exact hτ ▸ mul_mem (inv_mem hω) hj
  · rw [Subgroup.closure_le]
    rintro u (rfl | rfl | rfl)
    · exact quaternionUnitI_mem_binaryTetrahedralUnitSubgroup
    · exact quaternionUnitJ_mem_binaryTetrahedralUnitSubgroup
    · exact tetrahedralOmega_mem_binaryTetrahedralUnitSubgroup

instance : Finite binaryTetrahedralUnitSubgroup :=
  (Quaternion.finite_isTetrahedralUnit.preimage Subtype.val_injective.injOn).to_subtype

/-- **The binary tetrahedral subgroup has exact order `24`.** -/
@[simp]
theorem natCard_binaryTetrahedralUnitSubgroup :
    Nat.card binaryTetrahedralUnitSubgroup = 24 := by
  have himg : Subtype.val '' (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ])) =
      {q : ℍ[ℝ] | q.IsTetrahedralUnit} := by
    ext q
    refine ⟨?_, fun hq => ⟨⟨q, hq.mem_unitary⟩, hq, rfl⟩⟩
    rintro ⟨u, hu, rfl⟩
    exact hu
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq,
    ← Set.ncard_image_of_injective _ Subtype.val_injective, himg,
    Quaternion.ncard_isTetrahedralUnit]

end TauCeti

end
