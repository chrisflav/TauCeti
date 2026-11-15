/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.GroupTheory.IndexNormal
public import TauCeti.Algebra.Quaternion.Polyhedral.Tetrahedral
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import TauCeti.Algebra.Group.Subgroup.Closure

/-!
# The binary octahedral group in unit-quaternion coordinates

Adjoining to the `24` Hurwitz tetrahedral units the `24` unit quaternions with **exactly two
nonzero coordinates, both `±1 / √2`** (`Quaternion.IsOctahedralPairUnit`) yields the `48` elements
of the **binary octahedral subgroup** `TauCeti.binaryOctahedralUnitSubgroup` of `unitary ℍ[ℝ]`.

In `<2, 3, 4>` presentation coordinates, the octahedral generator `r = (1 + i) / √2`
(`TauCeti.octahedralGenerator`) and the Hurwitz generator `ω = (1 + i + j + k) / 2`
(`TauCeti.tetrahedralOmega`) satisfy

`r ^ 4 = ω ^ 3 = (r * ω) ^ 2 = -1`,

with `r ^ 2 = i`, `r⁻¹ * ω * r = τ`, and `O₂₄ = r • T₂₄`. The binary tetrahedral subgroup sits
inside `TauCeti.binaryOctahedralUnitSubgroup` as a normal subgroup of index `2`.

## Main definitions

* `Quaternion.IsOctahedralPairUnit`: quaternions in `ℍ[ℝ]` with two coordinates `±1 / √2` and two
  zero coordinates.
* `Quaternion.IsOctahedralUnit`: the `48` binary octahedral unit quaternions in `ℍ[ℝ]`.
* `TauCeti.octahedralGenerator`: the `<2, 3, 4>` generator `(1 + i) / √2` in `unitary ℍ[ℝ]`.
* `TauCeti.binaryOctahedralUnitSubgroup`: the binary octahedral subgroup of `unitary ℍ[ℝ]`.

## References

* J. H. Conway and D. A. Smith, *On Quaternions and Octonions*, A K Peters, 2003, §6.5.
-/

public section

open scoped Quaternion Pointwise

namespace Quaternion

/-! ### The 24 two-coordinate `±1 / √2` points -/

/-- A quaternion in `ℍ[ℝ]` is an **octahedral pair unit** if it has exactly two nonzero
coordinates, both equal to `±1 / √2`. -/
def IsOctahedralPairUnit (q : ℍ[ℝ]) : Prop :=
  ∃ p r : Fin 4, p < r ∧
    (equivTuple ℝ q p = 1 / √2 ∨ equivTuple ℝ q p = -(1 / √2)) ∧
    (equivTuple ℝ q r = 1 / √2 ∨ equivTuple ℝ q r = -(1 / √2)) ∧
    ∀ s : Fin 4, s ≠ p → s ≠ r → equivTuple ℝ q s = 0

theorem isOctahedralPairUnit_def (q : ℍ[ℝ]) :
    q.IsOctahedralPairUnit ↔ ∃ p r : Fin 4, p < r ∧
      (equivTuple ℝ q p = 1 / √2 ∨ equivTuple ℝ q p = -(1 / √2)) ∧
      (equivTuple ℝ q r = 1 / √2 ∨ equivTuple ℝ q r = -(1 / √2)) ∧
      ∀ s : Fin 4, s ≠ p → s ≠ r → equivTuple ℝ q s = 0 := Iff.rfl

/-- Symmetric characterization of `Quaternion.IsOctahedralPairUnit` without ordering the two
nonzero coordinate indices. -/
theorem isOctahedralPairUnit_iff {q : ℍ[ℝ]} :
    q.IsOctahedralPairUnit ↔ ∃ p r : Fin 4, p ≠ r ∧
      (equivTuple ℝ q p = 1 / √2 ∨ equivTuple ℝ q p = -(1 / √2)) ∧
      (equivTuple ℝ q r = 1 / √2 ∨ equivTuple ℝ q r = -(1 / √2)) ∧
      ∀ s : Fin 4, s ≠ p → s ≠ r → equivTuple ℝ q s = 0 := by
  refine ⟨fun ⟨p, r, hlt, hp, hr, h0⟩ => ⟨p, r, hlt.ne, hp, hr, h0⟩, ?_⟩
  rintro ⟨p, r, hne, hp, hr, h0⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨p, r, hlt, hp, hr, h0⟩
  · exact ⟨r, p, hgt, hr, hp, fun s hsr hsp => h0 s hsp hsr⟩

/-- Explicit parametrization of the `24` octahedral pair units by an ordered index pair and two
signs (`6 × 4 = 24`). -/
noncomputable def octahedralPairUnit
    (idx : {pr : Fin 4 × Fin 4 // pr.1 < pr.2} × Bool × Bool) : ℍ[ℝ] :=
  (equivTuple ℝ).symm fun s =>
    if s = idx.1.1.1 then (if idx.2.1 then -(1 / √2) else 1 / √2)
    else if s = idx.1.1.2 then (if idx.2.2 then -(1 / √2) else 1 / √2)
    else 0

theorem equivTuple_octahedralPairUnit
    (idx : {pr : Fin 4 × Fin 4 // pr.1 < pr.2} × Bool × Bool) :
    equivTuple ℝ (octahedralPairUnit idx) = fun s =>
      if s = idx.1.1.1 then (if idx.2.1 then -(1 / √2) else 1 / √2)
      else if s = idx.1.1.2 then (if idx.2.2 then -(1 / √2) else 1 / √2)
      else 0 :=
  (equivTuple ℝ).apply_symm_apply _

private theorem one_div_sqrt_two_pos : (0 : ℝ) < 1 / √2 := by positivity

private theorem support_octahedralPairUnit
    (idx : {pr : Fin 4 × Fin 4 // pr.1 < pr.2} × Bool × Bool) (s : Fin 4) :
    equivTuple ℝ (octahedralPairUnit idx) s ≠ 0 ↔ s = idx.1.1.1 ∨ s = idx.1.1.2 := by
  have _ := one_div_sqrt_two_pos
  rw [equivTuple_octahedralPairUnit]
  by_cases hs1 : s = idx.1.1.1
  · subst hs1
    simp only [↓reduceIte, true_or, iff_true]
    cases idx.2.1 <;> intro h <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> linarith
  · by_cases hs2 : s = idx.1.1.2
    · subst hs2
      simp only [hs1, ↓reduceIte, or_true, iff_true]
      cases idx.2.2 <;> intro h <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> linarith
    · simp [hs1, hs2]

theorem injective_octahedralPairUnit : Function.Injective octahedralPairUnit := by
  rintro ⟨⟨⟨p₁, r₁⟩, h₁⟩, b₁, c₁⟩ ⟨⟨⟨p₂, r₂⟩, h₂⟩, b₂, c₂⟩ h
  have hlt₁ : p₁.1 < r₁.1 := h₁
  have hlt₂ : p₂.1 < r₂.1 := h₂
  have hsupp (s : Fin 4) : (s = p₁ ∨ s = r₁) ↔ (s = p₂ ∨ s = r₂) := by
    rw [← support_octahedralPairUnit ⟨⟨(p₁, r₁), h₁⟩, b₁, c₁⟩ s,
      ← support_octahedralPairUnit ⟨⟨(p₂, r₂), h₂⟩, b₂, c₂⟩ s, h]
  have hp1 : p₁.1 = p₂.1 ∨ p₁.1 = r₂.1 :=
    ((hsupp p₁).mp (.inl rfl)).imp (congrArg Fin.val) (congrArg Fin.val)
  have hr1 : r₁.1 = p₂.1 ∨ r₁.1 = r₂.1 :=
    ((hsupp r₁).mp (.inr rfl)).imp (congrArg Fin.val) (congrArg Fin.val)
  have hp : p₁ = p₂ := Fin.ext (by omega)
  have hr : r₁ = r₂ := Fin.ext (by omega)
  subst hp hr
  have ht := congrArg (equivTuple ℝ) h
  rw [equivTuple_octahedralPairUnit, equivTuple_octahedralPairUnit] at ht
  have _ := one_div_sqrt_two_pos
  have hb : b₁ = b₂ := by
    have hpval : (if b₁ then -(1 / √2) else 1 / √2) = if b₂ then -(1 / √2) else 1 / √2 := by
      simpa only [↓reduceIte] using congrFun ht p₁
    cases b₁ <;> cases b₂ <;> simp only [Bool.false_eq_true, ↓reduceIte] at hpval ⊢ <;> linarith
  have hc : c₁ = c₂ := by
    have hrval : (if c₁ then -(1 / √2) else 1 / √2) = if c₂ then -(1 / √2) else 1 / √2 := by
      simpa only [h₁.ne', ↓reduceIte] using congrFun ht r₁
    cases c₁ <;> cases c₂ <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrval ⊢ <;> linarith
  subst hb hc
  rfl

@[simp]
theorem isOctahedralPairUnit_octahedralPairUnit
    (idx : {pr : Fin 4 × Fin 4 // pr.1 < pr.2} × Bool × Bool) :
    (octahedralPairUnit idx).IsOctahedralPairUnit := by
  refine ⟨idx.1.1.1, idx.1.1.2, idx.1.2, ?_, ?_, fun s hs1 hs2 => ?_⟩
  · rw [equivTuple_octahedralPairUnit]
    cases idx.2.1
    · exact .inl (by simp)
    · exact .inr (by simp)
  · rw [equivTuple_octahedralPairUnit]
    cases idx.2.2
    · exact .inl (by simp [idx.1.2.ne'])
    · exact .inr (by simp [idx.1.2.ne'])
  · rw [equivTuple_octahedralPairUnit]
    simp [hs1, hs2]

theorem range_octahedralPairUnit :
    Set.range octahedralPairUnit = {q : ℍ[ℝ] | q.IsOctahedralPairUnit} := by
  ext q
  refine ⟨?_, fun ⟨p, r, hlt, hp, hr, h0⟩ => ?_⟩
  · rintro ⟨idx, rfl⟩
    exact isOctahedralPairUnit_octahedralPairUnit idx
  · classical
    have hne : (√2 : ℝ)⁻¹ ≠ -(√2)⁻¹ := by
      have : (0 : ℝ) < (√2)⁻¹ := by positivity
      linarith
    refine ⟨(⟨(p, r), hlt⟩, decide (equivTuple ℝ q p = -(1 / √2)),
      decide (equivTuple ℝ q r = -(1 / √2))), (equivTuple ℝ).injective ?_⟩
    rw [equivTuple_octahedralPairUnit]
    ext s
    by_cases hsp : s = p
    · subst hsp
      rcases hp with hp | hp
      · simp [hp, hne]
      · simp [hp]
    · by_cases hsr : s = r
      · subst hsr
        rcases hr with hr | hr
        · simp [hsp, hr, hne]
        · simp [hsp, hr]
      · simp [hsp, hsr, h0 s hsp hsr]

theorem finite_isOctahedralPairUnit : {q : ℍ[ℝ] | q.IsOctahedralPairUnit}.Finite := by
  rw [← range_octahedralPairUnit]
  exact Set.finite_range _

/-- There are `24` distinct octahedral pair units in `ℍ[ℝ]`. -/
@[simp]
theorem ncard_isOctahedralPairUnit : {q : ℍ[ℝ] | q.IsOctahedralPairUnit}.ncard = 24 := by
  have hcard : Fintype.card {pr : Fin 4 × Fin 4 // pr.1 < pr.2} = 6 := by decide
  rw [← range_octahedralPairUnit, Set.ncard_range_of_injective injective_octahedralPairUnit,
    Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod, hcard]
  norm_num

theorem disjoint_isTetrahedralUnit_isOctahedralPairUnit :
    Disjoint {q : ℍ[ℝ] | q.IsTetrahedralUnit} {q : ℍ[ℝ] | q.IsOctahedralPairUnit} := by
  rw [Set.disjoint_left]
  rintro q htet ⟨p, -, -, hp, -, -⟩
  have hsq : (equivTuple ℝ q p) ^ 2 = 2⁻¹ := by
    rcases hp with h | h <;> rw [h] <;> simp
  rcases htet.coord_sq_mem p with h | h | h <;> linarith

/-! ### The 48 binary octahedral units -/

/-- A quaternion in `ℍ[ℝ]` is an **octahedral unit** if it is either one of the `24` Hurwitz
tetrahedral units or one of the `24` octahedral pair units. -/
def IsOctahedralUnit (q : ℍ[ℝ]) : Prop :=
  q.IsTetrahedralUnit ∨ q.IsOctahedralPairUnit

theorem isOctahedralUnit_def (q : ℍ[ℝ]) :
    q.IsOctahedralUnit ↔ q.IsTetrahedralUnit ∨ q.IsOctahedralPairUnit := Iff.rfl

theorem finite_isOctahedralUnit : {q : ℍ[ℝ] | q.IsOctahedralUnit}.Finite :=
  finite_isTetrahedralUnit.union finite_isOctahedralPairUnit

/-- **The 48 binary octahedral unit quaternions are pairwise distinct.** -/
@[simp]
theorem ncard_isOctahedralUnit : {q : ℍ[ℝ] | q.IsOctahedralUnit}.ncard = 48 := by
  have heq : {q : ℍ[ℝ] | q.IsOctahedralUnit} =
      {q : ℍ[ℝ] | q.IsTetrahedralUnit} ∪ {q : ℍ[ℝ] | q.IsOctahedralPairUnit} := rfl
  rw [heq, Set.ncard_union_eq disjoint_isTetrahedralUnit_isOctahedralPairUnit
    finite_isTetrahedralUnit finite_isOctahedralPairUnit,
    ncard_isTetrahedralUnit, ncard_isOctahedralPairUnit]

theorem IsOctahedralPairUnit.normSq_eq_one {q : ℍ[ℝ]} (hq : q.IsOctahedralPairUnit) :
    q.normSq = 1 := by
  obtain ⟨p, r, hlt, hp, hr, h0⟩ := hq
  have hsum : q.normSq = ∑ s : Fin 4, (equivTuple ℝ q s) ^ 2 := by
    rw [normSq_def', Fin.sum_univ_four]
    rfl
  have hp2 : (equivTuple ℝ q p) ^ 2 = 2⁻¹ := by rcases hp with h | h <;> rw [h] <;> simp
  have hr2 : (equivTuple ℝ q r) ^ 2 = 2⁻¹ := by rcases hr with h | h <;> rw [h] <;> simp
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ p),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hlt.ne', Finset.mem_univ r⟩), hp2, hr2]
  have hrest : ∑ s ∈ (Finset.univ.erase p).erase r, (equivTuple ℝ q s) ^ 2 = 0 :=
    Finset.sum_eq_zero fun s hs => by
      simp only [Finset.mem_erase] at hs
      rw [h0 s hs.2.1 hs.1]
      norm_num
  linarith

theorem IsOctahedralUnit.normSq_eq_one {q : ℍ[ℝ]} (hq : q.IsOctahedralUnit) : q.normSq = 1 :=
  hq.elim IsTetrahedralUnit.normSq_eq_one IsOctahedralPairUnit.normSq_eq_one

theorem IsOctahedralUnit.mem_unitary {q : ℍ[ℝ]} (hq : q.IsOctahedralUnit) : q ∈ unitary ℍ[ℝ] :=
  (mem_unitary_iff_normSq_eq_one q).mpr hq.normSq_eq_one

theorem IsOctahedralUnit.one : (1 : ℍ[ℝ]).IsOctahedralUnit :=
  .inl IsTetrahedralUnit.one

private theorem equivTuple_neg_apply (q : ℍ[ℝ]) (s : Fin 4) :
    equivTuple ℝ (-q) s = -equivTuple ℝ q s := by
  fin_cases s <;> rfl

private theorem equivTuple_star_eq_or_neg (q : ℍ[ℝ]) (s : Fin 4) :
    equivTuple ℝ (Star.star q) s = equivTuple ℝ q s ∨
      equivTuple ℝ (Star.star q) s = -equivTuple ℝ q s := by
  fin_cases s <;> [left; right; right; right] <;> simp

theorem IsOctahedralUnit.neg {q : ℍ[ℝ]} (hq : q.IsOctahedralUnit) : (-q).IsOctahedralUnit := by
  rcases hq with htet | ⟨p, r, hlt, hp, hr, h0⟩
  · exact .inl htet.neg
  · refine .inr ⟨p, r, hlt, ?_, ?_, fun s hsp hsr => ?_⟩
    · rw [equivTuple_neg_apply]
      rcases hp with h | h <;> [right; left] <;> simp [h]
    · rw [equivTuple_neg_apply]
      rcases hr with h | h <;> [right; left] <;> simp [h]
    · rw [equivTuple_neg_apply, h0 s hsp hsr, neg_zero]

theorem IsOctahedralUnit.star {q : ℍ[ℝ]} (hq : q.IsOctahedralUnit) :
    (Star.star q).IsOctahedralUnit := by
  rcases hq with htet | ⟨p, r, hlt, hp, hr, h0⟩
  · exact .inl htet.star
  · refine .inr ⟨p, r, hlt, ?_, ?_, fun s hsp hsr => ?_⟩
    · rcases equivTuple_star_eq_or_neg q p with heq | heq <;> rw [heq]
      · exact hp
      · rcases hp with h | h <;> [right; left] <;> simp [h]
    · rcases equivTuple_star_eq_or_neg q r with heq | heq <;> rw [heq]
      · exact hr
      · rcases hr with h | h <;> [right; left] <;> simp [h]
    · rcases equivTuple_star_eq_or_neg q s with heq | heq <;> rw [heq, h0 s hsp hsr]
      exact neg_zero

end Quaternion

namespace TauCeti

/-! ### The `<2, 3, 4>` generator and coset decomposition -/

/-- The `<2, 3, 4>` octahedral generator `r = (1 + i) / √2` in `unitary ℍ[ℝ]`. -/
noncomputable def octahedralGenerator : unitary ℍ[ℝ] :=
  ⟨⟨1 / √2, 1 / √2, 0, 0⟩, (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr <| by
    rw [Quaternion.normSq_def']
    have hsq : (1 / √2 : ℝ) ^ 2 = 1 / 2 := by
      rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith⟩

@[simp]
theorem coe_octahedralGenerator :
    (octahedralGenerator : ℍ[ℝ]) = ⟨1 / √2, 1 / √2, 0, 0⟩ := (rfl)

/-- Squaring the octahedral generator gives `i`: `r ^ 2 = i`. -/
@[simp]
theorem octahedralGenerator_sq : octahedralGenerator ^ 2 = quaternionUnitI := by
  have hsq : (√2 : ℝ)⁻¹ * (√2)⁻¹ = 1 / 2 := by
    rw [← sq, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  refine Subtype.ext ?_
  ext <;> simp [sq, coe_octahedralGenerator, coe_quaternionUnitI]; linear_combination 2 * hsq

/-- The `<2, 3, 4>` relation `r ^ 4 = -1`. -/
@[simp]
theorem octahedralGenerator_pow_four : octahedralGenerator ^ 4 = -1 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, octahedralGenerator_sq, quaternionUnitI_sq]

/-- The `<2, 3, 4>` relation `(r * ω) ^ 2 = -1`. -/
@[simp]
theorem octahedralGenerator_mul_tetrahedralOmega_sq :
    (octahedralGenerator * tetrahedralOmega) ^ 2 = -1 := by
  have hsq : (√2 : ℝ)⁻¹ * (√2)⁻¹ = 1 / 2 := by
    rw [← sq, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hrω : ((octahedralGenerator * tetrahedralOmega : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      ⟨0, 1 / √2, 0, 1 / √2⟩ := by
    ext <;> simp [coe_octahedralGenerator, coe_tetrahedralOmega] <;> ring
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, sq, hrω, Unitary.coe_neg, OneMemClass.coe_one]
  ext <;> simp; linear_combination -2 * hsq

/-- Conjugating `ω` by `r⁻¹` yields the second tetrahedral generator `τ`: `r⁻¹ * ω * r = τ`. -/
theorem octahedralGenerator_inv_conj_tetrahedralOmega :
    octahedralGenerator⁻¹ * tetrahedralOmega * octahedralGenerator = tetrahedralTau := by
  have hsq : (√2 : ℝ)⁻¹ * (√2)⁻¹ = 1 / 2 := by
    rw [← sq, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  -- On `unitary ℍ[ℝ]`, group inversion is definitionally quaternion `star`.
  have hinv : ((octahedralGenerator⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ]) = ⟨1 / √2, -(1 / √2), 0, 0⟩ := by
    change Star.star (octahedralGenerator : ℍ[ℝ]) = _
    rw [coe_octahedralGenerator]
    ext <;> simp
  refine Subtype.ext ?_
  rw [Submonoid.coe_mul, Submonoid.coe_mul, hinv, coe_tetrahedralOmega, coe_octahedralGenerator,
    coe_tetrahedralTau]
  ext <;> simp <;> linear_combination hsq

/-- The octahedral generator `r = (1 + i) / √2` has exact order `8`. -/
@[simp]
theorem orderOf_octahedralGenerator : orderOf octahedralGenerator = 8 := by
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ fun p hp hdiv => ?_
  · rw [show (8 : ℕ) = 4 * 2 by rfl, pow_mul, octahedralGenerator_pow_four]
    norm_num
  · have hle := Nat.le_of_dvd (by norm_num) hdiv
    have hpge := hp.two_le
    interval_cases p
    · intro h
      have hre := congrArg (fun u : unitary ℍ[ℝ] => (u : ℍ[ℝ]).re) h
      rw [show (8 / 2 : ℕ) = 4 by norm_num, octahedralGenerator_pow_four] at hre
      norm_num [Unitary.coe_neg] at hre
    · norm_num at hdiv
    · exact absurd hp (by decide)
    · norm_num at hdiv
    · exact absurd hp (by decide)
    · norm_num at hdiv
    · exact absurd hp (by decide)

/-! ### Closure and the binary octahedral subgroup -/

private theorem two_mul_coord_or {x : ℝ} (hx : x = 1 / 2 ∨ x = -(1 / 2)) :
    x * (1 / √2) + x * (1 / √2) = 1 / √2 ∨ x * (1 / √2) + x * (1 / √2) = -(1 / √2) := by
  rcases hx with rfl | rfl <;> [left; right] <;> ring

private theorem isOctahedralPairUnit_octahedralGenerator_mul_basis {q : ℍ[ℝ]}
    (hbasis : q.IsSignedBasisUnit) :
    ((octahedralGenerator : ℍ[ℝ]) * q).IsOctahedralPairUnit := by
  rcases q with ⟨a, b, c, d⟩
  have hbasis' := Quaternion.isSignedBasisUnit_iff_coordinates.mp hbasis
  dsimp only at hbasis'
  rcases hbasis' with ⟨ha, rfl, rfl, rfl⟩ | ⟨rfl, hb, rfl, rfl⟩ |
    ⟨rfl, rfl, hc, rfl⟩ | ⟨rfl, rfl, rfl, hd⟩
  · refine ⟨0, 1, by decide, ?_, ?_, fun s hs0 hs1 => ?_⟩
    · rcases ha with rfl | rfl <;> [left; right] <;> simp [coe_octahedralGenerator]
    · rcases ha with rfl | rfl <;> [left; right] <;> simp [coe_octahedralGenerator]
    · fin_cases s <;> simp_all [coe_octahedralGenerator]
  · refine ⟨0, 1, by decide, ?_, ?_, fun s hs0 hs1 => ?_⟩
    · rcases hb with rfl | rfl <;> [right; left] <;> simp [coe_octahedralGenerator]
    · rcases hb with rfl | rfl <;> [left; right] <;> simp [coe_octahedralGenerator]
    · fin_cases s <;> simp_all [coe_octahedralGenerator]
  · refine ⟨2, 3, by decide, ?_, ?_, fun s hs2 hs3 => ?_⟩
    · rcases hc with rfl | rfl <;> [left; right] <;> simp [coe_octahedralGenerator]
    · rcases hc with rfl | rfl <;> [left; right] <;> simp [coe_octahedralGenerator]
    · fin_cases s <;> simp_all [coe_octahedralGenerator]
  · refine ⟨2, 3, by decide, ?_, ?_, fun s hs2 hs3 => ?_⟩
    · rcases hd with rfl | rfl <;> [right; left] <;> simp [coe_octahedralGenerator]
    · rcases hd with rfl | rfl <;> [left; right] <;> simp [coe_octahedralGenerator]
    · fin_cases s <;> simp_all [coe_octahedralGenerator]

private theorem isOctahedralPairUnit_octahedralGenerator_mul_half {q : ℍ[ℝ]}
    (hhalf : q.IsHalfUnit) :
    ((octahedralGenerator : ℍ[ℝ]) * q).IsOctahedralPairUnit := by
  rcases q with ⟨a, b, c, d⟩
  obtain ⟨ha, hb, hc, hd⟩ := Quaternion.isHalfUnit_iff_coordinates.mp hhalf
  have hab : b = a ∨ b = -a := by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  have hcd : d = c ∨ d = -c := by rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> simp
  rcases hab with rfl | rfl <;> rcases hcd with rfl | rfl
  · refine ⟨1, 3, by decide, ?_, ?_, fun s hs1 hs3 => ?_⟩
    · simpa [coe_octahedralGenerator, mul_comm] using two_mul_coord_or ha
    · simpa [coe_octahedralGenerator, mul_comm] using two_mul_coord_or hc
    · fin_cases s <;> simp_all [coe_octahedralGenerator]
  · refine ⟨1, 2, by decide, ?_, ?_, fun s hs1 hs2 => ?_⟩
    · simpa [coe_octahedralGenerator, mul_comm] using two_mul_coord_or ha
    · simpa [coe_octahedralGenerator, mul_comm, sub_neg_eq_add] using two_mul_coord_or hc
    · fin_cases s <;> simp_all [coe_octahedralGenerator]
  · refine ⟨0, 3, by decide, ?_, ?_, fun s hs0 hs3 => ?_⟩
    · simpa [coe_octahedralGenerator, mul_comm, sub_neg_eq_add] using two_mul_coord_or ha
    · simpa [coe_octahedralGenerator, mul_comm] using two_mul_coord_or hc
    · fin_cases s <;> simp_all [coe_octahedralGenerator]
  · refine ⟨0, 2, by decide, ?_, ?_, fun s hs0 hs2 => ?_⟩
    · simpa [coe_octahedralGenerator, mul_comm, sub_neg_eq_add] using two_mul_coord_or ha
    · simpa [coe_octahedralGenerator, mul_comm, sub_neg_eq_add] using two_mul_coord_or hc
    · fin_cases s <;> simp_all [coe_octahedralGenerator]

private theorem smul_binaryTetrahedralUnitSubgroup_eq_octahedralPair :
    octahedralGenerator • (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ])) =
      {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsOctahedralPairUnit} := by
  have hfin : {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsOctahedralPairUnit}.Finite :=
    Quaternion.finite_isOctahedralPairUnit.preimage Subtype.val_injective.injOn
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
  · rintro _ ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, mem_binaryTetrahedralUnitSubgroup_iff,
      Quaternion.isTetrahedralUnit_def] at ht
    exact ht.elim isOctahedralPairUnit_octahedralGenerator_mul_basis
      isOctahedralPairUnit_octahedralGenerator_mul_half
  · have himg : Subtype.val '' {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsOctahedralPairUnit} =
        {q : ℍ[ℝ] | q.IsOctahedralPairUnit} := by
      ext q
      refine ⟨fun ⟨_, hu, hq⟩ => hq ▸ hu, fun hq =>
        ⟨⟨q, Quaternion.IsOctahedralUnit.mem_unitary (.inr hq)⟩, hq, rfl⟩⟩
    have hcard_pair : {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsOctahedralPairUnit}.ncard = 24 := by
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg,
        Quaternion.ncard_isOctahedralPairUnit]
    rw [hcard_pair, Set.ncard_smul_set, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
      natCard_binaryTetrahedralUnitSubgroup]

private theorem coe_closure_octahedralGenerator_tetrahedralOmega :
    (Subgroup.closure ({octahedralGenerator, tetrahedralOmega} : Set (unitary ℍ[ℝ])) :
      Set (unitary ℍ[ℝ])) = {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsOctahedralUnit} := by
  let C := Subgroup.closure ({octahedralGenerator, tetrahedralOmega} : Set (unitary ℍ[ℝ]))
  have hr : octahedralGenerator ∈ C := Subgroup.subset_closure (by simp)
  have hω : tetrahedralOmega ∈ C := Subgroup.subset_closure (by simp)
  have htet_le : binaryTetrahedralUnitSubgroup ≤ C := by
    rw [binaryTetrahedralUnitSubgroup_eq_closure_coordinates, Subgroup.closure_le]
    have hi : quaternionUnitI ∈ C := octahedralGenerator_sq ▸ pow_mem hr 2
    have hj : quaternionUnitJ ∈ C :=
      tetrahedralOmega_conj_quaternionUnitI ▸ mul_mem (mul_mem hω hi) (inv_mem hω)
    rintro u (rfl | rfl | rfl)
    · exact hi
    · exact hj
    · exact hω
  have hO48_eq : {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsOctahedralUnit} =
      (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ])) ∪
        octahedralGenerator • (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ])) := by
    rw [smul_binaryTetrahedralUnitSubgroup_eq_octahedralPair]
    ext u
    simp [Quaternion.isOctahedralUnit_def, mem_binaryTetrahedralUnitSubgroup_iff]
  have hfin : {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsOctahedralUnit}.Finite :=
    Quaternion.finite_isOctahedralUnit.preimage Subtype.val_injective.injOn
  refine Subgroup.coe_closure_eq_of_forall_mul_mem hfin Quaternion.IsOctahedralUnit.one
    (fun u hu => ?_) (fun s hs u hu => ?_)
  · rw [hO48_eq] at hu
    rcases hu with hu | ⟨t, ht, rfl⟩
    · exact htet_le hu
    · exact mul_mem hr (htet_le ht)
  · rw [hO48_eq] at hu ⊢
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rcases hu with hu | ⟨t, ht, rfl⟩
      · exact .inr ⟨u, hu, rfl⟩
      · left
        dsimp only
        rw [smul_eq_mul, ← mul_assoc, ← sq, octahedralGenerator_sq]
        exact mul_mem quaternionUnitI_mem_binaryTetrahedralUnitSubgroup ht
    · rcases hu with hu | ⟨t, ht, rfl⟩
      · exact .inl (mul_mem tetrahedralOmega_mem_binaryTetrahedralUnitSubgroup hu)
      · right
        refine ⟨tetrahedralTau * t,
          mul_mem tetrahedralTau_mem_binaryTetrahedralUnitSubgroup ht, ?_⟩
        dsimp only
        rw [smul_eq_mul, smul_eq_mul, ← octahedralGenerator_inv_conj_tetrahedralOmega]
        simp [mul_assoc]

/-- **The 48 binary octahedral unit quaternions are closed under multiplication.** -/
theorem _root_.Quaternion.IsOctahedralUnit.mul {p q : ℍ[ℝ]}
    (hp : p.IsOctahedralUnit) (hq : q.IsOctahedralUnit) : (p * q).IsOctahedralUnit := by
  let up : unitary ℍ[ℝ] := ⟨p, hp.mem_unitary⟩
  let uq : unitary ℍ[ℝ] := ⟨q, hq.mem_unitary⟩
  have hup : up ∈ Subgroup.closure {octahedralGenerator, tetrahedralOmega} := by
    rw [← SetLike.mem_coe, coe_closure_octahedralGenerator_tetrahedralOmega]
    exact hp
  have huq : uq ∈ Subgroup.closure {octahedralGenerator, tetrahedralOmega} := by
    rw [← SetLike.mem_coe, coe_closure_octahedralGenerator_tetrahedralOmega]
    exact hq
  have hmul : up * uq ∈ (Subgroup.closure {octahedralGenerator, tetrahedralOmega} :
      Set (unitary ℍ[ℝ])) := mul_mem hup huq
  rwa [coe_closure_octahedralGenerator_tetrahedralOmega] at hmul

/-- **The 48 binary octahedral unit quaternions are closed under inversion.** -/
theorem _root_.Quaternion.IsOctahedralUnit.inv {q : ℍ[ℝ]} (hq : q.IsOctahedralUnit) :
    q⁻¹.IsOctahedralUnit := by
  have hunit : q * Star.star q = 1 := (Unitary.mem_iff.mp hq.mem_unitary).2
  rw [inv_eq_of_mul_eq_one_right hunit]
  exact hq.star

/-- **The binary octahedral subgroup of `unitary ℍ[ℝ]`**, formed by adjoining to the `24` Hurwitz
tetrahedral units the `24` unit quaternions with two coordinates `±1 / √2` and two zero
coordinates. -/
noncomputable def binaryOctahedralUnitSubgroup : Subgroup (unitary ℍ[ℝ]) where
  carrier := {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsOctahedralUnit}
  one_mem' := Quaternion.IsOctahedralUnit.one
  mul_mem' hp hq := hp.mul hq
  inv_mem' hq := hq.star

theorem mem_binaryOctahedralUnitSubgroup_iff {u : unitary ℍ[ℝ]} :
    u ∈ binaryOctahedralUnitSubgroup ↔ (u : ℍ[ℝ]).IsOctahedralUnit := Iff.rfl

@[simp]
theorem octahedralGenerator_mem_binaryOctahedralUnitSubgroup :
    octahedralGenerator ∈ binaryOctahedralUnitSubgroup :=
  Quaternion.isOctahedralUnit_def _ |>.mpr <| .inr
    ⟨0, 1, by decide, .inl (by simp [coe_octahedralGenerator]),
      .inl (by simp [coe_octahedralGenerator]),
      fun s hs0 hs1 => by fin_cases s <;> simp_all [coe_octahedralGenerator]⟩

/-- The binary tetrahedral subgroup is contained in the binary octahedral subgroup. -/
theorem binaryTetrahedralUnitSubgroup_le_binaryOctahedralUnitSubgroup :
    binaryTetrahedralUnitSubgroup ≤ binaryOctahedralUnitSubgroup := fun _ hu =>
  (mem_binaryOctahedralUnitSubgroup_iff.mpr
    (Quaternion.isOctahedralUnit_def _ |>.mpr (.inl (mem_binaryTetrahedralUnitSubgroup_iff.mp hu))))

/-- **The binary octahedral subgroup is generated by the `<2, 3, 4>` pair `{r, ω}`.** -/
theorem binaryOctahedralUnitSubgroup_eq_closure :
    binaryOctahedralUnitSubgroup = Subgroup.closure {octahedralGenerator, tetrahedralOmega} :=
  SetLike.ext' coe_closure_octahedralGenerator_tetrahedralOmega.symm

instance : Finite binaryOctahedralUnitSubgroup :=
  (Quaternion.finite_isOctahedralUnit.preimage Subtype.val_injective.injOn).to_subtype

/-- **The binary octahedral subgroup has exact order `48`.** -/
@[simp]
theorem natCard_binaryOctahedralUnitSubgroup :
    Nat.card binaryOctahedralUnitSubgroup = 48 := by
  have himg : Subtype.val '' (binaryOctahedralUnitSubgroup : Set (unitary ℍ[ℝ])) =
      {q : ℍ[ℝ] | q.IsOctahedralUnit} := by
    ext q
    refine ⟨?_, fun hq => ⟨⟨q, hq.mem_unitary⟩, hq, rfl⟩⟩
    rintro ⟨u, hu, rfl⟩
    exact hu
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq,
    ← Set.ncard_image_of_injective _ Subtype.val_injective, himg,
    Quaternion.ncard_isOctahedralUnit]

/-- The binary tetrahedral subgroup has relative index `2` inside the binary octahedral subgroup. -/
@[simp]
theorem relIndex_binaryTetrahedralUnitSubgroup_binaryOctahedralUnitSubgroup :
    binaryTetrahedralUnitSubgroup.relIndex binaryOctahedralUnitSubgroup = 2 := by
  have hmul := binaryTetrahedralUnitSubgroup.relIndex_mul_card binaryOctahedralUnitSubgroup
  rw [inf_of_le_left binaryTetrahedralUnitSubgroup_le_binaryOctahedralUnitSubgroup,
    natCard_binaryTetrahedralUnitSubgroup, natCard_binaryOctahedralUnitSubgroup] at hmul
  omega

/-- The binary tetrahedral subgroup is normal inside the binary octahedral subgroup. -/
instance :
    (binaryTetrahedralUnitSubgroup.subgroupOf binaryOctahedralUnitSubgroup).Normal :=
  Subgroup.normal_of_index_eq_two
    relIndex_binaryTetrahedralUnitSubgroup_binaryOctahedralUnitSubgroup

end TauCeti

end
