/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Real.GoldenRatio
public import TauCeti.Algebra.Quaternion.Polyhedral.Tetrahedral
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import TauCeti.Algebra.Group.Subgroup.Closure

/-!
# The binary icosahedral group and the unit `600`-cell

The **binary icosahedral subgroup** `TauCeti.binaryIcosahedralUnitSubgroup` of `unitary ℍ[ℝ]` has
order `120`; its elements are the vertices of the regular four-dimensional **`600`-cell**:

* the `24` Hurwitz tetrahedral units (`Quaternion.IsTetrahedralUnit`), and
* the `96` golden-ratio units (`Quaternion.IsIcosahedralGoldenUnit`) obtained from
  `(0, ±1, ±φ, ±φ⁻¹) / 2` — where `φ = (1 + √5) / 2` is `Real.goldenRatio` — by **even**
  permutations of the four coordinates (`alternatingGroup (Fin 4)`).

Allowing *all* `24` coordinate permutations gives `192` golden points
(`Quaternion.IsAllPermGoldenUnit`), hence `24 + 192 = 216` points together with the Hurwitz units
(`Quaternion.ncard_isTetrahedralUnit_or_isAllPermGoldenUnit`), and this `216`-element set is **not**
closed under quaternion multiplication
(`Quaternion.not_forall_mul_isTetrahedralUnit_or_isAllPermGoldenUnit`).

In `<2, 3, 5>` presentation coordinates, the generator `ζ = (φ + j + φ⁻¹ k) / 2`
(`TauCeti.icosahedralGenerator`) and the Hurwitz generator `ω = (1 + i + j + k) / 2`
(`TauCeti.tetrahedralOmega`) satisfy

`ζ ^ 5 = ω ^ 3 = (ζ * ω) ^ 2 = -1`,

with `ζ ^ 2 * ω * ζ⁻¹ = j` and five-coset decomposition `I₁₂₀ = ⋃_{m < 5} ζ ^ m • T₂₄`.

## Main definitions

* `Quaternion.icosahedralBaseTuple`: the signed tuple `![0, ±1 / 2, ±φ / 2, ±φ⁻¹ / 2]`.
* `Quaternion.IsIcosahedralGoldenUnit`: the `96` even-permutation golden unit quaternions.
* `Quaternion.IsAllPermGoldenUnit`: the `192` arbitrary-permutation golden unit quaternions.
* `Quaternion.IsIcosahedralUnit`: the `120` vertices of the unit `600`-cell in `ℍ[ℝ]`.
* `TauCeti.icosahedralGenerator`: the `<2, 3, 5>` generator `(φ + j + φ⁻¹ k) / 2` in `unitary ℍ[ℝ]`.
* `TauCeti.binaryIcosahedralUnitSubgroup`: the binary icosahedral subgroup of `unitary ℍ[ℝ]`.

## References

* J. H. Conway and D. A. Smith, *On Quaternions and Octonions*, A K Peters, 2003, §6.5.
-/

public section

open scoped Quaternion Pointwise goldenRatio

namespace Quaternion

private theorem inv_one_add_sqrt_five : (1 + √5 : ℝ)⁻¹ = (√5 - 1) / 4 := by
  apply inv_eq_of_mul_eq_one_left
  calc ((√5 - 1) / 4) * (1 + √5) = ((√5) ^ 2 - 1) / 4 := by ring
    _ = 1 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num

/-! ### Even and arbitrary coordinate permutations of `(0, ±1, ±φ, ±φ⁻¹) / 2` -/

/-- The base four-tuple `![0, ±1 / 2, ±φ / 2, ±φ⁻¹ / 2]` indexed by three sign bits. -/
noncomputable def icosahedralBaseTuple (b₁ b₂ b₃ : Bool) : Fin 4 → ℝ :=
  ![0, (if b₁ then -1 else 1) / 2, (if b₂ then -φ else φ) / 2,
    (if b₃ then -φ⁻¹ else φ⁻¹) / 2]

theorem icosahedralBaseTuple_def (b₁ b₂ b₃ : Bool) :
    icosahedralBaseTuple b₁ b₂ b₃ =
      ![0, (if b₁ then -1 else 1) / 2, (if b₂ then -φ else φ) / 2,
        (if b₃ then -φ⁻¹ else φ⁻¹) / 2] := (rfl)

/-- A quaternion in `ℍ[ℝ]` is an **icosahedral golden unit** if its four coordinates are an **even**
permutation of `(0, ±1 / 2, ±φ / 2, ±φ⁻¹ / 2)`. -/
def IsIcosahedralGoldenUnit (q : ℍ[ℝ]) : Prop :=
  ∃ σ ∈ alternatingGroup (Fin 4), ∃ b₁ b₂ b₃ : Bool,
    equivTuple ℝ q = icosahedralBaseTuple b₁ b₂ b₃ ∘ σ

theorem isIcosahedralGoldenUnit_def (q : ℍ[ℝ]) :
    q.IsIcosahedralGoldenUnit ↔ ∃ σ ∈ alternatingGroup (Fin 4), ∃ b₁ b₂ b₃ : Bool,
      equivTuple ℝ q = icosahedralBaseTuple b₁ b₂ b₃ ∘ σ := Iff.rfl

/-- A quaternion in `ℍ[ℝ]` is an **all-permutation golden unit** if its four coordinates are *any*
permutation (even or odd) of `(0, ±1 / 2, ±φ / 2, ±φ⁻¹ / 2)`. -/
def IsAllPermGoldenUnit (q : ℍ[ℝ]) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), ∃ b₁ b₂ b₃ : Bool,
    equivTuple ℝ q = icosahedralBaseTuple b₁ b₂ b₃ ∘ σ

theorem isAllPermGoldenUnit_def (q : ℍ[ℝ]) :
    q.IsAllPermGoldenUnit ↔ ∃ σ : Equiv.Perm (Fin 4), ∃ b₁ b₂ b₃ : Bool,
      equivTuple ℝ q = icosahedralBaseTuple b₁ b₂ b₃ ∘ σ := Iff.rfl

theorem IsIcosahedralGoldenUnit.isAllPermGoldenUnit {q : ℍ[ℝ]} (hq : q.IsIcosahedralGoldenUnit) :
    q.IsAllPermGoldenUnit := by
  obtain ⟨σ, -, b₁, b₂, b₃, h⟩ := hq
  exact ⟨σ, b₁, b₂, b₃, h⟩

/-- Explicit parametrization of the `192` all-permutation golden units by `S₄ × Bool³`. -/
noncomputable def allPermGoldenUnit (idx : Equiv.Perm (Fin 4) × Bool × Bool × Bool) : ℍ[ℝ] :=
  (equivTuple ℝ).symm (icosahedralBaseTuple idx.2.1 idx.2.2.1 idx.2.2.2 ∘ idx.1)

/-- Explicit parametrization of the `96` icosahedral golden units by `A₄ × Bool³`. -/
noncomputable def icosahedralGoldenUnit
    (idx : alternatingGroup (Fin 4) × Bool × Bool × Bool) : ℍ[ℝ] :=
  allPermGoldenUnit (idx.1.1, idx.2)

theorem equivTuple_allPermGoldenUnit (idx : Equiv.Perm (Fin 4) × Bool × Bool × Bool) :
    equivTuple ℝ (allPermGoldenUnit idx) =
      icosahedralBaseTuple idx.2.1 idx.2.2.1 idx.2.2.2 ∘ idx.1 :=
  (equivTuple ℝ).apply_symm_apply _

theorem equivTuple_icosahedralGoldenUnit (idx : alternatingGroup (Fin 4) × Bool × Bool × Bool) :
    equivTuple ℝ (icosahedralGoldenUnit idx) =
      icosahedralBaseTuple idx.2.1 idx.2.2.1 idx.2.2.2 ∘ idx.1.1 :=
  (equivTuple ℝ).apply_symm_apply _

private noncomputable def goldenSqCoord : Fin 4 → ℝ :=
  ![0, 1 / 4, (φ + 1) / 4, (2 - φ) / 4]

private theorem icosahedralBaseTuple_sq (b₁ b₂ b₃ : Bool) (t : Fin 4) :
    (icosahedralBaseTuple b₁ b₂ b₃ t) ^ 2 = goldenSqCoord t := by
  fin_cases t
  · simp [icosahedralBaseTuple, goldenSqCoord]
  · cases b₁ <;> simp [icosahedralBaseTuple, goldenSqCoord] <;> norm_num
  · cases b₂ <;> simp [icosahedralBaseTuple, goldenSqCoord] <;>
      grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]
  · cases b₃ <;> simp [icosahedralBaseTuple, goldenSqCoord] <;>
      grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]

private theorem injective_goldenSqCoord : Function.Injective goldenSqCoord := by
  intro i j hij
  have h1 := Real.one_lt_goldenRatio
  have h2 := Real.goldenRatio_lt_two
  fin_cases i <;> fin_cases j <;> simp [goldenSqCoord] at hij ⊢ <;> linarith

theorem injective_allPermGoldenUnit : Function.Injective allPermGoldenUnit := by
  rintro ⟨σ₁, b₁, b₂, b₃⟩ ⟨σ₂, c₁, c₂, c₃⟩ h
  have ht : icosahedralBaseTuple b₁ b₂ b₃ ∘ σ₁ = icosahedralBaseTuple c₁ c₂ c₃ ∘ σ₂ := by
    simpa only [equivTuple_allPermGoldenUnit] using congrArg (equivTuple ℝ) h
  have hσ : σ₁ = σ₂ := Equiv.ext fun s => injective_goldenSqCoord <| by
    have hs := congrArg (· ^ 2) (congrFun ht s)
    simpa only [Function.comp_apply, icosahedralBaseTuple_sq] using hs
  subst hσ
  have _ := Real.one_lt_goldenRatio
  have _ : (0 : ℝ) < φ⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have hb₁ : b₁ = c₁ := by
    have h1 : (if b₁ then -1 else (1 : ℝ)) / 2 = (if c₁ then -1 else 1) / 2 := by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply, icosahedralBaseTuple,
        Matrix.cons_val_one, Matrix.cons_val_zero] using congrFun ht (σ₁.symm 1)
    cases b₁ <;> cases c₁ <;> simp only [Bool.false_eq_true, ↓reduceIte] at h1 ⊢ <;> linarith
  have hb₂ : b₂ = c₂ := by
    have h2 : (if b₂ then -φ else φ) / 2 = (if c₂ then -φ else φ) / 2 := by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply, icosahedralBaseTuple,
        Matrix.cons_val] using congrFun ht (σ₁.symm 2)
    cases b₂ <;> cases c₂ <;> simp only [Bool.false_eq_true, ↓reduceIte] at h2 ⊢ <;> linarith
  have hb₃ : b₃ = c₃ := by
    have h3 : (if b₃ then -φ⁻¹ else φ⁻¹) / 2 = (if c₃ then -φ⁻¹ else φ⁻¹) / 2 := by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply, icosahedralBaseTuple,
        Matrix.cons_val] using congrFun ht (σ₁.symm 3)
    cases b₃ <;> cases c₃ <;> simp only [Bool.false_eq_true, ↓reduceIte] at h3 ⊢ <;> linarith
  subst hb₁ hb₂ hb₃
  rfl

theorem injective_icosahedralGoldenUnit : Function.Injective icosahedralGoldenUnit := by
  rintro ⟨σ₁, b₁⟩ ⟨σ₂, b₂⟩ h
  have hinj := injective_allPermGoldenUnit h
  rw [Prod.mk.injEq] at hinj
  exact Prod.ext (Subtype.ext hinj.1) hinj.2

theorem range_allPermGoldenUnit :
    Set.range allPermGoldenUnit = {q : ℍ[ℝ] | q.IsAllPermGoldenUnit} := by
  ext q
  refine ⟨?_, fun ⟨σ, b₁, b₂, b₃, hq⟩ =>
    ⟨(σ, b₁, b₂, b₃), (equivTuple ℝ).injective ((equivTuple_allPermGoldenUnit _).trans hq.symm)⟩⟩
  rintro ⟨⟨σ, b₁, b₂, b₃⟩, rfl⟩
  exact ⟨σ, b₁, b₂, b₃, equivTuple_allPermGoldenUnit _⟩

theorem range_icosahedralGoldenUnit :
    Set.range icosahedralGoldenUnit = {q : ℍ[ℝ] | q.IsIcosahedralGoldenUnit} := by
  ext q
  refine ⟨?_, fun ⟨σ, hσ, b₁, b₂, b₃, hq⟩ =>
    ⟨(⟨σ, hσ⟩, b₁, b₂, b₃),
      (equivTuple ℝ).injective ((equivTuple_icosahedralGoldenUnit _).trans hq.symm)⟩⟩
  rintro ⟨⟨⟨σ, hσ⟩, b₁, b₂, b₃⟩, rfl⟩
  exact ⟨σ, hσ, b₁, b₂, b₃, equivTuple_icosahedralGoldenUnit _⟩

theorem finite_isAllPermGoldenUnit : {q : ℍ[ℝ] | q.IsAllPermGoldenUnit}.Finite := by
  rw [← range_allPermGoldenUnit]
  exact Set.finite_range _

theorem finite_isIcosahedralGoldenUnit : {q : ℍ[ℝ] | q.IsIcosahedralGoldenUnit}.Finite := by
  rw [← range_icosahedralGoldenUnit]
  exact Set.finite_range _

/-- Allowing all `24` coordinate permutations gives `192` distinct golden units. -/
@[simp]
theorem ncard_isAllPermGoldenUnit : {q : ℍ[ℝ] | q.IsAllPermGoldenUnit}.ncard = 192 := by
  rw [← range_allPermGoldenUnit, Set.ncard_range_of_injective injective_allPermGoldenUnit,
    Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_perm, Fintype.card_fin]
  decide

/-- Restricting to **even** coordinate permutations gives `96` distinct golden units. -/
@[simp]
theorem ncard_isIcosahedralGoldenUnit : {q : ℍ[ℝ] | q.IsIcosahedralGoldenUnit}.ncard = 96 := by
  rw [← range_icosahedralGoldenUnit, Set.ncard_range_of_injective injective_icosahedralGoldenUnit,
    Nat.card_prod, Nat.card_prod, Nat.card_prod, nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem disjoint_isTetrahedralUnit_isAllPermGoldenUnit :
    Disjoint {q : ℍ[ℝ] | q.IsTetrahedralUnit} {q : ℍ[ℝ] | q.IsAllPermGoldenUnit} := by
  rw [Set.disjoint_left]
  rintro q htet ⟨σ, b₁, b₂, b₃, hq⟩
  have hsq : (equivTuple ℝ q (σ.symm 2)) ^ 2 = (φ + 1) / 4 := by
    rw [hq, Function.comp_apply, Equiv.apply_symm_apply, icosahedralBaseTuple_sq]
    rfl
  have _ := Real.one_lt_goldenRatio
  have _ := Real.goldenRatio_lt_two
  rcases htet.coord_sq_mem (σ.symm 2) with h | h | h <;> linarith

theorem disjoint_isTetrahedralUnit_isIcosahedralGoldenUnit :
    Disjoint {q : ℍ[ℝ] | q.IsTetrahedralUnit} {q : ℍ[ℝ] | q.IsIcosahedralGoldenUnit} :=
  disjoint_isTetrahedralUnit_isAllPermGoldenUnit.mono_right fun _ h => h.isAllPermGoldenUnit

/-! ### The 120 vertices of the unit `600`-cell and the `216`-point non-closure check -/

/-- A quaternion in `ℍ[ℝ]` is an **icosahedral unit** (a vertex of the unit `600`-cell) if it is
either one of the `24` Hurwitz tetrahedral units or one of the `96` even-permutation golden
units. -/
def IsIcosahedralUnit (q : ℍ[ℝ]) : Prop :=
  q.IsTetrahedralUnit ∨ q.IsIcosahedralGoldenUnit

theorem isIcosahedralUnit_def (q : ℍ[ℝ]) :
    q.IsIcosahedralUnit ↔ q.IsTetrahedralUnit ∨ q.IsIcosahedralGoldenUnit := Iff.rfl

theorem finite_isIcosahedralUnit : {q : ℍ[ℝ] | q.IsIcosahedralUnit}.Finite :=
  finite_isTetrahedralUnit.union finite_isIcosahedralGoldenUnit

/-- **The 120 vertices of the unit `600`-cell are pairwise distinct.** -/
@[simp]
theorem ncard_isIcosahedralUnit : {q : ℍ[ℝ] | q.IsIcosahedralUnit}.ncard = 120 := by
  have heq : {q : ℍ[ℝ] | q.IsIcosahedralUnit} =
      {q : ℍ[ℝ] | q.IsTetrahedralUnit} ∪ {q : ℍ[ℝ] | q.IsIcosahedralGoldenUnit} := rfl
  rw [heq, Set.ncard_union_eq disjoint_isTetrahedralUnit_isIcosahedralGoldenUnit
    finite_isTetrahedralUnit finite_isIcosahedralGoldenUnit,
    ncard_isTetrahedralUnit, ncard_isIcosahedralGoldenUnit]

/-- **Allowing all coordinate permutations gives `24 + 192 = 216` distinct unit quaternions.** -/
@[simp]
theorem ncard_isTetrahedralUnit_or_isAllPermGoldenUnit :
    {q : ℍ[ℝ] | q.IsTetrahedralUnit ∨ q.IsAllPermGoldenUnit}.ncard = 216 := by
  have heq : {q : ℍ[ℝ] | q.IsTetrahedralUnit ∨ q.IsAllPermGoldenUnit} =
      {q : ℍ[ℝ] | q.IsTetrahedralUnit} ∪ {q : ℍ[ℝ] | q.IsAllPermGoldenUnit} := rfl
  rw [heq, Set.ncard_union_eq disjoint_isTetrahedralUnit_isAllPermGoldenUnit
    finite_isTetrahedralUnit finite_isAllPermGoldenUnit,
    ncard_isTetrahedralUnit, ncard_isAllPermGoldenUnit]

/-- **Witness that odd coordinate permutations break multiplicative closure**: the even golden unit
`(i + φ j + φ⁻¹ k) / 2` and the odd golden unit `(1 + φ j + φ⁻¹ k) / 2` have product with real part
`-3 / 4`, which lies outside the `216`-element all-permutation set. -/
theorem exists_mul_not_isTetrahedralUnit_or_isAllPermGoldenUnit :
    ∃ p q : ℍ[ℝ], p.IsAllPermGoldenUnit ∧ q.IsAllPermGoldenUnit ∧
      ¬ ((p * q).IsTetrahedralUnit ∨ (p * q).IsAllPermGoldenUnit) := by
  refine ⟨⟨0, 1 / 2, φ / 2, φ⁻¹ / 2⟩, ⟨1 / 2, 0, φ / 2, φ⁻¹ / 2⟩, ?_, ?_, ?_⟩
  · refine ⟨1, false, false, false, ?_⟩
    ext s; fin_cases s <;> simp [icosahedralBaseTuple]
  · refine ⟨Equiv.swap 0 1, false, false, false, ?_⟩
    ext s; fin_cases s <;> simp [icosahedralBaseTuple, Equiv.swap_apply_def]
  · have hre : (equivTuple ℝ ((⟨0, 1 / 2, φ / 2, φ⁻¹ / 2⟩ : ℍ[ℝ]) *
        ⟨1 / 2, 0, φ / 2, φ⁻¹ / 2⟩) 0) ^ 2 = 9 / 16 := by
      have hre0 : ((⟨0, 1 / 2, φ / 2, φ⁻¹ / 2⟩ : ℍ[ℝ]) * ⟨1 / 2, 0, φ / 2, φ⁻¹ / 2⟩).re =
          -(3 / 4) := by
        simp; grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]
      rw [equivTuple_apply, Matrix.cons_val_zero, hre0]
      norm_num
    rintro (htet | ⟨σ, b₁, b₂, b₃, hq⟩)
    · rcases htet.coord_sq_mem 0 with h | h | h <;> linarith
    · have hsq : goldenSqCoord (σ 0) = 9 / 16 := by
        rw [← icosahedralBaseTuple_sq b₁ b₂ b₃ (σ 0), ← Function.comp_apply (f :=
          icosahedralBaseTuple b₁ b₂ b₃), ← hq, hre]
      have hφ : φ ≠ 5 / 4 := fun h => by
        have h2 := Real.goldenRatio_sq
        rw [h] at h2
        norm_num at h2
      have _ := Real.one_lt_goldenRatio
      generalize σ 0 = k at hsq
      fin_cases k
      · simp [goldenSqCoord] at hsq; norm_num at hsq
      · simp [goldenSqCoord] at hsq; norm_num at hsq
      · simp [goldenSqCoord] at hsq; exact hφ (by linarith)
      · simp [goldenSqCoord] at hsq; linarith

/-- **The `216`-element set obtained from all coordinate permutations is not closed under
multiplication.** -/
theorem not_forall_mul_isTetrahedralUnit_or_isAllPermGoldenUnit :
    ¬ ∀ p q : ℍ[ℝ],
      (p.IsTetrahedralUnit ∨ p.IsAllPermGoldenUnit) →
      (q.IsTetrahedralUnit ∨ q.IsAllPermGoldenUnit) →
      ((p * q).IsTetrahedralUnit ∨ (p * q).IsAllPermGoldenUnit) := by
  intro hall
  obtain ⟨p, q, hp, hq, hnot⟩ := exists_mul_not_isTetrahedralUnit_or_isAllPermGoldenUnit
  exact hnot (hall p q (.inr hp) (.inr hq))

/-! ### Reduced norm and sign symmetries -/

theorem IsAllPermGoldenUnit.normSq_eq_one {q : ℍ[ℝ]} (hq : q.IsAllPermGoldenUnit) :
    q.normSq = 1 := by
  obtain ⟨σ, b₁, b₂, b₃, hq⟩ := hq
  have hsum : q.normSq = ∑ s : Fin 4, (equivTuple ℝ q s) ^ 2 := by
    rw [normSq_def', Fin.sum_univ_four]
    rfl
  simp_rw [hsum, hq, Function.comp_apply, icosahedralBaseTuple_sq, Equiv.sum_comp σ goldenSqCoord,
    Fin.sum_univ_four, goldenSqCoord]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem IsIcosahedralGoldenUnit.normSq_eq_one {q : ℍ[ℝ]} (hq : q.IsIcosahedralGoldenUnit) :
    q.normSq = 1 :=
  hq.isAllPermGoldenUnit.normSq_eq_one

theorem IsIcosahedralUnit.normSq_eq_one {q : ℍ[ℝ]} (hq : q.IsIcosahedralUnit) : q.normSq = 1 :=
  hq.elim IsTetrahedralUnit.normSq_eq_one IsIcosahedralGoldenUnit.normSq_eq_one

theorem IsIcosahedralUnit.mem_unitary {q : ℍ[ℝ]} (hq : q.IsIcosahedralUnit) : q ∈ unitary ℍ[ℝ] :=
  (mem_unitary_iff_normSq_eq_one q).mpr hq.normSq_eq_one

theorem IsIcosahedralUnit.one : (1 : ℍ[ℝ]).IsIcosahedralUnit :=
  .inl IsTetrahedralUnit.one

private def flipBaseSign (k : Fin 4) (b : Bool × Bool × Bool) : Bool × Bool × Bool :=
  match k with
  | 0 => b
  | 1 => (!b.1, b.2.1, b.2.2)
  | 2 => (b.1, !b.2.1, b.2.2)
  | 3 => (b.1, b.2.1, !b.2.2)

private theorem icosahedralBaseTuple_flipBaseSign
    (k : Fin 4) (b : Bool × Bool × Bool) (t : Fin 4) :
    icosahedralBaseTuple (flipBaseSign k b).1 (flipBaseSign k b).2.1 (flipBaseSign k b).2.2 t =
      if t = k then -icosahedralBaseTuple b.1 b.2.1 b.2.2 t
      else icosahedralBaseTuple b.1 b.2.1 b.2.2 t := by
  rcases b with ⟨b₁, b₂, b₃⟩
  fin_cases k <;> fin_cases t <;> cases b₁ <;> cases b₂ <;> cases b₃ <;>
    simp [flipBaseSign, icosahedralBaseTuple] <;> ring

private theorem swap_mul_swap_mem_alternatingGroup {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 4) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  rfl

theorem IsIcosahedralGoldenUnit.neg {q : ℍ[ℝ]} (hq : q.IsIcosahedralGoldenUnit) :
    (-q).IsIcosahedralGoldenUnit := by
  obtain ⟨σ, hσ, b₁, b₂, b₃, hq⟩ := hq
  refine ⟨σ, hσ, !b₁, !b₂, !b₃, ?_⟩
  ext s
  have hs := congrFun hq s
  have hneg : equivTuple ℝ (-q) s = -equivTuple ℝ q s := by fin_cases s <;> rfl
  rw [hneg, hs, Function.comp_apply, Function.comp_apply]
  generalize σ s = k
  fin_cases k <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> simp [icosahedralBaseTuple] <;> ring

theorem IsIcosahedralUnit.neg {q : ℍ[ℝ]} (hq : q.IsIcosahedralUnit) : (-q).IsIcosahedralUnit :=
  hq.imp IsTetrahedralUnit.neg IsIcosahedralGoldenUnit.neg

theorem IsIcosahedralGoldenUnit.star {q : ℍ[ℝ]} (hq : q.IsIcosahedralGoldenUnit) :
    (Star.star q).IsIcosahedralGoldenUnit := by
  obtain ⟨σ, hσ, b₁, b₂, b₃, hq⟩ := hq
  let b' := flipBaseSign (σ 1) (flipBaseSign (σ 2) (flipBaseSign (σ 3) (b₁, b₂, b₃)))
  refine ⟨σ, hσ, b'.1, b'.2.1, b'.2.2, ?_⟩
  have h0 := congrFun hq 0
  have h1 := congrFun hq 1
  have h2 := congrFun hq 2
  have h3 := congrFun hq 3
  ext s
  simp only [b', Function.comp_apply, icosahedralBaseTuple_flipBaseSign, σ.injective.eq_iff]
  fin_cases s
  · simpa using h0
  · simpa using neg_inj.mpr h1
  · simpa using neg_inj.mpr h2
  · simpa using neg_inj.mpr h3

theorem IsIcosahedralUnit.star {q : ℍ[ℝ]} (hq : q.IsIcosahedralUnit) :
    (Star.star q).IsIcosahedralUnit :=
  hq.imp IsTetrahedralUnit.star IsIcosahedralGoldenUnit.star

private theorem IsIcosahedralGoldenUnit.mul_i {q : ℍ[ℝ]} (hq : q.IsIcosahedralGoldenUnit) :
    (q * ⟨0, 1, 0, 0⟩).IsIcosahedralGoldenUnit := by
  obtain ⟨σ, hσ, b₁, b₂, b₃, hq⟩ := hq
  let τ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  have hτ : τ ∈ alternatingGroup (Fin 4) :=
    swap_mul_swap_mem_alternatingGroup (by decide) (by decide)
  let σ' := σ * τ
  let b' := flipBaseSign (σ' 0) (flipBaseSign (σ' 3) (b₁, b₂, b₃))
  refine ⟨σ', mul_mem hσ hτ, b'.1, b'.2.1, b'.2.2, ?_⟩
  have h0 := congrFun hq 0
  have h1 := congrFun hq 1
  have h2 := congrFun hq 2
  have h3 := congrFun hq 3
  ext s
  simp only [b', Function.comp_apply, icosahedralBaseTuple_flipBaseSign, σ'.injective.eq_iff]
  fin_cases s
  · simpa [σ', τ, Equiv.swap_apply_def] using neg_inj.mpr h1
  · simpa [σ', τ, Equiv.swap_apply_def] using h0
  · simpa [σ', τ, Equiv.swap_apply_def] using h3
  · simpa [σ', τ, Equiv.swap_apply_def] using neg_inj.mpr h2

private theorem IsIcosahedralGoldenUnit.mul_j {q : ℍ[ℝ]} (hq : q.IsIcosahedralGoldenUnit) :
    (q * ⟨0, 0, 1, 0⟩).IsIcosahedralGoldenUnit := by
  obtain ⟨σ, hσ, b₁, b₂, b₃, hq⟩ := hq
  let τ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
  have hτ : τ ∈ alternatingGroup (Fin 4) :=
    swap_mul_swap_mem_alternatingGroup (by decide) (by decide)
  let σ' := σ * τ
  let b' := flipBaseSign (σ' 0) (flipBaseSign (σ' 1) (b₁, b₂, b₃))
  refine ⟨σ', mul_mem hσ hτ, b'.1, b'.2.1, b'.2.2, ?_⟩
  have h0 := congrFun hq 0
  have h1 := congrFun hq 1
  have h2 := congrFun hq 2
  have h3 := congrFun hq 3
  ext s
  simp only [b', Function.comp_apply, icosahedralBaseTuple_flipBaseSign, σ'.injective.eq_iff]
  fin_cases s
  · simpa [σ', τ, Equiv.swap_apply_def] using neg_inj.mpr h2
  · simpa [σ', τ, Equiv.swap_apply_def] using neg_inj.mpr h3
  · simpa [σ', τ, Equiv.swap_apply_def] using h0
  · simpa [σ', τ, Equiv.swap_apply_def] using h1

private theorem IsIcosahedralGoldenUnit.mul_signedBasisUnit {q u : ℍ[ℝ]}
    (hq : q.IsIcosahedralGoldenUnit) (hu : u.IsSignedBasisUnit) :
    (q * u).IsIcosahedralGoldenUnit := by
  rcases u with ⟨a, b, c, d⟩
  rcases isSignedBasisUnit_iff_coordinates.mp hu with
    ⟨rfl | rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl | rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl | rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩
  · rw [show (⟨1, 0, 0, 0⟩ : ℍ[ℝ]) = 1 from rfl, mul_one]; exact hq
  · rw [show (⟨-1, 0, 0, 0⟩ : ℍ[ℝ]) = -1 by ext <;> norm_num, mul_neg, mul_one]; exact hq.neg
  · exact hq.mul_i
  · rw [show (⟨0, -1, 0, 0⟩ : ℍ[ℝ]) = -⟨0, 1, 0, 0⟩ by ext <;> norm_num, mul_neg]
    exact hq.mul_i.neg
  · exact hq.mul_j
  · rw [show (⟨0, 0, -1, 0⟩ : ℍ[ℝ]) = -⟨0, 0, 1, 0⟩ by ext <;> norm_num, mul_neg]
    exact hq.mul_j.neg
  · rw [show (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) = ⟨0, 1, 0, 0⟩ * ⟨0, 0, 1, 0⟩ by ext <;> norm_num, ← mul_assoc]
    exact hq.mul_i.mul_j
  · rw [show (⟨0, 0, 0, -1⟩ : ℍ[ℝ]) = -(⟨0, 1, 0, 0⟩ * ⟨0, 0, 1, 0⟩) by ext <;> norm_num,
      mul_neg, ← mul_assoc]
    exact hq.mul_i.mul_j.neg

end Quaternion

namespace TauCeti

/-! ### The `<2, 3, 5>` generator, five-coset decomposition, and `600`-cell closure -/

private theorem goldenRatio_inv_eq' : φ⁻¹ = φ - 1 := by
  linarith [Real.inv_goldenRatio, Real.one_sub_goldenConj]

private theorem inv_one_add_sqrt_five : (1 + √5 : ℝ)⁻¹ = (√5 - 1) / 4 := by
  apply inv_eq_of_mul_eq_one_left
  calc ((√5 - 1) / 4) * (1 + √5) = ((√5) ^ 2 - 1) / 4 := by ring
    _ = 1 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num

/-- The `<2, 3, 5>` icosahedral generator `ζ = (φ + j + φ⁻¹ k) / 2` in `unitary ℍ[ℝ]`. -/
noncomputable def icosahedralGenerator : unitary ℍ[ℝ] :=
  ⟨⟨φ / 2, 0, 1 / 2, φ⁻¹ / 2⟩, (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr <| by
    rw [Quaternion.normSq_def', goldenRatio_inv_eq']
    linear_combination (1 / 2) * Real.goldenRatio_sq⟩

@[simp]
theorem coe_icosahedralGenerator :
    (icosahedralGenerator : ℍ[ℝ]) = ⟨φ / 2, 0, 1 / 2, φ⁻¹ / 2⟩ := (rfl)

private theorem coe_icosahedralGenerator_sq :
    ((icosahedralGenerator ^ 2 : unitary ℍ[ℝ]) : ℍ[ℝ]) = ⟨φ⁻¹ / 2, 0, φ / 2, 1 / 2⟩ := by
  rw [SubmonoidClass.coe_pow, sq, coe_icosahedralGenerator]
  ext <;> simp <;> grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]

private theorem coe_icosahedralGenerator_pow_three :
    ((icosahedralGenerator ^ 3 : unitary ℍ[ℝ]) : ℍ[ℝ]) = ⟨-(φ⁻¹ / 2), 0, φ / 2, 1 / 2⟩ := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one, MulMemClass.coe_mul,
    coe_icosahedralGenerator_sq, coe_icosahedralGenerator]
  ext <;> simp <;> grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]

private theorem coe_icosahedralGenerator_pow_four :
    ((icosahedralGenerator ^ 4 : unitary ℍ[ℝ]) : ℍ[ℝ]) = ⟨-(φ / 2), 0, 1 / 2, φ⁻¹ / 2⟩ := by
  rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, MulMemClass.coe_mul,
    coe_icosahedralGenerator_sq]
  ext <;> simp <;> grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]

/-- The `<2, 3, 5>` relation `ζ ^ 5 = -1`. -/
@[simp]
theorem icosahedralGenerator_pow_five : icosahedralGenerator ^ 5 = -1 := by
  refine Subtype.ext ?_
  rw [show (5 : ℕ) = 4 + 1 by rfl, pow_add, pow_one, MulMemClass.coe_mul,
    coe_icosahedralGenerator_pow_four, coe_icosahedralGenerator, Unitary.coe_neg,
    OneMemClass.coe_one]
  ext <;> simp <;> grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]

/-- The `<2, 3, 5>` relation `(ζ * ω) ^ 2 = -1`. -/
@[simp]
theorem icosahedralGenerator_mul_tetrahedralOmega_sq :
    (icosahedralGenerator * tetrahedralOmega) ^ 2 = -1 := by
  have hζω : ((icosahedralGenerator * tetrahedralOmega : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      ⟨0, 1 / 2, φ / 2, φ⁻¹ / 2⟩ := by
    ext <;> simp [coe_icosahedralGenerator, coe_tetrahedralOmega] <;>
      grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, sq, hζω, Unitary.coe_neg, OneMemClass.coe_one]
  ext <;> simp <;> grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]

/-- The `<2, 3, 5>` generators recover `j` via `ζ ^ 2 * ω * ζ⁻¹ = j`. -/
theorem icosahedralGenerator_sq_mul_tetrahedralOmega_mul_inv :
    icosahedralGenerator ^ 2 * tetrahedralOmega * icosahedralGenerator⁻¹ = quaternionUnitJ := by
  -- On `unitary ℍ[ℝ]`, group inversion is definitionally quaternion `star`.
  have hinv : ((icosahedralGenerator⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      ⟨φ / 2, 0, -(1 / 2), -(φ⁻¹ / 2)⟩ := by
    change Star.star (icosahedralGenerator : ℍ[ℝ]) = _
    rw [coe_icosahedralGenerator]
    ext <;> simp
  refine Subtype.ext ?_
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, coe_icosahedralGenerator_sq,
    coe_tetrahedralOmega, hinv, coe_quaternionUnitJ]
  ext <;> simp <;> grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]

/-- The icosahedral generator `ζ` has exact order `10` in `unitary ℍ[ℝ]`. -/
@[simp]
theorem orderOf_icosahedralGenerator : orderOf icosahedralGenerator = 10 := by
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ fun p hp hd => ?_
  · rw [show (10 : ℕ) = 5 * 2 by rfl, pow_mul, icosahedralGenerator_pow_five, neg_one_sq]
  · have := hp.two_le
    have hle : p ≤ 10 := Nat.le_of_dvd (by decide) hd
    interval_cases p
    · rw [Nat.div_eq_of_eq_mul_left (by decide) (by decide : 10 = 5 * 2),
        icosahedralGenerator_pow_five]
      intro h
      have hre := congrArg (fun u : unitary ℍ[ℝ] => (u : ℍ[ℝ]).re) h
      norm_num [Unitary.coe_neg] at hre
    · exact absurd hd (by decide)
    · exact absurd hp (by decide)
    · rw [Nat.div_eq_of_eq_mul_left (by decide) (by decide : 10 = 2 * 5)]
      intro h
      have himK := congrArg (fun u : unitary ℍ[ℝ] => (u : ℍ[ℝ]).imK) h
      rw [coe_icosahedralGenerator_sq, OneMemClass.coe_one] at himK
      norm_num at himK
    · exact absurd hd (by decide)
    · exact absurd hd (by decide)
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)

private theorem isIcosahedralGoldenUnit_of_coords {q : ℍ[ℝ]} {σ : Equiv.Perm (Fin 4)}
    (hσ : σ ∈ alternatingGroup (Fin 4)) (b₁ b₂ b₃ : Bool)
    (h0 : q.re = Quaternion.icosahedralBaseTuple b₁ b₂ b₃ (σ 0))
    (h1 : q.imI = Quaternion.icosahedralBaseTuple b₁ b₂ b₃ (σ 1))
    (h2 : q.imJ = Quaternion.icosahedralBaseTuple b₁ b₂ b₃ (σ 2))
    (h3 : q.imK = Quaternion.icosahedralBaseTuple b₁ b₂ b₃ (σ 3)) :
    q.IsIcosahedralGoldenUnit := by
  refine ⟨σ, hσ, b₁, b₂, b₃, ?_⟩
  ext s
  fin_cases s <;> assumption

private theorem swap_mul_swap_mem_alt {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 4) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  rfl

private theorem isIcosahedralGoldenUnit_pow (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4) :
    ((icosahedralGenerator ^ m : unitary ℍ[ℝ]) : ℍ[ℝ]).IsIcosahedralGoldenUnit := by
  interval_cases m
  · rw [pow_one, coe_icosahedralGenerator]
    exact isIcosahedralGoldenUnit_of_coords (swap_mul_swap_mem_alt (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 2)) false false false
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def])
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def])
      (by simp [Quaternion.icosahedralBaseTuple])
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def])
  · rw [coe_icosahedralGenerator_sq]
    exact isIcosahedralGoldenUnit_of_coords (swap_mul_swap_mem_alt (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 3)) false false false
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def])
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def])
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def])
      (by simp [Quaternion.icosahedralBaseTuple])
  · rw [coe_icosahedralGenerator_pow_three]
    exact isIcosahedralGoldenUnit_of_coords (swap_mul_swap_mem_alt (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 3)) false false true
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def]; ring)
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def])
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def])
      (by simp [Quaternion.icosahedralBaseTuple])
  · rw [coe_icosahedralGenerator_pow_four]
    exact isIcosahedralGoldenUnit_of_coords (swap_mul_swap_mem_alt (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 2)) false true false
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def]; ring)
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def])
      (by simp [Quaternion.icosahedralBaseTuple])
      (by simp [Quaternion.icosahedralBaseTuple, Equiv.swap_apply_def])

open Equiv Quaternion in
private theorem isIcosahedralGoldenUnit_pow_mul_omega (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4) :
    ((icosahedralGenerator ^ m * tetrahedralOmega : unitary ℍ[ℝ]) :
      ℍ[ℝ]).IsIcosahedralGoldenUnit := by
  interval_cases m
  · rw [pow_one, MulMemClass.coe_mul, coe_icosahedralGenerator, coe_tetrahedralOmega]
    exact isIcosahedralGoldenUnit_of_coords (one_mem _) false false false
      (by simp [icosahedralBaseTuple]; grind [Real.goldenRatio_sq, inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple]; grind [Real.goldenRatio_sq, inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple]; grind [Real.goldenRatio_sq, inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple]; grind [Real.goldenRatio_sq, inv_one_add_sqrt_five])
  · rw [MulMemClass.coe_mul, coe_icosahedralGenerator_sq, coe_tetrahedralOmega]
    exact isIcosahedralGoldenUnit_of_coords (swap_mul_swap_mem_alt (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (0 : Fin 4) ≠ 1)) true false false
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
  · rw [MulMemClass.coe_mul, coe_icosahedralGenerator_pow_three, coe_tetrahedralOmega]
    exact isIcosahedralGoldenUnit_of_coords (swap_mul_swap_mem_alt (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 2)) false true true
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
  · rw [MulMemClass.coe_mul, coe_icosahedralGenerator_pow_four, coe_tetrahedralOmega]
    exact isIcosahedralGoldenUnit_of_coords (swap_mul_swap_mem_alt (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (1 : Fin 4) ≠ 3)) true true true
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])

open Equiv Quaternion in
private theorem isIcosahedralGoldenUnit_pow_mul_omega_sq (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4) :
    ((icosahedralGenerator ^ m * tetrahedralOmega ^ 2 : unitary ℍ[ℝ]) :
      ℍ[ℝ]).IsIcosahedralGoldenUnit := by
  have hω2 : ((tetrahedralOmega ^ 2 : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      ⟨-(1 / 2), 1 / 2, 1 / 2, 1 / 2⟩ := by
    rw [SubmonoidClass.coe_pow, sq, coe_tetrahedralOmega]
    ext <;> norm_num
  interval_cases m
  · rw [pow_one, MulMemClass.coe_mul, coe_icosahedralGenerator, hω2]
    exact isIcosahedralGoldenUnit_of_coords (swap_mul_swap_mem_alt (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (0 : Fin 4) ≠ 2)) false true false
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
  · rw [MulMemClass.coe_mul, coe_icosahedralGenerator_sq, hω2]
    exact isIcosahedralGoldenUnit_of_coords (swap_mul_swap_mem_alt (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (1 : Fin 4) ≠ 3)) true true false
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
  · rw [MulMemClass.coe_mul, coe_icosahedralGenerator_pow_three, hω2]
    exact isIcosahedralGoldenUnit_of_coords (swap_mul_swap_mem_alt (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (2 : Fin 4) ≠ 3)) true true true
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
  · rw [MulMemClass.coe_mul, coe_icosahedralGenerator_pow_four, hω2]
    exact isIcosahedralGoldenUnit_of_coords (swap_mul_swap_mem_alt (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (1 : Fin 4) ≠ 3)) true true true
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple, swap_apply_def]; grind [inv_one_add_sqrt_five])
      (by simp [icosahedralBaseTuple]; grind [inv_one_add_sqrt_five])

private theorem isIcosahedralGoldenUnit_pow_mul_omega_pow
    (m a : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4) (ha : a < 3) :
    ((icosahedralGenerator ^ m * tetrahedralOmega ^ a : unitary ℍ[ℝ]) :
      ℍ[ℝ]).IsIcosahedralGoldenUnit := by
  interval_cases a
  · simpa using isIcosahedralGoldenUnit_pow m hm1 hm4
  · simpa using isIcosahedralGoldenUnit_pow_mul_omega m hm1 hm4
  · exact isIcosahedralGoldenUnit_pow_mul_omega_sq m hm1 hm4

private theorem exists_omega_pow_mul_signedBasis_of_mem_tetrahedral {u : unitary ℍ[ℝ]}
    (hu : u ∈ binaryTetrahedralUnitSubgroup) :
    ∃ a < 3, ∃ b : unitary ℍ[ℝ], (b : ℍ[ℝ]).IsSignedBasisUnit ∧
      u = tetrahedralOmega ^ a * b := by
  have hneg_basis {x : ℍ[ℝ]} (hx : x.IsSignedBasisUnit) : (-x).IsSignedBasisUnit := by
    obtain ⟨r, hr, h0⟩ := (Quaternion.isSignedBasisUnit_def x).mp hx
    refine (Quaternion.isSignedBasisUnit_def (-x)).mpr ⟨r, ?_, fun s hs => by
      rw [show Quaternion.equivTuple ℝ (-x) s = -Quaternion.equivTuple ℝ x s by fin_cases s <;> rfl,
        h0 s hs, neg_zero]⟩
    rw [show Quaternion.equivTuple ℝ (-x) r = -Quaternion.equivTuple ℝ x r by fin_cases r <;> rfl]
    rcases hr with h | h <;> [right; left] <;> simp [h]
  rcases (Quaternion.isTetrahedralUnit_def _).mp (mem_binaryTetrahedralUnitSubgroup_iff.mp hu) with
    hbasis | hhalf
  · exact ⟨0, by decide, u, hbasis, by simp⟩
  · have h1 := mem_binaryTetrahedralUnitSubgroup_iff.mp
      (mul_mem tetrahedralOmega_mem_binaryTetrahedralUnitSubgroup hu)
    rcases (Quaternion.isTetrahedralUnit_def _).mp h1 with hb1 | hh1
    · refine ⟨2, by decide, -(tetrahedralOmega * u), hneg_basis hb1, ?_⟩
      rw [mul_neg, ← mul_assoc, ← pow_succ, tetrahedralOmega_pow_three, neg_one_mul, neg_neg]
    · have h2 := mem_binaryTetrahedralUnitSubgroup_iff.mp
        (mul_mem tetrahedralOmega_mem_binaryTetrahedralUnitSubgroup
          (mul_mem tetrahedralOmega_mem_binaryTetrahedralUnitSubgroup hu))
      rcases (Quaternion.isTetrahedralUnit_def _).mp h2 with hb2 | hh2
      · refine ⟨1, by decide, -(tetrahedralOmega * (tetrahedralOmega * u)), hneg_basis hb2, ?_⟩
        symm
        rw [pow_one, mul_neg, ← mul_assoc, ← mul_assoc, ← sq, ← pow_succ,
          tetrahedralOmega_pow_three, neg_one_mul, neg_neg]
      · exfalso
        rw [MulMemClass.coe_mul] at hh1
        rw [MulMemClass.coe_mul, MulMemClass.coe_mul] at hh2
        rcases hq : (u : ℍ[ℝ]) with ⟨a, b, c, d⟩
        rw [hq, Quaternion.isHalfUnit_iff_coordinates] at hhalf
        dsimp only at hhalf
        have h12 : ((tetrahedralOmega : ℍ[ℝ]) * ⟨a, b, c, d⟩).IsHalfUnit ∧
            ((tetrahedralOmega : ℍ[ℝ]) *
              ((tetrahedralOmega : ℍ[ℝ]) * ⟨a, b, c, d⟩)).IsHalfUnit := by
          rw [← hq]
          exact ⟨hh1, hh2⟩
        obtain ⟨rfl | rfl, rfl | rfl, rfl | rfl, rfl | rfl⟩ := hhalf <;>
          · rw [Quaternion.isHalfUnit_iff_coordinates,
              Quaternion.isHalfUnit_iff_coordinates] at h12
            norm_num [coe_tetrahedralOmega] at h12

private theorem isIcosahedralGoldenUnit_pow_mul_tetrahedral
    {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) {t : unitary ℍ[ℝ]}
    (ht : t ∈ binaryTetrahedralUnitSubgroup) :
    ((icosahedralGenerator ^ m * t : unitary ℍ[ℝ]) : ℍ[ℝ]).IsIcosahedralGoldenUnit := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_omega_pow_mul_signedBasis_of_mem_tetrahedral ht
  rw [← mul_assoc, MulMemClass.coe_mul]
  exact (isIcosahedralGoldenUnit_pow_mul_omega_pow m a hm1 hm4 ha).mul_signedBasisUnit hb

private theorem disjoint_golden_coset_of_lt {m₁ m₂ : ℕ} (hm₂ : m₂ ≤ 4) (hlt : m₁ < m₂) :
    Disjoint ((icosahedralGenerator ^ m₁) • (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ])))
      ((icosahedralGenerator ^ m₂) • (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ]))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, heq⟩
  simp only [smul_eq_mul] at heq
  have hd : icosahedralGenerator ^ (m₂ - m₁) = t₁ * t₂⁻¹ := by
    have hpow : icosahedralGenerator ^ m₂ =
        icosahedralGenerator ^ m₁ * icosahedralGenerator ^ (m₂ - m₁) := by
      rw [← pow_add, Nat.add_sub_of_le hlt.le]
    have hmul : icosahedralGenerator ^ m₁ * (icosahedralGenerator ^ (m₂ - m₁) * t₂) =
        icosahedralGenerator ^ m₁ * t₁ := by
      simpa [hpow, mul_assoc] using heq
    exact eq_mul_inv_of_mul_eq (mul_left_cancel hmul)
  have htet : ((icosahedralGenerator ^ (m₂ - m₁) : unitary ℍ[ℝ]) : ℍ[ℝ]).IsTetrahedralUnit :=
    hd ▸ mem_binaryTetrahedralUnitSubgroup_iff.mp (mul_mem ht₁ (inv_mem ht₂))
  have hgold : ((icosahedralGenerator ^ (m₂ - m₁) : unitary ℍ[ℝ]) : ℍ[ℝ]).IsIcosahedralGoldenUnit :=
    isIcosahedralGoldenUnit_pow (m₂ - m₁) (by omega) (by omega)
  exact Set.disjoint_left.mp Quaternion.disjoint_isTetrahedralUnit_isIcosahedralGoldenUnit
    htet hgold

private theorem pairwiseDisjoint_golden_cosets :
    Set.PairwiseDisjoint (Finset.Icc 1 4 : Set ℕ)
      (fun m => (icosahedralGenerator ^ m) •
        (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ]))) := by
  intro m₁ hm₁ m₂ hm₂ hne
  simp only [Finset.coe_Icc, Set.mem_Icc] at hm₁ hm₂
  rcases lt_trichotomy m₁ m₂ with hlt | rfl | hgt
  · exact disjoint_golden_coset_of_lt hm₂.2 hlt
  · exact absurd rfl hne
  · exact (disjoint_golden_coset_of_lt hm₁.2 hgt).symm

private theorem golden_unit_set_eq_biUnion_cosets :
    {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralGoldenUnit} =
      ⋃ m ∈ (Finset.Icc 1 4 : Finset ℕ),
        (icosahedralGenerator ^ m) • (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ])) := by
  have hfinT : (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ])).Finite := by
    convert Quaternion.finite_isTetrahedralUnit.preimage Subtype.val_injective.injOn
    ext u
    exact mem_binaryTetrahedralUnitSubgroup_iff
  have hfinG : {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralGoldenUnit}.Finite :=
    Quaternion.finite_isIcosahedralGoldenUnit.preimage Subtype.val_injective.injOn
  have hcardT : (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ])).ncard = 24 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, natCard_binaryTetrahedralUnitSubgroup]
  have hcardG : {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralGoldenUnit}.ncard = 96 := by
    have himg : Subtype.val '' {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralGoldenUnit} =
        {q : ℍ[ℝ] | q.IsIcosahedralGoldenUnit} := by
      ext q
      refine ⟨?_, fun hq =>
        ⟨⟨q, ((Quaternion.isIcosahedralUnit_def q).mpr (.inr hq)).mem_unitary⟩, hq, rfl⟩⟩
      rintro ⟨u, hu, rfl⟩
      exact hu
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg,
      Quaternion.ncard_isIcosahedralGoldenUnit]
  have hsub : (⋃ m ∈ (Finset.Icc 1 4 : Finset ℕ),
      (icosahedralGenerator ^ m) • (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ]))) ⊆
        {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralGoldenUnit} := by
    intro u hu
    simp only [Set.mem_iUnion, Finset.mem_Icc] at hu
    obtain ⟨m, ⟨hm1, hm4⟩, t, ht, rfl⟩ := hu
    exact isIcosahedralGoldenUnit_pow_mul_tetrahedral hm1 hm4 ht
  have hcardU : (⋃ m ∈ (Finset.Icc 1 4 : Finset ℕ),
      (icosahedralGenerator ^ m) • (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ]))).ncard =
        96 := by
    change (⋃ m ∈ ((Finset.Icc 1 4 : Finset ℕ) : Set ℕ),
      (icosahedralGenerator ^ m) •
        (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ]))).ncard = 96
    rw [(Finset.finite_toSet _).ncard_biUnion (fun m _ => hfinT.smul_set)
      pairwiseDisjoint_golden_cosets, finsum_mem_coe_finset]
    simp [Set.ncard_smul_set, hcardT]
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcardG, hcardU]) hfinG).symm

private theorem icosahedral_unit_set_eq_biUnion_five_cosets :
    {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralUnit} =
      ⋃ m ∈ Finset.range 5,
        (icosahedralGenerator ^ m) • (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ])) := by
  ext u
  change (u : ℍ[ℝ]).IsIcosahedralUnit ↔ _
  rw [Quaternion.isIcosahedralUnit_def, ← mem_binaryTetrahedralUnitSubgroup_iff,
    ← SetLike.mem_coe]
  have hmemG : (u : ℍ[ℝ]).IsIcosahedralGoldenUnit ↔
      u ∈ ⋃ m ∈ (Finset.Icc 1 4 : Finset ℕ),
        (icosahedralGenerator ^ m) • (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ])) := by
    rw [← golden_unit_set_eq_biUnion_cosets]
    rfl
  rw [hmemG]
  simp only [Set.mem_iUnion, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro (hu | ⟨m, ⟨hm1, hm4⟩, hcos⟩)
    · exact ⟨0, by decide, u, hu, by simp⟩
    · exact ⟨m, by omega, hcos⟩
  · rintro ⟨m, hm5, hcos⟩
    rcases eq_or_ne m 0 with rfl | hm0
    · obtain ⟨t, ht, rfl⟩ := hcos
      exact .inl (by simpa using ht)
    · exact .inr ⟨m, ⟨by omega, by omega⟩, hcos⟩

private theorem omega_mul_icosahedralGenerator_pows :
    (tetrahedralOmega * icosahedralGenerator =
        icosahedralGenerator ^ 4 * tetrahedralOmega⁻¹) ∧
    (tetrahedralOmega * icosahedralGenerator ^ 2 =
        icosahedralGenerator ^ 2 *
          ⟨⟨1 / 2, -(1 / 2), 1 / 2, 1 / 2⟩,
            (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr
              (by rw [Quaternion.normSq_def']; norm_num)⟩) ∧
    (tetrahedralOmega * icosahedralGenerator ^ 3 =
        icosahedralGenerator *
          ⟨⟨-(1 / 2), -(1 / 2), 1 / 2, 1 / 2⟩,
            (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr
              (by rw [Quaternion.normSq_def']; norm_num)⟩) ∧
    (tetrahedralOmega * icosahedralGenerator ^ 4 =
        icosahedralGenerator ^ 3 * quaternionUnitJ) := by
  -- On `unitary ℍ[ℝ]`, group inversion is definitionally quaternion `star`.
  have hωinv : ((tetrahedralOmega⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      ⟨1 / 2, -(1 / 2), -(1 / 2), -(1 / 2)⟩ := by
    change Star.star (tetrahedralOmega : ℍ[ℝ]) = _
    rw [coe_tetrahedralOmega]
    ext <;> simp
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [MulMemClass.coe_mul, MulMemClass.coe_mul, coe_tetrahedralOmega,
      coe_icosahedralGenerator, coe_icosahedralGenerator_pow_four, hωinv]
    ext <;> simp <;> grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]
  · rw [MulMemClass.coe_mul, MulMemClass.coe_mul, coe_tetrahedralOmega,
      coe_icosahedralGenerator_sq]
    ext <;> simp <;> grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]
  · rw [MulMemClass.coe_mul, MulMemClass.coe_mul, coe_tetrahedralOmega,
      coe_icosahedralGenerator_pow_three, coe_icosahedralGenerator]
    ext <;> simp <;> grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]
  · rw [MulMemClass.coe_mul, MulMemClass.coe_mul, coe_tetrahedralOmega,
      coe_icosahedralGenerator_pow_four, coe_icosahedralGenerator_pow_three, coe_quaternionUnitJ]
    ext <;> simp <;> grind [Real.goldenRatio_sq, inv_one_add_sqrt_five]

private theorem binaryTetrahedralUnitSubgroup_le_closure :
    binaryTetrahedralUnitSubgroup ≤
      Subgroup.closure {icosahedralGenerator, tetrahedralOmega} := by
  rw [binaryTetrahedralUnitSubgroup_eq_closure, Subgroup.closure_le]
  rintro u (rfl | rfl)
  · exact Subgroup.subset_closure (by simp)
  · have hζ : icosahedralGenerator ∈
        Subgroup.closure {icosahedralGenerator, tetrahedralOmega} :=
      Subgroup.subset_closure (by simp)
    have hω : tetrahedralOmega ∈ Subgroup.closure {icosahedralGenerator, tetrahedralOmega} :=
      Subgroup.subset_closure (by simp)
    have hj : quaternionUnitJ ∈ Subgroup.closure {icosahedralGenerator, tetrahedralOmega} :=
      icosahedralGenerator_sq_mul_tetrahedralOmega_mul_inv ▸
        mul_mem (mul_mem (pow_mem hζ 2) hω) (inv_mem hζ)
    have hτ : tetrahedralTau = tetrahedralOmega⁻¹ * quaternionUnitJ := by
      rw [← tetrahedralOmega_mul_tetrahedralTau, inv_mul_cancel_left]
    exact hτ ▸ mul_mem (inv_mem hω) hj

private theorem omega_mul_coset_mem_five_cosets {m : ℕ} (hm : m < 5) {t : unitary ℍ[ℝ]}
    (ht : t ∈ binaryTetrahedralUnitSubgroup) :
    ∃ k < 5, tetrahedralOmega * ((icosahedralGenerator ^ m) • t) ∈
      (icosahedralGenerator ^ k) • (binaryTetrahedralUnitSubgroup : Set (unitary ℍ[ℝ])) := by
  simp only [Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul]
  obtain ⟨h1, h2, h3, h4⟩ := omega_mul_icosahedralGenerator_pows
  interval_cases m
  · exact ⟨0, by decide, tetrahedralOmega * t,
      mul_mem tetrahedralOmega_mem_binaryTetrahedralUnitSubgroup ht, by simp⟩
  · exact ⟨4, by decide, tetrahedralOmega⁻¹ * t,
      mul_mem (inv_mem tetrahedralOmega_mem_binaryTetrahedralUnitSubgroup) ht,
      by simpa [pow_one, mul_assoc] using (congrArg (· * t) h1).symm⟩
  · refine ⟨2, by decide,
      ⟨⟨1 / 2, -(1 / 2), 1 / 2, 1 / 2⟩,
        (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr
          (by rw [Quaternion.normSq_def']; norm_num)⟩ * t,
      mul_mem (mem_binaryTetrahedralUnitSubgroup_iff.mpr ((Quaternion.isTetrahedralUnit_def _).mpr
        (.inr (Quaternion.isHalfUnit_iff_coordinates.mpr (by simp))))) ht, ?_⟩
    rw [← mul_assoc, ← h2, mul_assoc]
  · refine ⟨1, by decide,
      ⟨⟨-(1 / 2), -(1 / 2), 1 / 2, 1 / 2⟩,
        (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr
          (by rw [Quaternion.normSq_def']; norm_num)⟩ * t,
      mul_mem (mem_binaryTetrahedralUnitSubgroup_iff.mpr ((Quaternion.isTetrahedralUnit_def _).mpr
        (.inr (Quaternion.isHalfUnit_iff_coordinates.mpr (by simp))))) ht, ?_⟩
    rw [pow_one, ← mul_assoc, ← h3, mul_assoc]
  · exact ⟨3, by decide, quaternionUnitJ * t,
      mul_mem quaternionUnitJ_mem_binaryTetrahedralUnitSubgroup ht,
      by simpa [mul_assoc] using (congrArg (· * t) h4).symm⟩

private theorem coe_closure_icosahedralGenerator_tetrahedralOmega :
    (Subgroup.closure ({icosahedralGenerator, tetrahedralOmega} : Set (unitary ℍ[ℝ])) :
      Set (unitary ℍ[ℝ])) = {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralUnit} := by
  have hfin : {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralUnit}.Finite :=
    Quaternion.finite_isIcosahedralUnit.preimage Subtype.val_injective.injOn
  refine Subgroup.coe_closure_eq_of_forall_mul_mem hfin Quaternion.IsIcosahedralUnit.one
    (fun u hu => ?_) (fun s hs u hu => ?_)
  · change u ∈ {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralUnit} at hu
    rw [icosahedral_unit_set_eq_biUnion_five_cosets] at hu
    simp only [Set.mem_iUnion, Finset.mem_range] at hu
    obtain ⟨m, -, t, ht, rfl⟩ := hu
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) m)
      (binaryTetrahedralUnitSubgroup_le_closure ht)
  · change u ∈ {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralUnit} at hu
    change s * u ∈ {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralUnit}
    rw [icosahedral_unit_set_eq_biUnion_five_cosets] at hu ⊢
    simp only [Set.mem_iUnion, Finset.mem_range] at hu ⊢
    obtain ⟨m, hm, t, ht, rfl⟩ := hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · simp only [Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul]
      rcases eq_or_ne m 4 with rfl | hm4
      · have hneg : -t ∈ binaryTetrahedralUnitSubgroup :=
          neg_one_mul t ▸ mul_mem neg_one_mem_binaryTetrahedralUnitSubgroup ht
        refine ⟨0, by decide, -t, hneg, ?_⟩
        rw [pow_zero, one_mul, ← mul_assoc, ← pow_succ', icosahedralGenerator_pow_five,
          neg_one_mul]
      · exact ⟨m + 1, by omega, t, ht, by rw [pow_succ', mul_assoc]⟩
    · obtain ⟨k, hk, hmem⟩ := omega_mul_coset_mem_five_cosets hm ht
      exact ⟨k, hk, hmem⟩

/-- **The `120` vertices of the unit `600`-cell are closed under quaternion multiplication.** -/
theorem _root_.Quaternion.IsIcosahedralUnit.mul {p q : ℍ[ℝ]}
    (hp : p.IsIcosahedralUnit) (hq : q.IsIcosahedralUnit) : (p * q).IsIcosahedralUnit := by
  let up : unitary ℍ[ℝ] := ⟨p, hp.mem_unitary⟩
  let uq : unitary ℍ[ℝ] := ⟨q, hq.mem_unitary⟩
  have hup : up ∈ Subgroup.closure {icosahedralGenerator, tetrahedralOmega} := by
    rw [← SetLike.mem_coe, coe_closure_icosahedralGenerator_tetrahedralOmega]
    exact hp
  have huq : uq ∈ Subgroup.closure {icosahedralGenerator, tetrahedralOmega} := by
    rw [← SetLike.mem_coe, coe_closure_icosahedralGenerator_tetrahedralOmega]
    exact hq
  have hmul : up * uq ∈ (Subgroup.closure {icosahedralGenerator, tetrahedralOmega} :
      Set (unitary ℍ[ℝ])) := mul_mem hup huq
  rwa [coe_closure_icosahedralGenerator_tetrahedralOmega] at hmul

/-- **The `120` vertices of the unit `600`-cell are closed under inversion.** -/
theorem _root_.Quaternion.IsIcosahedralUnit.inv {q : ℍ[ℝ]} (hq : q.IsIcosahedralUnit) :
    q⁻¹.IsIcosahedralUnit := by
  have hunit : q * Star.star q = 1 := (Unitary.mem_iff.mp hq.mem_unitary).2
  rw [inv_eq_of_mul_eq_one_right hunit]
  exact hq.star

/-- **The binary icosahedral subgroup of `unitary ℍ[ℝ]`**, whose `120` elements are the vertices of
the unit `600`-cell (`24` Hurwitz units together with `96` even-permutation golden units). -/
noncomputable def binaryIcosahedralUnitSubgroup : Subgroup (unitary ℍ[ℝ]) where
  carrier := {u : unitary ℍ[ℝ] | (u : ℍ[ℝ]).IsIcosahedralUnit}
  one_mem' := Quaternion.IsIcosahedralUnit.one
  mul_mem' hp hq := hp.mul hq
  inv_mem' hq := hq.star

theorem mem_binaryIcosahedralUnitSubgroup_iff {u : unitary ℍ[ℝ]} :
    u ∈ binaryIcosahedralUnitSubgroup ↔ (u : ℍ[ℝ]).IsIcosahedralUnit := Iff.rfl

@[simp]
theorem icosahedralGenerator_mem_binaryIcosahedralUnitSubgroup :
    icosahedralGenerator ∈ binaryIcosahedralUnitSubgroup :=
  (Quaternion.isIcosahedralUnit_def _).mpr
    (.inr (by simpa using isIcosahedralGoldenUnit_pow 1 (by decide) (by decide)))

@[simp]
theorem tetrahedralOmega_mem_binaryIcosahedralUnitSubgroup :
    tetrahedralOmega ∈ binaryIcosahedralUnitSubgroup :=
  (Quaternion.isIcosahedralUnit_def _).mpr
    (.inl (mem_binaryTetrahedralUnitSubgroup_iff.mp
      tetrahedralOmega_mem_binaryTetrahedralUnitSubgroup))

/-- **The binary tetrahedral subgroup is contained in the binary icosahedral subgroup.** -/
theorem binaryTetrahedralUnitSubgroup_le_binaryIcosahedralUnitSubgroup :
    binaryTetrahedralUnitSubgroup ≤ binaryIcosahedralUnitSubgroup := fun _ hu =>
  (Quaternion.isIcosahedralUnit_def _).mpr (.inl (mem_binaryTetrahedralUnitSubgroup_iff.mp hu))

/-- **The binary icosahedral subgroup is generated by the `<2, 3, 5>` pair `{ζ, ω}`.** -/
theorem binaryIcosahedralUnitSubgroup_eq_closure :
    binaryIcosahedralUnitSubgroup = Subgroup.closure {icosahedralGenerator, tetrahedralOmega} :=
  SetLike.ext' coe_closure_icosahedralGenerator_tetrahedralOmega.symm

instance : Finite binaryIcosahedralUnitSubgroup :=
  (Quaternion.finite_isIcosahedralUnit.preimage Subtype.val_injective.injOn).to_subtype

/-- **The binary icosahedral subgroup has exact order `120`.** -/
@[simp]
theorem natCard_binaryIcosahedralUnitSubgroup :
    Nat.card binaryIcosahedralUnitSubgroup = 120 := by
  have himg : Subtype.val '' (binaryIcosahedralUnitSubgroup : Set (unitary ℍ[ℝ])) =
      {q : ℍ[ℝ] | q.IsIcosahedralUnit} := by
    ext q
    refine ⟨?_, fun hq => ⟨⟨q, hq.mem_unitary⟩, hq, rfl⟩⟩
    rintro ⟨u, hu, rfl⟩
    exact hu
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq,
    ← Set.ncard_image_of_injective _ Subtype.val_injective, himg,
    Quaternion.ncard_isIcosahedralUnit]

/-- The binary tetrahedral subgroup has relative index `5` inside the binary icosahedral
subgroup. -/
@[simp]
theorem relIndex_binaryTetrahedralUnitSubgroup_binaryIcosahedralUnitSubgroup :
    binaryTetrahedralUnitSubgroup.relIndex binaryIcosahedralUnitSubgroup = 5 := by
  have hmul := binaryTetrahedralUnitSubgroup.relIndex_mul_card binaryIcosahedralUnitSubgroup
  rw [inf_of_le_left binaryTetrahedralUnitSubgroup_le_binaryIcosahedralUnitSubgroup,
    natCard_binaryTetrahedralUnitSubgroup, natCard_binaryIcosahedralUnitSubgroup] at hmul
  omega

end TauCeti

end
