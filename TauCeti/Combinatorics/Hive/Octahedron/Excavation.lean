/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Octahedron.Recurrence
import Mathlib.Tactic.NormNum

/-!
# Legal unit-cell excavation schedules and agreement with global time recursion

A space-time section `S : SpaceTimeSection n` is locally excavatable upward at `(x, y)`
(`SpaceTimeSection.IsExcavatableAt`) when `0 < x, y < n` and all four horizontal neighbours
`(x ± 1, y)`, `(x, y ± 1)` have height `S x y + 1`. Excavating `(x, y)`
(`SpaceTimeSection.excavate`) raises `S x y` to `S x y + 2` while preserving parity and unit slope
on all grid edges, and `SpaceTimeSection.excavateState` updates the state at `(x, y)` by the
interior rule `e' = max(a + c, b + d) - e`.

`sectionTransition_excavate` proves that a single unit-cell excavation agrees with the global
time-recursive transition `sectionTransition`, and `evalExcavationSchedule_eq_sectionTransition`
extends this to any legal multi-step schedule (`IsExcavationSchedule`). Finally,
`exists_excavationSchedule_of_le` and `exists_associatorExcavationSchedule` prove by minimum-height
potential descent that any wall-agreeing sections `S₁ ≤ S₂` (in particular `lowerSection n` and
`upperSection n` for all `n : ℕ`) admit a terminating legal excavation schedule of length
`sectionPotential S₁ S₂`.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

section ExcavationSchedule

variable {n : ℕ}

/-- A section `S` is locally excavatable upward at `(x, y)` if `0 < x, y < n` and all four
horizontal grid neighbours have height `S x y + 1`. -/
def SpaceTimeSection.IsExcavatableAt (S : SpaceTimeSection n) (x y : Fin (n + 1)) : Prop :=
  if hx : 0 < x.val ∧ x.val < n then
    if hy : 0 < y.val ∧ y.val < n then
      S ⟨x.val + 1, by omega⟩ y = S x y + 1 ∧
      S ⟨x.val - 1, by omega⟩ y = S x y + 1 ∧
      S x ⟨y.val + 1, by omega⟩ = S x y + 1 ∧
      S x ⟨y.val - 1, by omega⟩ = S x y + 1
    else False
  else False

theorem SpaceTimeSection.isExcavatableAt_def (S : SpaceTimeSection n) (x y : Fin (n + 1)) :
    S.IsExcavatableAt x y ↔
      if hx : 0 < x.val ∧ x.val < n then
        if hy : 0 < y.val ∧ y.val < n then
          S ⟨x.val + 1, by omega⟩ y = S x y + 1 ∧
          S ⟨x.val - 1, by omega⟩ y = S x y + 1 ∧
          S x ⟨y.val + 1, by omega⟩ = S x y + 1 ∧
          S x ⟨y.val - 1, by omega⟩ = S x y + 1
        else False
      else False :=
  Iff.rfl

instance (S : SpaceTimeSection n) (x y : Fin (n + 1)) : Decidable (S.IsExcavatableAt x y) :=
  decidable_of_iff _ (S.isExcavatableAt_def x y).symm

namespace SpaceTimeSection.IsExcavatableAt

variable {S : SpaceTimeSection n} {x y : Fin (n + 1)}

theorem hx (h : S.IsExcavatableAt x y) : 0 < x.val ∧ x.val < n := by
  unfold IsExcavatableAt at h; split_ifs at h with hx; exact hx

theorem hy (h : S.IsExcavatableAt x y) : 0 < y.val ∧ y.val < n := by
  unfold IsExcavatableAt at h; split_ifs at h with hx hy; exact hy

theorem two_le (h : S.IsExcavatableAt x y) : 2 ≤ n := by have := h.hx; omega
theorem one_le (h : S.IsExcavatableAt x y) : 1 ≤ n := by have := h.hx; omega

theorem add_x (h : S.IsExcavatableAt x y) :
    S ⟨x.val + 1, by have := h.hx; omega⟩ y = S x y + 1 := by
  have hx := h.hx; have hy := h.hy
  simp only [IsExcavatableAt, hx, hy] at h; exact h.1

theorem sub_x (h : S.IsExcavatableAt x y) :
    S ⟨x.val - 1, by have := h.hx; omega⟩ y = S x y + 1 := by
  have hx := h.hx; have hy := h.hy
  simp only [IsExcavatableAt, hx, hy] at h; exact h.2.1

theorem add_y (h : S.IsExcavatableAt x y) :
    S x ⟨y.val + 1, by have := h.hy; omega⟩ = S x y + 1 := by
  have hx := h.hx; have hy := h.hy
  simp only [IsExcavatableAt, hx, hy] at h; exact h.2.2.1

theorem sub_y (h : S.IsExcavatableAt x y) :
    S x ⟨y.val - 1, by have := h.hy; omega⟩ = S x y + 1 := by
  have hx := h.hx; have hy := h.hy
  simp only [IsExcavatableAt, hx, hy] at h; exact h.2.2.2

theorem mk' (hx : 0 < x.val ∧ x.val < n) (hy : 0 < y.val ∧ y.val < n)
    (hax : S ⟨x.val + 1, by omega⟩ y = S x y + 1)
    (hsx : S ⟨x.val - 1, by omega⟩ y = S x y + 1)
    (hay : S x ⟨y.val + 1, by omega⟩ = S x y + 1)
    (hsy : S x ⟨y.val - 1, by omega⟩ = S x y + 1) :
    S.IsExcavatableAt x y := by
  simp [IsExcavatableAt, hx, hy, hax, hsx, hay, hsy]

theorem add_x_ne (h : S.IsExcavatableAt x y) :
    (⟨x.val + 1, by have := h.hx; omega⟩ : Fin (n + 1)) ≠ x := by
  intro hc; have := congrArg Fin.val hc; dsimp at this; omega

theorem sub_x_ne (h : S.IsExcavatableAt x y) :
    (⟨x.val - 1, by have := h.hx; omega⟩ : Fin (n + 1)) ≠ x := by
  intro hc; have := h.hx; have := congrArg Fin.val hc; dsimp at this; omega

theorem add_y_ne (h : S.IsExcavatableAt x y) :
    (⟨y.val + 1, by have := h.hy; omega⟩ : Fin (n + 1)) ≠ y := by
  intro hc; have := congrArg Fin.val hc; dsimp at this; omega

theorem sub_y_ne (h : S.IsExcavatableAt x y) :
    (⟨y.val - 1, by have := h.hy; omega⟩ : Fin (n + 1)) ≠ y := by
  intro hc; have := h.hy; have := congrArg Fin.val hc; dsimp at this; omega

end SpaceTimeSection.IsExcavatableAt

private theorem excavate_abs_sub_x {S : SpaceTimeSection n} {x y : Fin (n + 1)}
    (h : S.IsExcavatableAt x y) (i : Fin n) (y' : Fin (n + 1)) :
    |(if i.succ = x ∧ y' = y then S x y + 2 else S i.succ y') -
      (if i.castSucc = x ∧ y' = y then S x y + 2 else S i.castSucc y')| = 1 := by
  have hxh := h.hx
  by_cases h₁ : i.succ = x ∧ y' = y
  · rcases h₁ with ⟨hi, hy'⟩
    have hic : i.castSucc = ⟨x.val - 1, by omega⟩ := by
      ext; have := congrArg Fin.val hi; simp at this ⊢; omega
    simp only [hi, hy', and_self, ↓reduceIte, hic, h.sub_x_ne, false_and, h.sub_x]
    norm_num
  · by_cases h₂ : i.castSucc = x ∧ y' = y
    · rcases h₂ with ⟨hi, hy'⟩
      have his : i.succ = ⟨x.val + 1, by omega⟩ := by
        ext; have := congrArg Fin.val hi; simp at this ⊢; omega
      simp only [his, h.add_x_ne, false_and, ↓reduceIte, hi, hy', and_self, h.add_x]
      norm_num
    · simp only [h₁, h₂, ↓reduceIte]
      exact S.abs_sub_x i y'

private theorem excavate_abs_sub_y {S : SpaceTimeSection n} {x y : Fin (n + 1)}
    (h : S.IsExcavatableAt x y) (x' : Fin (n + 1)) (j : Fin n) :
    |(if x' = x ∧ j.succ = y then S x y + 2 else S x' j.succ) -
      (if x' = x ∧ j.castSucc = y then S x y + 2 else S x' j.castSucc)| = 1 := by
  have hyh := h.hy
  by_cases h₁ : x' = x ∧ j.succ = y
  · rcases h₁ with ⟨hx', hj⟩
    have hjc : j.castSucc = ⟨y.val - 1, by omega⟩ := by
      ext; have := congrArg Fin.val hj; simp at this ⊢; omega
    simp only [hx', hj, and_self, ↓reduceIte, hjc, h.sub_y_ne, and_false, h.sub_y]
    norm_num
  · by_cases h₂ : x' = x ∧ j.castSucc = y
    · rcases h₂ with ⟨hx', hj⟩
      have hjs : j.succ = ⟨y.val + 1, by omega⟩ := by
        ext; have := congrArg Fin.val hj; simp at this ⊢; omega
      simp only [hjs, h.add_y_ne, and_false, ↓reduceIte, hx', hj, and_self, h.add_y]
      norm_num
    · simp only [h₁, h₂, ↓reduceIte]
      exact S.abs_sub_y x' j

/-- Excavate one unit octahedron above `(x, y)` on `S`, raising `S x y` to `S x y + 2`. -/
def SpaceTimeSection.excavate (S : SpaceTimeSection n) (x y : Fin (n + 1))
    (h : S.IsExcavatableAt x y) : SpaceTimeSection n where
  height x' y' := if x' = x ∧ y' = y then S x y + 2 else S x' y'
  even_sum x' y' := by
    by_cases heq : x' = x ∧ y' = y
    · rw [heq.1, heq.2]
      simp only [and_self, ↓reduceIte]
      obtain ⟨k, hk⟩ := S.even_sum x y
      exact ⟨k + 1, by omega⟩
    · simp only [heq, ↓reduceIte]; exact S.even_sum x' y'
  abs_sub_x := excavate_abs_sub_x h
  abs_sub_y := excavate_abs_sub_y h

@[simp] theorem SpaceTimeSection.excavate_apply (S : SpaceTimeSection n) (x y : Fin (n + 1))
    (h : S.IsExcavatableAt x y) (x' y' : Fin (n + 1)) :
    S.excavate x y h x' y' = if x' = x ∧ y' = y then S x y + 2 else S x' y' := (rfl)

/-- Local interior state update `e' = max(a + c, b + d) - e` at an excavatable vertex `(x, y)`. -/
def SpaceTimeSection.excavateState {R : Type*} [AddCommGroup R] [LinearOrder R]
    {S : SpaceTimeSection n} {x y : Fin (n + 1)} (h : S.IsExcavatableAt x y)
    (val : SectionState n R) : SectionState n R :=
  fun x' y' =>
    if x' = x ∧ y' = y then
      max (val ⟨x.val + 1, by have := h.hx; omega⟩ y + val ⟨x.val - 1, by have := h.hx; omega⟩ y)
        (val x ⟨y.val + 1, by have := h.hy; omega⟩ + val x ⟨y.val - 1, by have := h.hy; omega⟩) -
        val x y
    else
      val x' y'

@[simp] theorem SpaceTimeSection.excavateState_apply {R : Type*} [AddCommGroup R] [LinearOrder R]
    {S : SpaceTimeSection n} {x y : Fin (n + 1)} (h : S.IsExcavatableAt x y)
    (val : SectionState n R) (x' y' : Fin (n + 1)) :
    S.excavateState h val x' y' =
      if x' = x ∧ y' = y then
        max (val ⟨x.val + 1, by have := h.hx; omega⟩ y + val ⟨x.val - 1, by have := h.hx; omega⟩ y)
          (val x ⟨y.val + 1, by have := h.hy; omega⟩ + val x ⟨y.val - 1, by have := h.hy; omega⟩) -
          val x y
      else val x' y' := (rfl)

/-- Local interior excavation state update `excavateState h` is an involution on `SectionState n R`
(including when the two `max` branches tie), since the four horizontal neighbours of `(x, y)` are
unchanged by the first update. -/
@[simp] theorem SpaceTimeSection.excavateState_involutive {R : Type*} [AddCommGroup R]
    [LinearOrder R] {S : SpaceTimeSection n} {x y : Fin (n + 1)} (h : S.IsExcavatableAt x y)
    (val : SectionState n R) :
    S.excavateState h (S.excavateState h val) = val := by
  ext x' y'
  by_cases heq : x' = x ∧ y' = y
  · rcases heq with ⟨rfl, rfl⟩
    simp [h.add_x_ne, h.sub_x_ne, h.add_y_ne, h.sub_y_ne]
  · simp [heq]

/-- One unit-cell excavation step agrees with `sectionTransition`. -/
theorem sectionTransition_excavate {R : Type*} [AddCommGroup R] [LinearOrder R] (hn : 1 ≤ n)
    (S : SpaceTimeSection n) {x y : Fin (n + 1)} (h : S.IsExcavatableAt x y)
    (val : SectionState n R) :
    sectionTransition hn S (S.excavate x y h) val = S.excavateState h val := by
  ext x' y'
  rw [sectionTransition_apply]
  by_cases heq : x' = x ∧ y' = y
  · rw [heq.1, heq.2]
    set p := (S.excavate x y h).point x y
    have hgt : S p.finX p.finY < p.t := by simp [p]
    rw [extendSection_of_gt hn S val hgt]
    have hx := h.hx; have hy := h.hy
    have hpair_f : horizPair hn false x y =
        ((⟨x.val + 1, by omega⟩, y), (⟨x.val - 1, by omega⟩, y)) :=
      horizPair_false_interior hn y hx
    have hpair_t : horizPair hn true x y =
        ((x, ⟨y.val + 1, by omega⟩), (x, ⟨y.val - 1, by omega⟩)) :=
      horizPair_true_interior hn x hy
    have hv : extendSection hn S val (pastVert p) = val x y := by
      rw [extendSection_of_eq hn S val (by simp [p])]; simp [p]
    have hf1 : extendSection hn S val (pastHoriz₁ hn false p) = val ⟨x.val + 1, by omega⟩ y := by
      rw [extendSection_of_eq hn S val (by simp [p, hpair_f, h.add_x]; omega)]
      simp [p, hpair_f]
    have hf2 : extendSection hn S val (pastHoriz₂ hn false p) = val ⟨x.val - 1, by omega⟩ y := by
      rw [extendSection_of_eq hn S val (by simp [p, hpair_f, h.sub_x]; omega)]
      simp [p, hpair_f]
    have ht1 : extendSection hn S val (pastHoriz₁ hn true p) = val x ⟨y.val + 1, by omega⟩ := by
      rw [extendSection_of_eq hn S val (by simp [p, hpair_t, h.add_y]; omega)]
      simp [p, hpair_t]
    have ht2 : extendSection hn S val (pastHoriz₂ hn true p) = val x ⟨y.val - 1, by omega⟩ := by
      rw [extendSection_of_eq hn S val (by simp [p, hpair_t, h.sub_y]; omega)]
      simp [p, hpair_t]
    simp [hv, hf1, hf2, ht1, ht2]
  · have h_on : ((S.excavate x y h).point x' y').t =
        S ((S.excavate x y h).point x' y').finX ((S.excavate x y h).point x' y').finY := by
      simp [heq]
    rw [extendSection_of_eq hn S val h_on]
    simp [heq]

/-- Predicate characterizing legal sequences of upward unit-cell excavations from `S₁` to `S₂`. -/
def IsExcavationSchedule : SpaceTimeSection n → SpaceTimeSection n →
    List (Fin (n + 1) × Fin (n + 1)) → Prop
  | S₁, S₂, [] => S₁ = S₂
  | S₁, S₂, p :: ps =>
      ∃ h : S₁.IsExcavatableAt p.1 p.2,
        IsExcavationSchedule (S₁.excavate p.1 p.2 h) S₂ ps

@[simp] theorem isExcavationSchedule_nil (S₁ S₂ : SpaceTimeSection n) :
    IsExcavationSchedule S₁ S₂ [] ↔ S₁ = S₂ := Iff.rfl

@[simp] theorem isExcavationSchedule_cons (S₁ S₂ : SpaceTimeSection n)
    (p : Fin (n + 1) × Fin (n + 1)) (ps : List (Fin (n + 1) × Fin (n + 1))) :
    IsExcavationSchedule S₁ S₂ (p :: ps) ↔
      ∃ h : S₁.IsExcavatableAt p.1 p.2,
        IsExcavationSchedule (S₁.excavate p.1 p.2 h) S₂ ps := Iff.rfl

namespace IsExcavationSchedule

theorem head {S₁ S₂ : SpaceTimeSection n} {p : Fin (n + 1) × Fin (n + 1)}
    {ps : List (Fin (n + 1) × Fin (n + 1))} (h : IsExcavationSchedule S₁ S₂ (p :: ps)) :
    S₁.IsExcavatableAt p.1 p.2 := by
  rcases h with ⟨hp, _⟩; exact hp

theorem tail {S₁ S₂ : SpaceTimeSection n} {p : Fin (n + 1) × Fin (n + 1)}
    {ps : List (Fin (n + 1) × Fin (n + 1))} (h : IsExcavationSchedule S₁ S₂ (p :: ps)) :
    IsExcavationSchedule (S₁.excavate p.1 p.2 h.head) S₂ ps := by
  rcases h with ⟨_, hps⟩; exact hps

end IsExcavationSchedule

/-- Evaluate a legal unit-cell excavation schedule step-by-step via local interior updates. -/
def evalExcavationSchedule {R : Type*} [AddCommGroup R] [LinearOrder R] :
    ∀ {S₁ S₂ : SpaceTimeSection n} (steps : List (Fin (n + 1) × Fin (n + 1))),
      IsExcavationSchedule S₁ S₂ steps → SectionState n R → SectionState n R
  | _, _, [], _ => id
  | S₁, _, _ :: ps, h => fun val =>
      evalExcavationSchedule ps h.tail (S₁.excavateState h.head val)

@[simp] theorem evalExcavationSchedule_nil {R : Type*} [AddCommGroup R] [LinearOrder R]
    {S₁ S₂ : SpaceTimeSection n} (h : IsExcavationSchedule S₁ S₂ []) (val : SectionState n R) :
    evalExcavationSchedule [] h val = val := (rfl)

@[simp] theorem evalExcavationSchedule_cons {R : Type*} [AddCommGroup R] [LinearOrder R]
    {S₁ S₂ : SpaceTimeSection n} (p : Fin (n + 1) × Fin (n + 1))
    (ps : List (Fin (n + 1) × Fin (n + 1))) (h : IsExcavationSchedule S₁ S₂ (p :: ps))
    (val : SectionState n R) :
    evalExcavationSchedule (p :: ps) h val =
      evalExcavationSchedule ps h.tail (S₁.excavateState h.head val) := (rfl)

/-- Every legal unit-cell excavation schedule from `S₁` to `S₂` evaluates to
`sectionTransition hn S₁ S₂` (`1 ≤ n`). -/
theorem evalExcavationSchedule_eq_sectionTransition {R : Type*} [AddCommGroup R] [LinearOrder R]
    (hn : 1 ≤ n) :
    ∀ {S₁ S₂ : SpaceTimeSection n} (steps : List (Fin (n + 1) × Fin (n + 1)))
      (h : IsExcavationSchedule S₁ S₂ steps) (val : SectionState n R),
      evalExcavationSchedule steps h val = sectionTransition hn S₁ S₂ val
  | _, _, [], h, val => by subst h; simp [evalExcavationSchedule]
  | S₁, S₂, _ :: ps, h, val => by
      simp only [evalExcavationSchedule]
      rw [evalExcavationSchedule_eq_sectionTransition hn ps h.tail,
        ← sectionTransition_excavate hn S₁ h.head val, ← Equiv.trans_apply,
        sectionTransition_trans]

/-- Because any two spacetime sections have the same parity at `(x, y)`, strict inequality
`S₁ x y < S₂ x y` implies `S₁ x y + 2 ≤ S₂ x y`. -/
theorem SpaceTimeSection.add_two_le_of_lt (S₁ S₂ : SpaceTimeSection n) {x y : Fin (n + 1)}
    (hlt : S₁ x y < S₂ x y) :
    S₁ x y + 2 ≤ S₂ x y := by
  have hp : S₁ (S₂.point x y).finX (S₂.point x y).finY < (S₂.point x y).t := by
    simpa only [SpaceTimeSection.point_finX, SpaceTimeSection.point_finY,
      SpaceTimeSection.point_t] using hlt
  simpa only [SpaceTimeSection.point_finX, SpaceTimeSection.point_finY,
    SpaceTimeSection.point_t] using S₁.add_two_le_t_of_lt hp

/-- Every legal excavation schedule from `S₁` to `S₂` raises the total height sum by `2` per step.
-/
theorem IsExcavationSchedule.sum_height_eq :
    ∀ {S₁ S₂ : SpaceTimeSection n} {steps : List (Fin (n + 1) × Fin (n + 1))},
      IsExcavationSchedule S₁ S₂ steps →
      (∑ x : Fin (n + 1), ∑ y : Fin (n + 1), S₂ x y) =
        (∑ x : Fin (n + 1), ∑ y : Fin (n + 1), S₁ x y) + 2 * (steps.length : ℤ)
  | _, _, [], h => by
      have heq : _ = _ := h
      subst heq; simp
  | S₁, S₂, (x, y) :: ps, h => by
      rw [h.tail.sum_height_eq]
      have hstep : (∑ x' : Fin (n + 1), ∑ y' : Fin (n + 1), S₁.excavate x y h.head x' y') =
          (∑ x' : Fin (n + 1), ∑ y' : Fin (n + 1), S₁ x' y') + 2 := by
        have hterm (x' y' : Fin (n + 1)) : S₁.excavate x y h.head x' y' =
            S₁ x' y' + if x' = x ∧ y' = y then 2 else 0 := by
          simp only [SpaceTimeSection.excavate_apply]
          split_ifs with heq
          · rcases heq with ⟨rfl, rfl⟩; omega
          · omega
        simp only [hterm, Finset.sum_add_distrib, ite_and]
        simp
      rw [hstep, List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

/-- Remaining unit-octahedron count between two spacetime sections `S₁` and `S₂`. -/
def sectionPotential (S₁ S₂ : SpaceTimeSection n) : ℕ :=
  ∑ x : Fin (n + 1), ∑ y : Fin (n + 1), ((S₂ x y - S₁ x y) / 2).toNat

/-- Excavating a vertex `(x, y)` with `S₁ x y < S₂ x y` decreases `sectionPotential S₁ S₂` by `1`.
-/
theorem sectionPotential_excavate {S₁ S₂ : SpaceTimeSection n} {x y : Fin (n + 1)}
    (hex : S₁.IsExcavatableAt x y) (hlt : S₁ x y < S₂ x y) :
    sectionPotential (S₁.excavate x y hex) S₂ + 1 = sectionPotential S₁ S₂ := by
  have h2 := S₁.add_two_le_of_lt S₂ hlt
  have hterm (x' y' : Fin (n + 1)) :
      ((S₂ x' y' - S₁ x' y') / 2).toNat =
        ((S₂ x' y' - S₁.excavate x y hex x' y') / 2).toNat +
          if x' = x ∧ y' = y then 1 else 0 := by
    simp only [SpaceTimeSection.excavate_apply]
    split_ifs with heq
    · rcases heq with ⟨rfl, rfl⟩; omega
    · omega
  calc sectionPotential (S₁.excavate x y hex) S₂ + 1
      = (∑ x', ∑ y', ((S₂ x' y' - S₁.excavate x y hex x' y') / 2).toNat) +
          ∑ x' : Fin (n + 1), ∑ y' : Fin (n + 1), if x' = x ∧ y' = y then 1 else 0 := by
        simp [sectionPotential, ite_and]
    _ = ∑ x', ∑ y', (((S₂ x' y' - S₁.excavate x y hex x' y') / 2).toNat +
          if x' = x ∧ y' = y then 1 else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = sectionPotential S₁ S₂ := by
        simp only [sectionPotential, ← hterm]

private theorem exists_min_excavatable {S₁ S₂ : SpaceTimeSection n}
    (hwall : ∀ x y : Fin (n + 1),
      (x.val = 0 ∨ x.val = n ∨ y.val = 0 ∨ y.val = n) → S₁ x y = S₂ x y)
    (hhi : ∀ x y, S₁ x y ≤ S₂ x y) (hne : S₁ ≠ S₂) :
    ∃ (x y : Fin (n + 1)) (h : S₁.IsExcavatableAt x y),
      (∀ x' y' : Fin (n + 1),
        (x'.val = 0 ∨ x'.val = n ∨ y'.val = 0 ∨ y'.val = n) →
          S₁.excavate x y h x' y' = S₂ x' y') ∧
      (∀ x' y', S₁.excavate x y h x' y' ≤ S₂ x' y') ∧
      sectionPotential (S₁.excavate x y h) S₂ + 1 = sectionPotential S₁ S₂ := by
  let U : Finset (Fin (n + 1) × Fin (n + 1)) :=
    Finset.univ.filter fun p => S₁ p.1 p.2 < S₂ p.1 p.2
  have hU : U.Nonempty := by
    by_contra h_empty; apply hne; ext x y
    have hnot : (x, y) ∉ U := fun hm => h_empty ⟨(x, y), hm⟩
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
    exact le_antisymm (hhi x y) hnot
  obtain ⟨⟨x, y⟩, hmem, hmin⟩ := U.exists_min_image (fun p => S₁ p.1 p.2) hU
  dsimp only at hmin
  have hlt : S₁ x y < S₂ x y := (Finset.mem_filter.mp hmem).2
  have hnw : ¬ (x.val = 0 ∨ x.val = n ∨ y.val = 0 ∨ y.val = n) :=
    fun hw => hlt.ne (hwall x y hw)
  have hx : 0 < x.val ∧ x.val < n := by have := x.isLt; omega
  have hy : 0 < y.val ∧ y.val < n := by have := y.isLt; omega
  have h2 := S₁.add_two_le_of_lt S₂ hlt
  have hnbr (q : Fin (n + 1) × Fin (n + 1)) (hm : |(q.1 : ℤ) - x| + |(q.2 : ℤ) - y| = 1) :
      S₁ q.1 q.2 = S₁ x y + 1 := by
    have hS1 := S₁.abs_sub_of_manhattan_eq_one hm
    have hS2 := abs_le.mp (S₂.abs_sub_of_manhattan_eq_one hm).le
    rcases eq_or_eq_neg_of_abs_eq hS1 with hplus | hminus
    · omega
    · have hminq := hmin q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      omega
  have hex : S₁.IsExcavatableAt x y := SpaceTimeSection.IsExcavatableAt.mk' hx hy
    (hnbr (⟨x.val + 1, by omega⟩, y) (by simp))
    (hnbr (⟨x.val - 1, by omega⟩, y) (by
      simp only [sub_self, abs_zero, add_zero]; rw [abs_of_nonpos (by omega)]; omega))
    (hnbr (x, ⟨y.val + 1, by omega⟩) (by simp))
    (hnbr (x, ⟨y.val - 1, by omega⟩) (by
      simp only [sub_self, abs_zero, zero_add]; rw [abs_of_nonpos (by omega)]; omega))
  refine ⟨x, y, hex, ?_, ?_, sectionPotential_excavate hex hlt⟩
  · intro x' y' hw; simp only [SpaceTimeSection.excavate_apply]
    split_ifs with heq
    · rcases heq with ⟨rfl, rfl⟩; exact absurd hw hnw
    · exact hwall x' y' hw
  · intro x' y'; simp only [SpaceTimeSection.excavate_apply]
    split_ifs with heq
    · rcases heq with ⟨rfl, rfl⟩; exact h2
    · exact hhi x' y'

private theorem exists_schedule_of_potential :
    ∀ (k : ℕ) (S₁ S₂ : SpaceTimeSection n),
      sectionPotential S₁ S₂ = k →
      (∀ x y : Fin (n + 1),
        (x.val = 0 ∨ x.val = n ∨ y.val = 0 ∨ y.val = n) → S₁ x y = S₂ x y) →
      (∀ x y, S₁ x y ≤ S₂ x y) →
      ∃ steps : List (Fin (n + 1) × Fin (n + 1)),
        IsExcavationSchedule S₁ S₂ steps ∧ steps.length = k
  | 0, S₁, S₂, hk, _, hhi => by
      have heq : S₁ = S₂ := by
        ext x y; by_contra hne
        have h2 := S₁.add_two_le_of_lt S₂ (lt_of_le_of_ne (hhi x y) hne)
        have hpos : 0 < sectionPotential S₁ S₂ := by
          calc 0 < ((S₂ x y - S₁ x y) / 2).toNat := by omega
            _ ≤ ∑ y', ((S₂ x y' - S₁ x y') / 2).toNat :=
                Finset.single_le_sum (f := fun y' => ((S₂ x y' - S₁ x y') / 2).toNat)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
            _ ≤ sectionPotential S₁ S₂ :=
                Finset.single_le_sum
                  (f := fun x' => ∑ y', ((S₂ x' y' - S₁ x' y') / 2).toNat)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
        omega
      exact ⟨[], heq, rfl⟩
  | k + 1, S₁, S₂, hk, hwall, hhi => by
      have hne : S₁ ≠ S₂ := by rintro rfl; simp [sectionPotential] at hk
      obtain ⟨x, y, hex, hwall', hhi', hpot⟩ := exists_min_excavatable hwall hhi hne
      obtain ⟨ps, hps, hlen⟩ := exists_schedule_of_potential k (S₁.excavate x y hex) S₂
        (by omega) hwall' hhi'
      exact ⟨(x, y) :: ps, ⟨hex, hps⟩, by simp [hlen]⟩

/-- Any two spacetime sections `S₁ ≤ S₂` that agree on the four boundary walls admit a terminating
legal unit-cell excavation schedule from `S₁` to `S₂` of length `sectionPotential S₁ S₂`. -/
theorem exists_excavationSchedule_of_le {S₁ S₂ : SpaceTimeSection n}
    (hwall : ∀ x y : Fin (n + 1),
      (x.val = 0 ∨ x.val = n ∨ y.val = 0 ∨ y.val = n) → S₁ x y = S₂ x y)
    (hle : ∀ x y, S₁ x y ≤ S₂ x y) :
    ∃ steps : List (Fin (n + 1) × Fin (n + 1)),
      IsExcavationSchedule S₁ S₂ steps ∧ steps.length = sectionPotential S₁ S₂ :=
  exists_schedule_of_potential (sectionPotential S₁ S₂) S₁ S₂ rfl hwall hle

/-- For every `n : ℕ`, repeated minimum-height excavation produces a terminating legal unit-cell
excavation schedule from `lowerSection n` to `upperSection n` of length
`sectionPotential (lowerSection n) (upperSection n)`. -/
theorem exists_associatorExcavationSchedule (n : ℕ) :
    ∃ steps : List (Fin (n + 1) × Fin (n + 1)),
      IsExcavationSchedule (lowerSection n) (upperSection n) steps ∧
        steps.length = sectionPotential (lowerSection n) (upperSection n) :=
  exists_excavationSchedule_of_le (fun x y hw => (lowerSection_eq_upperSection_iff x y).mpr hw)
    (lowerSection_le_upperSection n)

end ExcavationSchedule

end TauCeti.Hive
