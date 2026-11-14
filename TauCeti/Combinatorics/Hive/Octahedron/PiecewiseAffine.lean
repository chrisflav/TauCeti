/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Octahedron.Recurrence
public import TauCeti.Topology.PL.Map
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Integral branch coefficients and piecewise-affine state transitions

Fixing a binary `max`-branch choice `σ : SpaceTimePoint n → Bool` at each point of the bounded
space-time lattice linearizes `extendSection` into `extendSectionBranch`, which evaluates at every
point `p` as an explicit `ℤ`-linear combination `∑ x, ∑ y, branchCoeff hn S σ p x y • val x y` of
the initial section data.

Over `ℝ`, restricting `σ` to the finite dependency closure `depClosure` of any finite future/past
target region `K : Finset (SpaceTimePoint n)` partitions `SectionState n ℝ` into finitely many
convex polyhedral cones (`TauCeti.IsConvexPolyhedron`), on each of which `extendSection` agrees
with a continuous linear map with integral coefficients. Consequently, both region evaluation on
any `K : Finset (SpaceTimePoint n)` and the section-to-section map `sectionTransition hn S₁ S₂`
satisfy `TauCeti.IsPiecewiseAffineOn _ Set.univ` and are continuous.

## Main definitions

* `TauCeti.Hive.depClosure`: finite dependency closure of a space-time point relative to a section.
* `TauCeti.Hive.extendSectionBranch`, `TauCeti.Hive.branchCoeff`, `TauCeti.Hive.activeBranch`:
  fixed-branch linearized recurrence, its integral coefficients, and the active `max`-branch
  selector.
* `TauCeti.Hive.extendSectionBranchCLM`: continuous `ℝ`-linear evaluation of a fixed branch.

## Main results

* `TauCeti.Hive.extendSectionBranch_eq_sum_zsmul`,
  `TauCeti.Hive.extendSection_eq_sum_activeBranch`: integral linear expansion of every branch and
  of `extendSection`.
* `TauCeti.Hive.isPiecewiseAffineOn_extendSection_finset`,
  `TauCeti.Hive.continuous_extendSection_finset`: native finite piecewise-affineness and continuity
  on any finite future/past region.
* `TauCeti.Hive.isPiecewiseAffineOn_sectionTransition`,
  `TauCeti.Hive.continuous_sectionTransition`: piecewise-affineness and continuity of
  `sectionTransition`.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

section PiecewiseAffine

variable {n : ℕ}

/-- Finite set of all points in `SpaceTimePoint n` queried when evaluating `extendSection hn S`
at `p`. -/
def depClosure (hn : 1 ≤ n) (S : SpaceTimeSection n) (p : SpaceTimePoint n) :
    Finset (SpaceTimePoint n) :=
  if h_eq : p.t = S p.finX p.finY then
    {p}
  else if h_gt : S p.finX p.finY < p.t then
    have := sectionDepth_pastHoriz₁_lt hn false h_gt
    have := sectionDepth_pastHoriz₂_lt hn false h_gt
    have := sectionDepth_pastHoriz₁_lt hn true h_gt
    have := sectionDepth_pastHoriz₂_lt hn true h_gt
    have := sectionDepth_pastVert_lt h_gt
    insert p (depClosure hn S (pastHoriz₁ hn false p) ∪
      depClosure hn S (pastHoriz₂ hn false p) ∪
      depClosure hn S (pastHoriz₁ hn true p) ∪
      depClosure hn S (pastHoriz₂ hn true p) ∪
      depClosure hn S (pastVert p))
  else
    have h_lt : p.t < S p.finX p.finY := lt_of_le_of_ne (not_lt.mp h_gt) h_eq
    have := sectionDepth_futureHoriz₁_lt hn false h_lt
    have := sectionDepth_futureHoriz₂_lt hn false h_lt
    have := sectionDepth_futureHoriz₁_lt hn true h_lt
    have := sectionDepth_futureHoriz₂_lt hn true h_lt
    have := sectionDepth_futureVert_lt h_lt
    insert p (depClosure hn S (futureHoriz₁ hn false p) ∪
      depClosure hn S (futureHoriz₂ hn false p) ∪
      depClosure hn S (futureHoriz₁ hn true p) ∪
      depClosure hn S (futureHoriz₂ hn true p) ∪
      depClosure hn S (futureVert p))
termination_by sectionDepth S p

theorem depClosure_of_eq (hn : 1 ≤ n) (S : SpaceTimeSection n) {p : SpaceTimePoint n}
    (h : p.t = S p.finX p.finY) : depClosure hn S p = {p} := by
  rw [depClosure]; simp only [h, ↓reduceDIte]

theorem depClosure_of_gt (hn : 1 ≤ n) (S : SpaceTimeSection n) {p : SpaceTimePoint n}
    (h : S p.finX p.finY < p.t) :
    depClosure hn S p = insert p (depClosure hn S (pastHoriz₁ hn false p) ∪
      depClosure hn S (pastHoriz₂ hn false p) ∪
      depClosure hn S (pastHoriz₁ hn true p) ∪
      depClosure hn S (pastHoriz₂ hn true p) ∪
      depClosure hn S (pastVert p)) := by
  have hne : p.t ≠ S p.finX p.finY := ne_of_gt h
  rw [depClosure]; simp only [hne, h, ↓reduceDIte]

theorem depClosure_of_lt (hn : 1 ≤ n) (S : SpaceTimeSection n) {p : SpaceTimePoint n}
    (h : p.t < S p.finX p.finY) :
    depClosure hn S p = insert p (depClosure hn S (futureHoriz₁ hn false p) ∪
      depClosure hn S (futureHoriz₂ hn false p) ∪
      depClosure hn S (futureHoriz₁ hn true p) ∪
      depClosure hn S (futureHoriz₂ hn true p) ∪
      depClosure hn S (futureVert p)) := by
  have hne : p.t ≠ S p.finX p.finY := ne_of_lt h
  have hngt : ¬ S p.finX p.finY < p.t := not_lt.mpr h.le
  rw [depClosure]; simp only [hne, hngt, ↓reduceDIte]

theorem mem_depClosure_self (hn : 1 ≤ n) (S : SpaceTimeSection n) (p : SpaceTimePoint n) :
    p ∈ depClosure hn S p := by
  rcases lt_trichotomy p.t (S p.finX p.finY) with hlt | heq | hgt
  · rw [depClosure_of_lt hn S hlt]; simp
  · rw [depClosure_of_eq hn S heq]; simp
  · rw [depClosure_of_gt hn S hgt]; simp

theorem depClosure_subset_of_mem (hn : 1 ≤ n) (S : SpaceTimeSection n) :
    ∀ {p q : SpaceTimePoint n}, q ∈ depClosure hn S p → depClosure hn S q ⊆ depClosure hn S p := by
  intro p
  induction p using (measure (sectionDepth S)).wf.induction with
  | h p ih =>
    intro q hq
    rcases lt_trichotomy p.t (S p.finX p.finY) with hlt | heq | hgt
    · rw [depClosure_of_lt hn S hlt] at hq ⊢
      simp only [Finset.mem_insert, Finset.mem_union] at hq
      rcases hq with rfl | (((hq | hq) | hq) | hq) | hq
      · rw [depClosure_of_lt hn S hlt]
      · exact (ih _ (sectionDepth_futureHoriz₁_lt hn false hlt) hq).trans
          (fun _ hx => by simp [hx])
      · exact (ih _ (sectionDepth_futureHoriz₂_lt hn false hlt) hq).trans
          (fun _ hx => by simp [hx])
      · exact (ih _ (sectionDepth_futureHoriz₁_lt hn true hlt) hq).trans
          (fun _ hx => by simp [hx])
      · exact (ih _ (sectionDepth_futureHoriz₂_lt hn true hlt) hq).trans
          (fun _ hx => by simp [hx])
      · exact (ih _ (sectionDepth_futureVert_lt hlt) hq).trans
          (fun _ hx => by simp [hx])
    · rw [depClosure_of_eq hn S heq] at hq ⊢
      simp only [Finset.mem_singleton] at hq; subst hq
      rw [depClosure_of_eq hn S heq]
    · rw [depClosure_of_gt hn S hgt] at hq ⊢
      simp only [Finset.mem_insert, Finset.mem_union] at hq
      rcases hq with rfl | (((hq | hq) | hq) | hq) | hq
      · rw [depClosure_of_gt hn S hgt]
      · exact (ih _ (sectionDepth_pastHoriz₁_lt hn false hgt) hq).trans
          (fun _ hx => by simp [hx])
      · exact (ih _ (sectionDepth_pastHoriz₂_lt hn false hgt) hq).trans
          (fun _ hx => by simp [hx])
      · exact (ih _ (sectionDepth_pastHoriz₁_lt hn true hgt) hq).trans
          (fun _ hx => by simp [hx])
      · exact (ih _ (sectionDepth_pastHoriz₂_lt hn true hgt) hq).trans
          (fun _ hx => by simp [hx])
      · exact (ih _ (sectionDepth_pastVert_lt hgt) hq).trans
          (fun _ hx => by simp [hx])

/-- Linearized recurrence along a fixed binary branch assignment `σ : SpaceTimePoint n → Bool`. -/
def extendSectionBranch {R : Type*} [AddCommGroup R] (hn : 1 ≤ n) (S : SpaceTimeSection n)
    (σ : SpaceTimePoint n → Bool) (val : SectionState n R) (p : SpaceTimePoint n) : R :=
  if h_eq : p.t = S p.finX p.finY then
    val p.finX p.finY
  else if h_gt : S p.finX p.finY < p.t then
    have := sectionDepth_pastHoriz₁_lt hn (σ p) h_gt
    have := sectionDepth_pastHoriz₂_lt hn (σ p) h_gt
    have := sectionDepth_pastVert_lt h_gt
    extendSectionBranch hn S σ val (pastHoriz₁ hn (σ p) p) +
      extendSectionBranch hn S σ val (pastHoriz₂ hn (σ p) p) -
      extendSectionBranch hn S σ val (pastVert p)
  else
    have h_lt : p.t < S p.finX p.finY := lt_of_le_of_ne (not_lt.mp h_gt) h_eq
    have := sectionDepth_futureHoriz₁_lt hn (σ p) h_lt
    have := sectionDepth_futureHoriz₂_lt hn (σ p) h_lt
    have := sectionDepth_futureVert_lt h_lt
    extendSectionBranch hn S σ val (futureHoriz₁ hn (σ p) p) +
      extendSectionBranch hn S σ val (futureHoriz₂ hn (σ p) p) -
      extendSectionBranch hn S σ val (futureVert p)
termination_by sectionDepth S p

theorem extendSectionBranch_of_eq {R : Type*} [AddCommGroup R] (hn : 1 ≤ n)
    (S : SpaceTimeSection n) (σ : SpaceTimePoint n → Bool) (val : SectionState n R)
    {p : SpaceTimePoint n} (h : p.t = S p.finX p.finY) :
    extendSectionBranch hn S σ val p = val p.finX p.finY := by
  rw [extendSectionBranch]; simp only [h, ↓reduceDIte]

theorem extendSectionBranch_of_gt {R : Type*} [AddCommGroup R] (hn : 1 ≤ n)
    (S : SpaceTimeSection n) (σ : SpaceTimePoint n → Bool) (val : SectionState n R)
    {p : SpaceTimePoint n} (h : S p.finX p.finY < p.t) :
    extendSectionBranch hn S σ val p =
      extendSectionBranch hn S σ val (pastHoriz₁ hn (σ p) p) +
        extendSectionBranch hn S σ val (pastHoriz₂ hn (σ p) p) -
        extendSectionBranch hn S σ val (pastVert p) := by
  have hne : p.t ≠ S p.finX p.finY := ne_of_gt h
  rw [extendSectionBranch]; simp only [hne, h, ↓reduceDIte]

theorem extendSectionBranch_of_lt {R : Type*} [AddCommGroup R] (hn : 1 ≤ n)
    (S : SpaceTimeSection n) (σ : SpaceTimePoint n → Bool) (val : SectionState n R)
    {p : SpaceTimePoint n} (h : p.t < S p.finX p.finY) :
    extendSectionBranch hn S σ val p =
      extendSectionBranch hn S σ val (futureHoriz₁ hn (σ p) p) +
        extendSectionBranch hn S σ val (futureHoriz₂ hn (σ p) p) -
        extendSectionBranch hn S σ val (futureVert p) := by
  have hne : p.t ≠ S p.finX p.finY := ne_of_lt h
  have hngt : ¬ S p.finX p.finY < p.t := not_lt.mpr h.le
  rw [extendSectionBranch]; simp only [hne, hngt, ↓reduceDIte]

/-- Integral coefficient of `val x y` in the linearized branch recurrence at `p`. -/
def branchCoeff (hn : 1 ≤ n) (S : SpaceTimeSection n) (σ : SpaceTimePoint n → Bool)
    (p : SpaceTimePoint n) (x y : Fin (n + 1)) : ℤ :=
  extendSectionBranch hn S σ (fun x' y' => if x' = x ∧ y' = y then 1 else 0) p

/-- Every fixed-branch evaluation is an explicit `ℤ`-linear combination of the initial section
values `val x y`. -/
theorem extendSectionBranch_eq_sum_zsmul {R : Type*} [AddCommGroup R] (hn : 1 ≤ n)
    (S : SpaceTimeSection n) (σ : SpaceTimePoint n → Bool) (val : SectionState n R)
    (p : SpaceTimePoint n) :
    extendSectionBranch hn S σ val p =
      ∑ x : Fin (n + 1), ∑ y : Fin (n + 1), branchCoeff hn S σ p x y • val x y := by
  induction p using (measure (sectionDepth S)).wf.induction with
  | h p ih =>
    rcases lt_trichotomy p.t (S p.finX p.finY) with hlt | heq | hgt
    · rw [extendSectionBranch_of_lt hn S σ val hlt,
        ih _ (sectionDepth_futureHoriz₁_lt hn (σ p) hlt),
        ih _ (sectionDepth_futureHoriz₂_lt hn (σ p) hlt),
        ih _ (sectionDepth_futureVert_lt hlt)]
      simp_rw [branchCoeff, extendSectionBranch_of_lt hn S σ _ hlt]
      simp only [sub_eq_add_neg, add_zsmul, neg_zsmul, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
    · rw [extendSectionBranch_of_eq hn S σ val heq]
      simp_rw [branchCoeff, extendSectionBranch_of_eq hn S σ _ heq]
      simp [ite_smul, ite_and]
    · rw [extendSectionBranch_of_gt hn S σ val hgt,
        ih _ (sectionDepth_pastHoriz₁_lt hn (σ p) hgt),
        ih _ (sectionDepth_pastHoriz₂_lt hn (σ p) hgt),
        ih _ (sectionDepth_pastVert_lt hgt)]
      simp_rw [branchCoeff, extendSectionBranch_of_gt hn S σ _ hgt]
      simp only [sub_eq_add_neg, add_zsmul, neg_zsmul, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]

/-- Active `max`-branch selector for a given section state `val`. -/
def activeBranch {R : Type*} [AddCommGroup R] [LinearOrder R] (hn : 1 ≤ n)
    (S : SpaceTimeSection n) (val : SectionState n R) (p : SpaceTimePoint n) : Bool :=
  if S p.finX p.finY < p.t then
    decide (extendSection hn S val (pastHoriz₁ hn false p) +
        extendSection hn S val (pastHoriz₂ hn false p) ≤
      extendSection hn S val (pastHoriz₁ hn true p) +
        extendSection hn S val (pastHoriz₂ hn true p))
  else
    decide (extendSection hn S val (futureHoriz₁ hn false p) +
        extendSection hn S val (futureHoriz₂ hn false p) ≤
      extendSection hn S val (futureHoriz₁ hn true p) +
        extendSection hn S val (futureHoriz₂ hn true p))

theorem extendSection_eq_extendSectionBranch_active {R : Type*} [AddCommGroup R] [LinearOrder R]
    (hn : 1 ≤ n) (S : SpaceTimeSection n) (val : SectionState n R) (p : SpaceTimePoint n) :
    extendSection hn S val p = extendSectionBranch hn S (activeBranch hn S val) val p := by
  induction p using (measure (sectionDepth S)).wf.induction with
  | h p ih =>
    rcases lt_trichotomy p.t (S p.finX p.finY) with hlt | heq | hgt
    · have hngt : ¬ S p.finX p.finY < p.t := not_lt.mpr hlt.le
      rw [extendSection_of_lt hn S val hlt, extendSectionBranch_of_lt hn S _ val hlt,
        ← ih _ (sectionDepth_futureHoriz₁_lt hn _ hlt),
        ← ih _ (sectionDepth_futureHoriz₂_lt hn _ hlt),
        ← ih _ (sectionDepth_futureVert_lt hlt)]
      simp only [activeBranch, hngt, ↓reduceIte]
      by_cases hle : extendSection hn S val (futureHoriz₁ hn false p) +
          extendSection hn S val (futureHoriz₂ hn false p) ≤
        extendSection hn S val (futureHoriz₁ hn true p) +
          extendSection hn S val (futureHoriz₂ hn true p)
      · simp [hle]
      · simp [hle, max_eq_left (le_of_not_ge hle)]
    · rw [extendSection_of_eq hn S val heq, extendSectionBranch_of_eq hn S _ val heq]
    · rw [extendSection_of_gt hn S val hgt, extendSectionBranch_of_gt hn S _ val hgt,
        ← ih _ (sectionDepth_pastHoriz₁_lt hn _ hgt),
        ← ih _ (sectionDepth_pastHoriz₂_lt hn _ hgt),
        ← ih _ (sectionDepth_pastVert_lt hgt)]
      simp only [activeBranch, hgt, ↓reduceIte]
      by_cases hle : extendSection hn S val (pastHoriz₁ hn false p) +
          extendSection hn S val (pastHoriz₂ hn false p) ≤
        extendSection hn S val (pastHoriz₁ hn true p) +
          extendSection hn S val (pastHoriz₂ hn true p)
      · simp [hle]
      · simp [hle, max_eq_left (le_of_not_ge hle)]

/-- Every point value of `extendSection` is an integral linear combination of initial section
values determined by `activeBranch`. -/
theorem extendSection_eq_sum_activeBranch {R : Type*} [AddCommGroup R] [LinearOrder R]
    (hn : 1 ≤ n) (S : SpaceTimeSection n) (val : SectionState n R) (p : SpaceTimePoint n) :
    extendSection hn S val p =
      ∑ x : Fin (n + 1), ∑ y : Fin (n + 1),
        branchCoeff hn S (activeBranch hn S val) p x y • val x y := by
  rw [extendSection_eq_extendSectionBranch_active, extendSectionBranch_eq_sum_zsmul]

theorem extendSectionBranch_congr {R : Type*} [AddCommGroup R] (hn : 1 ≤ n)
    (S : SpaceTimeSection n) {σ₁ σ₂ : SpaceTimePoint n → Bool} (val : SectionState n R) :
    ∀ {p : SpaceTimePoint n}, (∀ q ∈ depClosure hn S p, σ₁ q = σ₂ q) →
      extendSectionBranch hn S σ₁ val p = extendSectionBranch hn S σ₂ val p := by
  intro p
  induction p using (measure (sectionDepth S)).wf.induction with
  | h p ih =>
    intro hσ
    have hp : σ₁ p = σ₂ p := hσ p (mem_depClosure_self hn S p)
    rcases lt_trichotomy p.t (S p.finX p.finY) with hlt | heq | hgt
    · rw [extendSectionBranch_of_lt hn S σ₁ val hlt, extendSectionBranch_of_lt hn S σ₂ val hlt, hp,
        ih _ (sectionDepth_futureHoriz₁_lt hn (σ₂ p) hlt) fun q hq => hσ q
          (depClosure_subset_of_mem hn S
            (by rw [depClosure_of_lt hn S hlt]; cases σ₂ p <;> simp [mem_depClosure_self]) hq),
        ih _ (sectionDepth_futureHoriz₂_lt hn (σ₂ p) hlt) fun q hq => hσ q
          (depClosure_subset_of_mem hn S
            (by rw [depClosure_of_lt hn S hlt]; cases σ₂ p <;> simp [mem_depClosure_self]) hq),
        ih _ (sectionDepth_futureVert_lt hlt) fun q hq => hσ q
          (depClosure_subset_of_mem hn S
            (by rw [depClosure_of_lt hn S hlt]; simp [mem_depClosure_self]) hq)]
    · rw [extendSectionBranch_of_eq hn S σ₁ val heq, extendSectionBranch_of_eq hn S σ₂ val heq]
    · rw [extendSectionBranch_of_gt hn S σ₁ val hgt, extendSectionBranch_of_gt hn S σ₂ val hgt, hp,
        ih _ (sectionDepth_pastHoriz₁_lt hn (σ₂ p) hgt) fun q hq => hσ q
          (depClosure_subset_of_mem hn S
            (by rw [depClosure_of_gt hn S hgt]; cases σ₂ p <;> simp [mem_depClosure_self]) hq),
        ih _ (sectionDepth_pastHoriz₂_lt hn (σ₂ p) hgt) fun q hq => hσ q
          (depClosure_subset_of_mem hn S
            (by rw [depClosure_of_gt hn S hgt]; cases σ₂ p <;> simp [mem_depClosure_self]) hq),
        ih _ (sectionDepth_pastVert_lt hgt) fun q hq => hσ q
          (depClosure_subset_of_mem hn S
            (by rw [depClosure_of_gt hn S hgt]; simp [mem_depClosure_self]) hq)]

/-- Continuous `ℝ`-linear functional evaluating `extendSectionBranch hn S σ · p`. -/
noncomputable def extendSectionBranchCLM (hn : 1 ≤ n) (S : SpaceTimeSection n)
    (σ : SpaceTimePoint n → Bool) (p : SpaceTimePoint n) : SectionState n ℝ →L[ℝ] ℝ :=
  ∑ x : Fin (n + 1), ∑ y : Fin (n + 1),
    (branchCoeff hn S σ p x y : ℝ) •
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) y).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => Fin (n + 1) → ℝ) x))

@[simp] theorem extendSectionBranchCLM_apply (hn : 1 ≤ n) (S : SpaceTimeSection n)
    (σ : SpaceTimePoint n → Bool) (p : SpaceTimePoint n) (val : SectionState n ℝ) :
    extendSectionBranchCLM hn S σ p val = extendSectionBranch hn S σ val p := by
  rw [extendSectionBranchCLM, extendSectionBranch_eq_sum_zsmul]
  simp [zsmul_eq_mul]

private noncomputable def branchDiffCLM (hn : 1 ≤ n) (S : SpaceTimeSection n)
    (σ : SpaceTimePoint n → Bool) (p : SpaceTimePoint n) : SectionState n ℝ →L[ℝ] ℝ :=
  if p.t = S p.finX p.finY then 0
  else if S p.finX p.finY < p.t then
    (extendSectionBranchCLM hn S σ (pastHoriz₁ hn (!σ p) p) +
      extendSectionBranchCLM hn S σ (pastHoriz₂ hn (!σ p) p)) -
    (extendSectionBranchCLM hn S σ (pastHoriz₁ hn (σ p) p) +
      extendSectionBranchCLM hn S σ (pastHoriz₂ hn (σ p) p))
  else
    (extendSectionBranchCLM hn S σ (futureHoriz₁ hn (!σ p) p) +
      extendSectionBranchCLM hn S σ (futureHoriz₂ hn (!σ p) p)) -
    (extendSectionBranchCLM hn S σ (futureHoriz₁ hn (σ p) p) +
      extendSectionBranchCLM hn S σ (futureHoriz₂ hn (σ p) p))

private theorem extendSection_eq_branch_of_cell (hn : 1 ≤ n) (S : SpaceTimeSection n)
    {D : Finset (SpaceTimePoint n)} (hD : ∀ q ∈ D, depClosure hn S q ⊆ D)
    (σ : SpaceTimePoint n → Bool) {val : SectionState n ℝ}
    (hcell : ∀ q ∈ D, branchDiffCLM hn S σ q val ≤ 0) :
    ∀ q ∈ D, extendSection hn S val q = extendSectionBranch hn S σ val q := by
  intro q
  induction q using (measure (sectionDepth S)).wf.induction with
  | h q ih =>
    intro hqD
    have hsub := hD q hqD
    have hle := hcell q hqD
    rcases lt_trichotomy q.t (S q.finX q.finY) with hlt | heq | hgt
    · have hne : q.t ≠ S q.finX q.finY := ne_of_lt hlt
      have hngt : ¬ S q.finX q.finY < q.t := not_lt.mpr hlt.le
      have hmem (b : Bool) : futureHoriz₁ hn b q ∈ D ∧ futureHoriz₂ hn b q ∈ D := by
        constructor <;> apply hsub <;> rw [depClosure_of_lt hn S hlt] <;>
          cases b <;> simp [mem_depClosure_self]
      have hvD : futureVert q ∈ D :=
        hsub (by rw [depClosure_of_lt hn S hlt]; simp [mem_depClosure_self])
      simp only [branchDiffCLM, hne, hngt, ↓reduceIte, sub_apply, _root_.add_apply,
        extendSectionBranchCLM_apply,
        ← ih _ (sectionDepth_futureHoriz₁_lt hn _ hlt) (hmem _).1,
        ← ih _ (sectionDepth_futureHoriz₂_lt hn _ hlt) (hmem _).2] at hle
      rw [extendSection_of_lt hn S val hlt, extendSectionBranch_of_lt hn S σ val hlt,
        ← ih _ (sectionDepth_futureHoriz₁_lt hn (σ q) hlt) (hmem (σ q)).1,
        ← ih _ (sectionDepth_futureHoriz₂_lt hn (σ q) hlt) (hmem (σ q)).2,
        ← ih _ (sectionDepth_futureVert_lt hlt) hvD]
      cases hσ : σ q <;> simp only [hσ, Bool.not_false, Bool.not_true, sub_nonpos] at hle ⊢
      · rw [max_eq_left hle]
      · rw [max_eq_right hle]
    · rw [extendSection_of_eq hn S val heq, extendSectionBranch_of_eq hn S σ val heq]
    · have hne : q.t ≠ S q.finX q.finY := ne_of_gt hgt
      have hmem (b : Bool) : pastHoriz₁ hn b q ∈ D ∧ pastHoriz₂ hn b q ∈ D := by
        constructor <;> apply hsub <;> rw [depClosure_of_gt hn S hgt] <;>
          cases b <;> simp [mem_depClosure_self]
      have hvD : pastVert q ∈ D :=
        hsub (by rw [depClosure_of_gt hn S hgt]; simp [mem_depClosure_self])
      simp only [branchDiffCLM, hne, hgt, ↓reduceIte, sub_apply, _root_.add_apply,
        extendSectionBranchCLM_apply,
        ← ih _ (sectionDepth_pastHoriz₁_lt hn _ hgt) (hmem _).1,
        ← ih _ (sectionDepth_pastHoriz₂_lt hn _ hgt) (hmem _).2] at hle
      rw [extendSection_of_gt hn S val hgt, extendSectionBranch_of_gt hn S σ val hgt,
        ← ih _ (sectionDepth_pastHoriz₁_lt hn (σ q) hgt) (hmem (σ q)).1,
        ← ih _ (sectionDepth_pastHoriz₂_lt hn (σ q) hgt) (hmem (σ q)).2,
        ← ih _ (sectionDepth_pastVert_lt hgt) hvD]
      cases hσ : σ q <;> simp only [hσ, Bool.not_false, Bool.not_true, sub_nonpos] at hle ⊢
      · rw [max_eq_left hle]
      · rw [max_eq_right hle]

private theorem branchDiffCLM_nonpos_of_active (hn : 1 ≤ n) (S : SpaceTimeSection n)
    {D : Finset (SpaceTimePoint n)} (hD : ∀ q ∈ D, depClosure hn S q ⊆ D)
    (val : SectionState n ℝ) {σ : SpaceTimePoint n → Bool}
    (hσ : ∀ q ∈ D, σ q = activeBranch hn S val q) {q : SpaceTimePoint n} (hq : q ∈ D) :
    branchDiffCLM hn S σ q val ≤ 0 := by
  have heval (r : SpaceTimePoint n) (hr : r ∈ D) :
      extendSectionBranch hn S σ val r = extendSection hn S val r :=
    (extendSectionBranch_congr hn S val fun u hu => hσ u (hD r hr hu)).trans
      (extendSection_eq_extendSectionBranch_active hn S val r).symm
  have hsub := hD q hq
  rcases lt_trichotomy q.t (S q.finX q.finY) with hlt | heq | hgt
  · have hne : q.t ≠ S q.finX q.finY := ne_of_lt hlt
    have hngt : ¬ S q.finX q.finY < q.t := not_lt.mpr hlt.le
    have hmem (b : Bool) : futureHoriz₁ hn b q ∈ D ∧ futureHoriz₂ hn b q ∈ D := by
      constructor <;> apply hsub <;> rw [depClosure_of_lt hn S hlt] <;>
        cases b <;> simp [mem_depClosure_self]
    simp only [branchDiffCLM, hne, hngt, ↓reduceIte, sub_apply, _root_.add_apply,
      extendSectionBranchCLM_apply,
      heval _ (hmem _).1, heval _ (hmem _).2, hσ q hq, activeBranch]
    by_cases hle : extendSection hn S val (futureHoriz₁ hn false q) +
        extendSection hn S val (futureHoriz₂ hn false q) ≤
      extendSection hn S val (futureHoriz₁ hn true q) +
        extendSection hn S val (futureHoriz₂ hn true q) <;> simp [hle]
    linarith
  · simp [branchDiffCLM, heq]
  · have hne : q.t ≠ S q.finX q.finY := ne_of_gt hgt
    have hmem (b : Bool) : pastHoriz₁ hn b q ∈ D ∧ pastHoriz₂ hn b q ∈ D := by
      constructor <;> apply hsub <;> rw [depClosure_of_gt hn S hgt] <;>
        cases b <;> simp [mem_depClosure_self]
    simp only [branchDiffCLM, hne, hgt, ↓reduceIte, sub_apply, _root_.add_apply,
      extendSectionBranchCLM_apply,
      heval _ (hmem _).1, heval _ (hmem _).2, hσ q hq, activeBranch]
    by_cases hle : extendSection hn S val (pastHoriz₁ hn false q) +
        extendSection hn S val (pastHoriz₂ hn false q) ≤
      extendSection hn S val (pastHoriz₁ hn true q) +
        extendSection hn S val (pastHoriz₂ hn true q) <;> simp [hle]
    linarith

/-- On any finite future/past region `K : Finset (SpaceTimePoint n)`, evaluating `extendSection`
over `ℝ` is piecewise affine on `Set.univ`, with polyhedral cones indexed by `max`-branch choices
on the dependency closure of `K`. -/
theorem isPiecewiseAffineOn_extendSection_finset (hn : 1 ≤ n) (S : SpaceTimeSection n)
    (K : Finset (SpaceTimePoint n)) :
    IsPiecewiseAffineOn (fun (val : SectionState n ℝ) (q : K) => extendSection hn S val q.1)
      Set.univ := by
  let D : Finset (SpaceTimePoint n) := K.biUnion (depClosure hn S)
  have hD : ∀ q ∈ D, depClosure hn S q ⊆ D := by
    intro q hq r hr
    obtain ⟨p, hpK, hqp⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_biUnion.mpr ⟨p, hpK, depClosure_subset_of_mem hn S hqp hr⟩
  have hKD : ∀ q : K, q.1 ∈ D := fun q =>
    Finset.mem_biUnion.mpr ⟨q.1, q.2, mem_depClosure_self hn S q.1⟩
  let ext (τ : D → Bool) (q : SpaceTimePoint n) : Bool :=
    if h : q ∈ D then τ ⟨q, h⟩ else false
  let C (τ : D → Bool) : Set (SectionState n ℝ) :=
    {val | ∀ q : D, (branchDiffCLM hn S (ext τ) q.1).toContinuousAffineMap val ≤ 0}
  let A (τ : D → Bool) : SectionState n ℝ →ᴬ[ℝ] (K → ℝ) :=
    (ContinuousLinearMap.pi fun q : K =>
      extendSectionBranchCLM hn S (ext τ) q.1).toContinuousAffineMap
  refine isPiecewiseAffineOn_of_finite (ι := D → Bool) (C := C) (A := A)
    (fun τ => isConvexPolyhedron_setOf_forall _) ?_ ?_
  · intro val _
    let τ : D → Bool := fun q => activeBranch hn S val q.1
    refine Set.mem_iUnion.mpr ⟨τ, fun q => ?_⟩
    exact branchDiffCLM_nonpos_of_active hn S hD val
      (fun r hr => by simp [ext, τ, hr]) q.2
  · intro τ val ⟨_, hval⟩
    funext q
    simpa [A] using
      extendSection_eq_branch_of_cell hn S hD (ext τ) (fun r hr => hval ⟨r, hr⟩) q.1 (hKD q)

/-- Evaluating `extendSection` on any finite region `K` over `ℝ` is continuous. -/
theorem continuous_extendSection_finset (hn : 1 ≤ n) (S : SpaceTimeSection n)
    (K : Finset (SpaceTimePoint n)) :
    Continuous (fun (val : SectionState n ℝ) (q : K) => extendSection hn S val q.1) :=
  continuousOn_univ.mp (isPiecewiseAffineOn_extendSection_finset hn S K).continuousOn

/-- The section-to-section transition `sectionTransition hn S₁ S₂` over `ℝ` is piecewise affine on
`Set.univ`. -/
theorem isPiecewiseAffineOn_sectionTransition (hn : 1 ≤ n) (S₁ S₂ : SpaceTimeSection n) :
    IsPiecewiseAffineOn (sectionTransition hn S₁ S₂ : SectionState n ℝ → SectionState n ℝ)
      Set.univ := by
  let K : Finset (SpaceTimePoint n) :=
    Finset.univ.image fun p : Fin (n + 1) × Fin (n + 1) => S₂.point p.1 p.2
  have hmem (x y : Fin (n + 1)) : S₂.point x y ∈ K :=
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, rfl⟩
  let readCLM : (K → ℝ) →L[ℝ] SectionState n ℝ :=
    ContinuousLinearMap.pi fun x => ContinuousLinearMap.pi fun y =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : K => ℝ) (⟨S₂.point x y, hmem x y⟩ : K)
  have heq : (sectionTransition hn S₁ S₂ : SectionState n ℝ → SectionState n ℝ) =
      readCLM.toContinuousAffineMap ∘
        fun (val : SectionState n ℝ) (q : K) => extendSection hn S₁ val q.1 := by
    ext val x y; simp [readCLM]
  rw [heq]
  exact (isPiecewiseAffineOn_continuousAffineMap readCLM.toContinuousAffineMap Set.univ).comp
    (isPiecewiseAffineOn_extendSection_finset hn S₁ K) (Set.mapsTo_univ _ _)

/-- The section-to-section transition `sectionTransition hn S₁ S₂` over `ℝ` is continuous. -/
theorem continuous_sectionTransition (hn : 1 ≤ n) (S₁ S₂ : SpaceTimeSection n) :
    Continuous (sectionTransition hn S₁ S₂ : SectionState n ℝ → SectionState n ℝ) :=
  continuousOn_univ.mp (isPiecewiseAffineOn_sectionTransition hn S₁ S₂).continuousOn

end PiecewiseAffine

end TauCeti.Hive
