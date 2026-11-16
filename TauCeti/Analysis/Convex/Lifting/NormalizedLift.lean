/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Lifting.FiniteModel
import Mathlib.Tactic.Linarith

/-!
# Affine-argument normalization for finite mixed-integer models

When each nonlinear residual of a `FiniteModel` decomposes as a weighted finite sum of univariate
functions evaluated at affine arguments,

    d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x),

`FiniteModel.normalizedLift` appends one continuous variable per argument, retains every original
affine row and integer bound, assigns zero objective coefficients to the new variables, and adds
pairs of opposite affine inequalities enforcing
`height z j = affineArgument (a j) (b j) (offset j) (project z)`.

Because normalization acts by exact equality substitution, it preserves the mixed-integer feasible
set, the continuous relaxation, feasible minima, and attainment of feasible minima without
positivity, convexity, or smoothness assumptions.

## Main definitions

* `TauCeti.ConvexLifting.FiniteModel.normalizedLift`: lifted model introducing one continuous
  equality variable per affine argument.

## Main statements

* `TauCeti.ConvexLifting.FiniteModel.normalizedLift_affine_iff`: characterization of the
  normalized affine rows as the original rows plus the exact argument equalities.
* `TauCeti.ConvexLifting.FiniteModel.normalization_projection`: exact projection of mixed-integer
  feasible points.
* `TauCeti.ConvexLifting.FiniteModel.normalization_relaxation_projection`: exact projection of
  the continuous relaxation.
* `TauCeti.ConvexLifting.FiniteModel.normalization_minimum_iff` and
  `TauCeti.ConvexLifting.FiniteModel.normalization_attainment_iff`: transfer of feasible minima
  and their attainment.

## References

* H. Hijazi, P. Bonami, and A. Ouorou, *An Outer-Inner Approximation for Separable Mixed-Integer
  Nonlinear Programs*, INFORMS Journal on Computing, Articles in Advance (2013), pp. 1–14,
  §3 opening, p. 4 (affine-argument normalization).
-/

public section

open Set

namespace TauCeti.ConvexLifting.FiniteModel

variable {n m l r q : ℕ}

/-- Affine-argument normalization: append one continuous coordinate per affine argument, retain
all original affine rows, and add pairs of opposite affine inequalities imposing each argument
equality. -/
def normalizedLift (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    FiniteModel (n + q) m l (r + (q + q)) where
  g := fun i z => ∑ j, weight i j * phi j (height z j)
  A := Fin.addCases (fun i => Fin.addCases (d.A i) (fun _ => 0))
    (Fin.addCases (fun j => Fin.addCases (-a j) (Pi.single j 1))
      (fun j => Fin.addCases (a j) (Pi.single j (-1))))
  B := Fin.addCases d.B (Fin.addCases (fun j => -b j) b)
  rhs := Fin.addCases d.rhs (Fin.addCases offset (-offset))
  c1 := Fin.addCases d.c1 (fun _ => 0)
  c2 := d.c2
  lo := d.lo
  hi := d.hi

/-- Nonlinear residual evaluation of `normalizedLift`. -/
@[simp]
theorem normalizedLift_g (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (i : Fin l) (z : Point (n + q) m) :
    (d.normalizedLift a b offset phi weight).g i z = ∑ j, weight i j * phi j (height z j) :=
  (rfl)

/-- Continuous-block affine matrix of `normalizedLift`. -/
@[simp]
theorem normalizedLift_A (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.normalizedLift a b offset phi weight).A =
      Fin.addCases (fun i => Fin.addCases (d.A i) (fun _ => 0))
        (Fin.addCases (fun j => Fin.addCases (-a j) (Pi.single j 1))
          (fun j => Fin.addCases (a j) (Pi.single j (-1)))) :=
  (rfl)

/-- Integer-block affine matrix of `normalizedLift`. -/
@[simp]
theorem normalizedLift_B (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.normalizedLift a b offset phi weight).B =
      Fin.addCases d.B (Fin.addCases (fun j => -b j) b) :=
  (rfl)

/-- Right-hand side vector of `normalizedLift`. -/
@[simp]
theorem normalizedLift_rhs (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.normalizedLift a b offset phi weight).rhs =
      Fin.addCases d.rhs (Fin.addCases offset (-offset)) :=
  (rfl)

/-- Continuous-block objective coefficients of `normalizedLift`. -/
@[simp]
theorem normalizedLift_c1 (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.normalizedLift a b offset phi weight).c1 = Fin.addCases d.c1 (fun _ => 0) :=
  (rfl)

/-- Integer-block objective coefficients of `normalizedLift`. -/
@[simp]
theorem normalizedLift_c2 (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.normalizedLift a b offset phi weight).c2 = d.c2 :=
  (rfl)

/-- Lower bounds of `normalizedLift`. -/
@[simp]
theorem normalizedLift_lo (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.normalizedLift a b offset phi weight).lo = d.lo :=
  (rfl)

/-- Upper bounds of `normalizedLift`. -/
@[simp]
theorem normalizedLift_hi (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.normalizedLift a b offset phi weight).hi = d.hi :=
  (rfl)

/-- The objective of `normalizedLift` is the pullback of the original objective along `project`. -/
@[simp]
theorem normalizedLift_objective (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (z : Point (n + q) m) :
    (d.normalizedLift a b offset phi weight).objective z = d.objective (project z) :=
  d.objective_eq_comp_project (d.normalizedLift a b offset phi weight) rfl rfl z

/-- The affine rows of `normalizedLift` are equivalent to the original affine rows on `project z`
together with the argument equalities
`height z j = affineArgument (a j) (b j) (offset j) (project z)`. -/
theorem normalizedLift_affine_iff (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (z : Point (n + q) m) :
    (∀ k, (∑ i, (d.normalizedLift a b offset phi weight).A k i * z.1 i) +
        (∑ j, (d.normalizedLift a b offset phi weight).B k j * z.2 j) ≤
          (d.normalizedLift a b offset phi weight).rhs k) ↔
      (∀ k, (∑ i, d.A k i * (project z).1 i) + (∑ j, d.B k j * (project z).2 j) ≤ d.rhs k) ∧
        ∀ j, height z j = affineArgument (a j) (b j) (offset j) (project z) := by
  rw [Fin.forall_fin_add]
  simp only [normalizedLift_A, normalizedLift_B, normalizedLift_rhs, Fin.addCases_left,
    Fin.addCases_right, sum_addCases_zero_mul, project_snd]
  refine and_congr_right fun _ => ?_
  rw [Fin.forall_fin_add]
  simp only [Fin.addCases_left, Fin.addCases_right, sum_addCases_single_mul, Pi.neg_apply,
    neg_mul, Finset.sum_neg_distrib, one_mul]
  constructor
  · rintro ⟨hle, hge⟩ j
    have h1 := hle j
    have h2 := hge j
    rw [affineArgument_apply, project_snd]
    linarith
  · intro heq
    refine ⟨fun j => ?_, fun j => ?_⟩ <;>
    · have h := heq j
      rw [affineArgument_apply, project_snd] at h
      linarith

/-- Mixed-integer feasibility in `normalizedLift` at `z` is equivalent to mixed-integer feasibility
of `project z` together with the argument equalities. -/
theorem mem_normalizedLift_feasibleOn_iff (d : FiniteModel n m l r) {D : Set (Point n m)}
    {a : Fin q → Fin n → ℝ} {b : Fin q → Fin m → ℝ} {offset : Fin q → ℝ}
    {phi : Fin q → ℝ → ℝ} {weight : Fin l → Fin q → ℝ} {z : Point (n + q) m}
    (hg : project z ∈ D → ∀ i, d.g i (project z) = ∑ j, weight i j *
      phi j (affineArgument (a j) (b j) (offset j) (project z))) :
    z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) ↔
      project z ∈ d.feasibleOn D ∧
        ∀ j, height z j = affineArgument (a j) (b j) (offset j) (project z) := by
  simp only [mem_feasibleOn_iff, mem_preimage, normalizedLift_g, normalizedLift_lo,
    normalizedLift_hi, normalizedLift_affine_iff, project_snd]
  constructor
  · rintro ⟨hzD, hgn, ⟨haff, heq⟩, hint⟩
    refine ⟨⟨hzD, fun i => ?_, haff, hint⟩, heq⟩
    rw [hg hzD i]
    simpa only [heq] using hgn i
  · rintro ⟨⟨hzD, hgo, haff, hint⟩, heq⟩
    refine ⟨hzD, fun i => ?_, ⟨haff, heq⟩, hint⟩
    simpa only [heq, ← hg hzD i] using hgo i

/-- Continuous-relaxation feasibility in `normalizedLift` at `z` is equivalent to relaxation
feasibility of `project z` together with the argument equalities. -/
theorem mem_normalizedLift_relaxationOn_iff (d : FiniteModel n m l r) {D : Set (Point n m)}
    {a : Fin q → Fin n → ℝ} {b : Fin q → Fin m → ℝ} {offset : Fin q → ℝ}
    {phi : Fin q → ℝ → ℝ} {weight : Fin l → Fin q → ℝ} {z : Point (n + q) m}
    (hg : project z ∈ D → ∀ i, d.g i (project z) = ∑ j, weight i j *
      phi j (affineArgument (a j) (b j) (offset j) (project z))) :
    z ∈ (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) ↔
      project z ∈ d.relaxationOn D ∧
        ∀ j, height z j = affineArgument (a j) (b j) (offset j) (project z) := by
  simp only [mem_relaxationOn_iff, mem_preimage, normalizedLift_g, normalizedLift_lo,
    normalizedLift_hi, normalizedLift_affine_iff, project_snd]
  constructor
  · rintro ⟨hzD, hgn, ⟨haff, heq⟩, hbox⟩
    refine ⟨⟨hzD, fun i => ?_, haff, hbox⟩, heq⟩
    rw [hg hzD i]
    simpa only [heq] using hgn i
  · rintro ⟨⟨hzD, hgo, haff, hbox⟩, heq⟩
    refine ⟨hzD, fun i => ?_, ⟨haff, heq⟩, hbox⟩
    simpa only [heq, ← hg hzD i] using hgo i

/-- Canonical insertion of the actual affine argument values lifts mixed-integer feasibility. -/
theorem insertHeight_mem_normalizedLift_feasibleOn_iff (d : FiniteModel n m l r)
    {D : Set (Point n m)} {a : Fin q → Fin n → ℝ} {b : Fin q → Fin m → ℝ} {offset : Fin q → ℝ}
    {phi : Fin q → ℝ → ℝ} {weight : Fin l → Fin q → ℝ} {x : Point n m}
    (hg : x ∈ D → ∀ i, d.g i x = ∑ j, weight i j *
      phi j (affineArgument (a j) (b j) (offset j) x)) :
    insertHeight x (fun j => affineArgument (a j) (b j) (offset j) x) ∈
        (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) ↔
      x ∈ d.feasibleOn D := by
  rw [d.mem_normalizedLift_feasibleOn_iff (by simpa using hg)]
  simp

/-- Canonical insertion of the actual affine argument values lifts relaxation feasibility. -/
theorem insertHeight_mem_normalizedLift_relaxationOn_iff (d : FiniteModel n m l r)
    {D : Set (Point n m)} {a : Fin q → Fin n → ℝ} {b : Fin q → Fin m → ℝ} {offset : Fin q → ℝ}
    {phi : Fin q → ℝ → ℝ} {weight : Fin l → Fin q → ℝ} {x : Point n m}
    (hg : x ∈ D → ∀ i, d.g i x = ∑ j, weight i j *
      phi j (affineArgument (a j) (b j) (offset j) x)) :
    insertHeight x (fun j => affineArgument (a j) (b j) (offset j) x) ∈
        (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) ↔
      x ∈ d.relaxationOn D := by
  rw [d.mem_normalizedLift_relaxationOn_iff (by simpa using hg)]
  simp

/-- Affine-argument normalization projects mixed-integer feasible points exactly onto the original
feasible set, without positivity, convexity, or smoothness assumptions. -/
theorem normalization_projection (d : FiniteModel n m l r) {D : Set (Point n m)}
    {a : Fin q → Fin n → ℝ} {b : Fin q → Fin m → ℝ} {offset : Fin q → ℝ}
    {phi : Fin q → ℝ → ℝ} {weight : Fin l → Fin q → ℝ}
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j *
      phi j (affineArgument (a j) (b j) (offset j) x)) :
    project '' (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) =
      d.feasibleOn D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ((d.mem_normalizedLift_feasibleOn_iff fun h i => hg i _ h).1 hz).1
  · intro hx
    exact ⟨insertHeight x (fun j => affineArgument (a j) (b j) (offset j) x),
      (d.insertHeight_mem_normalizedLift_feasibleOn_iff fun h i => hg i _ h).2 hx,
      project_insertHeight _ _⟩

/-- Affine-argument normalization preserves the continuous relaxation exactly under projection. -/
theorem normalization_relaxation_projection (d : FiniteModel n m l r) {D : Set (Point n m)}
    {a : Fin q → Fin n → ℝ} {b : Fin q → Fin m → ℝ} {offset : Fin q → ℝ}
    {phi : Fin q → ℝ → ℝ} {weight : Fin l → Fin q → ℝ}
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j *
      phi j (affineArgument (a j) (b j) (offset j) x)) :
    project '' (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) =
      d.relaxationOn D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ((d.mem_normalizedLift_relaxationOn_iff fun h i => hg i _ h).1 hz).1
  · intro hx
    exact ⟨insertHeight x (fun j => affineArgument (a j) (b j) (offset j) x),
      (d.insertHeight_mem_normalizedLift_relaxationOn_iff fun h i => hg i _ h).2 hx,
      project_insertHeight _ _⟩

/-- Feasible minima of `normalizedLift` correspond directly to feasible minima of the original
model at the projected point. -/
theorem normalization_minimum_iff (d : FiniteModel n m l r) {D : Set (Point n m)}
    {a : Fin q → Fin n → ℝ} {b : Fin q → Fin m → ℝ} {offset : Fin q → ℝ}
    {phi : Fin q → ℝ → ℝ} {weight : Fin l → Fin q → ℝ}
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j *
      phi j (affineArgument (a j) (b j) (offset j) x)) (z : Point (n + q) m) :
    (z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) ∧
      IsMinOn (d.normalizedLift a b offset phi weight).objective
        ((d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D)) z) ↔
      z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) ∧
        project z ∈ d.feasibleOn D ∧ IsMinOn d.objective (d.feasibleOn D) (project z) := by
  have hobj : (d.normalizedLift a b offset phi weight).objective = d.objective ∘ project :=
    funext (d.normalizedLift_objective a b offset phi weight)
  rw [hobj]
  constructor
  · rintro ⟨hz, hmin⟩
    refine ⟨hz, ((d.mem_normalizedLift_feasibleOn_iff fun h i => hg i _ h).1 hz).1, fun x hx => ?_⟩
    have hlift := (d.insertHeight_mem_normalizedLift_feasibleOn_iff fun h i => hg i _ h).2 hx
    simpa [Function.comp_apply] using hmin hlift
  · rintro ⟨hz, _, hmin⟩
    have hmaps : MapsTo project
        ((d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D)) (d.feasibleOn D) :=
      fun _ hw => ((d.mem_normalizedLift_feasibleOn_iff fun h i => hg i _ h).1 hw).1
    exact ⟨hz, hmin.comp_of_mapsTo hmaps rfl⟩

/-- Existence of an attained feasible minimum transfers in both directions under affine-argument
normalization. -/
theorem normalization_attainment_iff (d : FiniteModel n m l r) {D : Set (Point n m)}
    {a : Fin q → Fin n → ℝ} {b : Fin q → Fin m → ℝ} {offset : Fin q → ℝ}
    {phi : Fin q → ℝ → ℝ} {weight : Fin l → Fin q → ℝ}
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j *
      phi j (affineArgument (a j) (b j) (offset j) x)) :
    (∃ z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D),
      IsMinOn (d.normalizedLift a b offset phi weight).objective
        ((d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D)) z) ↔
      ∃ x ∈ d.feasibleOn D, IsMinOn d.objective (d.feasibleOn D) x := by
  constructor
  · rintro ⟨z, hz, hmin⟩
    have h := (d.normalization_minimum_iff hg z).1 ⟨hz, hmin⟩
    exact ⟨project z, h.2.1, h.2.2⟩
  · rintro ⟨x, hx, hmin⟩
    let z := insertHeight x (fun j => affineArgument (a j) (b j) (offset j) x)
    have hz : z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) :=
      (d.insertHeight_mem_normalizedLift_feasibleOn_iff fun h i => hg i _ h).2 hx
    have h := (d.normalization_minimum_iff hg z).2 ⟨hz, by simpa [z] using hx, by simpa [z]⟩
    exact ⟨z, h.1, h.2⟩

end TauCeti.ConvexLifting.FiniteModel
