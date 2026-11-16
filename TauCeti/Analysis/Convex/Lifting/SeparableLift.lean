/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Lifting.Basic
public import TauCeti.Analysis.Convex.Lifting.FiniteModel

/-!
# Separable-height lifting for finite mixed-integer models

When each nonlinear residual of a `FiniteModel` decomposes as a nonnegative-weight finite sum of
component functions,

    d.g i x = ∑ j, weight i j * component j x,    0 ≤ weight i j,

`FiniteModel.separableLift` appends one free continuous height variable per component, replaces
the aggregate nonlinear rows by the component inequalities
`component j (project z) - height z j ≤ 0`, and adds the affine budget rows
`∑ j, weight i j * height z j ≤ 0`. All original affine rows, integer coordinates and bounds, and
objective coefficients are retained, with zero objective coefficients on the appended heights.

Exactness of mixed-integer projection, continuous-relaxation projection, feasible minima, and
minimum attainment is derived by identifying the lifted feasible sets (through `pointEquivProd`)
with `TauCeti.ConvexLifting.liftedSet` and invoking the order-level exact projection theory in
`TauCeti.Analysis.Convex.Lifting.Basic`.

## Main definitions

* `TauCeti.ConvexLifting.FiniteModel.separableLift`: separable-height extended formulation of a
  finite mixed-integer model.

## Main statements

* `TauCeti.ConvexLifting.FiniteModel.separableLift_affine_iff`: characterization of the affine
  rows of `separableLift`.
* `TauCeti.ConvexLifting.FiniteModel.separable_projection`: exact projection of mixed-integer
  feasible points under nonnegative weights.
* `TauCeti.ConvexLifting.FiniteModel.separable_relaxation_projection`: exact projection of the
  continuous relaxation under nonnegative weights.
* `TauCeti.ConvexLifting.FiniteModel.separable_minimum_iff` and
  `TauCeti.ConvexLifting.FiniteModel.separable_attainment_iff`: transfer of feasible minima and
  their attainment under nonnegative weights.

## References

* H. Hijazi, P. Bonami, and A. Ouorou, *An Outer-Inner Approximation for Separable Mixed-Integer
  Nonlinear Programs*, INFORMS Journal on Computing, Articles in Advance (2013), pp. 1–14,
  §3.1, p. 4 (separable extended formulation).
-/

public section

open Set

namespace TauCeti.ConvexLifting.FiniteModel

variable {n m l r q : ℕ}

/-- Separable-height lifting: introduce one continuous height variable per component with
nonlinear epigraph residuals `component j (project z) - height z j ≤ 0` and affine budget rows
`∑ j, weight i j * height z j ≤ 0`. Original affine rows, integer bounds, and objective are
retained, with zero objective coefficients on the appended heights. -/
def separableLift (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    FiniteModel (n + q) m q (r + l) where
  g := fun j z => component j (project z) - height z j
  A := Fin.addCases (fun i => Fin.addCases (d.A i) (fun _ => 0))
    (fun i => Fin.addCases (fun _ => 0) (weight i))
  B := Fin.addCases d.B (fun _ _ => 0)
  rhs := Fin.addCases d.rhs (fun _ => 0)
  c1 := Fin.addCases d.c1 (fun _ => 0)
  c2 := d.c2
  lo := d.lo
  hi := d.hi

/-- Nonlinear residual evaluation of `separableLift`. -/
@[simp]
theorem separableLift_g (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)
    (j : Fin q) (z : Point (n + q) m) :
    (d.separableLift component weight).g j z = component j (project z) - height z j :=
  (rfl)

/-- Continuous-block affine matrix of `separableLift`. -/
@[simp]
theorem separableLift_A (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).A =
      Fin.addCases (fun i => Fin.addCases (d.A i) (fun _ => 0))
        (fun i => Fin.addCases (fun _ => 0) (weight i)) :=
  (rfl)

/-- Integer-block affine matrix of `separableLift`. -/
@[simp]
theorem separableLift_B (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).B = Fin.addCases d.B (fun _ _ => 0) :=
  (rfl)

/-- Right-hand side vector of `separableLift`. -/
@[simp]
theorem separableLift_rhs (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).rhs = Fin.addCases d.rhs (fun _ => 0) :=
  (rfl)

/-- Continuous-block objective coefficients of `separableLift`. -/
@[simp]
theorem separableLift_c1 (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).c1 = Fin.addCases d.c1 (fun _ => 0) :=
  (rfl)

/-- Integer-block objective coefficients of `separableLift`. -/
@[simp]
theorem separableLift_c2 (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).c2 = d.c2 :=
  (rfl)

/-- Lower bounds of `separableLift`. -/
@[simp]
theorem separableLift_lo (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).lo = d.lo :=
  (rfl)

/-- Upper bounds of `separableLift`. -/
@[simp]
theorem separableLift_hi (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).hi = d.hi :=
  (rfl)

/-- The objective of `separableLift` is the pullback of the original objective along `project`. -/
@[simp]
theorem separableLift_objective (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) (z : Point (n + q) m) :
    (d.separableLift component weight).objective z = d.objective (project z) :=
  d.objective_eq_comp_project (d.separableLift component weight) rfl rfl z

/-- The affine rows of `separableLift` split into the original affine rows on `project z` and
the weighted height budget inequalities `∑ j, weight i j * height z j ≤ 0`. -/
theorem separableLift_affine_iff (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) (z : Point (n + q) m) :
    (∀ k, (∑ i, (d.separableLift component weight).A k i * z.1 i) +
        (∑ j, (d.separableLift component weight).B k j * z.2 j) ≤
          (d.separableLift component weight).rhs k) ↔
      (∀ k, (∑ i, d.A k i * (project z).1 i) + (∑ j, d.B k j * (project z).2 j) ≤ d.rhs k) ∧
        ∀ i, (∑ j, weight i j * height z j) ≤ 0 := by
  rw [Fin.forall_fin_add]
  simp [sum_addCases_zero_mul, sum_zero_addCases_mul]

/-- Mixed-integer membership characterization for `separableLift`: domain, component-height
inequalities, original affine rows, weighted budget rows, and bounded integer coordinates. -/
theorem mem_separableLift_feasibleOn_iff (d : FiniteModel n m l r) {D : Set (Point n m)}
    {component : Fin q → Point n m → ℝ} {weight : Fin l → Fin q → ℝ} {z : Point (n + q) m} :
    z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D) ↔
      project z ∈ D ∧
        (∀ j, component j (project z) ≤ height z j) ∧
        (∀ k, (∑ i, d.A k i * (project z).1 i) + (∑ j, d.B k j * (project z).2 j) ≤ d.rhs k) ∧
        (∀ i, (∑ j, weight i j * height z j) ≤ 0) ∧
        ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
          (project z).2 = fun j => (y j : ℝ) := by
  simp only [mem_feasibleOn_iff, mem_preimage, separableLift_g, sub_nonpos, separableLift_lo,
    separableLift_hi, separableLift_affine_iff, project_snd]
  tauto

/-- Continuous-relaxation membership characterization for `separableLift`. -/
theorem mem_separableLift_relaxationOn_iff (d : FiniteModel n m l r) {D : Set (Point n m)}
    {component : Fin q → Point n m → ℝ} {weight : Fin l → Fin q → ℝ} {z : Point (n + q) m} :
    z ∈ (d.separableLift component weight).relaxationOn (project ⁻¹' D) ↔
      project z ∈ D ∧
        (∀ j, component j (project z) ≤ height z j) ∧
        (∀ k, (∑ i, d.A k i * (project z).1 i) + (∑ j, d.B k j * (project z).2 j) ≤ d.rhs k) ∧
        (∀ i, (∑ j, weight i j * height z j) ≤ 0) ∧
        ∀ j, d.lo j ≤ (project z).2 j ∧ (project z).2 j ≤ d.hi j := by
  simp only [mem_relaxationOn_iff, mem_preimage, separableLift_g, sub_nonpos, separableLift_lo,
    separableLift_hi, separableLift_affine_iff, project_snd]
  tauto

/-- Inserting the actual component values lifts any mixed-integer feasible point into
`separableLift`. No weight nonnegativity is required for this graph witness. -/
theorem insertHeight_component_mem_separableLift_feasibleOn (d : FiniteModel n m l r)
    {D : Set (Point n m)} {component : Fin q → Point n m → ℝ} {weight : Fin l → Fin q → ℝ}
    {x : Point n m} (hg : ∀ i, d.g i x = ∑ j, weight i j * component j x)
    (hx : x ∈ d.feasibleOn D) :
    insertHeight x (fun j => component j x) ∈
      (d.separableLift component weight).feasibleOn (project ⁻¹' D) := by
  rw [d.mem_separableLift_feasibleOn_iff]
  rcases d.mem_feasibleOn_iff.1 hx with ⟨hxD, hgx, haff, hint⟩
  refine ⟨by simpa using hxD, fun j => by simp, by simpa using haff, fun i => ?_,
    by simpa using hint⟩
  simpa [← hg i] using hgx i

/-- Inserting the actual component values lifts any relaxation-feasible point into
`separableLift`. No weight nonnegativity is required for this graph witness. -/
theorem insertHeight_component_mem_separableLift_relaxationOn (d : FiniteModel n m l r)
    {D : Set (Point n m)} {component : Fin q → Point n m → ℝ} {weight : Fin l → Fin q → ℝ}
    {x : Point n m} (hg : ∀ i, d.g i x = ∑ j, weight i j * component j x)
    (hx : x ∈ d.relaxationOn D) :
    insertHeight x (fun j => component j x) ∈
      (d.separableLift component weight).relaxationOn (project ⁻¹' D) := by
  rw [d.mem_separableLift_relaxationOn_iff]
  rcases d.mem_relaxationOn_iff.1 hx with ⟨hxD, hgx, haff, hbox⟩
  refine ⟨by simpa using hxD, fun j => by simp, by simpa using haff, fun i => ?_,
    by simpa using hbox⟩
  simpa [← hg i] using hgx i

/-- Base linear and integrality domain for reducing `separableLift` to `originalSet`/`liftedSet`. -/
private def linearFeasibleBase (d : FiniteModel n m l r) (D : Set (Point n m)) :
    Set (Point n m) :=
  {x | x ∈ D ∧
    (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
    ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
      x.2 = fun j => (y j : ℝ)}

/-- Base linear and box-bound domain for reducing the continuous relaxation of `separableLift`. -/
private def linearRelaxationBase (d : FiniteModel n m l r) (D : Set (Point n m)) :
    Set (Point n m) :=
  {x | x ∈ D ∧
    (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
    ∀ j, d.lo j ≤ x.2 j ∧ x.2 j ≤ d.hi j}

private theorem feasibleOn_eq_originalSet (d : FiniteModel n m l r) {D : Set (Point n m)}
    {component : Fin q → Point n m → ℝ} {weight : Fin l → Fin q → ℝ}
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) :
    d.feasibleOn D =
      originalSet (d.linearFeasibleBase D) (fun x j => component j x)
        (fun y i => ∑ j, weight i j * y j) 0 := by
  ext x
  simp only [mem_feasibleOn_iff, mem_originalSet_iff, linearFeasibleBase, mem_ofPred_eq,
    Pi.le_def, Pi.zero_apply]
  constructor
  · rintro ⟨hxD, hgx, haff, hint⟩
    exact ⟨⟨hxD, haff, hint⟩, fun i => by simpa [← hg i x hxD] using hgx i⟩
  · rintro ⟨⟨hxD, haff, hint⟩, hsum⟩
    exact ⟨hxD, fun i => by simpa [hg i x hxD] using hsum i, haff, hint⟩

private theorem relaxationOn_eq_originalSet (d : FiniteModel n m l r) {D : Set (Point n m)}
    {component : Fin q → Point n m → ℝ} {weight : Fin l → Fin q → ℝ}
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) :
    d.relaxationOn D =
      originalSet (d.linearRelaxationBase D) (fun x j => component j x)
        (fun y i => ∑ j, weight i j * y j) 0 := by
  ext x
  simp only [mem_relaxationOn_iff, mem_originalSet_iff, linearRelaxationBase, mem_ofPred_eq,
    Pi.le_def, Pi.zero_apply]
  constructor
  · rintro ⟨hxD, hgx, haff, hbox⟩
    exact ⟨⟨hxD, haff, hbox⟩, fun i => by simpa [← hg i x hxD] using hgx i⟩
  · rintro ⟨⟨hxD, haff, hbox⟩, hsum⟩
    exact ⟨hxD, fun i => by simpa [hg i x hxD] using hsum i, haff, hbox⟩

private theorem separableLift_feasibleOn_eq_preimage_liftedSet (d : FiniteModel n m l r)
    (D : Set (Point n m)) (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).feasibleOn (project ⁻¹' D) =
      pointEquivProd n m q ⁻¹'
        liftedSet (d.linearFeasibleBase D) Set.univ (fun x j => component j x)
          (fun y i => ∑ j, weight i j * y j) 0 := by
  ext z
  simp only [mem_separableLift_feasibleOn_iff, mem_preimage, pointEquivProd_apply,
    mem_liftedSet_iff, linearFeasibleBase, mem_ofPred_eq, mem_univ, true_and, Pi.le_def,
    Pi.zero_apply]
  tauto

private theorem separableLift_relaxationOn_eq_preimage_liftedSet (d : FiniteModel n m l r)
    (D : Set (Point n m)) (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).relaxationOn (project ⁻¹' D) =
      pointEquivProd n m q ⁻¹'
        liftedSet (d.linearRelaxationBase D) Set.univ (fun x j => component j x)
          (fun y i => ∑ j, weight i j * y j) 0 := by
  ext z
  simp only [mem_separableLift_relaxationOn_iff, mem_preimage, pointEquivProd_apply,
    mem_liftedSet_iff, linearRelaxationBase, mem_ofPred_eq, mem_univ, true_and, Pi.le_def,
    Pi.zero_apply]
  tauto

/-- Mixed-integer feasible points of `separableLift` project exactly onto the original feasible
set under nonnegative weights. -/
theorem separable_projection (d : FiniteModel n m l r) {D : Set (Point n m)}
    {component : Fin q → Point n m → ℝ} {weight : Fin l → Fin q → ℝ}
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) :
    project '' (d.separableLift component weight).feasibleOn (project ⁻¹' D) =
      d.feasibleOn D := by
  rw [d.separableLift_feasibleOn_eq_preimage_liftedSet D component weight,
    d.feasibleOn_eq_originalSet hg, ← fst_comp_pointEquivProd n m q, image_comp,
    (pointEquivProd n m q).image_preimage]
  exact projection_eq (mapsTo_univ _ _) fun _ _ _ _ hy i =>
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy j) (hw i j)

/-- The continuous relaxation of `separableLift` projects exactly onto the original continuous
relaxation under nonnegative weights. -/
theorem separable_relaxation_projection (d : FiniteModel n m l r) {D : Set (Point n m)}
    {component : Fin q → Point n m → ℝ} {weight : Fin l → Fin q → ℝ}
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) :
    project '' (d.separableLift component weight).relaxationOn (project ⁻¹' D) =
      d.relaxationOn D := by
  rw [d.separableLift_relaxationOn_eq_preimage_liftedSet D component weight,
    d.relaxationOn_eq_originalSet hg, ← fst_comp_pointEquivProd n m q, image_comp,
    (pointEquivProd n m q).image_preimage]
  exact projection_eq (mapsTo_univ _ _) fun _ _ _ _ hy i =>
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy j) (hw i j)

/-- Heights carry zero objective coefficients and preserve feasible minima under nonnegative
weights. -/
theorem separable_minimum_iff (d : FiniteModel n m l r) {D : Set (Point n m)}
    {component : Fin q → Point n m → ℝ} {weight : Fin l → Fin q → ℝ}
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) (z : Point (n + q) m) :
    (z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D) ∧
      IsMinOn (d.separableLift component weight).objective
        ((d.separableLift component weight).feasibleOn (project ⁻¹' D)) z) ↔
      z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D) ∧
        project z ∈ d.feasibleOn D ∧ IsMinOn d.objective (d.feasibleOn D) (project z) := by
  let L := liftedSet (d.linearFeasibleBase D) Set.univ (fun x j => component j x)
    (fun y i => ∑ j, weight i j * y j) 0
  have hobj : (d.separableLift component weight).objective =
      (d.objective ∘ Prod.fst) ∘ pointEquivProd n m q :=
    funext fun w => by simp [d.separableLift_objective]
  have hL : (d.separableLift component weight).feasibleOn (project ⁻¹' D) =
      pointEquivProd n m q ⁻¹' L :=
    d.separableLift_feasibleOn_eq_preimage_liftedSet D component weight
  have hS := d.feasibleOn_eq_originalSet hg
  have hmin : IsMinOn ((d.objective ∘ Prod.fst) ∘ pointEquivProd n m q)
      (pointEquivProd n m q ⁻¹' L) z ↔
      IsMinOn (d.objective ∘ Prod.fst) L (pointEquivProd n m q z) := by
    refine ⟨fun h p hp => ?_, fun h => h.preimage (pointEquivProd n m q)⟩
    have hmem : (pointEquivProd n m q).symm p ∈ pointEquivProd n m q ⁻¹' L := by simpa using hp
    simpa [Function.comp_apply] using h hmem
  have hmono : MonotoneOn (fun (y : Fin q → ℝ) (i : Fin l) => ∑ j, weight i j * y j) Set.univ :=
    fun _ _ _ _ hy i => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy j) (hw i j)
  have hfst : (pointEquivProd n m q z).1 = project z := by simp
  rw [hobj, hL, hS, hmin, ← hfst]
  exact feasible_minimum_iff (mapsTo_univ _ _) hmono d.objective (pointEquivProd n m q z)

/-- Existence of an attained feasible minimum transfers in both directions under nonnegative-weight
separable-height lifting. -/
theorem separable_attainment_iff (d : FiniteModel n m l r) {D : Set (Point n m)}
    {component : Fin q → Point n m → ℝ} {weight : Fin l → Fin q → ℝ}
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) :
    (∃ z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D),
      IsMinOn (d.separableLift component weight).objective
        ((d.separableLift component weight).feasibleOn (project ⁻¹' D)) z) ↔
      ∃ x ∈ d.feasibleOn D, IsMinOn d.objective (d.feasibleOn D) x := by
  constructor
  · rintro ⟨z, hz, hmin⟩
    have h := (d.separable_minimum_iff hw hg z).1 ⟨hz, hmin⟩
    exact ⟨project z, h.2.1, h.2.2⟩
  · rintro ⟨x, hx, hmin⟩
    let z := insertHeight x (fun j => component j x)
    have hz : z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D) :=
      d.insertHeight_component_mem_separableLift_feasibleOn
        (fun i => hg i x (d.feasibleOn_subset_domain D hx)) hx
    have h := (d.separable_minimum_iff hw hg z).2 ⟨hz, by simpa [z] using hx, by simpa [z]⟩
    exact ⟨z, h.1, h.2⟩

end TauCeti.ConvexLifting.FiniteModel
