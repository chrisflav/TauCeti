/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Finite mixed-integer nonlinear models and lifting coordinates

This file defines finite-dimensional mixed-integer nonlinear models with a continuous coordinate
block of length `n` and an integer-constrained coordinate block of length `m`, together with the
coordinate operations and affine-argument calculus used to construct exact lifted reformulations.

A point `x : Point n m` lies in `(Fin n → ℝ) × (Fin m → ℝ)`: both coordinate blocks are ambient
real vectors, and integrality of the second block is imposed in the mixed-integer feasible set
`FiniteModel.feasibleOn`, while `FiniteModel.relaxationOn` keeps the same nonlinear residuals,
affine rows, and box bounds with real second coordinates. Enlarging the continuous block from `n`
to `n + q` is handled by `project`, `height`, and `insertHeight`, bundled into the equivalence
`pointEquivProd`.

Affine expressions in both coordinate blocks (`affineArgument`) come with their continuous linear
derivative (`affineArgumentCLM`) and Fréchet derivative transport for univariate compositions and
weighted sums when the individual univariate derivatives are supplied.

## Main definitions

* `TauCeti.ConvexLifting.Point`: `(Fin n → ℝ) × (Fin m → ℝ)`.
* `TauCeti.ConvexLifting.project`, `TauCeti.ConvexLifting.height`,
  `TauCeti.ConvexLifting.insertHeight`, and `TauCeti.ConvexLifting.pointEquivProd`: coordinate
  maps for appending auxiliary continuous variables.
* `TauCeti.ConvexLifting.affineArgument` and `TauCeti.ConvexLifting.affineArgumentCLM`: affine
  expressions in both coordinate blocks and their continuous linear derivative.
* `TauCeti.ConvexLifting.FiniteModel`: finite nonlinear residuals, affine rows, linear objective,
  and real box bounds for the integer coordinate block.
* `TauCeti.ConvexLifting.FiniteModel.objective`, `TauCeti.ConvexLifting.FiniteModel.feasibleOn`,
  and `TauCeti.ConvexLifting.FiniteModel.relaxationOn`: objective, mixed-integer feasible set,
  and continuous relaxation.

## Main statements

* `TauCeti.ConvexLifting.hasFDerivAt_affineArgument`,
  `TauCeti.ConvexLifting.hasFDerivAt_comp_affineArgument`,
  `TauCeti.ConvexLifting.hasFDerivAt_comp_affineArgument_pi`, and
  `TauCeti.ConvexLifting.hasFDerivAt_sum_mul_comp_affineArgument`: Fréchet derivative transport
  for affine arguments and univariate compositions.
* `TauCeti.ConvexLifting.FiniteModel.objective_eq_comp_project`: zero-extension objective
  pullback.
* `TauCeti.ConvexLifting.FiniteModel.feasibleOn_subset_relaxationOn`,
  `TauCeti.ConvexLifting.FiniteModel.feasibleOn_eq_relaxationOn_inter_integral`, and
  `TauCeti.ConvexLifting.FiniteModel.feasibleOn_eq_relaxationOn_of_zero`: relations between
  mixed-integer feasibility and the continuous relaxation.

## References

* H. Hijazi, P. Bonami, and A. Ouorou, *An Outer-Inner Approximation for Separable Mixed-Integer
  Nonlinear Programs*, INFORMS Journal on Computing, Articles in Advance (2013), pp. 1–14,
  pp. 1–2 (problem formulation).
-/

public section

open Set

namespace TauCeti.ConvexLifting

/-! ### Coordinate blocks and lifting projections -/

/-- Continuous coordinates paired with real coordinates on which integrality can be imposed. -/
abbrev Point (n m : ℕ) := (Fin n → ℝ) × (Fin m → ℝ)

section Coordinates

variable {n m q : ℕ}

/-- Forget the appended `q` continuous coordinates and retain the original `n` continuous and
`m` integer-block coordinates. -/
def project (z : Point (n + q) m) : Point n m :=
  (fun i => z.1 (i.castAdd q), z.2)

/-- Read the appended `q` continuous argument or height coordinates. -/
def height (z : Point (n + q) m) : Fin q → ℝ :=
  fun j => z.1 (j.natAdd n)

/-- Append `q` continuous argument or height coordinates to the continuous block of a point. -/
def insertHeight (x : Point n m) (y : Fin q → ℝ) : Point (n + q) m :=
  (Fin.addCases x.1 y, x.2)

/-- Evaluation of the continuous block of `project z`. -/
theorem project_fst (z : Point (n + q) m) (i : Fin n) :
    (project z).1 i = z.1 (i.castAdd q) :=
  (rfl)

/-- Evaluation of the second block of `project z`. -/
@[simp]
theorem project_snd (z : Point (n + q) m) :
    (project z).2 = z.2 :=
  (rfl)

/-- Evaluation of `height z` at coordinate `j`. -/
theorem height_apply (z : Point (n + q) m) (j : Fin q) :
    height z j = z.1 (j.natAdd n) :=
  (rfl)

/-- Evaluation of `insertHeight x y` on the original continuous coordinates. -/
@[simp]
theorem insertHeight_fst_castAdd (x : Point n m) (y : Fin q → ℝ) (i : Fin n) :
    (insertHeight x y).1 (i.castAdd q) = x.1 i := by
  simp [insertHeight]

/-- Evaluation of `insertHeight x y` on the appended continuous coordinates. -/
@[simp]
theorem insertHeight_fst_natAdd (x : Point n m) (y : Fin q → ℝ) (j : Fin q) :
    (insertHeight x y).1 (j.natAdd n) = y j := by
  simp [insertHeight]

/-- Evaluation of `insertHeight x y` on the integer coordinate block. -/
@[simp]
theorem insertHeight_snd (x : Point n m) (y : Fin q → ℝ) :
    (insertHeight x y).2 = x.2 :=
  (rfl)

/-- Projecting an inserted point recovers the original point. -/
@[simp]
theorem project_insertHeight (x : Point n m) (y : Fin q → ℝ) :
    project (insertHeight x y) = x := by
  ext i
  · exact insertHeight_fst_castAdd x y i
  · rfl

/-- Reading the appended heights of an inserted point recovers the inserted vector. -/
@[simp]
theorem height_insertHeight (x : Point n m) (y : Fin q → ℝ) :
    height (insertHeight x y) = y := by
  ext j
  exact insertHeight_fst_natAdd x y j

/-- Reconstructing a point from its projection and appended heights recovers the original point. -/
@[simp]
theorem insertHeight_project_height (z : Point (n + q) m) :
    insertHeight (project z) (height z) = z := by
  ext i
  · exact Fin.addCases_castAdd_natAdd z.1 i
  · rfl

/-- Equivalence splitting an enlarged point into its original coordinates and appended heights. -/
def pointEquivProd (n m q : ℕ) : Point (n + q) m ≃ Point n m × (Fin q → ℝ) where
  toFun z := (project z, height z)
  invFun p := insertHeight p.1 p.2
  left_inv := insertHeight_project_height
  right_inv p := Prod.ext (project_insertHeight p.1 p.2) (height_insertHeight p.1 p.2)

/-- Forward evaluation of `pointEquivProd`. -/
@[simp]
theorem pointEquivProd_apply (z : Point (n + q) m) :
    pointEquivProd n m q z = (project z, height z) :=
  (rfl)

/-- Inverse evaluation of `pointEquivProd`. -/
@[simp]
theorem pointEquivProd_symm_apply (p : Point n m × (Fin q → ℝ)) :
    (pointEquivProd n m q).symm p = insertHeight p.1 p.2 :=
  (rfl)

/-- Composing `pointEquivProd` with `Prod.fst` recovers `project`. -/
@[simp]
theorem fst_comp_pointEquivProd (n m q : ℕ) :
    Prod.fst ∘ pointEquivProd n m q = (project : Point (n + q) m → Point n m) :=
  (rfl)

/-- Composing `pointEquivProd` with `Prod.snd` recovers `height`. -/
@[simp]
theorem snd_comp_pointEquivProd (n m q : ℕ) :
    Prod.snd ∘ pointEquivProd n m q = (height : Point (n + q) m → Fin q → ℝ) :=
  (rfl)

/-- Splitting a continuous-block inner product along `Fin.addCases` separates the original
coordinates from the appended heights. -/
theorem sum_addCases_mul (a : Fin n → ℝ) (w : Fin q → ℝ) (z : Point (n + q) m) :
    (∑ i : Fin (n + q), Fin.addCases a w i * z.1 i) =
      (∑ i : Fin n, a i * (project z).1 i) + ∑ j : Fin q, w j * height z j := by
  simp [Fin.sum_univ_add, project_fst, height_apply]

/-- A continuous-block row with zero coefficients on the appended block evaluates on `project z`. -/
theorem sum_addCases_zero_mul (a : Fin n → ℝ) (z : Point (n + q) m) :
    (∑ i : Fin (n + q), Fin.addCases a (fun _ => (0 : ℝ)) i * z.1 i) =
      ∑ i : Fin n, a i * (project z).1 i := by
  simp [sum_addCases_mul]

/-- A continuous-block row with zero coefficients on the original block evaluates on `height z`. -/
theorem sum_zero_addCases_mul (w : Fin q → ℝ) (z : Point (n + q) m) :
    (∑ i : Fin (n + q), Fin.addCases (fun _ => (0 : ℝ)) w i * z.1 i) =
      ∑ j : Fin q, w j * height z j := by
  simp [sum_addCases_mul]

/-- A continuous-block row placing a single coefficient `c` at appended index `j` splits into the
original sum plus `c * height z j`. -/
theorem sum_addCases_single_mul (a : Fin n → ℝ) (j : Fin q) (c : ℝ) (z : Point (n + q) m) :
    (∑ i : Fin (n + q), Fin.addCases a (Pi.single j c) i * z.1 i) =
      (∑ i : Fin n, a i * (project z).1 i) + c * height z j := by
  simp [sum_addCases_mul, Pi.single_apply]

end Coordinates

/-! ### Affine arguments and derivative transport -/

section AffineArgument

variable {n m : ℕ}

/-- An affine expression in the continuous and integer coordinate blocks. -/
def affineArgument (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ) (x : Point n m) : ℝ :=
  (∑ i, a i * x.1 i) + (∑ j, b j * x.2 j) + offset

/-- Sum-and-offset evaluation of `affineArgument`. -/
theorem affineArgument_apply (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ) (x : Point n m) :
    affineArgument a b offset x = (∑ i, a i * x.1 i) + (∑ j, b j * x.2 j) + offset :=
  (rfl)

/-- The continuous linear part of `affineArgument a b offset`. -/
noncomputable def affineArgumentCLM (a : Fin n → ℝ) (b : Fin m → ℝ) : Point n m →L[ℝ] ℝ :=
  (∑ i : Fin n, a i • (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin m → ℝ))) +
    ∑ j : Fin m, b j • (ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin m → ℝ))

/-- Evaluation of `affineArgumentCLM` as a pair of finite sums. -/
@[simp]
theorem affineArgumentCLM_apply (a : Fin n → ℝ) (b : Fin m → ℝ) (v : Point n m) :
    affineArgumentCLM a b v = (∑ i, a i * v.1 i) + ∑ j, b j * v.2 j := by
  simp [affineArgumentCLM, smul_eq_mul]

/-- `affineArgument` equals its linear part plus its scalar offset. -/
theorem affineArgument_eq_add_offset (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ)
    (x : Point n m) :
    affineArgument a b offset x = affineArgumentCLM a b x + offset := by
  simp [affineArgument_apply]

/-- The actual Fréchet derivative of `affineArgument a b offset` is `affineArgumentCLM a b`. -/
theorem hasFDerivAt_affineArgument (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ) (x : Point n m) :
    HasFDerivAt (affineArgument a b offset) (affineArgumentCLM a b) x := by
  have h : affineArgument a b offset = fun y => affineArgumentCLM a b y + offset :=
    funext (affineArgument_eq_add_offset a b offset)
  rw [h]
  exact (affineArgumentCLM a b).hasFDerivAt.add_const offset

/-- Actual Fréchet derivative transport for a univariate function composed with an affine
argument. -/
theorem hasFDerivAt_comp_affineArgument (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ)
    {φ : ℝ → ℝ} {dφ : ℝ} {x : Point n m}
    (hφ : HasDerivAt φ dφ (affineArgument a b offset x)) :
    HasFDerivAt (fun y => φ (affineArgument a b offset y)) (dφ • affineArgumentCLM a b) x :=
  hφ.comp_hasFDerivAt x (hasFDerivAt_affineArgument a b offset x)

/-- Coordinatewise Fréchet derivative transport for a family of univariate functions composed with
affine arguments, supplied with a univariate derivative for each component at its argument. -/
theorem hasFDerivAt_comp_affineArgument_pi {q : ℕ} (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ)
    (offset : Fin q → ℝ) {φ : Fin q → ℝ → ℝ} {dφ : Fin q → ℝ} {x : Point n m}
    (hφ : ∀ j, HasDerivAt (φ j) (dφ j) (affineArgument (a j) (b j) (offset j) x)) :
    HasFDerivAt (fun y j => φ j (affineArgument (a j) (b j) (offset j) y))
      (ContinuousLinearMap.pi fun j => dφ j • affineArgumentCLM (a j) (b j)) x :=
  hasFDerivAt_pi.2 fun j => hasFDerivAt_comp_affineArgument (a j) (b j) (offset j) (hφ j)

/-- Actual Fréchet derivative transport for a weighted finite sum of univariate compositions with
affine arguments, given a univariate derivative at each nonzero-weight component. -/
theorem hasFDerivAt_sum_mul_comp_affineArgument {q : ℕ} (a : Fin q → Fin n → ℝ)
    (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ) (weight : Fin q → ℝ) {φ : Fin q → ℝ → ℝ}
    {dφ : Fin q → ℝ} {x : Point n m}
    (hφ : ∀ j, weight j ≠ 0 →
      HasDerivAt (φ j) (dφ j) (affineArgument (a j) (b j) (offset j) x)) :
    HasFDerivAt (fun y => ∑ j, weight j * φ j (affineArgument (a j) (b j) (offset j) y))
      (∑ j, (weight j * dφ j) • affineArgumentCLM (a j) (b j)) x := by
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin q)),
      HasFDerivAt (fun y => weight j * φ j (affineArgument (a j) (b j) (offset j) y))
        ((weight j * dφ j) • affineArgumentCLM (a j) (b j)) x := by
    intro j _
    by_cases hw : weight j = 0
    · simp [hw, hasFDerivAt_const]
    · simpa [mul_smul] using
        (hasFDerivAt_comp_affineArgument (a j) (b j) (offset j) (hφ j hw)).const_mul (weight j)
  exact HasFDerivAt.fun_sum hterm

end AffineArgument

/-! ### Finite mixed-integer models -/

/-- Finite nonlinear residuals, affine inequality rows, a linear objective, and real box bounds
for the integer-constrained coordinate block. -/
@[ext]
structure FiniteModel (n m l r : ℕ) where
  /-- Nonlinear residual functions bounded above by zero. -/
  g : Fin l → Point n m → ℝ
  /-- Continuous-block coefficient matrix for the affine inequality rows. -/
  A : Fin r → Fin n → ℝ
  /-- Integer-block coefficient matrix for the affine inequality rows. -/
  B : Fin r → Fin m → ℝ
  /-- Right-hand side vector for the affine inequality rows. -/
  rhs : Fin r → ℝ
  /-- Linear objective coefficients on the continuous coordinate block. -/
  c1 : Fin n → ℝ
  /-- Linear objective coefficients on the integer coordinate block. -/
  c2 : Fin m → ℝ
  /-- Lower bounds on the integer-block coordinates. -/
  lo : Fin m → ℝ
  /-- Upper bounds on the integer-block coordinates. -/
  hi : Fin m → ℝ

namespace FiniteModel

variable {n m l r : ℕ}

/-- The linear objective in the continuous and integer coordinate blocks. -/
def objective (d : FiniteModel n m l r) (x : Point n m) : ℝ :=
  (∑ i, d.c1 i * x.1 i) + ∑ j, d.c2 j * x.2 j

/-- Two-sum evaluation of `FiniteModel.objective`. -/
theorem objective_apply (d : FiniteModel n m l r) (x : Point n m) :
    d.objective x = (∑ i, d.c1 i * x.1 i) + ∑ j, d.c2 j * x.2 j :=
  (rfl)

/-- Zero-extension pullback identity: appending zero continuous objective coefficients leaves the
objective equal to `d.objective ∘ project`. -/
theorem objective_eq_comp_project {q l' r' : ℕ} (d : FiniteModel n m l r)
    (d' : FiniteModel (n + q) m l' r')
    (hc1 : d'.c1 = Fin.addCases d.c1 (fun _ => 0)) (hc2 : d'.c2 = d.c2)
    (z : Point (n + q) m) :
    d'.objective z = d.objective (project z) := by
  simp [objective_apply, hc1, hc2, sum_addCases_zero_mul]

/-- Mixed-integer feasible set on a domain `D`: nonlinear residuals `≤ 0`, affine rows `≤ rhs`,
and bounded integral second coordinates. -/
def feasibleOn (d : FiniteModel n m l r) (D : Set (Point n m)) : Set (Point n m) :=
  {x | x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
    (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
    ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
      x.2 = fun j => (y j : ℝ)}

/-- Continuous relaxation on a domain `D`: the same nonlinear residuals, affine rows, and box
bounds as `feasibleOn`, with real second coordinates. -/
def relaxationOn (d : FiniteModel n m l r) (D : Set (Point n m)) : Set (Point n m) :=
  {x | x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
    (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
    ∀ j, d.lo j ≤ x.2 j ∧ x.2 j ≤ d.hi j}

/-- Definitional unfolding of `FiniteModel.feasibleOn`. -/
theorem feasibleOn_def (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.feasibleOn D =
      {x | x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
        (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
        ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
          x.2 = fun j => (y j : ℝ)} :=
  (rfl)

/-- Definitional unfolding of `FiniteModel.relaxationOn`. -/
theorem relaxationOn_def (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.relaxationOn D =
      {x | x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
        (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
        ∀ j, d.lo j ≤ x.2 j ∧ x.2 j ≤ d.hi j} :=
  (rfl)

/-- Membership criterion for `FiniteModel.feasibleOn`. -/
@[simp]
theorem mem_feasibleOn_iff (d : FiniteModel n m l r) {D : Set (Point n m)} {x : Point n m} :
    x ∈ d.feasibleOn D ↔
      x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
        (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
        ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
          x.2 = fun j => (y j : ℝ) :=
  Iff.rfl

/-- Membership criterion for `FiniteModel.relaxationOn`. -/
@[simp]
theorem mem_relaxationOn_iff (d : FiniteModel n m l r) {D : Set (Point n m)} {x : Point n m} :
    x ∈ d.relaxationOn D ↔
      x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
        (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
        ∀ j, d.lo j ≤ x.2 j ∧ x.2 j ≤ d.hi j :=
  Iff.rfl

/-- `feasibleOn` is contained in its domain `D`. -/
theorem feasibleOn_subset_domain (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.feasibleOn D ⊆ D :=
  fun _ hx => hx.1

/-- `relaxationOn` is contained in its domain `D`. -/
theorem relaxationOn_subset_domain (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.relaxationOn D ⊆ D :=
  fun _ hx => hx.1

/-- Enlarging the domain enlarges `feasibleOn`. -/
theorem feasibleOn_mono (d : FiniteModel n m l r) {D₁ D₂ : Set (Point n m)} (hD : D₁ ⊆ D₂) :
    d.feasibleOn D₁ ⊆ d.feasibleOn D₂ :=
  fun _ hx => ⟨hD hx.1, hx.2⟩

/-- Enlarging the domain enlarges `relaxationOn`. -/
theorem relaxationOn_mono (d : FiniteModel n m l r) {D₁ D₂ : Set (Point n m)} (hD : D₁ ⊆ D₂) :
    d.relaxationOn D₁ ⊆ d.relaxationOn D₂ :=
  fun _ hx => ⟨hD hx.1, hx.2⟩

/-- Every mixed-integer feasible point belongs to the continuous relaxation. -/
theorem feasibleOn_subset_relaxationOn (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.feasibleOn D ⊆ d.relaxationOn D := by
  rintro x ⟨hxD, hg, haff, y, hyb, hyx⟩
  refine ⟨hxD, hg, haff, fun j => ?_⟩
  rw [hyx]
  exact hyb j

/-- Mixed-integer feasibility is the intersection of the continuous relaxation with integrality
of the second coordinate block. -/
theorem feasibleOn_eq_relaxationOn_inter_integral (d : FiniteModel n m l r)
    (D : Set (Point n m)) :
    d.feasibleOn D = d.relaxationOn D ∩ {x | ∃ y : Fin m → ℤ, x.2 = fun j => (y j : ℝ)} := by
  ext x
  constructor
  · intro hx
    exact ⟨d.feasibleOn_subset_relaxationOn D hx, let ⟨y, _, hyx⟩ := hx.2.2.2; ⟨y, hyx⟩⟩
  · rintro ⟨⟨hxD, hg, haff, hbox⟩, y, hyx⟩
    refine ⟨hxD, hg, haff, y, fun j => ?_, hyx⟩
    simpa [hyx] using hbox j

/-- When there are no integer coordinates (`m = 0`), mixed-integer feasibility coincides with the
continuous relaxation. -/
theorem feasibleOn_eq_relaxationOn_of_zero (d : FiniteModel n 0 l r) (D : Set (Point n 0)) :
    d.feasibleOn D = d.relaxationOn D := by
  refine Subset.antisymm (d.feasibleOn_subset_relaxationOn D) ?_
  rintro x ⟨hxD, hg, haff, _⟩
  exact ⟨hxD, hg, haff, Fin.elim0, fun j => Fin.elim0 j, funext fun j => Fin.elim0 j⟩

end FiniteModel

end TauCeti.ConvexLifting
