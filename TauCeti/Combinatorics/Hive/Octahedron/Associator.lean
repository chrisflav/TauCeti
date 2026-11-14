/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Octahedron.Excavation
public import TauCeti.Combinatorics.Hive.Octahedron.PiecewiseAffine
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Face gluing, associator restriction, and boundary preservation

This file specializes the bounded modified octahedron recurrence to the associator region
`A_n = {|x - y| ≤ t ≤ n - |n - x - y|}` bounded by `S = lowerSection n` and `S' = upperSection n`.

## Face gluing and boundary formulas

* Two input lattice functions `f₁, f₂ : Vertex n → R` sharing values along `f₁`'s `A → C` side and
  `f₂`'s `A → B` side glue via `glueLower` onto `S = lowerSection n`; `readLeftFst` and
  `readLeftSnd` recover `(f₁, f₂)` with no cross-diagonal rhombus condition. When `h₁, h₂` are
  normalized integer hives of boundaries `(λ, μ, σ*)` and `(σ, ν, π*)`, their shared-edge partial
  sums coincide (`sharedLowerDiag_eq_of_productBoundary`).
* On `S' = upperSection n`, `readRightFst` pulls back along `(x, y, z) ↦ (n - z, n - x, n - y)` and
  subtracts the `(n, 0)` wall value (`|λ|`) to normalize its `A`-corner, while `readRightSnd` pulls
  back along `(x, y, z) ↦ (y, z, n - x)` without a constant shift. Conversely, `glueUpper g₁ g₂`
  adds `g₂ (0, n, 0) = |λ|` back to `g₁` before gluing across `x + y = n`.

## Associator restriction and explicit checks

* Every point of `A_n` strictly above `S` (or strictly below `S'`) is strictly interior to
  `[0, n]²`, and all five past/future recurrence dependencies—hence the entire recursive dependency
  closure `depClosure`—remain inside `A_n`.
* Defining `associatorSectionEquiv n : SectionState n R ≃ SectionState n R` for all `n : ℕ` (the
  identity for `n = 0` and `sectionTransition` from `S` to `S'` for `1 ≤ n`), every legal
  excavation schedule from `S` to `S'` evaluates to `associatorSectionEquiv n`, wall values are
  fixed, and the four exterior boundary sides `(λ, μ, ν, π*)` are preserved, yielding output
  boundaries `(μ, ν, τ*)` and `(λ, τ, π*)`.
* Explicit checks verify `max` vs `min` involutivity and demonstrate at `n = 2` that replacing `max`
  by `min` violates rhombus concavity on `S'`, verify `y = 0` wall edge-difference propagation, and
  summarize the `n = 0` one-point hive identity.

## References

* A. Henriques and J. Kamnitzer, *Crystals and coboundary categories*, Adv. Math. **206** (2006),
  §3.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §5.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### Normalized face readout, gluing across shared diagonals, and boundary formulas -/

section Gluing

variable {n : ℕ} {R : Type*}

/-- Read the first input face from a lower-section state via `(x, y, z) ↦ (n - x, z)`. -/
def readLeftFst (F : SectionState n R) (p : Vertex n) : R :=
  F ⟨n - p.x, by omega⟩ ⟨p.z, by have := p.sum_eq; omega⟩

theorem readLeftFst_apply (F : SectionState n R) (p : Vertex n) :
    readLeftFst F p = F ⟨n - p.x, by omega⟩ ⟨p.z, by have := p.sum_eq; omega⟩ := (rfl)

/-- Read the second input face from a lower-section state via `(x, y, z) ↦ (y, n - x)`. -/
def readLeftSnd (F : SectionState n R) (p : Vertex n) : R :=
  F ⟨p.y, by have := p.sum_eq; omega⟩ ⟨n - p.x, by omega⟩

theorem readLeftSnd_apply (F : SectionState n R) (p : Vertex n) :
    readLeftSnd F p = F ⟨p.y, by have := p.sum_eq; omega⟩ ⟨n - p.x, by omega⟩ := (rfl)

/-- Glue two input faces onto `S = lowerSection n`: use `f₁` on `{y ≤ x}` and `f₂` on `{x < y}`. -/
def glueLower (f₁ f₂ : Vertex n → R) : SectionState n R :=
  fun x y =>
    if h : y.val ≤ x.val then
      f₁ ⟨n - x.val, x.val - y.val, y.val, by have := x.isLt; omega⟩
    else
      f₂ ⟨n - y.val, x.val, y.val - x.val, by have := y.isLt; omega⟩

theorem glueLower_apply (f₁ f₂ : Vertex n → R) (x y : Fin (n + 1)) :
    glueLower f₁ f₂ x y =
      if h : y.val ≤ x.val then
        f₁ ⟨n - x.val, x.val - y.val, y.val, by have := x.isLt; omega⟩
      else
        f₂ ⟨n - y.val, x.val, y.val - x.val, by have := y.isLt; omega⟩ := (rfl)

@[simp] theorem readLeftFst_glueLower (f₁ f₂ : Vertex n → R) :
    readLeftFst (glueLower f₁ f₂) = f₁ := by
  ext p
  have hp := p.sum_eq
  have hle : p.z ≤ n - p.x := by omega
  simp only [readLeftFst, glueLower, hle, ↓reduceDIte]
  congr 1; ext <;> dsimp <;> omega

theorem readLeftSnd_glueLower {f₁ f₂ : Vertex n → R}
    (hdiag : ∀ k : Fin (n + 1),
      f₁ (Vertex.edgePoint n 2 ⟨n - k.val, by omega⟩) = f₂ (Vertex.edgePoint n 0 k)) :
    readLeftSnd (glueLower f₁ f₂) = f₂ := by
  ext p
  have hp := p.sum_eq
  simp only [readLeftSnd, glueLower]
  by_cases hle : n - p.x ≤ p.y
  · simp only [hle, ↓reduceDIte]
    have hpy : p.y = n - p.x := by omega
    have hpz : p.z = 0 := by omega
    have heq := hdiag ⟨p.y, by omega⟩
    have hv₁ : (⟨n - p.y, 0, n - (n - p.y), by omega⟩ : Vertex n) =
        Vertex.edgePoint n 2 ⟨n - p.y, by omega⟩ := by ext <;> simp
    have hv₂ : p = Vertex.edgePoint n 0 ⟨p.y, by omega⟩ := by
      ext <;> simp [hpy, hpz]; omega
    rw [show (⟨n - p.y, p.y - (n - p.x), n - p.x, by omega⟩ : Vertex n) =
      ⟨n - p.y, 0, n - (n - p.y), by omega⟩ by ext <;> dsimp <;> omega, hv₁, heq, ← hv₂]
  · simp only [hle, ↓reduceDIte]
    congr 1; ext <;> dsimp <;> omega

@[simp] theorem glueLower_readLeft (F : SectionState n R) :
    glueLower (readLeftFst F) (readLeftSnd F) = F := by
  ext x y
  have := x.isLt; have := y.isLt
  simp only [glueLower, readLeftFst, readLeftSnd]
  split_ifs with hle
  · exact congrArg₂ F (by ext; dsimp; omega) (by ext; dsimp)
  · exact congrArg₂ F (by ext; dsimp) (by ext; dsimp; omega)

/-- Gluing two functions on `S` recovers two rhombus-concave faces if and only if each face is
individually rhombus-concave; there are no extra rhombus inequalities across `x = y`. -/
theorem isRhombusConcave_readLeft_glueLower_iff [AddCommGroup R] [Preorder R]
    {f₁ f₂ : Vertex n → R}
    (hdiag : ∀ k : Fin (n + 1),
      f₁ (Vertex.edgePoint n 2 ⟨n - k.val, by omega⟩) = f₂ (Vertex.edgePoint n 0 k)) :
    (IsRhombusConcave (readLeftFst (glueLower f₁ f₂)) ∧
      IsRhombusConcave (readLeftSnd (glueLower f₁ f₂))) ↔
      IsRhombusConcave f₁ ∧ IsRhombusConcave f₂ := by
  rw [readLeftFst_glueLower, readLeftSnd_glueLower hdiag]

/-- Read the `(μ, ν, τ*)` output face from an upper-section state via
`(x, y, z) ↦ (n - z, n - x)`, subtracting `F (Fin.last n) 0` (`|λ|`) to normalize its `A`-corner.
-/
def readRightFst [AddCommGroup R] (F : SectionState n R) (p : Vertex n) : R :=
  F ⟨n - p.z, by omega⟩ ⟨n - p.x, by omega⟩ - F (Fin.last n) 0

theorem readRightFst_apply [AddCommGroup R] (F : SectionState n R) (p : Vertex n) :
    readRightFst F p = F ⟨n - p.z, by omega⟩ ⟨n - p.x, by omega⟩ - F (Fin.last n) 0 := (rfl)

/-- Read the `(λ, τ, π*)` output face from an upper-section state via `(x, y, z) ↦ (y, z)` without
a constant shift. -/
def readRightSnd (F : SectionState n R) (p : Vertex n) : R :=
  F ⟨p.y, by have := p.sum_eq; omega⟩ ⟨p.z, by have := p.sum_eq; omega⟩

theorem readRightSnd_apply (F : SectionState n R) (p : Vertex n) :
    readRightSnd F p = F ⟨p.y, by have := p.sum_eq; omega⟩ ⟨p.z, by have := p.sum_eq; omega⟩ :=
  (rfl)

@[simp] theorem readRightFst_cornerA [AddCommGroup R] (F : SectionState n R) :
    readRightFst F (Vertex.cornerA n) = 0 := by
  simp only [readRightFst, Vertex.cornerA_x, Vertex.cornerA_z, Nat.sub_zero, Nat.sub_self]
  exact sub_self _

@[simp] theorem readRightSnd_cornerA (F : SectionState n R) :
    readRightSnd F (Vertex.cornerA n) = F 0 0 := by
  simp only [readRightSnd, Vertex.cornerA_y, Vertex.cornerA_z]
  rfl

/-- Glue two output faces onto `S' = upperSection n`, adding `g₂ (0, n, 0)` (`|λ|`) back to `g₁`
on `{n < x + y}` and using `g₂` on `{x + y ≤ n}`. -/
def glueUpper [Add R] (g₁ g₂ : Vertex n → R) : SectionState n R :=
  fun x y =>
    if h : x.val + y.val ≤ n then
      g₂ ⟨n - x.val - y.val, x.val, y.val, by omega⟩
    else
      g₁ ⟨n - y.val, x.val + y.val - n, n - x.val, by have := x.isLt; have := y.isLt; omega⟩ +
        g₂ (Vertex.edgePoint n 0 (Fin.last n))

theorem glueUpper_apply [Add R] (g₁ g₂ : Vertex n → R) (x y : Fin (n + 1)) :
    glueUpper g₁ g₂ x y =
      if h : x.val + y.val ≤ n then
        g₂ ⟨n - x.val - y.val, x.val, y.val, by omega⟩
      else
        g₁ ⟨n - y.val, x.val + y.val - n, n - x.val, by have := x.isLt; have := y.isLt; omega⟩ +
          g₂ (Vertex.edgePoint n 0 (Fin.last n)) := (rfl)

@[simp] theorem readRightSnd_glueUpper [Add R] (g₁ g₂ : Vertex n → R) :
    readRightSnd (glueUpper g₁ g₂) = g₂ := by
  ext p
  have hp := p.sum_eq
  have hle : p.y + p.z ≤ n := by omega
  simp only [readRightSnd, glueUpper, hle, ↓reduceDIte]
  congr 1; ext <;> dsimp; omega

theorem readRightFst_glueUpper [AddCommGroup R] {g₁ g₂ : Vertex n → R}
    (hdiag : ∀ k : Fin (n + 1),
      g₁ (Vertex.edgePoint n 2 k) + g₂ (Vertex.edgePoint n 0 (Fin.last n)) =
        g₂ (Vertex.edgePoint n 1 ⟨n - k.val, by omega⟩)) :
    readRightFst (glueUpper g₁ g₂) = g₁ := by
  ext p
  have hp := p.sum_eq
  have hlast : glueUpper g₁ g₂ (Fin.last n) 0 = g₂ (Vertex.edgePoint n 0 (Fin.last n)) := by
    have hle : (Fin.last n).val + (0 : Fin (n + 1)).val ≤ n := by simp
    simp only [glueUpper, hle, ↓reduceDIte]
    congr 1; ext <;> simp
  rw [readRightFst, hlast]
  simp only [glueUpper]
  by_cases hle : (n - p.z) + (n - p.x) ≤ n
  · simp only [hle, ↓reduceDIte]
    have hpy : p.y = 0 := by omega
    have hpz : p.z = n - p.x := by omega
    have heq := hdiag ⟨p.x, by omega⟩
    have hv₂ : (⟨n - (n - p.z) - (n - p.x), n - p.z, n - p.x, by omega⟩ : Vertex n) =
        Vertex.edgePoint n 1 ⟨n - p.x, by omega⟩ := by ext <;> simp [hpz]
    have hv₁ : p = Vertex.edgePoint n 2 ⟨p.x, by omega⟩ := by
      ext <;> simp [hpy, hpz]
    rw [hv₂, ← heq, ← hv₁, add_sub_cancel_right]
  · simp only [hle, ↓reduceDIte, add_sub_cancel_right]
    congr 1; ext <;> dsimp <;> omega

@[simp] theorem glueUpper_readRight [AddCommGroup R] (F : SectionState n R) :
    glueUpper (readRightFst F) (readRightSnd F) = F := by
  ext x y
  have := x.isLt; have := y.isLt
  simp only [glueUpper, readRightFst, readRightSnd]
  have hlast : F ⟨(Vertex.edgePoint n 0 (Fin.last n)).y, by simp⟩
      ⟨(Vertex.edgePoint n 0 (Fin.last n)).z, by simp⟩ = F (Fin.last n) 0 := by
    refine congrArg₂ F ?_ ?_ <;> (ext; simp)
  split_ifs with hle
  · rfl
  · rw [hlast, sub_add_cancel]
    refine congrArg₂ F ?_ ?_ <;> (ext; dsimp; omega)

/-- If `h₁` has boundary `(λ, μ, σ*)` and `h₂` has boundary `(σ, ν, π*)`, then `h₁` along `A → C`
and `h₂` along `A → B` take identical dominant-weight partial-sum values (with `0` at `A`). -/
theorem sharedLowerDiag_eq_of_productBoundary {lam μ σ ν pi : DominantWeight n}
    {h₁ h₂ : IntegerHive n}
    (hb₁ : h₁.boundary = productBoundary lam μ σ)
    (hb₂ : h₂.boundary = productBoundary σ ν pi) (k : Fin (n + 1)) :
    h₁ (Vertex.edgePoint n 2 ⟨n - k.val, by omega⟩) = h₂ (Vertex.edgePoint n 0 k) := by
  rw [h₁.apply_edgePoint_two, h₂.apply_edgePoint_zero, hb₁, hb₂]
  simp only [productBoundary_two, productBoundary_zero, DominantWeight.dual_apply,
    Finset.sum_neg_distrib, neg_neg, Finset.sum_filter]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have := i.isLt; have := k.isLt
  split_ifs <;> omega

/-- If `g₁` has boundary `(μ, ν, τ*)` and `g₂` has boundary `(λ, τ, π*)`, then `g₁ + |λ|` along
`C → A` agrees with `g₂` along `B → C` at every vertex of the shared upper diagonal `x + y = n`. -/
theorem sharedUpperDiag_eq_of_productBoundary {lam μ ν τ pi : DominantWeight n}
    {g₁ g₂ : IntegerHive n}
    (hb₁ : g₁.boundary = productBoundary μ ν τ)
    (hb₂ : g₂.boundary = productBoundary lam τ pi) (k : Fin (n + 1)) :
    g₁ (Vertex.edgePoint n 2 k) + g₂ (Vertex.edgePoint n 0 (Fin.last n)) =
      g₂ (Vertex.edgePoint n 1 ⟨n - k.val, by omega⟩) := by
  have hlast : g₂ (Vertex.edgePoint n 0 (Fin.last n)) = ∑ i : Fin n, lam.1 i := by
    rw [g₂.apply_edgePoint_zero, hb₂, productBoundary_zero]
    have hall : ({i : Fin n | i.val < (Fin.last n).val} : Finset (Fin n)) = Finset.univ := by
      ext i; simp
    rw [hall]
  rw [hlast, g₁.apply_edgePoint_two, g₂.apply_edgePoint_one, hb₁, hb₂]
  simp only [productBoundary_two, productBoundary_zero, productBoundary_one,
    DominantWeight.dual_apply, Finset.sum_neg_distrib, neg_neg, Finset.sum_filter]
  rw [add_comm]
  congr 1
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have := i.isLt; have := k.isLt
  split_ifs <;> omega

/-- Edge-difference sequence along the shared upper diagonal `(n - i, i) → (n - (i + 1), i + 1)`.
-/
def upperDiagDiff [AddCommGroup R] (F : SectionState n R) (i : Fin n) : R :=
  F ⟨n - (i.val + 1), by omega⟩ i.succ - F ⟨n - i.val, by omega⟩ i.castSucc

theorem upperDiagDiff_apply [AddCommGroup R] (F : SectionState n R) (i : Fin n) :
    upperDiagDiff F i =
      F ⟨n - (i.val + 1), by omega⟩ i.succ - F ⟨n - i.val, by omega⟩ i.castSucc := (rfl)

/-- Boundary of `readRightFst F` in terms of the `x = n` wall, `y = n` wall, and shared diagonal. -/
theorem boundaryLinear_readRightFst [AddCommGroup R] (F : SectionState n R) :
    boundaryLinear ℤ n R (readRightFst F) =
      ![fun i => F (Fin.last n) i.succ - F (Fin.last n) i.castSucc,
        fun i => F ⟨n - (i.val + 1), by omega⟩ (Fin.last n) - F ⟨n - i.val, by omega⟩ (Fin.last n),
        fun i => -upperDiagDiff F i.rev] := by
  ext s i
  rw [boundaryLinear_apply]
  fin_cases s <;> dsimp only
  · simp only [readRightFst, sub_sub_sub_cancel_right]
    congr 1 <;> exact congrArg₂ F (by ext; simp) (by ext; simp; omega)
  · simp only [readRightFst, sub_sub_sub_cancel_right]
    congr 1 <;> (refine congrArg₂ F ?_ ?_ <;> (ext; simp))
  · simp only [readRightFst, upperDiagDiff, sub_sub_sub_cancel_right, neg_sub]
    congr 1
    · refine congrArg₂ F ?_ ?_ <;> (ext; simp [Fin.val_rev])
    · refine congrArg₂ F ?_ ?_ <;> (ext; simp [Fin.val_rev]; omega)

/-- Boundary of `readRightSnd F` in terms of the `y = 0` wall, shared diagonal, and `x = 0` wall. -/
theorem boundaryLinear_readRightSnd [AddCommGroup R] (F : SectionState n R) :
    boundaryLinear ℤ n R (readRightSnd F) =
      ![fun i => F i.succ 0 - F i.castSucc 0,
        upperDiagDiff F,
        fun i => F 0 ⟨n - (i.val + 1), by omega⟩ - F 0 ⟨n - i.val, by omega⟩] := by
  ext s i
  rw [boundaryLinear_apply]
  fin_cases s <;> dsimp only [readRightSnd, upperDiagDiff]
  · congr 1 <;> (refine congrArg₂ F ?_ ?_ <;> (ext; simp))
  · congr 1 <;> (refine congrArg₂ F ?_ ?_ <;> (ext; simp))
  · congr 1 <;> (refine congrArg₂ F ?_ ?_ <;> (ext; simp))

/-- On the `x = n` wall, `glueLower f₁ f₂` reads side `1` (`B → C`) of `f₁`. -/
@[simp] theorem glueLower_last_left (f₁ f₂ : Vertex n → R) (k : Fin (n + 1)) :
    glueLower f₁ f₂ (Fin.last n) k = f₁ (Vertex.edgePoint n 1 k) := by
  have h := congrFun (readLeftFst_glueLower f₁ f₂) (Vertex.edgePoint n 1 k)
  dsimp only [readLeftFst] at h
  exact Eq.trans (congrArg₂ _ (by ext; simp) (by ext; simp)) h

/-- On the `y = 0` wall, `glueLower f₁ f₂` reads side `0` (`A → B`) of `f₁`. -/
@[simp] theorem glueLower_zero_right (f₁ f₂ : Vertex n → R) (k : Fin (n + 1)) :
    glueLower f₁ f₂ k 0 = f₁ (Vertex.edgePoint n 0 k) := by
  have h := congrFun (readLeftFst_glueLower f₁ f₂) (Vertex.edgePoint n 0 k)
  dsimp only [readLeftFst] at h
  exact Eq.trans (congrArg₂ _ (by ext; simp; omega) (by ext; simp)) h

/-- On the `y = n` wall, `glueLower f₁ f₂` reads side `1` (`B → C`) of `f₂` whenever `f₁` and `f₂`
agree along the shared lower diagonal. -/
theorem glueLower_last_right {f₁ f₂ : Vertex n → R}
    (hdiag : ∀ k : Fin (n + 1),
      f₁ (Vertex.edgePoint n 2 ⟨n - k.val, by omega⟩) = f₂ (Vertex.edgePoint n 0 k))
    (k : Fin (n + 1)) :
    glueLower f₁ f₂ ⟨n - k.val, by omega⟩ (Fin.last n) = f₂ (Vertex.edgePoint n 1 k) := by
  have h := congrFun (readLeftSnd_glueLower hdiag) (Vertex.edgePoint n 1 k)
  dsimp only [readLeftSnd] at h
  exact Eq.trans (congrArg₂ _ (by ext; simp) (by ext; simp)) h

/-- On the `x = 0` wall, `glueLower f₁ f₂` reads side `2` (`C → A`) of `f₂` whenever `f₁` and `f₂`
agree along the shared lower diagonal. -/
theorem glueLower_zero_left {f₁ f₂ : Vertex n → R}
    (hdiag : ∀ k : Fin (n + 1),
      f₁ (Vertex.edgePoint n 2 ⟨n - k.val, by omega⟩) = f₂ (Vertex.edgePoint n 0 k))
    (k : Fin (n + 1)) :
    glueLower f₁ f₂ 0 ⟨n - k.val, by omega⟩ = f₂ (Vertex.edgePoint n 2 k) := by
  have h := congrFun (readLeftSnd_glueLower hdiag) (Vertex.edgePoint n 2 k)
  dsimp only [readLeftSnd] at h
  exact Eq.trans (congrArg₂ _ (by ext; simp) (by ext; simp)) h

/-- Any upper-section state `F'` agreeing on the four boundary walls with `glueLower h₁ h₂` (where
`h₁` has boundary `(λ, μ, σ*)` and `h₂` has boundary `(σ, ν, π*)`) has output boundaries
`(μ, ν, -τ ∘ rev)` on `readRightFst F'` and `(λ, τ, π*)` on `readRightSnd F'`, where
`τ = upperDiagDiff F'`. -/
theorem boundaryLinear_readRight_of_wall_eq {lam μ σ ν pi : DominantWeight n}
    {h₁ h₂ : IntegerHive n}
    (hb₁ : h₁.boundary = productBoundary lam μ σ)
    (hb₂ : h₂.boundary = productBoundary σ ν pi)
    {F' : SectionState n ℤ}
    (hwall : ∀ x y : Fin (n + 1),
      (x.val = 0 ∨ x.val = n ∨ y.val = 0 ∨ y.val = n) →
        F' x y = glueLower h₁ h₂ x y) :
    boundaryLinear ℤ n ℤ (readRightFst F') =
        ![μ.1, ν.1, fun i => -upperDiagDiff F' i.rev] ∧
      boundaryLinear ℤ n ℤ (readRightSnd F') =
        ![lam.1, upperDiagDiff F', pi.dual.1] := by
  have hd := sharedLowerDiag_eq_of_productBoundary hb₁ hb₂
  have h_μ : (fun i : Fin n => F' (Fin.last n) i.succ - F' (Fin.last n) i.castSucc) = μ.1 := by
    ext i; rw [hwall _ _ (by simp), hwall _ _ (by simp), glueLower_last_left, glueLower_last_left,
      ← h₁.boundary_apply, hb₁, productBoundary_one]
  have h_ν : (fun i : Fin n =>
      F' ⟨n - (i.val + 1), by omega⟩ (Fin.last n) - F' ⟨n - i.val, by omega⟩ (Fin.last n)) =
      ν.1 := by
    ext i
    have hp₁ : glueLower h₁ h₂ ⟨n - (i.val + 1), by omega⟩ (Fin.last n) = _ :=
      glueLower_last_right hd i.succ
    have hp₀ : glueLower h₁ h₂ ⟨n - i.val, by omega⟩ (Fin.last n) = _ :=
      glueLower_last_right hd i.castSucc
    rw [hwall _ _ (by simp), hwall _ _ (by simp), hp₁, hp₀, ← h₂.boundary_apply, hb₂,
      productBoundary_one]
  have h_lam : (fun i : Fin n => F' i.succ 0 - F' i.castSucc 0) = lam.1 := by
    ext i; rw [hwall _ _ (by simp), hwall _ _ (by simp), glueLower_zero_right, glueLower_zero_right,
      ← h₁.boundary_apply, hb₁, productBoundary_zero]
  have h_pi : (fun i : Fin n => F' 0 ⟨n - (i.val + 1), by omega⟩ - F' 0 ⟨n - i.val, by omega⟩) =
      pi.dual.1 := by
    ext i
    have hp₁ : glueLower h₁ h₂ 0 ⟨n - (i.val + 1), by omega⟩ = _ := glueLower_zero_left hd i.succ
    have hp₀ : glueLower h₁ h₂ 0 ⟨n - i.val, by omega⟩ = _ := glueLower_zero_left hd i.castSucc
    rw [hwall _ _ (by simp), hwall _ _ (by simp), hp₁, hp₀, ← h₂.boundary_apply, hb₂,
      productBoundary_two]
  rw [boundaryLinear_readRightFst, boundaryLinear_readRightSnd, h_μ, h_ν, h_lam, h_pi]
  exact ⟨rfl, rfl⟩

end Gluing

/-! ### Associator dependency closure and all-`n` section transition -/

section AssociatorRestriction

variable {n : ℕ}

/-- Predicate stating that `q : SpaceTimePoint n` belongs to the associator region `A_n`. -/
def SpaceTimePoint.InAssociator (q : SpaceTimePoint n) : Prop :=
  lowerSection n q.finX q.finY ≤ q.t ∧ q.t ≤ upperSection n q.finX q.finY

theorem SpaceTimePoint.inAssociator_def (q : SpaceTimePoint n) :
    q.InAssociator ↔ lowerSection n q.finX q.finY ≤ q.t ∧ q.t ≤ upperSection n q.finX q.finY :=
  Iff.rfl

theorem AssociatorPoint.inAssociator (p : AssociatorPoint n) : p.toSpaceTimePoint.InAssociator :=
  ⟨by simpa using p.abs_sub_le_t, by simpa using p.t_le_sub_abs⟩

/-- Every point of `AssociatorPoint n` strictly above `lowerSection n` lies strictly in the interior
`0 < x, y < n`. -/
theorem AssociatorPoint.interior_of_lowerSection_lt (p : AssociatorPoint n)
    (hp : lowerSection n p.finX p.finY < p.t) :
    0 < p.x ∧ p.x < n ∧ 0 < p.y ∧ p.y < n := by
  have h := (lowerSection_lt_upperSection_iff p.finX p.finY).mp (hp.trans_le p.inAssociator.2)
  simpa using h

/-- Every point of `AssociatorPoint n` strictly below `upperSection n` lies strictly in the interior
`0 < x, y < n`. -/
theorem AssociatorPoint.interior_of_lt_upperSection (p : AssociatorPoint n)
    (hp : p.t < upperSection n p.finX p.finY) :
    0 < p.x ∧ p.x < n ∧ 0 < p.y ∧ p.y < n := by
  have h := (lowerSection_lt_upperSection_iff p.finX p.finY).mp
    (lt_of_le_of_lt p.inAssociator.1 hp)
  simpa using h

/-- Every past vertical dependency from a point in `A_n` strictly above `S` remains in `A_n`. -/
theorem inAssociator_pastVert {q : SpaceTimePoint n} (hq : q.InAssociator)
    (hgt : lowerSection n q.finX q.finY < q.t) : (pastVert q).InAssociator := by
  refine ⟨section_le_pastVert hgt, ?_⟩
  have hup := hq.2
  simp only [pastVert_finX, pastVert_finY, pastVert_t]; omega

/-- The first past horizontal dependency in branch `b` from a point in `A_n` strictly above `S`
remains in `A_n`. -/
theorem inAssociator_pastHoriz₁ (hn : 1 ≤ n) (b : Bool) {q : SpaceTimePoint n}
    (hq : q.InAssociator) (hgt : lowerSection n q.finX q.finY < q.t) :
    (pastHoriz₁ hn b q).InAssociator := by
  refine ⟨section_le_pastHoriz₁ hn b hgt, ?_⟩
  have hup := hq.2
  have hm := abs_le.mp ((upperSection n).abs_sub_of_manhattan_eq_one
    (manhattan_horizPair_fst hn b q.finX q.finY)).le
  simp only [pastHoriz₁_finX, pastHoriz₁_finY, pastHoriz₁_t]; omega

/-- The second past horizontal dependency in branch `b` from a point in `A_n` strictly above `S`
remains in `A_n`. -/
theorem inAssociator_pastHoriz₂ (hn : 1 ≤ n) (b : Bool) {q : SpaceTimePoint n}
    (hq : q.InAssociator) (hgt : lowerSection n q.finX q.finY < q.t) :
    (pastHoriz₂ hn b q).InAssociator := by
  refine ⟨section_le_pastHoriz₂ hn b hgt, ?_⟩
  have hup := hq.2
  have hm := abs_le.mp ((upperSection n).abs_sub_of_manhattan_eq_one
    (manhattan_horizPair_snd hn b q.finX q.finY)).le
  simp only [pastHoriz₂_finX, pastHoriz₂_finY, pastHoriz₂_t]; omega

/-- Every future vertical dependency from a point in `A_n` strictly below `S'` remains in `A_n`. -/
theorem inAssociator_futureVert {q : SpaceTimePoint n} (hq : q.InAssociator)
    (hlt : q.t < upperSection n q.finX q.finY) : (futureVert q).InAssociator := by
  refine ⟨?_, futureVert_le_section hlt⟩
  have hlo := hq.1
  simp only [futureVert_finX, futureVert_finY, futureVert_t]; omega

/-- The first future horizontal dependency in branch `b` from a point in `A_n` strictly below `S'`
remains in `A_n`. -/
theorem inAssociator_futureHoriz₁ (hn : 1 ≤ n) (b : Bool) {q : SpaceTimePoint n}
    (hq : q.InAssociator) (hlt : q.t < upperSection n q.finX q.finY) :
    (futureHoriz₁ hn b q).InAssociator := by
  refine ⟨?_, futureHoriz₁_le_section hn b hlt⟩
  have hlo := hq.1
  have hm := abs_le.mp ((lowerSection n).abs_sub_of_manhattan_eq_one
    (manhattan_horizPair_fst hn b q.finX q.finY)).le
  simp only [futureHoriz₁_finX, futureHoriz₁_finY, futureHoriz₁_t]; omega

/-- The second future horizontal dependency in branch `b` from a point in `A_n` strictly below `S'`
remains in `A_n`. -/
theorem inAssociator_futureHoriz₂ (hn : 1 ≤ n) (b : Bool) {q : SpaceTimePoint n}
    (hq : q.InAssociator) (hlt : q.t < upperSection n q.finX q.finY) :
    (futureHoriz₂ hn b q).InAssociator := by
  refine ⟨?_, futureHoriz₂_le_section hn b hlt⟩
  have hlo := hq.1
  have hm := abs_le.mp ((lowerSection n).abs_sub_of_manhattan_eq_one
    (manhattan_horizPair_snd hn b q.finX q.finY)).le
  simp only [futureHoriz₂_finX, futureHoriz₂_finY, futureHoriz₂_t]; omega

/-- Every point in the recursive dependency closure `depClosure hn (lowerSection n) p` of a point
`p` in `A_n` stays inside `A_n`. -/
theorem depClosure_lowerSection_inAssociator (hn : 1 ≤ n) :
    ∀ {p : SpaceTimePoint n}, p.InAssociator →
      ∀ r ∈ depClosure hn (lowerSection n) p, r.InAssociator := by
  intro p
  induction p using (measure (sectionDepth (lowerSection n))).wf.induction with
  | h p ih =>
    intro hp r hr
    by_cases heq : p.t = lowerSection n p.finX p.finY
    · rw [depClosure_of_eq hn (lowerSection n) heq] at hr
      simpa using (Finset.mem_singleton.mp hr) ▸ hp
    · have hgt : lowerSection n p.finX p.finY < p.t := lt_of_le_of_ne hp.1 (Ne.symm heq)
      rw [depClosure_of_gt hn (lowerSection n) hgt] at hr
      simp only [Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | (((hr | hr) | hr) | hr) | hr
      · exact hp
      · exact ih _ (sectionDepth_pastHoriz₁_lt hn false hgt)
          (inAssociator_pastHoriz₁ hn false hp hgt) r hr
      · exact ih _ (sectionDepth_pastHoriz₂_lt hn false hgt)
          (inAssociator_pastHoriz₂ hn false hp hgt) r hr
      · exact ih _ (sectionDepth_pastHoriz₁_lt hn true hgt)
          (inAssociator_pastHoriz₁ hn true hp hgt) r hr
      · exact ih _ (sectionDepth_pastHoriz₂_lt hn true hgt)
          (inAssociator_pastHoriz₂ hn true hp hgt) r hr
      · exact ih _ (sectionDepth_pastVert_lt hgt) (inAssociator_pastVert hp hgt) r hr

/-- Every point in the recursive dependency closure `depClosure hn (upperSection n) p` of a point
`p` in `A_n` stays inside `A_n`. -/
theorem depClosure_upperSection_inAssociator (hn : 1 ≤ n) :
    ∀ {p : SpaceTimePoint n}, p.InAssociator →
      ∀ r ∈ depClosure hn (upperSection n) p, r.InAssociator := by
  intro p
  induction p using (measure (sectionDepth (upperSection n))).wf.induction with
  | h p ih =>
    intro hp r hr
    by_cases heq : p.t = upperSection n p.finX p.finY
    · rw [depClosure_of_eq hn (upperSection n) heq] at hr
      simpa using (Finset.mem_singleton.mp hr) ▸ hp
    · have hlt : p.t < upperSection n p.finX p.finY := lt_of_le_of_ne hp.2 heq
      rw [depClosure_of_lt hn (upperSection n) hlt] at hr
      simp only [Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | (((hr | hr) | hr) | hr) | hr
      · exact hp
      · exact ih _ (sectionDepth_futureHoriz₁_lt hn false hlt)
          (inAssociator_futureHoriz₁ hn false hp hlt) r hr
      · exact ih _ (sectionDepth_futureHoriz₂_lt hn false hlt)
          (inAssociator_futureHoriz₂ hn false hp hlt) r hr
      · exact ih _ (sectionDepth_futureHoriz₁_lt hn true hlt)
          (inAssociator_futureHoriz₁ hn true hp hlt) r hr
      · exact ih _ (sectionDepth_futureHoriz₂_lt hn true hlt)
          (inAssociator_futureHoriz₂ hn true hp hlt) r hr
      · exact ih _ (sectionDepth_futureVert_lt hlt) (inAssociator_futureVert hp hlt) r hr

/-- All-`n` associator state equivalence from `S = lowerSection n` to `S' = upperSection n`:
`Equiv.refl` at `n = 0`, and `sectionTransition hn (lowerSection n) (upperSection n)` for `1 ≤ n`.
-/
def associatorSectionEquiv (n : ℕ) {R : Type*} [AddCommGroup R] [LinearOrder R] :
    SectionState n R ≃ SectionState n R :=
  if hn : 1 ≤ n then
    sectionTransition hn (lowerSection n) (upperSection n)
  else
    Equiv.refl (SectionState n R)

@[simp] theorem associatorSectionEquiv_zero {R : Type*} [AddCommGroup R] [LinearOrder R] :
    associatorSectionEquiv 0 (R := R) = Equiv.refl (SectionState 0 R) := (rfl)

theorem associatorSectionEquiv_of_one_le {R : Type*} [AddCommGroup R] [LinearOrder R]
    (hn : 1 ≤ n) :
    associatorSectionEquiv n (R := R) =
      sectionTransition hn (lowerSection n) (upperSection n) := by
  simp [associatorSectionEquiv, hn]

/-- At `n = 1`, `lowerSection 1 = upperSection 1`, so `associatorSectionEquiv 1` is also the
identity. -/
@[simp] theorem associatorSectionEquiv_one {R : Type*} [AddCommGroup R] [LinearOrder R] :
    associatorSectionEquiv 1 (R := R) = Equiv.refl (SectionState 1 R) := by
  have heq : lowerSection 1 = upperSection 1 := by
    ext x y; fin_cases x <;> fin_cases y <;> simp
  rw [associatorSectionEquiv_of_one_le le_rfl, heq, sectionTransition_refl]

/-- Time-reversing `S` and `S'` expresses `(associatorSectionEquiv n).symm` via `-upperSection n`
and `-lowerSection n`. -/
theorem associatorSectionEquiv_symm_of_one_le {R : Type*} [AddCommGroup R] [LinearOrder R]
    (hn : 1 ≤ n) :
    (associatorSectionEquiv n (R := R)).symm =
      sectionTransition hn (-upperSection n) (-lowerSection n) := by
  rw [associatorSectionEquiv_of_one_le hn, sectionTransition_symm, sectionTransition_neg]

/-- For every `n : ℕ` (`n = 0` included), every legal excavation schedule from `lowerSection n` to
`upperSection n` agrees with `associatorSectionEquiv n`. -/
theorem evalExcavationSchedule_eq_associatorSectionEquiv {R : Type*} [AddCommGroup R]
    [LinearOrder R] (steps : List (Fin (n + 1) × Fin (n + 1)))
    (h : IsExcavationSchedule (lowerSection n) (upperSection n) steps)
    (val : SectionState n R) :
    evalExcavationSchedule steps h val = associatorSectionEquiv n val := by
  by_cases hn : 1 ≤ n
  · rw [associatorSectionEquiv_of_one_le hn]
    exact evalExcavationSchedule_eq_sectionTransition hn steps h val
  · have hn0 : n = 0 := by omega
    subst hn0
    cases steps with
    | nil => simp
    | cons p ps => exact absurd h.head.one_le (by decide)

/-- `associatorSectionEquiv n` leaves all four boundary walls `x = 0`, `x = n`, `y = 0`, `y = n`
unchanged. -/
theorem associatorSectionEquiv_wall {R : Type*} [AddCommGroup R] [LinearOrder R]
    (val : SectionState n R) (x y : Fin (n + 1))
    (hw : x.val = 0 ∨ x.val = n ∨ y.val = 0 ∨ y.val = n) :
    associatorSectionEquiv n val x y = val x y := by
  by_cases hn : 1 ≤ n
  · rw [associatorSectionEquiv_of_one_le hn, sectionTransition_apply]
    have heq : ((upperSection n).point x y).t =
        lowerSection n ((upperSection n).point x y).finX ((upperSection n).point x y).finY := by
      rw [SpaceTimeSection.point_t, SpaceTimeSection.point_finX, SpaceTimeSection.point_finY,
        (lowerSection_eq_upperSection_iff x y).mpr hw]
    rw [extendSection_of_eq hn (lowerSection n) val heq]
    simp
  · have hn0 : n = 0 := by omega
    subst hn0; rfl

/-- Applying `associatorSectionEquiv n` to `glueLower h₁ h₂` preserves all four exterior boundary
sides `(λ, μ, ν, π*)`. -/
theorem boundaryLinear_readRight_associatorSectionEquiv {lam μ σ ν pi : DominantWeight n}
    {h₁ h₂ : IntegerHive n}
    (hb₁ : h₁.boundary = productBoundary lam μ σ)
    (hb₂ : h₂.boundary = productBoundary σ ν pi) :
    let F' := associatorSectionEquiv n (glueLower (⇑h₁) (⇑h₂))
    boundaryLinear ℤ n ℤ (readRightFst F') =
        ![μ.1, ν.1, fun i => -upperDiagDiff F' i.rev] ∧
      boundaryLinear ℤ n ℤ (readRightSnd F') =
        ![lam.1, upperDiagDiff F', pi.dual.1] :=
  boundaryLinear_readRight_of_wall_eq hb₁ hb₂ (associatorSectionEquiv_wall _)

/-- Order-preserving additive monoid homomorphisms (`ℤ →+o ℝ`) commute with
`associatorSectionEquiv n` for all `n : ℕ`. -/
theorem map_associatorSectionEquiv {R R' : Type*} [AddCommGroup R] [LinearOrder R]
    [AddCommGroup R'] [LinearOrder R'] (φ : R →+o R') (val : SectionState n R)
    (x y : Fin (n + 1)) :
    φ (associatorSectionEquiv n val x y) =
      associatorSectionEquiv n (fun x' y' => φ (val x' y')) x y := by
  by_cases hn : 1 ≤ n
  · simp [associatorSectionEquiv_of_one_le hn, map_extendSection]
  · have hn0 : n = 0 := by omega
    subst hn0; rfl

/-- `associatorSectionEquiv n` is positively homogeneous for all `n : ℕ`. -/
theorem associatorSectionEquiv_smul_of_nonneg {K R : Type*} [Semiring K] [PartialOrder K]
    [AddCommGroup R] [LinearOrder R] [Module K R] [PosSMulMono K R] {c : K} (hc : 0 ≤ c)
    (val : SectionState n R) :
    associatorSectionEquiv n (c • val) = c • associatorSectionEquiv n val := by
  ext x y
  by_cases hn : 1 ≤ n
  · simp [associatorSectionEquiv_of_one_le hn, extendSection_smul_of_nonneg hn _ _ hc]
  · have hn0 : n = 0 := by omega
    subst hn0; rfl

/-- Over `ℝ`, `associatorSectionEquiv n` is piecewise affine on `Set.univ` for all `n : ℕ`. -/
theorem isPiecewiseAffineOn_associatorSectionEquiv (n : ℕ) :
    IsPiecewiseAffineOn (associatorSectionEquiv n : SectionState n ℝ → SectionState n ℝ)
      Set.univ := by
  by_cases hn : 1 ≤ n
  · rw [associatorSectionEquiv_of_one_le hn]
    exact isPiecewiseAffineOn_sectionTransition hn (lowerSection n) (upperSection n)
  · have hn0 : n = 0 := by omega
    subst hn0
    simpa [associatorSectionEquiv_zero] using
      isPiecewiseAffineOn_continuousAffineMap (ContinuousAffineMap.id ℝ (SectionState 0 ℝ))
        Set.univ

/-- Over `ℝ`, `associatorSectionEquiv n` is continuous for all `n : ℕ`. -/
theorem continuous_associatorSectionEquiv (n : ℕ) :
    Continuous (associatorSectionEquiv n : SectionState n ℝ → SectionState n ℝ) :=
  continuousOn_univ.mp (isPiecewiseAffineOn_associatorSectionEquiv n).continuousOn

end AssociatorRestriction

/-! ### Explicit checks: `max` vs `min` involution, `y = 0` wall propagation, and `n = 0` -/

section Checks

/-- Variant local interior state update `e' = min(a + c, b + d) - e` replacing `max` by `min` at an
excavatable vertex `(x, y)`. -/
def SpaceTimeSection.excavateStateMin {n : ℕ} {R : Type*} [AddCommGroup R] [LinearOrder R]
    {S : SpaceTimeSection n} {x y : Fin (n + 1)} (h : S.IsExcavatableAt x y)
    (val : SectionState n R) : SectionState n R :=
  fun x' y' =>
    if x' = x ∧ y' = y then
      min (val ⟨x.val + 1, by have := h.hx; omega⟩ y + val ⟨x.val - 1, by have := h.hx; omega⟩ y)
        (val x ⟨y.val + 1, by have := h.hy; omega⟩ + val x ⟨y.val - 1, by have := h.hy; omega⟩) -
        val x y
    else
      val x' y'

@[simp] theorem SpaceTimeSection.excavateStateMin_apply {n : ℕ} {R : Type*} [AddCommGroup R]
    [LinearOrder R] {S : SpaceTimeSection n} {x y : Fin (n + 1)} (h : S.IsExcavatableAt x y)
    (val : SectionState n R) (x' y' : Fin (n + 1)) :
    S.excavateStateMin h val x' y' =
      if x' = x ∧ y' = y then
        min (val ⟨x.val + 1, by have := h.hx; omega⟩ y + val ⟨x.val - 1, by have := h.hx; omega⟩ y)
          (val x ⟨y.val + 1, by have := h.hy; omega⟩ + val x ⟨y.val - 1, by have := h.hy; omega⟩) -
          val x y
      else val x' y' := (rfl)

/-- Replacing `max` by `min` in the local interior update (`SpaceTimeSection.excavateStateMin`) is
still an involution on `SectionState n R` (ties included), even though it fails to preserve hive
rhombus concavity. -/
@[simp] theorem SpaceTimeSection.excavateStateMin_involutive {n : ℕ} {R : Type*} [AddCommGroup R]
    [LinearOrder R] {S : SpaceTimeSection n} {x y : Fin (n + 1)} (h : S.IsExcavatableAt x y)
    (val : SectionState n R) :
    S.excavateStateMin h (S.excavateStateMin h val) = val := by
  ext x' y'
  by_cases heq : x' = x ∧ y' = y
  · rcases heq with ⟨rfl, rfl⟩
    simp [h.add_x_ne, h.sub_x_ne, h.add_y_ne, h.sub_y_ne]
  · simp [heq]

/-- At `n = 2`, the unique interior vertex `(1, 1)` is excavatable on `lowerSection 2`. -/
theorem lowerSection_two_isExcavatableAt : (lowerSection 2).IsExcavatableAt 1 1 :=
  SpaceTimeSection.IsExcavatableAt.mk' (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)

/-- At `n = 2` (a single unit octahedron), `associatorSectionEquiv 2` is given by the single
excavation step at `(1, 1)`. -/
theorem associatorSectionEquiv_two_apply {R : Type*} [AddCommGroup R] [LinearOrder R]
    (F : SectionState 2 R) :
    associatorSectionEquiv 2 F =
      (lowerSection 2).excavateState lowerSection_two_isExcavatableAt F := by
  have hsched : IsExcavationSchedule (lowerSection 2) (upperSection 2) [(1, 1)] := by
    rw [isExcavationSchedule_cons]
    exact ⟨lowerSection_two_isExcavatableAt, (isExcavationSchedule_nil _ _).mpr
      (by ext x y; fin_cases x <;> fin_cases y <;> simp)⟩
  simpa using (evalExcavationSchedule_eq_associatorSectionEquiv [(1, 1)] hsched F).symm

/-- At `n = 2`, gluing `exampleTwo` and `2 • exampleTwo` onto `S` and evolving to `S'` via the
`max` recurrence (`associatorSectionEquiv 2`) produces rhombus-concave functions on both output
faces, whereas replacing `max` by `min` at `(1, 1)` (`excavateStateMin`) violates the unit-rhombus
inequality on `S'`. -/
theorem minRule_breaks_isRhombusConcave_two :
    let F : SectionState 2 ℤ := glueLower (⇑exampleTwo) (⇑((2 : ℕ) • exampleTwo))
    let F_max : SectionState 2 ℤ := associatorSectionEquiv 2 F
    let F_min : SectionState 2 ℤ :=
      (lowerSection 2).excavateStateMin lowerSection_two_isExcavatableAt F
    IsRhombusConcave (readRightFst F_max) ∧
      IsRhombusConcave (readRightSnd F_max) ∧
      ¬ IsRhombusConcave (readRightSnd F_min) := by
  intro F F_max F_min
  have hF (x y : Fin 3) :
      F x y = if y.val ≤ x.val then
        (if 2 - x.val = 2 then 0 else 1) + (if y.val = 0 then 0 else 1)
      else 4 := by
    fin_cases x <;> fin_cases y <;> simp [F, glueLower_apply]
  have hFmax (x y : Fin 3) :
      F_max x y = if x = 1 ∧ y = 1 then 4 else F x y := by
    rw [show F_max = _ from associatorSectionEquiv_two_apply F,
      SpaceTimeSection.excavateState_apply]
    by_cases h11 : x = 1 ∧ y = 1
    · rcases h11 with ⟨rfl, rfl⟩; simp [hF]
    · simp [h11]
  let stepZ : IntegerHive 2 := detTwo.reflect + affine 2 (-1) 0
  have hstepZ (p : Vertex 2) : stepZ p = if p.z = 0 then 0 else 1 := by simp [stepZ]
  have hF1 : readRightFst F_max = ⇑(exampleTwo + stepZ) := by
    ext p
    have hxp : p.x = 0 ∨ p.x = 1 ∨ p.x = 2 := by have := p.sum_eq; omega
    have hzp : p.z = 0 ∨ p.z = 1 ∨ p.z = 2 := by have := p.sum_eq; omega
    rcases hxp with hx | hx | hx <;> rcases hzp with hz | hz | hz
    all_goals
      first
      | (have := p.sum_eq; omega)
      | simp [readRightFst_apply, hstepZ, hFmax, hF, hx, hz]
  have hF2 : readRightSnd F_max = ⇑(exampleTwo + (2 : ℕ) • stepZ) := by
    ext p
    have hyp : p.y = 0 ∨ p.y = 1 ∨ p.y = 2 := by have := p.sum_eq; omega
    have hzp : p.z = 0 ∨ p.z = 1 ∨ p.z = 2 := by have := p.sum_eq; omega
    rcases hyp with hy | hy | hy <;> rcases hzp with hz | hz | hz
    all_goals
      first
      | (have := p.sum_eq; omega)
      | (have hx : p.x = 2 - p.y - p.z := by have := p.sum_eq; omega
         simp [readRightSnd_apply, hstepZ, hFmax, hF, hx, hy, hz])
  refine ⟨hF1 ▸ (exampleTwo + stepZ).isRhombusConcave,
    hF2 ▸ (exampleTwo + (2 : ℕ) • stepZ).isRhombusConcave, fun hf => ?_⟩
  rw [isRhombusConcave_def] at hf
  have hB := hf isRhombus_at_cornerA.rotate
  simp [readRightSnd_apply, F_min, hF] at hB

/-- On the `y = 0` wall (`0 < x < n`), the wall recurrence
`f(x, 0, t + 1) = f(x + 1, 0, t) + f(x - 1, 0, t) - f(x, 0, t - 1)` propagates edge differences
unchanged: `f(x, 0, t + 1) - f(x - 1, 0, t) = f(x + 1, 0, t) - f(x, 0, t - 1)`. -/
theorem stepAt_wall_zero_diff_eq {n : ℕ} {R : Type*} [AddCommGroup R] [LinearOrder R]
    (hn : 1 ≤ n) (curr prev : SectionState n R) {x : Fin (n + 1)} (hx : 0 < x.val ∧ x.val < n) :
    stepAt hn curr prev x 0 - curr ⟨x.val - 1, by omega⟩ 0 =
      curr ⟨x.val + 1, by omega⟩ 0 - prev x 0 := by
  rw [stepAt_wall_y hn curr prev hx (Or.inl rfl)]
  abel

/-- At `n = 0`, `AssociatorPoint 0` has a single point, `lowerSection 0 = upperSection 0`, and the
induced map on the one-point hive `Hive 0 R` is the identity. -/
theorem associator_zero_summary {R : Type*} [AddCommGroup R] [LinearOrder R] :
    Fintype.card (AssociatorPoint 0) = 1 ∧
      lowerSection 0 = upperSection 0 ∧
      associatorSectionEquiv 0 (R := R) = Equiv.refl (SectionState 0 R) ∧
      ∀ h : Hive 0 R, readRightSnd (associatorSectionEquiv 0 (glueLower (⇑h) (⇑h))) = ⇑h := by
  refine ⟨Fintype.card_unique, lowerSection_zero_eq_upperSection_zero, rfl, fun h => ?_⟩
  ext p
  have hp : p = Vertex.cornerA 0 := by have := p.sum_eq; ext <;> simp <;> omega
  subst hp
  have hv : (⟨0, 0, 0, rfl⟩ : Vertex 0) = Vertex.cornerA 0 := by ext <;> simp
  simp [readRightSnd_apply, glueLower_apply, hv]

end Checks

end TauCeti.Hive
