/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Octahedron.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The bounded modified octahedron recurrence and global section transitions

For `1 ≤ n`, Henriques and Kamnitzer define a bounded modified octahedron recurrence on
`Y_n = [0, n]² × ℝ` (and on the parity lattice `L_n = SpaceTimePoint n`): to compute
`f(x, y, t + 1)` from slice `t` and slice `t - 1`, one subtracts `f(x, y, t - 1)` from
`max (f(x + 1, y, t) + f(x - 1, y, t)) (f(x, y + 1, t) + f(x, y - 1, t))` in the interior, uses
only `f(x + 1, y, t) + f(x - 1, y, t)` along the `y = 0, n` walls, uses only
`f(x, y + 1, t) + f(x, y - 1, t)` along the `x = 0, n` walls, and uses the sum of the two inward
neighbours at each of the four corners.

Because `e ↦ M - e` is an involution in every abelian group (ties in `max` included), reversing
time (`t ↦ -t`) inverts the recurrence on both `Y_n` and `L_n`. Given any initial section
`S : SpaceTimeSection n` and grid data `val : SectionState n R`, finite dependency recursion
constructs the unique global solution `extendSection hn S val : SpaceTimePoint n → R` agreeing
with `val` on `S`. Evaluating on a second section `S₂` yields the invertible transition equivalence
`sectionTransition hn S₁ S₂ : SectionState n R ≃ SectionState n R`.

## Main definitions

* `TauCeti.Hive.inwardCoord`, `TauCeti.Hive.horizPair`, `TauCeti.Hive.branchSum`,
  `TauCeti.Hive.stepAt`: the bounded modified recurrence update rule for `1 ≤ n`.
* `TauCeti.Hive.IsRealTimeSolution`, `TauCeti.Hive.IsLatticeSolution`: solution predicates on
  `[0, n]² × ℝ` and `SpaceTimePoint n`.
* `TauCeti.Hive.sectionDepth`, `TauCeti.Hive.extendSection`, `TauCeti.Hive.sectionTransition`:
  well-founded recursion depth, finite dependency extension from a section, and invertible
  section-to-section state transitions.

## Main results

* `TauCeti.Hive.stepAt_interior`, `TauCeti.Hive.stepAt_wall_y`, `TauCeti.Hive.stepAt_wall_x`,
  `TauCeti.Hive.stepAt_corner`, `TauCeti.Hive.stepAt_involutive`: regional update formulas and
  involutivity.
* `TauCeti.Hive.isRealTimeSolution_timeRev_iff`, `TauCeti.Hive.isLatticeSolution_timeRev_iff`:
  time-reversal inversion on `[0, n]² × ℝ` and `SpaceTimePoint n`.
* `TauCeti.Hive.isLatticeSolution_extendSection`,
  `TauCeti.Hive.eq_extendSection_of_isLatticeSolution`: existence and uniqueness of global lattice
  solutions from any section.
* `TauCeti.Hive.extendSection_smul_of_nonneg`, `TauCeti.Hive.map_extendSection`: positive
  homogeneity and compatibility with order-preserving additive homomorphisms (`ℤ →+o ℝ`).

## References

* A. Henriques and J. Kamnitzer, *Crystals and coboundary categories*, Adv. Math. **206** (2006),
  §3, equation (5).
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §5.
-/

public section

namespace TauCeti.Hive

/-! ### Bounded horizontal neighbour stencil and local update rule (`1 ≤ n`) -/

section Stencil

variable {n : ℕ}

/-- For `1 ≤ n`, the inward coordinate adjacent to `k ∈ {0, n}`: `1` when `k = 0`, and `n - 1`
otherwise. -/
def inwardCoord (hn : 1 ≤ n) (k : Fin (n + 1)) : Fin (n + 1) :=
  if k.val = 0 then ⟨1, by omega⟩ else ⟨n - 1, by omega⟩

theorem abs_inwardCoord_sub (hn : 1 ≤ n) {k : Fin (n + 1)} (hk : k.val = 0 ∨ k.val = n) :
    |(inwardCoord hn k : ℤ) - k| = 1 := by
  rcases hk with h0 | hn'
  · simp only [inwardCoord, h0, ↓reduceIte]; rfl
  · have hne : n ≠ 0 := by omega
    simp only [inwardCoord, hn', hne, ↓reduceIte]
    rw [Nat.cast_sub hn]
    norm_num

/-- The pair of horizontal grid neighbours summed by branch `b : Bool` of Henriques–Kamnitzer's
bounded recurrence at `(x, y)` for `1 ≤ n`. On walls and corners both `false` and `true` return
the unique boundary neighbour pair. -/
def horizPair (hn : 1 ≤ n) (b : Bool) (x y : Fin (n + 1)) :
    (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1)) :=
  if hx : 0 < x.val ∧ x.val < n then
    if hy : 0 < y.val ∧ y.val < n then
      match b with
      | false => ((⟨x.val + 1, by omega⟩, y), (⟨x.val - 1, by omega⟩, y))
      | true => ((x, ⟨y.val + 1, by omega⟩), (x, ⟨y.val - 1, by omega⟩))
    else
      ((⟨x.val + 1, by omega⟩, y), (⟨x.val - 1, by omega⟩, y))
  else if hy : 0 < y.val ∧ y.val < n then
    ((x, ⟨y.val + 1, by omega⟩), (x, ⟨y.val - 1, by omega⟩))
  else
    ((inwardCoord hn x, y), (x, inwardCoord hn y))

/-- Along branch `false`, any strictly interior `x`-coordinate (`0 < x < n`) selects the two
`x`-neighbours `(x + 1, y)` and `(x - 1, y)`, regardless of `y`. -/
theorem horizPair_false_interior (hn : 1 ≤ n) {x : Fin (n + 1)} (y : Fin (n + 1))
    (hx : 0 < x.val ∧ x.val < n) :
    horizPair hn false x y = ((⟨x.val + 1, by omega⟩, y), (⟨x.val - 1, by omega⟩, y)) := by
  simp [horizPair, hx]

/-- Along branch `true`, any strictly interior `y`-coordinate (`0 < y < n`) selects the two
`y`-neighbours `(x, y + 1)` and `(x, y - 1)`, regardless of `x`. -/
theorem horizPair_true_interior (hn : 1 ≤ n) (x : Fin (n + 1)) {y : Fin (n + 1)}
    (hy : 0 < y.val ∧ y.val < n) :
    horizPair hn true x y = ((x, ⟨y.val + 1, by omega⟩), (x, ⟨y.val - 1, by omega⟩)) := by
  simp [horizPair, hy]

/-- The first neighbour in `horizPair hn b x y` has horizontal Manhattan distance `1` from
`(x, y)`. -/
theorem manhattan_horizPair_fst (hn : 1 ≤ n) (b : Bool) (x y : Fin (n + 1)) :
    |((horizPair hn b x y).1.1 : ℤ) - x| + |((horizPair hn b x y).1.2 : ℤ) - y| = 1 := by
  have hxlt := x.isLt
  unfold horizPair
  split_ifs with hx hy hy'
  · cases b <;> simp
  · simp
  · simp
  · simp only [sub_self, abs_zero, add_zero]
    exact abs_inwardCoord_sub hn (by omega)

/-- The second neighbour in `horizPair hn b x y` has horizontal Manhattan distance `1` from
`(x, y)`. -/
theorem manhattan_horizPair_snd (hn : 1 ≤ n) (b : Bool) (x y : Fin (n + 1)) :
    |((horizPair hn b x y).2.1 : ℤ) - x| + |((horizPair hn b x y).2.2 : ℤ) - y| = 1 := by
  have hylt := y.isLt
  unfold horizPair
  split_ifs with hx hy hy'
  · cases b
    · simp only [sub_self, abs_zero, add_zero]
      rw [abs_of_nonpos (by omega)]; omega
    · simp only [sub_self, abs_zero, zero_add]
      rw [abs_of_nonpos (by omega)]; omega
  · simp only [sub_self, abs_zero, add_zero]
    rw [abs_of_nonpos (by omega)]; omega
  · simp only [sub_self, abs_zero, zero_add]
    rw [abs_of_nonpos (by omega)]; omega
  · simp only [sub_self, abs_zero, zero_add]
    exact abs_inwardCoord_sub hn (by omega)

/-- Sum of the two horizontal neighbours selected by branch `b` at `(x, y)`. -/
def branchSum {R : Type*} [Add R] (hn : 1 ≤ n) (curr : SectionState n R) (b : Bool)
    (x y : Fin (n + 1)) : R :=
  curr (horizPair hn b x y).1.1 (horizPair hn b x y).1.2 +
    curr (horizPair hn b x y).2.1 (horizPair hn b x y).2.2

/-- Local update rule of Henriques–Kamnitzer's bounded modified octahedron recurrence (eq. 5)
for `1 ≤ n`, computing slice `t + 1` from slice `t` (`curr`) and slice `t - 1` (`prev`). -/
def stepAt {R : Type*} [AddCommGroup R] [LinearOrder R] (hn : 1 ≤ n)
    (curr prev : SectionState n R) (x y : Fin (n + 1)) : R :=
  max (branchSum hn curr false x y) (branchSum hn curr true x y) - prev x y

section Formulas

variable {R : Type*} [AddCommGroup R] [LinearOrder R] (hn : 1 ≤ n)
  (curr prev : SectionState n R)

/-- Interior rule `e' = max(a + c, b + d) - e` for `0 < x < n` and `0 < y < n`. -/
theorem stepAt_interior {x y : Fin (n + 1)} (hx : 0 < x.val ∧ x.val < n)
    (hy : 0 < y.val ∧ y.val < n) :
    stepAt hn curr prev x y =
      max (curr ⟨x.val + 1, by omega⟩ y + curr ⟨x.val - 1, by omega⟩ y)
        (curr x ⟨y.val + 1, by omega⟩ + curr x ⟨y.val - 1, by omega⟩) - prev x y := by
  simp [stepAt, branchSum, horizPair, hx, hy]

/-- Open `y = 0, n` wall rule `f(x, y, t + 1) = f(x + 1, y, t) + f(x - 1, y, t) - f(x, y, t - 1)`.
-/
theorem stepAt_wall_y {x y : Fin (n + 1)} (hx : 0 < x.val ∧ x.val < n)
    (hy : y.val = 0 ∨ y.val = n) :
    stepAt hn curr prev x y =
      curr ⟨x.val + 1, by omega⟩ y + curr ⟨x.val - 1, by omega⟩ y - prev x y := by
  unfold stepAt branchSum horizPair
  split_ifs <;> try omega
  simp

/-- Open `x = 0, n` wall rule `f(x, y, t + 1) = f(x, y + 1, t) + f(x, y - 1, t) - f(x, y, t - 1)`.
-/
theorem stepAt_wall_x {x y : Fin (n + 1)} (hx : x.val = 0 ∨ x.val = n)
    (hy : 0 < y.val ∧ y.val < n) :
    stepAt hn curr prev x y =
      curr x ⟨y.val + 1, by omega⟩ + curr x ⟨y.val - 1, by omega⟩ - prev x y := by
  unfold stepAt branchSum horizPair
  split_ifs <;> try omega
  simp

/-- Corner rule `f(x, y, t + 1) = f(x_in, y, t) + f(x, y_in, t) - f(x, y, t - 1)` at the four
corners `(x, y) ∈ {0, n}²`. -/
theorem stepAt_corner {x y : Fin (n + 1)} (hx : x.val = 0 ∨ x.val = n)
    (hy : y.val = 0 ∨ y.val = n) :
    stepAt hn curr prev x y =
      curr (inwardCoord hn x) y + curr x (inwardCoord hn y) - prev x y := by
  unfold stepAt branchSum horizPair
  split_ifs <;> try omega
  simp

/-- Applying `stepAt hn curr` twice in the `prev` slot recovers `prev` (ties in `max` included). -/
@[simp] theorem stepAt_involutive (x y : Fin (n + 1)) :
    stepAt hn curr (stepAt hn curr prev) x y = prev x y :=
  sub_sub_cancel _ _

end Formulas

end Stencil

/-! ### Continuous-time (`[0, n]² × ℝ`) and parity-lattice (`SpaceTimePoint n`) solutions -/

section Solutions

variable {n : ℕ} {R : Type*} [AddCommGroup R] [LinearOrder R]

/-- Solution predicate for Henriques–Kamnitzer's bounded modified recurrence (eq. 5) on
`Y_n = [0, n]² × ℝ` (`1 ≤ n`). -/
def IsRealTimeSolution (hn : 1 ≤ n) (f : Fin (n + 1) → Fin (n + 1) → ℝ → R) : Prop :=
  ∀ (t : ℝ) (x y : Fin (n + 1)),
    f x y (t + 1) = stepAt hn (fun x' y' => f x' y' t) (fun x' y' => f x' y' (t - 1)) x y

/-- Reversing time `t ↦ -t` preserves `IsRealTimeSolution` (and hence inverts the recurrence). -/
theorem isRealTimeSolution_timeRev {hn : 1 ≤ n} {f : Fin (n + 1) → Fin (n + 1) → ℝ → R}
    (hf : IsRealTimeSolution hn f) :
    IsRealTimeSolution hn (fun x y t => f x y (-t)) := by
  intro t x y
  have ht1 : -(t - 1) = -t + 1 := by ring
  have ht2 : -(t + 1) = -t - 1 := by ring
  simp only [ht1, ht2]
  have hfun : (fun x' y' => f x' y' (-t + 1)) =
      stepAt hn (fun x' y' => f x' y' (-t)) (fun x' y' => f x' y' (-t - 1)) := by
    ext x' y'; exact hf (-t) x' y'
  rw [hfun, stepAt_involutive]

@[simp] theorem isRealTimeSolution_timeRev_iff (hn : 1 ≤ n)
    (f : Fin (n + 1) → Fin (n + 1) → ℝ → R) :
    IsRealTimeSolution hn (fun x y t => f x y (-t)) ↔ IsRealTimeSolution hn f :=
  ⟨fun h => by simpa using isRealTimeSolution_timeRev h, isRealTimeSolution_timeRev⟩

/-- Top point `(x, y, t₀ + 1)` of an odd-centered stencil in `SpaceTimePoint n`. -/
def stencilTop (x y : Fin (n + 1)) (t₀ : ℤ) (hodd : Odd ((x : ℤ) + y + t₀)) :
    SpaceTimePoint n where
  x := x.val
  y := y.val
  t := t₀ + 1
  x_le := Nat.le_of_lt_succ x.isLt
  y_le := Nat.le_of_lt_succ y.isLt
  even_sum := by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩

/-- Bottom point `(x, y, t₀ - 1)` of an odd-centered stencil in `SpaceTimePoint n`. -/
def stencilBot (x y : Fin (n + 1)) (t₀ : ℤ) (hodd : Odd ((x : ℤ) + y + t₀)) :
    SpaceTimePoint n where
  x := x.val
  y := y.val
  t := t₀ - 1
  x_le := Nat.le_of_lt_succ x.isLt
  y_le := Nat.le_of_lt_succ y.isLt
  even_sum := by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩

/-- Horizontal neighbour `(q.1, q.2, t₀)` at Manhattan distance `1` from an odd-centered stencil
belongs to `SpaceTimePoint n`. -/
def stencilHoriz {q : Fin (n + 1) × Fin (n + 1)} {x y : Fin (n + 1)}
    (hm : |(q.1 : ℤ) - x| + |(q.2 : ℤ) - y| = 1) (t₀ : ℤ) (hodd : Odd ((x : ℤ) + y + t₀)) :
    SpaceTimePoint n where
  x := q.1.val
  y := q.2.val
  t := t₀
  x_le := Nat.le_of_lt_succ q.1.isLt
  y_le := Nat.le_of_lt_succ q.2.isLt
  even_sum := by
    rw [Int.even_iff]
    have ho := Int.odd_iff.mp hodd
    rcases le_total (q.1 : ℤ) x with hx | hx <;> rcases le_total (q.2 : ℤ) y with hy | hy
    · rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)] at hm; omega
    · rw [abs_of_nonpos (by omega), abs_of_nonneg (by omega)] at hm; omega
    · rw [abs_of_nonneg (by omega), abs_of_nonpos (by omega)] at hm; omega
    · rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)] at hm; omega

@[simp] theorem stencilTop_x (x y : Fin (n + 1)) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilTop x y t₀ h).x = x := (rfl)
@[simp] theorem stencilTop_y (x y : Fin (n + 1)) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilTop x y t₀ h).y = y := (rfl)
@[simp] theorem stencilTop_t (x y : Fin (n + 1)) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilTop x y t₀ h).t = t₀ + 1 := (rfl)
@[simp] theorem stencilTop_finX (x y : Fin (n + 1)) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilTop x y t₀ h).finX = x := by ext; simp
@[simp] theorem stencilTop_finY (x y : Fin (n + 1)) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilTop x y t₀ h).finY = y := by ext; simp

@[simp] theorem stencilBot_x (x y : Fin (n + 1)) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilBot x y t₀ h).x = x := (rfl)
@[simp] theorem stencilBot_y (x y : Fin (n + 1)) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilBot x y t₀ h).y = y := (rfl)
@[simp] theorem stencilBot_t (x y : Fin (n + 1)) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilBot x y t₀ h).t = t₀ - 1 := (rfl)
@[simp] theorem stencilBot_finX (x y : Fin (n + 1)) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilBot x y t₀ h).finX = x := by ext; simp
@[simp] theorem stencilBot_finY (x y : Fin (n + 1)) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilBot x y t₀ h).finY = y := by ext; simp

@[simp] theorem stencilHoriz_x {q : Fin (n + 1) × Fin (n + 1)} {x y : Fin (n + 1)}
    (hm : |(q.1 : ℤ) - x| + |(q.2 : ℤ) - y| = 1) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilHoriz hm t₀ h).x = q.1 := (rfl)
@[simp] theorem stencilHoriz_y {q : Fin (n + 1) × Fin (n + 1)} {x y : Fin (n + 1)}
    (hm : |(q.1 : ℤ) - x| + |(q.2 : ℤ) - y| = 1) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilHoriz hm t₀ h).y = q.2 := (rfl)
@[simp] theorem stencilHoriz_t {q : Fin (n + 1) × Fin (n + 1)} {x y : Fin (n + 1)}
    (hm : |(q.1 : ℤ) - x| + |(q.2 : ℤ) - y| = 1) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilHoriz hm t₀ h).t = t₀ := (rfl)
@[simp] theorem stencilHoriz_finX {q : Fin (n + 1) × Fin (n + 1)} {x y : Fin (n + 1)}
    (hm : |(q.1 : ℤ) - x| + |(q.2 : ℤ) - y| = 1) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilHoriz hm t₀ h).finX = q.1 := by ext; simp
@[simp] theorem stencilHoriz_finY {q : Fin (n + 1) × Fin (n + 1)} {x y : Fin (n + 1)}
    (hm : |(q.1 : ℤ) - x| + |(q.2 : ℤ) - y| = 1) (t₀ : ℤ) (h : Odd ((x : ℤ) + y + t₀)) :
    (stencilHoriz hm t₀ h).finY = q.2 := by ext; simp

/-- Sum of the two parity-lattice neighbours in branch `b` around odd stencil center `(x, y, t₀)`.
-/
def latticeBranchSum {R : Type*} [AddCommGroup R] (hn : 1 ≤ n) (f : SpaceTimePoint n → R)
    (b : Bool) (x y : Fin (n + 1)) (t₀ : ℤ) (hodd : Odd ((x : ℤ) + y + t₀)) : R :=
  f (stencilHoriz (manhattan_horizPair_fst hn b x y) t₀ hodd) +
    f (stencilHoriz (manhattan_horizPair_snd hn b x y) t₀ hodd)

/-- Solution predicate for Henriques–Kamnitzer's bounded modified recurrence on the parity lattice
`SpaceTimePoint n` (`1 ≤ n`). -/
def IsLatticeSolution (hn : 1 ≤ n) (f : SpaceTimePoint n → R) : Prop :=
  ∀ (x y : Fin (n + 1)) (t₀ : ℤ) (hodd : Odd ((x : ℤ) + y + t₀)),
    f (stencilTop x y t₀ hodd) =
      max (latticeBranchSum hn f false x y t₀ hodd) (latticeBranchSum hn f true x y t₀ hodd) -
        f (stencilBot x y t₀ hodd)

/-- Restricting a continuous-time solution on `[0, n]² × ℝ` to `SpaceTimePoint n` yields a lattice
solution. -/
theorem IsRealTimeSolution.toLatticeSolution {hn : 1 ≤ n}
    {F : Fin (n + 1) → Fin (n + 1) → ℝ → R} (hF : IsRealTimeSolution hn F) :
    IsLatticeSolution hn (fun p : SpaceTimePoint n => F p.finX p.finY (p.t : ℝ)) := by
  intro x y t₀ hodd
  have h := hF (t₀ : ℝ) x y
  simp only [stencilTop_finX, stencilTop_finY, stencilTop_t, Int.cast_add, Int.cast_one, h,
    stepAt, branchSum, latticeBranchSum, stencilHoriz_finX, stencilHoriz_finY, stencilHoriz_t,
    stencilBot_finX, stencilBot_finY, stencilBot_t, Int.cast_sub]

/-- Time reversal `p ↦ p.timeRev` preserves `IsLatticeSolution`. -/
theorem isLatticeSolution_timeRev {hn : 1 ≤ n} {f : SpaceTimePoint n → R}
    (hf : IsLatticeSolution hn f) :
    IsLatticeSolution hn (fun p => f p.timeRev) := by
  intro x y t₀ hodd
  have hodd' : Odd ((x : ℤ) + y + -t₀) := by
    rw [Int.odd_iff]; have := Int.odd_iff.mp hodd; omega
  have h := hf x y (-t₀) hodd'
  have htop : (stencilTop x y t₀ hodd).timeRev = stencilBot x y (-t₀) hodd' := by
    ext <;> simp; omega
  have hbot : (stencilBot x y t₀ hodd).timeRev = stencilTop x y (-t₀) hodd' := by
    ext <;> simp; omega
  have hbr (b : Bool) : latticeBranchSum hn (fun p => f p.timeRev) b x y t₀ hodd =
      latticeBranchSum hn f b x y (-t₀) hodd' := by
    simp only [latticeBranchSum]
    congr 2 <;> (ext <;> simp)
  dsimp only
  rw [htop, hbot, hbr false, hbr true, h, sub_sub_cancel]

@[simp] theorem isLatticeSolution_timeRev_iff (hn : 1 ≤ n) (f : SpaceTimePoint n → R) :
    IsLatticeSolution hn (fun p => f p.timeRev) ↔ IsLatticeSolution hn f :=
  ⟨fun h => by simpa using isLatticeSolution_timeRev h, isLatticeSolution_timeRev⟩

end Solutions

/-! ### Finite dependency recursion from a section and global uniqueness -/

section DependencyRecursion

variable {n : ℕ}

theorem SpaceTimePoint.odd_pred_t (p : SpaceTimePoint n) :
    Odd ((p.finX : ℤ) + p.finY + (p.t - 1)) := by
  rw [Int.odd_iff]; have := Int.even_iff.mp p.even_sum; simp; omega

theorem SpaceTimePoint.odd_succ_t (p : SpaceTimePoint n) :
    Odd ((p.finX : ℤ) + p.finY + (p.t + 1)) := by
  rw [Int.odd_iff]; have := Int.even_iff.mp p.even_sum; simp; omega

/-- Past vertical dependency `(x, y, t - 2)` of `p : SpaceTimePoint n`. -/
def pastVert (p : SpaceTimePoint n) : SpaceTimePoint n :=
  stencilBot p.finX p.finY (p.t - 1) p.odd_pred_t

/-- First past horizontal dependency `(q₁.1, q₁.2, t - 1)` of `p` in branch `b`. -/
def pastHoriz₁ (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) : SpaceTimePoint n :=
  stencilHoriz (manhattan_horizPair_fst hn b p.finX p.finY) (p.t - 1) p.odd_pred_t

/-- Second past horizontal dependency `(q₂.1, q₂.2, t - 1)` of `p` in branch `b`. -/
def pastHoriz₂ (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) : SpaceTimePoint n :=
  stencilHoriz (manhattan_horizPair_snd hn b p.finX p.finY) (p.t - 1) p.odd_pred_t

/-- Future vertical dependency `(x, y, t + 2)` of `p : SpaceTimePoint n`. -/
def futureVert (p : SpaceTimePoint n) : SpaceTimePoint n :=
  stencilTop p.finX p.finY (p.t + 1) p.odd_succ_t

/-- First future horizontal dependency `(q₁.1, q₁.2, t + 1)` of `p` in branch `b`. -/
def futureHoriz₁ (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) : SpaceTimePoint n :=
  stencilHoriz (manhattan_horizPair_fst hn b p.finX p.finY) (p.t + 1) p.odd_succ_t

/-- Second future horizontal dependency `(q₂.1, q₂.2, t + 1)` of `p` in branch `b`. -/
def futureHoriz₂ (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) : SpaceTimePoint n :=
  stencilHoriz (manhattan_horizPair_snd hn b p.finX p.finY) (p.t + 1) p.odd_succ_t

@[simp] theorem pastVert_x (p : SpaceTimePoint n) : (pastVert p).x = p.x := by simp [pastVert]
@[simp] theorem pastVert_y (p : SpaceTimePoint n) : (pastVert p).y = p.y := by simp [pastVert]
@[simp] theorem pastVert_t (p : SpaceTimePoint n) : (pastVert p).t = p.t - 2 := by
  simp [pastVert]; omega
@[simp] theorem pastVert_finX (p : SpaceTimePoint n) : (pastVert p).finX = p.finX := by
  ext; simp
@[simp] theorem pastVert_finY (p : SpaceTimePoint n) : (pastVert p).finY = p.finY := by
  ext; simp

@[simp] theorem pastHoriz₁_finX (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (pastHoriz₁ hn b p).finX = (horizPair hn b p.finX p.finY).1.1 := by simp [pastHoriz₁]
@[simp] theorem pastHoriz₁_finY (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (pastHoriz₁ hn b p).finY = (horizPair hn b p.finX p.finY).1.2 := by simp [pastHoriz₁]
@[simp] theorem pastHoriz₁_t (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (pastHoriz₁ hn b p).t = p.t - 1 := (rfl)

@[simp] theorem pastHoriz₂_finX (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (pastHoriz₂ hn b p).finX = (horizPair hn b p.finX p.finY).2.1 := by simp [pastHoriz₂]
@[simp] theorem pastHoriz₂_finY (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (pastHoriz₂ hn b p).finY = (horizPair hn b p.finX p.finY).2.2 := by simp [pastHoriz₂]
@[simp] theorem pastHoriz₂_t (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (pastHoriz₂ hn b p).t = p.t - 1 := (rfl)

@[simp] theorem futureVert_x (p : SpaceTimePoint n) : (futureVert p).x = p.x := by
  simp [futureVert]
@[simp] theorem futureVert_y (p : SpaceTimePoint n) : (futureVert p).y = p.y := by
  simp [futureVert]
@[simp] theorem futureVert_t (p : SpaceTimePoint n) : (futureVert p).t = p.t + 2 := by
  simp [futureVert]; omega
@[simp] theorem futureVert_finX (p : SpaceTimePoint n) : (futureVert p).finX = p.finX := by
  ext; simp
@[simp] theorem futureVert_finY (p : SpaceTimePoint n) : (futureVert p).finY = p.finY := by
  ext; simp

@[simp] theorem futureHoriz₁_finX (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (futureHoriz₁ hn b p).finX = (horizPair hn b p.finX p.finY).1.1 := by simp [futureHoriz₁]
@[simp] theorem futureHoriz₁_finY (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (futureHoriz₁ hn b p).finY = (horizPair hn b p.finX p.finY).1.2 := by simp [futureHoriz₁]
@[simp] theorem futureHoriz₁_t (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (futureHoriz₁ hn b p).t = p.t + 1 := (rfl)

@[simp] theorem futureHoriz₂_finX (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (futureHoriz₂ hn b p).finX = (horizPair hn b p.finX p.finY).2.1 := by simp [futureHoriz₂]
@[simp] theorem futureHoriz₂_finY (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (futureHoriz₂ hn b p).finY = (horizPair hn b p.finX p.finY).2.2 := by simp [futureHoriz₂]
@[simp] theorem futureHoriz₂_t (hn : 1 ≤ n) (b : Bool) (p : SpaceTimePoint n) :
    (futureHoriz₂ hn b p).t = p.t + 1 := (rfl)

/-- Well-founded recursion depth of `p : SpaceTimePoint n` relative to a section `S`: `0` on `S`,
and a strictly positive height offset above `S 0 0 - 2n` (when `S < t`) or below `S 0 0 + 2n`
(when `t < S`). -/
def sectionDepth (S : SpaceTimeSection n) (p : SpaceTimePoint n) : ℕ :=
  if p.t = S p.finX p.finY then 0
  else if S p.finX p.finY < p.t then (p.t - (S 0 0 - 2 * (n : ℤ)) + 1).toNat
  else ((S 0 0 + 2 * (n : ℤ)) - p.t + 1).toNat

private theorem section_bounds_origin (S : SpaceTimeSection n) (x y : Fin (n + 1)) :
    S 0 0 - 2 * (n : ℤ) ≤ S x y ∧ S x y ≤ S 0 0 + 2 * (n : ℤ) := by
  have hm := S.abs_sub_le_manhattan x y 0 0
  have hx := x.isLt; have hy := y.isLt
  have hnonneg : |(x : ℤ) - (0 : Fin (n + 1))| + |(y : ℤ) - (0 : Fin (n + 1))| ≤ 2 * (n : ℤ) := by
    simp only [Fin.val_zero, Nat.cast_zero, sub_zero, Nat.abs_cast]
    omega
  have habs := abs_le.mp (hm.trans hnonneg)
  omega

private theorem sectionDepth_lt_of_above {S : SpaceTimeSection n} {p r : SpaceTimePoint n}
    (hp : S p.finX p.finY < p.t) (hr_ge : S r.finX r.finY ≤ r.t) (hrt : r.t < p.t) :
    sectionDepth S r < sectionDepth S p := by
  have := (section_bounds_origin S p.finX p.finY).1
  have := (section_bounds_origin S r.finX r.finY).1
  have hp_ne : p.t ≠ S p.finX p.finY := by omega
  unfold sectionDepth
  simp only [hp_ne, hp, ↓reduceIte]
  by_cases hreq : r.t = S r.finX r.finY
  · simp only [hreq, ↓reduceIte]; omega
  · have hrlt : S r.finX r.finY < r.t := lt_of_le_of_ne hr_ge (Ne.symm hreq)
    simp only [hreq, hrlt, ↓reduceIte]; omega

private theorem sectionDepth_lt_of_below {S : SpaceTimeSection n} {p r : SpaceTimePoint n}
    (hp : p.t < S p.finX p.finY) (hr_le : r.t ≤ S r.finX r.finY) (hrt : p.t < r.t) :
    sectionDepth S r < sectionDepth S p := by
  have := (section_bounds_origin S p.finX p.finY).2
  have := (section_bounds_origin S r.finX r.finY).2
  have hp_ne : p.t ≠ S p.finX p.finY := by omega
  have hp_nlt : ¬ S p.finX p.finY < p.t := by omega
  unfold sectionDepth
  simp only [hp_ne, hp_nlt, ↓reduceIte]
  by_cases hreq : r.t = S r.finX r.finY
  · simp only [hreq, ↓reduceIte]; omega
  · have hrlt : ¬ S r.finX r.finY < r.t := by omega
    simp only [hreq, hrlt, ↓reduceIte]; omega

theorem section_le_pastVert {S : SpaceTimeSection n} {p : SpaceTimePoint n}
    (hp : S p.finX p.finY < p.t) :
    S (pastVert p).finX (pastVert p).finY ≤ (pastVert p).t := by
  have h2 := S.add_two_le_t_of_lt hp
  simp only [pastVert_finX, pastVert_finY, pastVert_t]; omega

theorem section_le_pastHoriz₁ (hn : 1 ≤ n) (b : Bool) {S : SpaceTimeSection n}
    {p : SpaceTimePoint n} (hp : S p.finX p.finY < p.t) :
    S (pastHoriz₁ hn b p).finX (pastHoriz₁ hn b p).finY ≤ (pastHoriz₁ hn b p).t := by
  have h2 := S.add_two_le_t_of_lt hp
  have hm := abs_le.mp (S.abs_sub_of_manhattan_eq_one
    (manhattan_horizPair_fst hn b p.finX p.finY)).le
  simp only [pastHoriz₁_finX, pastHoriz₁_finY, pastHoriz₁_t]; omega

theorem section_le_pastHoriz₂ (hn : 1 ≤ n) (b : Bool) {S : SpaceTimeSection n}
    {p : SpaceTimePoint n} (hp : S p.finX p.finY < p.t) :
    S (pastHoriz₂ hn b p).finX (pastHoriz₂ hn b p).finY ≤ (pastHoriz₂ hn b p).t := by
  have h2 := S.add_two_le_t_of_lt hp
  have hm := abs_le.mp (S.abs_sub_of_manhattan_eq_one
    (manhattan_horizPair_snd hn b p.finX p.finY)).le
  simp only [pastHoriz₂_finX, pastHoriz₂_finY, pastHoriz₂_t]; omega

theorem futureVert_le_section {S : SpaceTimeSection n} {p : SpaceTimePoint n}
    (hp : p.t < S p.finX p.finY) :
    (futureVert p).t ≤ S (futureVert p).finX (futureVert p).finY := by
  have h2 := S.t_add_two_le_of_lt hp
  simp only [futureVert_finX, futureVert_finY, futureVert_t]; omega

theorem futureHoriz₁_le_section (hn : 1 ≤ n) (b : Bool) {S : SpaceTimeSection n}
    {p : SpaceTimePoint n} (hp : p.t < S p.finX p.finY) :
    (futureHoriz₁ hn b p).t ≤ S (futureHoriz₁ hn b p).finX (futureHoriz₁ hn b p).finY := by
  have h2 := S.t_add_two_le_of_lt hp
  have hm := abs_le.mp (S.abs_sub_of_manhattan_eq_one
    (manhattan_horizPair_fst hn b p.finX p.finY)).le
  simp only [futureHoriz₁_finX, futureHoriz₁_finY, futureHoriz₁_t]; omega

theorem futureHoriz₂_le_section (hn : 1 ≤ n) (b : Bool) {S : SpaceTimeSection n}
    {p : SpaceTimePoint n} (hp : p.t < S p.finX p.finY) :
    (futureHoriz₂ hn b p).t ≤ S (futureHoriz₂ hn b p).finX (futureHoriz₂ hn b p).finY := by
  have h2 := S.t_add_two_le_of_lt hp
  have hm := abs_le.mp (S.abs_sub_of_manhattan_eq_one
    (manhattan_horizPair_snd hn b p.finX p.finY)).le
  simp only [futureHoriz₂_finX, futureHoriz₂_finY, futureHoriz₂_t]; omega

theorem sectionDepth_pastVert_lt {S : SpaceTimeSection n} {p : SpaceTimePoint n}
    (hp : S p.finX p.finY < p.t) : sectionDepth S (pastVert p) < sectionDepth S p :=
  sectionDepth_lt_of_above hp (section_le_pastVert hp) (by simp)

theorem sectionDepth_pastHoriz₁_lt (hn : 1 ≤ n) (b : Bool) {S : SpaceTimeSection n}
    {p : SpaceTimePoint n} (hp : S p.finX p.finY < p.t) :
    sectionDepth S (pastHoriz₁ hn b p) < sectionDepth S p :=
  sectionDepth_lt_of_above hp (section_le_pastHoriz₁ hn b hp) (by simp)

theorem sectionDepth_pastHoriz₂_lt (hn : 1 ≤ n) (b : Bool) {S : SpaceTimeSection n}
    {p : SpaceTimePoint n} (hp : S p.finX p.finY < p.t) :
    sectionDepth S (pastHoriz₂ hn b p) < sectionDepth S p :=
  sectionDepth_lt_of_above hp (section_le_pastHoriz₂ hn b hp) (by simp)

theorem sectionDepth_futureVert_lt {S : SpaceTimeSection n} {p : SpaceTimePoint n}
    (hp : p.t < S p.finX p.finY) : sectionDepth S (futureVert p) < sectionDepth S p :=
  sectionDepth_lt_of_below hp (futureVert_le_section hp) (by simp)

theorem sectionDepth_futureHoriz₁_lt (hn : 1 ≤ n) (b : Bool) {S : SpaceTimeSection n}
    {p : SpaceTimePoint n} (hp : p.t < S p.finX p.finY) :
    sectionDepth S (futureHoriz₁ hn b p) < sectionDepth S p :=
  sectionDepth_lt_of_below hp (futureHoriz₁_le_section hn b hp) (by simp)

theorem sectionDepth_futureHoriz₂_lt (hn : 1 ≤ n) (b : Bool) {S : SpaceTimeSection n}
    {p : SpaceTimePoint n} (hp : p.t < S p.finX p.finY) :
    sectionDepth S (futureHoriz₂ hn b p) < sectionDepth S p :=
  sectionDepth_lt_of_below hp (futureHoriz₂_le_section hn b hp) (by simp)

/-- Propagate section data `val : SectionState n R` on `S : SpaceTimeSection n` across all of
`SpaceTimePoint n` (`1 ≤ n`) by finite dependency recursion. -/
def extendSection {R : Type*} [AddCommGroup R] [LinearOrder R] (hn : 1 ≤ n)
    (S : SpaceTimeSection n) (val : SectionState n R) (p : SpaceTimePoint n) : R :=
  if h_eq : p.t = S p.finX p.finY then
    val p.finX p.finY
  else if h_gt : S p.finX p.finY < p.t then
    have := sectionDepth_pastHoriz₁_lt hn false h_gt
    have := sectionDepth_pastHoriz₂_lt hn false h_gt
    have := sectionDepth_pastHoriz₁_lt hn true h_gt
    have := sectionDepth_pastHoriz₂_lt hn true h_gt
    have := sectionDepth_pastVert_lt h_gt
    max (extendSection hn S val (pastHoriz₁ hn false p) +
          extendSection hn S val (pastHoriz₂ hn false p))
        (extendSection hn S val (pastHoriz₁ hn true p) +
          extendSection hn S val (pastHoriz₂ hn true p)) -
      extendSection hn S val (pastVert p)
  else
    have h_lt : p.t < S p.finX p.finY := lt_of_le_of_ne (not_lt.mp h_gt) h_eq
    have := sectionDepth_futureHoriz₁_lt hn false h_lt
    have := sectionDepth_futureHoriz₂_lt hn false h_lt
    have := sectionDepth_futureHoriz₁_lt hn true h_lt
    have := sectionDepth_futureHoriz₂_lt hn true h_lt
    have := sectionDepth_futureVert_lt h_lt
    max (extendSection hn S val (futureHoriz₁ hn false p) +
          extendSection hn S val (futureHoriz₂ hn false p))
        (extendSection hn S val (futureHoriz₁ hn true p) +
          extendSection hn S val (futureHoriz₂ hn true p)) -
      extendSection hn S val (futureVert p)
termination_by sectionDepth S p

section ExtendProps

variable {R : Type*} [AddCommGroup R] [LinearOrder R] (hn : 1 ≤ n)
  (S : SpaceTimeSection n) (val : SectionState n R)

theorem extendSection_of_eq {p : SpaceTimePoint n} (h : p.t = S p.finX p.finY) :
    extendSection hn S val p = val p.finX p.finY := by
  rw [extendSection]; simp only [h, ↓reduceDIte]

@[simp] theorem extendSection_point (x y : Fin (n + 1)) :
    extendSection hn S val (S.point x y) = val x y := by
  rw [extendSection_of_eq hn S val (by simp), S.point_finX, S.point_finY]

theorem extendSection_of_gt {p : SpaceTimePoint n} (h : S p.finX p.finY < p.t) :
    extendSection hn S val p =
      max (extendSection hn S val (pastHoriz₁ hn false p) +
            extendSection hn S val (pastHoriz₂ hn false p))
          (extendSection hn S val (pastHoriz₁ hn true p) +
            extendSection hn S val (pastHoriz₂ hn true p)) -
        extendSection hn S val (pastVert p) := by
  have hne : p.t ≠ S p.finX p.finY := ne_of_gt h
  rw [extendSection]; simp only [hne, h, ↓reduceDIte]

theorem extendSection_of_lt {p : SpaceTimePoint n} (h : p.t < S p.finX p.finY) :
    extendSection hn S val p =
      max (extendSection hn S val (futureHoriz₁ hn false p) +
            extendSection hn S val (futureHoriz₂ hn false p))
          (extendSection hn S val (futureHoriz₁ hn true p) +
            extendSection hn S val (futureHoriz₂ hn true p)) -
        extendSection hn S val (futureVert p) := by
  have hne : p.t ≠ S p.finX p.finY := ne_of_lt h
  have hngt : ¬ S p.finX p.finY < p.t := not_lt.mpr h.le
  rw [extendSection]; simp only [hne, hngt, ↓reduceDIte]

/-- `extendSection hn S val` satisfies the bounded octahedron recurrence at every odd stencil
center in `SpaceTimePoint n`. -/
theorem isLatticeSolution_extendSection : IsLatticeSolution hn (extendSection hn S val) := by
  intro x y t₀ hodd
  have hS := Int.even_iff.mp (S.even_sum x y)
  have ho := Int.odd_iff.mp hodd
  rcases (by omega : S x y ≤ t₀ - 1 ∨ t₀ + 1 ≤ S x y) with h_abv | h_blw
  · set top := stencilTop x y t₀ hodd
    have hgt : S top.finX top.finY < top.t := by simp [top]; omega
    rw [extendSection_of_gt hn S val hgt]
    have hv : pastVert top = stencilBot x y t₀ hodd := by ext <;> simp [top]; omega
    have hh1 (b : Bool) : pastHoriz₁ hn b top =
        stencilHoriz (manhattan_horizPair_fst hn b x y) t₀ hodd := by
      ext <;> simp [pastHoriz₁, top]
    have hh2 (b : Bool) : pastHoriz₂ hn b top =
        stencilHoriz (manhattan_horizPair_snd hn b x y) t₀ hodd := by
      ext <;> simp [pastHoriz₂, top]
    simp only [hv, hh1, hh2, latticeBranchSum]
  · have hlt : (stencilBot x y t₀ hodd).t <
        S (stencilBot x y t₀ hodd).finX (stencilBot x y t₀ hodd).finY := by simp; omega
    have hstep := extendSection_of_lt hn S val hlt
    have hv : futureVert (stencilBot x y t₀ hodd) = stencilTop x y t₀ hodd := by
      ext <;> simp; omega
    have hh1 (b : Bool) : futureHoriz₁ hn b (stencilBot x y t₀ hodd) =
        stencilHoriz (manhattan_horizPair_fst hn b x y) t₀ hodd := by
      ext <;> simp [futureHoriz₁]
    have hh2 (b : Bool) : futureHoriz₂ hn b (stencilBot x y t₀ hodd) =
        stencilHoriz (manhattan_horizPair_snd hn b x y) t₀ hodd := by
      ext <;> simp [futureHoriz₂]
    simp only [hv, hh1, hh2] at hstep
    rw [hstep, latticeBranchSum, latticeBranchSum, sub_sub_cancel]

/-- Any global lattice solution `f` is uniquely determined by its restriction to `S`. -/
theorem eq_extendSection_of_isLatticeSolution {f : SpaceTimePoint n → R}
    (hf : IsLatticeSolution hn f) (p : SpaceTimePoint n) :
    f p = extendSection hn S (fun x y => f (S.point x y)) p := by
  induction p using (measure (sectionDepth S)).wf.induction with
  | h p ih =>
    rcases lt_trichotomy p.t (S p.finX p.finY) with hlt | heq | hgt
    · rw [extendSection_of_lt hn S _ hlt]
      have hsol := hf p.finX p.finY (p.t + 1) p.odd_succ_t
      have hbot : stencilBot p.finX p.finY (p.t + 1) p.odd_succ_t = p := by ext <;> simp
      have htop : stencilTop p.finX p.finY (p.t + 1) p.odd_succ_t = futureVert p := rfl
      rw [hbot, htop] at hsol
      have hinv : f p = max (latticeBranchSum hn f false p.finX p.finY (p.t + 1) p.odd_succ_t)
          (latticeBranchSum hn f true p.finX p.finY (p.t + 1) p.odd_succ_t) - f (futureVert p) := by
        rw [hsol, sub_sub_cancel]
      rw [hinv]
      exact congrArg₂ (· - ·)
        (congrArg₂ max
          (congrArg₂ (· + ·) (ih _ (sectionDepth_futureHoriz₁_lt hn false hlt))
            (ih _ (sectionDepth_futureHoriz₂_lt hn false hlt)))
          (congrArg₂ (· + ·) (ih _ (sectionDepth_futureHoriz₁_lt hn true hlt))
            (ih _ (sectionDepth_futureHoriz₂_lt hn true hlt))))
        (ih _ (sectionDepth_futureVert_lt hlt))
    · rw [extendSection_of_eq hn S _ heq]
      congr 1; ext <;> simp [heq]
    · rw [extendSection_of_gt hn S _ hgt]
      have hsol := hf p.finX p.finY (p.t - 1) p.odd_pred_t
      have htop : stencilTop p.finX p.finY (p.t - 1) p.odd_pred_t = p := by ext <;> simp
      have hbot : stencilBot p.finX p.finY (p.t - 1) p.odd_pred_t = pastVert p := rfl
      rw [htop, hbot] at hsol
      rw [hsol]
      exact congrArg₂ (· - ·)
        (congrArg₂ max
          (congrArg₂ (· + ·) (ih _ (sectionDepth_pastHoriz₁_lt hn false hgt))
            (ih _ (sectionDepth_pastHoriz₂_lt hn false hgt)))
          (congrArg₂ (· + ·) (ih _ (sectionDepth_pastHoriz₁_lt hn true hgt))
            (ih _ (sectionDepth_pastHoriz₂_lt hn true hgt))))
        (ih _ (sectionDepth_pastVert_lt hgt))

/-- Time-reversing the section `-S` conjugates `extendSection` by `SpaceTimePoint.timeRev`. -/
theorem extendSection_neg (p : SpaceTimePoint n) :
    extendSection hn (-S) val p = extendSection hn S val p.timeRev := by
  have hf := isLatticeSolution_timeRev (isLatticeSolution_extendSection hn S val)
  have heq := eq_extendSection_of_isLatticeSolution hn (-S) hf p
  simpa using heq.symm

/-- Order-preserving additive monoid homomorphisms (such as `ℤ →+o ℝ`) commute with
`extendSection`. -/
theorem map_extendSection {R' : Type*} [AddCommGroup R'] [LinearOrder R']
    (φ : R →+o R') (p : SpaceTimePoint n) :
    φ (extendSection hn S val p) = extendSection hn S (fun x y => φ (val x y)) p := by
  have hsol : IsLatticeSolution hn (fun q => φ (extendSection hn S val q)) := by
    intro x y t₀ hodd
    have h := isLatticeSolution_extendSection hn S val x y t₀ hodd
    simpa [latticeBranchSum, map_sub, map_add, OrderHomClass.mono φ |>.map_max] using congrArg φ h
  simpa using eq_extendSection_of_isLatticeSolution hn S hsol p

/-- Nonnegative scalar multiplication commutes with `extendSection` (positive homogeneity). -/
theorem extendSection_smul_of_nonneg {K : Type*} [Semiring K] [PartialOrder K]
    [Module K R] [PosSMulMono K R] {c : K} (hc : 0 ≤ c) (p : SpaceTimePoint n) :
    extendSection hn S (c • val) p = c • extendSection hn S val p := by
  have hmono : Monotone (fun r : R => c • r) := fun _ _ h => smul_le_smul_of_nonneg_left h hc
  have hsol : IsLatticeSolution hn (fun q => c • extendSection hn S val q) := by
    intro x y t₀ hodd
    have h := isLatticeSolution_extendSection hn S val x y t₀ hodd
    simpa [latticeBranchSum, smul_sub, smul_add, hmono.map_max] using congrArg (c • ·) h
  have hinit : (fun x y => c • extendSection hn S val (S.point x y)) = c • val := by
    ext x y; simp
  exact hinit ▸ (eq_extendSection_of_isLatticeSolution hn S hsol p).symm

end ExtendProps

/-! ### Invertible section-to-section transition maps -/

section Transition

variable {R : Type*} [AddCommGroup R] [LinearOrder R] (hn : 1 ≤ n)

/-- State-transition equivalence from section `S₁` to section `S₂` induced by the bounded
octahedron recurrence (`1 ≤ n`). -/
def sectionTransition (S₁ S₂ : SpaceTimeSection n) : SectionState n R ≃ SectionState n R where
  toFun val x y := extendSection hn S₁ val (S₂.point x y)
  invFun val x y := extendSection hn S₂ val (S₁.point x y)
  left_inv val := by
    funext x y
    have h := eq_extendSection_of_isLatticeSolution hn S₂
      (isLatticeSolution_extendSection hn S₁ val) (S₁.point x y)
    simpa using h.symm
  right_inv val := by
    funext x y
    have h := eq_extendSection_of_isLatticeSolution hn S₁
      (isLatticeSolution_extendSection hn S₂ val) (S₂.point x y)
    simpa using h.symm

@[simp] theorem sectionTransition_apply (S₁ S₂ : SpaceTimeSection n) (val : SectionState n R)
    (x y : Fin (n + 1)) :
    sectionTransition hn S₁ S₂ val x y = extendSection hn S₁ val (S₂.point x y) := (rfl)

@[simp] theorem sectionTransition_refl (S : SpaceTimeSection n) :
    sectionTransition hn S S = Equiv.refl (SectionState n R) := by
  ext val x y; simp

@[simp] theorem sectionTransition_symm (S₁ S₂ : SpaceTimeSection n) :
    (sectionTransition hn S₁ S₂ (R := R)).symm = sectionTransition hn S₂ S₁ := (rfl)

@[simp] theorem sectionTransition_trans (S₁ S₂ S₃ : SpaceTimeSection n) :
    (sectionTransition hn S₁ S₂ (R := R)).trans (sectionTransition hn S₂ S₃) =
      sectionTransition hn S₁ S₃ := by
  ext val x y
  exact (eq_extendSection_of_isLatticeSolution hn S₂
    (isLatticeSolution_extendSection hn S₁ val) (S₃.point x y)).symm

@[simp] theorem sectionTransition_neg (S₁ S₂ : SpaceTimeSection n) :
    sectionTransition hn (-S₁) (-S₂) (R := R) = sectionTransition hn S₁ S₂ := by
  ext val x y
  simp [extendSection_neg]

end Transition

end DependencyRecursion

end TauCeti.Hive
