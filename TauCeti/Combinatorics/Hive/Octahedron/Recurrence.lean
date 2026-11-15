/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import TauCeti.Combinatorics.Hive.Octahedron.Lattice
public import TauCeti.Topology.PL.Map
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The bounded octahedron recurrence and associator excavation

Henriques and Kamnitzer formulate the tropical **bounded octahedron recurrence** on the parity
lattice `SpaceTime n = {(x, y, t) ∈ [0, n]² × ℤ : x + y + t ≡ 0 (mod 2)}` (`n ≥ 1`): for every
`(x, y, t) ∈ [0, n]² × ℤ` with `x + y + t` odd,
* in the spatial interior (`0 < x < n` and `0 < y < n`),
  `f(x, y, t + 1) + f(x, y, t - 1) =`
  `max(f(x + 1, y, t) + f(x - 1, y, t), f(x, y + 1, t) + f(x, y - 1, t))`;
* on a non-corner spatial wall (`y ∈ {0, n}` with `0 < x < n`, or `x ∈ {0, n}` with `0 < y < n`),
  the out-of-range pair is omitted rather than maximized with `0`;
* at the four spatial corners `(0, 0), (0, n), (n, 0), (n, n)`, the sum is taken over the two
  in-bounds unit spatial neighbours.

Every function `g : [0, n]² → R` on a spacelike section `τ : Section n` extends uniquely to a
global solution `extendSection hn τ g : SpaceTime n → R` of the bounded recurrence, yielding an
invertible section-to-section transition `Section.transitionEquiv hn τ₁ τ₂`. Whenever `τ₁ ≤ τ₂`,
`τ₁` can be excavated to `τ₂` through a finite sequence of legal local-minimum `+2` updates
(`Section.ExcavationSchedule`), each inducing the single-site involution `excavateAt hn p`;
uniqueness of extension makes the composite transition independent of the chosen schedule.

Specializing to `[lowerSection n, upperSection n]` defines `associatorSectionEquiv n` (the identity
for `n ≤ 1`). Every excavation inside the associator region occurs at a strictly interior grid site
(`IsInteriorPos p`), so all spatial wall values are fixed
(`associatorSectionEquiv_apply_of_isWallPos`) and all four exterior hive boundaries `(μ, ν)` and
`(λ, π*)` together with corner normalizations are preserved. Over `ℝ`, every single-site excavation
and every section-to-section transition is globally piecewise affine
(`TauCeti.IsPiecewiseAffineOn · Set.univ`) and hence a homeomorphism. Finally, at rank `n = 2` on
`glueLower exampleTwo.reflect detTwo`, the `max` rule produces two valid output hives while
replacing `max` by `min` fails rhombus concavity with slack `-1`.

## Main definitions

* `TauCeti.Hive.spatialEquatorialSum`, `TauCeti.Hive.equatorialSum`,
  `TauCeti.Hive.SatisfiesRecurrence`: tropical equatorial sums and Henriques–Kamnitzer eq. (5).
* `TauCeti.Hive.extendSection`, `TauCeti.Hive.Section.solutionEquiv`,
  `TauCeti.Hive.Section.transitionEquiv`: unique extension from a spacelike section and invertible
  transitions between arbitrary sections.
* `TauCeti.Hive.Section.IsExcavationAt`, `TauCeti.Hive.Section.excavate`,
  `TauCeti.Hive.excavateAt`, `TauCeti.Hive.Section.ExcavationSchedule`,
  `TauCeti.Hive.Section.canonicalSchedule`: unit-cell excavations and legal schedules.
* `TauCeti.Hive.associatorSectionEquiv`, `TauCeti.Hive.associatorSectionHomeomorph`: full
  associator excavation from `lowerSection n` to `upperSection n`.

## Main results

* `TauCeti.Hive.satisfiesRecurrence_extendSection`,
  `TauCeti.Hive.SatisfiesRecurrence.eq_of_eq_on_section`: existence and uniqueness of global
  extensions.
* `TauCeti.Hive.Section.ExcavationSchedule.eval_eq_transitionEquiv`: schedule independence of
  excavated transitions.
* `TauCeti.Hive.isInteriorPos_of_excavate_le_upperSection`,
  `TauCeti.Hive.associatorSectionEquiv_apply_of_isWallPos`: interior confinement and spatial wall
  invariance across the associator region.
* `TauCeti.Hive.Section.isPiecewiseAffineOn_transitionEquiv`,
  `TauCeti.Hive.isPiecewiseAffineOn_associatorSectionEquiv`: global piecewise affineness over `ℝ`.
* `TauCeti.Hive.max_vs_min_counterexample_two`: rank-`2` chirality check distinguishing `max` from
  `min`.

## References

* A. Henriques and J. Kamnitzer, *Crystals and coboundary categories*, Duke Math. J. **132**
  (2006), 191–266, §3.1, equation (5), and Lemma 3.1.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §5.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### Equatorial sums and the bounded octahedron recurrence -/

section Recurrence

variable {n : ℕ} {R : Type*} [Lattice R] [AddCommGroup R]

/-- Tropical equatorial sum on a spatial slice `s : [0, n]² → R` (`1 ≤ n`) at grid site `p`:
maximum of the two opposite-neighbour sums in the interior, the single in-bounds opposite pair on
each non-corner wall, and the sum of the two in-bounds unit neighbours at each corner. -/
def spatialEquatorialSum (hn : 1 ≤ n) (s : Fin (n + 1) × Fin (n + 1) → R)
    (p : Fin (n + 1) × Fin (n + 1)) : R :=
  if hx : 0 < p.1.val ∧ p.1.val < n then
    if hy : 0 < p.2.val ∧ p.2.val < n then
      (s (⟨p.1.val + 1, by omega⟩, p.2) + s (⟨p.1.val - 1, by omega⟩, p.2)) ⊔
        (s (p.1, ⟨p.2.val + 1, by omega⟩) + s (p.1, ⟨p.2.val - 1, by omega⟩))
    else
      s (⟨p.1.val + 1, by omega⟩, p.2) + s (⟨p.1.val - 1, by omega⟩, p.2)
  else if hy : 0 < p.2.val ∧ p.2.val < n then
    s (p.1, ⟨p.2.val + 1, by omega⟩) + s (p.1, ⟨p.2.val - 1, by omega⟩)
  else if hx0 : p.1.val = 0 then
    if hy0 : p.2.val = 0 then
      s (⟨p.1.val + 1, by omega⟩, p.2) + s (p.1, ⟨p.2.val + 1, by omega⟩)
    else
      s (⟨p.1.val + 1, by omega⟩, p.2) + s (p.1, ⟨p.2.val - 1, by have := p.2.isLt; omega⟩)
  else
    if hy0 : p.2.val = 0 then
      s (⟨p.1.val - 1, by have := p.1.isLt; omega⟩, p.2) + s (p.1, ⟨p.2.val + 1, by omega⟩)
    else
      s (⟨p.1.val - 1, by have := p.1.isLt; omega⟩, p.2) +
        s (p.1, ⟨p.2.val - 1, by have := p.2.isLt; omega⟩)

/-- At a strictly interior grid site `(x, y)`, `spatialEquatorialSum` takes `⊔` over the two
opposite-neighbour pairs. -/
theorem spatialEquatorialSum_interior (hn : 1 ≤ n) (s : Fin (n + 1) × Fin (n + 1) → R)
    {p : Fin (n + 1) × Fin (n + 1)} (hp : IsInteriorPos p) :
    spatialEquatorialSum hn s p =
      (s (⟨p.1.val + 1, by have := (isInteriorPos_def p).mp hp; omega⟩, p.2) +
          s (⟨p.1.val - 1, by have := (isInteriorPos_def p).mp hp; omega⟩, p.2)) ⊔
        (s (p.1, ⟨p.2.val + 1, by have := (isInteriorPos_def p).mp hp; omega⟩) +
          s (p.1, ⟨p.2.val - 1, by have := (isInteriorPos_def p).mp hp; omega⟩)) := by
  obtain ⟨hx0, hxn, hy0, hyn⟩ := (isInteriorPos_def p).mp hp
  simp [spatialEquatorialSum, hx0, hxn, hy0, hyn]

/-- Along the bottom wall `y = 0` (`0 < x < n`), `spatialEquatorialSum` omits the out-of-range
`y`-neighbours and evaluates to `s(x + 1, 0) + s(x - 1, 0)` without a `⊔`. -/
theorem spatialEquatorialSum_wall_y_zero (hn : 1 ≤ n) (s : Fin (n + 1) × Fin (n + 1) → R)
    {x : Fin (n + 1)} (hx0 : 0 < x.val) (hxn : x.val < n) :
    spatialEquatorialSum hn s (x, 0) =
      s (⟨x.val + 1, by omega⟩, 0) + s (⟨x.val - 1, by omega⟩, 0) := by
  simp [spatialEquatorialSum, hx0, hxn]

/-- `spatialEquatorialSum hn s p` depends only on the values of `s` at unit grid neighbours of `p`.
-/
theorem spatialEquatorialSum_congr (hn : 1 ≤ n) {s₁ s₂ : Fin (n + 1) × Fin (n + 1) → R}
    {p : Fin (n + 1) × Fin (n + 1)} (h : ∀ q, IsGridAdj p q → s₁ q = s₂ q) :
    spatialEquatorialSum hn s₁ p = spatialEquatorialSum hn s₂ p := by
  have hxlt := p.1.isLt
  have hylt := p.2.isLt
  have hxp (hc : p.1.val < n) : s₁ (⟨p.1.val + 1, by omega⟩, p.2) =
      s₂ (⟨p.1.val + 1, by omega⟩, p.2) :=
    h _ ((isGridAdj_def _ _).mpr (by simp))
  have hxm (hc : 0 < p.1.val) : s₁ (⟨p.1.val - 1, by omega⟩, p.2) =
      s₂ (⟨p.1.val - 1, by omega⟩, p.2) := by
    refine h _ ((isGridAdj_def _ _).mpr ?_)
    have hp1 : (p.1.val : ℤ) - ((p.1.val - 1 : ℕ) : ℤ) = 1 := by omega
    simp [hp1]
  have hyp (hc : p.2.val < n) : s₁ (p.1, ⟨p.2.val + 1, by omega⟩) =
      s₂ (p.1, ⟨p.2.val + 1, by omega⟩) :=
    h _ ((isGridAdj_def _ _).mpr (by simp))
  have hym (hc : 0 < p.2.val) : s₁ (p.1, ⟨p.2.val - 1, by omega⟩) =
      s₂ (p.1, ⟨p.2.val - 1, by omega⟩) := by
    refine h _ ((isGridAdj_def _ _).mpr ?_)
    have hp1 : (p.2.val : ℤ) - ((p.2.val - 1 : ℕ) : ℤ) = 1 := by omega
    simp [hp1]
  unfold spatialEquatorialSum
  split_ifs with hx hy hy' hx0 hy0 hy0'
  · rw [hxp hx.2, hxm hx.1, hyp hy.2, hym hy.1]
  · rw [hxp hx.2, hxm hx.1]
  · rw [hyp hy'.2, hym hy'.1]
  · rw [hxp (by omega), hyp (by omega)]
  · rw [hxp (by omega), hym (by omega)]
  · rw [hxm (by omega), hyp (by omega)]
  · rw [hxm (by omega), hym (by omega)]

/-- Unit spatial neighbours of an odd space-time center `(p.1, p.2, t)` lie on `SpaceTime n`. -/
theorem even_of_odd_isGridAdj {p q : Fin (n + 1) × Fin (n + 1)} {t : ℤ}
    (hodd : Odd ((p.1.val : ℤ) + p.2.val + t)) (hadj : IsGridAdj p q) :
    Even ((q.1.val : ℤ) + q.2.val + t) := by
  have h1 := Int.odd_iff.mp hodd
  have h2 := Int.odd_iff.mp hadj.odd_sum_sub
  rw [Int.even_iff]; omega

/-- Spatial slice of `f : SpaceTime n → R` at integer time `t` (defaulting to `0` off the parity
sublattice; at odd centers `(x, y, t)`, every unit spatial neighbour lies on the sublattice). -/
def sliceAt (f : SpaceTime n → R) (t : ℤ) (q : Fin (n + 1) × Fin (n + 1)) : R :=
  if hev : Even ((q.1.val : ℤ) + q.2.val + t) then f ⟨q.1, q.2, t, hev⟩ else 0

omit [Lattice R] in
theorem sliceAt_of_odd_adj (f : SpaceTime n → R) {p q : Fin (n + 1) × Fin (n + 1)} {t : ℤ}
    (hodd : Odd ((p.1.val : ℤ) + p.2.val + t)) (hadj : IsGridAdj p q) :
    ∃ hev : Even ((q.1.val : ℤ) + q.2.val + t), sliceAt f t q = f ⟨q.1, q.2, t, hev⟩ :=
  ⟨even_of_odd_isGridAdj hodd hadj, by simp [sliceAt, even_of_odd_isGridAdj hodd hadj]⟩

/-- Space-time equatorial tropical sum at `(x, y, t)` for `f : SpaceTime n → R`. -/
def equatorialSum (hn : 1 ≤ n) (f : SpaceTime n → R) (x y : Fin (n + 1)) (t : ℤ) : R :=
  spatialEquatorialSum hn (sliceAt f t) (x, y)

theorem equatorialSum_def (hn : 1 ≤ n) (f : SpaceTime n → R) (x y : Fin (n + 1)) (t : ℤ) :
    equatorialSum hn f x y t = spatialEquatorialSum hn (sliceAt f t) (x, y) := (rfl)

/-- Explicit interior formula for `equatorialSum` when `x + y + t` is odd. -/
theorem equatorialSum_interior (hn : 1 ≤ n) (f : SpaceTime n → R) {x y : Fin (n + 1)} {t : ℤ}
    (hp : IsInteriorPos (x, y)) (hodd : Odd ((x.val : ℤ) + y.val + t)) :
    equatorialSum hn f x y t =
      (f ⟨⟨x.val + 1, by have h := (isInteriorPos_def (x, y)).mp hp; dsimp only at h; omega⟩, y, t,
          by have := Int.odd_iff.mp hodd; rw [Int.even_iff]; push_cast; omega⟩ +
        f ⟨⟨x.val - 1, by have h := (isInteriorPos_def (x, y)).mp hp; dsimp only at h; omega⟩, y, t,
          by
            have h := ((isInteriorPos_def (x, y)).mp hp).1; dsimp only at h
            have := Int.odd_iff.mp hodd; rw [Int.even_iff]; dsimp only; omega⟩) ⊔
      (f ⟨x, ⟨y.val + 1, by have h := (isInteriorPos_def (x, y)).mp hp; dsimp only at h; omega⟩, t,
          by have := Int.odd_iff.mp hodd; rw [Int.even_iff]; push_cast; omega⟩ +
        f ⟨x, ⟨y.val - 1, by have h := (isInteriorPos_def (x, y)).mp hp; dsimp only at h; omega⟩, t,
          by
            have h := ((isInteriorPos_def (x, y)).mp hp).2.2.1; dsimp only at h
            have := Int.odd_iff.mp hodd; rw [Int.even_iff]; dsimp only; omega⟩) := by
  obtain ⟨hx0, _, hy0, _⟩ := (isInteriorPos_def (x, y)).mp hp
  dsimp only at hx0 hy0
  have hodd' := Int.odd_iff.mp hodd
  have hev1 : Even (((x.val + 1 : ℕ) : ℤ) + y.val + t) := by rw [Int.even_iff]; push_cast; omega
  have hev2 : Even (((x.val - 1 : ℕ) : ℤ) + y.val + t) := by rw [Int.even_iff]; omega
  have hev3 : Even ((x.val : ℤ) + (y.val + 1 : ℕ) + t) := by rw [Int.even_iff]; push_cast; omega
  have hev4 : Even ((x.val : ℤ) + (y.val - 1 : ℕ) + t) := by rw [Int.even_iff]; omega
  rw [equatorialSum, spatialEquatorialSum_interior hn _ hp]
  simp only [sliceAt, hev1, hev2, hev3, hev4, ↓reduceDIte]

/-- Explicit bottom-wall (`y = 0`, `0 < x < n`) formula for `equatorialSum`: only the single
in-bounds pair `f(x + 1, 0, t) + f(x - 1, 0, t)` appears, with no `⊔`. -/
theorem equatorialSum_wall_y_zero (hn : 1 ≤ n) (f : SpaceTime n → R) {x : Fin (n + 1)} {t : ℤ}
    (hx0 : 0 < x.val) (hxn : x.val < n) (hodd : Odd ((x.val : ℤ) + 0 + t)) :
    equatorialSum hn f x 0 t =
      f ⟨⟨x.val + 1, by omega⟩, 0, t,
          by have := Int.odd_iff.mp hodd; rw [Int.even_iff]; simp; omega⟩ +
        f ⟨⟨x.val - 1, by omega⟩, 0, t,
          by have := Int.odd_iff.mp hodd; rw [Int.even_iff]; simp; omega⟩ := by
  have hodd' := Int.odd_iff.mp hodd
  have hev1 : Even (((x.val + 1 : ℕ) : ℤ) + (0 : Fin (n + 1)).val + t) := by
    rw [Int.even_iff]; simp; omega
  have hev2 : Even (((x.val - 1 : ℕ) : ℤ) + (0 : Fin (n + 1)).val + t) := by
    rw [Int.even_iff]; simp; omega
  rw [equatorialSum, spatialEquatorialSum_wall_y_zero hn _ hx0 hxn]
  simp only [sliceAt, hev1, hev2, ↓reduceDIte]

/-- The upper apex `(x, y, t + 1)` of the unit octahedron centered at `(x, y, t)`. -/
def SpaceTime.northPole {n : ℕ} (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : SpaceTime n :=
  ⟨x, y, t + 1, by have := Int.odd_iff.mp hodd; rw [Int.even_iff]; omega⟩

/-- The lower apex `(x, y, t - 1)` of the unit octahedron centered at `(x, y, t)`. -/
def SpaceTime.southPole {n : ℕ} (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : SpaceTime n :=
  ⟨x, y, t - 1, by have := Int.odd_iff.mp hodd; rw [Int.even_iff]; omega⟩

@[simp] theorem SpaceTime.northPole_x {n : ℕ} (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : (northPole x y t hodd).x = x := (rfl)
@[simp] theorem SpaceTime.northPole_y {n : ℕ} (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : (northPole x y t hodd).y = y := (rfl)
@[simp] theorem SpaceTime.northPole_t {n : ℕ} (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : (northPole x y t hodd).t = t + 1 := (rfl)

@[simp] theorem SpaceTime.southPole_x {n : ℕ} (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : (southPole x y t hodd).x = x := (rfl)
@[simp] theorem SpaceTime.southPole_y {n : ℕ} (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : (southPole x y t hodd).y = y := (rfl)
@[simp] theorem SpaceTime.southPole_t {n : ℕ} (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : (southPole x y t hodd).t = t - 1 := (rfl)

/-- Henriques–Kamnitzer's bounded octahedron recurrence (equation (5)): at every odd space-time
center `(x, y, t)`, `f(x, y, t + 1) + f(x, y, t - 1) = equatorialSum hn f x y t`. -/
def SatisfiesRecurrence (hn : 1 ≤ n) (f : SpaceTime n → R) : Prop :=
  ∀ (x y : Fin (n + 1)) (t : ℤ) (hodd : Odd ((x.val : ℤ) + y.val + t)),
    f (SpaceTime.northPole x y t hodd) + f (SpaceTime.southPole x y t hodd) =
      equatorialSum hn f x y t

theorem satisfiesRecurrence_def (hn : 1 ≤ n) (f : SpaceTime n → R) :
    SatisfiesRecurrence hn f ↔
      ∀ (x y : Fin (n + 1)) (t : ℤ) (hodd : Odd ((x.val : ℤ) + y.val + t)),
        f (SpaceTime.northPole x y t hodd) + f (SpaceTime.southPole x y t hodd) =
          equatorialSum hn f x y t := Iff.rfl

theorem SatisfiesRecurrence.northPole_eq {hn : 1 ≤ n} {f : SpaceTime n → R}
    (hf : SatisfiesRecurrence hn f) (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) :
    f (SpaceTime.northPole x y t hodd) =
      equatorialSum hn f x y t - f (SpaceTime.southPole x y t hodd) :=
  eq_sub_of_add_eq (hf x y t hodd)

theorem SatisfiesRecurrence.southPole_eq {hn : 1 ≤ n} {f : SpaceTime n → R}
    (hf : SatisfiesRecurrence hn f) (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) :
    f (SpaceTime.southPole x y t hodd) =
      equatorialSum hn f x y t - f (SpaceTime.northPole x y t hodd) :=
  eq_sub_of_add_eq ((add_comm _ _).trans (hf x y t hodd))

/-- Time reversal `(x, y, t) ↦ (x, y, -t)` preserves `SatisfiesRecurrence` because north and south
poles enter symmetrically. -/
theorem satisfiesRecurrence_comp_timeRev_iff (hn : 1 ≤ n) (f : SpaceTime n → R) :
    SatisfiesRecurrence hn (f ∘ SpaceTime.timeRev) ↔ SatisfiesRecurrence hn f := by
  have aux : ∀ g : SpaceTime n → R, SatisfiesRecurrence hn g →
      SatisfiesRecurrence hn (g ∘ SpaceTime.timeRev) := by
    intro g hg x y t hodd
    have hodd' : Odd ((x.val : ℤ) + y.val + -t) := by
      have := Int.odd_iff.mp hodd; rw [Int.odd_iff]; omega
    have hnp : (SpaceTime.northPole x y t hodd).timeRev = SpaceTime.southPole x y (-t) hodd' := by
      (ext <;> simp); ring
    have hsp : (SpaceTime.southPole x y t hodd).timeRev = SpaceTime.northPole x y (-t) hodd' := by
      (ext <;> simp); ring
    have heq : equatorialSum hn (g ∘ SpaceTime.timeRev) x y t = equatorialSum hn g x y (-t) := by
      refine spatialEquatorialSum_congr hn fun q hadj => ?_
      have hev1 := even_of_odd_isGridAdj (p := (x, y)) hodd hadj
      have hev2 := even_of_odd_isGridAdj (p := (x, y)) hodd' hadj
      simp only [sliceAt, hev1, hev2, ↓reduceDIte, Function.comp_apply]
      congr 1; ext <;> simp
    simp only [Function.comp_apply, hnp, hsp, heq]
    rw [add_comm]
    exact hg x y (-t) hodd'
  refine ⟨fun h => ?_, aux f⟩
  have h2 := aux (f ∘ SpaceTime.timeRev) h
  have hcomp : (f ∘ SpaceTime.timeRev) ∘ SpaceTime.timeRev = f := by ext p; simp
  rwa [hcomp] at h2

/-- Adding a global constant `c` shifts both poles by `+c` and every equatorial pair by `+2c`,
preserving `SatisfiesRecurrence` in any ordered abelian group. -/
theorem SatisfiesRecurrence.add_const [IsOrderedAddMonoid R] {hn : 1 ≤ n} {f : SpaceTime n → R}
    (hf : SatisfiesRecurrence hn f) (c : R) :
    SatisfiesRecurrence hn (fun p => f p + c) := by
  intro x y t hodd
  have hsum : equatorialSum hn (fun p => f p + c) x y t = equatorialSum hn f x y t + (c + c) := by
    have hslice : ∀ q, IsGridAdj (x, y) q →
        sliceAt (fun p => f p + c) t q = sliceAt f t q + c := by
      intro q hadj
      have hev := even_of_odd_isGridAdj (p := (x, y)) hodd hadj
      simp [sliceAt, hev]
    rw [equatorialSum, spatialEquatorialSum_congr hn hslice, equatorialSum]
    unfold spatialEquatorialSum
    split_ifs
    · simpa only [OrderIso.addRight_apply, add_add_add_comm _ c _ c] using
        ((OrderIso.addRight (c + c)).map_sup _ _).symm
    all_goals exact add_add_add_comm _ c _ c
  calc f (SpaceTime.northPole x y t hodd) + c + (f (SpaceTime.southPole x y t hodd) + c)
      = (f (SpaceTime.northPole x y t hodd) + f (SpaceTime.southPole x y t hodd)) + (c + c) :=
        add_add_add_comm _ _ _ _
    _ = equatorialSum hn f x y t + (c + c) := by rw [hf x y t hodd]
    _ = equatorialSum hn (fun p => f p + c) x y t := hsum.symm

end Recurrence

/-! ### Unique extension from a spacelike section and section transitions -/

section Extension

variable {n : ℕ} {R : Type*} [Lattice R] [AddCommGroup R]

/-- Upward slice-by-slice recursion starting from `τ.minHeight`: slice `k` represents time
`τ.minHeight + k`, copying `g` at or below `τ` and applying the recurrence strictly above `τ`. -/
def futureSlice (hn : 1 ≤ n) (τ : Section n) (g : Fin (n + 1) × Fin (n + 1) → R) :
    ℕ → Fin (n + 1) × Fin (n + 1) → R
  | 0, q => g q
  | 1, q => g q
  | k + 2, q =>
    if τ.minHeight + ((k + 2 : ℕ) : ℤ) ≤ τ q then g q
    else spatialEquatorialSum hn (futureSlice hn τ g (k + 1)) q - futureSlice hn τ g k q

theorem futureSlice_of_le (hn : 1 ≤ n) (τ : Section n) (g : Fin (n + 1) × Fin (n + 1) → R)
    (k : ℕ) {q : Fin (n + 1) × Fin (n + 1)} (hle : τ.minHeight + (k : ℤ) ≤ τ q) :
    futureSlice hn τ g k q = g q := by
  rcases k with _ | _ | k
  · rfl
  · rfl
  · dsimp only [futureSlice]
    split_ifs with h
    · rfl
    · omega

/-- Future extension of `g` on and above `τ`. -/
def extendFuture (hn : 1 ≤ n) (τ : Section n) (g : Fin (n + 1) × Fin (n + 1) → R)
    (p : SpaceTime n) : R :=
  futureSlice hn τ g (p.t - τ.minHeight).toNat (p.x, p.y)

@[simp] theorem extendFuture_point (hn : 1 ≤ n) (τ : Section n)
    (g : Fin (n + 1) × Fin (n + 1) → R) (q : Fin (n + 1) × Fin (n + 1)) :
    extendFuture hn τ g (τ.point q) = g q := by
  have hm := τ.minHeight_le q
  rw [extendFuture, Section.point_x, Section.point_y, Section.point_t, Prod.mk.eta]
  exact futureSlice_of_le hn τ g _ (by omega)

/-- Global extension of `g : [0, n]² → R` from a spacelike section `τ : Section n` to all of
`SpaceTime n`, propagating upward above `τ` and downward (via time reversal) below `τ`. -/
def extendSection (hn : 1 ≤ n) (τ : Section n) (g : Fin (n + 1) × Fin (n + 1) → R)
    (p : SpaceTime n) : R :=
  if τ (p.x, p.y) ≤ p.t then
    extendFuture hn τ g p
  else
    extendFuture hn τ.timeRev g p.timeRev

/-- Restricting `extendSection hn τ g` back to `τ` recovers `g`. -/
@[simp] theorem extendSection_point (hn : 1 ≤ n) (τ : Section n)
    (g : Fin (n + 1) × Fin (n + 1) → R) (q : Fin (n + 1) × Fin (n + 1)) :
    extendSection hn τ g (τ.point q) = g q := by
  simp [extendSection]

theorem extendSection_eq_extendFuture_of_le (hn : 1 ≤ n) (τ : Section n)
    (g : Fin (n + 1) × Fin (n + 1) → R) {p : SpaceTime n} (hp : τ (p.x, p.y) ≤ p.t) :
    extendSection hn τ g p = extendFuture hn τ g p := by
  simp [extendSection, hp]

theorem extendSection_timeRev (hn : 1 ≤ n) (τ : Section n)
    (g : Fin (n + 1) × Fin (n + 1) → R) (p : SpaceTime n) :
    extendSection hn τ.timeRev g p = extendSection hn τ g p.timeRev := by
  rcases lt_trichotomy (τ (p.x, p.y)) (-p.t) with hlt | heq | hgt
  · have h1 : ¬ -τ (p.x, p.y) ≤ p.t := by omega
    have h2 : τ (p.x, p.y) ≤ -p.t := by omega
    simp [extendSection, h1, h2]
  · have hp1 : p = τ.timeRev.point (p.x, p.y) := by (ext <;> simp); omega
    have hp2 : p.timeRev = τ.point (p.x, p.y) := by (ext <;> simp); omega
    have hL : extendSection hn τ.timeRev g p = g (p.x, p.y) :=
      (congrArg (extendSection hn τ.timeRev g) hp1).trans (extendSection_point hn τ.timeRev g _)
    have hR : extendSection hn τ g p.timeRev = g (p.x, p.y) :=
      (congrArg (extendSection hn τ g) hp2).trans (extendSection_point hn τ g _)
    exact hL.trans hR.symm
  · have h1 : -τ (p.x, p.y) ≤ p.t := by omega
    have h2 : ¬ τ (p.x, p.y) ≤ -p.t := by omega
    simp [extendSection, h1, h2]

private theorem extendFuture_northPole_add_southPole (hn : 1 ≤ n) (τ : Section n)
    (g : Fin (n + 1) × Fin (n + 1) → R) (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) (ht : τ (x, y) + 1 ≤ t) :
    extendSection hn τ g (SpaceTime.northPole x y t hodd) +
        extendSection hn τ g (SpaceTime.southPole x y t hodd) =
      equatorialSum hn (extendSection hn τ g) x y t := by
  have hm := τ.minHeight_le (x, y)
  set k := (t - 1 - τ.minHeight).toNat
  have hk2 : (t + 1 - τ.minHeight).toNat = k + 2 := by omega
  have hk1 : (t - τ.minHeight).toNat = k + 1 := by omega
  rw [extendSection_eq_extendFuture_of_le hn τ g (by simp; omega),
    extendSection_eq_extendFuture_of_le hn τ g (by simp; omega)]
  simp only [extendFuture, SpaceTime.northPole_x, SpaceTime.northPole_y, SpaceTime.northPole_t,
    SpaceTime.southPole_x, SpaceTime.southPole_y, SpaceTime.southPole_t, hk2]
  dsimp only [futureSlice]
  split_ifs with hle
  · omega
  · rw [sub_add_cancel]
    refine spatialEquatorialSum_congr hn fun q hadj => ?_
    have hev := even_of_odd_isGridAdj (p := (x, y)) hodd hadj
    have hτq : τ q ≤ t := by
      have := abs_le.mp (τ.abs_sub_le_one_apply hadj)
      omega
    simp only [sliceAt, hev, ↓reduceDIte]
    rw [extendSection_eq_extendFuture_of_le hn τ g hτq, extendFuture, hk1]

/-- Every section extension `extendSection hn τ g` satisfies Henriques–Kamnitzer's bounded
octahedron recurrence globally on `SpaceTime n`. -/
theorem satisfiesRecurrence_extendSection (hn : 1 ≤ n) (τ : Section n)
    (g : Fin (n + 1) × Fin (n + 1) → R) :
    SatisfiesRecurrence hn (extendSection hn τ g) := by
  intro x y t hodd
  have hne : t ≠ τ (x, y) := by
    rintro rfl
    have hev := Int.even_iff.mp (τ.even_sum_apply (x, y))
    dsimp only at hev
    have hod := Int.odd_iff.mp hodd
    omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hodd' : Odd ((x.val : ℤ) + y.val + -t) := by
      have := Int.odd_iff.mp hodd; rw [Int.odd_iff]; omega
    have hrev : extendSection hn τ.timeRev g = extendSection hn τ g ∘ SpaceTime.timeRev := by
      ext p; exact extendSection_timeRev hn τ g p
    have hstep := extendFuture_northPole_add_southPole hn τ.timeRev g x y (-t) hodd'
      (by simp; omega)
    rw [hrev] at hstep
    have hnp : (SpaceTime.northPole x y (-t) hodd').timeRev = SpaceTime.southPole x y t hodd := by
      (ext <;> simp); ring
    have hsp : (SpaceTime.southPole x y (-t) hodd').timeRev = SpaceTime.northPole x y t hodd := by
      (ext <;> simp); ring
    have heq : equatorialSum hn (extendSection hn τ g ∘ SpaceTime.timeRev) x y (-t) =
        equatorialSum hn (extendSection hn τ g) x y t := by
      refine spatialEquatorialSum_congr hn fun q hadj => ?_
      have hev1 := even_of_odd_isGridAdj (p := (x, y)) hodd' hadj
      have hev2 := even_of_odd_isGridAdj (p := (x, y)) hodd hadj
      simp only [sliceAt, hev1, hev2, ↓reduceDIte, Function.comp_apply]
      congr 1; ext <;> simp
    simp only [Function.comp_apply, hnp, hsp, heq] at hstep
    rwa [add_comm] at hstep
  · exact extendFuture_northPole_add_southPole hn τ g x y t hodd (by omega)

private theorem eq_of_eq_on_section_of_le {hn : 1 ≤ n} {f₁ f₂ : SpaceTime n → R}
    (hf₁ : SatisfiesRecurrence hn f₁) (hf₂ : SatisfiesRecurrence hn f₂) {τ : Section n}
    (heq : ∀ q, f₁ (τ.point q) = f₂ (τ.point q)) :
    ∀ k : ℕ, ∀ p : SpaceTime n, τ (p.x, p.y) ≤ p.t → (p.t - τ.minHeight).toNat ≤ k →
      f₁ p = f₂ p := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro p hle hbound
    rcases eq_or_lt_of_le hle with hpt | hlt
    · have hp : p = τ.point (p.x, p.y) := by ext <;> simp [hpt]
      rw [hp, heq]
    · have h2 : τ (p.x, p.y) + 2 ≤ p.t := by
        have hp1 := Int.even_iff.mp p.even_sum
        have hp2 := Int.even_iff.mp (τ.even_sum_apply (p.x, p.y))
        dsimp only at hp2
        omega
      have hm := τ.minHeight_le (p.x, p.y)
      have hodd : Odd ((p.x.val : ℤ) + p.y.val + (p.t - 1)) := by
        have := Int.even_iff.mp p.even_sum; rw [Int.odd_iff]; omega
      have hp_np : p = SpaceTime.northPole p.x p.y (p.t - 1) hodd := by ext <;> simp
      rw [hp_np, hf₁.northPole_eq, hf₂.northPole_eq]
      have hsp := ih ((p.t - 2 - τ.minHeight).toNat) (by omega)
        (SpaceTime.southPole p.x p.y (p.t - 1) hodd) (by simp; omega)
        (by simp; omega)
      have heqat : equatorialSum hn f₁ p.x p.y (p.t - 1) =
          equatorialSum hn f₂ p.x p.y (p.t - 1) := by
        refine spatialEquatorialSum_congr hn fun q hadj => ?_
        have hev := even_of_odd_isGridAdj (p := (p.x, p.y)) hodd hadj
        have hτq : τ q ≤ p.t - 1 := by
          have := abs_le.mp (τ.abs_sub_le_one_apply hadj); omega
        have := τ.minHeight_le q
        simp only [sliceAt, hev, ↓reduceDIte]
        exact ih ((p.t - 1 - τ.minHeight).toNat) (by omega) ⟨q.1, q.2, p.t - 1, hev⟩ hτq le_rfl
      rw [heqat, hsp]

/-- Two solutions of the bounded octahedron recurrence that agree on a spacelike section `τ` are
equal everywhere on `SpaceTime n`. -/
theorem SatisfiesRecurrence.eq_of_eq_on_section {hn : 1 ≤ n} {f₁ f₂ : SpaceTime n → R}
    (hf₁ : SatisfiesRecurrence hn f₁) (hf₂ : SatisfiesRecurrence hn f₂) (τ : Section n)
    (heq : ∀ q, f₁ (τ.point q) = f₂ (τ.point q)) : f₁ = f₂ := by
  ext p
  rcases le_total (τ (p.x, p.y)) p.t with hle | hle
  · exact eq_of_eq_on_section_of_le hf₁ hf₂ heq _ p hle le_rfl
  · have hf₁' := (satisfiesRecurrence_comp_timeRev_iff hn f₁).mpr hf₁
    have hf₂' := (satisfiesRecurrence_comp_timeRev_iff hn f₂).mpr hf₂
    have heq' : ∀ q, (f₁ ∘ SpaceTime.timeRev) (τ.timeRev.point q) =
        (f₂ ∘ SpaceTime.timeRev) (τ.timeRev.point q) := fun q => by simp [heq]
    have hrev := eq_of_eq_on_section_of_le hf₁' hf₂' heq' _ p.timeRev (by simp; omega) le_rfl
    simpa [Function.comp_apply] using hrev

/-- Restricting global solutions of `SatisfiesRecurrence hn` to any spacelike section `τ` is a
bijection onto `(Fin (n + 1) × Fin (n + 1) → R)` with inverse `extendSection hn τ`. -/
def Section.solutionEquiv (hn : 1 ≤ n) (τ : Section n) :
    {f : SpaceTime n → R // SatisfiesRecurrence hn f} ≃ (Fin (n + 1) × Fin (n + 1) → R) where
  toFun f q := f.1 (τ.point q)
  invFun g := ⟨extendSection hn τ g, satisfiesRecurrence_extendSection hn τ g⟩
  left_inv f := Subtype.ext <|
    (satisfiesRecurrence_extendSection hn τ _).eq_of_eq_on_section f.2 τ fun q =>
      extendSection_point hn τ _ q
  right_inv g := funext fun q => extendSection_point hn τ g q

@[simp] theorem Section.solutionEquiv_apply (hn : 1 ≤ n) (τ : Section n)
    (f : {f : SpaceTime n → R // SatisfiesRecurrence hn f}) (q : Fin (n + 1) × Fin (n + 1)) :
    τ.solutionEquiv hn f q = f.1 (τ.point q) := (rfl)

@[simp] theorem Section.solutionEquiv_symm_apply (hn : 1 ≤ n) (τ : Section n)
    (g : Fin (n + 1) × Fin (n + 1) → R) :
    ((τ.solutionEquiv hn).symm g).1 = extendSection hn τ g := (rfl)

/-- Invertible transition from data on section `τ₁` to data on section `τ₂` induced by unique
extension under the bounded octahedron recurrence. -/
def Section.transitionEquiv (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    (Fin (n + 1) × Fin (n + 1) → R) ≃ (Fin (n + 1) × Fin (n + 1) → R) :=
  (τ₁.solutionEquiv hn).symm.trans (τ₂.solutionEquiv hn)

@[simp] theorem Section.transitionEquiv_apply (hn : 1 ≤ n) (τ₁ τ₂ : Section n)
    (g : Fin (n + 1) × Fin (n + 1) → R) (q : Fin (n + 1) × Fin (n + 1)) :
    Section.transitionEquiv hn τ₁ τ₂ g q = extendSection hn τ₁ g (τ₂.point q) := (rfl)

@[simp] theorem Section.transitionEquiv_refl (hn : 1 ≤ n) (τ : Section n) :
    Section.transitionEquiv (R := R) hn τ τ = Equiv.refl _ :=
  Equiv.symm_trans_self (τ.solutionEquiv hn)

@[simp] theorem Section.transitionEquiv_symm (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    (Section.transitionEquiv (R := R) hn τ₁ τ₂).symm = Section.transitionEquiv hn τ₂ τ₁ := (rfl)

theorem Section.transitionEquiv_trans (hn : 1 ≤ n) (τ₁ τ₂ τ₃ : Section n) :
    (Section.transitionEquiv (R := R) hn τ₁ τ₂).trans (Section.transitionEquiv hn τ₂ τ₃) =
      Section.transitionEquiv hn τ₁ τ₃ := by
  ext g q
  have h2 := (τ₂.solutionEquiv (R := R) hn).symm_apply_apply
    ⟨extendSection hn τ₁ g, satisfiesRecurrence_extendSection hn τ₁ g⟩
  exact congrArg (fun s => s.1 (τ₃.point q)) h2

/-- Time-reversing both sections leaves the transition map unchanged. -/
@[simp] theorem Section.transitionEquiv_timeRev (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    Section.transitionEquiv (R := R) hn τ₁.timeRev τ₂.timeRev =
      Section.transitionEquiv hn τ₁ τ₂ := by
  ext g q
  simp [Section.transitionEquiv_apply, extendSection_timeRev]

/-- Constant-shift equivariance of `Section.transitionEquiv` in any ordered abelian group. -/
theorem Section.transitionEquiv_add_const [IsOrderedAddMonoid R] (hn : 1 ≤ n) (τ₁ τ₂ : Section n)
    (g : Fin (n + 1) × Fin (n + 1) → R) (c : R) :
    Section.transitionEquiv hn τ₁ τ₂ (fun q => g q + c) =
      fun q => Section.transitionEquiv hn τ₁ τ₂ g q + c := by
  have heq : extendSection hn τ₁ (fun q => g q + c) = fun p => extendSection hn τ₁ g p + c :=
    (satisfiesRecurrence_extendSection hn τ₁ _).eq_of_eq_on_section
      ((satisfiesRecurrence_extendSection hn τ₁ g).add_const c) τ₁ fun q => by simp
  ext q
  simp [Section.transitionEquiv_apply, heq]

end Extension

/-! ### Compatibility with `ℤ → ℝ` casting and nonnegative real scaling -/

section Scaling

/-- Integer solutions cast directly to real solutions under `(Int.cast : ℤ → ℝ)`. -/
theorem SatisfiesRecurrence.intCast {n : ℕ} {hn : 1 ≤ n} {f : SpaceTime n → ℤ}
    (hf : SatisfiesRecurrence hn f) :
    SatisfiesRecurrence (R := ℝ) hn (fun p => (f p : ℝ)) := by
  intro x y t hodd
  have hsum : equatorialSum (R := ℝ) hn (fun p => (f p : ℝ)) x y t =
      Int.cast (equatorialSum (R := ℤ) hn f x y t) := by
    have hslice : ∀ q, IsGridAdj (x, y) q →
        sliceAt (R := ℝ) (fun p => (f p : ℝ)) t q = Int.cast (sliceAt (R := ℤ) f t q) := by
      intro q hadj
      have hev := even_of_odd_isGridAdj (p := (x, y)) hodd hadj
      simp [sliceAt, hev]
    rw [equatorialSum, spatialEquatorialSum_congr hn hslice, equatorialSum]
    unfold spatialEquatorialSum
    split_ifs
    · simp only [← Int.cast_add, ← Int.cast_mono.map_sup]
    all_goals simp only [← Int.cast_add]
  rw [hsum, ← hf x y t hodd, Int.cast_add]

/-- Section transitions commute with `(Int.cast : ℤ → ℝ)`. -/
theorem Section.transitionEquiv_intCast {n : ℕ} (hn : 1 ≤ n) (τ₁ τ₂ : Section n)
    (g : Fin (n + 1) × Fin (n + 1) → ℤ) :
    Section.transitionEquiv (R := ℝ) hn τ₁ τ₂ (fun q => (g q : ℝ)) =
      fun q => Int.cast (Section.transitionEquiv (R := ℤ) hn τ₁ τ₂ g q) := by
  have heq : extendSection (R := ℝ) hn τ₁ (fun q => (g q : ℝ)) =
      fun p => Int.cast (extendSection (R := ℤ) hn τ₁ g p) :=
    (satisfiesRecurrence_extendSection (R := ℝ) hn τ₁ _).eq_of_eq_on_section
      (satisfiesRecurrence_extendSection hn τ₁ g).intCast τ₁ fun q => by simp
  ext q
  simp [Section.transitionEquiv_apply, heq]

/-- Positive-homogeneous scaling (`0 ≤ c`) preserves `SatisfiesRecurrence` over `ℝ`. -/
theorem SatisfiesRecurrence.smul_of_nonneg {n : ℕ} {hn : 1 ≤ n} {f : SpaceTime n → ℝ}
    (hf : SatisfiesRecurrence hn f) {c : ℝ} (hc : 0 ≤ c) :
    SatisfiesRecurrence hn (fun p => c * f p) := by
  intro x y t hodd
  have hmono : Monotone (fun r : ℝ => c * r) := fun _ _ h => mul_le_mul_of_nonneg_left h hc
  have hsum : equatorialSum hn (fun p => c * f p) x y t = c * equatorialSum hn f x y t := by
    have hslice : ∀ q, IsGridAdj (x, y) q →
        sliceAt (fun p => c * f p) t q = c * sliceAt f t q := by
      intro q hadj
      have hev := even_of_odd_isGridAdj (p := (x, y)) hodd hadj
      simp [sliceAt, hev]
    rw [equatorialSum, spatialEquatorialSum_congr hn hslice, equatorialSum]
    unfold spatialEquatorialSum
    split_ifs
    · simp only [← mul_add, ← hmono.map_sup]
    all_goals simp only [← mul_add]
  rw [hsum, ← hf x y t hodd, mul_add]

/-- Section transitions over `ℝ` are positively homogeneous (`0 ≤ c`). -/
theorem Section.transitionEquiv_smul_of_nonneg {n : ℕ} (hn : 1 ≤ n) (τ₁ τ₂ : Section n)
    (g : Fin (n + 1) × Fin (n + 1) → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Section.transitionEquiv hn τ₁ τ₂ (fun q => c * g q) =
      fun q => c * Section.transitionEquiv hn τ₁ τ₂ g q := by
  have heq : extendSection hn τ₁ (fun q => c * g q) = fun p => c * extendSection hn τ₁ g p :=
    (satisfiesRecurrence_extendSection hn τ₁ _).eq_of_eq_on_section
      ((satisfiesRecurrence_extendSection hn τ₁ g).smul_of_nonneg hc) τ₁ fun q => by simp
  ext q
  simp [Section.transitionEquiv_apply, heq]

end Scaling

/-! ### Unit-cell excavations and legal excavation schedules -/

section Excavation

variable {n : ℕ} {R : Type*} [Lattice R] [AddCommGroup R]

/-- A grid site `p` is legally excavatable upward on `τ : Section n` when every unit spatial
neighbour of `p` has height `τ p + 1` (equivalently, `p` is a strict local minimum of `τ`). -/
def Section.IsExcavationAt (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) : Prop :=
  ∀ q, IsGridAdj p q → τ q = τ p + 1

theorem Section.isExcavationAt_def (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    τ.IsExcavationAt p ↔ ∀ q, IsGridAdj p q → τ q = τ p + 1 := Iff.rfl

instance (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) : Decidable (τ.IsExcavationAt p) :=
  decidable_of_iff _ (τ.isExcavationAt_def p).symm

theorem Section.isExcavationAt_iff_lt (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    τ.IsExcavationAt p ↔ ∀ q, IsGridAdj p q → τ p < τ q := by
  refine ⟨fun h q hadj => by have := h q hadj; omega, fun h q hadj => ?_⟩
  have hlt := h q hadj
  have habs := abs_le.mp (τ.abs_sub_le_one_apply hadj)
  omega

/-- Excavate `τ : Section n` upward by `+2` at a legal local minimum `p`. -/
def Section.excavate (τ : Section n) (p : Fin (n + 1) × Fin (n + 1))
    (hp : τ.IsExcavationAt p) : Section n where
  height q := if q = p then τ p + 2 else τ q
  even_sum q := by
    by_cases hq : q = p
    · subst hq
      have := Int.even_iff.mp (τ.even_sum_apply q)
      simp only [↓reduceIte, Int.even_iff]; omega
    · simp [hq, τ.even_sum_apply q]
  abs_sub_le_one q₁ q₂ hadj := by
    by_cases h1 : q₁ = p
    · subst h1
      have hne : q₂ ≠ q₁ := hadj.ne.symm
      simp only [↓reduceIte, hne, hp q₂ hadj]
      norm_num
    · by_cases h2 : q₂ = p
      · subst h2
        simp only [h1, ↓reduceIte, hp q₁ hadj.symm]
        norm_num
      · simp only [h1, h2, ↓reduceIte]
        exact τ.abs_sub_le_one_apply hadj

@[simp] theorem Section.excavate_apply_self (τ : Section n) (p : Fin (n + 1) × Fin (n + 1))
    (hp : τ.IsExcavationAt p) : τ.excavate p hp p = τ p + 2 := by
  simp [Section.excavate]

@[simp] theorem Section.excavate_apply_of_ne (τ : Section n) {p q : Fin (n + 1) × Fin (n + 1)}
    (hp : τ.IsExcavationAt p) (hq : q ≠ p) : τ.excavate p hp q = τ q := by
  simp [Section.excavate, hq]

theorem Section.le_excavate (τ : Section n) (p : Fin (n + 1) × Fin (n + 1))
    (hp : τ.IsExcavationAt p) : τ ≤ τ.excavate p hp := by
  intro q
  by_cases hq : q = p
  · subst hq; simp
  · simp [hq]

/-- Single-site tropical excavation operator on `[0, n]² → R`: replaces `g p` by
`spatialEquatorialSum hn g p - g p` and fixes all other coordinates. Because `spatialEquatorialSum`
reads only neighbours `q ≠ p`, this map is a strict involution. -/
def excavateAt (hn : 1 ≤ n) (p : Fin (n + 1) × Fin (n + 1)) :
    (Fin (n + 1) × Fin (n + 1) → R) ≃ (Fin (n + 1) × Fin (n + 1) → R) where
  toFun g q := if q = p then spatialEquatorialSum hn g p - g p else g q
  invFun g q := if q = p then spatialEquatorialSum hn g p - g p else g q
  left_inv g := by
    ext q
    by_cases hq : q = p
    · subst hq
      simp only [↓reduceIte]
      have hcongr : spatialEquatorialSum hn
          (fun r => if r = q then spatialEquatorialSum hn g q - g q else g r) q =
          spatialEquatorialSum hn g q :=
        spatialEquatorialSum_congr hn fun r hadj => by simp [hadj.ne.symm]
      rw [hcongr, sub_sub_cancel]
    · simp [hq]
  right_inv g := by
    ext q
    by_cases hq : q = p
    · subst hq
      simp only [↓reduceIte]
      have hcongr : spatialEquatorialSum hn
          (fun r => if r = q then spatialEquatorialSum hn g q - g q else g r) q =
          spatialEquatorialSum hn g q :=
        spatialEquatorialSum_congr hn fun r hadj => by simp [hadj.ne.symm]
      rw [hcongr, sub_sub_cancel]
    · simp [hq]

@[simp] theorem excavateAt_apply_self (hn : 1 ≤ n) (p : Fin (n + 1) × Fin (n + 1))
    (g : Fin (n + 1) × Fin (n + 1) → R) :
    excavateAt hn p g p = spatialEquatorialSum hn g p - g p := by
  simp [excavateAt]

@[simp] theorem excavateAt_apply_of_ne (hn : 1 ≤ n) {p q : Fin (n + 1) × Fin (n + 1)}
    (g : Fin (n + 1) × Fin (n + 1) → R) (hq : q ≠ p) :
    excavateAt hn p g q = g q := by
  simp [excavateAt, hq]

@[simp] theorem excavateAt_symm (hn : 1 ≤ n) (p : Fin (n + 1) × Fin (n + 1)) :
    (excavateAt (R := R) hn p).symm = excavateAt hn p := (rfl)

theorem excavateAt_involutive (hn : 1 ≤ n) (p : Fin (n + 1) × Fin (n + 1)) :
    Function.Involutive (excavateAt (R := R) hn p) :=
  (excavateAt hn p).left_inv

/-- Transitioning across a single legal excavation `τ → τ.excavate p hp` equals `excavateAt hn p`.
-/
@[simp] theorem Section.transitionEquiv_excavate (hn : 1 ≤ n) (τ : Section n)
    (p : Fin (n + 1) × Fin (n + 1)) (hp : τ.IsExcavationAt p) :
    Section.transitionEquiv (R := R) hn τ (τ.excavate p hp) = excavateAt hn p := by
  ext g q
  by_cases hq : q = p
  · subst hq
    have hodd : Odd ((q.1.val : ℤ) + q.2.val + (τ q + 1)) := by
      have := Int.even_iff.mp (τ.even_sum_apply q); rw [Int.odd_iff]; omega
    have hnp : (τ.excavate q hp).point q = SpaceTime.northPole q.1 q.2 (τ q + 1) hodd := by
      (ext <;> simp); ring
    have hsp : SpaceTime.southPole q.1 q.2 (τ q + 1) hodd = τ.point q := by
      ext <;> simp
    rw [Section.transitionEquiv_apply, hnp,
      (satisfiesRecurrence_extendSection hn τ g).northPole_eq, hsp, extendSection_point,
      excavateAt_apply_self]
    congr 1
    refine spatialEquatorialSum_congr hn fun r hadj => ?_
    have hev := even_of_odd_isGridAdj hodd hadj
    have hpt : (⟨r.1, r.2, τ q + 1, hev⟩ : SpaceTime n) = τ.point r := by
      ext <;> simp [hp r hadj]
    simp only [sliceAt, hev, ↓reduceDIte, hpt, extendSection_point]
  · have hpt : (τ.excavate p hp).point q = τ.point q := by ext <;> simp [hq]
    rw [Section.transitionEquiv_apply, hpt, extendSection_point, excavateAt_apply_of_ne _ _ hq]

/-- Whenever `τ₁ < τ₂` in `Section n`, any minimum-height point of `{p | τ₁ p < τ₂ p}` is legally
excavatable on `τ₁` and keeps `τ₁.excavate p hp ≤ τ₂`. -/
theorem Section.exists_isExcavationAt_of_lt {τ₁ τ₂ : Section n} (hlt : τ₁ < τ₂) :
    ∃ (p : Fin (n + 1) × Fin (n + 1)) (hp : τ₁.IsExcavationAt p), τ₁.excavate p hp ≤ τ₂ := by
  obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.mp hlt
  have hS : (Finset.univ.filter fun p => τ₁ p < τ₂ p).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hne; ext p
    have hnp : ¬ τ₁ p < τ₂ p := fun hp =>
      Finset.notMem_empty p (hemp ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩)
    exact le_antisymm (hle p) (not_lt.mp hnp)
  obtain ⟨p, hpS, hpmin⟩ := (Finset.univ.filter fun q => τ₁ q < τ₂ q).exists_min_image τ₁ hS
  have hp_lt : τ₁ p < τ₂ p := (Finset.mem_filter.mp hpS).2
  have hp2 : τ₁ p + 2 ≤ τ₂ p := Section.add_two_le_of_lt hp_lt
  have hex : τ₁.IsExcavationAt p := by
    intro q hadj
    have h1 := abs_le.mp (τ₁.abs_sub_le_one_apply hadj)
    have h2 := abs_le.mp (τ₂.abs_sub_le_one_apply hadj)
    have hodd := Int.odd_iff.mp hadj.odd_sum_sub
    have hev1 := Int.even_iff.mp (τ₁.even_sum_apply p)
    have hev2 := Int.even_iff.mp (τ₁.even_sum_apply q)
    by_contra hneq
    have hq_eq : τ₁ q = τ₁ p - 1 := by omega
    have hq_lt : τ₁ q < τ₂ q := by omega
    have hmin := hpmin q (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq_lt⟩)
    omega
  refine ⟨p, hex, fun q => ?_⟩
  by_cases hq : q = p
  · subst hq; simpa using hp2
  · simpa [hq] using hle q

/-- A legal unit-cell excavation schedule from `τ₁` to `τ₂` in `Section n`. -/
inductive Section.ExcavationSchedule : Section n → Section n → Type
  | refl (τ : Section n) : ExcavationSchedule τ τ
  | step {τ₁ τ₂ : Section n} (p : Fin (n + 1) × Fin (n + 1)) (hp : τ₁.IsExcavationAt p)
      (rest : ExcavationSchedule (τ₁.excavate p hp) τ₂) : ExcavationSchedule τ₁ τ₂

/-- Any legal excavation schedule witnesses `τ₁ ≤ τ₂`. -/
theorem Section.ExcavationSchedule.le {τ₁ τ₂ : Section n}
    (s : Section.ExcavationSchedule τ₁ τ₂) : τ₁ ≤ τ₂ := by
  induction s with
  | refl _ => exact le_rfl
  | @step σ₁ _ p hp _ ih => exact (σ₁.le_excavate p hp).trans ih

/-- Number of unit octahedra excavated by a schedule. -/
def Section.ExcavationSchedule.length {τ₁ τ₂ : Section n} :
    Section.ExcavationSchedule τ₁ τ₂ → ℕ
  | .refl _ => 0
  | .step _ _ rest => rest.length + 1

/-- Every legal excavation schedule from `τ₁` to `τ₂` has total height gain `2 * s.length`, so its
length depends only on the endpoints `τ₁, τ₂`. -/
theorem Section.ExcavationSchedule.sum_sub_eq_two_mul_length {τ₁ τ₂ : Section n}
    (s : Section.ExcavationSchedule τ₁ τ₂) :
    (∑ q : Fin (n + 1) × Fin (n + 1), (τ₂ q - τ₁ q)) = 2 * (s.length : ℤ) := by
  induction s with
  | refl _ => simp [Section.ExcavationSchedule.length]
  | @step σ₁ σ₂ p hp rest ih =>
    have hdiff : (∑ q, ((σ₁.excavate p hp) q - σ₁ q)) = 2 := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hqp; simp [hqp]
      · intro hp'; exact absurd (Finset.mem_univ p) hp'
    have hadd : (∑ q, (σ₂ q - σ₁ q)) =
        (∑ q, (σ₂ q - (σ₁.excavate p hp) q)) + ∑ q, ((σ₁.excavate p hp) q - σ₁ q) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => by ring
    rw [hadd, ih, hdiff, Section.ExcavationSchedule.length, Nat.cast_add, Nat.cast_one]
    ring

/-- Composite bijection `(Fin (n + 1) × Fin (n + 1) → R) ≃ (Fin (n + 1) × Fin (n + 1) → R)`
obtained by applying `excavateAt` step-by-step along a schedule. -/
def Section.ExcavationSchedule.eval (hn : 1 ≤ n) {τ₁ τ₂ : Section n} :
    Section.ExcavationSchedule τ₁ τ₂ →
      ((Fin (n + 1) × Fin (n + 1) → R) ≃ (Fin (n + 1) × Fin (n + 1) → R))
  | .refl _ => Equiv.refl _
  | .step p _ rest => (excavateAt hn p).trans (rest.eval hn)

/-- **Schedule independence**: evaluating *any* legal excavation schedule from `τ₁` to `τ₂` equals
the canonical section transition `Section.transitionEquiv hn τ₁ τ₂`. -/
theorem Section.ExcavationSchedule.eval_eq_transitionEquiv (hn : 1 ≤ n) {τ₁ τ₂ : Section n}
    (s : Section.ExcavationSchedule τ₁ τ₂) :
    s.eval (R := R) hn = Section.transitionEquiv hn τ₁ τ₂ := by
  induction s with
  | refl τ => exact (Section.transitionEquiv_refl hn τ).symm
  | step p hp rest ih =>
    rw [Section.ExcavationSchedule.eval, ih, ← Section.transitionEquiv_excavate hn _ p hp,
      Section.transitionEquiv_trans]

/-- Any two legal excavation schedules between the same sections induce the exact same map. -/
theorem Section.ExcavationSchedule.eval_eq_eval (hn : 1 ≤ n) {τ₁ τ₂ : Section n}
    (s₁ s₂ : Section.ExcavationSchedule τ₁ τ₂) :
    s₁.eval (R := R) hn = s₂.eval hn := by
  rw [s₁.eval_eq_transitionEquiv, s₂.eval_eq_transitionEquiv]

/-- Canonical excavation schedule from `τ₁` to `τ₂` whenever `τ₁ ≤ τ₂`. -/
noncomputable def Section.canonicalSchedule {τ₁ τ₂ : Section n} (hle : τ₁ ≤ τ₂) :
    Section.ExcavationSchedule τ₁ τ₂ :=
  if hne : τ₁ = τ₂ then
    hne ▸ .refl τ₁
  else
    let hlt : τ₁ < τ₂ := lt_of_le_of_ne hle hne
    let p := (Section.exists_isExcavationAt_of_lt hlt).choose
    let hp := (Section.exists_isExcavationAt_of_lt hlt).choose_spec.choose
    let hle' := (Section.exists_isExcavationAt_of_lt hlt).choose_spec.choose_spec
    .step p hp (Section.canonicalSchedule hle')
termination_by (∑ q : Fin (n + 1) × Fin (n + 1), (τ₂ q - τ₁ q)).toNat
decreasing_by
  simp_wf
  have hp_eq := Section.excavate_apply_self τ₁ p hp
  have h2 := hle' p
  dsimp only [p] at hp_eq h2 ⊢
  exact ⟨Finset.sum_lt_sum (fun q _ => τ₁.le_excavate _ hp q)
      ⟨(Section.exists_isExcavationAt_of_lt hlt).choose, Finset.mem_univ _, by omega⟩,
    Finset.sum_lt_sum (fun q _ => hle q)
      ⟨(Section.exists_isExcavationAt_of_lt hlt).choose, Finset.mem_univ _, by omega⟩⟩

end Excavation

/-! ### Associator excavation, interior confinement, and preservation of exterior boundaries -/

section Associator

variable {n : ℕ} {R : Type*} [Lattice R] [AddCommGroup R]

/-- Every legal excavation sandwiched between `lowerSection n` and `upperSection n` occurs at a
strictly interior spatial position (`0 < x < n` and `0 < y < n`), so wall and corner rules are
never triggered during associator excavation. -/
theorem isInteriorPos_of_excavate_le_upperSection {τ : Section n}
    {p : Fin (n + 1) × Fin (n + 1)} (hlo : lowerSection n ≤ τ) (hp : τ.IsExcavationAt p)
    (hhi : τ.excavate p hp ≤ upperSection n) : IsInteriorPos p := by
  rw [← lowerSection_lt_upperSection_iff]
  exact lt_of_le_of_lt (hlo p) (lt_of_lt_of_le (by simp) (hhi p))

/-- All six vertices of any unit octahedron excavated inside `[lowerSection n, upperSection n]`
lie inside the associator region `A_n`. -/
theorem inAssociator_of_excavate_le_upperSection {τ : Section n}
    {p : Fin (n + 1) × Fin (n + 1)} (hlo : lowerSection n ≤ τ) (hp : τ.IsExcavationAt p)
    (hhi : τ.excavate p hp ≤ upperSection n) :
    (τ.point p).InAssociator ∧ ((τ.excavate p hp).point p).InAssociator ∧
      ∀ q, IsGridAdj p q → (τ.point q).InAssociator := by
  have hτ_hi : τ ≤ upperSection n := (τ.le_excavate p hp).trans hhi
  have hex_lo : lowerSection n ≤ τ.excavate p hp := hlo.trans (τ.le_excavate p hp)
  exact ⟨τ.point_inAssociator hlo hτ_hi p, (τ.excavate p hp).point_inAssociator hex_lo hhi p,
    fun q _ => τ.point_inAssociator hlo hτ_hi q⟩

/-- Full associator section bijection from `lowerSection n` to `upperSection n` (defined as the
identity at `n = 0` where `AssociatorPoint 0` is a singleton, and via `Section.transitionEquiv`
for `1 ≤ n`). -/
def associatorSectionEquiv (n : ℕ) :
    (Fin (n + 1) × Fin (n + 1) → R) ≃ (Fin (n + 1) × Fin (n + 1) → R) :=
  if hn : 1 ≤ n then
    Section.transitionEquiv hn (lowerSection n) (upperSection n)
  else
    Equiv.refl _

theorem associatorSectionEquiv_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    associatorSectionEquiv (R := R) n =
      Section.transitionEquiv hn (lowerSection n) (upperSection n) := by
  simp [associatorSectionEquiv, hn]

/-- At `n = 0`, the associator region is the single vertex `(0, 0, 0)` and `associatorSectionEquiv`
is the identity. -/
@[simp] theorem associatorSectionEquiv_zero :
    associatorSectionEquiv (R := R) 0 = Equiv.refl _ := by
  simp [associatorSectionEquiv]

/-- At `n = 1`, `lowerSection 1 = upperSection 1`, so `associatorSectionEquiv 1` is also the
identity. -/
@[simp] theorem associatorSectionEquiv_one :
    associatorSectionEquiv (R := R) 1 = Equiv.refl _ := by
  rw [associatorSectionEquiv_of_one_le (le_refl 1), lowerSection_one_eq_upperSection,
    Section.transitionEquiv_refl]

/-- At `n = 2`, the associator region contains a single unit octahedron centered at `(1, 1, 1)`, so
`associatorSectionEquiv 2` is a single interior excavation at `(1, 1)`. -/
@[simp] theorem associatorSectionEquiv_two :
    associatorSectionEquiv (R := R) 2 = excavateAt (by decide) (1, 1) := by
  have hex : (lowerSection 2).IsExcavationAt (1, 1) := by
    rintro ⟨x, y⟩ hadj
    rw [isGridAdj_def] at hadj
    fin_cases x <;> fin_cases y <;> simp_all
  have hsec : (lowerSection 2).excavate (1, 1) hex = upperSection 2 := by
    ext ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> simp [Section.excavate]
  rw [associatorSectionEquiv_of_one_le (by decide), ← hsec, Section.transitionEquiv_excavate]

private theorem schedule_eval_apply_of_isWallPos (hn : 1 ≤ n) {τ₁ τ₂ : Section n}
    (s : Section.ExcavationSchedule τ₁ τ₂) (hlo : lowerSection n ≤ τ₁)
    (hhi : τ₂ ≤ upperSection n) (g : Fin (n + 1) × Fin (n + 1) → R)
    {q : Fin (n + 1) × Fin (n + 1)} (hq : IsWallPos q) :
    s.eval hn g q = g q := by
  induction s generalizing g with
  | refl _ => rfl
  | @step σ₁ _ p hp rest ih =>
    have hσ_hi : σ₁.excavate p hp ≤ upperSection n := rest.le.trans hhi
    have hint : IsInteriorPos p := isInteriorPos_of_excavate_le_upperSection hlo hp hσ_hi
    have hqp : q ≠ p := fun heq => ((not_isWallPos_iff_isInteriorPos q).mpr (heq ▸ hint)) hq
    simp only [Section.ExcavationSchedule.eval, Equiv.trans_apply]
    rw [ih (hlo.trans (σ₁.le_excavate p hp)) hhi (excavateAt hn p g),
      excavateAt_apply_of_ne _ _ hqp]

/-- **Spatial wall invariance**: `associatorSectionEquiv n` fixes every value on the spatial
boundary `x = 0`, `x = n`, `y = 0`, `y = n`, because `lowerSection n` and `upperSection n` already
coincide there. -/
theorem associatorSectionEquiv_apply_of_isWallPos (g : Fin (n + 1) × Fin (n + 1) → R)
    {q : Fin (n + 1) × Fin (n + 1)} (hq : IsWallPos q) :
    associatorSectionEquiv n g q = g q := by
  by_cases hn : 1 ≤ n
  · rw [associatorSectionEquiv_of_one_le hn,
      ← (Section.canonicalSchedule (lowerSection_le_upperSection n)).eval_eq_transitionEquiv hn]
    exact schedule_eval_apply_of_isWallPos hn _ le_rfl le_rfl g hq
  · have hn0 : n = 0 := by omega
    subst hn0; simp

/-- At `(n, 0)`, `associatorSectionEquiv n (glueLower h₁ h₂)` preserves the total weight
`∑ i, h₁.boundary 0 i` (`= |λ|`). -/
theorem associatorSectionEquiv_corner_last_zero (h₁ h₂ : Hive n R) :
    associatorSectionEquiv n (glueLower h₁ h₂) (Fin.last n, 0) = ∑ i : Fin n, h₁.boundary 0 i := by
  rw [associatorSectionEquiv_apply_of_isWallPos _ ((isWallPos_def _).mpr (Or.inr (Or.inl rfl))),
    glueLower_corner_last_zero]

/-- At `(0, 0)`, `associatorSectionEquiv n (glueLower h₁ h₂)` vanishes. -/
@[simp] theorem associatorSectionEquiv_corner_zero_zero (h₁ h₂ : Hive n R) :
    associatorSectionEquiv n (glueLower h₁ h₂) (0, 0) = 0 := by
  simpa using readOutput_cornerA_zero h₁ h₂ fun _ hp =>
    associatorSectionEquiv_apply_of_isWallPos _ hp

/-- `readOutputSecond` on the excavated associator output vanishes at `A = (n, 0, 0)`. -/
theorem readOutputSecond_associator_cornerA (h₁ h₂ : Hive n R) :
    readOutputSecond (associatorSectionEquiv n (glueLower h₁ h₂)) (Vertex.cornerA n) = 0 := by
  simp

/-- Side `0` of the first excavated output face equals `h₁.boundary 1` (`μ`). -/
theorem boundaryLinear_readOutputFirst_associator_zero (h₁ h₂ : Hive n R) :
    boundaryLinear ℤ n R (readOutputFirst (associatorSectionEquiv n (glueLower h₁ h₂))) 0 =
      h₁.boundary 1 :=
  boundaryLinear_readOutputFirst_zero h₁ h₂ fun _ hp =>
    associatorSectionEquiv_apply_of_isWallPos _ hp

/-- Side `1` of the first excavated output face equals `h₂.boundary 1` (`ν`) whenever `h₁, h₂`
have dual shared boundary along `X = Y`. -/
theorem boundaryLinear_readOutputFirst_associator_one (h₁ h₂ : Hive n R)
    (hb : ∀ i : Fin n, h₁.boundary 2 i = -h₂.boundary 0 i.rev) :
    boundaryLinear ℤ n R (readOutputFirst (associatorSectionEquiv n (glueLower h₁ h₂))) 1 =
      h₂.boundary 1 :=
  boundaryLinear_readOutputFirst_one h₁ h₂ hb fun _ hp =>
    associatorSectionEquiv_apply_of_isWallPos _ hp

/-- Side `0` of the second excavated output face equals `h₁.boundary 0` (`λ`). -/
theorem boundaryLinear_readOutputSecond_associator_zero (h₁ h₂ : Hive n R) :
    boundaryLinear ℤ n R (readOutputSecond (associatorSectionEquiv n (glueLower h₁ h₂))) 0 =
      h₁.boundary 0 :=
  boundaryLinear_readOutputSecond_zero h₁ h₂ fun _ hp =>
    associatorSectionEquiv_apply_of_isWallPos _ hp

/-- Side `2` of the second excavated output face equals `h₂.boundary 2` (`π*`) whenever `h₁, h₂`
have dual shared boundary along `X = Y`. -/
theorem boundaryLinear_readOutputSecond_associator_two (h₁ h₂ : Hive n R)
    (hb : ∀ i : Fin n, h₁.boundary 2 i = -h₂.boundary 0 i.rev) :
    boundaryLinear ℤ n R (readOutputSecond (associatorSectionEquiv n (glueLower h₁ h₂))) 2 =
      h₂.boundary 2 :=
  boundaryLinear_readOutputSecond_two h₁ h₂ hb fun _ hp =>
    associatorSectionEquiv_apply_of_isWallPos _ hp

/-- Re-gluing the two excavated output faces with constant shift `∑ i, h₁.boundary 0 i` (`= |λ|`)
and applying `(associatorSectionEquiv n).symm` recovers `glueLower h₁ h₂`. -/
theorem associatorSectionEquiv_symm_glueUpper (h₁ h₂ : Hive n R) :
    let g' := associatorSectionEquiv n (glueLower h₁ h₂)
    (associatorSectionEquiv n).symm
      (glueUpper (∑ i : Fin n, h₁.boundary 0 i) (readOutputFirst g') (readOutputSecond g')) =
      glueLower h₁ h₂ := by
  intro g'
  rw [← associatorSectionEquiv_corner_last_zero h₁ h₂, glueUpper_readOutputs,
    Equiv.symm_apply_apply]

end Associator

/-! ### Piecewise affineness and continuity over `ℝ` -/

section PiecewiseAffine

variable {n : ℕ}

private theorem exists_clm_spatialEquatorialSum_of_not_isInteriorPos (hn : 1 ≤ n)
    {p : Fin (n + 1) × Fin (n + 1)} (hp : ¬ IsInteriorPos p) :
    ∃ L : (Fin (n + 1) × Fin (n + 1) → ℝ) →L[ℝ] ℝ,
      ∀ g, spatialEquatorialSum hn g p = L g := by
  let pairProj (q₁ q₂ : Fin (n + 1) × Fin (n + 1)) :
      (Fin (n + 1) × Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) q₁ +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) q₂
  by_cases hx : 0 < p.1.val ∧ p.1.val < n
  · have hy : ¬ (0 < p.2.val ∧ p.2.val < n) :=
      fun hy => hp ((isInteriorPos_def p).mpr ⟨hx.1, hx.2, hy.1, hy.2⟩)
    exact ⟨pairProj (⟨p.1.val + 1, by omega⟩, p.2) (⟨p.1.val - 1, by omega⟩, p.2), fun g => by
      unfold spatialEquatorialSum; split_ifs; simp [pairProj]⟩
  · by_cases hy : 0 < p.2.val ∧ p.2.val < n
    · exact ⟨pairProj (p.1, ⟨p.2.val + 1, by omega⟩) (p.1, ⟨p.2.val - 1, by omega⟩), fun g => by
        unfold spatialEquatorialSum; split_ifs; simp [pairProj]⟩
    · by_cases hx0 : p.1.val = 0
      · by_cases hy0 : p.2.val = 0
        · exact ⟨pairProj (⟨p.1.val + 1, by omega⟩, p.2) (p.1, ⟨p.2.val + 1, by omega⟩),
            fun g => by unfold spatialEquatorialSum; split_ifs; simp [pairProj]⟩
        · exact ⟨pairProj (⟨p.1.val + 1, by omega⟩, p.2)
              (p.1, ⟨p.2.val - 1, by have := p.2.isLt; omega⟩), fun g => by
            unfold spatialEquatorialSum; split_ifs; simp [pairProj]⟩
      · by_cases hy0 : p.2.val = 0
        · exact ⟨pairProj (⟨p.1.val - 1, by have := p.1.isLt; omega⟩, p.2)
              (p.1, ⟨p.2.val + 1, by omega⟩), fun g => by
            unfold spatialEquatorialSum; split_ifs; simp [pairProj]⟩
        · exact ⟨pairProj (⟨p.1.val - 1, by have := p.1.isLt; omega⟩, p.2)
              (p.1, ⟨p.2.val - 1, by have := p.2.isLt; omega⟩), fun g => by
            unfold spatialEquatorialSum; split_ifs; simp [pairProj]⟩

/-- Every single-site excavation `excavateAt (R := ℝ) hn p` is globally piecewise affine on
`Fin (n + 1) × Fin (n + 1) → ℝ` (covered by two closed half-spaces at interior sites and a single
linear map on walls and corners). -/
theorem isPiecewiseAffineOn_excavateAt (hn : 1 ≤ n) (p : Fin (n + 1) × Fin (n + 1)) :
    TauCeti.IsPiecewiseAffineOn (excavateAt (R := ℝ) hn p) Set.univ := by
  let upd (L : (Fin (n + 1) × Fin (n + 1) → ℝ) →L[ℝ] ℝ) :
      (Fin (n + 1) × Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) × Fin (n + 1) → ℝ) :=
    ContinuousLinearMap.pi fun q =>
      if q = p then L - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) p
      else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) q
  by_cases hp : IsInteriorPos p
  · obtain ⟨hx0, hxn, hy0, hyn⟩ := (isInteriorPos_def p).mp hp
    let pr := fun q =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) × Fin (n + 1) => ℝ) q
    let L₁ := pr (⟨p.1.val + 1, by omega⟩, p.2) + pr (⟨p.1.val - 1, by omega⟩, p.2)
    let L₂ := pr (p.1, ⟨p.2.val + 1, by omega⟩) + pr (p.1, ⟨p.2.val - 1, by omega⟩)
    let C : Bool → Set (Fin (n + 1) × Fin (n + 1) → ℝ) := fun b =>
      if b then {g | (L₂ - L₁).toContinuousAffineMap g ≤ 0}
      else {g | (L₁ - L₂).toContinuousAffineMap g ≤ 0}
    let A : Bool → ((Fin (n + 1) × Fin (n + 1) → ℝ) →ᴬ[ℝ] (Fin (n + 1) × Fin (n + 1) → ℝ)) :=
      fun b => if b then (upd L₁).toContinuousAffineMap else (upd L₂).toContinuousAffineMap
    refine TauCeti.isPiecewiseAffineOn_of_finite (C := C) (A := A)
      (fun b => by cases b <;> exact TauCeti.isConvexPolyhedron_setOf_le _) ?_ ?_
    · intro g _
      rcases le_total (L₂ g) (L₁ g) with hle | hle
      · exact Set.mem_iUnion.mpr ⟨true, by simpa [C] using sub_nonpos.mpr hle⟩
      · exact Set.mem_iUnion.mpr ⟨false, by simpa [C] using sub_nonpos.mpr hle⟩
    · intro b g ⟨_, hcell⟩
      ext q
      by_cases hq : q = p
      · subst hq
        rw [excavateAt_apply_self, spatialEquatorialSum_interior hn g hp]
        cases b
        · have hle : L₁ g ≤ L₂ g := by simpa [C, sub_nonpos] using hcell
          rw [sup_of_le_right (by simpa [L₁, L₂, pr] using hle)]
          simp [A, upd, L₂, pr]
        · have hle : L₂ g ≤ L₁ g := by simpa [C, sub_nonpos] using hcell
          rw [sup_of_le_left (by simpa [L₁, L₂, pr] using hle)]
          simp [A, upd, L₁, pr]
      · cases b <;> simp [A, upd, excavateAt_apply_of_ne _ _ hq, hq]
  · obtain ⟨L, hL⟩ := exists_clm_spatialEquatorialSum_of_not_isInteriorPos hn hp
    refine (TauCeti.isPiecewiseAffineOn_continuousAffineMap
      (upd L).toContinuousAffineMap Set.univ).congr fun g _ => ?_
    ext q
    by_cases hq : q = p
    · subst hq; simp [upd, hL]
    · simp [upd, hq]

private theorem isPiecewiseAffineOn_transitionEquiv_of_le (hn : 1 ≤ n) {τ₁ τ₂ : Section n}
    (hle : τ₁ ≤ τ₂) :
    TauCeti.IsPiecewiseAffineOn (Section.transitionEquiv (R := ℝ) hn τ₁ τ₂) Set.univ := by
  rw [← (Section.canonicalSchedule hle).eval_eq_transitionEquiv hn]
  generalize Section.canonicalSchedule hle = s
  clear hle
  induction s with
  | refl _ =>
    exact TauCeti.isPiecewiseAffineOn_continuousAffineMap
      (ContinuousLinearMap.id ℝ (Fin (n + 1) × Fin (n + 1) → ℝ)).toContinuousAffineMap Set.univ
  | step p _ _ ih =>
    simpa only [Section.ExcavationSchedule.eval, Equiv.coe_trans] using
      ih.comp (isPiecewiseAffineOn_excavateAt hn p) (Set.mapsTo_univ _ _)

/-- For **every** pair of spacelike sections `τ₁, τ₂ : Section n` (`1 ≤ n`), the transition map
`Section.transitionEquiv (R := ℝ) hn τ₁ τ₂` is globally piecewise affine on `Set.univ`. -/
theorem Section.isPiecewiseAffineOn_transitionEquiv (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    TauCeti.IsPiecewiseAffineOn (Section.transitionEquiv (R := ℝ) hn τ₁ τ₂) Set.univ := by
  have hdown : TauCeti.IsPiecewiseAffineOn
      (Section.transitionEquiv (R := ℝ) hn τ₁ (τ₁ ⊓ τ₂)) Set.univ := by
    rw [← Section.transitionEquiv_timeRev]
    exact isPiecewiseAffineOn_transitionEquiv_of_le hn fun q => by
      simp only [Section.timeRev_apply]
      exact neg_le_neg (inf_le_left (b := τ₂ q))
  have hup : TauCeti.IsPiecewiseAffineOn
      (Section.transitionEquiv (R := ℝ) hn (τ₁ ⊓ τ₂) τ₂) Set.univ :=
    isPiecewiseAffineOn_transitionEquiv_of_le hn inf_le_right
  rw [← Section.transitionEquiv_trans hn τ₁ (τ₁ ⊓ τ₂) τ₂, Equiv.coe_trans]
  exact hup.comp hdown (Set.mapsTo_univ _ _)

/-- Every real section-to-section transition is continuous. -/
theorem Section.continuous_transitionEquiv (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    Continuous (Section.transitionEquiv (R := ℝ) hn τ₁ τ₂) :=
  continuousOn_univ.mp (Section.isPiecewiseAffineOn_transitionEquiv hn τ₁ τ₂).continuousOn

/-- Every real section-to-section transition is a homeomorphism of `Fin (n + 1) × Fin (n + 1) → ℝ`.
-/
def Section.transitionHomeomorph (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    (Fin (n + 1) × Fin (n + 1) → ℝ) ≃ₜ (Fin (n + 1) × Fin (n + 1) → ℝ) where
  toEquiv := Section.transitionEquiv hn τ₁ τ₂
  continuous_toFun := Section.continuous_transitionEquiv hn τ₁ τ₂
  continuous_invFun := Section.continuous_transitionEquiv hn τ₂ τ₁

@[simp] theorem Section.coe_transitionHomeomorph (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    ⇑(Section.transitionHomeomorph hn τ₁ τ₂) = Section.transitionEquiv hn τ₁ τ₂ := (rfl)

@[simp] theorem Section.transitionHomeomorph_symm (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    (Section.transitionHomeomorph hn τ₁ τ₂).symm = Section.transitionHomeomorph hn τ₂ τ₁ := (rfl)

/-- `associatorSectionEquiv (R := ℝ) n` is globally piecewise affine for every `n : ℕ`. -/
theorem isPiecewiseAffineOn_associatorSectionEquiv (n : ℕ) :
    TauCeti.IsPiecewiseAffineOn (associatorSectionEquiv (R := ℝ) n) Set.univ := by
  by_cases hn : 1 ≤ n
  · rw [associatorSectionEquiv_of_one_le hn]
    exact Section.isPiecewiseAffineOn_transitionEquiv hn (lowerSection n) (upperSection n)
  · have hn0 : n = 0 := by omega
    subst hn0
    simp only [associatorSectionEquiv_zero, Equiv.coe_refl]
    exact TauCeti.isPiecewiseAffineOn_continuousAffineMap
      (ContinuousLinearMap.id ℝ (Fin 1 × Fin 1 → ℝ)).toContinuousAffineMap Set.univ

/-- `associatorSectionEquiv (R := ℝ) n` is continuous for every `n : ℕ`. -/
theorem continuous_associatorSectionEquiv (n : ℕ) :
    Continuous (associatorSectionEquiv (R := ℝ) n) :=
  continuousOn_univ.mp (isPiecewiseAffineOn_associatorSectionEquiv n).continuousOn

/-- Real associator excavation packaged as a homeomorphism of `Fin (n + 1) × Fin (n + 1) → ℝ`. -/
def associatorSectionHomeomorph (n : ℕ) :
    (Fin (n + 1) × Fin (n + 1) → ℝ) ≃ₜ (Fin (n + 1) × Fin (n + 1) → ℝ) where
  toEquiv := associatorSectionEquiv n
  continuous_toFun := continuous_associatorSectionEquiv n
  continuous_invFun := by
    simp only [Equiv.invFun_as_coe]
    by_cases hn : 1 ≤ n
    · rw [associatorSectionEquiv_of_one_le hn, Section.transitionEquiv_symm]
      exact Section.continuous_transitionEquiv hn (upperSection n) (lowerSection n)
    · have hn0 : n = 0 := by omega
      subst hn0
      simp [continuous_id]

@[simp] theorem coe_associatorSectionHomeomorph (n : ℕ) :
    ⇑(associatorSectionHomeomorph n) = associatorSectionEquiv n := (rfl)

end PiecewiseAffine

/-! ### Algebraic involution and rank-`2` `max`-versus-`min` chirality checks -/

section Checks

/-- Algebraic involution of the tropical octahedron update: setting `e' = (a + c) ⊔ (b + d) - e`
with the four equatorial values `(a, b, c, d)` fixed satisfies `(a + c) ⊔ (b + d) - e' = e`. -/
theorem interiorStep_involutive {R : Type*} [Lattice R] [AddCommGroup R] (a b c d e : R) :
    let e' := (a + c) ⊔ (b + d) - e
    (a + c) ⊔ (b + d) - e' = e :=
  sub_sub_cancel ((a + c) ⊔ (b + d)) e

private theorem glueLower_exampleTwo_reflect_detTwo :
    glueLower exampleTwo.reflect detTwo =
      fun q : Fin 3 × Fin 3 => ![![(0 : ℤ), 1, 2], ![2, 1, 2], ![2, 2, 1]] q.1 q.2 := by
  ext ⟨x, y⟩
  fin_cases x <;> fin_cases y <;>
    first
    | rw [glueLower_apply_of_le _ _ (by decide)]; simp
    | rw [glueLower_apply_of_gt _ _ (by decide)]; simp

private theorem isRhombusConcave_readOutputs_max_two :
    IsRhombusConcave
        (readOutputFirst (associatorSectionEquiv 2 (glueLower exampleTwo.reflect detTwo))) ∧
      IsRhombusConcave
        (readOutputSecond (associatorSectionEquiv 2 (glueLower exampleTwo.reflect detTwo))) := by
  let m : Fin 3 × Fin 3 → ℤ :=
    fun q => ![![(0 : ℤ), 1, 2], ![2, 3, 2], ![2, 2, 1]] q.1 q.2
  have hg : associatorSectionEquiv 2 (glueLower exampleTwo.reflect detTwo) = m := by
    rw [associatorSectionEquiv_two, glueLower_exampleTwo_reflect_detTwo]
    ext ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> simp [m, excavateAt, spatialEquatorialSum]
  rw [hg]
  have h1 : readOutputFirst m = ⇑exampleTwo + barycentricLinear 0 0 (-1) (-1) := by
    ext ⟨x, y, z, _⟩
    rcases (by omega : (x = 2 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 0) ∨
        (x = 0 ∧ y = 2 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 1) ∨
        (x = 0 ∧ y = 1 ∧ z = 1) ∨ (x = 0 ∧ y = 0 ∧ z = 2)) with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [m, readOutputFirst_apply]
  have h2 : readOutputSecond m = ⇑(2 • detTwo) + barycentricLinear 0 0 0 (-1) := by
    ext ⟨x, y, z, _⟩
    rcases (by omega : (x = 2 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 0) ∨
        (x = 0 ∧ y = 2 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 1) ∨
        (x = 0 ∧ y = 1 ∧ z = 1) ∨ (x = 0 ∧ y = 0 ∧ z = 2)) with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [m, readOutputSecond_apply]
  rw [h1, h2]
  exact ⟨(isRhombusConcave_add_barycentricLinear_iff _ _ _ _ _).mpr exampleTwo.isRhombusConcave,
    (isRhombusConcave_add_barycentricLinear_iff _ _ _ _ _).mpr (2 • detTwo).isRhombusConcave⟩

/-- Rank-`2` chirality check distinguishing `max` (`⊔`) from `min` (`⊓`): gluing the valid rank-`2`
hives `exampleTwo.reflect` (`λ = (2, 0)`, `μ = (0, -1)`, `σ = (1, 0)`) and `detTwo` (`σ = (1, 0)`,
`ν = (1, 0)`, `π = (1, 1)`) onto `lowerSection 2`, excavating the unique interior octahedron at
`(1, 1)` with Henriques–Kamnitzer's `max` rule yields rhombus-concave outputs on both upper faces,
whereas replacing `max` by `min` at `(1, 1)` gives rhombus slack `-1` on
`isRhombus_at_cornerA.rotate.rotate` in `readOutputSecond`. -/
theorem max_vs_min_counterexample_two :
    let g := glueLower exampleTwo.reflect detTwo
    let g_max := associatorSectionEquiv 2 g
    let g_min : Fin 3 × Fin 3 → ℤ := fun q =>
      if q = (1, 1) then
        (g (2, 1) + g (0, 1)) ⊓ (g (1, 2) + g (1, 0)) - g (1, 1)
      else g q
    IsRhombusConcave (readOutputFirst g_max) ∧
      IsRhombusConcave (readOutputSecond g_max) ∧
      rhombusSlack (readOutputSecond g_min)
        (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate.rotate (Vertex.cornerA 2).rotate.rotate
        (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate.rotate (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate.rotate = -1 ∧
      ¬ IsRhombusConcave (readOutputSecond g_min) := by
  obtain ⟨hmax1, hmax2⟩ := isRhombusConcave_readOutputs_max_two
  refine ⟨hmax1, hmax2, ?_, ?_⟩
  · simp [rhombusSlack_def, readOutputSecond_apply, glueLower_exampleTwo_reflect_detTwo]
  · intro hconc
    have h := (isRhombusConcave_def _).mp hconc isRhombus_at_cornerA.rotate.rotate
    simp [readOutputSecond_apply, glueLower_exampleTwo_reflect_detTwo] at h

end Checks

end TauCeti.Hive
