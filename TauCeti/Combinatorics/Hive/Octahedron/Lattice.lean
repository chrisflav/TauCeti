/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The tetrahedral lattice, space-time sections, and associator face embeddings

This file sets up the discrete three-dimensional geometry underlying the bounded octahedron
recurrence and the associativity bijection for hives.

`TetVertex n` consists of nonnegative integer quadruples `(a, b, c, d)` of sum `n`, forming the
size-`n` tetrahedral lattice. Translating the four corners of `TetVertex 1`, the four
anti-corners of `TetVertex 3`, and the six edge midpoints of `TetVertex 2` gives the unit
upright tetrahedra, unit downward tetrahedra, and unit octahedra of its subdivision.

`SpaceTimePoint n` is the bounded parity space-time lattice
`L_n = {(x, y, t) ∈ ℤ³ : 0 ≤ x, y ≤ n, Even (x + y + t)}`, and `AssociatorPoint n` cuts out the
associator region `A_n = {|x - y| ≤ t ≤ n - |n - x - y|}`. The affine coordinate change
`(a, b, c, d) ↦ (b + c, c + d, b + d)` gives an isometric equivalence
`TetVertex.equivAssociatorPoint : TetVertex n ≃ AssociatorPoint n` carrying each unit octahedron
indexed by `TetVertex m` in `TetVertex (m + 2)` to an interior stencil
`(x₀, y₀, t₀ ± 1)`, `(x₀ ± 1, y₀, t₀)`, `(x₀, y₀ ± 1, t₀)`.

`SpaceTimeSection n` represents sections in the `2`-skeleton of `L_n` meeting each vertical line
once, including `lowerSection n` (`t = |x - y|`) and `upperSection n` (`t = n - |n - x - y|`),
which coincide exactly along the four boundary walls. Finally, `embedLeftFst`, `embedLeftSnd`,
`embedRightFst`, and `embedRightSnd` embed the four triangular hive faces onto `lowerSection n`
and `upperSection n`.

## Main definitions

* `TauCeti.Hive.TetVertex`, `TauCeti.Hive.TetVertex.corner`, `TauCeti.Hive.TetVertex.antiCorner`,
  `TauCeti.Hive.TetVertex.octaVertex`: the tetrahedral lattice and its unit cells.
* `TauCeti.Hive.SpaceTimePoint`, `TauCeti.Hive.AssociatorPoint`,
  `TauCeti.Hive.TetVertex.equivAssociatorPoint`: the bounded parity space-time lattice, the
  associator region, and the isometric barycentric-to-space-time equivalence.
* `TauCeti.Hive.SpaceTimeSection`, `TauCeti.Hive.lowerSection`, `TauCeti.Hive.upperSection`,
  `TauCeti.Hive.SectionState`: space-time sections, the lower and upper associator sections, and
  grid states.
* `TauCeti.Hive.embedLeftFst`, `TauCeti.Hive.embedLeftSnd`, `TauCeti.Hive.embedRightFst`,
  `TauCeti.Hive.embedRightSnd`: embeddings of the four hive faces into `AssociatorPoint n`.

## Main results

* `TauCeti.Hive.TetVertex.sqDist_equivAssociatorPoint`,
  `TauCeti.Hive.TetVertex.equivAssociatorPoint_add_octaVertex`: isometry and unit-octahedron
  stencil correspondence.
* `TauCeti.Hive.SpaceTimeSection.sqDist_diag_eq_two`,
  `TauCeti.Hive.SpaceTimeSection.abs_sub_le_manhattan`: `2`-skeleton triangulation and horizontal
  Manhattan `1`-Lipschitz bound for sections.
* `TauCeti.Hive.lowerSection_eq_upperSection_iff`, `TauCeti.Hive.lowerSection_lt_upperSection_iff`,
  `TauCeti.Hive.AssociatorPoint.t_eq_lowerSection_of_wall`: wall coincidence and strict interior
  characterization for `lowerSection` and `upperSection`.

## References

* A. Henriques and J. Kamnitzer, *Crystals and coboundary categories*, Adv. Math. **206** (2006),
  §3.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §5.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### The size-`n` tetrahedral lattice and its unit cells -/

/-- A nonnegative barycentric lattice point in the regular tetrahedron of side length `n`. -/
@[ext]
structure TetVertex (n : ℕ) where
  /-- First barycentric coordinate. -/
  a : ℕ
  /-- Second barycentric coordinate. -/
  b : ℕ
  /-- Third barycentric coordinate. -/
  c : ℕ
  /-- Fourth barycentric coordinate. -/
  d : ℕ
  /-- The four barycentric coordinates sum to `n`. -/
  sum_eq : a + b + c + d = n
  deriving DecidableEq

namespace TetVertex

variable {n m : ℕ}

/-- The four barycentric coordinates as a tuple `Fin 4 → ℕ`. -/
def coord (p : TetVertex n) : Fin 4 → ℕ := ![p.a, p.b, p.c, p.d]

@[simp] theorem coord_zero (p : TetVertex n) : p.coord 0 = p.a := (rfl)
@[simp] theorem coord_one (p : TetVertex n) : p.coord 1 = p.b := (rfl)
@[simp] theorem coord_two (p : TetVertex n) : p.coord 2 = p.c := (rfl)
@[simp] theorem coord_three (p : TetVertex n) : p.coord 3 = p.d := (rfl)

/-- Equivalence between `TetVertex n` and `Finset.Nat.antidiagonalTuple 4 n`. -/
def equivAntidiagonalTuple : TetVertex n ≃ ↥(Finset.Nat.antidiagonalTuple 4 n) where
  toFun p := ⟨p.coord, by
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa [coord, Fin.sum_univ_four, add_assoc] using p.sum_eq⟩
  invFun t := ⟨t.1 0, t.1 1, t.1 2, t.1 3, by
    have ht := Finset.Nat.mem_antidiagonalTuple.mp t.2
    simpa [Fin.sum_univ_four, add_assoc] using ht⟩
  left_inv p := by ext <;> rfl
  right_inv t := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

@[simp] theorem equivAntidiagonalTuple_apply (p : TetVertex n) :
    (equivAntidiagonalTuple p).val = p.coord := (rfl)

instance : Fintype (TetVertex n) := Fintype.ofEquiv _ equivAntidiagonalTuple.symm

instance : Unique (TetVertex 0) where
  default := ⟨0, 0, 0, 0, rfl⟩
  uniq p := by have := p.sum_eq; ext <;> simp <;> omega

/-- Coordinatewise addition, translating a sub-tetrahedron of size `m` by `TetVertex n`. -/
def add (p : TetVertex n) (q : TetVertex m) : TetVertex (n + m) :=
  ⟨p.a + q.a, p.b + q.b, p.c + q.c, p.d + q.d, by have := p.sum_eq; have := q.sum_eq; omega⟩

@[simp] theorem add_a (p : TetVertex n) (q : TetVertex m) : (p.add q).a = p.a + q.a := (rfl)
@[simp] theorem add_b (p : TetVertex n) (q : TetVertex m) : (p.add q).b = p.b + q.b := (rfl)
@[simp] theorem add_c (p : TetVertex n) (q : TetVertex m) : (p.add q).c = p.c + q.c := (rfl)
@[simp] theorem add_d (p : TetVertex n) (q : TetVertex m) : (p.add q).d = p.d + q.d := (rfl)

/-- Squared Euclidean distance in ambient integer barycentric coordinates. -/
def sqDist (p q : TetVertex n) : ℤ :=
  ((p.a : ℤ) - q.a) ^ 2 + ((p.b : ℤ) - q.b) ^ 2 + ((p.c : ℤ) - q.c) ^ 2 + ((p.d : ℤ) - q.d) ^ 2

theorem sqDist_def (p q : TetVertex n) :
    sqDist p q = ((p.a : ℤ) - q.a) ^ 2 + ((p.b : ℤ) - q.b) ^ 2 +
      ((p.c : ℤ) - q.c) ^ 2 + ((p.d : ℤ) - q.d) ^ 2 := (rfl)

@[simp] theorem sqDist_self (p : TetVertex n) : sqDist p p = 0 := by simp [sqDist]

theorem sqDist_comm (p q : TetVertex n) : sqDist p q = sqDist q p := by unfold sqDist; ring

@[simp] theorem sqDist_add_left (p : TetVertex n) (q r : TetVertex m) :
    sqDist (p.add q) (p.add r) = sqDist q r := by
  simp only [sqDist, add_a, add_b, add_c, add_d, Nat.cast_add]; ring

/-- The `i`-th corner of `TetVertex n`, with `n` in coordinate `i` and `0` elsewhere. -/
def corner (n : ℕ) : Fin 4 → TetVertex n
  | ⟨0, _⟩ => ⟨n, 0, 0, 0, by omega⟩
  | ⟨1, _⟩ => ⟨0, n, 0, 0, by omega⟩
  | ⟨2, _⟩ => ⟨0, 0, n, 0, by omega⟩
  | ⟨3, _⟩ => ⟨0, 0, 0, n, by omega⟩

/-- The `i`-th vertex of the downward unit tetrahedron inside `TetVertex 3`. -/
def antiCorner : Fin 4 → TetVertex 3
  | ⟨0, _⟩ => ⟨0, 1, 1, 1, rfl⟩
  | ⟨1, _⟩ => ⟨1, 0, 1, 1, rfl⟩
  | ⟨2, _⟩ => ⟨1, 1, 0, 1, rfl⟩
  | ⟨3, _⟩ => ⟨1, 1, 1, 0, rfl⟩

/-- Distinct vertices of an upright unit tetrahedron `p.add (corner 1 ·)` have `sqDist = 2`. -/
theorem sqDist_add_corner_one (p : TetVertex n) {i j : Fin 4} (hij : i ≠ j) :
    sqDist (p.add (corner 1 i)) (p.add (corner 1 j)) = 2 := by
  rw [sqDist_add_left]
  fin_cases i <;> fin_cases j <;> simp_all [corner, sqDist]

/-- Distinct vertices of a downward unit tetrahedron `p.add (antiCorner ·)` have `sqDist = 2`. -/
theorem sqDist_add_antiCorner (p : TetVertex n) {i j : Fin 4} (hij : i ≠ j) :
    sqDist (p.add (antiCorner i)) (p.add (antiCorner j)) = 2 := by
  rw [sqDist_add_left]
  fin_cases i <;> fin_cases j <;> simp_all [antiCorner, sqDist]

/-- The six vertices of the unit octahedron inside `TetVertex 2`, labelled by their directions in
space-time coordinates. -/
inductive OctaDir
  | bottom | top | east | west | north | south
  deriving DecidableEq

/-- Enumeration of `OctaDir` by `Fin 6`. -/
def OctaDir.equivFin6 : OctaDir ≃ Fin 6 where
  toFun
    | .bottom => 0 | .top => 1 | .east => 2 | .west => 3 | .north => 4 | .south => 5
  invFun
    | ⟨0, _⟩ => .bottom | ⟨1, _⟩ => .top | ⟨2, _⟩ => .east
    | ⟨3, _⟩ => .west | ⟨4, _⟩ => .north | ⟨_ + 5, _⟩ => .south
  left_inv d := by cases d <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype OctaDir := Fintype.ofEquiv _ OctaDir.equivFin6.symm

/-- Opposite vertex involution on a unit octahedron. -/
def OctaDir.opp : OctaDir → OctaDir
  | .bottom => .top
  | .top => .bottom
  | .east => .west
  | .west => .east
  | .north => .south
  | .south => .north

@[simp] theorem OctaDir.opp_opp (d : OctaDir) : d.opp.opp = d := by cases d <;> rfl

/-- Embedding of the six unit-octahedron directions as the edge midpoints of `TetVertex 2`. -/
def octaVertex : OctaDir → TetVertex 2
  | .bottom => ⟨1, 0, 1, 0, rfl⟩
  | .top => ⟨0, 1, 0, 1, rfl⟩
  | .east => ⟨0, 1, 1, 0, rfl⟩
  | .west => ⟨1, 0, 0, 1, rfl⟩
  | .north => ⟨0, 0, 1, 1, rfl⟩
  | .south => ⟨1, 1, 0, 0, rfl⟩

/-- Opposite vertices of a unit octahedron `p.add (octaVertex ·)` have `sqDist = 4`, while
adjacent vertices have `sqDist = 2`. -/
theorem sqDist_add_octaVertex (p : TetVertex n) (u v : OctaDir) :
    sqDist (p.add (octaVertex u)) (p.add (octaVertex v)) =
      if u = v then 0 else if u = v.opp then 4 else 2 := by
  rw [sqDist_add_left]
  cases u <;> cases v <;> decide

end TetVertex

/-! ### Bounded parity space-time lattice and the associator region -/

/-- A point in Henriques-Kamnitzer's bounded parity space-time lattice
`L_n = {(x, y, t) ∈ ℤ³ : 0 ≤ x, y ≤ n, Even (x + y + t)}`. -/
@[ext]
structure SpaceTimePoint (n : ℕ) where
  /-- First horizontal coordinate in `{0, ..., n}`. -/
  x : ℕ
  /-- Second horizontal coordinate in `{0, ..., n}`. -/
  y : ℕ
  /-- Vertical time coordinate. -/
  t : ℤ
  /-- Bound `x ≤ n`. -/
  x_le : x ≤ n
  /-- Bound `y ≤ n`. -/
  y_le : y ≤ n
  /-- Parity condition `Even (x + y + t)`. -/
  even_sum : Even ((x : ℤ) + y + t)
  deriving DecidableEq

namespace SpaceTimePoint

variable {n : ℕ}

/-- First horizontal coordinate packaged in `Fin (n + 1)`. -/
def finX (p : SpaceTimePoint n) : Fin (n + 1) := ⟨p.x, Nat.lt_succ_of_le p.x_le⟩

/-- Second horizontal coordinate packaged in `Fin (n + 1)`. -/
def finY (p : SpaceTimePoint n) : Fin (n + 1) := ⟨p.y, Nat.lt_succ_of_le p.y_le⟩

@[simp] theorem val_finX (p : SpaceTimePoint n) : p.finX.val = p.x := (rfl)
@[simp] theorem val_finY (p : SpaceTimePoint n) : p.finY.val = p.y := (rfl)

/-- Time reversal `(x, y, t) ↦ (x, y, -t)` on `L_n`. -/
def timeRev (p : SpaceTimePoint n) : SpaceTimePoint n where
  x := p.x
  y := p.y
  t := -p.t
  x_le := p.x_le
  y_le := p.y_le
  even_sum := by
    rw [Int.even_iff]
    have h := Int.even_iff.mp p.even_sum
    omega

@[simp] theorem timeRev_x (p : SpaceTimePoint n) : p.timeRev.x = p.x := (rfl)
@[simp] theorem timeRev_y (p : SpaceTimePoint n) : p.timeRev.y = p.y := (rfl)
@[simp] theorem timeRev_t (p : SpaceTimePoint n) : p.timeRev.t = -p.t := (rfl)
@[simp] theorem finX_timeRev (p : SpaceTimePoint n) : p.timeRev.finX = p.finX := (rfl)
@[simp] theorem finY_timeRev (p : SpaceTimePoint n) : p.timeRev.finY = p.finY := (rfl)
@[simp] theorem timeRev_timeRev (p : SpaceTimePoint n) : p.timeRev.timeRev = p := by ext <;> simp

/-- Time reversal as a computable self-equivalence of `SpaceTimePoint n`. -/
def timeRevEquiv : SpaceTimePoint n ≃ SpaceTimePoint n where
  toFun := timeRev
  invFun := timeRev
  left_inv := timeRev_timeRev
  right_inv := timeRev_timeRev

@[simp] theorem timeRevEquiv_apply (p : SpaceTimePoint n) : timeRevEquiv p = p.timeRev := (rfl)
@[simp] theorem timeRevEquiv_symm : (timeRevEquiv (n := n)).symm = timeRevEquiv := (rfl)

/-- Squared Euclidean distance `(x₁ - x₂)² + (y₁ - y₂)² + (t₁ - t₂)²` in space-time coordinates. -/
def sqDist (p q : SpaceTimePoint n) : ℤ :=
  ((p.x : ℤ) - q.x) ^ 2 + ((p.y : ℤ) - q.y) ^ 2 + (p.t - q.t) ^ 2

theorem sqDist_def (p q : SpaceTimePoint n) :
    sqDist p q = ((p.x : ℤ) - q.x) ^ 2 + ((p.y : ℤ) - q.y) ^ 2 + (p.t - q.t) ^ 2 := (rfl)

@[simp] theorem coords_zero (p : SpaceTimePoint 0) : p.x = 0 ∧ p.y = 0 :=
  ⟨Nat.eq_zero_of_le_zero p.x_le, Nat.eq_zero_of_le_zero p.y_le⟩

end SpaceTimePoint

/-- A lattice point in the associator region
`A_n = {(x, y, t) ∈ L_n : |x - y| ≤ t ≤ n - |n - x - y|}`. -/
@[ext]
structure AssociatorPoint (n : ℕ) extends SpaceTimePoint n where
  /-- Lower section bound `|x - y| ≤ t`. -/
  abs_sub_le_t : |(x : ℤ) - y| ≤ t
  /-- Upper section bound `t ≤ n - |n - x - y|`. -/
  t_le_sub_abs : t ≤ (n : ℤ) - |(n : ℤ) - x - y|
  deriving DecidableEq

/-- Equivalence between the size-`n` tetrahedral lattice `TetVertex n` and the associator region
`AssociatorPoint n`, sending `(a, b, c, d)` to `(b + c, c + d, b + d)`. -/
def TetVertex.equivAssociatorPoint {n : ℕ} : TetVertex n ≃ AssociatorPoint n where
  toFun p :=
    { x := p.b + p.c
      y := p.c + p.d
      t := (p.b : ℤ) + p.d
      x_le := by have := p.sum_eq; omega
      y_le := by have := p.sum_eq; omega
      even_sum := ⟨p.b + p.c + p.d, by push_cast; ring⟩
      abs_sub_le_t := by
        rw [abs_le]
        constructor <;> push_cast <;> omega
      t_le_sub_abs := by
        have hs : (p.a : ℤ) + p.b + p.c + p.d = n := by exact_mod_cast p.sum_eq
        have hle : |(n : ℤ) - ↑(p.b + p.c) - ↑(p.c + p.d)| ≤ (n : ℤ) - ((p.b : ℤ) + p.d) := by
          rw [abs_le]
          constructor <;> push_cast <;> omega
        linarith }
  invFun q :=
    { a := ((2 * (n : ℤ) - q.x - q.y - q.t) / 2).toNat
      b := ((q.t + q.x - q.y) / 2).toNat
      c := ((q.x + q.y - q.t) / 2).toNat
      d := ((q.t - q.x + q.y) / 2).toNat
      sum_eq := by
        have hev := Int.even_iff.mp q.even_sum
        have hlo := abs_le.mp q.abs_sub_le_t
        have hhi : |(n : ℤ) - q.x - q.y| ≤ (n : ℤ) - q.t := by linarith [q.t_le_sub_abs]
        have hhi' := abs_le.mp hhi
        omega }
  left_inv p := by
    have hs := p.sum_eq
    ext <;> dsimp <;> omega
  right_inv q := by
    have hev := Int.even_iff.mp q.even_sum
    have hlo := abs_le.mp q.abs_sub_le_t
    have hhi : |(n : ℤ) - q.x - q.y| ≤ (n : ℤ) - q.t := by linarith [q.t_le_sub_abs]
    have hhi' := abs_le.mp hhi
    ext <;> dsimp <;> omega

namespace TetVertex

variable {n m : ℕ}

@[simp] theorem equivAssociatorPoint_x (p : TetVertex n) :
    (equivAssociatorPoint p).x = p.b + p.c := (rfl)
@[simp] theorem equivAssociatorPoint_y (p : TetVertex n) :
    (equivAssociatorPoint p).y = p.c + p.d := (rfl)
@[simp] theorem equivAssociatorPoint_t (p : TetVertex n) :
    (equivAssociatorPoint p).t = (p.b : ℤ) + p.d := (rfl)

/-- `equivAssociatorPoint` preserves squared distances between `TetVertex` and `SpaceTimePoint`. -/
theorem sqDist_equivAssociatorPoint (p q : TetVertex n) :
    SpaceTimePoint.sqDist (equivAssociatorPoint p).toSpaceTimePoint
      (equivAssociatorPoint q).toSpaceTimePoint = sqDist p q := by
  have hp : (p.a : ℤ) + p.b + p.c + p.d = n := by exact_mod_cast p.sum_eq
  have hq : (q.a : ℤ) + q.b + q.c + q.d = n := by exact_mod_cast q.sum_eq
  have hda : (p.a : ℤ) - q.a = -(((p.b : ℤ) - q.b) + ((p.c : ℤ) - q.c) + ((p.d : ℤ) - q.d)) := by
    linarith
  simp only [SpaceTimePoint.sqDist, sqDist, equivAssociatorPoint_x, equivAssociatorPoint_y,
    equivAssociatorPoint_t, Nat.cast_add]
  rw [hda]
  ring

/-- Every unit octahedron `p.add (octaVertex ·)` in `TetVertex (m + 2)` maps to the six-point
space-time stencil centered at `(p.b + p.c + 1, p.c + p.d + 1, p.b + p.d + 1)`. -/
theorem equivAssociatorPoint_add_octaVertex (p : TetVertex m) (dir : OctaDir) :
    let q := equivAssociatorPoint (p.add (octaVertex dir))
    ((q.x : ℤ), (q.y : ℤ), q.t) = match dir with
      | .bottom => ((p.b : ℤ) + p.c + 1, (p.c : ℤ) + p.d + 1, (p.b : ℤ) + p.d)
      | .top => ((p.b : ℤ) + p.c + 1, (p.c : ℤ) + p.d + 1, (p.b : ℤ) + p.d + 2)
      | .east => ((p.b : ℤ) + p.c + 2, (p.c : ℤ) + p.d + 1, (p.b : ℤ) + p.d + 1)
      | .west => ((p.b : ℤ) + p.c, (p.c : ℤ) + p.d + 1, (p.b : ℤ) + p.d + 1)
      | .north => ((p.b : ℤ) + p.c + 1, (p.c : ℤ) + p.d + 2, (p.b : ℤ) + p.d + 1)
      | .south => ((p.b : ℤ) + p.c + 1, (p.c : ℤ) + p.d, (p.b : ℤ) + p.d + 1) := by
  cases dir <;> simp [octaVertex] <;> omega

end TetVertex

instance {n : ℕ} : Fintype (AssociatorPoint n) :=
  Fintype.ofEquiv (TetVertex n) TetVertex.equivAssociatorPoint

instance : Unique (AssociatorPoint 0) where
  default := TetVertex.equivAssociatorPoint default
  uniq q := by
    rw [← TetVertex.equivAssociatorPoint.apply_symm_apply q,
      Subsingleton.elim (TetVertex.equivAssociatorPoint.symm q) default]

/-! ### Sections in `L_n` and the lower and upper associator sections -/

/-- A section in the `2`-skeleton of `L_n` meeting each vertical line `(x, y)` once: a parity
height function `Fin (n + 1) → Fin (n + 1) → ℤ` with unit height steps along grid edges. -/
@[ext]
structure SpaceTimeSection (n : ℕ) where
  /-- Height assigned to the vertical line `(x, y)`. -/
  height : Fin (n + 1) → Fin (n + 1) → ℤ
  /-- Every graph point `(x, y, height x y)` belongs to the parity lattice `L_n`. -/
  even_sum : ∀ x y : Fin (n + 1), Even ((x : ℤ) + y + height x y)
  /-- Unit height change along horizontal `x`-steps. -/
  abs_sub_x : ∀ (x : Fin n) (y : Fin (n + 1)), |height x.succ y - height x.castSucc y| = 1
  /-- Unit height change along horizontal `y`-steps. -/
  abs_sub_y : ∀ (x : Fin (n + 1)) (y : Fin n), |height x y.succ - height x y.castSucc| = 1
  deriving DecidableEq

namespace SpaceTimeSection

variable {n : ℕ}

instance : CoeFun (SpaceTimeSection n) (fun _ => Fin (n + 1) → Fin (n + 1) → ℤ) := ⟨height⟩

@[simp] theorem mk_apply (h : Fin (n + 1) → Fin (n + 1) → ℤ)
    (he : ∀ x y : Fin (n + 1), Even ((x : ℤ) + y + h x y))
    (hx : ∀ (x : Fin n) (y : Fin (n + 1)), |h x.succ y - h x.castSucc y| = 1)
    (hy : ∀ (x : Fin (n + 1)) (y : Fin n), |h x y.succ - h x y.castSucc| = 1)
    (x y : Fin (n + 1)) :
    (⟨h, he, hx, hy⟩ : SpaceTimeSection n) x y = h x y := (rfl)

/-- Partial order on sections given by pointwise inequality of heights. -/
instance : PartialOrder (SpaceTimeSection n) :=
  PartialOrder.lift height fun _ _ => SpaceTimeSection.ext

theorem le_def {S₁ S₂ : SpaceTimeSection n} : S₁ ≤ S₂ ↔ ∀ x y, S₁ x y ≤ S₂ x y := Iff.rfl

/-- The point `(x, y, S x y)` of `SpaceTimePoint n` lying on `S` above `(x, y)`. -/
def point (S : SpaceTimeSection n) (x y : Fin (n + 1)) : SpaceTimePoint n where
  x := x.val
  y := y.val
  t := S x y
  x_le := Nat.le_of_lt_succ x.isLt
  y_le := Nat.le_of_lt_succ y.isLt
  even_sum := S.even_sum x y

@[simp] theorem point_x (S : SpaceTimeSection n) (x y : Fin (n + 1)) : (S.point x y).x = x := (rfl)
@[simp] theorem point_y (S : SpaceTimeSection n) (x y : Fin (n + 1)) : (S.point x y).y = y := (rfl)
@[simp] theorem point_t (S : SpaceTimeSection n) (x y : Fin (n + 1)) : (S.point x y).t = S x y :=
  (rfl)

@[simp] theorem point_finX (S : SpaceTimeSection n) (x y : Fin (n + 1)) :
    (S.point x y).finX = x := by ext; rfl
@[simp] theorem point_finY (S : SpaceTimeSection n) (x y : Fin (n + 1)) :
    (S.point x y).finY = y := by ext; rfl

/-- At any lattice point `p : SpaceTimePoint n`, `p.t - S p.finX p.finY` is even. -/
theorem even_t_sub (S : SpaceTimeSection n) (p : SpaceTimePoint n) :
    Even (p.t - S p.finX p.finY) := by
  rw [Int.even_iff]
  have hp := Int.even_iff.mp p.even_sum
  have hS := Int.even_iff.mp (S.even_sum p.finX p.finY)
  simp only [SpaceTimePoint.val_finX, SpaceTimePoint.val_finY] at hS
  omega

/-- Any lattice point strictly above `S` has height at least `S p.finX p.finY + 2`. -/
theorem add_two_le_t_of_lt (S : SpaceTimeSection n) {p : SpaceTimePoint n}
    (hlt : S p.finX p.finY < p.t) : S p.finX p.finY + 2 ≤ p.t := by
  have hev := Int.even_iff.mp (S.even_t_sub p)
  omega

/-- Any lattice point strictly below `S` has height at most `S p.finX p.finY - 2`. -/
theorem t_add_two_le_of_lt (S : SpaceTimeSection n) {p : SpaceTimePoint n}
    (hlt : p.t < S p.finX p.finY) : p.t + 2 ≤ S p.finX p.finY := by
  have hev := Int.even_iff.mp (S.even_t_sub p)
  omega

/-- Over every elementary square `[x, x + 1] × [y, y + 1]`, at least one diagonal of `S` has
squared length `2`, triangulating the graph of `S` by unit triangles of the `2`-skeleton. -/
theorem sqDist_diag_eq_two (S : SpaceTimeSection n) (x y : Fin n) :
    SpaceTimePoint.sqDist (S.point x.succ y.succ) (S.point x.castSucc y.castSucc) = 2 ∨
      SpaceTimePoint.sqDist (S.point x.succ y.castSucc) (S.point x.castSucc y.succ) = 2 := by
  have hx0 := S.abs_sub_x x y.castSucc
  have hx1 := S.abs_sub_x x y.succ
  have hy0 := S.abs_sub_y x.castSucc y
  have hy1 := S.abs_sub_y x.succ y
  have hdx : ((x.succ : ℕ) : ℤ) - (x.castSucc : ℕ) = 1 := by simp
  have hdy : ((y.succ : ℕ) : ℤ) - (y.castSucc : ℕ) = 1 := by simp
  have hdy' : ((y.castSucc : ℕ) : ℤ) - (y.succ : ℕ) = -1 := by linarith
  rcases eq_or_eq_neg_of_abs_eq hx0 with h1 | h1 <;>
    rcases eq_or_eq_neg_of_abs_eq hy1 with h4 | h4
  · rcases eq_or_eq_neg_of_abs_eq hy0 with h3 | h3
    · right
      have hdt : S x.succ y.castSucc - S x.castSucc y.succ = 0 := by linarith
      simp only [SpaceTimePoint.sqDist, point_x, point_y, point_t, hdx, hdy', hdt]; norm_num
    · exfalso
      have hbad : |S x.succ y.succ - S x.castSucc y.succ| = 3 := by
        rw [abs_of_nonneg (by linarith)]; linarith
      linarith [hx1]
  · left
    have hdt : S x.succ y.succ - S x.castSucc y.castSucc = 0 := by linarith
    simp only [SpaceTimePoint.sqDist, point_x, point_y, point_t, hdx, hdy, hdt]; norm_num
  · left
    have hdt : S x.succ y.succ - S x.castSucc y.castSucc = 0 := by linarith
    simp only [SpaceTimePoint.sqDist, point_x, point_y, point_t, hdx, hdy, hdt]; norm_num
  · rcases eq_or_eq_neg_of_abs_eq hy0 with h3 | h3
    · exfalso
      have hbad : |S x.succ y.succ - S x.castSucc y.succ| = 3 := by
        rw [abs_of_nonpos (by linarith)]; linarith
      linarith [hx1]
    · right
      have hdt : S x.succ y.castSucc - S x.castSucc y.succ = 0 := by linarith
      simp only [SpaceTimePoint.sqDist, point_x, point_y, point_t, hdx, hdy', hdt]; norm_num

/-- Any lattice-adjacent pair `(x₁, y₁)` and `(x₂, y₂)` at Manhattan distance `1` has unit height
difference on `S`. -/
theorem abs_sub_of_manhattan_eq_one (S : SpaceTimeSection n) {x₁ y₁ x₂ y₂ : Fin (n + 1)}
    (h : |(x₁ : ℤ) - x₂| + |(y₁ : ℤ) - y₂| = 1) :
    |S x₁ y₁ - S x₂ y₂| = 1 := by
  have hx0 := abs_nonneg ((x₁ : ℤ) - x₂)
  have hy0 := abs_nonneg ((y₁ : ℤ) - y₂)
  have hx1 := x₁.isLt; have hx2 := x₂.isLt; have hy1 := y₁.isLt; have hy2 := y₂.isLt
  rcases (by omega : (|(x₁ : ℤ) - x₂| = 1 ∧ |(y₁ : ℤ) - y₂| = 0) ∨
      (|(x₁ : ℤ) - x₂| = 0 ∧ |(y₁ : ℤ) - y₂| = 1)) with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hy' : y₁ = y₂ := Fin.ext (by simpa [sub_eq_zero] using abs_eq_zero.mp hy)
    rcases eq_or_eq_neg_of_abs_eq hx with hd | hd
    · let i : Fin n := ⟨x₂.val, by omega⟩
      have hx₁ : x₁ = i.succ := Fin.ext (by simp [i]; omega)
      have hx₂ : x₂ = i.castSucc := Fin.ext (by simp [i])
      rw [hy', hx₁, hx₂]; exact S.abs_sub_x i y₂
    · let i : Fin n := ⟨x₁.val, by omega⟩
      have hx₂ : x₂ = i.succ := Fin.ext (by simp [i]; omega)
      have hx₁ : x₁ = i.castSucc := Fin.ext (by simp [i])
      rw [hy', hx₁, hx₂, abs_sub_comm]; exact S.abs_sub_x i y₂
  · have hx' : x₁ = x₂ := Fin.ext (by simpa [sub_eq_zero] using abs_eq_zero.mp hx)
    rcases eq_or_eq_neg_of_abs_eq hy with hd | hd
    · let j : Fin n := ⟨y₂.val, by omega⟩
      have hy₁ : y₁ = j.succ := Fin.ext (by simp [j]; omega)
      have hy₂ : y₂ = j.castSucc := Fin.ext (by simp [j])
      rw [hx', hy₁, hy₂]; exact S.abs_sub_y x₂ j
    · let j : Fin n := ⟨y₁.val, by omega⟩
      have hy₂ : y₂ = j.succ := Fin.ext (by simp [j]; omega)
      have hy₁ : y₁ = j.castSucc := Fin.ext (by simp [j])
      rw [hx', hy₁, hy₂, abs_sub_comm]; exact S.abs_sub_y x₂ j

private theorem abs_sub_le_same_y (S : SpaceTimeSection n) (y : Fin (n + 1)) :
    ∀ {a b : ℕ} (ha : a ≤ b) (hb : b ≤ n),
      |S ⟨b, Nat.lt_succ_of_le hb⟩ y - S ⟨a, Nat.lt_succ_of_le (ha.trans hb)⟩ y| ≤ (b : ℤ) - a := by
  intro a b ha hb
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  induction k with
  | zero => simp
  | succ k ih =>
    let idx : Fin n := ⟨a + k, by omega⟩
    have hstep := S.abs_sub_x idx y
    have hsucc : idx.succ = ⟨a + (k + 1), Nat.lt_succ_of_le hb⟩ :=
      Fin.ext (by simp [idx, add_assoc])
    have hcast : idx.castSucc = ⟨a + k, by omega⟩ := rfl
    rw [hsucc, hcast] at hstep
    have hih := ih (Nat.le_add_right a k) (by omega)
    have htri := abs_sub_le (S ⟨a + (k + 1), Nat.lt_succ_of_le hb⟩ y)
      (S ⟨a + k, by omega⟩ y) (S ⟨a, by omega⟩ y)
    push_cast at hih ⊢
    linarith

private theorem abs_sub_le_same_x (S : SpaceTimeSection n) (x : Fin (n + 1)) :
    ∀ {a b : ℕ} (ha : a ≤ b) (hb : b ≤ n),
      |S x ⟨b, Nat.lt_succ_of_le hb⟩ - S x ⟨a, Nat.lt_succ_of_le (ha.trans hb)⟩| ≤ (b : ℤ) - a := by
  intro a b ha hb
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  induction k with
  | zero => simp
  | succ k ih =>
    let idx : Fin n := ⟨a + k, by omega⟩
    have hstep := S.abs_sub_y x idx
    have hsucc : idx.succ = ⟨a + (k + 1), Nat.lt_succ_of_le hb⟩ :=
      Fin.ext (by simp [idx, add_assoc])
    have hcast : idx.castSucc = ⟨a + k, by omega⟩ := rfl
    rw [hsucc, hcast] at hstep
    have hih := ih (Nat.le_add_right a k) (by omega)
    have htri := abs_sub_le (S x ⟨a + (k + 1), Nat.lt_succ_of_le hb⟩)
      (S x ⟨a + k, by omega⟩) (S x ⟨a, by omega⟩)
    push_cast at hih ⊢
    linarith

/-- Every section is `1`-Lipschitz with respect to the horizontal Manhattan metric. -/
theorem abs_sub_le_manhattan (S : SpaceTimeSection n) (x₁ y₁ x₂ y₂ : Fin (n + 1)) :
    |S x₁ y₁ - S x₂ y₂| ≤ |(x₁ : ℤ) - x₂| + |(y₁ : ℤ) - y₂| := by
  have hx : |S x₁ y₁ - S x₂ y₁| ≤ |(x₁ : ℤ) - x₂| := by
    rcases le_total x₁.val x₂.val with h | h
    · have habs : |(x₁ : ℤ) - x₂| = (x₂ : ℤ) - x₁ := by
        rw [abs_sub_comm, abs_of_nonneg (by omega)]
      rw [abs_sub_comm, habs]
      exact abs_sub_le_same_y S y₁ h (Nat.le_of_lt_succ x₂.isLt)
    · have habs : |(x₁ : ℤ) - x₂| = (x₁ : ℤ) - x₂ := abs_of_nonneg (by omega)
      rw [habs]
      exact abs_sub_le_same_y S y₁ h (Nat.le_of_lt_succ x₁.isLt)
  have hy : |S x₂ y₁ - S x₂ y₂| ≤ |(y₁ : ℤ) - y₂| := by
    rcases le_total y₁.val y₂.val with h | h
    · have habs : |(y₁ : ℤ) - y₂| = (y₂ : ℤ) - y₁ := by
        rw [abs_sub_comm, abs_of_nonneg (by omega)]
      rw [abs_sub_comm, habs]
      exact abs_sub_le_same_x S x₂ h (Nat.le_of_lt_succ y₂.isLt)
    · have habs : |(y₁ : ℤ) - y₂| = (y₁ : ℤ) - y₂ := abs_of_nonneg (by omega)
      rw [habs]
      exact abs_sub_le_same_x S x₂ h (Nat.le_of_lt_succ y₁.isLt)
  linarith [abs_sub_le (S x₁ y₁) (S x₂ y₁) (S x₂ y₂)]

/-- Time-reversed section `-S`, negating every height. -/
instance : Neg (SpaceTimeSection n) where
  neg S :=
    { height := fun x y => -S x y
      even_sum := fun x y => by
        rw [Int.even_iff]
        have h := Int.even_iff.mp (S.even_sum x y)
        omega
      abs_sub_x := fun x y => by
        have h := S.abs_sub_x x y
        rw [← abs_neg] at h
        simpa [sub_eq_add_neg, add_comm] using h
      abs_sub_y := fun x y => by
        have h := S.abs_sub_y x y
        rw [← abs_neg] at h
        simpa [sub_eq_add_neg, add_comm] using h }

@[simp] theorem neg_apply (S : SpaceTimeSection n) (x y : Fin (n + 1)) : (-S) x y = -S x y := (rfl)
@[simp] theorem neg_neg_section (S : SpaceTimeSection n) : -(-S) = S := by ext x y; simp

@[simp] theorem point_neg (S : SpaceTimeSection n) (x y : Fin (n + 1)) :
    (-S).point x y = (S.point x y).timeRev := by ext <;> simp

end SpaceTimeSection

/-- The lower section `S` of the associator region `A_n`, given by `t = |x - y|`. -/
def lowerSection (n : ℕ) : SpaceTimeSection n where
  height x y := |(x : ℤ) - y|
  even_sum x y := by
    rw [Int.even_iff]
    rcases le_total (x : ℤ) y with h | h
    · rw [abs_of_nonpos (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega
  abs_sub_x x y := by
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    rcases le_or_gt ((x : ℤ) + 1) y with h | h
    · have hd : |(x : ℤ) + 1 - y| - |(x : ℤ) - y| = -1 := by
        rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; omega
      rw [hd]; rfl
    · have hd : |(x : ℤ) + 1 - y| - |(x : ℤ) - y| = 1 := by
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
      rw [hd]; rfl
  abs_sub_y x y := by
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    rcases le_or_gt ((y : ℤ) + 1) x with h | h
    · have hd : |(x : ℤ) - (y + 1)| - |(x : ℤ) - y| = -1 := by
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
      rw [hd]; rfl
    · have hd : |(x : ℤ) - (y + 1)| - |(x : ℤ) - y| = 1 := by
        rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; omega
      rw [hd]; rfl

/-- The upper section `S'` of the associator region `A_n`, given by `t = n - |n - x - y|`. -/
def upperSection (n : ℕ) : SpaceTimeSection n where
  height x y := (n : ℤ) - |(n : ℤ) - x - y|
  even_sum x y := by
    rw [Int.even_iff]
    rcases le_total ((n : ℤ) - x - y) 0 with h | h
    · rw [abs_of_nonpos h]; omega
    · rw [abs_of_nonneg h]; omega
  abs_sub_x x y := by
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    rcases le_or_gt ((x : ℤ) + y + 1) n with h | h
    · have hd : (n : ℤ) - |(n : ℤ) - (x + 1) - y| - ((n : ℤ) - |(n : ℤ) - x - y|) = 1 := by
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
      rw [hd]; rfl
    · have hd : (n : ℤ) - |(n : ℤ) - (x + 1) - y| - ((n : ℤ) - |(n : ℤ) - x - y|) = -1 := by
        rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; omega
      rw [hd]; rfl
  abs_sub_y x y := by
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    rcases le_or_gt ((x : ℤ) + y + 1) n with h | h
    · have hd : (n : ℤ) - |(n : ℤ) - x - (y + 1)| - ((n : ℤ) - |(n : ℤ) - x - y|) = 1 := by
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
      rw [hd]; rfl
    · have hd : (n : ℤ) - |(n : ℤ) - x - (y + 1)| - ((n : ℤ) - |(n : ℤ) - x - y|) = -1 := by
        rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; omega
      rw [hd]; rfl

@[simp] theorem lowerSection_apply (n : ℕ) (x y : Fin (n + 1)) :
    lowerSection n x y = |(x : ℤ) - y| := (rfl)

@[simp] theorem upperSection_apply (n : ℕ) (x y : Fin (n + 1)) :
    upperSection n x y = (n : ℤ) - |(n : ℤ) - x - y| := (rfl)

theorem lowerSection_le_upperSection (n : ℕ) : lowerSection n ≤ upperSection n := fun x y => by
  simp only [lowerSection_apply, upperSection_apply]
  have hx := x.isLt; have hy := y.isLt
  rcases le_total (x : ℤ) y with hxy | hxy <;>
    rcases le_total ((n : ℤ) - x - y) 0 with hsum | hsum
  · rw [abs_of_nonpos (by omega), abs_of_nonpos hsum]; omega
  · rw [abs_of_nonpos (by omega), abs_of_nonneg hsum]; omega
  · rw [abs_of_nonneg (by omega), abs_of_nonpos hsum]; omega
  · rw [abs_of_nonneg (by omega), abs_of_nonneg hsum]; omega

/-- `lowerSection n` and `upperSection n` coincide exactly on the four boundary walls. -/
theorem lowerSection_eq_upperSection_iff {n : ℕ} (x y : Fin (n + 1)) :
    lowerSection n x y = upperSection n x y ↔
      x.val = 0 ∨ x.val = n ∨ y.val = 0 ∨ y.val = n := by
  simp only [lowerSection_apply, upperSection_apply]
  have hx := x.isLt; have hy := y.isLt
  rcases le_total (x : ℤ) y with hxy | hxy <;>
    rcases le_total ((n : ℤ) - x - y) 0 with hsum | hsum
  · rw [abs_of_nonpos (by omega), abs_of_nonpos hsum]; omega
  · rw [abs_of_nonpos (by omega), abs_of_nonneg hsum]; omega
  · rw [abs_of_nonneg (by omega), abs_of_nonpos hsum]; omega
  · rw [abs_of_nonneg (by omega), abs_of_nonneg hsum]; omega

/-- `lowerSection n x y < upperSection n x y` holds exactly at strictly interior grid points. -/
theorem lowerSection_lt_upperSection_iff {n : ℕ} (x y : Fin (n + 1)) :
    lowerSection n x y < upperSection n x y ↔
      0 < x.val ∧ x.val < n ∧ 0 < y.val ∧ y.val < n := by
  rw [(lowerSection_le_upperSection n x y).lt_iff_ne, Ne, lowerSection_eq_upperSection_iff]
  have hx := x.isLt; have hy := y.isLt
  omega

@[simp] theorem lowerSection_zero_eq_upperSection_zero : lowerSection 0 = upperSection 0 := by
  ext x y; fin_cases x; fin_cases y; rfl

theorem AssociatorPoint.lowerSection_le_t {n : ℕ} (p : AssociatorPoint n) :
    lowerSection n p.finX p.finY ≤ p.t := p.abs_sub_le_t

theorem AssociatorPoint.t_le_upperSection {n : ℕ} (p : AssociatorPoint n) :
    p.t ≤ upperSection n p.finX p.finY := p.t_le_sub_abs

/-- Every wall point of `AssociatorPoint n` already lies on `lowerSection n` and `upperSection n`.
-/
theorem AssociatorPoint.t_eq_lowerSection_of_wall {n : ℕ} (p : AssociatorPoint n)
    (hw : p.x = 0 ∨ p.x = n ∨ p.y = 0 ∨ p.y = n) :
    p.t = lowerSection n p.finX p.finY := by
  have heq := (lowerSection_eq_upperSection_iff p.finX p.finY).mpr hw
  exact le_antisymm (heq ▸ p.t_le_sub_abs) p.abs_sub_le_t

/-- State space on a horizontal grid `Fin (n + 1) × Fin (n + 1)` with values in `R`. -/
abbrev SectionState (n : ℕ) (R : Type*) := Fin (n + 1) → Fin (n + 1) → R

/-! ### Barycentric face embeddings onto `S` and `S'` -/

section FaceEmbeddings

variable {n : ℕ}

/-- First input face embedding `(x, y, z) ↦ (n - x, z, y)` onto `S ∩ {y ≤ x}` (`d = 0`). -/
def embedLeftFst (p : Vertex n) : AssociatorPoint n :=
  TetVertex.equivAssociatorPoint ⟨p.x, p.y, p.z, 0, by have := p.sum_eq; omega⟩

/-- Second input face embedding `(x, y, z) ↦ (y, n - x, z)` onto `S ∩ {x ≤ y}` (`b = 0`). -/
def embedLeftSnd (p : Vertex n) : AssociatorPoint n :=
  TetVertex.equivAssociatorPoint ⟨p.x, 0, p.y, p.z, by have := p.sum_eq; omega⟩

/-- First output face embedding `(x, y, z) ↦ (n - z, n - x, n - y)` onto `S' ∩ {n ≤ x + y}`
(`a = 0`). -/
def embedRightFst (p : Vertex n) : AssociatorPoint n :=
  TetVertex.equivAssociatorPoint ⟨0, p.x, p.y, p.z, by have := p.sum_eq; omega⟩

/-- Second output face embedding `(x, y, z) ↦ (y, z, n - x)` onto `S' ∩ {x + y ≤ n}` (`c = 0`). -/
def embedRightSnd (p : Vertex n) : AssociatorPoint n :=
  TetVertex.equivAssociatorPoint ⟨p.x, p.y, 0, p.z, by have := p.sum_eq; omega⟩

@[simp] theorem embedLeftFst_x (p : Vertex n) : (embedLeftFst p).x = n - p.x := by
  have := p.sum_eq; simp [embedLeftFst]; omega
@[simp] theorem embedLeftFst_y (p : Vertex n) : (embedLeftFst p).y = p.z := by simp [embedLeftFst]
@[simp] theorem embedLeftFst_t (p : Vertex n) : (embedLeftFst p).t = p.y := by simp [embedLeftFst]

@[simp] theorem embedLeftSnd_x (p : Vertex n) : (embedLeftSnd p).x = p.y := by simp [embedLeftSnd]
@[simp] theorem embedLeftSnd_y (p : Vertex n) : (embedLeftSnd p).y = n - p.x := by
  have := p.sum_eq; simp [embedLeftSnd]; omega
@[simp] theorem embedLeftSnd_t (p : Vertex n) : (embedLeftSnd p).t = p.z := by simp [embedLeftSnd]

@[simp] theorem embedRightFst_x (p : Vertex n) : (embedRightFst p).x = n - p.z := by
  have := p.sum_eq; simp [embedRightFst]; omega
@[simp] theorem embedRightFst_y (p : Vertex n) : (embedRightFst p).y = n - p.x := by
  have := p.sum_eq; simp [embedRightFst]; omega
@[simp] theorem embedRightFst_t (p : Vertex n) : (embedRightFst p).t = (n : ℤ) - p.y := by
  have := p.sum_eq; simp [embedRightFst]; omega

@[simp] theorem embedRightSnd_x (p : Vertex n) : (embedRightSnd p).x = p.y := by
  simp [embedRightSnd]
@[simp] theorem embedRightSnd_y (p : Vertex n) : (embedRightSnd p).y = p.z := by
  simp [embedRightSnd]
@[simp] theorem embedRightSnd_t (p : Vertex n) : (embedRightSnd p).t = (n : ℤ) - p.x := by
  have := p.sum_eq; simp [embedRightSnd]; omega

/-- The first input face embedding `embedLeftFst` lands on `lowerSection n`. -/
theorem embedLeftFst_on_lowerSection (p : Vertex n) :
    (embedLeftFst p).t = lowerSection n (embedLeftFst p).finX (embedLeftFst p).finY := by
  have := p.sum_eq
  simp only [lowerSection_apply, SpaceTimePoint.val_finX, SpaceTimePoint.val_finY, embedLeftFst_x,
    embedLeftFst_y, embedLeftFst_t]
  rw [abs_of_nonneg (by omega)]; omega

/-- The second input face embedding `embedLeftSnd` lands on `lowerSection n`. -/
theorem embedLeftSnd_on_lowerSection (p : Vertex n) :
    (embedLeftSnd p).t = lowerSection n (embedLeftSnd p).finX (embedLeftSnd p).finY := by
  have := p.sum_eq
  simp only [lowerSection_apply, SpaceTimePoint.val_finX, SpaceTimePoint.val_finY, embedLeftSnd_x,
    embedLeftSnd_y, embedLeftSnd_t]
  rw [abs_of_nonpos (by omega)]; omega

/-- The first output face embedding `embedRightFst` lands on `upperSection n`. -/
theorem embedRightFst_on_upperSection (p : Vertex n) :
    (embedRightFst p).t = upperSection n (embedRightFst p).finX (embedRightFst p).finY := by
  have := p.sum_eq
  simp only [upperSection_apply, SpaceTimePoint.val_finX, SpaceTimePoint.val_finY, embedRightFst_x,
    embedRightFst_y, embedRightFst_t]
  rw [abs_of_nonpos (by omega)]; omega

/-- The second output face embedding `embedRightSnd` lands on `upperSection n`. -/
theorem embedRightSnd_on_upperSection (p : Vertex n) :
    (embedRightSnd p).t = upperSection n (embedRightSnd p).finX (embedRightSnd p).finY := by
  have := p.sum_eq
  simp only [upperSection_apply, SpaceTimePoint.val_finX, SpaceTimePoint.val_finY, embedRightSnd_x,
    embedRightSnd_y, embedRightSnd_t]
  rw [abs_of_nonneg (by omega)]; omega

end FaceEmbeddings

end TauCeti.Hive
