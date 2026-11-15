/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The tetrahedral-octahedral lattice, space-time sections, and hive face gluings

The size-`n` **tetrahedral lattice** `TetraVertex n` consists of nonnegative integer quadruples
`(a, b, c, d)` of sum `n`. Slicing the dilated simplex `a + b + c + d = n` by integer coordinate
hyperplanes decomposes it into translated upward unit tetrahedra (`TetraVertex 1`), unit octahedra
(`TetraVertex.IsUnitOcta`, the six `{0, 1}`-vectors of weight `2`), and downward unit tetrahedra
(`TetraVertex.IsUnitDownTetra`, the four `{0, 1}`-vectors of weight `3`).

Following Henriques and Kamnitzer, the bounded **space-time parity lattice** `SpaceTime n` consists
of triples `(x, y, t) ∈ [0, n]² × ℤ` with `x + y + t` even. A **section** (`Section n`) is a graph
`t = τ(x, y)` in `SpaceTime n` changing by `±1` along each unit grid step of `[0, n]²`; sections
form a lattice under pointwise `min` and `max` and admit an order-reversing time-reversal
involution `Section.timeRev`. The **associator region** `AssociatorPoint n` is carved out inside
`SpaceTime n` by `lowerSection n` (`t = |x - y|`) and `upperSection n` (`t = n - |n - x - y|`),
which agree precisely along the four spatial walls (`IsWallPos`). The map
`(a, b, c, d) ↦ (b + c, b + d, c + d)` identifies `TetraVertex n` bijectively with
`AssociatorPoint n` and sends each translated unit octahedron to the six space-time neighbours
`(x_c, y_c, t_c ± 1)`, `(x_c ± 1, y_c, t_c)`, `(x_c, y_c ± 1, t_c)` around an interior center.

Finally, the four boundary faces of `TetraVertex n` give four embeddings of `Hive.Vertex n` onto
`lowerSection n` (`embedInputFirst`, `embedInputSecond`) and `upperSection n` (`embedOutputFirst`,
`embedOutputSecond`). Gluing two normalized hives of boundaries `(λ, μ, σ*)` and `(σ, ν, π*)` along
the diagonal `x = y` produces a function `glueLower` on `lowerSection n`, and reading a function on
`upperSection n` back along the two upper faces (normalizing the first output face by subtracting
its `(n, 0)` corner value `|λ|`) produces functions with boundaries `(μ, ν, τ*)` and `(λ, τ, π*)`
whenever the four exterior spatial walls agree with `glueLower`.

## Main definitions

* `TauCeti.Hive.TetraVertex`, `TauCeti.Hive.TetraVertex.IsUnitOcta`,
  `TauCeti.Hive.TetraVertex.IsUnitDownTetra`: tetrahedral lattice vertices and unit cells.
* `TauCeti.Hive.SpaceTime`, `TauCeti.Hive.IsGridAdj`, `TauCeti.Hive.IsWallPos`,
  `TauCeti.Hive.IsInteriorPos`: bounded space-time parity lattice and spatial grid predicates.
* `TauCeti.Hive.Section`, `TauCeti.Hive.lowerSection`, `TauCeti.Hive.upperSection`,
  `TauCeti.Hive.AssociatorPoint`: space-time sections and the associator region.
* `TauCeti.Hive.TetraVertex.equivAssociatorPoint`: bijection `TetraVertex n ≃ AssociatorPoint n`.
* `TauCeti.Hive.embedInputFirst`, `TauCeti.Hive.embedInputSecond`,
  `TauCeti.Hive.embedOutputFirst`, `TauCeti.Hive.embedOutputSecond`: the four hive face embeddings.
* `TauCeti.Hive.glueLower`, `TauCeti.Hive.readOutputFirst`, `TauCeti.Hive.readOutputSecond`,
  `TauCeti.Hive.glueUpper`: face gluing and readout operators on `lowerSection n` and
  `upperSection n`.

## References

* A. Henriques and J. Kamnitzer, *Crystals and coboundary categories*, Duke Math. J. **132**
  (2006), 191–266, §3.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §5.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### The size-`n` tetrahedral lattice and its unit cells -/

/-- A nonnegative barycentric lattice point `(a, b, c, d)` in the tetrahedron of size `n`. -/
@[ext]
structure TetraVertex (n : ℕ) where
  /-- First barycentric coordinate (`a = 0` is the first output hive face). -/
  a : ℕ
  /-- Second barycentric coordinate (`b = 0` is the second output hive face). -/
  b : ℕ
  /-- Third barycentric coordinate (`c = 0` is the second input hive face). -/
  c : ℕ
  /-- Fourth barycentric coordinate (`d = 0` is the first input hive face). -/
  d : ℕ
  /-- The four barycentric coordinates sum to `n`. -/
  sum_eq : a + b + c + d = n
  deriving DecidableEq

namespace TetraVertex

variable {n : ℕ}

/-- The four barycentric coordinates indexed by `Fin 4`. -/
def coord (q : TetraVertex n) : Fin 4 → ℕ := ![q.a, q.b, q.c, q.d]

@[simp] theorem coord_zero (q : TetraVertex n) : q.coord 0 = q.a := (rfl)
@[simp] theorem coord_one (q : TetraVertex n) : q.coord 1 = q.b := (rfl)
@[simp] theorem coord_two (q : TetraVertex n) : q.coord 2 = q.c := (rfl)
@[simp] theorem coord_three (q : TetraVertex n) : q.coord 3 = q.d := (rfl)

/-- Identify `TetraVertex n` with the computably enumerated `4`-tuples of sum `n`. -/
def equivAntidiagonalTuple : TetraVertex n ≃ ↥(Finset.Nat.antidiagonalTuple 4 n) where
  toFun q := ⟨q.coord, by
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa [coord, Fin.sum_univ_four, add_assoc] using q.sum_eq⟩
  invFun t := ⟨t.1 0, t.1 1, t.1 2, t.1 3, by
    have ht := Finset.Nat.mem_antidiagonalTuple.mp t.2
    simpa [Fin.sum_univ_four, add_assoc] using ht⟩
  left_inv q := by ext <;> rfl
  right_inv t := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

instance : Fintype (TetraVertex n) := Fintype.ofEquiv _ equivAntidiagonalTuple.symm

instance uniqueZero : Unique (TetraVertex 0) where
  default := ⟨0, 0, 0, 0, rfl⟩
  uniq q := by have := q.sum_eq; ext <;> simp <;> omega

/-- Coordinatewise addition, translating a unit cell inside a larger tetrahedron. -/
def add {m : ℕ} (p : TetraVertex n) (q : TetraVertex m) : TetraVertex (n + m) :=
  ⟨p.a + q.a, p.b + q.b, p.c + q.c, p.d + q.d, by have := p.sum_eq; have := q.sum_eq; omega⟩

@[simp] theorem add_a {m : ℕ} (p : TetraVertex n) (q : TetraVertex m) :
    (p.add q).a = p.a + q.a := (rfl)
@[simp] theorem add_b {m : ℕ} (p : TetraVertex n) (q : TetraVertex m) :
    (p.add q).b = p.b + q.b := (rfl)
@[simp] theorem add_c {m : ℕ} (p : TetraVertex n) (q : TetraVertex m) :
    (p.add q).c = p.c + q.c := (rfl)
@[simp] theorem add_d {m : ℕ} (p : TetraVertex n) (q : TetraVertex m) :
    (p.add q).d = p.d + q.d := (rfl)

/-- The `i`-th corner of `TetraVertex n`, placing weight `n` in coordinate `i`. -/
def corner (n : ℕ) : Fin 4 → TetraVertex n
  | ⟨0, _⟩ => ⟨n, 0, 0, 0, by omega⟩
  | ⟨1, _⟩ => ⟨0, n, 0, 0, by omega⟩
  | ⟨2, _⟩ => ⟨0, 0, n, 0, by omega⟩
  | ⟨3, _⟩ => ⟨0, 0, 0, n, by omega⟩

/-- The unit upward tetrahedron `TetraVertex 1` has `4` vertices. -/
theorem card_one : Fintype.card (TetraVertex 1) = 4 := by decide

/-- A vertex of the unit octahedron inside `TetraVertex 2`: a `{0, 1}`-quadruple of sum `2`. -/
def IsUnitOcta (u : TetraVertex 2) : Prop := u.a ≤ 1 ∧ u.b ≤ 1 ∧ u.c ≤ 1 ∧ u.d ≤ 1

theorem isUnitOcta_def (u : TetraVertex 2) :
    u.IsUnitOcta ↔ u.a ≤ 1 ∧ u.b ≤ 1 ∧ u.c ≤ 1 ∧ u.d ≤ 1 := Iff.rfl

instance (u : TetraVertex 2) : Decidable u.IsUnitOcta :=
  decidable_of_iff _ (isUnitOcta_def u).symm

/-- The unit octahedron inside `TetraVertex 2` has `6` vertices. -/
theorem card_isUnitOcta : Fintype.card {u : TetraVertex 2 // u.IsUnitOcta} = 6 := by decide

/-- A vertex of the unit downward tetrahedron inside `TetraVertex 3`: a `{0, 1}`-quadruple of
sum `3`. -/
def IsUnitDownTetra (u : TetraVertex 3) : Prop := u.a ≤ 1 ∧ u.b ≤ 1 ∧ u.c ≤ 1 ∧ u.d ≤ 1

theorem isUnitDownTetra_def (u : TetraVertex 3) :
    u.IsUnitDownTetra ↔ u.a ≤ 1 ∧ u.b ≤ 1 ∧ u.c ≤ 1 ∧ u.d ≤ 1 := Iff.rfl

instance (u : TetraVertex 3) : Decidable u.IsUnitDownTetra :=
  decidable_of_iff _ (isUnitDownTetra_def u).symm

/-- The unit downward tetrahedron inside `TetraVertex 3` has `4` vertices. -/
theorem card_isUnitDownTetra : Fintype.card {u : TetraVertex 3 // u.IsUnitDownTetra} = 4 := by
  decide

end TetraVertex

/-! ### Spatial grid predicates and the bounded space-time parity lattice -/

/-- Unit Manhattan adjacency on the spatial grid `[0, n]²`. -/
def IsGridAdj {n : ℕ} (p q : Fin (n + 1) × Fin (n + 1)) : Prop :=
  |(p.1.val : ℤ) - q.1.val| + |(p.2.val : ℤ) - q.2.val| = 1

theorem isGridAdj_def {n : ℕ} (p q : Fin (n + 1) × Fin (n + 1)) :
    IsGridAdj p q ↔ |(p.1.val : ℤ) - q.1.val| + |(p.2.val : ℤ) - q.2.val| = 1 := Iff.rfl

instance {n : ℕ} (p q : Fin (n + 1) × Fin (n + 1)) : Decidable (IsGridAdj p q) :=
  decidable_of_iff _ (isGridAdj_def p q).symm

theorem IsGridAdj.symm {n : ℕ} {p q : Fin (n + 1) × Fin (n + 1)} (h : IsGridAdj p q) :
    IsGridAdj q p := by
  rw [isGridAdj_def] at h ⊢
  rwa [abs_sub_comm (q.1.val : ℤ), abs_sub_comm (q.2.val : ℤ)]

theorem IsGridAdj.ne {n : ℕ} {p q : Fin (n + 1) × Fin (n + 1)} (h : IsGridAdj p q) : p ≠ q := by
  rintro rfl
  simp [isGridAdj_def] at h

/-- Along a unit grid edge, `(p.1 + p.2)` and `(q.1 + q.2)` differ by `±1`. -/
theorem IsGridAdj.odd_sum_sub {n : ℕ} {p q : Fin (n + 1) × Fin (n + 1)} (h : IsGridAdj p q) :
    Odd (((p.1.val : ℤ) + p.2.val) - ((q.1.val : ℤ) + q.2.val)) := by
  rw [isGridAdj_def] at h
  rw [Int.odd_iff]
  rcases abs_cases ((p.1.val : ℤ) - q.1.val) with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases abs_cases ((p.2.val : ℤ) - q.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

/-- A point `p ∈ [0, n]²` lies on one of the four exterior walls `x ∈ {0, n}` or `y ∈ {0, n}`. -/
def IsWallPos {n : ℕ} (p : Fin (n + 1) × Fin (n + 1)) : Prop :=
  p.1.val = 0 ∨ p.1.val = n ∨ p.2.val = 0 ∨ p.2.val = n

theorem isWallPos_def {n : ℕ} (p : Fin (n + 1) × Fin (n + 1)) :
    IsWallPos p ↔ p.1.val = 0 ∨ p.1.val = n ∨ p.2.val = 0 ∨ p.2.val = n := Iff.rfl

instance {n : ℕ} (p : Fin (n + 1) × Fin (n + 1)) : Decidable (IsWallPos p) :=
  decidable_of_iff _ (isWallPos_def p).symm

/-- A point `p ∈ [0, n]²` lies strictly in the spatial interior `(0, n)²`. -/
def IsInteriorPos {n : ℕ} (p : Fin (n + 1) × Fin (n + 1)) : Prop :=
  0 < p.1.val ∧ p.1.val < n ∧ 0 < p.2.val ∧ p.2.val < n

theorem isInteriorPos_def {n : ℕ} (p : Fin (n + 1) × Fin (n + 1)) :
    IsInteriorPos p ↔ 0 < p.1.val ∧ p.1.val < n ∧ 0 < p.2.val ∧ p.2.val < n := Iff.rfl

instance {n : ℕ} (p : Fin (n + 1) × Fin (n + 1)) : Decidable (IsInteriorPos p) :=
  decidable_of_iff _ (isInteriorPos_def p).symm

theorem not_isWallPos_iff_isInteriorPos {n : ℕ} (p : Fin (n + 1) × Fin (n + 1)) :
    ¬ IsWallPos p ↔ IsInteriorPos p := by
  have hx := p.1.isLt
  have hy := p.2.isLt
  simp only [IsWallPos, IsInteriorPos]
  omega

/-- A point `(x, y, t)` of Henriques–Kamnitzer's bounded space-time parity lattice
`L_n = {(x, y, t) ∈ [0, n]² × ℤ : x + y + t even}`. -/
@[ext]
structure SpaceTime (n : ℕ) where
  /-- First spatial coordinate in `[0, n]`. -/
  x : Fin (n + 1)
  /-- Second spatial coordinate in `[0, n]`. -/
  y : Fin (n + 1)
  /-- Integer time coordinate. -/
  t : ℤ
  /-- Parity constraint placing `(x, y, t)` on the octahedral sublattice. -/
  even_sum : Even ((x.val : ℤ) + y.val + t)
  deriving DecidableEq

namespace SpaceTime

variable {n : ℕ}

/-- The spatial projection `(x, y) ∈ [0, n]²` of a space-time point. -/
def pos (p : SpaceTime n) : Fin (n + 1) × Fin (n + 1) := (p.x, p.y)

@[simp] theorem pos_fst (p : SpaceTime n) : p.pos.1 = p.x := (rfl)
@[simp] theorem pos_snd (p : SpaceTime n) : p.pos.2 = p.y := (rfl)

/-- Time reversal `(x, y, t) ↦ (x, y, -t)` on `SpaceTime n`. -/
def timeRev (p : SpaceTime n) : SpaceTime n where
  x := p.x
  y := p.y
  t := -p.t
  even_sum := by
    have h := Int.even_iff.mp p.even_sum
    rw [Int.even_iff]
    omega

@[simp] theorem timeRev_x (p : SpaceTime n) : p.timeRev.x = p.x := (rfl)
@[simp] theorem timeRev_y (p : SpaceTime n) : p.timeRev.y = p.y := (rfl)
@[simp] theorem timeRev_t (p : SpaceTime n) : p.timeRev.t = -p.t := (rfl)

@[simp] theorem timeRev_timeRev (p : SpaceTime n) : p.timeRev.timeRev = p := by
  ext <;> simp

theorem timeRev_involutive : Function.Involutive (timeRev (n := n)) := timeRev_timeRev

/-- Two space-time points over the same spatial position differ by an even time step. -/
theorem even_sub_t {p q : SpaceTime n} (hx : p.x = q.x) (hy : p.y = q.y) :
    Even (p.t - q.t) := by
  have hp := Int.even_iff.mp p.even_sum
  have hq := Int.even_iff.mp q.even_sum
  rw [hx, hy] at hp
  rw [Int.even_iff]
  omega

end SpaceTime

/-! ### Space-time sections and the associator region -/

/-- A **section** in `SpaceTime n`: a height function `τ : [0, n]² → ℤ` landing in the parity
lattice and changing by at most `1` (hence by `±1`) along every unit grid edge. -/
structure Section (n : ℕ) where
  /-- The height assigned to each spatial grid point. -/
  height : Fin (n + 1) × Fin (n + 1) → ℤ
  /-- Every point `(x, y, τ(x, y))` has `x + y + τ(x, y)` even. -/
  even_sum : ∀ p, Even ((p.1.val : ℤ) + p.2.val + height p)
  /-- Along every unit spatial step, the height changes by at most `1`. -/
  abs_sub_le_one : ∀ ⦃p q⦄, IsGridAdj p q → |height p - height q| ≤ 1

namespace Section

variable {n : ℕ}

instance instFunLike : FunLike (Section n) (Fin (n + 1) × Fin (n + 1)) ℤ where
  coe := Section.height
  coe_injective τ₁ τ₂ h := by cases τ₁; cases τ₂; congr

@[simp] theorem height_eq_coe (τ : Section n) : τ.height = ⇑τ := (rfl)

@[ext] theorem ext {τ₁ τ₂ : Section n} (h : ∀ p, τ₁ p = τ₂ p) : τ₁ = τ₂ :=
  DFunLike.ext τ₁ τ₂ h

instance : DecidableEq (Section n) := fun τ₁ τ₂ =>
  decidable_of_iff (∀ p, τ₁ p = τ₂ p) ⟨ext, fun h p => congrArg (· p) h⟩

@[simp] theorem mk_apply (f : Fin (n + 1) × Fin (n + 1) → ℤ)
    (hev : ∀ p, Even ((p.1.val : ℤ) + p.2.val + f p))
    (hsl : ∀ ⦃p q⦄, IsGridAdj p q → |f p - f q| ≤ 1)
    (p : Fin (n + 1) × Fin (n + 1)) : (⟨f, hev, hsl⟩ : Section n) p = f p := (rfl)

theorem even_sum_apply (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    Even ((p.1.val : ℤ) + p.2.val + τ p) :=
  τ.even_sum p

theorem abs_sub_le_one_apply (τ : Section n) {p q : Fin (n + 1) × Fin (n + 1)}
    (h : IsGridAdj p q) : |τ p - τ q| ≤ 1 :=
  τ.abs_sub_le_one h

/-- By parity, a section changes by **exact** slope `±1` across every unit grid edge. -/
@[simp] theorem abs_sub_eq_one (τ : Section n) {p q : Fin (n + 1) × Fin (n + 1)}
    (h : IsGridAdj p q) : |τ p - τ q| = 1 := by
  have hle := τ.abs_sub_le_one_apply h
  have hp := Int.even_iff.mp (τ.even_sum_apply p)
  have hq := Int.even_iff.mp (τ.even_sum_apply q)
  have hodd := Int.odd_iff.mp h.odd_sum_sub
  rcases abs_cases (τ p - τ q) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

/-- Two sections evaluate to integers of the same parity at every grid point. -/
theorem even_sub (τ₁ τ₂ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    Even (τ₁ p - τ₂ p) := by
  have h₁ := Int.even_iff.mp (τ₁.even_sum_apply p)
  have h₂ := Int.even_iff.mp (τ₂.even_sum_apply p)
  rw [Int.even_iff]
  omega

/-- If `τ₁ p < τ₂ p`, parity forces `τ₁ p + 2 ≤ τ₂ p`. -/
theorem add_two_le_of_lt {τ₁ τ₂ : Section n} {p : Fin (n + 1) × Fin (n + 1)}
    (h : τ₁ p < τ₂ p) : τ₁ p + 2 ≤ τ₂ p := by
  have hev := Int.even_iff.mp (even_sub τ₂ τ₁ p)
  omega

/-- The space-time point `(p.1, p.2, τ p)` on the graph of `τ`. -/
def point (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) : SpaceTime n :=
  ⟨p.1, p.2, τ p, τ.even_sum_apply p⟩

@[simp] theorem point_x (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    (τ.point p).x = p.1 := (rfl)
@[simp] theorem point_y (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    (τ.point p).y = p.2 := (rfl)
@[simp] theorem point_t (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    (τ.point p).t = τ p := (rfl)

instance : PartialOrder (Section n) :=
  PartialOrder.lift (⇑·) DFunLike.coe_injective

theorem le_def {τ₁ τ₂ : Section n} : τ₁ ≤ τ₂ ↔ ∀ p, τ₁ p ≤ τ₂ p := Iff.rfl

instance : Lattice (Section n) where
  sup τ₁ τ₂ := ⟨fun p => τ₁ p ⊔ τ₂ p,
    fun p => by
      rcases le_total (τ₁ p) (τ₂ p) with h | h
      · rw [sup_of_le_right h]; exact τ₂.even_sum_apply p
      · rw [sup_of_le_left h]; exact τ₁.even_sum_apply p,
    fun p q hadj => by
      have h₁ := abs_le.mp (τ₁.abs_sub_le_one_apply hadj)
      have h₂ := abs_le.mp (τ₂.abs_sub_le_one_apply hadj)
      rw [abs_le]
      rcases le_total (τ₁ p) (τ₂ p) with hp | hp
      · rw [sup_of_le_right hp]
        rcases le_total (τ₁ q) (τ₂ q) with hq | hq
        · rw [sup_of_le_right hq]; exact ⟨by omega, by omega⟩
        · rw [sup_of_le_left hq]; exact ⟨by omega, by omega⟩
      · rw [sup_of_le_left hp]
        rcases le_total (τ₁ q) (τ₂ q) with hq | hq
        · rw [sup_of_le_right hq]; exact ⟨by omega, by omega⟩
        · rw [sup_of_le_left hq]; exact ⟨by omega, by omega⟩⟩
  le_sup_left _ _ p := le_sup_left
  le_sup_right _ _ p := le_sup_right
  sup_le _ _ _ h₁ h₂ p := sup_le (h₁ p) (h₂ p)
  inf τ₁ τ₂ := ⟨fun p => τ₁ p ⊓ τ₂ p,
    fun p => by
      rcases le_total (τ₁ p) (τ₂ p) with h | h
      · rw [inf_of_le_left h]; exact τ₁.even_sum_apply p
      · rw [inf_of_le_right h]; exact τ₂.even_sum_apply p,
    fun p q hadj => by
      have h₁ := abs_le.mp (τ₁.abs_sub_le_one_apply hadj)
      have h₂ := abs_le.mp (τ₂.abs_sub_le_one_apply hadj)
      rw [abs_le]
      rcases le_total (τ₁ p) (τ₂ p) with hp | hp
      · rw [inf_of_le_left hp]
        rcases le_total (τ₁ q) (τ₂ q) with hq | hq
        · rw [inf_of_le_left hq]; exact ⟨by omega, by omega⟩
        · rw [inf_of_le_right hq]; exact ⟨by omega, by omega⟩
      · rw [inf_of_le_right hp]
        rcases le_total (τ₁ q) (τ₂ q) with hq | hq
        · rw [inf_of_le_left hq]; exact ⟨by omega, by omega⟩
        · rw [inf_of_le_right hq]; exact ⟨by omega, by omega⟩⟩
  inf_le_left _ _ p := inf_le_left
  inf_le_right _ _ p := inf_le_right
  le_inf _ _ _ h₁ h₂ p := le_inf (h₁ p) (h₂ p)

@[simp] theorem sup_apply (τ₁ τ₂ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    (τ₁ ⊔ τ₂) p = τ₁ p ⊔ τ₂ p := (rfl)
@[simp] theorem inf_apply (τ₁ τ₂ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    (τ₁ ⊓ τ₂) p = τ₁ p ⊓ τ₂ p := (rfl)

/-- Time reversal of a section: `p ↦ -τ p`. -/
def timeRev (τ : Section n) : Section n where
  height p := -τ p
  even_sum p := (τ.point p).timeRev.even_sum
  abs_sub_le_one p q hadj := by
    have h := τ.abs_sub_le_one_apply hadj
    have hneg : -τ p - -τ q = -(τ p - τ q) := by ring
    rwa [hneg, abs_neg]

@[simp] theorem timeRev_apply (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    τ.timeRev p = -τ p := (rfl)

@[simp] theorem timeRev_timeRev (τ : Section n) : τ.timeRev.timeRev = τ := by
  ext p; simp

@[simp] theorem point_timeRev (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    τ.timeRev.point p = (τ.point p).timeRev := (rfl)

@[simp] theorem timeRev_le_timeRev_iff {τ₁ τ₂ : Section n} :
    τ₁.timeRev ≤ τ₂.timeRev ↔ τ₂ ≤ τ₁ :=
  ⟨fun h p => neg_le_neg_iff.mp (h p), fun h p => neg_le_neg (h p)⟩

/-- Minimum height attained by a section on `[0, n]²`. -/
def minHeight (τ : Section n) : ℤ :=
  Finset.univ.inf' Finset.univ_nonempty (fun p => τ p)

theorem minHeight_le (τ : Section n) (p : Fin (n + 1) × Fin (n + 1)) :
    τ.minHeight ≤ τ p :=
  Finset.inf'_le _ (Finset.mem_univ p)

end Section

/-- The lower section `S` of the associator region: `t = |x - y|`. -/
def lowerSection (n : ℕ) : Section n where
  height p := |(p.1.val : ℤ) - p.2.val|
  even_sum p := by
    rw [Int.even_iff]
    rcases abs_cases ((p.1.val : ℤ) - p.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  abs_sub_le_one p q hadj := by
    rw [isGridAdj_def] at hadj
    rw [abs_le]
    rcases abs_cases ((p.1.val : ℤ) - q.1.val) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases ((p.2.val : ℤ) - q.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases ((p.1.val : ℤ) - p.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases ((q.1.val : ℤ) - q.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

@[simp] theorem lowerSection_apply (n : ℕ) (p : Fin (n + 1) × Fin (n + 1)) :
    lowerSection n p = |(p.1.val : ℤ) - p.2.val| := (rfl)

/-- The upper section `S'` of the associator region: `t = n - |n - x - y|`. -/
def upperSection (n : ℕ) : Section n where
  height p := (n : ℤ) - |(n : ℤ) - p.1.val - p.2.val|
  even_sum p := by
    rw [Int.even_iff]
    rcases abs_cases ((n : ℤ) - p.1.val - p.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  abs_sub_le_one p q hadj := by
    rw [isGridAdj_def] at hadj
    rw [abs_le]
    rcases abs_cases ((p.1.val : ℤ) - q.1.val) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases ((p.2.val : ℤ) - q.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases ((n : ℤ) - p.1.val - p.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases ((n : ℤ) - q.1.val - q.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

@[simp] theorem upperSection_apply (n : ℕ) (p : Fin (n + 1) × Fin (n + 1)) :
    upperSection n p = (n : ℤ) - |(n : ℤ) - p.1.val - p.2.val| := (rfl)

/-- The lower section lies below the upper section everywhere on `[0, n]²`. -/
theorem lowerSection_le_upperSection (n : ℕ) : lowerSection n ≤ upperSection n := by
  intro p
  have hx := p.1.isLt
  have hy := p.2.isLt
  simp only [lowerSection_apply, upperSection_apply]
  rcases abs_cases ((p.1.val : ℤ) - p.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases abs_cases ((n : ℤ) - p.1.val - p.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

/-- `lowerSection n` and `upperSection n` agree at `p` precisely when `p` lies on one of the four
exterior walls of `[0, n]²`. -/
theorem lowerSection_eq_upperSection_iff {n : ℕ} (p : Fin (n + 1) × Fin (n + 1)) :
    lowerSection n p = upperSection n p ↔ IsWallPos p := by
  have hx := p.1.isLt
  have hy := p.2.isLt
  simp only [lowerSection_apply, upperSection_apply, IsWallPos]
  rcases abs_cases ((p.1.val : ℤ) - p.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases abs_cases ((n : ℤ) - p.1.val - p.2.val) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

/-- `lowerSection n p < upperSection n p` holds precisely at strictly interior points `p`. -/
theorem lowerSection_lt_upperSection_iff {n : ℕ} (p : Fin (n + 1) × Fin (n + 1)) :
    lowerSection n p < upperSection n p ↔ IsInteriorPos p := by
  rw [← not_isWallPos_iff_isInteriorPos, ← lowerSection_eq_upperSection_iff, lt_iff_le_and_ne]
  exact and_iff_right (lowerSection_le_upperSection n p)

@[simp] theorem lowerSection_zero_eq_upperSection : lowerSection 0 = upperSection 0 := by
  ext p
  exact (lowerSection_eq_upperSection_iff p).mpr (Or.inl (Fin.eq_zero p.1 ▸ rfl))

@[simp] theorem lowerSection_one_eq_upperSection : lowerSection 1 = upperSection 1 := by
  ext p
  refine (lowerSection_eq_upperSection_iff p).mpr ?_
  simp only [IsWallPos]
  omega

/-! ### The associator region and its bijection with `TetraVertex n` -/

/-- Membership in the associator region `A_n = {|x - y| ≤ t ≤ n - |n - x - y|}` inside
`SpaceTime n`. -/
def SpaceTime.InAssociator {n : ℕ} (p : SpaceTime n) : Prop :=
  lowerSection n (p.x, p.y) ≤ p.t ∧ p.t ≤ upperSection n (p.x, p.y)

theorem SpaceTime.inAssociator_def {n : ℕ} (p : SpaceTime n) :
    p.InAssociator ↔ lowerSection n (p.x, p.y) ≤ p.t ∧ p.t ≤ upperSection n (p.x, p.y) :=
  Iff.rfl

instance {n : ℕ} (p : SpaceTime n) : Decidable p.InAssociator :=
  decidable_of_iff _ (SpaceTime.inAssociator_def p).symm

/-- The subtype of lattice points in the associator region `A_n ⊆ SpaceTime n`. -/
abbrev AssociatorPoint (n : ℕ) : Type := {p : SpaceTime n // p.InAssociator}

/-- Every section sandwiched between `lowerSection n` and `upperSection n` stays inside `A_n`. -/
theorem Section.point_inAssociator {n : ℕ} {τ : Section n}
    (hlo : lowerSection n ≤ τ) (hhi : τ ≤ upperSection n)
    (p : Fin (n + 1) × Fin (n + 1)) : (τ.point p).InAssociator :=
  ⟨hlo p, hhi p⟩

/-- Map a tetrahedral lattice vertex `(a, b, c, d)` to `(b + c, b + d, c + d)` in `SpaceTime n`. -/
def TetraVertex.toSpaceTime {n : ℕ} (q : TetraVertex n) : SpaceTime n where
  x := ⟨q.b + q.c, by have := q.sum_eq; omega⟩
  y := ⟨q.b + q.d, by have := q.sum_eq; omega⟩
  t := (q.c : ℤ) + q.d
  even_sum := by simp only [Int.even_iff]; omega

@[simp] theorem TetraVertex.toSpaceTime_x {n : ℕ} (q : TetraVertex n) :
    q.toSpaceTime.x.val = q.b + q.c := (rfl)
@[simp] theorem TetraVertex.toSpaceTime_y {n : ℕ} (q : TetraVertex n) :
    q.toSpaceTime.y.val = q.b + q.d := (rfl)
@[simp] theorem TetraVertex.toSpaceTime_t {n : ℕ} (q : TetraVertex n) :
    q.toSpaceTime.t = (q.c : ℤ) + q.d := (rfl)

theorem TetraVertex.toSpaceTime_inAssociator {n : ℕ} (q : TetraVertex n) :
    q.toSpaceTime.InAssociator := by
  have hsum := q.sum_eq
  simp only [SpaceTime.InAssociator, lowerSection_apply, upperSection_apply,
    toSpaceTime_x, toSpaceTime_y, toSpaceTime_t]
  rcases abs_cases (((q.b + q.c : ℕ) : ℤ) - (q.b + q.d : ℕ)) with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases abs_cases ((n : ℤ) - (q.b + q.c : ℕ) - (q.b + q.d : ℕ)) with ⟨_, _⟩ | ⟨_, _⟩ <;>
    exact ⟨by omega, by omega⟩

private theorem associator_bounds {n : ℕ} (p : AssociatorPoint n) :
    (p.1.x.val : ℤ) - p.1.y.val ≤ p.1.t ∧ (p.1.y.val : ℤ) - p.1.x.val ≤ p.1.t ∧
      p.1.t ≤ (p.1.x.val : ℤ) + p.1.y.val ∧
      p.1.t ≤ 2 * (n : ℤ) - p.1.x.val - p.1.y.val := by
  obtain ⟨hlo, hhi⟩ := p.2
  simp only [lowerSection_apply, upperSection_apply] at hlo hhi
  have hlo' := abs_le.mp hlo
  have hhi' := abs_le.mp (by linarith : |(n : ℤ) - p.1.x.val - p.1.y.val| ≤ (n : ℤ) - p.1.t)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Recover the tetrahedral vertex `(a, b, c, d)` from an associator point `(X, Y, T)`. -/
def AssociatorPoint.toTetraVertex {n : ℕ} (p : AssociatorPoint n) : TetraVertex n where
  a := ((2 * (n : ℤ) - p.1.x.val - p.1.y.val - p.1.t) / 2).toNat
  b := (((p.1.x.val : ℤ) + p.1.y.val - p.1.t) / 2).toNat
  c := ((p.1.t + p.1.x.val - p.1.y.val) / 2).toNat
  d := ((p.1.t - p.1.x.val + p.1.y.val) / 2).toNat
  sum_eq := by
    have hev := Int.even_iff.mp p.1.even_sum
    obtain ⟨h1, h2, h3, h4⟩ := associator_bounds p
    omega

/-- Explicit bijection `(a, b, c, d) ↦ (b + c, b + d, c + d)` between the size-`n` tetrahedral
lattice and Henriques–Kamnitzer's associator region `A_n`. -/
def TetraVertex.equivAssociatorPoint (n : ℕ) : TetraVertex n ≃ AssociatorPoint n where
  toFun q := ⟨q.toSpaceTime, q.toSpaceTime_inAssociator⟩
  invFun := AssociatorPoint.toTetraVertex
  left_inv q := by
    have hsum := q.sum_eq
    ext <;> simp [AssociatorPoint.toTetraVertex] <;> omega
  right_inv p := by
    have hev := Int.even_iff.mp p.1.even_sum
    obtain ⟨h1, h2, h3, _⟩ := associator_bounds p
    apply Subtype.ext
    ext <;> simp only [AssociatorPoint.toTetraVertex, toSpaceTime_x, toSpaceTime_y,
      toSpaceTime_t] <;> omega

@[simp] theorem TetraVertex.equivAssociatorPoint_apply {n : ℕ} (q : TetraVertex n) :
    (TetraVertex.equivAssociatorPoint n q).1 = q.toSpaceTime := (rfl)

@[simp] theorem TetraVertex.equivAssociatorPoint_symm_apply {n : ℕ} (p : AssociatorPoint n) :
    (TetraVertex.equivAssociatorPoint n).symm p = p.toTetraVertex := (rfl)

instance (n : ℕ) : Fintype (AssociatorPoint n) :=
  Fintype.ofEquiv (TetraVertex n) (TetraVertex.equivAssociatorPoint n)

/-- At `n = 0`, `AssociatorPoint 0` consists solely of `(0, 0, 0)`. -/
instance uniqueAssociatorZero : Unique (AssociatorPoint 0) :=
  (TetraVertex.equivAssociatorPoint 0).symm.unique

/-- Each unit octahedron translated by `p₀ : TetraVertex m` maps to the six space-time vertices
`(x_c, y_c, t_c ± 1)`, `(x_c ± 1, y_c, t_c)`, `(x_c, y_c ± 1, t_c)` centered at the strictly
interior position `(b₀ + c₀ + 1, b₀ + d₀ + 1, c₀ + d₀ + 1)`. -/
theorem TetraVertex.toSpaceTime_octahedron {m : ℕ} (p₀ : TetraVertex m)
    {u : TetraVertex 2} (hu : u.IsUnitOcta) :
    let xc : ℤ := (p₀.b : ℤ) + p₀.c + 1
    let yc : ℤ := (p₀.b : ℤ) + p₀.d + 1
    let tc : ℤ := (p₀.c : ℤ) + p₀.d + 1
    (0 < xc ∧ xc < m + 2 ∧ 0 < yc ∧ yc < m + 2) ∧
      let s := (p₀.add u).toSpaceTime
      ((s.x.val : ℤ), (s.y.val : ℤ), s.t) ∈
        ({(xc, yc, tc - 1), (xc, yc, tc + 1),
          (xc + 1, yc, tc), (xc - 1, yc, tc),
          (xc, yc + 1, tc), (xc, yc - 1, tc)} : Set (ℤ × ℤ × ℤ)) := by
  have hp₀ := p₀.sum_eq
  have hu_sum := u.sum_eq
  obtain ⟨ha, hb, hc, hd⟩ := hu
  refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
    toSpaceTime_x, toSpaceTime_y, toSpaceTime_t, add_b, add_c, add_d, Nat.cast_add]
  omega

/-! ### Four hive face embeddings onto `lowerSection n` and `upperSection n` -/

/-- First input face embedding `(x, y, z) ↦ (n - x, z, y)`, landing on `lowerSection n` in the
half `Y ≤ X` (corresponding to `d = 0` in `TetraVertex n`). -/
def embedInputFirst {n : ℕ} (p : Vertex n) : SpaceTime n where
  x := ⟨n - p.x, by omega⟩
  y := ⟨p.z, by have := p.sum_eq; omega⟩
  t := p.y
  even_sum := by have := p.sum_eq; simp only [Int.even_iff]; omega

/-- Second input face embedding `(x, y, z) ↦ (y, n - x, z)`, landing on `lowerSection n` in the
half `X ≤ Y` (corresponding to `c = 0` in `TetraVertex n`). -/
def embedInputSecond {n : ℕ} (p : Vertex n) : SpaceTime n where
  x := ⟨p.y, by have := p.sum_eq; omega⟩
  y := ⟨n - p.x, by omega⟩
  t := p.z
  even_sum := by have := p.sum_eq; simp only [Int.even_iff]; omega

/-- First output face embedding `(x, y, z) ↦ (n - z, n - x, n - y)`, landing on `upperSection n`
in the half `n ≤ X + Y` (corresponding to `a = 0` in `TetraVertex n`). -/
def embedOutputFirst {n : ℕ} (p : Vertex n) : SpaceTime n where
  x := ⟨n - p.z, by omega⟩
  y := ⟨n - p.x, by omega⟩
  t := (n : ℤ) - p.y
  even_sum := by have := p.sum_eq; simp only [Int.even_iff]; omega

/-- Second output face embedding `(x, y, z) ↦ (y, z, n - x)`, landing on `upperSection n` in the
half `X + Y ≤ n` (corresponding to `b = 0` in `TetraVertex n`). -/
def embedOutputSecond {n : ℕ} (p : Vertex n) : SpaceTime n where
  x := ⟨p.y, by have := p.sum_eq; omega⟩
  y := ⟨p.z, by have := p.sum_eq; omega⟩
  t := (n : ℤ) - p.x
  even_sum := by have := p.sum_eq; simp only [Int.even_iff]; omega

@[simp] theorem embedInputFirst_x {n : ℕ} (p : Vertex n) :
    (embedInputFirst p).x.val = n - p.x := (rfl)
@[simp] theorem embedInputFirst_y {n : ℕ} (p : Vertex n) :
    (embedInputFirst p).y.val = p.z := (rfl)
@[simp] theorem embedInputFirst_t {n : ℕ} (p : Vertex n) :
    (embedInputFirst p).t = p.y := (rfl)

@[simp] theorem embedInputSecond_x {n : ℕ} (p : Vertex n) :
    (embedInputSecond p).x.val = p.y := (rfl)
@[simp] theorem embedInputSecond_y {n : ℕ} (p : Vertex n) :
    (embedInputSecond p).y.val = n - p.x := (rfl)
@[simp] theorem embedInputSecond_t {n : ℕ} (p : Vertex n) :
    (embedInputSecond p).t = p.z := (rfl)

@[simp] theorem embedOutputFirst_x {n : ℕ} (p : Vertex n) :
    (embedOutputFirst p).x.val = n - p.z := (rfl)
@[simp] theorem embedOutputFirst_y {n : ℕ} (p : Vertex n) :
    (embedOutputFirst p).y.val = n - p.x := (rfl)
@[simp] theorem embedOutputFirst_t {n : ℕ} (p : Vertex n) :
    (embedOutputFirst p).t = (n : ℤ) - p.y := (rfl)

@[simp] theorem embedOutputSecond_x {n : ℕ} (p : Vertex n) :
    (embedOutputSecond p).x.val = p.y := (rfl)
@[simp] theorem embedOutputSecond_y {n : ℕ} (p : Vertex n) :
    (embedOutputSecond p).y.val = p.z := (rfl)
@[simp] theorem embedOutputSecond_t {n : ℕ} (p : Vertex n) :
    (embedOutputSecond p).t = (n : ℤ) - p.x := (rfl)

theorem embedInputFirst_eq_point {n : ℕ} (p : Vertex n) :
    embedInputFirst p =
      (lowerSection n).point (⟨n - p.x, by omega⟩, ⟨p.z, by have := p.sum_eq; omega⟩) := by
  have hp := p.sum_eq
  ext
  · rfl
  · rfl
  · simp only [embedInputFirst_t, Section.point_t, lowerSection_apply]
    rcases abs_cases (((n - p.x : ℕ) : ℤ) - p.z) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

theorem embedInputSecond_eq_point {n : ℕ} (p : Vertex n) :
    embedInputSecond p =
      (lowerSection n).point (⟨p.y, by have := p.sum_eq; omega⟩, ⟨n - p.x, by omega⟩) := by
  have hp := p.sum_eq
  ext
  · rfl
  · rfl
  · simp only [embedInputSecond_t, Section.point_t, lowerSection_apply]
    rcases abs_cases ((p.y : ℤ) - (n - p.x : ℕ)) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

theorem embedOutputFirst_eq_point {n : ℕ} (p : Vertex n) :
    embedOutputFirst p =
      (upperSection n).point (⟨n - p.z, by omega⟩, ⟨n - p.x, by omega⟩) := by
  have hp := p.sum_eq
  ext
  · rfl
  · rfl
  · simp only [embedOutputFirst_t, Section.point_t, upperSection_apply]
    rcases abs_cases ((n : ℤ) - (n - p.z : ℕ) - (n - p.x : ℕ)) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

theorem embedOutputSecond_eq_point {n : ℕ} (p : Vertex n) :
    embedOutputSecond p =
      (upperSection n).point
        (⟨p.y, by have := p.sum_eq; omega⟩, ⟨p.z, by have := p.sum_eq; omega⟩) := by
  have hp := p.sum_eq
  ext
  · rfl
  · rfl
  · simp only [embedOutputSecond_t, Section.point_t, upperSection_apply]
    rcases abs_cases ((n : ℤ) - p.y - p.z) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

/-! ### Lower and upper face gluing and exact boundary readouts -/

section RawGluing

variable {n : ℕ} {R : Type*}

/-- Glue two face functions `f₁, f₂ : Vertex n → R` onto `lowerSection n` across the diagonal
`X = Y`: use `f₁` on `Y ≤ X` and `f₂` on `X < Y`. -/
def glueLower (f₁ f₂ : Vertex n → R) (q : Fin (n + 1) × Fin (n + 1)) : R :=
  if _ : q.2.val ≤ q.1.val then
    f₁ ⟨n - q.1.val, q.1.val - q.2.val, q.2.val, by have := q.1.isLt; omega⟩
  else
    f₂ ⟨n - q.2.val, q.1.val, q.2.val - q.1.val, by have := q.2.isLt; omega⟩

theorem glueLower_apply_of_le (f₁ f₂ : Vertex n → R) {q : Fin (n + 1) × Fin (n + 1)}
    (hq : q.2.val ≤ q.1.val) :
    glueLower f₁ f₂ q =
      f₁ ⟨n - q.1.val, q.1.val - q.2.val, q.2.val, by have := q.1.isLt; omega⟩ := by
  simp [glueLower, hq]

theorem glueLower_apply_of_gt (f₁ f₂ : Vertex n → R) {q : Fin (n + 1) × Fin (n + 1)}
    (hq : q.1.val < q.2.val) :
    glueLower f₁ f₂ q =
      f₂ ⟨n - q.2.val, q.1.val, q.2.val - q.1.val, by have := q.2.isLt; omega⟩ := by
  simp [glueLower, Nat.not_le_of_gt hq]

/-- Read the second output face from `g : [0, n]² → R` along `(x, y, z) ↦ (y, z)` without a
constant shift. -/
def readOutputSecond (g : Fin (n + 1) × Fin (n + 1) → R) (p : Vertex n) : R :=
  g (⟨p.y, by have := p.sum_eq; omega⟩, ⟨p.z, by have := p.sum_eq; omega⟩)

theorem readOutputSecond_apply (g : Fin (n + 1) × Fin (n + 1) → R) (p : Vertex n) :
    readOutputSecond g p =
      g (⟨p.y, by have := p.sum_eq; omega⟩, ⟨p.z, by have := p.sum_eq; omega⟩) := (rfl)

@[simp] theorem readOutputSecond_cornerA (g : Fin (n + 1) × Fin (n + 1) → R) :
    readOutputSecond g (Vertex.cornerA n) = g (0, 0) := by
  unfold readOutputSecond
  congr 1
  ext <;> simp

/-- Pulling `glueLower f₁ f₂` back along `embedInputFirst` always recovers `f₁`. -/
@[simp] theorem glueLower_embedInputFirst (f₁ f₂ : Vertex n → R) (p : Vertex n) :
    glueLower f₁ f₂ ((embedInputFirst p).x, (embedInputFirst p).y) = f₁ p := by
  have hp := p.sum_eq
  rw [glueLower_apply_of_le f₁ f₂ (by simp; omega)]
  congr 1
  ext <;> simp <;> omega

/-- Pulling `glueLower f₁ f₂` back along `embedInputSecond` recovers `f₂` whenever `f₁`'s side `2`
(`C → A`, reversed) agrees with `f₂`'s side `0` (`A → B`). -/
theorem glueLower_embedInputSecond {f₁ f₂ : Vertex n → R}
    (hdiag : ∀ j : Fin (n + 1), f₁ (Vertex.edgePoint n 2 ⟨n - j.val, by omega⟩) =
      f₂ (Vertex.edgePoint n 0 j))
    (p : Vertex n) :
    glueLower f₁ f₂ ((embedInputSecond p).x, (embedInputSecond p).y) = f₂ p := by
  have hp := p.sum_eq
  by_cases hz : p.z = 0
  · trans f₁ (Vertex.edgePoint n 2 ⟨n - p.y, by omega⟩)
    · rw [glueLower_apply_of_le f₁ f₂ (by simp; omega)]
      congr 1
      ext <;> simp <;> omega
    · rw [hdiag ⟨p.y, by omega⟩]
      congr 1
      ext <;> simp <;> omega
  · rw [glueLower_apply_of_gt f₁ f₂ (by simp; omega)]
    congr 1
    ext <;> simp <;> omega

/-- Recovering a lower-section function from its two input face pullbacks is the identity. -/
@[simp] theorem glueLower_pullbacks (g : Fin (n + 1) × Fin (n + 1) → R) :
    glueLower (fun p => g ((embedInputFirst p).x, (embedInputFirst p).y))
      (fun p => g ((embedInputSecond p).x, (embedInputSecond p).y)) = g := by
  ext ⟨x, y⟩
  by_cases h : y.val ≤ x.val
  · rw [glueLower_apply_of_le _ _ h]
    congr 1
    (ext <;> simp); omega
  · rw [glueLower_apply_of_gt _ _ (Nat.lt_of_not_le h)]
    congr 1
    (ext <;> simp); omega

end RawGluing

section Gluing

variable {n : ℕ} {R : Type*} [AddCommGroup R]

/-- Read the first output face from `g : [0, n]² → R` along `(x, y, z) ↦ (n - z, n - x)`,
subtracting `g(n, 0)` to normalize its `A`-corner to `0`. -/
def readOutputFirst (g : Fin (n + 1) × Fin (n + 1) → R) (p : Vertex n) : R :=
  g (⟨n - p.z, by omega⟩, ⟨n - p.x, by omega⟩) - g (Fin.last n, 0)

theorem readOutputFirst_apply (g : Fin (n + 1) × Fin (n + 1) → R) (p : Vertex n) :
    readOutputFirst g p =
      g (⟨n - p.z, by omega⟩, ⟨n - p.x, by omega⟩) - g (Fin.last n, 0) := (rfl)

/-- Inverse upper gluing: add the constant shift `c` (`= |λ|`) back to the first output face `k₁`
on `n < X + Y` and glue with `k₂` on `X + Y ≤ n`. -/
def glueUpper (c : R) (k₁ k₂ : Vertex n → R) (q : Fin (n + 1) × Fin (n + 1)) : R :=
  if _ : q.1.val + q.2.val ≤ n then
    k₂ ⟨n - (q.1.val + q.2.val), q.1.val, q.2.val, by omega⟩
  else
    k₁ ⟨n - q.2.val, q.1.val + q.2.val - n, n - q.1.val, by
      have := q.1.isLt; have := q.2.isLt; omega⟩ + c

theorem glueUpper_apply_of_le (c : R) (k₁ k₂ : Vertex n → R) {q : Fin (n + 1) × Fin (n + 1)}
    (hq : q.1.val + q.2.val ≤ n) :
    glueUpper c k₁ k₂ q = k₂ ⟨n - (q.1.val + q.2.val), q.1.val, q.2.val, by omega⟩ := by
  simp [glueUpper, hq]

theorem glueUpper_apply_of_gt (c : R) (k₁ k₂ : Vertex n → R) {q : Fin (n + 1) × Fin (n + 1)}
    (hq : n < q.1.val + q.2.val) :
    glueUpper c k₁ k₂ q =
      k₁ ⟨n - q.2.val, q.1.val + q.2.val - n, n - q.1.val, by
        have := q.1.isLt; have := q.2.isLt; omega⟩ + c := by
  simp [glueUpper, Nat.not_le_of_gt hq]

@[simp] theorem readOutputFirst_cornerA (g : Fin (n + 1) × Fin (n + 1) → R) :
    readOutputFirst g (Vertex.cornerA n) = 0 := by
  unfold readOutputFirst
  have hc :
      ((⟨n - (Vertex.cornerA n).z, by omega⟩,
        ⟨n - (Vertex.cornerA n).x, by omega⟩) : Fin (n + 1) × Fin (n + 1)) =
      (Fin.last n, 0) := by
    ext <;> simp
  rw [hc, sub_self]

/-- Two normalized hives whose shared boundary satisfies `h₁.boundary 2 i = -h₂.boundary 0 i.rev`
automatically agree along the diagonal `X = Y`. -/
theorem hive_diag_eq_of_boundary [PartialOrder R] (h₁ h₂ : Hive n R)
    (hb : ∀ i : Fin n, h₁.boundary 2 i = -h₂.boundary 0 i.rev)
    (j : Fin (n + 1)) :
    h₁ (Vertex.edgePoint n 2 ⟨n - j.val, by omega⟩) = h₂ (Vertex.edgePoint n 0 j) := by
  rw [h₁.apply_edgePoint_two, h₂.apply_edgePoint_zero]
  simp only [hb, Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_bij (fun i _ => i.rev) ?_ ?_ ?_ fun _ _ => rfl
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hi ⊢
    omega
  · intro i₁ _ i₂ _ heq
    exact Fin.rev_injective heq
  · intro k hk
    refine ⟨k.rev, ?_, Fin.rev_rev k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hk ⊢
    omega

/-- Pulling `glueLower h₁ h₂` back along `embedInputSecond` recovers `h₂` for any normalized hives
with dual shared boundary `σ*` and `σ`. -/
theorem glueLower_hive_embedInputSecond [PartialOrder R] (h₁ h₂ : Hive n R)
    (hb : ∀ i : Fin n, h₁.boundary 2 i = -h₂.boundary 0 i.rev) (p : Vertex n) :
    glueLower h₁ h₂ ((embedInputSecond p).x, (embedInputSecond p).y) = h₂ p :=
  glueLower_embedInputSecond (hive_diag_eq_of_boundary h₁ h₂ hb) p

/-- Specialization of `glueLower_hive_embedInputSecond` to `productBoundary lam μ σ` and
`productBoundary σ ν π`. -/
theorem glueLower_productBoundary_embedInputSecond {lam μ σ ν π : DominantWeight n}
    {h₁ h₂ : IntegerHive n} (hb₁ : h₁.boundary = productBoundary lam μ σ)
    (hb₂ : h₂.boundary = productBoundary σ ν π) (p : Vertex n) :
    glueLower h₁ h₂ ((embedInputSecond p).x, (embedInputSecond p).y) = h₂ p :=
  glueLower_hive_embedInputSecond h₁ h₂ (fun i => by simp [hb₁, hb₂]) p

/-- `readOutputSecond` pulls `glueUpper c k₁ k₂` back to `k₂` unconditionally. -/
@[simp] theorem readOutputSecond_glueUpper (c : R) (k₁ k₂ : Vertex n → R) (p : Vertex n) :
    readOutputSecond (glueUpper c k₁ k₂) p = k₂ p := by
  have hp := p.sum_eq
  unfold readOutputSecond
  rw [glueUpper_apply_of_le c k₁ k₂ (by simp; omega)]
  congr 1
  (ext <;> simp); omega

/-- `readOutputFirst` pulls `glueUpper c k₁ k₂` back to `k₁` whenever `k₁` is normalized at `A`
and `k₁ + c` agrees with `k₂` along the shared antidiagonal `X + Y = n`. -/
theorem readOutputFirst_glueUpper {c : R} {k₁ k₂ : Vertex n → R}
    (hk₁A : k₁ (Vertex.cornerA n) = 0)
    (hanti : ∀ j : Fin (n + 1), k₁ (Vertex.edgePoint n 2 ⟨n - j.val, by omega⟩) + c =
      k₂ (Vertex.edgePoint n 1 j))
    (p : Vertex n) :
    readOutputFirst (glueUpper c k₁ k₂) p = k₁ p := by
  have hp := p.sum_eq
  have hlast : glueUpper c k₁ k₂ (Fin.last n, 0) = c := by
    have h0 := (hanti 0).symm
    have hfin : (⟨n - (0 : Fin (n + 1)).val, by omega⟩ : Fin (n + 1)) = Fin.last n := by
      ext; simp
    rw [hfin, Vertex.edgePoint_two_last, hk₁A, zero_add] at h0
    rw [glueUpper_apply_of_le c k₁ k₂ (by simp)]
    have hv :
        (⟨n - ((Fin.last n).val + (0 : Fin (n + 1)).val),
          (Fin.last n).val, (0 : Fin (n + 1)).val, by simp⟩ : Vertex n) =
        Vertex.edgePoint n 1 0 := by ext <;> simp
    rw [hv, h0]
  rw [readOutputFirst, hlast]
  by_cases hy : p.y = 0
  · rw [glueUpper_apply_of_le c k₁ k₂ (by simp; omega)]
    have hqeq :
        (⟨n - ((⟨n - p.z, by omega⟩ : Fin (n + 1)).val +
            (⟨n - p.x, by omega⟩ : Fin (n + 1)).val),
            n - p.z, n - p.x, by simp; omega⟩ : Vertex n) =
          Vertex.edgePoint n 1 ⟨p.z, by omega⟩ := by
      ext <;> simp <;> omega
    rw [hqeq, (hanti ⟨p.z, by omega⟩).symm, add_sub_cancel_right]
    congr 1
    ext <;> simp [hy] <;> omega
  · rw [glueUpper_apply_of_gt c k₁ k₂ (by simp; omega), add_sub_cancel_right]
    congr 1
    ext <;> simp <;> omega

/-- For normalized hives `k₁, k₂` with `k₁.boundary 2 i = -k₂.boundary 1 i.rev` and
`c = ∑ i, k₂.boundary 0 i` (`= |λ|`), `k₁ + c` and `k₂` agree along the antidiagonal `X + Y = n`.
-/
theorem hive_antidiag_eq_of_boundary [PartialOrder R] (k₁ k₂ : Hive n R)
    (hb : ∀ i : Fin n, k₁.boundary 2 i = -k₂.boundary 1 i.rev)
    (j : Fin (n + 1)) :
    k₁ (Vertex.edgePoint n 2 ⟨n - j.val, by omega⟩) + (∑ i : Fin n, k₂.boundary 0 i) =
      k₂ (Vertex.edgePoint n 1 j) := by
  rw [k₁.apply_edgePoint_two, k₂.apply_edgePoint_one, add_comm]
  congr 1
  simp only [hb, Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_bij (fun i _ => i.rev) ?_ ?_ ?_ fun _ _ => rfl
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hi ⊢
    omega
  · intro i₁ _ i₂ _ heq
    exact Fin.rev_injective heq
  · intro m hm
    refine ⟨m.rev, ?_, Fin.rev_rev m⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hm ⊢
    omega

/-- Re-gluing the two output readouts with constant shift `g(n, 0)` recovers any function `g` on
`upperSection n`. -/
@[simp] theorem glueUpper_readOutputs (g : Fin (n + 1) × Fin (n + 1) → R) :
    glueUpper (g (Fin.last n, 0)) (readOutputFirst g) (readOutputSecond g) = g := by
  ext ⟨x, y⟩
  by_cases h : x.val + y.val ≤ n
  · rw [glueUpper_apply_of_le _ _ _ h]
    rfl
  · rw [glueUpper_apply_of_gt _ _ _ (Nat.lt_of_not_le h)]
    unfold readOutputFirst
    rw [sub_add_cancel]
    congr 1
    ext <;> simp <;> omega

/-! ### Exterior wall agreement and output boundary formulas -/

/-- Any `g'` agreeing with `glueLower h₁ h₂` on `IsWallPos` vanishes at `(0, 0)`, hence normalizes
`readOutputSecond g'` at `A`. -/
theorem readOutput_cornerA_zero [PartialOrder R] (h₁ h₂ : Hive n R)
    {g' : Fin (n + 1) × Fin (n + 1) → R}
    (hwall : ∀ p, IsWallPos p → g' p = glueLower h₁ h₂ p) :
    readOutputSecond g' (Vertex.cornerA n) = 0 := by
  rw [readOutputSecond_cornerA, hwall (0, 0) (Or.inl rfl),
    glueLower_apply_of_le _ _ (Nat.zero_le _)]
  have hv :
      (⟨n - (0 : Fin (n + 1)).val,
        (0 : Fin (n + 1)).val - (0 : Fin (n + 1)).val,
        (0 : Fin (n + 1)).val, by simp⟩ : Vertex n) = Vertex.cornerA n := by
    ext <;> simp
  rw [hv, h₁.apply_cornerA]

/-- At `(n, 0)`, `glueLower h₁ h₂` evaluates to the total side-`0` weight `∑ i, h₁.boundary 0 i`.
-/
theorem glueLower_corner_last_zero [PartialOrder R] (h₁ h₂ : Hive n R) :
    glueLower h₁ h₂ (Fin.last n, 0) = ∑ i : Fin n, h₁.boundary 0 i := by
  have heq : glueLower h₁ h₂ (Fin.last n, 0) = h₁ (Vertex.edgePoint n 0 (Fin.last n)) := by
    rw [glueLower_apply_of_le _ _ (Nat.zero_le _)]
    congr 1
    ext <;> simp
  rw [heq, h₁.apply_edgePoint_zero]
  congr 1
  ext i
  simp [Fin.last]

/-- Side `0` of `readOutputFirst g'` equals `h₁.boundary 1` (`μ`) whenever `g'` agrees with
`glueLower h₁ h₂` on the spatial walls. -/
theorem boundaryLinear_readOutputFirst_zero [PartialOrder R] (h₁ h₂ : Hive n R)
    {g' : Fin (n + 1) × Fin (n + 1) → R}
    (hwall : ∀ p, IsWallPos p → g' p = glueLower h₁ h₂ p) :
    boundaryLinear ℤ n R (readOutputFirst g') 0 = h₁.boundary 1 := by
  ext i
  have hw (k : Fin (n + 1)) :
      g' (⟨n - (Vertex.edgePoint n 0 k).z, by omega⟩,
        ⟨n - (Vertex.edgePoint n 0 k).x, by omega⟩) = h₁ (Vertex.edgePoint n 1 k) := by
    have hpt :
        ((⟨n - (Vertex.edgePoint n 0 k).z, by omega⟩,
          ⟨n - (Vertex.edgePoint n 0 k).x, by omega⟩) : Fin (n + 1) × Fin (n + 1)) =
        (Fin.last n, k) := by
      (ext <;> simp); omega
    rw [hpt, hwall (Fin.last n, k) (Or.inr (Or.inl rfl)),
      glueLower_apply_of_le _ _ (Fin.le_last k)]
    congr 1
    ext <;> simp
  simp only [boundaryLinear_apply, readOutputFirst, hw, boundary_apply]
  abel

/-- Side `1` of `readOutputFirst g'` equals `h₂.boundary 1` (`ν`) whenever `g'` agrees with
`glueLower h₁ h₂` on the spatial walls and `h₁, h₂` have compatible shared boundary. -/
theorem boundaryLinear_readOutputFirst_one [PartialOrder R] (h₁ h₂ : Hive n R)
    (hb : ∀ i : Fin n, h₁.boundary 2 i = -h₂.boundary 0 i.rev)
    {g' : Fin (n + 1) × Fin (n + 1) → R}
    (hwall : ∀ p, IsWallPos p → g' p = glueLower h₁ h₂ p) :
    boundaryLinear ℤ n R (readOutputFirst g') 1 = h₂.boundary 1 := by
  ext i
  have hw (k : Fin (n + 1)) :
      g' (⟨n - (Vertex.edgePoint n 1 k).z, by omega⟩,
        ⟨n - (Vertex.edgePoint n 1 k).x, by omega⟩) = h₂ (Vertex.edgePoint n 1 k) := by
    have hpt :
        ((⟨n - (Vertex.edgePoint n 1 k).z, by omega⟩,
          ⟨n - (Vertex.edgePoint n 1 k).x, by omega⟩) : Fin (n + 1) × Fin (n + 1)) =
        ((embedInputSecond (Vertex.edgePoint n 1 k)).x,
          (embedInputSecond (Vertex.edgePoint n 1 k)).y) := by
      ext <;> simp
    have hwallk : IsWallPos ((embedInputSecond (Vertex.edgePoint n 1 k)).x,
        (embedInputSecond (Vertex.edgePoint n 1 k)).y) :=
      Or.inr (Or.inr (Or.inr (by simp)))
    rw [hpt, hwall _ hwallk, glueLower_hive_embedInputSecond h₁ h₂ hb]
  simp only [boundaryLinear_apply, readOutputFirst, hw, boundary_apply]
  abel

/-- Side `0` of `readOutputSecond g'` equals `h₁.boundary 0` (`λ`) whenever `g'` agrees with
`glueLower h₁ h₂` on the spatial walls. -/
theorem boundaryLinear_readOutputSecond_zero [PartialOrder R] (h₁ h₂ : Hive n R)
    {g' : Fin (n + 1) × Fin (n + 1) → R}
    (hwall : ∀ p, IsWallPos p → g' p = glueLower h₁ h₂ p) :
    boundaryLinear ℤ n R (readOutputSecond g') 0 = h₁.boundary 0 := by
  ext i
  have hw (k : Fin (n + 1)) : readOutputSecond g' (Vertex.edgePoint n 0 k) =
      h₁ (Vertex.edgePoint n 0 k) := by
    unfold readOutputSecond
    have hpt :
        ((⟨(Vertex.edgePoint n 0 k).y, by have := (Vertex.edgePoint n 0 k).sum_eq; omega⟩,
          ⟨(Vertex.edgePoint n 0 k).z, by have := (Vertex.edgePoint n 0 k).sum_eq; omega⟩) :
            Fin (n + 1) × Fin (n + 1)) = (k, 0) := by ext <;> simp
    rw [hpt, hwall (k, 0) (Or.inr (Or.inr (Or.inl rfl))),
      glueLower_apply_of_le _ _ (Nat.zero_le _)]
    congr 1
    ext <;> simp
  simp only [boundaryLinear_apply, hw, boundary_apply]

/-- Side `2` of `readOutputSecond g'` equals `h₂.boundary 2` (`π*`) whenever `g'` agrees with
`glueLower h₁ h₂` on the spatial walls and `h₁, h₂` have compatible shared boundary. -/
theorem boundaryLinear_readOutputSecond_two [PartialOrder R] (h₁ h₂ : Hive n R)
    (hb : ∀ i : Fin n, h₁.boundary 2 i = -h₂.boundary 0 i.rev)
    {g' : Fin (n + 1) × Fin (n + 1) → R}
    (hwall : ∀ p, IsWallPos p → g' p = glueLower h₁ h₂ p) :
    boundaryLinear ℤ n R (readOutputSecond g') 2 = h₂.boundary 2 := by
  ext i
  have hw (k : Fin (n + 1)) : readOutputSecond g' (Vertex.edgePoint n 2 k) =
      h₂ (Vertex.edgePoint n 2 k) := by
    unfold readOutputSecond
    have hpt :
        ((⟨(Vertex.edgePoint n 2 k).y, by have := (Vertex.edgePoint n 2 k).sum_eq; omega⟩,
          ⟨(Vertex.edgePoint n 2 k).z, by have := (Vertex.edgePoint n 2 k).sum_eq; omega⟩) :
            Fin (n + 1) × Fin (n + 1)) =
        ((embedInputSecond (Vertex.edgePoint n 2 k)).x,
          (embedInputSecond (Vertex.edgePoint n 2 k)).y) := by
      ext <;> simp
    have hwallk : IsWallPos ((embedInputSecond (Vertex.edgePoint n 2 k)).x,
        (embedInputSecond (Vertex.edgePoint n 2 k)).y) := Or.inl (by simp)
    rw [hpt, hwall _ hwallk, glueLower_hive_embedInputSecond h₁ h₂ hb]
  simp only [boundaryLinear_apply, hw, boundary_apply]

/-- For **every** `g' : [0, n]² → R`, the two interior output boundaries along `X + Y = n` are dual:
side `2` of `readOutputFirst g'` is `fun i => - boundary (readOutputSecond g') 1 i.rev`. -/
theorem boundaryLinear_readOutputFirst_two_eq_neg_rev (g' : Fin (n + 1) × Fin (n + 1) → R)
    (i : Fin n) :
    boundaryLinear ℤ n R (readOutputFirst g') 2 i =
      -boundaryLinear ℤ n R (readOutputSecond g') 1 i.rev := by
  simp only [boundaryLinear_apply, readOutputFirst, readOutputSecond]
  have h1 :
      ((⟨n - (Vertex.edgePoint n 2 i.succ).z, by omega⟩,
        ⟨n - (Vertex.edgePoint n 2 i.succ).x, by omega⟩) : Fin (n + 1) × Fin (n + 1)) =
      (⟨(Vertex.edgePoint n 1 i.rev.castSucc).y,
          by have := (Vertex.edgePoint n 1 i.rev.castSucc).sum_eq; omega⟩,
        ⟨(Vertex.edgePoint n 1 i.rev.castSucc).z,
          by have := (Vertex.edgePoint n 1 i.rev.castSucc).sum_eq; omega⟩) := by
    ext <;> simp [Fin.val_rev]
  have h2 :
      ((⟨n - (Vertex.edgePoint n 2 i.castSucc).z, by omega⟩,
        ⟨n - (Vertex.edgePoint n 2 i.castSucc).x, by omega⟩) : Fin (n + 1) × Fin (n + 1)) =
      (⟨(Vertex.edgePoint n 1 i.rev.succ).y,
          by have := (Vertex.edgePoint n 1 i.rev.succ).sum_eq; omega⟩,
        ⟨(Vertex.edgePoint n 1 i.rev.succ).z,
          by have := (Vertex.edgePoint n 1 i.rev.succ).sum_eq; omega⟩) := by
    ext <;> simp [Fin.val_rev] <;> omega
  rw [h1, h2]
  abel

end Gluing

end TauCeti.Hive
