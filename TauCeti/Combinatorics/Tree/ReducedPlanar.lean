/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Reduced planar rooted trees

A reduced planar rooted tree has ordered inputs at every vertex and no unary vertices.
The single leaf is allowed. These are the shapes of the finite sums in homological transfer:
leaves carry the inclusion, internal vertices carry operations of arity at least two,
internal edges carry the homotopy, and the root carries the projection. The unary differential
belongs to the contraction, not to a vertex of the tree.

`ReducedPlanarTree.Arity n` is finite. The proof uses the strict decrease in the number of
leaves when passing to a child, and the bound on the valence of the root. Thus fixed-arity
sums over these trees need neither a convergence hypothesis nor a bound on vertex valences
chosen separately. The number of internal vertices is at most the number of leaves minus one,
with equality precisely for the binary trees (`IsBinary`), in which every internal vertex has
valence two.

Ordered tuples of trees with prescribed total leaf count (`ReducedPlanarTree.Forest`) decompose
by splitting off their first tree (`forestConsEquiv`), and trees of arity at least two decompose
into a root valence and a forest of children (`nodeEquiv`). In arity three, `Arity 3` consists
of the ternary corolla together with the left- and right-associated binary trees
(`sum_arity_three`).

The tree shapes follow the transfer convention of Loday--Vallette, *Algebraic Operads*,
Chapter 10, and Merkulov, *Strongly homotopy algebras of a Kähler manifold*.
-/

public section

namespace TauCeti

/-- A planar rooted tree with no unary vertices. The `n + 2` children of a vertex are
ordered by `Fin (n + 2)`, so distinct planar bracketings remain distinct trees. -/
inductive ReducedPlanarTree : Type
  | leaf : ReducedPlanarTree
  | node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) : ReducedPlanarTree

namespace ReducedPlanarTree

/-- The number of input leaves. The single leaf has arity one. The body is exposed so that
dependent arity types `Fin t.numLeaves` reduce definitionally on constructors. -/
@[expose]
def numLeaves : ReducedPlanarTree → ℕ
  | leaf => 1
  | node _ children => ∑ i, numLeaves (children i)

/-- The number of internal vertices, excluding the input leaves. -/
def numInternal : ReducedPlanarTree → ℕ
  | leaf => 0
  | node _ children => 1 + ∑ i, numInternal (children i)

@[simp] theorem numLeaves_leaf : numLeaves leaf = 1 := (rfl)

@[simp] theorem numLeaves_node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) :
    numLeaves (node n children) = ∑ i, numLeaves (children i) := (rfl)

@[simp] theorem numInternal_leaf : numInternal leaf = 0 := (rfl)

@[simp] theorem numInternal_node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) :
    numInternal (node n children) = 1 + ∑ i, numInternal (children i) := (rfl)

/-- A tree has at least one input leaf. -/
theorem numLeaves_pos (t : ReducedPlanarTree) : 0 < t.numLeaves := by
  induction t with
  | leaf => simp
  | node n children ih =>
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ Nat.succ_le_iff.mpr (ih i))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] at h
    simp only [numLeaves_node]
    omega

/-- The root cannot have more inputs than the whole tree has leaves. -/
theorem arity_le_numLeaves_node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) :
    n + 2 ≤ (node n children).numLeaves := by
  simpa using Finset.sum_le_sum (s := Finset.univ)
    (fun i _ ↦ Nat.succ_le_iff.mpr (children i).numLeaves_pos)

/-- Every child has strictly fewer leaves than its parent. Excluding unary vertices
is essential for this strict inequality. -/
theorem numLeaves_child_lt (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree)
    (i : Fin (n + 2)) : (children i).numLeaves < (node n children).numLeaves := by
  obtain ⟨j, hji⟩ := exists_ne i
  simpa only [numLeaves_node] using Finset.single_lt_sum (f := fun k ↦ (children k).numLeaves) hji
    (Finset.mem_univ i) (Finset.mem_univ j) (children j).numLeaves_pos
    (fun k _ _ ↦ Nat.zero_le _)

/-- Internal vertices are bounded by arity minus one. This also bounds the number
of homotopy-labelled internal edges in a transfer tree. -/
theorem numInternal_add_one_le_numLeaves (t : ReducedPlanarTree) :
    t.numInternal + 1 ≤ t.numLeaves := by
  induction t with
  | leaf => simp
  | node n children ih =>
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ ih i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Nat.nsmul_eq_mul, mul_one] at h
    simp only [numInternal_node, numLeaves_node]
    omega

/-- A tree with one leaf is the single leaf: no internal operation can occur in arity one. -/
@[simp]
theorem numLeaves_eq_one_iff (t : ReducedPlanarTree) : t.numLeaves = 1 ↔ t = leaf := by
  cases t with
  | leaf => simp
  | node n children =>
    have h := arity_le_numLeaves_node n children
    simp only [reduceCtorEq, iff_false]
    omega

/-- The corolla with `n + 2` inputs, consisting of a single internal vertex. -/
@[expose]
def corolla (n : ℕ) : ReducedPlanarTree := node n (fun _ ↦ leaf)

/-- A corolla has a single root whose children are all leaves. -/
theorem corolla_def (n : ℕ) : corolla n = node n (fun _ ↦ leaf) := (rfl)

@[simp] theorem numLeaves_corolla (n : ℕ) : (corolla n).numLeaves = n + 2 := by
  simp [corolla]

@[simp] theorem numInternal_corolla (n : ℕ) : (corolla n).numInternal = 1 := by
  simp [corolla]

/-- The only two-leaf tree is the binary corolla. Thus the arity-two transfer
sum has exactly one term. -/
@[simp]
theorem numLeaves_eq_two_iff (t : ReducedPlanarTree) : t.numLeaves = 2 ↔ t = corolla 0 := by
  constructor
  · intro ht
    cases t with
    | leaf => simp at ht
    | node n children =>
      have h := arity_le_numLeaves_node n children
      have hn : n = 0 := by omega
      subst n
      have hc (i : Fin 2) : children i = leaf := by
        have hi := numLeaves_child_lt 0 children i
        have hp := (children i).numLeaves_pos
        exact (numLeaves_eq_one_iff _).mp (by omega)
      unfold corolla
      exact congrArg (node 0) (funext hc)
  · rintro rfl
    exact numLeaves_corolla 0

/-! ## Finiteness in each arity -/

-- A bounded tree is encoded by either a leaf or its root valence and a family of
-- strictly smaller bounded trees. The code is only used in the finiteness proof.
private def rootCode (n : ℕ) : {t : ReducedPlanarTree // t.numLeaves ≤ n + 1} →
    Unit ⊕ (Σ k : Fin (n + 1), Fin (k.val + 2) →
      {t : ReducedPlanarTree // t.numLeaves ≤ n})
  | ⟨leaf, _⟩ => Sum.inl ()
  | ⟨node k children, ht⟩ => Sum.inr ⟨⟨k, by
      have h := arity_le_numLeaves_node k children
      omega⟩, fun i ↦ ⟨children i, by
        have h := numLeaves_child_lt k children i
        omega⟩⟩

private theorem rootCode_injective (n : ℕ) : Function.Injective (rootCode n) := by
  let decode : Unit ⊕ (Σ k : Fin (n + 1), Fin (k.val + 2) →
      {t : ReducedPlanarTree // t.numLeaves ≤ n}) → ReducedPlanarTree :=
    Sum.elim (fun _ ↦ leaf) (fun ⟨k, children⟩ ↦ node k.val (fun i ↦ (children i).val))
  have h (t : {t : ReducedPlanarTree // t.numLeaves ≤ n + 1}) :
      decode (rootCode n t) = t.val := by
    rcases t with ⟨t, ht⟩
    cases t <;> rfl
  intro s t e
  exact Subtype.ext ((h s).symm.trans ((congrArg decode e).trans (h t)))

/-- There are finitely many reduced planar trees with any fixed bound on their arity. -/
instance finite_numLeaves_le (n : ℕ) : Finite {t : ReducedPlanarTree // t.numLeaves ≤ n} := by
  induction n with
  | zero =>
    have : IsEmpty {t : ReducedPlanarTree // t.numLeaves ≤ 0} :=
      ⟨fun t ↦ by have h := t.val.numLeaves_pos; omega⟩
    infer_instance
  | succ n ih =>
    have := ih
    exact Finite.of_injective (rootCode n) (rootCode_injective n)

/-- The finite type of planar transfer-tree shapes with exactly `n` ordered input leaves. -/
abbrev Arity (n : ℕ) := {t : ReducedPlanarTree // t.numLeaves = n}

instance (n : ℕ) : Finite (Arity n) :=
  Finite.of_injective (fun t ↦ (⟨t.val, t.property.le⟩ : {t // t.numLeaves ≤ n}))
    (fun _ _ e ↦ Subtype.ext
      (congrArg (fun t : {t : ReducedPlanarTree // t.numLeaves ≤ n} ↦ t.val) e))

/-- Fixed-arity transfer expressions can be summed over all tree shapes. -/
noncomputable instance (n : ℕ) : Fintype (Arity n) := Fintype.ofFinite _

instance : IsEmpty (Arity 0) :=
  ⟨fun t ↦ (ne_of_gt t.val.numLeaves_pos) t.property⟩

/-- The single leaf is the unique tree of arity one. -/
instance : Unique (Arity 1) where
  default := ⟨leaf, numLeaves_leaf⟩
  uniq t := Subtype.ext ((numLeaves_eq_one_iff t.val).mp t.property)

/-- The binary corolla is the unique tree of arity two. -/
instance : Unique (Arity 2) where
  default := ⟨corolla 0, numLeaves_corolla 0⟩
  uniq t := Subtype.ext ((numLeaves_eq_two_iff t.val).mp t.property)

/-- Every positive arity is realized: by a leaf in arity one and by a corolla thereafter. -/
theorem nonempty_arity_iff (n : ℕ) : Nonempty (Arity n) ↔ 0 < n := by
  refine ⟨fun ⟨t⟩ ↦ t.property ▸ t.val.numLeaves_pos, ?_⟩
  intro hn
  rcases n with _ | _ | n
  · omega
  · exact ⟨⟨leaf, numLeaves_leaf⟩⟩
  · exact ⟨⟨corolla n, numLeaves_corolla n⟩⟩

/-! ## Binary trees and arity three -/

/-- A reduced planar tree is **binary** when every internal vertex has valence two (`n = 0`). -/
def IsBinary : ReducedPlanarTree → Prop
  | leaf => True
  | node n children => n = 0 ∧ ∀ i, (children i).IsBinary

@[simp]
theorem isBinary_leaf : leaf.IsBinary := trivial

@[simp]
theorem isBinary_node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) :
    (node n children).IsBinary ↔ n = 0 ∧ ∀ i, (children i).IsBinary :=
  Iff.rfl

/-- Decidability of `IsBinary`. -/
instance decidableIsBinary : (t : ReducedPlanarTree) → Decidable t.IsBinary
  | leaf => isTrue isBinary_leaf
  | node n children =>
    letI : ∀ i, Decidable (children i).IsBinary := fun i ↦ decidableIsBinary (children i)
    decidable_of_iff (n = 0 ∧ ∀ i, (children i).IsBinary) (isBinary_node n children).symm

@[simp]
theorem isBinary_corolla_iff (n : ℕ) : (corolla n).IsBinary ↔ n = 0 := by
  simp [corolla_def]

/-- A reduced planar tree achieves the upper bound `numInternal + 1 = numLeaves` if and only if
every internal vertex is binary. -/
theorem numInternal_add_one_eq_numLeaves_iff (t : ReducedPlanarTree) :
    t.numInternal + 1 = t.numLeaves ↔ t.IsBinary := by
  induction t with
  | leaf => simp
  | node n children ih =>
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin (n + 2))),
        (children i).numInternal + 1 ≤ (children i).numLeaves :=
      fun i _ ↦ (children i).numInternal_add_one_le_numLeaves
    have hsum := Finset.sum_le_sum hle
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, mul_one] at hsum
    simp only [numInternal_node, numLeaves_node, isBinary_node]
    constructor
    · intro heq
      have hn : n = 0 := by omega
      subst hn
      refine ⟨rfl, fun i ↦ (ih i).mp ?_⟩
      have hsum_eq : ∑ j, ((children j).numInternal + 1) = ∑ j, (children j).numLeaves := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Nat.nsmul_eq_mul, mul_one]
        omega
      exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum_eq i (Finset.mem_univ i)
    · rintro ⟨rfl, hbin⟩
      have hsum_eq : ∑ j, ((children j).numInternal + 1) = ∑ j, (children j).numLeaves :=
        Finset.sum_congr rfl fun i _ ↦ (ih i).mpr (hbin i)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul, mul_one] at hsum_eq
      omega

/-- The left-associated binary tree with three leaves, `((•, •), •)`. -/
@[expose]
def leftBinary : ReducedPlanarTree := node 0 ![corolla 0, leaf]

theorem leftBinary_def : leftBinary = node 0 ![corolla 0, leaf] := (rfl)

/-- The right-associated binary tree with three leaves, `(•, (•, •))`. -/
@[expose]
def rightBinary : ReducedPlanarTree := node 0 ![leaf, corolla 0]

theorem rightBinary_def : rightBinary = node 0 ![leaf, corolla 0] := (rfl)

@[simp]
theorem numLeaves_leftBinary : leftBinary.numLeaves = 3 := by
  simp [leftBinary_def, Fin.sum_univ_two]

@[simp]
theorem numLeaves_rightBinary : rightBinary.numLeaves = 3 := by
  simp [rightBinary_def, Fin.sum_univ_two]

@[simp]
theorem numInternal_leftBinary : leftBinary.numInternal = 2 := by
  simp [leftBinary_def, Fin.sum_univ_two]

@[simp]
theorem numInternal_rightBinary : rightBinary.numInternal = 2 := by
  simp [rightBinary_def, Fin.sum_univ_two]

@[simp]
theorem isBinary_leftBinary : leftBinary.IsBinary := by
  simp [leftBinary_def, Fin.forall_fin_two]

@[simp]
theorem isBinary_rightBinary : rightBinary.IsBinary := by
  simp [rightBinary_def, Fin.forall_fin_two]

theorem corolla_one_ne_leftBinary : corolla 1 ≠ leftBinary := by
  intro h
  have := congrArg numInternal h
  simp at this

theorem corolla_one_ne_rightBinary : corolla 1 ≠ rightBinary := by
  intro h
  have := congrArg numInternal h
  simp at this

theorem leftBinary_ne_rightBinary : leftBinary ≠ rightBinary := by
  rw [leftBinary_def, rightBinary_def]
  intro h
  injection h with _ hch
  have h0 := congrFun hch 0
  have hl := congrArg numLeaves h0
  simp at hl

/-- A reduced planar tree has three leaves if and only if it is the ternary corolla or one of the
two binary trees of arity three. -/
theorem numLeaves_eq_three_iff (t : ReducedPlanarTree) :
    t.numLeaves = 3 ↔ t = corolla 1 ∨ t = leftBinary ∨ t = rightBinary := by
  refine ⟨?_, ?_⟩
  · cases t with
    | leaf => simp
    | node n children =>
      intro ht
      have hle := arity_le_numLeaves_node n children
      have hn : n = 0 ∨ n = 1 := by omega
      rcases hn with rfl | rfl
      · rw [numLeaves_node, Fin.sum_univ_two] at ht
        have h0 := (children 0).numLeaves_pos
        have h1 := (children 1).numLeaves_pos
        have hcases : (children 0).numLeaves = 2 ∧ (children 1).numLeaves = 1 ∨
            (children 0).numLeaves = 1 ∧ (children 1).numLeaves = 2 := by omega
        rcases hcases with ⟨hc0, hc1⟩ | ⟨hc0, hc1⟩
        · right; left
          rw [leftBinary_def]
          congr 1
          funext i
          fin_cases i
          · exact (numLeaves_eq_two_iff _).mp hc0
          · exact (numLeaves_eq_one_iff _).mp hc1
        · right; right
          rw [rightBinary_def]
          congr 1
          funext i
          fin_cases i
          · exact (numLeaves_eq_one_iff _).mp hc0
          · exact (numLeaves_eq_two_iff _).mp hc1
      · left
        have hpos : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 1 ≤ (children i).numLeaves :=
          fun i _ ↦ (children i).numLeaves_pos
        have hsum : ∑ _ : Fin 3, 1 = ∑ i : Fin 3, (children i).numLeaves := by
          simpa using ht.symm
        have hall := (Finset.sum_eq_sum_iff_of_le hpos).mp hsum
        rw [corolla_def]
        congr 1
        funext i
        exact (numLeaves_eq_one_iff _).mp (hall i (Finset.mem_univ i)).symm
  · rintro (rfl | rfl | rfl) <;> simp

/-- Any sum over the three-leaf reduced planar trees expands into the ternary corolla and the
left- and right-associated binary trees. -/
theorem sum_arity_three {M : Type*} [AddCommMonoid M] (φ : Arity 3 → M) :
    ∑ t : Arity 3, φ t =
      φ ⟨corolla 1, numLeaves_corolla 1⟩ +
        φ ⟨leftBinary, numLeaves_leftBinary⟩ +
        φ ⟨rightBinary, numLeaves_rightBinary⟩ := by
  classical
  set c₁ : Arity 3 := ⟨corolla 1, numLeaves_corolla 1⟩
  set l₂ : Arity 3 := ⟨leftBinary, numLeaves_leftBinary⟩
  set r₂ : Arity 3 := ⟨rightBinary, numLeaves_rightBinary⟩
  have huniv : (Finset.univ : Finset (Arity 3)) = {c₁, l₂, r₂} := by
    ext t
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff,
      true_iff, c₁, l₂, r₂]
    exact (numLeaves_eq_three_iff t.val).mp t.property
  have hcl : c₁ ≠ l₂ := fun h ↦ corolla_one_ne_leftBinary (congrArg Subtype.val h)
  have hcr : c₁ ≠ r₂ := fun h ↦ corolla_one_ne_rightBinary (congrArg Subtype.val h)
  have hlr : l₂ ≠ r₂ := fun h ↦ leftBinary_ne_rightBinary (congrArg Subtype.val h)
  rw [huniv, Finset.sum_insert (by simp [hcl, hcr]), Finset.sum_insert (by simp [hlr]),
    Finset.sum_singleton, add_assoc]

/-! ## Ordered forests and recursive decomposition -/

/-- An ordered forest of `m` reduced planar trees with `b` input leaves in total. -/
abbrev Forest (m b : ℕ) := {ts : Fin m → ReducedPlanarTree // ∑ i, (ts i).numLeaves = b}

instance (m b : ℕ) : Finite (Forest m b) :=
  Finite.of_injective
    (fun ts : Forest m b ↦ fun i : Fin m ↦
      (⟨ts.val i, (Finset.single_le_sum (f := fun j ↦ (ts.val j).numLeaves)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans ts.property.le⟩ :
        {t : ReducedPlanarTree // t.numLeaves ≤ b}))
    fun _ _ h ↦ Subtype.ext <| funext fun i ↦ congrArg Subtype.val (congrFun h i)

noncomputable instance (m b : ℕ) : Fintype (Forest m b) := Fintype.ofFinite _

/-- An ordered forest of `m` trees has at least `m` leaves. -/
theorem le_of_forest {m b : ℕ} (ts : Forest m b) : m ≤ b := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    fun i _ ↦ Nat.succ_le_iff.mpr (ts.val i).numLeaves_pos
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ts.property] at h
  omega

/-- No forest of `m` trees can have fewer than `m` leaves. -/
theorem isEmpty_forest_of_lt {m b : ℕ} (h : b < m) : IsEmpty (Forest m b) :=
  ⟨fun ts ↦ Nat.not_le_of_gt h (le_of_forest ts)⟩

-- The equivalence bodies below are `@[expose]`d so that dependent types indexed by `numLeaves`
-- reduce definitionally on their values in downstream modules.

/-- A one-tree forest is a single tree of the same arity. -/
@[expose]
def forestOneEquiv (b : ℕ) : Forest 1 b ≃ Arity b where
  toFun ts := ⟨ts.val 0, by simpa using ts.property⟩
  invFun t := ⟨fun _ ↦ t.val, by simpa using t.property⟩
  left_inv ts := Subtype.ext <| funext fun i ↦ by rw [Fin.eq_zero i]
  right_inv _ := rfl

@[simp]
theorem forestOneEquiv_symm_apply_val (b : ℕ) (t : Arity b) (i : Fin 1) :
    ((forestOneEquiv b).symm t).val i = t.val :=
  (rfl)

/-- Splitting off the first tree identifies ordered `(m + 1)`-tree forests (with `0 < m`) of `b`
leaves with pairs of a first tree of `d < b` leaves and an `m`-tree forest of `b - d` leaves. -/
@[expose]
def forestConsEquiv {m : ℕ} (hm : 0 < m) (b : ℕ) :
    (Σ d : Fin b, Arity d.val × Forest m (b - d.val)) ≃ Forest (m + 1) b where
  toFun
    | ⟨d, t₀, rest⟩ =>
      ⟨Fin.cons t₀.val rest.val, by
        have := d.isLt
        rw [Fin.sum_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ, t₀.property, rest.property]
        omega⟩
  invFun ts :=
    have : (ts.val 0).numLeaves + ∑ i : Fin m, (ts.val i.succ).numLeaves = b := by
      simpa [Fin.sum_univ_succ] using ts.property
    have : m ≤ ∑ i : Fin m, (ts.val i.succ).numLeaves := by
      simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
        fun i _ ↦ Nat.succ_le_iff.mpr (ts.val i.succ).numLeaves_pos
    ⟨⟨(ts.val 0).numLeaves, by omega⟩,
      ⟨ts.val 0, rfl⟩,
      ⟨Fin.tail ts.val, by dsimp [Fin.tail]; omega⟩⟩
  left_inv
    | ⟨⟨_, _⟩, ⟨_, ht₀⟩, ⟨_, _⟩⟩ => by
      dsimp at ht₀
      subst ht₀
      simp
      rfl
  right_inv ts := Subtype.ext (Fin.cons_self_tail ts.val)

@[simp]
theorem forestConsEquiv_apply_val {m : ℕ} (hm : 0 < m) (b : ℕ) (d : Fin b) (t₀ : Arity d.val)
    (rest : Forest m (b - d.val)) :
    (forestConsEquiv hm b ⟨d, t₀, rest⟩).val = Fin.cons t₀.val rest.val :=
  (rfl)

/-- Trees of arity `b ≥ 2` correspond bijectively to pairs of a root valence `k + 2` (with
`k < b - 1`) and an ordered `(k + 2)`-tree forest of `b` leaves. -/
@[expose]
def nodeEquiv {b : ℕ} (hb : 2 ≤ b) :
    (Σ k : Fin (b - 1), Forest (k.val + 2) b) ≃ Arity b where
  toFun | ⟨k, ts⟩ => ⟨node k.val ts.val, (numLeaves_node k.val ts.val).trans ts.property⟩
  invFun
    | ⟨leaf, ht⟩ => absurd ht (by simp; omega)
    | ⟨node k children, ht⟩ =>
      ⟨⟨k, by have := arity_le_numLeaves_node k children; omega⟩, ⟨children, ht⟩⟩
  left_inv | ⟨k, ts⟩ => rfl
  right_inv
    | ⟨leaf, ht⟩ => absurd ht (by simp; omega)
    | ⟨node _ _, _⟩ => rfl

@[simp]
theorem nodeEquiv_apply_val {b : ℕ} (hb : 2 ≤ b) (k : Fin (b - 1)) (ts : Forest (k.val + 2) b) :
    (nodeEquiv hb ⟨k, ts⟩).val = node k.val ts.val :=
  (rfl)

end ReducedPlanarTree

end TauCeti
