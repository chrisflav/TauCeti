/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Basic

/-!
# Cocycles on Coxeter groups

A `1`-cocycle on the right Cayley graph of a Coxeter system `cs : CoxeterSystem M W` with values
in a monoid `G` attaches an element `g w i : G` to each directed edge `w ↦ w * s i`. Multiplying
these edge values along a word `ω` starting from `w` produces `cs.cocycleProd g w ω`.

If `g` cancels along every two-step backtracking path (`g w i * g (w * s i) i = 1`) and has equal
products along the two sides of every braid relation (`braidWord M i j` and `braidWord M j i`)
starting at every `w`, then `g` is a coboundary: there is a unique function `f : W → G` with
`f 1 = 1` such that `f w * g w i = f (w * s i)` for all `w` and `i`.

## Main definitions

* `CoxeterSystem.cocycleProd`: the product of `g` along the Cayley-graph path starting at `w`
  and following a word `ω` of simple generators.

## Main results

* `CoxeterSystem.eq_const_of_forall_mul_simple`: a function on `W` invariant under right
  multiplication by every simple reflection is constant.
* `CoxeterSystem.existsUnique_mul_eq_of_cocycle`: a `1`-cocycle on the right Cayley graph of a
  Coxeter system satisfying the involution and braid conditions admits a unique trivialization
  `f : W → G` with `f 1 = 1` and `f w * g w i = f (w * s i)`.
* `CoxeterSystem.existsUnique_inv_mul_eq_of_cocycle`: the group-valued form
  `g w i = (f w)⁻¹ * f (w * s i)`.

## Implementation notes

To trivialize `g`, we let each simple reflection `s i` act on `W × G` by the involution
`(w, a) ↦ (w * s i, a * g w i)`. Viewed in the opposite group `(Equiv.Perm (W × G))ᵐᵒᵖ`,
these involutions satisfy the braid relations and hence the Coxeter relations of `M`, so
`CoxeterSystem.lift` produces a homomorphism `W →* (Equiv.Perm (W × G))ᵐᵒᵖ` whose orbit of
`(1, 1)` is the graph of the desired trivialization `f`.
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- A function on a Coxeter group invariant under right multiplication by every simple reflection
is constant. -/
theorem eq_const_of_forall_mul_simple {α : Type*} {f : W → α}
    (h : ∀ w i, f (w * cs.simple i) = f w) (w : W) : f w = f 1 :=
  cs.simple_induction_right (p := fun w ↦ f w = f 1) w rfl fun w i ih ↦ (h w i).trans ih

section Monoid

variable {G : Type*} [Monoid G]

/-- The product of a family `g : W → B → G` along the right Cayley-graph path starting at `w`
and following the word `ω` of simple generators. -/
def cocycleProd (cs : CoxeterSystem M W) (g : W → B → G) : W → List B → G
  | _, [] => 1
  | w, i :: ω => g w i * cocycleProd cs g (w * cs.simple i) ω

/-- The cocycle product along the empty word is `1`. -/
@[simp]
theorem cocycleProd_nil (g : W → B → G) (w : W) : cs.cocycleProd g w [] = 1 := by
  simp [cocycleProd]

/-- The cocycle product along `i :: ω` multiplies the first edge `g w i` by the remaining path
starting at `w * cs.simple i`. -/
@[simp]
theorem cocycleProd_cons (g : W → B → G) (w : W) (i : B) (ω : List B) :
    cs.cocycleProd g w (i :: ω) = g w i * cs.cocycleProd g (w * cs.simple i) ω := by
  simp [cocycleProd]

/-- The cocycle product along a one-letter word `[i]` is the edge value `g w i`. -/
theorem cocycleProd_singleton (g : W → B → G) (w : W) (i : B) :
    cs.cocycleProd g w [i] = g w i := by
  simp

/-- The cocycle product along a concatenation of words is the product of the cocycle products
along the two segments. -/
theorem cocycleProd_append (g : W → B → G) (w : W) (ω₁ ω₂ : List B) :
    cs.cocycleProd g w (ω₁ ++ ω₂) =
      cs.cocycleProd g w ω₁ * cs.cocycleProd g (w * cs.wordProd ω₁) ω₂ := by
  induction ω₁ generalizing w with
  | nil => simp
  | cons i ω₁ ih =>
    simp only [List.cons_append, cocycleProd_cons, wordProd_cons, ih, mul_assoc]

/-- Appending a single generator `i` to a word multiplies the cocycle product on the right by the
edge value at the endpoint `w * cs.wordProd ω`. -/
theorem cocycleProd_concat (g : W → B → G) (w : W) (ω : List B) (i : B) :
    cs.cocycleProd g w (ω.concat i) =
      cs.cocycleProd g w ω * g (w * cs.wordProd ω) i := by
  rw [List.concat_eq_append, cocycleProd_append, cocycleProd_singleton]

/-- The cocycle product along the alternating word of length `2`. -/
theorem cocycleProd_alternatingWord_two (g : W → B → G) (w : W) (i j : B) :
    cs.cocycleProd g w (alternatingWord i j 2) = g w i * g (w * cs.simple i) j := by
  simp [alternatingWord]

/-- The cocycle product along the alternating word of length `3`. -/
theorem cocycleProd_alternatingWord_three (g : W → B → G) (w : W) (i j : B) :
    cs.cocycleProd g w (alternatingWord i j 3) =
      g w j * g (w * cs.simple j) i * g (w * cs.simple j * cs.simple i) j := by
  simp [alternatingWord, mul_assoc]

/-- Multiplying a trivialization `f` at `w` by the cocycle product along `ω` yields the value of
`f` at the endpoint `w * cs.wordProd ω`. -/
theorem mul_cocycleProd_eq_of_forall_mul_eq {g : W → B → G} {f : W → G}
    (hf : ∀ w i, f w * g w i = f (w * cs.simple i)) (w : W) (ω : List B) :
    f w * cs.cocycleProd g w ω = f (w * cs.wordProd ω) := by
  induction ω generalizing w with
  | nil => simp
  | cons i ω ih =>
    simp only [cocycleProd_cons, wordProd_cons, ← mul_assoc, hf, ih]

/-- **Trivialization of `1`-cocycles on a Coxeter group.** If `g : W → B → G` cancels along
every backtracking edge and has equal products along both sides of every braid relation at every
vertex, then there is a unique `f : W → G` with `f 1 = 1` and `f w * g w i = f (w * s i)`. -/
theorem existsUnique_mul_eq_of_cocycle (g : W → B → G)
    (hinv : ∀ w i, g w i * g (w * cs.simple i) i = 1)
    (hbraid : ∀ w i j, cs.cocycleProd g w (braidWord M i j) =
      cs.cocycleProd g w (braidWord M j i)) :
    ∃! f : W → G, f 1 = 1 ∧ ∀ w i, f w * g w i = f (w * cs.simple i) := by
  let step (i : B) : Equiv.Perm (W × G) :=
    { toFun p := (p.1 * cs.simple i, p.2 * g p.1 i)
      invFun p := (p.1 * cs.simple i, p.2 * g p.1 i)
      left_inv p := Prod.ext (by simp [mul_assoc]) (by simp [mul_assoc, hinv])
      right_inv p := Prod.ext (by simp [mul_assoc]) (by simp [mul_assoc, hinv]) }
  let T : B → (Equiv.Perm (W × G))ᵐᵒᵖ := fun i ↦ MulOpposite.op (step i)
  have hsq : ∀ i, T i * T i = 1 := fun i ↦
    MulOpposite.unop_injective <| Equiv.Perm.ext fun p ↦ by
    simp only [MulOpposite.unop_mul, MulOpposite.unop_one, Equiv.Perm.mul_apply,
      Equiv.Perm.one_apply, T, MulOpposite.unop_op]
    exact (step i).left_inv p
  have hword : ∀ (ω : List B) (p : W × G),
      ((ω.map T).prod).unop p = (p.1 * cs.wordProd ω, p.2 * cs.cocycleProd g p.1 ω) := by
    intro ω
    induction ω with
    | nil => intro p; simp
    | cons i ω ih =>
      intro p
      simp only [List.map_cons, List.prod_cons, MulOpposite.unop_mul, Equiv.Perm.mul_apply,
        wordProd_cons, cocycleProd_cons]
      rw [ih]
      simp [T, step, mul_assoc]
  have hlift : M.IsLiftable T :=
    M.isLiftable_of_mul_self_of_braidWord hsq fun i j ↦ MulOpposite.unop_injective <|
      Equiv.Perm.ext fun p ↦ by
        rw [hword, hword, cs.wordProd_braidWord_eq i j, hbraid p.1 i j]
  let Φ : W →* (Equiv.Perm (W × G))ᵐᵒᵖ := cs.lift ⟨T, hlift⟩
  have hΦ_mul : ∀ w i,
      (Φ (w * cs.simple i)).unop (1, 1) = step i ((Φ w).unop (1, 1)) := fun w i ↦ by
    simp only [map_mul, MulOpposite.unop_mul, Equiv.Perm.mul_apply, Φ, lift_apply_simple]
    rfl
  have hfst : ∀ w, ((Φ w).unop (1, 1)).1 = w := fun w ↦
    cs.simple_induction_right (p := fun w ↦ ((Φ w).unop (1, 1)).1 = w) w (by simp [Φ])
      fun w i ih ↦ by rw [hΦ_mul]; simp [step, ih]
  refine ⟨fun w ↦ ((Φ w).unop (1, 1)).2, ⟨by simp [Φ], fun w i ↦ ?_⟩, ?_⟩
  · dsimp only
    rw [hΦ_mul]
    simp [step, hfst w]
  · rintro f' ⟨hf'1, hf'⟩
    funext w
    refine cs.simple_induction_right (p := fun w ↦ f' w = ((Φ w).unop (1, 1)).2) w
      (by simp [Φ, hf'1]) fun w i ih ↦ ?_
    rw [← hf' w i, ih, hΦ_mul]
    simp [step, hfst w]

end Monoid

/-- The group-valued form of `CoxeterSystem.existsUnique_mul_eq_of_cocycle`: a `1`-cocycle on
a Coxeter group satisfying the involution and braid conditions is uniquely of the form
`g w i = (f w)⁻¹ * f (w * s i)` with `f 1 = 1`. -/
theorem existsUnique_inv_mul_eq_of_cocycle {G : Type*} [Group G] (g : W → B → G)
    (hinv : ∀ w i, g w i * g (w * cs.simple i) i = 1)
    (hbraid : ∀ w i j, cs.cocycleProd g w (braidWord M i j) =
      cs.cocycleProd g w (braidWord M j i)) :
    ∃! f : W → G, f 1 = 1 ∧ ∀ w i, g w i = (f w)⁻¹ * f (w * cs.simple i) := by
  simpa [eq_inv_mul_iff_mul_eq] using cs.existsUnique_mul_eq_of_cocycle g hinv hbraid

end CoxeterSystem
