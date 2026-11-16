/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Basic
import Mathlib.Algebra.Group.Opposite

/-!
# Coboundaries on the Cayley graph of a Coxeter group

Let `cs` be a Coxeter system with matrix `M` on a group `W`, and let `A` be any group. An
`A`-valued edge labelling `c : W → B → A` assigns an element `c w i` to each
right-multiplication edge `w → w * s i` in the Cayley graph of `(W, S)`. The product of `c`
along a word `ω` starting at `w` is recorded by `CoxeterSystem.wordCocycleProd cs c w ω`.

If every edge and its reverse multiply to `1`, and around every finite Coxeter relation
`M i j ≠ 0` the two alternating paths `braidWord M i j` and `braidWord M j i` from any vertex
`w` carry the same product, then `c` is a coboundary: there is a unique function `f : W → A`
with `f 1 = 1` such that `(f w)⁻¹ * f (w * s i) = c w i` for all `w` and `i`. More generally,
any two functions with the same coboundary differ by left multiplication by a constant in `A`.

The proof lifts the Cayley-graph step permutations `(w, a) ↦ (w * s i, a * c w i)` via the
universal property `CoxeterSystem.lift` into `(Equiv.Perm (W × A))ᵐᵒᵖ`, and reads `f w` off
the second coordinate of the image of `(1, 1)`.

## Main definitions

* `CoxeterSystem.wordCocycleProd`: the product of an edge labelling along a word in the simple
  reflections starting from a vertex `w`.

## Main results

* `CoxeterSystem.wordCocycleProd_append`: path products multiply under word concatenation.
* `CoxeterSystem.wordCocycleProd_reverse`: reversing a path inverts its product when each edge
  cancels its reverse.
* `CoxeterSystem.eq_mul_of_inv_mul_eq`: two vertex labellings with the same coboundary differ by a
  constant left factor.
* `CoxeterSystem.existsUnique_coboundary`: a flat edge labelling on the Cayley complex of a Coxeter
  group is uniquely a coboundary normalized at `1`.
* `CoxeterSystem.exists_coboundary`: existential form without normalization.

## References

This is the standard 1-cocycle triviality (vanishing of `H¹`) on the simply connected Cayley
2-complex of a Coxeter presentation; see K. S. Brown, *Buildings*, Springer (1989), Chapter I, and
M. W. Davis, *The Geometry and Topology of Coxeter Groups*, Princeton (2008), Chapter 4.
-/

public section

namespace CoxeterSystem

variable {B W A : Type*} [Group W] [Group A] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-! ### Path products along Coxeter words -/

/-- The product of an edge labelling `c : W → B → A` along the right-Cayley path from `w`
spelled by the word `ω`. -/
def wordCocycleProd (c : W → B → A) : W → List B → A
  | _, [] => 1
  | w, i :: ω => c w i * wordCocycleProd c (w * cs.simple i) ω

/-- The product along the empty word is `1`. -/
@[simp]
theorem wordCocycleProd_nil (c : W → B → A) (w : W) :
    cs.wordCocycleProd c w [] = 1 :=
  (rfl)

/-- The product along a nonempty word splits off its first step. -/
@[simp]
theorem wordCocycleProd_cons (c : W → B → A) (w : W) (i : B) (ω : List B) :
    cs.wordCocycleProd c w (i :: ω) = c w i * cs.wordCocycleProd c (w * cs.simple i) ω :=
  (rfl)

/-- The product along a one-letter word is the single edge label. -/
theorem wordCocycleProd_singleton (c : W → B → A) (w : W) (i : B) :
    cs.wordCocycleProd c w [i] = c w i := by
  simp [wordCocycleProd]

/-- The product along a concatenated word multiplies the prefix product by the suffix product
starting at the endpoint of the prefix. -/
theorem wordCocycleProd_append (c : W → B → A) (w : W) (ω₁ ω₂ : List B) :
    cs.wordCocycleProd c w (ω₁ ++ ω₂) =
      cs.wordCocycleProd c w ω₁ * cs.wordCocycleProd c (w * cs.wordProd ω₁) ω₂ := by
  induction ω₁ generalizing w with
  | nil => simp
  | cons i ω₁ ih =>
    simp only [List.cons_append, wordCocycleProd_cons, wordProd_cons, ← mul_assoc, ih]

/-- Reversing a word inverts its path product whenever every edge cancels its reverse. -/
theorem wordCocycleProd_reverse {c : W → B → A}
    (hinv : ∀ w i, c w i * c (w * cs.simple i) i = 1) (w : W) (ω : List B) :
    cs.wordCocycleProd c (w * cs.wordProd ω) ω.reverse = (cs.wordCocycleProd c w ω)⁻¹ := by
  induction ω generalizing w with
  | nil => simp
  | cons i ω ih =>
    rw [List.reverse_cons, wordCocycleProd_append, wordProd_cons, ← mul_assoc, ih,
      wordCocycleProd_singleton, wordProd_reverse, mul_inv_cancel_right, wordCocycleProd_cons,
      mul_inv_rev]
    congr 1
    exact eq_inv_of_mul_eq_one_right (hinv w i)

/-- The path product along an alternating word of length `2`. -/
theorem wordCocycleProd_alternatingWord_two (c : W → B → A) (w : W) (i j : B) :
    cs.wordCocycleProd c w (alternatingWord i j 2) = c w i * c (w * cs.simple i) j := by
  simp [alternatingWord]

/-- The path product along an alternating word of length `3`. -/
theorem wordCocycleProd_alternatingWord_three (c : W → B → A) (w : W) (i j : B) :
    cs.wordCocycleProd c w (alternatingWord i j 3) =
      c w j * c (w * cs.simple j) i * c (w * cs.simple j * cs.simple i) j := by
  simp [alternatingWord, mul_assoc]

/-! ### Uniqueness up to a constant factor -/

/-- Two vertex labellings on a Coxeter group with the same coboundary differ by left multiplication
by a constant. -/
theorem eq_mul_of_inv_mul_eq {f g : W → A}
    (h : ∀ w i, (f w)⁻¹ * f (w * cs.simple i) = (g w)⁻¹ * g (w * cs.simple i)) (w : W) :
    g w = (g 1 * (f 1)⁻¹) * f w := by
  suffices hconst : g w * (f w)⁻¹ = g 1 * (f 1)⁻¹ by
    simpa [mul_assoc] using congrArg (· * f w) hconst
  refine cs.simple_induction_right (p := fun u => g u * (f u)⁻¹ = g 1 * (f 1)⁻¹) w rfl
    fun u i ih => ?_
  have hstep : f (u * cs.simple i) = f u * ((g u)⁻¹ * g (u * cs.simple i)) := by
    rw [← h u i, mul_inv_cancel_left]
  rw [hstep, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel_left]
  exact ih

/-! ### Existence of a coboundary from braid flatness -/

private theorem alternatingWord_append_reverse_eq (i j : B) (m : ℕ) :
    (if Even m then alternatingWord i j m else alternatingWord j i m) ++
      (if Even m then alternatingWord j i m else alternatingWord i j m).reverse =
      alternatingWord i j (2 * m) := by
  refine List.ext_getElem ?_ fun k hk₁ hk₂ => ?_
  · split_ifs <;> simp <;> omega
  · have hk2m : k < 2 * m := by simpa using hk₂
    by_cases hm : Even m
    · simp only [hm, ↓reduceIte, TauCeti.reverse_alternatingWord]
      by_cases hk : k < m
      · rw [List.getElem_append_left (by simp [hk]), getElem_alternatingWord _ _ _ _ hk,
          getElem_alternatingWord _ _ _ _ hk2m]
        simp [hm, Nat.even_add]
      · rw [List.getElem_append_right (by simp; omega),
          getElem_alternatingWord _ _ _ _ (by simp; omega),
          getElem_alternatingWord _ _ _ _ hk2m]
        simp only [length_alternatingWord]
        have hpar : Even (m + (k - m)) ↔ Even (2 * m + k) := by
          have : m + (k - m) = k := by omega
          rw [this, Nat.even_add]
          simp
        simp [hpar]
    · simp only [hm, ↓reduceIte, TauCeti.reverse_alternatingWord]
      by_cases hk : k < m
      · rw [List.getElem_append_left (by simp [hk]), getElem_alternatingWord _ _ _ _ hk,
          getElem_alternatingWord _ _ _ _ hk2m]
        have hodd : ¬Even (m + k) ↔ Even (2 * m + k) := by
          rw [Nat.even_add, Nat.even_add]
          simp [hm]
        by_cases hmk : Even (m + k) <;> simp [hmk, hodd.mp, mt hodd.mpr]
      · rw [List.getElem_append_right (by simp; omega),
          getElem_alternatingWord _ _ _ _ (by simp; omega),
          getElem_alternatingWord _ _ _ _ hk2m]
        simp only [length_alternatingWord]
        have hpar : Even (m + (k - m)) ↔ Even (2 * m + k) := by
          have : m + (k - m) = k := by omega
          rw [this, Nat.even_add]
          simp
        simp [hpar]

private theorem wordCocycleProd_alternatingWord_two_mul_eq_one {c : W → B → A}
    (hinv : ∀ w i, c w i * c (w * cs.simple i) i = 1)
    (hbraid : ∀ w i j, M i j ≠ 0 →
      cs.wordCocycleProd c w (braidWord M i j) = cs.wordCocycleProd c w (braidWord M j i))
    (w : W) (i j : B) :
    cs.wordCocycleProd c w (alternatingWord i j (2 * M i j)) = 1 := by
  by_cases hzero : M i j = 0
  · simp [hzero, alternatingWord]
  rw [← alternatingWord_append_reverse_eq i j (M i j), wordCocycleProd_append]
  have hsym : M j i = M i j := M.symmetric j i
  have hprod : cs.wordProd (braidWord M i j) = cs.wordProd (braidWord M j i) :=
    cs.wordProd_braidWord_eq i j
  by_cases hm : Even (M i j)
  · simp only [hm, ↓reduceIte]
    have heq : cs.wordProd (alternatingWord i j (M i j)) =
        cs.wordProd (alternatingWord j i (M i j)) := by
      simpa only [braidWord, hsym] using hprod
    rw [heq, cs.wordCocycleProd_reverse hinv]
    have hb := hbraid w i j hzero
    simp only [braidWord, hsym] at hb
    rw [hb, mul_inv_cancel]
  · simp only [hm, ↓reduceIte]
    have heq : cs.wordProd (alternatingWord j i (M i j)) =
        cs.wordProd (alternatingWord i j (M i j)) := by
      simpa only [braidWord, hsym] using hprod.symm
    rw [heq, cs.wordCocycleProd_reverse hinv]
    have hb := hbraid w i j hzero
    simp only [braidWord, hsym] at hb
    rw [← hb, mul_inv_cancel]

/-- The twisted right-step permutation on `W × A` induced by an involutive edge labelling. -/
private def coboundaryStep {c : W → B → A}
    (hinv : ∀ w i, c w i * c (w * cs.simple i) i = 1) (i : B) :
    Equiv.Perm (W × A) where
  toFun p := (p.1 * cs.simple i, p.2 * c p.1 i)
  invFun p := (p.1 * cs.simple i, p.2 * c p.1 i)
  left_inv p := by
    ext <;> simp [mul_assoc, hinv]
  right_inv p := by
    ext <;> simp [mul_assoc, hinv]

private theorem unop_prod_map_coboundaryStep {c : W → B → A}
    (hinv : ∀ w i, c w i * c (w * cs.simple i) i = 1) (ω : List B) (p : W × A) :
    MulOpposite.unop ((ω.map fun i => MulOpposite.op (cs.coboundaryStep hinv i)).prod) p =
      (p.1 * cs.wordProd ω, p.2 * cs.wordCocycleProd c p.1 ω) := by
  induction ω generalizing p with
  | nil => simp
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, MulOpposite.unop_mul, MulOpposite.unop_op,
      Equiv.Perm.mul_apply, ih]
    simp [coboundaryStep, wordProd_cons, wordCocycleProd_cons, mul_assoc]

private theorem isLiftable_coboundaryStep {c : W → B → A}
    (hinv : ∀ w i, c w i * c (w * cs.simple i) i = 1)
    (hbraid : ∀ w i j, M i j ≠ 0 →
      cs.wordCocycleProd c w (braidWord M i j) = cs.wordCocycleProd c w (braidWord M j i)) :
    M.IsLiftable (fun i => MulOpposite.op (cs.coboundaryStep hinv i)) := by
  intro i j
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_one]
  ext1 p
  have hpow := TauCeti.prod_map_alternatingWord
    (fun k => MulOpposite.op (cs.coboundaryStep hinv k)) i j (2 * M i j)
  simp only [even_two, Even.mul_right, ↓reduceIte, one_mul,
    Nat.mul_div_cancel_left _ two_pos] at hpow
  rw [← hpow, cs.unop_prod_map_coboundaryStep hinv,
    cs.wordCocycleProd_alternatingWord_two_mul_eq_one hinv hbraid]
  have hword : cs.wordProd (alternatingWord i j (2 * M i j)) = 1 := by
    rw [cs.prod_alternatingWord_eq_mul_pow]
    simp [Nat.mul_div_cancel_left _ two_pos]
  simp [hword]

/-- **Cayley-complex coboundary theorem for Coxeter groups.** An edge labelling `c : W → B → A`
on the right Cayley graph of a Coxeter system that cancels along every back-and-forth edge and
takes equal products along the two sides of every finite Coxeter relation `M i j ≠ 0` is uniquely
a coboundary normalized by `f 1 = 1`. -/
theorem existsUnique_coboundary {c : W → B → A}
    (hinv : ∀ w i, c w i * c (w * cs.simple i) i = 1)
    (hbraid : ∀ w i j, M i j ≠ 0 →
      cs.wordCocycleProd c w (braidWord M i j) = cs.wordCocycleProd c w (braidWord M j i)) :
    ∃! f : W → A, f 1 = 1 ∧ ∀ w i, (f w)⁻¹ * f (w * cs.simple i) = c w i := by
  let Φ : W →* (Equiv.Perm (W × A))ᵐᵒᵖ :=
    cs.lift ⟨fun i => MulOpposite.op (cs.coboundaryStep hinv i),
      cs.isLiftable_coboundaryStep hinv hbraid⟩
  have hΦs : ∀ i : B, Φ (cs.simple i) = MulOpposite.op (cs.coboundaryStep hinv i) :=
    fun i => cs.lift_apply_simple _ i
  have hfst : ∀ w : W, (MulOpposite.unop (Φ w) (1, 1)).1 = w := fun w => by
    refine cs.simple_induction_right (p := fun u => (MulOpposite.unop (Φ u) (1, 1)).1 = u)
      w (by simp [Φ]) fun u i ih => ?_
    rw [map_mul, MulOpposite.unop_mul, hΦs i, MulOpposite.unop_op, Equiv.Perm.mul_apply]
    simp [coboundaryStep, ih]
  let f : W → A := fun w => (MulOpposite.unop (Φ w) (1, 1)).2
  have hf1 : f 1 = 1 := by simp [f, Φ]
  have hfstep : ∀ w i, (f w)⁻¹ * f (w * cs.simple i) = c w i := fun w i => by
    have hstep : f (w * cs.simple i) = f w * c w i := by
      dsimp only [f]
      rw [map_mul, MulOpposite.unop_mul, hΦs i, MulOpposite.unop_op, Equiv.Perm.mul_apply]
      simp [coboundaryStep, hfst w]
    rw [hstep, inv_mul_cancel_left]
  refine ⟨f, ⟨hf1, hfstep⟩, ?_⟩
  rintro g ⟨hg1, hg⟩
  funext w
  have hmul := cs.eq_mul_of_inv_mul_eq (fun u i => (hfstep u i).trans (hg u i).symm) w
  simpa [hf1, hg1] using hmul

/-- Existential form of `CoxeterSystem.existsUnique_coboundary` without normalization at `1`. -/
theorem exists_coboundary {c : W → B → A}
    (hinv : ∀ w i, c w i * c (w * cs.simple i) i = 1)
    (hbraid : ∀ w i j, M i j ≠ 0 →
      cs.wordCocycleProd c w (braidWord M i j) = cs.wordCocycleProd c w (braidWord M j i)) :
    ∃ f : W → A, ∀ w i, (f w)⁻¹ * f (w * cs.simple i) = c w i := by
  obtain ⟨f, ⟨-, hf⟩, -⟩ := cs.existsUnique_coboundary hinv hbraid
  exact ⟨f, hf⟩

end CoxeterSystem
