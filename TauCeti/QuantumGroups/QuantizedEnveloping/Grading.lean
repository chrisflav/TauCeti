/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.QuantumGroups.QuantizedEnveloping.Basic

/-!
# Root-lattice grading of quantized enveloping algebras

For any Cartan datum `D : CartanDatum ι X Y` and parameter `q : K`, the Drinfeld–Jimbo defining
relations of `QuantizedEnvelopingAlgebra D q` are homogeneous with respect to the root lattice
`D.rootLattice = span_ℤ {αᵢ}`:
* `Eᵢ` has degree `αᵢ`;
* `Fᵢ` has degree `-αᵢ`;
* `K_y` (`y : Y`) has degree `0`.

In particular, `Eᵢ Fᵢ - Fᵢ Eᵢ = (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)` is homogeneous of degree `0`,
`Eᵢ Fⱼ = Fⱼ Eᵢ` (`i ≠ j`) is homogeneous of degree `αᵢ - αⱼ`, and the `qᵢ`-divided-power Serre
combinations `serreElement D q (e D q) i j` and `serreElement D q (f D q) i j` have degrees
`(1 - aᵢⱼ) αᵢ + αⱼ` and `-((1 - aᵢⱼ) αᵢ + αⱼ)`.

This file defines the homogeneous subspaces `gradePiece D q β` as the `K`-spans of generator words
of total root degree `β : D.rootLattice`, establishes the `SetLike.GradedMonoid` structure and the
toral conjugation formula `K_y x K_(-y) = q^⟨β, y⟩ • x` on `gradePiece D q β` without any
decidable-equality or nonvanishing assumption on `q`, and equips `QuantizedEnvelopingAlgebra D q`
with an internal `GradedAlgebra (gradePiece D q)` decomposition when `[DecidableEq D.rootLattice]`.

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.rootDegree` and
  `TauCeti.QuantizedEnvelopingAlgebra.generatorDegree`: the degrees in `D.rootLattice` of simple
  roots and presentation generators.
* `TauCeti.QuantizedEnvelopingAlgebra.gradePiece`: the homogeneous submodule of degree
  `β : D.rootLattice`.
* `TauCeti.QuantizedEnvelopingAlgebra.k_mul_mul_k_neg_of_mem_gradePiece`: for
  `x ∈ gradePiece D q β`, `K_y x K_(-y) = q^⟨β, y⟩ • x`.
* `TauCeti.QuantizedEnvelopingAlgebra.isInternal_gradePiece` and
  `TauCeti.QuantizedEnvelopingAlgebra.instGradedAlgebra`: `QuantizedEnvelopingAlgebra D q` is the
  internal direct sum of `gradePiece D q β` (`β : D.rootLattice`).

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, §4.7.
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.
* The universal-property grading realization follows
  `TauCeti.Algebra.Lie.UniversalEnveloping.Grading`.
-/

public section

open scoped DirectSum
open Finset

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-! ### Degrees of generators and homogeneous pieces -/

/-- The `i`-th simple root `αᵢ` viewed as an element of `D.rootLattice`. -/
def rootDegree (D : CartanDatum ι X Y) (i : ι) : D.rootLattice :=
  ⟨D.root i, D.root_mem_rootLattice i⟩

@[simp]
theorem coe_rootDegree (D : CartanDatum ι X Y) (i : ι) :
    (rootDegree D i : X) = D.root i := (rfl)

/-- Root-lattice degree of a presentation generator: `αᵢ` on `Eᵢ`, `-αᵢ` on `Fᵢ`, and `0` on
`K_y`. -/
def generatorDegree (D : CartanDatum ι X Y) : Generator ι Y → D.rootLattice
  | .e i => rootDegree D i
  | .f i => -rootDegree D i
  | .k _ => 0

@[simp]
theorem generatorDegree_e (D : CartanDatum ι X Y) (i : ι) :
    generatorDegree D (.e i) = rootDegree D i := (rfl)

@[simp]
theorem generatorDegree_f (D : CartanDatum ι X Y) (i : ι) :
    generatorDegree D (.f i) = -rootDegree D i := (rfl)

@[simp]
theorem generatorDegree_k (D : CartanDatum ι X Y) (y : Y) :
    generatorDegree D (.k y) = 0 := (rfl)

variable (D : CartanDatum ι X Y) (q : K)

/-- The homogeneous subspace of `QuantizedEnvelopingAlgebra D q` of root degree
`β : D.rootLattice`, defined as the `K`-span of products of generator words whose degrees sum to
`β`. -/
noncomputable def gradePiece (β : D.rootLattice) : Submodule K (QuantizedEnvelopingAlgebra D q) :=
  Submodule.span K
    {x | ∃ l : List (Generator ι Y),
      (l.map (generatorDegree D)).sum = β ∧ (l.map (generator D q)).prod = x}

/-- The defining word-span description of `gradePiece`. -/
theorem gradePiece_def (β : D.rootLattice) :
    gradePiece D q β =
      Submodule.span K
        {x | ∃ l : List (Generator ι Y),
          (l.map (generatorDegree D)).sum = β ∧ (l.map (generator D q)).prod = x} := (rfl)

/-- A submodule contains `gradePiece D q β` if and only if it contains every generator word of
degree `β`. -/
theorem gradePiece_le_iff (β : D.rootLattice)
    (p : Submodule K (QuantizedEnvelopingAlgebra D q)) :
    gradePiece D q β ≤ p ↔
      ∀ l : List (Generator ι Y), (l.map (generatorDegree D)).sum = β →
        (l.map (generator D q)).prod ∈ p := by
  rw [gradePiece_def, Submodule.span_le]
  constructor
  · intro h l hl
    exact h ⟨l, hl, rfl⟩
  · rintro h _ ⟨l, hl, rfl⟩
    exact h l hl

/-- Every generator word lies in the homogeneous piece of its total degree. -/
theorem listProd_mem_gradePiece (l : List (Generator ι Y)) :
    (l.map (generator D q)).prod ∈ gradePiece D q (l.map (generatorDegree D)).sum :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

/-- Every presentation generator lies in the homogeneous piece of its `generatorDegree`. -/
theorem generator_mem_gradePiece (g : Generator ι Y) :
    generator D q g ∈ gradePiece D q (generatorDegree D g) := by
  simpa using listProd_mem_gradePiece D q [g]

/-- `Eᵢ` has root degree `αᵢ`. -/
theorem e_mem_gradePiece (i : ι) : e D q i ∈ gradePiece D q (rootDegree D i) :=
  generator_mem_gradePiece D q (.e i)

/-- `Fᵢ` has root degree `-αᵢ`. -/
theorem f_mem_gradePiece (i : ι) : f D q i ∈ gradePiece D q (-rootDegree D i) :=
  generator_mem_gradePiece D q (.f i)

/-- `K_y` has root degree `0`. -/
theorem k_mem_gradePiece (y : Y) : k D q y ∈ gradePiece D q 0 :=
  generator_mem_gradePiece D q (.k y)

/-- `gradePiece D q` forms a `D.rootLattice`-graded monoid under multiplication. -/
instance instGradedMonoid : SetLike.GradedMonoid (gradePiece D q) where
  one_mem := Submodule.subset_span ⟨[], by simp, rfl⟩
  mul_mem := by
    intro α β a b ha hb
    have hmul : gradePiece D q α * gradePiece D q β ≤ gradePiece D q (α + β) := by
      rw [gradePiece_def, gradePiece_def, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨l₁, hl₁, rfl⟩, _, ⟨l₂, hl₂, rfl⟩, rfl⟩
      simpa [hl₁, hl₂] using listProd_mem_gradePiece D q (l₁ ++ l₂)
    exact hmul (Submodule.mul_mem_mul ha hb)

/-- Scalars lie in degree `0`. -/
theorem algebraMap_mem_gradePiece_zero (r : K) :
    algebraMap K (QuantizedEnvelopingAlgebra D q) r ∈ gradePiece D q 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ r (SetLike.one_mem_graded (gradePiece D q))

/-- `Eᵢ^(n)_(qᵢ)` has root degree `n • αᵢ`. -/
theorem quantumDividedPower_e_mem_gradePiece (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n ∈
      gradePiece D q (n • rootDegree D i) := by
  rw [quantumDividedPower_def]
  exact Submodule.smul_mem _ _ (SetLike.pow_mem_graded n (e_mem_gradePiece D q i))

/-- `Fᵢ^(n)_(qᵢ)` has root degree `-(n • αᵢ)`. -/
theorem quantumDividedPower_f_mem_gradePiece (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n ∈
      gradePiece D q (-(n • rootDegree D i)) := by
  rw [quantumDividedPower_def, ← smul_neg]
  exact Submodule.smul_mem _ _ (SetLike.pow_mem_graded n (f_mem_gradePiece D q i))

/-- For any family `x` with `x k ∈ gradePiece D q (σ k)`, `serreElement D q x i j` lies in
`gradePiece D q (serreLength D i j • σ i + σ j)`. -/
theorem serreElement_mem_gradePiece {σ : ι → D.rootLattice}
    {x : ι → QuantizedEnvelopingAlgebra D q} (hx : ∀ k, x k ∈ gradePiece D q (σ k)) (i j : ι) :
    serreElement D q x i j ∈ gradePiece D q (serreLength D i j • σ i + σ j) := by
  rw [serreElement_def]
  refine Submodule.sum_mem _ fun r hr => Submodule.smul_mem _ _ ?_
  have hle : r ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp hr)
  have hdeg : r • σ i + σ j + (serreLength D i j - r) • σ i =
      serreLength D i j • σ i + σ j := by
    rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hle]
  refine hdeg ▸ SetLike.mul_mem_graded (SetLike.mul_mem_graded ?_ (hx j)) ?_
  · rw [quantumDividedPower_def]
    exact Submodule.smul_mem _ _ (SetLike.pow_mem_graded r (hx i))
  · rw [quantumDividedPower_def]
    exact Submodule.smul_mem _ _ (SetLike.pow_mem_graded _ (hx i))

/-! ### Toral conjugation on homogeneous pieces -/

private theorem k_mul_generator_mul_k_neg (y : Y) (g : Generator ι Y) :
    k D q y * generator D q g * k D q (-y) =
      q ^ D.pairing (generatorDegree D g : X) y • generator D q g := by
  cases g with
  | e i => exact k_mul_e_mul_k_neg D q y i
  | f i =>
    simpa only [generatorDegree_f, NegMemClass.coe_neg, coe_rootDegree, map_neg,
      LinearMap.neg_apply] using k_mul_f_mul_k_neg D q y i
  | k z =>
    simp [add_comm y z, add_neg_cancel_right]

private theorem k_mul_listProd_mul_k_neg (l : List (Generator ι Y)) (y : Y) :
    k D q y * (l.map (generator D q)).prod * k D q (-y) =
      q ^ D.pairing (((l.map (generatorDegree D)).sum : D.rootLattice) : X) y •
        (l.map (generator D q)).prod := by
  by_cases hq : q = 0
  · induction l with
    | nil => simp
    | cons g l ih =>
      cases g with
      | e i =>
        have he : generator D q (.e i) = 0 := hq ▸ e_zero D i
        simp [List.map_cons, he]
      | f i =>
        have hf : generator D q (.f i) = 0 := hq ▸ f_zero D i
        simp [List.map_cons, hf]
      | k z =>
        simp only [List.map_cons, List.sum_cons, List.prod_cons, generatorDegree_k, zero_add]
        have hcomm : k D q y * (generator D q (.k z) * (l.map (generator D q)).prod) *
            k D q (-y) =
            generator D q (.k z) * (k D q y * (l.map (generator D q)).prod * k D q (-y)) := by
          rw [← mul_assoc (k D q y), (k_commute D q y z).eq]
          simp [mul_assoc]
        rw [hcomm, ih, mul_smul_comm]
  · induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons, Submodule.coe_add, map_add,
        LinearMap.add_apply]
      have hins : k D q y * (generator D q g * (l.map (generator D q)).prod) * k D q (-y) =
          (k D q y * generator D q g * k D q (-y)) *
            (k D q y * (l.map (generator D q)).prod * k D q (-y)) := by
        calc
          k D q y * (generator D q g * (l.map (generator D q)).prod) * k D q (-y) =
              k D q y * generator D q g * (k D q (-y + y) * (l.map (generator D q)).prod) *
                k D q (-y) := by simp [mul_assoc]
          _ = (k D q y * generator D q g * k D q (-y)) *
                (k D q y * (l.map (generator D q)).prod * k D q (-y)) := by
            rw [← k_mul_k]; simp [mul_assoc]
      rw [hins, k_mul_generator_mul_k_neg, ih, smul_mul_smul_comm, ← zpow_add₀ hq]

/-- Conjugating any homogeneous element `x ∈ gradePiece D q β` by `K_y` multiplies `x` by
`q^⟨β, y⟩`. -/
theorem k_mul_mul_k_neg_of_mem_gradePiece {D : CartanDatum ι X Y} {q : K} {β : D.rootLattice}
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradePiece D q β) (y : Y) :
    k D q y * x * k D q (-y) = q ^ D.pairing (β : X) y • x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl, rfl⟩ := hx
    exact k_mul_listProd_mul_k_neg D q l y
  | zero => simp
  | add a b _ _ ha hb =>
    rw [mul_add, add_mul, ha, hb, smul_add]
  | smul r a _ ha =>
    rw [mul_smul_comm, smul_mul_assoc, ha, smul_comm]

/-! ### Internal direct sum decomposition -/

section GradedAlgebra

variable [DecidableEq D.rootLattice]

private theorem of_gradePiece_mul {α β γ : D.rootLattice} (h : α + β = γ)
    {a b : QuantizedEnvelopingAlgebra D q} (ha : a ∈ gradePiece D q α)
    (hb : b ∈ gradePiece D q β) :
    DirectSum.of (fun δ => ↥(gradePiece D q δ)) α ⟨a, ha⟩ *
      DirectSum.of (fun δ => ↥(gradePiece D q δ)) β ⟨b, hb⟩ =
    DirectSum.of (fun δ => ↥(gradePiece D q δ)) γ ⟨a * b, h ▸ SetLike.mul_mem_graded ha hb⟩ := by
  subst h
  rw [DirectSum.of_mul_of]
  rfl

private theorem of_gradePiece_pow {α : D.rootLattice} {a : QuantizedEnvelopingAlgebra D q}
    (ha : a ∈ gradePiece D q α) (n : ℕ) :
    DirectSum.of (fun δ => ↥(gradePiece D q δ)) α ⟨a, ha⟩ ^ n =
      DirectSum.of (fun δ => ↥(gradePiece D q δ)) (n • α)
        ⟨a ^ n, SetLike.pow_mem_graded n ha⟩ := by
  induction n with
  | zero =>
    rw [pow_zero, DirectSum.one_def]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    exact Sigma.subtype_ext (zero_nsmul α).symm (pow_zero a).symm
  | succ n ih =>
    rw [pow_succ, ih, of_gradePiece_mul D q (succ_nsmul α n).symm]
    congr 1
    exact Subtype.ext (pow_succ a n).symm

private theorem of_gradePiece_quantumDividedPower (q₀ : K) {α : D.rootLattice}
    {a : QuantizedEnvelopingAlgebra D q} (ha : a ∈ gradePiece D q α) (n : ℕ) :
    quantumDividedPower q₀ (DirectSum.of (fun δ => ↥(gradePiece D q δ)) α ⟨a, ha⟩) n =
      DirectSum.of (fun δ => ↥(gradePiece D q δ)) (n • α)
        ⟨quantumDividedPower q₀ a n,
          quantumDividedPower_def q₀ a n ▸
            Submodule.smul_mem _ _ (SetLike.pow_mem_graded n ha)⟩ := by
  rw [quantumDividedPower_def, of_gradePiece_pow, ← DirectSum.of_smul]
  congr 1
  exact Subtype.ext (quantumDividedPower_def q₀ a n).symm

private theorem serreElement_of_gradePiece (σ : ι → D.rootLattice)
    (x : ι → QuantizedEnvelopingAlgebra D q) (hx : ∀ k, x k ∈ gradePiece D q (σ k)) (i j : ι) :
    serreElement D q
        (fun k => DirectSum.of (fun δ => ↥(gradePiece D q δ)) (σ k) ⟨x k, hx k⟩) i j =
      DirectSum.of (fun δ => ↥(gradePiece D q δ)) (serreLength D i j • σ i + σ j)
        ⟨serreElement D q x i j, serreElement_mem_gradePiece D q hx i j⟩ := by
  let term : ↥(range (serreLength D i j + 1)) →
      ↥(gradePiece D q (serreLength D i j • σ i + σ j)) := fun r =>
    (-1 : K) ^ (r : ℕ) •
      ⟨quantumDividedPower (q ^ D.symmetrizer i) (x i) r * x j *
          quantumDividedPower (q ^ D.symmetrizer i) (x i) (serreLength D i j - r), by
        have hle : (r : ℕ) ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp r.2)
        have hdeg : (r : ℕ) • σ i + σ j + (serreLength D i j - r) • σ i =
            serreLength D i j • σ i + σ j := by
          rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hle]
        refine hdeg ▸ SetLike.mul_mem_graded (SetLike.mul_mem_graded ?_ (hx j)) ?_
        · rw [quantumDividedPower_def]
          exact Submodule.smul_mem _ _ (SetLike.pow_mem_graded (r : ℕ) (hx i))
        · rw [quantumDividedPower_def]
          exact Submodule.smul_mem _ _ (SetLike.pow_mem_graded _ (hx i))⟩
  have hterm : ∀ r : ↥(range (serreLength D i j + 1)),
      (-1 : K) ^ (r : ℕ) •
          (quantumDividedPower (q ^ D.symmetrizer i)
              (DirectSum.of (fun δ => ↥(gradePiece D q δ)) (σ i) ⟨x i, hx i⟩) r *
            DirectSum.of (fun δ => ↥(gradePiece D q δ)) (σ j) ⟨x j, hx j⟩ *
            quantumDividedPower (q ^ D.symmetrizer i)
              (DirectSum.of (fun δ => ↥(gradePiece D q δ)) (σ i) ⟨x i, hx i⟩)
              (serreLength D i j - r)) =
        DirectSum.of (fun δ => ↥(gradePiece D q δ)) (serreLength D i j • σ i + σ j) (term r) := by
    intro r
    have hle : (r : ℕ) ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp r.2)
    have hdeg : (r : ℕ) • σ i + σ j + (serreLength D i j - r) • σ i =
        serreLength D i j • σ i + σ j := by
      rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hle]
    rw [of_gradePiece_quantumDividedPower, of_gradePiece_quantumDividedPower,
      of_gradePiece_mul D q rfl, of_gradePiece_mul D q hdeg, ← DirectSum.of_smul]
  conv_lhs => rw [serreElement_def, ← sum_attach]
  rw [sum_congr rfl fun r _ => hterm r, ← map_sum]
  congr 1
  apply Subtype.ext
  rw [← (gradePiece D q _).coe_subtype, map_sum]
  simp only [Submodule.coe_subtype, term, SetLike.val_smul, serreElement_def]
  exact sum_attach (range (serreLength D i j + 1)) fun r =>
    (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i) (x i) r * x j *
        quantumDividedPower (q ^ D.symmetrizer i) (x i) (serreLength D i j - r))

private noncomputable def decomposeAlgHom :
    QuantizedEnvelopingAlgebra D q →ₐ[K] ⨁ β, gradePiece D q β :=
  lift
    { e := fun i =>
        DirectSum.of (fun β => ↥(gradePiece D q β)) (rootDegree D i)
          ⟨e D q i, e_mem_gradePiece D q i⟩
      f := fun i =>
        DirectSum.of (fun β => ↥(gradePiece D q β)) (-rootDegree D i)
          ⟨f D q i, f_mem_gradePiece D q i⟩
      k := fun y =>
        DirectSum.of (fun β => ↥(gradePiece D q β)) 0
          ⟨k D q y, k_mem_gradePiece D q y⟩
      k_zero := by
        rw [DirectSum.one_def]
        congr 1
        exact Subtype.ext (k_zero D q)
      k_mul_k := fun y z => by
        rw [of_gradePiece_mul D q (zero_add 0)]
        congr 1
        exact Subtype.ext (k_mul_k D q y z)
      k_mul_e_mul_k_neg := fun y i => by
        rw [of_gradePiece_mul D q (zero_add _), of_gradePiece_mul D q (add_zero _),
          ← DirectSum.of_smul]
        congr 1
        exact Subtype.ext (k_mul_e_mul_k_neg D q y i)
      k_mul_f_mul_k_neg := fun y i => by
        rw [of_gradePiece_mul D q (zero_add _), of_gradePiece_mul D q (add_zero _),
          ← DirectSum.of_smul]
        congr 1
        exact Subtype.ext (k_mul_f_mul_k_neg D q y i)
      e_mul_f_sub_f_mul_e_self := fun i => by
        rw [of_gradePiece_mul D q (add_neg_cancel _), of_gradePiece_mul D q (neg_add_cancel _),
          ← map_sub (DirectSum.of (fun β => ↥(gradePiece D q β)) 0),
          ← map_sub (DirectSum.of (fun β => ↥(gradePiece D q β)) 0),
          ← DirectSum.of_smul]
        congr 1
        exact Subtype.ext (e_mul_f_sub_f_mul_e_self D q i)
      e_mul_f_of_ne := fun {i j} hij => by
        rw [of_gradePiece_mul D q rfl,
          of_gradePiece_mul D q (add_comm (-rootDegree D j) (rootDegree D i))]
        congr 1
        exact Subtype.ext (e_mul_f_of_ne D q hij)
      serre_e := fun {i j} hij => by
        rw [serreElement_of_gradePiece D q (rootDegree D) (e D q) (e_mem_gradePiece D q) i j]
        have h0 :
            (⟨serreElement D q (e D q) i j,
                serreElement_mem_gradePiece D q (e_mem_gradePiece D q) i j⟩ :
              ↥(gradePiece D q _)) = 0 :=
          Subtype.ext (serre_e D q hij)
        rw [h0, map_zero]
      serre_f := fun {i j} hij => by
        rw [serreElement_of_gradePiece D q (fun k => -rootDegree D k) (f D q)
          (f_mem_gradePiece D q) i j]
        have h0 :
            (⟨serreElement D q (f D q) i j,
                serreElement_mem_gradePiece D q (f_mem_gradePiece D q) i j⟩ :
              ↥(gradePiece D q _)) = 0 :=
          Subtype.ext (serre_f D q hij)
        rw [h0, map_zero] }

private theorem decomposeAlgHom_generator (g : Generator ι Y) :
    decomposeAlgHom D q (generator D q g) =
      DirectSum.of (fun β => ↥(gradePiece D q β)) (generatorDegree D g)
        ⟨generator D q g, generator_mem_gradePiece D q g⟩ := by
  cases g with
  | e i => exact lift_e _ i
  | f i => exact lift_f _ i
  | k y => exact lift_k _ y

private theorem coeAlgHom_comp_decomposeAlgHom :
    (DirectSum.coeAlgHom (gradePiece D q)).comp (decomposeAlgHom D q) =
      AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by
  ext <;> simp [decomposeAlgHom]

private theorem decomposeAlgHom_listProd (l : List (Generator ι Y)) :
    decomposeAlgHom D q (l.map (generator D q)).prod =
      DirectSum.of (fun β => ↥(gradePiece D q β)) (l.map (generatorDegree D)).sum
        ⟨(l.map (generator D q)).prod, listProd_mem_gradePiece D q l⟩ := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, map_one, DirectSum.one_def]
    rfl
  | cons g l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, decomposeAlgHom_generator,
      ih, of_gradePiece_mul D q rfl]
    rfl

private theorem decomposeAlgHom_apply (β : D.rootLattice) (x : gradePiece D q β) :
    decomposeAlgHom D q (x : QuantizedEnvelopingAlgebra D q) =
      DirectSum.of (fun δ => ↥(gradePiece D q δ)) β x := by
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl, rfl⟩ := hx
    exact decomposeAlgHom_listProd D q l
  | zero =>
    rw [map_zero]
    exact (map_zero (DirectSum.of (fun δ => ↥(gradePiece D q δ)) β)).symm
  | add a b _ _ ha hb =>
    rw [map_add, ha, hb, ← map_add]
    rfl
  | smul r a _ ha =>
    rw [map_smul, ha, ← DirectSum.of_smul]
    rfl

/-- The homogeneous root-degree pieces form an internal direct sum decomposition of
`QuantizedEnvelopingAlgebra D q`. -/
theorem isInternal_gradePiece : DirectSum.IsInternal (gradePiece D q) := by
  let := GradedAlgebra.ofAlgHom (gradePiece D q) (decomposeAlgHom D q)
    (coeAlgHom_comp_decomposeAlgHom D q) (decomposeAlgHom_apply D q)
  exact DirectSum.Decomposition.isInternal (gradePiece D q)

/-- `QuantizedEnvelopingAlgebra D q` is internally graded by the root lattice `D.rootLattice`. -/
noncomputable instance instGradedAlgebra : GradedAlgebra (gradePiece D q) :=
  (isInternal_gradePiece D q).gradedAlgebra

end GradedAlgebra

end TauCeti.QuantizedEnvelopingAlgebra
