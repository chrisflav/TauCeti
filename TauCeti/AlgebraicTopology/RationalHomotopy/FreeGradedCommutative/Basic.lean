/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic

import Mathlib.Data.Finsupp.Basic
import TauCeti.Algebra.CharP.Invertible
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Free graded-commutative algebras

An internally `ℤ`-graded `R`-algebra `(A, 𝒜)` is **free graded-commutative** on a linearly
ordered family of homogeneous generators `x : ι → A` of natural-number degrees `deg : ι → ℕ` when:

1. each generator `x i` lies in `𝒜 (deg i)`;
2. the generators satisfy the Koszul commutation law
   `x i * x j = (-1) ^ (deg i * deg j) • (x j * x i)`;
3. the standard monomials `x_{i₁}^{f i₁} ⋯ x_{i_k}^{f i_k}` (`i₁ < ⋯ < i_k`) indexed by
   exponent vectors `f : ι →₀ ℕ` with `f i ≤ 1` for odd `deg i` form an `R`-basis of `A`.

Over a commutative ring `R` in which `2` is invertible (in particular over any field of
characteristic zero), odd generators square to zero and products of standard monomials are either
zero (when an odd generator appears in both factors) or a Koszul sign times a standard monomial.
This yields the universal property (`TauCeti.IsFreeGradedCommutative.lift`,
`TauCeti.IsFreeGradedCommutative.existsUnique_algHom`).

Over an arbitrary commutative ring `R`, the graded commutativity of homogeneous elements, degree
spans, algebra-map extensionality, and the criterion characterizing morphisms of differential
graded algebras out of a free graded-commutative DG algebra
(`TauCeti.IsFreeGradedCommutative.exists_dgAlgHom_iff`) hold without inverting `2`.

## Main definitions

* `TauCeti.ExponentVector`: finitely supported exponent vectors bounded by `1` on odd-degree
  indices.
* `TauCeti.monomialDegree` and `TauCeti.standardMonomial`: the total degree and ordered product
  attached to an exponent vector.
* `TauCeti.monomialMulSign`: the Koszul sign arising when multiplying two standard monomials.
* `TauCeti.IsFreeGradedCommutative`: predicate asserting that an internally `ℤ`-graded algebra is
  free graded-commutative on a linearly ordered family of homogeneous generators.
* `TauCeti.IsFreeGradedCommutative.basis`: the standard monomial basis.
* `TauCeti.IsFreeGradedCommutative.lift`, `TauCeti.IsFreeGradedCommutative.gradedLift`, and
  `TauCeti.IsFreeGradedCommutative.dgLift`: universal-property maps out of a free
  graded-commutative (DG) algebra.

## Main results

* `TauCeti.standardMonomial_mul_eq_smul` and `TauCeti.standardMonomial_mul_eq_zero_of_odd`: the
  product formula for standard monomials.
* `TauCeti.IsFreeGradedCommutative.grade_eq_span_standardMonomial`,
  `TauCeti.IsFreeGradedCommutative.grade_eq_bot_of_neg`, and
  `TauCeti.IsFreeGradedCommutative.grade_zero_eq_one_of_pos`: degree structure.
* `TauCeti.IsFreeGradedCommutative.mul_comm_graded`: homogeneous elements supercommute.
* `TauCeti.IsFreeGradedCommutative.algHom_ext`: algebra maps are determined on generators.
* `TauCeti.IsFreeGradedCommutative.existsUnique_algHom`: universal property of `ΛV`.
* `TauCeti.IsFreeGradedCommutative.exists_dgAlgHom_iff`: an algebra map preserving generator
  degrees is a DG algebra morphism iff it commutes with the differentials on generators.

## References

* Y. Félix, S. Halperin, and J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in
  Mathematics 205, Springer (2001), Section 3.
* K. Hess, *Rational homotopy theory: a brief introduction*, Contemporary Mathematics 436 (2007),
  Section 1.
* J. W. Morgan, *The algebraic topology of smooth algebraic varieties*, Publications Mathématiques
  de l'IHÉS 48 (1978), Section 5.
-/

public section

open DirectSum

namespace TauCeti

universe u v w

/-! ### Exponent vectors and standard monomials -/

section Monomials

/-- Exponent vectors of standard monomials in generators of degrees `deg`: finitely supported,
with every generator of odd degree occurring at most once. -/
abbrev ExponentVector {ι : Type w} (deg : ι → ℕ) : Type w :=
  {f : ι →₀ ℕ // ∀ i, Odd (deg i) → f i ≤ 1}

namespace ExponentVector

variable {ι : Type w} {deg : ι → ℕ}

instance : Zero (ExponentVector deg) where
  zero := ⟨0, fun _ _ => Nat.zero_le 1⟩

@[simp]
theorem coe_zero : ((0 : ExponentVector deg) : ι →₀ ℕ) = 0 := (rfl)

/-- The unit exponent vector concentrated at a single generator `i`. -/
noncomputable def single (i : ι) : ExponentVector deg :=
  ⟨Finsupp.single i 1, fun j _ => by
    classical
    rw [Finsupp.single_apply]
    split_ifs <;> omega⟩

@[simp]
theorem coe_single (i : ι) : ((single (deg := deg) i : ExponentVector deg) : ι →₀ ℕ) =
    Finsupp.single i 1 := (rfl)

/-- An exponent vector concentrated at a single generator `i` with exponent `n`. -/
noncomputable def singlePow (i : ι) (n : ℕ) (hn : Odd (deg i) → n ≤ 1) : ExponentVector deg :=
  ⟨Finsupp.single i n, fun j hj => by
    classical
    rw [Finsupp.single_apply]
    split_ifs with h
    · subst h; exact hn hj
    · exact Nat.zero_le 1⟩

@[simp]
theorem coe_singlePow (i : ι) (n : ℕ) (hn : Odd (deg i) → n ≤ 1) :
    ((singlePow (deg := deg) i n hn : ExponentVector deg) : ι →₀ ℕ) = Finsupp.single i n := (rfl)

end ExponentVector

/-- The total degree `∑ᵢ f i * deg i` of an exponent vector `f`. -/
def monomialDegree {ι : Type w} (deg : ι → ℕ) (f : ι →₀ ℕ) : ℕ :=
  f.sum fun i n => n * deg i

theorem monomialDegree_def {ι : Type w} (deg : ι → ℕ) (f : ι →₀ ℕ) :
    monomialDegree deg f = f.sum fun i n => n * deg i := (rfl)

@[simp]
theorem monomialDegree_zero {ι : Type w} (deg : ι → ℕ) :
    monomialDegree deg 0 = 0 := by
  simp [monomialDegree]

@[simp]
theorem monomialDegree_single {ι : Type w} (deg : ι → ℕ) (i : ι) (n : ℕ) :
    monomialDegree deg (Finsupp.single i n) = n * deg i := by
  simp [monomialDegree]

theorem monomialDegree_add {ι : Type w} (deg : ι → ℕ) (f g : ι →₀ ℕ) :
    monomialDegree deg (f + g) = monomialDegree deg f + monomialDegree deg g :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem monomialDegree_eq_zero_iff {ι : Type w} {deg : ι → ℕ}
    (hpos : ∀ i, 0 < deg i) {f : ι →₀ ℕ} :
    monomialDegree deg f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext i
    by_contra hi
    exact Nat.ne_of_gt (Nat.mul_pos (Nat.pos_of_ne_zero hi) (hpos i))
      (Finset.sum_eq_zero_iff.1 h i (Finsupp.mem_support_iff.2 hi))
  · rintro rfl
    exact monomialDegree_zero deg

theorem monomialDegree_pos_iff {ι : Type w} {deg : ι → ℕ}
    (hpos : ∀ i, 0 < deg i) {f : ι →₀ ℕ} :
    0 < monomialDegree deg f ↔ f ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, monomialDegree_eq_zero_iff hpos]

/-- The standard monomial `x_{i₁}^{f i₁} ⋯ x_{i_k}^{f i_k}`, `i₁ < ⋯ < i_k`, of an exponent
vector `f`. -/
def standardMonomial {A : Type v} [Monoid A] {ι : Type w} [LinearOrder ι]
    (x : ι → A) (f : ι →₀ ℕ) : A :=
  ((f.support.sort (· ≤ ·)).map fun i => x i ^ f i).prod

theorem standardMonomial_def {A : Type v} [Monoid A] {ι : Type w} [LinearOrder ι]
    (x : ι → A) (f : ι →₀ ℕ) :
    standardMonomial x f = ((f.support.sort (· ≤ ·)).map fun i => x i ^ f i).prod := (rfl)

@[simp]
theorem standardMonomial_zero {A : Type v} [Monoid A] {ι : Type w} [LinearOrder ι]
    (x : ι → A) : standardMonomial x 0 = 1 := by
  simp [standardMonomial]

@[simp]
theorem standardMonomial_single {A : Type v} [Monoid A] {ι : Type w} [LinearOrder ι]
    (x : ι → A) (i : ι) (n : ℕ) : standardMonomial x (Finsupp.single i n) = x i ^ n := by
  by_cases hn : n = 0
  · subst hn; simp
  · simp [standardMonomial, Finsupp.support_single i hn]

theorem standardMonomial_single_one {A : Type v} [Monoid A] {ι : Type w} [LinearOrder ι]
    (x : ι → A) (i : ι) : standardMonomial x (Finsupp.single i 1) = x i := by
  simp

theorem map_standardMonomial {A B F : Type*} [Monoid A] [Monoid B] [FunLike F A B]
    [MonoidHomClass F A B] {ι : Type*} [LinearOrder ι] (φ : F) (x : ι → A) (f : ι →₀ ℕ) :
    φ (standardMonomial x f) = standardMonomial (φ ∘ x) f := by
  simp [standardMonomial, map_list_prod, List.map_map, Function.comp_def]

/-- When every index in the support of `f₁` strictly precedes every index in the support of `f₂`,
the sorted support of `f₁ + f₂` is the concatenation of their sorted supports. -/
private theorem sort_support_add_of_lt {ι : Type*} [LinearOrder ι] {f₁ f₂ : ι →₀ ℕ}
    (h : ∀ a ∈ f₁.support, ∀ b ∈ f₂.support, a < b) :
    (f₁ + f₂).support.sort (· ≤ ·) =
      f₁.support.sort (· ≤ ·) ++ f₂.support.sort (· ≤ ·) := by
  have hsupp : (f₁ + f₂).support = f₁.support ∪ f₂.support := by
    ext i
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finset.mem_union]
    omega
  have hnodup : (f₁.support.sort (· ≤ ·) ++ f₂.support.sort (· ≤ ·)).Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.sort_nodup _ _, Finset.sort_nodup _ _, fun a ha b hb hab => ?_⟩
    rw [Finset.mem_sort] at ha hb
    exact (h a ha b hb).ne hab
  have hperm : ((f₁ + f₂).support.sort (· ≤ ·)).Perm
      (f₁.support.sort (· ≤ ·) ++ f₂.support.sort (· ≤ ·)) := by
    refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hnodup).2 fun a => ?_
    simp [Finset.mem_sort, hsupp]
  have hpw : (f₁.support.sort (· ≤ ·) ++ f₂.support.sort (· ≤ ·)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨Finset.pairwise_sort _ _, Finset.pairwise_sort _ _, fun a ha b hb => ?_⟩
    rw [Finset.mem_sort] at ha hb
    exact (h a ha b hb).le
  exact hperm.eq_of_pairwise' (Finset.pairwise_sort _ _) hpw

/-- If every index in the support of `f₁` strictly precedes every index in the support of `f₂`,
the standard monomial of `f₁ + f₂` is the product of those of `f₁` and `f₂`. -/
theorem standardMonomial_add_of_lt {A : Type*} [Monoid A] {ι : Type*} [LinearOrder ι]
    (x : ι → A) {f₁ f₂ : ι →₀ ℕ} (h : ∀ a ∈ f₁.support, ∀ b ∈ f₂.support, a < b) :
    standardMonomial x (f₁ + f₂) = standardMonomial x f₁ * standardMonomial x f₂ := by
  simp only [standardMonomial, sort_support_add_of_lt h, List.map_append, List.prod_append]
  congr 1
  · congr 1
    refine List.map_congr_left fun i hi => ?_
    rw [Finset.mem_sort] at hi
    have hi₂ : f₂ i = 0 := by
      by_contra hne
      exact (h i hi i (Finsupp.mem_support_iff.2 hne)).false
    simp [hi₂]
  · congr 1
    refine List.map_congr_left fun i hi => ?_
    rw [Finset.mem_sort] at hi
    have hi₁ : f₁ i = 0 := by
      by_contra hne
      exact (h i (Finsupp.mem_support_iff.2 hne) i hi).false
    simp [hi₁]

/-- Sum of `f i * deg i` over the sorted support list equals `monomialDegree deg f`. -/
private theorem sum_sort_support_degree {ι : Type*} [LinearOrder ι] (deg : ι → ℕ) (f : ι →₀ ℕ) :
    ((f.support.sort (· ≤ ·)).map fun i => (f i * deg i : ℤ)).sum =
      (monomialDegree deg f : ℤ) := by
  have hms : ((f.support.sort (· ≤ ·)).map fun i => (f i * deg i : ℤ)).sum =
      f.support.sum fun i => (f i * deg i : ℤ) := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
    rfl
  rw [hms, monomialDegree, Finsupp.sum, Nat.cast_sum]
  simp [Nat.cast_mul]

/-- Standard monomials of homogeneous generators are homogeneous of the corresponding total
degree. -/
theorem standardMonomial_mem_graded {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [SetLike.GradedMonoid 𝒜] {ι : Type*} [LinearOrder ι]
    {x : ι → A} {deg : ι → ℕ} (hx : ∀ i, x i ∈ 𝒜 (deg i)) (f : ι →₀ ℕ) :
    standardMonomial x f ∈ 𝒜 (monomialDegree deg f : ℤ) := by
  have hlist : ∀ l : List ι,
      (l.map fun i => x i ^ f i).prod ∈ 𝒜 ((l.map fun i => (f i * deg i : ℤ)).sum) := by
    intro l
    induction l with
    | nil => simpa using SetLike.one_mem_graded 𝒜
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      have hpow : x i ^ f i ∈ 𝒜 ((f i * deg i : ℕ) : ℤ) := by
        simpa [Nat.cast_mul] using SetLike.pow_mem_graded (f i) (hx i)
      simpa [Nat.cast_mul] using SetLike.mul_mem_graded hpow ih
  rw [standardMonomial, ← sum_sort_support_degree deg f]
  exact hlist _

end Monomials

/-! ### Product formula for standard monomials -/

section ProductFormula

/-- The Koszul sign obtained when reordering `standardMonomial x f * standardMonomial x g` into
`standardMonomial x (f + g)`. -/
def monomialMulSign {ι : Type w} [LinearOrder ι] (deg : ι → ℕ) (f g : ι →₀ ℕ) : ℤˣ :=
  (((f.support ×ˢ g.support).filter fun p => p.2 < p.1).sum fun p =>
    ((f p.1 * deg p.1 : ℕ) * (g p.2 * deg p.2 : ℕ) : ℤ)).negOnePow

@[simp]
theorem monomialMulSign_zero_left {ι : Type w} [LinearOrder ι] (deg : ι → ℕ) (g : ι →₀ ℕ) :
    monomialMulSign deg 0 g = 1 := by
  simp [monomialMulSign]

@[simp]
theorem monomialMulSign_zero_right {ι : Type w} [LinearOrder ι] (deg : ι → ℕ) (f : ι →₀ ℕ) :
    monomialMulSign deg f 0 = 1 := by
  simp [monomialMulSign]

/-- If every element in the support of `f` has even degree, the reordering sign against any `g`
is `1`. -/
theorem monomialMulSign_eq_one_of_even_left {ι : Type w} [LinearOrder ι] (deg : ι → ℕ)
    {f : ι →₀ ℕ} (hf : ∀ i ∈ f.support, Even (deg i)) (g : ι →₀ ℕ) :
    monomialMulSign deg f g = 1 := by
  apply Int.negOnePow_even
  refine Finset.even_sum _ fun p hp => ?_
  obtain ⟨k, hk⟩ := hf p.1 (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1
  refine ⟨((f p.1 * k : ℕ) * (g p.2 * deg p.2 : ℕ) : ℤ), ?_⟩
  push_cast [hk]
  ring

/-- Powers of Koszul-commuting elements satisfy the scaled Koszul commutation law. -/
private theorem pow_mul_pow_comm {A : Type*} [Ring A] {a b : A} {p q : ℕ}
    (h : a * b = ((p : ℤ) * q).negOnePow • (b * a)) (m n : ℕ) :
    a ^ m * b ^ n = (((m * p : ℕ) * (n * q : ℕ) : ℤ)).negOnePow • (b ^ n * a ^ m) := by
  have h1 : ∀ k : ℕ, a * b ^ k = (((p : ℤ) * (k * q : ℕ))).negOnePow • (b ^ k * a) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mul_assoc, h, smul_mul_assoc, mul_assoc, ih, mul_smul_comm, ← mul_assoc,
        smul_smul, ← Int.negOnePow_add]
      congr 2; push_cast; ring
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_assoc, h1 n, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc, mul_assoc,
      smul_smul, ← Int.negOnePow_add]
    congr 2; push_cast; ring

/-- Commuting a single generator power past a standard monomial. -/
private theorem standardMonomial_mul_pow {A : Type*} [Ring A] {ι : Type*} [LinearOrder ι]
    {u : ι → A} {deg : ι → ℕ}
    (hcomm : ∀ i j, u i * u j = (((deg i : ℤ) * deg j)).negOnePow • (u j * u i))
    (f : ι →₀ ℕ) (j : ι) (m : ℕ) :
    standardMonomial u f * u j ^ m =
      ((f.support.sum fun i => ((f i * deg i : ℕ) * (m * deg j : ℕ) : ℤ))).negOnePow •
        (u j ^ m * standardMonomial u f) := by
  have hlist : ∀ l : List ι,
      (l.map fun i => u i ^ f i).prod * u j ^ m =
        ((l.map fun i => ((f i * deg i : ℕ) * (m * deg j : ℕ) : ℤ)).sum).negOnePow •
          (u j ^ m * (l.map fun i => u i ^ f i).prod) := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [mul_assoc, ih, mul_smul_comm, ← mul_assoc,
        pow_mul_pow_comm (hcomm i j) (f i) m, smul_mul_assoc, mul_assoc, smul_smul,
        ← Int.negOnePow_add, add_comm]
  have hsum : ((f.support.sort (· ≤ ·)).map fun i =>
        ((f i * deg i : ℕ) * (m * deg j : ℕ) : ℤ)).sum =
      f.support.sum fun i => ((f i * deg i : ℕ) * (m * deg j : ℕ) : ℤ) := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
    rfl
  rw [standardMonomial, ← hsum]
  exact hlist _

/-- Splitting a standard monomial at an index `j` into `< j`, `= j`, and `> j` parts. -/
private theorem standardMonomial_split_at {A : Type*} [Monoid A] {ι : Type*} [LinearOrder ι]
    (u : ι → A) (f : ι →₀ ℕ) (j : ι) (k : ℕ) :
    standardMonomial u (f.filter (· < j) + Finsupp.single j k + f.filter (j < ·)) =
      standardMonomial u (f.filter (· < j)) * u j ^ k * standardMonomial u (f.filter (j < ·)) := by
  have h1 : ∀ a ∈ (f.filter (· < j)).support, ∀ b ∈ (Finsupp.single j k).support, a < b := by
    intro a ha b hb
    have ha' : a < j := (Finsupp.mem_support_iff.1 ha |> fun h => by
      simp only [Finsupp.filter_apply] at h; split_ifs at h <;> [assumption; contradiction])
    exact (Finset.mem_singleton.1 (Finsupp.support_single_subset hb)) ▸ ha'
  have h2 : ∀ a ∈ (f.filter (· < j) + Finsupp.single j k).support,
      ∀ b ∈ (f.filter (j < ·)).support, a < b := by
    intro a ha b hb
    have hb' : j < b := (Finsupp.mem_support_iff.1 hb |> fun h => by
      simp only [Finsupp.filter_apply] at h; split_ifs at h <;> [assumption; contradiction])
    have ha' : a ≤ j := by
      have h := Finsupp.mem_support_iff.1 ha
      simp only [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.single_apply] at h
      by_contra hnot
      have hgt : j < a := lt_of_not_ge hnot
      simp [not_lt.2 hgt.le, hgt.ne] at h
    exact lt_of_le_of_lt ha' hb'
  rw [standardMonomial_add_of_lt u h2, standardMonomial_add_of_lt u h1, standardMonomial_single]

/-- Right multiplication of a standard monomial by a single generator power. -/
private theorem standardMonomial_mul_single {A : Type*} [Ring A] {ι : Type*} [LinearOrder ι]
    {u : ι → A} {deg : ι → ℕ}
    (hcomm : ∀ i j, u i * u j = (((deg i : ℤ) * deg j)).negOnePow • (u j * u i))
    (f : ι →₀ ℕ) (j : ι) (m : ℕ) :
    standardMonomial u f * u j ^ m =
      monomialMulSign deg f (Finsupp.single j m) •
        standardMonomial u (f + Finsupp.single j m) := by
  by_cases hm : m = 0
  · subst hm; simp
  have hf : f = f.filter (· < j) + Finsupp.single j (f j) + f.filter (j < ·) := by
    ext i
    simp only [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.single_apply]
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · simp [hlt, hlt.ne', not_lt.2 hlt.le]
    · simp
    · simp [hgt, hgt.ne, not_lt.2 hgt.le]
  have hf' : f + Finsupp.single j m =
      f.filter (· < j) + Finsupp.single j (f j + m) + f.filter (j < ·) := by
    conv_lhs => rw [hf]
    rw [Finsupp.single_add]
    abel
  have hsign : (((f.filter (j < ·)).support.sum fun i =>
        (((f.filter (j < ·)) i * deg i : ℕ) * (m * deg j : ℕ) : ℤ))).negOnePow =
      monomialMulSign deg f (Finsupp.single j m) := by
    unfold monomialMulSign
    congr 1
    rw [Finsupp.support_single j hm]
    have hGtSupp : (f.filter (j < ·)).support = f.support.filter (j < ·) := by
      ext i; simp [Finsupp.mem_support_iff]
    rw [hGtSupp]
    refine Finset.sum_bij (fun i _ => (i, j)) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hi ⊢
      exact ⟨⟨hi.1, trivial⟩, hi.2⟩
    · intro _ _ _ _ h; exact (Prod.mk.inj h).1
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp
      exact ⟨p.1, Finset.mem_filter.2 ⟨hp.1.1, hp.1.2 ▸ hp.2⟩, Prod.ext rfl hp.1.2.symm⟩
    · intro i hi
      simp [(Finset.mem_filter.1 hi).2]
  conv_lhs => rw [hf, standardMonomial_split_at]
  rw [hf', standardMonomial_split_at, mul_assoc, standardMonomial_mul_pow hcomm _ j m,
    mul_smul_comm, ← mul_assoc, mul_assoc (standardMonomial u (f.filter (· < j))), ← pow_add,
    hsign]

/-- **Product formula for standard monomials**: for any Koszul-commuting family `u`, the product of
two standard monomials equals the Koszul reordering sign times the standard monomial of the sum of
their exponent vectors. -/
theorem standardMonomial_mul_eq_smul {A : Type*} [Ring A] {ι : Type*} [LinearOrder ι]
    {u : ι → A} {deg : ι → ℕ}
    (hcomm : ∀ i j, u i * u j = (((deg i : ℤ) * deg j)).negOnePow • (u j * u i))
    (f g : ι →₀ ℕ) :
    standardMonomial u f * standardMonomial u g =
      monomialMulSign deg f g • standardMonomial u (f + g) := by
  induction hn : g.support.card generalizing f g with
  | zero =>
    have hg : g = 0 := Finsupp.support_eq_empty.1 (Finset.card_eq_zero.1 hn)
    subst hg; simp
  | succ n ih =>
    have hne : g.support.Nonempty := Finset.card_pos.1 (hn ▸ Nat.succ_pos n)
    let j : ι := g.support.min' hne
    have hj : j ∈ g.support := Finset.min'_mem _ hne
    have hgj : g j ≠ 0 := Finsupp.mem_support_iff.1 hj
    let g₁ : ι →₀ ℕ := Finsupp.single j (g j)
    let g₂ : ι →₀ ℕ := g.filter (· ≠ j)
    have hg : g = g₁ + g₂ := by
      ext i
      simp only [g₁, g₂, Finsupp.add_apply, Finsupp.single_apply, Finsupp.filter_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    have hlt : ∀ a ∈ g₁.support, ∀ b ∈ g₂.support, a < b := by
      intro a ha b hb
      have ha' : a = j := Finset.mem_singleton.1 (Finsupp.support_single_subset ha)
      have hb' : b ∈ g.support ∧ b ≠ j := by simpa [g₂, Finsupp.mem_support_iff] using hb
      exact ha' ▸ lt_of_le_of_ne (Finset.min'_le _ _ hb'.1) hb'.2.symm
    have hg₂card : g₂.support.card = n := by
      have hsupp : g₂.support = g.support.erase j := by
        ext i; simp [g₂, Finsupp.mem_support_iff, and_comm]
      rw [hsupp, Finset.card_erase_of_mem hj, hn]; simp
    have hsign_step : monomialMulSign deg (f + g₁) g₂ = monomialMulSign deg f g₂ := by
      unfold monomialMulSign
      congr 1
      have hfilt : ((f + g₁).support ×ˢ g₂.support).filter (fun p => p.2 < p.1) =
          (f.support ×ˢ g₂.support).filter (fun p => p.2 < p.1) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finsupp.mem_support_iff,
          Finsupp.add_apply]
        constructor
        · rintro ⟨⟨hab, hb⟩, hba⟩
          have haj : j ≠ a := by
            rintro rfl
            exact (lt_asymm hba (hlt j (by simp [g₁, hgj]) b
              (Finsupp.mem_support_iff.2 hb))).elim
          have hg₁a : g₁ a = 0 := Finsupp.single_eq_of_ne haj.symm
          rw [hg₁a, add_zero] at hab
          exact ⟨⟨hab, hb⟩, hba⟩
        · rintro ⟨⟨ha, hb⟩, hba⟩
          exact ⟨⟨by omega, hb⟩, hba⟩
      rw [hfilt]
      refine Finset.sum_congr rfl fun ⟨a, b⟩ hab => ?_
      have hb : b ∈ g₂.support := (Finset.mem_product.1 (Finset.mem_filter.1 hab).1).2
      have hba : b < a := (Finset.mem_filter.1 hab).2
      have haj : j ≠ a := by
        rintro rfl
        exact (lt_asymm hba (hlt j (by simp [g₁, hgj]) b hb)).elim
      have hg₁a : g₁ a = 0 := Finsupp.single_eq_of_ne haj.symm
      rw [Finsupp.add_apply, hg₁a, add_zero]
    have hsign_mul : monomialMulSign deg f g₁ * monomialMulSign deg f g₂ =
        monomialMulSign deg f g := by
      unfold monomialMulSign
      rw [← Int.negOnePow_add]
      congr 1
      have hdisj : Disjoint ((f.support ×ˢ g₁.support).filter fun p => p.2 < p.1)
          ((f.support ×ˢ g₂.support).filter fun p => p.2 < p.1) :=
        Finset.disjoint_left.2 fun ⟨_, b⟩ h₁ h₂ =>
          (hlt b (Finset.mem_product.1 (Finset.mem_filter.1 h₁).1).2 b
            (Finset.mem_product.1 (Finset.mem_filter.1 h₂).1).2).false
      have hgsupp : g.support = g₁.support ∪ g₂.support := by
        ext k
        simp only [Finset.mem_union, g₁, g₂, Finsupp.support_single j hgj,
          Finset.mem_singleton, Finsupp.mem_support_iff, Finsupp.filter_apply]
        by_cases hkj : k = j <;> simp [hkj, hgj]
      have hunion : ((f.support ×ˢ g₁.support).filter fun p => p.2 < p.1) ∪
          ((f.support ×ˢ g₂.support).filter fun p => p.2 < p.1) =
          (f.support ×ˢ g.support).filter fun p => p.2 < p.1 := by
        ext ⟨a, b⟩
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, hgsupp]
        tauto
      rw [← hunion, Finset.sum_union hdisj]
      congr 1
      · refine Finset.sum_congr rfl fun ⟨a, b⟩ h => ?_
        have hbj : b = j := Finset.mem_singleton.1
          (Finsupp.support_single_subset (Finset.mem_product.1 (Finset.mem_filter.1 h).1).2)
        subst hbj
        have hgj_eq : g₁ j = g j := Finsupp.single_eq_same
        rw [hgj_eq]
      · refine Finset.sum_congr rfl fun ⟨a, b⟩ h => ?_
        have hjb : j ≠ b := (hlt j (by simp [g₁, hgj]) b
          (Finset.mem_product.1 (Finset.mem_filter.1 h).1).2).ne
        have hgb_eq : g₂ b = g b := by simp [g₂, hjb.symm]
        rw [hgb_eq]
    have hsign_g1 : monomialMulSign deg f (Finsupp.single j (g j)) = monomialMulSign deg f g₁ :=
      rfl
    conv_lhs => rw [hg, standardMonomial_add_of_lt u hlt]
    rw [standardMonomial_single, ← mul_assoc, standardMonomial_mul_single hcomm f j (g j),
      smul_mul_assoc, ih (f + g₁) g₂ hg₂card, smul_smul, hsign_step, hsign_g1,
      hsign_mul, add_assoc, ← hg]

/-- If an exponent vector has value at least `2` on an odd-degree generator whose square is zero,
its standard monomial vanishes. -/
theorem standardMonomial_eq_zero_of_odd_two_le {A : Type*} [Ring A] {ι : Type*} [LinearOrder ι]
    {u : ι → A} {deg : ι → ℕ} (hsq : ∀ i, Odd (deg i) → u i * u i = 0)
    {f : ι →₀ ℕ} (h : ∃ i, Odd (deg i) ∧ 2 ≤ f i) :
    standardMonomial u f = 0 := by
  obtain ⟨i, hi, h2⟩ := h
  have hmem : i ∈ f.support.sort (· ≤ ·) :=
    (Finset.mem_sort (· ≤ ·)).2 (Finsupp.mem_support_iff.2 (by omega))
  have hpow : u i ^ f i = 0 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' h2
    rw [hk, pow_add, pow_two, hsq i hi, mul_zero]
  rw [standardMonomial]
  exact List.prod_eq_zero (List.mem_map.2 ⟨i, hmem, hpow⟩)

/-- If an odd-degree generator occurs in both `f` and `g`, the product of their standard monomials
vanishes whenever odd generators square to zero. -/
theorem standardMonomial_mul_eq_zero_of_odd {A : Type*} [Ring A] {ι : Type*} [LinearOrder ι]
    {u : ι → A} {deg : ι → ℕ}
    (hcomm : ∀ i j, u i * u j = (((deg i : ℤ) * deg j)).negOnePow • (u j * u i))
    (hsq : ∀ i, Odd (deg i) → u i * u i = 0)
    {f g : ι →₀ ℕ} (h : ∃ i, Odd (deg i) ∧ f i ≠ 0 ∧ g i ≠ 0) :
    standardMonomial u f * standardMonomial u g = 0 := by
  rw [standardMonomial_mul_eq_smul hcomm f g]
  obtain ⟨i, hi, hf, hg⟩ := h
  rw [standardMonomial_eq_zero_of_odd_two_le hsq ⟨i, hi, by simp; omega⟩, smul_zero]

/-- In a ring where `2` is invertible, a Koszul-commuting family has odd-degree squares zero. -/
theorem sq_eq_zero_of_mul_comm_of_odd {R A : Type*} [CommRing R] [Invertible (2 : R)]
    [Ring A] [Algebra R A] {ι : Type*} {u : ι → A} {deg : ι → ℕ}
    (hcomm : ∀ i j, u i * u j = (((deg i : ℤ) * deg j)).negOnePow • (u j * u i))
    {i : ι} (hi : Odd (deg i)) : u i * u i = 0 := by
  have hodd : Odd ((deg i : ℤ) * deg i) :=
    ((Int.odd_natCast (deg i)).2 hi).mul ((Int.odd_natCast (deg i)).2 hi)
  have h := hcomm i i
  rw [Int.negOnePow_odd _ hodd, Units.smul_def, Units.val_neg, Units.val_one, neg_smul,
    one_smul] at h
  exact eq_zero_of_eq_neg_of_invertible_two (R := R) h

end ProductFormula

/-! ### Free graded-commutative algebras -/

section FreeGradedCommutative

variable {R : Type u} [CommRing R] {A : Type v} [Ring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A)

/-- `A` is the free graded-commutative algebra `ΛV` on the homogeneous generators `x i` of
degrees `deg i`: the generators commute up to the Koszul sign, and the standard monomials form a
basis of `A`. -/
structure IsFreeGradedCommutative {ι : Type w} [LinearOrder ι] (x : ι → A) (deg : ι → ℕ) :
    Prop where
  /-- Each generator is homogeneous of its degree. -/
  mem : ∀ i, x i ∈ 𝒜 (deg i)
  /-- The generators commute up to the Koszul sign. -/
  mul_comm : ∀ i j, x i * x j = (((deg i : ℤ) * deg j).negOnePow) • (x j * x i)
  /-- The standard monomials are linearly independent. -/
  linearIndependent : LinearIndependent R fun f : ExponentVector deg => standardMonomial x f.1
  /-- The standard monomials span. -/
  span_eq_top :
    Submodule.span R (Set.range fun f : ExponentVector deg => standardMonomial x f.1) = ⊤

namespace IsFreeGradedCommutative

variable {𝒜} {ι : Type w} [LinearOrder ι] {x : ι → A} {deg : ι → ℕ}

/-- The standard monomial basis of a free graded-commutative algebra. -/
noncomputable def basis (hx : IsFreeGradedCommutative 𝒜 x deg) :
    Module.Basis (ExponentVector deg) R A :=
  Module.Basis.mk hx.linearIndependent hx.span_eq_top.ge

@[simp]
theorem basis_apply (hx : IsFreeGradedCommutative 𝒜 x deg) (f : ExponentVector deg) :
    hx.basis f = standardMonomial x f.1 := by
  simp [basis]

/-- Every standard monomial lies in the homogeneous piece of its total degree. -/
theorem standardMonomial_mem [SetLike.GradedMonoid 𝒜] (hx : IsFreeGradedCommutative 𝒜 x deg)
    (f : ι →₀ ℕ) : standardMonomial x f ∈ 𝒜 (monomialDegree deg f : ℤ) :=
  standardMonomial_mem_graded hx.mem f

/-- When `2` is invertible, every generator of odd degree squares to zero. -/
theorem sq_eq_zero_of_odd [Invertible (2 : R)] (hx : IsFreeGradedCommutative 𝒜 x deg)
    {i : ι} (hi : Odd (deg i)) : x i * x i = 0 :=
  sq_eq_zero_of_mul_comm_of_odd (R := R) hx.mul_comm hi

/-- The product of two standard monomials in a free graded-commutative algebra is `0` when an
odd-degree generator occurs in both (assuming `2` is invertible). -/
theorem standardMonomial_mul_eq_zero_of_odd [Invertible (2 : R)]
    (hx : IsFreeGradedCommutative 𝒜 x deg) {f g : ι →₀ ℕ}
    (h : ∃ i, Odd (deg i) ∧ f i ≠ 0 ∧ g i ≠ 0) :
    standardMonomial x f * standardMonomial x g = 0 :=
  TauCeti.standardMonomial_mul_eq_zero_of_odd hx.mul_comm (fun _ => hx.sq_eq_zero_of_odd) h

/-- The degree-`p` piece of a free graded-commutative algebra is spanned by the standard
monomials of degree `p`. -/
theorem grade_eq_span_standardMonomial [GradedAlgebra 𝒜] (hx : IsFreeGradedCommutative 𝒜 x deg)
    (p : ℤ) :
    𝒜 p = Submodule.span R {a | ∃ f : ExponentVector deg,
      (monomialDegree deg f.1 : ℤ) = p ∧ standardMonomial x f.1 = a} := by
  apply le_antisymm
  · intro a ha
    have hmem : a ∈ Submodule.span R (Set.range fun f : ExponentVector deg =>
        standardMonomial x f.1) := hx.span_eq_top ▸ Submodule.mem_top
    have hproj : (DirectSum.decompose 𝒜 a p : A) ∈
        Submodule.span R {a | ∃ f : ExponentVector deg,
          (monomialDegree deg f.1 : ℤ) = p ∧ standardMonomial x f.1 = a} := by
      clear ha
      induction hmem using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨f, rfl⟩ := hb
        by_cases hp : (monomialDegree deg f.1 : ℤ) = p
        · rw [DirectSum.decompose_of_mem_same 𝒜 (hp ▸ hx.standardMonomial_mem f.1)]
          exact Submodule.subset_span ⟨f, hp, rfl⟩
        · rw [DirectSum.decompose_of_mem_ne 𝒜 (hx.standardMonomial_mem f.1) hp]
          exact zero_mem _
      | zero => simp
      | add b c _ _ hb hc =>
        simpa only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add] using
          add_mem hb hc
      | smul r b _ hb =>
        simpa only [DirectSum.decompose_smul, DirectSum.smul_apply, SetLike.val_smul] using
          Submodule.smul_mem _ r hb
    simpa only [DirectSum.decompose_of_mem_same 𝒜 ha] using hproj
  · rw [Submodule.span_le]
    rintro _ ⟨f, rfl, rfl⟩
    exact hx.standardMonomial_mem f.1

/-- A free graded-commutative algebra on generators of natural-number degrees vanishes in negative
degrees. -/
theorem grade_eq_bot_of_neg [GradedAlgebra 𝒜] (hx : IsFreeGradedCommutative 𝒜 x deg)
    {p : ℤ} (hp : p < 0) : 𝒜 p = ⊥ := by
  rw [hx.grade_eq_span_standardMonomial p, Submodule.span_eq_bot]
  rintro _ ⟨f, hf, _⟩
  omega

/-- When every generator has positive degree, the degree-zero piece consists of scalars alone. -/
theorem grade_zero_eq_one_of_pos [GradedAlgebra 𝒜] (hx : IsFreeGradedCommutative 𝒜 x deg)
    (hpos : ∀ i, 0 < deg i) : 𝒜 0 = 1 := by
  apply le_antisymm
  · rw [hx.grade_eq_span_standardMonomial 0, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hf0 : f.1 = 0 := (monomialDegree_eq_zero_iff hpos).1 (Int.ofNat_eq_zero.1 hf)
    rw [hf0, standardMonomial_zero]
    exact Submodule.one_le.1 le_rfl
  · rw [Submodule.one_le]
    exact SetLike.one_mem_graded 𝒜

/-- **Graded commutativity**: in a free graded-commutative algebra, any two homogeneous elements
commute up to the Koszul sign. -/
theorem mul_comm_graded [GradedAlgebra 𝒜] (hx : IsFreeGradedCommutative 𝒜 x deg)
    {p q : ℤ} {a b : A} (ha : a ∈ 𝒜 p) (hb : b ∈ 𝒜 q) :
    a * b = (p * q).negOnePow • (b * a) := by
  have hmul_left : ∀ {p₁ p₂ q₁ : ℤ} {a₁ a₂ b₁ : A},
      a₁ * b₁ = (p₁ * q₁).negOnePow • (b₁ * a₁) →
      a₂ * b₁ = (p₂ * q₁).negOnePow • (b₁ * a₂) →
      (a₁ * a₂) * b₁ = ((p₁ + p₂) * q₁).negOnePow • (b₁ * (a₁ * a₂)) := by
    intro p₁ p₂ q₁ a₁ a₂ b₁ h₁ h₂
    rw [mul_assoc, h₂, mul_smul_comm, ← mul_assoc, h₁, smul_mul_assoc, mul_assoc,
      smul_smul, ← Int.negOnePow_add, add_mul, add_comm]
  have hgen : ∀ (f g : ι →₀ ℕ),
      standardMonomial x f * standardMonomial x g =
        ((monomialDegree deg f : ℤ) * monomialDegree deg g).negOnePow •
          (standardMonomial x g * standardMonomial x f) := by
    intro f g
    have hpow_g : ∀ (i : ι) (m : ℕ),
        x i ^ m * standardMonomial x g =
          (((m * deg i : ℕ) : ℤ) * monomialDegree deg g).negOnePow •
            (standardMonomial x g * x i ^ m) := by
      intro i m
      have h := standardMonomial_mul_pow hx.mul_comm g i m
      have hdeg : (g.support.sum fun j => ((g j * deg j : ℕ) * (m * deg i : ℕ) : ℤ)) =
          ((m * deg i : ℕ) : ℤ) * monomialDegree deg g := by
        rw [monomialDegree, Finsupp.sum, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast; ring
      rw [hdeg] at h
      have hinv := congrArg (((((m * deg i : ℕ) : ℤ) * monomialDegree deg g).negOnePow) • ·) h
      simpa [smul_smul, ← Int.negOnePow_add] using hinv.symm
    have hlist : ∀ l : List ι,
        (l.map fun i => x i ^ f i).prod * standardMonomial x g =
          ((l.map fun i => (f i * deg i : ℤ)).sum * monomialDegree deg g).negOnePow •
            (standardMonomial x g * (l.map fun i => x i ^ f i).prod) := by
      intro l
      induction l with
      | nil => simp
      | cons i l ih =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        exact hmul_left (by simpa [Nat.cast_mul] using hpow_g i (f i)) ih
    rw [standardMonomial_def, ← sum_sort_support_degree deg f]
    exact hlist _
  rw [hx.grade_eq_span_standardMonomial p] at ha
  rw [hx.grade_eq_span_standardMonomial q] at hb
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨f, rfl, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb => obtain ⟨g, rfl, rfl⟩ := hb; exact hgen f.1 g.1
    | zero => simp
    | add b₁ b₂ _ _ hb₁ hb₂ => rw [mul_add, add_mul, smul_add, hb₁, hb₂]
    | smul r b _ hb' => rw [mul_smul_comm, smul_mul_assoc, smul_comm, hb']
  | zero => simp
  | add a₁ a₂ _ _ ha₁ ha₂ => rw [add_mul, mul_add, smul_add, ha₁, ha₂]
  | smul r a _ ha' => rw [smul_mul_assoc, mul_smul_comm, smul_comm, ha']

/-- The generators of a free graded-commutative algebra generate it as an `R`-algebra. -/
theorem adjoin_range_eq_top (hx : IsFreeGradedCommutative 𝒜 x deg) :
    Algebra.adjoin R (Set.range x) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  have hmem : a ∈ Submodule.span R (Set.range fun f : ExponentVector deg =>
      standardMonomial x f.1) := hx.span_eq_top ▸ Submodule.mem_top
  refine Submodule.span_induction (p := fun b _ => b ∈ Algebra.adjoin R (Set.range x))
    ?_ (zero_mem _) (fun _ _ _ _ => add_mem) (fun r _ _ hb => Subalgebra.smul_mem _ hb r) hmem
  rintro _ ⟨f, rfl⟩
  dsimp only
  rw [standardMonomial_def]
  exact list_prod_mem fun y hy => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hy
    exact pow_mem (Algebra.subset_adjoin (Set.mem_range_self i)) _

/-- **Extensionality**: two algebra maps out of a free graded-commutative algebra are equal as
soon as they agree on every generator. -/
theorem algHom_ext {B : Type*} [Semiring B] [Algebra R B]
    (hx : IsFreeGradedCommutative 𝒜 x deg) {f g : A →ₐ[R] B}
    (h : ∀ i, f (x i) = g (x i)) : f = g := by
  have hlin : f.toLinearMap = g.toLinearMap :=
    hx.basis.ext fun f₀ => by
      simp only [AlgHom.toLinearMap_apply, basis_apply, map_standardMonomial]
      have hcomp : f ∘ x = g ∘ x := funext h
      rw [hcomp]
  exact AlgHom.ext fun a => LinearMap.congr_fun hlin a

/-- An algebra map out of a free graded-commutative algebra sending each generator into its degree
preserves the entire grading. -/
def gradedAlgHomOfAlgHom [GradedAlgebra 𝒜] (hx : IsFreeGradedCommutative 𝒜 x deg)
    {B : Type*} [Semiring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (φ : A →ₐ[R] B) (hφ : ∀ i, φ (x i) ∈ ℬ (deg i)) : 𝒜 →ₐᵍ[R] ℬ where
  toAlgHom := φ
  map_mem {p a} ha := by
    rw [hx.grade_eq_span_standardMonomial p] at ha
    refine Submodule.span_induction (p := fun b _ => φ b ∈ ℬ p) ?_
      (by rw [map_zero]; exact zero_mem (ℬ p))
      (fun _ _ _ _ hb hc => by rw [map_add]; exact add_mem hb hc)
      (fun r _ _ hb => by rw [map_smul]; exact Submodule.smul_mem (ℬ p) r hb) ha
    rintro _ ⟨f, rfl, rfl⟩
    rw [map_standardMonomial]
    exact standardMonomial_mem_graded hφ f.1

@[simp]
theorem gradedAlgHomOfAlgHom_apply [GradedAlgebra 𝒜] (hx : IsFreeGradedCommutative 𝒜 x deg)
    {B : Type*} [Semiring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (φ : A →ₐ[R] B) (hφ : ∀ i, φ (x i) ∈ ℬ (deg i)) (a : A) :
    hx.gradedAlgHomOfAlgHom φ hφ a = φ a := (rfl)

/-! ### Universal property -/

/-- **Universal property (construction)**: when `2` is invertible, any family `b : ι → B`
satisfying the Koszul commutation relations extends to an algebra homomorphism `A →ₐ[R] B`. -/
noncomputable def lift [Invertible (2 : R)] (hx : IsFreeGradedCommutative 𝒜 x deg)
    {B : Type*} [Ring B] [Algebra R B] (b : ι → B)
    (hb : ∀ i j, b i * b j = (((deg i : ℤ) * deg j).negOnePow) • (b j * b i)) :
    A →ₐ[R] B := by
  let φ : A →ₗ[R] B := hx.basis.constr R fun f : ExponentVector deg => standardMonomial b f.1
  have h1 : φ 1 = 1 := by
    have h0 : (1 : A) = hx.basis 0 := by simp
    rw [h0, Module.Basis.constr_basis]; simp
  have hmul_basis : ∀ f g : ExponentVector deg,
      φ (hx.basis f * hx.basis g) = φ (hx.basis f) * φ (hx.basis g) := by
    intro f g
    by_cases hodd : ∃ i, Odd (deg i) ∧ f.1 i ≠ 0 ∧ g.1 i ≠ 0
    · rw [basis_apply, basis_apply, hx.standardMonomial_mul_eq_zero_of_odd hodd, map_zero,
        ← hx.basis_apply f, ← hx.basis_apply g, Module.Basis.constr_basis,
        Module.Basis.constr_basis, TauCeti.standardMonomial_mul_eq_zero_of_odd hb
          (fun _ => sq_eq_zero_of_mul_comm_of_odd (R := R) hb) hodd]
    · push Not at hodd
      let fg : ExponentVector deg := ⟨f.1 + g.1, fun i hi => by
        have hf := f.2 i hi
        have hg := g.2 i hi
        by_cases hfi : f.1 i = 0
        · simp [hfi, hg]
        · simp [hodd i hi hfi, hf]⟩
      have hmulA : hx.basis f * hx.basis g =
          monomialMulSign deg f.1 g.1 • hx.basis fg := by
        simpa [basis_apply, fg] using standardMonomial_mul_eq_smul hx.mul_comm f.1 g.1
      rw [hmulA, Units.smul_def, map_zsmul, Module.Basis.constr_basis, Module.Basis.constr_basis,
        Module.Basis.constr_basis, ← Units.smul_def]
      exact (standardMonomial_mul_eq_smul hb f.1 g.1).symm
  have hmul_left : ∀ (f : ExponentVector deg) (a₂ : A),
      φ (hx.basis f * a₂) = φ (hx.basis f) * φ a₂ := by
    intro f a₂
    have hlin : φ ∘ₗ LinearMap.mulLeft R (hx.basis f) =
        LinearMap.mulLeft R (φ (hx.basis f)) ∘ₗ φ :=
      hx.basis.ext fun g => by simpa using hmul_basis f g
    simpa using LinearMap.congr_fun hlin a₂
  have hmul : ∀ a₁ a₂ : A, φ (a₁ * a₂) = φ a₁ * φ a₂ := by
    intro a₁ a₂
    have hlin : φ ∘ₗ LinearMap.mulRight R a₂ = LinearMap.mulRight R (φ a₂) ∘ₗ φ :=
      hx.basis.ext fun f => by simpa using hmul_left f a₂
    simpa using LinearMap.congr_fun hlin a₁
  exact AlgHom.ofLinearMap φ h1 hmul

@[simp]
theorem lift_apply [Invertible (2 : R)] (hx : IsFreeGradedCommutative 𝒜 x deg)
    {B : Type*} [Ring B] [Algebra R B] (b : ι → B)
    (hb : ∀ i j, b i * b j = (((deg i : ℤ) * deg j).negOnePow) • (b j * b i)) (i : ι) :
    hx.lift b hb (x i) = b i := by
  have hxi : x i = hx.basis (ExponentVector.single i) := by simp
  -- Unfold `lift` to expose its underlying `Module.Basis.constr` linear map.
  change (hx.basis.constr R fun f : ExponentVector deg => standardMonomial b f.1) (x i) = b i
  rw [hxi, Module.Basis.constr_basis]; simp

/-- Uniqueness of the algebra extension in the universal property. -/
theorem lift_unique [Invertible (2 : R)] (hx : IsFreeGradedCommutative 𝒜 x deg)
    {B : Type*} [Ring B] [Algebra R B] (b : ι → B)
    (hb : ∀ i j, b i * b j = (((deg i : ℤ) * deg j).negOnePow) • (b j * b i))
    {φ : A →ₐ[R] B} (hφ : ∀ i, φ (x i) = b i) :
    φ = hx.lift b hb :=
  hx.algHom_ext fun i => by rw [hφ i, hx.lift_apply]

/-- The graded universal-property extension into an internally graded algebra. -/
noncomputable def gradedLift [GradedAlgebra 𝒜] [Invertible (2 : R)]
    (hx : IsFreeGradedCommutative 𝒜 x deg) {B : Type*} [Ring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (hB : ∀ {p q : ℤ} {a b : B}, a ∈ ℬ p → b ∈ ℬ q → a * b = (p * q).negOnePow • (b * a))
    (b : ι → B) (hb : ∀ i, b i ∈ ℬ (deg i)) : 𝒜 →ₐᵍ[R] ℬ :=
  hx.gradedAlgHomOfAlgHom (hx.lift b fun i j => hB (hb i) (hb j)) fun i => by
    rw [hx.lift_apply]; exact hb i

@[simp]
theorem gradedLift_apply [GradedAlgebra 𝒜] [Invertible (2 : R)]
    (hx : IsFreeGradedCommutative 𝒜 x deg) {B : Type*} [Ring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (hB : ∀ {p q : ℤ} {a b : B}, a ∈ ℬ p → b ∈ ℬ q → a * b = (p * q).negOnePow • (b * a))
    (b : ι → B) (hb : ∀ i, b i ∈ ℬ (deg i)) (i : ι) :
    hx.gradedLift hB b hb (x i) = b i :=
  hx.lift_apply b (fun i j => hB (hb i) (hb j)) i

/-- **Universal property of `ΛV`**: when `2` is invertible in `R` (in particular over any field
of characteristic zero), for every graded-commutative `(B, ℬ)` and `b : ι → B` with
`b i ∈ ℬ (deg i)` there is a unique algebra map `φ : A →ₐ[R] B` with `φ (x i) = b i`. -/
theorem existsUnique_algHom [Invertible (2 : R)]
    (hx : IsFreeGradedCommutative 𝒜 x deg) {B : Type*} [Ring B] [Algebra R B]
    (ℬ : ℤ → Submodule R B)
    (hB : ∀ {p q : ℤ} {a b : B}, a ∈ ℬ p → b ∈ ℬ q → a * b = (p * q).negOnePow • (b * a))
    (b : ι → B) (hb : ∀ i, b i ∈ ℬ (deg i)) :
    ∃! φ : A →ₐ[R] B, ∀ i, φ (x i) = b i :=
  ⟨hx.lift b fun i j => hB (hb i) (hb j),
    fun i => hx.lift_apply b _ i,
    fun _ hφ => hx.lift_unique _ _ hφ⟩

/-! ### Morphisms of differential graded algebras out of `ΛV` -/

/-- Two morphisms of differential graded algebras out of a free graded-commutative DG algebra
agree as soon as they agree on every generator. -/
theorem dgAlgHom_ext [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 d}
    (hx : IsFreeGradedCommutative 𝒜 x deg) {B : Type*} [Ring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
    {f g : DGAlgHom hA hB} (h : ∀ i, f (x i) = g (x i)) : f = g := by
  have halg : f.toGradedAlgHom.toAlgHom = g.toGradedAlgHom.toAlgHom := hx.algHom_ext h
  exact DGAlgHom.ext fun a => AlgHom.congr_fun halg a

/-- Promote an algebra homomorphism `φ : A →ₐ[R] B` out of a free graded-commutative DG algebra
to a DG algebra morphism, given that `φ` preserves generator degrees and commutes with the
differentials on generators. -/
def dgAlgHomOfAlgHom [GradedAlgebra 𝒜] {d : A →ₗ[R] A} (hA : IsDGAlgebra 𝒜 d)
    (hx : IsFreeGradedCommutative 𝒜 x deg) {B : Type*} [Ring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)
    (φ : A →ₐ[R] B) (hφ : ∀ i, φ (x i) ∈ ℬ (deg i))
    (hd : ∀ i, dB (φ (x i)) = φ (d (x i))) : DGAlgHom hA hB where
  toGradedAlgHom := hx.gradedAlgHomOfAlgHom φ hφ
  map_d' a := by
    let φg : 𝒜 →ₐᵍ[R] ℬ := hx.gradedAlgHomOfAlgHom φ hφ
    let D : A →ₗ[R] B := dB ∘ₗ φ.toLinearMap - φ.toLinearMap ∘ₗ d
    have hD_leibniz : ∀ {p : ℤ} {u : A}, u ∈ 𝒜 p → ∀ v : A,
        D (u * v) = D u * φ v + p.negOnePow • (φ u * D v) := by
      intro p u hu v
      have hφu : φ u ∈ ℬ p := φg.map_mem hu
      simp only [D, LinearMap.sub_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
        hB.leibniz hφu (φ v), hA.leibniz hu v, map_add, Units.smul_def, map_zsmul, sub_mul,
        mul_sub, zsmul_sub]
      abel
    have hD_one : D 1 = 0 := by simp [D, hA.map_one_eq_zero, hB.map_one_eq_zero]
    have hD_pow : ∀ (i : ι) (n : ℕ), D (x i ^ n) = 0 := by
      intro i n
      induction n with
      | zero => simpa using hD_one
      | succ n ih =>
        have hDi : D (x i) = 0 := sub_eq_zero.2 (hd i)
        rw [pow_succ', hD_leibniz (hx.mem i), ih, mul_zero, smul_zero, add_zero, hDi, zero_mul]
    have hD_mon : ∀ f : ι →₀ ℕ, D (standardMonomial x f) = 0 := by
      intro f
      have hlist : ∀ l : List ι, D ((l.map fun i => x i ^ f i).prod) = 0 := by
        intro l
        induction l with
        | nil => simpa using hD_one
        | cons i l ih =>
          simp only [List.map_cons, List.prod_cons]
          have hpow : x i ^ f i ∈ 𝒜 ((f i * deg i : ℕ) : ℤ) := by
            simpa [Nat.cast_mul] using SetLike.pow_mem_graded (f i) (hx.mem i)
          rw [hD_leibniz hpow, hD_pow i (f i), ih, zero_mul, mul_zero, smul_zero, add_zero]
      exact hlist _
    have hD_zero : D = 0 := hx.basis.ext fun f => by simp [hD_mon f.1]
    exact sub_eq_zero.1 (LinearMap.congr_fun hD_zero a)

@[simp]
theorem dgAlgHomOfAlgHom_apply [GradedAlgebra 𝒜] {d : A →ₗ[R] A} (hA : IsDGAlgebra 𝒜 d)
    (hx : IsFreeGradedCommutative 𝒜 x deg) {B : Type*} [Ring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)
    (φ : A →ₐ[R] B) (hφ : ∀ i, φ (x i) ∈ ℬ (deg i))
    (hd : ∀ i, dB (φ (x i)) = φ (d (x i))) (a : A) :
    hx.dgAlgHomOfAlgHom hA hB φ hφ hd a = φ a := (rfl)

/-- An algebra map out of a free graded-commutative DG algebra sending each generator to an
element of its degree lifts to a morphism of DG algebras if and only if it commutes with the
differentials on the generators. -/
theorem exists_dgAlgHom_iff [GradedAlgebra 𝒜] {d : A →ₗ[R] A} (hA : IsDGAlgebra 𝒜 d)
    (hx : IsFreeGradedCommutative 𝒜 x deg) {B : Type*} [Ring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)
    (φ : A →ₐ[R] B) (hφ : ∀ i, φ (x i) ∈ ℬ (deg i)) :
    (∃ f : DGAlgHom hA hB, ∀ a, f a = φ a) ↔ ∀ i, dB (φ (x i)) = φ (d (x i)) :=
  ⟨fun ⟨f, hf⟩ i => by rw [← hf (x i), ← hf (d (x i)), f.map_d],
   fun hd => ⟨hx.dgAlgHomOfAlgHom hA hB φ hφ hd, fun _ => rfl⟩⟩

/-- **Universal property for DG algebra morphisms**: when `2` is invertible, a family `b : ι → B`
of elements in degrees `deg i` in a graded-commutative DG algebra `(B, ℬ, dB)` extends to a
unique DG algebra morphism `A → B` as soon as `dB (b i) = φ (d (x i))` for the underlying algebra
extension `φ`. -/
noncomputable def dgLift [GradedAlgebra 𝒜] [Invertible (2 : R)] {d : A →ₗ[R] A}
    (hA : IsDGAlgebra 𝒜 d) (hx : IsFreeGradedCommutative 𝒜 x deg)
    {B : Type*} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)
    (hBc : ∀ {p q : ℤ} {a b : B}, a ∈ ℬ p → b ∈ ℬ q → a * b = (p * q).negOnePow • (b * a))
    (b : ι → B) (hb : ∀ i, b i ∈ ℬ (deg i))
    (hd : ∀ i, dB (b i) = hx.lift b (fun j k => hBc (hb j) (hb k)) (d (x i))) :
    DGAlgHom hA hB :=
  hx.dgAlgHomOfAlgHom hA hB (hx.lift b fun j k => hBc (hb j) (hb k))
    (fun i => by rw [hx.lift_apply]; exact hb i)
    (fun i => by rw [hx.lift_apply]; exact hd i)

@[simp]
theorem dgLift_apply [GradedAlgebra 𝒜] [Invertible (2 : R)] {d : A →ₗ[R] A}
    (hA : IsDGAlgebra 𝒜 d) (hx : IsFreeGradedCommutative 𝒜 x deg)
    {B : Type*} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)
    (hBc : ∀ {p q : ℤ} {a b : B}, a ∈ ℬ p → b ∈ ℬ q → a * b = (p * q).negOnePow • (b * a))
    (b : ι → B) (hb : ∀ i, b i ∈ ℬ (deg i))
    (hd : ∀ i, dB (b i) = hx.lift b (fun j k => hBc (hb j) (hb k)) (d (x i))) (i : ι) :
    hx.dgLift hA hB hBc b hb hd (x i) = b i :=
  hx.lift_apply b (fun j k => hBc (hb j) (hb k)) i

end IsFreeGradedCommutative

end FreeGradedCommutative

end TauCeti
