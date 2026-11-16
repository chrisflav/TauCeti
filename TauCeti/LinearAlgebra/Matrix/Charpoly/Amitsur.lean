/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
-- Non-public: `Function.IsPeriodicPt` and `Function.minimalPeriod` classify periodic words.
import Mathlib.Dynamics.PeriodicPts.Defs
-- Non-public: universal matrices over `MvPolynomial _ ℤ` transfer the `ℚ`-algebra identity to
-- arbitrary commutative rings.
import Mathlib.RingTheory.MvPolynomial.Basic
-- Non-public: `Fin.coe_finRotate_pow` computes iterated cyclic shifts on `Fin k`.
import TauCeti.Data.Fin.Basic
-- Non-public: `List.ofFn_comp_finRotate_pow` and `List.IsRotated.apply_prod_eq` give cyclic
-- invariance of `charpolyRev` of word products.
import TauCeti.Data.List.Rotate
-- Non-public: `Matrix.logOf_charpolyRev` and `Matrix.trace_pow_eq_of_charpolyRev_eq` drive the
-- formal power series logarithm computation over `ℚ`-algebras.
import TauCeti.LinearAlgebra.Matrix.Charpoly.Zeta

/-!
# Amitsur's theorem for characteristic polynomials of sums

For a finite family of square matrices `A i` over an arbitrary commutative ring `R`, the reversed
characteristic polynomial `det (1 - X ∑ i, A i)` is determined by the reversed characteristic
polynomials of the nonempty word products `A i₁ ⋯ A iₖ` of length `k` at most the matrix size.
In particular, if two families of matrices (or endomorphisms of finite free modules of the same
rank) have the same characteristic polynomials on all nonempty word products up to the rank, then
their sums have the same characteristic polynomial
(`Matrix.charpoly_sum_eq_of_forall_list_prod`, `LinearMap.charpoly_sum_eq_of_forall_list_prod`).

The proof establishes the truncated Witt–Amitsur necklace factorization: for every `d` and every
`r ≤ d`, the degree-`r` coefficient of `det (1 - X ∑ i, A i)` agrees with that of the product

`∏ k ∈ Icc 1 d, ∏ c, det (1 - X ^ k * A_c)`

taken over the primitive cyclic words (necklaces) `c` of length `k ≤ d`. Over a `ℚ`-algebra this
follows by taking the formal power series logarithm (`Matrix.logOf_charpolyRev`): expanding
`tr ((∑ i, A i) ^ m)` as a sum over all words of length `m` and grouping each word by its minimal
rotational period `k ∣ m` matches the logarithmic coefficients through degree `d`, and formal
exponentiation modulo `X ^ (d + 1)` recovers the polynomial coefficients. Specializing from the
universal matrices over `ℤ[X_{i,p,q}]` (which embed into `ℚ[X_{i,p,q}]`) transfers the identity
to every commutative ring in every characteristic.

## Main results

* `Matrix.coeff_charpolyRev_sum_eq_of_forall_list_prod`: through degree `d`, the coefficients of
  `det (1 - X ∑ i ∈ s, A i)` are determined by `det (1 - X A_w)` on nonempty words `w` in `s` of
  length at most `d`.
* `Matrix.charpolyRev_sum_eq_of_forall_list_prod`: `det (1 - X ∑ i ∈ s, A i)` is determined by
  `det (1 - X A_w)` on nonempty words of length at most the larger matrix size.
* `Matrix.charpoly_sum_eq_of_forall_list_prod`: for matrices of the same size, the characteristic
  polynomial of `∑ i ∈ s, A i` is determined by the characteristic polynomials of nonempty word
  products of length at most the matrix size.
* `LinearMap.charpoly_sum_eq_of_forall_list_prod`: the basis-free form for endomorphisms of finite
  free modules of equal rank.

## References

* S. A. Amitsur, *On the characteristic polynomial of a sum of matrices*, Linear and Multilinear
  Algebra **8** (1980), 177–182.
* C. Reutenauer and M.-P. Schützenberger, *A formula for the determinant of a sum of matrices*,
  Lett. Math. Phys. **13** (1987), 299–302.
* G. Chenevier, *The `p`-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, in *Automorphic Forms and Galois Representations*,
  Vol. 1, London Math. Soc. Lecture Note Ser. **414**, Cambridge Univ. Press (2014), §1.13–1.14.
-/

public section

open Finset Polynomial

namespace Matrix

/-! ### Primitive words and cyclic rotations -/

section Necklaces

/-- Cyclic left rotation of a length-`k` word `Fin k → ι`. -/
private def wordRot {ι : Type*} (k : ℕ) (w : Fin k → ι) : Fin k → ι :=
  w ∘ finRotate k

private theorem wordRot_iterate {ι : Type*} (k : ℕ) (r : ℕ) (w : Fin k → ι) :
    (wordRot k)^[r] w = w ∘ ⇑(finRotate k ^ r) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, wordRot, pow_succ]
    rfl

private theorem wordRot_iterate_apply {ι : Type*} {k : ℕ} (r : ℕ) (w : Fin k → ι)
    (i : Fin k) :
    ((wordRot k)^[r] w) i = w ⟨(i.1 + r) % k, Nat.mod_lt _ i.pos⟩ := by
  rw [wordRot_iterate, Function.comp_apply]
  congr 1
  exact Fin.ext (Fin.coe_finRotate_pow r i)

private theorem isPeriodicPt_wordRot_self {ι : Type*} (k : ℕ) (w : Fin k → ι) :
    Function.IsPeriodicPt (wordRot k) k w := by
  funext i
  rw [wordRot_iterate_apply]
  congr 1
  exact Fin.ext (by simp [Nat.mod_eq_of_lt i.2])

private theorem minimalPeriod_wordRot_dvd {ι : Type*} (k : ℕ) (w : Fin k → ι) :
    Function.minimalPeriod (wordRot k) w ∣ k :=
  (isPeriodicPt_wordRot_self k w).minimalPeriod_dvd

private theorem minimalPeriod_wordRot_pos {ι : Type*} {k : ℕ} (hk : 0 < k) (w : Fin k → ι) :
    0 < Function.minimalPeriod (wordRot k) w :=
  Nat.pos_of_dvd_of_pos (minimalPeriod_wordRot_dvd k w) hk

/-- Periodic extension of a length-`k` word to length `n`. -/
private def repeatWord {ι : Type*} {k n : ℕ} (hk : 0 < k) (u : Fin k → ι) : Fin n → ι :=
  fun i ↦ u ⟨i.1 % k, Nat.mod_lt _ hk⟩

private theorem wordRot_iterate_repeatWord {ι : Type*} {k n : ℕ} (hk : 0 < k) (hkn : k ∣ n)
    (r : ℕ) (u : Fin k → ι) :
    (wordRot n)^[r] (repeatWord hk u) = repeatWord hk ((wordRot k)^[r] u) := by
  funext i
  simp only [wordRot_iterate_apply, repeatWord]
  congr 1
  exact Fin.ext (by dsimp only; rw [Nat.mod_mod_of_dvd _ hkn, Nat.mod_add_mod])

private theorem repeatWord_injective {ι : Type*} {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    Function.Injective (repeatWord (ι := ι) (n := n) hk) := fun u v h ↦ funext fun j ↦ by
  have hj := congrFun h ⟨j.1, j.2.trans_le hkn⟩
  simpa [repeatWord, Nat.mod_eq_of_lt j.2] using hj

private theorem minimalPeriod_wordRot_repeatWord {ι : Type*} {k n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ∣ n) (u : Fin k → ι) :
    Function.minimalPeriod (wordRot n) (repeatWord hk u) =
      Function.minimalPeriod (wordRot k) u := by
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro r
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, wordRot_iterate_repeatWord hk hkn,
    (repeatWord_injective hk (Nat.le_of_dvd hn hkn)).eq_iff]

private theorem eq_repeatWord_of_isPeriodicPt {ι : Type*} {k n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ∣ n) {w : Fin n → ι} (hper : Function.IsPeriodicPt (wordRot n) k w) :
    w = repeatWord hk (fun j : Fin k ↦ w ⟨j.1, j.2.trans_le (Nat.le_of_dvd hn hkn)⟩) := by
  funext i
  have hmul : (wordRot n)^[k * (i.1 / k)] w = w := (hper.mul_const (i.1 / k)).eq
  have hi := congrFun hmul ⟨i.1 % k, (Nat.mod_lt _ hk).trans_le (Nat.le_of_dvd hn hkn)⟩
  rw [wordRot_iterate_apply] at hi
  have heq : (i.1 % k + k * (i.1 / k)) % n = i.1 := by
    rw [add_comm, Nat.div_add_mod, Nat.mod_eq_of_lt i.2]
  simpa [repeatWord, heq] using hi

/-- Primitive words of length `k`: words whose minimal rotational period is `k`. -/
private abbrev PrimWord (ι : Type*) (k : ℕ) :=
  {u : Fin k → ι // Function.minimalPeriod (wordRot k) u = k}

private theorem primWord_heq {ι : Type*} {k₁ k₂ : ℕ} (hk : k₁ = k₂)
    {u₁ : PrimWord ι k₁} {u₂ : PrimWord ι k₂}
    (h : ∀ j : Fin k₁, u₁.1 j = u₂.1 (j.cast hk)) : HEq u₁ u₂ := by
  subst hk
  exact heq_of_eq (Subtype.ext (funext h))

/-- Every word of positive length `n` is uniquely a periodic repetition of a primitive word of
length `k ∣ n`. -/
private noncomputable def wordEquivSigmaPrimWord {ι : Type*} {n : ℕ} (hn : 0 < n) :
    (Fin n → ι) ≃ Σ k : n.divisors, PrimWord ι k.1 where
  toFun w :=
    let hk_dvd := minimalPeriod_wordRot_dvd n w
    let hk_pos := minimalPeriod_wordRot_pos hn w
    let u : Fin (Function.minimalPeriod (wordRot n) w) → ι :=
      fun j ↦ w ⟨j.1, j.2.trans_le (Nat.le_of_dvd hn hk_dvd)⟩
    have hw : w = repeatWord hk_pos u :=
      eq_repeatWord_of_isPeriodicPt hn hk_pos hk_dvd (Function.isPeriodicPt_minimalPeriod _ _)
    ⟨⟨_, Nat.mem_divisors.mpr ⟨hk_dvd, hn.ne'⟩⟩,
      ⟨u, by rw [← minimalPeriod_wordRot_repeatWord hn hk_pos hk_dvd u, ← hw]⟩⟩
  invFun p := repeatWord (Nat.pos_of_mem_divisors p.1.2) p.2.1
  left_inv w := by
    dsimp only
    exact (eq_repeatWord_of_isPeriodicPt hn (minimalPeriod_wordRot_pos hn w)
      (minimalPeriod_wordRot_dvd n w) (Function.isPeriodicPt_minimalPeriod _ _)).symm
  right_inv := by
    rintro ⟨⟨k, hk⟩, ⟨u, hu⟩⟩
    have hk_dvd : k ∣ n := (Nat.mem_divisors.mp hk).1
    have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
    have hmp : Function.minimalPeriod (wordRot n) (repeatWord hk_pos u) = k := by
      rw [minimalPeriod_wordRot_repeatWord hn hk_pos hk_dvd, hu]
    refine Sigma.ext (Subtype.ext hmp) (primWord_heq hmp fun j ↦ ?_)
    have hj : j.1 < k := by have := j.2; omega
    simp only [repeatWord]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt hj)

/-- Rotational equivalence on primitive words of length `k`. -/
private def primWordSetoid (ι : Type*) (k : ℕ) (hk : 0 < k) : Setoid (PrimWord ι k) where
  r u v := ∃ r : ℕ, (wordRot k)^[r] u.1 = v.1
  iseqv :=
    { refl := fun _ ↦ ⟨0, rfl⟩
      symm := fun {u v} ⟨r, hr⟩ ↦ by
        refine ⟨k - r % k, ?_⟩
        have hmod : (wordRot k)^[r % k] u.1 = (wordRot k)^[r] u.1 := by
          simpa [u.2] using
            Function.iterate_mod_minimalPeriod_eq (f := wordRot k) (x := u.1) (n := r)
        rw [← hr, ← hmod, ← Function.iterate_add_apply,
          Nat.sub_add_cancel (Nat.mod_lt r hk).le]
        exact (isPeriodicPt_wordRot_self k u.1).eq
      trans := fun ⟨r₁, h₁⟩ ⟨r₂, h₂⟩ ↦
        ⟨r₂ + r₁, by rw [Function.iterate_add_apply, h₁, h₂]⟩ }

/-- Primitive necklaces of length `k`: rotational equivalence classes of primitive words. -/
private abbrev PrimNecklace (ι : Type*) (k : ℕ) (hk : 0 < k) :=
  Quotient (primWordSetoid ι k hk)

/-- A rotation of a primitive word is primitive. -/
private theorem minimalPeriod_wordRot_iterate_prim {ι : Type*} {k : ℕ} (hk : 0 < k)
    (u : PrimWord ι k) (r : ℕ) :
    Function.minimalPeriod (wordRot k) ((wordRot k)^[r] u.1) = k := by
  have hper : u.1 ∈ Function.periodicPts (wordRot k) :=
    ⟨k, hk, isPeriodicPt_wordRot_self k u.1⟩
  rw [Function.minimalPeriod_apply_iterate hper, u.2]

/-- Each primitive necklace of length `k` has exactly `k` representatives. -/
private noncomputable def primNecklaceFiberEquiv {ι : Type*} {k : ℕ} (hk : 0 < k)
    (c : PrimNecklace ι k hk) :
    Fin k ≃ {u : PrimWord ι k //
      (Quotient.mk (primWordSetoid ι k hk) u : PrimNecklace ι k hk) = c}
    where
  toFun r :=
    ⟨⟨(wordRot k)^[r.1] c.out.1, minimalPeriod_wordRot_iterate_prim hk c.out r.1⟩, by
      conv_rhs => rw [← Quotient.out_eq c]
      exact (Quotient.sound (s := primWordSetoid ι k hk) ⟨r.1, rfl⟩).symm⟩
  invFun u := by
    have hrel : primWordSetoid ι k hk c.out u.1 :=
      Quotient.exact (by rw [u.2, Quotient.out_eq])
    exact ⟨hrel.choose % k, Nat.mod_lt _ hk⟩
  left_inv r := by
    dsimp only
    set u : PrimWord ι k :=
      ⟨(wordRot k)^[r.1] c.out.1, minimalPeriod_wordRot_iterate_prim hk c.out r.1⟩
    have hu : (Quotient.mk (primWordSetoid ι k hk) u : PrimNecklace ι k hk) = c := by
      conv_rhs => rw [← Quotient.out_eq c]
      exact (Quotient.sound (s := primWordSetoid ι k hk) ⟨r.1, rfl⟩).symm
    have hrel : primWordSetoid ι k hk c.out u :=
      Quotient.exact (by rw [hu, Quotient.out_eq])
    have hmod : (wordRot k)^[hrel.choose % k] c.out.1 = (wordRot k)^[r.1] c.out.1 := by
      have h1 : (wordRot k)^[hrel.choose % k] c.out.1 = (wordRot k)^[hrel.choose] c.out.1 := by
        simpa [c.out.2] using
          Function.iterate_mod_minimalPeriod_eq (f := wordRot k) (x := c.out.1) (n := hrel.choose)
      exact h1.trans hrel.choose_spec
    exact Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by rw [c.out.2]; exact Nat.mod_lt _ hk) (by rw [c.out.2]; exact r.2)).mp hmod)
  right_inv u := by
    have hrel : primWordSetoid ι k hk c.out u.1 :=
      Quotient.exact (by rw [u.2, Quotient.out_eq])
    refine Subtype.ext (Subtype.ext ?_)
    dsimp only
    have h1 : (wordRot k)^[hrel.choose % k] c.out.1 = (wordRot k)^[hrel.choose] c.out.1 := by
      simpa [c.out.2] using
        Function.iterate_mod_minimalPeriod_eq (f := wordRot k) (x := c.out.1) (n := hrel.choose)
    exact h1.trans hrel.choose_spec

/-- Summing a rotation-invariant function over primitive words of length `k` multiplies its sum
over primitive necklaces by `k`. -/
private theorem sum_primWord_eq_sum_primNecklace {ι M : Type*} [AddCommMonoid M]
    {k : ℕ} (hk : 0 < k) [Fintype (PrimWord ι k)] [Fintype (PrimNecklace ι k hk)]
    (F : PrimWord ι k → M)
    (hF : ∀ (u : PrimWord ι k) (r : ℕ),
      F ⟨(wordRot k)^[r] u.1, minimalPeriod_wordRot_iterate_prim hk u r⟩ = F u) :
    ∑ u : PrimWord ι k, F u = ∑ c : PrimNecklace ι k hk, k • F c.out := by
  classical
  let q : PrimWord ι k → PrimNecklace ι k hk := Quotient.mk (primWordSetoid ι k hk)
  rw [← Fintype.sum_equiv (Equiv.sigmaFiberEquiv q) (fun p ↦ F p.2.1) F (fun _ ↦ rfl),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [← Fintype.sum_equiv (primNecklaceFiberEquiv hk c)
    (fun r ↦ F (primNecklaceFiberEquiv hk c r).1) (fun u ↦ F u.1) (fun _ ↦ rfl)]
  have hconst : ∀ r : Fin k, F (primNecklaceFiberEquiv hk c r).1 = F c.out :=
    fun r ↦ hF c.out r.1
  simp [hconst]

/-! ### Word products and powers of sums -/

/-- The product of `A (w 0) * A (w 1) * ⋯ * A (w (k - 1))`. -/
private def wordProd {ι M : Type*} [Monoid M] (A : ι → M) {k : ℕ} (w : Fin k → ι) : M :=
  (List.ofFn fun j ↦ A (w j)).prod

private theorem sum_pow_eq_sum_wordProd {ι S : Type*} [Fintype ι] [Semiring S]
    (A : ι → S) (n : ℕ) :
    (∑ i : ι, A i) ^ n = ∑ w : Fin n → ι, wordProd A w := by
  induction n with
  | zero =>
    rw [pow_zero, Fintype.sum_unique]
    simp [wordProd]
  | succ n ih =>
    rw [pow_succ', ih, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Fin.consEquiv fun _ ↦ ι) _ _ fun ⟨i, w⟩ ↦ ?_
    simp [wordProd, List.ofFn_succ]

private theorem wordProd_repeatWord {ι M : Type*} [Monoid M] (A : ι → M) {k : ℕ} (hk : 0 < k)
    (u : Fin k → ι) (q : ℕ) :
    wordProd A (repeatWord (n := k * q) hk u) = wordProd A u ^ q := by
  induction q with
  | zero => simp [wordProd]
  | succ q ih =>
    rw [pow_succ, ← ih]
    simp only [wordProd]
    have hsplit : (List.ofFn fun j : Fin (k * (q + 1)) ↦ A (repeatWord hk u j)) =
        (List.ofFn fun j : Fin (k * q) ↦ A (repeatWord hk u j)) ++
        (List.ofFn fun j : Fin k ↦ A (u j)) := by
      refine List.ext_getElem (by simp [Nat.mul_succ]) fun m hm _ ↦ ?_
      rw [List.getElem_ofFn, List.getElem_append]
      simp only [List.length_ofFn, repeatWord]
      split_ifs with hlt
      · rw [List.getElem_ofFn]
      · rw [List.getElem_ofFn]
        have hmod : m % k = m - k * q := by
          have hm' : m < k * q + k := by simpa [Nat.mul_succ] using hm
          have hsub : m - k * q < k := by omega
          have hmul : m = k * q + (m - k * q) := by omega
          conv_lhs => rw [hmul]
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hsub]
        congr 2
        exact Fin.ext hmod
    rw [hsplit, List.prod_append]

private theorem wordProd_repeatWord_of_dvd {ι M : Type*} [Monoid M] (A : ι → M) {k n : ℕ}
    (hk : 0 < k) (hkn : k ∣ n) (u : Fin k → ι) :
    wordProd A (repeatWord (n := n) hk u) = wordProd A u ^ (n / k) := by
  obtain ⟨q, rfl⟩ := hkn
  rw [Nat.mul_div_cancel_left q hk]
  exact wordProd_repeatWord A hk u q

private theorem charpolyRev_wordProd_wordRot_iterate {ι n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] (A : ι → Matrix n n R) {k : ℕ} (r : ℕ) (w : Fin k → ι) :
    (wordProd A ((wordRot k)^[r] w)).charpolyRev = (wordProd A w).charpolyRev := by
  have hrot : List.ofFn (fun j ↦ A (((wordRot k)^[r] w) j)) =
      (List.ofFn (fun j ↦ A (w j))).rotate r := by
    simpa [wordRot_iterate, Function.comp_def] using
      List.ofFn_comp_finRotate_pow (fun j ↦ A (w j)) r
  rw [wordProd, wordProd, hrot]
  have hIsRot : List.IsRotated (List.ofFn (fun j ↦ A (w j)))
      ((List.ofFn (fun j ↦ A (w j))).rotate r) := ⟨r, rfl⟩
  exact hIsRot.symm.apply_prod_eq Matrix.charpolyRev_mul_comm

private theorem trace_pow_sum_eq_sum_primNecklace {ι n R : Type*} [Fintype ι] [Fintype n]
    [DecidableEq n] [CommRing R] (A : ι → Matrix n n R) {m : ℕ} (hm : 0 < m) :
    ((∑ i : ι, A i) ^ m).trace =
      ∑ k : m.divisors,
        ∑ c ∈ (Fintype.ofFinite (PrimNecklace ι k.1 (Nat.pos_of_mem_divisors k.2))).elems,
          k.1 • ((wordProd A c.out.1) ^ (m / k.1)).trace := by
  classical
  rw [sum_pow_eq_sum_wordProd, Matrix.trace_sum]
  rw [Fintype.sum_equiv (wordEquivSigmaPrimWord hm)
    (fun w ↦ (wordProd A w).trace)
    (fun p ↦ (wordProd A ((wordEquivSigmaPrimWord hm).symm p)).trace)
    (fun w ↦ by simp), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk_pos : 0 < k.1 := Nat.pos_of_mem_divisors k.2
  have hk_dvd : k.1 ∣ m := (Nat.mem_divisors.mp k.2).1
  have hdiv_pos : 0 < m / k.1 := Nat.div_pos (Nat.le_of_dvd hm hk_dvd) hk_pos
  have hrep : ∀ u : PrimWord ι k.1,
      (wordProd A ((wordEquivSigmaPrimWord hm).symm ⟨k, u⟩)).trace =
        ((wordProd A u.1) ^ (m / k.1)).trace := fun u ↦ by
    simpa [wordEquivSigmaPrimWord] using
      congrArg Matrix.trace (wordProd_repeatWord_of_dvd A hk_pos hk_dvd u.1)
  simp_rw [hrep]
  have hinv : ∀ (u : PrimWord ι k.1) (r : ℕ),
      ((wordProd A ((wordRot k.1)^[r] u.1)) ^ (m / k.1)).trace =
        ((wordProd A u.1) ^ (m / k.1)).trace := fun u r ↦
    Matrix.trace_pow_eq_of_charpolyRev_eq (charpolyRev_wordProd_wordRot_iterate A r u.1) hdiv_pos
  let _ : Fintype (PrimNecklace ι k.1 hk_pos) := Fintype.ofFinite _
  exact sum_primWord_eq_sum_primNecklace hk_pos
    (fun u ↦ ((wordProd A u.1) ^ (m / k.1)).trace) hinv

/-! ### Truncated necklace factorization of `det (1 - X ∑ Aᵢ)` -/

/-- The truncated Witt–Amitsur necklace product of length at most `d`:
`∏_{1 ≤ k ≤ d} ∏_{c} det (1 - X ^ k A_c)` over primitive necklaces `c` of length `k`. -/
private noncomputable def necklaceProd {ι n R : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    [CommRing R] (A : ι → Matrix n n R) (d : ℕ) : R[X] :=
  ∏ k ∈ (Finset.Icc 1 d).attach,
    ∏ c ∈ (Fintype.ofFinite (PrimNecklace ι k.1 (Finset.mem_Icc.mp k.2).1)).elems,
      (wordProd A c.out.1).charpolyRev.comp (X ^ k.1)

private theorem map_finset_sum {ι n R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (s : Finset ι) (A : ι → Matrix n n R) :
    (∑ i ∈ s, A i).map f = ∑ i ∈ s, (A i).map f := by
  ext p q
  simp [Matrix.sum_apply, map_sum]

private theorem map_wordProd {ι n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    [CommRing S] (f : R →+* S) (A : ι → Matrix n n R) {k : ℕ} (w : Fin k → ι) :
    (wordProd A w).map f = wordProd (fun i ↦ (A i).map f) w := by
  simp only [wordProd]
  have : ∀ (l : List (Matrix n n R)), l.prod.map f = (l.map (Matrix.map · f)).prod := by
    intro l
    induction l with
    | nil => simp [Matrix.map_one]
    | cons B l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, Matrix.map_mul, ih]
  rw [this, List.map_ofFn]
  rfl

private theorem map_necklaceProd {ι n R S : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    [CommRing R] [CommRing S] (f : R →+* S) (A : ι → Matrix n n R) (d : ℕ) :
    (necklaceProd A d).map f = necklaceProd (fun i ↦ (A i).map f) d := by
  simp only [necklaceProd, Polynomial.map_prod, Polynomial.map_comp, Polynomial.map_pow,
    Polynomial.map_X, ← Matrix.charpolyRev_map, map_wordProd]

private theorem coe_comp_X_pow {R : Type*} [CommRing R] (p : R[X]) {k : ℕ} (hk : k ≠ 0) :
    ((p.comp (X ^ k) : R[X]) : PowerSeries R) =
      (p : PowerSeries R).subst (PowerSeries.X ^ k : PowerSeries R) := by
  rw [PowerSeries.subst_coe (PowerSeries.HasSubst.X_pow hk), Polynomial.aeval_def,
    Polynomial.comp, ← Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.hom_eval₂]
  congr 1
  · ext r; simp
  · simp

private theorem logOf_subst_X_pow {R : Type*} [CommRing R] [Algebra ℚ R] {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 1) {k : ℕ} (hk : k ≠ 0) :
    PowerSeries.logOf (f.subst (PowerSeries.X ^ k : PowerSeries R)) =
      (PowerSeries.logOf f).subst (PowerSeries.X ^ k : PowerSeries R) := by
  have hsub1 : PowerSeries.HasSubst (f - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hf])
  have hsub2 : PowerSeries.HasSubst (PowerSeries.X ^ k : PowerSeries R) :=
    PowerSeries.HasSubst.X_pow hk
  have hsubf : f.subst (PowerSeries.X ^ k : PowerSeries R) - 1 =
      (f - 1).subst (PowerSeries.X ^ k : PowerSeries R) := by
    rw [PowerSeries.subst_sub hsub2, PowerSeries.subst_one]
  rw [PowerSeries.logOf_eq, PowerSeries.logOf_eq, hsubf,
    PowerSeries.subst_comp_subst_apply hsub1 hsub2 (PowerSeries.log R)]

private theorem coe_finset_prod {α R : Type*} [CommRing R] (s : Finset α) (f : α → R[X]) :
    ((∏ i ∈ s, f i : R[X]) : PowerSeries R) = ∏ i ∈ s, (f i : PowerSeries R) :=
  map_prod (Polynomial.coeToPowerSeries.ringHom (R := R)) f s

private theorem constantCoeff_coe_charpolyRev_comp_X_pow {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] (B : Matrix n n R) {k : ℕ} (hk : k ≠ 0) :
    PowerSeries.constantCoeff ((B.charpolyRev.comp (X ^ k) : R[X]) : PowerSeries R) = 1 := by
  rw [coe_comp_X_pow _ hk, PowerSeries.constantCoeff_subst_X_pow hk,
    Matrix.constantCoeff_coe_charpolyRev, Algebra.algebraMap_self_apply]

private theorem constantCoeff_coe_necklaceProd {ι n R : Type*} [Fintype ι] [Fintype n]
    [DecidableEq n] [CommRing R] (A : ι → Matrix n n R) (d : ℕ) :
    PowerSeries.constantCoeff (necklaceProd A d : PowerSeries R) = 1 := by
  simp only [necklaceProd, coe_finset_prod, map_prod]
  exact Finset.prod_eq_one fun k _ ↦ Finset.prod_eq_one fun c _ ↦
    constantCoeff_coe_charpolyRev_comp_X_pow _ (Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp k.2).1)

private theorem logOf_necklaceProd {ι n R : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    [CommRing R] [Algebra ℚ R] (A : ι → Matrix n n R) (d : ℕ) :
    PowerSeries.logOf (necklaceProd A d : PowerSeries R) =
      ∑ k ∈ (Finset.Icc 1 d).attach,
        ∑ c ∈ (Fintype.ofFinite (PrimNecklace ι k.1 (Finset.mem_Icc.mp k.2).1)).elems,
          (PowerSeries.logOf ((wordProd A c.out.1).charpolyRev : PowerSeries R)).subst
            (PowerSeries.X ^ k.1 : PowerSeries R) := by
  simp only [necklaceProd, coe_finset_prod]
  rw [PowerSeries.logOf_prod fun k _ ↦ by
    rw [map_prod]
    exact Finset.prod_eq_one fun c _ ↦
      constantCoeff_coe_charpolyRev_comp_X_pow _ (Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp k.2).1)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk0 : k.1 ≠ 0 := Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp k.2).1
  rw [PowerSeries.logOf_prod fun c _ ↦ constantCoeff_coe_charpolyRev_comp_X_pow _ hk0]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [coe_comp_X_pow _ hk0, logOf_subst_X_pow (Matrix.constantCoeff_coe_charpolyRev _) hk0]

private theorem coeff_logOf_necklaceProd_term {ι n R : Type*} [Finite ι] [Fintype n]
    [DecidableEq n] [CommRing R] [Algebra ℚ R] (A : ι → Matrix n n R) {k m : ℕ}
    (hk_pos : 0 < k) (hm_pos : 0 < m) :
    (∑ c ∈ (Fintype.ofFinite (PrimNecklace ι k hk_pos)).elems,
        PowerSeries.coeff m ((PowerSeries.logOf
          ((wordProd A c.out.1).charpolyRev : PowerSeries R)).subst
            (PowerSeries.X ^ k : PowerSeries R))) =
      if k ∣ m then
        (m : ℚ)⁻¹ • -∑ c ∈ (Fintype.ofFinite (PrimNecklace ι k hk_pos)).elems,
          k • ((wordProd A c.out.1) ^ (m / k)).trace
      else 0 := by
  have hk0 : k ≠ 0 := hk_pos.ne'
  simp_rw [PowerSeries.coeff_subst_X_pow hk0, Matrix.logOf_charpolyRev, PowerSeries.coeff_mk,
    Algebra.algebraMap_self_apply]
  split_ifs with hdvd
  · rw [smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    have hkm : ((m / k : ℕ) : ℚ)⁻¹ = (m : ℚ)⁻¹ * (k : ℚ) := by
      have hm_eq : (m : ℚ) = (k : ℚ) * ((m / k : ℕ) : ℚ) := by
        exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
      have hk_q : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
      have hq_q : ((m / k : ℕ) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.div_pos (Nat.le_of_dvd hm_pos hdvd) hk_pos).ne'
      field_simp [hk_q, hq_q]
      linarith
    rw [hkm, mul_smul, smul_neg, smul_neg, Nat.cast_smul_eq_nsmul]
  · simp

private theorem sum_Icc_filter_dvd_eq_sum_divisors {M : Type*} [AddCommMonoid M]
    {d m : ℕ} (hm_pos : 0 < m) (hm : m ≤ d) (F : ∀ k : ℕ, 0 < k → M) :
    ∑ k ∈ (Finset.Icc 1 d).attach.filter (fun k ↦ k.1 ∣ m),
        F k.1 (Finset.mem_Icc.mp k.2).1 =
      ∑ k : m.divisors, F k.1 (Nat.pos_of_mem_divisors k.2) := by
  refine Finset.sum_bij (fun k hk ↦
    ⟨k.1, Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hk).2, hm_pos.ne'⟩⟩) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro k₁ _ k₂ _ h
    exact Subtype.ext (congrArg (fun x : m.divisors ↦ x.1) h)
  · intro k _
    have hk_pos : 0 < k.1 := Nat.pos_of_mem_divisors k.2
    have hk_dvd : k.1 ∣ m := (Nat.mem_divisors.mp k.2).1
    have hk_icc : k.1 ∈ Finset.Icc 1 d :=
      Finset.mem_Icc.mpr ⟨hk_pos, (Nat.le_of_dvd hm_pos hk_dvd).trans hm⟩
    exact ⟨⟨k.1, hk_icc⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hk_dvd⟩, rfl⟩
  · intro _ _; rfl

private theorem coeff_logOf_necklaceProd_eq {ι n R : Type*} [Fintype ι] [Fintype n]
    [DecidableEq n] [CommRing R] [Algebra ℚ R] (A : ι → Matrix n n R)
    {d m : ℕ} (hm : m ≤ d) :
    PowerSeries.coeff m (PowerSeries.logOf ((∑ i : ι, A i).charpolyRev : PowerSeries R)) =
      PowerSeries.coeff m (PowerSeries.logOf (necklaceProd A d : PowerSeries R)) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · simp [PowerSeries.constantCoeff_logOf (Matrix.constantCoeff_coe_charpolyRev _),
      PowerSeries.constantCoeff_logOf (constantCoeff_coe_necklaceProd A d)]
  rw [logOf_necklaceProd, map_sum]
  simp_rw [map_sum]
  have hterm : ∀ k ∈ (Finset.Icc 1 d).attach,
      (∑ c ∈ (Fintype.ofFinite (PrimNecklace ι k.1 (Finset.mem_Icc.mp k.2).1)).elems,
          PowerSeries.coeff m ((PowerSeries.logOf
            ((wordProd A c.out.1).charpolyRev : PowerSeries R)).subst
              (PowerSeries.X ^ k.1 : PowerSeries R))) =
        if k.1 ∣ m then
          (m : ℚ)⁻¹ • -∑ c ∈ (Fintype.ofFinite
              (PrimNecklace ι k.1 (Finset.mem_Icc.mp k.2).1)).elems,
            k.1 • ((wordProd A c.out.1) ^ (m / k.1)).trace
        else 0 :=
    fun k _ ↦ coeff_logOf_necklaceProd_term A (Finset.mem_Icc.mp k.2).1 hm_pos
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter,
    sum_Icc_filter_dvd_eq_sum_divisors hm_pos hm fun k hk ↦
      (m : ℚ)⁻¹ • -∑ c ∈ (Fintype.ofFinite (PrimNecklace ι k hk)).elems,
        k • ((wordProd A c.out.1) ^ (m / k)).trace,
    ← Finset.smul_sum, Finset.sum_neg_distrib, ← trace_pow_sum_eq_sum_primNecklace A hm_pos]
  simp [Matrix.logOf_charpolyRev]

private theorem coeff_charpolyRev_sum_eq_necklaceProd_of_algebra_rat {ι n R : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [CommRing R] [Algebra ℚ R]
    (A : ι → Matrix n n R) (d r : ℕ) (hr : r ≤ d) :
    (∑ i : ι, A i).charpolyRev.coeff r = (necklaceProd A d).coeff r := by
  set P : PowerSeries R := ((∑ i : ι, A i).charpolyRev : PowerSeries R)
  set Q : PowerSeries R := (necklaceProd A d : PowerSeries R)
  have hP0 : PowerSeries.constantCoeff P = 1 := Matrix.constantCoeff_coe_charpolyRev _
  have hQ0 : PowerSeries.constantCoeff Q = 1 := constantCoeff_coe_necklaceProd A d
  have hdvd : PowerSeries.X ^ (d + 1) ∣ PowerSeries.logOf P - PowerSeries.logOf Q :=
    PowerSeries.X_pow_dvd_iff.mpr fun m hm ↦ by
      rw [map_sub, coeff_logOf_necklaceProd_eq A (Nat.lt_succ_iff.mp hm), sub_self]
  have hdvdPQ : PowerSeries.X ^ (d + 1) ∣ P - Q := by
    have h := PowerSeries.X_pow_dvd_subst_sub_subst
      (PowerSeries.constantCoeff_logOf hP0) hdvd (PowerSeries.exp R)
    rwa [PowerSeries.subst_exp_logOf hP0, PowerSeries.subst_exp_logOf hQ0] at h
  have hsub := PowerSeries.X_pow_dvd_iff.mp hdvdPQ r (Nat.lt_succ_of_le hr)
  rw [map_sub, sub_eq_zero, Polynomial.coeff_coe, Polynomial.coeff_coe] at hsub
  exact hsub

/-- **Truncated Witt–Amitsur necklace factorization** over any commutative ring: through degree
`d`, the coefficients of `det (1 - X ∑ i, A i)` agree with those of the primitive necklace product
of length at most `d`. -/
private theorem coeff_charpolyRev_sum_eq_necklaceProd {ι n R : Type*} [Fintype ι] [Fintype n]
    [DecidableEq n] [CommRing R] (A : ι → Matrix n n R) (d r : ℕ) (hr : r ≤ d) :
    (∑ i : ι, A i).charpolyRev.coeff r = (necklaceProd A d).coeff r := by
  let U : ι → Matrix n n (MvPolynomial (ι × n × n) ℤ) :=
    fun i ↦ Matrix.of fun p q ↦ MvPolynomial.X (i, p, q)
  let ιQ : MvPolynomial (ι × n × n) ℤ →+* MvPolynomial (ι × n × n) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hιQ : Function.Injective ιQ := MvPolynomial.map_injective _ Int.cast_injective
  have hU : (∑ i : ι, U i).charpolyRev.coeff r = (necklaceProd U d).coeff r := by
    apply hιQ
    rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpolyRev_map,
      map_finset_sum, map_necklaceProd]
    exact coeff_charpolyRev_sum_eq_necklaceProd_of_algebra_rat (fun i ↦ (U i).map ιQ) d r hr
  let φ : MvPolynomial (ι × n × n) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) fun t ↦ A t.1 t.2.1 t.2.2
  have hφ : ∀ i, (U i).map φ = A i := fun i ↦ by
    ext p q
    simp [U, φ]
  have h := congrArg φ hU
  rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpolyRev_map,
    map_finset_sum, map_necklaceProd] at h
  simpa only [hφ] using h

end Necklaces

/-! ### Amitsur's determination theorems -/

section Amitsur

variable {ι n m R : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [CommRing R]

/-- **Amitsur's theorem for coefficients of `det (1 - X ∑ Aᵢ)`**: through degree `d`, the
coefficients of `det (1 - X ∑ i ∈ s, A i)` are determined by the reversed characteristic
polynomials of nonempty word products in `s` of length at most `d`. The two families of matrices
may have different sizes. -/
theorem coeff_charpolyRev_sum_eq_of_forall_list_prod {s : Finset ι}
    {A : ι → Matrix n n R} {B : ι → Matrix m m R} {d : ℕ}
    (h : ∀ l : List ι, l ≠ [] → l.length ≤ d → (∀ i ∈ l, i ∈ s) →
      (l.map A).prod.charpolyRev = (l.map B).prod.charpolyRev)
    {r : ℕ} (hr : r ≤ d) :
    (∑ i ∈ s, A i).charpolyRev.coeff r = (∑ i ∈ s, B i).charpolyRev.coeff r := by
  let A' : s → Matrix n n R := fun i ↦ A i.1
  let B' : s → Matrix m m R := fun i ↦ B i.1
  have hsumA : ∑ i ∈ s, A i = ∑ i : s, A' i := (Finset.sum_coe_sort s A).symm
  have hsumB : ∑ i ∈ s, B i = ∑ i : s, B' i := (Finset.sum_coe_sort s B).symm
  rw [hsumA, hsumB, coeff_charpolyRev_sum_eq_necklaceProd A' d r hr,
    coeff_charpolyRev_sum_eq_necklaceProd B' d r hr]
  refine congrArg (fun p : R[X] ↦ p.coeff r) ?_
  simp only [necklaceProd]
  refine Finset.prod_congr rfl fun k _ ↦ Finset.prod_congr rfl fun c _ ↦
    congrArg (fun p : R[X] ↦ p.comp (X ^ k.1)) ?_
  have hk_pos : 0 < k.1 := (Finset.mem_Icc.mp k.2).1
  have hk_le : k.1 ≤ d := (Finset.mem_Icc.mp k.2).2
  set l : List ι := List.ofFn fun j : Fin k.1 ↦ (c.out.1 j).1
  have hl_ne : l ≠ [] := by
    intro hl
    have := congrArg List.length hl
    simp [l] at this
    omega
  have hl_len : l.length ≤ d := by simpa [l] using hk_le
  have hl_mem : ∀ i ∈ l, i ∈ s := by
    intro i hi
    rw [List.mem_ofFn] at hi
    obtain ⟨j, rfl⟩ := hi
    exact (c.out.1 j).2
  have hA : wordProd A' c.out.1 = (l.map A).prod := by
    simp [wordProd, l, List.map_ofFn, A', Function.comp_def]
  have hB : wordProd B' c.out.1 = (l.map B).prod := by
    simp [wordProd, l, List.map_ofFn, B', Function.comp_def]
  rw [hA, hB, h l hl_ne hl_len hl_mem]

/-- **Amitsur's theorem for `det (1 - X ∑ Aᵢ)`**: over any commutative ring,
`det (1 - X ∑ Aᵢ)` is determined by `det (1 - X A_w)` on nonempty words `w` of length at most
`max |n| |m|`. -/
theorem charpolyRev_sum_eq_of_forall_list_prod {s : Finset ι}
    {A : ι → Matrix n n R} {B : ι → Matrix m m R}
    (h : ∀ l : List ι, l ≠ [] → l.length ≤ max (Fintype.card n) (Fintype.card m) →
      (∀ i ∈ l, i ∈ s) → (l.map A).prod.charpolyRev = (l.map B).prod.charpolyRev) :
    (∑ i ∈ s, A i).charpolyRev = (∑ i ∈ s, B i).charpolyRev := by
  ext r
  rcases le_or_gt r (max (Fintype.card n) (Fintype.card m)) with hr | hr
  · exact coeff_charpolyRev_sum_eq_of_forall_list_prod h hr
  · rw [coeff_charpolyRev_eq_zero _ ((le_max_left _ _).trans_lt hr),
      coeff_charpolyRev_eq_zero _ ((le_max_right _ _).trans_lt hr)]

/-- **Amitsur's theorem for characteristic polynomials of sums of matrices**: over any commutative
ring, if two families of matrices of the same size `d × d` have the same characteristic polynomials
on all nonempty word products of length at most `d`, then their sums have the same characteristic
polynomial. -/
theorem charpoly_sum_eq_of_forall_list_prod {s : Finset ι}
    {A : ι → Matrix n n R} {B : ι → Matrix m m R} (hnm : Fintype.card n = Fintype.card m)
    (h : ∀ l : List ι, l ≠ [] → l.length ≤ Fintype.card n → (∀ i ∈ l, i ∈ s) →
      (l.map A).prod.charpoly = (l.map B).prod.charpoly) :
    (∑ i ∈ s, A i).charpoly = (∑ i ∈ s, B i).charpoly := by
  rw [← charpolyRev_eq_charpolyRev_iff hnm]
  refine charpolyRev_sum_eq_of_forall_list_prod fun l hl hlen hmem ↦ ?_
  rw [charpolyRev_eq_charpolyRev_iff hnm]
  exact h l hl (by simpa [hnm] using hlen) hmem

end Amitsur

end Matrix

namespace LinearMap

variable {ι R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]

/-- **Amitsur's theorem for endomorphisms of finite free modules**: over any commutative ring, if
two families of endomorphisms on finite free modules of equal rank `d` have the same characteristic
polynomials on all nonempty word products of length at most `d`, then their sums have the same
characteristic polynomial. -/
theorem charpoly_sum_eq_of_forall_list_prod {s : Finset ι}
    {f : ι → Module.End R V} {g : ι → Module.End R W}
    (hVW : Module.finrank R V = Module.finrank R W)
    (h : ∀ l : List ι, l ≠ [] → l.length ≤ Module.finrank R V →
      (∀ i ∈ l, i ∈ s) → (l.map f).prod.charpoly = (l.map g).prod.charpoly) :
    (∑ i ∈ s, f i).charpoly = (∑ i ∈ s, g i).charpoly := by
  nontriviality R
  let bV := Module.Free.chooseBasis R V
  let bW := Module.Free.chooseBasis R W
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R V) =
      Fintype.card (Module.Free.ChooseBasisIndex R W) := by
    simpa [Module.finrank_eq_card_chooseBasisIndex] using hVW
  have htoV (u : Module.End R V) : (LinearMap.toMatrixAlgEquiv bV u).charpoly = u.charpoly :=
    charpoly_toMatrix u bV
  have htoW (u : Module.End R W) : (LinearMap.toMatrixAlgEquiv bW u).charpoly = u.charpoly :=
    charpoly_toMatrix u bW
  rw [← htoV, ← htoW, map_sum, map_sum]
  refine Matrix.charpoly_sum_eq_of_forall_list_prod hcard fun l hl hlen hmem ↦ ?_
  have hmapV : l.map (fun x ↦ LinearMap.toMatrixAlgEquiv bV (f x)) =
      (l.map f).map (LinearMap.toMatrixAlgEquiv bV) := (List.map_map ..).symm
  have hmapW : l.map (fun x ↦ LinearMap.toMatrixAlgEquiv bW (g x)) =
      (l.map g).map (LinearMap.toMatrixAlgEquiv bW) := (List.map_map ..).symm
  rw [hmapV, hmapW, ← map_list_prod (LinearMap.toMatrixAlgEquiv bV),
    ← map_list_prod (LinearMap.toMatrixAlgEquiv bW), htoV, htoW]
  exact h l hl (by simpa [Module.finrank_eq_card_chooseBasisIndex] using hlen) hmem

end LinearMap
