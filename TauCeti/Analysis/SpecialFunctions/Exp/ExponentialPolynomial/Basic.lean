/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Polynomial.Roots
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Calculus.LocalExtr.Rolle
import TauCeti.LinearAlgebra.Vandermonde

/-!
# Zeros and linear independence of exponential polynomials

A real *exponential polynomial* is a function `f(x) = ∑ₖ pₖ(x) exp(γₖ x)` with real polynomials
`pₖ` and real exponents `γₖ`, indexed by a finite set. If the index set is nonempty, the
exponents are pairwise distinct and the `pₖ` are nonzero, then `f` has fewer than
`∑ₖ (deg pₖ + 1)` real zeros (`TauCeti.card_lt_of_sum_eval_mul_exp_eq_zero`); in particular its
zero set is finite. Nonemptiness is needed: the empty sum vanishes everywhere.
For a single term this is the bound on the number of roots of a polynomial.

This zero estimate is used in Schneider's proof of the Gelfond–Schneider theorem for real
numbers: an auxiliary function `∑ᵢⱼ aᵢⱼ zⁱ exp(j z log α)` cannot vanish at more real points
than the number of its coefficients.

Over the complex numbers, the zero set need no longer be finite (`exp z - 1` vanishes at `2 π i ℤ`),
but the order of vanishing at every point is bounded. For an *exponential sum*
`E(z) = ∑ᵢ cᵢ exp(ρᵢ z)` with constant coefficients, `E⁽ᵏ⁾(z) = ∑ᵢ cᵢ ρᵢᵏ exp(ρᵢ z)`: if the
frequencies `ρᵢ` are pairwise distinct and the coefficients are not all zero, then at every point
`z₀` one of the first `N` derivatives is nonzero, `N` being the number of terms, because the
Vandermonde matrix of the `ρᵢ` is invertible. Thus `E` vanishes to order less than `N` everywhere.
This bounds the order of the first nonvanishing derivative of Gelfond's auxiliary function
`∑ₐ,ᵦ ηₐᵦ exp((a + bβ) λ z)` in his proof of the Gelfond–Schneider theorem.

More generally, for a complex exponential polynomial `f(z) = ∑ᵢ pᵢ(z) exp(ρᵢ z)` with polynomial
coefficients `pᵢ ∈ ℂ[X]`, pairwise distinct frequencies `ρᵢ`, and at least one nonzero `pᵢ`, one
of the first `∑ᵢ (deg pᵢ + 1)` derivatives of `f` is nonzero at every point `z₀`: dividing out
`exp(ρₐ z)` turns the `a`-th summand into `pₐ(z)`, which `deg pₐ + 1` differentiations annihilate
while the remaining shifted operators `r ↦ r' + (ρᵢ - ρₐ) r` preserve degree and nonvanishing.
Consequently `analyticOrderAt f z₀ < ∑ᵢ (deg pᵢ + 1)` everywhere, `f` vanishes identically only
when every `pᵢ = 0`, its polynomial coefficients over distinct frequencies are unique, and the
exponential monomials `z ↦ z ^ k exp(ρᵢ z)` for injective `ρ` are linearly independent over `ℂ`.

## Main results

* `Finset.hasDerivAt_sum_eval_mul_exp`: the derivative of `∑ₖ pₖ(x) exp(γₖ x)` is again an
  exponential polynomial, `∑ₖ (pₖ' + γₖ pₖ)(x) exp(γₖ x)`.
* `TauCeti.card_lt_of_sum_eval_mul_exp_eq_zero`: for a nonempty finite index set, pairwise
  distinct exponents `γₖ` and nonzero `pₖ`, a finite set of zeros of `∑ₖ pₖ(x) exp(γₖ x)` has
  fewer than `∑ₖ (deg pₖ + 1)` points.
* `TauCeti.finite_setOf_sum_eval_mul_exp_eq_zero`: under the same hypotheses, the zero set of
  such a function is finite.
* `Finset.iteratedDeriv_sum_mul_cexp`: the iterated derivatives of a complex exponential sum.
* `TauCeti.exists_lt_card_iteratedDeriv_sum_mul_cexp_ne_zero`: with pairwise distinct frequencies
  and coefficients not all zero, one of the first `N` derivatives of `∑ᵢ cᵢ exp(ρᵢ z)` is nonzero
  at every point.
* `TauCeti.analyticOrderAt_sum_mul_cexp_lt_card`: under the same hypotheses, the order of
  vanishing of `∑ᵢ cᵢ exp(ρᵢ z)` at every point is less than the number `N` of terms.
* `Finset.hasDerivAt_sum_eval_mul_cexp`, `Finset.iteratedDeriv_sum_eval_mul_cexp`: derivatives of
  `∑ᵢ pᵢ(z) exp(ρᵢ z)` via iterates of `r ↦ r' + ρᵢ r`.
* `TauCeti.exists_lt_sum_iteratedDeriv_sum_eval_mul_cexp_ne_zero`,
  `TauCeti.analyticOrderAt_sum_eval_mul_cexp_lt`: with pairwise distinct frequencies and at least
  one nonzero `pᵢ`, one of the first `∑ᵢ (deg pᵢ + 1)` derivatives is nonzero at every point, so
  the analytic order of vanishing there is less than `∑ᵢ (deg pᵢ + 1)`.
* `TauCeti.sum_eval_mul_cexp_eq_zero_iff`, `TauCeti.sum_eval_mul_cexp_eq_iff`: vanishing
  characterization and uniqueness of polynomial coefficients over distinct complex frequencies.
* `TauCeti.linearIndependent_pow_mul_cexp`: linear independence over `ℂ` of the functions
  `z ↦ z ^ k exp(ρᵢ z)` for injective `ρ`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.4, Lemma 4.23.
* M. Karatarakis and F. Wiedijk, *A formalization of the Gelfond–Schneider theorem*,
  arXiv:2603.24823 (2026), §3.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000), ch. 4.
-/

public section

open Finset Polynomial

namespace Finset

/-- The derivative of `∑ₖ pₖ(x) exp(γₖ x)` is `∑ₖ (pₖ' + γₖ pₖ)(x) exp(γₖ x)`. -/
theorem hasDerivAt_sum_eval_mul_exp {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (p : ι → ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x ↦ ∑ i ∈ s, (p i).eval x * Real.exp (γ i * x))
      (∑ i ∈ s, (derivative (p i) + C (γ i) * p i).eval x * Real.exp (γ i * x)) x := by
  refine HasDerivAt.fun_sum fun i _ ↦ ?_
  refine (((p i).hasDerivAt x).fun_mul ((hasDerivAt_id' x).const_mul (γ i)).exp).congr_deriv ?_
  simp only [eval_add, eval_mul, eval_C, mul_one]
  ring

end Finset

namespace TauCeti

/-- **Zero estimate for real exponential polynomials** (Evertse, Lemma 4.23). Let `s` be a
nonempty finite index set, `γ` exponents that are pairwise distinct on `s`, and `p` nonzero real
polynomials. Then every finite set `Z` of zeros of `x ↦ ∑ₖ pₖ(x) exp(γₖ x)` has fewer than
`∑ₖ (deg pₖ + 1)` points. -/
theorem card_lt_of_sum_eval_mul_exp_eq_zero {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {γ : ι → ℝ} (hγ : Set.InjOn γ s) {p : ι → ℝ[X]} (hp : ∀ i ∈ s, p i ≠ 0) {Z : Finset ℝ}
    (hZ : ∀ x ∈ Z, ∑ i ∈ s, (p i).eval x * Real.exp (γ i * x) = 0) :
    #Z < ∑ i ∈ s, ((p i).natDegree + 1) := by
  classical
  -- Induction on the number of terms. Multiplying by `exp(-γₐ x)` does not change the zeros and
  -- makes the exponent of `pₐ` equal to `0`. Differentiating `deg pₐ + 1` times removes this
  -- term, while every other term `q(x) exp(δ x)` with `δ ≠ 0` becomes
  -- `((d/dx + δ) ^ (deg pₐ + 1) q)(x) exp(δ x)`, whose polynomial has the same degree as `q`.
  -- By Rolle's theorem each differentiation loses at most one zero.
  induction hs using Finset.Nonempty.cons_induction generalizing γ p Z with
  | singleton a =>
    -- A single term `p(x) exp(γ x)` vanishes exactly at the roots of `p`.
    have hpa := hp a (mem_singleton_self a)
    have hsub : Z ⊆ (p a).roots.toFinset := fun x hx ↦ by
      have := hZ x hx
      rw [sum_singleton, mul_eq_zero, or_iff_left (Real.exp_ne_zero _)] at this
      exact Multiset.mem_toFinset.2 ((mem_roots hpa).2 this)
    rw [sum_singleton]
    exact Nat.lt_succ_of_le ((card_le_card hsub).trans
      ((Multiset.toFinset_card_le _).trans (card_roots' _)))
  | cons a t hat _ ih =>
    simp only [Finset.mem_cons, forall_eq_or_imp] at hp
    have hγ' : Set.InjOn γ t := hγ.mono (by simp)
    -- Shift the exponents by `-γ a` and differentiate `N = deg p_a + 1` times.
    set δ : ι → ℝ := fun i ↦ γ i - γ a
    set D : ℝ → ℝ[X] → ℝ[X] := fun d r ↦ derivative r + C d * r
    set N := (p a).natDegree + 1
    set F : ℕ → ℝ → ℝ := fun n x ↦
      ∑ i ∈ cons a t hat, ((D (δ i))^[n] (p i)).eval x * Real.exp (δ i * x)
    have hF : ∀ n < N, ∀ x, HasDerivAt (F n) (F (n + 1) x) x := fun n _ x ↦ by
      simpa only [F, Function.iterate_succ_apply'] using
        (cons a t hat).hasDerivAt_sum_eval_mul_exp δ (fun i ↦ (D (δ i))^[n] (p i)) x
    have hF₀ : ∀ x ∈ Z, F 0 x = 0 := fun x hx ↦ by
      have h : F 0 x = Real.exp (-(γ a * x)) *
          ∑ i ∈ cons a t hat, (p i).eval x * Real.exp (γ i * x) := by
        simp only [F, δ, Function.iterate_zero_apply, mul_sum]
        refine sum_congr rfl fun i _ ↦ ?_
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      rw [h, hZ x hx, mul_zero]
    obtain ⟨Z', hZ', hcard⟩ := exists_card_le_card_add_of_hasDerivAt hF hF₀
    -- The term of index `a` has exponent `0`, so it disappears after `N` differentiations.
    have hδ : ∀ i ∈ t, δ i ≠ 0 := fun i hi h ↦
      hat (hγ (by simp [hi]) (by simp) (sub_eq_zero.1 h) ▸ hi)
    have hDa : (D (δ a))^[N] (p a) = 0 := by
      simp only [D, δ, sub_self, map_zero, zero_mul, add_zero]
      exact iterate_derivative_eq_zero (Nat.lt_succ_self _)
    have hFN : ∀ x, F N x = ∑ i ∈ t, ((D (δ i))^[N] (p i)).eval x * Real.exp (δ i * x) :=
      fun x ↦ by simp only [F, sum_cons, hDa, eval_zero, zero_mul, zero_add]
    have hlt := ih (γ := δ) (fun i hi j hj h ↦ hγ' hi hj (sub_left_inj.1 h))
      (p := fun i ↦ (D (δ i))^[N] (p i))
      (fun i hi ↦ (iterate_derivative_add_C_mul_eq_zero_iff (hδ i hi) N).not.2 (hp.2 i hi))
      (fun x hx ↦ (hFN x).symm.trans (hZ' x hx))
    rw [sum_congr rfl fun i hi ↦ by
      rw [natDegree_iterate_derivative_add_C_mul (hδ i hi) N]] at hlt
    rw [sum_cons]
    omega

/-- The zero set of a real exponential polynomial `x ↦ ∑ₖ pₖ(x) exp(γₖ x)`, with nonzero
polynomials `pₖ` and exponents `γₖ` pairwise distinct on a nonempty finite index set, is
finite. -/
theorem finite_setOf_sum_eval_mul_exp_eq_zero {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {γ : ι → ℝ} (hγ : Set.InjOn γ s) {p : ι → ℝ[X]} (hp : ∀ i ∈ s, p i ≠ 0) :
    {x : ℝ | ∑ i ∈ s, (p i).eval x * Real.exp (γ i * x) = 0}.Finite := by
  by_contra h
  obtain ⟨Z, hZ, hcard⟩ := Set.Infinite.exists_subset_card_eq h (∑ i ∈ s, ((p i).natDegree + 1))
  exact (card_lt_of_sum_eval_mul_exp_eq_zero hs hγ hp fun x hx ↦ hZ hx).ne hcard

end TauCeti

/-! ### Complex exponential sums -/

namespace Finset

/-- The `k`-th derivative of the exponential sum `∑ᵢ cᵢ exp(ρᵢ z)` is `∑ᵢ cᵢ ρᵢᵏ exp(ρᵢ z)`. -/
@[simp]
theorem iteratedDeriv_sum_mul_cexp {ι : Type*} (s : Finset ι) (c ρ : ι → ℂ) (k : ℕ) :
    iteratedDeriv k (fun z ↦ ∑ i ∈ s, c i * Complex.exp (ρ i * z)) =
      fun z ↦ ∑ i ∈ s, c i * ρ i ^ k * Complex.exp (ρ i * z) := by
  funext z
  rw [iteratedDeriv_fun_sum fun i _ ↦ by fun_prop]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul, mul_assoc]

end Finset

namespace TauCeti

/-- Let the frequencies `ρ` be pairwise distinct on a finite set `s` of indices, and let the
coefficients `c` be nonzero somewhere on `s`. Then at every point `z₀` one of the first `#s`
derivatives of `z ↦ ∑ i ∈ s, c i * exp (ρ i * z)` is nonzero. -/
theorem exists_lt_card_iteratedDeriv_sum_mul_cexp_ne_zero {ι : Type*} {s : Finset ι}
    {ρ : ι → ℂ} (hρ : Set.InjOn ρ s) {c : ι → ℂ} (hc : ∃ i ∈ s, c i ≠ 0) (z₀ : ℂ) :
    ∃ k < #s, iteratedDeriv k (fun z ↦ ∑ i ∈ s, c i * Complex.exp (ρ i * z)) z₀ ≠ 0 := by
  obtain ⟨i, hi, hci⟩ := hc
  obtain ⟨k, hk, hne⟩ := exists_lt_card_sum_mul_pow_ne_zero (w := fun i ↦ c i *
    Complex.exp (ρ i * z₀)) hρ ⟨i, hi, mul_ne_zero hci (Complex.exp_ne_zero _)⟩
  refine ⟨k, hk, ?_⟩
  rw [s.iteratedDeriv_sum_mul_cexp]
  convert hne using 2 with i
  ring

/-- Let the frequencies `ρ` be pairwise distinct on a finite set `s` of indices, and let the
coefficients `c` be nonzero somewhere on `s`. Then the exponential sum
`z ↦ ∑ i ∈ s, c i * exp (ρ i * z)` vanishes to order less than `#s` at every point. In particular
it is not identically zero. -/
theorem analyticOrderAt_sum_mul_cexp_lt_card {ι : Type*} {s : Finset ι} {ρ : ι → ℂ}
    (hρ : Set.InjOn ρ s) {c : ι → ℂ} (hc : ∃ i ∈ s, c i ≠ 0) (z₀ : ℂ) :
    analyticOrderAt (fun z ↦ ∑ i ∈ s, c i * Complex.exp (ρ i * z)) z₀ < #s := by
  obtain ⟨k, hk, hne⟩ := exists_lt_card_iteratedDeriv_sum_mul_cexp_ne_zero hρ hc z₀
  by_contra! h
  have hE : AnalyticAt ℂ (fun z ↦ ∑ i ∈ s, c i * Complex.exp (ρ i * z)) z₀ := by fun_prop
  exact hne ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hE).1 h k hk)

end TauCeti

/-! ### Complex exponential polynomials -/

namespace Finset

/-- The derivative of the complex exponential polynomial `∑ᵢ pᵢ(z) exp(ρᵢ z)` is
`∑ᵢ (pᵢ' + ρᵢ pᵢ)(z) exp(ρᵢ z)`. -/
theorem hasDerivAt_sum_eval_mul_cexp {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (p : ι → ℂ[X]) (z : ℂ) :
    HasDerivAt (fun z ↦ ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z))
      (∑ i ∈ s, (derivative (p i) + C (ρ i) * p i).eval z * Complex.exp (ρ i * z)) z := by
  refine HasDerivAt.fun_sum fun i _ ↦ ?_
  refine (((p i).hasDerivAt z).fun_mul ((hasDerivAt_id' z).const_mul (ρ i)).cexp).congr_deriv ?_
  simp only [eval_add, eval_mul, eval_C, mul_one]
  ring

/-- The `k`-th derivative of `∑ᵢ pᵢ(z) exp(ρᵢ z)` applies `r ↦ r' + ρᵢ r` `k` times to each
coefficient polynomial `pᵢ`. -/
theorem iteratedDeriv_sum_eval_mul_cexp {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (p : ι → ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun z ↦ ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z)) =
      fun z ↦ ∑ i ∈ s, ((fun r ↦ derivative r + C (ρ i) * r)^[k] (p i)).eval z *
        Complex.exp (ρ i * z) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    simpa only [Function.iterate_succ_apply'] using
      (s.hasDerivAt_sum_eval_mul_cexp ρ
        (fun i ↦ (fun r ↦ derivative r + C (ρ i) * r)^[k] (p i)) z).deriv

end Finset

namespace TauCeti

/-- A finite complex exponential polynomial is analytic at every point `z₀ ∈ ℂ`. -/
private theorem analyticAt_sum_eval_mul_cexp {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (p : ι → ℂ[X]) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z ↦ ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z)) z₀ :=
  Finset.analyticAt_fun_sum _ fun i _ ↦
    (AnalyticOnNhd.eval_polynomial (p i) z₀ trivial).mul (by fun_prop)

/-- Multiplying an analytic function `g` by `exp(c z)` preserves the vanishing of all derivatives
up to any given order at `z₀`. -/
private theorem iteratedDeriv_eq_zero_of_forall_lt_mul_cexp {g : ℂ → ℂ} {c z₀ : ℂ}
    (hg : AnalyticAt ℂ g z₀) {M : ℕ}
    (h : ∀ k < M, iteratedDeriv k (fun z ↦ g z * Complex.exp (c * z)) z₀ = 0) :
    ∀ k < M, iteratedDeriv k g z₀ = 0 := by
  intro k hk
  have hge : g = fun z ↦ (g z * Complex.exp (c * z)) * Complex.exp (-c * z) := by
    funext z
    rw [mul_assoc, ← Complex.exp_add]
    simp
  rw [hge, iteratedDeriv_fun_mul ((hg.contDiffAt.of_le le_top).mul (by fun_prop)) (by fun_prop)]
  exact sum_eq_zero fun j hj ↦ by simp [h j ((mem_range_succ_iff.1 hj).trans_lt hk)]

/-- A nonzero complex polynomial `p` has a nonzero `(deg p)`-th derivative at every point `z₀`. -/
private theorem iteratedDeriv_natDegree_eval_ne_zero {p : ℂ[X]} (hp : p ≠ 0) (z₀ : ℂ) :
    iteratedDeriv p.natDegree (fun z ↦ p.eval z) z₀ ≠ 0 := by
  rw [p.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv, hasseDeriv_natDegree_eq_C, eval_C]
  exact mul_ne_zero (Nat.cast_ne_zero.2 p.natDegree.factorial_ne_zero) (leadingCoeff_ne_zero.2 hp)

/-- Factoring `exp(c z)` out of `∑ i ∈ s, pᵢ(z) exp(ρᵢ z)` shifts every frequency by `-c`. -/
private theorem sum_eval_mul_cexp_eq_sum_sub_mul_cexp {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (p : ι → ℂ[X]) (c : ℂ) :
    (fun z ↦ ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z)) =
      fun z ↦ (∑ i ∈ s, (p i).eval z * Complex.exp ((ρ i - c) * z)) * Complex.exp (c * z) := by
  funext z
  rw [sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2; ring

/-- Inductive core of `exists_lt_sum_iteratedDeriv_sum_eval_mul_cexp_ne_zero` when every
coefficient polynomial on the nonempty index set `s` is nonzero. -/
private theorem exists_lt_sum_iteratedDeriv_ne_zero_of_forall_ne_zero {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {ρ : ι → ℂ} (hρ : Set.InjOn ρ s) {p : ι → ℂ[X]}
    (hp : ∀ i ∈ s, p i ≠ 0) (z₀ : ℂ) :
    ∃ k < ∑ i ∈ s, ((p i).natDegree + 1),
      iteratedDeriv k (fun z ↦ ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z)) z₀ ≠ 0 := by
  classical
  by_contra! h
  induction hs using Finset.Nonempty.cons_induction generalizing ρ p with
  | singleton a =>
    have h0 := iteratedDeriv_eq_zero_of_forall_lt_mul_cexp
      (AnalyticOnNhd.eval_polynomial (p a) z₀ trivial) (c := ρ a) (M := (p a).natDegree + 1)
      (by simpa using h) (p a).natDegree (Nat.lt_succ_self _)
    exact iteratedDeriv_natDegree_eval_ne_zero (hp a (mem_singleton_self a)) z₀ h0
  | cons a t hat _ ih =>
    simp only [mem_cons, forall_eq_or_imp] at hp
    set δ : ι → ℂ := fun i ↦ ρ i - ρ a
    set D : ℂ → ℂ[X] → ℂ[X] := fun d r ↦ derivative r + C d * r
    set N := (p a).natDegree + 1
    set g : ℂ → ℂ := fun z ↦ ∑ i ∈ cons a t hat, (p i).eval z * Complex.exp (δ i * z)
    have hg0 := iteratedDeriv_eq_zero_of_forall_lt_mul_cexp
      (analyticAt_sum_eval_mul_cexp (cons a t hat) δ p z₀)
      (by rwa [← sum_eval_mul_cexp_eq_sum_sub_mul_cexp (cons a t hat) ρ p (ρ a)])
    have hDa : (D (δ a))^[N] (p a) = 0 := by
      simp only [D, δ, sub_self, map_zero, zero_mul, add_zero]
      exact iterate_derivative_eq_zero (Nat.lt_succ_self _)
    have hgN : iteratedDeriv N g =
        fun z ↦ ∑ i ∈ t, ((D (δ i))^[N] (p i)).eval z * Complex.exp (δ i * z) := by
      rw [(cons a t hat).iteratedDeriv_sum_eval_mul_cexp]
      funext z
      simp [D, hDa]
    have hδ : ∀ i ∈ t, δ i ≠ 0 := fun i hi h0 ↦
      hat (hρ (by simp [hi]) (by simp) (sub_eq_zero.1 h0) ▸ hi)
    refine ih (ρ := δ) (fun i hi j hj hij ↦ hρ.mono (by simp) hi hj (sub_left_inj.1 hij))
      (p := fun i ↦ (D (δ i))^[N] (p i))
      (fun i hi ↦ (iterate_derivative_add_C_mul_eq_zero_iff (hδ i hi) N).not.2 (hp.2 i hi))
      fun j hj ↦ ?_
    have hdeg : ∑ i ∈ t, (((D (δ i))^[N] (p i)).natDegree + 1) =
        ∑ i ∈ t, ((p i).natDegree + 1) :=
      sum_congr rfl fun i hi ↦ by rw [natDegree_iterate_derivative_add_C_mul (hδ i hi) N]
    rw [hdeg] at hj
    rw [← hgN, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, ← Function.iterate_add_apply,
      ← iteratedDeriv_eq_iterate]
    exact hg0 (j + N) (by rw [sum_cons]; omega)

/-- **Nonvanishing derivative bound for complex exponential polynomials.** If the frequencies `ρ`
are pairwise distinct on `s` and at least one coefficient polynomial `pᵢ` (`i ∈ s`) is nonzero,
then at every point `z₀ ∈ ℂ` one of the first `∑ i ∈ s, (deg pᵢ + 1)` derivatives of
`z ↦ ∑ i ∈ s, pᵢ(z) exp(ρᵢ z)` is nonzero. -/
theorem exists_lt_sum_iteratedDeriv_sum_eval_mul_cexp_ne_zero {ι : Type*} {s : Finset ι}
    {ρ : ι → ℂ} (hρ : Set.InjOn ρ s) {p : ι → ℂ[X]} (hp : ∃ i ∈ s, p i ≠ 0) (z₀ : ℂ) :
    ∃ k < ∑ i ∈ s, ((p i).natDegree + 1),
      iteratedDeriv k (fun z ↦ ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z)) z₀ ≠ 0 := by
  classical
  set s' := {i ∈ s | p i ≠ 0}
  obtain ⟨i₀, hi₀, hpi₀⟩ := hp
  have hs' : s'.Nonempty := ⟨i₀, mem_filter.2 ⟨hi₀, hpi₀⟩⟩
  have hsum : (fun z ↦ ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z)) =
      fun z ↦ ∑ i ∈ s', (p i).eval z * Complex.exp (ρ i * z) := by
    funext z
    refine (sum_subset (filter_subset _ _) fun i hi hnot ↦ ?_).symm
    have hpi : p i = 0 := by simpa [s', hi] using hnot
    simp [hpi]
  obtain ⟨k, hk, hne⟩ := exists_lt_sum_iteratedDeriv_ne_zero_of_forall_ne_zero hs'
    (hρ.mono (filter_subset _ _)) (fun i hi ↦ (mem_filter.1 hi).2) z₀
  exact ⟨k, hk.trans_le (sum_le_sum_of_subset (filter_subset _ _)), hsum ▸ hne⟩

/-- **Order of vanishing bound for complex exponential polynomials.** If `ρ` is injective on `s`
and `pᵢ ≠ 0` for some `i ∈ s`, then `z ↦ ∑ i ∈ s, pᵢ(z) exp(ρᵢ z)` vanishes at every point `z₀`
to order strictly less than `∑ i ∈ s, (deg pᵢ + 1)`. For constant coefficients this reduces to
`TauCeti.analyticOrderAt_sum_mul_cexp_lt_card`. -/
theorem analyticOrderAt_sum_eval_mul_cexp_lt {ι : Type*} {s : Finset ι} {ρ : ι → ℂ}
    (hρ : Set.InjOn ρ s) {p : ι → ℂ[X]} (hp : ∃ i ∈ s, p i ≠ 0) (z₀ : ℂ) :
    analyticOrderAt (fun z ↦ ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z)) z₀ <
      ↑(∑ i ∈ s, ((p i).natDegree + 1)) := by
  obtain ⟨k, hk, hne⟩ := exists_lt_sum_iteratedDeriv_sum_eval_mul_cexp_ne_zero hρ hp z₀
  by_contra! h
  exact hne ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (analyticAt_sum_eval_mul_cexp s ρ p z₀)).1 h k hk)

/-- A complex exponential polynomial `∑ i ∈ s, pᵢ(z) exp(ρᵢ z)` with `ρ` injective on `s` and at
least one nonzero `pᵢ` (`i ∈ s`) does not vanish identically on `ℂ`. -/
theorem exists_sum_eval_mul_cexp_ne_zero {ι : Type*} {s : Finset ι} {ρ : ι → ℂ}
    (hρ : Set.InjOn ρ s) {p : ι → ℂ[X]} (hp : ∃ i ∈ s, p i ≠ 0) :
    ∃ z : ℂ, ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z) ≠ 0 := by
  by_contra! h
  have htop : analyticOrderAt (fun z ↦ ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z)) 0 = ⊤ :=
    analyticOrderAt_eq_top.2 (Filter.Eventually.of_forall h)
  exact (analyticOrderAt_sum_eval_mul_cexp_lt hρ hp 0).ne_top htop

/-- If `∑ i ∈ s, pᵢ(z) exp(ρᵢ z) = 0` for all `z ∈ ℂ` and `ρ` is injective on `s`, then every
coefficient polynomial `pᵢ` (`i ∈ s`) is zero. -/
theorem eq_zero_of_sum_eval_mul_cexp_eq_zero {ι : Type*} {s : Finset ι} {ρ : ι → ℂ}
    (hρ : Set.InjOn ρ s) {p : ι → ℂ[X]}
    (h : ∀ z : ℂ, ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z) = 0) :
    ∀ i ∈ s, p i = 0 := by
  by_contra! hp
  obtain ⟨z, hz⟩ := exists_sum_eval_mul_cexp_ne_zero hρ hp
  exact hz (h z)

/-- For `ρ` injective on `s`, the exponential polynomial `∑ i ∈ s, pᵢ(z) exp(ρᵢ z)` vanishes
everywhere on `ℂ` if and only if `pᵢ = 0` for all `i ∈ s`. -/
theorem sum_eval_mul_cexp_eq_zero_iff {ι : Type*} {s : Finset ι} {ρ : ι → ℂ}
    (hρ : Set.InjOn ρ s) {p : ι → ℂ[X]} :
    (∀ z : ℂ, ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z) = 0) ↔ ∀ i ∈ s, p i = 0 :=
  ⟨eq_zero_of_sum_eval_mul_cexp_eq_zero hρ, fun hp z ↦ sum_eq_zero fun i hi ↦ by simp [hp i hi]⟩

/-- **Uniqueness of polynomial coefficients** on `s` in a complex exponential polynomial with `ρ`
injective on `s`. -/
theorem sum_eval_mul_cexp_eq_iff {ι : Type*} {s : Finset ι} {ρ : ι → ℂ}
    (hρ : Set.InjOn ρ s) {p q : ι → ℂ[X]} :
    (∀ z : ℂ, ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z) =
      ∑ i ∈ s, (q i).eval z * Complex.exp (ρ i * z)) ↔ ∀ i ∈ s, p i = q i := by
  refine ⟨fun h ↦ ?_, fun h z ↦ sum_congr rfl fun i hi ↦ by rw [h i hi]⟩
  have hz : ∀ z : ℂ, ∑ i ∈ s, (p i - q i).eval z * Complex.exp (ρ i * z) = 0 := fun z ↦ by
    simp only [eval_sub, sub_mul, sum_sub_distrib, h z, sub_self]
  exact fun i hi ↦ sub_eq_zero.1 (eq_zero_of_sum_eval_mul_cexp_eq_zero hρ hz i hi)

/-- **Linear independence of univariate exponential monomials.** For an injective family of complex
frequencies `ρ : ι → ℂ`, the functions `z ↦ z ^ k exp(ρᵢ z)` (`(i, k) : ι × ℕ`) are linearly
independent over `ℂ`. -/
theorem linearIndependent_pow_mul_cexp {ι : Type*} {ρ : ι → ℂ} (hρ : Function.Injective ρ) :
    LinearIndependent ℂ (fun ik : ι × ℕ ↦ fun z : ℂ ↦ z ^ ik.2 * Complex.exp (ρ ik.1 * z)) := by
  classical
  refine linearIndependent_iff'.2 fun t g hg ik₀ hik₀ ↦ ?_
  set s : Finset ι := t.image Prod.fst
  set p : ι → ℂ[X] := fun i ↦ ∑ ik ∈ t with ik.1 = i, monomial ik.2 (g ik) with hp_def
  have hsum : ∀ z : ℂ, ∑ i ∈ s, (p i).eval z * Complex.exp (ρ i * z) = 0 := fun z ↦ by
    have hz := congrFun hg z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
    rw [← hz, ← sum_fiberwise_of_maps_to (g := Prod.fst) (fun ik hik ↦ mem_image_of_mem _ hik)]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [hp_def, eval_finsetSum, eval_monomial, sum_mul]
    refine sum_congr rfl fun ik hik ↦ ?_
    rw [(mem_filter.1 hik).2, mul_assoc]
  have hp0 := eq_zero_of_sum_eval_mul_cexp_eq_zero hρ.injOn hsum ik₀.1 (mem_image_of_mem _ hik₀)
  have hc := congrArg (fun q ↦ q.coeff ik₀.2) hp0
  simp only [hp_def, finsetSum_coeff, coeff_monomial_apply, coeff_zero] at hc
  rw [sum_eq_single_of_mem ik₀ (s := {ik ∈ t | ik.1 = ik₀.1}) (mem_filter.2 ⟨hik₀, rfl⟩)] at hc
  · simpa using hc
  · intro ik hik hne
    rw [ite_eq_right_iff]
    intro hk
    exact absurd (Prod.ext (mem_filter.1 hik).2 hk) hne

end TauCeti
