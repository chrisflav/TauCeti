/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Analysis.SpecialFunctions.Exp.ExponentialPolynomial.Basic

import Mathlib.Algebra.MvPolynomial.Funext
import TauCeti.RingTheory.MvPolynomial.Homogeneous
import TauCeti.RingTheory.MvPolynomial.LineRestriction

/-!
# Linear independence of multivariate complex exponential polynomials

Let `σ` be a finite coordinate type, `w₁, …, wᵣ ∈ ℂ^σ` pairwise distinct frequency vectors, and
`p₁, …, pᵣ ∈ MvPolynomial σ ℂ` multivariate polynomials, not all zero. This file shows that the
entire function

`F(z) = ∑ i ∈ s, pᵢ(z) exp(wᵢ · z)`

does not vanish identically on `ℂ^σ`. More precisely, there exists a single complex direction
`u ∈ ℂ^σ` such that the projected frequencies `wᵢ · u` are pairwise distinct on `s` and the top
homogeneous component of every nonzero `pᵢ` does not vanish at `u`: both conditions are defined by
finitely many nonzero polynomials in `MvPolynomial σ ℂ`, whose product cannot vanish identically on
`ℂ^σ`. Along the affine complex line `ζ ↦ z₀ + ζ • u` through any basepoint `z₀ ∈ ℂ^σ`, each
summand `pᵢ(z₀ + ζ • u) exp(wᵢ · (z₀ + ζ • u))` restricts to a univariate exponential polynomial
of the same polynomial degree `totalDegree (pᵢ)`, so the univariate order bound of
`TauCeti.Analysis.SpecialFunctions.Exp.ExponentialPolynomial.Basic` gives

`analyticOrderAt (fun ζ ↦ F(z₀ + ζ • u)) 0 < ∑ i ∈ s, (totalDegree (pᵢ) + 1)`.

In particular `F` is not identically zero, its multivariate polynomial coefficients over pairwise
distinct frequencies are unique, and for an injective family `w : ι → σ → ℂ` the exponential
monomials `z ↦ (∏ ν, z ν ^ τ ν) exp(wᵢ · z)` (`(i, τ) : ι × (σ → ℕ)`) are linearly independent
over `ℂ`.

## Main results

* `TauCeti.exists_injOn_dotProduct_and_eval_homogeneousComponent_ne_zero`: over any infinite
  integral domain `R`, simultaneous existence of a direction `u : σ → R` separating finitely many
  vectors under `⬝ᵥ u` and keeping the top homogeneous components of finitely many nonzero
  polynomials nonzero.
* `TauCeti.exists_forall_lt_sum_iteratedDeriv_mvPolynomial_eval_mul_cexp_line_ne_zero`,
  `TauCeti.exists_forall_analyticOrderAt_sum_mvPolynomial_eval_mul_cexp_line_lt`: existence of a
  direction `u` along which, at every basepoint `z₀ ∈ ℂ^σ`, the affine line slice
  `ζ ↦ F(z₀ + ζ • u)` vanishes at `0` to order strictly less than `∑ i ∈ s, (totalDegree (pᵢ) + 1)`.
* `TauCeti.exists_sum_mvPolynomial_eval_mul_cexp_ne_zero`: if `w` is injective on `s` and some
  `pᵢ` (`i ∈ s`) is nonzero, then `z ↦ ∑ i ∈ s, pᵢ(z) exp(wᵢ · z)` is not identically zero.
* `TauCeti.eq_zero_of_sum_mvPolynomial_eval_mul_cexp_eq_zero`,
  `TauCeti.sum_mvPolynomial_eval_mul_cexp_eq_zero_iff`,
  `TauCeti.sum_mvPolynomial_eval_mul_cexp_eq_iff`: vanishing characterization and uniqueness of
  multivariate polynomial coefficients over pairwise distinct frequencies.
* `TauCeti.linearIndependent_prod_pow_mul_cexp`: linear independence over `ℂ` of the multivariate
  exponential monomials `z ↦ (∏ ν, z ν ^ τ ν) exp(wᵢ · z)` for injective `w`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000), ch. 4.
-/

public section

open Finset MvPolynomial
open scoped Polynomial

namespace TauCeti

section Direction

variable {σ R : Type*} [Fintype σ] [CommRing R]

/-- Evaluating `∑ ν, v ν * X ν` at `u : σ → R` computes the dot product `v ⬝ᵥ u`. -/
private theorem eval_sum_C_mul_X (v u : σ → R) :
    eval u (∑ ν : σ, C (v ν) * X ν : MvPolynomial σ R) = v ⬝ᵥ u := by
  simp [dotProduct]

/-- Over a commutative ring, a nonzero vector `v : σ → R` defines a nonzero homogeneous linear form
`∑ ν, v ν * X ν ∈ MvPolynomial σ R`. -/
private theorem sum_C_mul_X_ne_zero {v : σ → R} (hv : v ≠ 0) :
    (∑ ν : σ, C (v ν) * X ν : MvPolynomial σ R) ≠ 0 := by
  classical
  obtain ⟨ν₀, hν₀⟩ := Function.ne_iff.1 hv
  intro h0
  have hev := congrArg (eval (Pi.single ν₀ 1)) h0
  rw [eval_sum_C_mul_X, dotProduct_single_one, map_zero] at hev
  exact hν₀ hev

/-- Over an infinite integral domain `R` and finite coordinate type `σ`, given a finite index set
`s`, vectors `w : ι → σ → R` pairwise distinct on `s`, and polynomials `p : ι → MvPolynomial σ R`,
there exists a direction `u : σ → R` such that `i ↦ w i ⬝ᵥ u` is injective on `s` and the top
homogeneous component of every nonzero `p i` (`i ∈ s`) does not vanish at `u`. -/
theorem exists_injOn_dotProduct_and_eval_homogeneousComponent_ne_zero [IsDomain R] [Infinite R]
    {ι : Type*} {s : Finset ι} {w : ι → σ → R} (hw : Set.InjOn w s) (p : ι → MvPolynomial σ R) :
    ∃ u : σ → R, Set.InjOn (fun i ↦ w i ⬝ᵥ u) s ∧
      ∀ i ∈ s, p i ≠ 0 → eval u (homogeneousComponent (p i).totalDegree (p i)) ≠ 0 := by
  classical
  let H (i : ι) : MvPolynomial σ R :=
    if p i = 0 then 1 else homogeneousComponent (p i).totalDegree (p i)
  let pairs : Finset (ι × ι) := (s ×ˢ s).filter fun ij ↦ ij.1 ≠ ij.2
  let L (ij : ι × ι) : MvPolynomial σ R := ∑ ν : σ, C ((w ij.1 - w ij.2) ν) * X ν
  have hH : ∀ i ∈ s, H i ≠ 0 := fun i _ ↦ by
    by_cases hpi : p i = 0
    · simp [H, hpi]
    · simpa [H, hpi] using (p i).homogeneousComponent_totalDegree_ne_zero hpi
  have hL : ∀ ij ∈ pairs, L ij ≠ 0 := fun ij hij ↦ by
    obtain ⟨hij', hne⟩ := mem_filter.1 hij
    obtain ⟨hi, hj⟩ := mem_product.1 hij'
    exact sum_C_mul_X_ne_zero (sub_ne_zero.2 fun heq ↦ hne (hw hi hj heq))
  have hQ : (∏ i ∈ s, H i) * (∏ ij ∈ pairs, L ij) ≠ 0 :=
    mul_ne_zero (prod_ne_zero_iff.2 hH) (prod_ne_zero_iff.2 hL)
  obtain ⟨u, hu⟩ : ∃ u : σ → R, eval u ((∏ i ∈ s, H i) * (∏ ij ∈ pairs, L ij)) ≠ 0 := by
    by_contra! hall
    exact hQ (MvPolynomial.funext hall)
  rw [map_mul, map_prod, map_prod, mul_ne_zero_iff, prod_ne_zero_iff, prod_ne_zero_iff] at hu
  refine ⟨u, fun i hi j hj hij ↦ ?_, fun i hi hpi ↦ ?_⟩
  · by_contra hne
    have hmem : (i, j) ∈ pairs := mem_filter.2 ⟨mem_product.2 ⟨hi, hj⟩, hne⟩
    have hlu := hu.2 (i, j) hmem
    rw [eval_sum_C_mul_X, sub_dotProduct, sub_ne_zero] at hlu
    exact hlu hij
  · simpa [H, hpi] using hu.1 i hi

end Direction

section Complex

variable {σ : Type*} [Fintype σ]

/-- Restricting `z ↦ p(z) exp(w · z)` to the affine complex line `ζ ↦ z₀ + ζ • u` produces a
univariate exponential polynomial of frequency `w ⬝ᵥ u` whose polynomial factor has degree at most
`totalDegree p`, and is nonzero whenever the top homogeneous component of `p` does not vanish at
`u`. -/
private noncomputable def affineLinePoly (w z₀ u : σ → ℂ) (p : MvPolynomial σ ℂ) : ℂ[X] :=
  Polynomial.C (Complex.exp (w ⬝ᵥ z₀)) *
    aeval (fun ν ↦ Polynomial.C (z₀ ν) + Polynomial.C (u ν) * Polynomial.X) p

private theorem eval_affineLinePoly_mul_cexp (w z₀ u : σ → ℂ) (p : MvPolynomial σ ℂ) (ζ : ℂ) :
    (affineLinePoly w z₀ u p).eval ζ * Complex.exp ((w ⬝ᵥ u) * ζ) =
      eval (z₀ + ζ • u) p * Complex.exp (w ⬝ᵥ (z₀ + ζ • u)) := by
  rw [affineLinePoly, Polynomial.eval_mul, Polynomial.eval_C, eval_aeval_C_add_C_mul_X,
    dotProduct_add, dotProduct_smul, smul_eq_mul, Complex.exp_add]
  ring_nf

private theorem natDegree_affineLinePoly_le (w z₀ u : σ → ℂ) (p : MvPolynomial σ ℂ) :
    (affineLinePoly w z₀ u p).natDegree ≤ p.totalDegree :=
  (Polynomial.natDegree_C_mul_le _ _).trans <| by
    simpa only [aeval_def, Polynomial.algebraMap_eq, RingHom.comp_id, coe_eval₂Hom] using
      p.natDegree_eval₂_C_add_C_mul_X_le (RingHom.id ℂ) z₀ u

private theorem affineLinePoly_ne_zero (w z₀ u : σ → ℂ) {p : MvPolynomial σ ℂ}
    (hu : eval u (homogeneousComponent p.totalDegree p) ≠ 0) :
    affineLinePoly w z₀ u p ≠ 0 := by
  refine mul_ne_zero (Polynomial.C_ne_zero.2 (Complex.exp_ne_zero _)) fun h0 ↦ hu ?_
  have hc := congrArg (fun q : ℂ[X] ↦ q.coeff p.totalDegree) h0
  have htop := p.coeff_eval₂_C_add_C_mul_X_of_totalDegree_le (RingHom.id ℂ) z₀ u le_rfl
  simp only [aeval_def, Polynomial.algebraMap_eq, RingHom.comp_id, eval₂_id] at hc htop
  exact htop.symm.trans hc

variable {ι : Type*}

/-- **Uniform directional derivative bound for multivariate complex exponential polynomials.** For
finite `σ`, if `w` is injective on `s` and some `pᵢ` (`i ∈ s`) is nonzero, there exists a single
direction `u ∈ ℂ^σ` such that at every basepoint `z₀ ∈ ℂ^σ` one of the first
`∑ i ∈ s, (totalDegree (pᵢ) + 1)` derivatives at `0` of the line slice
`ζ ↦ ∑ i ∈ s, pᵢ(z₀ + ζ • u) exp(wᵢ · (z₀ + ζ • u))` is nonzero. -/
theorem exists_forall_lt_sum_iteratedDeriv_mvPolynomial_eval_mul_cexp_line_ne_zero
    {s : Finset ι} {w : ι → σ → ℂ} (hw : Set.InjOn w s) {p : ι → MvPolynomial σ ℂ}
    (hp : ∃ i ∈ s, p i ≠ 0) :
    ∃ u : σ → ℂ, ∀ z₀ : σ → ℂ, ∃ k < ∑ i ∈ s, ((p i).totalDegree + 1),
      iteratedDeriv k (fun ζ : ℂ ↦
        ∑ i ∈ s, eval (z₀ + ζ • u) (p i) * Complex.exp (w i ⬝ᵥ (z₀ + ζ • u))) 0 ≠ 0 := by
  obtain ⟨u, hwu, hpu⟩ := exists_injOn_dotProduct_and_eval_homogeneousComponent_ne_zero hw p
  obtain ⟨i₀, hi₀, hpi₀⟩ := hp
  refine ⟨u, fun z₀ ↦ ?_⟩
  have hslice : (fun ζ : ℂ ↦ ∑ i ∈ s, eval (z₀ + ζ • u) (p i) * Complex.exp (w i ⬝ᵥ (z₀ + ζ • u))) =
      fun ζ : ℂ ↦ ∑ i ∈ s, (affineLinePoly (w i) z₀ u (p i)).eval ζ *
        Complex.exp ((w i ⬝ᵥ u) * ζ) := by
    funext ζ
    exact sum_congr rfl fun i _ ↦ (eval_affineLinePoly_mul_cexp (w i) z₀ u (p i) ζ).symm
  obtain ⟨k, hk, hne⟩ := exists_lt_sum_iteratedDeriv_sum_eval_mul_cexp_ne_zero hwu
    (p := fun i ↦ affineLinePoly (w i) z₀ u (p i))
    ⟨i₀, hi₀, affineLinePoly_ne_zero (w i₀) z₀ u (hpu i₀ hi₀ hpi₀)⟩ 0
  refine ⟨k, hk.trans_le (sum_le_sum fun i _ ↦ ?_), hslice ▸ hne⟩
  exact Nat.add_le_add_right (natDegree_affineLinePoly_le (w i) z₀ u (p i)) 1

/-- **Uniform directional order bound for multivariate complex exponential polynomials.** Under the
hypotheses of `exists_forall_lt_sum_iteratedDeriv_mvPolynomial_eval_mul_cexp_line_ne_zero`, there
exists a direction `u ∈ ℂ^σ` along which, at every basepoint `z₀ ∈ ℂ^σ`, the affine line slice
`ζ ↦ ∑ i ∈ s, pᵢ(z₀ + ζ • u) exp(wᵢ · (z₀ + ζ • u))` vanishes at `0` to analytic order strictly
less than `∑ i ∈ s, (totalDegree (pᵢ) + 1)`. -/
theorem exists_forall_analyticOrderAt_sum_mvPolynomial_eval_mul_cexp_line_lt
    {s : Finset ι} {w : ι → σ → ℂ} (hw : Set.InjOn w s) {p : ι → MvPolynomial σ ℂ}
    (hp : ∃ i ∈ s, p i ≠ 0) :
    ∃ u : σ → ℂ, ∀ z₀ : σ → ℂ,
      analyticOrderAt (fun ζ : ℂ ↦
        ∑ i ∈ s, eval (z₀ + ζ • u) (p i) * Complex.exp (w i ⬝ᵥ (z₀ + ζ • u))) 0 <
          ↑(∑ i ∈ s, ((p i).totalDegree + 1)) := by
  obtain ⟨u, hwu, hpu⟩ := exists_injOn_dotProduct_and_eval_homogeneousComponent_ne_zero hw p
  obtain ⟨i₀, hi₀, hpi₀⟩ := hp
  refine ⟨u, fun z₀ ↦ ?_⟩
  have hslice : (fun ζ : ℂ ↦ ∑ i ∈ s, eval (z₀ + ζ • u) (p i) * Complex.exp (w i ⬝ᵥ (z₀ + ζ • u))) =
      fun ζ : ℂ ↦ ∑ i ∈ s, (affineLinePoly (w i) z₀ u (p i)).eval ζ *
        Complex.exp ((w i ⬝ᵥ u) * ζ) := by
    funext ζ
    exact sum_congr rfl fun i _ ↦ (eval_affineLinePoly_mul_cexp (w i) z₀ u (p i) ζ).symm
  rw [hslice]
  refine (analyticOrderAt_sum_eval_mul_cexp_lt hwu
    ⟨i₀, hi₀, affineLinePoly_ne_zero (w i₀) z₀ u (hpu i₀ hi₀ hpi₀)⟩ 0).trans_le ?_
  exact_mod_cast sum_le_sum fun i _ ↦
    Nat.add_le_add_right (natDegree_affineLinePoly_le (w i) z₀ u (p i)) 1

/-- **Nonvanishing of multivariate complex exponential polynomials.** For finite `σ`, pairwise
distinct frequency vectors `wᵢ ∈ ℂ^σ` (`i ∈ s`), and polynomials `pᵢ ∈ MvPolynomial σ ℂ` not all
zero on `s`, the function `z ↦ ∑ i ∈ s, pᵢ(z) exp(wᵢ · z)` is not identically zero on `ℂ^σ`. -/
theorem exists_sum_mvPolynomial_eval_mul_cexp_ne_zero {s : Finset ι} {w : ι → σ → ℂ}
    (hw : Set.InjOn w s) {p : ι → MvPolynomial σ ℂ} (hp : ∃ i ∈ s, p i ≠ 0) :
    ∃ z : σ → ℂ, ∑ i ∈ s, eval z (p i) * Complex.exp (w i ⬝ᵥ z) ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_forall_analyticOrderAt_sum_mvPolynomial_eval_mul_cexp_line_lt hw hp
  by_contra! hall
  have htop : analyticOrderAt (fun ζ : ℂ ↦
      ∑ i ∈ s, eval (0 + ζ • u) (p i) * Complex.exp (w i ⬝ᵥ (0 + ζ • u))) 0 = ⊤ :=
    analyticOrderAt_eq_top.2 (Filter.Eventually.of_forall fun ζ ↦ hall (0 + ζ • u))
  exact (hu 0).ne_top htop

/-- For finite `σ`, if `∑ i ∈ s, pᵢ(z) exp(wᵢ · z) = 0` for all `z ∈ ℂ^σ` and `w` is injective on
`s`, then `pᵢ = 0` for all `i ∈ s`. -/
theorem eq_zero_of_sum_mvPolynomial_eval_mul_cexp_eq_zero {s : Finset ι} {w : ι → σ → ℂ}
    (hw : Set.InjOn w s) {p : ι → MvPolynomial σ ℂ}
    (h : ∀ z : σ → ℂ, ∑ i ∈ s, eval z (p i) * Complex.exp (w i ⬝ᵥ z) = 0) :
    ∀ i ∈ s, p i = 0 := by
  by_contra! hp
  obtain ⟨z, hz⟩ := exists_sum_mvPolynomial_eval_mul_cexp_ne_zero hw hp
  exact hz (h z)

/-- For finite `σ` and `w` injective on `s`, the multivariate exponential polynomial
`∑ i ∈ s, pᵢ(z) exp(wᵢ · z)` vanishes everywhere on `ℂ^σ` if and only if `pᵢ = 0` for all
`i ∈ s`. -/
theorem sum_mvPolynomial_eval_mul_cexp_eq_zero_iff {s : Finset ι} {w : ι → σ → ℂ}
    (hw : Set.InjOn w s) {p : ι → MvPolynomial σ ℂ} :
    (∀ z : σ → ℂ, ∑ i ∈ s, eval z (p i) * Complex.exp (w i ⬝ᵥ z) = 0) ↔ ∀ i ∈ s, p i = 0 :=
  ⟨eq_zero_of_sum_mvPolynomial_eval_mul_cexp_eq_zero hw,
    fun hp z ↦ sum_eq_zero fun i hi ↦ by simp [hp i hi]⟩

/-- **Uniqueness of multivariate polynomial coefficients** on `s` in a complex exponential
polynomial over `ℂ^σ` (`σ` finite) with `w` injective on `s`. -/
theorem sum_mvPolynomial_eval_mul_cexp_eq_iff {s : Finset ι} {w : ι → σ → ℂ}
    (hw : Set.InjOn w s) {p q : ι → MvPolynomial σ ℂ} :
    (∀ z : σ → ℂ, ∑ i ∈ s, eval z (p i) * Complex.exp (w i ⬝ᵥ z) =
      ∑ i ∈ s, eval z (q i) * Complex.exp (w i ⬝ᵥ z)) ↔ ∀ i ∈ s, p i = q i := by
  refine ⟨fun h ↦ ?_, fun h z ↦ sum_congr rfl fun i hi ↦ by rw [h i hi]⟩
  have hz : ∀ z : σ → ℂ, ∑ i ∈ s, eval z (p i - q i) * Complex.exp (w i ⬝ᵥ z) = 0 := fun z ↦ by
    simp only [map_sub, sub_mul, sum_sub_distrib, h z, sub_self]
  exact fun i hi ↦ sub_eq_zero.1 (eq_zero_of_sum_mvPolynomial_eval_mul_cexp_eq_zero hw hz i hi)

/-- **Linear independence of multivariate exponential monomials.** For a finite coordinate type `σ`
and an injective family of frequency vectors `w : ι → σ → ℂ`, the entire functions
`z ↦ (∏ ν, z ν ^ τ ν) exp(wᵢ · z)` (`(i, τ) : ι × (σ → ℕ)`) are linearly independent over `ℂ`. -/
theorem linearIndependent_prod_pow_mul_cexp {w : ι → σ → ℂ} (hw : Function.Injective w) :
    LinearIndependent ℂ
      (fun iτ : ι × (σ → ℕ) ↦ fun z : σ → ℂ ↦ (∏ ν, z ν ^ iτ.2 ν) * Complex.exp (w iτ.1 ⬝ᵥ z)) := by
  classical
  refine linearIndependent_iff'.2 fun t g hg iτ₀ hiτ₀ ↦ ?_
  set s : Finset ι := t.image Prod.fst
  let e : (σ → ℕ) ≃ (σ →₀ ℕ) := Finsupp.equivFunOnFinite.symm
  set p : ι → MvPolynomial σ ℂ := fun i ↦ ∑ iτ ∈ t with iτ.1 = i, monomial (e iτ.2) (g iτ)
    with hp_def
  have hmon (τ : σ → ℕ) (c : ℂ) (z : σ → ℂ) :
      eval z (monomial (e τ) c) = c * ∏ ν, z ν ^ τ ν := by
    rw [eval_monomial]
    congr 1
    exact Finsupp.prod_of_support_subset (e τ) (subset_univ _) (fun ν n ↦ z ν ^ n)
      (fun _ _ ↦ pow_zero _)
  have hsum : ∀ z : σ → ℂ, ∑ i ∈ s, eval z (p i) * Complex.exp (w i ⬝ᵥ z) = 0 := fun z ↦ by
    have hz := congrFun hg z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
    rw [← hz, ← sum_fiberwise_of_maps_to (g := Prod.fst) (fun iτ hiτ ↦ mem_image_of_mem _ hiτ)]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [hp_def, map_sum, hmon, sum_mul]
    refine sum_congr rfl fun iτ hiτ ↦ ?_
    rw [(mem_filter.1 hiτ).2, mul_assoc]
  have hp0 := eq_zero_of_sum_mvPolynomial_eval_mul_cexp_eq_zero hw.injOn hsum iτ₀.1
    (mem_image_of_mem _ hiτ₀)
  have hc := congrArg (fun q ↦ q.coeff (e iτ₀.2)) hp0
  simp only [hp_def, coeff_sum, coeff_monomial, AddMonoidAlgebra.coeff_zero] at hc
  rw [sum_eq_single_of_mem iτ₀ (s := {iτ ∈ t | iτ.1 = iτ₀.1}) (mem_filter.2 ⟨hiτ₀, rfl⟩)] at hc
  · simpa using hc
  · intro iτ hiτ hne
    rw [ite_eq_right_iff]
    intro hk
    exact absurd (Prod.ext (mem_filter.1 hiτ).2 (e.injective hk)) hne

end Complex

end TauCeti
