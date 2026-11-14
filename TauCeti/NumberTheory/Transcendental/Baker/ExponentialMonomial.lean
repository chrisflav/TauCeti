/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import TauCeti.NumberTheory.Transcendental.Baker.MDeriv

import Mathlib.LinearAlgebra.LinearIndependent.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.ExponentialPolynomial.MvPolynomial

/-!
# Linear independence of Schneider–Lang and Baker exponential monomials

In Waldschmidt's several-variable transcendence constructions (the Schneider–Lang criterion and
Baker's theorem on linear forms in logarithms), the auxiliary entire function on `ℂ^σ` is an
integer linear combination of the exponential monomials

`φ_{τ, t}(z) = (∏ ν, z ν ^ τ ν) exp((∑ i, t i • x i) · z)`,

where `x₁, …, x_{d₁} ∈ ℂ^σ` are linearly independent over `ℚ` (or, more generally, over a scalar
semiring `R` acting on `ℂ^σ`). By `linearIndependent_iff_injective_fintypeLinearCombination`,
`R`-linear independence of `x` makes `t ↦ ∑ i, t i • x i` injective on `κ → R`, so the frequency
vectors `∑ i, t i • x i` are pairwise distinct, and the multivariate exponential polynomial
independence results of `TauCeti.Analysis.SpecialFunctions.Exp.ExponentialPolynomial.MvPolynomial`
imply that the family `φ_{τ, t}` is linearly independent over `ℂ`.

Consequently, any finite linear combination `F(z) = ∑ a ∈ s, c a * φ_{p a}(z)` with pairwise
distinct multi-indices `p a` and coefficients `c a` (in `ℂ` or in `ℤ`) not all zero on `s` defines
a nonzero entire function `F`, and by the identity principle for mixed partial derivatives
(`TauCeti.Baker.exists_mDeriv_ne_zero`) has at every point `z₀ ∈ ℂⁿ` some mixed partial derivative
`D^σ F(z₀) ≠ 0`.

## Main results

* `TauCeti.Baker.linearIndependent_monomial_mul_cexp_smul`,
  `TauCeti.Baker.linearIndependent_monomial_mul_cexp_zsmul`,
  `TauCeti.Baker.linearIndependent_monomial_mul_cexp_nsmul`: linear independence over `ℂ` of the
  exponential monomials `z ↦ (∏ ν, z ν ^ τ ν) exp((∑ i, t i • x i) · z)` for `R`-independent `x`
  (and in particular for `ℚ`-independent `x` with `ℤ`- or `ℕ`-exponents `t`).
* `TauCeti.Baker.sum_mul_monomial_mul_cexp_smul_eq_zero_iff`,
  `TauCeti.Baker.exists_sum_mul_monomial_mul_cexp_smul_ne_zero`: nontrivial finite linear
  combinations of distinct exponential monomials do not vanish identically.
* `TauCeti.Baker.exists_mDeriv_sum_mul_monomial_mul_cexp_smul_ne_zero`,
  `TauCeti.Baker.exists_mDeriv_sum_mul_monomial_mul_cexp_zsmul_ne_zero`,
  `TauCeti.Baker.exists_mDeriv_sum_intCast_mul_monomial_mul_cexp_nsmul_ne_zero`: at every point
  `z₀ ∈ ℂⁿ`, a nontrivial finite linear combination of Schneider–Lang exponential monomials has a
  nonzero mixed partial derivative `D^σ F(z₀) ≠ 0`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §§4.4–4.6.
-/

public section

open Finset Function

namespace TauCeti.Baker

section LinearIndependence

variable {κ σ R : Type*} [Fintype κ] [Fintype σ]

/-- **Linear independence of exponential monomials.** For finite `κ` and `σ`, any scalar semiring
`R` acting on `ℂ^σ`, and any `R`-linearly independent family `x : κ → σ → ℂ`, the entire functions
`z ↦ (∏ ν, z ν ^ τ ν) exp((∑ i, t i • x i) · z)` (`(τ, t) : (σ → ℕ) × (κ → R)`) are linearly
independent over `ℂ`. -/
theorem linearIndependent_monomial_mul_cexp_smul [Semiring R] [Module R (σ → ℂ)] {x : κ → σ → ℂ}
    (hx : LinearIndependent R x) :
    LinearIndependent ℂ (fun p : (σ → ℕ) × (κ → R) ↦ fun z : σ → ℂ ↦
      (∏ ν, z ν ^ p.1 ν) * Complex.exp ((∑ i, p.2 i • x i) ⬝ᵥ z)) := by
  have hinj : Injective (fun t : κ → R ↦ ∑ i, t i • x i) := by
    simpa [Function.Injective, Fintype.linearCombination_apply] using
      linearIndependent_iff_injective_fintypeLinearCombination.1 hx
  exact (TauCeti.linearIndependent_prod_pow_mul_cexp hinj).comp
    (Equiv.prodComm (σ → ℕ) (κ → R)) (Equiv.injective _)

/-- **Linear independence of integer-grid exponential monomials.** For finite `κ` and `σ`, if
`x : κ → σ → ℂ` is linearly independent over `ℚ`, then the entire functions
`z ↦ (∏ ν, z ν ^ τ ν) exp((∑ i, t i • x i) · z)` (`(τ, t) : (σ → ℕ) × (κ → ℤ)`) are linearly
independent over `ℂ`. -/
theorem linearIndependent_monomial_mul_cexp_zsmul {x : κ → σ → ℂ}
    (hx : LinearIndependent ℚ x) :
    LinearIndependent ℂ (fun p : (σ → ℕ) × (κ → ℤ) ↦ fun z : σ → ℂ ↦
      (∏ ν, z ν ^ p.1 ν) * Complex.exp ((∑ i, p.2 i • x i) ⬝ᵥ z)) :=
  linearIndependent_monomial_mul_cexp_smul (hx.restrict_scalars' ℤ)

/-- **Linear independence of non-negative-grid exponential monomials.** For finite `κ` and `σ`, if
`x : κ → σ → ℂ` is linearly independent over `ℚ`, then the entire functions
`z ↦ (∏ ν, z ν ^ τ ν) exp((∑ i, t i • x i) · z)` (`(τ, t) : (σ → ℕ) × (κ → ℕ)`) are linearly
independent over `ℂ`. -/
theorem linearIndependent_monomial_mul_cexp_nsmul {x : κ → σ → ℂ}
    (hx : LinearIndependent ℚ x) :
    LinearIndependent ℂ (fun p : (σ → ℕ) × (κ → ℕ) ↦ fun z : σ → ℂ ↦
      (∏ ν, z ν ^ p.1 ν) * Complex.exp ((∑ i, p.2 i • x i) ⬝ᵥ z)) :=
  linearIndependent_monomial_mul_cexp_smul (hx.restrict_scalars' ℕ)

variable {ι : Type*} [Semiring R] [Module R (σ → ℂ)]

/-- For finite `κ` and `σ` and an `R`-linearly independent family `x : κ → σ → ℂ`, a finite linear
combination of exponential monomials indexed by `p` injective on `s` vanishes everywhere on `ℂ^σ`
if and only if every coefficient on `s` is zero. -/
theorem sum_mul_monomial_mul_cexp_smul_eq_zero_iff {x : κ → σ → ℂ}
    (hx : LinearIndependent R x) {s : Finset ι} {p : ι → (σ → ℕ) × (κ → R)}
    (hp : Set.InjOn p s) {c : ι → ℂ} :
    (∀ z : σ → ℂ, ∑ a ∈ s, c a * ((∏ ν, z ν ^ (p a).1 ν) *
      Complex.exp ((∑ i, (p a).2 i • x i) ⬝ᵥ z)) = 0) ↔ ∀ a ∈ s, c a = 0 := by
  refine ⟨fun h ↦ ?_, fun hc z ↦ sum_eq_zero fun a ha ↦ by simp [hc a ha]⟩
  have hli := (linearIndependent_monomial_mul_cexp_smul hx).comp (fun a : s ↦ p a.1) hp.injective
  have h0 : ∑ a : s, c a.1 • (fun z : σ → ℂ ↦ (∏ ν, z ν ^ (p a.1).1 ν) *
      Complex.exp ((∑ i, (p a.1).2 i • x i) ⬝ᵥ z)) = 0 := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Finset.univ_eq_attach]
    rw [sum_attach s (fun a ↦ c a * ((∏ ν, z ν ^ (p a).1 ν) *
      Complex.exp ((∑ i, (p a).2 i • x i) ⬝ᵥ z)))]
    exact h z
  exact fun a ha ↦ Fintype.linearIndependent_iff.1 hli (fun b : s ↦ c b.1) h0 ⟨a, ha⟩

/-- For finite `κ` and `σ`, a finite linear combination of exponential monomials with
`R`-independent `x`, `p` injective on `s`, and at least one nonzero coefficient on `s` does not
vanish identically on `ℂ^σ`. -/
theorem exists_sum_mul_monomial_mul_cexp_smul_ne_zero {x : κ → σ → ℂ}
    (hx : LinearIndependent R x) {s : Finset ι} {p : ι → (σ → ℕ) × (κ → R)}
    (hp : Set.InjOn p s) {c : ι → ℂ} (hc : ∃ a ∈ s, c a ≠ 0) :
    ∃ z : σ → ℂ, ∑ a ∈ s, c a * ((∏ ν, z ν ^ (p a).1 ν) *
      Complex.exp ((∑ i, (p a).2 i • x i) ⬝ᵥ z)) ≠ 0 := by
  by_contra! hall
  obtain ⟨a, ha, hca⟩ := hc
  exact hca ((sum_mul_monomial_mul_cexp_smul_eq_zero_iff hx hp).1 hall a ha)

end LinearIndependence

section MDeriv

variable {ι κ R : Type*} [Fintype κ] {n : ℕ}

/-- **Nonvanishing mixed partial derivative of an auxiliary exponential polynomial.** For finite `κ`
and an `R`-linearly independent family `x : κ → Fin n → ℂ`, let `p : ι → (Fin n → ℕ) × (κ → R)` be
injective on `s` and let `c : ι → ℂ` be nonzero somewhere on `s`. Then at every point `z₀ ∈ ℂⁿ`
there exists `σ : Fin n → ℕ` with `D^σ F(z₀) ≠ 0` for
`F(z) = ∑ a ∈ s, c a * (∏ ν, z ν ^ (p a).1 ν) exp((∑ i, (p a).2 i • x i) · z)`. -/
theorem exists_mDeriv_sum_mul_monomial_mul_cexp_smul_ne_zero [Semiring R]
    [Module R (Fin n → ℂ)] {x : κ → Fin n → ℂ} (hx : LinearIndependent R x) {s : Finset ι}
    {p : ι → (Fin n → ℕ) × (κ → R)} (hp : Set.InjOn p s) {c : ι → ℂ} (hc : ∃ a ∈ s, c a ≠ 0)
    (z₀ : Fin n → ℂ) :
    ∃ σ : Fin n → ℕ, mDeriv σ (fun z : Fin n → ℂ ↦ ∑ a ∈ s, c a * ((∏ ν, z ν ^ (p a).1 ν) *
      Complex.exp ((∑ i, (p a).2 i • x i) ⬝ᵥ z))) z₀ ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_sum_mul_monomial_mul_cexp_smul_ne_zero hx hp hc
  exact exists_mDeriv_ne_zero (by simp only [dotProduct]; fun_prop)
    (fun h0 ↦ hz (congrFun h0 z)) z₀

/-- Specialization of `exists_mDeriv_sum_mul_monomial_mul_cexp_smul_ne_zero` to `ℚ`-linearly
independent `x : κ → Fin n → ℂ` and integer exponent tuples `κ → ℤ`. -/
theorem exists_mDeriv_sum_mul_monomial_mul_cexp_zsmul_ne_zero {x : κ → Fin n → ℂ}
    (hx : LinearIndependent ℚ x) {s : Finset ι} {p : ι → (Fin n → ℕ) × (κ → ℤ)}
    (hp : Set.InjOn p s) {c : ι → ℂ} (hc : ∃ a ∈ s, c a ≠ 0) (z₀ : Fin n → ℂ) :
    ∃ σ : Fin n → ℕ, mDeriv σ (fun z : Fin n → ℂ ↦ ∑ a ∈ s, c a * ((∏ ν, z ν ^ (p a).1 ν) *
      Complex.exp ((∑ i, (p a).2 i • x i) ⬝ᵥ z))) z₀ ≠ 0 :=
  exists_mDeriv_sum_mul_monomial_mul_cexp_smul_ne_zero (hx.restrict_scalars' ℤ) hp hc z₀

/-- Integer-coefficient and non-negative-exponent specialization of
`exists_mDeriv_sum_mul_monomial_mul_cexp_smul_ne_zero`, matching the auxiliary function of the
Schneider–Lang and Baker constructions. -/
theorem exists_mDeriv_sum_intCast_mul_monomial_mul_cexp_nsmul_ne_zero {x : κ → Fin n → ℂ}
    (hx : LinearIndependent ℚ x) {s : Finset ι} {p : ι → (Fin n → ℕ) × (κ → ℕ)}
    (hp : Set.InjOn p s) {q : ι → ℤ} (hq : ∃ a ∈ s, q a ≠ 0) (z₀ : Fin n → ℂ) :
    ∃ σ : Fin n → ℕ, mDeriv σ (fun z : Fin n → ℂ ↦ ∑ a ∈ s, (q a : ℂ) * ((∏ ν, z ν ^ (p a).1 ν) *
      Complex.exp ((∑ i, (p a).2 i • x i) ⬝ᵥ z))) z₀ ≠ 0 := by
  obtain ⟨a, ha, hqa⟩ := hq
  exact exists_mDeriv_sum_mul_monomial_mul_cexp_smul_ne_zero (hx.restrict_scalars' ℕ) hp
    ⟨a, ha, Int.cast_ne_zero.2 hqa⟩ z₀

end MDeriv

end TauCeti.Baker
