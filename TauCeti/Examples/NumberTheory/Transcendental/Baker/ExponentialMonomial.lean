/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.ExponentialPolynomial.MvPolynomial
import TauCeti.NumberTheory.Transcendental.Baker.ExponentialMonomial

/-!
# Examples and sharpness checks for complex exponential polynomials and `mDeriv`

This file checks concrete instances, sharpness, and hypothesis necessity for:
* the order-of-vanishing bound `TauCeti.analyticOrderAt_sum_eval_mul_cexp_lt` on univariate complex
  exponential polynomials;
* the identity principle `Differentiable.eq_zero_of_forall_iteratedDeriv_eq_zero` and mixed partial
  derivatives `TauCeti.Baker.mDeriv` on `ℂⁿ`;
* the linear independence of Schneider–Lang and Baker exponential monomials in
  `TauCeti.NumberTheory.Transcendental.Baker.ExponentialMonomial`.
-/

namespace TauCeti.Baker.ExponentialMonomialExample

open Finset Polynomial

/-! ### Sharpness of `< ∑ i ∈ s, (deg pᵢ + 1)` -/

/-- The two-term complex exponential polynomial `(1 + z) exp(0 · z) - exp(1 · z) = 1 + z - exp z`
has `∑ i ∈ {0, 1}, (deg pᵢ + 1) = (1 + 1) + (0 + 1) = 3` and vanishes at `0` to exact order `2`,
showing that the strict upper bound `TauCeti.analyticOrderAt_sum_eval_mul_cexp_lt` is sharp. -/
example :
    let p : Fin 2 → ℂ[X] := ![1 + X, -1]
    let ρ : Fin 2 → ℂ := ![0, 1]
    (∑ i : Fin 2, ((p i).natDegree + 1)) = 3 ∧
      analyticOrderAt (fun z : ℂ ↦ ∑ i : Fin 2, (p i).eval z * Complex.exp (ρ i * z)) 0 = 2 := by
  set p : Fin 2 → ℂ[X] := ![1 + X, -1]
  set ρ : Fin 2 → ℂ := ![0, 1]
  have hdeg : (∑ i : Fin 2, ((p i).natDegree + 1)) = 3 := by
    simp [Fin.sum_univ_two, p]
  refine ⟨hdeg, le_antisymm ?_ ?_⟩
  · have hρ : Set.InjOn ρ ↑(univ : Finset (Fin 2)) := by
      intro i _ j _ hij
      fin_cases i <;> fin_cases j <;> simp [ρ] at hij ⊢
    have hp : ∃ i ∈ (univ : Finset (Fin 2)), p i ≠ 0 :=
      ⟨1, mem_univ 1, by simp [p]⟩
    have hlt : analyticOrderAt (fun z : ℂ ↦ ∑ i : Fin 2, (p i).eval z * Complex.exp (ρ i * z)) 0 <
        (3 : ℕ) := hdeg ▸ analyticOrderAt_sum_eval_mul_cexp_lt hρ hp 0
    cases ha : analyticOrderAt
        (fun z : ℂ ↦ ∑ i : Fin 2, (p i).eval z * Complex.exp (ρ i * z)) 0 with
    | top => exact absurd ha hlt.ne_top
    | coe m =>
      rw [ha, Nat.cast_lt] at hlt
      exact_mod_cast Nat.le_of_lt_succ hlt
  · have hfun : (fun z : ℂ ↦ ∑ i : Fin 2, (p i).eval z * Complex.exp (ρ i * z)) =
        fun z : ℂ ↦ 1 + z - Complex.exp z := by
      funext z
      simp [Fin.sum_univ_two, p, ρ]
      ring
    rw [hfun]
    have han : AnalyticAt ℂ (fun z : ℂ ↦ 1 + z - Complex.exp z) 0 := by fun_prop
    refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).2 fun k hk ↦ ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk0 | rfl
    · obtain rfl := Nat.lt_one_iff.1 hk0
      simp
    · have hd : deriv (fun z : ℂ ↦ 1 + z - Complex.exp z) = fun z ↦ 1 - Complex.exp z := by
        funext z
        simpa using (((hasDerivAt_const z (1 : ℂ)).fun_add (hasDerivAt_id z)).fun_sub
          (Complex.hasDerivAt_exp z)).deriv
      simp [iteratedDeriv_one, hd]

/-! ### Complex zero sets can be infinite while local vanishing order is bounded -/

/-- Unlike real exponential polynomials, `exp z - 1` vanishes on the infinite set `2 π i ℤ`, while
its analytic order of vanishing at `0` is bounded above by `2`. -/
example (n : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * n) - 1 = 0 ∧
      analyticOrderAt (fun z : ℂ ↦
        ∑ i : Fin 2, (![(1 : ℂ[X]), -1] i).eval z * Complex.exp (![1, 0] i * z)) 0 < 2 := by
  refine ⟨sub_eq_zero.2 ?_, ?_⟩
  · rw [show (2 : ℂ) * Real.pi * Complex.I * n = n * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  · have hρ : Set.InjOn (![(1 : ℂ), 0] : Fin 2 → ℂ) ↑(univ : Finset (Fin 2)) := by
      intro i _ j _ hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    have hp : ∃ i ∈ (univ : Finset (Fin 2)), (![(1 : ℂ[X]), -1] : Fin 2 → ℂ[X]) i ≠ 0 :=
      ⟨0, mem_univ 0, by simp⟩
    simpa [Fin.sum_univ_two] using analyticOrderAt_sum_eval_mul_cexp_lt hρ hp 0

/-! ### Necessity of hypotheses -/

/-- Without `Differentiable ℂ g`, all `ℂ`-linear `iteratedDeriv`s at `0` can vanish (via junk
values of `deriv` at points of non-differentiability) for a nonzero function `g : ℂ → ℂ`. -/
example :
    let g : ℂ → ℂ := fun z ↦ (z.im : ℂ)
    (∀ k : ℕ, iteratedDeriv k g 0 = 0) ∧ g ≠ 0 := by
  set g : ℂ → ℂ := fun z ↦ (z.im : ℂ)
  have hnd : ∀ z : ℂ, ¬ DifferentiableAt ℂ g z := by
    intro z hdiff
    have hC : HasFDerivAt g ((fderiv ℂ g z).restrictScalars ℝ) z :=
      HasFDerivAt.restrictScalars ℝ hdiff.hasFDerivAt
    have hR : HasFDerivAt g (Complex.ofRealCLM.comp Complex.imCLM) z :=
      (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt
    have heq := hC.unique hR
    have h1 : fderiv ℂ g z 1 = 0 := by
      simpa using ContinuousLinearMap.ext_iff.1 heq 1
    have hI : fderiv ℂ g z Complex.I = 1 := by
      simpa using ContinuousLinearMap.ext_iff.1 heq Complex.I
    have hI' : fderiv ℂ g z Complex.I = 0 := by
      simpa [h1] using (fderiv ℂ g z).map_smul Complex.I (1 : ℂ)
    exact zero_ne_one (hI'.symm.trans hI)
  have hderiv : deriv g = 0 := funext fun z ↦ deriv_zero_of_not_differentiableAt (hnd z)
  refine ⟨fun k ↦ ?_, fun h0 ↦ ?_⟩
  · cases k with
    | zero => simp [g]
    | succ k => simp [iteratedDeriv_succ', hderiv]
  · have hI := congrFun h0 Complex.I
    simp [g] at hI

/-- Without `Set.InjOn ρ s`, a sum with nonzero polynomial coefficients can vanish identically. -/
example :
    let p : Fin 2 → ℂ[X] := ![1, -1]
    let ρ : Fin 2 → ℂ := ![1, 1]
    (∃ i ∈ (univ : Finset (Fin 2)), p i ≠ 0) ∧
      ∀ z : ℂ, ∑ i : Fin 2, (p i).eval z * Complex.exp (ρ i * z) = 0 := by
  refine ⟨⟨0, mem_univ 0, by simp⟩, fun z ↦ ?_⟩
  simp [Fin.sum_univ_two]

/-- Without `ℚ`-linear independence of `x`, the exponential monomials
`z ↦ (∏ ν, z ν ^ τ ν) exp((∑ i, t i • x i) · z)` fail to be linearly independent over `ℂ`. -/
example :
    let x : Fin 2 → Fin 1 → ℂ := fun _ _ ↦ 1
    ¬ LinearIndependent ℂ (fun p : (Fin 1 → ℕ) × (Fin 2 → ℤ) ↦ fun z : Fin 1 → ℂ ↦
      (∏ ν, z ν ^ p.1 ν) * Complex.exp ((∑ i, p.2 i • x i) ⬝ᵥ z)) := by
  intro x hli
  have h : (fun z : Fin 1 → ℂ ↦
      (∏ ν, z ν ^ (0 : Fin 1 → ℕ) ν) * Complex.exp ((∑ i, (![1, 0] : Fin 2 → ℤ) i • x i) ⬝ᵥ z)) =
    fun z : Fin 1 → ℂ ↦
      (∏ ν, z ν ^ (0 : Fin 1 → ℕ) ν) * Complex.exp ((∑ i, (![0, 1] : Fin 2 → ℤ) i • x i) ⬝ᵥ z) := by
    funext z
    simp [Fin.sum_univ_two, x]
  have hinj := hli.injective
  have heq := congrFun (congrArg Prod.snd
    (@hinj ((0 : Fin 1 → ℕ), (![1, 0] : Fin 2 → ℤ)) (0, ![0, 1]) h)) 0
  simp at heq

/-! ### Sanity checks on `mDeriv` and Baker exponential monomials -/

/-- `mDeriv` of order `e₀` on `z₀ * z₁` is `z₁`, while `mDeriv ![1, 1]` on `z₀ ^ 2` vanishes
(confirming `mDeriv ![1, 1]` is `∂₀ ∂₁`, not a total second derivative). -/
example :
    mDeriv (Pi.single 0 1) (fun z : Fin 2 → ℂ ↦ z 0 * z 1) = (fun z ↦ z 1) ∧
      mDeriv ![1, 1] (fun z : Fin 2 → ℂ ↦ z 0 ^ 2) = 0 := by
  have hf1 : (fun z : Fin 2 → ℂ ↦ z 0 * z 1) =
      fun z ↦ ∏ i : Fin 2, (![fun w : ℂ ↦ w, fun w : ℂ ↦ w] i) (z i) := by
    funext z; simp [Fin.prod_univ_two]
  have hf2 : (fun z : Fin 2 → ℂ ↦ z 0 ^ 2) =
      fun z ↦ ∏ i : Fin 2, (![fun w : ℂ ↦ w ^ 2, fun _ : ℂ ↦ (1 : ℂ)] i) (z i) := by
    funext z; simp [Fin.prod_univ_two]
  refine ⟨?_, ?_⟩
  · rw [hf1, mDeriv_prod (fun i ↦ by fin_cases i <;> dsimp <;> fun_prop)]
    funext z
    simp [Fin.prod_univ_two, iteratedDeriv_one]
  · rw [hf2, mDeriv_prod (fun i ↦ by fin_cases i <;> dsimp <;> fun_prop)]
    funext z
    simp [Fin.prod_univ_two, iteratedDeriv_one]

/-- An integer combination `z₀ - exp z₀` of two Schneider–Lang exponential monomials on `ℂ¹` has a
nonvanishing mixed partial derivative at `0`. -/
example :
    ∃ σ : Fin 1 → ℕ,
      mDeriv σ (fun z : Fin 1 → ℂ ↦
        ∑ a ∈ (univ : Finset (Fin 2)),
          ((![1, -1] : Fin 2 → ℤ) a : ℂ) *
            ((∏ ν : Fin 1, z ν ^ (![![1], ![0]] a : Fin 1 → ℕ) ν) *
              Complex.exp ((∑ i : Fin 1, (![![0], ![1]] a : Fin 1 → ℕ) i •
                (fun _ _ ↦ (1 : ℂ)) i) ⬝ᵥ z))) 0 ≠ 0 := by
  have hx : LinearIndependent ℚ (fun _ : Fin 1 ↦ fun _ : Fin 1 ↦ (1 : ℂ)) :=
    Fintype.linearIndependent_iff.2 fun g hg i ↦ by
      fin_cases i
      have h0 := congrFun hg 0
      simpa using h0
  let p : Fin 2 → (Fin 1 → ℕ) × (Fin 1 → ℕ) := ![(![1], ![0]), (![0], ![1])]
  have hp : Set.InjOn p ↑(univ : Finset (Fin 2)) := by
    intro a _ b _ hab
    fin_cases a <;> fin_cases b
    · rfl
    · have := congrFun (congrArg Prod.fst hab) 0; simp [p] at this
    · have := congrFun (congrArg Prod.fst hab) 0; simp [p] at this
    · rfl
  exact exists_mDeriv_sum_intCast_mul_monomial_mul_cexp_nsmul_ne_zero hx hp
    (q := ![1, -1]) ⟨0, mem_univ 0, by decide⟩ 0

end TauCeti.Baker.ExponentialMonomialExample
