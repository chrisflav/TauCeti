/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.NumberTheory.Transcendental.Mahler.Basic

/-!
# Concrete Mahler systems, the Fredholm series, and non-Mahler examples

This file develops the classical examples and non-examples of Mahler series, Mahler functions,
and regular points.

## Main definitions

* `TauCeti.fredholmSeries`: the lacunary Fredholm power series `∑ n ≥ 0, X^(2^n)`.
* `TauCeti.fredholmMatrix`: the `2 × 2` companion matrix `!![1, X; 0, 1]` over `RatFunc K`
  associated with `(fredholmSeries, 1)`.

## Main results

* `TauCeti.fredholmSeries_eq_X_add_expand`: the functional equation `F(X) = X + F(X^2)`.
* `TauCeti.isMahlerSeries_fredholmSeries` and `TauCeti.isMahlerFunction_fredholmSeries`: the
  Fredholm series is a `2`-Mahler series and a `2`-Mahler function.
* `TauCeti.isMahlerRegularPoint_fredholmMatrix`: every point of the punctured unit disc is regular
  for `fredholmMatrix`.
* `TauCeti.lacunary_not_rational`: over any commutative ring `R`, no nonzero `r ∈ R[X]` and
  `p ∈ R[X]` satisfy `r * fredholmSeries = p`.
* `TauCeti.transcendental_fredholmSeries`: over any field `K` of characteristic zero, the Fredholm
  series is transcendental over `K(X)`.
* `TauCeti.linearIndependent_expand_exp`, `TauCeti.not_isMahlerSeries_exp`, and
  `TauCeti.not_isMahlerFunction_exp`: for every `q ≥ 2`, the formal exponential series `exp(X)` is
  not `q`-Mahler over any field of characteristic zero.
* `TauCeti.not_isMahlerSeries_of_sq_eq_one_sub_X`: any formal Laurent series solving
  `f ^ 2 = 1 - X` is not `q`-Mahler for any `q`.
* `TauCeti.not_isMahlerRegularPoint_inv_one_sub_two_X_two` and
  `TauCeti.isMahlerRegularPoint_inv_one_sub_two_X_three`: for `A = !![(1 - 2X)⁻¹]`, the point
  `α = (Real.sqrt 2)⁻¹` is not `2`-regular (its square `1/2` is a pole) but is `3`-regular.

## References

* B. Adamczewski and C. Faverjon, *Méthode de Mahler : relations linéaires, transcendance et
  applications aux nombres automatiques*, Proc. London Math. Soc. (3) **115** (2017), §1, p. 2.
* K. Nishioka, *Mahler Functions and Transcendence*, Lecture Notes in Math. **1631**, Springer,
  1996, §1.1 and Theorem 5.1.7.
-/

public section

open Polynomial
open scoped LaurentSeries PowerSeries

attribute [local instance 10] RatFunc.liftAlgebra

namespace TauCeti

/-! ### The Fredholm series and its Mahler system -/

section Fredholm

/-- The lacunary Fredholm power series `∑ n ≥ 0, X^(2^n)`. -/
noncomputable def fredholmSeries (R : Type*) [Semiring R] : PowerSeries R :=
  open scoped Classical in
  PowerSeries.mk fun m ↦ if ∃ n : ℕ, m = 2 ^ n then 1 else 0

/-- Coefficient formula for the Fredholm power series. -/
theorem coeff_fredholmSeries (R : Type*) [Semiring R] (m : ℕ) :
    PowerSeries.coeff m (fredholmSeries R) =
      open scoped Classical in if ∃ n : ℕ, m = 2 ^ n then 1 else 0 := by
  classical
  simp [fredholmSeries]

/-- Every power-of-two coefficient of the Fredholm series is `1`. -/
@[simp]
theorem coeff_fredholmSeries_pow_two (R : Type*) [Semiring R] (n : ℕ) :
    PowerSeries.coeff (2 ^ n) (fredholmSeries R) = 1 := by
  classical
  simp [fredholmSeries]

/-- Every non-power-of-two coefficient of the Fredholm series is `0`. -/
theorem coeff_fredholmSeries_of_not_pow_two (R : Type*) [Semiring R] {m : ℕ}
    (hm : ¬ ∃ n : ℕ, m = 2 ^ n) :
    PowerSeries.coeff m (fredholmSeries R) = 0 := by
  classical
  simp [fredholmSeries, hm]

/-- The Fredholm power series satisfies `F(X) = X + F(X^2)`. -/
theorem fredholmSeries_eq_X_add_expand (R : Type*) [CommRing R] :
    fredholmSeries R = PowerSeries.X + PowerSeries.expand 2 (by norm_num) (fredholmSeries R) := by
  classical
  ext m
  rw [map_add, PowerSeries.coeff_X]
  rcases m with _ | _ | m
  · have h0 : ¬ ∃ n : ℕ, (0 : ℕ) = 2 ^ n := fun ⟨n, hn⟩ ↦ by
      have : 0 < 2 ^ n := pow_pos (by norm_num) n
      omega
    rw [coeff_fredholmSeries_of_not_pow_two R h0, ite_eq_right (by omega), zero_add]
    simpa [PowerSeries.coeff_expand_mul] using (coeff_fredholmSeries_of_not_pow_two R h0).symm
  · have hnd : ¬ (2 : ℕ) ∣ 1 := by omega
    rw [Nat.zero_add, ite_eq_left rfl,
      PowerSeries.coeff_expand_of_not_dvd 2 (by norm_num) _ hnd, add_zero]
    simpa using coeff_fredholmSeries_pow_two R 0
  · rw [ite_eq_right (by omega), zero_add]
    by_cases h2 : 2 ∣ (m + 2)
    · obtain ⟨k, hk⟩ := h2
      rw [hk, PowerSeries.coeff_expand_mul 2 (by norm_num)]
      have hiff : (∃ n : ℕ, 2 * k = 2 ^ n) ↔ ∃ n : ℕ, k = 2 ^ n := by
        constructor
        · rintro ⟨n, hn⟩
          cases n with
          | zero => omega
          | succ n => exact ⟨n, by rw [pow_succ'] at hn; omega⟩
        · rintro ⟨n, rfl⟩
          exact ⟨n + 1, by rw [pow_succ']⟩
      simp [fredholmSeries, hiff]
    · rw [PowerSeries.coeff_expand_of_not_dvd 2 (by norm_num) _ h2]
      refine coeff_fredholmSeries_of_not_pow_two R fun ⟨n, hn⟩ ↦ ?_
      cases n with
      | zero => omega
      | succ n => exact h2 ⟨2 ^ n, by rw [← pow_succ']; exact hn⟩

/-- The `2 × 2` rational Mahler matrix `!![1, X; 0, 1]` for the Fredholm vector `(F, 1)`. -/
noncomputable def fredholmMatrix (K : Type*) [Field K] :
    Matrix (Fin 2) (Fin 2) (RatFunc K) :=
  !![1, RatFunc.X; 0, 1]

/-- Unfolding equation for `fredholmMatrix`. -/
theorem fredholmMatrix_def (K : Type*) [Field K] :
    fredholmMatrix K = !![1, RatFunc.X; 0, 1] := by
  unfold fredholmMatrix
  rfl

/-- The determinant of `fredholmMatrix K` is `1`. -/
@[simp]
theorem det_fredholmMatrix (K : Type*) [Field K] : (fredholmMatrix K).det = 1 := by
  simp [fredholmMatrix, Matrix.det_fin_two]

/-- The inverse of `fredholmMatrix K` is `!![1, -X; 0, 1]`. -/
theorem fredholmMatrix_inv (K : Type*) [Field K] :
    (fredholmMatrix K)⁻¹ = !![1, -RatFunc.X; 0, 1] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fredholmMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Fredholm vector `(fredholmSeries K, 1)` solves the `2`-Mahler system attached to
`fredholmMatrix K`. -/
theorem fredholmMatrix_system (K : Type*) [Field K] :
    let F : Fin 2 → PowerSeries K := ![fredholmSeries K, 1]
    (fun i ↦ (F i : K⸨X⸩)) =
      ((fredholmMatrix K).map (algebraMap (RatFunc K) K⸨X⸩)).mulVec
        (fun i ↦ ((PowerSeries.expand 2 (by norm_num) (F i) : PowerSeries K) : K⸨X⸩)) := by
  intro F
  have hX : algebraMap (RatFunc K) K⸨X⸩ RatFunc.X =
      ((PowerSeries.X : PowerSeries K) : K⸨X⸩) := by
    rw [← RatFunc.algebraMap_X]
    exact (RatFunc.coe_coe (Polynomial.X : K[X])).symm.trans (by simp)
  funext i
  fin_cases i
  · simp only [F, Fin.zero_eta, Fin.isValue, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, fredholmMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_one, one_mul, mul_one, hX, ← map_add, add_comm]
    exact congrArg (HahnSeries.ofPowerSeries ℤ K) (fredholmSeries_eq_X_add_expand K)
  · simp [F, Matrix.mulVec, dotProduct, Fin.sum_univ_two, fredholmMatrix]

/-- Every point of the punctured unit disc is regular for `fredholmMatrix K` and any `q ≥ 2`. -/
theorem isMahlerRegularPoint_fredholmMatrix {K : Type*} [NormedField K] {q : ℕ} (hq : 2 ≤ q)
    {α : K} (h0 : 0 < ‖α‖) (h1 : ‖α‖ < 1) :
    IsMahlerRegularPoint q (fredholmMatrix K) α := by
  let P : Matrix (Fin 2) (Fin 2) K[X] := !![1, Polynomial.X; 0, 1]
  have hP : fredholmMatrix K = P.map (algebraMap K[X] (RatFunc K)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fredholmMatrix, P, RatFunc.algebraMap_X]
  have hdet : IsUnit P.det := by simp [P, Matrix.det_fin_two]
  rw [hP]
  exact isMahlerRegularPoint_of_polynomial hq hdet h0 h1

/-- The Fredholm series is a `2`-Mahler Laurent series over any field `K`. -/
theorem isMahlerSeries_fredholmSeries (K : Type*) [Field K] :
    IsMahlerSeries 2 ((fredholmSeries K : PowerSeries K) : K⸨X⸩) := by
  rw [isMahlerSeries_coe_iff_exists_powerSeries_system]
  refine ⟨le_rfl, 2, by norm_num, fredholmMatrix K, ![fredholmSeries K, 1],
    by simp, fredholmMatrix_system K, rfl⟩

/-- The Fredholm series is a `2`-Mahler function over any field `K` of characteristic zero. -/
theorem isMahlerFunction_fredholmSeries (K : Type*) [Field K] [CharZero K] :
    IsMahlerFunction 2 (fredholmSeries K) := by
  classical
  rw [isMahlerFunction_iff_isMahlerSeries]
  refine ⟨fun m ↦ ?_, isMahlerSeries_fredholmSeries K⟩
  simp only [fredholmSeries, PowerSeries.coeff_mk]
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

/-- **Irrationality of the Fredholm series.** Over any commutative ring `R`, no nonzero polynomial
`r` and polynomial `p` satisfy `r * fredholmSeries = p`. -/
theorem lacunary_not_rational {R : Type*} [CommRing R] (r p : R[X]) (hr : r ≠ 0) :
    (r : PowerSeries R) * fredholmSeries R ≠ (p : PowerSeries R) := by
  intro h
  set d := r.natDegree
  set e := p.natDegree
  set N := d + e + 2
  have hN : d + e + 2 < 2 ^ N := Nat.lt_two_pow_self
  have hcoeff := congrArg (PowerSeries.coeff (2 ^ N + d)) h
  rw [PowerSeries.coeff_mul, Polynomial.coeff_coe,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)] at hcoeff
  rw [Finset.sum_eq_single (d, 2 ^ N)] at hcoeff
  · rw [Polynomial.coeff_coe, coeff_fredholmSeries_pow_two, mul_one] at hcoeff
    exact Polynomial.leadingCoeff_ne_zero.mpr hr hcoeff
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [Polynomial.coeff_coe]
    by_cases had : d < a
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt had, zero_mul]
    · have hal : a < d := by
        rcases lt_or_eq_of_le (Nat.le_of_not_lt had) with hlt | rfl
        · exact hlt
        · exact (hne (Prod.ext rfl (by omega))).elim
      have hnotpow : ¬ ∃ k : ℕ, b = 2 ^ k := by
        rintro ⟨k, hk⟩
        rcases le_or_gt k N with hkN | hNk
        · have : 2 ^ k ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hkN
          omega
        · have : 2 ^ (N + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hNk
          rw [pow_succ] at this
          omega
      rw [coeff_fredholmSeries_of_not_pow_two R hnotpow, mul_zero]
  · intro hmem
    exact (hmem (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_comm d (2 ^ N)))).elim

/-- **Functional transcendence of the Fredholm series.** Over any field `K` of characteristic zero,
the Fredholm series `∑ n ≥ 0, X^(2^n)` is transcendental over `K(X)`. -/
theorem transcendental_fredholmSeries (K : Type*) [Field K] [CharZero K] :
    Transcendental (RatFunc K) ((fredholmSeries K : PowerSeries K) : K⸨X⸩) :=
  (isMahlerFunction_fredholmSeries K).transcendental_of_not_ratFunc
    fun p r hr ↦ lacunary_not_rational r p hr

end Fredholm

/-! ### Non-Mahler criterion for the formal exponential series -/

section Exponential

variable {K : Type*} [Field K] [CharZero K]

private theorem derivative_expand_exp {r : ℕ} (hr : r ≠ 0) :
    PowerSeries.derivative (PowerSeries.expand r hr (PowerSeries.exp K)) =
      ((Polynomial.C (r : K) * Polynomial.X ^ (r - 1) : K[X]) : PowerSeries K) *
        PowerSeries.expand r hr (PowerSeries.exp K) := by
  rw [PowerSeries.expand_apply, PowerSeries.derivative_subst (PowerSeries.HasSubst.X_pow hr),
    PowerSeries.derivative_exp, PowerSeries.derivative_X_pow, mul_comm]
  congr 1
  rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]

private theorem natDegree_exp_diff_weight {q j m : ℕ} (hq : 2 ≤ q) (hjm : j < m) :
    let w : ℕ → K[X] := fun r ↦ Polynomial.C (r : K) * Polynomial.X ^ (r - 1)
    w (q ^ j) - w (q ^ m) ≠ 0 ∧ (w (q ^ j) - w (q ^ m)).natDegree = q ^ m - 1 := by
  intro w
  have hqm : 2 ≤ q ^ m := by
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : q ^ j < q ^ m := Nat.pow_lt_pow_right (by omega) hjm
  have hdeg_m : (w (q ^ m)).natDegree = q ^ m - 1 := by
    have hc : ((q ^ m : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact Polynomial.natDegree_C_mul_X_pow (q ^ m - 1) ((q ^ m : ℕ) : K) hc
  have hdeg_j : (w (q ^ j)).natDegree < (w (q ^ m)).natDegree := by
    rw [hdeg_m]
    have hle : (w (q ^ j)).natDegree ≤ q ^ j - 1 :=
      Polynomial.natDegree_C_mul_X_pow_le ((q ^ j : ℕ) : K) (q ^ j - 1)
    omega
  have hdeg : (w (q ^ j) - w (q ^ m)).natDegree = q ^ m - 1 := by
    rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_right_of_natDegree_lt
      (by rwa [Polynomial.natDegree_neg]), Polynomial.natDegree_neg, hdeg_m]
  refine ⟨fun h0 ↦ ?_, hdeg⟩
  rw [h0, Polynomial.natDegree_zero] at hdeg
  omega

private theorem exp_elim_coeff_ne_zero {q j m : ℕ} (hq : 2 ≤ q) (hjm : j < m)
    {pm pj : K[X]} (hpm : pm ≠ 0) (hpj : pj ≠ 0) :
    let w : ℕ → K[X] := fun r ↦ Polynomial.C (r : K) * Polynomial.X ^ (r - 1)
    pm * (Polynomial.derivative pj + pj * w (q ^ j)) -
      (Polynomial.derivative pm + pm * w (q ^ m)) * pj ≠ 0 := by
  intro w
  obtain ⟨hw0, hwdeg⟩ := natDegree_exp_diff_weight (K := K) hq hjm
  set T₁ : K[X] := pm * pj * (w (q ^ j) - w (q ^ m))
  set T₂ : K[X] := pm * Polynomial.derivative pj - Polynomial.derivative pm * pj
  have hsplit : pm * (Polynomial.derivative pj + pj * w (q ^ j)) -
      (Polynomial.derivative pm + pm * w (q ^ m)) * pj = T₁ + T₂ := by
    simp only [T₁, T₂]; ring
  rw [hsplit]
  have hqm : 2 ≤ q ^ m := by
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  have hT₁deg : T₁.natDegree = pm.natDegree + pj.natDegree + (q ^ m - 1) := by
    simp only [T₁]
    rw [Polynomial.natDegree_mul (mul_ne_zero hpm hpj) hw0, Polynomial.natDegree_mul hpm hpj, hwdeg]
  have hT₂deg : T₂.natDegree ≤ pm.natDegree + pj.natDegree := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · have h1 := Polynomial.natDegree_mul_le (p := pm) (q := Polynomial.derivative pj)
      have h2 := Polynomial.natDegree_derivative_le pj
      omega
    · have h1 := Polynomial.natDegree_mul_le (p := Polynomial.derivative pm) (q := pj)
      have h2 := Polynomial.natDegree_derivative_le pm
      omega
  intro h0
  have heq : T₁ = -T₂ := eq_neg_of_add_eq_zero_left h0
  have hdeg_eq : T₁.natDegree = T₂.natDegree := by rw [heq, Polynomial.natDegree_neg]
  omega

private theorem exp_elim_sum {q : ℕ} (hq : 2 ≤ q) {t : Finset ℕ} {m : ℕ} (hm : m ∈ t)
    {c : ℕ → K[X]}
    (hrel : ∑ i ∈ t, (c i : PowerSeries K) *
      PowerSeries.expand (q ^ i) (pow_ne_zero i (by omega)) (PowerSeries.exp K) = 0) :
    let w : ℕ → K[X] := fun r ↦ Polynomial.C (r : K) * Polynomial.X ^ (r - 1)
    let b : ℕ → K[X] := fun i ↦
      c m * (Polynomial.derivative (c i) + c i * w (q ^ i)) -
        (Polynomial.derivative (c m) + c m * w (q ^ m)) * c i
    ∑ i ∈ t.erase m, (b i : PowerSeries K) *
      PowerSeries.expand (q ^ i) (pow_ne_zero i (by omega)) (PowerSeries.exp K) = 0 := by
  intro w b
  let E : ℕ → PowerSeries K := fun i ↦
    PowerSeries.expand (q ^ i) (pow_ne_zero i (by omega)) (PowerSeries.exp K)
  have hderiv : ∑ i ∈ t,
      ((Polynomial.derivative (c i) + c i * w (q ^ i) : K[X]) : PowerSeries K) * E i = 0 := by
    have hd := congrArg PowerSeries.derivative hrel
    rw [map_zero, map_sum] at hd
    rw [← hd]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PowerSeries.derivative.leibniz, PowerSeries.derivative_coe,
      derivative_expand_exp (pow_ne_zero i (by omega))]
    simp only [E, w, Polynomial.coe_add, Polynomial.coe_mul, smul_eq_mul]
    ring
  have hcomb : (c m : PowerSeries K) *
      (∑ i ∈ t,
        ((Polynomial.derivative (c i) + c i * w (q ^ i) : K[X]) : PowerSeries K) * E i) -
      ((Polynomial.derivative (c m) + c m * w (q ^ m) : K[X]) : PowerSeries K) *
      (∑ i ∈ t, (c i : PowerSeries K) * E i) = 0 := by
    rw [hderiv, hrel, mul_zero, mul_zero, sub_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.add_sum_erase t _ hm] at hcomb
  have hterm : ∀ i ∈ t, (c m : PowerSeries K) *
      (((Polynomial.derivative (c i) + c i * w (q ^ i) : K[X]) : PowerSeries K) * E i) -
      ((Polynomial.derivative (c m) + c m * w (q ^ m) : K[X]) : PowerSeries K) *
        ((c i : PowerSeries K) * E i) = (b i : PowerSeries K) * E i := fun i _ ↦ by
    simp only [b, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_add]
    ring
  have hbm : b m = 0 := by simp only [b]; ring
  rw [hterm m hm, hbm, Polynomial.coe_zero, zero_mul, zero_add] at hcomb
  rw [← hcomb]
  exact Finset.sum_congr rfl fun i hi ↦ (hterm i (Finset.mem_of_mem_erase hi)).symm

/-- Over a characteristic-zero field `K`, for any `q ≥ 2`, the iterates `exp(X^(q^i))` satisfy no
nontrivial polynomial-coefficient linear relation. -/
theorem linearIndependent_expand_exp {q : ℕ} (hq : 2 ≤ q) (s : Finset ℕ) (p : ℕ → K[X])
    (hsum : ∑ i ∈ s, (p i : PowerSeries K) *
      PowerSeries.expand (q ^ i) (pow_ne_zero i (by omega)) (PowerSeries.exp K) = 0) :
    ∀ i ∈ s, p i = 0 := by
  classical
  suffices h : ∀ (n : ℕ) (t : Finset ℕ) (c : ℕ → K[X]), t.card = n →
      (∑ i ∈ t, (c i : PowerSeries K) *
        PowerSeries.expand (q ^ i) (pow_ne_zero i (by omega)) (PowerSeries.exp K) = 0) →
      ∀ i ∈ t, c i = 0 from h s.card s p rfl hsum
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t c hcard hrel
    by_contra hall
    push Not at hall
    -- Step 1: Restrict to the nonempty support `t'` of nonzero polynomial coefficients.
    let t' := t.filter fun i ↦ c i ≠ 0
    have ht'sub : t' ⊆ t := Finset.filter_subset _ t
    have ht'ne : t'.Nonempty := by
      obtain ⟨i, hi, hci⟩ := hall
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
    have hrel' : ∑ i ∈ t', (c i : PowerSeries K) *
        PowerSeries.expand (q ^ i) (pow_ne_zero i (by omega)) (PowerSeries.exp K) = 0 := by
      rw [← hrel, Finset.sum_subset ht'sub]
      intro i hi hni
      have hc0 : c i = 0 := by
        by_contra hne
        exact hni (Finset.mem_filter.mpr ⟨hi, hne⟩)
      simp [hc0]
    -- Step 2: Differentiate to eliminate the top exponent `m = max t'`, contradicting minimality.
    let m := t'.max' ht'ne
    have hm_mem : m ∈ t' := Finset.max'_mem t' ht'ne
    have hcm : c m ≠ 0 := (Finset.mem_filter.mp hm_mem).2
    by_cases hcard1 : (t'.erase m).Nonempty
    · obtain ⟨j, hj_erase⟩ := hcard1
      have hj_mem : j ∈ t' := Finset.mem_of_mem_erase hj_erase
      have hjm : j < m :=
        lt_of_le_of_ne (Finset.le_max' t' j hj_mem) (Finset.ne_of_mem_erase hj_erase)
      have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj_mem).2
      have hcard_lt : (t'.erase m).card < n := by
        have hle : t'.card ≤ t.card := Finset.card_le_card ht'sub
        have hlt : (t'.erase m).card < t'.card := Finset.card_erase_lt_of_mem hm_mem
        omega
      have hbj0 := ih (t'.erase m).card hcard_lt (t'.erase m) _ rfl
        (exp_elim_sum hq hm_mem hrel') j hj_erase
      exact exp_elim_coeff_ne_zero hq hjm hcm hcj hbj0
    · rw [Finset.not_nonempty_iff_eq_empty] at hcard1
      have ht'eq : t' = {m} := by rw [← Finset.insert_erase hm_mem, hcard1]; rfl
      rw [ht'eq, Finset.sum_singleton] at hrel'
      have hEm0 :
          PowerSeries.expand (q ^ m) (pow_ne_zero m (by omega)) (PowerSeries.exp K) ≠ 0 := by
        intro h0
        have hc0 := congrArg PowerSeries.constantCoeff h0
        rw [PowerSeries.constantCoeff_expand, PowerSeries.constantCoeff_exp, map_zero] at hc0
        exact one_ne_zero hc0
      have hcm0 : (c m : PowerSeries K) = 0 := (mul_eq_zero.mp hrel').resolve_right hEm0
      exact hcm (by ext k; simpa [Polynomial.coeff_coe] using congrArg (PowerSeries.coeff k) hcm0)

/-- The formal exponential series `PowerSeries.exp K` is not a `q`-Mahler Laurent series for any
`q : ℕ`. -/
theorem not_isMahlerSeries_exp (q : ℕ) :
    ¬ IsMahlerSeries q ((PowerSeries.exp K : PowerSeries K) : K⸨X⸩) := by
  intro hmah
  obtain ⟨hq, n, p, hlast, hsum⟩ := isMahlerSeries_iff.mp hmah
  have hps : ∑ i ∈ Finset.range (n + 1),
      ((if h : i < n + 1 then p ⟨i, h⟩ else 0 : K[X]) : PowerSeries K) *
        PowerSeries.expand (q ^ i) (pow_ne_zero i (by omega)) (PowerSeries.exp K) = 0 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    rw [map_zero, map_sum, ← hsum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [i.isLt, ↓reduceDIte, map_mul]
    rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩, RatFunc.coe_coe,
      LaurentSeries.expand_coe]
    rfl
  have hzero := linearIndependent_expand_exp hq (Finset.range (n + 1))
    (fun i ↦ if h : i < n + 1 then p ⟨i, h⟩ else 0) hps n
    (Finset.mem_range.mpr (Nat.lt_succ_self n))
  simp only [Nat.lt_succ_self, ↓reduceDIte] at hzero
  exact hlast hzero

/-- The formal exponential series `PowerSeries.exp K` is not a `q`-Mahler function for any
`q : ℕ`. -/
theorem not_isMahlerFunction_exp (q : ℕ) : ¬ IsMahlerFunction q (PowerSeries.exp K) :=
  fun h ↦ not_isMahlerSeries_exp q h.isMahlerSeries

end Exponential

/-! ### Additional criteria and regularity examples -/

section Examples

/-- A constant power series with transcendental value is not a `q`-Mahler function for any `q`. -/
theorem not_isMahlerFunction_C_of_transcendental {K : Type*} [Field K] [CharZero K] {q : ℕ}
    {c : K} (hc : Transcendental ℚ c) : ¬ IsMahlerFunction q (PowerSeries.C c) :=
  fun h ↦ hc (isMahlerFunction_C_iff.mp h).2

/-- Any power series with algebraic coefficients satisfying a first-order Mahler equation
`a(X) f(X) = b(X) f(X^q)` with `q ≥ 2`, algebraic-coefficient `a, b ∈ K[X]`, and `b ≠ 0` is a
`q`-Mahler function (in particular, solutions of `f(X) = (1 - X) f(X^2)` are `2`-Mahler). -/
theorem isMahlerFunction_of_mul_eq_mul_expand {K : Type*} [Field K] [CharZero K]
    {q : ℕ} (hq : 2 ≤ q) {a b : K[X]} {f : PowerSeries K}
    (hf : ∀ m, IsAlgebraic ℚ (PowerSeries.coeff m f))
    (ha : ∀ m, IsAlgebraic ℚ (a.coeff m)) (hb : ∀ m, IsAlgebraic ℚ (b.coeff m))
    (hb0 : b ≠ 0)
    (heq : (a : PowerSeries K) * f =
      (b : PowerSeries K) * PowerSeries.expand q (by omega) f) :
    IsMahlerFunction q f := by
  rw [isMahlerFunction_iff]
  refine ⟨hq, hf, 1, ![a, -b], fun i m ↦ ?_, ?_, ?_⟩
  · fin_cases i
    · exact ha m
    · simpa [Polynomial.coeff_neg] using (hb m).neg
  · simpa using neg_ne_zero.mpr hb0
  · rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, pow_zero, PowerSeries.expand_one, AlgHom.id_apply, Fin.val_one,
      pow_one, Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.coe_neg, neg_mul,
      ← sub_eq_add_neg]
    exact sub_eq_zero.mpr heq

/-- No formal Laurent series `f : K⸨X⸩` over a characteristic-zero field satisfying
`f ^ 2 = 1 - X` is `q`-Mahler for any `q`. -/
theorem not_isMahlerSeries_of_sq_eq_one_sub_X {K : Type*} [Field K] [CharZero K]
    {q : ℕ} {f : K⸨X⸩} (hf : f ^ 2 = algebraMap (RatFunc K) K⸨X⸩ (1 - RatFunc.X)) :
    ¬ IsMahlerSeries q f := by
  intro hmah
  have halg : IsAlgebraic (RatFunc K) f := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (1 - RatFunc.X), ?_, ?_⟩
    · intro h0
      have hdeg := congrArg Polynomial.natDegree h0
      have h2 : (Polynomial.X ^ 2 - Polynomial.C (1 - RatFunc.X) : (RatFunc K)[X]).natDegree =
          2 := by
        rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
        · exact Polynomial.natDegree_X_pow 2
        · rw [Polynomial.natDegree_neg, Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
          omega
      rw [h2, Polynomial.natDegree_zero] at hdeg
      omega
    · simp [Polynomial.aeval_X, Polynomial.aeval_C, hf]
  obtain ⟨r, hr⟩ := isMahlerSeries_isAlgebraic_mem_range_ratFunc hmah halg
  have hr2 : r ^ 2 = 1 - RatFunc.X :=
    (algebraMap (RatFunc K) K⸨X⸩).injective (by rw [map_pow, hr, hf])
  have hpoly : r.num ^ 2 = (1 - Polynomial.X) * r.denom ^ 2 := by
    apply RatFunc.algebraMap_injective K
    rw [map_pow, map_mul, map_sub, map_one, RatFunc.algebraMap_X, map_pow, ← hr2]
    have hdiv := RatFunc.num_div_denom r
    have hmul : r * algebraMap K[X] (RatFunc K) r.denom = algebraMap K[X] (RatFunc K) r.num :=
      (eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r))).mp hdiv.symm
    rw [← hmul, mul_pow]
  have h1X : (1 - Polynomial.X : K[X]) ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.eval (0 : K)) h0
    simp at this
  have h1Xdeg : (1 - Polynomial.X : K[X]).natDegree = 1 := by
    rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_right_of_natDegree_lt]
    · simp
    · simp
  have hdeg := congrArg Polynomial.natDegree hpoly
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_mul h1X
    (pow_ne_zero 2 (RatFunc.denom_ne_zero r)), h1Xdeg, Polynomial.natDegree_pow] at hdeg
  omega

private theorem denom_inv_one_sub_two_X_eval_eq_zero_iff {K : Type*} [Field K] [CharZero K]
    (z : K) :
    ((algebraMap K[X] (RatFunc K) (1 - 2 * Polynomial.X))⁻¹).denom.eval z = 0 ↔
      1 - 2 * z = 0 := by
  let q : K[X] := 1 - 2 * Polynomial.X
  let r : RatFunc K := (algebraMap K[X] (RatFunc K) q)⁻¹
  have hq0 : q ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.eval (0 : K)) h0
    simp [q] at this
  have hr : r = algebraMap K[X] (RatFunc K) 1 / algebraMap K[X] (RatFunc K) q := by
    simp [r]
  have hdvd₁ : r.denom ∣ q := hr ▸ RatFunc.denom_div_dvd 1 q
  have hmul : r.num * q = r.denom := by
    apply RatFunc.algebraMap_injective K
    rw [map_mul]
    have hdiv := RatFunc.num_div_denom r
    have h1 : algebraMap K[X] (RatFunc K) r.num / algebraMap K[X] (RatFunc K) r.denom =
        1 / algebraMap K[X] (RatFunc K) q := by
      rw [hdiv]
      simp [r]
    have := (div_eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r))
      (RatFunc.algebraMap_ne_zero hq0)).mp h1
    simpa using this
  have hdvd₂ : q ∣ r.denom := ⟨r.num, by rw [← hmul, mul_comm]⟩
  constructor
  · intro hz
    obtain ⟨c, hc⟩ := hdvd₁
    have : q.eval z = 0 := by rw [hc, Polynomial.eval_mul, hz, zero_mul]
    simpa [q] using this
  · intro hz
    obtain ⟨c, hc⟩ := hdvd₂
    have hqz : q.eval z = 0 := by simpa [q] using hz
    rw [hc, Polynomial.eval_mul, hqz, zero_mul]

/-- For `A = !![(1 - 2X)⁻¹]`, the point `(Real.sqrt 2)⁻¹` is not `2`-regular because its
square `1/2` is a pole of `A`. -/
theorem not_isMahlerRegularPoint_inv_one_sub_two_X_two :
    ¬ IsMahlerRegularPoint 2
      (!![(algebraMap ℝ[X] (RatFunc ℝ) (1 - 2 * Polynomial.X))⁻¹] : Matrix (Fin 1) (Fin 1) _)
      (Real.sqrt 2)⁻¹ := by
  intro h
  have h1 := h.denom_eval_ne_zero 1 0 0
  simp only [Matrix.of_apply, Matrix.cons_val_zero, pow_one] at h1
  apply h1
  rw [denom_inv_one_sub_two_X_eval_eq_zero_iff]
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- For `A = !![(1 - 2X)⁻¹]`, the point `(Real.sqrt 2)⁻¹` is `3`-regular because
`(Real.sqrt 2)⁻¹ ^ (3 ^ ℓ) ≠ 1/2` for every `ℓ : ℕ`. -/
theorem isMahlerRegularPoint_inv_one_sub_two_X_three :
    IsMahlerRegularPoint 3
      (!![(algebraMap ℝ[X] (RatFunc ℝ) (1 - 2 * Polynomial.X))⁻¹] : Matrix (Fin 1) (Fin 1) _)
      (Real.sqrt 2)⁻¹ := by
  let q : ℝ[X] := 1 - 2 * Polynomial.X
  let A : Matrix (Fin 1) (Fin 1) (RatFunc ℝ) := !![(algebraMap ℝ[X] (RatFunc ℝ) q)⁻¹]
  have hq0 : q ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.eval (0 : ℝ)) h0
    simp [q] at this
  have hAinv : A⁻¹ = !![algebraMap ℝ[X] (RatFunc ℝ) q] := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i; fin_cases j
    simp [A, Matrix.mul_apply, mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hq0)]
  have hsqrt_gt1 : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrt_pos : 0 < Real.sqrt 2 := by linarith
  rw [isMahlerRegularPoint_iff]
  refine ⟨by norm_num, ?_, ?_, ?_, fun ℓ i j ↦ ?_⟩
  · rw [Matrix.det_fin_one]
    exact inv_ne_zero (RatFunc.algebraMap_ne_zero hq0)
  · rw [Real.norm_of_nonneg (inv_nonneg.mpr hsqrt_pos.le)]
    exact inv_pos.mpr hsqrt_pos
  · rw [Real.norm_of_nonneg (inv_nonneg.mpr hsqrt_pos.le)]
    exact inv_lt_one_of_one_lt₀ hsqrt_gt1
  · fin_cases i; fin_cases j
    refine ⟨?_, ?_⟩
    · simp only [Matrix.of_apply, Matrix.cons_val_fin_one]
      intro hz
      rw [denom_inv_one_sub_two_X_eval_eq_zero_iff] at hz
      have hval : ((Real.sqrt 2)⁻¹) ^ (3 ^ ℓ) = (2 : ℝ)⁻¹ := by linarith
      have hsq := congrArg (fun x : ℝ ↦ x ^ 2) hval
      rw [← pow_mul, mul_comm (3 ^ ℓ) 2, pow_mul, inv_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), inv_pow, inv_pow] at hsq
      have hpow : (2 : ℝ) ^ (3 ^ ℓ) = (2 : ℝ) ^ 2 := inv_injective hsq
      have hpowN : (2 : ℕ) ^ (3 ^ ℓ) = (2 : ℕ) ^ 2 := by exact_mod_cast hpow
      have h32 : 3 ^ ℓ = 2 := Nat.pow_right_injective (by norm_num) hpowN
      have hmod := congrArg (· % 2) h32
      rw [Nat.pow_mod] at hmod
      norm_num at hmod
    · rw [hAinv]
      simp

end Examples

end TauCeti
