/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Valued.NormedValued
import TauCeti.Analysis.Normed.Algebra.Logarithm.Basic
import TauCeti.NumberTheory.Padics.Factorial
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.Valuation.Polynomial

/-!
# The `p`-adic exponential and logarithm on the convergence disc

Let `p` be a prime and set `ρ_p = p ^ (-1 / (p - 1))`, written `TauCeti.padicExpRadius p`.
Over any normed `ℚ_[p]`-algebra `A` with `‖1‖ = 1`, Legendre's formula
`(p - 1) * v_p(n!) = n - s_p(n) ≤ n - 1` (for `n ≥ 1`, where `s_p(n) ≥ 1` is the base-`p` digit
sum of `n`) yields the sharp factorial lower bound

`ρ_p ^ (n - 1) ≤ ‖(n ! : A)‖`,

attained at every prime power `n = p ^ k`. Consequently, Mathlib's `NormedSpace.expSeries ℚ_[p] A`
has exact radius of convergence `ρ_p`.

The convergence disc of the exponential is open: at `p = 2`, the point `2` satisfies
`‖2‖ = ρ_2 = 1 / 2`, and the terms `2 ^ n / n !` have norm `1 / 2` at every power of `2`. For odd
primes `p`, `p⁻¹ < ρ_p` so `p` lies strictly inside the disc; more generally, a depth `p ^ (-i)`
lies inside the disc exactly when `1 < (p - 1) * i`.

In a complete normed field `L` over `ℚ_[p]` (such as `ℚ_[p]`, any finite extension of `ℚ_[p]`, or
`ℂ_[p]`), the norm is ultrametric (`IsUltrametricDist.of_normedAlgebra`). On the open disc
`‖x‖ < ρ_p`, the exponential satisfies the additive functional equation
`exp (x + y) = exp x * exp y` and its finite-sum and integer-multiple forms, preserves distances
(`‖exp x - exp y‖ = ‖x - y‖`, `‖exp x - 1‖ = ‖x‖`, `‖exp x‖ = 1`), and restricts to an isometric
bijection onto the open disc `‖y - 1‖ < ρ_p`, with `NormedSpace.log` as its two-sided inverse.
On `‖y - 1‖ < ρ_p` the logarithm is likewise an isometry (`‖log u - log v‖ = ‖u - v‖`,
`‖log y‖ = ‖y - 1‖`) and turns products into sums (`log (u * v) = log u + log v`). The identity
`exp (log y) = y` cannot be enlarged to the convergence disc `‖y - 1‖ < 1` of the logarithm: at
`p = 2`, `y = -1` has `‖y - 1‖ = ρ_2` and `log (-1) = 0`, so `exp (log (-1)) = 1 ≠ -1`.

## Main definitions

* `TauCeti.padicExpRadius`: the real radius `p ^ (-1 / (p - 1))` of convergence of the `p`-adic
  exponential series.

## Main results

* `TauCeti.padicExpRadius_pos`, `TauCeti.padicExpRadius_lt_one`,
  `TauCeti.padicExpRadius_pow_sub_one`, `TauCeti.inv_lt_padicExpRadius_iff`,
  `TauCeti.zpow_neg_lt_padicExpRadius_iff`: basic properties of `padicExpRadius p`.
* `TauCeti.padicExpRadius_pow_sub_one_le_norm_factorial`, `TauCeti.norm_factorial_prime_pow`,
  `TauCeti.padicExpRadius_pow_sub_one_le_norm_natCast`: sharp lower bounds on `‖n!‖` and `‖n‖`.
* `TauCeti.norm_pow_div_factorial_le`, `TauCeti.norm_pow_div_natCast_le`: term estimates for the
  exponential and logarithm series.
* `TauCeti.ofReal_padicExpRadius_le_radius_expSeries`,
  `TauCeti.radius_expSeries_eq_ofReal_padicExpRadius`: convergence radius of
  `NormedSpace.expSeries`.
* `TauCeti.padicExp_add`, `TauCeti.padicExp_neg`, `TauCeti.padicExp_sub`, `TauCeti.padicExp_sum`,
  `TauCeti.padicExp_natCast_mul`, `TauCeti.padicExp_intCast_mul`: functional equations of
  `NormedSpace.exp` on the open disc `‖x‖ < padicExpRadius p`.
* `TauCeti.norm_padicExp_sub_one`, `TauCeti.norm_padicExp`, `TauCeti.norm_padicExp_sub_padicExp`,
  `TauCeti.injOn_padicExp`: isometry and injectivity of `NormedSpace.exp`.
* `TauCeti.norm_log_sub_log`, `TauCeti.norm_log_eq_norm_sub_one`, `TauCeti.injOn_padicLog`,
  `TauCeti.log_padicExp`, `TauCeti.padicExp_log`, `TauCeti.padicLog_mul`,
  `TauCeti.bijOn_padicExp`, `TauCeti.bijOn_padicLog`: isometry, homomorphism property, and mutual
  inversion of `NormedSpace.exp` and `NormedSpace.log` on the open discs of radius
  `padicExpRadius p`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58, Springer,
  1984, Chapter IV, §1.
-/

public section

open Filter Topology
open scoped Nat NNReal ENNReal Polynomial

namespace TauCeti

/-! ### The `p`-adic exponential convergence radius -/

/-- The radius `p ^ (-1 / (p - 1))` of the open disc on which the `p`-adic exponential series
converges, written as a real power. -/
noncomputable def padicExpRadius (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)

/-- Unfolding lemma for `padicExpRadius`. -/
theorem padicExpRadius_def (p : ℕ) :
    padicExpRadius p = (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := (rfl)

/-- At `p = 2`, the `p`-adic exponential convergence radius is `2⁻¹`. -/
@[simp]
theorem padicExpRadius_two : padicExpRadius 2 = 2⁻¹ := by
  rw [padicExpRadius_def]
  norm_num

section Radius

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-adic exponential convergence radius is positive for every prime `p`. -/
theorem padicExpRadius_pos : 0 < padicExpRadius p := by
  rw [padicExpRadius_def]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _

/-- The `p`-adic exponential convergence radius is strictly less than `1` for every prime `p`. -/
theorem padicExpRadius_lt_one : padicExpRadius p < 1 := by
  rw [padicExpRadius_def]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_lt_zero.mpr (inv_pos.mpr (sub_pos.mpr hp1)))

/-- Raising `padicExpRadius p` to the `(p - 1)`-st power gives `p⁻¹`. -/
theorem padicExpRadius_pow_sub_one : padicExpRadius p ^ (p - 1) = (p : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  rw [padicExpRadius_def, ← Real.rpow_natCast, ← Real.rpow_mul hp0, hsub, neg_mul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hp1.ne'), Real.rpow_neg_one]

/-- For every prime `p`, `p⁻¹ ≤ padicExpRadius p`. -/
theorem inv_le_padicExpRadius : (p : ℝ)⁻¹ ≤ padicExpRadius p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have h2 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
    linarith
  rw [padicExpRadius_def, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hp1.le (neg_le_neg (inv_le_one_of_one_le₀ h2))

/-- The `p`-adic norm `p⁻¹` of `p` lies strictly inside the open exponential convergence disc
exactly when `p` is odd. -/
theorem inv_lt_padicExpRadius_iff : (p : ℝ)⁻¹ < padicExpRadius p ↔ p ≠ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [padicExpRadius_def, ← Real.rpow_neg_one, Real.rpow_lt_rpow_left_iff hp1, neg_lt_neg_iff,
    inv_lt_one_iff₀]
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hp1
  constructor
  · rintro (h | h)
    · linarith
    · intro h2
      subst h2
      norm_num at h
  · intro hne
    right
    have h3 : (3 : ℕ) ≤ p := by
      have := hp.out.two_le
      omega
    have : (3 : ℝ) ≤ p := by exact_mod_cast h3
    linarith

/-- A power `p ^ (-i)` lies strictly inside the open exponential convergence disc of radius
`padicExpRadius p` exactly when `1 < (p - 1) * i`. -/
theorem zpow_neg_lt_padicExpRadius_iff (i : ℕ) :
    (p : ℝ) ^ (-(i : ℤ)) < padicExpRadius p ↔ 1 < (p - 1) * i := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  rw [padicExpRadius_def, ← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast,
    Real.rpow_lt_rpow_left_iff hp1, neg_lt_neg_iff, inv_lt_iff_one_lt_mul₀ (sub_pos.mpr hp1),
    ← hsub, mul_comm (i : ℝ), ← Nat.cast_mul, ← Nat.cast_one, Nat.cast_lt]

end Radius

/-! ### Factorial bounds and convergence radii in normed `ℚ_[p]`-algebras -/

section NormedAlgebra

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Sharp `p`-adic lower bound on `n!`.** In every seminormed `ℚ_[p]`-algebra `A` with `‖1‖ = 1`,
`padicExpRadius p ^ (n - 1) ≤ ‖(n ! : A)‖` for every `n ≥ 1`. Equality holds at every power of
`p` (`norm_factorial_prime_pow`). -/
theorem padicExpRadius_pow_sub_one_le_norm_factorial {A : Type*} [SeminormedRing A]
    [NormOneClass A] [NormedAlgebra ℚ_[p] A] {n : ℕ} (hn : n ≠ 0) :
    padicExpRadius p ^ (n - 1) ≤ ‖(n ! : A)‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] A), norm_algebraMap',
    Padic.norm_natCast_eq_zpow (Nat.factorial_ne_zero n)]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  have hsub : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.out.one_lt
  refine (pow_le_pow_iff_left₀ (pow_nonneg (padicExpRadius_pos p).le _)
    (zpow_nonneg (Nat.cast_nonneg p) _) hsub).mp ?_
  rw [← pow_mul, mul_comm (n - 1), pow_mul, padicExpRadius_pow_sub_one, inv_pow,
    ← zpow_natCast, ← zpow_neg, ← zpow_natCast, ← zpow_mul]
  refine zpow_le_zpow_right₀ hp1 ?_
  have hleg : (p - 1) * padicValNat p n ! ≤ n - 1 := by
    rw [Nat.padicValNat_def]
    exact Nat.le_sub_one_of_lt (sub_one_mul_multiplicity_factorial_lt_of_ne_zero p hn)
  have hcast : ((p - 1 : ℕ) : ℤ) * (padicValNat p n ! : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
    exact_mod_cast hleg
  linarith [hcast]

/-- At every prime power `p ^ k`, the factorial lower bound is attained:
`‖((p ^ k)! : A)‖ = padicExpRadius p ^ (p ^ k - 1)`. -/
theorem norm_factorial_prime_pow {A : Type*} [SeminormedRing A] [NormOneClass A]
    [NormedAlgebra ℚ_[p] A] (k : ℕ) :
    ‖((p ^ k)! : A)‖ = padicExpRadius p ^ (p ^ k - 1) := by
  rw [← map_natCast (algebraMap ℚ_[p] A), norm_algebraMap',
    Padic.norm_natCast_eq_zpow (Nat.factorial_ne_zero _)]
  have hsub : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.out.one_lt
  refine (pow_left_inj₀ (zpow_nonneg (Nat.cast_nonneg p) _)
    (pow_nonneg (padicExpRadius_pos p).le _) hsub).mp ?_
  rw [← pow_mul, mul_comm (p ^ k - 1), pow_mul, padicExpRadius_pow_sub_one, ← zpow_neg_one,
    ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul]
  congr 1
  have hleg := sub_one_mul_padicValNat_factorial_pow p k
  have hcast : ((p - 1 : ℕ) : ℤ) * (padicValNat p (p ^ k)! : ℤ) = ((p ^ k - 1 : ℕ) : ℤ) := by
    exact_mod_cast hleg
  linarith [hcast]

/-- For every `n ≥ 1`, `padicExpRadius p ^ (n - 1) ≤ ‖(n : A)‖` in any seminormed `ℚ_[p]`-algebra
`A` with `‖1‖ = 1`. -/
theorem padicExpRadius_pow_sub_one_le_norm_natCast {A : Type*} [SeminormedRing A]
    [NormOneClass A] [NormedAlgebra ℚ_[p] A] {n : ℕ} (hn : n ≠ 0) :
    padicExpRadius p ^ (n - 1) ≤ ‖(n : A)‖ := by
  refine (padicExpRadius_pow_sub_one_le_norm_factorial (p := p) (A := A) hn).trans ?_
  rw [← map_natCast (algebraMap ℚ_[p] A), ← map_natCast (algebraMap ℚ_[p] A),
    norm_algebraMap', norm_algebraMap']
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hn) le_rfl
  rw [hk, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using Padic.norm_int_le_one (p := p) k)

/-- **Exponential term bound.** In a normed division ring `L` over `ℚ_[p]`,
`‖x ^ n / n !‖ ≤ ‖x‖ * (‖x‖ / padicExpRadius p) ^ (n - 1)` for every `n ≥ 1`. -/
theorem norm_pow_div_factorial_le {L : Type*} [NormedDivisionRing L] [NormedAlgebra ℚ_[p] L]
    (x : L) {n : ℕ} (hn : n ≠ 0) :
    ‖x ^ n / (n ! : L)‖ ≤ ‖x‖ * (‖x‖ / padicExpRadius p) ^ (n - 1) := by
  have hρ : 0 < padicExpRadius p := padicExpRadius_pos p
  have hfac : padicExpRadius p ^ (n - 1) ≤ ‖(n ! : L)‖ :=
    padicExpRadius_pow_sub_one_le_norm_factorial hn
  rw [norm_div, norm_pow, div_pow, mul_div_assoc', ← pow_succ',
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
  exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg x) n) (pow_pos hρ _) hfac

/-- **Logarithm term bound.** In a normed division ring `L` over `ℚ_[p]`,
`‖x ^ n / n‖ ≤ ‖x‖ * (‖x‖ / padicExpRadius p) ^ (n - 1)` for every `n ≥ 1`. -/
theorem norm_pow_div_natCast_le {L : Type*} [NormedDivisionRing L] [NormedAlgebra ℚ_[p] L]
    (x : L) {n : ℕ} (hn : n ≠ 0) :
    ‖x ^ n / (n : L)‖ ≤ ‖x‖ * (‖x‖ / padicExpRadius p) ^ (n - 1) := by
  have hρ : 0 < padicExpRadius p := padicExpRadius_pos p
  have hnat : padicExpRadius p ^ (n - 1) ≤ ‖(n : L)‖ :=
    padicExpRadius_pow_sub_one_le_norm_natCast hn
  rw [norm_div, norm_pow, div_pow, mul_div_assoc', ← pow_succ',
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
  exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg x) n) (pow_pos hρ _) hnat

/-- **Lower bound on the convergence radius of the `p`-adic exponential series.** In every normed
`ℚ_[p]`-algebra `A`, `NormedSpace.expSeries ℚ_[p] A` has convergence radius at least
`padicExpRadius p`. -/
theorem ofReal_padicExpRadius_le_radius_expSeries (A : Type*) [NormedRing A]
    [NormedAlgebra ℚ_[p] A] :
    ENNReal.ofReal (padicExpRadius p) ≤ (NormedSpace.expSeries ℚ_[p] A).radius := by
  have hρ : 0 < padicExpRadius p := padicExpRadius_pos p
  rw [ENNReal.ofReal_eq_coe_nnreal hρ.le]
  refine (NormedSpace.expSeries ℚ_[p] A).le_radius_of_bound
    (max ‖NormedSpace.expSeries ℚ_[p] A 0‖ 1) fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hcoeff : ‖NormedSpace.expSeries ℚ_[p] A n‖ ≤ ‖(n ! : ℚ_[p])‖⁻¹ := by
      rw [NormedSpace.expSeries_eq_ofScalars]
      exact (FormalMultilinearSeries.ofScalars_norm_le A _ n hn).trans_eq (norm_inv _)
    have hfac : padicExpRadius p ^ (n - 1) ≤ ‖(n ! : ℚ_[p])‖ :=
      padicExpRadius_pow_sub_one_le_norm_factorial hn.ne'
    have hr : ((⟨padicExpRadius p, hρ.le⟩ : ℝ≥0) : ℝ) ^ n =
        padicExpRadius p * padicExpRadius p ^ (n - 1) := by
      rw [Subtype.coe_mk, ← pow_succ', Nat.sub_add_cancel hn]
    calc ‖NormedSpace.expSeries ℚ_[p] A n‖ * ((⟨padicExpRadius p, hρ.le⟩ : ℝ≥0) : ℝ) ^ n
        ≤ ‖(n ! : ℚ_[p])‖⁻¹ * (padicExpRadius p * padicExpRadius p ^ (n - 1)) := by
          rw [← hr]
          exact mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hρ.le n)
      _ ≤ (padicExpRadius p ^ (n - 1))⁻¹ * (padicExpRadius p * padicExpRadius p ^ (n - 1)) := by
          gcongr
      _ = padicExpRadius p := by field_simp [hρ.ne']
      _ ≤ 1 := (padicExpRadius_lt_one p).le
      _ ≤ max ‖NormedSpace.expSeries ℚ_[p] A 0‖ 1 := le_max_right _ _

/-- **Exact convergence radius of the `p`-adic exponential series.** In every normed `ℚ_[p]`-algebra
`A` with `‖1‖ = 1`, `NormedSpace.expSeries ℚ_[p] A` has radius of convergence exactly
`padicExpRadius p`. -/
theorem radius_expSeries_eq_ofReal_padicExpRadius (A : Type*) [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℚ_[p] A] :
    (NormedSpace.expSeries ℚ_[p] A).radius = ENNReal.ofReal (padicExpRadius p) := by
  refine le_antisymm ?_ (ofReal_padicExpRadius_le_radius_expSeries A)
  -- Any `r > padicExpRadius p` makes `‖expSeries (p^k)‖ * r^(p^k) = ρ_p * (r / ρ_p)^(p^k) → ∞`.
  refine iSup₂_le fun r C ↦ iSup_le fun hC ↦ ?_
  by_contra! hlt
  have hρ : 0 < padicExpRadius p := padicExpRadius_pos p
  rw [ENNReal.ofReal_eq_coe_nnreal hρ.le, ENNReal.coe_lt_coe] at hlt
  have hlt' : padicExpRadius p < (r : ℝ) := NNReal.coe_lt_coe.mpr hlt
  have hq : 1 < (r : ℝ) / padicExpRadius p := (one_lt_div hρ).mpr hlt'
  have htend : Tendsto (fun k : ℕ ↦ padicExpRadius p * ((r : ℝ) / padicExpRadius p) ^ (p ^ k))
      atTop atTop :=
    Filter.Tendsto.const_mul_atTop hρ
      ((tendsto_pow_atTop_atTop_of_one_lt hq).comp
        (tendsto_pow_atTop_atTop_of_one_lt hp.out.one_lt))
  obtain ⟨k, hk⟩ := (htend.eventually_gt_atTop C).exists
  have hk_le := hC (p ^ k)
  rw [NormedSpace.expSeries_eq_ofScalars, FormalMultilinearSeries.ofScalars_norm, norm_inv,
    norm_factorial_prime_pow (A := ℚ_[p]) k] at hk_le
  have hpow : (padicExpRadius p ^ (p ^ k - 1))⁻¹ * (r : ℝ) ^ (p ^ k) =
      padicExpRadius p * ((r : ℝ) / padicExpRadius p) ^ (p ^ k) := by
    have hpk : 1 ≤ p ^ k := Nat.one_le_pow k p hp.out.pos
    rw [div_pow, mul_div_assoc', inv_mul_eq_div,
      div_eq_div_iff (pow_ne_zero _ hρ.ne') (pow_ne_zero _ hρ.ne')]
    calc (r : ℝ) ^ (p ^ k) * padicExpRadius p ^ (p ^ k)
        = (r : ℝ) ^ (p ^ k) * (padicExpRadius p * padicExpRadius p ^ (p ^ k - 1)) := by
          rw [← pow_succ', Nat.sub_add_cancel hpk]
      _ = padicExpRadius p * (r : ℝ) ^ (p ^ k) * padicExpRadius p ^ (p ^ k - 1) := by ring
  linarith

/-- Every element of norm strictly less than `padicExpRadius p` lies inside the open ball of
convergence of `NormedSpace.expSeries ℚ_[p] A`. -/
theorem mem_eball_radius_expSeries_of_norm_lt {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A]
    {x : A} (hx : ‖x‖ < padicExpRadius p) :
    x ∈ Metric.eball (0 : A) (NormedSpace.expSeries ℚ_[p] A).radius := by
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff (padicExpRadius_pos p)).mpr hx |>.trans_le
    (ofReal_padicExpRadius_le_radius_expSeries A)

/-- On the open disc `‖x‖ < padicExpRadius p` of a complete normed division ring over `ℚ_[p]`,
the exponential series `∑ x ^ n / n !` converges to `NormedSpace.exp x`. -/
theorem hasSum_padicExp {L : Type*} [NormedDivisionRing L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] {x : L} (hx : ‖x‖ < padicExpRadius p) :
    HasSum (fun n : ℕ ↦ x ^ n / (n ! : L)) (NormedSpace.exp x) :=
  NormedSpace.expSeries_div_hasSum_exp_of_mem_ball ℚ_[p] x
    (mem_eball_radius_expSeries_of_norm_lt hx)

end NormedAlgebra

/-! ### Functional equations and isometry of `NormedSpace.exp` on the `p`-adic disc -/

section ExpDisc

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Functional equation of the `p`-adic exponential.** In a complete commutative normed
`ℚ_[p]`-algebra, `exp (x + y) = exp x * exp y` whenever `‖x‖ < padicExpRadius p` and
`‖y‖ < padicExpRadius p`. -/
theorem padicExp_add {A : Type*} [NormedCommRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]
    {x y : A} (hx : ‖x‖ < padicExpRadius p) (hy : ‖y‖ < padicExpRadius p) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  NormedSpace.exp_add_of_mem_ball (𝕂 := ℚ_[p])
    (mem_eball_radius_expSeries_of_norm_lt hx) (mem_eball_radius_expSeries_of_norm_lt hy)

/-- On the open disc `‖x‖ < padicExpRadius p`, `exp (-x) = (exp x)⁻¹`. -/
theorem padicExp_neg {L : Type*} [NormedDivisionRing L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] {x : L} (hx : ‖x‖ < padicExpRadius p) :
    NormedSpace.exp (-x) = (NormedSpace.exp x)⁻¹ :=
  NormedSpace.exp_neg_of_mem_ball (𝕂 := ℚ_[p]) (mem_eball_radius_expSeries_of_norm_lt hx)

/-- On the open disc `‖x‖ < padicExpRadius p`, `exp (x - y) = exp x / exp y`. -/
theorem padicExp_sub {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
    {x y : L} (hx : ‖x‖ < padicExpRadius p) (hy : ‖y‖ < padicExpRadius p) :
    NormedSpace.exp (x - y) = NormedSpace.exp x / NormedSpace.exp y := by
  rw [sub_eq_add_neg, padicExp_add hx (by simpa using hy), padicExp_neg hy, div_eq_mul_inv]

/-- **Finite-product functional equation of the `p`-adic exponential.** If every `f i` for
`i ∈ s` satisfies `‖f i‖ < padicExpRadius p`, then `exp (∑ i ∈ s, f i) = ∏ i ∈ s, exp (f i)`. -/
theorem padicExp_sum {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
    {ι : Type*} (s : Finset ι) {f : ι → L} (hf : ∀ i ∈ s, ‖f i‖ < padicExpRadius p) :
    NormedSpace.exp (∑ i ∈ s, f i) = ∏ i ∈ s, NormedSpace.exp (f i) := by
  classical
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  induction s using Finset.induction_on with
  | empty => simp [NormedSpace.exp_zero]
  | insert a s ha ih =>
    have hfa : ‖f a‖ < padicExpRadius p := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, ‖f i‖ < padicExpRadius p :=
      fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hsum : ‖∑ i ∈ s, f i‖ < padicExpRadius p := by
      rcases s.eq_empty_or_nonempty with rfl | hs
      · simpa using padicExpRadius_pos p
      · exact (hs.norm_sum_le_sup'_norm f).trans_lt ((Finset.sup'_lt_iff hs).mpr hfs)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, padicExp_add hfa hsum, ih hfs]

/-- For every natural number `n` and `‖x‖ < padicExpRadius p`, `exp (n * x) = (exp x) ^ n`. -/
theorem padicExp_natCast_mul {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℚ_[p] A]
    [CompleteSpace A] (n : ℕ) {x : A} (hx : ‖x‖ < padicExpRadius p) :
    NormedSpace.exp ((n : A) * x) = NormedSpace.exp x ^ n := by
  induction n with
  | zero => simp [NormedSpace.exp_zero]
  | succ n ih =>
    have hnx : ‖(n : A) * x‖ < padicExpRadius p := by
      have hn : ‖(n : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) n
      calc ‖(n : A) * x‖ ≤ ‖(n : A)‖ * ‖x‖ := norm_mul_le _ _
        _ = ‖(n : ℚ_[p])‖ * ‖x‖ := by rw [← map_natCast (algebraMap ℚ_[p] A), norm_algebraMap']
        _ ≤ 1 * ‖x‖ := by gcongr
        _ = ‖x‖ := one_mul _
        _ < padicExpRadius p := hx
    have hcomm : Commute ((n : A) * x) x := (Nat.cast_commute n x).mul_left (Commute.refl x)
    rw [Nat.cast_succ, add_mul, one_mul,
      NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℚ_[p]) hcomm
        (mem_eball_radius_expSeries_of_norm_lt hnx) (mem_eball_radius_expSeries_of_norm_lt hx),
      ih, pow_succ]

/-- For every integer `n` and `‖x‖ < padicExpRadius p`, `exp (n * x) = (exp x) ^ n`. The open
exponential disc is stable under integer multiples since `‖(n : L)‖ ≤ 1`. -/
theorem padicExp_intCast_mul {L : Type*} [NormedDivisionRing L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] (n : ℤ) {x : L} (hx : ‖x‖ < padicExpRadius p) :
    NormedSpace.exp ((n : L) * x) = NormedSpace.exp x ^ n := by
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast, zpow_natCast]
    exact padicExp_natCast_mul m hx
  | negSucc m =>
    have hmx : ‖((m + 1 : ℕ) : L) * x‖ < padicExpRadius p := by
      rw [norm_mul, ← map_natCast (algebraMap ℚ_[p] L), norm_algebraMap']
      have hm : ‖((m + 1 : ℕ) : ℚ_[p])‖ ≤ 1 := by
        simpa using Padic.norm_int_le_one (p := p) (m + 1 : ℕ)
      exact (mul_le_of_le_one_left (norm_nonneg x) hm).trans_lt hx
    rw [Int.cast_negSucc, neg_mul, padicExp_neg hmx, padicExp_natCast_mul (m + 1) hx, zpow_negSucc]

/-- On the open disc `‖x‖ < padicExpRadius p`, the higher-order tail `exp x - 1 - x` has norm at
most `‖x‖ * (‖x‖ / padicExpRadius p)`. -/
theorem norm_padicExp_sub_one_sub_le {L : Type*} [NormedDivisionRing L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] {x : L} (hx : ‖x‖ < padicExpRadius p) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ * (‖x‖ / padicExpRadius p) := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hsum : HasSum (fun n : ℕ ↦ if n < 2 then (0 : L) else x ^ n / (n ! : L))
      (NormedSpace.exp x - 1 - x) := by
    have h01 := ((hasSum_padicExp hx).sub (hasSum_ite_eq 0 (1 : L))).sub (hasSum_ite_eq 1 x)
    refine h01.congr_fun fun n ↦ ?_
    rcases n with _ | _ | n <;> simp
  rw [← hsum.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n ↦ ?_
  split_ifs with hn
  · simp [mul_nonneg (norm_nonneg x) (div_nonneg (norm_nonneg x) (padicExpRadius_pos p).le)]
  · push Not at hn
    have hq : ‖x‖ / padicExpRadius p ≤ 1 := (div_le_one (padicExpRadius_pos p)).mpr hx.le
    calc ‖x ^ n / (n ! : L)‖
        ≤ ‖x‖ * (‖x‖ / padicExpRadius p) ^ (n - 1) := norm_pow_div_factorial_le x (by omega)
      _ ≤ ‖x‖ * (‖x‖ / padicExpRadius p) ^ 1 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (div_nonneg (norm_nonneg x) (padicExpRadius_pos p).le) hq
              (by omega))
            (norm_nonneg x)
      _ = ‖x‖ * (‖x‖ / padicExpRadius p) := by rw [pow_one]

/-- **Isometry of the `p`-adic exponential at zero.** For `‖x‖ < padicExpRadius p`,
`‖exp x - 1‖ = ‖x‖`. -/
theorem norm_padicExp_sub_one {L : Type*} [NormedDivisionRing L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] {x : L} (hx : ‖x‖ < padicExpRadius p) :
    ‖NormedSpace.exp x - 1‖ = ‖x‖ := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [NormedSpace.exp_zero]
  have hlt : ‖NormedSpace.exp x - 1 - x‖ < ‖x‖ := by
    refine (norm_padicExp_sub_one_sub_le hx).trans_lt ?_
    exact mul_lt_of_lt_one_right (norm_pos_iff.mpr hx0)
      ((div_lt_one (padicExpRadius_pos p)).mpr hx)
  rw [← sub_add_cancel (NormedSpace.exp x - 1) x,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le]

/-- Every value of the `p`-adic exponential on its open convergence disc has norm `1`. -/
theorem norm_padicExp {L : Type*} [NormedDivisionRing L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] {x : L} (hx : ‖x‖ < padicExpRadius p) :
    ‖NormedSpace.exp x‖ = 1 := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hlt : ‖NormedSpace.exp x - 1‖ < ‖(1 : L)‖ := by
    rw [norm_padicExp_sub_one hx, norm_one]
    exact hx.trans (padicExpRadius_lt_one p)
  rw [← sub_add_cancel (NormedSpace.exp x) 1,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le, norm_one]

/-- **The `p`-adic exponential is an isometry on its open convergence disc.** For `x, y` with norm
strictly less than `padicExpRadius p`, `‖exp x - exp y‖ = ‖x - y‖`. -/
theorem norm_padicExp_sub_padicExp {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] {x y : L} (hx : ‖x‖ < padicExpRadius p) (hy : ‖y‖ < padicExpRadius p) :
    ‖NormedSpace.exp x - NormedSpace.exp y‖ = ‖x - y‖ := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hxy : ‖x - y‖ < padicExpRadius p := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max x (-y)).trans_lt (by simpa using max_lt hx hy)
  have hfac : NormedSpace.exp x - NormedSpace.exp y =
      NormedSpace.exp y * (NormedSpace.exp (x - y) - 1) := by
    rw [mul_sub, mul_one, ← padicExp_add hy hxy, add_sub_cancel]
  rw [hfac, norm_mul, norm_padicExp hy, one_mul, norm_padicExp_sub_one hxy]

/-- The `p`-adic exponential is injective on the open disc of radius `padicExpRadius p` about
zero. -/
theorem injOn_padicExp (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L] :
    Set.InjOn (NormedSpace.exp : L → L) (Metric.ball 0 (padicExpRadius p)) := by
  intro x hx y hy hxy
  rw [mem_ball_zero_iff] at hx hy
  have h := norm_padicExp_sub_padicExp hx hy
  rw [hxy, sub_self, norm_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)

end ExpDisc

/-! ### The `p`-adic logarithm and mutual inversion on the exponential disc -/

section LogDisc

variable {p : ℕ} [hp : Fact p.Prime]

/-- Termwise bound for the difference of two `p`-adic logarithm series at commuting arguments `u, v`
in the open disc of radius `padicExpRadius p` about `1`. -/
private theorem norm_logSeries_diff_term_le {L : Type*} [NormedDivisionRing L]
    [NormedAlgebra ℚ_[p] L] {u v : L} (huv : Commute u v) (hu : ‖u - 1‖ < padicExpRadius p)
    (hv : ‖v - 1‖ < padicExpRadius p) {n : ℕ} (hn : 2 ≤ n) :
    ‖((-1 : ℚ_[p]) ^ (n + 1) / n) • ((u - 1) ^ n - (v - 1) ^ n)‖ ≤
      ‖u - v‖ * (max ‖u - 1‖ ‖v - 1‖ / padicExpRadius p) := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hρ : 0 < padicExpRadius p := padicExpRadius_pos p
  have hm : max ‖u - 1‖ ‖v - 1‖ < padicExpRadius p := max_lt hu hv
  have hm0 : 0 ≤ max ‖u - 1‖ ‖v - 1‖ := le_max_of_le_left (norm_nonneg _)
  have hab : Commute (u - 1) (v - 1) :=
    (huv.sub_right (Commute.one_right u)).sub_left
      ((Commute.one_left v).sub_right (Commute.one_right 1))
  have hdiff : (u - 1) ^ n - (v - 1) ^ n =
      (u - v) * ∑ j ∈ Finset.range n, (u - 1) ^ j * (v - 1) ^ (n - 1 - j) := by
    rw [← sub_sub_sub_cancel_right u v 1, hab.mul_geom_sum₂ n]
  have hgeom : ‖∑ j ∈ Finset.range n, (u - 1) ^ j * (v - 1) ^ (n - 1 - j)‖ ≤
      max ‖u - 1‖ ‖v - 1‖ ^ (n - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hm0 _) fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖u - 1‖ ^ j * ‖v - 1‖ ^ (n - 1 - j)
        ≤ max ‖u - 1‖ ‖v - 1‖ ^ j * max ‖u - 1‖ ‖v - 1‖ ^ (n - 1 - j) := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_right _ _
      _ = max ‖u - 1‖ ‖v - 1‖ ^ (j + (n - 1 - j)) := (pow_add _ _ _).symm
      _ = max ‖u - 1‖ ‖v - 1‖ ^ (n - 1) := by rw [Nat.add_sub_cancel' (by omega)]
  have hcoeff : ‖((-1 : ℚ_[p]) ^ (n + 1) / n)‖ ≤ (padicExpRadius p ^ (n - 1))⁻¹ := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
    exact inv_anti₀ (pow_pos hρ _) (padicExpRadius_pow_sub_one_le_norm_natCast (by omega))
  have hq : max ‖u - 1‖ ‖v - 1‖ / padicExpRadius p ≤ 1 := (div_le_one hρ).mpr hm.le
  rw [norm_smul, hdiff, norm_mul]
  calc ‖((-1 : ℚ_[p]) ^ (n + 1) / n)‖ *
        (‖u - v‖ * ‖∑ j ∈ Finset.range n, (u - 1) ^ j * (v - 1) ^ (n - 1 - j)‖)
      ≤ (padicExpRadius p ^ (n - 1))⁻¹ * (‖u - v‖ * max ‖u - 1‖ ‖v - 1‖ ^ (n - 1)) :=
        mul_le_mul hcoeff (mul_le_mul_of_nonneg_left hgeom (norm_nonneg _))
          (by positivity) (by positivity)
    _ = ‖u - v‖ * (max ‖u - 1‖ ‖v - 1‖ / padicExpRadius p) ^ (n - 1) := by
        rw [div_pow]
        ring
    _ ≤ ‖u - v‖ * (max ‖u - 1‖ ‖v - 1‖ / padicExpRadius p) ^ 1 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (div_nonneg hm0 hρ.le) hq (by omega)) (norm_nonneg _)
    _ = ‖u - v‖ * (max ‖u - 1‖ ‖v - 1‖ / padicExpRadius p) := by rw [pow_one]

/-- For commuting `u, v` in the open disc of radius `padicExpRadius p` about `1`, `log u - log v`
agrees with `u - v` up to `‖u - v‖ * (max ‖u - 1‖ ‖v - 1‖ / padicExpRadius p)`. -/
private theorem norm_log_sub_log_sub_sub_le {L : Type*} [NormedDivisionRing L]
    [NormedAlgebra ℚ_[p] L] [CompleteSpace L] {u v : L} (huv : Commute u v)
    (hu : ‖u - 1‖ < padicExpRadius p) (hv : ‖v - 1‖ < padicExpRadius p) :
    ‖NormedSpace.log u - NormedSpace.log v - (u - v)‖ ≤
      ‖u - v‖ * (max ‖u - 1‖ ‖v - 1‖ / padicExpRadius p) := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  have hlog_u : HasSum (fun n : ℕ ↦ ((-1 : ℚ_[p]) ^ (n + 1) / n) • (u - 1) ^ n)
      (NormedSpace.log u) := by
    rw [NormedSpace.log_eq_tsum ℚ_[p]]
    exact (NormedSpace.logSeries_summable_of_norm_lt_one ℚ_[p] L
      (hu.trans (padicExpRadius_lt_one p))).hasSum
  have hlog_v : HasSum (fun n : ℕ ↦ ((-1 : ℚ_[p]) ^ (n + 1) / n) • (v - 1) ^ n)
      (NormedSpace.log v) := by
    rw [NormedSpace.log_eq_tsum ℚ_[p]]
    exact (NormedSpace.logSeries_summable_of_norm_lt_one ℚ_[p] L
      (hv.trans (padicExpRadius_lt_one p))).hasSum
  have hsum : HasSum
      (fun n : ℕ ↦
        if n < 2 then (0 : L) else ((-1 : ℚ_[p]) ^ (n + 1) / n) • ((u - 1) ^ n - (v - 1) ^ n))
      (NormedSpace.log u - NormedSpace.log v - (u - v)) := by
    refine ((hlog_u.sub hlog_v).sub (hasSum_ite_eq 1 (u - v))).congr_fun fun n ↦ ?_
    rcases n with _ | _ | n
    · simp
    · simp
    · simp [smul_sub]
  rw [← hsum.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n ↦ ?_
  split_ifs with hn
  · have hm0 : 0 ≤ max ‖u - 1‖ ‖v - 1‖ := le_max_of_le_left (norm_nonneg _)
    simp [mul_nonneg (norm_nonneg _) (div_nonneg hm0 (padicExpRadius_pos p).le)]
  · push Not at hn
    exact norm_logSeries_diff_term_le huv hu hv hn

/-- **Isometry of the `p`-adic logarithm for commuting arguments.** If `u` and `v` commute and lie
in the open disc of radius `padicExpRadius p` about `1`, then `‖log u - log v‖ = ‖u - v‖`. -/
private theorem norm_log_sub_log_of_commute {L : Type*} [NormedDivisionRing L]
    [NormedAlgebra ℚ_[p] L] [CompleteSpace L] {u v : L} (huv : Commute u v)
    (hu : ‖u - 1‖ < padicExpRadius p) (hv : ‖v - 1‖ < padicExpRadius p) :
    ‖NormedSpace.log u - NormedSpace.log v‖ = ‖u - v‖ := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  rcases eq_or_ne u v with rfl | hne
  · simp
  have hlt : ‖NormedSpace.log u - NormedSpace.log v - (u - v)‖ < ‖u - v‖ := by
    refine (norm_log_sub_log_sub_sub_le huv hu hv).trans_lt ?_
    exact mul_lt_of_lt_one_right (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
      ((div_lt_one (padicExpRadius_pos p)).mpr (max_lt hu hv))
  rw [← sub_add_cancel (NormedSpace.log u - NormedSpace.log v) (u - v),
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le]

/-- **Isometry of the `p`-adic logarithm at `1`.** For `‖y - 1‖ < padicExpRadius p`,
`‖log y‖ = ‖y - 1‖`. -/
theorem norm_log_eq_norm_sub_one {L : Type*} [NormedDivisionRing L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] {y : L} (hy : ‖y - 1‖ < padicExpRadius p) :
    ‖NormedSpace.log y‖ = ‖y - 1‖ := by
  simpa [NormedSpace.log_one] using
    norm_log_sub_log_of_commute (Commute.one_right y) hy (by simpa using padicExpRadius_pos p)

/-- **The `p`-adic logarithm is an isometry on the open disc of radius `padicExpRadius p` about
`1`.** -/
theorem norm_log_sub_log {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
    {u v : L} (hu : ‖u - 1‖ < padicExpRadius p) (hv : ‖v - 1‖ < padicExpRadius p) :
    ‖NormedSpace.log u - NormedSpace.log v‖ = ‖u - v‖ :=
  norm_log_sub_log_of_commute (Commute.all u v) hu hv

/-- The `p`-adic logarithm is injective on the open disc of radius `padicExpRadius p` about `1`. -/
theorem injOn_padicLog (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L] :
    Set.InjOn (NormedSpace.log : L → L) (Metric.ball 1 (padicExpRadius p)) := by
  intro u hu v hv huv
  rw [Metric.mem_ball, dist_eq_norm] at hu hv
  have h := norm_log_sub_log hu hv
  rw [huv, sub_self, norm_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)

/-- Coefficient valuation bound for the truncated `PowerSeries.exp - 1` polynomial. -/
private theorem valuation_coeff_trunc_exp_sub_one_mul_pow_le {L : Type*} [NormedField L]
    [NormedAlgebra ℚ_[p] L] [CharZero L] [IsUltrametricDist L] (x : L) (N k : ℕ) :
    let S : ℝ≥0 := ‖x‖₊ / ⟨padicExpRadius p, (padicExpRadius_pos p).le⟩
    NormedField.valuation ((PowerSeries.trunc N (PowerSeries.exp L - 1)).coeff k * x ^ k) * S ≤
      ‖x‖₊ * S ^ k := by
  have hρ_pos : 0 < padicExpRadius p := padicExpRadius_pos p
  rw [← NNReal.coe_le_coe]
  simp only [NormedField.valuation_apply, NNReal.coe_mul, NNReal.coe_pow, coe_nnNorm,
    PowerSeries.coeff_trunc]
  split_ifs with hk
  · rcases eq_or_ne k 0 with rfl | hk0
    · simp only [map_sub, PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_exp,
        PowerSeries.constantCoeff_one, sub_self, zero_mul, norm_zero, pow_zero, mul_one]
      positivity
    · have hterm : PowerSeries.coeff k (PowerSeries.exp L - 1) * x ^ k = x ^ k / (k ! : L) := by
        simp [PowerSeries.coeff_exp, PowerSeries.coeff_one, hk0, div_eq_inv_mul, mul_comm]
      rw [hterm]
      calc ‖x ^ k / (k ! : L)‖ * (‖x‖ / padicExpRadius p)
          ≤ ‖x‖ * (‖x‖ / padicExpRadius p) ^ (k - 1) * (‖x‖ / padicExpRadius p) := by
            gcongr
            exact norm_pow_div_factorial_le x hk0
        _ = ‖x‖ * (‖x‖ / padicExpRadius p) ^ k := by
            rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
  · simp only [zero_mul, norm_zero]
    positivity

/-- Coefficient valuation bound for the truncated `PowerSeries.log` polynomial. -/
private theorem valuation_coeff_trunc_log_mul_pow_le {L : Type*} [NormedField L]
    [NormedAlgebra ℚ_[p] L] [CharZero L] [IsUltrametricDist L] (x : L) (M n : ℕ) :
    let S : ℝ≥0 := ‖x‖₊ / ⟨padicExpRadius p, (padicExpRadius_pos p).le⟩
    NormedField.valuation ((PowerSeries.trunc M (PowerSeries.log L)).coeff n) * ‖x‖₊ ^ n * S ≤
      ‖x‖₊ * S ^ n := by
  have hρ_pos : 0 < padicExpRadius p := padicExpRadius_pos p
  rw [← NNReal.coe_le_coe]
  simp only [NormedField.valuation_apply, NNReal.coe_mul, NNReal.coe_pow, coe_nnNorm,
    PowerSeries.coeff_trunc]
  split_ifs with hn
  · rcases eq_or_ne n 0 with rfl | hn0
    · simp only [PowerSeries.coeff_log, ↓reduceIte, norm_zero, pow_zero, zero_mul, mul_one]
      positivity
    · have hcoeff : ‖PowerSeries.coeff n (PowerSeries.log L)‖ * ‖x‖ ^ n = ‖x ^ n / (n : L)‖ := by
        simp only [PowerSeries.coeff_log, hn0, ↓reduceIte, map_div₀, map_pow, map_neg, map_one,
          map_natCast, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div, inv_mul_eq_div]
      rw [hcoeff]
      calc ‖x ^ n / (n : L)‖ * (‖x‖ / padicExpRadius p)
          ≤ ‖x‖ * (‖x‖ / padicExpRadius p) ^ (n - 1) * (‖x‖ / padicExpRadius p) := by
            gcongr
            exact norm_pow_div_natCast_le x hn0
        _ = ‖x‖ * (‖x‖ / padicExpRadius p) ^ n := by
            rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
  · simp only [norm_zero, zero_mul]
    positivity

/-- Truncated composition bound for `log ∘ (exp - 1)` on the open disc `‖x‖ < padicExpRadius p`. -/
private theorem norm_eval_trunc_log_eval_trunc_exp_sub_one_sub_le {L : Type*} [NormedField L]
    [NormedAlgebra ℚ_[p] L] [CharZero L] {x : L} (hx : ‖x‖ < padicExpRadius p) (M N : ℕ) :
    ‖(PowerSeries.trunc M (PowerSeries.log L)).eval
        ((PowerSeries.trunc N (PowerSeries.exp L - 1)).eval x) - x‖ *
        (‖x‖ / padicExpRadius p) ≤
      ‖x‖ * (‖x‖ / padicExpRadius p) ^ min M N := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  set v : Valuation L ℝ≥0 := NormedField.valuation
  set A : ℝ≥0 := ‖x‖₊
  set S : ℝ≥0 := A / ⟨padicExpRadius p, (padicExpRadius_pos p).le⟩
  have hS_le : S ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    exact (div_le_one (padicExpRadius_pos p)).mpr hx.le
  set F := PowerSeries.trunc M (PowerSeries.log L)
  set Q := PowerSeries.trunc N (PowerSeries.exp L - 1)
  have hX : ∀ k, v ((Polynomial.X : L[X]).coeff k * x ^ k) * S ≤ A * S ^ k := fun k ↦ by
    rw [Polynomial.coeff_X]
    split_ifs with hk
    · subst hk
      simp [v, A]
    · simp
  have hval := Valuation.map_eval_mul_le (v := v) (G := F.comp Q - Polynomial.X) (M := min M N)
    hS_le
    (fun k hk ↦ by
      rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc_log_comp_trunc_exp_sub_one
        (lt_min_iff.mp hk).1 (lt_min_iff.mp hk).2, sub_self])
    (fun k ↦ by
      have hcomp := Valuation.map_coeff_comp_mul_pow_le
        (valuation_coeff_trunc_log_mul_pow_le (p := p) x M)
        (valuation_coeff_trunc_exp_sub_one_mul_pow_le (p := p) x N) k
      rw [Polynomial.coeff_sub, sub_mul]
      calc v ((F.comp Q).coeff k * x ^ k - (Polynomial.X : L[X]).coeff k * x ^ k) * S
          ≤ max (v ((F.comp Q).coeff k * x ^ k))
              (v ((Polynomial.X : L[X]).coeff k * x ^ k)) * S := by
            gcongr
            exact v.map_sub_le (le_max_left _ _) (le_max_right _ _)
        _ = max (v ((F.comp Q).coeff k * x ^ k) * S)
              (v ((Polynomial.X : L[X]).coeff k * x ^ k) * S) := max_mul_of_nonneg _ _ S.2
        _ ≤ A * S ^ k := max_le hcomp (hX k))
  have hG : (F.comp Q - Polynomial.X).eval x = F.eval (Q.eval x) - x := by
    simp [Polynomial.eval_comp]
  rw [hG] at hval
  exact_mod_cast hval

/-- Truncations of `PowerSeries.exp - 1` evaluated at `x` converge to `exp x - 1` on the
convergence disc. -/
private theorem tendsto_eval_trunc_exp_sub_one {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] [CharZero L] {x : L} (hx : ‖x‖ < padicExpRadius p) :
    Tendsto (fun N ↦ (PowerSeries.trunc N (PowerSeries.exp L - 1)).eval x) atTop
      (𝓝 (NormedSpace.exp x - 1)) := by
  refine ((hasSum_padicExp hx).sub (hasSum_ite_eq 0 (1 : L))).tendsto_sum_nat.congr fun N ↦ ?_
  simp only [Polynomial.eval, PowerSeries.eval₂_trunc_eq_sum_range, RingHom.id_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [PowerSeries.coeff_exp, PowerSeries.coeff_one, hk, div_eq_inv_mul, mul_comm]

/-- Truncations of `PowerSeries.log` evaluated at `exp x - 1` converge to `log (exp x)` on the
open exponential convergence disc. -/
private theorem tendsto_eval_trunc_log_exp_sub_one {L : Type*} [NormedField L]
    [NormedAlgebra ℚ_[p] L] [CompleteSpace L] [CharZero L] {x : L}
    (hx : ‖x‖ < padicExpRadius p) :
    Tendsto (fun M ↦ (PowerSeries.trunc M (PowerSeries.log L)).eval (NormedSpace.exp x - 1))
      atTop (𝓝 (NormedSpace.log (NormedSpace.exp x))) := by
  have hexp_lt : ‖NormedSpace.exp x - 1‖ < 1 := by
    rw [norm_padicExp_sub_one hx]
    exact hx.trans (padicExpRadius_lt_one p)
  have hlog : HasSum (fun n : ℕ ↦ ((-1 : ℚ_[p]) ^ (n + 1) / n) • (NormedSpace.exp x - 1) ^ n)
      (NormedSpace.log (NormedSpace.exp x)) := by
    rw [NormedSpace.log_eq_tsum ℚ_[p]]
    exact (NormedSpace.logSeries_summable_of_norm_lt_one ℚ_[p] L hexp_lt).hasSum
  refine hlog.tendsto_sum_nat.congr fun M ↦ ?_
  simp only [Polynomial.eval, PowerSeries.eval₂_trunc_eq_sum_range, RingHom.id_apply]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [PowerSeries.coeff_log]
  · simp only [PowerSeries.coeff_log, hn, ↓reduceIte, Algebra.smul_def, map_div₀, map_pow, map_neg,
      map_one, map_natCast]

/-- **The logarithm inverts the exponential on the `p`-adic convergence disc.** For every `x` in a
complete normed field `L` over `ℚ_[p]` with `‖x‖ < padicExpRadius p`, `log (exp x) = x`. -/
theorem log_padicExp {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
    {x : L} (hx : ‖x‖ < padicExpRadius p) :
    NormedSpace.log (NormedSpace.exp x) = x := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [NormedSpace.exp_zero, NormedSpace.log_one]
  set s := ‖x‖ / padicExpRadius p
  have hs_pos : 0 < s := div_pos (norm_pos_iff.mpr hx0) (padicExpRadius_pos p)
  have hs_lt : s < 1 := (div_lt_one (padicExpRadius_pos p)).mpr hx
  have hM : ∀ M : ℕ, ‖(PowerSeries.trunc M (PowerSeries.log L)).eval (NormedSpace.exp x - 1) - x‖ *
      s ≤ ‖x‖ * s ^ M := fun M ↦ by
    set F := PowerSeries.trunc M (PowerSeries.log L)
    have hlim : Tendsto (fun N ↦ ‖F.eval ((PowerSeries.trunc N (PowerSeries.exp L - 1)).eval x) -
        x‖ * s) atTop (𝓝 (‖F.eval (NormedSpace.exp x - 1) - x‖ * s)) :=
      (((F.continuous.tendsto _).comp
        (tendsto_eval_trunc_exp_sub_one hx)).sub_const x).norm.mul_const s
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop M] with N hMN
    simpa [s, min_eq_left hMN] using norm_eval_trunc_log_eval_trunc_exp_sub_one_sub_le hx M N
  have hlim_lhs : Tendsto (fun M ↦ ‖(PowerSeries.trunc M (PowerSeries.log L)).eval
      (NormedSpace.exp x - 1) - x‖ * s) atTop
      (𝓝 (‖NormedSpace.log (NormedSpace.exp x) - x‖ * s)) :=
    ((tendsto_eval_trunc_log_exp_sub_one hx).sub_const x).norm.mul_const s
  have hlim_rhs : Tendsto (fun M : ℕ ↦ ‖x‖ * s ^ M) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hs_pos.le hs_lt).const_mul ‖x‖
  have hle0 : ‖NormedSpace.log (NormedSpace.exp x) - x‖ * s ≤ 0 :=
    le_of_tendsto_of_tendsto' hlim_lhs hlim_rhs hM
  have hnorm0 : ‖NormedSpace.log (NormedSpace.exp x) - x‖ = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_left hle0 hs_pos) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)

/-- **The exponential inverts the logarithm on the `p`-adic convergence disc.** For every `y` in a
complete normed field `L` over `ℚ_[p]` with `‖y - 1‖ < padicExpRadius p`, `exp (log y) = y`. -/
theorem padicExp_log {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
    {y : L} (hy : ‖y - 1‖ < padicExpRadius p) :
    NormedSpace.exp (NormedSpace.log y) = y := by
  have hlog : ‖NormedSpace.log y‖ < padicExpRadius p := by
    rwa [norm_log_eq_norm_sub_one hy]
  have hexp : ‖NormedSpace.exp (NormedSpace.log y) - 1‖ < padicExpRadius p := by
    rwa [norm_padicExp_sub_one hlog]
  exact injOn_padicLog L (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
    (Metric.mem_ball.mpr (by rwa [dist_eq_norm])) (log_padicExp hlog)

/-- **The `p`-adic logarithm is a homomorphism on the open exponential disc.** For `u, v` with
`‖u - 1‖ < padicExpRadius p` and `‖v - 1‖ < padicExpRadius p`, `log (u * v) = log u + log v`. -/
theorem padicLog_mul {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
    {u v : L} (hu : ‖u - 1‖ < padicExpRadius p) (hv : ‖v - 1‖ < padicExpRadius p) :
    NormedSpace.log (u * v) = NormedSpace.log u + NormedSpace.log v := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hlu : ‖NormedSpace.log u‖ < padicExpRadius p := by rwa [norm_log_eq_norm_sub_one hu]
  have hlv : ‖NormedSpace.log v‖ < padicExpRadius p := by rwa [norm_log_eq_norm_sub_one hv]
  have hadd : ‖NormedSpace.log u + NormedSpace.log v‖ < padicExpRadius p :=
    (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hlu hlv)
  conv_lhs => rw [← padicExp_log hu, ← padicExp_log hv]
  rw [← padicExp_add hlu hlv, log_padicExp hadd]

/-- `NormedSpace.exp` is a bijection from the open disc of radius `padicExpRadius p` about `0`
onto the open disc of the same radius about `1`. -/
theorem bijOn_padicExp (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L] :
    Set.BijOn (NormedSpace.exp : L → L)
      (Metric.ball 0 (padicExpRadius p)) (Metric.ball 1 (padicExpRadius p)) := by
  refine ⟨fun x hx ↦ ?_, injOn_padicExp L, fun y hy ↦ ?_⟩
  · rw [mem_ball_zero_iff] at hx
    rw [Metric.mem_ball, dist_eq_norm, norm_padicExp_sub_one hx]
    exact hx
  · rw [Metric.mem_ball, dist_eq_norm] at hy
    refine ⟨NormedSpace.log y, ?_, padicExp_log hy⟩
    rw [mem_ball_zero_iff, norm_log_eq_norm_sub_one hy]
    exact hy

/-- `NormedSpace.log` is a bijection from the open disc of radius `padicExpRadius p` about `1`
onto the open disc of the same radius about `0`. -/
theorem bijOn_padicLog (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L] :
    Set.BijOn (NormedSpace.log : L → L)
      (Metric.ball 1 (padicExpRadius p)) (Metric.ball 0 (padicExpRadius p)) := by
  refine ⟨fun y hy ↦ ?_, injOn_padicLog L, fun x hx ↦ ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm] at hy
    rw [mem_ball_zero_iff, norm_log_eq_norm_sub_one hy]
    exact hy
  · rw [mem_ball_zero_iff] at hx
    refine ⟨NormedSpace.exp x, ?_, log_padicExp hx⟩
    rw [Metric.mem_ball, dist_eq_norm, norm_padicExp_sub_one hx]
    exact hx

end LogDisc

end TauCeti
