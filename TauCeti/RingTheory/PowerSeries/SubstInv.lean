/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Power series with a left inverse for substitution

Mathlib constructs the inverse for substitution of a power series `Q = uX + ⋯` whose linear
coefficient `u` is a unit (`PowerSeries.substInvOfIsUnit`). This file records the converse: if a
power series `Q` with nilpotent constant coefficient, so that it can be substituted, has a left
inverse `P` for substitution, `P(Q) = X`, then the linear coefficient of `Q` is a unit. Indeed the
chain rule gives `P'(Q) * Q' = 1`, so the derivative `Q'` is a unit of `R⟦X⟧`, and its constant
coefficient is the linear coefficient of `Q`.

If moreover `Q` has zero constant coefficient, then `Q` is `X` times a unit of `R⟦X⟧`, which is
the form used to change formal parameters. Together with the universal negative-power derivative
identity of `TauCeti.RingTheory.PowerSeries.Derivative`, this yields the formal Lagrange–Bürmann
inversion formula over any commutative ring: if `(X * F)(U) = X` with `F` a unit and
`constantCoeff U = 0`, then `[Xˢ] (A(U) * U') = [Xˢ] (A * F⁻⁽ˢ⁺¹⁾)`.

## Main results

* `PowerSeries.isUnit_coeff_one_of_subst_eq_X`: if `Q` can be substituted and `P(Q) = X`, then the
  linear coefficient of `Q` is a unit.
* `PowerSeries.exists_unit_eq_X_mul_of_subst_eq_X`: if `constantCoeff Q = 0` and `P(Q) = X`, then
  `Q = X * v` for a unit `v` of `R⟦X⟧`.
* `PowerSeries.subst_eq_iff_eq_subst_substInvOfIsUnit`: substituting a series `P = u X + ⋯` with
  `u` a unit is undone by substituting its compositional inverse: `f(P) = g ↔ f = g(P⁻¹)`, so `f`
  is determined by `f(P)`.
* `PowerSeries.map_substInvOfIsUnit`: coefficient maps commute with the explicit construction
  `substInvOfIsUnit` for any series with a unit linear coefficient; it is a compositional inverse
  when the constant coefficient is zero.
* `PowerSeries.coeff_subst_mul_derivative_of_X_mul_subst_eq_X`: formal Lagrange–Bürmann inversion
  over any commutative ring.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- A power series `Q` with nilpotent constant coefficient that has a left inverse `P` for
substitution, `P(Q) = X`, has a unit of `R` as its linear coefficient. -/
theorem isUnit_coeff_one_of_subst_eq_X {P Q : R⟦X⟧} (hQ : HasSubst Q) (h : P.subst Q = X) :
    IsUnit (coeff 1 Q) := by
  -- by the chain rule, `P'(Q) * Q' = 1`
  have hd : (d⁄dX P).subst Q * d⁄dX Q = 1 := by rw [← derivative_subst hQ, h, derivative_X]
  -- so `Q'` is a unit, and its constant coefficient is the linear coefficient of `Q`
  simpa only [← coeff_zero_eq_constantCoeff_apply, coeff_derivative, Nat.cast_zero, zero_add,
    mul_one] using isUnit_iff_constantCoeff.mp (.of_mul_eq_one_right _ hd)

/-- A power series `Q` with zero constant coefficient that has a left inverse `P` for
substitution, `P(Q) = X`, is `X` times a unit of `R⟦X⟧`. -/
theorem exists_unit_eq_X_mul_of_subst_eq_X {P Q : R⟦X⟧} (hQ : constantCoeff Q = 0)
    (h : P.subst Q = X) : ∃ v : R⟦X⟧ˣ, Q = X * (v : R⟦X⟧) := by
  have hu := isUnit_coeff_one_of_subst_eq_X (.of_constantCoeff_zero' hQ) h
  obtain ⟨b, rfl⟩ := X_dvd_iff.mpr hQ
  -- the linear coefficient of `X * b` is the constant coefficient of `b`
  rw [coeff_succ_X_mul 0 b, coeff_zero_eq_constantCoeff_apply] at hu
  obtain ⟨v, rfl⟩ := isUnit_iff_constantCoeff.mpr hu
  exact ⟨v, rfl⟩

/-- Substituting a series `P = u X + ⋯` with `u` a unit is undone by substituting its
compositional inverse: `f(P) = g` if and only if `f = g(P⁻¹)`. In particular a power series `f` is
determined by `f(P)`. -/
theorem subst_eq_iff_eq_subst_substInvOfIsUnit {P : R⟦X⟧} (hP : constantCoeff P = 0)
    (hP' : IsUnit (coeff 1 P)) {f g : R⟦X⟧} :
    f.subst P = g ↔ f = g.subst (P.substInvOfIsUnit hP') := by
  have hP₀ : HasSubst P := .of_constantCoeff_zero' hP
  have hQ := HasSubst.substInvOfIsUnit P hP'
  constructor <;> rintro rfl
  · rw [subst_comp_subst_apply hP₀ hQ, P.subst_substInvOfIsUnit_right hP hP', X_subst]
  · rw [subst_comp_subst_apply hQ hP₀, P.subst_substInvOfIsUnit_left hP hP', X_subst]

/-- The coefficients of the explicit construction `substInvFun` commute with ring homomorphisms,
for any series with an invertible linear coefficient. -/
private theorem map_substInvFun {S : Type*} [CommRing S] (f : R →+* S) (P : R⟦X⟧)
    [Invertible (coeff 1 P)] [Invertible (coeff 1 (P.map f))] (n : ℕ) :
    f (substInvFun P n) = substInvFun (P.map f) n := by
  have hinv : f (⅟(coeff 1 P)) = ⅟(coeff 1 (P.map f)) := by
    let _ : Invertible (f (coeff 1 P)) :=
      ‹Invertible (coeff 1 (P.map f))›.copy _ (coeff_map f 1 P).symm
    convert map_invOf f (coeff 1 P) using 1
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [substInvFun]
    | 1, _ => simp [substInvFun, hinv]
    | m + 2, ih =>
      have hS : HasSubst (∑ i : Fin (m + 2), C (substInvFun P i.1) * X ^ i.1) := by
        refine .of_constantCoeff_zero' ?_
        rw [map_sum]
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        rcases i with ⟨_ | k, hk⟩
        · simp [substInvFun]
        · simp [map_pow]
      have key : map f (P.subst (∑ i : Fin (m + 2), C (substInvFun P i.1) * X ^ i.1)) =
          ((P.map f).subst (map f (∑ i : Fin (m + 2), C (substInvFun P i.1) * X ^ i.1))) :=
        map_subst hS P
      have hSm : map f (∑ i : Fin (m + 2), C (substInvFun P i.1) * X ^ i.1) =
          ∑ i : Fin (m + 2), C (substInvFun (P.map f) i.1) * X ^ i.1 := by
        simp only [map_sum, map_mul, map_C, map_pow, map_X]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [ih i (by omega)]
      rw [substInvFun, substInvFun, map_mul, map_neg, hinv, ← coeff_map, key, hSm]
      all_goals omega

/-- Applying a ring homomorphism to the coefficients commutes with the explicit construction
`substInvOfIsUnit`, for any series `P` whose linear coefficient is a unit; no condition on the
constant coefficient of `P` is needed. When `constantCoeff P = 0` this construction is the
compositional inverse of `P`. -/
@[simp]
theorem map_substInvOfIsUnit {S : Type*} [CommRing S] (f : R →+* S) {P : R⟦X⟧}
    (hP' : IsUnit (coeff 1 P)) :
    (P.substInvOfIsUnit hP').map f =
      (P.map f).substInvOfIsUnit (by simpa only [coeff_map] using hP'.map f) := by
  have hPf : IsUnit (coeff 1 (P.map f)) := by simpa only [coeff_map] using hP'.map f
  let := hP'.invertible
  let := hPf.invertible
  ext n
  simp only [substInvOfIsUnit, substInv, coeff_map, coeff_mk]
  exact map_substInvFun f P n

/-- Decomposition of a power series into its degree-`< m` polynomial part and a multiple of
`X ^ m`. -/
private theorem exists_eq_sum_range_add_X_pow_mul (S : R⟦X⟧) (m : ℕ) :
    ∃ W : R⟦X⟧, S = (∑ j ∈ Finset.range m, C (coeff j S) * X ^ j) + X ^ m * W := by
  have hdvd : X ^ m ∣ S - ∑ j ∈ Finset.range m, C (coeff j S) * X ^ j := by
    rw [X_pow_dvd_iff]
    intro j hj
    rw [map_sub, map_sum, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij.symm]
    · intro hjm
      exact absurd (Finset.mem_range.mpr hj) hjm
  obtain ⟨W, hW⟩ := hdvd
  exact ⟨W, eq_add_of_sub_eq' hW⟩

/-- Monomial case (`A = X ^ k`, `k ≤ s`) of the formal Lagrange–Bürmann inversion formula. -/
private theorem coeff_pow_mul_derivative_of_X_mul_subst_eq_X {F G : R⟦X⟧ˣ}
    (hFG : (↑F⁻¹ : R⟦X⟧).subst (X * (G : R⟦X⟧)) = (G : R⟦X⟧))
    {k s : ℕ} (hks : k ≤ s) :
    coeff s ((X * (G : R⟦X⟧)) ^ k * d⁄dX (X * (G : R⟦X⟧))) =
      coeff (s - k) ((↑F⁻¹ : R⟦X⟧) ^ (s + 1)) := by
  set r : ℕ := s - k
  set U : R⟦X⟧ := X * (G : R⟦X⟧)
  set S : R⟦X⟧ := (↑F⁻¹ : R⟦X⟧) ^ (s + 1)
  have hU0 : constantCoeff U = 0 := by simp [U]
  have hU : HasSubst U := .of_constantCoeff_zero' hU0
  have hSU : S.subst U = (G : R⟦X⟧) ^ (s + 1) := by
    rw [subst_pow hU, hFG]
  obtain ⟨W, hS⟩ := exists_eq_sum_range_add_X_pow_mul S (r + 1)
  have hsub := congrArg (fun f ↦ f.subst U) hS
  rw [hSU, subst_add hU, subst_mul hU, subst_pow hU, subst_X hU] at hsub
  have hsum_sub :
      (∑ j ∈ Finset.range (r + 1), C (coeff j S) * X ^ j).subst U =
        ∑ j ∈ Finset.range (r + 1), C (coeff j S) * U ^ j := by
    rw [← coe_substAlgHom hU, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [coe_substAlgHom hU, subst_mul hU, subst_pow hU, subst_X hU, subst_C]
    rfl
  rw [hsum_sub] at hsub
  -- Multiply by `G⁻¹ ^ (r + 1) * d⁄dX U` so the left side becomes `G ^ k * d⁄dX U`.
  have hGinv : (G : R⟦X⟧) * (↑G⁻¹ : R⟦X⟧) = 1 := Units.mul_inv G
  have hmul := congrArg (fun f ↦ f * ((↑G⁻¹ : R⟦X⟧) ^ (r + 1) * d⁄dX U)) hsub
  have hlhs : (G : R⟦X⟧) ^ (s + 1) * ((↑G⁻¹ : R⟦X⟧) ^ (r + 1) * d⁄dX U) =
      (G : R⟦X⟧) ^ k * d⁄dX U := by
    have hsk : s + 1 = k + (r + 1) := by omega
    rw [hsk, pow_add, ← mul_assoc, mul_assoc ((G : R⟦X⟧) ^ k), ← mul_pow, hGinv, one_pow,
      mul_one]
  rw [hlhs, add_mul, Finset.sum_mul] at hmul
  have hcoeff := congrArg (coeff r) hmul
  -- On the left, `coeff r (G ^ k * d⁄dX U) = coeff s (U ^ k * d⁄dX U)`.
  have hcoeff_lhs : coeff s (U ^ k * d⁄dX U) = coeff r ((G : R⟦X⟧) ^ k * d⁄dX U) := by
    have hsk : s = k + r := by omega
    rw [hsk, mul_pow, mul_assoc, coeff_X_pow_mul']
    simp
  rw [hcoeff_lhs, hcoeff, map_add, map_sum]
  -- The `X ^ (r + 1)` tail has zero coefficient at degree `r`.
  have htail :
      coeff r (U ^ (r + 1) * W.subst U * ((↑G⁻¹ : R⟦X⟧) ^ (r + 1) * d⁄dX U)) = 0 := by
    rw [mul_pow, mul_assoc, mul_assoc, coeff_X_pow_mul']
    simp
  rw [htail, add_zero, Finset.sum_range_succ]
  -- Every term with `j < r` vanishes by the universal negative-power derivative identity.
  have hderivU : d⁄dX U = (G : R⟦X⟧) + X * d⁄dX (G : R⟦X⟧) := by
    simp [U, Derivation.leibniz, smul_eq_mul, add_comm]
  have hzero : ∑ j ∈ Finset.range r,
      coeff r (C (coeff j S) * U ^ j * ((↑G⁻¹ : R⟦X⟧) ^ (r + 1) * d⁄dX U)) = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hjr : j < r := Finset.mem_range.mp hj
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.sub_ne_zero_of_lt hjr)
    have hpow :
        (G : R⟦X⟧) ^ j * (↑G⁻¹ : R⟦X⟧) ^ (r + 1) = (↑G⁻¹ : R⟦X⟧) ^ (m + 2) := by
      have hrj : r + 1 = j + (m + 2) := by omega
      rw [hrj, pow_add, ← mul_assoc, ← mul_pow, hGinv, one_pow, one_mul]
    have hterm : C (coeff j S) * U ^ j * ((↑G⁻¹ : R⟦X⟧) ^ (r + 1) * d⁄dX U) =
        C (coeff j S) * (X ^ j * (((↑G⁻¹ : R⟦X⟧) ^ (m + 1) +
          X * ((↑G⁻¹ : R⟦X⟧) ^ (m + 2) * d⁄dX (G : R⟦X⟧))))) := by
      have hG1 :
          (↑G⁻¹ : R⟦X⟧) ^ (m + 2) * (G : R⟦X⟧) = (↑G⁻¹ : R⟦X⟧) ^ (m + 1) := by
        rw [pow_succ, mul_assoc, Units.inv_mul G, mul_one]
      calc
        C (coeff j S) * U ^ j * ((↑G⁻¹ : R⟦X⟧) ^ (r + 1) * d⁄dX U)
            = C (coeff j S) *
                (X ^ j * ((G : R⟦X⟧) ^ j * (↑G⁻¹ : R⟦X⟧) ^ (r + 1) * d⁄dX U)) := by
              rw [mul_pow]; ring
        _ = C (coeff j S) * (X ^ j * ((↑G⁻¹ : R⟦X⟧) ^ (m + 2) *
              ((G : R⟦X⟧) + X * d⁄dX (G : R⟦X⟧)))) := by rw [hpow, hderivU]
        _ = C (coeff j S) * (X ^ j * (((↑G⁻¹ : R⟦X⟧) ^ (m + 1) +
              X * ((↑G⁻¹ : R⟦X⟧) ^ (m + 2) * d⁄dX (G : R⟦X⟧))))) := by
              rw [mul_add, hG1]; ring
    rw [hterm, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hjr.le, hm, map_add]
    have hid :=
      nsmul_coeff_val_inv_pow_succ_add_coeff_X_mul_val_inv_pow_add_two_mul_derivative_eq_zero G 1 m
    simp only [one_mul, one_nsmul] at hid
    rw [hid, mul_zero]
  rw [hzero, zero_add]
  -- The `j = r` term yields `coeff r S`.
  have hlast : C (coeff r S) * U ^ r * ((↑G⁻¹ : R⟦X⟧) ^ (r + 1) * d⁄dX U) =
      C (coeff r S) * (X ^ r * (1 + X * ((↑G⁻¹ : R⟦X⟧) * d⁄dX (G : R⟦X⟧)))) := by
    have hpow : (G : R⟦X⟧) ^ r * (↑G⁻¹ : R⟦X⟧) ^ (r + 1) = (↑G⁻¹ : R⟦X⟧) := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, hGinv, one_pow, one_mul]
    calc
      C (coeff r S) * U ^ r * ((↑G⁻¹ : R⟦X⟧) ^ (r + 1) * d⁄dX U)
          = C (coeff r S) *
              (X ^ r * ((G : R⟦X⟧) ^ r * (↑G⁻¹ : R⟦X⟧) ^ (r + 1) * d⁄dX U)) := by
            rw [mul_pow]; ring
      _ = C (coeff r S) *
            (X ^ r * ((↑G⁻¹ : R⟦X⟧) * ((G : R⟦X⟧) + X * d⁄dX (G : R⟦X⟧)))) := by
            rw [hpow, hderivU]
      _ = C (coeff r S) * (X ^ r * (1 + X * ((↑G⁻¹ : R⟦X⟧) * d⁄dX (G : R⟦X⟧)))) := by
            rw [mul_add, Units.inv_mul G]; ring
  rw [hlast, coeff_C_mul, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, map_add,
    coeff_zero_one, coeff_zero_X_mul, add_zero, mul_one]

/-- **Formal Lagrange–Bürmann inversion formula.** Over any commutative ring `R`, if `F` is a
unit of `R⟦X⟧` and `U` has zero constant coefficient with `(X * F)(U) = X`, then for every power
series `A : R⟦X⟧` and every `s : ℕ`,
`coeff s (A.subst U * d⁄dX U) = coeff s (A * (↑F⁻¹) ^ (s + 1))`. -/
theorem coeff_subst_mul_derivative_of_X_mul_subst_eq_X {F : R⟦X⟧ˣ} {U : R⟦X⟧}
    (hU0 : constantCoeff U = 0) (hU : (X * (F : R⟦X⟧)).subst U = X) (A : R⟦X⟧) (s : ℕ) :
    coeff s (A.subst U * d⁄dX U) = coeff s (A * (↑F⁻¹ : R⟦X⟧) ^ (s + 1)) := by
  obtain ⟨G, rfl⟩ := exists_unit_eq_X_mul_of_subst_eq_X hU0 hU
  have hsubst : HasSubst (X * (G : R⟦X⟧)) := .of_constantCoeff_zero' hU0
  -- Cancel `X` in `(X * G) * F(X * G) = X` to obtain `F⁻¹(X * G) = G`.
  have hGF : (G : R⟦X⟧) * (F : R⟦X⟧).subst (X * (G : R⟦X⟧)) = 1 := by
    rw [subst_mul hsubst, subst_X hsubst, mul_assoc] at hU
    ext n
    have h := congrArg (coeff (n + 1)) hU
    simpa [coeff_succ_X_mul, coeff_X] using h
  have hFG : (↑F⁻¹ : R⟦X⟧).subst (X * (G : R⟦X⟧)) = (G : R⟦X⟧) := by
    have h1 :
        (↑F⁻¹ : R⟦X⟧).subst (X * (G : R⟦X⟧)) * (F : R⟦X⟧).subst (X * (G : R⟦X⟧)) = 1 := by
      rw [← subst_mul hsubst, Units.inv_mul F, ← coe_substAlgHom hsubst, map_one]
    calc
      (↑F⁻¹ : R⟦X⟧).subst (X * (G : R⟦X⟧))
          = (↑F⁻¹ : R⟦X⟧).subst (X * (G : R⟦X⟧)) * 1 := (mul_one _).symm
      _ = (↑F⁻¹ : R⟦X⟧).subst (X * (G : R⟦X⟧)) *
            ((F : R⟦X⟧).subst (X * (G : R⟦X⟧)) * (G : R⟦X⟧)) := by
            rw [← hGF, mul_comm (G : R⟦X⟧)]
      _ = ((↑F⁻¹ : R⟦X⟧).subst (X * (G : R⟦X⟧)) *
            (F : R⟦X⟧).subst (X * (G : R⟦X⟧))) * (G : R⟦X⟧) := (mul_assoc _ _ _).symm
      _ = (G : R⟦X⟧) := by rw [h1, one_mul]
  -- Reduce to monomials `X ^ k` for `k ≤ s`.
  obtain ⟨W, hA⟩ := exists_eq_sum_range_add_X_pow_mul A (s + 1)
  rw [hA, subst_add hsubst, add_mul, add_mul, map_add, map_add]
  have htail_r : coeff s (X ^ (s + 1) * W * (↑F⁻¹ : R⟦X⟧) ^ (s + 1)) = 0 := by
    rw [mul_assoc, coeff_X_pow_mul']
    simp
  have htail_l :
      coeff s ((X ^ (s + 1) * W).subst (X * (G : R⟦X⟧)) * d⁄dX (X * (G : R⟦X⟧))) = 0 := by
    rw [subst_mul hsubst, subst_pow hsubst, subst_X hsubst, mul_pow, mul_assoc, mul_assoc,
      coeff_X_pow_mul']
    simp
  rw [htail_l, htail_r, add_zero, add_zero]
  have hsum_sub :
      (∑ k ∈ Finset.range (s + 1), C (coeff k A) * X ^ k).subst (X * (G : R⟦X⟧)) =
        ∑ k ∈ Finset.range (s + 1), C (coeff k A) * (X * (G : R⟦X⟧)) ^ k := by
    rw [← coe_substAlgHom hsubst, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [coe_substAlgHom hsubst, subst_mul hsubst, subst_pow hsubst, subst_X hsubst, subst_C]
    rfl
  rw [hsum_sub, Finset.sum_mul, Finset.sum_mul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hks : k ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [mul_assoc, mul_assoc, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hks,
    coeff_pow_mul_derivative_of_X_mul_subst_eq_X hFG hks]

end PowerSeries
