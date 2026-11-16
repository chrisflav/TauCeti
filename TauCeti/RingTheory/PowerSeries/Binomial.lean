/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution

import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Formal derivatives and substitutions of binomial power series

For an element `r` of a commutative binomial ring `R` and a commutative `R`-algebra `A`, the
formal derivative of the binomial power series `(1 + X) ^ r = ∑ₙ choose r n • Xⁿ` is
`r • (1 + X) ^ (r - 1)`. Equivalently,
`(1 + X) * d⁄dX (binomialSeries A r) = r • binomialSeries A r`.

Substituting a series `U : A⟦X⟧` with `constantCoeff U = 0` gives the formal power `(1 + U) ^ r`,
which satisfies the usual exponent laws, is a unit of `A⟦X⟧`, and differentiates by the chain rule.

## Main results

* `PowerSeries.derivative_binomialSeries`:
  `d⁄dX (binomialSeries A r) = r • binomialSeries A (r - 1)`.
* `PowerSeries.one_add_X_mul_derivative_binomialSeries`:
  `(1 + X) * d⁄dX (binomialSeries A r) = r • binomialSeries A r`.
* `PowerSeries.constantCoeff_binomialSeries_subst`, `PowerSeries.isUnit_binomialSeries_subst`:
  `(binomialSeries A r).subst U` has constant coefficient `1` and is a unit when
  `constantCoeff U = 0`.
* `PowerSeries.binomialSeries_zero_subst`, `PowerSeries.binomialSeries_one_subst`,
  `PowerSeries.binomialSeries_add_subst`, `PowerSeries.binomialSeries_subst_mul_neg`,
  `PowerSeries.binomialSeries_subst_pow`: exponent laws for `(binomialSeries A r).subst U`.
* `PowerSeries.derivative_binomialSeries_subst`:
  `d⁄dX ((binomialSeries A r).subst U) = r • (binomialSeries A (r - 1)).subst U * d⁄dX U`.
-/

public section

namespace PowerSeries

variable {R A : Type*} [CommRing R] [BinomialRing R] [CommRing A] [Algebra R A]

/-- The formal derivative of the binomial series `(1 + X) ^ r` is `r • (1 + X) ^ (r - 1)`. -/
theorem derivative_binomialSeries (r : R) :
    d⁄dX (binomialSeries A r) = r • binomialSeries A (r - 1) := by
  ext n
  have hchoose : (n + 1) • Ring.choose r (n + 1) = r * Ring.choose (r - 1) n := by
    have h := Ring.choose_smul_choose r (Nat.succ_pos n)
    simpa [Nat.choose_one_right, Ring.choose_one_right] using h
  rw [coeff_derivative, binomialSeries_coeff, coeff_smul, binomialSeries_coeff,
    mul_comm, ← Nat.cast_add_one, ← nsmul_eq_mul, ← smul_assoc, hchoose, mul_smul]

/-- The binomial series `(1 + X) ^ r` satisfies the differential equation
`(1 + X) * d⁄dX ((1 + X) ^ r) = r • (1 + X) ^ r`. -/
theorem one_add_X_mul_derivative_binomialSeries (r : R) :
    (1 + X) * d⁄dX (binomialSeries A r) = r • binomialSeries A r := by
  rw [derivative_binomialSeries, mul_smul_comm]
  have h1 : (1 + X : A⟦X⟧) = binomialSeries A (1 : R) := by
    simpa using (binomialSeries_nat (A := A) (R := R) 1).symm
  rw [h1, ← binomialSeries_add, add_sub_cancel]

/-- Substituting a series with zero constant term into `(1 + X) ^ r` gives constant term `1`. -/
@[simp]
theorem constantCoeff_binomialSeries_subst {U : A⟦X⟧} (hU : constantCoeff U = 0) (r : R) :
    constantCoeff ((binomialSeries A r).subst U) = 1 := by
  rw [constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero hU, binomialSeries_constantCoeff,
    map_one]

/-- Substituting into `(1 + X) ^ 0` gives `1`. -/
theorem binomialSeries_zero_subst {U : A⟦X⟧} (hU : constantCoeff U = 0) :
    (binomialSeries A (0 : R)).subst U = 1 := by
  rw [binomialSeries_zero, ← coe_substAlgHom (.of_constantCoeff_zero' hU), map_one]

/-- Substituting `U` with zero constant term into `(1 + X) ^ 1` gives `1 + U`. -/
@[simp]
theorem binomialSeries_one_subst {U : A⟦X⟧} (hU : constantCoeff U = 0) :
    (binomialSeries A (1 : R)).subst U = 1 + U := by
  have hsub : HasSubst U := .of_constantCoeff_zero' hU
  have hb1 : binomialSeries A (1 : R) = 1 + X := by
    simpa using binomialSeries_nat (A := A) (R := R) 1
  rw [hb1, subst_add hsub, ← coe_substAlgHom hsub, map_one, coe_substAlgHom hsub, subst_X hsub]

/-- Addition law for substituted binomial series:
`(1 + U) ^ (r₁ + r₂) = (1 + U) ^ r₁ * (1 + U) ^ r₂`. -/
theorem binomialSeries_add_subst {U : A⟦X⟧} (hU : constantCoeff U = 0) (r₁ r₂ : R) :
    (binomialSeries A (r₁ + r₂)).subst U =
      (binomialSeries A r₁).subst U * (binomialSeries A r₂).subst U := by
  have hsub : HasSubst U := .of_constantCoeff_zero' hU
  rw [binomialSeries_add, subst_mul hsub]

/-- Inverse law for substituted binomial series: `(1 + U) ^ r * (1 + U) ^ (-r) = 1`. -/
theorem binomialSeries_subst_mul_neg {U : A⟦X⟧} (hU : constantCoeff U = 0) (r : R) :
    (binomialSeries A r).subst U * (binomialSeries A (-r)).subst U = 1 := by
  rw [← binomialSeries_add_subst hU, add_neg_cancel, binomialSeries_zero_subst hU]

/-- Substituting a series with zero constant term into `(1 + X) ^ r` yields a unit of `A⟦X⟧`. -/
theorem isUnit_binomialSeries_subst {U : A⟦X⟧} (hU : constantCoeff U = 0) (r : R) :
    IsUnit ((binomialSeries A r).subst U) :=
  ⟨⟨(binomialSeries A r).subst U, (binomialSeries A (-r)).subst U,
    binomialSeries_subst_mul_neg hU r, by rw [mul_comm, binomialSeries_subst_mul_neg hU r]⟩, rfl⟩

/-- Natural-power law for substituted binomial series: `((1 + U) ^ r) ^ n = (1 + U) ^ (n • r)`. -/
theorem binomialSeries_subst_pow {U : A⟦X⟧} (hU : constantCoeff U = 0) (r : R) (n : ℕ) :
    (binomialSeries A r).subst U ^ n = (binomialSeries A (n • r)).subst U := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← binomialSeries_add_subst hU, succ_nsmul]

/-- Chain rule for substituted binomial series:
`d⁄dX ((1 + U) ^ r) = r • (1 + U) ^ (r - 1) * d⁄dX U`. -/
theorem derivative_binomialSeries_subst {U : A⟦X⟧} (hU : constantCoeff U = 0) (r : R) :
    d⁄dX ((binomialSeries A r).subst U) = r • (binomialSeries A (r - 1)).subst U * d⁄dX U := by
  have hsub : HasSubst U := .of_constantCoeff_zero' hU
  rw [derivative_subst hsub, derivative_binomialSeries, subst_smul hsub]

end PowerSeries
