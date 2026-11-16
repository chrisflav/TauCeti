/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.RingTheory.PowerSeries.Expand
public import TauCeti.NumberTheory.Transcendental.Mahler.Rationality
import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.FieldTheory.RatFunc.NumDenom
import TauCeti.RingTheory.LaurentSeries.Map

/-!
# Mahler functions and regular points

This file defines `q`-Mahler power series with algebraic coefficients over a field of
characteristic zero (`TauCeti.IsMahlerFunction`) and regular points of rational Mahler systems
over a normed field (`TauCeti.IsMahlerRegularPoint`).

## Main definitions

* `TauCeti.IsMahlerFunction q f`: for a field `K` of characteristic zero, a power series
  `f : PowerSeries K` is `q`-Mahler if `q ≥ 2`, every coefficient of `f` is algebraic over `ℚ`,
  and `f` satisfies a nontrivial linear functional equation
  `∑ i ≤ n, pᵢ(X) f(X^(q^i)) = 0` where `pᵢ ∈ K[X]` have algebraic coefficients and
  `pₙ ≠ 0`.
* `TauCeti.IsMahlerRegularPoint q A α`: for a normed field `K` and a square matrix `A` over
  `RatFunc K`, a point `α : K` is regular for `(q, A)` if `q ≥ 2`, `det A` is a unit,
  `0 < ‖α‖ < 1`, and no forward iterate `α^(q^ℓ)` (`ℓ ≥ 0`) is a zero of the reduced
  denominator of any entry of `A` or `A⁻¹`.

## Main results

* `TauCeti.isMahlerFunction_iff_isMahlerSeries`: `f` is `q`-Mahler iff its coefficients are
  algebraic over `ℚ` and `(f : K⸨X⸩)` satisfies `TauCeti.IsMahlerSeries q`.
* `TauCeti.IsMahlerFunction.add`, `TauCeti.IsMahlerFunction.mul`,
  `TauCeti.IsMahlerFunction.expand`, `TauCeti.isMahlerFunction_polynomial`: closure properties of
  `q`-Mahler functions.
* `TauCeti.isMahlerFunction_iff_exists_system`: equivalence with being the first coordinate of a
  vector of algebraic-coefficient power series solving `F(X) = A(X) F(X^q)` with invertible `A`
  whose reduced numerators and denominators have algebraic coefficients.
* `TauCeti.IsMahlerFunction.exists_ratFunc_isAlgebraic_of_isAlgebraic`: algebraic Mahler
  rationality with algebraic polynomial numerator and denominator.
* `TauCeti.IsMahlerRegularPoint.pow`, `TauCeti.isMahlerRegularPoint_of_polynomial`,
  `TauCeti.IsMahlerRegularPoint.fromBlocks`, `TauCeti.IsMahlerRegularPoint.kronecker`: stability
  and construction principles for regular points.

## References

* B. Adamczewski and C. Faverjon, *Méthode de Mahler : relations linéaires, transcendance et
  applications aux nombres automatiques*, Proc. London Math. Soc. (3) **115** (2017), §1,
  pp. 1–3.
* K. Nishioka, *Mahler Functions and Transcendence*, Lecture Notes in Math. **1631**, Springer,
  1996, §1.1 and Theorem 5.1.7.
-/

public section

open Polynomial HahnSeries LaurentSeries
open scoped LaurentSeries PowerSeries nonZeroDivisors

attribute [local instance 10] RatFunc.liftAlgebra

namespace TauCeti

/-! ### Lifting algebraic coefficients to `algebraicClosure ℚ K` -/

section AlgebraicLift

private noncomputable abbrev algClosureHom (K : Type*) [Field K] [CharZero K] :
    algebraicClosure ℚ K →+* K :=
  (algebraicClosure ℚ K).val.toRingHom

private theorem isAlgebraic_algClosureHom {K : Type*} [Field K] [CharZero K]
    (a : algebraicClosure ℚ K) : IsAlgebraic ℚ (algClosureHom K a) :=
  mem_algebraicClosure_iff.mp a.2

private theorem exists_polynomial_map_algClosureHom {K : Type*} [Field K] [CharZero K] {p : K[X]}
    (hp : ∀ m, IsAlgebraic ℚ (p.coeff m)) :
    ∃ p₀ : (algebraicClosure ℚ K)[X], p₀.map (algClosureHom K) = p := by
  refine ⟨∑ m ∈ p.support, Polynomial.monomial m
    ⟨p.coeff m, mem_algebraicClosure_iff.mpr (hp m)⟩, ?_⟩
  rw [Polynomial.map_sum]
  simp only [Polynomial.map_monomial]
  exact p.as_sum_support.symm

private theorem exists_powerSeries_map_algClosureHom {K : Type*} [Field K] [CharZero K]
    {f : PowerSeries K} (hf : ∀ m, IsAlgebraic ℚ (PowerSeries.coeff m f)) :
    ∃ f₀ : PowerSeries (algebraicClosure ℚ K), PowerSeries.map (algClosureHom K) f₀ = f :=
  ⟨PowerSeries.mk fun m ↦ ⟨PowerSeries.coeff m f, mem_algebraicClosure_iff.mpr (hf m)⟩, by
    ext m; simp [algClosureHom]⟩

private theorem mem_range_ratFunc_algClosureHom_iff {K : Type*} [Field K] [CharZero K]
    {r : RatFunc K} :
    r ∈ Set.range (RatFunc.mapRingHom (Polynomial.mapRingHom (algClosureHom K))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ (algClosureHom K).injective))) ↔
      ∀ m, IsAlgebraic ℚ (r.num.coeff m) ∧ IsAlgebraic ℚ (r.denom.coeff m) := by
  constructor
  · rintro ⟨r₀, rfl⟩ m
    rw [RatFunc.num_mapRingHom, RatFunc.denom_mapRingHom, Polynomial.coeff_map,
      Polynomial.coeff_map]
    exact ⟨isAlgebraic_algClosureHom _, isAlgebraic_algClosureHom _⟩
  · intro hr
    obtain ⟨p₀, hp₀⟩ := exists_polynomial_map_algClosureHom fun m ↦ (hr m).1
    obtain ⟨q₀, hq₀⟩ := exists_polynomial_map_algClosureHom fun m ↦ (hr m).2
    refine ⟨algebraMap _ _ p₀ / algebraMap _ _ q₀, ?_⟩
    rw [map_div₀, RatFunc.mapRingHom_algebraMap, RatFunc.mapRingHom_algebraMap,
      Polynomial.coe_mapRingHom, hp₀, hq₀, RatFunc.num_div_denom]

end AlgebraicLift

/-! ### `q`-Mahler functions with algebraic coefficients -/

section MahlerFunction

variable {K : Type*} [Field K] [CharZero K]

/-- A formal power series `f : PowerSeries K` over a field of characteristic zero is a
*`q`-Mahler function* if `q ≥ 2`, every coefficient of `f` is algebraic over `ℚ`, and `f`
satisfies a nontrivial linear functional equation `∑ i ≤ n, pᵢ(X) f(X^(q^i)) = 0` where
each `pᵢ ∈ K[X]` has algebraic coefficients and `pₙ ≠ 0`. -/
def IsMahlerFunction (q : ℕ) (f : PowerSeries K) : Prop :=
  ∃ hq : 2 ≤ q,
    (∀ m, IsAlgebraic ℚ (PowerSeries.coeff m f)) ∧
    ∃ (n : ℕ) (p : Fin (n + 1) → K[X]),
      (∀ i m, IsAlgebraic ℚ ((p i).coeff m)) ∧
      p (Fin.last n) ≠ 0 ∧
      ∑ i : Fin (n + 1), (p i : PowerSeries K) *
        PowerSeries.expand (q ^ (i : ℕ)) (pow_ne_zero _ (by omega)) f = 0

/-- Unfolding characterization of `IsMahlerFunction`. -/
theorem isMahlerFunction_iff {q : ℕ} {f : PowerSeries K} :
    IsMahlerFunction q f ↔
      ∃ hq : 2 ≤ q,
        (∀ m, IsAlgebraic ℚ (PowerSeries.coeff m f)) ∧
        ∃ (n : ℕ) (p : Fin (n + 1) → K[X]),
          (∀ i m, IsAlgebraic ℚ ((p i).coeff m)) ∧
          p (Fin.last n) ≠ 0 ∧
          ∑ i : Fin (n + 1), (p i : PowerSeries K) *
            PowerSeries.expand (q ^ (i : ℕ)) (pow_ne_zero _ (by omega)) f = 0 :=
  Iff.rfl

/-- Any `q`-Mahler function has base `q ≥ 2`. -/
theorem IsMahlerFunction.two_le {q : ℕ} {f : PowerSeries K}
    (hf : IsMahlerFunction q f) : 2 ≤ q :=
  hf.1

/-- Every coefficient of a `q`-Mahler function is algebraic over `ℚ`. -/
theorem IsMahlerFunction.isAlgebraic_coeff {q : ℕ} {f : PowerSeries K}
    (hf : IsMahlerFunction q f) (m : ℕ) : IsAlgebraic ℚ (PowerSeries.coeff m f) :=
  hf.2.1 m

/-- A power series is a `q`-Mahler function iff it lifts to a power series over
`algebraicClosure ℚ K` that is a `q`-Mahler Laurent series. -/
theorem isMahlerFunction_iff_exists_lift {q : ℕ} {f : PowerSeries K} :
    IsMahlerFunction q f ↔
      ∃ f₀ : PowerSeries (algebraicClosure ℚ K),
        PowerSeries.map (algebraicClosure ℚ K).val.toRingHom f₀ = f ∧
        IsMahlerSeries q (f₀ : (algebraicClosure ℚ K)⸨X⸩) := by
  let σ := algClosureHom K
  constructor
  · rintro ⟨hq, hcoeff, n, p, hp_alg, hlast, hsum⟩
    obtain ⟨f₀, hf₀⟩ := exists_powerSeries_map_algClosureHom hcoeff
    choose p₀ hp₀ using fun i ↦ exists_polynomial_map_algClosureHom (hp_alg i)
    refine ⟨f₀, hf₀, isMahlerSeries_iff.mpr ⟨hq, n, p₀, ?_, ?_⟩⟩
    · intro h0
      exact hlast (by rw [← hp₀ (Fin.last n), h0, Polynomial.map_zero])
    · apply HahnSeries.mapRingHom_injective σ.injective
      rw [map_zero, map_sum]
      have hterm : ∀ i : Fin (n + 1),
          HahnSeries.mapRingHom σ
            (algebraMap _ _ (p₀ i) *
              LaurentSeries.expand (algebraicClosure ℚ K) (Nat.toPNat q (by omega) ^ (i : ℕ))
                (f₀ : (algebraicClosure ℚ K)⸨X⸩)) =
          HahnSeries.ofPowerSeries ℤ K ((p i : PowerSeries K) *
            PowerSeries.expand (q ^ (i : ℕ)) (pow_ne_zero _ (by omega)) f) := fun i ↦ by
        rw [map_mul, mapRingHom_algebraMap_polynomial, hp₀ i,
          algebraMap_polynomial_eq_ofPowerSeries, mapRingHom_expand, HahnSeries.mapRingHom_apply,
          HahnSeries.map_ofPowerSeries, hf₀, LaurentSeries.expand_coe, ← map_mul]
        rfl
      rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← map_sum (HahnSeries.ofPowerSeries ℤ K),
        hsum, map_zero]
  · rintro ⟨f₀, rfl, hf₀⟩
    obtain ⟨hq, n, p₀, hlast, hsum⟩ := isMahlerSeries_iff.mp hf₀
    refine ⟨hq, fun m ↦ ?_, n, fun i ↦ (p₀ i).map σ, fun i m ↦ ?_, ?_, ?_⟩
    · rw [PowerSeries.coeff_map]
      exact isAlgebraic_algClosureHom _
    · rw [Polynomial.coeff_map]
      exact isAlgebraic_algClosureHom _
    · exact Polynomial.map_ne_zero hlast
    · apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
      rw [map_zero, map_sum]
      have hmap := congrArg (HahnSeries.mapRingHom σ) hsum
      rw [map_zero, map_sum] at hmap
      convert hmap using 2 with i
      rw [map_mul (HahnSeries.mapRingHom σ), mapRingHom_algebraMap_polynomial,
        algebraMap_polynomial_eq_ofPowerSeries, mapRingHom_expand, HahnSeries.mapRingHom_apply,
        HahnSeries.map_ofPowerSeries, LaurentSeries.expand_coe,
        map_mul (HahnSeries.ofPowerSeries ℤ K)]
      rfl

/-- A power series `f : PowerSeries K` is a `q`-Mahler function iff all its coefficients are
algebraic over `ℚ` and `(f : K⸨X⸩)` is a `q`-Mahler Laurent series over `K`. -/
theorem isMahlerFunction_iff_isMahlerSeries {q : ℕ} {f : PowerSeries K} :
    IsMahlerFunction q f ↔
      (∀ m, IsAlgebraic ℚ (PowerSeries.coeff m f)) ∧ IsMahlerSeries q (f : K⸨X⸩) := by
  let σ := algClosureHom K
  rw [isMahlerFunction_iff_exists_lift]
  constructor
  · rintro ⟨f₀, rfl, hf₀⟩
    refine ⟨fun m ↦ by rw [PowerSeries.coeff_map]; exact isAlgebraic_algClosureHom _, ?_⟩
    have hcoe : HahnSeries.mapRingHom σ (f₀ : (algebraicClosure ℚ K)⸨X⸩) =
        ((PowerSeries.map σ f₀ : PowerSeries K) : K⸨X⸩) := by
      rw [HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries]
    rw [← hcoe]
    exact (isMahlerSeries_mapRingHom_iff σ).mpr hf₀
  · rintro ⟨hcoeff, hmah⟩
    obtain ⟨f₀, hf₀⟩ := exists_powerSeries_map_algClosureHom hcoeff
    refine ⟨f₀, hf₀, (isMahlerSeries_mapRingHom_iff σ).mp ?_⟩
    rwa [HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries, hf₀]

/-- Every `q`-Mahler function is a `q`-Mahler Laurent series over `K`. -/
theorem IsMahlerFunction.isMahlerSeries {q : ℕ} {f : PowerSeries K}
    (hf : IsMahlerFunction q f) : IsMahlerSeries q (f : K⸨X⸩) :=
  (isMahlerFunction_iff_isMahlerSeries.mp hf).2

/-- Any nontrivial polynomial relation with algebraic coefficients among the `q`-iterates of an
algebraic-coefficient power series (with `q ≥ 2`) makes it a `q`-Mahler function. -/
theorem isMahlerFunction_iff_exists_ne_zero {q : ℕ} {f : PowerSeries K} :
    IsMahlerFunction q f ↔
      ∃ hq : 2 ≤ q,
        (∀ m, IsAlgebraic ℚ (PowerSeries.coeff m f)) ∧
        ∃ (n : ℕ) (p : Fin (n + 1) → K[X]),
          (∀ i m, IsAlgebraic ℚ ((p i).coeff m)) ∧
          (∃ i, p i ≠ 0) ∧
          ∑ i : Fin (n + 1), (p i : PowerSeries K) *
            PowerSeries.expand (q ^ (i : ℕ)) (pow_ne_zero _ (by omega)) f = 0 := by
  constructor
  · rintro ⟨hq, hcoeff, n, p, hp_alg, hlast, hsum⟩
    exact ⟨hq, hcoeff, n, p, hp_alg, ⟨Fin.last n, hlast⟩, hsum⟩
  · rintro ⟨hq, hcoeff, n, p, _, hne, hsum⟩
    rw [isMahlerFunction_iff_isMahlerSeries]
    refine ⟨hcoeff, isMahlerSeries_iff_exists_ne_zero.mpr ⟨hq, n, p, hne, ?_⟩⟩
    have hcoe := congrArg (HahnSeries.ofPowerSeries ℤ K) hsum
    rw [map_zero, map_sum] at hcoe
    convert hcoe using 2 with i
    rw [algebraMap_polynomial_eq_ofPowerSeries, LaurentSeries.expand_coe, map_mul]
    rfl

/-- The zero power series is `q`-Mahler for every `q ≥ 2`. -/
theorem isMahlerFunction_zero {q : ℕ} (hq : 2 ≤ q) : IsMahlerFunction q (0 : PowerSeries K) :=
  isMahlerFunction_iff_isMahlerSeries.mpr
    ⟨fun _ ↦ by simp [isAlgebraic_zero], by simpa using isMahlerSeries_zero (K := K) hq⟩

/-- The constant power series `1` is `q`-Mahler for every `q ≥ 2`. -/
theorem isMahlerFunction_one {q : ℕ} (hq : 2 ≤ q) : IsMahlerFunction q (1 : PowerSeries K) :=
  isMahlerFunction_iff_isMahlerSeries.mpr
    ⟨fun m ↦ by
      rw [PowerSeries.coeff_one]
      split_ifs
      · exact isAlgebraic_one
      · exact isAlgebraic_zero,
      by simpa using isMahlerSeries_C (K := K) hq 1⟩

/-- A constant power series `PowerSeries.C c` is `q`-Mahler iff `q ≥ 2` and `c` is algebraic
over `ℚ`. -/
theorem isMahlerFunction_C_iff {q : ℕ} {c : K} :
    IsMahlerFunction q (PowerSeries.C c) ↔ 2 ≤ q ∧ IsAlgebraic ℚ c := by
  rw [isMahlerFunction_iff_isMahlerSeries]
  constructor
  · rintro ⟨hcoeff, hmah⟩
    exact ⟨hmah.two_le, by simpa using hcoeff 0⟩
  · rintro ⟨hq, hc⟩
    refine ⟨fun m ↦ ?_, ?_⟩
    · rw [PowerSeries.coeff_C]
      split_ifs
      · exact hc
      · exact isAlgebraic_zero
    · simpa [HahnSeries.ofPowerSeries_C] using isMahlerSeries_C (K := K) hq c

/-- Every polynomial with algebraic coefficients is a `q`-Mahler function for every `q ≥ 2`. -/
theorem isMahlerFunction_polynomial {q : ℕ} (hq : 2 ≤ q) {p : K[X]}
    (hp : ∀ m, IsAlgebraic ℚ (p.coeff m)) : IsMahlerFunction q (p : PowerSeries K) := by
  rw [isMahlerFunction_iff_isMahlerSeries]
  refine ⟨fun m ↦ by simpa [Polynomial.coeff_coe] using hp m, ?_⟩
  rw [← algebraMap_polynomial_eq_ofPowerSeries]
  exact isMahlerSeries_polynomial hq p

/-- The indeterminate `PowerSeries.X` is a `q`-Mahler function for every `q ≥ 2`. -/
theorem isMahlerFunction_X {q : ℕ} (hq : 2 ≤ q) :
    IsMahlerFunction q (PowerSeries.X : PowerSeries K) := by
  have hX : (PowerSeries.X : PowerSeries K) = ((Polynomial.X : K[X]) : PowerSeries K) := by
    simp
  rw [hX]
  refine isMahlerFunction_polynomial hq fun m ↦ ?_
  rw [Polynomial.coeff_X]
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

/-- Sums of `q`-Mahler functions are `q`-Mahler. -/
theorem IsMahlerFunction.add {q : ℕ} {f g : PowerSeries K}
    (hf : IsMahlerFunction q f) (hg : IsMahlerFunction q g) :
    IsMahlerFunction q (f + g) := by
  obtain ⟨f₀, rfl, hf₀⟩ := isMahlerFunction_iff_exists_lift.mp hf
  obtain ⟨g₀, rfl, hg₀⟩ := isMahlerFunction_iff_exists_lift.mp hg
  exact isMahlerFunction_iff_exists_lift.mpr
    ⟨f₀ + g₀, by rw [map_add], by simpa using hf₀.add hg₀⟩

/-- Negations of `q`-Mahler functions are `q`-Mahler. -/
theorem IsMahlerFunction.neg {q : ℕ} {f : PowerSeries K} (hf : IsMahlerFunction q f) :
    IsMahlerFunction q (-f) := by
  obtain ⟨f₀, rfl, hf₀⟩ := isMahlerFunction_iff_exists_lift.mp hf
  exact isMahlerFunction_iff_exists_lift.mpr
    ⟨-f₀, by rw [map_neg], by simpa using hf₀.neg⟩

/-- Differences of `q`-Mahler functions are `q`-Mahler. -/
theorem IsMahlerFunction.sub {q : ℕ} {f g : PowerSeries K}
    (hf : IsMahlerFunction q f) (hg : IsMahlerFunction q g) :
    IsMahlerFunction q (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- Products of `q`-Mahler functions are `q`-Mahler. -/
theorem IsMahlerFunction.mul {q : ℕ} {f g : PowerSeries K}
    (hf : IsMahlerFunction q f) (hg : IsMahlerFunction q g) :
    IsMahlerFunction q (f * g) := by
  obtain ⟨f₀, rfl, hf₀⟩ := isMahlerFunction_iff_exists_lift.mp hf
  obtain ⟨g₀, rfl, hg₀⟩ := isMahlerFunction_iff_exists_lift.mp hg
  exact isMahlerFunction_iff_exists_lift.mpr
    ⟨f₀ * g₀, by rw [map_mul], by simpa using hf₀.mul hg₀⟩

/-- Scalar multiples of a `q`-Mahler function by an algebraic scalar are `q`-Mahler. -/
theorem IsMahlerFunction.smul {q : ℕ} {c : K} (hc : IsAlgebraic ℚ c) {f : PowerSeries K}
    (hf : IsMahlerFunction q f) : IsMahlerFunction q (c • f) := by
  rw [PowerSeries.smul_eq_C_mul]
  exact (isMahlerFunction_C_iff.mpr ⟨hf.two_le, hc⟩).mul hf

/-- Powers of a `q`-Mahler function are `q`-Mahler. -/
theorem IsMahlerFunction.pow {q : ℕ} {f : PowerSeries K} (hf : IsMahlerFunction q f) (k : ℕ) :
    IsMahlerFunction q (f ^ k) := by
  induction k with
  | zero => simpa using isMahlerFunction_one (K := K) hf.two_le
  | succ k ih => rw [pow_succ]; exact ih.mul hf

/-- Expanding a `q`-Mahler function by `X ↦ X ^ q` preserves the `q`-Mahler property. -/
theorem IsMahlerFunction.expand {q : ℕ} {f : PowerSeries K} (hf : IsMahlerFunction q f) :
    IsMahlerFunction q (PowerSeries.expand q (by have := hf.two_le; omega) f) := by
  obtain ⟨f₀, rfl, hf₀⟩ := isMahlerFunction_iff_exists_lift.mp hf
  have hq : 2 ≤ q := hf₀.two_le
  refine isMahlerFunction_iff_exists_lift.mpr
    ⟨PowerSeries.expand q (by omega) f₀,
      PowerSeries.map_expand q (by omega) (algClosureHom K) f₀, ?_⟩
  have hcoe : ((PowerSeries.expand q (by omega) f₀ : PowerSeries (algebraicClosure ℚ K)) :
      (algebraicClosure ℚ K)⸨X⸩) =
      LaurentSeries.expand (algebraicClosure ℚ K) (Nat.toPNat q (by omega))
        (f₀ : (algebraicClosure ℚ K)⸨X⸩) := by
    rw [LaurentSeries.expand_coe]; rfl
  rw [hcoe]
  exact hf₀.expand (d := Nat.toPNat q (by omega))

/-- Any `q`-Mahler function is also `q ^ k`-Mahler for every `k ≥ 1`. -/
theorem IsMahlerFunction.pow_base {q k : ℕ} (hk : 1 ≤ k) {f : PowerSeries K}
    (hf : IsMahlerFunction q f) : IsMahlerFunction (q ^ k) f :=
  isMahlerFunction_iff_isMahlerSeries.mpr
    ⟨hf.isAlgebraic_coeff, hf.isMahlerSeries.pow_base hk⟩

/-- **System equivalence for `q`-Mahler functions.** A power series `f : PowerSeries K` is a
`q`-Mahler function iff `q ≥ 2` and `f` is the first coordinate of a vector `F` of
algebraic-coefficient power series solving `F(X) = A(X) F(X^q)` for an invertible rational matrix
`A ∈ GL_m(K(X))` whose reduced entry numerators and denominators have algebraic coefficients. -/
theorem isMahlerFunction_iff_exists_system {q : ℕ} {f : PowerSeries K} :
    IsMahlerFunction q f ↔
      ∃ hq : 2 ≤ q, ∃ (m : ℕ) (hm : 0 < m)
        (A : Matrix (Fin m) (Fin m) (RatFunc K)) (F : Fin m → PowerSeries K),
        (∀ i k, IsAlgebraic ℚ (PowerSeries.coeff k (F i))) ∧
        (∀ i j k, IsAlgebraic ℚ ((A i j).num.coeff k) ∧
          IsAlgebraic ℚ ((A i j).denom.coeff k)) ∧
        IsUnit A.det ∧
        (fun i ↦ (F i : K⸨X⸩)) =
          (A.map (algebraMap (RatFunc K) K⸨X⸩)).mulVec
            (fun i ↦ ((PowerSeries.expand q (by omega) (F i) : PowerSeries K) : K⸨X⸩)) ∧
        F ⟨0, hm⟩ = f := by
  let σ := algClosureHom K
  let φ : RatFunc (algebraicClosure ℚ K) →+* RatFunc K :=
    RatFunc.mapRingHom (Polynomial.mapRingHom σ)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ σ.injective))
  constructor
  · intro hf
    obtain ⟨f₀, rfl, hf₀⟩ := isMahlerFunction_iff_exists_lift.mp hf
    obtain ⟨hq, m, hm, A₀, F₀, hdet₀, hsys₀, hF₀⟩ :=
      isMahlerSeries_coe_iff_exists_powerSeries_system.mp hf₀
    refine ⟨hq, m, hm, A₀.map φ, fun i ↦ PowerSeries.map σ (F₀ i), ?_, ?_, ?_, ?_, by
      dsimp; rw [hF₀]; rfl⟩
    · intro i k
      rw [PowerSeries.coeff_map]
      exact isAlgebraic_algClosureHom _
    · intro i j k
      exact (mem_range_ratFunc_algClosureHom_iff.mp ⟨A₀ i j, rfl⟩) k
    · have hdet' : (A₀.map φ).det = φ A₀.det := (RingHom.map_det φ A₀).symm
      rw [hdet']
      exact hdet₀.map φ
    · funext i
      have hi := congrArg (fun v ↦ HahnSeries.mapRingHom σ (v i)) hsys₀
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul] at hi ⊢
      rw [HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries] at hi
      rw [hi]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mapRingHom_algebraMap_ratFunc σ (A₀ i j), HahnSeries.mapRingHom_apply,
        HahnSeries.map_ofPowerSeries, PowerSeries.map_expand]
  · rintro ⟨hq, m, hm, A, F, hFalg, _, hdet, hsys, hF0⟩
    rw [isMahlerFunction_iff_isMahlerSeries]
    refine ⟨by rw [← hF0]; exact hFalg ⟨0, hm⟩, ?_⟩
    exact isMahlerSeries_coe_iff_exists_powerSeries_system.mpr
      ⟨hq, m, hm, A, F, hdet, hsys, hF0⟩

/-- **Algebraic Mahler rationality with algebraic coefficients.** If a `q`-Mahler function
`f : PowerSeries K` is algebraic over `K(X)`, then `r * f = p` for polynomials `p, r ∈ K[X]` with
algebraic coefficients and `r ≠ 0`. -/
theorem IsMahlerFunction.exists_ratFunc_isAlgebraic_of_isAlgebraic {q : ℕ} {f : PowerSeries K}
    (hf : IsMahlerFunction q f) (halg : IsAlgebraic (RatFunc K) (f : K⸨X⸩)) :
    ∃ p r : K[X],
      (∀ m, IsAlgebraic ℚ (p.coeff m)) ∧
      (∀ m, IsAlgebraic ℚ (r.coeff m)) ∧
      r ≠ 0 ∧ (r : PowerSeries K) * f = p := by
  let σ := algClosureHom K
  obtain ⟨f₀, rfl, hf₀⟩ := isMahlerFunction_iff_exists_lift.mp hf
  have hcoe : HahnSeries.mapRingHom σ (f₀ : (algebraicClosure ℚ K)⸨X⸩) =
      ((PowerSeries.map σ f₀ : PowerSeries K) : K⸨X⸩) := by
    rw [HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries]
  rw [← hcoe] at halg
  have halg₀ :
      IsAlgebraic (RatFunc (algebraicClosure ℚ K)) (f₀ : (algebraicClosure ℚ K)⸨X⸩) :=
    (isAlgebraic_mapRingHom_iff σ).mp halg
  obtain ⟨r₀, hr₀⟩ := isMahlerSeries_isAlgebraic_mem_range_ratFunc hf₀ halg₀
  have hmul₀ : (r₀.denom : PowerSeries (algebraicClosure ℚ K)) * f₀ = r₀.num := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := algebraicClosure ℚ K)
    rw [map_mul, RatFunc.coe_coe, RatFunc.coe_coe, ← hr₀, ← map_mul]
    congr 1
    rw [mul_comm]
    exact (eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r₀))).mp
      (RatFunc.num_div_denom r₀).symm
  refine ⟨r₀.num.map σ, r₀.denom.map σ,
    fun m ↦ by rw [Polynomial.coeff_map]; exact isAlgebraic_algClosureHom _,
    fun m ↦ by rw [Polynomial.coeff_map]; exact isAlgebraic_algClosureHom _,
    Polynomial.map_ne_zero (RatFunc.denom_ne_zero r₀), ?_⟩
  have hmap := congrArg (PowerSeries.map σ) hmul₀
  rwa [map_mul, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe] at hmap

/-- Any algebraic `q`-Mahler function lies in the range of `RatFunc K → K⸨X⸩`. -/
theorem IsMahlerFunction.mem_range_ratFunc_of_isAlgebraic {q : ℕ} {f : PowerSeries K}
    (hf : IsMahlerFunction q f) (halg : IsAlgebraic (RatFunc K) (f : K⸨X⸩)) :
    (f : K⸨X⸩) ∈ Set.range (algebraMap (RatFunc K) K⸨X⸩) :=
  isMahlerSeries_isAlgebraic_mem_range_ratFunc hf.isMahlerSeries halg

/-- A `q`-Mahler function that satisfies no nontrivial polynomial equation `r * f = p` with
`r ≠ 0` is transcendental over `K(X)`. -/
theorem IsMahlerFunction.transcendental_of_not_ratFunc {q : ℕ} {f : PowerSeries K}
    (hf : IsMahlerFunction q f)
    (hnot : ∀ p r : K[X], r ≠ 0 → (r : PowerSeries K) * f ≠ p) :
    Transcendental (RatFunc K) (f : K⸨X⸩) := by
  intro halg
  obtain ⟨p, r, _, _, hr0, hmul⟩ := hf.exists_ratFunc_isAlgebraic_of_isAlgebraic halg
  exact hnot p r hr0 hmul

end MahlerFunction

/-! ### Regular points of Mahler systems -/

section RegularPoint

variable {K : Type*} [NormedField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- For `q ≥ 2` and an invertible rational matrix `A`, a point `α` of the punctured unit disc
is *regular* if no forward iterate `α^(q^ℓ)` (`ℓ ≥ 0`) is a zero of the reduced denominator
of any entry of `A` or `A⁻¹`. Invalid `q` and singular matrices fail the predicate. -/
def IsMahlerRegularPoint (q : ℕ) (A : Matrix ι ι (RatFunc K)) (α : K) : Prop :=
  2 ≤ q ∧ IsUnit A.det ∧ 0 < ‖α‖ ∧ ‖α‖ < 1 ∧ ∀ ℓ : ℕ, ∀ i j,
    (A i j).denom.eval (α ^ q ^ ℓ) ≠ 0 ∧ (A⁻¹ i j).denom.eval (α ^ q ^ ℓ) ≠ 0

/-- Unfolding characterization of `IsMahlerRegularPoint` with `A.det ≠ 0`. -/
theorem isMahlerRegularPoint_iff {q : ℕ} {A : Matrix ι ι (RatFunc K)} {α : K} :
    IsMahlerRegularPoint q A α ↔
      2 ≤ q ∧ A.det ≠ 0 ∧ 0 < ‖α‖ ∧ ‖α‖ < 1 ∧ ∀ ℓ : ℕ, ∀ i j,
        (A i j).denom.eval (α ^ q ^ ℓ) ≠ 0 ∧
          (A⁻¹ i j).denom.eval (α ^ q ^ ℓ) ≠ 0 := by
  simp only [IsMahlerRegularPoint, isUnit_iff_ne_zero]

/-- A regular point of a `q`-Mahler system satisfies `2 ≤ q`. -/
theorem IsMahlerRegularPoint.two_le {q : ℕ} {A : Matrix ι ι (RatFunc K)} {α : K}
    (h : IsMahlerRegularPoint q A α) : 2 ≤ q := h.1

/-- The matrix of a Mahler system with a regular point has unit determinant. -/
theorem IsMahlerRegularPoint.isUnit_det {q : ℕ} {A : Matrix ι ι (RatFunc K)} {α : K}
    (h : IsMahlerRegularPoint q A α) : IsUnit A.det := h.2.1

/-- The matrix of a Mahler system with a regular point has nonzero determinant. -/
theorem IsMahlerRegularPoint.det_ne_zero {q : ℕ} {A : Matrix ι ι (RatFunc K)} {α : K}
    (h : IsMahlerRegularPoint q A α) : A.det ≠ 0 := h.isUnit_det.ne_zero

/-- A regular point of a Mahler system has positive norm. -/
theorem IsMahlerRegularPoint.norm_pos {q : ℕ} {A : Matrix ι ι (RatFunc K)} {α : K}
    (h : IsMahlerRegularPoint q A α) : 0 < ‖α‖ := h.2.2.1

/-- A regular point of a Mahler system lies in the open unit disc (`‖α‖ < 1`). -/
theorem IsMahlerRegularPoint.norm_lt_one {q : ℕ} {A : Matrix ι ι (RatFunc K)} {α : K}
    (h : IsMahlerRegularPoint q A α) : ‖α‖ < 1 := h.2.2.2.1

/-- No forward iterate `α^(q^ℓ)` of a regular point vanishes the reduced denominator of any entry
of `A`. -/
theorem IsMahlerRegularPoint.denom_eval_ne_zero {q : ℕ} {A : Matrix ι ι (RatFunc K)} {α : K}
    (h : IsMahlerRegularPoint q A α) (ℓ : ℕ) (i j : ι) :
    (A i j).denom.eval (α ^ q ^ ℓ) ≠ 0 := (h.2.2.2.2 ℓ i j).1

/-- No forward iterate `α^(q^ℓ)` of a regular point vanishes the reduced denominator of any entry
of `A⁻¹`. -/
theorem IsMahlerRegularPoint.inv_denom_eval_ne_zero {q : ℕ} {A : Matrix ι ι (RatFunc K)}
    {α : K} (h : IsMahlerRegularPoint q A α) (ℓ : ℕ) (i j : ι) :
    (A⁻¹ i j).denom.eval (α ^ q ^ ℓ) ≠ 0 := (h.2.2.2.2 ℓ i j).2

/-- If `α` is regular for `(q, A)`, then so is `α ^ q`. -/
theorem IsMahlerRegularPoint.pow {q : ℕ} {A : Matrix ι ι (RatFunc K)} {α : K}
    (h : IsMahlerRegularPoint q A α) : IsMahlerRegularPoint q A (α ^ q) := by
  refine ⟨h.two_le, h.isUnit_det, ?_, ?_, fun ℓ i j ↦ ?_⟩
  · rw [norm_pow]; exact pow_pos h.norm_pos q
  · rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg α) h.norm_lt_one (by have := h.two_le; omega)
  · rw [← pow_mul, ← pow_succ']
    exact h.2.2.2.2 (ℓ + 1) i j

/-- If `α` is regular for `(q, A)`, then so is every forward iterate `α ^ q ^ k`. -/
theorem IsMahlerRegularPoint.pow_pow {q : ℕ} {A : Matrix ι ι (RatFunc K)} {α : K}
    (h : IsMahlerRegularPoint q A α) (k : ℕ) : IsMahlerRegularPoint q A (α ^ q ^ k) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, pow_mul]
    exact ih.pow

/-- For `q ≥ 2` and a polynomial matrix `P` with unit determinant in `K[X]`, every point of the
punctured open unit disc is regular for `(q, P)`. -/
theorem isMahlerRegularPoint_of_polynomial {q : ℕ} (hq : 2 ≤ q)
    {P : Matrix ι ι K[X]} (hdet : IsUnit P.det)
    {α : K} (h0 : 0 < ‖α‖) (h1 : ‖α‖ < 1) :
    IsMahlerRegularPoint q (P.map (algebraMap K[X] (RatFunc K))) α := by
  let f := algebraMap K[X] (RatFunc K)
  have hdetA : IsUnit (P.map f).det := by
    have hdet' : (P.map f).det = f P.det := (RingHom.map_det f P).symm
    rw [hdet']
    exact hdet.map f
  have hinv : (P.map f)⁻¹ = P⁻¹.map f := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul P hdet,
      Matrix.map_one f (map_zero f) (map_one f)]
  refine ⟨hq, hdetA, h0, h1, fun ℓ i j ↦ ?_⟩
  rw [hinv, Matrix.map_apply, Matrix.map_apply, RatFunc.denom_algebraMap, RatFunc.denom_algebraMap,
    Polynomial.eval_one]
  exact ⟨one_ne_zero, one_ne_zero⟩

/-- For `q ≥ 2`, every point of the punctured unit disc is regular for the identity matrix. -/
theorem isMahlerRegularPoint_one {q : ℕ} (hq : 2 ≤ q) {α : K} (h0 : 0 < ‖α‖)
    (h1 : ‖α‖ < 1) :
    IsMahlerRegularPoint q (1 : Matrix ι ι (RatFunc K)) α := by
  have h1' : (1 : Matrix ι ι (RatFunc K)) =
      (1 : Matrix ι ι K[X]).map (algebraMap K[X] (RatFunc K)) := by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rw [h1']
  exact isMahlerRegularPoint_of_polynomial hq (by simp) h0 h1

/-- For `q ≥ 2`, every point of the punctured unit disc is regular for an empty (`0 × 0`)
system. -/
theorem isMahlerRegularPoint_of_isEmpty [IsEmpty ι] {q : ℕ} (hq : 2 ≤ q)
    (A : Matrix ι ι (RatFunc K)) {α : K} (h0 : 0 < ‖α‖) (h1 : ‖α‖ < 1) :
    IsMahlerRegularPoint q A α :=
  ⟨hq, by simp, h0, h1, fun _ i ↦ isEmptyElim i⟩

/-- Reindexing a Mahler system preserves regularity. -/
theorem IsMahlerRegularPoint.reindex {q : ℕ} {A : Matrix ι ι (RatFunc K)} {α : K}
    (h : IsMahlerRegularPoint q A α) (e : ι ≃ κ) :
    IsMahlerRegularPoint q (A.reindex e e) α := by
  have hinv : (A.reindex e e)⁻¹ = A⁻¹.reindex e e := by
    apply Matrix.inv_eq_left_inv
    have hm : A⁻¹.reindex e e * A.reindex e e = (A⁻¹ * A).reindex e e :=
      (map_mul (Matrix.reindexAlgEquiv (RatFunc K) (RatFunc K) e) A⁻¹ A).symm
    rw [hm, Matrix.nonsing_inv_mul A h.isUnit_det]
    exact map_one (Matrix.reindexAlgEquiv (RatFunc K) (RatFunc K) e)
  refine ⟨h.two_le, ?_, h.norm_pos, h.norm_lt_one, fun ℓ i j ↦ ?_⟩
  · rw [Matrix.det_reindex_self]
    exact h.isUnit_det
  · rw [hinv]
    exact h.2.2.2.2 ℓ (e.symm i) (e.symm j)

/-- A point regular for two Mahler systems is regular for their block-diagonal direct sum. -/
theorem IsMahlerRegularPoint.fromBlocks {q : ℕ} {A : Matrix ι ι (RatFunc K)}
    {B : Matrix κ κ (RatFunc K)} {α : K}
    (hA : IsMahlerRegularPoint q A α) (hB : IsMahlerRegularPoint q B α) :
    IsMahlerRegularPoint q (Matrix.fromBlocks A 0 0 B) α := by
  have hdet : IsUnit (Matrix.fromBlocks A 0 0 B).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    exact hA.isUnit_det.mul hB.isUnit_det
  have hinv : (Matrix.fromBlocks A 0 0 B)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 B⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul A hA.isUnit_det,
      Matrix.nonsing_inv_mul B hB.isUnit_det]
    simp [Matrix.fromBlocks_one]
  refine ⟨hA.two_le, hdet, hA.norm_pos, hA.norm_lt_one, fun ℓ i j ↦ ?_⟩
  rw [hinv]
  cases i <;> cases j <;> simp [hA.denom_eval_ne_zero, hA.inv_denom_eval_ne_zero,
    hB.denom_eval_ne_zero, hB.inv_denom_eval_ne_zero]

private theorem denom_mul_eval_ne_zero {x y : RatFunc K} {z : K}
    (hx : x.denom.eval z ≠ 0) (hy : y.denom.eval z ≠ 0) :
    (x * y).denom.eval z ≠ 0 := by
  intro h
  obtain ⟨c, hc⟩ := RatFunc.denom_mul_dvd x y
  have hmul : (x.denom * y.denom).eval z = 0 := by rw [hc, Polynomial.eval_mul, h, zero_mul]
  rw [Polynomial.eval_mul] at hmul
  exact mul_ne_zero hx hy hmul

/-- A point regular for two Mahler systems is regular for their Kronecker product. -/
theorem IsMahlerRegularPoint.kronecker {q : ℕ} {A : Matrix ι ι (RatFunc K)}
    {B : Matrix κ κ (RatFunc K)} {α : K}
    (hA : IsMahlerRegularPoint q A α) (hB : IsMahlerRegularPoint q B α) :
    IsMahlerRegularPoint q (Matrix.kroneckerMap (· * ·) A B) α := by
  let AB := Matrix.kroneckerMap (· * ·) A B
  let ABinv := Matrix.kroneckerMap (· * ·) A⁻¹ B⁻¹
  have hleft : ABinv * AB = 1 := by
    rw [← Matrix.mul_kronecker_mul, Matrix.nonsing_inv_mul A hA.isUnit_det,
      Matrix.nonsing_inv_mul B hB.isUnit_det]
    exact Matrix.kroneckerMap_one_one (· * ·)
      (fun _ ↦ zero_mul _) (fun _ ↦ mul_zero _) (one_mul 1)
  have hright : AB * ABinv = 1 := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_nonsing_inv A hA.isUnit_det,
      Matrix.mul_nonsing_inv B hB.isUnit_det]
    exact Matrix.kroneckerMap_one_one (· * ·)
      (fun _ ↦ zero_mul _) (fun _ ↦ mul_zero _) (one_mul 1)
  have hdet : IsUnit AB.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨AB, ABinv, hright, hleft⟩, rfl⟩
  have hinv : AB⁻¹ = ABinv := Matrix.inv_eq_left_inv hleft
  refine ⟨hA.two_le, hdet, hA.norm_pos, hA.norm_lt_one, ?_⟩
  rintro ℓ ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [hinv, AB, ABinv, Matrix.kroneckerMap_apply]
  exact ⟨denom_mul_eval_ne_zero
      (hA.denom_eval_ne_zero ℓ i₁ j₁) (hB.denom_eval_ne_zero ℓ i₂ j₂),
    denom_mul_eval_ne_zero
      (hA.inv_denom_eval_ne_zero ℓ i₁ j₁) (hB.inv_denom_eval_ne_zero ℓ i₂ j₂)⟩

/-- No point is regular for a Mahler system with `q < 2`. -/
theorem not_isMahlerRegularPoint_of_lt_two {q : ℕ} (hq : q < 2)
    (A : Matrix ι ι (RatFunc K)) (α : K) : ¬ IsMahlerRegularPoint q A α :=
  fun h ↦ by have := h.two_le; omega

/-- No point is regular for a singular matrix (`A.det = 0`). -/
theorem not_isMahlerRegularPoint_of_det_eq_zero {q : ℕ} {A : Matrix ι ι (RatFunc K)}
    (hdet : A.det = 0) (α : K) : ¬ IsMahlerRegularPoint q A α :=
  fun h ↦ h.det_ne_zero hdet

/-- Zero is never a regular point of any Mahler system. -/
theorem not_isMahlerRegularPoint_zero (q : ℕ) (A : Matrix ι ι (RatFunc K)) :
    ¬ IsMahlerRegularPoint q A (0 : K) :=
  fun h ↦ by simpa using h.norm_pos

end RegularPoint

end TauCeti
