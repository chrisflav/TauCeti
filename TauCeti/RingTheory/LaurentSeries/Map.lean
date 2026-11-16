/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Map
public import TauCeti.RingTheory.LaurentSeries.Ramified

import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.FieldTheory.RatFunc.Map

/-!
# Coefficientwise maps, expansion, and descent for Laurent series

This file establishes compatibility between the Laurent series expansion `X ↦ X ^ d`
(`LaurentSeries.expand`), coefficientwise base change (`HahnSeries.mapRingHom`), and the
subfields of polynomials and rational functions inside `K⸨X⸩`, together with coefficient-field
descent for polynomial relations, rationality, and algebraicity over `K(X)`.

## Main results

* `LaurentSeries.expand_algebraMap_polynomial` and
  `LaurentSeries.expand_algebraMap_ratFunc_mem_range`: expanding a polynomial or rational
  function in `K⸨X⸩` by `X ↦ X ^ d` yields the corresponding substituted polynomial or
  rational function.
* `LaurentSeries.mapRingHom_expand`, `LaurentSeries.mapRingHom_algebraMap_polynomial`, and
  `LaurentSeries.mapRingHom_algebraMap_ratFunc`: coefficientwise base change commutes with
  `LaurentSeries.expand` and acts coefficientwise on polynomials and rational functions.
* `LaurentSeries.mem_range_ratFunc_of_finite_support`: every Laurent series with finite support
  belongs to `K(X)`.
* `LaurentSeries.exists_polynomial_relation_of_mapRingHom`: a nontrivial `L[X]`-linear relation
  among Laurent series over `K` descends to a nontrivial `K[X]`-linear relation via a `K`-linear
  functional `L → K`.
* `LaurentSeries.mem_range_ratFunc_mapRingHom_iff` and
  `LaurentSeries.isAlgebraic_mapRingHom_iff`: rationality and algebraicity of a Laurent series
  over `K(X)` are invariant under field extensions `K →+* L`.
-/

public section

open Polynomial HahnSeries
open scoped RatFunc LaurentSeries PowerSeries nonZeroDivisors

namespace LaurentSeries

section Semiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Coefficientwise change of scalars commutes with `LaurentSeries.expand`. -/
theorem mapRingHom_expand (σ : R →+* S) (d : ℕ+) (f : R⸨X⸩) :
    HahnSeries.mapRingHom σ (expand R d f) = expand S d (HahnSeries.mapRingHom σ f) := by
  ext n
  rw [HahnSeries.coeff_mapRingHom]
  by_cases hn : (d : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [coeff_expand_mul, coeff_expand_mul, HahnSeries.coeff_mapRingHom]
  · rw [coeff_expand_of_not_dvd d f hn, coeff_expand_of_not_dvd d _ hn, map_zero]

end Semiring

section Field

variable {K L : Type*} [Field K] [Field L]

/-- The algebra map `K[X] → K⸨X⸩` agrees with coercing a polynomial to a power series and then
to a Laurent series. -/
theorem algebraMap_polynomial_eq_ofPowerSeries (p : K[X]) :
    algebraMap K[X] K⸨X⸩ p = HahnSeries.ofPowerSeries ℤ K (p : K⟦X⟧) := by
  rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
  exact (RatFunc.coe_coe p).symm

private theorem algebraMap_polynomial_C (c : K) :
    algebraMap K[X] K⸨X⸩ (Polynomial.C c) = HahnSeries.C c := by
  rw [algebraMap_polynomial_eq_ofPowerSeries, Polynomial.coe_C, PowerSeries.coe_C]

private theorem algebraMap_polynomial_X_pow (n : ℕ) :
    algebraMap K[X] K⸨X⸩ (Polynomial.X ^ n) = HahnSeries.single (n : ℤ) (1 : K) := by
  rw [map_pow, algebraMap_polynomial_eq_ofPowerSeries, Polynomial.coe_X, HahnSeries.ofPowerSeries_X,
    HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]

private theorem ratFunc_denom_mul_eq_num (r : RatFunc K) :
    algebraMap K[X] (RatFunc K) r.denom * r = algebraMap K[X] (RatFunc K) r.num := by
  have h := RatFunc.algebraMap_ne_zero r.denom_ne_zero
  calc algebraMap K[X] (RatFunc K) r.denom * r
      = algebraMap K[X] (RatFunc K) r.denom *
          (algebraMap K[X] (RatFunc K) r.num / algebraMap K[X] (RatFunc K) r.denom) := by
        rw [RatFunc.num_div_denom]
    _ = algebraMap K[X] (RatFunc K) r.num := mul_div_cancel₀ _ h

/-- Expanding the image of a polynomial `p` in `K⸨X⸩` by `X ↦ X ^ d` equals the image of
`p(X ^ d)`. -/
theorem expand_algebraMap_polynomial (d : ℕ+) (p : K[X]) :
    expand K d (algebraMap K[X] K⸨X⸩ p) =
      algebraMap K[X] K⸨X⸩ (p.comp (Polynomial.X ^ (d : ℕ))) := by
  have hX : expand K d (algebraMap K[X] K⸨X⸩ Polynomial.X) =
      algebraMap K[X] K⸨X⸩ (Polynomial.X ^ (d : ℕ)) := by
    rw [← pow_one (Polynomial.X : K[X]), algebraMap_polynomial_X_pow, Nat.cast_one,
      expand_single, mul_one, ← algebraMap_polynomial_X_pow, pow_one]
  refine Polynomial.induction_on' p (fun p q hp hq ↦ ?_) (fun n a ↦ ?_)
  · rw [map_add, map_add, Polynomial.add_comp, map_add, hp, hq]
  · rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow,
      Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
      map_mul, map_pow, hX, algebraMap_polynomial_C, ← algebraMap_apply, AlgHom.commutes]

/-- Expanding a rational function in `K⸨X⸩` by `X ↦ X ^ d` lands back in `K(X)`. -/
theorem expand_algebraMap_ratFunc_mem_range (d : ℕ+) (r : RatFunc K) :
    expand K d (algebraMap (RatFunc K) K⸨X⸩ r) ∈
      Set.range (algebraMap (RatFunc K) K⸨X⸩) := by
  refine ⟨algebraMap K[X] (RatFunc K) (r.num.comp (Polynomial.X ^ (d : ℕ))) /
    algebraMap K[X] (RatFunc K) (r.denom.comp (Polynomial.X ^ (d : ℕ))), ?_⟩
  rw [map_div₀, ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩,
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩,
    ← expand_algebraMap_polynomial, ← expand_algebraMap_polynomial,
    ← map_div₀, IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩,
    IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩, ← map_div₀, RatFunc.num_div_denom]

/-- Coefficientwise change of field acts on polynomial images in `K⸨X⸩` by mapping
coefficients. -/
theorem mapRingHom_algebraMap_polynomial (σ : K →+* L) (p : K[X]) :
    HahnSeries.mapRingHom σ (algebraMap K[X] K⸨X⸩ p) =
      algebraMap L[X] L⸨X⸩ (p.map σ) := by
  rw [HahnSeries.mapRingHom_apply, algebraMap_polynomial_eq_ofPowerSeries,
    algebraMap_polynomial_eq_ofPowerSeries, HahnSeries.map_ofPowerSeries,
    Polynomial.polynomial_map_coe]

/-- Coefficientwise change of field acts on `RatFunc` images in `K⸨X⸩` via
`RatFunc.mapRingHom`. -/
theorem mapRingHom_algebraMap_ratFunc (σ : K →+* L) (r : RatFunc K) :
    HahnSeries.mapRingHom σ (algebraMap (RatFunc K) K⸨X⸩ r) =
      algebraMap (RatFunc L) L⸨X⸩
        (RatFunc.mapRingHom (Polynomial.mapRingHom σ)
          (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
            (Polynomial.map_injective _ σ.injective)) r) := by
  rw [← RatFunc.num_div_denom r, map_div₀, map_div₀, map_div₀, map_div₀,
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩,
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩,
    mapRingHom_algebraMap_polynomial, mapRingHom_algebraMap_polynomial,
    IsScalarTower.algebraMap_apply L[X] (RatFunc L) L⸨X⸩,
    IsScalarTower.algebraMap_apply L[X] (RatFunc L) L⸨X⸩]
  congr 1 <;>
    rw [RatFunc.mapRingHom_algebraMap, Polynomial.coe_mapRingHom]

/-- Every Laurent series with finite support belongs to `K(X)`. -/
theorem mem_range_ratFunc_of_finite_support {f : K⸨X⸩} (hfin : f.support.Finite) :
    f ∈ Set.range (algebraMap (RatFunc K) K⸨X⸩) := by
  have hC : ∀ c : K,
      algebraMap (RatFunc K) K⸨X⸩ (RatFunc.C c) = HahnSeries.C c := fun c ↦ by
    rw [← RatFunc.algebraMap_C, ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩,
      algebraMap_polynomial_C]
  have hXz : ∀ k : ℤ,
      algebraMap (RatFunc K) K⸨X⸩ ((RatFunc.X : RatFunc K) ^ k) = HahnSeries.single k (1 : K) :=
    fun k ↦ by rw [map_zpow₀, RatFunc.coe_X, ← RatFunc.single_zpow]
  refine ⟨∑ k ∈ hfin.toFinset, RatFunc.C (f.coeff k) * (RatFunc.X : RatFunc K) ^ k, ?_⟩
  rw [map_sum]
  ext n
  rw [HahnSeries.coeff_sum]
  simp only [map_mul, hC, hXz, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    HahnSeries.coeff_single, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Set.Finite.mem_toFinset]
  split_ifs with hn
  · rfl
  · by_contra hne
    exact hn (hfin.mem_toFinset.mpr ((HahnSeries.mem_support f n).mpr (Ne.symm hne)))

/-! ### Coefficient-field descent for Laurent series -/

/-- Applying a `K`-linear functional `φ : L → K` coefficientwise to a polynomial over `L`. -/
private noncomputable def projPoly [Algebra K L] (φ : L →ₗ[K] K) (p : L[X]) : K[X] :=
  ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.monomial i (φ (p.coeff i))

private theorem coeff_projPoly [Algebra K L] (φ : L →ₗ[K] K) (p : L[X]) (n : ℕ) :
    (projPoly φ p).coeff n = φ (p.coeff n) := by
  simp only [projPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply,
    Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hn
  · rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

private theorem projPoly_ne_zero [Algebra K L] {φ : L →ₗ[K] K} {p : L[X]} {k : ℕ}
    (h : φ (p.coeff k) ≠ 0) : projPoly φ p ≠ 0 := fun h0 ↦
  h (by rw [← coeff_projPoly φ p k, h0, Polynomial.coeff_zero])

private def coeffMapAddHom [Algebra K L] (φ : L →ₗ[K] K) : L⸨X⸩ →+ K⸨X⸩ where
  toFun y := y.map φ
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

private theorem coeffMapAddHom_apply [Algebra K L] (φ : L →ₗ[K] K) (y : L⸨X⸩) :
    coeffMapAddHom φ y = y.map φ :=
  rfl

private theorem map_algebraMap_polynomial_mul [Algebra K L] (φ : L →ₗ[K] K) (p : L[X])
    (g : K⸨X⸩) :
    (algebraMap L[X] L⸨X⸩ p * HahnSeries.mapRingHom (algebraMap K L) g).map φ =
      algebraMap K[X] K⸨X⸩ (projPoly φ p) * g := by
  rw [← coeffMapAddHom_apply, projPoly, map_sum, Finset.sum_mul]
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
  rw [map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsingle : HahnSeries.single (i : ℤ) (1 : L) =
      HahnSeries.mapRingHom (algebraMap K L) (HahnSeries.single (i : ℤ) (1 : K)) := by
    ext n
    simp [HahnSeries.coeff_mapRingHom, HahnSeries.coeff_single]
  rw [coeffMapAddHom_apply, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul,
    algebraMap_polynomial_C, algebraMap_polynomial_C,
    algebraMap_polynomial_X_pow, algebraMap_polynomial_X_pow,
    mul_assoc, mul_assoc, HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul,
    hsingle, ← map_mul]
  exact HahnSeries.map_smul_mapRingHom_algebraMap φ (p.coeff i)
    (HahnSeries.single (i : ℤ) (1 : K) * g)

/-- **Descent of polynomial-coefficient relations among Laurent series.** If a finite family
of series `g : ι → K⸨X⸩` satisfies a relation `∑ i, P i * g i = 0` over `L[X]` with
`P i₀ ≠ 0`, then it satisfies a relation `∑ i, Q i * g i = 0` over `K[X]` with
`Q i₀ ≠ 0`. -/
theorem exists_polynomial_relation_of_mapRingHom (σ : K →+* L) {ι : Type*} [Fintype ι]
    {g : ι → K⸨X⸩} {P : ι → L[X]} {i₀ : ι} (hi₀ : P i₀ ≠ 0)
    (hrel : ∑ i, algebraMap L[X] L⸨X⸩ (P i) * HahnSeries.mapRingHom σ (g i) = 0) :
    ∃ Q : ι → K[X], Q i₀ ≠ 0 ∧ ∑ i, algebraMap K[X] K⸨X⸩ (Q i) * g i = 0 := by
  let _ : Algebra K L := σ.toAlgebra
  obtain ⟨φ, hφ⟩ :=
    Module.Projective.exists_dual_eq_one K (Polynomial.leadingCoeff_ne_zero.mpr hi₀)
  refine ⟨fun i ↦ projPoly φ (P i),
    projPoly_ne_zero (k := (P i₀).natDegree) (by simp [hφ]), ?_⟩
  have h0 : coeffMapAddHom φ
      (∑ i, algebraMap L[X] L⸨X⸩ (P i) *
        HahnSeries.mapRingHom (algebraMap K L) (g i)) = 0 := by
    have hσ : algebraMap K L = σ := rfl
    rw [hσ, hrel, map_zero]
  rw [map_sum] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeffMapAddHom_apply]
  exact (map_algebraMap_polynomial_mul φ (P i) (g i)).symm

/-- A Laurent series over `K` is a rational function over `L` if and only if it is already a
rational function over `K`. -/
theorem mem_range_ratFunc_mapRingHom_iff (σ : K →+* L) {f : K⸨X⸩} :
    HahnSeries.mapRingHom σ f ∈ Set.range (algebraMap (RatFunc L) L⸨X⸩) ↔
      f ∈ Set.range (algebraMap (RatFunc K) K⸨X⸩) := by
  constructor
  · rintro ⟨r, hr⟩
    have hmul : algebraMap L[X] L⸨X⸩ r.denom * HahnSeries.mapRingHom σ f +
        algebraMap L[X] L⸨X⸩ (-r.num) * HahnSeries.mapRingHom σ 1 = 0 := by
      rw [← hr, map_one, mul_one, map_neg,
        IsScalarTower.algebraMap_apply L[X] (RatFunc L) L⸨X⸩,
        IsScalarTower.algebraMap_apply L[X] (RatFunc L) L⸨X⸩, ← map_mul,
        ratFunc_denom_mul_eq_num, add_neg_cancel]
    have hsum : ∑ i : Fin 2, algebraMap L[X] L⸨X⸩ (![r.denom, -r.num] i) *
        HahnSeries.mapRingHom σ (![f, 1] i) = 0 := by
      simpa [Fin.sum_univ_two] using hmul
    obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_relation_of_mapRingHom σ (i₀ := (0 : Fin 2))
      r.denom_ne_zero hsum
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at hQ
    refine ⟨algebraMap K[X] (RatFunc K) (-Q 1) / algebraMap K[X] (RatFunc K) (Q 0), ?_⟩
    rw [map_div₀, ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩,
      ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩, map_neg]
    have hQ0' : algebraMap K[X] K⸨X⸩ (Q 0) ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
      exact (map_ne_zero_iff _ (algebraMap (RatFunc K) K⸨X⸩).injective).mpr
        (RatFunc.algebraMap_ne_zero hQ0)
    exact div_eq_of_eq_mul hQ0' (by linear_combination -hQ)
  · rintro ⟨r, rfl⟩
    exact ⟨_, (mapRingHom_algebraMap_ratFunc σ r).symm⟩

/-- Clear denominators from a polynomial over `L(X)` vanishing on `HahnSeries.mapRingHom σ f`. -/
private theorem exists_poly_relation_pow_of_aeval_eq_zero (σ : K →+* L) {f : K⸨X⸩}
    {P : (RatFunc L)[X]} (hP0 : P ≠ 0)
    (hPeval : Polynomial.aeval (HahnSeries.mapRingHom σ f) P = 0) :
    ∃ a : Fin (P.natDegree + 1) → L[X], a (Fin.last P.natDegree) ≠ 0 ∧
      ∑ i : Fin (P.natDegree + 1),
        algebraMap L[X] L⸨X⸩ (a i) * HahnSeries.mapRingHom σ (f ^ (i : ℕ)) = 0 := by
  let D : L[X] := ∏ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).denom
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ (P.coeff i).denom_ne_zero
  let a : Fin (P.natDegree + 1) → L[X] := fun i ↦
    (P.coeff i).num * ∏ j ∈ (Finset.range (P.natDegree + 1)).erase i, (P.coeff j).denom
  have ha_eq : ∀ i : Fin (P.natDegree + 1),
      algebraMap L[X] (RatFunc L) (a i) = algebraMap L[X] (RatFunc L) D * P.coeff i := fun i ↦ by
    have hi : (i : ℕ) ∈ Finset.range (P.natDegree + 1) := Finset.mem_range.mpr i.isLt
    have hDsplit : D = (P.coeff i).denom *
        ∏ j ∈ (Finset.range (P.natDegree + 1)).erase i, (P.coeff j).denom :=
      (Finset.mul_prod_erase _ _ hi).symm
    rw [hDsplit, map_mul, map_mul, mul_right_comm, ratFunc_denom_mul_eq_num]
  refine ⟨a, fun h0 ↦ ?_, ?_⟩
  · have h1 := ha_eq (Fin.last P.natDegree)
    rw [h0, map_zero] at h1
    exact mul_ne_zero (RatFunc.algebraMap_ne_zero hD0) (Polynomial.leadingCoeff_ne_zero.mpr hP0)
      h1.symm
  · have hev : ∑ i : Fin (P.natDegree + 1),
        algebraMap (RatFunc L) L⸨X⸩ (P.coeff i) *
          (HahnSeries.mapRingHom σ f) ^ (i : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i ↦
        algebraMap (RatFunc L) L⸨X⸩ (P.coeff i) * (HahnSeries.mapRingHom σ f) ^ i)]
      simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range] using hPeval
    calc ∑ i : Fin (P.natDegree + 1),
          algebraMap L[X] L⸨X⸩ (a i) * HahnSeries.mapRingHom σ (f ^ (i : ℕ))
        = algebraMap (RatFunc L) L⸨X⸩ (algebraMap L[X] (RatFunc L) D) *
            ∑ i : Fin (P.natDegree + 1),
              algebraMap (RatFunc L) L⸨X⸩ (P.coeff i) *
                (HahnSeries.mapRingHom σ f) ^ (i : ℕ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [IsScalarTower.algebraMap_apply L[X] (RatFunc L) L⸨X⸩, ha_eq i, map_mul, map_pow,
            mul_assoc]
      _ = 0 := by rw [hev, mul_zero]

/-- A Laurent series over `K` is algebraic over `L(X)` if and only if it is algebraic over
`K(X)`. -/
theorem isAlgebraic_mapRingHom_iff (σ : K →+* L) {f : K⸨X⸩} :
    IsAlgebraic (RatFunc L) (HahnSeries.mapRingHom σ f) ↔ IsAlgebraic (RatFunc K) f := by
  constructor
  · rintro ⟨P, hP0, hPeval⟩
    obtain ⟨a, ha_last, hrel⟩ := exists_poly_relation_pow_of_aeval_eq_zero σ hP0 hPeval
    obtain ⟨Q, hQlast, hQ⟩ :=
      exists_polynomial_relation_of_mapRingHom σ (i₀ := Fin.last P.natDegree) ha_last hrel
    refine ⟨∑ i : Fin (P.natDegree + 1),
      Polynomial.monomial i (algebraMap K[X] (RatFunc K) (Q i)), ?_, ?_⟩
    · intro h0
      have hcoeff := congrArg (fun p : (RatFunc K)[X] ↦ p.coeff P.natDegree) h0
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply,
        Polynomial.coeff_zero] at hcoeff
      rw [Finset.sum_eq_single (Fin.last P.natDegree)] at hcoeff
      · simp only [Fin.val_last, ↓reduceIte] at hcoeff
        exact RatFunc.algebraMap_ne_zero hQlast hcoeff
      · intro i _ hi
        have : (i : ℕ) ≠ P.natDegree := fun h ↦ hi (Fin.ext h)
        simp [this]
      · simp
    · simp only [map_sum, Polynomial.aeval_monomial,
        ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
      exact hQ
  · rintro ⟨P, hP0, hPeval⟩
    let φ : RatFunc K →+* RatFunc L :=
      RatFunc.mapRingHom (Polynomial.mapRingHom σ)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (Polynomial.map_injective _ σ.injective))
    refine ⟨P.map φ, Polynomial.map_ne_zero hP0, ?_⟩
    have hcomm : (algebraMap (RatFunc L) L⸨X⸩).comp φ =
        (HahnSeries.mapRingHom σ).comp (algebraMap (RatFunc K) K⸨X⸩) :=
      RingHom.ext fun r ↦ (mapRingHom_algebraMap_ratFunc σ r).symm
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomm, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, hPeval, map_zero]

end Field

end LaurentSeries
