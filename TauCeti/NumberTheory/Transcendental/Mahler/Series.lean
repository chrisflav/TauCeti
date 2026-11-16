/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Map
public import TauCeti.RingTheory.LaurentSeries.Ramified

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import TauCeti.RingTheory.LaurentSeries.Cartier
import TauCeti.RingTheory.LaurentSeries.Map
import TauCeti.RingTheory.PowerSeries.Cartier

/-!
# Mahler Laurent series over arbitrary fields

Let `K` be a field and `q ≥ 2` an integer. A formal Laurent series `f : K⸨X⸩` is *`q`-Mahler*
(`TauCeti.IsMahlerSeries q f`) if it satisfies a nontrivial linear functional equation

  `p₀(X) f(X) + p₁(X) f(X^q) + ⋯ + pₙ(X) f(X^(q^n)) = 0`

with polynomial coefficients `pᵢ ∈ K[X]` and nonzero leading coefficient `pₙ`. Equivalently,
the iterated expansions `f(X^(q^i))` are linearly dependent over `K(X)`
(`TauCeti.isMahlerSeries_iff_not_linearIndependent`), or lie in a finite-dimensional
`K(X)`-subspace of `K⸨X⸩` (`TauCeti.isMahlerSeries_iff_exists_finiteDimensional`).

This finite-dimensional characterization yields closure of `q`-Mahler Laurent series under
addition, negation, subtraction, multiplication, scalar multiplication by rational functions,
expansion `X ↦ X^q`, and passing from base `q` to `q ^ k`. Furthermore, applying the Laurent
contraction operators `LaurentSeries.contract` reduces any Mahler equation for a nonzero series
to one whose first and last polynomial coefficients are both nonzero
(`TauCeti.IsMahlerSeries.exists_first_last_ne_zero`). Its companion matrix then expresses `f`
as the first coordinate of a vector solution `F(X) = A(X) F(X^q)` with `A ∈ GL_m(K(X))`, and
conversely every coordinate of such a system is `q`-Mahler
(`TauCeti.isMahlerSeries_iff_exists_system`). Coefficient-field descent from
`TauCeti.RingTheory.LaurentSeries.Map` gives invariance of `IsMahlerSeries` under arbitrary
field extensions (`TauCeti.isMahlerSeries_mapRingHom_iff`).

## Main definitions

* `TauCeti.IsMahlerSeries q f`: the Laurent series `f : K⸨X⸩` satisfies a nontrivial `q`-Mahler
  equation over `K[X]` with `q ≥ 2`.

## Main results

* `TauCeti.isMahlerSeries_iff_not_linearIndependent`: `f` is `q`-Mahler iff `q ≥ 2` and the
  iterates `i ↦ f(X^(q^i))` are linearly dependent over `K(X)`.
* `TauCeti.isMahlerSeries_iff_exists_finiteDimensional`: `f` is `q`-Mahler iff `q ≥ 2` and all
  iterates `f(X^(q^i))` lie in a finite-dimensional `K(X)`-subspace of `K⸨X⸩`.
* `TauCeti.isMahlerSeries_mapRingHom_iff`: invariance of `IsMahlerSeries` under extensions of
  the coefficient field.
* `TauCeti.IsMahlerSeries.add`, `TauCeti.IsMahlerSeries.mul`, `TauCeti.IsMahlerSeries.expand`,
  `TauCeti.IsMahlerSeries.mul_ratFunc`, `TauCeti.IsMahlerSeries.pow`,
  `TauCeti.IsMahlerSeries.pow_base`: closure of `q`-Mahler series under ring operations,
  rational multipliers, `X ↦ X^q`, and base powers.
* `TauCeti.isMahlerSeries_iff_exists_system` and
  `TauCeti.isMahlerSeries_coe_iff_exists_powerSeries_system`: equivalence with being the first
  coordinate of a vector solution `F(X) = A(X) F(X^q)` with invertible `A` over `K(X)`.

## References

* B. Adamczewski and C. Faverjon, *Méthode de Mahler : relations linéaires, transcendance et
  applications aux nombres automatiques*, Proc. London Math. Soc. (3) **115** (2017), §1,
  pp. 1–3.
* K. Nishioka, *Mahler Functions and Transcendence*, Lecture Notes in Math. **1631**, Springer,
  1996, §1.1.
-/

public section

open Polynomial HahnSeries LaurentSeries
open scoped RatFunc LaurentSeries PowerSeries nonZeroDivisors

namespace TauCeti

/-! ### Definition and characterizations of `q`-Mahler Laurent series -/

section Definition

variable {K : Type*} [Field K]

/-- A formal Laurent series `f : K⸨X⸩` is *`q`-Mahler* if `q ≥ 2` and `f` satisfies a linear
functional equation `∑ i ≤ n, pᵢ(X) f(X^(q^i)) = 0` with `pᵢ ∈ K[X]` and `pₙ ≠ 0`. -/
def IsMahlerSeries (q : ℕ) (f : K⸨X⸩) : Prop :=
  ∃ hq : 2 ≤ q, ∃ (n : ℕ) (p : Fin (n + 1) → K[X]),
    p (Fin.last n) ≠ 0 ∧
    ∑ i : Fin (n + 1), algebraMap K[X] K⸨X⸩ (p i) *
      LaurentSeries.expand K (Nat.toPNat q (by omega) ^ (i : ℕ)) f = 0

/-- Defining characterization of `IsMahlerSeries`. -/
theorem isMahlerSeries_iff {q : ℕ} {f : K⸨X⸩} :
    IsMahlerSeries q f ↔
      ∃ hq : 2 ≤ q, ∃ (n : ℕ) (p : Fin (n + 1) → K[X]),
        p (Fin.last n) ≠ 0 ∧
        ∑ i : Fin (n + 1), algebraMap K[X] K⸨X⸩ (p i) *
          LaurentSeries.expand K (Nat.toPNat q (by omega) ^ (i : ℕ)) f = 0 :=
  Iff.rfl

/-- Any `q`-Mahler Laurent series has base `q ≥ 2`. -/
theorem IsMahlerSeries.two_le {q : ℕ} {f : K⸨X⸩} (hf : IsMahlerSeries q f) : 2 ≤ q :=
  hf.1

/-- Shorten a nonzero tuple of coefficients to one whose last entry is nonzero. -/
private theorem exists_last_ne_zero {M : Type*} [Zero M]
    {P : ∀ n : ℕ, (Fin (n + 1) → M) → Prop}
    (hP : ∀ n c, c (Fin.last (n + 1)) = 0 → P (n + 1) c → P n fun i ↦ c i.castSucc)
    {n : ℕ} {c : Fin (n + 1) → M} (hc : ∃ i, c i ≠ 0) (h : P n c) :
    ∃ (m : ℕ) (d : Fin (m + 1) → M), d (Fin.last m) ≠ 0 ∧ P m d := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := hc
    exact ⟨0, c, by rwa [Fin.fin_one_eq_zero i] at hi, h⟩
  | succ n ih =>
    by_cases hlast : c (Fin.last (n + 1)) = 0
    · obtain ⟨i, hi⟩ := hc
      refine ih ?_ (hP n c hlast h)
      induction i using Fin.lastCases with
      | last => exact (hi hlast).elim
      | cast j => exact ⟨j, hi⟩
    · exact ⟨n + 1, c, hlast, h⟩

/-- Any nontrivial polynomial relation among the `q`-iterates of `f` (for `q ≥ 2`) makes `f` a
`q`-Mahler series, without requiring the top coefficient to be nonzero in advance. -/
theorem isMahlerSeries_iff_exists_ne_zero {q : ℕ} {f : K⸨X⸩} :
    IsMahlerSeries q f ↔
      ∃ hq : 2 ≤ q, ∃ (n : ℕ) (p : Fin (n + 1) → K[X]),
        (∃ i, p i ≠ 0) ∧
        ∑ i : Fin (n + 1), algebraMap K[X] K⸨X⸩ (p i) *
          LaurentSeries.expand K (Nat.toPNat q (by omega) ^ (i : ℕ)) f = 0 := by
  constructor
  · rintro ⟨hq, n, p, hlast, hsum⟩
    exact ⟨hq, n, p, ⟨Fin.last n, hlast⟩, hsum⟩
  · rintro ⟨hq, n, p, hne, hsum⟩
    refine ⟨hq, exists_last_ne_zero (P := fun m (c : Fin (m + 1) → K[X]) ↦
      ∑ i : Fin (m + 1), algebraMap K[X] K⸨X⸩ (c i) *
        LaurentSeries.expand K (Nat.toPNat q (by omega) ^ (i : ℕ)) f = 0) ?_ hne hsum⟩
    intro m c hlast h
    simpa [Fin.sum_univ_castSucc, hlast] using h

/-- Clear denominators in a `K(X)`-linear relation among finitely many `q`-iterates of `f`. -/
private theorem isMahlerSeries_of_finset_sum_eq_zero {q : ℕ} (hq : 2 ≤ q) {f : K⸨X⸩}
    {s : Finset ℕ} {g : ℕ → RatFunc K} {i₀ : ℕ} (hi₀s : i₀ ∈ s)
    (hi₀ : g i₀ ≠ 0)
    (hg : ∑ j ∈ s, g j • LaurentSeries.expand K (Nat.toPNat q (by omega) ^ j) f = 0) :
    IsMahlerSeries q f := by
  rw [isMahlerSeries_iff_exists_ne_zero]
  let N : ℕ := s.sup id
  have hN : ∀ j ∈ s, j < N + 1 := fun j hj ↦ Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
  let D : K[X] := ∏ j ∈ s, (g j).denom
  let p : Fin (N + 1) → K[X] := fun i ↦
    if (i : ℕ) ∈ s then (g i).num * ∏ j ∈ s.erase i, (g j).denom else 0
  refine ⟨hq, N, p, ⟨⟨i₀, hN i₀ hi₀s⟩, ?_⟩, ?_⟩
  · simp only [p, hi₀s, ↓reduceIte]
    exact mul_ne_zero (RatFunc.num_ne_zero hi₀)
      (Finset.prod_ne_zero_iff.mpr fun j _ ↦ (g j).denom_ne_zero)
  · have hp : ∀ i : Fin (N + 1), algebraMap K[X] (RatFunc K) (p i) =
        algebraMap K[X] (RatFunc K) D * (if (i : ℕ) ∈ s then g i else 0) := fun i ↦ by
      by_cases hi : (i : ℕ) ∈ s
      · simp only [p, hi, ↓reduceIte, D]
        have hdn : algebraMap K[X] (RatFunc K) (g i).denom * g i =
            algebraMap K[X] (RatFunc K) (g i).num := by
          rw [mul_comm, ← eq_div_iff (RatFunc.algebraMap_ne_zero (g i).denom_ne_zero),
            RatFunc.num_div_denom]
        rw [← Finset.mul_prod_erase s _ hi, map_mul, map_mul, mul_right_comm, hdn]
      · simp [p, hi]
    have hsum' : ∑ i : Fin (N + 1), (if (i : ℕ) ∈ s then g i else 0) •
        LaurentSeries.expand K (Nat.toPNat q (by omega) ^ (i : ℕ)) f = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun j ↦ (if j ∈ s then g j else 0) •
        LaurentSeries.expand K (Nat.toPNat q (by omega) ^ j) f),
        ← Finset.sum_subset (fun j hj ↦ Finset.mem_range.mpr (hN j hj))]
      · simpa [Finset.sum_congr] using hg
      · intro j _ hj; simp [hj]
    calc ∑ i : Fin (N + 1), algebraMap K[X] K⸨X⸩ (p i) *
            LaurentSeries.expand K (Nat.toPNat q (by omega) ^ (i : ℕ)) f
        = algebraMap (RatFunc K) K⸨X⸩ (algebraMap K[X] (RatFunc K) D) *
            ∑ i : Fin (N + 1), (if (i : ℕ) ∈ s then g i else 0) •
              LaurentSeries.expand K (Nat.toPNat q (by omega) ^ (i : ℕ)) f := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩, hp i, map_mul,
            Algebra.smul_def, mul_assoc]
      _ = 0 := by rw [hsum', mul_zero]

/-- A Laurent series `f` is `q`-Mahler iff `q ≥ 2` and its iterates `f(X^(q^i))` are linearly
dependent over `K(X)`. -/
theorem isMahlerSeries_iff_not_linearIndependent {q : ℕ} {f : K⸨X⸩} :
    IsMahlerSeries q f ↔
      ∃ hq : 2 ≤ q, ¬LinearIndependent (RatFunc K)
        (fun i : ℕ ↦ LaurentSeries.expand K (Nat.toPNat q (by omega) ^ i) f) := by
  constructor
  · rintro ⟨hq, n, p, hlast, hsum⟩
    refine ⟨hq, fun hli ↦ hlast ?_⟩
    have hli' := Fintype.linearIndependent_iff.mp
      (hli.comp (Fin.val : Fin (n + 1) → ℕ) Fin.val_injective)
    have h0 : ∑ i : Fin (n + 1), algebraMap K[X] (RatFunc K) (p i) •
        LaurentSeries.expand K (Nat.toPNat q (by omega) ^ (i : ℕ)) f = 0 := by
      simpa only [Algebra.smul_def, ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
        using hsum
    exact RatFunc.algebraMap_injective K (by simpa using hli' _ h0 (Fin.last n))
  · rintro ⟨hq, hdep⟩
    obtain ⟨s, g, hg, i₀, hi₀s, hi₀⟩ := not_linearIndependent_iff.mp hdep
    exact isMahlerSeries_of_finset_sum_eq_zero hq hi₀s hi₀ hg

/-- From a polynomial relation with nonzero top coefficient, express `expand (q^n) f` as a
`K(X)`-linear combination of the earlier iterates. -/
private theorem expand_pow_eq_sum_of_relation {q : ℕ} (hq : 0 < q) {f : K⸨X⸩} {n : ℕ}
    {p : Fin (n + 1) → K[X]} (hlast : p (Fin.last n) ≠ 0)
    (hsum : ∑ i : Fin (n + 1), algebraMap K[X] K⸨X⸩ (p i) *
      LaurentSeries.expand K (Nat.toPNat q hq ^ (i : ℕ)) f = 0) :
    LaurentSeries.expand K (Nat.toPNat q hq ^ n) f =
      ∑ i : Fin n, (-(algebraMap K[X] (RatFunc K) (p i.castSucc)) /
        algebraMap K[X] (RatFunc K) (p (Fin.last n))) •
          LaurentSeries.expand K (Nat.toPNat q hq ^ (i : ℕ)) f := by
  have hpn : algebraMap (RatFunc K) K⸨X⸩ (algebraMap K[X] (RatFunc K) (p (Fin.last n))) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc K) K⸨X⸩).injective).mpr
      (RatFunc.algebraMap_ne_zero hlast)
  rw [Fin.sum_univ_castSucc] at hsum
  have h1 : algebraMap (RatFunc K) K⸨X⸩ (algebraMap K[X] (RatFunc K) (p (Fin.last n))) *
      LaurentSeries.expand K (Nat.toPNat q hq ^ n) f =
      -(∑ i : Fin n, algebraMap K[X] K⸨X⸩ (p i.castSucc) *
        LaurentSeries.expand K (Nat.toPNat q hq ^ (i : ℕ)) f) := by
    rw [← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
    exact eq_neg_of_add_eq_zero_right hsum
  apply mul_left_cancel₀ hpn
  rw [h1, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.smul_def, map_div₀, map_neg, ← mul_assoc, mul_div_cancel₀ _ hpn, neg_mul,
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]

/-- A Laurent series `f` is `q`-Mahler iff `q ≥ 2` and all iterates `f(X^(q^i))` lie in a
finite-dimensional `K(X)`-subspace of `K⸨X⸩`. -/
theorem isMahlerSeries_iff_exists_finiteDimensional {q : ℕ} {f : K⸨X⸩} :
    IsMahlerSeries q f ↔
      ∃ hq : 2 ≤ q, ∃ V : Submodule (RatFunc K) K⸨X⸩,
        FiniteDimensional (RatFunc K) V ∧
        ∀ i : ℕ, LaurentSeries.expand K (Nat.toPNat q (by omega) ^ i) f ∈ V := by
  constructor
  · rintro ⟨hq, n, p, hlast, hsum⟩
    have hq0 : 0 < q := by omega
    let d : ℕ+ := Nat.toPNat q hq0
    let V : Submodule (RatFunc K) K⸨X⸩ :=
      Submodule.span (RatFunc K)
        (Set.range fun i : Fin n ↦ LaurentSeries.expand K (d ^ (i : ℕ)) f)
    refine ⟨hq, V, FiniteDimensional.span_of_finite (RatFunc K) (Set.finite_range _),
      fun m ↦ ?_⟩
    have htop := expand_pow_eq_sum_of_relation hq0 hlast hsum
    induction m using Nat.strongRecOn with
    | ind m ih =>
      by_cases hm : m < n
      · exact Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + n := ⟨m - n, by omega⟩
        have hd : Nat.toPNat q (by omega) = d := rfl
        rw [hd, pow_add, ← LaurentSeries.expand_expand, htop, map_sum]
        refine Submodule.sum_mem V fun i _ ↦ ?_
        rw [Algebra.smul_def, map_mul, LaurentSeries.expand_expand, ← pow_add]
        obtain ⟨r, hr⟩ := expand_algebraMap_ratFunc_mem_range (d ^ k)
          (-(algebraMap K[X] (RatFunc K) (p i.castSucc)) /
            algebraMap K[X] (RatFunc K) (p (Fin.last n)))
        rw [← hr, ← Algebra.smul_def]
        exact V.smul_mem r (ih (k + i) (by omega))
  · rintro ⟨hq, V, hfin, hmem⟩
    rw [isMahlerSeries_iff_not_linearIndependent]
    refine ⟨hq, fun hli ↦ ?_⟩
    let N : ℕ := Module.finrank (RatFunc K) V + 1
    let g : Fin N → V := fun i ↦
      ⟨LaurentSeries.expand K (Nat.toPNat q (by omega) ^ (i : ℕ)) f, hmem i⟩
    have hg : LinearIndependent (RatFunc K) g :=
      LinearIndependent.of_comp V.subtype (hli.comp (Fin.val : Fin N → ℕ) Fin.val_injective)
    have hle := hg.fintype_card_le_finrank
    simp only [Fintype.card_fin, N] at hle
    omega

/-- Invariance of `IsMahlerSeries` under extensions of the coefficient field. -/
theorem isMahlerSeries_mapRingHom_iff {L : Type*} [Field L] (σ : K →+* L) {q : ℕ}
    {f : K⸨X⸩} :
    IsMahlerSeries q (HahnSeries.mapRingHom σ f) ↔ IsMahlerSeries q f := by
  constructor
  · rintro ⟨hq, n, p, hlast, hsum⟩
    have hsum' : ∑ i : Fin (n + 1), algebraMap L[X] L⸨X⸩ (p i) *
        HahnSeries.mapRingHom σ
          (LaurentSeries.expand K (Nat.toPNat q (by omega) ^ (i : ℕ)) f) = 0 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mapRingHom_expand]
    obtain ⟨Q, hQlast, hQ⟩ :=
      exists_polynomial_relation_of_mapRingHom σ (i₀ := Fin.last n) hlast hsum'
    exact ⟨hq, n, Q, hQlast, hQ⟩
  · rintro ⟨hq, n, p, hlast, hsum⟩
    refine ⟨hq, n, fun i ↦ (p i).map σ, Polynomial.map_ne_zero hlast, ?_⟩
    have h0 := congrArg (HahnSeries.mapRingHom σ) hsum
    rw [map_sum, map_zero] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, mapRingHom_algebraMap_polynomial, mapRingHom_expand]

end Definition

/-! ### Closure properties -/

section Closure

variable {K : Type*} [Field K]

/-- The zero Laurent series is `q`-Mahler for every `q ≥ 2`. -/
theorem isMahlerSeries_zero {q : ℕ} (hq : 2 ≤ q) : IsMahlerSeries q (0 : K⸨X⸩) :=
  ⟨hq, 0, fun _ ↦ 1, one_ne_zero, by simp⟩

/-- Every rational function in `K(X)` is `q`-Mahler for every `q ≥ 2`. -/
theorem isMahlerSeries_ratFunc {q : ℕ} (hq : 2 ≤ q) (r : RatFunc K) :
    IsMahlerSeries q (algebraMap (RatFunc K) K⸨X⸩ r) := by
  rw [isMahlerSeries_iff_exists_finiteDimensional]
  refine ⟨hq, Submodule.span (RatFunc K) {(1 : K⸨X⸩)},
    FiniteDimensional.span_of_finite (RatFunc K) (Set.finite_singleton 1), fun i ↦ ?_⟩
  obtain ⟨r', hr'⟩ := expand_algebraMap_ratFunc_mem_range (Nat.toPNat q (by omega) ^ i) r
  rw [← hr', ← mul_one (algebraMap (RatFunc K) K⸨X⸩ r'), ← Algebra.smul_def]
  exact Submodule.smul_mem _ r' (Submodule.subset_span rfl)

/-- Every polynomial is `q`-Mahler for every `q ≥ 2`. -/
theorem isMahlerSeries_polynomial {q : ℕ} (hq : 2 ≤ q) (p : K[X]) :
    IsMahlerSeries q (algebraMap K[X] K⸨X⸩ p) := by
  rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
  exact isMahlerSeries_ratFunc hq _

/-- Every constant Laurent series is `q`-Mahler for every `q ≥ 2`. -/
theorem isMahlerSeries_C {q : ℕ} (hq : 2 ≤ q) (c : K) :
    IsMahlerSeries q (HahnSeries.C c : K⸨X⸩) := by
  have hC : algebraMap K[X] K⸨X⸩ (Polynomial.C c) = HahnSeries.C c := by
    rw [algebraMap_polynomial_eq_ofPowerSeries, Polynomial.coe_C, PowerSeries.coe_C]
  rw [← hC]
  exact isMahlerSeries_polynomial hq (Polynomial.C c)

/-- The sum of two `q`-Mahler Laurent series is `q`-Mahler. -/
theorem IsMahlerSeries.add {q : ℕ} {f g : K⸨X⸩}
    (hf : IsMahlerSeries q f) (hg : IsMahlerSeries q g) : IsMahlerSeries q (f + g) := by
  rw [isMahlerSeries_iff_exists_finiteDimensional] at hf hg ⊢
  obtain ⟨hq, V, hV, hfV⟩ := hf
  obtain ⟨_, W, hW, hgW⟩ := hg
  refine ⟨hq, V ⊔ W, inferInstance, fun i ↦ ?_⟩
  rw [map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hfV i)) (Submodule.mem_sup_right (hgW i))

/-- The negation of a `q`-Mahler Laurent series is `q`-Mahler. -/
theorem IsMahlerSeries.neg {q : ℕ} {f : K⸨X⸩} (hf : IsMahlerSeries q f) :
    IsMahlerSeries q (-f) := by
  rw [isMahlerSeries_iff_exists_finiteDimensional] at hf ⊢
  obtain ⟨hq, V, hV, hfV⟩ := hf
  exact ⟨hq, V, hV, fun i ↦ by rw [map_neg]; exact V.neg_mem (hfV i)⟩

/-- The difference of two `q`-Mahler Laurent series is `q`-Mahler. -/
theorem IsMahlerSeries.sub {q : ℕ} {f g : K⸨X⸩}
    (hf : IsMahlerSeries q f) (hg : IsMahlerSeries q g) : IsMahlerSeries q (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- Multiplying a `q`-Mahler Laurent series by a rational function preserves the `q`-Mahler
property. -/
theorem IsMahlerSeries.mul_ratFunc {q : ℕ} {f : K⸨X⸩} (hf : IsMahlerSeries q f)
    (r : RatFunc K) :
    IsMahlerSeries q (algebraMap (RatFunc K) K⸨X⸩ r * f) := by
  rw [isMahlerSeries_iff_exists_finiteDimensional] at hf ⊢
  obtain ⟨hq, V, hV, hfV⟩ := hf
  refine ⟨hq, V, hV, fun i ↦ ?_⟩
  rw [map_mul]
  obtain ⟨r', hr'⟩ := expand_algebraMap_ratFunc_mem_range (Nat.toPNat q (by omega) ^ i) r
  rw [← hr', ← Algebra.smul_def]
  exact V.smul_mem r' (hfV i)

/-- The product of two `q`-Mahler Laurent series is `q`-Mahler. -/
theorem IsMahlerSeries.mul {q : ℕ} {f g : K⸨X⸩}
    (hf : IsMahlerSeries q f) (hg : IsMahlerSeries q g) : IsMahlerSeries q (f * g) := by
  rw [isMahlerSeries_iff_exists_finiteDimensional] at hf hg ⊢
  obtain ⟨hq, V, hV, hfV⟩ := hf
  obtain ⟨_, W, hW, hgW⟩ := hg
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := RatFunc K) (M := V)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := RatFunc K) (M := W)
  let s' : Set K⸨X⸩ := Subtype.val '' (s : Set V)
  let t' : Set K⸨X⸩ := Subtype.val '' (t : Set W)
  let U : Submodule (RatFunc K) K⸨X⸩ := Submodule.span (RatFunc K) (Set.image2 (· * ·) s' t')
  have hsV : V = Submodule.span (RatFunc K) s' := by
    rw [← Submodule.map_subtype_top V, ← hs, Submodule.map_span]; rfl
  have htW : W = Submodule.span (RatFunc K) t' := by
    rw [← Submodule.map_subtype_top W, ← ht, Submodule.map_span]; rfl
  have hmul : ∀ v ∈ V, ∀ w ∈ W, v * w ∈ U := fun v hv w hw ↦ by
    rw [hsV] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      rw [htW] at hw
      induction hw using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (Set.mem_image2_of_mem hx hy)
      | zero => simp
      | add y₁ y₂ _ _ ih₁ ih₂ => rw [mul_add]; exact U.add_mem ih₁ ih₂
      | smul c y _ ih => rw [mul_smul_comm]; exact U.smul_mem c ih
    | zero => simp
    | add x₁ x₂ _ _ ih₁ ih₂ => rw [add_mul]; exact U.add_mem ih₁ ih₂
    | smul c x _ ih => rw [smul_mul_assoc]; exact U.smul_mem c ih
  have hfin : FiniteDimensional (RatFunc K) U :=
    FiniteDimensional.span_of_finite (RatFunc K)
      ((s.finite_toSet.image Subtype.val).image2 (· * ·) (t.finite_toSet.image Subtype.val))
  refine ⟨hq, U, hfin, fun i ↦ ?_⟩
  rw [map_mul]
  exact hmul _ (hfV i) _ (hgW i)

/-- Expanding a `q`-Mahler Laurent series by `X ↦ X ^ q` preserves the `q`-Mahler property. -/
theorem IsMahlerSeries.expand {d : ℕ+} {f : K⸨X⸩} (hf : IsMahlerSeries (d : ℕ) f) :
    IsMahlerSeries (d : ℕ) (LaurentSeries.expand K d f) := by
  rw [isMahlerSeries_iff_exists_finiteDimensional] at hf ⊢
  obtain ⟨hq, V, hV, hfV⟩ := hf
  refine ⟨hq, V, hV, fun i ↦ ?_⟩
  have hd : Nat.toPNat (d : ℕ) (by omega) = d := PNat.eq rfl
  rw [hd, LaurentSeries.expand_expand, ← pow_succ]
  simpa [hd] using hfV (i + 1)

/-- Powers of a `q`-Mahler Laurent series are `q`-Mahler. -/
theorem IsMahlerSeries.pow {q : ℕ} {f : K⸨X⸩} (hf : IsMahlerSeries q f) (k : ℕ) :
    IsMahlerSeries q (f ^ k) := by
  induction k with
  | zero =>
    simpa [pow_zero] using isMahlerSeries_ratFunc hf.two_le (1 : RatFunc K)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul hf

/-- Any `q`-Mahler Laurent series is also `q ^ k`-Mahler for every `k ≥ 1`. -/
theorem IsMahlerSeries.pow_base {q k : ℕ} (hk : 1 ≤ k) {f : K⸨X⸩}
    (hf : IsMahlerSeries q f) :
    IsMahlerSeries (q ^ k) f := by
  rw [isMahlerSeries_iff_exists_finiteDimensional] at hf ⊢
  obtain ⟨hq, V, hV, hfV⟩ := hf
  have hqk : 2 ≤ q ^ k := le_trans hq (Nat.le_self_pow (by omega) q)
  refine ⟨hqk, V, hV, fun i ↦ ?_⟩
  have hpow : Nat.toPNat (q ^ k) (by omega) ^ i = Nat.toPNat q (by omega) ^ (k * i) :=
    PNat.eq (by rw [PNat.pow_coe, PNat.pow_coe]; exact (pow_mul q k i).symm)
  rw [hpow]
  exact hfV (k * i)

end Closure

/-! ### Reduction to nonzero leading and constant coefficients and system equivalence -/

section System

variable {K : Type*} [Field K]

/-- Contraction of a polynomial coerced to `K⸨X⸩` is again a polynomial coerced to
`K⸨X⸩`. -/
private theorem exists_contract_algebraMap_polynomial (d : ℕ+) (r : Fin d) (p : K[X]) :
    ∃ p' : K[X],
      LaurentSeries.contract d (algebraMap K[X] K⸨X⸩ p) r = algebraMap K[X] K⸨X⸩ p' := by
  obtain ⟨p', _, hp'⟩ := PowerSeries.exists_cartier_coe_polynomial_eq d r d.ne_zero p
  refine ⟨p', ?_⟩
  rw [algebraMap_polynomial_eq_ofPowerSeries, algebraMap_polynomial_eq_ofPowerSeries,
    LaurentSeries.contract_coe, hp']

/-- Contract a Mahler relation whose constant-index coefficient `p 0` vanishes to lower its order
by one while keeping the leading coefficient nonzero. -/
private theorem exists_contract_mahler_relation {q : ℕ} (hq : 0 < q) {f : K⸨X⸩} {m : ℕ}
    {p : Fin (m + 2) → K[X]} (hp0 : p 0 = 0) (hlast : p (Fin.last (m + 1)) ≠ 0)
    (hsum : ∑ i : Fin (m + 2), algebraMap K[X] K⸨X⸩ (p i) *
      LaurentSeries.expand K (Nat.toPNat q hq ^ (i : ℕ)) f = 0) :
    ∃ q' : Fin (m + 1) → K[X], q' (Fin.last m) ≠ 0 ∧
      ∑ i : Fin (m + 1), algebraMap K[X] K⸨X⸩ (q' i) *
        LaurentSeries.expand K (Nat.toPNat q hq ^ (i : ℕ)) f = 0 := by
  let d : ℕ+ := Nat.toPNat q hq
  have hex : ∃ r : Fin d,
      LaurentSeries.contract d (algebraMap K[X] K⸨X⸩ (p (Fin.last (m + 1)))) r ≠ 0 := by
    by_contra! hall
    have hzero : algebraMap K[X] K⸨X⸩ (p (Fin.last (m + 1))) = 0 := by
      rw [← LaurentSeries.sum_single_mul_expand_contract d
        (algebraMap K[X] K⸨X⸩ (p (Fin.last (m + 1))))]
      exact Finset.sum_eq_zero fun r _ ↦ by rw [hall r, map_zero, mul_zero]
    rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩] at hzero
    exact hlast (RatFunc.algebraMap_injective K
      ((algebraMap (RatFunc K) K⸨X⸩).injective (by simpa using hzero)))
  obtain ⟨r, hr⟩ := hex
  choose q' hq' using fun i : Fin (m + 1) ↦ exists_contract_algebraMap_polynomial d r (p i.succ)
  refine ⟨q', fun h0 ↦ hr (by rw [← Fin.succ_last m, hq' (Fin.last m), h0, map_zero]), ?_⟩
  rw [Fin.sum_univ_succ, hp0, map_zero, zero_mul, zero_add] at hsum
  have hcon : LaurentSeries.contract d
      (∑ i : Fin (m + 1), algebraMap K[X] K⸨X⸩ (p i.succ) *
        LaurentSeries.expand K (d ^ (i.succ : ℕ)) f) r = 0 := by
    rw [hsum]; ext k; simp
  have hmap : LaurentSeries.contract d
      (∑ i : Fin (m + 1), algebraMap K[X] K⸨X⸩ (p i.succ) *
        LaurentSeries.expand K (d ^ (i.succ : ℕ)) f) r =
      ∑ i : Fin (m + 1), LaurentSeries.contract d
        (algebraMap K[X] K⸨X⸩ (p i.succ) *
          LaurentSeries.expand K (d ^ (i.succ : ℕ)) f) r := by
    ext k; simp [LaurentSeries.coeff_contract]
  rw [← hcon, hmap]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hq' i, Fin.val_succ, pow_succ', ← LaurentSeries.expand_expand,
    mul_comm (algebraMap K[X] K⸨X⸩ (p i.succ)), LaurentSeries.contract_expand_mul, mul_comm]

/-- Any nonzero `q`-Mahler Laurent series satisfies a `q`-Mahler equation of positive order
`n ≥ 1` in which both the first coefficient `p 0` and the last coefficient `p (Fin.last n)` are
nonzero. -/
theorem IsMahlerSeries.exists_first_last_ne_zero {q : ℕ} {f : K⸨X⸩}
    (hf : IsMahlerSeries q f) (hf0 : f ≠ 0) :
    ∃ hq : 2 ≤ q, ∃ (n : ℕ) (_ : 0 < n) (p : Fin (n + 1) → K[X]),
      p 0 ≠ 0 ∧ p (Fin.last n) ≠ 0 ∧
      ∑ i : Fin (n + 1), algebraMap K[X] K⸨X⸩ (p i) *
        LaurentSeries.expand K (Nat.toPNat q (by omega) ^ (i : ℕ)) f = 0 := by
  obtain ⟨hq, n, p, hlast, hsum⟩ := hf
  refine ⟨hq, ?_⟩
  have hq0 : 0 < q := by omega
  induction n with
  | zero =>
    rw [Fin.sum_univ_one, Fin.val_zero, pow_zero, LaurentSeries.expand_one, AlgHom.id_apply] at hsum
    have hp0 : algebraMap K[X] K⸨X⸩ (p 0) ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
      exact (map_ne_zero_iff _ (algebraMap (RatFunc K) K⸨X⸩).injective).mpr
        (RatFunc.algebraMap_ne_zero hlast)
    exact ((mul_eq_zero.mp hsum).resolve_left hp0 |> hf0).elim
  | succ m ih =>
    by_cases hp0 : p 0 = 0
    · obtain ⟨q', hq'last, hq'sum⟩ := exists_contract_mahler_relation hq0 hp0 hlast hsum
      exact ih q' hq'last hq'sum
    · exact ⟨m + 1, Nat.succ_pos m, p, hp0, hlast, hsum⟩

/-- The companion matrix attached to a polynomial Mahler relation with `p 0 ≠ 0`. -/
private noncomputable def companionMatrix {n : ℕ} (p : Fin (n + 1) → K[X]) :
    Matrix (Fin n) (Fin n) (RatFunc K) :=
  Matrix.of fun i j ↦
    if i.1 = 0 then -(algebraMap K[X] (RatFunc K) (p j.succ)) / algebraMap K[X] (RatFunc K) (p 0)
    else if i.1 = j.1 + 1 then 1 else 0

private theorem det_companionMatrix {n : ℕ} (hn : 0 < n) (p : Fin (n + 1) → K[X]) :
    (companionMatrix p).det =
      (-1) ^ (n - 1) *
        (-(algebraMap K[X] (RatFunc K) (p (Fin.last n))) / algebraMap K[X] (RatFunc K) (p 0)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Matrix.det_succ_column (companionMatrix p) (Fin.last m),
    Finset.sum_eq_single (0 : Fin (m + 1))]
  · have hsub : (companionMatrix p).submatrix (Fin.succAbove (0 : Fin (m + 1)))
        (Fin.succAbove (Fin.last m)) = 1 := by
      ext i j
      simp only [Matrix.submatrix_apply, companionMatrix, Matrix.of_apply, Fin.succAbove_zero,
        Fin.val_succ, Nat.succ_ne_zero, ↓reduceIte, Fin.succAbove_last, Fin.val_castSucc,
        Nat.add_right_cancel_iff, Matrix.one_apply, Fin.ext_iff]
    rw [hsub, Matrix.det_one, mul_one, companionMatrix, Matrix.of_apply]
    simp [Fin.succ_last]
  · intro i _ hi
    have hi0 : i.1 ≠ 0 := fun h ↦ hi (Fin.ext h)
    have hlt : i.1 ≠ m + 1 := by omega
    have hcol : companionMatrix p i (Fin.last m) = 0 := by
      simp only [companionMatrix, Matrix.of_apply, Fin.val_last, hi0, hlt, ↓reduceIte]
    rw [hcol, mul_zero, zero_mul]
  · simp

private theorem companionMatrix_mulVec {q : ℕ} (hq : 0 < q) {f : K⸨X⸩} {n : ℕ} (hn : 0 < n)
    {p : Fin (n + 1) → K[X]} (hp0 : p 0 ≠ 0)
    (hsum : ∑ i : Fin (n + 1), algebraMap K[X] K⸨X⸩ (p i) *
      LaurentSeries.expand K (Nat.toPNat q hq ^ (i : ℕ)) f = 0) :
    (fun i : Fin n ↦ LaurentSeries.expand K (Nat.toPNat q hq ^ (i : ℕ)) f) =
      ((companionMatrix p).map (algebraMap (RatFunc K) K⸨X⸩)).mulVec
        (fun i : Fin n ↦ LaurentSeries.expand K (Nat.toPNat q hq)
          (LaurentSeries.expand K (Nat.toPNat q hq ^ (i : ℕ)) f)) := by
  let d : ℕ+ := Nat.toPNat q hq
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, companionMatrix, Matrix.of_apply]
  by_cases hi : i.1 = 0
  · obtain rfl : i = ⟨0, hn⟩ := Fin.ext hi
    have hp0' : algebraMap (RatFunc K) K⸨X⸩ (algebraMap K[X] (RatFunc K) (p 0)) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap (RatFunc K) K⸨X⸩).injective).mpr
        (RatFunc.algebraMap_ne_zero hp0)
    rw [Fin.sum_univ_succ] at hsum
    simp only [Fin.val_zero, pow_zero, LaurentSeries.expand_one, AlgHom.id_apply, ↓reduceIte]
      at hsum ⊢
    apply mul_left_cancel₀ hp0'
    have hneg : algebraMap (RatFunc K) K⸨X⸩ (algebraMap K[X] (RatFunc K) (p 0)) * f =
        -(∑ j : Fin n, algebraMap K[X] K⸨X⸩ (p j.succ) *
          LaurentSeries.expand K (d ^ (j.succ : ℕ)) f) := by
      rw [← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
      exact eq_neg_of_add_eq_zero_left hsum
    rw [Finset.mul_sum, hneg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [LaurentSeries.expand_expand, ← pow_succ', ← Fin.val_succ, map_div₀, map_neg,
      ← mul_assoc, mul_div_cancel₀ _ hp0', neg_mul,
      ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
  · simp only [hi, ↓reduceIte]
    let j₀ : Fin n := ⟨i.1 - 1, by omega⟩
    have hij : i.1 = j₀.1 + 1 := by simp only [j₀]; omega
    rw [Finset.sum_eq_single j₀]
    · simp only [hij, ↓reduceIte, map_one, one_mul]
      rw [LaurentSeries.expand_expand, ← pow_succ']
    · intro j _ hj
      have hne : i.1 ≠ j.1 + 1 := fun h ↦ hj (Fin.ext (by simp only [j₀]; omega))
      simp [hne]
    · simp

/-- Every coordinate of an invertible `q`-Mahler linear system has all its `q`-iterates in the
`K(X)`-span of the system coordinates. -/
private theorem expand_pow_mem_span_of_system {q m : ℕ} (hq : 0 < q)
    {A : Matrix (Fin m) (Fin m) (RatFunc K)} {F : Fin m → K⸨X⸩} (hdet : IsUnit A.det)
    (hsys : F = (A.map (algebraMap (RatFunc K) K⸨X⸩)).mulVec
      (fun i ↦ LaurentSeries.expand K (Nat.toPNat q hq) (F i))) :
    ∀ k : ℕ, ∀ i : Fin m,
      LaurentSeries.expand K (Nat.toPNat q hq ^ k) (F i) ∈
        Submodule.span (RatFunc K) (Set.range F) := by
  let d : ℕ+ := Nat.toPNat q hq
  let V : Submodule (RatFunc K) K⸨X⸩ := Submodule.span (RatFunc K) (Set.range F)
  have hinv : (fun i ↦ LaurentSeries.expand K d (F i)) =
      (A⁻¹.map (algebraMap (RatFunc K) K⸨X⸩)).mulVec F := by
    calc (fun i ↦ LaurentSeries.expand K d (F i))
        = ((A⁻¹ * A).map (algebraMap (RatFunc K) K⸨X⸩)).mulVec
            (fun i ↦ LaurentSeries.expand K d (F i)) := by
          rw [Matrix.nonsing_inv_mul A hdet, Matrix.map_one _ (map_zero _) (map_one _),
            Matrix.one_mulVec]
      _ = (A⁻¹.map (algebraMap (RatFunc K) K⸨X⸩)).mulVec F := by
          rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, ← hsys]
  intro k
  induction k with
  | zero =>
    intro i
    simpa [LaurentSeries.expand_one] using Submodule.subset_span (Set.mem_range_self i)
  | succ k ih =>
    intro i
    have hi := congrFun hinv i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hi
    rw [pow_succ, ← LaurentSeries.expand_expand, hi, map_sum]
    refine Submodule.sum_mem V fun j _ ↦ ?_
    rw [map_mul]
    obtain ⟨r, hr⟩ := expand_algebraMap_ratFunc_mem_range (d ^ k) (A⁻¹ i j)
    rw [← hr, ← Algebra.smul_def]
    exact V.smul_mem r (ih j)

/-- **System equivalence for `q`-Mahler Laurent series.** A series `f : K⸨X⸩` is `q`-Mahler if
and only if `q ≥ 2` and `f` is the first coordinate of a vector `F : Fin m → K⸨X⸩` solving
`F(X) = A(X) F(X^q)` for an invertible rational matrix `A ∈ GL_m(K(X))`. -/
theorem isMahlerSeries_iff_exists_system {q : ℕ} {f : K⸨X⸩} :
    IsMahlerSeries q f ↔
      ∃ hq : 2 ≤ q, ∃ (m : ℕ) (hm : 0 < m) (A : Matrix (Fin m) (Fin m) (RatFunc K))
        (F : Fin m → K⸨X⸩),
        IsUnit A.det ∧
        F = (A.map (algebraMap (RatFunc K) K⸨X⸩)).mulVec
          (fun i ↦ LaurentSeries.expand K (Nat.toPNat q (by omega)) (F i)) ∧
        F ⟨0, hm⟩ = f := by
  constructor
  · intro hf
    have hq := hf.two_le
    have hq0 : 0 < q := by omega
    rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨hq, 1, one_pos, 1, 0, by simp, by funext i; simp [Matrix.mulVec], rfl⟩
    · obtain ⟨_, n, hn, p, hp0, hplast, hsum⟩ := hf.exists_first_last_ne_zero hf0
      refine ⟨hq, n, hn, companionMatrix p,
        fun i ↦ LaurentSeries.expand K (Nat.toPNat q hq0 ^ (i : ℕ)) f, ?_,
        companionMatrix_mulVec hq0 hn hp0 hsum, by simp [LaurentSeries.expand_one]⟩
      rw [det_companionMatrix hn p, isUnit_iff_ne_zero]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num))
        (div_ne_zero (neg_ne_zero.mpr (RatFunc.algebraMap_ne_zero hplast))
          (RatFunc.algebraMap_ne_zero hp0))
  · rintro ⟨hq, m, hm, A, F, hdet, hsys, hF0⟩
    rw [isMahlerSeries_iff_exists_finiteDimensional]
    refine ⟨hq, Submodule.span (RatFunc K) (Set.range F),
      FiniteDimensional.span_of_finite (RatFunc K) (Set.finite_range F), fun k ↦ ?_⟩
    rw [← hF0]
    exact expand_pow_mem_span_of_system (by omega) hdet hsys k ⟨0, hm⟩

/-- If a power series `f : K⟦X⟧` is `q`-Mahler as a Laurent series, then the companion system
consists of power series in `K⟦X⟧`. -/
theorem isMahlerSeries_coe_iff_exists_powerSeries_system {q : ℕ} {f : K⟦X⟧} :
    IsMahlerSeries q (f : K⸨X⸩) ↔
      ∃ hq : 2 ≤ q, ∃ (m : ℕ) (hm : 0 < m) (A : Matrix (Fin m) (Fin m) (RatFunc K))
        (F : Fin m → K⟦X⟧),
        IsUnit A.det ∧
        (fun i ↦ (F i : K⸨X⸩)) = (A.map (algebraMap (RatFunc K) K⸨X⸩)).mulVec
          (fun i ↦ ((PowerSeries.expand q (by omega) (F i) : K⟦X⟧) : K⸨X⸩)) ∧
        F ⟨0, hm⟩ = f := by
  constructor
  · intro hf
    have hq := hf.two_le
    have hq0 : 0 < q := by omega
    rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨hq, 1, one_pos, 1, 0, by simp, by funext i; simp [Matrix.mulVec], rfl⟩
    · have hf0' : (f : K⸨X⸩) ≠ 0 :=
        (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr hf0
      obtain ⟨_, n, hn, p, hp0, hplast, hsum⟩ := hf.exists_first_last_ne_zero hf0'
      let F : Fin n → K⟦X⟧ := fun i ↦
        PowerSeries.expand (q ^ (i : ℕ)) (pow_ne_zero _ hq0.ne') f
      have hFcoe : ∀ i : Fin n,
          (F i : K⸨X⸩) = LaurentSeries.expand K (Nat.toPNat q hq0 ^ (i : ℕ)) (f : K⸨X⸩) :=
        fun i ↦ by
          rw [LaurentSeries.expand_coe (Nat.toPNat q hq0 ^ (i : ℕ)) f]
          simp only [F, PNat.pow_coe]
          rfl
      refine ⟨hq, n, hn, companionMatrix p, F, ?_, ?_, by simp [F]⟩
      · rw [det_companionMatrix hn p, isUnit_iff_ne_zero]
        exact mul_ne_zero (pow_ne_zero _ (by norm_num))
          (div_ne_zero (neg_ne_zero.mpr (RatFunc.algebraMap_ne_zero hplast))
            (RatFunc.algebraMap_ne_zero hp0))
      · have hsys := companionMatrix_mulVec hq0 hn hp0 hsum
        convert hsys using 1
        · funext i; exact hFcoe i
        · congr 1
          funext i
          rw [← hFcoe i, LaurentSeries.expand_coe (Nat.toPNat q hq0) (F i)]
          rfl
  · rintro ⟨hq, m, hm, A, F, hdet, hsys, hF0⟩
    rw [isMahlerSeries_iff_exists_system]
    refine ⟨hq, m, hm, A, fun i ↦ (F i : K⸨X⸩), hdet, ?_, congrArg _ hF0⟩
    convert hsys using 2
    funext i
    rw [LaurentSeries.expand_coe (Nat.toPNat q (by omega)) (F i)]
    rfl

end System

end TauCeti
