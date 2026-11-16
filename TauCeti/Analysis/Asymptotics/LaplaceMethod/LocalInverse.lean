/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Asymptotics.LaplaceMethod.Basic

import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.PowerSeries.Binomial
import TauCeti.RingTheory.PowerSeries.SubstInv
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Local inversion expansion for Laplace's method

This file proves the local inversion expansion of Laplace's method (DLMF §2.3(iii), formula
2.3.16; Olver 1997, Chapter 3, §7): if `p(t) - p(a) ~ ∑ pₛ (t - a)^{s + μ}` (`μ > 0`, `p₀ > 0`),
`p'(t) ~ ∑ (s + μ) pₛ (t - a)^{s + μ - 1}`, and `q(t) ~ ∑ qₛ (t - a)^{s + λ - 1}` as `t → a+`,
then `p` admits a strictly increasing local inverse `T` near `a` and

`q(T(p(a) + v)) / p'(T(p(a) + v)) ~ ∑ bₛ v^{(s + λ - μ)/μ}` as `v → 0+`,

where `bₛ = Asymptotics.laplaceCoeff μ λ (Real.log p₀) P Q s`. The coefficients are identified via
the formal Lagrange–Bürmann inversion theorem of `TauCeti.RingTheory.PowerSeries.SubstInv`.

## Main results

* `Asymptotics.isBigO_div_deriv_comp_sub_sum_laplaceCoeff`: DLMF 2.3.16 for any local right
  inverse `T` of `p` near `a`.
* `Asymptotics.exists_localInverse_laplace_expansion`: existence of `ε > 0` and a local inverse
  `T` on `[a, a + ε]` with `p` continuous and strictly increasing on `[a, a + ε]`, `p' > 0` on
  `(a, a + ε]`, and `q(T(p(a) + v)) / p'(T(p(a) + v))` satisfying DLMF 2.3.16.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.3(iii),
  <https://dlmf.nist.gov/2.3.iii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 3, §7.
-/

public section

noncomputable section

open Complex Filter Topology Set Finset PowerSeries
open scoped Real Nat

namespace Asymptotics

/-! ### Internal formal power and asymptotic power-series helpers -/

private def powSeries (ℓ r : ℂ) (P : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  C (cexp (r * ℓ)) * (PowerSeries.binomialSeries ℂ r).subst (C (cexp (-ℓ)) * P - 1)

private theorem constantCoeff_shift {ℓ : ℂ} {P : ℂ⟦X⟧} (hP : constantCoeff P = cexp ℓ) :
    constantCoeff (C (cexp (-ℓ)) * P - 1) = 0 := by
  rw [map_sub, map_mul, constantCoeff_C, hP, map_one, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, sub_self]

private theorem constantCoeff_powSeries {ℓ r : ℂ} {P : ℂ⟦X⟧} (hP : constantCoeff P = cexp ℓ) :
    constantCoeff (powSeries ℓ r P) = cexp (r * ℓ) := by
  rw [powSeries, map_mul, constantCoeff_C,
    constantCoeff_binomialSeries_subst (constantCoeff_shift hP), mul_one]

private theorem isUnit_powSeries {ℓ r : ℂ} {P : ℂ⟦X⟧} (hP : constantCoeff P = cexp ℓ) :
    IsUnit (powSeries ℓ r P) :=
  isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_powSeries hP]; exact (exp_ne_zero _).isUnit)

private theorem powSeries_zero {ℓ : ℂ} {P : ℂ⟦X⟧} (hP : constantCoeff P = cexp ℓ) :
    powSeries ℓ 0 P = 1 := by
  rw [powSeries, zero_mul, Complex.exp_zero, map_one, one_mul,
    binomialSeries_zero_subst (constantCoeff_shift hP)]

private theorem powSeries_one {ℓ : ℂ} {P : ℂ⟦X⟧} (hP : constantCoeff P = cexp ℓ) :
    powSeries ℓ 1 P = P := by
  rw [powSeries, one_mul, binomialSeries_one_subst (constantCoeff_shift hP), add_sub_cancel,
    ← mul_assoc, ← map_mul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, map_one, one_mul]

private theorem powSeries_add {ℓ r₁ r₂ : ℂ} {P : ℂ⟦X⟧} (hP : constantCoeff P = cexp ℓ) :
    powSeries ℓ (r₁ + r₂) P = powSeries ℓ r₁ P * powSeries ℓ r₂ P := by
  rw [powSeries, powSeries, powSeries, add_mul, Complex.exp_add, map_mul,
    binomialSeries_add_subst (constantCoeff_shift hP)]
  ring

private theorem powSeries_pow {ℓ r : ℂ} {P : ℂ⟦X⟧} (hP : constantCoeff P = cexp ℓ) (n : ℕ) :
    powSeries ℓ r P ^ n = powSeries ℓ (n * r) P := by
  rw [powSeries, powSeries, mul_pow, ← map_pow, ← Complex.exp_nat_mul,
    binomialSeries_subst_pow (constantCoeff_shift hP), nsmul_eq_mul, mul_assoc]

private theorem derivative_powSeries {ℓ r : ℂ} {P : ℂ⟦X⟧} (hP : constantCoeff P = cexp ℓ) :
    d⁄dX (powSeries ℓ r P) = C r * powSeries ℓ (r - 1) P * d⁄dX P := by
  have hder : d⁄dX (C (cexp (-ℓ)) * P - 1) = C (cexp (-ℓ)) * d⁄dX P := by
    rw [map_sub, derivative_one, sub_zero, Derivation.leibniz, derivative_C, smul_zero, add_zero,
      smul_eq_mul]
  rw [powSeries, Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul,
    derivative_binomialSeries_subst (constantCoeff_shift hP), hder, powSeries, sub_mul, one_mul,
    Complex.exp_sub, div_eq_mul_inv, ← Complex.exp_neg, map_mul, Algebra.smul_def, algebraMap_eq]
  ring

/-- Local predicate: `f` admits `S` as an asymptotic power series in `z` along `l`. -/
private def HasPowExp {α : Type*} (l : Filter α) (z : α → ℂ) (S : ℂ⟦X⟧) (f : α → ℂ) : Prop :=
  ∀ N : ℕ, (fun x ↦ f x - ∑ k ∈ range N, coeff k S * z x ^ k) =O[l] fun x ↦ ‖z x‖ ^ N

private theorem hasPowExp_congr {α : Type*} {l : Filter α} {z : α → ℂ} {S : ℂ⟦X⟧} {f g : α → ℂ}
    (h : f =ᶠ[l] g) (hf : HasPowExp l z S f) : HasPowExp l z S g := fun N ↦
  (hf N).congr' (h.mono fun _ hx ↦ by dsimp only; rw [hx]) EventuallyEq.rfl

private theorem hasPowExp_comp_tendsto {α β : Type*} {l : Filter α} {l' : Filter β} {z : α → ℂ}
    {S : ℂ⟦X⟧} {f : α → ℂ} {y : β → α} (hy : Tendsto y l' l) (hf : HasPowExp l z S f) :
    HasPowExp l' (z ∘ y) S (f ∘ y) := fun N ↦ (hf N).comp_tendsto hy

private theorem hasPowExp_const {α : Type*} (l : Filter α) (z : α → ℂ) (c : ℂ) :
    HasPowExp l z (C c) (fun _ ↦ c) := fun N ↦ by
  cases N with
  | zero => exact isBigO_iff.mpr ⟨‖c‖, Eventually.of_forall fun _ ↦ by simp⟩
  | succ n =>
    have hsum : ∀ x, ∑ k ∈ range (n + 1), coeff k (C c) * z x ^ k = c := fun x ↦ by
      rw [Finset.sum_eq_single 0 (fun k _ hk ↦ by simp [coeff_C, hk]) (by simp)]; simp
    simp only [hsum, sub_self]; exact isBigO_zero _ _

private theorem hasPowExp_X {α : Type*} {l : Filter α} {z : α → ℂ} (hz : Tendsto z l (𝓝 0)) :
    HasPowExp l z X z := fun N ↦ by
  match N with
  | 0 => simpa using hz.isBigO_one ℝ
  | 1 => simpa using (isBigO_refl z l).norm_right
  | n + 2 =>
    have hsum : ∀ x, ∑ k ∈ range (n + 2), coeff k (X : ℂ⟦X⟧) * z x ^ k = z x := fun x ↦ by
      rw [Finset.sum_eq_single 1 (fun k _ hk ↦ by simp [coeff_X, hk]) (by simp)]; simp
    simp only [hsum, sub_self]; exact isBigO_zero _ _

private theorem hasPowExp_sub {α : Type*} {l : Filter α} {z : α → ℂ} {S T : ℂ⟦X⟧} {f g : α → ℂ}
    (hf : HasPowExp l z S f) (hg : HasPowExp l z T g) :
    HasPowExp l z (S - T) (fun x ↦ f x - g x) := fun N ↦ by
  simpa [map_sub, sub_mul, Finset.sum_sub_distrib, sub_sub_sub_comm] using (hf N).sub (hg N)

private theorem hasPowExp_const_mul {α : Type*} {l : Filter α} {z : α → ℂ} {S : ℂ⟦X⟧}
    {f : α → ℂ} (c : ℂ) (hf : HasPowExp l z S f) :
    HasPowExp l z (C c * S) (fun x ↦ c * f x) := fun N ↦
  ((hf N).const_mul_left c).congr_left fun _ ↦ by
    simp only [coeff_C_mul, mul_assoc, ← Finset.mul_sum, mul_sub]

private theorem hasPowExp_finset_sum {α ι : Type*} {l : Filter α} {z : α → ℂ} (s : Finset ι)
    {S : ι → ℂ⟦X⟧} {f : ι → α → ℂ} (h : ∀ i ∈ s, HasPowExp l z (S i) (f i)) :
    HasPowExp l z (∑ i ∈ s, S i) (fun x ↦ ∑ i ∈ s, f i x) := fun N ↦
  (IsBigO.sum fun i hi ↦ h i hi N).congr_left fun _ ↦ by
    simp only [Finset.sum_apply, Finset.sum_sub_distrib, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]

private theorem hasPowExp_tendsto_constantCoeff {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto z l (𝓝 0)) {S : ℂ⟦X⟧} {f : α → ℂ} (hf : HasPowExp l z S f) :
    Tendsto f l (𝓝 (constantCoeff S)) := by
  simpa using ((by simpa [coeff_zero_eq_constantCoeff] using hf 1 :
    (fun x ↦ f x - constantCoeff S) =O[l] fun x ↦ ‖z x‖).trans_tendsto
    (by simpa using hz.norm)).add_const (constantCoeff S)

private theorem hasPowExp_eventually_pos {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto z l (𝓝 0)) {c : ℝ} (hc : 0 < c) {S : ℂ⟦X⟧} (hS : constantCoeff S = (c : ℂ))
    {f : α → ℝ} (hf : HasPowExp l z S (fun x ↦ (f x : ℂ))) : ∀ᶠ x in l, 0 < f x := by
  have ht := ((Complex.continuous_re.tendsto (c : ℂ)).comp
    (hS ▸ hasPowExp_tendsto_constantCoeff hz hf)).congr fun _ ↦ ofReal_re _
  rw [ofReal_re] at ht
  exact ht.eventually (lt_mem_nhds hc)

private theorem isBigO_const_mul_pow_of_le {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto z l (𝓝 0)) (c : ℂ) {m n : ℕ} (hnm : n ≤ m) :
    (fun x ↦ c * z x ^ m) =O[l] fun x ↦ ‖z x‖ ^ n := by
  have hzn : Tendsto (fun x ↦ ‖z x‖) l (𝓝 0) := by simpa using hz.norm
  have hle : (fun x ↦ ‖z x‖ ^ m) =O[l] fun x ↦ ‖z x‖ ^ n :=
    isBigO_iff.mpr ⟨1, (hzn.eventually (ge_mem_nhds zero_lt_one)).mono fun _ hx ↦ by
      simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), one_mul]
      exact pow_le_pow_of_le_one (norm_nonneg _) hx hnm⟩
  exact ((isBigO_iff.mpr ⟨1, Eventually.of_forall fun _ ↦ by simp⟩).trans hle).const_mul_left c

private theorem hasPowExp_mul {α : Type*} {l : Filter α} {z : α → ℂ} (hz : Tendsto z l (𝓝 0))
    {S T : ℂ⟦X⟧} {f g : α → ℂ} (hf : HasPowExp l z S f) (hg : HasPowExp l z T g) :
    HasPowExp l z (S * T) (fun x ↦ f x * g x) := fun N ↦ by
  set pN : α → ℂ := fun x ↦ ∑ i ∈ range N, coeff i S * z x ^ i
  set qN : α → ℂ := fun x ↦ ∑ j ∈ range N, coeff j T * z x ^ j
  have hpN_bd : pN =O[l] fun _ ↦ (1 : ℝ) :=
    (IsBigO.sum (s := range N) (A := fun i x ↦ coeff i S * z x ^ i) fun i _ ↦
      (isBigO_const_mul_pow_of_le hz (coeff i S) (Nat.zero_le i)).congr_right
        fun _ ↦ by simp).congr_left fun _ ↦ by simp [pN, Finset.sum_apply]
  have h1 : (fun x ↦ (f x - pN x) * g x) =O[l] fun x ↦ ‖z x‖ ^ N := by
    simpa using (hf N).mul (by simpa using hg 0 : g =O[l] fun _ ↦ (1 : ℝ))
  have h2 : (fun x ↦ pN x * (g x - qN x)) =O[l] fun x ↦ ‖z x‖ ^ N := by
    simpa using hpN_bd.mul (hg N)
  have hfilt : (range N ×ˢ range N).filter (fun p ↦ p.1 + p.2 < N) =
      (range N).biUnion Finset.antidiagonal := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_biUnion,
      Finset.mem_antidiagonal]
    exact ⟨fun ⟨_, hij⟩ ↦ ⟨i + j, hij, rfl⟩, fun ⟨k, hk, h⟩ ↦ ⟨⟨by omega, by omega⟩, h ▸ hk⟩⟩
  have hdisj : Set.PairwiseDisjoint (Finset.range N : Set ℕ) Finset.antidiagonal :=
    fun _ _ _ _ hne ↦ Finset.disjoint_left.mpr fun _ h1 h2 ↦
      hne ((Finset.mem_antidiagonal.mp h1).symm.trans (Finset.mem_antidiagonal.mp h2))
  have h3 : (fun x ↦ pN x * qN x - ∑ k ∈ range N, coeff k (S * T) * z x ^ k) =O[l]
      fun x ↦ ‖z x‖ ^ N := by
    refine (IsBigO.sum (s := (range N ×ˢ range N).filter (fun p ↦ ¬ p.1 + p.2 < N))
      (A := fun p x ↦ coeff p.1 S * coeff p.2 T * z x ^ (p.1 + p.2)) fun p hp ↦
      isBigO_const_mul_pow_of_le hz (coeff p.1 S * coeff p.2 T)
        (Nat.le_of_not_lt (Finset.mem_filter.mp hp).2)).congr_left fun x ↦ ?_
    have hmul : pN x * qN x =
        ∑ p ∈ range N ×ˢ range N, coeff p.1 S * coeff p.2 T * z x ^ (p.1 + p.2) := by
      simp only [pN, qN, Finset.sum_mul_sum, Finset.sum_product]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by rw [pow_add]; ring
    have hlow : ∑ p ∈ (range N ×ˢ range N).filter (fun p ↦ p.1 + p.2 < N),
        coeff p.1 S * coeff p.2 T * z x ^ (p.1 + p.2) =
        ∑ k ∈ range N, coeff k (S * T) * z x ^ k := by
      rw [hfilt, Finset.sum_biUnion hdisj]
      exact Finset.sum_congr rfl fun k _ ↦ by
        rw [coeff_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p hp ↦ by rw [Finset.mem_antidiagonal.mp hp]
    rw [hmul, ← Finset.sum_filter_add_sum_filter_not (range N ×ˢ range N) (fun p ↦ p.1 + p.2 < N),
      hlow, add_sub_cancel_left, Finset.sum_apply]
  exact ((h1.add h2).add h3).congr_left fun _ ↦ by ring

private theorem hasPowExp_pow {α : Type*} {l : Filter α} {z : α → ℂ} (hz : Tendsto z l (𝓝 0))
    {S : ℂ⟦X⟧} {f : α → ℂ} (hf : HasPowExp l z S f) (n : ℕ) :
    HasPowExp l z (S ^ n) (fun x ↦ f x ^ n) := by
  induction n with
  | zero => simpa using hasPowExp_const l z 1
  | succ n ih => simpa [pow_succ] using hasPowExp_mul hz ih hf

private theorem hasPowExp_inv {α : Type*} {l : Filter α} {z : α → ℂ} (hz : Tendsto z l (𝓝 0))
    {S : ℂ⟦X⟧} (hS : constantCoeff S ≠ 0) {f : α → ℂ} (hf : HasPowExp l z S f) :
    HasPowExp l z S⁻¹ (fun x ↦ (f x)⁻¹) := by
  have hf_tend := hasPowExp_tendsto_constantCoeff hz hf
  have hf_inv_bd : (fun x ↦ (f x)⁻¹) =O[l] fun _ ↦ (1 : ℝ) := (hf_tend.inv₀ hS).isBigO_one ℝ
  intro N; cases N with
  | zero => simpa using hf_inv_bd
  | succ n =>
    set PN : ℂ⟦X⟧ := ∑ k ∈ range (n + 1), C (coeff k S⁻¹) * X ^ k
    have hrN : HasPowExp l z PN (fun x ↦ ∑ k ∈ range (n + 1), coeff k S⁻¹ * z x ^ k) :=
      hasPowExp_finset_sum (range (n + 1)) fun k _ ↦
        hasPowExp_const_mul (coeff k S⁻¹) (hasPowExp_pow hz (hasPowExp_X hz) k)
    have hcoeff_PN : ∀ j < n + 1, coeff j PN = coeff j S⁻¹ := fun j hj ↦ by
      simp only [PN, map_sum, coeff_C_mul, coeff_X_pow]
      rw [Finset.sum_eq_single j (fun k _ hkj ↦ by simp [Ne.symm hkj])
        (fun h ↦ absurd (Finset.mem_range.mpr hj) h)]; simp
    have hsum1 : ∀ x, ∑ k ∈ range (n + 1), coeff k (S * PN) * z x ^ k = 1 := fun x ↦ by
      have hmul : ∀ k ∈ range (n + 1), coeff k (S * PN) = coeff k (1 : ℂ⟦X⟧) := fun k hk ↦ by
        rw [← PowerSeries.mul_inv_cancel S hS, coeff_mul, coeff_mul]
        exact Finset.sum_congr rfl fun p hp ↦ by
          rw [hcoeff_PN p.2 (by
            have := Finset.mem_antidiagonal.mp hp; have := Finset.mem_range.mp hk; omega)]
      rw [Finset.sum_congr rfl fun k hk ↦ by rw [hmul k hk],
        Finset.sum_eq_single 0 (fun k _ hk ↦ by simp [coeff_one, hk]) (by simp)]; simp
    have hfr : (fun x ↦ f x * (∑ k ∈ range (n + 1), coeff k S⁻¹ * z x ^ k) - 1) =O[l]
        fun x ↦ ‖z x‖ ^ (n + 1) := by simpa only [hsum1] using hasPowExp_mul hz hf hrN (n + 1)
    exact (by simpa using (hf_inv_bd.mul hfr).neg_left :
        (fun x ↦ -((f x)⁻¹ * (f x * (∑ k ∈ range (n + 1), coeff k S⁻¹ * z x ^ k) - 1))) =O[l]
          fun x ↦ ‖z x‖ ^ (n + 1)).congr'
      ((hf_tend.eventually_ne hS).mono fun _ hx ↦ by field_simp [hx]; ring) EventuallyEq.rfl

private theorem coeff_pow_eq_zero_of_lt {U : ℂ⟦X⟧} (hU0 : constantCoeff U = 0) {j k : ℕ}
    (hjk : j < k) : coeff j (U ^ k) = 0 := by
  obtain ⟨V, rfl⟩ := X_dvd_iff.mpr hU0
  rw [mul_pow, coeff_X_pow_mul', ite_eq_right (not_le.mpr hjk)]

private theorem hasPowExp_subst {α : Type*} {l : Filter α} {w u : α → ℂ}
    (hw : Tendsto w l (𝓝 0)) {U S : ℂ⟦X⟧} (hU0 : constantCoeff U = 0) {f : α → ℂ}
    (hu : HasPowExp l w U u) (hf : HasPowExp l u S f) :
    HasPowExp l w (S.subst U) f := fun N ↦ by
  have hu_bd : u =O[l] fun x ↦ ‖w x‖ := by simpa [coeff_zero_eq_constantCoeff, hU0] using hu 1
  have h1 : (fun x ↦ f x - ∑ k ∈ range N, coeff k S * u x ^ k) =O[l] fun x ↦ ‖w x‖ ^ N :=
    (hf N).trans (by simpa using hu_bd.norm_left.pow N)
  have h2 : (fun x ↦ (∑ k ∈ range N, coeff k S * u x ^ k) -
      ∑ j ∈ range N, coeff j (S.subst U) * w x ^ j) =O[l] fun x ↦ ‖w x‖ ^ N := by
    refine (IsBigO.sum (s := range N)
      (A := fun k x ↦ coeff k S * u x ^ k -
        ∑ j ∈ range N, coeff k S * coeff j (U ^ k) * w x ^ j) fun k _ ↦
      (hasPowExp_const_mul (coeff k S) (hasPowExp_pow hw hu k) N).congr_left fun _ ↦ by
        simp [coeff_C_mul, mul_assoc]).congr_left fun x ↦ ?_
    rw [Finset.sum_apply, Finset.sum_sub_distrib, Finset.sum_comm]
    congr 1; refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [← Finset.sum_mul, coeff_subst_eq_sum_range S hU0 j]
    congr 1; simp only [smul_eq_mul]
    rw [← Finset.sum_subset (Finset.range_mono (Finset.mem_range.mp hj))]
    intro k _ hk; simp only [Finset.mem_range, not_lt] at hk
    rw [coeff_pow_eq_zero_of_lt hU0 (by omega), mul_zero]
  exact (h1.add h2).congr_left fun _ ↦ by ring

private theorem hasPowExp_cpow_of_pos {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto z l (𝓝 0)) {p0 : ℝ} (hp0 : 0 < p0) {P : ℂ⟦X⟧}
    (hP0 : constantCoeff P = (p0 : ℂ)) {f : α → ℝ}
    (hf : HasPowExp l z P (fun x ↦ (f x : ℂ))) (r : ℂ) :
    HasPowExp l z (powSeries (Real.log p0) r P) (fun x ↦ ((f x : ℝ) : ℂ) ^ r) := by
  set ℓ : ℂ := (Real.log p0 : ℂ)
  have hexp : cexp ℓ = (p0 : ℂ) := by rw [← ofReal_exp, Real.exp_log hp0]
  set u : α → ℂ := fun x ↦ cexp (-ℓ) * (f x : ℂ) - 1
  set U : ℂ⟦X⟧ := C (cexp (-ℓ)) * P - 1
  have hU0 : constantCoeff U = 0 := constantCoeff_shift (hP0.trans hexp.symm)
  have hu_exp : HasPowExp l z U u :=
    hasPowExp_sub (hasPowExp_const_mul (cexp (-ℓ)) hf) (hasPowExp_const l z 1)
  have hbin : HasPowExp l u (PowerSeries.binomialSeries ℂ r) (fun x ↦ (1 + u x) ^ r) := fun N ↦
    ((Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := r)).isBigO_sub_partialSum_pow N
      |>.comp_tendsto (hU0 ▸ hasPowExp_tendsto_constantCoeff hz hu_exp)).congr_left fun _ ↦ by
      simp only [Function.comp_apply, zero_add, FormalMultilinearSeries.partialSum,
        _root_.binomialSeries_apply, smul_eq_mul, List.ofFn_const, List.prod_replicate,
        PowerSeries.binomialSeries_coeff, mul_one]
  refine hasPowExp_congr ((hasPowExp_eventually_pos hz hp0 hP0 hf).mono fun x hx ↦ ?_)
    (hasPowExp_const_mul (cexp (r * ℓ)) (hasPowExp_subst hz hU0 hu_exp hbin))
  have h1u : 1 + u x = ((f x / p0 : ℝ) : ℂ) := by
    simp only [u, Complex.exp_neg, hexp]; push_cast; ring
  dsimp only
  rw [h1u, cpow_def_of_ne_zero (ofReal_ne_zero.mpr (div_pos hx hp0).ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← ofReal_log (div_pos hx hp0).le,
    ← ofReal_log hx.le, Real.log_div hx.ne' hp0.ne', ofReal_sub, ← Complex.exp_add]
  congr 1; simp only [ℓ]; ring

private theorem hasPowExp_substInv {α : Type*} {l : Filter α} {w u : α → ℂ}
    (hu : Tendsto u l (𝓝 0)) {H : ℂ⟦X⟧} (hH0 : constantCoeff H = 0)
    (hH1 : IsUnit (coeff 1 H)) {h : α → ℂ} (hh : HasPowExp l u H h) (hhw : h =ᶠ[l] w) :
    HasPowExp l w (H.substInvOfIsUnit hH1) u := by
  set U : ℂ⟦X⟧ := H.substInvOfIsUnit hH1
  have hu_bd : u =O[l] w := by
    have h2 : (fun x ↦ h x - coeff 1 H * u x) =O[l] fun x ↦ ‖u x‖ ^ 2 := by
      simpa [Finset.sum_range_succ, coeff_zero_eq_constantCoeff, hH0] using hh 2
    have hsq : (fun x ↦ ‖u x‖ ^ 2) =o[l] u := isLittleO_iff.mpr fun c hc ↦
      ((by simpa using hu.norm : Tendsto (fun x ↦ ‖u x‖) l (𝓝 0)).eventually
        (gt_mem_nhds hc)).mono fun _ hx ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
        exact mul_le_mul_of_nonneg_right hx.le (norm_nonneg _)
    have hu_c1 : u =O[l] fun x ↦ coeff 1 H * u x :=
      isBigO_iff.mpr ⟨‖coeff 1 H‖⁻¹, Eventually.of_forall fun _ ↦ by
        rw [norm_mul, inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hH1.ne_zero)]⟩
    have heq : h ~[l] fun x ↦ coeff 1 H * u x := (h2.trans_isLittleO hsq).trans_isBigO hu_c1
    exact (hu_c1.trans heq.symm.isBigO).congr' EventuallyEq.rfl hhw
  intro N; match N with
  | 0 => simpa using hu.isBigO_one ℝ
  | 1 => simpa [U, coeff_zero_eq_constantCoeff,
      PowerSeries.constantCoeff_substInvOfIsUnit H hH1] using hu_bd.norm_right
  | n + 2 =>
    set PN : ℂ⟦X⟧ := ∑ k ∈ range (n + 2), C (coeff k U) * H ^ k
    have hPN : HasPowExp l u PN (fun x ↦ ∑ k ∈ range (n + 2), coeff k U * h x ^ k) :=
      hasPowExp_finset_sum (range (n + 2)) fun k _ ↦
        hasPowExp_const_mul (coeff k U) (hasPowExp_pow hu hh k)
    have hsumX : ∀ x, ∑ j ∈ range (n + 2), coeff j PN * u x ^ j = u x := fun x ↦ by
      have hcoeff : ∀ j ∈ range (n + 2), coeff j PN = coeff j (X : ℂ⟦X⟧) := fun j hj ↦ by
        rw [← H.subst_substInvOfIsUnit_left hH0 hH1, coeff_subst_eq_sum_range U hH0 j]
        simp only [PN, map_sum, coeff_C_mul, smul_eq_mul]
        rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))]
        intro k _ hk; simp only [Finset.mem_range, not_lt] at hk
        rw [coeff_pow_eq_zero_of_lt hH0 (by omega), mul_zero]
      rw [Finset.sum_congr rfl fun j hj ↦ by rw [hcoeff j hj],
        Finset.sum_eq_single 1 (fun k _ hk ↦ by simp [coeff_X, hk]) (by simp)]; simp
    exact ((by simpa only [hsumX, neg_sub] using (hPN (n + 2)).neg_left :
        (fun x ↦ u x - ∑ k ∈ range (n + 2), coeff k U * h x ^ k) =O[l]
          fun x ↦ ‖u x‖ ^ (n + 2)).congr' (hhw.mono fun _ hx ↦ by simp [hx]) EventuallyEq.rfl).trans
      (by simpa using hu_bd.norm_left.norm_right.pow (n + 2))

private theorem tendsto_sub_nhdsGT (a : ℝ) : Tendsto (fun t : ℝ ↦ t - a) (𝓝[>] a) (𝓝 0) := by
  have hsub : Tendsto (fun t : ℝ ↦ t - a) (𝓝 a) (𝓝 (a - a)) :=
    (continuous_id.sub continuous_const).continuousAt
  simpa [sub_self] using hsub.mono_left nhdsWithin_le_nhds

/-- Factoring out `((t - a) : ℂ) ^ α` turns an expansion in `(t - a)^{s + α}` into `HasPowExp`. -/
private theorem hasPowExp_div_cpow {a : ℝ} {α : ℂ} {g : ℝ → ℂ} {cs : ℕ → ℂ}
    (hg : ∀ M : ℕ,
      (fun t : ℝ ↦ g t - ∑ s ∈ range M, cs s * ((t - a : ℝ) : ℂ) ^ ((s : ℂ) + α)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((M : ℝ) + α.re)) :
    HasPowExp (𝓝[>] a) (fun t ↦ ((t - a : ℝ) : ℂ)) (PowerSeries.mk cs)
      (fun t ↦ g t / ((t - a : ℝ) : ℂ) ^ α) := fun M ↦ by
  have hden : (fun t : ℝ ↦ (((t - a : ℝ) : ℂ) ^ α)⁻¹) =O[𝓝[>] a] fun t ↦ ((t - a) ^ α.re)⁻¹ :=
    isBigO_iff.mpr ⟨1, eventually_mem_nhdsWithin.mono fun t ht ↦ by
      have hta : 0 < t - a := sub_pos.mpr ht
      rw [norm_inv, norm_cpow_eq_rpow_re_of_pos hta, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos hta _)), one_mul]⟩
  refine ((hg M).mul hden).congr' (eventually_mem_nhdsWithin.mono fun t ht ↦ ?_)
    (eventually_mem_nhdsWithin.mono fun t ht ↦ ?_)
  · dsimp only
    have htac : ((t - a : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (sub_pos.mpr ht).ne'
    simp only [div_eq_mul_inv, sub_mul, Finset.sum_mul, coeff_mk]
    congr 1; refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [cpow_add _ _ htac, cpow_natCast, mul_assoc, mul_assoc,
      mul_inv_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl htac)), mul_one]
  · dsimp only
    have hta : 0 < t - a := sub_pos.mpr ht
    rw [Real.rpow_add hta, Real.rpow_natCast, mul_assoc,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hta α.re).ne', mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hta]

/-- Real specialization of `hasPowExp_div_cpow`: factoring out `(t - a) ^ α` for real `g`. -/
private theorem hasPowExp_ofReal_div_rpow {a α : ℝ} {g : ℝ → ℝ} {cs : ℕ → ℝ}
    (hg : ∀ M : ℕ,
      (fun t : ℝ ↦ g t - ∑ s ∈ range M, cs s * (t - a) ^ ((s : ℝ) + α)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((M : ℝ) + α)) :
    HasPowExp (𝓝[>] a) (fun t ↦ ((t - a : ℝ) : ℂ)) (PowerSeries.mk fun n ↦ (cs n : ℂ))
      (fun t ↦ ((g t / (t - a) ^ α : ℝ) : ℂ)) :=
  hasPowExp_congr
    (eventually_mem_nhdsWithin.mono fun _ ht ↦ by
      dsimp only; rw [ofReal_div, ofReal_cpow (sub_pos.mpr ht).le])
    (hasPowExp_div_cpow (α := (α : ℂ)) fun M ↦
      (isBigO_norm_left.mp
        ((hg M).norm_left.congr_left fun _ ↦ (Complex.norm_real _).symm)).congr'
        (eventually_mem_nhdsWithin.mono fun _ ht ↦ by
          dsimp only; simp only [ofReal_sub, ofReal_sum, ofReal_mul]
          exact congrArg _ (Finset.sum_congr rfl fun _ _ ↦ by
            rw [ofReal_cpow (sub_pos.mpr ht).le, ofReal_add, ofReal_natCast, ofReal_sub]))
        (Eventually.of_forall fun _ ↦ by simp))

/-- Formal Lagrange–Bürmann computation identifying the coefficients of `M(U)` with
`laplaceCoeff μ lam ℓ P Q s`. -/
private theorem coeff_subst_laplace_aux {μ : ℝ} (hμ : μ ≠ 0) {lam ℓ : ℂ} {P Q : ℂ⟦X⟧}
    (hP0 : constantCoeff P = cexp ℓ) (s : ℕ) :
    let F : ℂ⟦X⟧ := powSeries ℓ (μ : ℂ)⁻¹ P
    let H : ℂ⟦X⟧ := X * F
    have hH1 : IsUnit (coeff 1 H) := by
      have : coeff 1 H = cexp ((μ : ℂ)⁻¹ * ℓ) := by
        simp [H, F, coeff_succ_X_mul 0, coeff_zero_eq_constantCoeff, constantCoeff_powSeries hP0]
      rw [this]; exact (exp_ne_zero _).isUnit
    let U : ℂ⟦X⟧ := H.substInvOfIsUnit hH1
    let R : ℂ⟦X⟧ := C (μ : ℂ) * P + X * d⁄dX P
    let M : ℂ⟦X⟧ := Q * (R * powSeries ℓ ((lam - μ) / μ) P)⁻¹
    coeff s (M.subst U) = laplaceCoeff μ lam ℓ P Q s := by
  intro F H hH1 U R M
  have hμc : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ
  have hμ1 : C (μ : ℂ) * C (μ : ℂ)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hμc, map_one]
  have hU0 : constantCoeff U = 0 := PowerSeries.constantCoeff_substInvOfIsUnit H hH1
  have hHU : H.subst U = X := H.subst_substInvOfIsUnit_right (by simp [H]) hH1
  have hUsub : HasSubst U := .of_constantCoeff_zero' hU0
  have hR_eq : R = C (μ : ℂ) * powSeries ℓ (1 - (μ : ℂ)⁻¹) P * d⁄dX H := by
    have hdH : d⁄dX H = F + X * (C (μ : ℂ)⁻¹ * powSeries ℓ ((μ : ℂ)⁻¹ - 1) P * d⁄dX P) := by
      simp only [H, F, Derivation.leibniz, derivative_X, smul_eq_mul, derivative_powSeries hP0]
      ring
    have h1 : powSeries ℓ (1 - (μ : ℂ)⁻¹) P * F = P := by
      dsimp only [F]; rw [← powSeries_add hP0, sub_add_cancel, powSeries_one hP0]
    have h0 : powSeries ℓ (1 - (μ : ℂ)⁻¹) P * powSeries ℓ ((μ : ℂ)⁻¹ - 1) P = 1 := by
      rw [← powSeries_add hP0, sub_add_sub_cancel', sub_self, powSeries_zero hP0]
    rw [hdH, mul_add]
    linear_combination C (μ : ℂ) * h1.symm +
      (C (μ : ℂ) * C (μ : ℂ)⁻¹) * (X * d⁄dX P) * h0.symm + (X * d⁄dX P) * hμ1.symm
  have hdenom : R * powSeries ℓ ((lam - μ) / μ) P =
      C (μ : ℂ) * powSeries ℓ ((lam - 1) / μ) P * d⁄dX H := by
    have hmul := (powSeries_add (r₁ := 1 - (μ : ℂ)⁻¹) (r₂ := (lam - μ) / μ) hP0).symm
    rw [(by field_simp [hμc]; ring : (1 - (μ : ℂ)⁻¹) + (lam - μ) / μ = (lam - 1) / μ)] at hmul
    rw [hR_eq]; linear_combination C (μ : ℂ) * d⁄dX H * hmul
  have hMQ : M * (C (μ : ℂ) * powSeries ℓ ((lam - 1) / μ) P * d⁄dX H) = Q := by
    have hdenom0 : constantCoeff (R * powSeries ℓ ((lam - μ) / μ) P) ≠ 0 := by
      rw [map_mul, (by simp [R, hP0] : constantCoeff R = (μ : ℂ) * cexp ℓ),
        constantCoeff_powSeries hP0]
      exact mul_ne_zero (mul_ne_zero hμc (exp_ne_zero _)) (exp_ne_zero _)
    rw [← hdenom]; dsimp only [M]; rw [mul_assoc, PowerSeries.inv_mul_cancel _ hdenom0, mul_one]
  have hMU : M.subst U =
      C (μ : ℂ)⁻¹ * ((Q * powSeries ℓ ((1 - lam) / μ) P).subst U * d⁄dX U) := by
    have hchain : (d⁄dX H).subst U * d⁄dX U = 1 := by
      rw [← derivative_subst hUsub, hHU, derivative_X]
    have hsub_eq : M.subst U *
        (C (μ : ℂ) * (powSeries ℓ ((lam - 1) / μ) P).subst U * (d⁄dX H).subst U) = Q.subst U := by
      have h := congrArg (PowerSeries.subst U) hMQ
      rwa [subst_mul hUsub (f := M), subst_mul hUsub (g := d⁄dX H),
        subst_mul hUsub (f := C (μ : ℂ)), subst_C] at h
    have hinv_pow :
        (powSeries ℓ ((lam - 1) / μ) P).subst U * (powSeries ℓ ((1 - lam) / μ) P).subst U = 1 := by
      rw [← subst_mul hUsub, ← powSeries_add hP0,
        (by ring : (lam - 1) / (μ : ℂ) + (1 - lam) / (μ : ℂ) = 0), powSeries_zero hP0,
        ← coe_substAlgHom hUsub, map_one]
    conv_rhs => rw [subst_mul hUsub]
    linear_combination
      C (μ : ℂ)⁻¹ * (powSeries ℓ ((1 - lam) / μ) P).subst U * d⁄dX U * hsub_eq -
      M.subst U * (C (μ : ℂ) * C (μ : ℂ)⁻¹) *
        ((powSeries ℓ ((lam - 1) / μ) P).subst U * (powSeries ℓ ((1 - lam) / μ) P).subst U) *
        hchain -
      M.subst U * (C (μ : ℂ) * C (μ : ℂ)⁻¹) * hinv_pow - M.subst U * hμ1
  let Fu : ℂ⟦X⟧ˣ := (isUnit_powSeries (r := (μ : ℂ)⁻¹) hP0).unit
  have hFu_inv : (↑Fu⁻¹ : ℂ⟦X⟧) = powSeries ℓ (-(μ : ℂ)⁻¹) P := by
    have hmul : (Fu : ℂ⟦X⟧) * powSeries ℓ (-(μ : ℂ)⁻¹) P = 1 := by
      rw [(isUnit_powSeries (r := (μ : ℂ)⁻¹) hP0).unit_spec, ← powSeries_add hP0, add_neg_cancel,
        powSeries_zero hP0]
    linear_combination powSeries ℓ (-(μ : ℂ)⁻¹) P * Units.inv_mul Fu - (↑Fu⁻¹ : ℂ⟦X⟧) * hmul
  rw [hMU, coeff_C_mul,
    PowerSeries.coeff_subst_mul_derivative_of_X_mul_subst_eq_X hU0
      (hHU : (X * (Fu : ℂ⟦X⟧)).subst U = X),
    hFu_inv, powSeries_pow hP0, mul_assoc, ← powSeries_add hP0,
    (by push_cast; field_simp [hμc]; ring :
      (1 - lam) / (μ : ℂ) + ((s + 1 : ℕ) : ℂ) * -(μ : ℂ)⁻¹ = -(lam + (s : ℂ)) / (μ : ℂ)),
    laplaceCoeff_def, powSeries]

/-! ### Local inversion expansion (DLMF 2.3.16) -/

/-- **DLMF 2.3.16 (Local inversion expansion).** Let `p : ℝ → ℝ` and `q : ℝ → ℂ` have asymptotic
expansions `p(t) - p(a) ~ ∑ pₛ (t - a)^{s + μ}` (`μ > 0`, `p₀ > 0`),
`p'(t) ~ ∑ (s + μ) pₛ (t - a)^{s + μ - 1}`, and `q(t) ~ ∑ qₛ (t - a)^{s + λ - 1}` as `t → a+`.
For any right inverse `T` of `p` near `p a` satisfying `T(p(a) + v) → a+` and
`p(T(p(a) + v)) = p(a) + v` as `v → 0+`, the transformed integrand admits the asymptotic expansion

`q(T(p(a) + v)) / p'(T(p(a) + v)) ~ ∑ bₛ v^{(s + λ - μ)/μ}` as `v → 0+`,

where `bₛ = laplaceCoeff μ λ (log p₀) P Q s`. -/
theorem isBigO_div_deriv_comp_sub_sum_laplaceCoeff {a μ : ℝ} (hμ : 0 < μ) {lam : ℂ}
    {p T : ℝ → ℝ} {q : ℝ → ℂ} {ps : ℕ → ℝ} (hp0 : 0 < ps 0) {qs : ℕ → ℂ}
    (hp : ∀ N : ℕ,
      (fun t : ℝ ↦ p t - p a - ∑ s ∈ range N, ps s * (t - a) ^ ((s : ℝ) + μ)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((N : ℝ) + μ))
    (hp' : ∀ N : ℕ,
      (fun t : ℝ ↦ deriv p t -
        ∑ s ∈ range N, ((s : ℝ) + μ) * ps s * (t - a) ^ ((s : ℝ) + μ - 1)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((N : ℝ) + μ - 1))
    (hq : ∀ N : ℕ,
      (fun t : ℝ ↦ q t - ∑ s ∈ range N, qs s * ((t - a : ℝ) : ℂ) ^ ((s : ℂ) + lam - 1))
        =O[𝓝[>] a] fun t ↦ (t - a) ^ ((N : ℝ) + lam.re - 1))
    (hT_tend : Tendsto (fun v ↦ T (p a + v)) (𝓝[>] 0) (𝓝[>] a))
    (hT_inv : ∀ᶠ v in 𝓝[>] 0, p (T (p a + v)) = p a + v) (N : ℕ) :
    (fun v : ℝ ↦ q (T (p a + v)) / ((deriv p (T (p a + v)) : ℝ) : ℂ) -
      ∑ s ∈ range N,
        laplaceCoeff μ lam (Real.log (ps 0)) (PowerSeries.mk fun n ↦ (ps n : ℂ))
          (PowerSeries.mk qs) s * (v : ℂ) ^ (((s : ℂ) + lam - μ) / μ)) =O[𝓝[>] 0]
      fun v ↦ v ^ (((N : ℝ) + lam.re - μ) / μ) := by
  set P : ℂ⟦X⟧ := PowerSeries.mk fun n ↦ (ps n : ℂ)
  set Q : ℂ⟦X⟧ := PowerSeries.mk qs
  set ℓ : ℂ := (Real.log (ps 0) : ℂ)
  have hP0 : constantCoeff P = (ps 0 : ℂ) := by simp [P, ← coeff_zero_eq_constantCoeff_apply]
  have hP0_exp : constantCoeff P = cexp ℓ := by rw [hP0, ← ofReal_exp, Real.exp_log hp0]
  have hμc : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  set z : ℝ → ℂ := fun t ↦ ((t - a : ℝ) : ℂ)
  have hz_tend : Tendsto z (𝓝[>] a) (𝓝 0) :=
    (continuous_ofReal.tendsto 0).comp (tendsto_sub_nhdsGT a)
  set fP : ℝ → ℝ := fun t ↦ (p t - p a) / (t - a) ^ μ
  set fR : ℝ → ℝ := fun t ↦ deriv p t / (t - a) ^ (μ - 1)
  set fQ : ℝ → ℂ := fun t ↦ q t / ((t - a : ℝ) : ℂ) ^ (lam - 1)
  set R : ℂ⟦X⟧ := C (μ : ℂ) * P + X * d⁄dX P
  have hfP : HasPowExp (𝓝[>] a) z P (fun t ↦ (fP t : ℂ)) := hasPowExp_ofReal_div_rpow (α := μ) hp
  have hR_mk : R = PowerSeries.mk fun s ↦ ((((s : ℝ) + μ) * ps s : ℝ) : ℂ) := by
    ext s; cases s with
    | zero => simp [R, P, coeff_zero_eq_constantCoeff]
    | succ s =>
      simp only [R, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_derivative, P, coeff_mk,
        ofReal_mul, ofReal_add, ofReal_natCast, Nat.cast_add, Nat.cast_one]; ring
  have hfR : HasPowExp (𝓝[>] a) z R (fun t ↦ (fR t : ℂ)) :=
    hR_mk ▸ hasPowExp_ofReal_div_rpow (α := μ - 1) fun M ↦ by simpa only [add_sub_assoc] using hp' M
  have hfQ : HasPowExp (𝓝[>] a) z Q fQ :=
    hasPowExp_div_cpow (α := lam - 1) fun M ↦ by
      simpa only [add_sub_assoc, sub_re, one_re] using hq M
  set F : ℂ⟦X⟧ := powSeries ℓ (μ : ℂ)⁻¹ P
  set H : ℂ⟦X⟧ := X * F
  have hH0 : constantCoeff H = 0 := by simp [H]
  have hH1 : IsUnit (coeff 1 H) := by
    simp [H, F, coeff_succ_X_mul 0, coeff_zero_eq_constantCoeff, constantCoeff_powSeries hP0_exp]
  set U : ℂ⟦X⟧ := H.substInvOfIsUnit hH1
  have hfP_pos := hasPowExp_eventually_pos hz_tend hp0 hP0 hfP
  set h_fn : ℝ → ℂ := fun t ↦ (((p t - p a) ^ μ⁻¹ : ℝ) : ℂ)
  have hh_exp : HasPowExp (𝓝[>] a) z H h_fn := by
    refine hasPowExp_congr ((eventually_mem_nhdsWithin.and hfP_pos).mono fun t ⟨ht, hpos⟩ ↦ ?_)
      (hasPowExp_mul hz_tend (hasPowExp_X hz_tend)
        (hasPowExp_cpow_of_pos hz_tend hp0 hP0 hfP (μ : ℂ)⁻¹))
    have hta : 0 < t - a := sub_pos.mpr ht
    have h1 : ((p t - p a) ^ μ⁻¹ : ℝ) = (t - a) * (fP t) ^ μ⁻¹ := by
      rw [(by dsimp only [fP]; field_simp [(Real.rpow_pos_of_pos hta μ).ne'] :
            p t - p a = (t - a) ^ μ * fP t),
        Real.mul_rpow (Real.rpow_pos_of_pos hta μ).le hpos.le,
        ← Real.rpow_mul hta.le, mul_inv_cancel₀ hμ.ne', Real.rpow_one]
    simp only [h_fn, h1, ofReal_mul, z, ofReal_cpow hpos.le, ofReal_inv]
  set w : ℝ → ℂ := fun v ↦ ((v ^ μ⁻¹ : ℝ) : ℂ)
  set u : ℝ → ℂ := fun v ↦ z (T (p a + v))
  have hw_tend : Tendsto w (𝓝[>] 0) (𝓝 0) :=
    (continuous_ofReal.tendsto 0).comp <| by
      simpa [Real.zero_rpow (inv_pos.mpr hμ).ne'] using
        (Real.continuousAt_rpow_const (0 : ℝ) μ⁻¹ (Or.inr (inv_pos.mpr hμ).le)).tendsto.mono_left
          nhdsWithin_le_nhds
  have hu_exp : HasPowExp (𝓝[>] 0) w U u :=
    hasPowExp_substInv (hz_tend.comp hT_tend) hH0 hH1 (hasPowExp_comp_tendsto hT_tend hh_exp)
      (hT_inv.mono fun v hv ↦ by simp [h_fn, w, hv])
  set R_den : ℂ⟦X⟧ := R * powSeries ℓ ((lam - μ) / μ) P
  set M : ℂ⟦X⟧ := Q * R_den⁻¹
  set fM : ℝ → ℂ := fun t ↦ fQ t * ((fR t : ℂ) * ((fP t : ℝ) : ℂ) ^ ((lam - μ) / μ))⁻¹
  have hR_den0 : constantCoeff R_den ≠ 0 := by
    rw [map_mul, (by simp [R, P] : constantCoeff R = (μ : ℂ) * (ps 0 : ℂ)),
      constantCoeff_powSeries hP0_exp]
    exact mul_ne_zero (mul_ne_zero hμc (ofReal_ne_zero.mpr hp0.ne')) (exp_ne_zero _)
  have hfM_w : HasPowExp (𝓝[>] 0) w (M.subst U) (fun v ↦ fM (T (p a + v))) :=
    hasPowExp_subst hw_tend (PowerSeries.constantCoeff_substInvOfIsUnit H hH1) hu_exp
      (hasPowExp_comp_tendsto hT_tend <| hasPowExp_mul hz_tend hfQ
        (hasPowExp_inv hz_tend hR_den0 (hasPowExp_mul hz_tend hfR
          (hasPowExp_cpow_of_pos hz_tend hp0 hP0 hfP ((lam - μ) / μ)))))
  refine ((hfM_w N).mul
      (isBigO_refl (fun v : ℝ ↦ (v : ℂ) ^ ((lam - μ) / μ)) (𝓝[>] 0)).norm_right).congr'
    ((eventually_mem_nhdsWithin.and (hT_inv.and
      ((hT_tend.eventually eventually_mem_nhdsWithin).and (hT_tend.eventually hfP_pos)))).mono
      fun v ⟨hv, hinv, hgt, hpos⟩ ↦ ?_)
    (eventually_mem_nhdsWithin.mono fun v hv ↦ ?_)
  · dsimp only
    have hta : 0 < T (p a + v) - a := sub_pos.mpr hgt
    have htac : ((T (p a + v) - a : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hta.ne'
    have hvc : (v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hv.ne'
    have hv_cpow : (v : ℂ) ^ ((lam - μ) / μ) =
        ((T (p a + v) - a : ℝ) : ℂ) ^ (lam - μ) *
          ((fP (T (p a + v)) : ℝ) : ℂ) ^ ((lam - μ) / μ) := by
      have hv_eq : v = (T (p a + v) - a) ^ μ * fP (T (p a + v)) := by
        dsimp only [fP]; field_simp [(Real.rpow_pos_of_pos hta μ).ne']; linarith [hinv]
      conv_lhs => rw [hv_eq]
      rw [ofReal_mul, mul_cpow_ofReal_nonneg (Real.rpow_pos_of_pos hta μ).le hpos.le,
        ← cpow_mul_ofReal_nonneg hta.le, mul_div_cancel₀ _ hμc]
    have hmain : fM (T (p a + v)) * (v : ℂ) ^ ((lam - μ) / μ) =
        q (T (p a + v)) / ((deriv p (T (p a + v)) : ℝ) : ℂ) := by
      simp only [fM, fQ, fR, hv_cpow, ofReal_div, ofReal_cpow hta.le, ofReal_sub μ 1, ofReal_one]
      by_cases hder : ((deriv p (T (p a + v)) : ℝ) : ℂ) = 0
      · simp [hder]
      · rw [(by rw [← cpow_add _ _ htac]; congr 1; ring :
          ((T (p a + v) - a : ℝ) : ℂ) ^ (lam - 1) =
            ((T (p a + v) - a : ℝ) : ℂ) ^ ((μ : ℂ) - 1) *
              ((T (p a + v) - a : ℝ) : ℂ) ^ (lam - μ))]
        have hc : ∀ w : ℂ, ((T (p a + v) - a : ℝ) : ℂ) ^ w ≠ 0 :=
          fun _ ↦ cpow_ne_zero_iff.mpr (Or.inl htac)
        field_simp [hder, hc ((μ : ℂ) - 1), hc (lam - μ),
          cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hpos.ne'))]
        rw [mul_assoc, mul_div_cancel_right₀ _ (mul_ne_zero (hc _) (hc _))]
    rw [sub_mul, hmain, Finset.sum_mul]
    congr 1; refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [coeff_subst_laplace_aux hμ.ne' hP0_exp s, mul_assoc]
    congr 1; simp only [w]
    rw [← cpow_natCast ((v ^ μ⁻¹ : ℝ) : ℂ) s, ← cpow_mul_ofReal_nonneg hv.le, ← cpow_add _ _ hvc]
    congr 1; push_cast; field_simp [hμc]; ring
  · dsimp only
    rw [(by simp only [w, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos hv μ⁻¹), ← Real.rpow_natCast, ← Real.rpow_mul hv.le,
          div_eq_inv_mul] : ‖w v‖ ^ N = v ^ ((N : ℝ) / μ)),
      norm_cpow_eq_rpow_re_of_pos hv, div_ofReal_re, sub_re, ofReal_re,
      ← Real.rpow_add hv, ← add_div, add_sub_assoc]

/-- **Existence of the local inverse and DLMF 2.3.16.** Under the local asymptotic hypotheses of
Laplace's method, there exist `ε > 0` and a local inverse `T` of `p` on `[a, a + ε]` such that `p`
is continuous and strictly increasing on `[a, a + ε]` with `p'(t) > 0` on `(a, a + ε]`,
`p '' Ioo a (a + ε) = Ioo (p a) (p (a + ε))`, `T` inverts `p` between `[a, a + ε]` and
`[p a, p (a + ε)]`, and `q(T(p(a) + v)) / p'(T(p(a) + v))` satisfies DLMF 2.3.16 as `v → 0+`. -/
theorem exists_localInverse_laplace_expansion {a μ : ℝ} (hμ : 0 < μ) {lam : ℂ}
    {p : ℝ → ℝ} {q : ℝ → ℂ} {ps : ℕ → ℝ} (hp0 : 0 < ps 0) {qs : ℕ → ℂ}
    (hp : ∀ N : ℕ,
      (fun t : ℝ ↦ p t - p a - ∑ s ∈ range N, ps s * (t - a) ^ ((s : ℝ) + μ)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((N : ℝ) + μ))
    (hp' : ∀ N : ℕ,
      (fun t : ℝ ↦ deriv p t -
        ∑ s ∈ range N, ((s : ℝ) + μ) * ps s * (t - a) ^ ((s : ℝ) + μ - 1)) =O[𝓝[>] a]
        fun t ↦ (t - a) ^ ((N : ℝ) + μ - 1))
    (hq : ∀ N : ℕ,
      (fun t : ℝ ↦ q t - ∑ s ∈ range N, qs s * ((t - a : ℝ) : ℂ) ^ ((s : ℂ) + lam - 1))
        =O[𝓝[>] a] fun t ↦ (t - a) ^ ((N : ℝ) + lam.re - 1)) :
    ∃ (ε : ℝ) (_ : 0 < ε) (T : ℝ → ℝ),
      ContinuousOn p (Icc a (a + ε)) ∧
      StrictMonoOn p (Icc a (a + ε)) ∧
      (∀ t ∈ Ioc a (a + ε), 0 < deriv p t) ∧
      p '' Ioo a (a + ε) = Ioo (p a) (p (a + ε)) ∧
      LeftInvOn T p (Icc a (a + ε)) ∧
      RightInvOn T p (Icc (p a) (p (a + ε))) ∧
      ∀ N : ℕ,
        (fun v : ℝ ↦ q (T (p a + v)) / ((deriv p (T (p a + v)) : ℝ) : ℂ) -
          ∑ s ∈ range N,
            laplaceCoeff μ lam (Real.log (ps 0)) (PowerSeries.mk fun n ↦ (ps n : ℂ))
              (PowerSeries.mk qs) s * (v : ℂ) ^ (((s : ℂ) + lam - μ) / μ)) =O[𝓝[>] 0]
          fun v ↦ v ^ (((N : ℝ) + lam.re - μ) / μ) := by
  have hderiv_pos : ∀ᶠ t in 𝓝[>] a, 0 < deriv p t := by
    have hR := hasPowExp_ofReal_div_rpow (α := μ - 1)
      fun M ↦ by simpa only [add_sub_assoc] using hp' M
    have hq_pos := hasPowExp_eventually_pos
      ((continuous_ofReal.tendsto 0).comp (tendsto_sub_nhdsGT a)) (mul_pos hμ hp0)
      (by simp [← coeff_zero_eq_constantCoeff_apply]) hR
    filter_upwards [eventually_mem_nhdsWithin, hq_pos] with t ht hqpos
    exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos (sub_pos.mpr ht) _)).mp hqpos
  obtain ⟨r, hr, hderiv_r⟩ := Metric.mem_nhdsWithin_iff.mp hderiv_pos
  set ε : ℝ := r / 2
  have hε : 0 < ε := half_pos hr
  have hεr : ε < r := half_lt_self hr
  have hder_Ioc : ∀ t ∈ Ioc a (a + ε), 0 < deriv p t := fun t ⟨hta, hte⟩ ↦
    hderiv_r ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hta)]; linarith, hta⟩
  have hp_tend_a : Tendsto p (𝓝[>] a) (𝓝 (p a)) := by
    have hrpow : Tendsto (fun t : ℝ ↦ (t - a) ^ μ) (𝓝[>] a) (𝓝 0) := by
      simpa [Function.comp_def, Real.zero_rpow hμ.ne'] using
        (Real.continuousAt_rpow_const (0 : ℝ) μ (Or.inr hμ.le)).tendsto.comp (tendsto_sub_nhdsGT a)
    simpa using ((by simpa using hp 0 :
      (fun t : ℝ ↦ p t - p a) =O[𝓝[>] a] fun t ↦ (t - a) ^ μ).trans_tendsto hrpow).add_const (p a)
  have hp_cont : ContinuousOn p (Icc a (a + ε)) := fun t ⟨hat, hte⟩ ↦ by
    rcases eq_or_lt_of_le hat with rfl | hlt
    · refine ContinuousWithinAt.mono ?_ Icc_subset_Ici_self
      rw [ContinuousWithinAt, (by ext x; simp [le_iff_eq_or_lt] : Ici a = {a} ∪ Ioi a),
        nhdsWithin_union, nhdsWithin_singleton, tendsto_sup]
      exact ⟨tendsto_pure_nhds p a, hp_tend_a⟩
    · exact (not_imp_comm.mp (deriv_zero_of_not_differentiableAt (f := p) (x := t))
        (hder_Ioc t ⟨hlt, hte⟩).ne').continuousAt.continuousWithinAt
  have hp_strict : StrictMonoOn p (Icc a (a + ε)) :=
    strictMonoOn_of_deriv_pos (convex_Icc a (a + ε)) hp_cont fun t ht ↦ by
      rw [interior_Icc] at ht; exact hder_Ioc t ⟨ht.1, ht.2.le⟩
  have himg_Icc : p '' Icc a (a + ε) = Icc (p a) (p (a + ε)) :=
    Subset.antisymm (fun _ ⟨_, ht, hEq⟩ ↦ hEq ▸
      ⟨hp_strict.monotoneOn (left_mem_Icc.mpr (by linarith)) ht ht.1,
        hp_strict.monotoneOn ht (right_mem_Icc.mpr (by linarith)) ht.2⟩)
      (intermediate_value_Icc (by linarith) hp_cont)
  have himg_Ioo : p '' Ioo a (a + ε) = Ioo (p a) (p (a + ε)) := by
    refine Subset.antisymm (fun _ ⟨_, ⟨hta, hte⟩, hEq⟩ ↦ hEq ▸
      ⟨hp_strict (left_mem_Icc.mpr (by linarith)) ⟨hta.le, hte.le⟩ hta,
        hp_strict ⟨hta.le, hte.le⟩ (right_mem_Icc.mpr (by linarith)) hte⟩) fun y ⟨hy1, hy2⟩ ↦ ?_
    obtain ⟨t, ht, rfl⟩ := himg_Icc.symm.subset ⟨hy1.le, hy2.le⟩
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 fun h ↦ by subst h; exact hy1.ne' rfl,
      lt_of_le_of_ne ht.2 fun h ↦ by subst h; exact hy2.ne rfl⟩, rfl⟩
  set T : ℝ → ℝ := Function.invFunOn p (Icc a (a + ε))
  have hT_right : RightInvOn T p (Icc (p a) (p (a + ε))) := fun _ hy ↦
    Function.invFunOn_eq (himg_Icc.symm.subset hy)
  have hT_maps : MapsTo T (Icc (p a) (p (a + ε))) (Icc a (a + ε)) := fun _ hy ↦
    Function.invFunOn_mem (himg_Icc.symm.subset hy)
  have hδ : 0 < p (a + ε) - p a := sub_pos.mpr
    (hp_strict (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith)) (by linarith))
  have hT_tend : Tendsto (fun v ↦ T (p a + v)) (𝓝[>] 0) (𝓝[>] a) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Metric.tendsto_nhds.mpr fun r' hr' ↦ ?_,
      Filter.eventually_of_mem (Ioo_mem_nhdsGT hδ) fun v ⟨hv0, hvδ⟩ ↦ by
        have hmem : p a + v ∈ Icc (p a) (p (a + ε)) := ⟨by linarith, by linarith⟩
        exact lt_of_le_of_ne (hT_maps hmem).1 fun heq ↦ by
          have := hT_right hmem; rw [← heq] at this; linarith⟩
    set t₀ : ℝ := min (a + ε) (a + r' / 2)
    have ht₀_mem : t₀ ∈ Icc a (a + ε) := ⟨(lt_min (by linarith) (by linarith)).le, min_le_left _ _⟩
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr
      (hp_strict (left_mem_Icc.mpr (by linarith)) ht₀_mem (lt_min (by linarith) (by linarith))))]
      with v ⟨hv0, hvδ'⟩
    have hmem : p a + v ∈ Icc (p a) (p (a + ε)) := ⟨by linarith, by
      linarith [hp_strict.monotoneOn ht₀_mem (right_mem_Icc.mpr (by linarith)) (min_le_left _ _)]⟩
    have hlt : T (p a + v) < t₀ := by
      by_contra hge
      linarith [hp_strict.monotoneOn ht₀_mem (hT_maps hmem) (not_lt.mp hge), hT_right hmem]
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hT_maps hmem).1)]
    linarith [min_le_right (a + ε) (a + r' / 2)]
  exact ⟨ε, hε, T, hp_cont, hp_strict, hder_Ioc, himg_Ioo, hp_strict.injOn.leftInvOn_invFunOn,
    hT_right, fun N ↦ isBigO_div_deriv_comp_sub_sum_laplaceCoeff hμ hp0 hp hp' hq hT_tend
      (Filter.eventually_of_mem (Ioo_mem_nhdsGT hδ) fun _ ⟨hv0, hvδ⟩ ↦
        hT_right ⟨by linarith, by linarith⟩) N⟩

end Asymptotics
