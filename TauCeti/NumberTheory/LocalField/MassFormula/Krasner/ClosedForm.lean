/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Count
public import TauCeti.NumberTheory.LocalField.Padic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Closed-form Krasner counts in mixed and equal characteristic

This file evaluates the exponent sum `∑_{h=1}^{n-1} oreCoefficientDepth K n j h` in Krasner's
discriminant-refined count (`TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq`) in both
characteristics, yielding closed-form formulas with no residual depth sum:

* **Mixed characteristic** (`CharZero K`): writing `p = ringChar 𝓀[K]`, `q = Nat.card 𝓀[K]`,
  `e = natCastValuation K p` (the absolute ramification index of `K`), `a = j / n`, and `b = j % n`,
  for every Ore-admissible `(n, j)`:
  * if `b = 0`, then `#σ_K(n, j) = n · q ^ (e · ∑_{i=1}^{v_p(n)} ⌊n / p^i⌋)`;
  * if `0 < b`, then `#σ_K(n, j) = n · (q - 1) · q ^ E`, where
    `E = e · ∑_{i=1}^{⌊a/e⌋} ⌊n / p^i⌋ + (a % e) · ⌊n / p^{⌊a/e⌋+1}⌋ + ⌊b / p^{⌊a/e⌋+1}⌋`.
  When `e = 1` (in particular for `K = ℚ_[p]`, where `q = p`), this specializes to Pauli–Roblot
  Theorem 6.1: `n · p ^ (∑_{i=1}^a ⌊n / p^i⌋)` for `b = 0` and
  `n · (p - 1) · p ^ (∑_{i=1}^a ⌊n / p^i⌋ + ⌊b / p^{a+1}⌋)` for `0 < b`.
* **Equal characteristic** (`ringChar K = p ≠ 0`, `p ∣ n`, `0 < n`, `¬ p ∣ j`):
  `#σ_K(n, j) = n · (q - 1) · q ^ ⌊j / p⌋`.

Finally, we record concrete evaluations over `ℚ_[p]`: the quadratic wild-exponent strata over
`ℚ_[2]` (`j = 1 → 2`, `j = 2 → 4`), the cubic strata (`6, 6, 9`) and total `#σ_{ℚ_3}(3) = 21` over
`ℚ_[3]`, the non-admissible quartic vanishing (`j = 2, 4 → 0`) and total `#σ_{ℚ_2}(4) = 92` over
`ℚ_[2]`.

## Main results

* `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_of_charZero`: general closed form in
  mixed characteristic (arbitrary absolute ramification index `e`).
* `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_of_ringChar_ne_zero`: closed form in
  equal characteristic `p` when `p ∣ n`.
* `TauCeti.Padic.isOreAdmissible_iff` and
  `TauCeti.Padic.ncard_totallyRamifiedOfDegree_wildExponent_eq`: Ore's conditions and
  Pauli–Roblot Theorem 6.1 over `ℚ_[p]`.
* `TauCeti.ncard_totallyRamifiedOfDegree_three_padicThree` (`#σ_{ℚ_3}(3) = 21`) and
  `TauCeti.ncard_totallyRamifiedOfDegree_four_padicTwo` (`#σ_{ℚ_2}(4) = 92`).

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `𝔭`-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, Colloq. Internat. CNRS **143** (1966), 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Proposition 3.1 and Theorem 6.1.
-/

public section
noncomputable section

open ValuativeRel IsDiscreteValuationRing

namespace TauCeti

/-! ### Elementary arithmetic identities for the depth sum -/

private theorem sum_ite_dvd_Ico (M d : ℕ) :
    (∑ h ∈ Finset.Ico 1 M, if d ∣ h then 1 else 0) = (M - 1) / d := by
  have hIco : Finset.Ico 1 M = Finset.Ioc 0 (M - 1) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega
  rw [Finset.sum_boole, Nat.cast_id, hIco, Nat.Ioc_filter_dvd_card_eq_div]

private theorem pred_div_add_one_of_dvd {n d : ℕ} (hn : 0 < n) (hdvd : d ∣ n) :
    (n - 1) / d + 1 = n / d := by
  have h := Nat.succ_div_of_dvd (a := n - 1) (b := d) (by rw [Nat.sub_add_cancel hn]; exact hdvd)
  rw [Nat.sub_add_cancel hn] at h
  exact h.symm

private theorem pred_div_eq_div_of_not_dvd {b d : ℕ} (hb : 0 < b) (hnd : ¬ d ∣ b) :
    (b - 1) / d = b / d := by
  have h := Nat.succ_div_of_not_dvd (a := b - 1) (by rwa [Nat.sub_add_cancel hb])
  rw [Nat.sub_add_cancel hb] at h
  exact h.symm

private theorem min_mul_eq {e v k : ℕ} (he : 0 < e) :
    min (e * v) k =
      e * (∑ i ∈ Finset.Icc 1 (k / e), if i ≤ v then 1 else 0) +
        (k % e) * (if k / e + 1 ≤ v then 1 else 0) := by
  have hfilt : (Finset.Icc 1 (k / e)).filter (· ≤ v) = Finset.Icc 1 (min (k / e) v) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
    tauto
  rw [Finset.sum_boole, Nat.cast_id, hfilt, Nat.card_Icc, Nat.add_sub_cancel]
  have hdiv : e * (k / e) + k % e = k := Nat.div_add_mod k e
  have hmod : k % e < e := Nat.mod_lt k he
  rcases le_or_gt (k / e + 1) v with hv | hv
  · rw [ite_eq_left hv, mul_one, min_eq_left (by omega : k / e ≤ v)]
    have hge : k ≤ e * v := by
      have : e * (k / e + 1) ≤ e * v := Nat.mul_le_mul_left e hv
      rw [mul_add, mul_one] at this
      omega
    rw [min_eq_right hge]
    omega
  · rw [ite_eq_right (by omega : ¬ k / e + 1 ≤ v), mul_zero, add_zero,
      min_eq_right (by omega : v ≤ k / e)]
    have hle : e * v ≤ k := by
      have : e * v ≤ e * (k / e) := Nat.mul_le_mul_left e (by omega)
      omega
    rw [min_eq_left hle]

private theorem le_mul_iff_div_add_one_le {e v a : ℕ} (he : 0 < e) :
    a + 1 ≤ e * v ↔ a / e + 1 ≤ v := by
  rw [Nat.add_one_le_iff, Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul he, mul_comm]

section GeneralBridge

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

private theorem sum_targetDepth_eq {n : ℕ} (hn : 0 < n) (j : ℕ) :
    (∑ h ∈ Finset.Ico 1 n, (j / n + 1 + if h < j % n then 1 else 0)) =
      (n - 1) * (j / n + 1) + (j % n - 1) := by
  have hfilt : (Finset.Ico 1 n).filter (· < j % n) = Finset.Ico 1 (j % n) := by
    ext h
    have hlt : j % n < n := Nat.mod_lt j hn
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul,
    Finset.sum_boole, Nat.cast_id, hfilt, Nat.card_Ico]

private theorem exponent_eq_add_sum_sub_of_mod_eq_zero {n j : ℕ} (hn : 0 < n) (hb : j % n = 0) :
    n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h =
      j / n + ∑ h ∈ Finset.Ico 1 n,
        (j / n + 1 + (if h < j % n then 1 else 0) - oreCoefficientDepth K n j h) := by
  set a := j / n
  set S := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  set D := ∑ h ∈ Finset.Ico 1 n,
    (a + 1 + (if h < j % n then 1 else 0) - oreCoefficientDepth K n j h)
  have hsum_sub : D + S = (n - 1) * (a + 1) := by
    have h1 : D + S = ∑ h ∈ Finset.Ico 1 n, (a + 1 + if h < j % n then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun h _ ↦ Nat.sub_add_cancel (oreCoefficientDepth_le n j h)
    rw [h1, sum_targetDepth_eq hn j, hb, Nat.zero_sub, add_zero]
  have hmul : (n - 1) * (a + 1) + (a + 1) = n + j := by
    calc (n - 1) * (a + 1) + (a + 1)
        = (n - 1 + 1) * (a + 1) := by ring
      _ = n * (a + 1) := by rw [Nat.sub_add_cancel hn]
      _ = n + (n * a + j % n) := by rw [hb]; ring
      _ = n + j := by rw [Nat.div_add_mod]
  have htot : (a + D) + S + 1 = n + j := by linarith [hsum_sub, hmul]
  exact Nat.sub_eq_of_eq_add (Nat.sub_eq_of_eq_add htot.symm)

private theorem exponent_eq_add_sum_sub_of_mod_pos {n j : ℕ} (hn : 0 < n) (hb : 0 < j % n) :
    n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h =
      j / n + ∑ h ∈ Finset.Ico 1 n,
        (j / n + 1 + (if h < j % n then 1 else 0) - oreCoefficientDepth K n j h) := by
  set a := j / n
  set b := j % n
  set S := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  set D := ∑ h ∈ Finset.Ico 1 n,
    (a + 1 + (if h < b then 1 else 0) - oreCoefficientDepth K n j h)
  have hsum_sub : D + S = (n - 1) * (a + 1) + (b - 1) := by
    have h1 : D + S = ∑ h ∈ Finset.Ico 1 n, (a + 1 + if h < b then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun h _ ↦ Nat.sub_add_cancel (oreCoefficientDepth_le n j h)
    rw [h1, sum_targetDepth_eq hn j]
  have hmul : (n - 1) * (a + 1) + (a + 1) + b = n + j := by
    calc (n - 1) * (a + 1) + (a + 1) + b
        = (n - 1 + 1) * (a + 1) + b := by ring
      _ = n * (a + 1) + b := by rw [Nat.sub_add_cancel hn]
      _ = n + (n * a + b) := by ring
      _ = n + j := by rw [Nat.div_add_mod]
  have htot : (a + D) + S + 2 = n + j := by linarith [hsum_sub, hmul, Nat.sub_add_cancel hb]
  exact Nat.sub_eq_of_eq_add (Nat.sub_eq_of_eq_add htot.symm)

end GeneralBridge

/-! ### Closed form in mixed characteristic -/

section MixedChar

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K]

private theorem pow_dvd_iff_le_padicValNat {p h i : ℕ} (hp : p.Prime) (hh : 0 < h) :
    p ^ i ∣ h ↔ i ≤ padicValNat p h := by
  rw [Nat.padicValNat_def]
  exact Nat.pow_dvd_iff_le_multiplicity hp.ne_one hh.ne'

private theorem add_sum_pred_div_eq_sum_div {p n m : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hle : m ≤ padicValNat p n) :
    m + ∑ i ∈ Finset.Icc 1 m, (n - 1) / p ^ i = ∑ i ∈ Finset.Icc 1 m, n / p ^ i := by
  have hcard : m = ∑ _i ∈ Finset.Icc 1 m, 1 := by simp [Nat.card_Icc]
  conv_lhs => arg 1; rw [hcard]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [add_comm]
  exact pred_div_add_one_of_dvd hn
    ((pow_dvd_iff_le_padicValNat hp hn).mpr (le_trans (Finset.mem_Icc.mp hi).2 hle))

private theorem sum_min_padicValNat_Ico {p e : ℕ} (hp : p.Prime) (he : 0 < e) (M k : ℕ) :
    (∑ h ∈ Finset.Ico 1 M, min (e * padicValNat p h) k) =
      e * (∑ i ∈ Finset.Icc 1 (k / e), (M - 1) / p ^ i) +
        (k % e) * ((M - 1) / p ^ (k / e + 1)) := by
  have hdvd (h i : ℕ) (hh : 0 < h) : i ≤ padicValNat p h ↔ p ^ i ∣ h :=
    (pow_dvd_iff_le_padicValNat hp hh).symm
  have h1 : (∑ h ∈ Finset.Ico 1 M, min (e * padicValNat p h) k) =
      ∑ h ∈ Finset.Ico 1 M,
        (e * (∑ i ∈ Finset.Icc 1 (k / e), if p ^ i ∣ h then 1 else 0) +
          (k % e) * (if p ^ (k / e + 1) ∣ h then 1 else 0)) := by
    refine Finset.sum_congr rfl fun h hh ↦ ?_
    have hh0 : 0 < h := (Finset.mem_Ico.mp hh).1
    rw [min_mul_eq he]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by simp [hdvd h i hh0]
    · simp [hdvd h (k / e + 1) hh0]
  rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm,
    sum_ite_dvd_Ico]
  congr 2
  exact Finset.sum_congr rfl fun i _ ↦ sum_ite_dvd_Ico M (p ^ i)

private theorem exponent_mixedChar_of_mod_eq_zero {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hb : j % n = 0) :
    let p := ringChar 𝓀[K]
    let e := natCastValuation K p (natCast_ringChar_residueField_ne_zero K)
    n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h =
      e * ∑ i ∈ Finset.Icc 1 (padicValNat p n), n / p ^ i := by
  intro p e
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] _
  have hpK : (p : K) ≠ 0 := natCast_ringChar_residueField_ne_zero K
  have he : 0 < e := Nat.pos_of_ne_zero
    ((natCastValuation_ne_zero_iff_ringChar_eq K hp hpK).mpr rfl)
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hadm.pos.ne'
  have ha_eq : j / n = padicValNat p n * e := by
    have h1 := (isOreAdmissible_iff_of_mod_eq_zero hadm.pos hb).mp hadm
    rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K n hnK,
      natCastValuation_eq_padicValNat_mul K hnK hpK] at h1
    exact_mod_cast h1
  rw [exponent_eq_add_sum_sub_of_mod_eq_zero hadm.pos hb]
  have hterm : ∑ h ∈ Finset.Ico 1 n,
        (j / n + 1 + (if h < j % n then 1 else 0) - oreCoefficientDepth K n j h) =
      ∑ h ∈ Finset.Ico 1 n, min (e * padicValNat p h) (j / n) := by
    refine Finset.sum_congr rfl fun h hh ↦ ?_
    have hh0 : 0 < h := (Finset.mem_Ico.mp hh).1
    have hhK : (h : K) ≠ 0 := Nat.cast_ne_zero.mpr hh0.ne'
    have hv : natCastValuation K h hhK = e * padicValNat p h := by
      rw [natCastValuation_eq_padicValNat_mul K hhK hpK, mul_comm]
    rw [oreCoefficientDepth_eq_of_natCast_ne_zero hhK, hv, hb]
    simp only [Nat.not_lt_zero, ↓reduceIte, add_zero]
    generalize j / n = a
    omega
  rw [hterm, sum_min_padicValNat_Ico hp he, ha_eq, Nat.mul_div_left _ he,
    Nat.mul_mod_left, zero_mul, add_zero, mul_comm (padicValNat p n) e, ← mul_add,
    add_sum_pred_div_eq_sum_div hp hadm.pos le_rfl]

private theorem sum_sub_oreCoefficientDepth_of_mod_pos {n j : ℕ} (hn : 0 < n) :
    let p := ringChar 𝓀[K]
    let e := natCastValuation K p (natCast_ringChar_residueField_ne_zero K)
    ∑ h ∈ Finset.Ico 1 n,
        (j / n + 1 + (if h < j % n then 1 else 0) - oreCoefficientDepth K n j h) =
      (∑ h ∈ Finset.Ico 1 n, min (e * padicValNat p h) (j / n)) +
        ∑ h ∈ Finset.Ico 1 (j % n), if p ^ (j / n / e + 1) ∣ h then 1 else 0 := by
  intro p e
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] _
  have hpK : (p : K) ≠ 0 := natCast_ringChar_residueField_ne_zero K
  have he : 0 < e := Nat.pos_of_ne_zero
    ((natCastValuation_ne_zero_iff_ringChar_eq K hp hpK).mpr rfl)
  have hsplit : ∑ h ∈ Finset.Ico 1 n,
        (j / n + 1 + (if h < j % n then 1 else 0) - oreCoefficientDepth K n j h) =
      ∑ h ∈ Finset.Ico 1 n,
        (min (e * padicValNat p h) (j / n) +
          if h < j % n then if p ^ (j / n / e + 1) ∣ h then 1 else 0 else 0) := by
    refine Finset.sum_congr rfl fun h hh ↦ ?_
    have hh0 : 0 < h := (Finset.mem_Ico.mp hh).1
    have hhK : (h : K) ≠ 0 := Nat.cast_ne_zero.mpr hh0.ne'
    have hv : natCastValuation K h hhK = e * padicValNat p h := by
      rw [natCastValuation_eq_padicValNat_mul K hhK hpK, mul_comm]
    rw [oreCoefficientDepth_eq_of_natCast_ne_zero hhK, hv]
    have hdvd : p ^ (j / n / e + 1) ∣ h ↔ j / n + 1 ≤ e * padicValNat p h := by
      rw [pow_dvd_iff_le_padicValNat hp hh0, le_mul_iff_div_add_one_le he]
    split_ifs with hlt hd
    · have := hdvd.mp hd; generalize j / n = a at *; omega
    · have : ¬ j / n + 1 ≤ e * padicValNat p h := mt hdvd.mpr hd
      generalize j / n = a at *; omega
    · generalize j / n = a; omega
  rw [hsplit, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_filter]
  have hfilt : (Finset.Ico 1 n).filter (· < j % n) = Finset.Ico 1 (j % n) := by
    ext h
    have hlt : j % n < n := Nat.mod_lt j hn
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hfilt]

private theorem exponent_mixedChar_of_mod_pos {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hb : 0 < j % n) :
    let p := ringChar 𝓀[K]
    let e := natCastValuation K p (natCast_ringChar_residueField_ne_zero K)
    n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h =
      e * (∑ i ∈ Finset.Icc 1 (j / n / e), n / p ^ i) +
        (j / n % e) * (n / p ^ (j / n / e + 1)) + (j % n) / p ^ (j / n / e + 1) := by
  intro p e
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] _
  have hpK : (p : K) ≠ 0 := natCast_ringChar_residueField_ne_zero K
  have he : 0 < e := Nat.pos_of_ne_zero
    ((natCastValuation_ne_zero_iff_ringChar_eq K hp hpK).mpr rfl)
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hadm.pos.ne'
  have hbK : ((j % n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  obtain ⟨hvb, hvn⟩ := (isOreAdmissible_iff_of_mod_pos hadm.pos hb).mp hadm
  rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K (j % n) hbK,
    natCastValuation_eq_padicValNat_mul K hbK hpK] at hvb
  rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K n hnK,
    natCastValuation_eq_padicValNat_mul K hnK hpK] at hvn
  have hvb' : e * padicValNat p (j % n) ≤ j / n := by
    rw [mul_comm]; exact_mod_cast hvb
  have hvn' : j / n + 1 ≤ e * padicValNat p n := by
    rw [mul_comm]; exact_mod_cast hvn
  have hle_vn : j / n / e + 1 ≤ padicValNat p n := (le_mul_iff_div_add_one_le he).mp hvn'
  have hndvd_b : ¬ p ^ (j / n / e + 1) ∣ j % n := by
    rw [pow_dvd_iff_le_padicValNat hp hb]
    exact fun hle ↦ by have := (le_mul_iff_div_add_one_le he).mpr hle; omega
  rw [exponent_eq_add_sum_sub_of_mod_pos hadm.pos hb,
    sum_sub_oreCoefficientDepth_of_mod_pos (K := K) hadm.pos,
    sum_min_padicValNat_Ico hp he, sum_ite_dvd_Ico,
    pred_div_eq_div_of_not_dvd hb hndvd_b]
  have hdiv_n : (n - 1) / p ^ (j / n / e + 1) + 1 = n / p ^ (j / n / e + 1) :=
    pred_div_add_one_of_dvd hadm.pos ((pow_dvd_iff_le_padicValNat hp hadm.pos).mpr hle_vn)
  have hsum_n := add_sum_pred_div_eq_sum_div hp hadm.pos (Nat.le_of_succ_le hle_vn)
  have hdiv_a : e * (j / n / e) + j / n % e = j / n := Nat.div_add_mod (j / n) e
  calc j / n + (e * ∑ i ∈ Finset.Icc 1 (j / n / e), (n - 1) / p ^ i +
          j / n % e * ((n - 1) / p ^ (j / n / e + 1)) + j % n / p ^ (j / n / e + 1))
      = e * (j / n / e + ∑ i ∈ Finset.Icc 1 (j / n / e), (n - 1) / p ^ i) +
          j / n % e * ((n - 1) / p ^ (j / n / e + 1) + 1) + j % n / p ^ (j / n / e + 1) := by
        conv_lhs => arg 1; rw [← hdiv_a]
        ring
    _ = e * (∑ i ∈ Finset.Icc 1 (j / n / e), n / p ^ i) +
          j / n % e * (n / p ^ (j / n / e + 1)) + j % n / p ^ (j / n / e + 1) := by
        rw [hsum_n, hdiv_n]

/-- **Closed form of Krasner's count in mixed characteristic**: for any characteristic-zero
nonarchimedean local field `K` with residue characteristic `p = ringChar 𝓀[K]`, residue cardinality
`q = Nat.card 𝓀[K]`, and absolute ramification index `e = natCastValuation K p`, and for any
Ore-admissible `(n, j)`:
* when `j % n = 0`, `#σ_K(n, j) = n · q ^ (e · ∑_{i=1}^{v_p(n)} ⌊n / p^i⌋)`;
* when `0 < j % n`, `#σ_K(n, j) = n · (q - 1) · q ^ E`, where
  `E = e · ∑_{i=1}^{⌊a/e⌋} ⌊n / p^i⌋ + (a % e) · ⌊n / p^{⌊a/e⌋+1}⌋ + ⌊b / p^{⌊a/e⌋+1}⌋`,
  `a = j / n`, and `b = j % n`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_of_charZero {n j : ℕ}
    (hadm : IsOreAdmissible K n j) :
    let p := ringChar 𝓀[K]
    let e := natCastValuation K p (natCast_ringChar_residueField_ne_zero K)
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard =
      if j % n = 0 then
        n * Nat.card 𝓀[K] ^ (e * ∑ i ∈ Finset.Icc 1 (padicValNat p n), n / p ^ i)
      else
        n * (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^
          (e * (∑ i ∈ Finset.Icc 1 (j / n / e), n / p ^ i) +
            (j / n % e) * (n / p ^ (j / n / e + 1)) + (j % n) / p ^ (j / n / e + 1)) := by
  intro p e
  rw [ncard_totallyRamifiedOfDegree_wildExponent_eq, ite_eq_left hadm]
  rcases (j % n).eq_zero_or_pos with hb0 | hbpos
  · rw [ite_eq_left hb0, ite_eq_left hb0, exponent_mixedChar_of_mod_eq_zero hadm hb0]
  · rw [ite_eq_right hbpos.ne', ite_eq_right hbpos.ne', exponent_mixedChar_of_mod_pos hadm hbpos]

end MixedChar

/-! ### Closed form in equal characteristic -/

section EqualChar

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem sum_sub_oreCoefficientDepth_of_ringChar_ne_zero {n j : ℕ}
    (hK : ringChar K ≠ 0) (hn : 0 < n) :
    ∑ h ∈ Finset.Ico 1 n,
        (j / n + 1 + (if h < j % n then 1 else 0) - oreCoefficientDepth K n j h) =
      (j / n) * ((n - 1) / ringChar K) + (j % n - 1) / ringChar K := by
  set p := ringChar K
  have h1 : ∑ h ∈ Finset.Ico 1 n,
        (j / n + 1 + (if h < j % n then 1 else 0) - oreCoefficientDepth K n j h) =
      ∑ h ∈ Finset.Ico 1 n,
        ((if p ∣ h then j / n else 0) +
          if h < j % n then if p ∣ h then 1 else 0 else 0) := by
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    by_cases hph : p ∣ h
    · have hh0 : (h : K) = 0 := (ringChar.spec K h).mpr hph
      rw [oreCoefficientDepth_eq_one_of_natCast_eq_zero hh0, ite_eq_left hph, ite_eq_left hph]
      generalize j / n = a
      split_ifs <;> omega
    · have hhK : (h : K) ≠ 0 := mt (ringChar.spec K h).mp hph
      rw [oreCoefficientDepth_eq_of_natCast_ne_zero hhK,
        natCastValuation_eq_zero_of_ringChar_ne_zero K hK h hhK,
        ite_eq_right hph, ite_eq_right hph]
      generalize j / n = a
      split_ifs <;> omega
  rw [h1, Finset.sum_add_distrib]
  congr 1
  · calc (∑ h ∈ Finset.Ico 1 n, if p ∣ h then j / n else 0)
        = ∑ h ∈ Finset.Ico 1 n, (j / n) * (if p ∣ h then 1 else 0) :=
          Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> simp
      _ = (j / n) * (∑ h ∈ Finset.Ico 1 n, if p ∣ h then 1 else 0) := (Finset.mul_sum ..).symm
      _ = (j / n) * ((n - 1) / p) := by rw [sum_ite_dvd_Ico]
  · rw [← Finset.sum_filter]
    have hfilt : (Finset.Ico 1 n).filter (· < j % n) = Finset.Ico 1 (j % n) := by
      ext h
      have hlt : j % n < n := Nat.mod_lt j hn
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [hfilt, sum_ite_dvd_Ico]

/-- **Closed form of Krasner's count in equal characteristic**: if `K` has positive characteristic
`p = ringChar K`, `0 < n` with `p ∣ n`, and `¬ p ∣ j` (the Ore-admissible condition), then
`#σ_K(n, j) = n · (q - 1) · q ^ ⌊j / p⌋`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_of_ringChar_ne_zero {n j : ℕ}
    (hK : ringChar K ≠ 0) (hn : 0 < n) (hpn : ringChar K ∣ n) (hnd : ¬ ringChar K ∣ j) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard =
      n * (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (j / ringChar K) := by
  set p := ringChar K
  have hp : p.Prime := CharP.char_prime_of_ne_zero K hK
  have hnK : (n : K) = 0 := (ringChar.spec K n).mpr hpn
  have hadm : IsOreAdmissible K n j :=
    (isOreAdmissible_iff_not_dvd_of_natCast_eq_zero hn hnK).mpr hnd
  have hndb : ¬ p ∣ j % n := by
    intro h
    apply hnd
    rw [← Nat.div_add_mod j n]
    exact dvd_add (dvd_mul_of_dvd_left hpn _) h
  have hbpos : 0 < j % n := Nat.pos_of_ne_zero fun h0 ↦ hndb (h0 ▸ dvd_zero _)
  rw [ncard_totallyRamifiedOfDegree_wildExponent_eq, ite_eq_left hadm, ite_eq_right hbpos.ne',
    exponent_eq_add_sum_sub_of_mod_pos hn hbpos,
    sum_sub_oreCoefficientDepth_of_ringChar_ne_zero (K := K) hK hn,
    pred_div_eq_div_of_not_dvd hbpos hndb]
  congr 2
  have hdiv_n : (n - 1) / p + 1 = n / p := pred_div_add_one_of_dvd hn hpn
  have hjdiv : j / n * (n / p) + j % n / p = j / p := by
    obtain ⟨m, rfl⟩ := hpn
    rw [Nat.mul_div_cancel_left m hp.pos]
    calc j / (p * m) * m + j % (p * m) / p
        = (p * (j / (p * m) * m) + j % (p * m)) / p := by rw [Nat.mul_add_div hp.pos]
      _ = (p * m * (j / (p * m)) + j % (p * m)) / p := by congr 1; ring
      _ = j / p := by rw [Nat.div_add_mod]
  calc j / n + (j / n * ((n - 1) / p) + j % n / p)
      = j / n * ((n - 1) / p + 1) + j % n / p := by ring
    _ = j / n * (n / p) + j % n / p := by rw [hdiv_n]
    _ = j / p := hjdiv

end EqualChar

/-! ### Specialization to `ℚ_[p]` and concrete evaluations -/

namespace Padic

variable (p : ℕ) [Fact p.Prime]

/-- **Ore's conditions over `ℚ_[p]`** ([Pauli–Roblot 2001, Proposition 3.1]): a degree `n` and wild
exponent `j` are Ore-admissible over `ℚ_[p]` if and only if `0 < n` and either
`j % n = 0 ∧ j / n = padicValNat p n`, or
`0 < j % n ∧ padicValNat p (j % n) ≤ j / n ∧ j / n + 1 ≤ padicValNat p n`. -/
theorem isOreAdmissible_iff {n j : ℕ} :
    IsOreAdmissible ℚ_[p] n j ↔
      0 < n ∧
        ((j % n = 0 ∧ j / n = padicValNat p n) ∨
          (0 < j % n ∧ padicValNat p (j % n) ≤ j / n ∧ j / n + 1 ≤ padicValNat p n)) := by
  rw [TauCeti.isOreAdmissible_iff]
  refine and_congr_right fun hn ↦ ?_
  have hnK : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [TauCeti.IsDiscreteValuationRing.addVal_natCast ℚ_[p] n hnK,
    _root_.Padic.natCastValuation_eq_padicValNat]
  refine or_congr ?_ ?_
  · exact and_congr_right fun _ ↦ by norm_cast
  · refine and_congr_right fun hb ↦ ?_
    have hbK : ((j % n : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    rw [TauCeti.IsDiscreteValuationRing.addVal_natCast ℚ_[p] (j % n) hbK,
      _root_.Padic.natCastValuation_eq_padicValNat]
    norm_cast

/-- **Pauli–Roblot Theorem 6.1** (Krasner's count over `ℚ_[p]`): for an Ore-admissible pair
`(n, j)` over `ℚ_[p]`, writing `a = j / n` and `b = j % n`,
* `#σ_{ℚ_p}(n, j) = n · p ^ (∑_{i=1}^a ⌊n / p^i⌋)` if `b = 0`, and
* `#σ_{ℚ_p}(n, j) = n · (p - 1) · p ^ (∑_{i=1}^a ⌊n / p^i⌋ + ⌊b / p^{a+1}⌋)` if `0 < b`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq {n j : ℕ}
    (hadm : IsOreAdmissible ℚ_[p] n j) :
    {E ∈ totallyRamifiedOfDegree ℚ_[p] n | E.wildExponent = j}.ncard =
      if j % n = 0 then
        n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)
      else
        n * (p - 1) *
          p ^ ((∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) + (j % n) / p ^ (j / n + 1)) := by
  have h := ncard_totallyRamifiedOfDegree_wildExponent_eq_of_charZero (K := ℚ_[p]) hadm
  have hchar : ringChar 𝓀[ℚ_[p]] = p := _root_.Padic.ringChar_residueField p
  have he : natCastValuation ℚ_[p] (ringChar 𝓀[ℚ_[p]])
      (natCast_ringChar_residueField_ne_zero ℚ_[p]) = 1 := by
    rw [_root_.Padic.natCastValuation_eq_padicValNat, hchar, Nat.padicValNat_def,
      Nat.multiplicity_self (Fact.out : p.Prime).one_lt]
  rw [h, _root_.Padic.natCard_residueField, he, hchar]
  rcases (j % n).eq_zero_or_pos with hb0 | hbpos
  · have ha : j / n = padicValNat p n := by
      rcases ((Padic.isOreAdmissible_iff p).mp hadm).2 with ⟨_, ha⟩ | ⟨hpos, _⟩
      · exact ha
      · omega
    simp [hb0, ha]
  · simp [hbpos.ne', Nat.mod_one]

end Padic

/-! ### Concrete stratum and total counts over `ℚ_[2]` and `ℚ_[3]` -/

/-- Over `ℚ_[2]`, there are `2` totally ramified quadratic subextensions of wild exponent `1`. -/
theorem ncard_totallyRamifiedOfDegree_two_wildExponent_one_padicTwo :
    {E ∈ totallyRamifiedOfDegree ℚ_[2] 2 | E.wildExponent = 1}.ncard = 2 := by
  have hadm : IsOreAdmissible ℚ_[2] 2 1 :=
    (Padic.isOreAdmissible_iff 2).mpr (by norm_num [Nat.padicValNat_def])
  rw [Padic.ncard_totallyRamifiedOfDegree_wildExponent_eq 2 hadm]
  norm_num

/-- Over `ℚ_[2]`, there are `4` totally ramified quadratic subextensions of wild exponent `2`. -/
theorem ncard_totallyRamifiedOfDegree_two_wildExponent_two_padicTwo :
    {E ∈ totallyRamifiedOfDegree ℚ_[2] 2 | E.wildExponent = 2}.ncard = 4 := by
  have hadm : IsOreAdmissible ℚ_[2] 2 2 :=
    (Padic.isOreAdmissible_iff 2).mpr (by norm_num [Nat.padicValNat_def])
  rw [Padic.ncard_totallyRamifiedOfDegree_wildExponent_eq 2 hadm]
  norm_num

/-- Over `ℚ_[3]`, there are `6` totally ramified cubic subextensions of wild exponent `1`. -/
theorem ncard_totallyRamifiedOfDegree_three_wildExponent_one_padicThree :
    {E ∈ totallyRamifiedOfDegree ℚ_[3] 3 | E.wildExponent = 1}.ncard = 6 := by
  have hadm : IsOreAdmissible ℚ_[3] 3 1 :=
    (Padic.isOreAdmissible_iff 3).mpr (by norm_num [Nat.padicValNat_def])
  rw [Padic.ncard_totallyRamifiedOfDegree_wildExponent_eq 3 hadm]
  norm_num

/-- Over `ℚ_[3]`, there are `6` totally ramified cubic subextensions of wild exponent `2`. -/
theorem ncard_totallyRamifiedOfDegree_three_wildExponent_two_padicThree :
    {E ∈ totallyRamifiedOfDegree ℚ_[3] 3 | E.wildExponent = 2}.ncard = 6 := by
  have h32 : multiplicity 3 2 = 0 := multiplicity_eq_zero_of_not_dvd (by decide)
  have hadm : IsOreAdmissible ℚ_[3] 3 2 :=
    (Padic.isOreAdmissible_iff 3).mpr (by norm_num [Nat.padicValNat_def, h32])
  rw [Padic.ncard_totallyRamifiedOfDegree_wildExponent_eq 3 hadm]
  norm_num

/-- Over `ℚ_[3]`, there are `9` totally ramified cubic subextensions of wild exponent `3`. -/
theorem ncard_totallyRamifiedOfDegree_three_wildExponent_three_padicThree :
    {E ∈ totallyRamifiedOfDegree ℚ_[3] 3 | E.wildExponent = 3}.ncard = 9 := by
  have hadm : IsOreAdmissible ℚ_[3] 3 3 :=
    (Padic.isOreAdmissible_iff 3).mpr (by norm_num [Nat.padicValNat_def])
  rw [Padic.ncard_totallyRamifiedOfDegree_wildExponent_eq 3 hadm]
  norm_num

/-- A separable closure of `ℚ_[3]` has exactly `21` totally ramified cubic subextensions
(`6 + 6 + 9 = 21`). -/
theorem ncard_totallyRamifiedOfDegree_three_padicThree :
    (totallyRamifiedOfDegree ℚ_[3] 3).ncard = 21 := by
  have h3 : ((3 : ℕ) : ℚ_[3]) ≠ 0 := by norm_num
  rw [ncard_totallyRamifiedOfDegree_eq_sum h3, _root_.Padic.natCastValuation_self]
  have h0 : {E ∈ totallyRamifiedOfDegree ℚ_[3] 3 | E.wildExponent = 0}.ncard = 0 := by
    rw [ncard_totallyRamifiedOfDegree_wildExponent_eq, ite_eq_right]
    rw [Padic.isOreAdmissible_iff]
    norm_num [Nat.padicValNat_def]
  have h4 : 3 * 1 + 1 = 4 := by norm_num
  rw [h4, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, h0,
    ncard_totallyRamifiedOfDegree_three_wildExponent_one_padicThree,
    ncard_totallyRamifiedOfDegree_three_wildExponent_two_padicThree,
    ncard_totallyRamifiedOfDegree_three_wildExponent_three_padicThree]

/-- Over `ℚ_[2]`, wild exponent `2` is not Ore-admissible for degree `4`, so the corresponding
quartic stratum is empty. -/
theorem ncard_totallyRamifiedOfDegree_four_wildExponent_two_padicTwo :
    {E ∈ totallyRamifiedOfDegree ℚ_[2] 4 | E.wildExponent = 2}.ncard = 0 := by
  rw [ncard_totallyRamifiedOfDegree_wildExponent_eq, ite_eq_right]
  rw [Padic.isOreAdmissible_iff]
  norm_num [Nat.padicValNat_def]

/-- Over `ℚ_[2]`, wild exponent `4` is not Ore-admissible for degree `4`, so the corresponding
quartic stratum is empty. -/
theorem ncard_totallyRamifiedOfDegree_four_wildExponent_four_padicTwo :
    {E ∈ totallyRamifiedOfDegree ℚ_[2] 4 | E.wildExponent = 4}.ncard = 0 := by
  have hv4 : multiplicity 2 4 = 2 := multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
  rw [ncard_totallyRamifiedOfDegree_wildExponent_eq, ite_eq_right]
  rw [Padic.isOreAdmissible_iff]
  norm_num [Nat.padicValNat_def, hv4]

private theorem ncard_quartic_padicTwo_of_adm {j : ℕ} (hadm : IsOreAdmissible ℚ_[2] 4 j) :
    {E ∈ totallyRamifiedOfDegree ℚ_[2] 4 | E.wildExponent = j}.ncard =
      if j % 4 = 0 then
        4 * 2 ^ (∑ i ∈ Finset.Icc 1 (j / 4), 4 / 2 ^ i)
      else
        4 * 2 ^ ((∑ i ∈ Finset.Icc 1 (j / 4), 4 / 2 ^ i) + (j % 4) / 2 ^ (j / 4 + 1)) := by
  simpa using Padic.ncard_totallyRamifiedOfDegree_wildExponent_eq 2 hadm

/-- A separable closure of `ℚ_[2]` has exactly `92` totally ramified quartic subextensions
(`4 + 8 + 16 + 16 + 16 + 32 = 92`). -/
theorem ncard_totallyRamifiedOfDegree_four_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 4).ncard = 92 := by
  have h4 : ((4 : ℕ) : ℚ_[2]) ≠ 0 := by norm_num
  have hv4 : multiplicity 2 4 = 2 := multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
  have hv3 : multiplicity 2 3 = 0 := multiplicity_eq_zero_of_not_dvd (by decide)
  rw [ncard_totallyRamifiedOfDegree_eq_sum h4, _root_.Padic.natCastValuation_eq_padicValNat,
    Nat.padicValNat_def, hv4]
  have h0 : {E ∈ totallyRamifiedOfDegree ℚ_[2] 4 | E.wildExponent = 0}.ncard = 0 := by
    rw [ncard_totallyRamifiedOfDegree_wildExponent_eq, ite_eq_right]
    rw [Padic.isOreAdmissible_iff]
    norm_num [Nat.padicValNat_def, hv4]
  have h1 : {E ∈ totallyRamifiedOfDegree ℚ_[2] 4 | E.wildExponent = 1}.ncard = 4 := by
    rw [ncard_quartic_padicTwo_of_adm
      ((Padic.isOreAdmissible_iff 2).mpr (by norm_num [Nat.padicValNat_def, hv4]))]
    decide
  have h3 : {E ∈ totallyRamifiedOfDegree ℚ_[2] 4 | E.wildExponent = 3}.ncard = 8 := by
    rw [ncard_quartic_padicTwo_of_adm
      ((Padic.isOreAdmissible_iff 2).mpr (by norm_num [Nat.padicValNat_def, hv4, hv3]))]
    decide
  have h5 : {E ∈ totallyRamifiedOfDegree ℚ_[2] 4 | E.wildExponent = 5}.ncard = 16 := by
    rw [ncard_quartic_padicTwo_of_adm
      ((Padic.isOreAdmissible_iff 2).mpr (by norm_num [Nat.padicValNat_def, hv4]))]
    decide
  have h6 : {E ∈ totallyRamifiedOfDegree ℚ_[2] 4 | E.wildExponent = 6}.ncard = 16 := by
    rw [ncard_quartic_padicTwo_of_adm
      ((Padic.isOreAdmissible_iff 2).mpr (by norm_num [Nat.padicValNat_def, hv4]))]
    decide
  have h7 : {E ∈ totallyRamifiedOfDegree ℚ_[2] 4 | E.wildExponent = 7}.ncard = 16 := by
    rw [ncard_quartic_padicTwo_of_adm
      ((Padic.isOreAdmissible_iff 2).mpr (by norm_num [Nat.padicValNat_def, hv4, hv3]))]
    decide
  have h8 : {E ∈ totallyRamifiedOfDegree ℚ_[2] 4 | E.wildExponent = 8}.ncard = 32 := by
    rw [ncard_quartic_padicTwo_of_adm
      ((Padic.isOreAdmissible_iff 2).mpr (by norm_num [Nat.padicValNat_def, hv4]))]
    decide
  have h9 : 4 * 2 + 1 = 9 := by norm_num
  rw [h9]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    h0, h1, ncard_totallyRamifiedOfDegree_four_wildExponent_two_padicTwo,
    h3, ncard_totallyRamifiedOfDegree_four_wildExponent_four_padicTwo,
    h5, h6, h7, h8]

end TauCeti
