/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Primary
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Ideal
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.OneAddRoot.Basic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.QuarticReciprocity.IntCast
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.RationalResidue
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.SupplementaryLaws
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The supplementary law for `1 + i` in quartic reciprocity

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and let `λ = a + b i` be primary (`TauCeti.IsPrimaryGaussian`). Together with the
laws for `i` and `-1` in `TauCeti.NumberTheory.NumberField.Cyclotomic.Four.SupplementaryLaws` and
biquadratic reciprocity in
`TauCeti.NumberTheory.NumberField.Cyclotomic.Four.QuarticReciprocity.Primary`, this file completes
the evaluation of the quartic power residue symbol by computing it at the ramified prime `1 + i`,
its conjugate `1 - i`, and `2`:

* `((1 + i) / λ)_4 = i ^ ((a - b - b² - 1) / 4)`,
* `((1 - i) / λ)_4 = i ^ (-((a + b - b² - 1) / 4))`, and
* `(2 / λ)_4 = i ^ (-(b / 2))`,

the symbols being taken at the principal ideal `λ 𝓞 K` and read in `K`, using the same primitive
fourth root of unity `i` in `λ = a + b i`, in the numerator, and in the value. Composite primary
elements and primary elements whose coordinates `(a, b)` are not coprime are included.

For primary `λ = a + b i` with coprime coordinates `(a, b)` and `b ≠ 0`, the congruence
`a - b ≡ -b (1 + i) (mod λ)` relates `((1 + i) / λ)_4` to `((a - b) / λ)_4` and `(b / λ)_4`.
Since `a - b ≡ 1 (mod 4)`, primary–rational reciprocity
(`TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast`), triviality on coprime rational integers
(`Ideal.powerResidueSymbolIdeal_intCast_four`), and the rational-denominator supplement
(`IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger`) evaluate
`((a - b) / λ)_4 = i ^ ((a - b - 1) / 4)`. Writing `b = 2 ^ k * b'` with `b'` odd, `(b' / λ)_4`
reduces by odd-integer reciprocity to `(-1) ^ (((b' - 1) / 2) * ((a - 1) / 2))`, while
`2 = -i (1 + i)²` expresses `(2 / λ)_4` through `((1 + i) / λ)_4 ^ 2`. This determines
`((1 + i) / λ)_4 ^ (2 k + 1)`, and since `2 k + 1` is invertible modulo `4` it uniquely determines
`((1 + i) / λ)_4`. General primary elements follow from the factorisation
`λ = m (c + d i)` with `m ≡ 1 (mod 4)` and `IsCoprime c d`
(`TauCeti.IsPrimaryGaussian.exists_intCast_mul_add_mul_isCoprime`) and additivity of
`(a - b - b² - 1) / 4` modulo `4`
(`TauCeti.IsPrimaryGaussian.sub_sub_sq_sub_one_div_four_mul_modEq`).

## Main results

* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger`:
  `((1 + i) / λ)_4 = i ^ ((a - b - b² - 1) / 4)` for primary `λ = a + b i`.
* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_sub_toInteger`:
  `((1 - i) / λ)_4 = i ^ (-((a + b - b² - 1) / 4))` for primary `λ = a + b i`.
* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_two`:
  `(2 / λ)_4 = i ^ (-(b / 2))` for primary `λ = a + b i`.

## References

* C. F. Gauss, *Theoria residuorum biquadraticorum, Commentatio secunda*, §§68–76.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §§7–9.
* N. Xu, *Reciprocity Laws*, §5, Definitions 5.2–5.4 and Propositions 5.10–5.12.
-/

public section

open NumberField Ideal

namespace TauCeti

/-- Modulo `4`, inverting the odd exponent `2 k + 1` on the exponent arising from `b = 2 ^ k * b'`
produces `(a - b - b² - 1) / 4`. -/
private theorem two_mul_add_one_mul_sub_modEq {a b b' : ℤ} {k : ℕ}
    (hk : 1 ≤ k) (hb : b = 2 ^ k * b') (hb' : Odd b') (hab : a - b ≡ 1 [ZMOD 4]) :
    (2 * (k : ℤ) + 1) * ((a - b - 1) / 4 - ((k : ℤ) + b' + 1) * ((a - 1) / 2)) ≡
      (a - b - b ^ 2 - 1) / 4 [ZMOD 4] := by
  obtain ⟨r, ha⟩ : ∃ r, a = 1 + b + 4 * r :=
    ⟨(a - b - 1) / 4, by simp only [Int.ModEq] at hab; omega⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨t, rfl⟩ := hb'
  have hr : (a - b - 1) / 4 = r := by omega
  have ha2 : (a - 1) / 2 = 2 ^ m * (2 * t + 1) + 2 * r := by
    have h : a - 1 = 2 * (2 ^ m * (2 * t + 1) + 2 * r) := by
      rw [ha, hb, pow_succ']
      ring
    rw [h, Int.mul_ediv_cancel_left _ (by decide)]
  have hrhs : (a - b - b ^ 2 - 1) / 4 = r - (2 ^ m * (2 * t + 1)) ^ 2 := by
    have h : a - b - b ^ 2 - 1 = 4 * (r - (2 ^ m * (2 * t + 1)) ^ 2) := by
      rw [ha, hb, pow_succ']
      ring
    rw [h, Int.mul_ediv_cancel_left _ (by decide)]
  rw [hr, ha2, hrhs]
  rcases m with _ | _ | n
  · push_cast
    exact Int.modEq_iff_dvd.mpr ⟨4 * r + 2 * t ^ 2 + 5 * t + 3 * t * r + 2, by ring⟩
  · push_cast
    exact Int.modEq_iff_dvd.mpr
      ⟨-r + 5 * (t + 2) * (2 * t + 1 + r) - (2 * t + 1) ^ 2, by ring⟩
  · have hpow : (2 : ℤ) ^ (n + 2) = 4 * (2 : ℤ) ^ n := by rw [pow_add]; ring
    set w : ℤ := (2 : ℤ) ^ n
    rw [hpow]
    push_cast
    exact Int.modEq_iff_dvd.mpr
      ⟨(2 * (n : ℤ) + 7) * w * ((n : ℤ) + 2 * t + 5) * (2 * t + 1) +
        ((n : ℤ) ^ 2 + 2 * (n : ℤ) * t + 8 * (n : ℤ) + 7 * t + 16) * r -
        4 * w ^ 2 * (2 * t + 1) ^ 2, by ring⟩

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- From `2 = -i (1 + i)²` and the supplementary laws for `-1` and `i`, expresses `(2 / λ)_4` at a
primary element `λ = a + b i` in terms of `((1 + i) / λ)_4 ^ 2`. -/
private theorem coe_powerResidueSymbolIdeal_mk_two_eq {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b : ℤ} (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ 2) : 𝓞 K) : K) =
      ζ ^ ((a - 1) / 2) *
        ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
          (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) ^ 2 := by
  set i := hζ.toInteger
  set x : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * i
  have hsq : i ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have h2 : (2 : 𝓞 K) = (-1) * i * (1 + i) ^ 2 := by linear_combination (i + 2) * hsq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by decide)
  have hneg1 : (-1 : K) ^ ((a - 1) / 2) = ζ ^ (2 * ((a - 1) / 2)) := by
    rw [← hζ.sq_eq_neg_one, ← zpow_ofNat, ← zpow_mul]
  rw [h2]
  simp only [map_mul, map_pow, ← RingOfIntegers.coe_eq_algebraMap]
  rw [hx.powerResidueSymbolIdeal_add_mul_mk_neg_one, hx.powerResidueSymbolIdeal_mk_toInteger,
    hneg1, ← zpow_add₀ hζ0]
  congr 2
  ring

/-- For primary `λ = a + b i` and an odd integer `b'` dividing `b` and coprime to `a`,
`(b' / λ)_4 = ζ ^ ((b' - 1) * ((a - 1) / 2))`. -/
private theorem coe_powerResidueSymbolIdeal_mk_odd_of_dvd {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b b' : ℤ} (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hb' : Odd b') (hdvd : b' ∣ b) (hcop : IsCoprime a b') :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (b' : 𝓞 K)) : 𝓞 K) : K) =
      ζ ^ ((b' - 1) * ((a - 1) / 2)) := by
  obtain ⟨q, rfl⟩ := hdvd
  have hmk : Ideal.Quotient.mk (span {(b' : 𝓞 K)})
      ((a : 𝓞 K) + ((b' * q : ℤ) : 𝓞 K) * hζ.toInteger) =
      Ideal.Quotient.mk (span {(b' : 𝓞 K)}) (a : 𝓞 K) :=
    Ideal.Quotient.eq.mpr (mem_span_singleton.mpr ⟨(q : 𝓞 K) * hζ.toInteger, by push_cast; ring⟩)
  have h2b' : 2 * ((b' - 1) / 2) = b' - 1 := by obtain ⟨t, rfl⟩ := hb'; omega
  rw [hx.coe_quartic_reciprocity_intCast_add_mul_of_odd hb', hmk, map_intCast,
    powerResidueSymbolIdeal_intCast_four hcop, RingOfIntegers.coe_eq_algebraMap, map_one, one_mul,
    ← hζ.sq_eq_neg_one, ← zpow_ofNat, ← zpow_mul, ← mul_assoc, h2b']

/-- For primary `λ = a + b i` with coprime coordinates `(a, b)`, primary–rational reciprocity and
the rational-denominator supplement evaluate `((a - b) / λ)_4 = ζ ^ ((a - b - 1) / 4)`. -/
private theorem coe_powerResidueSymbolIdeal_mk_sub_eq {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b : ℤ} (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hab : IsCoprime a b) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((a - b : ℤ) : 𝓞 K)) : 𝓞 K) : K) =
      ζ ^ ((a - b - 1) / 4) := by
  have hab1 : a - b ≡ 1 [ZMOD 4] := hx.sub_modEq_one
  have hmk : Ideal.Quotient.mk (span {((a - b : ℤ) : 𝓞 K)})
      ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) =
      Ideal.Quotient.mk (span {((a - b : ℤ) : 𝓞 K)})
        ((b : 𝓞 K) * (1 + hζ.toInteger)) :=
    Ideal.Quotient.eq.mpr (mem_span_singleton.mpr ⟨1, by push_cast; ring⟩)
  have hcop_b : IsCoprime b (a - b) := by
    obtain ⟨u, v, huv⟩ := hab
    exact ⟨u + v, u, by linear_combination huv⟩
  rw [hx.quartic_reciprocity_intCast hab1, hmk, map_mul, map_mul, map_intCast,
    powerResidueSymbolIdeal_intCast_four hcop_b, one_mul]
  exact hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger hab1

/-- For primary `λ = a + b i` and `b = 2 ^ k * b'` with `b'` odd and coprime to `a`, expresses
`(b / λ)_4` in terms of `((1 + i) / λ)_4 ^ (2 k)`. -/
private theorem coe_powerResidueSymbolIdeal_mk_two_pow_mul_odd {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b b' : ℤ} {k : ℕ} (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hb : b = 2 ^ k * b') (hb' : Odd b') (hab' : IsCoprime a b') :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (b : 𝓞 K)) : 𝓞 K) : K) =
      ζ ^ (((k : ℤ) + b' - 1) * ((a - 1) / 2)) *
        ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
          (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) ^ (2 * k) := by
  set x : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
  have hb_cast : (b : 𝓞 K) = (2 : 𝓞 K) ^ k * (b' : 𝓞 K) := by rw [hb]; push_cast; rfl
  rw [hb_cast]
  simp only [map_mul, map_pow, ← RingOfIntegers.coe_eq_algebraMap]
  rw [coe_powerResidueSymbolIdeal_mk_two_eq hx,
    coe_powerResidueSymbolIdeal_mk_odd_of_dvd hx hb' ⟨2 ^ k, by rw [hb, mul_comm]⟩ hab',
    mul_pow, ← pow_mul, ← zpow_natCast, ← zpow_mul, mul_right_comm _ (_ ^ (2 * k)),
    ← zpow_add₀ (hζ.ne_zero (by decide))]
  congr 2
  ring

/-- Since a primary element `x` is coprime to `1 + i`, `((1 + i) / x)_4 ^ 4 = 1`. -/
private theorem powerResidueSymbolIdeal_mk_one_add_pow_four_eq_one {ζ : K}
    (hζ : IsPrimitiveRoot ζ 4) {x : 𝓞 K} (hx : IsPrimaryGaussian x) :
    powerResidueSymbolIdeal (span {x}) 4 (Ideal.Quotient.mk _ (1 + hζ.toInteger)) ^ 4 = 1 :=
  powerResidueSymbolIdeal_pow_eq_one (n := 4) (Ideal.Quotient.isUnit_mk_iff.mpr
    (isCoprime_iff_sup_eq.mp ((isCoprime_span_singleton_iff _ _).mpr
      (hx.isCoprime_one_add_toInteger hζ))))

/-- **The supplementary law for `1 + i`.** If `K = ℚ(i)` and `λ = a + b i` is primary in
`𝓞 K = ℤ[i]`, then `((1 + i) / λ)_4 = i ^ ((a - b - b² - 1) / 4)`, the symbol being taken at the
ideal `λ 𝓞 K` and read in `K`, with the same primitive fourth root `i` used in `λ`, in the
numerator, and in the value. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger {ζ : K}
    {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) =
      ζ ^ ((a - b - b ^ 2 - 1) / 4) := by
  wlog hab : IsCoprime a b generalizing a b
  · obtain ⟨m, c, d, hm, hcd, hα, heq⟩ := hx.exists_intCast_mul_add_mul_isCoprime hζ
    obtain ⟨ha, hb⟩ := (hζ.intCast_dvd_intCast_add_intCast_mul_toInteger_iff (by decide)).mp
      (⟨0, by push_cast; linear_combination heq⟩ :
        ((0 : ℤ) : 𝓞 K) ∣ ((a - m * c : ℤ) : 𝓞 K) + ((b - m * d : ℤ) : 𝓞 K) * hζ.toInteger)
    obtain ⟨rfl, rfl⟩ : a = m * c ∧ b = m * d :=
      ⟨sub_eq_zero.mp (zero_dvd_iff.mp ha), sub_eq_zero.mp (zero_dvd_iff.mp hb)⟩
    have hm0 : span {(m : 𝓞 K)} ≠ ⊥ := by simpa using (by rw [Int.ModEq] at hm; omega : m ≠ 0)
    have hα0 : span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger} ≠ ⊥ := by simpa using hα.ne_zero
    have hm_prim : IsPrimaryGaussian ((m : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger) := by
      simpa using (isPrimaryGaussian_intCast_iff (K := K)).mpr hm
    rw [heq, ← span_singleton_mul_span_singleton, powerResidueSymbolIdeal_mul_right hm0 hα0]
    simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap]
    rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger hm, this hα hcd,
      ← zpow_add₀ (hζ.ne_zero (by decide))]
    exact zpow_eq_zpow_of_modEq hζ.pow_eq_one
      (by simpa using (hm_prim.sub_sub_sq_sub_one_div_four_mul_modEq hα).symm)
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [(by simp : (a : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger = (a : 𝓞 K))]
    simpa using hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger
      (by simpa using hx.sub_modEq_one)
  set x : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
  set s : K :=
    ((powerResidueSymbolIdeal (span {x}) 4 (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by decide)
  obtain ⟨k, b', hk, hb', hb⟩ := hx.exists_eq_two_pow_mul_odd hb0
  have h := (coe_powerResidueSymbolIdeal_mk_sub_eq hx hab).symm
  rw [Ideal.Quotient.eq.mpr (mem_span_singleton.mpr
    ⟨1, by simp only [x]; push_cast; ring⟩ :
      ((a - b : ℤ) : 𝓞 K) - (-1) * (b : 𝓞 K) * (1 + hζ.toInteger) ∈ span {x})] at h
  simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap] at h
  rw [hx.powerResidueSymbolIdeal_add_mul_mk_neg_one, ← hζ.sq_eq_neg_one, ← zpow_ofNat, ← zpow_mul,
    coe_powerResidueSymbolIdeal_mk_two_pow_mul_odd hx hb hb' (hb ▸ hab).of_mul_right_right] at h
  have hs_pow : s ^ (2 * k + 1) = ζ ^ ((a - b - 1) / 4 - ((k : ℤ) + b' + 1) * ((a - 1) / 2)) := by
    rw [zpow_sub₀ hζ0, eq_div_iff (zpow_ne_zero _ hζ0), h]
    calc s ^ (2 * k + 1) * ζ ^ (((k : ℤ) + b' + 1) * ((a - 1) / 2))
        = (ζ ^ (2 * ((a - 1) / 2)) * ζ ^ (((k : ℤ) + b' - 1) * ((a - 1) / 2))) *
            (s ^ (2 * k) * s) := by rw [mul_comm, ← zpow_add₀ hζ0, ← pow_succ]; congr 2; ring
      _ = _ := by ring
  have hs4 : s ^ 4 = 1 := by
    simpa only [s, RingOfIntegers.coe_eq_algebraMap, ← map_pow, map_one] using
      congrArg (algebraMap (𝓞 K) K) (powerResidueSymbolIdeal_mk_one_add_pow_four_eq_one hζ hx)
  have hs_sq : (s ^ (2 * k + 1)) ^ (2 * k + 1) = s := by
    rw [← pow_mul, (by ring : (2 * k + 1) * (2 * k + 1) = 4 * (k ^ 2 + k) + 1), pow_add, pow_mul,
      hs4, one_pow, one_mul, pow_one]
  rw [← hs_sq, hs_pow, ← zpow_natCast, ← zpow_mul, mul_comm]
  exact zpow_eq_zpow_of_modEq hζ.pow_eq_one
    (by push_cast; exact two_mul_add_one_mul_sub_modEq hk hb hb' hx.sub_modEq_one)

/-- **The supplementary law for `1 - i`.** If `K = ℚ(i)` and `λ = a + b i` is primary in
`𝓞 K = ℤ[i]`, then `((1 - i) / λ)_4 = i ^ (-((a + b - b² - 1) / 4))`, the symbol being taken at
the ideal `λ 𝓞 K` and read in `K`, with the same primitive fourth root `i` used in `λ`, in the
numerator, and in the value. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_sub_toInteger {ζ : K}
    {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (1 - hζ.toInteger)) : 𝓞 K) : K) =
      ζ ^ (-((a + b - b ^ 2 - 1) / 4)) := by
  have hζ3 : ζ ^ 3 = -ζ := by rw [pow_succ, hζ.sq_eq_neg_one, neg_one_mul]
  have hζ' : IsPrimitiveRoot (-ζ) 4 := hζ3 ▸ hζ.pow_of_coprime 3 (by decide)
  have htoInt : hζ'.toInteger = -hζ.toInteger := by
    apply RingOfIntegers.coe_injective
    push_cast [hζ'.coe_toInteger, hζ.coe_toInteger]
    rfl
  have hx_eq : (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger =
      (a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * hζ'.toInteger := by
    rw [htoInt]
    push_cast
    ring
  have h1 : 1 - hζ.toInteger = 1 + hζ'.toInteger := by rw [htoInt, sub_eq_add_neg]
  have hx' : IsPrimaryGaussian ((a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * hζ'.toInteger) := hx_eq ▸ hx
  have hneg : -ζ = ζ⁻¹ := eq_inv_of_mul_eq_one_left (by
    rw [neg_mul, ← pow_two, hζ.sq_eq_neg_one, neg_neg])
  rw [hx_eq, h1, hx'.powerResidueSymbolIdeal_mk_one_add_toInteger, hneg, inv_zpow, ← zpow_neg]
  congr 3
  ring

/-- **The supplementary law for `2`.** If `K = ℚ(i)` and `λ = a + b i` is primary in
`𝓞 K = ℤ[i]`, then `(2 / λ)_4 = i ^ (-(b / 2))`, the symbol being taken at the ideal `λ 𝓞 K` and
read in `K`, with the same primitive fourth root `i` used in `λ` and in the value. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_two {ζ : K}
    {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ 2) : 𝓞 K) : K) =
      ζ ^ (-(b / 2)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by decide)
  rw [coe_powerResidueSymbolIdeal_mk_two_eq hx, hx.powerResidueSymbolIdeal_mk_one_add_toInteger,
    ← zpow_ofNat, ← zpow_mul, ← zpow_add₀ hζ0]
  refine zpow_eq_zpow_of_modEq hζ.pow_eq_one ?_
  rw [hζ.isPrimaryGaussian_add_mul_iff] at hx
  simp only [Int.ModEq] at hx
  obtain ⟨u, rfl⟩ : ∃ u, b = 2 * u := ⟨b / 2, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, a = 1 + 2 * u + 4 * r := ⟨(a - 2 * u - 1) / 4, by omega⟩
  have ha2 : (1 + 2 * u + 4 * r - 1) / 2 = u + 2 * r := by omega
  have hb2 : 2 * u / 2 = u := by omega
  have hdiv : ((1 + 2 * u + 4 * r) - 2 * u - (2 * u) ^ 2 - 1) / 4 = r - u ^ 2 := by
    have h : (1 + 2 * u + 4 * r) - 2 * u - (2 * u) ^ 2 - 1 = 4 * (r - u ^ 2) := by ring
    rw [h, Int.mul_ediv_cancel_left _ (by decide)]
  obtain ⟨w, hw⟩ := Int.two_dvd_mul_add_one u
  rw [ha2, hb2, hdiv]
  exact Int.modEq_iff_dvd.mpr ⟨w - r - u, by linear_combination 2 * hw⟩

/-! ### Examples -/

section Examples

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
include hζ

/- The inert prime `-3` (`a = -3, b = 0`) and the split primes `-1 + 2i` (norm `5`), `3 + 2i`
(norm `13`), and `1 + 4i` (norm `17`). -/
example : ((powerResidueSymbolIdeal
    (span {((-3 : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -ζ := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  norm_num
  exact inv_eq_of_mul_eq_one_left (by rw [neg_mul, ← pow_two, hζ.sq_eq_neg_one, neg_neg])

example : ((powerResidueSymbolIdeal
    (span {((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -1 := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  have hexp : ((-1 - 2 - 2 ^ 2 - 1 : ℤ) / 4) ≡ 2 [ZMOD 4] := by decide
  rw [zpow_eq_zpow_of_modEq hζ.pow_eq_one hexp, zpow_ofNat]
  exact hζ.sq_eq_neg_one

example : ((powerResidueSymbolIdeal
    (span {((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -ζ := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  norm_num
  exact inv_eq_of_mul_eq_one_left (by rw [neg_mul, ← pow_two, hζ.sq_eq_neg_one, neg_neg])

example : ((powerResidueSymbolIdeal
    (span {((1 : ℤ) : 𝓞 K) + ((4 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -ζ := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  have hexp : ((1 - 4 - 4 ^ 2 - 1 : ℤ) / 4) ≡ -1 [ZMOD 4] := by decide
  rw [zpow_eq_zpow_of_modEq hζ.pow_eq_one hexp, zpow_neg_one]
  exact inv_eq_of_mul_eq_one_left (by rw [neg_mul, ← pow_two, hζ.sq_eq_neg_one, neg_neg])

/- A composite primary square `5 + 12i = (3 + 2i)²` and a composite primary element `-9 - 6i =
(-3)(3 + 2i)` whose coordinates are not coprime (`gcd(-9, -6) = 3 ≠ 1`). -/
example : ((powerResidueSymbolIdeal
    (span {((5 : ℤ) : 𝓞 K) + ((12 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -1 := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  have hexp : ((5 - 12 - 12 ^ 2 - 1 : ℤ) / 4) ≡ 2 [ZMOD 4] := by decide
  rw [zpow_eq_zpow_of_modEq hζ.pow_eq_one hexp, zpow_ofNat]
  exact hζ.sq_eq_neg_one

example : ((powerResidueSymbolIdeal
    (span {((-9 : ℤ) : 𝓞 K) + ((-6 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -1 := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  have hexp : ((-9 - (-6) - (-6) ^ 2 - 1 : ℤ) / 4) ≡ 2 [ZMOD 4] := by decide
  rw [zpow_eq_zpow_of_modEq hζ.pow_eq_one hexp, zpow_ofNat]
  exact hζ.sq_eq_neg_one

/- The companion laws for `1 - i` and `2` at `-1 + 2i`. -/
example : ((powerResidueSymbolIdeal
    (span {((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (1 - hζ.toInteger)) : 𝓞 K) : K) = ζ := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_sub_toInteger
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  norm_num

example : ((powerResidueSymbolIdeal
    (span {((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ 2) : 𝓞 K) : K) = -ζ := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_two
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  norm_num
  exact inv_eq_of_mul_eq_one_left (by rw [neg_mul, ← pow_two, hζ.sq_eq_neg_one, neg_neg])

end Examples

end TauCeti
