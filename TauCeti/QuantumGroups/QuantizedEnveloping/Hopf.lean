/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import TauCeti.Algebra.HopfAlgebra.Basic
public import TauCeti.QuantumGroups.QuantizedEnveloping.Bialgebra

import Mathlib.Tactic.Ring

/-!
# Antipode and Hopf algebra structure on the generic Drinfeld–Jimbo algebra

For a symmetrizable Cartan datum `D : CartanDatum ι X Y` and a generic parameter `q : K`
(`[Fact (IsGenericQuantumParameter q)]`), this file equips the Drinfeld–Jimbo bialgebra
`QuantizedEnvelopingAlgebra D q` with its antipode and Hopf algebra structure over `K`:

* `S(Eᵢ) = -Kᵢ⁻¹ Eᵢ`, `S(Fᵢ) = -Fᵢ Kᵢ`, `S(K_y) = K_(-y)`.

Compatibility of `S` with the quantum Serre relations moves all toral powers in the opposite
algebra to one side and cancels the resulting quadratic exponents of `q`. Once `instHopfAlgebra`
is in place, `BialgHomClass.map_antipode` automatically implies that `mapBialgHom`,
`rescaleBialgEquiv`, and `torusBialgEquiv` commute with `S`.

This file also introduces the normalized raising and lowering operators `normE i = Kᵢ⁻¹ Eᵢ` and
`normF i = Fᵢ Kᵢ` (`-S(Eᵢ)` and `-S(Fᵢ)`), whose coproducts carry the group-like factor in the
transposed tensor leg.

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.antipodeOp` and
  `TauCeti.QuantizedEnvelopingAlgebra.instHopfAlgebra`: the opposite-valued antipode algebra map
  and the Hopf algebra instance on `QuantizedEnvelopingAlgebra D q`.
* `TauCeti.QuantizedEnvelopingAlgebra.antipode_e`,
  `TauCeti.QuantizedEnvelopingAlgebra.antipode_f`, and
  `TauCeti.QuantizedEnvelopingAlgebra.antipode_k`: values of `S` on the generators.
* `TauCeti.QuantizedEnvelopingAlgebra.normE` and `TauCeti.QuantizedEnvelopingAlgebra.normF`:
  normalized operators `Kᵢ⁻¹ Eᵢ` and `Fᵢ Kᵢ` with `Δ(normE i) = normE i ⊗ Kᵢ⁻¹ + 1 ⊗ normE i` and
  `Δ(normF i) = normF i ⊗ 1 + Kᵢ ⊗ normF i`.

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, §§4.8–4.11.
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §§1.3–1.4 and §3.1.
-/

public section

open scoped TensorProduct
open Finset HopfAlgebra

namespace TauCeti.QuantizedEnvelopingAlgebra

section Hopf

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

/-- The normalized raising element `eᵢ' = Kᵢ⁻¹ Eᵢ` (`= -S(Eᵢ)` for generic `q`), whose coproduct
has the group-like factor in the second tensor leg:
`Δ(normE D q i) = normE D q i ⊗ Kᵢ⁻¹ + 1 ⊗ normE D q i`. -/
noncomputable def normE (i : ι) : QuantizedEnvelopingAlgebra D q :=
  simpleKInv D q i * e D q i

/-- The normalized lowering element `fᵢ' = Fᵢ Kᵢ` (`= -S(Fᵢ)` for generic `q`), whose coproduct
has the group-like factor in the first tensor leg:
`Δ(normF D q i) = normF D q i ⊗ 1 + Kᵢ ⊗ normF D q i`. -/
noncomputable def normF (i : ι) : QuantizedEnvelopingAlgebra D q :=
  f D q i * simpleK D q i

theorem normE_def (i : ι) : normE D q i = simpleKInv D q i * e D q i := (rfl)

theorem normF_def (i : ι) : normF D q i = f D q i * simpleK D q i := (rfl)

private theorem nat_mul_pred_cast (n : ℕ) :
    ((n * (n - 1) : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  cases n <;> push_cast
  ring

private theorem quantumDividedPower_neg {B : Type*} [Ring B] [Algebra K B]
    (q₀ : K) (x : B) (n : ℕ) :
    quantumDividedPower q₀ (-x) n = (-1 : K) ^ n • quantumDividedPower q₀ x n := by
  rw [← neg_one_smul K x, quantumDividedPower_smul]

/-- Quantum divided power of `normE D q i = Kᵢ⁻¹ Eᵢ`:
`(Kᵢ⁻¹ Eᵢ)^(n) = qᵢ^(n(n - 1)) • (Kᵢ^(-n) * Eᵢ^(n))`. -/
theorem quantumDividedPower_normE (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (normE D q i) n =
      (q ^ D.symmetrizer i) ^ (n * (n - 1)) •
        (simpleKInv D q i ^ n * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) := by
  have hek : e D q i * simpleKInv D q i =
      (q ^ D.symmetrizer i) ^ 2 • (simpleKInv D q i * e D q i) := by
    simpa using e_mul_simpleKInv D q i i
  rw [normE_def, quantumDividedPower_def, mul_pow_of_mul_eq_smul_mul hek, smul_comm,
    ← mul_smul_comm, ← quantumDividedPower_def]

/-- Quantum divided power of `normF D q i = Fᵢ Kᵢ`:
`(Fᵢ Kᵢ)^(n) = (qᵢ⁻¹)^(n(n - 1)) • (Fᵢ^(n) * Kᵢ^n)`. -/
theorem quantumDividedPower_normF (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (normF D q i) n =
      ((q ^ D.symmetrizer i)⁻¹) ^ (n * (n - 1)) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n * simpleK D q i ^ n) := by
  have hkf : simpleK D q i * f D q i =
      ((q ^ D.symmetrizer i)⁻¹) ^ 2 • (f D q i * simpleK D q i) := by
    have h := simpleK_mul_f D q i i
    rwa [D.cartan_apply_self, zpow_neg, zpow_ofNat, ← inv_pow] at h
  rw [normF_def, quantumDividedPower_def, mul_pow_of_mul_eq_smul_mul hkf, smul_comm,
    ← smul_mul_assoc, ← quantumDividedPower_def]

private theorem serreElement_reflect {A : Type*} [Ring A] [Algebra K A]
    (x : ι → A) (i j : ι) :
    (∑ r ∈ range (serreLength D i j + 1),
        (-1 : K) ^ r •
          (quantumDividedPower (q ^ D.symmetrizer i) (x i) (serreLength D i j - r) * x j *
            quantumDividedPower (q ^ D.symmetrizer i) (x i) r)) =
      (-1 : K) ^ serreLength D i j • serreElement D q x i j := by
  set m := serreLength D i j
  rw [← sum_range_reflect]
  simp only [Nat.add_succ_sub_one, add_zero, serreElement_def, smul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hle : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
  have h1 : (-1 : K) ^ m = (-1 : K) ^ (m - r) * (-1 : K) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hsign : (-1 : K) ^ (m - r) = (-1 : K) ^ m * (-1 : K) ^ r := by
    rw [h1, mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]
  rw [Nat.sub_sub_self hle, hsign, mul_smul]

variable [Fact (IsGenericQuantumParameter q)]

private theorem antipode_serre_e_term {i j : ι} (hij : i ≠ j) {r : ℕ}
    (hle : r ≤ serreLength D i j) :
    MulOpposite.unop
        ((-1 : K) ^ r •
          (quantumDividedPower (q ^ D.symmetrizer i)
              (MulOpposite.op (-(simpleKInv D q i * e D q i))) r *
            MulOpposite.op (-(simpleKInv D q j * e D q j)) *
            quantumDividedPower (q ^ D.symmetrizer i)
              (MulOpposite.op (-(simpleKInv D q i * e D q i))) (serreLength D i j - r))) =
      (-(-1 : K) ^ serreLength D i j) •
        (k D q (serreLength D i j • (-D.simpleTorus i) - D.simpleTorus j) *
          ((-1 : K) ^ r •
            (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (serreLength D i j - r) *
              e D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r))) := by
  have hq0 : q ≠ 0 := (Fact.out : IsGenericQuantumParameter q).ne_zero
  set m := serreLength D i j
  set s := m - r
  simp only [MulOpposite.unop_smul, MulOpposite.unop_mul, MulOpposite.unop_quantumDividedPower,
    MulOpposite.unop_op, quantumDividedPower_neg]
  rw [← neg_one_smul K (simpleKInv D q j * e D q j)]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hcore :
      quantumDividedPower (q ^ D.symmetrizer i) (simpleKInv D q i * e D q i) s *
          (simpleKInv D q j * e D q j *
            quantumDividedPower (q ^ D.symmetrizer i) (simpleKInv D q i * e D q i) r) =
        k D q (m • (-D.simpleTorus i) - D.simpleTorus j) *
          (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s * e D q j *
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) := by
    rw [← normE_def D q i, quantumDividedPower_normE, quantumDividedPower_normE]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, k_pow]
    have hstep1 :
        k D q (-D.simpleTorus j) * e D q j *
            (k D q (r • -D.simpleTorus i) *
              quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) =
          q ^ (-D.pairing (D.root j) (r • -D.simpleTorus i)) •
            (k D q (-D.simpleTorus j + r • -D.simpleTorus i) *
              (e D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r)) := by
      calc
        k D q (-D.simpleTorus j) * e D q j *
            (k D q (r • -D.simpleTorus i) *
              quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) =
            k D q (-D.simpleTorus j) * (e D q j * k D q (r • -D.simpleTorus i)) *
              quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r := by
          simp [mul_assoc]
        _ = _ := by
          rw [e_mul_k, mul_smul_comm, smul_mul_assoc, ← mul_assoc (k D q (-D.simpleTorus j)),
            k_mul_k]
          simp [mul_assoc]
    rw [hstep1, mul_smul_comm, smul_smul]
    have hstep2 :
        k D q (s • -D.simpleTorus i) *
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s *
            (k D q (-D.simpleTorus j + r • -D.simpleTorus i) *
              (e D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r)) =
          (q ^ (-D.pairing (D.root i) (-D.simpleTorus j + r • -D.simpleTorus i))) ^ s •
            (k D q (m • -D.simpleTorus i - D.simpleTorus j) *
              (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s * e D q j *
                quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r)) := by
      calc
        k D q (s • -D.simpleTorus i) *
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s *
            (k D q (-D.simpleTorus j + r • -D.simpleTorus i) *
              (e D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r)) =
            k D q (s • -D.simpleTorus i) *
              (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s *
                k D q (-D.simpleTorus j + r • -D.simpleTorus i)) *
              (e D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) := by
          simp [mul_assoc]
        _ = _ := by
          rw [quantumDividedPower_e_mul_k, mul_smul_comm, smul_mul_assoc,
            ← mul_assoc (k D q (s • -D.simpleTorus i)), k_mul_k]
          have hy : s • -D.simpleTorus i + (-D.simpleTorus j + r • -D.simpleTorus i) =
              m • -D.simpleTorus i - D.simpleTorus j := by
            rw [add_left_comm, ← add_nsmul, Nat.sub_add_cancel hle, sub_eq_add_neg, add_comm]
          rw [hy]
          simp [mul_assoc]
    rw [hstep2, smul_smul]
    have hqone :
        (q ^ D.symmetrizer i) ^ (r * (r - 1)) * (q ^ D.symmetrizer i) ^ (s * (s - 1)) *
          q ^ (-D.pairing (D.root j) (r • -D.simpleTorus i)) *
          (q ^ (-D.pairing (D.root i) (-D.simpleTorus j + r • -D.simpleTorus i))) ^ s = 1 := by
      rw [← pow_mul, ← pow_mul, ← zpow_natCast q, ← zpow_natCast q,
        ← zpow_natCast (q ^ _), ← zpow_mul, ← zpow_add₀ hq0, ← zpow_add₀ hq0, ← zpow_add₀ hq0]
      suffices hexp :
          ((D.symmetrizer i * (r * (r - 1)) : ℕ) : ℤ) +
            ((D.symmetrizer i * (s * (s - 1)) : ℕ) : ℤ) +
            (-D.pairing (D.root j) (r • -D.simpleTorus i)) +
            (-D.pairing (D.root i) (-D.simpleTorus j + r • -D.simpleTorus i)) * (s : ℤ) = 0 by
        rw [hexp, zpow_zero]
      rw [Nat.cast_mul (D.symmetrizer i), Nat.cast_mul (D.symmetrizer i),
        nat_mul_pred_cast r, nat_mul_pred_cast s,
        map_nsmul, map_neg, D.pairing_root_simpleTorus, D.symmetrizer_mul_cartan j i,
        map_add, map_neg, map_nsmul, map_neg, D.pairing_root_simpleTorus,
        D.pairing_root_simpleTorus_self, ← one_sub_serreLength D hij]
      have hm : (m : ℤ) = s + r := by
        have := Nat.sub_add_cancel hle
        omega
      push_cast [nsmul_eq_mul]
      rw [hm]
      ring
    rw [hqone, one_smul]
  rw [hcore]
  congr 1
  have h1 : (-1 : K) ^ m = (-1 : K) ^ s * (-1 : K) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [h1]
  ring

private theorem antipode_serre_f_term {i j : ι} (hij : i ≠ j) {r : ℕ}
    (hle : r ≤ serreLength D i j) :
    MulOpposite.unop
        ((-1 : K) ^ r •
          (quantumDividedPower (q ^ D.symmetrizer i)
              (MulOpposite.op (-(f D q i * simpleK D q i))) r *
            MulOpposite.op (-(f D q j * simpleK D q j)) *
            quantumDividedPower (q ^ D.symmetrizer i)
              (MulOpposite.op (-(f D q i * simpleK D q i))) (serreLength D i j - r))) =
      (-(-1 : K) ^ serreLength D i j) •
        (((-1 : K) ^ r •
            (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) (serreLength D i j - r) *
              f D q j * quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r)) *
          k D q (serreLength D i j • D.simpleTorus i + D.simpleTorus j)) := by
  have hq0 : q ≠ 0 := (Fact.out : IsGenericQuantumParameter q).ne_zero
  set m := serreLength D i j
  set s := m - r
  simp only [MulOpposite.unop_smul, MulOpposite.unop_mul, MulOpposite.unop_quantumDividedPower,
    MulOpposite.unop_op, quantumDividedPower_neg]
  rw [← neg_one_smul K (f D q j * simpleK D q j)]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hcore :
      quantumDividedPower (q ^ D.symmetrizer i) (f D q i * simpleK D q i) s *
          (f D q j * simpleK D q j *
            quantumDividedPower (q ^ D.symmetrizer i) (f D q i * simpleK D q i) r) =
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) s * f D q j *
            quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r) *
          k D q (m • D.simpleTorus i + D.simpleTorus j) := by
    rw [← normF_def D q i, quantumDividedPower_normF, quantumDividedPower_normF]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, k_pow]
    have hstep1 :
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) s * k D q (s • D.simpleTorus i)) *
            (f D q j * k D q (D.simpleTorus j) *
              (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r *
                k D q (r • D.simpleTorus i))) =
          q ^ (-D.pairing (D.root j) (s • D.simpleTorus i)) •
            ((quantumDividedPower (q ^ D.symmetrizer i) (f D q i) s * f D q j) *
              (k D q (s • D.simpleTorus i + D.simpleTorus j) *
                quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r) *
              k D q (r • D.simpleTorus i)) := by
      calc
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) s * k D q (s • D.simpleTorus i)) *
            (f D q j * k D q (D.simpleTorus j) *
              (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r *
                k D q (r • D.simpleTorus i))) =
            quantumDividedPower (q ^ D.symmetrizer i) (f D q i) s *
              (k D q (s • D.simpleTorus i) * f D q j) * k D q (D.simpleTorus j) *
              quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r *
              k D q (r • D.simpleTorus i) := by
          simp [mul_assoc]
        _ = _ := by
          rw [k_mul_f, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
          simp [mul_assoc, k_mul_k]
    rw [hstep1, smul_smul]
    have hstep2 :
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) s * f D q j) *
            (k D q (s • D.simpleTorus i + D.simpleTorus j) *
              quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r) *
            k D q (r • D.simpleTorus i) =
          (q ^ (-D.pairing (D.root i) (s • D.simpleTorus i + D.simpleTorus j))) ^ r •
            ((quantumDividedPower (q ^ D.symmetrizer i) (f D q i) s * f D q j *
                quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r) *
              k D q (m • D.simpleTorus i + D.simpleTorus j)) := by
      rw [k_mul_quantumDividedPower_f, mul_smul_comm, smul_mul_assoc]
      have hy : (s • D.simpleTorus i + D.simpleTorus j) + r • D.simpleTorus i =
          m • D.simpleTorus i + D.simpleTorus j := by
        rw [add_right_comm, ← add_nsmul, Nat.sub_add_cancel hle]
      simp [mul_assoc, k_mul_k, hy]
    rw [hstep2, smul_smul]
    have hqone :
        ((q ^ D.symmetrizer i)⁻¹) ^ (r * (r - 1)) *
          ((q ^ D.symmetrizer i)⁻¹) ^ (s * (s - 1)) *
          q ^ (-D.pairing (D.root j) (s • D.simpleTorus i)) *
          (q ^ (-D.pairing (D.root i) (s • D.simpleTorus i + D.simpleTorus j))) ^ r = 1 := by
      rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, ← zpow_natCast q, ← zpow_natCast q,
        ← zpow_neg, ← zpow_neg, ← zpow_natCast (q ^ _), ← zpow_mul,
        ← zpow_add₀ hq0, ← zpow_add₀ hq0, ← zpow_add₀ hq0]
      suffices hexp :
          -((D.symmetrizer i * (r * (r - 1)) : ℕ) : ℤ) +
            -((D.symmetrizer i * (s * (s - 1)) : ℕ) : ℤ) +
            (-D.pairing (D.root j) (s • D.simpleTorus i)) +
            (-D.pairing (D.root i) (s • D.simpleTorus i + D.simpleTorus j)) * (r : ℤ) = 0 by
        rw [hexp, zpow_zero]
      rw [Nat.cast_mul (D.symmetrizer i), Nat.cast_mul (D.symmetrizer i),
        nat_mul_pred_cast r, nat_mul_pred_cast s,
        map_nsmul, D.pairing_root_simpleTorus, D.symmetrizer_mul_cartan j i,
        map_add, map_nsmul, D.pairing_root_simpleTorus_self, D.pairing_root_simpleTorus,
        ← one_sub_serreLength D hij]
      have hm : (m : ℤ) = s + r := by
        have := Nat.sub_add_cancel hle
        omega
      push_cast [nsmul_eq_mul]
      rw [hm]
      ring
    rw [hqone, one_smul]
  rw [hcore]
  congr 1
  have h1 : (-1 : K) ^ m = (-1 : K) ^ s * (-1 : K) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [h1]
  ring

private noncomputable def antipodeTuple :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ where
  e i := MulOpposite.op (-(simpleKInv D q i * e D q i))
  f i := MulOpposite.op (-(f D q i * simpleK D q i))
  k y := MulOpposite.op (k D q (-y))
  k_zero := by apply MulOpposite.unop_injective; simp
  k_mul_k y z := by
    apply MulOpposite.unop_injective
    simp [neg_add_rev, add_comm]
  k_mul_e_mul_k_neg y i := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, neg_neg,
      neg_mul, mul_neg, smul_neg, neg_inj, mul_assoc]
    rw [e_mul_k, mul_smul_comm]
    simp [← mul_assoc, k_mul_k, add_comm y]
  k_mul_f_mul_k_neg y i := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, neg_neg,
      neg_mul, mul_neg, smul_neg, neg_inj]
    calc
      k D q y * (f D q i * simpleK D q i * k D q (-y)) =
          (k D q y * f D q i * k D q (-y)) * (k D q y * simpleK D q i * k D q (-y)) := by
        calc
          k D q y * (f D q i * simpleK D q i * k D q (-y)) =
              k D q y * f D q i * (k D q (-y + y) * simpleK D q i) * k D q (-y) := by
            simp [mul_assoc]
          _ = _ := by rw [← k_mul_k]; simp [mul_assoc, add_comm (-y)]
      _ = q ^ (-D.pairing (D.root i) y) • (f D q i * simpleK D q i) := by
        rw [k_mul_f_mul_k_neg, smul_mul_assoc]
        congr 2
        simp [k_mul_k, add_comm y, add_neg_cancel_right]
  e_mul_f_sub_f_mul_e_self i := by
    have hqi : q ^ D.symmetrizer i ≠ 0 :=
      ((Fact.out : IsGenericQuantumParameter q).pow (D.symmetrizer_pos i)).ne_zero
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_smul, neg_mul_neg]
    have h1 : f D q i * simpleK D q i * (simpleKInv D q i * e D q i) = f D q i * e D q i := by
      calc
        f D q i * simpleK D q i * (simpleKInv D q i * e D q i) =
            f D q i * (simpleK D q i * simpleKInv D q i) * e D q i := by simp [mul_assoc]
        _ = f D q i * e D q i := by simp
    have h2 : simpleKInv D q i * e D q i * (f D q i * simpleK D q i) = e D q i * f D q i := by
      calc
        simpleKInv D q i * e D q i * (f D q i * simpleK D q i) =
            (simpleKInv D q i * e D q i) * f D q i * simpleK D q i := by simp [mul_assoc]
        _ = ((q ^ D.symmetrizer i) ^ (-2 : ℤ) * (q ^ D.symmetrizer i) ^ (2 : ℤ)) •
              (e D q i * f D q i * (simpleKInv D q i * simpleK D q i)) := by
          rw [simpleKInv_mul_e, D.cartan_apply_self, smul_mul_assoc, smul_mul_assoc,
            mul_assoc (e D q i), simpleKInv_mul_f, D.cartan_apply_self, mul_smul_comm,
            smul_mul_assoc, smul_smul]
          simp [mul_assoc]
        _ = e D q i * f D q i := by
          rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero 2 hqi), one_smul]
          simp
    rw [h1, h2, ← neg_sub (e D q i * f D q i), e_mul_f_sub_f_mul_e_self, ← smul_neg, neg_sub,
      neg_neg]
  e_mul_f_of_ne {i j} hij := by
    have hq0 : q ≠ 0 := (Fact.out : IsGenericQuantumParameter q).ne_zero
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, neg_mul_neg]
    calc
      f D q j * simpleK D q j * (simpleKInv D q i * e D q i) =
          (f D q j * simpleKInv D q i) * (simpleK D q j * e D q i) := by
        calc
          f D q j * simpleK D q j * (simpleKInv D q i * e D q i) =
              f D q j * (simpleK D q j * simpleKInv D q i) * e D q i := by simp [mul_assoc]
          _ = _ := by
            rw [(k_commute D q (D.simpleTorus j) (-D.simpleTorus i)).eq]
            simp [mul_assoc]
      _ = simpleKInv D q i * (f D q j * e D q i) * simpleK D q j := by
        rw [f_mul_k D q j (-D.simpleTorus i), k_mul_e D q (D.simpleTorus j) i,
          smul_mul_smul_comm]
        have hexp :
            q ^ D.pairing (D.root j) (-D.simpleTorus i) *
              q ^ D.pairing (D.root i) (D.simpleTorus j) = 1 := by
          rw [map_neg, D.pairing_root_simpleTorus, D.pairing_root_simpleTorus,
            D.symmetrizer_mul_cartan j i, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero]
        rw [hexp, one_smul]
        simp [mul_assoc]
      _ = simpleKInv D q i * e D q i * (f D q j * simpleK D q j) := by
        rw [← e_mul_f_of_ne D q hij]
        simp [mul_assoc]
  serre_e {i j} hij := by
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_zero, serreElement_def, ← MulOpposite.opAddEquiv_symm_apply, map_sum]
    simp only [MulOpposite.opAddEquiv_symm_apply]
    rw [sum_congr rfl fun r hr =>
        antipode_serre_e_term D q hij (Nat.lt_succ_iff.mp (mem_range.mp hr)),
      ← smul_sum, ← mul_sum, serreElement_reflect, serre_e D q hij, smul_zero, mul_zero, smul_zero]
  serre_f {i j} hij := by
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_zero, serreElement_def, ← MulOpposite.opAddEquiv_symm_apply, map_sum]
    simp only [MulOpposite.opAddEquiv_symm_apply]
    rw [sum_congr rfl fun r hr =>
        antipode_serre_f_term D q hij (Nat.lt_succ_iff.mp (mem_range.mp hr)),
      ← smul_sum, ← sum_mul, serreElement_reflect, serre_f D q hij, smul_zero, zero_mul, smul_zero]

/-- The antipode as an algebra homomorphism into the opposite algebra:
`S(Eᵢ) = -Kᵢ⁻¹ Eᵢ`, `S(Fᵢ) = -Fᵢ Kᵢ`, and `S(K_y) = K_(-y)`. -/
noncomputable def antipodeOp :
    QuantizedEnvelopingAlgebra D q →ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  lift (antipodeTuple D q)

@[local simp]
private theorem antipodeOp_e (i : ι) :
    antipodeOp D q (e D q i) = MulOpposite.op (-(simpleKInv D q i * e D q i)) :=
  lift_e _ i

@[local simp]
private theorem antipodeOp_f (i : ι) :
    antipodeOp D q (f D q i) = MulOpposite.op (-(f D q i * simpleK D q i)) :=
  lift_f _ i

@[local simp]
private theorem antipodeOp_k (y : Y) :
    antipodeOp D q (k D q y) = MulOpposite.op (k D q (-y)) :=
  lift_k _ y

/-- The Drinfeld–Jimbo Hopf algebra structure on `QuantizedEnvelopingAlgebra D q`. -/
noncomputable instance instHopfAlgebra : HopfAlgebra K (QuantizedEnvelopingAlgebra D q) :=
  HopfAlgebra.ofAntipodeOfAdjoin (antipodeOp D q) (adjoin_range_generator D q)
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;> simp [mul_assoc])
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;> simp [← mul_assoc (simpleK D q _)])

/-- `S(Eᵢ) = -Kᵢ⁻¹ Eᵢ`. -/
@[simp]
theorem antipode_e (i : ι) :
    antipode K (e D q i) = -(simpleKInv D q i * e D q i) := by
  simp [antipode]

/-- `S(Fᵢ) = -Fᵢ Kᵢ`. -/
@[simp]
theorem antipode_f (i : ι) :
    antipode K (f D q i) = -(f D q i * simpleK D q i) := by
  simp [antipode]

/-- `S(K_y) = K_(-y)`. -/
@[simp]
theorem antipode_k (y : Y) :
    antipode K (k D q y) = k D q (-y) := by
  simp [antipode]

/-- `antipodeOp D q` agrees with `MulOpposite.op ∘ antipode K`. -/
@[simp]
theorem antipodeOp_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeOp D q x = MulOpposite.op (antipode K x) := by
  apply MulOpposite.unop_injective
  rfl

/-! ### Normalized skew-primitive operators -/

/-- `S(Eᵢ) = -normE D q i`. -/
theorem antipode_e_eq_neg_normE (i : ι) : antipode K (e D q i) = -normE D q i :=
  antipode_e D q i

/-- `S(Fᵢ) = -normF D q i`. -/
theorem antipode_f_eq_neg_normF (i : ι) : antipode K (f D q i) = -normF D q i :=
  antipode_f D q i

/-- `ε(Kᵢ⁻¹ Eᵢ) = 0`. -/
@[simp]
theorem counit_normE (i : ι) : Coalgebra.counit (R := K) (normE D q i) = 0 := by
  rw [← counit_apply, normE, map_mul]
  simp

/-- `ε(Fᵢ Kᵢ) = 0`. -/
@[simp]
theorem counit_normF (i : ι) : Coalgebra.counit (R := K) (normF D q i) = 0 := by
  rw [← counit_apply, normF, map_mul]
  simp

/-- `Δ(Kᵢ⁻¹ Eᵢ) = (Kᵢ⁻¹ Eᵢ) ⊗ Kᵢ⁻¹ + 1 ⊗ (Kᵢ⁻¹ Eᵢ)`. -/
@[simp]
theorem comul_normE (i : ι) :
    Coalgebra.comul (R := K) (normE D q i) =
      normE D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] normE D q i := by
  rw [normE, ← comul_apply, map_mul, comul_apply, comul_apply, comul_k, comul_e, mul_add]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- `Δ(Fᵢ Kᵢ) = (Fᵢ Kᵢ) ⊗ 1 + Kᵢ ⊗ (Fᵢ Kᵢ)`. -/
@[simp]
theorem comul_normF (i : ι) :
    Coalgebra.comul (R := K) (normF D q i) =
      normF D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] normF D q i := by
  rw [normF, ← comul_apply, map_mul, comul_apply, comul_apply, comul_f, comul_k, add_mul]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end Hopf

end TauCeti.QuantizedEnvelopingAlgebra
