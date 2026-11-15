/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.QuantumGroups.QuantizedEnveloping.Rescale

import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Bialgebra structure on the generic Drinfeld–Jimbo quantized enveloping algebra

For a symmetrizable Cartan datum `D : CartanDatum ι X Y` and a generic parameter `q : K`
(`[Fact (IsGenericQuantumParameter q)]`), this file equips `QuantizedEnvelopingAlgebra D q` with
its Drinfeld–Jimbo bialgebra structure over `K` in the Lusztig–Jantzen conventions:

* `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`, `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`, `Δ(K_y) = K_y ⊗ K_y`;
* `ε(Eᵢ) = 0`, `ε(Fᵢ) = 0`, `ε(K_y) = 1` (defined unconditionally for all `q : K`).

Compatibility of `Δ` with the quantum Serre relations reduces to a general four-variable
skew-primitive quantum Serre identity whose off-diagonal mixed terms cancel via the alternating
`q`-binomial sum `sum_neg_one_pow_mul_zpow_mul_quantumBinomial`.

This file also derives the coproducts of quantum divided powers `Eᵢ^(n)` and `Fᵢ^(n)` and upgrades
functoriality in the Cartan datum (`mapBialgHom`), diagonal rescalings (`rescaleBialgEquiv`), and
the empty-root torus equivalence (`torusBialgEquiv`) to bialgebra morphisms. The antipode and Hopf
algebra structure are constructed in `TauCeti.QuantumGroups.QuantizedEnveloping.Hopf`.

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.counit`: the unconditional augmentation `U →ₐ[K] K`.
* `TauCeti.QuantizedEnvelopingAlgebra.comul` and
  `TauCeti.QuantizedEnvelopingAlgebra.instBialgebra`: the coproduct and bialgebra structure for
  generic `q`.
* `TauCeti.QuantizedEnvelopingAlgebra.comul_quantumDividedPower_e` and
  `TauCeti.QuantizedEnvelopingAlgebra.comul_quantumDividedPower_f`: coproducts of divided powers.
* `TauCeti.QuantizedEnvelopingAlgebra.mapBialgHom`,
  `TauCeti.QuantizedEnvelopingAlgebra.rescaleBialgEquiv`, and
  `TauCeti.QuantizedEnvelopingAlgebra.torusBialgEquiv`: bialgebra morphisms and equivalences.

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, §§4.8–4.9.
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §§1.3–1.4 and §3.1.
* Follows the rank-one bialgebra pattern in `TauCeti.QuantumGroups.UqSl2.Hopf` and
  `TauCeti.QuantumGroups.UqSl2.ComulPow`.
-/

public section

open scoped TensorProduct
open Finset

namespace TauCeti.QuantizedEnvelopingAlgebra

/-! ### Unconditional counit -/

section Counit

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

private def counitTuple : GeneratorTuple D q K where
  e _ := 0
  f _ := 0
  k _ := 1
  k_zero := rfl
  k_mul_k _ _ := one_mul 1
  k_mul_e_mul_k_neg _ _ := by simp
  k_mul_f_mul_k_neg _ _ := by simp
  e_mul_f_sub_f_mul_e_self _ := by simp
  e_mul_f_of_ne _ := rfl
  serre_e _ := by simp [serreElement_def]
  serre_f _ := by simp [serreElement_def]

/-- The unconditional counit `QuantizedEnvelopingAlgebra D q →ₐ[K] K`, sending `Eᵢ ↦ 0`,
`Fᵢ ↦ 0`, and `K_y ↦ 1`. -/
noncomputable def counit : QuantizedEnvelopingAlgebra D q →ₐ[K] K :=
  lift (counitTuple D q)

@[simp]
theorem counit_apply_e (i : ι) : counit D q (e D q i) = 0 :=
  lift_e _ i

@[simp]
theorem counit_apply_f (i : ι) : counit D q (f D q i) = 0 :=
  lift_f _ i

@[simp]
theorem counit_apply_k (y : Y) : counit D q (k D q y) = 1 :=
  lift_k _ y

end Counit

/-! ### Four-variable quantum Serre skew-primitive identity -/

section SerreSkewPrimitive

private theorem sum_triple_reindex_left {M : Type*} [AddCommMonoid M] (m : ℕ)
    (F : ℕ → ℕ → ℕ → M) :
    (∑ r ∈ range (m + 1), ∑ a₁ ∈ range (r + 1), ∑ b₁ ∈ range (m - r + 1),
        F a₁ b₁ (r - a₁)) =
      ∑ a₁ ∈ range (m + 1), ∑ b₁ ∈ range (m - a₁ + 1),
        ∑ a₂ ∈ range (m - a₁ - b₁ + 1), F a₁ b₁ a₂ := by
  simp only [sum_sigma']
  refine sum_bij (fun p _ => ⟨p.2.1, ⟨p.2.2, p.1 - p.2.1⟩⟩) ?_ ?_ ?_ ?_
  · rintro ⟨r, ⟨a₁, b₁⟩⟩ hp
    simp only [mem_sigma, mem_range] at hp ⊢
    omega
  · rintro ⟨r, ⟨a₁, b₁⟩⟩ hp ⟨r', ⟨a₁', b₁'⟩⟩ hp' hEq
    simp only [mem_sigma, mem_range, Sigma.mk.inj_iff, heq_eq_eq] at hp hp' hEq
    rcases hEq with ⟨rfl, hb, ha⟩
    have hr : r = r' := by omega
    subst hr hb
    rfl
  · rintro ⟨a₁, ⟨b₁, a₂⟩⟩ hp
    simp only [mem_sigma, mem_range] at hp
    refine ⟨⟨a₁ + a₂, ⟨a₁, b₁⟩⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      omega
    · simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
      omega
  · rintro ⟨r, ⟨a₁, b₁⟩⟩ _
    rfl

private theorem sum_triple_reindex_right {M : Type*} [AddCommMonoid M] (m : ℕ)
    (F : ℕ → ℕ → ℕ → M) :
    (∑ r ∈ range (m + 1), ∑ a₁ ∈ range (r + 1), ∑ b₁ ∈ range (m - r + 1),
        F (r - a₁) (m - r - b₁) a₁) =
      ∑ a₂ ∈ range (m + 1), ∑ b₂ ∈ range (m - a₂ + 1),
        ∑ a₁ ∈ range (m - a₂ - b₂ + 1), F a₂ b₂ a₁ := by
  simp only [sum_sigma']
  refine sum_bij (fun p _ => ⟨p.1 - p.2.1, ⟨m - p.1 - p.2.2, p.2.1⟩⟩) ?_ ?_ ?_ ?_
  · rintro ⟨r, ⟨a₁, b₁⟩⟩ hp
    simp only [mem_sigma, mem_range] at hp ⊢
    omega
  · rintro ⟨r, ⟨a₁, b₁⟩⟩ hp ⟨r', ⟨a₁', b₁'⟩⟩ hp' hEq
    simp only [mem_sigma, mem_range, Sigma.mk.inj_iff, heq_eq_eq] at hp hp' hEq
    rcases hEq with ⟨ha₂, hb₂, rfl⟩
    have hr : r = r' := by omega
    have hb : b₁ = b₁' := by omega
    subst hr hb
    rfl
  · rintro ⟨a₂, ⟨b₂, a₁⟩⟩ hp
    simp only [mem_sigma, mem_range] at hp
    refine ⟨⟨a₁ + a₂, ⟨a₁, m - a₂ - b₂ - a₁⟩⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      omega
    · simp only [Sigma.mk.inj_iff, heq_eq_eq]
      refine ⟨by omega, by omega, trivial⟩
  · rintro ⟨r, ⟨a₁, b₁⟩⟩ _
    rfl

private noncomputable def serrePoly {K B : Type*} [Field K] [Ring B] [Algebra K B]
    (q₀ : K) (m : ℕ) (x y : B) : B :=
  ∑ r ∈ range (m + 1),
    (-1 : K) ^ r • (quantumDividedPower q₀ x r * y * quantumDividedPower q₀ x (m - r))

private theorem dp_comm_two {K B : Type*} [Field K] [Ring B] [Algebra K B] {q₀ : K}
    {x₁ x₂ : B} (hx : x₂ * x₁ = q₀ ^ 2 • (x₁ * x₂)) (a b : ℕ) :
    quantumDividedPower q₀ x₂ a * quantumDividedPower q₀ x₁ b =
      q₀ ^ (2 * (a : ℤ) * b) • (quantumDividedPower q₀ x₁ b * quantumDividedPower q₀ x₂ a) := by
  rw [quantumDividedPower_def, quantumDividedPower_def, smul_mul_smul_comm, smul_mul_smul_comm,
    pow_mul_pow_of_mul_eq_smul_mul hx a b, mul_comm (quantumFactorial q₀ a)⁻¹, smul_comm]
  congr 1
  rw [← zpow_natCast (q₀ ^ 2), ← zpow_natCast q₀ 2, ← zpow_mul]
  congr 1
  push_cast
  ring

private theorem dp_comm_left {K B : Type*} [Field K] [Ring B] [Algebra K B] {q₀ : K} {m : ℕ}
    {x₂ y₁ : B} (hyx : x₂ * y₁ = q₀ ^ (1 - (m : ℤ)) • (y₁ * x₂)) (a : ℕ) :
    quantumDividedPower q₀ x₂ a * y₁ =
      q₀ ^ ((a : ℤ) * (1 - (m : ℤ))) • (y₁ * quantumDividedPower q₀ x₂ a) := by
  have h := pow_mul_pow_of_mul_eq_smul_mul hyx a 1
  rw [pow_one, mul_one] at h
  rw [quantumDividedPower_def, smul_mul_assoc, mul_smul_comm, h, smul_comm]
  congr 1
  rw [← zpow_natCast (q₀ ^ _), ← zpow_mul, mul_comm]

private theorem dp_comm_right {K B : Type*} [Field K] [Ring B] [Algebra K B] {q₀ : K} {m : ℕ}
    {x₁ y₂ : B} (hxy : y₂ * x₁ = q₀ ^ (1 - (m : ℤ)) • (x₁ * y₂)) (b : ℕ) :
    y₂ * quantumDividedPower q₀ x₁ b =
      q₀ ^ ((b : ℤ) * (1 - (m : ℤ))) • (quantumDividedPower q₀ x₁ b * y₂) := by
  have h := pow_mul_pow_of_mul_eq_smul_mul hxy 1 b
  rw [pow_one, one_mul] at h
  rw [quantumDividedPower_def, mul_smul_comm, smul_mul_assoc, h, smul_comm]
  congr 1
  rw [← zpow_natCast (q₀ ^ _), ← zpow_mul, mul_comm]

private theorem serrePoly_left_term {K B : Type*} [Field K] [Ring B] [Algebra K B]
    {q₀ : K} (hq₀ : q₀ ≠ 0) {m a₁ b₁ a₂ : ℕ} (ha₁ : a₁ ≤ m) (hb₁ : b₁ ≤ m - a₁)
    (ha₂ : a₂ ≤ m - a₁ - b₁) (hfc : quantumFactorial q₀ (m - a₁ - b₁) ≠ 0)
    {x₁ x₂ y₁ : B} (hx : x₂ * x₁ = q₀ ^ 2 • (x₁ * x₂))
    (hyx : x₂ * y₁ = q₀ ^ (1 - (m : ℤ)) • (y₁ * x₂)) :
    (-1 : K) ^ (a₁ + a₂) •
        ((q₀ ^ (a₁ * a₂) • (quantumDividedPower q₀ x₁ a₁ * quantumDividedPower q₀ x₂ a₂)) * y₁ *
          (q₀ ^ (b₁ * (m - (a₁ + a₂) - b₁)) •
            (quantumDividedPower q₀ x₁ b₁ * quantumDividedPower q₀ x₂ (m - (a₁ + a₂) - b₁)))) =
      (((-1 : K) ^ a₁ * q₀ ^ ((b₁ : ℤ) * (m - a₁ - b₁ : ℕ))) *
        ((-1 : K) ^ a₂ * q₀ ^ ((a₂ : ℤ) * (1 - ((m - a₁ - b₁ : ℕ) : ℤ))) *
          quantumBinomial q₀ (m - a₁ - b₁) a₂)) •
        (quantumDividedPower q₀ x₁ a₁ * y₁ * quantumDividedPower q₀ x₁ b₁ *
          quantumDividedPower q₀ x₂ (m - a₁ - b₁)) := by
  set c := m - a₁ - b₁
  have hsub : m - (a₁ + a₂) - b₁ = c - a₂ := by omega
  have hfc' : quantumFactorial q₀ (a₂ + (c - a₂)) ≠ 0 := by rwa [Nat.add_sub_of_le ha₂]
  rw [hsub]
  simp only [smul_mul_assoc, mul_smul_comm]
  have hmid :
      quantumDividedPower q₀ x₁ a₁ * quantumDividedPower q₀ x₂ a₂ * y₁ *
          (quantumDividedPower q₀ x₁ b₁ * quantumDividedPower q₀ x₂ (c - a₂)) =
        (q₀ ^ ((a₂ : ℤ) * (1 - (m : ℤ))) * q₀ ^ (2 * (a₂ : ℤ) * b₁) * quantumBinomial q₀ c a₂) •
          (quantumDividedPower q₀ x₁ a₁ * y₁ * quantumDividedPower q₀ x₁ b₁ *
            quantumDividedPower q₀ x₂ c) := by
    calc
      quantumDividedPower q₀ x₁ a₁ * quantumDividedPower q₀ x₂ a₂ * y₁ *
          (quantumDividedPower q₀ x₁ b₁ * quantumDividedPower q₀ x₂ (c - a₂)) =
          quantumDividedPower q₀ x₁ a₁ * (quantumDividedPower q₀ x₂ a₂ * y₁) *
            quantumDividedPower q₀ x₁ b₁ * quantumDividedPower q₀ x₂ (c - a₂) := by
        simp [mul_assoc]
      _ = q₀ ^ ((a₂ : ℤ) * (1 - (m : ℤ))) •
          (quantumDividedPower q₀ x₁ a₁ * y₁ *
            (quantumDividedPower q₀ x₂ a₂ * quantumDividedPower q₀ x₁ b₁) *
            quantumDividedPower q₀ x₂ (c - a₂)) := by
        rw [dp_comm_left hyx, mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
        simp [mul_assoc]
      _ = (q₀ ^ ((a₂ : ℤ) * (1 - (m : ℤ))) * q₀ ^ (2 * (a₂ : ℤ) * b₁)) •
          (quantumDividedPower q₀ x₁ a₁ * y₁ * quantumDividedPower q₀ x₁ b₁ *
            (quantumDividedPower q₀ x₂ a₂ * quantumDividedPower q₀ x₂ (c - a₂))) := by
        rw [dp_comm_two hx, mul_smul_comm, smul_mul_assoc, smul_smul]
        simp [mul_assoc]
      _ = _ := by
        rw [quantumDividedPower_mul_quantumDividedPower x₂ hfc', Nat.add_sub_of_le ha₂,
          mul_smul_comm, smul_smul, mul_assoc]
  rw [hmid]
  simp only [smul_smul]
  congr 1
  rw [pow_add ((-1 : K)), ← zpow_natCast q₀ (a₁ * a₂), ← zpow_natCast q₀ (b₁ * (c - a₂))]
  have hzp :
      q₀ ^ ((a₁ * a₂ : ℕ) : ℤ) * (q₀ ^ ((b₁ * (c - a₂) : ℕ) : ℤ) *
          (q₀ ^ ((a₂ : ℤ) * (1 - (m : ℤ))) * q₀ ^ (2 * (a₂ : ℤ) * b₁))) =
        q₀ ^ ((b₁ : ℤ) * c) * q₀ ^ ((a₂ : ℤ) * (1 - (c : ℤ))) := by
    rw [← mul_assoc, ← mul_assoc, ← zpow_add₀ hq₀, ← zpow_add₀ hq₀, ← zpow_add₀ hq₀,
      ← zpow_add₀ hq₀]
    congr 1
    have h1 : ((c - a₂ : ℕ) : ℤ) = (c : ℤ) - a₂ := Int.ofNat_sub ha₂
    have h2 : (m : ℤ) = a₁ + b₁ + c := by omega
    push_cast
    rw [h1, h2]
    ring
  linear_combination ((-1 : K) ^ a₁ * (-1 : K) ^ a₂ * quantumBinomial q₀ c a₂) * hzp

private theorem serrePoly_left_sum_eq_zero {K B : Type*} [Field K] [Ring B] [Algebra K B]
    {q₀ : K} (hq₀ : q₀ ≠ 0) {m : ℕ} (hm : quantumFactorial q₀ m ≠ 0)
    {x₁ x₂ y₁ : B} (hx : x₂ * x₁ = q₀ ^ 2 • (x₁ * x₂))
    (hyx : x₂ * y₁ = q₀ ^ (1 - (m : ℤ)) • (y₁ * x₂))
    (hs₁ : serrePoly q₀ m x₁ y₁ = 0) :
    (∑ r ∈ range (m + 1),
      (-1 : K) ^ r • (quantumDividedPower q₀ (x₁ + x₂) r * y₁ *
        quantumDividedPower q₀ (x₁ + x₂) (m - r))) = 0 := by
  let F : ℕ → ℕ → ℕ → B := fun a₁ b₁ a₂ =>
    (-1 : K) ^ (a₁ + a₂) •
      ((q₀ ^ (a₁ * a₂) • (quantumDividedPower q₀ x₁ a₁ * quantumDividedPower q₀ x₂ a₂)) * y₁ *
        (q₀ ^ (b₁ * (m - (a₁ + a₂) - b₁)) •
          (quantumDividedPower q₀ x₁ b₁ * quantumDividedPower q₀ x₂ (m - (a₁ + a₂) - b₁))))
  have hexp : ∀ r ∈ range (m + 1),
      (-1 : K) ^ r • (quantumDividedPower q₀ (x₁ + x₂) r * y₁ *
          quantumDividedPower q₀ (x₁ + x₂) (m - r)) =
        ∑ a₁ ∈ range (r + 1), ∑ b₁ ∈ range (m - r + 1), F a₁ b₁ (r - a₁) := by
    intro r hr
    have hrle : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
    rw [quantumDividedPower_add_of_mul_eq_smul_mul hx (quantumFactorial_ne_zero_of_le hrle hm),
      quantumDividedPower_add_of_mul_eq_smul_mul hx
        (quantumFactorial_ne_zero_of_le (Nat.sub_le m r) hm),
      sum_mul, sum_mul, smul_sum]
    refine sum_congr rfl fun a₁ ha₁ => ?_
    have ha₁le : a₁ ≤ r := Nat.lt_succ_iff.mp (mem_range.mp ha₁)
    rw [mul_sum, smul_sum]
    refine sum_congr rfl fun b₁ _ => ?_
    dsimp only [F]
    rw [Nat.add_sub_of_le ha₁le]
  rw [sum_congr rfl hexp, sum_triple_reindex_left m F]
  have hinner : ∀ a₁ ∈ range (m + 1),
      (∑ b₁ ∈ range (m - a₁ + 1), ∑ a₂ ∈ range (m - a₁ - b₁ + 1), F a₁ b₁ a₂) =
        (-1 : K) ^ a₁ •
          (quantumDividedPower q₀ x₁ a₁ * y₁ * quantumDividedPower q₀ x₁ (m - a₁)) := by
    intro a₁ ha₁
    have ha₁le : a₁ ≤ m := Nat.lt_succ_iff.mp (mem_range.mp ha₁)
    have hb_eq : ∀ b₁ ∈ range (m - a₁ + 1),
        (∑ a₂ ∈ range (m - a₁ - b₁ + 1), F a₁ b₁ a₂) =
          if b₁ = m - a₁ then
            (-1 : K) ^ a₁ •
              (quantumDividedPower q₀ x₁ a₁ * y₁ * quantumDividedPower q₀ x₁ (m - a₁))
          else 0 := by
      intro b₁ hb₁
      have hb₁le : b₁ ≤ m - a₁ := Nat.lt_succ_iff.mp (mem_range.mp hb₁)
      have hfc : quantumFactorial q₀ (m - a₁ - b₁) ≠ 0 :=
        quantumFactorial_ne_zero_of_le (by omega) hm
      rw [sum_congr rfl fun a₂ ha₂ => serrePoly_left_term hq₀ ha₁le hb₁le
        (Nat.lt_succ_iff.mp (mem_range.mp ha₂)) hfc hx hyx, ← sum_smul]
      by_cases hbc : b₁ = m - a₁
      · subst hbc; simp
      · have hc_pos : 0 < m - a₁ - b₁ := by omega
        simp only [hbc, ↓reduceIte]
        rw [← mul_sum, sum_neg_one_pow_mul_zpow_mul_quantumBinomial hq₀ hc_pos, mul_zero,
          zero_smul]
    rw [sum_congr rfl hb_eq, sum_ite_eq']
    simp only [mem_range, Nat.lt_succ_self, ↓reduceIte]
  rw [sum_congr rfl hinner]
  exact hs₁

private theorem serrePoly_right_term {K B : Type*} [Field K] [Ring B] [Algebra K B]
    {q₀ : K} (hq₀ : q₀ ≠ 0) {m a₂ b₂ a₁ : ℕ} (ha₂ : a₂ ≤ m) (hb₂ : b₂ ≤ m - a₂)
    (ha₁ : a₁ ≤ m - a₂ - b₂) (hfd : quantumFactorial q₀ (m - a₂ - b₂) ≠ 0)
    {x₁ x₂ y₂ : B} (hx : x₂ * x₁ = q₀ ^ 2 • (x₁ * x₂))
    (hxy : y₂ * x₁ = q₀ ^ (1 - (m : ℤ)) • (x₁ * y₂)) :
    (-1 : K) ^ (a₁ + a₂) •
        ((q₀ ^ (a₁ * a₂) • (quantumDividedPower q₀ x₁ a₁ * quantumDividedPower q₀ x₂ a₂)) * y₂ *
          (q₀ ^ ((m - a₁ - a₂ - b₂) * b₂) •
            (quantumDividedPower q₀ x₁ (m - a₁ - a₂ - b₂) * quantumDividedPower q₀ x₂ b₂))) =
      (((-1 : K) ^ a₂ *
          q₀ ^ (((m - a₂ - b₂ : ℕ) : ℤ) * b₂ + ((m - a₂ - b₂ : ℕ) : ℤ) * (1 - (m : ℤ)) +
            2 * (a₂ : ℤ) * (m - a₂ - b₂ : ℕ))) *
        ((-1 : K) ^ a₁ * (q₀⁻¹) ^ ((a₁ : ℤ) * (1 - ((m - a₂ - b₂ : ℕ) : ℤ))) *
          quantumBinomial q₀⁻¹ (m - a₂ - b₂) a₁)) •
        (quantumDividedPower q₀ x₁ (m - a₂ - b₂) *
          (quantumDividedPower q₀ x₂ a₂ * y₂ * quantumDividedPower q₀ x₂ b₂)) := by
  set d := m - a₂ - b₂
  have hsub : m - a₁ - a₂ - b₂ = d - a₁ := by omega
  have hfd' : quantumFactorial q₀ (a₁ + (d - a₁)) ≠ 0 := by rwa [Nat.add_sub_of_le ha₁]
  rw [hsub]
  simp only [smul_mul_assoc, mul_smul_comm]
  have hmid :
      quantumDividedPower q₀ x₁ a₁ * quantumDividedPower q₀ x₂ a₂ * y₂ *
          (quantumDividedPower q₀ x₁ (d - a₁) * quantumDividedPower q₀ x₂ b₂) =
        (q₀ ^ (((d - a₁ : ℕ) : ℤ) * (1 - (m : ℤ))) *
            q₀ ^ (2 * (a₂ : ℤ) * (d - a₁ : ℕ)) * quantumBinomial q₀ d a₁) •
          (quantumDividedPower q₀ x₁ d *
            (quantumDividedPower q₀ x₂ a₂ * y₂ * quantumDividedPower q₀ x₂ b₂)) := by
    calc
      quantumDividedPower q₀ x₁ a₁ * quantumDividedPower q₀ x₂ a₂ * y₂ *
          (quantumDividedPower q₀ x₁ (d - a₁) * quantumDividedPower q₀ x₂ b₂) =
          quantumDividedPower q₀ x₁ a₁ * quantumDividedPower q₀ x₂ a₂ *
            (y₂ * quantumDividedPower q₀ x₁ (d - a₁)) * quantumDividedPower q₀ x₂ b₂ := by
        simp [mul_assoc]
      _ = q₀ ^ (((d - a₁ : ℕ) : ℤ) * (1 - (m : ℤ))) •
          (quantumDividedPower q₀ x₁ a₁ *
            (quantumDividedPower q₀ x₂ a₂ * quantumDividedPower q₀ x₁ (d - a₁)) *
            y₂ * quantumDividedPower q₀ x₂ b₂) := by
        rw [dp_comm_right hxy, mul_smul_comm, smul_mul_assoc]
        simp [mul_assoc]
      _ = (q₀ ^ (((d - a₁ : ℕ) : ℤ) * (1 - (m : ℤ))) *
            q₀ ^ (2 * (a₂ : ℤ) * (d - a₁ : ℕ))) •
          ((quantumDividedPower q₀ x₁ a₁ * quantumDividedPower q₀ x₁ (d - a₁)) *
            (quantumDividedPower q₀ x₂ a₂ * y₂ * quantumDividedPower q₀ x₂ b₂)) := by
        rw [dp_comm_two hx, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_smul]
        simp [mul_assoc]
      _ = _ := by
        rw [quantumDividedPower_mul_quantumDividedPower x₁ hfd', Nat.add_sub_of_le ha₁,
          smul_mul_assoc, smul_smul, mul_assoc]
  rw [hmid, quantumBinomial_inv]
  simp only [smul_smul]
  congr 1
  rw [pow_add ((-1 : K)), ← zpow_natCast q₀ (a₁ * a₂), ← zpow_natCast q₀ ((d - a₁) * b₂),
    inv_zpow, ← zpow_neg]
  have hzp :
      q₀ ^ ((a₁ * a₂ : ℕ) : ℤ) * (q₀ ^ (((d - a₁) * b₂ : ℕ) : ℤ) *
          (q₀ ^ (((d - a₁ : ℕ) : ℤ) * (1 - (m : ℤ))) * q₀ ^ (2 * (a₂ : ℤ) * (d - a₁ : ℕ)))) =
        q₀ ^ ((d : ℤ) * b₂ + (d : ℤ) * (1 - (m : ℤ)) + 2 * (a₂ : ℤ) * d) *
          q₀ ^ (-((a₁ : ℤ) * (1 - (d : ℤ)))) := by
    rw [← mul_assoc, ← mul_assoc, ← zpow_add₀ hq₀, ← zpow_add₀ hq₀, ← zpow_add₀ hq₀,
      ← zpow_add₀ hq₀]
    congr 1
    have h1 : ((d - a₁ : ℕ) : ℤ) = (d : ℤ) - a₁ := Int.ofNat_sub ha₁
    have h2 : (m : ℤ) = a₂ + b₂ + d := by omega
    push_cast
    rw [h1, h2]
    ring
  linear_combination ((-1 : K) ^ a₁ * (-1 : K) ^ a₂ * quantumBinomial q₀ d a₁) * hzp

private theorem serrePoly_right_sum_eq_zero {K B : Type*} [Field K] [Ring B] [Algebra K B]
    {q₀ : K} (hq₀ : q₀ ≠ 0) {m : ℕ} (hm : quantumFactorial q₀ m ≠ 0)
    {x₁ x₂ y₂ : B} (hx : x₂ * x₁ = q₀ ^ 2 • (x₁ * x₂))
    (hxy : y₂ * x₁ = q₀ ^ (1 - (m : ℤ)) • (x₁ * y₂))
    (hs₂ : serrePoly q₀ m x₂ y₂ = 0) :
    (∑ r ∈ range (m + 1),
      (-1 : K) ^ r • (quantumDividedPower q₀ (x₁ + x₂) r * y₂ *
        quantumDividedPower q₀ (x₁ + x₂) (m - r))) = 0 := by
  let G : ℕ → ℕ → ℕ → B := fun a₂ b₂ a₁ =>
    (-1 : K) ^ (a₁ + a₂) •
      ((q₀ ^ (a₁ * a₂) • (quantumDividedPower q₀ x₁ a₁ * quantumDividedPower q₀ x₂ a₂)) * y₂ *
        (q₀ ^ ((m - a₁ - a₂ - b₂) * b₂) •
          (quantumDividedPower q₀ x₁ (m - a₁ - a₂ - b₂) * quantumDividedPower q₀ x₂ b₂)))
  have hexp : ∀ r ∈ range (m + 1),
      (-1 : K) ^ r • (quantumDividedPower q₀ (x₁ + x₂) r * y₂ *
          quantumDividedPower q₀ (x₁ + x₂) (m - r)) =
        ∑ a₁ ∈ range (r + 1), ∑ b₁ ∈ range (m - r + 1), G (r - a₁) (m - r - b₁) a₁ := by
    intro r hr
    have hrle : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
    rw [quantumDividedPower_add_of_mul_eq_smul_mul hx (quantumFactorial_ne_zero_of_le hrle hm),
      quantumDividedPower_add_of_mul_eq_smul_mul hx
        (quantumFactorial_ne_zero_of_le (Nat.sub_le m r) hm),
      sum_mul, sum_mul, smul_sum]
    refine sum_congr rfl fun a₁ ha₁ => ?_
    have ha₁le : a₁ ≤ r := Nat.lt_succ_iff.mp (mem_range.mp ha₁)
    rw [mul_sum, smul_sum]
    refine sum_congr rfl fun b₁ hb₁ => ?_
    have hb₁le : b₁ ≤ m - r := Nat.lt_succ_iff.mp (mem_range.mp hb₁)
    dsimp only [G]
    have hsub1 : a₁ + (r - a₁) = r := by omega
    have hsub2 : m - a₁ - (r - a₁) - (m - r - b₁) = b₁ := by omega
    rw [hsub1, hsub2]
  rw [sum_congr rfl hexp, sum_triple_reindex_right m G]
  have hinner : ∀ a₂ ∈ range (m + 1),
      (∑ b₂ ∈ range (m - a₂ + 1), ∑ a₁ ∈ range (m - a₂ - b₂ + 1), G a₂ b₂ a₁) =
        (-1 : K) ^ a₂ •
          (quantumDividedPower q₀ x₂ a₂ * y₂ * quantumDividedPower q₀ x₂ (m - a₂)) := by
    intro a₂ ha₂
    have ha₂le : a₂ ≤ m := Nat.lt_succ_iff.mp (mem_range.mp ha₂)
    have hb_eq : ∀ b₂ ∈ range (m - a₂ + 1),
        (∑ a₁ ∈ range (m - a₂ - b₂ + 1), G a₂ b₂ a₁) =
          if b₂ = m - a₂ then
            (-1 : K) ^ a₂ •
              (quantumDividedPower q₀ x₂ a₂ * y₂ * quantumDividedPower q₀ x₂ (m - a₂))
          else 0 := by
      intro b₂ hb₂
      have hb₂le : b₂ ≤ m - a₂ := Nat.lt_succ_iff.mp (mem_range.mp hb₂)
      have hfd : quantumFactorial q₀ (m - a₂ - b₂) ≠ 0 :=
        quantumFactorial_ne_zero_of_le (by omega) hm
      rw [sum_congr rfl fun a₁ ha₁ => serrePoly_right_term hq₀ ha₂le hb₂le
        (Nat.lt_succ_iff.mp (mem_range.mp ha₁)) hfd hx hxy, ← sum_smul]
      by_cases hbd : b₂ = m - a₂
      · subst hbd; simp
      · have hd_pos : 0 < m - a₂ - b₂ := by omega
        simp only [hbd, ↓reduceIte]
        rw [← mul_sum,
          sum_neg_one_pow_mul_zpow_mul_quantumBinomial (inv_ne_zero hq₀) hd_pos,
          mul_zero, zero_smul]
    rw [sum_congr rfl hb_eq, sum_ite_eq']
    simp only [mem_range, Nat.lt_succ_self, ↓reduceIte]
  rw [sum_congr rfl hinner]
  exact hs₂

private theorem serrePoly_add_eq_zero {K B : Type*} [Field K] [Ring B] [Algebra K B]
    {q₀ : K} (hq₀ : q₀ ≠ 0) {m : ℕ} (hm : quantumFactorial q₀ m ≠ 0)
    {x₁ x₂ y₁ y₂ : B} (hx : x₂ * x₁ = q₀ ^ 2 • (x₁ * x₂))
    (hyx : x₂ * y₁ = q₀ ^ (1 - (m : ℤ)) • (y₁ * x₂))
    (hxy : y₂ * x₁ = q₀ ^ (1 - (m : ℤ)) • (x₁ * y₂))
    (hs₁ : serrePoly q₀ m x₁ y₁ = 0) (hs₂ : serrePoly q₀ m x₂ y₂ = 0) :
    serrePoly q₀ m (x₁ + x₂) (y₁ + y₂) = 0 := by
  have hsplit : serrePoly q₀ m (x₁ + x₂) (y₁ + y₂) =
      (∑ r ∈ range (m + 1),
        (-1 : K) ^ r • (quantumDividedPower q₀ (x₁ + x₂) r * y₁ *
          quantumDividedPower q₀ (x₁ + x₂) (m - r))) +
      (∑ r ∈ range (m + 1),
        (-1 : K) ^ r • (quantumDividedPower q₀ (x₁ + x₂) r * y₂ *
          quantumDividedPower q₀ (x₁ + x₂) (m - r))) := by
    rw [serrePoly, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_add, add_mul, smul_add]
  rw [hsplit, serrePoly_left_sum_eq_zero hq₀ hm hx hyx hs₁,
    serrePoly_right_sum_eq_zero hq₀ hm hx hxy hs₂, add_zero]

end SerreSkewPrimitive

/-! ### Coproduct and bialgebra structure -/

section Bialgebra

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

private theorem serreElement_eq_serrePoly {B : Type*} [Ring B] [Algebra K B]
    (x : ι → B) (i j : ι) :
    serreElement D q x i j = serrePoly (q ^ D.symmetrizer i) (serreLength D i j) (x i) (x j) := by
  rw [serreElement_def, serrePoly]

private theorem tmul_quantumDividedPower_left (q₀ : K)
    (x : QuantizedEnvelopingAlgebra D q) (n : ℕ) :
    quantumDividedPower q₀ (x ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) n =
      quantumDividedPower q₀ x n ⊗ₜ[K] 1 := by
  rw [quantumDividedPower_def, Algebra.TensorProduct.tmul_pow, one_pow,
    TensorProduct.smul_tmul', ← quantumDividedPower_def]

private theorem tmul_quantumDividedPower_right_unit (q₀ : K) (y : Y)
    (x : QuantizedEnvelopingAlgebra D q) (n : ℕ) :
    quantumDividedPower q₀ (k D q y ⊗ₜ[K] x) n =
      (k D q y ^ n) ⊗ₜ[K] quantumDividedPower q₀ x n := by
  rw [quantumDividedPower_def, Algebra.TensorProduct.tmul_pow, ← TensorProduct.tmul_smul,
    ← quantumDividedPower_def]

private theorem tmul_quantumDividedPower_left_unit (q₀ : K)
    (x : QuantizedEnvelopingAlgebra D q) (y : Y) (n : ℕ) :
    quantumDividedPower q₀ (x ⊗ₜ[K] k D q y) n =
      quantumDividedPower q₀ x n ⊗ₜ[K] (k D q y ^ n) := by
  rw [quantumDividedPower_def, Algebra.TensorProduct.tmul_pow, TensorProduct.smul_tmul',
    ← quantumDividedPower_def]

variable [Fact (IsGenericQuantumParameter q)]

private theorem qi_generic (i : ι) : IsGenericQuantumParameter (q ^ D.symmetrizer i) :=
  (Fact.out : IsGenericQuantumParameter q).pow (D.symmetrizer_pos i)

private theorem qi_ne_zero (i : ι) : q ^ D.symmetrizer i ≠ 0 :=
  (qi_generic D q i).ne_zero

private noncomputable def comulTuple :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q) where
  e i := e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i
  f i := f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i
  k y := k D q y ⊗ₜ[K] k D q y
  k_zero := by simp [Algebra.TensorProduct.one_def]
  k_mul_k y z := by simp [Algebra.TensorProduct.tmul_mul_tmul]
  k_mul_e_mul_k_neg y i := by
    simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      k_mul_e_mul_k_neg, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
    simp [add_comm y, add_neg_cancel_right]
  k_mul_f_mul_k_neg y i := by
    simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      k_mul_f_mul_k_neg, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
    simp [add_comm y, add_neg_cancel_right]
  e_mul_f_sub_f_mul_e_self i := by
    have hqi : q ^ D.symmetrizer i ≠ 0 := qi_ne_zero D q i
    simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [simpleK_mul_f, e_mul_simpleKInv, D.cartan_apply_self]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, zpow_neg,
      mul_inv_cancel₀ (zpow_ne_zero 2 hqi), one_smul]
    calc
      _ = (e D q i * f D q i - f D q i * e D q i) ⊗ₜ[K] simpleKInv D q i +
            simpleK D q i ⊗ₜ[K] (e D q i * f D q i - f D q i * e D q i) := by
        simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
        abel
      _ = _ := by
        rw [e_mul_f_sub_f_mul_e_self]
        simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.sub_tmul,
          TensorProduct.tmul_sub, smul_sub]
        module
  e_mul_f_of_ne {i j} hij := by
    have hq0 : q ≠ 0 := (Fact.out : IsGenericQuantumParameter q).ne_zero
    simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e_mul_f_of_ne D q hij, k_mul_f D q (D.simpleTorus i) j,
      e_mul_k D q i (-D.simpleTorus j)]
    have hexp :
        q ^ (-D.pairing (D.root i) (-D.simpleTorus j)) *
          q ^ (-D.pairing (D.root j) (D.simpleTorus i)) = 1 := by
      rw [map_neg, neg_neg, D.pairing_root_simpleTorus, D.pairing_root_simpleTorus,
        D.symmetrizer_mul_cartan j i, ← zpow_add₀ hq0, add_neg_cancel, zpow_zero]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
    rw [hexp, one_smul]
    abel
  serre_e {i j} hij := by
    rw [serreElement_eq_serrePoly]
    refine serrePoly_add_eq_zero (qi_ne_zero D q i)
      (quantumFactorial_ne_zero (qi_generic D q i) _) ?_ ?_ ?_ ?_ ?_
    · simp [Algebra.TensorProduct.tmul_mul_tmul, simpleK_mul_e, TensorProduct.smul_tmul']
    · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_one, k_mul_e, D.pairing_root_simpleTorus, D.symmetrizer_mul_cartan j i,
        ← one_sub_serreLength D hij, ← zpow_natCast, zpow_mul, TensorProduct.smul_tmul']
    · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul, simpleK_mul_e, ← one_sub_serreLength D hij, TensorProduct.smul_tmul']
    · have hleft :
          serrePoly (q ^ D.symmetrizer i) (serreLength D i j)
              (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) (e D q j ⊗ₜ[K] 1) =
            serreElement D q (e D q) i j ⊗ₜ[K] 1 := by
        rw [serrePoly, serreElement_def, TensorProduct.sum_tmul]
        refine sum_congr rfl fun r _ => ?_
        simp only [tmul_quantumDividedPower_left, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          TensorProduct.smul_tmul']
      rw [hleft, serre_e D q hij, TensorProduct.zero_tmul]
    · have hright :
          serrePoly (q ^ D.symmetrizer i) (serreLength D i j)
              (simpleK D q i ⊗ₜ[K] e D q i) (simpleK D q j ⊗ₜ[K] e D q j) =
            (simpleK D q i ^ serreLength D i j * simpleK D q j) ⊗ₜ[K]
              serreElement D q (e D q) i j := by
        rw [serrePoly, serreElement_def, TensorProduct.tmul_sum]
        refine sum_congr rfl fun r hr => ?_
        have hle : r ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp hr)
        simp only [tmul_quantumDividedPower_right_unit, Algebra.TensorProduct.tmul_mul_tmul,
          TensorProduct.tmul_smul]
        congr 1
        simp only [k_pow, k_mul_k]
        congr 1
        rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hle]
      rw [hright, serre_e D q hij, TensorProduct.tmul_zero]
  serre_f {i j} hij := by
    rw [serreElement_eq_serrePoly, add_comm (f D q i ⊗ₜ[K] simpleKInv D q i),
      add_comm (f D q j ⊗ₜ[K] simpleKInv D q j)]
    refine serrePoly_add_eq_zero (qi_ne_zero D q i)
      (quantumFactorial_ne_zero (qi_generic D q i) _) ?_ ?_ ?_ ?_ ?_
    · simp [Algebra.TensorProduct.tmul_mul_tmul, simpleKInv_mul_f, TensorProduct.tmul_smul]
    · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul, k_mul_f, map_neg, neg_neg, D.pairing_root_simpleTorus,
        D.symmetrizer_mul_cartan j i, ← one_sub_serreLength D hij, ← zpow_natCast, zpow_mul,
        TensorProduct.tmul_smul]
    · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul, simpleKInv_mul_f, ← one_sub_serreLength D hij, TensorProduct.tmul_smul]
    · have hleft :
          serrePoly (q ^ D.symmetrizer i) (serreLength D i j)
              ((1 : QuantizedEnvelopingAlgebra D q) ⊗ₜ[K] f D q i) (1 ⊗ₜ[K] f D q j) =
            (1 : QuantizedEnvelopingAlgebra D q) ⊗ₜ[K] serreElement D q (f D q) i j := by
        rw [serrePoly, serreElement_def, TensorProduct.tmul_sum]
        refine sum_congr rfl fun r _ => ?_
        have h1 : ∀ n,
            quantumDividedPower (q ^ D.symmetrizer i)
                ((1 : QuantizedEnvelopingAlgebra D q) ⊗ₜ[K] f D q i) n =
              (1 : QuantizedEnvelopingAlgebra D q) ⊗ₜ[K]
                quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n := by
          intro n
          rw [← k_zero D q, tmul_quantumDividedPower_right_unit, k_zero, one_pow]
        simp only [h1, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_smul]
      rw [hleft, serre_f D q hij, TensorProduct.tmul_zero]
    · have hright :
          serrePoly (q ^ D.symmetrizer i) (serreLength D i j)
              (f D q i ⊗ₜ[K] simpleKInv D q i) (f D q j ⊗ₜ[K] simpleKInv D q j) =
            serreElement D q (f D q) i j ⊗ₜ[K]
              (simpleKInv D q i ^ serreLength D i j * simpleKInv D q j) := by
        rw [serrePoly, serreElement_def, TensorProduct.sum_tmul]
        refine sum_congr rfl fun r hr => ?_
        have hle : r ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp hr)
        simp only [tmul_quantumDividedPower_left_unit, Algebra.TensorProduct.tmul_mul_tmul,
          TensorProduct.smul_tmul']
        congr 1
        simp only [k_pow, k_mul_k]
        congr 1
        rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hle]
      rw [hright, serre_f D q hij, TensorProduct.zero_tmul]

/-- The coproduct `Δ : U →ₐ[K] U ⊗[K] U` with `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`,
`Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`, and `Δ(K_y) = K_y ⊗ K_y`. -/
noncomputable def comul :
    QuantizedEnvelopingAlgebra D q →ₐ[K]
      QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q :=
  lift (comulTuple D q)

@[local simp]
private theorem comul_eAux (i : ι) :
    comul D q (e D q i) = e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i :=
  lift_e _ i

@[local simp]
private theorem comul_fAux (i : ι) :
    comul D q (f D q i) = f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i :=
  lift_f _ i

@[local simp]
private theorem comul_kAux (y : Y) :
    comul D q (k D q y) = k D q y ⊗ₜ[K] k D q y :=
  lift_k _ y

/-- The Drinfeld–Jimbo bialgebra structure on `QuantizedEnvelopingAlgebra D q`. -/
noncomputable instance instBialgebra : Bialgebra K (QuantizedEnvelopingAlgebra D q) :=
  Bialgebra.ofAlgHom (comul D q) (counit D q)
    (by
      ext <;>
        simp [TensorProduct.tmul_add, TensorProduct.add_tmul, add_assoc,
          Algebra.TensorProduct.one_def])
    (by ext <;> simp)
    (by ext <;> simp)

/-- `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`. -/
@[simp]
theorem comul_e (i : ι) :
    Coalgebra.comul (R := K) (e D q i) =
      e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i :=
  comul_eAux D q i

/-- `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`. -/
@[simp]
theorem comul_f (i : ι) :
    Coalgebra.comul (R := K) (f D q i) =
      f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i :=
  comul_fAux D q i

/-- `Δ(K_y) = K_y ⊗ K_y`. -/
@[simp]
theorem comul_k (y : Y) :
    Coalgebra.comul (R := K) (k D q y) = k D q y ⊗ₜ[K] k D q y :=
  comul_kAux D q y

/-- `ε(Eᵢ) = 0`. -/
@[simp]
theorem counit_e (i : ι) : Coalgebra.counit (R := K) (e D q i) = 0 :=
  counit_apply_e D q i

/-- `ε(Fᵢ) = 0`. -/
@[simp]
theorem counit_f (i : ι) : Coalgebra.counit (R := K) (f D q i) = 0 :=
  counit_apply_f D q i

/-- `ε(K_y) = 1`. -/
@[simp]
theorem counit_k (y : Y) : Coalgebra.counit (R := K) (k D q y) = 1 :=
  counit_apply_k D q y

/-- Every toral element `K_y` is group-like. -/
theorem isGroupLikeElem_k (y : Y) : IsGroupLikeElem K (k D q y) :=
  ⟨counit_k D q y, comul_k D q y⟩

/-- `comul D q` agrees with `Coalgebra.comul`. -/
@[simp]
theorem comul_apply (x : QuantizedEnvelopingAlgebra D q) :
    comul D q x = Coalgebra.comul x := (rfl)

/-- `counit D q` agrees with `Coalgebra.counit`. -/
@[simp]
theorem counit_apply (x : QuantizedEnvelopingAlgebra D q) :
    counit D q x = Coalgebra.counit x := (rfl)

/-! ### Coproducts of quantum divided powers -/

/-- Coproduct of a raising divided power:
`Δ(Eᵢ^(n)) = ∑_{a = 0}^n qᵢ^(a(n - a)) • (Eᵢ^(a) Kᵢ^(n - a) ⊗ Eᵢ^(n - a))`. -/
theorem comul_quantumDividedPower_e (i : ι) (n : ℕ) :
    Coalgebra.comul (R := K) (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      ∑ a ∈ range (n + 1),
        (q ^ D.symmetrizer i) ^ (a * (n - a)) •
          ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a * simpleK D q i ^ (n - a)) ⊗ₜ[K]
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (n - a)) := by
  have hx :
      (simpleK D q i ⊗ₜ[K] e D q i) * (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) =
        (q ^ D.symmetrizer i) ^ 2 •
          ((e D q i ⊗ₜ[K] 1) * (simpleK D q i ⊗ₜ[K] e D q i)) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul, simpleK_mul_e, TensorProduct.smul_tmul']
  rw [← comul_apply, AlgHom.map_quantumDividedPower, comul_apply, comul_e,
    quantumDividedPower_add_of_mul_eq_smul_mul hx
      (quantumFactorial_ne_zero (qi_generic D q i) n)]
  refine sum_congr rfl fun a _ => ?_
  simp only [tmul_quantumDividedPower_left, tmul_quantumDividedPower_right_unit,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- Coproduct of a lowering divided power:
`Δ(Fᵢ^(n)) = ∑_{a = 0}^n qᵢ^(a(n - a)) • (Fᵢ^(a) ⊗ Fᵢ^(n - a) Kᵢ^(-a))`. -/
theorem comul_quantumDividedPower_f (i : ι) (n : ℕ) :
    Coalgebra.comul (R := K) (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
      ∑ a ∈ range (n + 1),
        (q ^ D.symmetrizer i) ^ (a * (n - a)) •
          (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) a ⊗ₜ[K]
            (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) (n - a) *
              simpleKInv D q i ^ a)) := by
  have hx :
      (f D q i ⊗ₜ[K] simpleKInv D q i) * ((1 : QuantizedEnvelopingAlgebra D q) ⊗ₜ[K] f D q i) =
        (q ^ D.symmetrizer i) ^ 2 •
          ((1 ⊗ₜ[K] f D q i) * (f D q i ⊗ₜ[K] simpleKInv D q i)) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul, simpleKInv_mul_f, TensorProduct.tmul_smul]
  have h1 : ∀ m,
      quantumDividedPower (q ^ D.symmetrizer i)
          ((1 : QuantizedEnvelopingAlgebra D q) ⊗ₜ[K] f D q i) m =
        (1 : QuantizedEnvelopingAlgebra D q) ⊗ₜ[K]
          quantumDividedPower (q ^ D.symmetrizer i) (f D q i) m := by
    intro m
    rw [← k_zero D q, tmul_quantumDividedPower_right_unit, k_zero, one_pow]
  rw [← comul_apply, AlgHom.map_quantumDividedPower, comul_apply, comul_f, add_comm,
    quantumDividedPower_add_of_mul_eq_smul_mul hx
      (quantumFactorial_ne_zero (qi_generic D q i) n),
    ← sum_range_reflect]
  simp only [Nat.add_succ_sub_one, add_zero]
  refine sum_congr rfl fun a ha => ?_
  have hle : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
  rw [Nat.sub_sub_self hle, mul_comm (n - a) a]
  simp only [h1, tmul_quantumDividedPower_left_unit, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end Bialgebra

/-! ### Functoriality, rescaling, and empty-datum bialgebra morphisms -/

section BialgMorphism

variable {ι X X' X'' Y Y' Y'' K : Type*}
  [AddCommGroup X] [AddCommGroup X'] [AddCommGroup X'']
  [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup Y'']
  [Field K]
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} {D'' : CartanDatum ι X'' Y''}
  (q : K) [Fact (IsGenericQuantumParameter q)]

/-- A morphism of Cartan data induces a bialgebra homomorphism on quantized enveloping algebras. -/
noncomputable def mapBialgHom (φ : CartanDatum.Hom D D') :
    QuantizedEnvelopingAlgebra D q →ₐc[K] QuantizedEnvelopingAlgebra D' q :=
  BialgHom.ofAlgHom (map q φ) (by ext <;> simp) (by ext <;> simp)

@[simp]
theorem mapBialgHom_toAlgHom (φ : CartanDatum.Hom D D') :
    (mapBialgHom q φ : QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q) =
      map q φ := (rfl)

@[simp]
theorem mapBialgHom_apply (φ : CartanDatum.Hom D D') (x : QuantizedEnvelopingAlgebra D q) :
    mapBialgHom q φ x = map q φ x := (rfl)

@[simp]
theorem mapBialgHom_id (D : CartanDatum ι X Y) :
    mapBialgHom q (CartanDatum.Hom.id D) = BialgHom.id K (QuantizedEnvelopingAlgebra D q) :=
  BialgHom.coe_toAlgHom_injective (map_id D q)

theorem mapBialgHom_comp (ψ : CartanDatum.Hom D' D'') (φ : CartanDatum.Hom D D') :
    mapBialgHom q (ψ.comp φ) = (mapBialgHom q ψ).comp (mapBialgHom q φ) :=
  BialgHom.coe_toAlgHom_injective (map_comp q ψ φ)

variable (D)

/-- Diagonal rescaling `(Eᵢ ↦ cᵢ Eᵢ, Fᵢ ↦ cᵢ⁻¹ Fᵢ, K_y ↦ K_y)` as a bialgebra equivalence. -/
noncomputable def rescaleBialgEquiv (c : ι → Kˣ) :
    QuantizedEnvelopingAlgebra D q ≃ₐc[K] QuantizedEnvelopingAlgebra D q :=
  BialgEquiv.ofAlgEquiv (rescale D q c)
    (by ext <;> simp)
    (by
      ext <;>
        simp [smul_add, TensorProduct.smul_tmul', TensorProduct.tmul_smul])

@[simp]
theorem rescaleBialgEquiv_apply (c : ι → Kˣ) (x : QuantizedEnvelopingAlgebra D q) :
    rescaleBialgEquiv D q c x = rescale D q c x := (rfl)

@[simp]
theorem rescaleBialgEquiv_symm (c : ι → Kˣ) :
    (rescaleBialgEquiv D q c).symm = rescaleBialgEquiv D q c⁻¹ := by
  ext x
  exact AlgEquiv.congr_fun (rescale_symm c) x

/-- When `ι` is empty, `torusEquiv` upgrades to a bialgebra isomorphism with the group algebra
`AddMonoidAlgebra K Y`. -/
noncomputable def torusBialgEquiv [IsEmpty ι] :
    QuantizedEnvelopingAlgebra D q ≃ₐc[K] AddMonoidAlgebra K Y :=
  BialgEquiv.ofAlgEquiv (torusEquiv D q)
    (by
      ext i
      · exact isEmptyElim i
      · exact isEmptyElim i
      · simp)
    (by
      ext i
      · exact isEmptyElim i
      · exact isEmptyElim i
      · simp)

@[simp]
theorem torusBialgEquiv_apply [IsEmpty ι] (x : QuantizedEnvelopingAlgebra D q) :
    torusBialgEquiv D q x = torusEquiv D q x := (rfl)

end BialgMorphism

/-! ### Concrete checks -/

section Checks

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K) [Fact (IsGenericQuantumParameter q)]

/-- Check on `Δ(Eᵢ^(2))`: the `a = 1` middle term has coefficient `qᵢ` (not `1` and not `qᵢ⁻¹`). -/
example (i : ι) :
    Coalgebra.comul (R := K) (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) 2) =
      ((simpleK D q i ^ 2) ⊗ₜ[K] quantumDividedPower (q ^ D.symmetrizer i) (e D q i) 2) +
        (q ^ D.symmetrizer i) • ((e D q i * simpleK D q i) ⊗ₜ[K] e D q i) +
        (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) 2 ⊗ₜ[K] 1) := by
  rw [comul_quantumDividedPower_e, sum_range_succ, sum_range_succ, sum_range_one]
  simp [add_assoc, quantumDividedPower_one (qi_generic D q i).sub_inv_ne_zero]

end Checks

end TauCeti.QuantizedEnvelopingAlgebra
