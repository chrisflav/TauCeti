/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import TauCeti.Probability.FreeProbability.Cumulant.Cyclic
public import TauCeti.Probability.FreeProbability.RDiagonal.Basic
import TauCeti.Data.Fin.Basic
import TauCeti.Probability.FreeProbability.Cumulant.Product

/-!
# Haar unitary elements and their free cumulants

An element `u` of a star-equipped `R`-module and semiring `A` is a **Haar unitary** with respect to
a linear functional `φ : A →ₗ[R] R` if `u ∈ unitary A`, `φ 1 = 1`, and every nonzero integer power
of `u` in the unitary group `unitary A` has expectation zero (`φ (u ^ k) = 0` for `k : ℤ`, `k ≠ 0`).
Equivalently, `u ∈ unitary A`, `φ 1 = 1`, and `φ (u ^ n) = φ (star u ^ n) = 0` for every positive
natural number `n`. Neither positivity nor traciality of `φ` is assumed; the connection with the
circle-valued spectral law in C⋆-probability spaces is proved in
`TauCeti.Probability.FreeProbability.HaarUnitary.Law`.

Over any commutative ring `R`, a Haar unitary satisfies two structural properties:

* **R-diagonality** (`TauCeti.IsHaarUnitary.isRDiagonal`, `TauCeti.isHaarUnitary_iff_isRDiagonal`):
  a unitary element is a Haar unitary if and only if it is R-diagonal (its joint cumulants in
  `u, star u` vanish outside nonempty even alternating words).
* **Signed Catalan alternating cumulants** (`TauCeti.IsHaarUnitary.rDiagonalDeterminingSequence`,
  `TauCeti.IsHaarUnitary.freeCumulant_rDiagonalWord`): both R-diagonal determining sequences equal
  `(-1) ^ n * catalan n` at index `n`, i.e., in even degree `2 * n` both alternating free cumulants
  `κ_{2n}(u, u⋆, …, u, u⋆)` and `κ_{2n}(u⋆, u, …, u⋆, u)` equal `(-1) ^ (n - 1) * catalan (n - 1)`
  (including `n = 0`, where both sides equal `1`).

## Main declarations

* `TauCeti.IsHaarUnitary φ u`: `u ∈ unitary A`, `φ 1 = 1`, and `φ (u ^ k) = 0` for all nonzero
  `k : ℤ`.
* `TauCeti.isHaarUnitary_iff_apply_zpow` and `TauCeti.isHaarUnitary_iff_apply_pow`: moment
  characterizations in terms of integer powers and positive natural powers of `u` and `star u`.
* `TauCeti.IsHaarUnitary.star`, `TauCeti.IsHaarUnitary.zpow`, `TauCeti.IsHaarUnitary.pow`,
  `TauCeti.IsHaarUnitary.smul_of_mem_unitary`, `TauCeti.IsHaarUnitary.map`: closure under adjoint,
  nonzero integer and natural powers, unitary scalar multiples, and unital `⋆`-homomorphisms.
* `TauCeti.IsHaarUnitary.starDistribution_eq` and `TauCeti.IsHaarUnitary.of_starDistribution_eq`:
  uniqueness and invariance of the algebraic star distribution of a Haar unitary.
* `TauCeti.IsHaarUnitary.isRDiagonal` and `TauCeti.isHaarUnitary_iff_isRDiagonal`: R-diagonality of
  Haar unitaries and its converse for unitary elements.
* `TauCeti.IsHaarUnitary.rDiagonalDeterminingSequence`,
  `TauCeti.IsHaarUnitary.freeCumulant_rDiagonalWord`, and
  `TauCeti.IsHaarUnitary.freeCumulant_ite`: the signed Catalan formula for the joint cumulants.

## Implementation notes

Because `u` and `star u` commute, their joint free cumulants are cyclically invariant even when `φ`
is non-tracial (`TauCeti.freeCumulant_comp_finRotate_pow_of_commute`). Rotating any mixed word so
that an adjacent pair `u * star u = 1` or `star u * u = 1` sits in the first two positions and
cancelling that pair via `TauCeti.freeCumulant_eq_neg_sum_of_mul_eq_one` expresses every joint free
cumulant recursively in terms of shorter subwords, yielding both R-diagonality and the Catalan
convolution recurrence without passing through formal power series or traciality.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Math. Soc.
  Lecture Note Ser. 335, Cambridge University Press (2006), Lectures 1, 11 (Example 11.27), and 15
  (Example 15.3).
-/

public section

open Finset

namespace TauCeti

/-! ### Definition, power moments, and algebraic invariance -/

section Moments

variable {R A : Type*} [Semiring R] [Semiring A] [Module R A] [StarMul A]
  {φ : A →ₗ[R] R} {u : A}

/-- An element `u` is a **Haar unitary** with respect to `φ : A →ₗ[R] R` if `u ∈ unitary A`, `φ` is
normalized (`φ 1 = 1`), and every nonzero integer power of `u` in `unitary A` lies in `ker φ`. -/
structure IsHaarUnitary (φ : A →ₗ[R] R) (u : A) : Prop where
  /-- The element `u` belongs to `unitary A`. -/
  mem_unitary : u ∈ unitary A
  /-- The functional `φ` is normalized. -/
  apply_one : φ 1 = 1
  /-- Every nonzero integer power of `u` in `unitary A` has expectation zero. -/
  apply_zpow_eq_zero {k : ℤ} (hk : k ≠ 0) :
    φ (((⟨u, mem_unitary⟩ : unitary A) ^ k : unitary A) : A) = 0

/-- An element is a Haar unitary if and only if it is unitary and its integer power moments equal
`1` at `0` and `0` elsewhere. -/
theorem isHaarUnitary_iff_apply_zpow :
    IsHaarUnitary φ u ↔
      ∃ hu : u ∈ unitary A, ∀ k : ℤ,
        φ (((⟨u, hu⟩ : unitary A) ^ k : unitary A) : A) = if k = 0 then 1 else 0 := by
  refine ⟨fun h => ⟨h.mem_unitary, fun k => ?_⟩, fun ⟨hu, hk⟩ => ⟨hu, ?_, fun {k} hne => ?_⟩⟩
  · split_ifs with hk
    · simp [hk, h.apply_one]
    · exact h.apply_zpow_eq_zero hk
  · simpa using hk 0
  · simpa [hne] using hk k

/-- An element is a Haar unitary if and only if it is unitary, `φ 1 = 1`, and all positive natural
powers of `u` and `star u` have expectation zero. -/
theorem isHaarUnitary_iff_apply_pow :
    IsHaarUnitary φ u ↔
      u ∈ unitary A ∧ φ 1 = 1 ∧
        (∀ {n : ℕ}, n ≠ 0 → φ (u ^ n) = 0) ∧
        (∀ {n : ℕ}, n ≠ 0 → φ (star u ^ n) = 0) := by
  have hneg_pow (hu : u ∈ unitary A) (n : ℕ) :
      (((⟨u, hu⟩ : unitary A) ^ (-(n : ℤ)) : unitary A) : A) = star u ^ n := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, ← Unitary.star_eq_inv, SubmonoidClass.coe_pow]
    rfl
  refine ⟨fun h => ⟨h.mem_unitary, h.apply_one, fun {n} hn => ?_, fun {n} hn => ?_⟩,
    fun ⟨hu, h1, hpos, hneg⟩ => ⟨hu, h1, fun {k} hk => ?_⟩⟩
  · simpa using h.apply_zpow_eq_zero (Int.natCast_ne_zero.mpr hn)
  · rw [← hneg_pow h.mem_unitary]
    exact h.apply_zpow_eq_zero (neg_ne_zero.mpr (Int.natCast_ne_zero.mpr hn))
  · cases k with
    | ofNat n =>
      have hn : n ≠ 0 := fun h => hk (by simp [h])
      simpa using hpos hn
    | negSucc n =>
      rw [Int.negSucc_eq, ← Nat.cast_succ, hneg_pow hu]
      exact hneg (Nat.succ_ne_zero n)

/-- Construct `IsHaarUnitary φ u` from vanishing of positive natural powers of `u` and `star u`. -/
theorem IsHaarUnitary.of_apply_pow (hu : u ∈ unitary A) (h1 : φ 1 = 1)
    (hpos : ∀ {n : ℕ}, n ≠ 0 → φ (u ^ n) = 0)
    (hneg : ∀ {n : ℕ}, n ≠ 0 → φ (star u ^ n) = 0) :
    IsHaarUnitary φ u :=
  isHaarUnitary_iff_apply_pow.2 ⟨hu, h1, hpos, hneg⟩

namespace IsHaarUnitary

/-- The integer power moments of a Haar unitary are `1` at `0` and `0` elsewhere. -/
@[simp]
theorem apply_zpow (h : IsHaarUnitary φ u) (k : ℤ) :
    φ (((⟨u, h.mem_unitary⟩ : unitary A) ^ k : unitary A) : A) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · simp [hk, h.apply_one]
  · exact h.apply_zpow_eq_zero hk

/-- Positive natural powers of a Haar unitary have expectation zero. -/
theorem apply_pow_eq_zero (h : IsHaarUnitary φ u) {n : ℕ} (hn : n ≠ 0) :
    φ (u ^ n) = 0 :=
  (isHaarUnitary_iff_apply_pow.1 h).2.2.1 hn

/-- Natural power moments of a Haar unitary: `1` at `0` and `0` at positive exponents. -/
theorem apply_pow (h : IsHaarUnitary φ u) (n : ℕ) :
    φ (u ^ n) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · simp [hn, h.apply_one]
  · exact h.apply_pow_eq_zero hn

/-- Positive natural powers of the adjoint of a Haar unitary have expectation zero. -/
theorem apply_star_pow_eq_zero (h : IsHaarUnitary φ u) {n : ℕ} (hn : n ≠ 0) :
    φ (star u ^ n) = 0 :=
  (isHaarUnitary_iff_apply_pow.1 h).2.2.2 hn

/-- Natural power moments of the adjoint of a Haar unitary. -/
theorem apply_star_pow (h : IsHaarUnitary φ u) (n : ℕ) :
    φ (star u ^ n) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · simp [hn, h.apply_one]
  · exact h.apply_star_pow_eq_zero hn

/-- A Haar unitary is centered. -/
@[simp]
theorem apply_self (h : IsHaarUnitary φ u) : φ u = 0 := by
  simpa using h.apply_pow_eq_zero one_ne_zero

/-- The adjoint of a Haar unitary is centered. -/
theorem apply_star (h : IsHaarUnitary φ u) : φ (star u) = 0 := by
  simpa using h.apply_star_pow_eq_zero one_ne_zero

/-- For a Haar unitary `u`, `φ (u * star u) = 1`. -/
@[simp]
theorem apply_mul_star (h : IsHaarUnitary φ u) : φ (u * star u) = 1 := by
  rw [(Unitary.mem_iff.mp h.mem_unitary).2, h.apply_one]

/-- For a Haar unitary `u`, `φ (star u * u) = 1`. -/
@[simp]
theorem apply_star_mul (h : IsHaarUnitary φ u) : φ (star u * u) = 1 := by
  rw [(Unitary.mem_iff.mp h.mem_unitary).1, h.apply_one]

/-- The adjoint of a Haar unitary is a Haar unitary. -/
theorem star (h : IsHaarUnitary φ u) : IsHaarUnitary φ (Star.star u) :=
  of_apply_pow (Unitary.star_mem h.mem_unitary) h.apply_one h.apply_star_pow_eq_zero
    fun hn => by simpa only [star_star] using h.apply_pow_eq_zero hn

/-- Every nonzero integer power of a Haar unitary in `unitary A` is again a Haar unitary.
The hypothesis `hm : m ≠ 0` is necessary since `u ^ 0 = 1` has `φ (1 ^ 1) = 1`. -/
theorem zpow (h : IsHaarUnitary φ u) {m : ℤ} (hm : m ≠ 0) :
    IsHaarUnitary φ (((⟨u, h.mem_unitary⟩ : unitary A) ^ m : unitary A) : A) where
  mem_unitary := ((⟨u, h.mem_unitary⟩ : unitary A) ^ m).2
  apply_one := h.apply_one
  apply_zpow_eq_zero {k} hk := by
    have heq : (⟨(((⟨u, h.mem_unitary⟩ : unitary A) ^ m : unitary A) : A),
        ((⟨u, h.mem_unitary⟩ : unitary A) ^ m).2⟩ : unitary A) ^ k =
        (⟨u, h.mem_unitary⟩ : unitary A) ^ (m * k) :=
      (zpow_mul (⟨u, h.mem_unitary⟩ : unitary A) m k).symm
    rw [congrArg Subtype.val heq]
    exact h.apply_zpow_eq_zero (mul_ne_zero hm hk)

/-- Every positive natural power of a Haar unitary is again a Haar unitary. -/
theorem pow (h : IsHaarUnitary φ u) {n : ℕ} (hn : n ≠ 0) :
    IsHaarUnitary φ (u ^ n) := by
  simpa using h.zpow (Int.natCast_ne_zero.mpr hn)

end IsHaarUnitary

/-- `star u` is a Haar unitary if and only if `u` is. -/
@[simp]
theorem isHaarUnitary_star_iff : IsHaarUnitary φ (star u) ↔ IsHaarUnitary φ u :=
  ⟨fun h => by simpa only [star_star] using h.star, IsHaarUnitary.star⟩

end Moments

section HomAndStarDistribution

/-- Multiplying a Haar unitary by a unitary scalar `z ∈ unitary R` yields a Haar unitary. -/
theorem IsHaarUnitary.smul_of_mem_unitary {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [StarMul R] [StarMul A] [StarModule R A] {φ : A →ₗ[R] R} {u : A}
    (h : IsHaarUnitary φ u) {z : R} (hz : z ∈ unitary R) :
    IsHaarUnitary φ (z • u) := by
  have hzu : z • u ∈ unitary A := by
    rw [Unitary.mem_iff]
    obtain ⟨hz1, hz2⟩ := Unitary.mem_iff.mp hz
    obtain ⟨hu1, hu2⟩ := Unitary.mem_iff.mp h.mem_unitary
    exact ⟨by rw [star_smul, smul_mul_smul_comm, hz1, hu1, one_smul],
      by rw [star_smul, smul_mul_smul_comm, hz2, hu2, one_smul]⟩
  refine IsHaarUnitary.of_apply_pow hzu h.apply_one (fun hn => ?_) (fun hn => ?_)
  · rw [smul_pow, map_smul, h.apply_pow_eq_zero hn, smul_zero]
  · rw [star_smul, smul_pow, map_smul, h.apply_star_pow_eq_zero hn, smul_zero]

/-- Transporting a Haar unitary along a unital `⋆`-algebra homomorphism preserves Haar
unitarity. -/
theorem IsHaarUnitary.map {R A B : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [StarMul A] [Semiring B] [Algebra R B] [StarMul B]
    {ψ : B →ₗ[R] R} (f : A →⋆ₐ[R] B) {u : A}
    (h : IsHaarUnitary (ψ.comp f.toLinearMap) u) :
    IsHaarUnitary ψ (f u) := by
  have hfu : f u ∈ unitary B := by
    rw [Unitary.mem_iff]
    obtain ⟨hu1, hu2⟩ := Unitary.mem_iff.mp h.mem_unitary
    exact ⟨by rw [← map_star, ← map_mul, hu1, map_one],
      by rw [← map_star, ← map_mul, hu2, map_one]⟩
  refine IsHaarUnitary.of_apply_pow hfu (by simpa using h.apply_one) (fun hn => ?_) (fun hn => ?_)
  · simpa [map_pow] using h.apply_pow_eq_zero hn
  · simpa [map_star, map_pow] using h.apply_star_pow_eq_zero hn

/-- For `u ∈ unitary A`, pulling back `ψ` along a unital `⋆`-algebra homomorphism `f` makes `u` a
Haar unitary if and only if `f u` is a Haar unitary for `ψ`.

The hypothesis `hu : u ∈ unitary A` cannot be dropped: for `f = Prod.fst : A × R →⋆ₐ[R] A` and a
Haar unitary `v ∈ A`, `(v, 0)` maps to `v` yet is not unitary when `R` is nontrivial. -/
theorem isHaarUnitary_comp_starAlgHom_iff {R A B : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [StarMul A] [Semiring B] [Algebra R B] [StarMul B]
    (ψ : B →ₗ[R] R) (f : A →⋆ₐ[R] B) {u : A} (hu : u ∈ unitary A) :
    IsHaarUnitary (ψ.comp f.toLinearMap) u ↔ IsHaarUnitary ψ (f u) := by
  refine ⟨IsHaarUnitary.map f, fun h => ?_⟩
  refine IsHaarUnitary.of_apply_pow hu (by simpa using h.apply_one) (fun hn => ?_) (fun hn => ?_)
  · simpa [map_pow] using h.apply_pow_eq_zero hn
  · simpa [map_star, map_pow] using h.apply_star_pow_eq_zero hn

private lemma list_prod_withStar_eq_zpow {A : Type*} [Monoid A] [StarMul A] {u : A}
    (hu : u ∈ unitary A) (w : List (Unit × Bool)) :
    (w.map (StarPolynomial.withStar (fun _ : Unit => u))).prod =
      (((⟨u, hu⟩ : unitary A) ^
        (w.map fun p : Unit × Bool => if p.2 then (-1 : ℤ) else 1).sum : unitary A) : A) := by
  induction w with
  | nil => simp
  | cons p w ih =>
    rcases p with ⟨⟨⟩, b⟩
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
    cases b
    · have hz := zpow_add (⟨u, hu⟩ : unitary A) 1
        (w.map fun p : Unit × Bool => if p.2 then (-1 : ℤ) else 1).sum
      simpa [StarPolynomial.withStar_mk_false] using (congrArg Subtype.val hz).symm
    · have hz := congrArg Subtype.val
        (zpow_add (⟨u, hu⟩ : unitary A) (-1)
          (w.map fun p : Unit × Bool => if p.2 then (-1 : ℤ) else 1).sum).symm
      rw [Submonoid.coe_mul, zpow_neg_one, ← Unitary.star_eq_inv] at hz
      rw [StarPolynomial.withStar_mk_true]
      exact hz

/-- Any two Haar unitaries, possibly in different algebras over `R`, have the same algebraic star
distribution. -/
theorem IsHaarUnitary.starDistribution_eq {R A B : Type*} [CommSemiring R] [StarRing R]
    [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
    [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]
    {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {u : A} {v : B}
    (hu : IsHaarUnitary φ u) (hv : IsHaarUnitary ψ v) :
    starDistribution φ (fun _ : Unit => u) = starDistribution ψ (fun _ : Unit => v) := by
  rw [starDistribution_eq_iff]
  intro w
  rw [list_prod_withStar_eq_zpow hu.mem_unitary, list_prod_withStar_eq_zpow hv.mem_unitary,
    hu.apply_zpow, hv.apply_zpow]

/-- If `v ∈ unitary B` has the same star distribution as a Haar unitary `u`, then `v` is also a
Haar unitary.

The hypothesis `hv : v ∈ unitary B` cannot be dropped: in `B = A × R` with `ψ (x, _) = φ x`,
`(u, 0)` has the same star distribution as `u` under `φ` yet is not unitary when `R` is
nontrivial. -/
theorem IsHaarUnitary.of_starDistribution_eq {R A B : Type*} [CommSemiring R] [StarRing R]
    [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
    [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]
    {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {u : A} {v : B}
    (hu : IsHaarUnitary φ u) (hv : v ∈ unitary B)
    (hdist : starDistribution φ (fun _ : Unit => u) = starDistribution ψ (fun _ : Unit => v)) :
    IsHaarUnitary ψ v := by
  have hword := starDistribution_eq_iff.1 hdist
  refine IsHaarUnitary.of_apply_pow hv (by simpa using (hword []).symm.trans hu.apply_one)
    (fun {n} hn => ?_) (fun {n} hn => ?_)
  · have hw := hword (List.replicate n ((), false))
    simp only [List.map_replicate, StarPolynomial.withStar_mk_false, List.prod_replicate] at hw
    exact hw.symm.trans (hu.apply_pow_eq_zero hn)
  · have hw := hword (List.replicate n ((), true))
    simp only [List.map_replicate, StarPolynomial.withStar_mk_true, List.prod_replicate] at hw
    exact hw.symm.trans (hu.apply_star_pow_eq_zero hn)

end HomAndStarDistribution

/-! ### Subword embeddings and parity lemmas for alternating words -/

section SubwordHelpers

/-- The strictly increasing parametrization of `Icc 1 r.succ` inside `Fin (m + 3)`. -/
private def iccSuccEmb {m : ℕ} (r : Fin (m + 2)) (j : Fin (r.val + 1)) : Fin (m + 3) :=
  ⟨j.val + 1, by omega⟩

private lemma strictMono_iccSuccEmb {m : ℕ} (r : Fin (m + 2)) :
    StrictMono (iccSuccEmb r) := by
  intro i j hij
  simp only [Fin.lt_def, iccSuccEmb] at hij ⊢
  omega

private lemma image_univ_iccSuccEmb {m : ℕ} (r : Fin (m + 2)) :
    (univ : Finset (Fin (r.val + 1))).image (iccSuccEmb r) = Icc 1 r.succ := by
  ext x
  simp only [mem_image, mem_univ, true_and, mem_Icc, Fin.le_def, Fin.val_one, Fin.val_succ]
  refine ⟨?_, fun hx => ⟨⟨x.val - 1, by omega⟩, Fin.ext (by simp [iccSuccEmb]; omega)⟩⟩
  rintro ⟨j, rfl⟩
  simp only [iccSuccEmb]
  omega

/-- The strictly increasing parametrization of `univ \ Icc 1 r.succ` inside `Fin (m + 3)`. -/
private def complIccSuccEmb {m : ℕ} (r : Fin (m + 2)) (j : Fin (m + 2 - r.val)) : Fin (m + 3) :=
  if j.val = 0 then 0 else ⟨j.val + r.val + 1, by omega⟩

private lemma strictMono_complIccSuccEmb {m : ℕ} (r : Fin (m + 2)) :
    StrictMono (complIccSuccEmb r) := by
  intro i j hij
  rw [Fin.lt_def] at hij ⊢
  simp only [complIccSuccEmb]
  split_ifs <;> simp <;> omega

private lemma image_univ_complIccSuccEmb {m : ℕ} (r : Fin (m + 2)) :
    (univ : Finset (Fin (m + 2 - r.val))).image (complIccSuccEmb r) = univ \ Icc 1 r.succ := by
  ext x
  simp only [mem_image, mem_univ, true_and, mem_sdiff, mem_Icc, Fin.le_def, Fin.val_one,
    Fin.val_succ]
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨j, rfl⟩
    simp only [complIccSuccEmb]
    split_ifs <;> simp
    omega
  · by_cases hx0 : x.val = 0
    · exact ⟨⟨0, by omega⟩, Fin.ext (by simp [complIccSuccEmb, hx0])⟩
    · refine ⟨⟨x.val - r.val - 1, by omega⟩, Fin.ext ?_⟩
      have hne0 : x.val - r.val - 1 ≠ 0 := by omega
      simp only [complIccSuccEmb, hne0, ↓reduceIte]
      omega

private lemma rDiagonalWord_comp_finRotate_symm (c : Bool) (k : ℕ) :
    rDiagonalWord c (2 * (k + 1)) ∘ (finRotate (2 * (k + 1))).symm =
      rDiagonalWord (!c) (2 * (k + 1)) := by
  funext i
  rw [Function.comp_apply, rDiagonalWord_apply, rDiagonalWord_apply, Bool.not_not]
  exact congrFun (Fin.ite_even_comp_finRotate_symm ⟨k + 1, by omega⟩ c (!c)) i

private lemma exists_rDiagonalWord_comp_finRotate_pow {n : ℕ} {w : Fin n → Bool} {p : ℕ}
    (h : ∃ k c, n = 2 * (k + 1) ∧ ∀ i, (w ∘ ⇑(finRotate n ^ p)) i = rDiagonalWord c n i) :
    ∃ k c, n = 2 * (k + 1) ∧ ∀ i, w i = rDiagonalWord c n i := by
  obtain ⟨k, c, rfl, hw⟩ := h
  have hfun : w ∘ ⇑(finRotate (2 * (k + 1)) ^ p) = rDiagonalWord c (2 * (k + 1)) := funext hw
  have hstep : ∀ q d, w ∘ ⇑(finRotate (2 * (k + 1)) ^ q) = rDiagonalWord d (2 * (k + 1)) →
      ∃ c', ∀ i, w i = rDiagonalWord c' (2 * (k + 1)) i := by
    intro q
    induction q with
    | zero =>
      intro d hd
      exact ⟨d, fun i => congrFun hd i⟩
    | succ q ih =>
      intro d hd
      refine ih (!d) ?_
      rw [← rDiagonalWord_comp_finRotate_symm d k, ← hd]
      ext i
      simp [pow_succ]
  obtain ⟨c', hc'⟩ := hstep p c hfun
  exact ⟨k, c', rfl, hc'⟩

/-- If `w' 0 ≠ w' 1` and both subwords `w' ∘ iccSuccEmb r` and `w' ∘ complIccSuccEmb r` are even
alternating words, then `w'` itself is an even alternating word. -/
private lemma exists_rDiagonalWord_of_subwords {m : ℕ} {w' : Fin (m + 3) → Bool}
    (h01 : w' 0 ≠ w' 1) {r : Fin (m + 2)}
    (h1 : ∃ k c, r.val + 1 = 2 * (k + 1) ∧
      ∀ j, (w' ∘ iccSuccEmb r) j = rDiagonalWord c (r.val + 1) j)
    (h2 : ∃ k c, m + 2 - r.val = 2 * (k + 1) ∧
      ∀ j, (w' ∘ complIccSuccEmb r) j = rDiagonalWord c (m + 2 - r.val) j) :
    ∃ k c, m + 3 = 2 * (k + 1) ∧ ∀ i, w' i = rDiagonalWord c (m + 3) i := by
  obtain ⟨k₁, c₁, hk₁, hc₁⟩ := h1
  obtain ⟨k₂, c₂, hk₂, hc₂⟩ := h2
  have hc₁_eq : c₁ = !w' 0 := by
    have h0 := hc₁ ⟨0, by omega⟩
    have hemb0 : iccSuccEmb r ⟨0, by omega⟩ = 1 := Fin.ext rfl
    rw [Function.comp_apply, hemb0, rDiagonalWord_apply] at h0
    simp only [Even.zero, ↓reduceIte] at h0
    cases hw0 : w' 0 <;> cases hc₁' : c₁ <;> simp_all
  have hc₂_eq : c₂ = w' 0 := by
    have h0 := hc₂ ⟨0, by omega⟩
    have hemb0 : complIccSuccEmb r ⟨0, by omega⟩ = 0 := Fin.ext rfl
    rw [Function.comp_apply, hemb0, rDiagonalWord_apply] at h0
    simp only [Even.zero, ↓reduceIte] at h0
    exact h0.symm
  refine ⟨k₁ + k₂ + 1, w' 0, by omega, fun i => ?_⟩
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    subst hi
    simp [rDiagonalWord_apply]
  · by_cases hir : i.val ≤ r.val + 1
    · have hi := hc₁ ⟨i.val - 1, by omega⟩
      have hemb : iccSuccEmb r ⟨i.val - 1, by omega⟩ = i :=
        Fin.ext (by simp [iccSuccEmb]; omega)
      rw [Function.comp_apply, hemb, hc₁_eq, rDiagonalWord_apply] at hi
      rw [hi, rDiagonalWord_apply]
      have hival : i.val = (i.val - 1) + 1 := by omega
      have hpar : Even (i.val - 1) ↔ ¬ Even i.val := by
        conv_rhs => rw [hival]
        simp [Nat.even_add_one]
      by_cases he : Even i.val <;> simp [he, hpar]
    · have hi := hc₂ ⟨i.val - (r.val + 1), by omega⟩
      have hemb : complIccSuccEmb r ⟨i.val - (r.val + 1), by omega⟩ = i := by
        refine Fin.ext ?_
        have hsub0 : i.val - (r.val + 1) ≠ 0 := by omega
        simp only [complIccSuccEmb, hsub0, ↓reduceIte]
        omega
      rw [Function.comp_apply, hemb, hc₂_eq, rDiagonalWord_apply] at hi
      rw [hi, rDiagonalWord_apply]
      have hival : i.val = (i.val - (r.val + 1)) + 2 * (k₁ + 1) := by omega
      have hpar : Even (i.val - (r.val + 1)) ↔ Even i.val := by
        conv_rhs => rw [hival]
        simp [Nat.even_add]
      by_cases he : Even i.val <;> simp [he, hpar]

end SubwordHelpers

/-! ### Cumulants and R-diagonality of Haar unitaries -/

section Cumulants

private lemma freeCumulant_Icc_one_succ {R A : Type*} [CommRing R] [Monoid A] (φ : A → R)
    {m : ℕ} (r : Fin (m + 2)) (a : Fin (m + 3) → A) :
    freeCumulant φ a (Icc 1 r.succ) = freeCumulant φ (a ∘ iccSuccEmb r) univ := by
  rw [← image_univ_iccSuccEmb r,
    ← freeCumulant_comp_of_strictMonoOn φ ((strictMono_iccSuccEmb r).strictMonoOn _) a]

private lemma freeCumulant_sdiff_Icc_one_succ {R A : Type*} [CommRing R] [Monoid A] (φ : A → R)
    {m : ℕ} (r : Fin (m + 2)) (a : Fin (m + 3) → A) :
    freeCumulant φ a (univ \ Icc 1 r.succ) = freeCumulant φ (a ∘ complIccSuccEmb r) univ := by
  rw [← image_univ_complIccSuccEmb r,
    ← freeCumulant_comp_of_strictMonoOn φ ((strictMono_complIccSuccEmb r).strictMonoOn _) a]

private lemma mul_ite_star_eq_one_of_ne {A : Type*} [Monoid A] [StarMul A] {u : A}
    (hu : u ∈ unitary A) {b₀ b₁ : Bool} (hb : b₀ ≠ b₁) :
    (if b₀ then star u else u) * (if b₁ then star u else u) = 1 := by
  cases b₀ <;> cases b₁
  · exact (hb rfl).elim
  · exact (Unitary.mem_iff.mp hu).2
  · exact (Unitary.mem_iff.mp hu).1
  · exact (hb rfl).elim

/-- Every nonempty free cumulant of the constant word `(u, …, u)` in a Haar unitary vanishes. -/
theorem IsHaarUnitary.freeCumulant_const_eq_zero {R A : Type*} [CommRing R] [Semiring A]
    [Module R A] [StarMul A] {φ : A →ₗ[R] R} {u : A} (h : IsHaarUnitary φ u)
    {α : Type*} [LinearOrder α] {s : Finset α} (hs : s.Nonempty) :
    freeCumulant φ (fun _ => u) s = 0 :=
  freeCumulant_const_eq_of_forall_apply_pow φ (fun _ => 0) hs fun t _ ht => by
    rw [h.apply_pow_eq_zero ht.card_ne_zero, eq_comm]
    refine sum_eq_zero fun π _ => ?_
    obtain ⟨B, hB⟩ := π.1.parts_nonempty ht.ne_empty
    exact prod_eq_zero hB rfl

/-- Every nonempty free cumulant of `(star u, …, star u)` in a Haar unitary vanishes. -/
theorem IsHaarUnitary.freeCumulant_const_star_eq_zero {R A : Type*} [CommRing R] [Semiring A]
    [Module R A] [StarMul A] {φ : A →ₗ[R] R} {u : A} (h : IsHaarUnitary φ u)
    {α : Type*} [LinearOrder α] {s : Finset α} (hs : s.Nonempty) :
    freeCumulant φ (fun _ => Star.star u) s = 0 :=
  h.star.freeCumulant_const_eq_zero hs

private lemma freeCumulant_ite_eq_zero_of_const {R A : Type*} [CommRing R] [Semiring A]
    [Module R A] [StarMul A] {φ : A →ₗ[R] R} {u : A} (h : IsHaarUnitary φ u) {n : ℕ} (i₀ : Fin n)
    {w : Fin n → Bool} (hconst : ∀ i, w i = w i₀) :
    freeCumulant φ (fun i => if w i then star u else u) univ = 0 := by
  have : Nonempty (Fin n) := ⟨i₀⟩
  have hfun : (fun i => if w i then star u else u) =
      fun _ => if w i₀ then star u else u := funext fun i => by rw [hconst i]
  rw [hfun]
  cases w i₀
  · exact h.freeCumulant_const_eq_zero univ_nonempty
  · exact h.freeCumulant_const_star_eq_zero univ_nonempty

variable {R A : Type*} [CommRing R] [Semiring A] [Algebra R A] [StarRing A]
  {φ : A →ₗ[R] R} {u : A}

/-- **Haar unitaries are R-diagonal.** Every joint free cumulant of a Haar unitary `u` and `star u`
outside nonempty even alternating words vanishes, without assuming traciality or positivity of
`φ`. -/
theorem IsHaarUnitary.isRDiagonal (h : IsHaarUnitary φ u) : IsRDiagonal φ u where
  apply_one := h.apply_one
  freeCumulant_eq_zero {n} hn w hw := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      rcases n with _ | _ | _ | m
      · exact (hn rfl).elim
      · exact freeCumulant_ite_eq_zero_of_const h 0 fun i => by fin_cases i; rfl
      · by_cases h01 : w 1 = w 0
        · exact freeCumulant_ite_eq_zero_of_const h 0 fun i => by fin_cases i <;> simp [h01]
        · refine (hw ⟨0, w 0, rfl, fun i => ?_⟩).elim
          fin_cases i <;> cases hw0 : w 0 <;> cases hw1 : w 1 <;> simp_all [rDiagonalWord_apply]
      · by_cases hconst : ∀ i : Fin (m + 3), w i = w 0
        · exact freeCumulant_ite_eq_zero_of_const h 0 hconst
        · have hex : ∃ p : Fin (m + 3), w p ≠ w (finRotate (m + 3) p) := by
            by_contra! hall
            exact hconst (apply_eq_apply_zero_of_add_one fun i => by
              rw [← finRotate_apply, hall i])
          obtain ⟨p, hp⟩ := hex
          set w' : Fin (m + 3) → Bool := w ∘ ⇑(finRotate (m + 3) ^ (p : ℕ))
          have hw' : ¬ ∃ k c, m + 3 = 2 * (k + 1) ∧ ∀ i, w' i = rDiagonalWord c (m + 3) i :=
            mt exists_rDiagonalWord_comp_finRotate_pow hw
          have hp0 : (finRotate (m + 3) ^ (p : ℕ)) 0 = p :=
            Fin.ext (by simp [Fin.coe_finRotate_pow, Nat.mod_eq_of_lt p.isLt])
          have hp1 : (finRotate (m + 3) ^ (p : ℕ)) 1 = finRotate (m + 3) p := by
            have h01 : finRotate (m + 3) 0 = 1 := Fin.finRotate_castSucc (0 : Fin (m + 2))
            rw [← h01, ← Equiv.Perm.mul_apply, ← pow_succ, pow_succ', Equiv.Perm.mul_apply, hp0]
          have hw'01 : w' 0 ≠ w' 1 := by simpa [w', hp0, hp1] using hp
          have hcomm (i j : Fin (m + 3)) :
              Commute (if w i then Star.star u else u) (if w j then Star.star u else u) := by
            cases w i <;> cases w j <;>
              simp [Commute.refl, commute_unitary_self_star h.mem_unitary,
                commute_unitary_star_self h.mem_unitary]
          rw [← freeCumulant_comp_finRotate_pow_of_commute φ hcomm (p : ℕ)]
          simp only [Function.comp_def]
          rw [freeCumulant_eq_neg_sum_of_mul_eq_one φ h.apply_one
            (mul_ite_star_eq_one_of_ne h.mem_unitary hw'01), neg_eq_zero]
          refine sum_eq_zero fun r _ => ?_
          rw [freeCumulant_Icc_one_succ, freeCumulant_sdiff_Icc_one_succ]
          by_cases hr1 : ∃ k c, r.val + 1 = 2 * (k + 1) ∧
              ∀ j, (w' ∘ iccSuccEmb r) j = rDiagonalWord c (r.val + 1) j
          · have hr2 : ¬ ∃ k c, m + 2 - r.val = 2 * (k + 1) ∧
                ∀ j, (w' ∘ complIccSuccEmb r) j = rDiagonalWord c (m + 2 - r.val) j :=
              fun h2 => hw' (exists_rDiagonalWord_of_subwords hw'01 hr1 h2)
            have hz := ih (m + 2 - r.val) (by omega) (by omega) (w' ∘ complIccSuccEmb r) hr2
            exact mul_eq_zero_of_right _ hz
          · have hz := ih (r.val + 1) (by omega) (by omega) (w' ∘ iccSuccEmb r) hr1
            exact mul_eq_zero_of_left hz _

/-- A unitary element is a Haar unitary if and only if it is R-diagonal.

The hypothesis `hu : u ∈ unitary A` cannot be dropped: `0 : A` is R-diagonal whenever `φ 1 = 1`,
yet `0 ∉ unitary A` in any nontrivial star ring. -/
theorem isHaarUnitary_iff_isRDiagonal (hu : u ∈ unitary A) :
    IsHaarUnitary φ u ↔ IsRDiagonal φ u :=
  ⟨IsHaarUnitary.isRDiagonal, fun h =>
    IsHaarUnitary.of_apply_pow hu h.apply_one h.apply_pow_eq_zero h.apply_star_pow_eq_zero⟩

private def oddFinEmb (n : ℕ) (j : Fin (n + 1)) : Fin ((2 * n + 1) + 2) :=
  ⟨2 * j.val + 1, by omega⟩

private lemma freeCumulant_rDiagonalWord_Icc_eq_zero_of_not_mem (h : IsHaarUnitary φ u)
    (c : Bool) (n : ℕ) {r : Fin ((2 * n + 1) + 2)} (hr : r ∉ univ.image (oddFinEmb n)) :
    freeCumulant φ
        (fun i : Fin ((2 * n + 1) + 3) =>
          if rDiagonalWord c ((2 * n + 1) + 3) i then star u else u)
        (Icc 1 r.succ) = 0 := by
  have heven : Even r.val := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨k, hk⟩ := hodd
    exact hr (mem_image.2 ⟨⟨k, by omega⟩, mem_univ _, Fin.ext (by simp [oddFinEmb, hk])⟩)
  rw [freeCumulant_Icc_one_succ]
  refine h.isRDiagonal.freeCumulant_eq_zero (by omega)
    (rDiagonalWord c ((2 * n + 1) + 3) ∘ iccSuccEmb r) ?_
  rintro ⟨k, d, hk, _⟩
  obtain ⟨m, hm⟩ := heven
  omega

private lemma freeCumulant_rDiagonalWord_iccSuccEmb_odd (c : Bool) (n : ℕ) (j : Fin (n + 1)) :
    freeCumulant φ
        ((fun i : Fin ((2 * n + 1) + 3) =>
            if rDiagonalWord c ((2 * n + 1) + 3) i then star u else u) ∘
          iccSuccEmb (oddFinEmb n j))
        univ =
      rDiagonalDeterminingSequence φ u (!c) j.val := by
  have hword : ((fun i : Fin ((2 * n + 1) + 3) =>
        if rDiagonalWord c ((2 * n + 1) + 3) i then star u else u) ∘
      iccSuccEmb (oddFinEmb n j)) =
      fun t : Fin ((oddFinEmb n j).val + 1) =>
        if rDiagonalWord (!c) ((oddFinEmb n j).val + 1) t then star u else u := by
    funext t
    simp only [Function.comp_apply, iccSuccEmb, rDiagonalWord_apply, Nat.even_add_one]
    by_cases ht : Even (t : ℕ) <;> simp [ht]
  rw [hword, rDiagonalDeterminingSequence_def]
  exact congrArg
    (fun K : ℕ => freeCumulant φ
      (fun t : Fin K => if rDiagonalWord (!c) K t then star u else u) univ)
    (by simp [oddFinEmb]; ring)

private lemma freeCumulant_rDiagonalWord_complIccSuccEmb_odd (c : Bool) (n : ℕ)
    (j : Fin (n + 1)) :
    freeCumulant φ
        ((fun i : Fin ((2 * n + 1) + 3) =>
            if rDiagonalWord c ((2 * n + 1) + 3) i then star u else u) ∘
          complIccSuccEmb (oddFinEmb n j))
        univ =
      rDiagonalDeterminingSequence φ u c (n - j.val) := by
  have hword : ((fun i : Fin ((2 * n + 1) + 3) =>
        if rDiagonalWord c ((2 * n + 1) + 3) i then star u else u) ∘
      complIccSuccEmb (oddFinEmb n j)) =
      fun t : Fin ((2 * n + 1) + 2 - (oddFinEmb n j).val) =>
        if rDiagonalWord c ((2 * n + 1) + 2 - (oddFinEmb n j).val) t then star u else u := by
    funext t
    rw [Function.comp_apply, rDiagonalWord_apply, rDiagonalWord_apply]
    dsimp only [complIccSuccEmb, oddFinEmb]
    by_cases ht0 : t.val = 0
    · simp [ht0]
    · simp only [ht0, ↓reduceIte]
      have hshift : t.val + (2 * j.val + 1) + 1 = t.val + 2 * (j.val + 1) := by ring
      have hpar : Even (t.val + (2 * j.val + 1) + 1) ↔ Even t.val := by
        rw [hshift]
        simp [Nat.even_add]
      by_cases ht : Even t.val <;> simp [ht, hpar]
  rw [hword, rDiagonalDeterminingSequence_def]
  exact congrArg
    (fun K : ℕ => freeCumulant φ
      (fun t : Fin K => if rDiagonalWord c K t then star u else u) univ)
    (by simp [oddFinEmb]; omega)

/-- **Alternating free cumulants of a Haar unitary (determining-sequence form).** Both R-diagonal
determining sequences of a Haar unitary equal `(-1) ^ n * catalan n` at index `n` (which has order
`2 * (n + 1)`). -/
@[simp]
theorem IsHaarUnitary.rDiagonalDeterminingSequence (h : IsHaarUnitary φ u) (c : Bool) (n : ℕ) :
    TauCeti.rDiagonalDeterminingSequence φ u c n = (-1) ^ n * (catalan n : R) := by
  induction n using Nat.strong_induction_on generalizing c with
  | ind n ih =>
    rcases n with _ | n
    · rw [rDiagonalDeterminingSequence_def, univ_fin2, freeCumulant_pair φ _ Fin.zero_lt_one]
      cases c <;>
        simp [rDiagonalWord_apply, catalan_zero, h.apply_mul_star, h.apply_star_mul, h.apply_self,
          h.apply_star]
    · have hlen : 2 * (n + 1 + 1) = (2 * n + 1) + 3 := by omega
      let aWord : Fin ((2 * n + 1) + 3) → A :=
        fun i => if rDiagonalWord c ((2 * n + 1) + 3) i then Star.star u else u
      rw [rDiagonalDeterminingSequence_def,
        congrArg (fun K : ℕ => freeCumulant φ
          (fun i : Fin K => if rDiagonalWord c K i then Star.star u else u) univ) hlen]
      have h01 : rDiagonalWord c ((2 * n + 1) + 3) 0 ≠ rDiagonalWord c ((2 * n + 1) + 3) 1 := by
        cases c <;> simp [rDiagonalWord_apply]
      rw [freeCumulant_eq_neg_sum_of_mul_eq_one φ h.apply_one
        (a := aWord) (mul_ite_star_eq_one_of_ne h.mem_unitary h01)]
      have hsub : ∑ r : Fin ((2 * n + 1) + 2),
            freeCumulant φ aWord (Icc 1 r.succ) * freeCumulant φ aWord (univ \ Icc 1 r.succ) =
          ∑ r ∈ univ.image (oddFinEmb n),
            freeCumulant φ aWord (Icc 1 r.succ) * freeCumulant φ aWord (univ \ Icc 1 r.succ) :=
        (sum_subset (subset_univ _) fun _ _ hr =>
          mul_eq_zero_of_left (freeCumulant_rDiagonalWord_Icc_eq_zero_of_not_mem h c n hr) _).symm
      rw [hsub, sum_image fun i _ j _ hij => by
        simp only [oddFinEmb, Fin.ext_iff] at hij ⊢; omega]
      have hterm (j : Fin (n + 1)) :
          freeCumulant φ aWord (Icc 1 (oddFinEmb n j).succ) *
              freeCumulant φ aWord (univ \ Icc 1 (oddFinEmb n j).succ) =
            (-1) ^ n * ((catalan j.val * catalan (n - j.val) : ℕ) : R) := by
        rw [freeCumulant_Icc_one_succ, freeCumulant_sdiff_Icc_one_succ,
          freeCumulant_rDiagonalWord_iccSuccEmb_odd,
          freeCumulant_rDiagonalWord_complIccSuccEmb_odd,
          ih j.val (by omega) (!c), ih (n - j.val) (by omega) c]
        have hexp : (-1 : R) ^ j.val * (-1 : R) ^ (n - j.val) = (-1 : R) ^ n := by
          rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp j.isLt)]
        push_cast
        linear_combination (catalan j.val : R) * (catalan (n - j.val) : R) * hexp
      simp_rw [hterm, ← mul_sum, ← Nat.cast_sum, ← catalan_succ]
      ring

/-- **Alternating free cumulants of a Haar unitary in degree `2 * n`.** For every `n : ℕ` and
starting letter `c : Bool`, the degree-`2 * n` alternating free cumulant of `u` and `star u` is
`(-1) ^ (n - 1) * catalan (n - 1)` (for `n = 0` both sides equal `1`). -/
theorem IsHaarUnitary.freeCumulant_rDiagonalWord (h : IsHaarUnitary φ u) (c : Bool) (n : ℕ) :
    freeCumulant φ (fun i : Fin (2 * n) =>
      if rDiagonalWord c (2 * n) i then Star.star u else u) univ =
      (-1) ^ (n - 1) * (catalan (n - 1) : R) := by
  rcases n with _ | k
  · simp [catalan_zero]
  · simpa [rDiagonalDeterminingSequence_def] using h.rDiagonalDeterminingSequence c k

/-- **Joint free cumulants of a Haar unitary.** For any Boolean word `w : Fin n → Bool`, the joint
free cumulant of `(u, star u)` along `w` equals `(-1) ^ (n / 2 - 1) * catalan (n / 2 - 1)` if `n`
is even and `w` alternates, and `0` otherwise (for `n = 0` both sides equal `1`). -/
theorem IsHaarUnitary.freeCumulant_ite (h : IsHaarUnitary φ u) {n : ℕ} (w : Fin n → Bool) :
    freeCumulant φ (fun i => if w i then Star.star u else u) univ =
      if Even n ∧ ∃ c, ∀ i, w i = rDiagonalWord c n i then
        (-1) ^ (n / 2 - 1) * (catalan (n / 2 - 1) : R)
      else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · have halt : Even 0 ∧ ∃ c, ∀ i : Fin 0, w i = rDiagonalWord c 0 i :=
      ⟨Even.zero, false, fun i => i.elim0⟩
    simp [halt, catalan_zero]
  · split_ifs with halt
    · obtain ⟨⟨m, hm⟩, c, hw⟩ := halt
      have hn2 : n = 2 * m := by omega
      have hfun : (fun i => if w i then Star.star u else u) =
          fun i => if rDiagonalWord c n i then Star.star u else u :=
        funext fun i => by rw [hw i]
      rw [hfun]
      simp only [hn2, Nat.mul_div_right _ two_pos]
      exact (congrArg
        (fun K : ℕ => freeCumulant φ
          (fun i : Fin K => if rDiagonalWord c K i then Star.star u else u) univ)
        hn2).trans (h.freeCumulant_rDiagonalWord c m)
    · refine h.isRDiagonal.freeCumulant_eq_zero hn w ?_
      rintro ⟨k, c, hk, hc⟩
      exact halt ⟨⟨k + 1, by omega⟩, c, hc⟩

end Cumulants

end TauCeti
