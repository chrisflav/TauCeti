/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

import Mathlib.Tactic.LinearCombination

/-!
# Units along surjective ring homomorphisms

A surjective map of commutative rings whose kernel consists of nilpotent elements reflects
units. Here unit reflection is Mathlib's `IsLocalHom`; neither ring is required to be local.

Together with Mathlib's kernel containment for unit-reflecting maps, this allows unit reflection
to propagate through inverse systems with locally nilpotent transition kernels. Elementwise
nilpotence suffices, without a uniform exponent. In particular, `Ideal.Quotient.factor` reflects
units whenever the larger ideal lies in the radical of the smaller
(`Ideal.Quotient.isLocalHom_factor_of_le_radical`), including the adic transition maps
`Ideal.Quotient.factorPow` for positive exponents (`Ideal.Quotient.isLocalHom_factorPow`).

A surjective map out of a semilocal ring (one with finitely many maximal ideals) is surjective
on units. This is the semilocal counterpart of Mathlib's
`IsLocalRing.surjective_units_map_of_local_ringHom`; it needs no unit reflection. By the Chinese
remainder theorem a lift of a unit can be corrected by an element of the kernel so that it avoids
every maximal ideal.

For a surjection of local rings `A → A'`, the image of the maximal ideal of `A` has radical the
maximal ideal of `A'` (`TauCeti.IsLocalRing.radical_map_maximalIdeal_of_surjective`): the closed
point of `Spec A'` is the only point over the closed point of `Spec A`.
-/

public section

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A surjective ring homomorphism with elementwise nilpotent kernel reflects units.
No uniform nilpotence exponent is required. -/
theorem isLocalHom_of_surjective_of_isNilpotent_ker (f : R →+* S)
    (hf : Function.Surjective f) (hnil : ∀ x, f x = 0 → IsNilpotent x) :
    IsLocalHom f := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := hf (↑hx.unit⁻¹)
  have hxy : IsNilpotent (x * y - 1) := hnil _ (by simp [hy, hx.mul_val_inv])
  exact isUnit_of_mul_isUnit_left (by simpa using hxy.isUnit_add_one)

/-- A surjective ring homomorphism out of a semilocal ring is surjective on units. -/
theorem surjective_units_map_of_surjective [_root_.Finite (MaximalSpectrum R)] (f : R →+* S)
    (hf : Function.Surjective f) : Function.Surjective (Units.map f.toMonoidHom) := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum R)
  intro u
  obtain ⟨a, ha⟩ := hf u
  obtain ⟨c, hc⟩ := hf ↑u⁻¹
  -- Write `1 = k + b` with `k ∈ ker f` and `b` in every maximal ideal not containing `ker f`.
  let s : Finset (MaximalSpectrum R) := {P | ¬ker f ≤ P.asIdeal}
  have hs : ker f ⊔ ⨅ P ∈ s, P.asIdeal = ⊤ := Ideal.sup_iInf_eq_top fun P hP ↦ by
    by_contra hne
    exact (Finset.mem_filter.mp hP).2
      (le_sup_left.trans_eq (P.isMaximal.eq_of_le hne le_sup_right).symm)
  obtain ⟨k, hk, b, hb, hkb⟩ := Submodule.mem_sup.mp (hs ▸ Submodule.mem_top (x := (1 : R)))
  -- The lift `a * b + k` of `u` lies in no maximal ideal `P`.
  have hunit : IsUnit (a * b + k) := by
    by_contra h
    obtain ⟨P, hP, haP⟩ := exists_max_ideal_of_mem_nonunits h
    refine hP.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    by_cases hkP : ker f ≤ P
    · -- Modulo `P` the lift is congruent to `a`, which is invertible modulo `ker f`.
      have hac : a * c - 1 ∈ ker f := by simp [mem_ker, ha, hc]
      rw [show (1 : R) = c * (a * b + k) + (a * c - c) * k - (a * c - 1) by
        linear_combination (-(a * c)) * hkb]
      exact P.sub_mem (P.add_mem (P.mul_mem_left _ haP) (P.mul_mem_left _ (hkP hk))) (hkP hac)
    · -- Modulo `P` the lift is congruent to `1`.
      have hbP : b ∈ P := Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hb ⟨P, hP⟩) (by simpa [s])
      rw [show (1 : R) = (a * b + k) + (1 - a) * b by linear_combination -hkb]
      exact P.add_mem haP (P.mul_mem_left _ hbP)
  have hfb : f b = 1 := by simpa [mem_ker.mp hk] using congrArg f hkb
  exact ⟨hunit.unit, Units.ext (by simp [ha, hfb, mem_ker.mp hk])⟩

end RingHom

namespace TauCeti.IsLocalRing

variable {A A' : Type*} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
  [Algebra A A']

/-- For a surjection of local rings `A → A'`, the closed point is the only point of `Spec A'`
over the closed point of `Spec A`. -/
theorem radical_map_maximalIdeal_of_surjective (hf : Function.Surjective (algebraMap A A')) :
    ((IsLocalRing.maximalIdeal A).map (algebraMap A A')).radical =
      IsLocalRing.maximalIdeal A' := by
  rw [IsLocalRing.map_maximalIdeal_of_surjective _ hf]
  exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime.radical

end TauCeti.IsLocalRing

namespace Ideal.Quotient

variable {R : Type*} [CommRing R]

/-- The quotient transition map `R ⧸ J →+* R ⧸ K` reflects units whenever `K` lies in the radical
of `J`: every element of its kernel has a power in `J`, hence is nilpotent in `R ⧸ J`. -/
theorem isLocalHom_factor_of_le_radical {J K : Ideal R} (hJK : J ≤ K) (hrad : K ≤ J.radical) :
    IsLocalHom (Ideal.Quotient.factor hJK) := by
  refine RingHom.isLocalHom_of_surjective_of_isNilpotent_ker _ (factor_surjective hJK) fun x hx ↦ ?_
  obtain ⟨r, rfl⟩ := mk_surjective x
  rw [factor_mk, eq_zero_iff_mem] at hx
  obtain ⟨k, hk⟩ := hrad hx
  exact ⟨k, by rwa [← map_pow, eq_zero_iff_mem]⟩

/-- For `1 ≤ m ≤ n`, the adic transition map `R ⧸ I ^ n →+* R ⧸ I ^ m` reflects units. The
hypothesis `m ≠ 0` is necessary because `R ⧸ I ^ 0` is the zero ring. -/
theorem isLocalHom_factorPow (I : Ideal R) {m n : ℕ} (hm : m ≠ 0) (h : m ≤ n) :
    IsLocalHom (Ideal.Quotient.factorPow I h) :=
  isLocalHom_factor_of_le_radical (Ideal.pow_le_pow_right h) fun _ hx ↦
    ⟨n, Ideal.pow_mem_pow (Ideal.pow_le_self hm hx) n⟩

/-- For `n ≠ 0`, the reduction `R ⧸ I ^ n →+* R ⧸ I` reflects units. -/
theorem isLocalHom_factor_pow_le_self (I : Ideal R) {n : ℕ} (hn : n ≠ 0) :
    IsLocalHom (Ideal.Quotient.factor (Ideal.pow_le_self (I := I) hn)) :=
  isLocalHom_factor_of_le_radical (Ideal.pow_le_self hn) fun _ hx ↦ ⟨n, Ideal.pow_mem_pow hx n⟩

end Ideal.Quotient
