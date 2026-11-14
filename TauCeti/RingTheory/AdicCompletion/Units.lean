/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import TauCeti.RingTheory.AdicCompletion.AlgHom

import Mathlib.Algebra.Polynomial.AlgebraMap
import TauCeti.RingTheory.LocalRing.RingHom

/-!
# Compatible elements and units of adic completions

Let `I` be an ideal of a commutative ring `R`. A compatible family of elements `a n : R ⧸ I ^ n`
along the transition maps `Ideal.Quotient.factorPow` determines a unique element
`AdicCompletion.liftElem I a ha` of `AdicCompletion I R` with projections `a n`.

Consequently an element of `AdicCompletion I R` is a unit if and only if its projection in
`R ⧸ I ^ n` is a unit for every `n`, and indeed if and only if its mod-`I` reduction
`AdicCompletion.evalOneₐ I x` is a unit in `R ⧸ I`: units in `R ⧸ I` lift along each
nilpotent-kernel quotient `R ⧸ I ^ (n + 1) →+* R ⧸ I`, and the inverses at each level assemble into
an inverse in `AdicCompletion I R`. Thus `AdicCompletion.evalOneₐ I` is a local homomorphism and is
surjective on units, with no finite-generation assumption on `I`.

## Main definitions and results

* `AdicCompletion.liftElem`: the element of `AdicCompletion I R` with prescribed compatible
  projections in `R ⧸ I ^ n`, together with `AdicCompletion.evalₐ_liftElem` and
  `AdicCompletion.liftElem_evalₐ`.
* `AdicCompletion.isUnit_iff_forall_evalₐ`: `x : AdicCompletion I R` is a unit if and only if
  `evalₐ I n x` is a unit for every `n`.
* `AdicCompletion.isLocalHom_evalOneₐ`: the projection `AdicCompletion I R →+* R ⧸ I` reflects
  units, without assuming `I.FG`.
* `AdicCompletion.isUnit_iff_evalOneₐ`: `x : AdicCompletion I R` is a unit if and only if
  `evalOneₐ I x` is a unit in `R ⧸ I`.
* `AdicCompletion.surjective_units_map_evalOneₐ`: every unit of `R ⧸ I` lifts to a unit of
  `AdicCompletion I R`.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)

private theorem liftElem_aux (a : ∀ n, R ⧸ I ^ n)
    (ha : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (a n) = a m) {m n : ℕ}
    (h : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)).comp
      (Polynomial.aeval (R := R) (a n)) = Polynomial.aeval (R := R) (a m) :=
  Polynomial.algHom_ext (by simpa using ha h)

/-- The element of `AdicCompletion I R` whose projection to `R ⧸ I ^ n` is `a n` for every `n`,
constructed from a family compatible with `Ideal.Quotient.factorPow`. -/
noncomputable def liftElem (a : ∀ n, R ⧸ I ^ n)
    (ha : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (a n) = a m) :
    AdicCompletion I R :=
  liftAlgHom I (fun n ↦ Polynomial.aeval (R := R) (a n)) (liftElem_aux I a ha)
    (Polynomial.X : Polynomial R)

/-- Evaluating `liftElem` at level `n` recovers `a n`. -/
@[simp]
theorem evalₐ_liftElem (a : ∀ n, R ⧸ I ^ n)
    (ha : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (a n) = a m) (n : ℕ) :
    evalₐ I n (liftElem I a ha) = a n :=
  (evalₐ_liftAlgHom I _ (liftElem_aux I a ha) n (Polynomial.X : Polynomial R)).trans
    (Polynomial.aeval_X (a n))

/-- Reassembling the projections of an element of `AdicCompletion I R` recovers that element. -/
@[simp]
theorem liftElem_evalₐ (x : AdicCompletion I R) :
    liftElem I (fun n ↦ evalₐ I n x) (fun h ↦ factor_evalₐ h x) = x :=
  ext_evalₐ fun n ↦ evalₐ_liftElem I _ _ n

/-- An element of `AdicCompletion I R` is a unit if and only if all of its projections to
`R ⧸ I ^ n` are units. -/
theorem isUnit_iff_forall_evalₐ {x : AdicCompletion I R} :
    IsUnit x ↔ ∀ n, IsUnit (evalₐ I n x) := by
  refine ⟨fun hx n ↦ hx.map (evalₐ I n).toRingHom, fun hx ↦ ?_⟩
  choose u hu using fun n ↦ hx n
  -- The levelwise inverses are compatible because inverses in `R ⧸ I ^ m` are unique.
  have hinv {m n : ℕ} (h : m ≤ n) :
      Ideal.Quotient.factorPow I h (↑(u n)⁻¹ : R ⧸ I ^ n) = ↑(u m)⁻¹ := by
    refine ((u m).inv_eq_of_mul_eq_one_right ?_).symm
    rw [hu m, ← factor_evalₐ h x, ← hu n, ← map_mul, Units.mul_inv, map_one]
  refine isUnit_iff_exists_inv.mpr ⟨liftElem I (fun n ↦ ↑(u n)⁻¹) hinv, ext_evalₐ fun n ↦ ?_⟩
  rw [map_mul, evalₐ_liftElem, ← hu n, Units.mul_inv, map_one]

/-- The mod-`I` projection `AdicCompletion I R →+* R ⧸ I` reflects units, without assuming that
`I` is finitely generated. -/
instance isLocalHom_evalOneₐ : IsLocalHom (evalOneₐ I).toRingHom where
  map_nonunit x hx := by
    refine (isUnit_iff_forall_evalₐ I).mpr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · have : Subsingleton (R ⧸ I ^ 0) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact isUnit_of_subsingleton _
    · have : IsLocalHom (Ideal.Quotient.factor (Ideal.pow_le_self (I := I) hn)) :=
        Ideal.Quotient.isLocalHom_factor_pow_le_self I hn
      have heq : Ideal.Quotient.factor (Ideal.pow_le_self hn) (evalₐ I n x) = evalOneₐ I x := by
        rw [← factorₐ_evalₐ_one, ← factor_evalₐ (Nat.one_le_iff_ne_zero.mpr hn) x]
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
        simp [← hr]
      exact isUnit_of_map_unit (Ideal.Quotient.factor (Ideal.pow_le_self hn)) _ (heq ▸ hx)

/-- An element of `AdicCompletion I R` is a unit if and only if its mod-`I` projection is a unit. -/
theorem isUnit_iff_evalOneₐ {x : AdicCompletion I R} :
    IsUnit x ↔ IsUnit (evalOneₐ I x) :=
  ⟨fun h ↦ h.map (evalOneₐ I).toRingHom, isUnit_of_map_unit (evalOneₐ I).toRingHom x⟩

/-- Every unit of `R ⧸ I` lifts to a unit of `AdicCompletion I R`. -/
theorem surjective_units_map_evalOneₐ :
    Function.Surjective (Units.map (evalOneₐ I).toRingHom.toMonoidHom) :=
  IsLocalRing.surjective_units_map_of_local_ringHom (evalOneₐ I).toRingHom
    (evalOneₐ_surjective I) inferInstance

end AdicCompletion
