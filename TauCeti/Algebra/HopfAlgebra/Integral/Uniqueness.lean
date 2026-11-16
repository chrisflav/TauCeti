/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral
import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# Uniqueness and antipode invariance of normalized integrals

Over any commutative semiring, a left invariant integral `h₁` and a right invariant integral `h₂`
on a bialgebra satisfy `h₂ a * h₁ 1 = h₁ a * h₂ 1`, obtained by applying `h₁` to the right
invariance identity for `h₂` and comparing with `h₂` applied to the left invariance identity for
`h₁`. In particular, a normalized left invariant integral agrees with any normalized right
invariant integral, so a normalized two-sided invariant integral is unique.

On a Hopf algebra whose antipode `S` is injective, composing a right invariant integral with `S`
produces a left invariant integral, because `S` reverses the comultiplication. Consequently a
normalized right invariant integral is automatically antipode-invariant and left invariant, and
symmetrically for a normalized left invariant integral.

## Main results

* `LinearMap.IsLeftInvariantIntegral.apply_mul_apply_one_eq`: `h₂ a * h₁ 1 = h₁ a * h₂ 1` for a
  left invariant integral `h₁` and a right invariant integral `h₂`.
* `LinearMap.IsLeftInvariantIntegral.eq_of_isRightInvariantIntegral`: normalized left and right
  invariant integrals coincide.
* `LinearMap.IsRightInvariantIntegral.comp_antipode_isLeftInvariantIntegral` and
  `LinearMap.IsLeftInvariantIntegral.comp_antipode_isRightInvariantIntegral`: when the antipode is
  injective, precomposing with it exchanges left and right invariance.
* `LinearMap.IsRightInvariantIntegral.comp_antipode_eq_self`,
  `LinearMap.IsRightInvariantIntegral.isLeftInvariantIntegral`, and their left counterparts: a
  normalized one-sided invariant integral on a Hopf algebra with injective antipode is
  antipode-invariant and two-sided invariant.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Proposition 2.2.4.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Theorem 1.6.6.
-/

public section

open Coalgebra HopfAlgebra

namespace LinearMap

variable {R H : Type*} [CommSemiring R] [Semiring H]

section Bialgebra

variable [Bialgebra R H] {h₁ h₂ : H →ₗ[R] R}

/-- Applying a left invariant integral `h₁` to the right invariance identity of `h₂` and comparing
with the reverse order gives `h₂ a * h₁ 1 = h₁ a * h₂ 1`. -/
theorem IsLeftInvariantIntegral.apply_mul_apply_one_eq
    (h₁L : h₁.IsLeftInvariantIntegral) (h₂R : h₂.IsRightInvariantIntegral) (a : H) :
    h₂ a * h₁ 1 = h₁ a * h₂ 1 := by
  let r := ℛ R a
  have hright : ∑ i ∈ r.index, h₂ (r.left i) * h₁ (r.right i) = h₂ a * h₁ 1 := by
    simpa [map_sum, smul_eq_mul] using congrArg h₁ (h₂R.sum_smul r)
  have hleft : ∑ i ∈ r.index, h₁ (r.right i) * h₂ (r.left i) = h₁ a * h₂ 1 := by
    simpa [map_sum, smul_eq_mul] using congrArg h₂ (h₁L.sum_smul r)
  rw [← hright, ← hleft]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- A left invariant integral and a right invariant integral are proportional via their values at
`1`: `h₁ 1 • h₂ = h₂ 1 • h₁`. -/
theorem IsLeftInvariantIntegral.smul_eq_of_isRightInvariantIntegral
    (h₁L : h₁.IsLeftInvariantIntegral) (h₂R : h₂.IsRightInvariantIntegral) :
    h₁ 1 • h₂ = h₂ 1 • h₁ := by
  ext a
  simpa [smul_eq_mul, mul_comm] using h₁L.apply_mul_apply_one_eq h₂R a

/-- A normalized left invariant integral agrees with any normalized right invariant integral. -/
theorem IsLeftInvariantIntegral.eq_of_isRightInvariantIntegral
    (h₁L : h₁.IsLeftInvariantIntegral) (h₂R : h₂.IsRightInvariantIntegral)
    (h₁1 : h₁ 1 = 1) (h₂1 : h₂ 1 = 1) : h₁ = h₂ := by
  simpa [h₁1, h₂1] using (h₁L.smul_eq_of_isRightInvariantIntegral h₂R).symm

end Bialgebra

section HopfAlgebra

variable [HopfAlgebra R H] {h : H →ₗ[R] R}

/-- Given a representation of `Δ a`, reversing its legs and applying the antipode represents
`Δ (S a)`. -/
private def antipodeRepr {a : H} {ι : Type*} (r : Coalgebra.Repr R a ι) :
    Coalgebra.Repr R (antipode R a) ι where
  index := r.index
  left i := antipode R (r.right i)
  right i := antipode R (r.left i)
  eq := by
    rw [TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply, ← r.eq, map_sum, map_sum]
    simp

/-- On a Hopf algebra with injective antipode, composing a right invariant integral with the
antipode yields a left invariant integral. -/
theorem IsRightInvariantIntegral.comp_antipode_isLeftInvariantIntegral
    (hh : h.IsRightInvariantIntegral) (hS : Function.Injective (antipode R : H → H)) :
    (h.comp (antipode R)).IsLeftInvariantIntegral := by
  rw [isLeftInvariantIntegral_iff]
  intro a
  let r := ℛ R a
  have hsum : ∑ i ∈ r.index, h (antipode R (r.right i)) • antipode R (r.left i) =
      h (antipode R a) • (1 : H) :=
    hh.sum_smul (antipodeRepr r)
  have heq : ∑ i ∈ r.index, h (antipode R (r.right i)) • r.left i =
      h (antipode R a) • (1 : H) := by
    apply hS
    simpa [map_sum, map_smul] using hsum
  simpa [← r.eq, map_sum] using heq

/-- On a Hopf algebra with injective antipode, composing a left invariant integral with the
antipode yields a right invariant integral. -/
theorem IsLeftInvariantIntegral.comp_antipode_isRightInvariantIntegral
    (hh : h.IsLeftInvariantIntegral) (hS : Function.Injective (antipode R : H → H)) :
    (h.comp (antipode R)).IsRightInvariantIntegral := by
  rw [isRightInvariantIntegral_iff]
  intro a
  let r := ℛ R a
  have hsum : ∑ i ∈ r.index, h (antipode R (r.left i)) • antipode R (r.right i) =
      h (antipode R a) • (1 : H) :=
    hh.sum_smul (antipodeRepr r)
  have heq : ∑ i ∈ r.index, h (antipode R (r.left i)) • r.right i =
      h (antipode R a) • (1 : H) := by
    apply hS
    simpa [map_sum, map_smul] using hsum
  simpa [← r.eq, map_sum] using heq

/-- A normalized right invariant integral on a Hopf algebra with injective antipode is invariant
under the antipode. -/
theorem IsRightInvariantIntegral.comp_antipode_eq_self
    (hh : h.IsRightInvariantIntegral) (hS : Function.Injective (antipode R : H → H))
    (h1 : h 1 = 1) : h.comp (antipode R) = h :=
  (hh.comp_antipode_isLeftInvariantIntegral hS).eq_of_isRightInvariantIntegral hh
    (by simp [h1]) h1

/-- A normalized right invariant integral on a Hopf algebra with injective antipode is
automatically left invariant. -/
theorem IsRightInvariantIntegral.isLeftInvariantIntegral
    (hh : h.IsRightInvariantIntegral) (hS : Function.Injective (antipode R : H → H))
    (h1 : h 1 = 1) : h.IsLeftInvariantIntegral := by
  simpa [hh.comp_antipode_eq_self hS h1] using hh.comp_antipode_isLeftInvariantIntegral hS

/-- A normalized left invariant integral on a Hopf algebra with injective antipode is invariant
under the antipode. -/
theorem IsLeftInvariantIntegral.comp_antipode_eq_self
    (hh : h.IsLeftInvariantIntegral) (hS : Function.Injective (antipode R : H → H))
    (h1 : h 1 = 1) : h.comp (antipode R) = h :=
  (hh.eq_of_isRightInvariantIntegral (hh.comp_antipode_isRightInvariantIntegral hS)
    h1 (by simp [h1])).symm

/-- A normalized left invariant integral on a Hopf algebra with injective antipode is
automatically right invariant. -/
theorem IsLeftInvariantIntegral.isRightInvariantIntegral
    (hh : h.IsLeftInvariantIntegral) (hS : Function.Injective (antipode R : H → H))
    (h1 : h 1 = 1) : h.IsRightInvariantIntegral := by
  simpa [hh.comp_antipode_eq_self hS h1] using hh.comp_antipode_isRightInvariantIntegral hS

end HopfAlgebra

end LinearMap
