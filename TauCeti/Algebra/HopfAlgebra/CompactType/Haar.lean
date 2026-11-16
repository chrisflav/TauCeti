/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
public import TauCeti.Algebra.Coalgebra.Star
public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.PositiveIntegral
import TauCeti.Algebra.HopfAlgebra.Integral.Positive
import TauCeti.Algebra.HopfAlgebra.Integral.Uniqueness
import TauCeti.Algebra.HopfAlgebra.Star

/-!
# Algebraic Haar states on complex star bialgebras and Hopf star algebras

An *algebraic Haar state* on a complex star bialgebra `A` is a normalized (`h 1 = 1`),
two-sided invariant, positive (`0 ≤ h (star a * a)`) complex linear functional `h : A →ₗ[ℂ] ℂ`.
No norm, order, or completeness on `A` is assumed.

Uniqueness (`Subsingleton (AlgebraicHaar A)`) holds already for any star bialgebra, by comparing
left and right invariance (`LinearMap.IsLeftInvariantIntegral.eq_of_isRightInvariantIntegral`).
On a Hopf star algebra, bijectivity of the antipode (`TauCeti.HopfAlgebra.antipode_bijective`)
upgrades any normalized positive one-sided invariant integral to an `AlgebraicHaar`, implies
antipode invariance `h (S a) = h a`, yields strict positivity `0 < h (star a * a)` for `a ≠ 0`,
and implies linear reductivity (`TauCeti.Coalgebra.IsLinearlyReductive`).

## Main declarations

* `TauCeti.AlgebraicHaar`: a normalized positive two-sided invariant linear functional on a
  complex star bialgebra.
* `TauCeti.AlgebraicHaar.instSubsingleton`: an algebraic Haar state is unique when it exists.
* `TauCeti.AlgebraicHaar.toStarPositiveFunctional`: forgetful map to `StarPositiveFunctional`.
* `TauCeti.AlgebraicHaar.ofRightInvariant` and `TauCeti.AlgebraicHaar.ofLeftInvariant`: construct
  an algebraic Haar state on a Hopf star algebra from a normalized positive one-sided invariant
  integral.
* `TauCeti.AlgebraicHaar.map_antipode`: antipode invariance `h (S a) = h a`.
* `TauCeti.AlgebraicHaar.map_star_mul_self_pos`: strict positivity on nonzero squares.
* `TauCeti.AlgebraicHaar.isLinearlyReductive`: existence of an algebraic Haar state implies linear
  reductivity in every carrier universe.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 2.2 and
  Section 3.2.
* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Section 11.1.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Section 1.6.
-/

public section

open scoped ComplexOrder

namespace TauCeti

section Bialgebra

variable (A : Type*) [Semiring A] [Bialgebra ℂ A] [StarRing A]

/-- An **algebraic Haar state** on a complex star bialgebra: a normalized, two-sided invariant,
positive complex linear functional. -/
structure AlgebraicHaar extends A →ₗ[ℂ] ℂ where
  /-- Normalization at the unit. -/
  map_one' : toLinearMap 1 = 1
  /-- Left invariance: `(id ⊗ h) ∘ Δ = h(·) • 1`. -/
  isLeftInvariantIntegral : toLinearMap.IsLeftInvariantIntegral
  /-- Right invariance: `(h ⊗ id) ∘ Δ = h(·) • 1`. -/
  isRightInvariantIntegral : toLinearMap.IsRightInvariantIntegral
  /-- Algebraic positivity on squares `star a * a`. -/
  square_nonneg : ∀ a : A, 0 ≤ toLinearMap (star a * a)

namespace AlgebraicHaar

variable {A}

instance : FunLike (AlgebraicHaar A) A ℂ where
  coe h := h.toLinearMap
  coe_injective h₁ h₂ heq := by
    cases h₁
    cases h₂
    congr
    exact DFunLike.coe_injective heq

instance : LinearMapClass (AlgebraicHaar A) ℂ A ℂ where
  map_add h := h.toLinearMap.map_add
  map_smulₛₗ h := h.toLinearMap.map_smul

/-- Algebraic Haar states are determined by their values. -/
@[ext]
theorem ext {h₁ h₂ : AlgebraicHaar A} (heq : ∀ a, h₁ a = h₂ a) : h₁ = h₂ :=
  DFunLike.ext h₁ h₂ heq

@[simp]
theorem toLinearMap_apply (h : AlgebraicHaar A) (a : A) : h.toLinearMap a = h a :=
  rfl

@[simp]
theorem map_one (h : AlgebraicHaar A) : h 1 = 1 :=
  h.map_one'

/-- An algebraic Haar state is nonnegative on squares `star a * a`. -/
theorem map_star_mul_self_nonneg (h : AlgebraicHaar A) (a : A) :
    0 ≤ h (star a * a) :=
  h.square_nonneg a

/-- An algebraic Haar state is unique whenever it exists. -/
instance instSubsingleton : Subsingleton (AlgebraicHaar A) where
  allEq h₁ h₂ := by
    have hlin : h₁.toLinearMap = h₂.toLinearMap :=
      h₁.isLeftInvariantIntegral.eq_of_isRightInvariantIntegral
        h₂.isRightInvariantIntegral h₁.map_one h₂.map_one
    ext a
    exact LinearMap.congr_fun hlin a

/-- The underlying linear functional of an algebraic Haar state is nonzero. -/
theorem toLinearMap_ne_zero (h : AlgebraicHaar A) : h.toLinearMap ≠ 0 := by
  intro h0
  have h1 := LinearMap.congr_fun h0 1
  simp [h.map_one] at h1

end AlgebraicHaar

end Bialgebra

namespace AlgebraicHaar

section Ring

variable {A : Type*} [Ring A] [Bialgebra ℂ A] [StarRing A]

/-- View an algebraic Haar state as an algebraic positive functional. -/
def toStarPositiveFunctional (h : AlgebraicHaar A) : StarPositiveFunctional A where
  toLinearMap := h.toLinearMap
  square_nonneg := h.square_nonneg

@[simp]
theorem toStarPositiveFunctional_apply (h : AlgebraicHaar A) (a : A) :
    h.toStarPositiveFunctional a = h a := by
  rfl

/-- An algebraic Haar state commutes with the star involution. -/
@[simp]
theorem map_star [StarModule ℂ A] (h : AlgebraicHaar A) (a : A) :
    h (star a) = star (h a) :=
  h.toStarPositiveFunctional.map_star a

end Ring

section HopfSemiring

variable {A : Type*} [Semiring A] [HopfAlgebra ℂ A] [StarRing A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]

/-- On a Hopf star algebra, an algebraic Haar state is invariant under the antipode. -/
@[simp]
theorem map_antipode (h : AlgebraicHaar A) (a : A) :
    h (HopfAlgebra.antipode ℂ a) = h a := by
  have heq := h.isRightInvariantIntegral.comp_antipode_eq_self
    (TauCeti.HopfAlgebra.antipode_bijective (R := ℂ) (A := A)).injective h.map_one
  exact LinearMap.congr_fun heq a

/-- On a Hopf star algebra, any normalized positive right invariant integral is an algebraic
Haar state. -/
def ofRightInvariant (h : A →ₗ[ℂ] ℂ) (h1 : h 1 = 1) (hR : h.IsRightInvariantIntegral)
    (hpos : ∀ a : A, 0 ≤ h (star a * a)) : AlgebraicHaar A where
  toLinearMap := h
  map_one' := h1
  isLeftInvariantIntegral :=
    hR.isLeftInvariantIntegral
      (TauCeti.HopfAlgebra.antipode_bijective (R := ℂ) (A := A)).injective h1
  isRightInvariantIntegral := hR
  square_nonneg := hpos

@[simp]
theorem ofRightInvariant_apply (h : A →ₗ[ℂ] ℂ) (h1 : h 1 = 1) (hR : h.IsRightInvariantIntegral)
    (hpos : ∀ a : A, 0 ≤ h (star a * a)) (a : A) :
    ofRightInvariant h h1 hR hpos a = h a := by
  rfl

/-- On a Hopf star algebra, any normalized positive left invariant integral is an algebraic
Haar state. -/
def ofLeftInvariant (h : A →ₗ[ℂ] ℂ) (h1 : h 1 = 1) (hL : h.IsLeftInvariantIntegral)
    (hpos : ∀ a : A, 0 ≤ h (star a * a)) : AlgebraicHaar A where
  toLinearMap := h
  map_one' := h1
  isLeftInvariantIntegral := hL
  isRightInvariantIntegral :=
    hL.isRightInvariantIntegral
      (TauCeti.HopfAlgebra.antipode_bijective (R := ℂ) (A := A)).injective h1
  square_nonneg := hpos

@[simp]
theorem ofLeftInvariant_apply (h : A →ₗ[ℂ] ℂ) (h1 : h 1 = 1) (hL : h.IsLeftInvariantIntegral)
    (hpos : ∀ a : A, 0 ≤ h (star a * a)) (a : A) :
    ofLeftInvariant h h1 hL hpos a = h a := by
  rfl

end HopfSemiring

section HopfRing

universe v w

variable {A : Type v} [Ring A] [HopfAlgebra ℂ A] [StarRing A] [StarModule ℂ A]

/-- An algebraic Haar state on a complex Hopf star algebra vanishes on `star a * a` only when
`a = 0`. -/
@[simp]
theorem map_star_mul_self_eq_zero_iff (h : AlgebraicHaar A) {a : A} :
    h (star a * a) = 0 ↔ a = 0 :=
  h.isRightInvariantIntegral.map_star_mul_self_eq_zero_iff h.toLinearMap_ne_zero h.square_nonneg

/-- An algebraic Haar state on a complex Hopf star algebra is strictly positive on nonzero
squares. -/
theorem map_star_mul_self_pos (h : AlgebraicHaar A) {a : A} (ha : a ≠ 0) :
    0 < h (star a * a) :=
  h.isRightInvariantIntegral.map_star_mul_self_pos h.toLinearMap_ne_zero h.square_nonneg ha

/-- A complex Hopf star algebra admitting an algebraic Haar state is linearly reductive in every
carrier universe. -/
theorem isLinearlyReductive [StarCoalgebra ℂ A] (h : AlgebraicHaar A) :
    Coalgebra.IsLinearlyReductive.{0, v, w} ℂ A :=
  h.isRightInvariantIntegral.isLinearlyReductive h.toLinearMap_ne_zero h.square_nonneg

end HopfRing

end AlgebraicHaar

end TauCeti
