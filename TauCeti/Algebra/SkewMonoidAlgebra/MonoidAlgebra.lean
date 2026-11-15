/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.SkewMonoidAlgebra.Basic
public import TauCeti.Algebra.Group.Action.MulDistribMulAction

/-!
# Comparison of skew monoid algebras with ordinary monoid algebras

When the action of a monoid `G` on a semiring `A` is trivial (`∀ g a, g • a = a`), the skewed
convolution product `single g a * single h b = single (g * h) (a * g • b)` reduces to the ordinary
convolution product `single (g * h) (a * b)` of `MonoidAlgebra A G`. Reading the underlying
finitely supported coefficient function directly as an element of `MonoidAlgebra A G` therefore
gives a ring isomorphism `SkewMonoidAlgebra A G ≃+* MonoidAlgebra A G`, and a `k`-algebra
isomorphism when `A` is a `k`-algebra.

In particular, when `A = k` is a commutative semiring and `SMulCommClass G k k` holds, every
element of `k` is fixed by `G` (`TauCeti.smul_eq_self_of_smulCommClass_self`), so
`SkewMonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k G` holds without any extra triviality hypothesis.

## Main definitions

* `TauCeti.skewMonoidAlgebraToMonoidAlgebraRingEquiv`: `SkewMonoidAlgebra A G ≃+* MonoidAlgebra A G`
  under `∀ g a, g • a = a`.
* `TauCeti.skewMonoidAlgebraToMonoidAlgebraAlgEquiv`: the `k`-algebra upgrade.
* `TauCeti.skewMonoidAlgebraSelfAlgEquiv`: `SkewMonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k G` for
  `[CommSemiring k] [Monoid G] [MulSemiringAction G k] [SMulCommClass G k k]`.
-/

public noncomputable section

namespace TauCeti

section Semiring

variable {A G : Type*} [Semiring A] [Monoid G] [MulSemiringAction G A]

/-- **Trivial-action skew monoid algebra is the ordinary monoid algebra.** When `G` acts trivially
on `A`, `SkewMonoidAlgebra A G` and `MonoidAlgebra A G` are isomorphic as rings via their common
underlying finitely supported functions `G →₀ A`. -/
def skewMonoidAlgebraToMonoidAlgebraRingEquiv (htriv : ∀ (g : G) (a : A), g • a = a) :
    SkewMonoidAlgebra A G ≃+* MonoidAlgebra A G where
  toFun x := ⟨x.coeff⟩
  invFun y := ⟨y.coeff⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' x y := by
    ext g
    simp
  map_mul' x y := by
    induction x using SkewMonoidAlgebra.induction_on with
    | zero => simp
    | add p q hp hq => simp [add_mul, hp, hq]
    | single g a =>
      induction y using SkewMonoidAlgebra.induction_on with
      | zero => simp
      | add p q hp hq => simp [mul_add, hp, hq]
      | single h b =>
        simp only [SkewMonoidAlgebra.single_mul_single, htriv]
        -- Both `⟨(SkewMonoidAlgebra.single g a).coeff⟩` and `MonoidAlgebra.single g a` are
        -- `⟨Finsupp.single g a⟩`.
        change MonoidAlgebra.single (g * h) (a * b) =
          MonoidAlgebra.single g a * MonoidAlgebra.single h b
        rw [MonoidAlgebra.single_mul_single]

@[simp]
theorem coeff_skewMonoidAlgebraToMonoidAlgebraRingEquiv
    (htriv : ∀ (g : G) (a : A), g • a = a) (x : SkewMonoidAlgebra A G) :
    (skewMonoidAlgebraToMonoidAlgebraRingEquiv htriv x).coeff = x.coeff :=
  (rfl)

@[simp]
theorem coeff_skewMonoidAlgebraToMonoidAlgebraRingEquiv_symm
    (htriv : ∀ (g : G) (a : A), g • a = a) (y : MonoidAlgebra A G) :
    ((skewMonoidAlgebraToMonoidAlgebraRingEquiv htriv).symm y).coeff = y.coeff :=
  (rfl)

@[simp]
theorem skewMonoidAlgebraToMonoidAlgebraRingEquiv_single
    (htriv : ∀ (g : G) (a : A), g • a = a) (g : G) (a : A) :
    skewMonoidAlgebraToMonoidAlgebraRingEquiv htriv (SkewMonoidAlgebra.single g a) =
      MonoidAlgebra.single g a :=
  (rfl)

@[simp]
theorem skewMonoidAlgebraToMonoidAlgebraRingEquiv_symm_single
    (htriv : ∀ (g : G) (a : A), g • a = a) (g : G) (a : A) :
    (skewMonoidAlgebraToMonoidAlgebraRingEquiv htriv).symm (MonoidAlgebra.single g a) =
      SkewMonoidAlgebra.single g a :=
  (rfl)

@[simp]
theorem skewMonoidAlgebraToMonoidAlgebraRingEquiv_singleOneRingHom
    (htriv : ∀ (g : G) (a : A), g • a = a) (a : A) :
    skewMonoidAlgebraToMonoidAlgebraRingEquiv htriv (SkewMonoidAlgebra.singleOneRingHom a) =
      MonoidAlgebra.singleOneRingHom a :=
  (rfl)

theorem skewMonoidAlgebraToMonoidAlgebraRingEquiv_of
    (htriv : ∀ (g : G) (a : A), g • a = a) (g : G) :
    skewMonoidAlgebraToMonoidAlgebraRingEquiv htriv (SkewMonoidAlgebra.of A G g) =
      MonoidAlgebra.of A G g :=
  (rfl)

theorem skewMonoidAlgebraToMonoidAlgebraRingEquiv_symm_of
    (htriv : ∀ (g : G) (a : A), g • a = a) (g : G) :
    (skewMonoidAlgebraToMonoidAlgebraRingEquiv htriv).symm (MonoidAlgebra.of A G g) =
      SkewMonoidAlgebra.of A G g :=
  (rfl)

end Semiring

section Algebra

variable (k : Type*) {A G : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G]
  [MulSemiringAction G A] [SMulCommClass G k A]

/-- **Algebra equivalence between a trivial-action skew monoid algebra and the ordinary monoid
algebra.** -/
def skewMonoidAlgebraToMonoidAlgebraAlgEquiv (htriv : ∀ (g : G) (a : A), g • a = a) :
    SkewMonoidAlgebra A G ≃ₐ[k] MonoidAlgebra A G where
  __ := skewMonoidAlgebraToMonoidAlgebraRingEquiv htriv
  commutes' _ := rfl

variable {k}

@[simp]
theorem skewMonoidAlgebraToMonoidAlgebraAlgEquiv_apply
    (htriv : ∀ (g : G) (a : A), g • a = a) (x : SkewMonoidAlgebra A G) :
    skewMonoidAlgebraToMonoidAlgebraAlgEquiv k htriv x =
      skewMonoidAlgebraToMonoidAlgebraRingEquiv htriv x :=
  (rfl)

@[simp]
theorem skewMonoidAlgebraToMonoidAlgebraAlgEquiv_symm_apply
    (htriv : ∀ (g : G) (a : A), g • a = a) (y : MonoidAlgebra A G) :
    (skewMonoidAlgebraToMonoidAlgebraAlgEquiv k htriv).symm y =
      (skewMonoidAlgebraToMonoidAlgebraRingEquiv htriv).symm y :=
  (rfl)

theorem skewMonoidAlgebraToMonoidAlgebraAlgEquiv_toRingEquiv
    (htriv : ∀ (g : G) (a : A), g • a = a) :
    (skewMonoidAlgebraToMonoidAlgebraAlgEquiv k htriv).toRingEquiv =
      skewMonoidAlgebraToMonoidAlgebraRingEquiv htriv :=
  (rfl)

theorem skewMonoidAlgebraToMonoidAlgebraAlgEquiv_single
    (htriv : ∀ (g : G) (a : A), g • a = a) (g : G) (a : A) :
    skewMonoidAlgebraToMonoidAlgebraAlgEquiv k htriv (SkewMonoidAlgebra.single g a) =
      MonoidAlgebra.single g a :=
  (rfl)

theorem skewMonoidAlgebraToMonoidAlgebraAlgEquiv_symm_single
    (htriv : ∀ (g : G) (a : A), g • a = a) (g : G) (a : A) :
    (skewMonoidAlgebraToMonoidAlgebraAlgEquiv k htriv).symm (MonoidAlgebra.single g a) =
      SkewMonoidAlgebra.single g a :=
  (rfl)

theorem skewMonoidAlgebraToMonoidAlgebraAlgEquiv_of
    (htriv : ∀ (g : G) (a : A), g • a = a) (g : G) :
    skewMonoidAlgebraToMonoidAlgebraAlgEquiv k htriv (SkewMonoidAlgebra.of A G g) =
      MonoidAlgebra.of A G g :=
  (rfl)

theorem skewMonoidAlgebraToMonoidAlgebraAlgEquiv_symm_of
    (htriv : ∀ (g : G) (a : A), g • a = a) (g : G) :
    (skewMonoidAlgebraToMonoidAlgebraAlgEquiv k htriv).symm (MonoidAlgebra.of A G g) =
      SkewMonoidAlgebra.of A G g :=
  (rfl)

end Algebra

section Self

variable (k G : Type*) [CommSemiring k] [Monoid G] [MulSemiringAction G k] [SMulCommClass G k k]

/-- **For `A = k` with `k`-linear action, `SkewMonoidAlgebra k G` is `MonoidAlgebra k G`.** -/
def skewMonoidAlgebraSelfAlgEquiv : SkewMonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k G :=
  skewMonoidAlgebraToMonoidAlgebraAlgEquiv k smul_eq_self_of_smulCommClass_self

variable {k G}

@[simp]
theorem skewMonoidAlgebraSelfAlgEquiv_single (g : G) (r : k) :
    skewMonoidAlgebraSelfAlgEquiv k G (SkewMonoidAlgebra.single g r) =
      MonoidAlgebra.single g r :=
  (rfl)

@[simp]
theorem skewMonoidAlgebraSelfAlgEquiv_symm_single (g : G) (r : k) :
    (skewMonoidAlgebraSelfAlgEquiv k G).symm (MonoidAlgebra.single g r) =
      SkewMonoidAlgebra.single g r :=
  (rfl)

theorem skewMonoidAlgebraSelfAlgEquiv_of (g : G) :
    skewMonoidAlgebraSelfAlgEquiv k G (SkewMonoidAlgebra.of k G g) = MonoidAlgebra.of k G g :=
  (rfl)

theorem skewMonoidAlgebraSelfAlgEquiv_symm_of (g : G) :
    (skewMonoidAlgebraSelfAlgEquiv k G).symm (MonoidAlgebra.of k G g) =
      SkewMonoidAlgebra.of k G g :=
  (rfl)

end Self

end TauCeti
