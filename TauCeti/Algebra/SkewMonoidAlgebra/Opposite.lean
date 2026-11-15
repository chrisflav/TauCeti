/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.SkewMonoidAlgebra.Lift
public import TauCeti.Algebra.Ring.Action.Opposite

/-!
# The opposite of a skew group algebra

In `SkewMonoidAlgebra A G`, the basis elements multiply by the left skew-product law
`single g a * single h b = single (g * h) (a * g • b)`. In the multiplicative opposite
`(SkewMonoidAlgebra A G)ᵐᵒᵖ`, the reversed product is
`op (single g a) * op (single h b) = op (single (h * g) (b * h • a))`.

When `G` is a group, inversion on `G` combined with the inverse twist on `A` turns this reversed
product into the left skew product over the opposite coefficient semiring `Aᵐᵒᵖ` (equipped with
`TauCeti.MulOpposite.instMulSemiringAction`, `g • op a = op (g • a)`): the map

  `op (single g a) ↦ single g⁻¹ (op (g⁻¹ • a))`

is a ring isomorphism `(SkewMonoidAlgebra A G)ᵐᵒᵖ ≃+* SkewMonoidAlgebra Aᵐᵒᵖ G`, with inverse
`single g (op a) ↦ op (single g⁻¹ (g⁻¹ • a))`. When `A` is a `k`-algebra whose `G`-action
commutes with `k`, this upgrades to a `k`-algebra isomorphism.

## Main definitions

* `TauCeti.skewMonoidAlgebraOpRingEquiv`: the ring isomorphism
  `(SkewMonoidAlgebra A G)ᵐᵒᵖ ≃+* SkewMonoidAlgebra Aᵐᵒᵖ G` for a group `G`.
* `TauCeti.skewMonoidAlgebraOpAlgEquiv`: the `k`-algebra upgrade when `G` acts `k`-linearly on `A`.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics **82** (1993), §4.1.
-/

public noncomputable section

open MulOpposite SkewMonoidAlgebra

namespace TauCeti

section Semiring

variable (A G : Type*) [Semiring A] [Group G] [MulSemiringAction G A]

-- Auxiliary monoid homomorphism `G →* (SkewMonoidAlgebra A G)ᵐᵒᵖ` sending `g` to
-- `op (single g⁻¹ 1)`.
private def invOpOf : G →* (SkewMonoidAlgebra A G)ᵐᵒᵖ where
  toFun g := op (SkewMonoidAlgebra.of A G g⁻¹)
  map_one' := by simp
  map_mul' g h := by
    rw [mul_inv_rev, map_mul, op_mul]

-- Auxiliary ring homomorphism `SkewMonoidAlgebra Aᵐᵒᵖ G →+* (SkewMonoidAlgebra A G)ᵐᵒᵖ` sending
-- `single g (op a)` to `op (single g⁻¹ (g⁻¹ • a))`.
private def fromSkewOpRingHom : SkewMonoidAlgebra Aᵐᵒᵖ G →+* (SkewMonoidAlgebra A G)ᵐᵒᵖ :=
  liftNCRingHom (singleOneRingHom (k := A) (G := G)).op (invOpOf A G) fun {x y} ↦ by
    induction x using MulOpposite.rec' with
    | h a =>
      apply unop_injective
      simp [invOpOf, singleOneRingHom]

private theorem fromSkewOpRingHom_single (g : G) (x : Aᵐᵒᵖ) :
    fromSkewOpRingHom A G (single g x) = op (single g⁻¹ (g⁻¹ • x.unop)) := by
  induction x using MulOpposite.rec' with
  | h a =>
    apply unop_injective
    -- `liftNCRingHom` evaluates via `liftNC`, which sends `single g (op a)` to `f (op a) * γ g`.
    change unop (liftNC ((singleOneRingHom (k := A) (G := G)).op : Aᵐᵒᵖ →+ _)
      (invOpOf A G) (single g (op a))) = single g⁻¹ (g⁻¹ • a)
    simp [invOpOf, singleOneRingHom]

-- Auxiliary ring homomorphism `SkewMonoidAlgebra A G →+* SkewMonoidAlgebra Aᵐᵒᵖᵐᵒᵖ G` applying
-- `RingEquiv.opOp A` to coefficients.
private def mapOpOpRingHom : SkewMonoidAlgebra A G →+* SkewMonoidAlgebra Aᵐᵒᵖᵐᵒᵖ G :=
  liftNCRingHom
    ((singleOneRingHom (k := Aᵐᵒᵖᵐᵒᵖ) (G := G)).comp (RingEquiv.opOp A).toRingHom)
    (SkewMonoidAlgebra.of Aᵐᵒᵖᵐᵒᵖ G) fun {x y} ↦ by
      simp [singleOneRingHom, RingEquiv.opOp]

private theorem mapOpOpRingHom_single (g : G) (a : A) :
    mapOpOpRingHom A G (single g a) = single g (op (op a)) := by
  -- `liftNCRingHom` evaluates via `liftNC` on `single g a`.
  change liftNC (((singleOneRingHom (k := Aᵐᵒᵖᵐᵒᵖ) (G := G)).comp
    (RingEquiv.opOp A).toRingHom) : A →+ _) (SkewMonoidAlgebra.of Aᵐᵒᵖᵐᵒᵖ G) (single g a) =
    single g (op (op a))
  simp [singleOneRingHom, RingEquiv.opOp]

-- Auxiliary ring homomorphism `(SkewMonoidAlgebra A G)ᵐᵒᵖ →+* SkewMonoidAlgebra Aᵐᵒᵖ G` sending
-- `op (single g a)` to `single g⁻¹ (op (g⁻¹ • a))`.
private def toSkewOpRingHom : (SkewMonoidAlgebra A G)ᵐᵒᵖ →+* SkewMonoidAlgebra Aᵐᵒᵖ G :=
  (RingEquiv.opOp (SkewMonoidAlgebra Aᵐᵒᵖ G)).symm.toRingHom.comp
    ((fromSkewOpRingHom Aᵐᵒᵖ G).comp (mapOpOpRingHom A G)).op

private theorem toSkewOpRingHom_op_single (g : G) (a : A) :
    toSkewOpRingHom A G (op (single g a)) = single g⁻¹ (op (g⁻¹ • a)) := by
  simp [toSkewOpRingHom, mapOpOpRingHom_single, fromSkewOpRingHom_single]

/-- **Opposite of a skew group algebra.** For a group `G` acting on a semiring `A` by semiring
automorphisms, `(SkewMonoidAlgebra A G)ᵐᵒᵖ` is isomorphic to `SkewMonoidAlgebra Aᵐᵒᵖ G` via
`op (single g a) ↦ single g⁻¹ (op (g⁻¹ • a))`, with inverse
`single g (op a) ↦ op (single g⁻¹ (g⁻¹ • a))`. -/
def skewMonoidAlgebraOpRingEquiv :
    (SkewMonoidAlgebra A G)ᵐᵒᵖ ≃+* SkewMonoidAlgebra Aᵐᵒᵖ G :=
  RingEquiv.ofRingHom
    (toSkewOpRingHom A G)
    (fromSkewOpRingHom A G)
    (by
      apply RingHom.ext
      intro z
      induction z using SkewMonoidAlgebra.induction_on with
      | zero => simp
      | add p q hp hq =>
        simp only [RingHom.comp_apply, RingHom.id_apply, map_add] at hp hq ⊢
        rw [hp, hq]
      | single g x =>
        induction x using MulOpposite.rec' with
        | h a =>
          simp [fromSkewOpRingHom_single, toSkewOpRingHom_op_single])
    (by
      apply RingHom.ext
      intro z
      induction z using MulOpposite.rec' with
      | h w =>
        induction w using SkewMonoidAlgebra.induction_on with
        | zero => simp
        | add p q hp hq =>
          simp only [RingHom.comp_apply, RingHom.id_apply, op_add, map_add] at hp hq ⊢
          rw [hp, hq]
        | single g a =>
          simp [toSkewOpRingHom_op_single, fromSkewOpRingHom_single])

variable {A G}

/-- `skewMonoidAlgebraOpRingEquiv` sends `op (single g a)` to `single g⁻¹ (op (g⁻¹ • a))`. -/
@[simp]
theorem skewMonoidAlgebraOpRingEquiv_op_single (g : G) (a : A) :
    skewMonoidAlgebraOpRingEquiv A G (op (single g a)) = single g⁻¹ (op (g⁻¹ • a)) :=
  toSkewOpRingHom_op_single A G g a

/-- On coefficients embedded at `1`, `skewMonoidAlgebraOpRingEquiv` sends `op (single 1 a)` to
`single 1 (op a)`. -/
@[simp]
theorem skewMonoidAlgebraOpRingEquiv_op_singleOneRingHom (a : A) :
    skewMonoidAlgebraOpRingEquiv A G (op (singleOneRingHom a)) = singleOneRingHom (op a) := by
  simp [singleOneRingHom]

/-- On group elements, `skewMonoidAlgebraOpRingEquiv` sends `op (of A G g)` to `of Aᵐᵒᵖ G g⁻¹`. -/
theorem skewMonoidAlgebraOpRingEquiv_op_of (g : G) :
    skewMonoidAlgebraOpRingEquiv A G (op (SkewMonoidAlgebra.of A G g)) =
      SkewMonoidAlgebra.of Aᵐᵒᵖ G g⁻¹ := by
  simp

/-- The inverse of `skewMonoidAlgebraOpRingEquiv` sends `single g x` to
`op (single g⁻¹ (g⁻¹ • x.unop))`. -/
@[simp]
theorem skewMonoidAlgebraOpRingEquiv_symm_single (g : G) (x : Aᵐᵒᵖ) :
    (skewMonoidAlgebraOpRingEquiv A G).symm (single g x) = op (single g⁻¹ (g⁻¹ • x.unop)) :=
  fromSkewOpRingHom_single A G g x

/-- On `single g (op a)`, the inverse of `skewMonoidAlgebraOpRingEquiv` gives
`op (single g⁻¹ (g⁻¹ • a))`. -/
theorem skewMonoidAlgebraOpRingEquiv_symm_single_op (g : G) (a : A) :
    (skewMonoidAlgebraOpRingEquiv A G).symm (single g (op a)) = op (single g⁻¹ (g⁻¹ • a)) := by
  simp

/-- On coefficients embedded at `1`, the inverse of `skewMonoidAlgebraOpRingEquiv` sends
`single 1 x` to `op (single 1 x.unop)`. -/
@[simp]
theorem skewMonoidAlgebraOpRingEquiv_symm_singleOneRingHom (x : Aᵐᵒᵖ) :
    (skewMonoidAlgebraOpRingEquiv A G).symm (singleOneRingHom x) =
      op (singleOneRingHom x.unop) := by
  simp [singleOneRingHom]

/-- On group elements, the inverse of `skewMonoidAlgebraOpRingEquiv` sends `of Aᵐᵒᵖ G g` to
`op (of A G g⁻¹)`. -/
theorem skewMonoidAlgebraOpRingEquiv_symm_of (g : G) :
    (skewMonoidAlgebraOpRingEquiv A G).symm (SkewMonoidAlgebra.of Aᵐᵒᵖ G g) =
      op (SkewMonoidAlgebra.of A G g⁻¹) := by
  simp

end Semiring

section Algebra

variable (k A G : Type*) [CommSemiring k] [Semiring A] [Algebra k A] [Group G]
  [MulSemiringAction G A] [SMulCommClass G k A]

/-- **Opposite of a skew group `k`-algebra.** When `G` acts on a `k`-algebra `A` by `k`-algebra
automorphisms, `skewMonoidAlgebraOpRingEquiv A G` is a `k`-algebra isomorphism
`(SkewMonoidAlgebra A G)ᵐᵒᵖ ≃ₐ[k] SkewMonoidAlgebra Aᵐᵒᵖ G`. -/
def skewMonoidAlgebraOpAlgEquiv :
    (SkewMonoidAlgebra A G)ᵐᵒᵖ ≃ₐ[k] SkewMonoidAlgebra Aᵐᵒᵖ G where
  __ := skewMonoidAlgebraOpRingEquiv A G
  commutes' r := by
    -- Unfold `algebraMap` on the opposite skew algebra to `op (single 1 (algebraMap k A r))`.
    change skewMonoidAlgebraOpRingEquiv A G (op (single 1 (algebraMap k A r))) =
      single 1 (op (algebraMap k A r))
    rw [skewMonoidAlgebraOpRingEquiv_op_single, inv_one, smul_algebraMap]

variable {k A G}

@[simp]
theorem skewMonoidAlgebraOpAlgEquiv_apply (x : (SkewMonoidAlgebra A G)ᵐᵒᵖ) :
    skewMonoidAlgebraOpAlgEquiv k A G x = skewMonoidAlgebraOpRingEquiv A G x :=
  (rfl)

@[simp]
theorem skewMonoidAlgebraOpAlgEquiv_symm_apply (y : SkewMonoidAlgebra Aᵐᵒᵖ G) :
    (skewMonoidAlgebraOpAlgEquiv k A G).symm y = (skewMonoidAlgebraOpRingEquiv A G).symm y :=
  (rfl)

theorem skewMonoidAlgebraOpAlgEquiv_toRingEquiv :
    (skewMonoidAlgebraOpAlgEquiv k A G).toRingEquiv = skewMonoidAlgebraOpRingEquiv A G :=
  (rfl)

theorem skewMonoidAlgebraOpAlgEquiv_op_single (g : G) (a : A) :
    skewMonoidAlgebraOpAlgEquiv k A G (op (single g a)) = single g⁻¹ (op (g⁻¹ • a)) :=
  skewMonoidAlgebraOpRingEquiv_op_single g a

theorem skewMonoidAlgebraOpAlgEquiv_symm_single (g : G) (x : Aᵐᵒᵖ) :
    (skewMonoidAlgebraOpAlgEquiv k A G).symm (single g x) = op (single g⁻¹ (g⁻¹ • x.unop)) :=
  skewMonoidAlgebraOpRingEquiv_symm_single g x

theorem skewMonoidAlgebraOpAlgEquiv_symm_single_op (g : G) (a : A) :
    (skewMonoidAlgebraOpAlgEquiv k A G).symm (single g (op a)) = op (single g⁻¹ (g⁻¹ • a)) :=
  skewMonoidAlgebraOpRingEquiv_symm_single_op g a

end Algebra

end TauCeti
