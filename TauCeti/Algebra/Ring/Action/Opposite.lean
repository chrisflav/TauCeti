/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Opposite
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Opposite

/-!
# Semiring actions on the multiplicative opposite

Mathlib equips the multiplicative opposite `Aᵐᵒᵖ` with `DistribMulAction M Aᵐᵒᵖ` and
`MulDistribMulAction M Aᵐᵒᵖ` whenever `M` acts on `A`, by acting on the underlying element:
`m • op a = op (m • a)`. Combining these two instances makes `M` act on `Aᵐᵒᵖ` by semiring
endomorphisms whenever `M` has a `MulSemiringAction` on `A`.

This instance lets constructions parameterized by `[MulSemiringAction G A]`—in particular the
skew monoid algebra `SkewMonoidAlgebra Aᵐᵒᵖ G` and semilinear actions on right `A`-modules—be
applied directly to `Aᵐᵒᵖ`.

## Main declarations

* `TauCeti.MulOpposite.instMulSemiringAction`: `MulSemiringAction M Aᵐᵒᵖ` from
  `MulSemiringAction M A`.
* `TauCeti.MulSemiringAction.toRingHom_op`: the induced ring endomorphism of `Aᵐᵒᵖ` is the opposite
  of the ring endomorphism of `A`.
-/

public section

namespace TauCeti.MulOpposite

/-- A monoid acting on a semiring by semiring endomorphisms acts on its multiplicative opposite
by semiring endomorphisms, via `m • op a = op (m • a)`. -/
instance instMulSemiringAction {M A : Type*} [Monoid M] [Semiring A] [MulSemiringAction M A] :
    MulSemiringAction M Aᵐᵒᵖ where
  __ := _root_.MulOpposite.instDistribMulAction
  __ := _root_.MulOpposite.instMulDistribMulAction

end TauCeti.MulOpposite

namespace TauCeti.MulSemiringAction

/-- For `m : M` acting on `Aᵐᵒᵖ`, the induced ring endomorphism `toRingHom M Aᵐᵒᵖ m` is the
opposite of `toRingHom M A m`. -/
@[simp]
theorem toRingHom_op (M A : Type*) [Monoid M] [Semiring A] [MulSemiringAction M A] (m : M) :
    _root_.MulSemiringAction.toRingHom M Aᵐᵒᵖ m = (_root_.MulSemiringAction.toRingHom M A m).op :=
  RingHom.ext fun _ ↦ rfl

end TauCeti.MulSemiringAction
